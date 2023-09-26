open Ast
open Env
open Exception

(* Helper function *)
let rec map_list l taint =
  match l with h1 :: t1 -> h1 taint :: map_list t1 taint | [] -> []

(* [eval env expr taint] evalues [expr] in the given enviroment [env]
   with the taint status [taint].
   Raises: [RuntimeError] if dividing by zero, or when a type mismatch occurs
   (i.e. the typechecker returned a false positive). *)
let rec eval env expr taint =
  match expr with
  | EInt n -> (Int n, taint)
  | EBool b -> (Bool b, taint)
  | EString x -> (String x, taint)
  | EUnit u -> (Unit u, taint)
  | Fun (args, _, body) -> (Closure (args, body, env), taint)
  | Den x -> eval_den env x
  | If (e1, e2, e3) -> eval_if env e1 e2 e3 taint
  | Let (id, _, _, e1, e2) -> eval_let env id e1 e2 taint
  | Op (op, e1, e2) -> eval_op env op e1 e2 taint
  | Call (f, args) -> eval_call env f args taint
  | Enclave body ->
      if taint then runtime_error "Tainted code trying to define Enclave"
      else eval empty_env body taint
  | End (id, _, _, e1, e2) -> eval_end env id e1 e2 taint
  | Access (e, id, _) -> eval_access env e id taint
  | Include e -> (UCode e, true)
  | Execute (e, _) -> eval_execute env e taint
  | Declassify e -> eval_dec env e taint
  | Endorse e -> eval_endorse env e taint

(* [eval_den env x] searches for a binding for [x] in [env].
   If the binding was a local one, it is returned. If it was global,
   it is checked that the Readable permission was set before returning it. *)
and eval_den env x = Env.lookup env x

(* [eval_if env e1 e2 e3] Evaluates [e1].
   If true, returns the evalution of [e2], else the evaluation of [e3].
   The taint status is given by the status of the guard OR-ed with the status of the branches
   to detect implicit flows.
   Raises: [RuntimeError] if [e1] does not evalute to a Bool *)
and eval_if env e1 e2 e3 taint =
  let v1, t1 = eval env e1 taint in
  match v1 with
  | Bool true ->
      let v2, t2 = eval env e2 t1 in
      (v2, t1 || t2)
  | Bool false ->
      let v3, t3 = eval env e3 t1 in
      (v3, t1 || t3)
  | _ -> runtime_error "If guard must evaluate to a boolean"

(* [eval_let env id vis e1 e2 taint]
   Evaluates [e1] and binds it to [id].
   Then, executes [e2] in the new environment. *)
and eval_let env id e1 e2 taint =
  let v1 = eval env e1 taint in
  eval (Env.bind env (id, v1)) e2 taint

(* [eval_op env op e1 e2 taint]
   Evaluates [e1] and [e2] and applies the given binary operation.
   Raises: [RuntimeError] if the operation is invalid, or we have
   divided by zero*)
and eval_op env op e1 e2 taint =
  let v1, t1 = eval env e1 taint in
  let v2, t2 = eval env e2 taint in
  (* As we "combine" two values, we also need to "combine" the two taint status *)
  match (op, v1, v2) with
  | Sum, Int n1, Int n2 -> (Int (n1 + n2), t1 || t2)
  | Times, Int n1, Int n2 -> (Int (n1 * n2), t1 || t2)
  | Minus, Int n1, Int n2 -> (Int (n1 - n2), t1 || t2)
  | Div, Int n1, Int n2 ->
      if n2 = 0 then runtime_error "Division by zero";
      (Int (n1 / n2), t1 || t2)
  | Mod, Int n1, Int n2 -> (Int (n1 mod n2), t1 || t2)
  | Equal, Int n1, Int n2 -> (Bool (n1 = n2), t1 || t2)
  | EqualStr, String s1, String s2 -> (Bool (s1 = s2), t1 || t2)
  | Lesser, Int n1, Int n2 -> (Bool (n1 < n2), t1 || t2)
  | Greater, Int n1, Int n2 -> (Bool (n1 > n2), t1 || t2)
  | Lesseq, Int n1, Int n2 -> (Bool (n1 <= n2), t1 || t2)
  | Greateq, Int n1, Int n2 -> (Bool (n1 >= n2), t1 || t2)
  | Diff, Int n1, Int n2 -> (Bool (n1 <> n2), t1 || t2)
  | Or, Bool b1, Bool b2 -> (Bool (b1 || b2), t1 || t2)
  | And, Bool b1, Bool b2 -> (Bool (b1 && b2), t1 || t2)
  | _ -> runtime_error "Invalid expression"

(* [eval_call env f args] evaluates the body of [f], if [f] in [env] was found of type Closure.
   First of all we check that we are not calling a tainted Closure.
   Then to evaluate [f] body, [args] are evaluated. Then, the body of [f] is evaluated in the saved
   environment of [f], augmented with the binding of (params * [args]).
   Raises: [RuntimeError] if [f] was not a closure, the number of arguments of [f] was mismatched,
   or the called function is tainted *)
and eval_call env f args taint =
  match eval env f taint with
  | Closure (params, body, fun_env), t ->
      if t then runtime_error "Calling tainted function"
      else if
        (* Check that the provided number of parameters matches the function declaration *)
        List.length args <> List.length params
      then
        runtime_error "Mismatched number of arguments passed to function call"
      else
        let args_val = map_list (List.map (eval env) args) taint in
        eval
          (List.combine (List.split params |> fst) args_val
          |> List.fold_left bind fun_env)
          body taint
  | _ -> runtime_error "Call first argument is not a closure"

(* [eval_access env enclave attribute taint]
   Evaluates [enclave] and then tries to access the file with id [attribute]
   Raises: [RuntimeError] if the accessed expression does evaluate to an enclave*)
and eval_access env enclave attribute taint =
  match eval env enclave taint with
  | REnclave e, _ -> Env.lookup e attribute
  | _ -> runtime_error "Not an Enclave"

(* [eval_end env id e1 e2 taint]
   Same as Let but it returns an Enclave. Must be the last instruction of the Enclave.
   Raises: [RuntimeError] if [taint]=true*)
and eval_end env id e1 e2 taint =
  if taint then runtime_error "Tainted code trying to use End"
  else
    let v1 = eval env e1 taint in
    let _ = eval (Env.bind env (id, v1)) e2 taint in
    (REnclave (Env.bind env (id, v1)), taint)

(* [eval_execute env e taint]
   Evaluates an unstrusted code
   Raises: [RuntimeError] if [e] is not an unstrusted code, if the untrusted code is untainted or if [taint]=true
   (It must be always tainted).*)
and eval_execute env e taint =
  if taint then runtime_error "Tainted code trying to call Execute"
  else
    match eval env e taint with
    | UCode body, true -> eval env body true
    | UCode _, false -> runtime_error "Found untainted untrusted code"
    | _ -> runtime_error "Execute not applied to untrusted code"

(* [eval_dec env e taint]
   Declassify a value to the security level Gateway.
   Raises: [RuntimeError] if [taint] is true or if the value to declasify is tainted (depends on tainted values)
   (It must be always tainted).*)
and eval_dec env e taint =
  if taint then runtime_error "Tainted code trying to call Declassify"
  else
    match eval env e taint with
    | v -> (
        match v with
        | _, true -> runtime_error "Cannot declassify tainted values"
        | _, false -> v)

(* [eval_dec env e taint]
   Transforms an untrusted value into a trusted one.
   Raises: [RuntimeError] if [taint] is true (tainted code cannot call Endorse)
   (It must be always tainted).*)
and eval_endorse env e taint =
  if taint then runtime_error "Tainted code trying to call Endorse"
  else match eval env e taint with v, _ -> (v, false)
