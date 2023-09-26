open Ast
open Exception
open Env

(* [typeof env e] is the type of [e] in the environment [env].
   That is, it is the [t] such that [env |- e : t].
   Raises: [TypecheckError] if no such [t] exists. *)
let rec typeof env = function
  | EInt _ -> TInt
  | EBool _ -> TBool
  | EString _ -> TString
  | EUnit _ -> TUnit
  | Fun (args, ret_type, body) -> TClosure' (args, ret_type, body, env)
  | Den x -> lookup_tc env x
  | If (e1, e2, e3) -> typeof_if env e1 e2 e3
  | Let (id, t, _, e1, e2) -> typeof_let env id t e1 e2
  | Op (op, e1, e2) -> typeof_binop env op e1 e2
  | Call (f, args) -> typeof_call env f args
  | Enclave body -> typeof_enclave [] body
  | End (id, t, _, e1, e2) -> typeof_end env id t e1 e2
  | Include body -> TUCode' body
  | Execute (e, t) -> typeof_execute env e t
  | Access (e, id, t) -> typeof_access env e id t
  | Declassify e -> typeof env e
  | Endorse e -> typeof env e

(* [typeof_if env e1 e2 e3] checks that:
   - [env |- e1 : t1] and t1 = TBool
   - [env |- e2 : t2] and [env |- e3 : t3] and t2 = t3
   Then, it returns t2 (or, equivalently, t3).
   Raises: [TypecheckError] if above typechecking rule fail. *)
and typeof_if env e1 e2 e3 =
  if typeof env e1 = TBool then
    let t2 = typeof env e2 in
    let t3 = typeof env e3 in
    if t2 = t3 then t2 else typecheck_error "If branches types must match"
  else typecheck_error "If guard must evaluate to a Bool"

(* [typeof_let env id t e1 e2] checks that:
   - [env |- e1 : t'] and t = t' or (t = TClosure | TEnclave | TUCode and t' = TClosure' | TEnclave' | TUCode')
   and returns t2, where t2 is the result of [env,(id, t) |- e2 : t1].
   Raises: [TypecheckError] if the type of e1 mismatches with [t] *)
and typeof_let env id t e1 e2 =
  let t' = typeof env e1 in
  if t = t' || check t t' then typeof (bind_tc env (id, t')) e2
  else typecheck_error "Let assignment typecheck failed"

and check t t' =
  match t' with
  | TClosure' _ -> t = TClosure
  | TUCode' _ -> t = TUCode
  | TEnclave' _ -> t = TEnclave
  | _ -> false

(* [typeof_binop env op e1 e2] checks that the operation and the
   operands types match.
   Raises: [TypecheckError] if the operations and operands mismatch. *)
and typeof_binop env op e1 e2 =
  match (op, typeof env e1, typeof env e2) with
  | Sum, TInt, TInt -> TInt
  | Times, TInt, TInt -> TInt
  | Minus, TInt, TInt -> TInt
  | Div, TInt, TInt -> TInt
  | Mod, TInt, TInt -> TInt
  | Equal, TInt, TInt -> TBool
  | EqualStr, TString, TString -> TBool
  | Lesser, TInt, TInt -> TBool
  | Greater, TInt, TInt -> TBool
  | Lesseq, TInt, TInt -> TBool
  | Greateq, TInt, TInt -> TBool
  | Diff, TInt, TInt -> TInt
  | Or, TBool, TBool -> TBool
  | And, TBool, TBool -> TBool
  | _ -> typecheck_error "Operator and operand typecheck failed"

(* [typeof_call env f args] checks that:
   - [env |- f : t] and t = TClosure'(...)
   - parameters' types match arguments' types
   - return type matches declared type
   Raises: [TypecheckError] if above conditions are not respected. *)
and typeof_call env f args =
  match typeof env f with
  | TClosure' (params, ret_type, body, fun_env) ->
      let ides = List.split params |> fst in
      let types = List.split params |> snd in
      let args_types = List.map (typeof env) args in
      if types = args_types then
        let fun_env' =
          List.combine ides types |> List.fold_left bind_tc fun_env
        in
        if typeof fun_env' body = ret_type then ret_type
        else typecheck_error "Function return value mismatch"
      else
        typecheck_error
          "Function parameters definition and passed arguments type mismatch"
  | _ -> typecheck_error "Call first argument must be of type Closure"

(* [typeof_execute env e t] checks that the return type of [e] matches [t].
   Raises: [TypecheckError] if typecheck fails. *)
and typeof_execute env e t =
  match typeof env e with
  | TUCode' body ->
      let t' = typeof env body in
      if t = t' || check t t' then t'
      else typecheck_error "Execution of untrusted code type mismatch"
  | _ -> typecheck_error "Trying to execute not UCode"

(* [typeof_enclave env body] checks that [env |- body : t] and t = TEnclave'(...).
    Raises: [TypecheckError] if typecheck fails. *)
and typeof_enclave env body =
  let t = typeof env body in
  match t with
  | TEnclave' _ -> t
  | _ -> typecheck_error "Not enclave inside Enclave(), maybe missed END"

(* [typeof_end env id t e1 e2] do the same as let but return the TEnclave type
    with the type's environment of the enclave.
    Raises: [TypecheckError] if typecheck fails. *)
and typeof_end env id t e1 e2 =
  let t' = typeof env e1 in
  if t = t' || check t t' then
    let _ = typeof (bind_tc env (id, t')) e2 in
    TEnclave' (bind_tc env (id, t'))
  else typecheck_error "Let assignment typecheck failed"

(* [typeof_access env e id t] checks that:
   - [env |- e : t'] and t' = TEnclave'(...)
   - the type of the field trying to be accessed matches the declared type [t]
   Raises: [TypecheckError] if typecheck fails. *)
and typeof_access env e id t =
  let t' = typeof env e in
  match t' with
  | TEnclave' enc_env ->
      let t' = lookup_tc enc_env id in
      if t = t' || check t t' then t'
      else typecheck_error "Wrong type of the accessed field"
  | _ -> typecheck_error "Trying to access to something that is not an enclave"

(* [typecheck e] is [e] if [e] typechecks, that is, if it exists a type [t]
   such that [{} |- e : t].
   Raises: [TypecheckError] if [e] does not typecheck. *)
let typecheck e =
  ignore (typeof [] e);
  e
