open Ast
open Exception
open Env

(* Notes for comments comments:
   - Γ represents the environment [env]
   - Γ(x) is the type of x *)

(* [sl1 <<= sl2] returns sl1 ⊑ sl2 *)
let ( <<= ) sl1 sl2 =
  match (sl1, sl2) with Secret, Gateway -> false | _ -> true

(* [sl1 >> sl2] returns sl1 ⊐ sl2 *)
let ( >> ) sl1 sl2 = not (sl1 <<= sl2)

(* [sl1 ++ sl2] returns sl1 ⊔ sl2 *)
let ( ++ ) sl1 sl2 =
  match (sl1, sl2) with Gateway, Gateway -> Gateway | _ -> Secret

(* [sec_level_of env ctx e] is the security level of [e] in the environment [env] -> Γ(e).
   Raises: [TypecheckError] if no such [t] exists. *)
let rec sec_level_of env ctx = function
  | EInt _ -> SL Gateway
  | EBool _ -> SL Gateway
  | EString _ -> SL Gateway
  | EUnit _ -> SL Gateway
  | Fun (params, _, body) -> FSL (Gateway, params, body, env)
  | Den x -> lookup_ctc env x
  | If (e1, e2, e3) -> sec_level_of_if env ctx e1 e2 e3
  | Let (id, _, sl, e1, e2) -> sec_level_of_let env ctx sl id e1 e2
  | Op (_, e1, e2) -> sec_level_of_op env ctx e1 e2
  | Call (f, args) -> sec_level_of_call env ctx f args
  | Enclave body -> sec_level_of_enclave [] body
  | End (id, _, sl, e1, e2) -> sec_level_of_end env ctx sl id e1 e2
  | Include body -> USL (Gateway, body)
  | Execute (e, _) -> sec_level_of_execute env ctx e
  | Access (e, id, _) -> sec_level_of_access env ctx e id
  | Declassify _ -> SL Gateway
  | Endorse e -> sec_level_of env ctx e

(* [sec_level_of_let env ctx sl id e1 e2] checks that Γ(e1) ⊔ ctx ⊑ sl.
   Then add sl to Γ and return the security level of [e2].
   Raises: [ConfidentialityError] if typecheck fails.*)
and sec_level_of_let env ctx sl id e1 e2 =
  let v = sec_level_of env ctx e1 in
  if get v ++ ctx <<= sl then sec_level_of (bind_ctc env (id, wrap v sl)) ctx e2
  else confidentiality_error "Explicit flow during assignment"

(* [sec_level_of_op env ctx e1 e2] returns Γ(e1) ⊔ Γ(e2) independently of the operation. *)
and sec_level_of_op env ctx e1 e2 =
  let v1 = sec_level_of env ctx e1 in
  let v2 = sec_level_of env ctx e2 in
  (* match op with
     | Sum -> SL (get v1 ++ get v2)
     | EqualStr -> SL (get v1 ++ get v2)
     | Times -> SL (get v1 ++ get v2)
     | Minus -> SL (get v1 ++ get v2)
     | Div -> SL (get v1 ++ get v2)
     | Mod -> SL (get v1 ++ get v2)
     | Equal -> SL (get v1 ++ get v2)
     | Lesser -> SL (get v1 ++ get v2)
     | Greater -> SL (get v1 ++ get v2)
     | Lesseq -> SL (get v1 ++ get v2)
     | Greateq -> SL (get v1 ++ get v2)
     | Diff -> SL (get v1 ++ get v2)
     | Or -> SL (get v1 ++ get v2)
     | And -> SL (get v1 ++ get v2) *)
  SL (get v1 ++ get v2)

(* [sec_level_of_if env ctx e1 e2 e3] does:
   - Compute the ctx' = Γ(e1) ⊔ ctx
   - Compute Γ(e2) and Γ(e3)
   - Check that there are no implicit flows to branches: ctx' ⊑ Γ(e2) and ctx' ⊑ Γ(e3)
   Raises: [ConfidentialityError] if typecheck fails or If guard is Gateway and branches are different*)
and sec_level_of_if env ctx e1 e2 e3 =
  let ctx' = get (sec_level_of env ctx e1) ++ ctx in
  let sl2 = get (sec_level_of env ctx' e2) in
  let sl3 = get (sec_level_of env ctx' e3) in
  (* if ctx' >> sl2 then
       confidentiality_error "Implicit flow from if guard to then branch"
     else if ctx' >> sl3 then
       confidentiality_error "Implicit flow from if guard to else branch" *)
  (* else *)
  match ctx' with
  | Secret -> SL Secret
  | Gateway ->
      if sl2 = sl3 then SL sl2
      else
        confidentiality_error "If guard is Gateway and branches are different"

(* [sec_level_of_enclave env body] checks that Γ(body) = ESL(...).
   Raises: [ConfidentialityError] if typecheck fails.*)
and sec_level_of_enclave env body =
  let sl' = sec_level_of env Gateway body in
  match sl' with
  | ESL (_, _) -> sl'
  | _ -> confidentiality_error "Something went wrong in Enclave"

(* [sec_level_of_end env ctx sl id e1 e2] do the same as let but return the ESL type
   with the type's environment of the enclave.
   Raises: [ConfidentialityError] if typecheck fails. *)
and sec_level_of_end env ctx sl id e1 e2 =
  let v = sec_level_of env ctx e1 in
  if get v ++ ctx <<= sl then
    let _ = sec_level_of (bind_ctc env (id, wrap v sl)) ctx e2 in
    ESL (Gateway, bind_ctc env (id, wrap v sl))
  else confidentiality_error "Explicit flow during assignment"

(* [sec_level_of_call env ctx f args] does:
   - check that Γ(body) = FSL(...)
   - assign args security levels to params and bind them in the function env
   - check that Gateway function does not leak secret info
   Raises: [ConfidentialityError] if above conditions are not respected. *)
and sec_level_of_call env ctx f args =
  match sec_level_of env ctx f with
  | FSL (sl, params, body, env') ->
      let slo = sec_level_of env' ctx in
      let env'' =
        List.combine (List.split params |> fst) (List.map slo args)
        |> List.fold_left bind_ctc env'
      in
      let sl' = sec_level_of env'' ctx body in
      if get sl' >> sl then
        confidentiality_error "Gateway function is leaking a secret value"
      else sl'
  | _ -> confidentiality_error "Called something that's not a function"

(* [sec_level_of_access env ctx e id] checks that:
   - Γ(e) = ESL(...)
   - No Secret fields of the Enclave are accessed
   Raises: [ConfidentialityError] if typecheck fails. *)
and sec_level_of_access env ctx e id =
  match sec_level_of env ctx e with
  | ESL (_, env') -> (
      let sl = lookup_ctc env' id in
      match get sl with
      | Gateway -> sl
      | Secret ->
          confidentiality_error "Trying to access a secret field of Enclave")
  | _ -> confidentiality_error "Something went wrong"

(* [sec_level_of_enclave env body] checks that Γ(body) = USL(...).
   Raises: [ConfidentialityError] if typecheck fails.*)
and sec_level_of_execute env ctx e =
  match sec_level_of env ctx e with
  | USL (_, body) -> sec_level_of env ctx body
  | _ -> confidentiality_error "Called Execute on something that's not UCode"

(* Extract actual security level from SL type *)
and get sl =
  match sl with
  | SL sl' -> sl'
  | FSL (sl', _, _, _) -> sl'
  | ESL (sl', _) -> sl'
  | USL (sl', _) -> sl'

(* Create wrapper for security level *)
and wrap v sl =
  match v with
  | SL _ -> SL sl
  | FSL (_, params, body, env) -> FSL (sl, params, body, env)
  | ESL (_, body) -> ESL (sl, body)
  | USL (_, body) -> USL (sl, body)

let conf_typecheck e =
  ignore (sec_level_of [] Gateway e);
  e
