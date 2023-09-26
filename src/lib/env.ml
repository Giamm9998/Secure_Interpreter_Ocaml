open Exception

(* Environment contains variables with a their taint status *)
type 'v env = (string * 'v) list

(* Empty environment for the interpreter *)
let empty_env = []

(* [lookup env ide] searches for a binding with identifier [ide] in [env].
   Raises: [RuntimeError] if the binding does not exist. *)
let lookup env ide =
  match List.assoc_opt ide env with
  | Some v -> v
  | None -> Printf.sprintf "Unbound variable: %s" ide |> runtime_error

(* [bind env (id, value)] binds the given tuple in [env]*)
let bind env (id, x) = (id, x) :: env

(***********************************************************************************************)

(* Static environment used for typechecking *)
type 'v static_env = (string * 'v) list

(* [bind_tc env (id, x)] binds [(id, x)] in [env]. *)
let bind_tc env (id, x) = (id, x) :: env

(* [lookup_tc env ide] searches for a binding with identifier [ide] in [env].
   Raises: [TypecheckError] if the binding does not exist. *)
let lookup_tc env ide =
  match List.assoc_opt ide env with
  | Some v -> v
  | None -> Printf.sprintf "Unbound variable: %s" ide |> typecheck_error

(***********************************************************************************************)

(* Static environment used for confidentiality typechecking *)
type 'v static_conf_env = (string * 'v) list

(* [bind_ctc env (id, x)] binds [(id, x)] in [env]. *)
let bind_ctc env (id, x) = (id, x) :: env

(* [lookup_ctc env ide] searches for a binding with identifier [ide] in [env].
   Raises: [ConfidentialityError] if the binding does not exist. *)
let lookup_ctc env ide =
  match List.assoc_opt ide env with
  | Some v -> v
  | None -> Printf.sprintf "Unbound variable: %s" ide |> confidentiality_error

(* **********************************************************************************************)
