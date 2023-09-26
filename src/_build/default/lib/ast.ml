(* Identifiers type declaration *)
type ide = string

(* Typechecking types definition *)
type 'e typ =
  | TBool
  | TInt
  | TString
  | TUnit
  (* We use a dummy type for closures, enclaves and ucodes type labels, and one for actual internal logic *)
  | TClosure
  | TClosure' of (ide * 'e typ) list * 'e typ * 'e * 'e typ Env.static_env
  | TEnclave
  | TEnclave' of 'e typ Env.static_env
  | TUCode
  | TUCode' of 'e

(* Type declaration for operations *)
type ops =
  | Sum
  | Times
  | Minus
  | Div
  | Mod
  | Equal
  | EqualStr
  | Lesser
  | Greater
  | Lesseq
  | Greateq
  | Diff
  | Or
  | And

(* Supported security levels in the lattice *)
type sec_level = Secret | Gateway

(* Supported expressions *)
type exp =
  | EInt of int
  | EBool of bool
  | EString of string
  | EUnit of unit
  | Fun of (ide * exp typ) list * exp typ * exp
  | Den of ide
  | Op of ops * exp * exp
  | If of exp * exp * exp
  | Let of ide * exp typ * sec_level * exp * exp
  | Call of exp * exp list
  | Enclave of exp
  | End of ide * exp typ * sec_level * exp * exp
  | Access of exp * ide * exp typ
  | Include of exp
  | Execute of exp * exp typ
  | Declassify of exp
  | Endorse of exp

type 'e sec_level' =
  | SL of sec_level
    (* We use a dummy type for closures, enclaves and ucodes type labels, and one for actual internal logic *)
  | FSL of
      sec_level * (ide * exp typ) list * exp * 'e sec_level' Env.static_conf_env
  | ESL of sec_level * 'e sec_level' Env.static_conf_env
  | USL of sec_level * exp

type 'v secure_runtime_value = 'v * bool

(* Runtime values are ints, booleans, closures, strings, unit (no-op), enclaves, untrusted codes *)
type runtime_value =
  | Int of int
  | Bool of bool
  | String of string
  | Unit of unit
  | Closure of
      (ide * exp typ) list * exp * runtime_value secure_runtime_value Env.env
  | REnclave of runtime_value secure_runtime_value Env.env
  | UCode of exp
