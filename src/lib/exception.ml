exception TypecheckError of string
exception RuntimeError of string
exception ConfidentialityError of string

let runtime_error x = raise (RuntimeError x)
let typecheck_error x = raise (TypecheckError x)
let confidentiality_error x = raise (ConfidentialityError x)
