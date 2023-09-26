open Lib
open Lib.Ast
open Lib.Env
open Lib.Exception

(* Interprets the given expression. This is done by typechecking it with the two type systems and,
   if it typechecks, it is executed. *)
let interprete e =
  let typecheked_exp =
    e |> Type_checker.typecheck |> Confidentiality.conf_typecheck
  in
  Interpreter.eval empty_env typecheked_exp false

(***********************************)
(* Tests *)
(***********************************)

let examples =
  [
    [
      ( "Anonymous functions work",
        Call (Fun ([ ("x", TInt) ], TInt, Op (Sum, Den "x", EInt 1)), [ EInt 3 ]),
        Some (Int 4, false) );
      ( "Functions accept multiple arguments",
        Call
          ( Fun ([ ("x", TInt); ("y", TInt) ], TInt, Op (Sum, Den "x", Den "y")),
            [ EInt 3; EInt 1 ] ),
        Some (Int 4, false) );
      ( "HW1 example",
        Let
          ( "enc",
            TEnclave,
            Gateway,
            Enclave
              (Let
                 ( "password",
                   TString,
                   Secret,
                   EString "secret",
                   End
                     ( "y",
                       TClosure,
                       Gateway,
                       Fun
                         ( [ ("guess", TString) ],
                           TBool,
                           Op (EqualStr, Den "guess", Den "password") ),
                       EUnit () ) )),
            Let
              ( "ucode",
                TUCode,
                Gateway,
                Include
                  (Call (Access (Den "enc", "y", TClosure), [ EString "secret" ])),
                Execute (Den "ucode", TBool) ) ),
        None );
    ];
    [
      ("Runtime error when dividing by zero", Op (Div, EInt 1, EInt 0), None);
      ( "Typecheck error test #1: if guard not bool",
        If (EInt 5, EInt 0, EInt 1),
        None );
      ( "Typecheck error test #2: if branches types don't match",
        If (EBool true, EInt 5, EString ""),
        None );
      ( "Typecheck error test #3: operands types don't match",
        Op (Sum, EInt 1, EBool true),
        None );
      ( "Typecheck error test #4: let assignment types mismatch",
        Let ("x", TString, Gateway, EInt 1, EUnit ()),
        None );
      ("Typecheck error test #5: Call non-Fun", Call (EInt 1, []), None);
      ( "Typecheck error test #6: Params-args types mismatch",
        Call (Fun ([ ("x", TString) ], TString, Den "x"), [ EInt 1 ]),
        None );
      ( "Typecheck error test #7: Return type mismatch",
        Call (Fun ([ ("x", TString) ], TInt, Den "x"), [ EString "x" ]),
        None );
      ( "Typecheck error test #8: Ok function",
        Call (Fun ([ ("x", TString) ], TString, Den "x"), [ EString "x" ]),
        Some (String "x", false) );
      ( "Typecheck error test #9: Non-ended Enclave",
        Let
          ( "my_enclave",
            TEnclave,
            Gateway,
            Enclave
              (Let ("password", TString, Secret, EString "s3cr3t", EUnit ())),
            Den "my_enclave" ),
        None );
      ( "Typecheck error test #10: Access non-Enclave",
        Access (EInt 1, "x", TInt),
        None );
      ( "Typecheck error test #11: Mismatch in accessed type",
        Let
          ( "my_enclave",
            TEnclave,
            Gateway,
            Enclave
              (End ("password", TString, Secret, EString "s3cr3t", EUnit ())),
            Access (Den "my_enclave", "password", TInt) ),
        None );
    ];
    [
      ( "Confidentiality error test #1: Explicit flow",
        Let
          ( "secret",
            TString,
            Secret,
            EString "53cr3t",
            Let ("x", TString, Gateway, Den "secret", Den "x") ),
        None );
      ( "Confidentiality error test #2: Implicit flow in if",
        Let
          ( "guard",
            TBool,
            Secret,
            EBool true,
            If
              (Den "guard", Let ("x", TInt, Gateway, EInt 2, EUnit ()), EUnit ())
          ),
        None );
      ( "Confidentiality error test #2: Implicit flow in if",
        Let
          ( "test",
            TBool,
            Secret,
            EBool true,
            If (EBool true, EBool false, Den "test") ),
        None );
      ( "Confidentiality error test #3: Implicit flow in if with let",
        Let
          ( "guard",
            TBool,
            Secret,
            EBool true,
            If
              ( Den "guard",
                Let ("x", TString, Gateway, EString "public", EUnit ()),
                EUnit () ) ),
        None );
      ( "Confidentiality error test #4: Implicit flow in nested if",
        Let
          ( "guard",
            TBool,
            Secret,
            EBool true,
            If
              ( Den "guard",
                If
                  ( EBool true,
                    Let ("x", TInt, Gateway, EInt 2, EUnit ()),
                    EUnit () ),
                EUnit () ) ),
        None );
      ( "Confidentiality error test #5: operands with different security levels",
        Let
          ( "secret_pin",
            TInt,
            Secret,
            EInt 1,
            Let
              ("x", TInt, Gateway, Op (Sum, EInt 1, Den "secret_pin"), EUnit ())
          ),
        None );
      ( "Confidentiality error test #6: Gateway function returns Secret values",
        Let
          ( "secret",
            TString,
            Secret,
            EString "s3cr3t",
            Call (Fun ([], TString, Den "secret"), []) ),
        None );
      ( "Confidentiality error test #7: Gateway function returns Secret values \
         through arguments",
        Let
          ( "secret",
            TString,
            Secret,
            EString "s3cr3t",
            Call (Fun ([ ("x", TString) ], TString, Den "x"), [ Den "secret" ])
          ),
        None );
      ( "Confidentiality error test #8: Accessing enclave private field",
        Let
          ( "enc",
            TEnclave,
            Gateway,
            Enclave
              (Let
                 ( "password",
                   TString,
                   Secret,
                   EString "secret",
                   End
                     ( "y",
                       TClosure,
                       Gateway,
                       Fun
                         ( [ ("guess", TString) ],
                           TBool,
                           Op (EqualStr, Den "guess", Den "password") ),
                       EInt 1 ) )),
            Access (Den "enc", "password", TString) ),
        None );
      ( "Confidentiality error test #9: Leak secret info from enclave",
        Let
          ( "enc",
            TEnclave,
            Gateway,
            Enclave
              (Let
                 ( "password",
                   TString,
                   Secret,
                   EString "secret",
                   End
                     ( "y",
                       TClosure,
                       Gateway,
                       Fun
                         ( [ ("guess", TString) ],
                           TBool,
                           Op (EqualStr, Den "guess", Den "password") ),
                       EInt 1 ) )),
            Call (Access (Den "enc", "y", TClosure), [ EString "secret" ]) ),
        None );
      ( "Confidentiality error test #10: Declassify allows to access enclave \
         private field",
        Let
          ( "enc",
            TEnclave,
            Gateway,
            Enclave
              (Let
                 ( "password",
                   TString,
                   Secret,
                   EString "s3cr3t",
                   End
                     ( "y",
                       TClosure,
                       Gateway,
                       Fun
                         ( [ ("guess", TString) ],
                           TBool,
                           Declassify
                             (Op (EqualStr, Den "guess", Den "password")) ),
                       EInt 1 ) )),
            Call (Access (Den "enc", "y", TClosure), [ EString "s3cr3t" ]) ),
        Some (Bool true, false) );
      ( "Confidentiality error test #11: Type system is incomplete \
         (non-interference satisfied, but typechecker rejects)",
        Let
          ( "secret",
            TInt,
            Secret,
            EInt 1,
            If
              ( Op (Equal, Den "secret", EInt 1),
                Den "secret",
                Let ("x", TBool, Gateway, EBool true, Den "x") ) ),
        None );
      ( "Confidentiality error test #12: Simple flow sensitivity",
        Let
          ( "secret",
            TInt,
            Secret,
            EInt 1,
            Let
              ( "secret",
                TInt,
                Gateway,
                EInt 2,
                Let ("test", TInt, Gateway, Den "secret", EUnit ()) ) ),
        Some (Unit (), false) );
    ];
    [
      ( "Taint analysis error test #1: Call tainted function directly ",
        Call
          ( Execute (Include (Fun ([], TString, EString "mal1c10u5")), TClosure),
            [] ),
        None );
      ( "Taint analysis error test #2: taint transmission ",
        Let
          ( "x",
            TString,
            Gateway,
            Execute (Include (EString "mal1c10u5"), TString),
            Den "x" ),
        Some (String "mal1c10u5", true) );
      ( "Taint analysis error test #3: taint transmission",
        Let
          ( "x",
            TBool,
            Gateway,
            Execute (Include (EBool true), TBool),
            If (Den "x", EString "then", EString "else") ),
        Some (String "then", true) );
      ( "Taint analysis error test #4: endorse ",
        Let
          ( "x",
            TString,
            Gateway,
            Execute (Include (EString "mal1c10u5"), TString),
            Endorse (Den "x") ),
        Some (String "mal1c10u5", false) );
      ( "Taint analysis error test #5: taint through untainted function ",
        Let
          ( "x",
            TString,
            Gateway,
            Execute (Include (EString "mal1c10u5"), TString),
            Call (Fun ([ ("x", TString) ], TString, Den "x"), [ Den "x" ]) ),
        Some (String "mal1c10u5", true) );
      ( "Taint analysis error test #6: declassify tainted value ",
        Let
          ( "x",
            TString,
            Secret,
            Execute (Include (EString "mal1c10u5"), TString),
            Declassify (Den "x") ),
        None );
      ( "Taint analysis error test #7: declassify cannot be called inside UCode ",
        Let
          ( "x",
            TString,
            Secret,
            EString "secret",
            Execute (Include (Declassify (Den "x")), TString) ),
        None );
      ( "Taint analysis error test #8: Endorse cannot be called inside UCode ",
        Let
          ( "x",
            TString,
            Secret,
            EString "secret",
            Execute (Include (Endorse (Den "x")), TString) ),
        None );
      ( "Taint analysis error test #9: Untrusted code cannot be endorsed by \
         mistake",
        Let
          ( "x",
            TString,
            Gateway,
            Execute (Endorse (Include (EString "mal1c10u5")), TString),
            Den "x" ),
        None );
      ( "Taint analysis error test #10: attacker tries to trigger declassify",
        Let
          ( "secret",
            TString,
            Secret,
            EString "s3cr3t",
            Let
              ( "x",
                TBool,
                Gateway,
                Execute (Include (EBool true), TBool),
                If (Den "x", Declassify (Den "secret"), EString "ok") ) ),
        None );
      ( "Taint analysis error test #11: attacker tries to call End",
        Execute
          (Include (End ("x", TUnit, Gateway, EUnit (), EUnit ())), TEnclave),
        None );
    ];
  ]

(****************)
(* RUN EXAMPLES *)
(****************)
let rec execute_examples examples =
  match examples with
  | [] -> ()
  | (title, e, expected_result) :: t ->
      let res =
        try
          let res = interprete e in
          if Some res = expected_result then "\027[0;32mPassed\027[0m"
          else
            (match res with
            | Int n, t -> string_of_int n ^ " " ^ string_of_bool t
            | Bool b, t -> string_of_bool b ^ " " ^ string_of_bool t
            | Closure _, t -> "function " ^ string_of_bool t
            | REnclave _, t -> "Enclave " ^ string_of_bool t
            | UCode _, t -> "Untrusted Code " ^ string_of_bool t
            | Unit _, t -> "() " ^ string_of_bool t
            | String x, t -> x ^ " " ^ string_of_bool t)
            |> Printf.sprintf "\027[0;31mFailed, got: %s\027[0m"
        with
        | RuntimeError x ->
            if Option.is_none expected_result then
              "\027[0;32mPassed\027[0m, got RE: " ^ x
            else Printf.sprintf "\027[0;31m[RuntimeError] %s\027[0m" x
        | TypecheckError x ->
            if Option.is_none expected_result then
              "\027[0;32mPassed\027[0m, got TE: " ^ x
            else Printf.sprintf "\027[0;31m[TypecheckError] %s\027[0m" x
        | ConfidentialityError x ->
            if Option.is_none expected_result then
              "\027[0;32mPassed\027[0m, got CE: " ^ x
            else Printf.sprintf "\027[0;31m[TypecheckError] %s\027[0m" x
      in
      Printf.printf "%s... %s\n" title res;
      execute_examples t

let rec execute_all_examples examples =
  match examples with
  | [] -> ()
  | h :: t ->
      execute_examples h;
      execute_all_examples t

let () = execute_all_examples examples
