datatype k = I of int | B of bool;
datatype exp = K of k | X of string | Plus of (exp * exp) | Less of (exp * exp)
datatype imp = Skip | Sec of (imp * imp) | If of (bool * imp * imp) |  While of (bool * imp) | := of (string * exp);

type domain = int option * int option
type variable = string * domain (* implementazione delle variabili *)

(* pre/post condition *)
datatype condition =  Lti of (variable * int) | Ltv of (variable * variable)
                    | Gti of (variable * int) | Gtv of (variable * variable)
                    | Eqi of (variable * int) | Eqv of (variable * variable)
                    | And of (condition * condition) | Or of (condition * condition)
                    | Implies of (condition * condition)

type triple = (condition * imp * condition)


fun main () =
    case TextIO.inputLine TextIO.stdIn of
         SOME s => print s
       | NONE => print "NONE\n"
