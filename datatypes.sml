(* ---- DATATYPES ------ *)
type domain = int option * int option
type variable = string * domain (* implementazione delle variabili *)

(* pre/post condition *)
datatype condition =  Lti of (variable * int) | Ltv of (variable * variable)
                    | Gti of (variable * int) | Gtv of (variable * variable)
                    | Eqi of (variable * int) | Eqv of (variable * variable)
                    | Neqi of (variable * int) | Neqv of (variable * variable)
                    | And of (condition * condition) | Or of (condition * condition)
                    | Implies of (condition * condition) | Not of condition;

datatype k = I of int | B of bool;
datatype exp = K of k | X of string | Plus of (exp * exp) | Minus of (exp * exp) | Less of (exp * exp);
datatype imp = Skip | Sec of (imp * imp) | If of (condition * imp * imp) |  While of (condition * imp) | Assign of (string * exp);

type triple = (condition * imp * condition)

datatype node = OpenNode of node
   | ProvenNode of node ref
   | Visited of (node ref) list | Implication of condition
   | TripleNode of triple;