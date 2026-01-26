(* ---- DATATYPES ------ *)
(* pre/post condition *)
datatype k = I of int | B of bool;
datatype exp = K of k | X of string | Plus of (exp * exp) | Minus of (exp * exp) | Less of (exp * exp);

datatype condition =  Lt of (exp * exp) 
                    | Gt of (exp * exp)
                    | Eq of (exp * exp)
                    | Neq of (exp * exp)
                    | And of (condition * condition) | Or of (condition * condition)
                    | Implies of (condition * condition) | Not of condition;

datatype imp = Skip | Sec of (imp * imp) | If of (condition * imp * imp) |  While of (condition * imp) | Assign of (string * exp);

type triple = (condition * imp * condition)

datatype node = OpenNode of node
   | ProvenNode of node ref
   | Visited of (node ref) list | Implication of condition
   | TripleNode of triple | WrongNode of node ref;