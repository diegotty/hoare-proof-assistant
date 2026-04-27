val resetColor  = "\027[0m";
val red    = "\027[31m";
val green  = "\027[32m";
val purple = "\027[35m";
val orange = "\027[38;5;214m";
val yellow = "\027[33m";

fun getElement([], _) = NONE
  | getElement(x::_, 0) = SOME x
  | getElement(x::xs, i) = getElement(xs, i - 1)

fun length ([]) = 0
  | length (x::xs) = 1 + length xs;

fun getConfirmationFromUser () =
   let
      val _ =  print("\nenter to continue: ")
      val input = TextIO.inputLine TextIO.stdIn
   in
      case input of
             NONE => print "stream closed ??\n"
           | SOME text => ()
   end  

(* fun expToString expr =  *)
(*     case expr of *)
(*           Plus (add1, add2) => expToString(add1) ^ " + " ^ expToString(add2) *)
(*         | Minus (sub1, sub2) => expToString(sub1) ^  " - " ^ expToString(sub2) *)
(*         | Less (v1, v2) => expToString(v1) ^ " < " ^ expToString(v2) *)
(*         | K(I i) => Int.toString i *)
(*         | K(B b) => Bool.toString b *)
(*         | X x => x; *)

fun expToString expr = 
    case expr of
          Plus (add1, add2)  => expToString(add1) ^ " + " ^ expToString(add2)
        | Minus (sub1, sub2) => expToString(sub1) ^ " - " ^ expToString(sub2)
        | Times (t1, t2)     => expToString(t1)   ^ " * " ^ expToString(t2)
        | Const i => Int.toString i
        | Var x => x             

fun conditionToString cond =
    case cond of 
          Lt (exp1, exp2) => expToString exp1 ^ " < " ^ expToString exp2
        | Lte (e1, e2) => expToString e1 ^ " <= " ^ expToString e2
        | Gt (exp1, exp2) => expToString exp1 ^ " > " ^ expToString exp2
        | Gte (e1, e2) => expToString e1 ^ " >= " ^ expToString e2
        | Eq (exp1, exp2) => expToString exp1 ^ " = " ^ expToString exp2
        (*| Neq (exp1, exp2) => expToString exp1 ^ " <> " ^ expToString exp2 *)
        | And (c1, c2) => conditionToString(c1) ^ " & " ^ conditionToString(c2)
        | Or (c1, c2) => conditionToString(c1) ^ " | " ^ conditionToString(c2)
        | Implies (c1, c2) => "(" ^ conditionToString(c1) ^ ") => (" ^ conditionToString(c2) ^ ")"
        | Not (Eq (e1, e2)) => expToString e1 ^ " <> " ^ expToString e2
        | Not c => "!(" ^ conditionToString(c) ^ ")"
        | True => "true"
        | False => "false";
        
fun progToString prog =
    case prog of 
          Skip => "skip"
        | Sec (p, q) => progToString(p) ^ "; " ^ progToString(q)
        | If (c, p, q) => "if " ^ conditionToString(c) ^ " then (" ^ progToString(p) ^ ") else (" ^ progToString(q) ^ ")"
        | While (cond, p) => "while (" ^ conditionToString(cond) ^ ") do (" ^ progToString(p) ^ ")"
        | WhileWithInv (cond, p, i) => "while (" ^ conditionToString(cond) ^ ") do (" ^ progToString(p) ^ ")"
        | Assign (str, expr) => str ^ " := " ^ expToString(expr) ^ "";

fun tripleToString (prec, prog, post) =
    let
        val newprec = "{" ^ conditionToString prec ^ "} ";
        val newprog = progToString prog;
        val newpost = " {" ^ conditionToString post ^ "}";
    in
        newprec ^ newprog ^ newpost
    end

fun nodeToString n = 
let 
  val ret = case !n of
        Implication i => conditionToString i
      | TripleNode i => tripleToString i
      | OpenNode i => nodeToString (ref i)
      | WrongNode i => nodeToString i
      | ProvenNode i => nodeToString i
      | Visited(me::rest) => nodeToString me
in
    ret
end

fun printLeaves (leaves, 0) = (print("\nunproven nodes are: \n\n"); printLeaves(leaves, 1))
  | printLeaves ([], y) = print("")
  | printLeaves ((leaf, level)::rest, y) = 
    (print (CharVector.tabulate ((level-1) * 4, fn _ => #" ") ^ "(" ^ Int.toString y ^ ") " ^ (nodeToString leaf) ^ "\n\n"); 
     printLeaves (rest, y+1)); 

exception Exit;
