(*
val it =
  (Lti (("x"f,(NONE,NONE)),5),
   If (Lti (("x",(NONE,NONE)),3),Assign ("x",Plus (X "x",K (I 1))),Skip),
   Lti (("x",(NONE,NONE)),10)) : condition * imp * condition
*)
fun conditionToString cond =
    case cond of 
          Lti ((str, _), i) => str ^ " < " ^ Int.toString i
        | Ltv ((str1, _), (str2, _)) => str1 ^ " < " ^ str2
        | Gti ((str, _), i) => str ^ " > " ^ Int.toString i
        | Gtv ((str1, _), (str2, _)) => str1 ^ " > " ^ str2
        | Eqi ((str,  _), i) => str ^ " = " ^ Int.toString i
        | Eqv ((str1, _), (str2, _)) => str1 ^ " = " ^ str2
        | Neqi ((str, _), i) => str ^ " <> " ^ Int.toString i
        | Neqv ((str1, _), (str2, _)) => str1 ^ " <> " ^ str2
        | And (c1, c2) => conditionToString(c1) ^ " & " ^ conditionToString(c2)
        | Or (c1, c2) => conditionToString(c1) ^ " <> " ^ conditionToString(c2)
        | Implies (c1, c2) => "(" ^ conditionToString(c1) ^ ") => (" ^ conditionToString(c2) ^ ")"
        | Not c => "!" ^ conditionToString(c);

fun expToString expr = 
    case expr of
          Plus (add1, add2) => expToString(add1) ^ " + " ^ expToString(add2)
        | Minus (sub1, sub2) => expToString(sub1) ^  " - " ^ expToString(sub2)
        | Less (v1, v2) => expToString(v1) ^ " < " ^ expToString(v2)
        | K(I i) => Int.toString i
        | K(B b) => Bool.toString b
        | X x => x;

fun progToString prog =
    case prog of 
          Skip => "skip "
        | Sec (p, q) => progToString(q) ^ ";" ^ progToString(q)
        | If (c, p, q) => "if " ^ conditionToString(c) ^ " then " ^ progToString(p) ^ " else " ^ progToString(q)
        | While (cond, p) => "while " ^ conditionToString(cond) ^ " do " ^ progToString(p)
        | Assign (str, expr) => str ^ " := " ^ expToString(expr) ^ " ";

fun tripleToString (prec, prog, post) =
    let
        val newprec = "{" ^ conditionToString prec ^ "} ";
        val newprog = progToString prog;
        val newpost = "{" ^ conditionToString post ^ "}";
    in
        newprec ^ newprog ^ newpost
    end

fun nodeToString n = 
    case !n of
          Implication i => conditionToString i
        | TripleNode i => tripleToString i
        | OpenNode(TripleNode(i)) => tripleToString i
        | OpenNode(Implication(i)) => conditionToString i
        | _ => "";