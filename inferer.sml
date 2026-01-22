use "datatypes.sml";
use "utils.sml";
use "parser.sml";

(*
val it =
  (Lti (("x",(NONE,NONE)),5),
   If (Lti (("x",(NONE,NONE)),3),Assign ("x",Plus (X "x",K (I 1))),Skip),
   Lti (("x",(NONE,NONE)),10)) : condition * imp * condition
*)

val dummy_cond = Lti (("x", (NONE, NONE)), 10);
val dummy_root_val = (dummy_cond, Skip, dummy_cond);
val root = ref (OpenNode(TripleNode dummy_root_val));

fun getElement([], _) = NONE
  | getElement(x::_, 0) = SOME x
  | getElement(x::xs, i) = getElement(xs, i - 1)

fun length ([]) = 0
  | length (x::xs) = 1 + length xs;

fun printLeaves (leaves, 0) = (print("unproven nodes are: \n\n"); printLeaves(leaves, 1))
  | printLeaves ([], y) = print("")
  | printLeaves ((leaf, level)::rest, y) = 
    (print (CharVector.tabulate ((level-1) * 4, fn _ => #" ") ^ "(" ^ Int.toString y ^ ") " ^ (nodeToString leaf) ^ "\n\n"); 
     printLeaves (rest, y+1)); 


fun getInvariant () =
   let
      val _ = print("to properly analyse this 'while', i need an invariant!\ntype it directly (ex. 'x > 2')\n- invariant: ");
      val input = TextIO.inputLine TextIO.stdIn
      val condi = case input of
           SOME line =>
            let
               val cleanLine = String.substring (line, 0, size line - 1);
               val (cond, _) = analyzeInvariant (tokenize cleanLine);
            in
               cond
            end
         | NONE => getInvariant ()
   in
      condi
   end

fun analyzeIf nod = 
   let
      val OpenNode(TripleNode (prec, prog, post)) = !nod
      val If (c, t, e) = prog;
      val then_triple = ref (OpenNode(TripleNode(And(prec, c), t, post)));
      val else_triple = ref (OpenNode(TripleNode(And(prec, Not(c)), e, post)));
      val children = [nod, then_triple, else_triple];
   in
      (* val _ = node := Visited(children) *)
      nod := Visited(children)
   end

fun analyzeWhile nod = 
   let
      val OpenNode (TripleNode (prec, prog, post)) = !nod
      val While (c, l) = prog;
      val invariant = getInvariant ();
      val _ = print("invariant is: " ^ (conditionToString invariant) ^ "\n");
      val strength = ref (OpenNode(Implication(Implies(prec, invariant))));
      val weak = ref (OpenNode(Implication(Implies(And(invariant, Not(c)), post))));
      val instr = ref (OpenNode((TripleNode (invariant, prog, And(invariant, Not(c))))));
      
      val children = [nod, strength, weak, instr]
   in
      nod := Visited(children)
   end

(*
   DA FARE!!!!
   se ho y < 5 e y := x+1
   dovrei fare
   x+1 <5
   ma invece faccio
   x < 5 - 1
   (le "var" sono string x domain, quindi devo avere una string 
   (un char) a sx)
*)
fun swap_i (constr, varInCond, integ, targetVar, replacementVar) =
   let 
      val (x, _) = varInCond;
   in 
      if x = targetVar then
         constr(targetVar, integ)
      else
         constr(varInCond, integ)
   end

fun swap_v (constr, (varInCond1 : variable), (varInCond2 : variable), targetVar, replacementVal ) =
   let 
      
      val newV1 = if (#1 varInCond1) = targetVar then replacementVal else varInCond1
      val newV2 = if (#1 varInCond2) = targetVar then replacementVal else varInCond2
   in 
      constr(newV1, newV2)
   end

fun substitute(And(cond1, cond2), variable, value) = 
      And(substitute (cond1, variable, value), substitute (cond2, variable, value))
  | substitute(Or(cond1, cond2), variable, value) =
      Or(substitute (cond1, variable, value), substitute (cond2, variable, value))
  | substitute(Implies(cond1, cond2), variable, value) =
      Implies(substitute (cond1, variable, value), substitute (cond2, variable, value))
  | substitute(Not(cond), variable, value) =
      Not(substitute (cond, variable, value))
  | substitute(cond, variable, value) =
      case cond of 
           Lti(var, i) => swap_i(Lti, var, i, variable, value)
         | Gti(var, i) => swap_i(Gti, var, i, variable, value)
         | Eqi(var, i) => swap_i(Lti, var, i, variable, value)
         | Neqi(var, i) => swap_i(Lti, var, i, variable, value)
         
         | Ltv(var1, var2) => swap_v(Ltv, var1, var2, variable, value)
         | Gtv(var1, var2) => swap_v(Gtv, var1, var2, variable, value)
         | Eqv(var1, var2) => swap_v(Eqv, var1, var2, variable, value)
         | Neqv(var1, var2) => swap_v(Neqv, var1, var2, variable, value)


(* 
  - vediamo se nella post-condizione c'è la variabile che abbiamo a sx
  - se c'è, la sostituiamo nella post con quello che c'è a dx
  - se non c'è, copiamo la post-condizione uguale
*)
fun analyzeAssign (nod) = 
   let
      val OpenNode (TripleNode (prec, prog, post)) = !nod
      val Assign(variable, value) = prog

      val newPrec = substitute(post, variable, value)
   in
      nod := ProvenNode (TripleNode(newPrec, prog, post))
   end
   
(* i + forti *)
fun visit (nod, l) = 
   case !nod of
      OpenNode i => [(nod, l)]
    | Visited i =>
        let
            val (me::rest) = i
        in 
            List.concat (map (fn x => visit (x, l+1)) rest)
        end
    | _ => []

fun updateTree (nod) = 
   case !nod of
      ProvenNode i => true
    | Visited i =>
        let
            val (me::rest) = i
            val isProved = List.all (fn x => updateTree x) rest;
        in
            if isProved then 
                (me := ProvenNode me;
                nod := ProvenNode(nod))
            else ();
            isProved
    end
    | _ => false


fun infer nod = 
   case nod of
      ref (OpenNode(TripleNode opp)) =>
         let 
            val (pre, prog, post) = opp;
            val _ = case prog of
                 If i => analyzeIf (nod)
               | While w => analyzeWhile (nod) 
               (*
               | Skip => (* skip? *);
               | Sec => analyzeSec (nod);
               | Assign => analyzeAssign (nod); *)
               | _ => raise ParseError "invalid program"
            
               (* fun analyse (prec :: If :: post) = 
               | analyse (prec :: While :: post) = 
               | analyse (prec :: Skip :: post) = 
               | analyse (prec :: Sec :: post) =
               | analyse (prec :: Assign :: post) =  *)
         in
            nod
         end

      | _ => raise ParseError "invalid program";


fun handleNode n =
   let
      val _ = infer n;
      val _ = updateTree root;
      val leveledLeaves = visit (root, 0)
   in
      leveledLeaves
   end

(* current leaves contains leaf nodes *)
fun interact (currentLeaves) =
   let
      val _ = OS.Process.system "clear";
      val _ = printLeaves (currentLeaves, 0);
      val _ = print ("\nenter index to select (or 'q' to quit): ")

      val input = 
         if (length currentLeaves) > 0 then 
            TextIO.inputLine TextIO.stdIn
         else
            SOME "DONE";
    in
      case input of
             NONE => print "stream closed ??\n"
           | SOME "DONE" => print "done proving!! :DD\n"
           | SOME line =>
                let
                     val cleanLine = String.substring (line, 0, size line - 1)
                     val leaves = map (fn (x, y) => x) (currentLeaves)
                    (* ^ newline removal *)
                in
                    if cleanLine = "q" then
                        print "giving up.... :(\n" 
                    else
                        case Int.fromString cleanLine of
                             NONE => 
                                 (print "aaaaaa wrong number or smth!\n"; 
                                 interact currentLeaves
                              ) (* same list *)
                           | SOME index =>
                                case getElement (leaves, index-1) of
                                     NONE => 
                                       (print "wrong!!!!! you idiot!!! >:-(\n"; 
                                         interact currentLeaves
                                       )
                                   | SOME item => 
                                       (print ("\nselected: " ^ (nodeToString item) ^ "\n");
                                       interact (handleNode item)) 
               end
   end


fun readTripleStr str = 
      let 
         val _ = OS.Process.system "clear";
         val trpl = parseTriple (tokenize str);
         val _ = root := OpenNode(TripleNode trpl);
         val _ = infer root;
         val leaves = visit (root, 0);
      in
         (* chiamiamo analisi triple *) 
         interact leaves
      end 

(* 
stack trace smlnj
CM.make "$smlnj-tdp/back-trace.cm";
SMLofNJ.Internals.TDP.mode := true;

OS.Process.system "clear";
use "inferer.sml";

readTripleStr "{ x <> 5 } if (x < 3) (while (x > 0) (x := x + 1)) (skip) { x < 10 }";
 *)

