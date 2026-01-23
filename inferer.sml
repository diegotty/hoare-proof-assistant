use "datatypes.sml";
use "utils.sml";
use "parser.sml";

(*
val it =
  (Lti (("x",(NONE,NONE)),5),
   If (Lti (("x",(NONE,NONE)),3),Assign ("x",Plus (X "x",K (I 1))),Skip),
   Lti (("x",(NONE,NONE)),10)) : condition * imp * condition
*)

val dummy_cond = Lt (X "x", K (I 10));
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
      OS.Process.system "clear";
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
      val tri = ref (OpenNode(TripleNode (And(invariant, c), l, invariant)));
      
      val children = [nod, strength, weak, tri]
   in
      OS.Process.system "clear";
      nod := Visited(children)
   end

(* 
  - vediamo se nella post-condizione c'è la variabile che abbiamo a sx
  - se c'è, la sostituiamo nella post con quello che c'è a dx
  - se non c'è, copiamo la post-condizione uguale
*)
fun analyzeAssign nod = 
   let
      val OpenNode (TripleNode (prec, prog, post)) = !nod
      val Assign(variable, value) = prog

      val newPrec = substitute(post, variable, value)
   in
      OS.Process.system "clear";
      print ("we have just proven that: " ^ nodeToString (ref (OpenNode (TripleNode(newPrec, prog, post)))) ^ "\n\n");
      nod := ProvenNode (ref(TripleNode(newPrec, prog, post)));
   end

fun getPreconditionConsideringNodeType node =
   case !node of
      OpenNode(TripleNode(pr1, _, _)) => pre
      Visited n => 
         let
            val OpenNode(TripleNode(pre, _, _)) = !(List.Nth(n, 0))
         in 
            pre
         end

fun buildNodes (prog, post) =
   case prog of
        Skip s => ref (OpenNode(TripleNode(post, prog, post)))
      | Assign (variable, value) => ref (ProvenNode(TripleNode(substitute(post, variable, value), prog, post)))
      | If (c, t, e) =>
         let 
            val node1 = buildNodes(t,c)
            val node2 = buildnodes(e,c)
            
            val pre1 = getPreconditionConsideringNodeType node1         
            val pre2 = getPreconditionConsideringNodeType node2
            
            val OpenNode(TripleNode(pre1, _, _)) = !node1;
            val OpenNode(TripleNode(pre2, _, _)) = !node2;

            val pre = And(Implies(c, pre1), Implies(Not(c), pre2))
         in
            ref Visited([ref OpenNode(pre, TripleNode(prog), post), node1, node2])
         end
      | While (c, d) => 
         let
            val i = getInvariant

            val impl1 = ref OpenNode((Implication(Implies(And(i, Not(c)), post))))
            val node = buildNode(d, i)
            val pre = getPreconditionConsideringNodeType node
            val impl2 = ref OpenNode(Implication(Implies(And(i, c), pre)))
         in
            ref Visited([ref OpenNode(i, TripleNode(prog), post), impl1, impl2])
         end
      | Sec (s1, s2) =>
         let
            val node1 = buildNodes(s2, post)
            val pre1 = getPreconditionConsideringNodeType node1
            
            val node2 = buildNodes(s1, pre1)
            val pre2 = getPreconditionConsideringNodeType node2
         in
            ref Visited([OpenNode(TripleNode(pre2, prog, post)), node1, node2])
         end

fun analyzeSex nod =
   let 
      val _ =  print("you first have to solve the right side of the seq! the triple is: " ^ tripleToString sec2 ^ "\n")
      val (prec, Sec(s1, s2), post) = !nod

      val wp = getWeakestPrec (nod);
      val sec2 = OpenNode(TripleNode(wp,s2, post))
      val sec1 = OpenNode(TripleNode(prec, s1, wp))

      val children = [nod, sec1, sec2]
   in
      nod := Visited(children)
   end

(* 

wp(C1​;C2​,Q)=wp(C1​, wp(C2​,Q))
wp(if B then S1​ else S2​,Q)=(B⟹wp(S1​,Q))∧(¬B⟹wp(S2​,Q))

 *)


(*

1) dico "c'è un seq !! devi)∧(¬B⟹wp(S2​,Q))
wp(while B inv I do S, Q)=I partire da destra"
2) dico "ecco la cosa a destra: stampo tripla"
3) chiedo <invio> per provare la cosa a destra
4) se la cosa a destra e' complicata, printo il suo sviluppo pezzo per pezzo interattivamente
5) poi dico "ok! hai dimostrato la cosa a destra"!!!! 
6) dico "ora dimostrami quella a sinistra se sei veramente fico"
7) lo faccio interattivamente
8) torno al normale flow del programma

*)



   



fun swapExp (cond, targetVar, replacementVar) =
   case cond of 
         Plus (exp1, exp2) => 
            Plus(swapExp (exp1, targetVar, replacementVar),
            swapExp (exp1, targetVar, replacementVar))
      | Minus (exp1, exp2) =>
            Minus(swapExp (exp1, targetVar, replacementVar),
            swapExp (exp1, targetVar, replacementVar))
      | X s => 
         if s = targetVar then
            replacementVar
         else
            cond
      | _ => cond

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
          Lt(exp1, exp2) => Lt(swapExp(exp1, variable, value), swapExp(exp2, variable, value))
         | Gt(exp1, exp2) => Gt(swapExp(exp1, variable, value), swapExp(exp2, variable, value))
         | Eq(exp1, exp2) => Eq(swapExp(exp1, variable, value), swapExp(exp2, variable, value))
         | Neq(exp1, exp2) => Neq(swapExp(exp1, variable, value), swapExp(exp2, variable, value))


   
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
                 If i => analyzeIf nod
               | While w => analyzeWhile nod 
               (*
               | Skip => (* skip? *);
               | Sec => analyzeSec (nod);*)
               | Assign a => analyzeAssign nod
               | _ => raise ParseError "invalid program"
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

