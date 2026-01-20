use "parser.sml";
use "utils.sml";

val root = ref OpenNode;

datatype node = OpenNode of triple
   | ProvenNode of node ref
   | Visited of (node ref) list | Implication of condition;

fun length ([] : int list) : int = 0
  | length (x::xs : int list) : int = 1 + length xs;

(*
val it =
  (Lti (("x"f,(NONE,NONE)),5),
   If (Lti (("x",(NONE,NONE)),3),Assign ("x",Plus (X "x",K (I 1))),Skip),
   Lti (("x",(NONE,NONE)),10)) : condition * imp * condition
*)

fun analyzeIf (nod) = 
   let
      val OpenNode (prec, prog, post) = !nod
      val If (c, t, e) = prog;
      val then_triple = ref (OpenNode(And(prec, c), t, post));
      val else_triple = ref (OpenNode(And(prec, Not(c)), e, post));
      val children = [nod, then_triple, else_triple];
   in
      (* val _ = node := Visited(children) *)
      nod := Visited(children)
   end

(* fun analyzeWhile (nod) = 
   let
      val OpenNode (prec, prog, post) = !nod
      val While (c, _) = prog;
      val strength = ref Implication(Implies(prec, (* invariante *)));
      val weak = ref Implication(Implies(And((* invariante *), Not(c)), post));
      val instr = ref (OpenNode ((* invariante *), prog, And((*invariante*), Not(c))));
      
      val children = [nod, strength, weak, instr]
   in
      nod := Visited(children)
   end *)

fun infer nod = 
   case !nod of 
      Implication imp =>
         raise ParseError "invalid program" 
      | OpenNode opp =>
         let 
            val (pre, prog, post) = opp;
            val _ = case prog of
               If i => analyzeIf (nod)
               (* | While => analyzeWhile (nod)
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

      
fun readTripleStr str = 
     let 
         val trpl = parseTriple (tokenize str);
         root := ref (OpenNode trpl);
     in
         (* chiamiamo analisi triple *) 
         infer root
     end

fun getElement ([], _) = NONE
  | getElement (x::xs, 0) = SOME x
  | getElement (x::xs, n) = getElement (xs, n - 1)

(*TODO: finire visita*)
fun visit (nod) = 
   case nod of
      OpenNode i => [i]
    | ProvenNode i => []
    | Implication i => [i]
    | Visited i => List.app (fn x => [visit x]) i

fun handleNode n =
   let
      val nod = infer n;
      
   in
      
   end

(* current list contains nodes *)

fun interact (currentList : string list) =
   let
      val _ = print "\n--- nodes are: ---\n"
      val _ = app (fn x => print (x ^ " ")) currentList
      val _ = print "\n\nenter index to select (or 'q' to quit): "

      if length currentList > 0 then 
         val input = TextIO.inputLine TextIO.stdIn
      else
         val input = "DONE"
    in
      case input of
            "DONE" => print "done proving!! :DD\n"
           | NONE => print "stream closed ??\n"
           | SOME line =>
                let
                    val cleanLine = String.substring (line, 0, size line - 1)
                    (* ^ newline removal *)
                in
                    if cleanLine = "q" then
                        print "giving up.... :( \n" 
                    else
                        case Int.fromString cleanLine of
                             NONE => 
                                 (print "aaaaaa wrong number!\n"; 
                                 interact currentList) (* same list *)
                           | SOME index =>
                                case getElement (currentList, index) of
                                     NONE => 
                                       (print "wrong!!!!! you idiot!!! >:-( \n"; 
                                         interact currentList)
                                   | SOME item => 
                                       (print ("\nselected: " ^ item ^ "\n");

                                       handleNode item;

                                       (*RISOLVI NODO*)
                                       (* NUOVA LISTA *)

                                       (* ricorsione *)
                                       interact currentList) 
               end
   end


(* 
stack trace smlnj
CM.make "$smlnj-tdp/back-trace.cm";
SMLofNJ.Internals.TDP.mode := true;

OS.Process.system "clear";
use "inferer.sml";

readTripleStr "{ x <> 5 } if (x < 3) (x := x + 1) (skip) { x < 10 }";
 *)

