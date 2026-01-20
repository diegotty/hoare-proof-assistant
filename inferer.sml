use "parser.sml";

(*
val it =
  (Lti (("x",(NONE,NONE)),5),
   If (Lti (("x",(NONE,NONE)),3),Assign ("x",Plus (X "x",K (I 1))),Skip),
   Lti (("x",(NONE,NONE)),10)) : condition * imp * condition
*)
fun length ([] : int list) : int = 0
  | length (x::xs : int list) : int = 1 + length xs

(* extends list until needed index, and appends element *)
fun smartAppend(index, list, element) = 
   if (length list)-2 = index then
      list @ element 
   else 
      smartAppend(index, list @ [-1])


fun readTripleStr str = 
     let 
        val triple = parseTriple (tokenize str)
     in
        (* chiamiamo analisi triple *)
        infer ([triple], [], 0, [])
     end

fun infer (triples, childs, current, implications) = 
    let
         val currentTriple = List.nth(triples, current);
         val (prec, prog, post) = currentTriple;

         case prog of
            If => analyzeIf (triples, childs, current, currentTriple)
            | While => analyzeWhile (triples, childs, currentTriple, implications)
            | Skip => (* skip? *)
            | Sec => analyzeSec (triples, childs, currentTriple)
            | Assign => analyzeAssign (triples, childs, currentTriple)
            | _ => raise ParseError "invalid program";
         
         (*
            fun analyse (prec :: If :: post) = 
           | analyse (prec :: While :: post) = 
           | analyse (prec :: Skip :: post) = 
           | analyse (prec :: Sec :: post) =
           | analyse (prec :: Assign :: post) = 
           | analyse _ = raise ParseError "Invalid program"
         *)
    in
      analyse (prec, prog, post);
    end

and analyzeIf (triples, childs, current, currentTriple) = 
   let
      val (prec, prog, post) = currentTriple
      val If (c, t, e) = prog;
      val then_triple = (And(prec, c), t, post);
      val else_triple = (And(prec, Not(c)), e, post);

      (* new triples will be appended, so their indexes will be
      length of triples and length of triples + 1 *)
      val firstIn = length triples;
   in
      triples = triples @ thenTriple @ elseTriple;
      smartAppend (childs, current, [firstIn, firstIn+1])

   end

and analyzeWhile (triples, childs, current, currentTriple, implications) = 
   let
      val (prec, prog, post) = currentTriple
      val While (c, g) = prog;
      val strength = Implies(prec, (* invariante *))
      val weak = Implies(And((* invariante *), Not(g)), post)
      val then_triple = (And(prec, c), t, post);
      val else_triple = (And(prec, Not(c)), e, post);

      (* new triples will be appended, so their indexes will be
      length of triples and length of triples + 1 *)
      val firstIn = length triples;
   in
      implications = implications @ strenght @ weak;
      triples = triples @ thenTriple @ elseTriple;
      smartAppend (childs, current, [firstIn, firstIn+1])
   end



(* 
stack trace smlnj
CM.make "$smlnj-tdp/back-trace.cm";
SMLofNJ.Internals.TDP.mode := true;

OS.Process.system "clear";
use "inferer.sml";

readTripleStr "{ x <> 5 } if (x < 3) (x := x + 1) (skip) { x < 10 }";
 *)