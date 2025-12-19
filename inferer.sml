use "parser.sml";

(* if rule *)
fun readTripleStr str = 
     let 
        val triple = parseTriple (tokenize str)
     in
        (* chiamiamo analisi triple *)
        infer ([triple], [], 0)
     end

fun infer (triples, childs) = 
    let
        
    in
    end

(* 
stack trace smlnj
CM.make "$smlnj-tdp/back-trace.cm";
SMLofNJ.Internals.TDP.mode := true;

OS.Process.system "clear";
use "inferer.sml";

readTripleStr "{ x < 5 } skip; while (x < 2) (x := 5; if (x < 3) (x := x + 1) (skip)) { x < 10 }";
 *)