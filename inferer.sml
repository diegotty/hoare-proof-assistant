use "datatypes.sml";
use "utils.sml";
use "parser.sml";
use "analyze.sml";
use "treeprinter.sml";

val dummy_cond = Lt (X "x", K (I 10));
val dummy_root_val = (dummy_cond, Skip, dummy_cond);
val root = ref (OpenNode(TripleNode dummy_root_val));

fun visit (nod, l) = 
   case !nod of
      OpenNode i => [(nod, l)]
    | Visited i =>
        let
            val (me::rest) = i
        in 
            List.concat (map (fn x => visit (x, l+1)) rest)
        end
    | WrongNode i => (printFancyTree root; 
      print "the proof is over! the initial triple was not valid DD:\n\n";
      OS.Process.exit OS.Process.success)
    | _ => []

fun updateTree (nod) = 
   case !nod of
      ProvenNode i => true
      | Visited i =>
        let
            val (me::rest) = i
            val isProved = List.all (fn x => updateTree x) rest
        in
            if isProved then 
                case !me of
                     TripleNode(inner) => 
                        (
                           me := ProvenNode(ref(TripleNode(inner)));
                           nod := ProvenNode(ref(Visited(me::rest)))
                        )
                  | OpenNode(TripleNode(inner)) => 
                        (
                            me := ProvenNode(ref(TripleNode(inner)));
                            nod := ProvenNode(ref(Visited(me::rest)))
                        )
                   | ProvenNode _ => 
                        (
                            nod := ProvenNode(ref(Visited(me::rest)))
                        )
                   | _ => ()
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
               | Skip => nod := ProvenNode(ref (TripleNode(opp)))
               | Sec s => analyzeSex nod
               | Assign a => analyzeAssign nod
         in
            nod
         end
      | ref(OpenNode(Implication(i))) => 
            let 
               val _ = analyzeImplication nod
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
      val _ = printFancyTree root;
      val _ = print ("\nenter index to select (or 'q' to quit): ")
      
      val input = 
         if (length currentLeaves) > 0 then 
            TextIO.inputLine TextIO.stdIn
         else
            SOME "DONE";
    in
      case input of
             NONE => print "stream closed ??\n"
           | SOME "DONE" => (print "the proof is over! the initial triple was valid :DD\n"; printFancyTree root)
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
                                       (print ("\nselected: " ^ purple ^ (nodeToString item) ^ resetColor ^ "\n");
                                       interact (handleNode item)) 
               end
   end

fun readTripleStr str = 
      let 
         val _ = OS.Process.system "clear";
         val trpl = parseTriple (tokenize str);
         
         val _ = print("starting triple is:\n" ^ purple ^ tripleToString trpl ^ resetColor ^ "\n")
         
         val _ = getConfirmationFromUser()
         val _ = root := OpenNode(TripleNode trpl);
         val _ = infer root;
         val leaves = visit (root, 0);
      in
         interact leaves
      end 

(* 
stack trace smlnj
CM.make "$smlnj-tdp/back-trace.cm";
SMLofNJ.Internals.TDP.mode := true;

OS.Process.system "clear";
use "inferer.sml";

readTripleStr "{ x < 5 } skip; while (x < 2) (x := 5; skip) { x < 10 }";
 
 *)

