(* 
    this specific file was written by
    generative AI, as we thought printing the 
    derivation in an actual tree shape
    could be cute, but had no interest
    in implementing it ourselves
*)
fun realSize s = 
    let
        fun aux [] _ = 0
          | aux (c::cs) inside = 
              if Char.ord c = 27 then aux cs true 
              else if inside then
                  if c = #"m" then aux cs false 
                  else aux cs true
              else 1 + aux cs false
    in
        aux (String.explode s) false
    end;

fun smartWrap (text, maxLen) =
    let
        val words = String.tokens (fn c => c = #" ") text
        fun buildLines ([], currentLine, lines) = 
                if currentLine = "" then List.rev lines 
                else List.rev (currentLine :: lines)
          | buildLines (w::ws, currentLine, lines) =
                let
                    val len = size currentLine
                    val wLen = size w
                    val (newLine, newLines) = 
                        if len + wLen + 1 > maxLen andalso len > 0 
                        then (w, currentLine :: lines)
                        else if len = 0 then (w, lines)
                        else (currentLine ^ " " ^ w, lines)
                in
                    buildLines(ws, newLine, newLines)
                end
    in
        if size text <= maxLen then [text]
        else buildLines(words, "", [])
    end;

fun centerStr (s, width) =
    let
        val len = realSize s
        val padding = Int.max(0, width - len)
        val left = padding div 2
        val right = padding - left
        val spaces = String.implode o (List.tabulate)
    in
        spaces (left, fn _ => #" ") ^ s ^ spaces (right, fn _ => #" ")
    end;

fun realSize s = 
    let
        fun aux [] _ = 0
          | aux (c::cs) inside = 
              if Char.ord c = 27 then aux cs true 
              else if inside then
                  if c = #"m" then aux cs false 
                  else aux cs true
              else 1 + aux cs false
    in
        aux (String.explode s) false
    end;

fun smartWrap (text, maxLen) =
    let
        val words = String.tokens (fn c => c = #" ") text
        fun buildLines ([], currentLine, lines) = 
                if currentLine = "" then List.rev lines 
                else List.rev (currentLine :: lines)
          | buildLines (w::ws, currentLine, lines) =
                let
                    val len = size currentLine
                    val wLen = size w
                    val (newLine, newLines) = 
                        if len + wLen + 1 > maxLen andalso len > 0 
                        then (w, currentLine :: lines)
                        else if len = 0 then (w, lines)
                        else (currentLine ^ " " ^ w, lines)
                in
                    buildLines(ws, newLine, newLines)
                end
    in
        if size text <= maxLen then [text]
        else buildLines(words, "", [])
    end;

fun centerStr (s, width) =
    let
        val len = realSize s
        val padding = Int.max(0, width - len)
        val left = padding div 2
        val right = padding - left
        val spaces = String.implode o (List.tabulate)
    in
        spaces (left, fn _ => #" ") ^ s ^ spaces (right, fn _ => #" ")
    end;

fun printFancyTree (root : node ref) =
    let
        val MAX_NODE_WIDTH = 25 
        val GAP = 2
        val leafCounter = ref 1

        (* COLORS *)
        val red = "\027[31m"
        val green = "\027[32m"
        val yellow = "\027[33m"
        val resetColor = "\027[0m"
        
        fun makeYellow s = yellow ^ s ^ resetColor
        fun makeRed s = red ^ s ^ resetColor
        fun makeGreen s = green ^ s ^ resetColor

        fun spaces n = String.implode (List.tabulate (n, fn _ => #" "))

        fun layoutTree (n : node ref) =
            let
                (* 1. Identify Node Type *)
                val (nodeType, rawLabel, assignedIdx) = 
                    case !n of
                         OpenNode _ => 
                             let val idx = !leafCounter
                                 val _ = leafCounter := idx + 1
                             in ("OPEN", nodeToString n, SOME idx) end
                       | WrongNode _ => ("WRONG", nodeToString n, NONE)
                       | ProvenNode _ => ("PROVEN", nodeToString n, NONE) 
                       | _ => ("OTHER", nodeToString n, NONE)

                val labelLines = smartWrap(rawLabel, MAX_NODE_WIDTH)

                val childrenOpt = 
                    case !n of
                        Visited (kids) => SOME kids
                      | ProvenNode (ref (Visited (kids))) => SOME kids
                      | _ => NONE

            in
                case childrenOpt of
                    SOME (me :: sons) =>
                        let
                            val childResults = map layoutTree sons
              
                            val childWidths = map (fn (_, w, _, _, _) => w) childResults
                            val childCenters = map (fn (_, _, c, _, _) => c) childResults
                            val childLinesList = map (fn (l, _, _, _, _) => l) childResults
                            val childIsWrong = map (fn (_, _, _, b, _) => b) childResults
                            val childIndexes = map (fn (_, _, _, _, i) => i) childResults

                            val amIWrong = List.exists (fn x => x) childIsWrong

                            val totalGap = (List.length sons - 1) * GAP
                            val totalChildrenWidth = (List.foldr (op +) 0 childWidths) + totalGap
                            
                            val finalLabelLines = 
                                if amIWrong then map makeRed labelLines 
                                else if nodeType = "PROVEN" then map makeGreen labelLines
                                else labelLines
                                 
                            val labelWidth = List.foldr (fn (s, max) => Int.max(realSize s, max)) 0 finalLabelLines
                            val boxWidth = Int.max(labelWidth, totalChildrenWidth)
                             
                            val maxChildHeight = List.foldr Int.max 0 (map length childLinesList)
                            fun padLines (lines, w) = 
                                lines @ List.tabulate(maxChildHeight - length lines, fn _ => spaces w)
                            val paddedChildLines = ListPair.map padLines (childLinesList, childWidths)
                             
                            fun transpose [] = []
                              | transpose ([]::_) = []
                              | transpose x = (map hd x) :: transpose (map tl x)
                            fun mergeLine strings = String.concatWith (spaces GAP) strings
                            val mergedChildLines = map mergeLine (transpose paddedChildLines)

                            fun calcOffsets (w::ws) acc = acc :: calcOffsets ws (acc + w + GAP)
                              | calcOffsets [] _ = []
                            val offsets = calcOffsets childWidths 0
                            val absoluteCenters = ListPair.map (fn (off, c) => off + c) (offsets, childCenters)
                             
                            val childrenShift = (boxWidth - totalChildrenWidth) div 2
                            val shiftedCenters = map (fn c => c + childrenShift) absoluteCenters
                            val myCenter = boxWidth div 2

                            val pipeChar = if amIWrong then makeRed "|" 
                                           else if nodeType = "PROVEN" then makeGreen "|"
                                           else "|"
                            val line1 = spaces myCenter ^ pipeChar ^ spaces (boxWidth - myCenter - 1)
                            
                            val line2Chars = Array.array(boxWidth, " ") 

                            val _ = if length sons > 1 then
                                let val start = List.hd shiftedCenters
                                    val stop = List.last shiftedCenters
                                in List.app (fn i => Array.update(line2Chars, i, "-")) 
                                            (List.tabulate(stop - start, fn i => start + i + 1))
                                end else ()

                            val _ = ListPair.app (fn (son, childCenter) => 
                                case !son of
                                    ProvenNode _ =>
                                        let
                                            val (start, stop) = if myCenter < childCenter 
                                                                then (myCenter, childCenter) 
                                                                else (childCenter, myCenter)
                                            fun fill i = 
                                                if i > stop then () 
                                                else (Array.update(line2Chars, i, makeGreen "-"); fill (i+1))
                                        in fill start end
                                    | _ => ()
                            ) (sons, shiftedCenters)
                            
                            val _ = ListPair.app (fn (isWrong, childCenter) => 
                                if isWrong then
                                    let
                                        val (start, stop) = if myCenter < childCenter 
                                                            then (myCenter, childCenter) 
                                                            else (childCenter, myCenter)
                                        fun fill i = 
                                            if i > stop then () 
                                            else (Array.update(line2Chars, i, makeRed "-"); fill (i+1))
                                    in fill start end
                                else ()
                             ) (childIsWrong, shiftedCenters)

                            val joint = if amIWrong then makeRed "+" 
                                        else if nodeType = "PROVEN" then makeGreen "+"
                                        else "+"
                            val _ = Array.update(line2Chars, myCenter, joint)

                            val sonsInfo = ListPair.zip(sons, ListPair.zip(childIsWrong, childIndexes))
                            
                            val _ = ListPair.app (fn ((sonNode, (isWrong, idxOpt)), centerPos) => 
                                let
                                    val (symbol, colorFunc) = 
                                        case idxOpt of
                                            SOME idx => ("(" ^ Int.toString idx ^ ")", makeYellow)
                                          | NONE => 
                                              if isWrong then ("|", makeRed)
                                              else 
                                                  case !sonNode of
                                                       ProvenNode _ => ("|", makeGreen)
                                                       | _ => ("|", fn s => s)
                                    
                                    val symLen = size symbol
                                    val startPos = centerPos - (symLen div 2)
                                    
                                    fun writeStr (i, []) = ()
                                      | writeStr (i, c::cs) = 
                                          if i >= 0 andalso i < boxWidth then
                                             (Array.update(line2Chars, i, colorFunc (String.str c)); 
                                              writeStr(i+1, cs))
                                          else ()
                                in
                                    writeStr(startPos, String.explode symbol)
                                end
                             ) (sonsInfo, shiftedCenters)

                            val line2 = String.concat (Array.foldr (op ::) [] line2Chars)

                            val centeredLabels = map (fn s => centerStr(s, boxWidth)) finalLabelLines
                            val finalChildrenLines = map (fn s => 
                                spaces childrenShift ^ s ^ spaces (boxWidth - totalChildrenWidth - childrenShift)
                            ) mergedChildLines
                        in
                            (centeredLabels @ [line1, line2] @ finalChildrenLines, boxWidth, myCenter, amIWrong, NONE)
                        end

                    | _ => (* leaf *)
                        let
                            val (isWrong, colorFunc) = 
                                case nodeType of
                                    "WRONG" => (true, makeRed)
                                   | "OPEN" => (false, makeYellow)
                                   | "PROVEN" => (false, makeGreen)
                                   | _ => (false, fn s => s)

                            val finalLabelLines = map colorFunc labelLines
                            val labelWidth = List.foldr (fn (s, max) => Int.max(realSize s, max)) 0 finalLabelLines
                            val centeredLabels = map (fn s => centerStr(s, labelWidth)) finalLabelLines
                        in
                            (centeredLabels, labelWidth, labelWidth div 2, isWrong, assignedIdx)
                        end
            end
        
        val (lines, w, _, _, rootIdx) = layoutTree root
        
        val finalLines = 
            case rootIdx of
               SOME idx => 
                   let val header = centerStr(makeYellow ("(" ^ Int.toString idx ^ ")"), w)
                   in header :: lines end
             | NONE => lines
    in
        print "\n";
        List.app (fn s => print (s ^ "\n")) finalLines;
        print "\n"
    end;