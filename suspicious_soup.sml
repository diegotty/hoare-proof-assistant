(* --- PARSE EXPRESSIONS (exp) --- *)

(* Parse atomic factors: Integers, Variables, or Parentheses *)
fun parseFactor (TInt i :: rest) = (K (I i), rest) (* returns the int *)
  | parseFactor (TWord "true" :: rest) = (K (B true), rest)
  | parseFactor (TWord "false" :: rest) = (K (B false), rest)
  | parseFactor (TWord x :: rest) = (X x, rest)
(* if there's a parenthesis + something else *)
  | parseFactor (TLParen :: rest) = 
      let val (e, r) = parseExp rest 
          val r2 = expect r TRParen
      in (e, r2) end
  | parseFactor _ = raise ParseError "Expected factor"

(* Parse Additions: Factor + Factor *)
and parsePlus tokens =
    let val (left, rest) = parseFactor tokens
    in 
        case rest of
             TPlus :: rest2 => 
                let val (right, rest3) = parsePlus rest2 
                in (Plus(left, right), rest3) end
           | _ => (left, rest)
    end

(* Parse Less Than: PlusExp < PlusExp (Lowest precedence here) *)
(* mi serve se ho tipo plus_exp < plus_exp in un assign (bool assign) *)
and parseExp tokens = 
    let val (left, rest) = parsePlus tokens
    in
        case rest of
             TLess :: rest2 =>
                let val (right, rest3) = parseExp rest2
                in (Less(left, right), rest3) end
           | _ => (left, rest)
    end

(* --- 2. PARSE COMMANDS (imp) --- *)

(* Because of Sequence (I1 ; I2), we parse atoms first, then chain them *)

fun parseAtomImp (TSemicolon :: rest) = parseAtomImp rest (* Skip extra semicolon (recursion 2+) *)
  | parseAtomImp (TWord "skip" :: rest) = (Skip, rest)
  
  (* Assignment: x := e *)
  (* rest è r-exp *)
  | parseAtomImp (TWord v :: TAssign :: rest) = 
      let val (e, r) = parseExp rest 
      in (Assign(v, e), r) end
      
  (* If: if true then c1 else c2 *)
  | parseAtomImp (TWord "if" :: rest) = 
      let 
         (* Strict adherence to your type: must be literal bool *)
         val (b, r1) = case rest of 
              (TWord "true" :: r) => (true, r)
            | (TWord "false" :: r) => (false, r)
            | _ => raise ParseError "If condition must be 'true' or 'false' based on datatype"
         val r2 = expect r1 (TWord "then")
         val (c1, r3) = parseImp r2
         val r4 = expect r3 (TWord "else")
         val (c2, r5) = parseImp r4
      in (If(b, c1, c2), r5) end

  (* While: while true do c *)
  | parseAtomImp (TWord "while" :: rest) =
      let
         val (b, r1) = case rest of
              (TWord "true" :: r) => (true, r)
            | (TWord "false" :: r) => (false, r)
            | _ => raise ParseError "While condition must be bool"
         val r2 = expect r1 (TWord "do")
         val (c, r3) = parseImp r2
      in (While(b, c), r3) end
      
  | parseAtomImp _ = raise ParseError "Unknown command"

(* Parse Sequence: atom ; atom ; atom ... *)
and parseImp tokens =
    let val (first, rest) = parseAtomImp tokens
    in
        case rest of
             TSemicolon :: rest2 => 
                let val (second, rest3) = parseImp rest2
                in (Sec(first, second), rest3) end
           | _ => (first, rest)
    end