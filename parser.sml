(* used to transform into parsable characters *)
datatype token = 
    TLBrace | TRBrace       (* { } *)
  | TLParen | TRParen       (* ( ) *)
  | TSemicolon              (* ; *)
  | TLess | TPlus | TMinus  (* < + - *)
  | TGre | TEq | TNeq       (* > = <> *)
  | TAnd | TOr              (* & | ! *)
  | TAssign                 (* := *)
  | TInt of int             (* 42 *)
  | TWord of string         (* x, y, while, if... *)
  | TEof

(* ---- CODE ------ *)

fun splitWith pred [] = ([], [])
  | splitWith pred (x::xs) = 
      if pred x then 
          let val (prefix, suffix) = splitWith pred xs 
          in (x::prefix, suffix) end
      else 
          ([], x::xs)

fun tokenize (str: string) : token list =
    let
        (* list of chars *)
        val chars = String.explode str
        fun scan [] = []
          (* #" " -> char *)
          (* cases on first character of the string (::) (recursion on rest of string) *)
          | scan (#" " :: cs) = scan cs
          | scan (#"\n" :: cs) = scan cs
          | scan (#"{" :: cs) = TLBrace :: scan cs
          | scan (#"}" :: cs) = TRBrace :: scan cs
          | scan (#"(" :: cs) = TLParen :: scan cs
          | scan (#")" :: cs) = TRParen :: scan cs
          | scan (#";" :: cs) = TSemicolon :: scan cs
          | scan (#"+" :: cs) = TPlus :: scan cs
          | scan (#"-" :: cs) = TMinus :: scan cs
          | scan (#"<" :: #">" :: cs) = TNeq :: scan cs
          | scan (#"<" :: cs) = TLess :: scan cs
          | scan (#">" :: cs) = TGre :: scan cs
          | scan (#"=" :: cs) = TEq :: scan cs
          | scan (#"&" :: cs) = TAnd :: scan cs
          | scan (#"|" :: cs) = TOr :: scan cs
          (* handle := compound token *)
          | scan (#":" :: #"=" :: cs) = TAssign :: scan cs
          | scan (c :: cs) = 
            if Char.isDigit c then
                (* separa i primi n numeri consecutivi dal resto *)
                let val (digits, rest) = splitWith Char.isDigit (c::cs)
                    (* Int.fromString ritorna int option quindi necessario valOf per ottenere int *)
                    val num = valOf (Int.fromString (String.implode digits))
                in TInt num :: scan rest end
            else if Char.isAlpha c then
                let val (chars, rest) = splitWith Char.isAlpha (c::cs)
                in TWord (String.implode chars) :: scan rest end
            else scan cs
    in scan chars end

exception ParseError of string

(* to check if a token is the first token in our list *)
fun expect (tok :: rest) expected = 
    if tok = expected then rest else raise ParseError "Unexpected token"
  | expect [] _ = raise ParseError "Unexpected End of Input"

(* constructs LessThans from given formula
  if formula is word + < + int or word + < + word, it builds the datatype via the correct constructor
*)

fun parseInvariant [TWord v, TLess, TInt i] = Lt(Var v, Const i)
  | parseInvariant [TWord v1, TLess, TWord v2] = Lt(Var v1, Var v2)
  | parseInvariant [TWord v1, TEq, TInt i] = Eq(Var v1, Const i)
  | parseInvariant [TWord v1, TEq, TWord v2] = Eq(Var v1, Var v2)
  (*| parseInvariant [TWord v1, TNeq, TWord v2] = Neq(Var v1, Var v2*)
  | parseInvariant [TWord v1, TNeq, TInt i] = Not(Eq(Var v1, Const i))
  | parseInvariant [TWord v1, TNeq, TWord v2] = Not(Eq(Var v1, Var v2))
  | parseInvariant [TWord v1, TGre, TInt i] = Gt(Var v1, Const i)
  | parseInvariant [TWord v1, TGre, TWord v2] = Gt(Var v1, Var v2)
  | parseInvariant _ = raise ParseError "Invalid Condition"

fun parseCondition (TWord v :: TLess :: TInt i :: rest) = (Lt(Var v, Const i), rest)
  | parseCondition (TWord v1 :: TLess :: TWord v2 :: rest) = (Lt(Var v1, Var v2), rest)
  | parseCondition (TWord v1 :: TEq :: TInt i :: rest) = (Eq(Var v1, Const i), rest)
  | parseCondition (TWord v1 :: TEq :: TWord v2 :: rest) = (Eq(Var v1, Var v2), rest)
 (*| parseCondition (TWord v1 :: TNeq :: TInt i :: rest) = (Neq(Var v1, Const i, rest)*)
  | parseCondition (TWord v1 :: TNeq :: TInt i :: rest) = (Not(Eq(Var v1, Const i)), rest)
  (*| parseCondition (TWord v1 :: TNeq :: TWord v2 :: rest) = (Neq(Var v1, Var v2), rest)*)
  | parseCondition (TWord v1 :: TNeq :: TWord v2 :: rest) = (Not(Eq(Var v1, Var v2)), rest)
  | parseCondition (TWord v1 :: TGre :: TInt i :: rest) = (Gt(Var v1, Const i), rest)
  | parseCondition (TWord v1 :: TGre :: TWord v2 :: rest) = (Gt(Var v1, Var v2), rest)
  | parseCondition _ = raise ParseError "Invalid Condition"

fun analyzeInvariant(a :: b :: c :: TAnd :: rest) = 
      let
          val (rightConditions, finalTokens) = analyzeInvariant rest
          val (leftCond, _) = parseCondition [a,b,c]
      in
          (And(leftCond, rightConditions), finalTokens)
      end
      (* OR case: an OR between the current formula + the result finalTokensof the recursion *)
  | analyzeInvariant (a :: b :: c :: TOr :: rest) = 
      let 
          val (rightConditions, finalTokens) = analyzeInvariant rest
          val (leftCond, _) = parseCondition [a,b,c]
      in
          (Or(leftCond, rightConditions), finalTokens)
      end
  | analyzeInvariant [a, b, c] = (parseInvariant [a, b, c], [])
  | analyzeInvariant _ = (raise Fail "Syntax Error: malformed formula or missing ")



fun analyzeCondition (TWord "true" :: TAnd :: rest) = 
      let val (right, final) = analyzeCondition rest in (And(True, right), final) end
  | analyzeCondition (TWord "true" :: TOr :: rest) = 
      let val (right, final) = analyzeCondition rest in (Or(True, right), final) end

  (* "false" followed by AND/OR *)
  | analyzeCondition (TWord "false" :: TAnd :: rest) = 
      let val (right, final) = analyzeCondition rest in (And(False, right), final) end
  | analyzeCondition (TWord "false" :: TOr :: rest) = 
      let val (right, final) = analyzeCondition rest in (Or(False, right), final) end

  (* "true" / "false" as the final formula (followed by } or ) ) *)
  | analyzeCondition (TWord "true" :: TRBrace :: rest) = (True, TRBrace::rest)
  | analyzeCondition (TWord "true" :: TRParen :: rest) = (True, TRParen::rest)
  | analyzeCondition (TWord "false" :: TRBrace :: rest) = (False, TRBrace::rest)
  | analyzeCondition (TWord "false" :: TRParen :: rest) = (False, TRParen::rest)
  (* AND case: an AND between the current formula + the result of the recursion (other conditions) *)
  | analyzeCondition (a :: b :: c :: TAnd :: rest) = 
      let
          val (rightConditions, finalTokens) = analyzeCondition rest
          val (leftCond, _) = parseCondition [a,b,c]
      in
          (And(leftCond, rightConditions), finalTokens)
      end
      (* OR case: an OR between the current formula + the result of the recursion *)
  | analyzeCondition (a :: b :: c :: TOr :: rest) = 
      let 
          val (rightConditions, finalTokens) = analyzeCondition rest
          val (leftCond, _) = parseCondition [a,b,c]
      in
          (Or(leftCond, rightConditions), finalTokens)
      end
      (* base case (formula + TBrace, we're done with the conditions) *)
  | analyzeCondition (a :: b :: c :: TRBrace :: rest) = 
      let 
      (* rest is in the input, we don't need it from parseCondition *)
        val (finalCondition, _) = parseCondition [a, b, c]
        val right = TRBrace::rest
      (* parse the last formula, and return 'rest' (the other stuff) *)
      in
        (finalCondition, right)
      end
  | analyzeCondition (a :: b :: c :: TRParen :: rest) = 
      let 
        val (finalCondition, _) = parseCondition [a, b, c]
        val right = TRParen::rest
      in
        (finalCondition, right)
      end
  | analyzeCondition _ = raise Fail "Syntax Error: malformed formula or missing }"

(* returns a correct "term" term *)
(* fun parseExp (TInt x :: TPlus :: rest) = *)
(*     let *)
(*       val (expr, rest) = parseExp rest *)
(*     in  *)
(*       (Plus(Const x, expr), rest) *)
(*     end *)
(*   | parseExp (TInt x :: TMinus :: rest) = *)
(*     let *)
(*       val (expr, rest) = parseExp rest *)
(*     in  *)
(*       (Minus(Const x, expr), rest) *)
(*     end *)
(*   | parseExp (TInt x :: TLess :: rest) =  *)
(*     let  *)
(*       val (expr, rest) = parseExp rest *)
(*     in  *)
(*       (Less(Const x, expr), rest) *)
(*     end *)
(*   | parseExp (TWord x :: TPlus :: rest) = *)
(*     let  *)
(*       val (expr, rest) = parseExp rest *)
(*     in  *)
(*       (Plus(Var x, expr), rest) *)
(*     end *)
(*   | parseExp (TWord x :: TMinus :: rest) = *)
(*     let  *)
(*       val (expr, rest) = parseExp rest *)
(*     in  *)
(*       (Minus(Var x, expr), rest) *)
(*     end *)
(*   (* base cases: *) *)
(*   | parseExp (TInt x :: rest) = (Const x, rest) *)
(*   | parseExp (TWord x :: rest) = (Var x, rest) *)
(*   | parseExp _ = raise Fail "parse error" *)
(**)

fun parseExp (TInt x :: TPlus :: rest) =
    let val (expr, rest) = parseExp rest in (Plus(Const x, expr), rest) end
  | parseExp (TInt x :: TMinus :: rest) =
    let val (expr, rest) = parseExp rest in (Minus(Const x, expr), rest) end
  | parseExp (TWord x :: TPlus :: rest) =
    let val (expr, rest) = parseExp rest in (Plus(Var x, expr), rest) end
  | parseExp (TWord x :: TMinus :: rest) =
    let val (expr, rest) = parseExp rest in (Minus(Var x, expr), rest) end
  | parseExp (TInt x :: rest) = (Const x, rest)
  | parseExp (TWord x :: rest) = (Var x, rest)
  | parseExp _ = raise Fail "parse error"

(* x := expr (int / bool / term *)
fun parseAssign var vl = 
  let 
    val (value, rest) = parseExp vl;
  in 
    (Assign(var, value), rest)
  end

fun parseInstruction (TWord "skip" :: rest) = (Skip, rest)
  | parseInstruction (TWord "if" :: rest) = (parseIf rest)
  | parseInstruction (TWord "while" :: rest) = (parseWhile rest)
  | parseInstruction (TWord x :: TAssign :: rest) = (parseAssign x rest)
 
and parseIf tokens = 
  let 
    (* IF : parenthesis + formula + parenthesis *)
    val body = expect tokens TLParen;
    val (cond, body) = analyzeCondition body;
    val body = expect body TRParen;
    (* THEN : parenthesis + program + parenthesis *)
    val thn = expect body TLParen;
    val (thn, body) = parseImp thn;
    val body = expect body TRParen;

    (* ELSE: parenthesis + program + parenthesis *)
    val body = expect body TLParen;
    val (els, body) = parseImp body;
    val body = expect body TRParen;
  in 
    (If(cond, thn, els), body)
  end

(* very cool recursion *)
and parseImp tokens =
    (* computes the first instruction *)
    let 

    val (first, rest) = parseInstruction tokens

    in
        case rest of
            (* removes the semicolon *)
             TSemicolon :: rest2 => 
             (* parses to find if there is another instruction followed by rest *)
                let val (second, rest3) = parseImp rest2
                (* semantically concatenates the expressions with a Sec *)
                in (Sec(first, second), rest3) end
           | _ => (first, rest)
    end

(* syntax: (CONDITION)(q) *)
and parseWhile tokens = 
  let 
    (* WHILE : parenthesis + formula + parenthesis *)
    val body = expect tokens TLParen;
    val (cond, rest) = analyzeCondition body;
    val rest = expect rest TRParen;

    (* DO: parenthesis + program + parenthesis *)
    val body = expect rest TLParen;
    val (dom, rest) = parseImp body;
    val body = expect rest TRParen;
  in 
    (While(cond, dom), body)
  end


fun parseTriple tokens =
    let
        (* parse preconditions *)
        (* expect returns the rest of the list except for the token specified *)
        
        val rest1 = expect tokens TLBrace
        val (pre, rest2) = analyzeCondition rest1
        val rest3 = expect rest2 TRBrace
        
        (* parse code *)
        val (cmd, rest4) = parseImp rest3
        
        val rest5 = expect rest4 TLBrace
        val (post, rest6) = analyzeCondition rest5
        val _ = expect rest6 TRBrace
    in
        (pre, cmd, post)
    end


fun readTripleStr str = parseTriple (tokenize str)
