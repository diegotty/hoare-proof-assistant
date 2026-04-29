(* used to transform into parsable characters *)
datatype token = 
    TLBrace | TRBrace       (* { } *)
  | TLParen | TRParen       (* ( ) *)
  | TSemicolon              (* ; *)
  | TLess | TLte            (* < <= *)
  | TGre | TGte             (* > >= *)
  | TPlus | TMinus | TTimes (* + - * *)
  | TEq | TNeq              (* = <> *)
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
          | scan (#"*" :: cs) = TTimes :: scan cs
          | scan (#"<" :: #"=" :: cs) = TLte :: scan cs
          | scan (#">" :: #"=" :: cs) = TGte :: scan cs
          | scan (#"<" :: #">" :: cs) = TNeq :: scan cs
          | scan (#"<" :: cs) = TLess :: scan cs
          | scan (#">" :: cs) = TGre :: scan cs
          | scan (#"=" :: cs) = TEq :: scan cs
          | scan (#"&" :: cs) = TAnd :: scan cs
          | scan (#"|" :: cs) = TOr :: scan cs
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


fun parseExp (TInt x :: TPlus :: rest) =
    let val (expr, rest) = parseExp rest in (Plus(Const x, expr), rest) end
  | parseExp (TInt x :: TMinus :: rest) =
    let val (expr, rest) = parseExp rest in (Minus(Const x, expr), rest) end
  | parseExp (TInt x :: TTimes :: rest) =
    let val (expr, rest) = parseExp rest in (Times(Const x, expr), rest) end
  | parseExp (TWord x :: TPlus :: rest) =
    let val (expr, rest) = parseExp rest in (Plus(Var x, expr), rest) end
  | parseExp (TWord x :: TMinus :: rest) =
    let val (expr, rest) = parseExp rest in (Minus(Var x, expr), rest) end
  | parseExp (TWord x :: TTimes :: rest) =
    let val (expr, rest) = parseExp rest in (Times(Var x, expr), rest) end
  | parseExp (TInt x :: rest) = (Const x, rest)
  | parseExp (TWord x :: rest) = (Var x, rest)
  | parseExp _ = raise Fail "parse error"

fun parseCondition (TWord "true" :: rest) = (True, rest)
  | parseCondition (TWord "false" :: rest) = (False, rest)
  | parseCondition tokens =
    let
        val (leftExp, rest1) = parseExp tokens
    in
        case rest1 of
              TEq :: rest2 => 
                let val (rightExp, finalTokens) = parseExp rest2 in (Eq(leftExp, rightExp), finalTokens) end
            | TLess :: rest2 => 
                let val (rightExp, finalTokens) = parseExp rest2 in (Lt(leftExp, rightExp), finalTokens) end
            | TLte :: rest2 => 
                let val (rightExp, finalTokens) = parseExp rest2 in (Lte(leftExp, rightExp), finalTokens) end
            | TGre :: rest2 => 
                let val (rightExp, finalTokens) = parseExp rest2 in (Gt(leftExp, rightExp), finalTokens) end
            | TGte :: rest2 => 
                let val (rightExp, finalTokens) = parseExp rest2 in (Gte(leftExp, rightExp), finalTokens) end
            | TNeq :: rest2 => 
                let val (rightExp, finalTokens) = parseExp rest2 in (Not(Eq(leftExp, rightExp)), finalTokens) end
            | _ => raise ParseError "invalid Condition: missing =, <, <=, >, >=, <>"
    end


fun analyzeInvariant tokens = 
    let
        val (leftCond, rest1) = parseCondition tokens
    in
        case rest1 of
              TAnd :: rest2 => 
                let val (rightCond, finalTokens) = analyzeInvariant rest2 in (And(leftCond, rightCond), finalTokens) end
            | TOr :: rest2 => 
                let val (rightCond, finalTokens) = analyzeInvariant rest2 in (Or(leftCond, rightCond), finalTokens) end
            | [] => (leftCond, []) (* invariants typed in stdin just end *)
            | _ => raise ParseError "syntax error: malformed invariant formula"
    end


fun analyzeCondition tokens = 
    let
        val (leftCond, rest1) = parseCondition tokens
    in
        case rest1 of
              TAnd :: rest2 => 
                let val (rightCond, finalTokens) = analyzeCondition rest2 in (And(leftCond, rightCond), finalTokens) end
            | TOr :: rest2 => 
                let val (rightCond, finalTokens) = analyzeCondition rest2 in (Or(leftCond, rightCond), finalTokens) end
            | TRBrace :: rest2 => (leftCond, TRBrace :: rest2)
            | TRParen :: rest2 => (leftCond, TRParen :: rest2)
            | _ => raise ParseError "syntax Error: malformed formula or missing } or )"
    end

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
