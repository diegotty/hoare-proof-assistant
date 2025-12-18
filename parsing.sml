datatype k = I of int | B of bool;
datatype exp = K of k | X of string | Plus of (exp * exp) | Less of (exp * exp)
datatype imp = Skip | Sec of (imp * imp) | If of (bool * imp * imp) |  While of (bool * imp) | Assign of (string * exp);

type domain = int option * int option
type variable = string * domain (* implementazione delle variabili *)

(* pre/post condition *)
datatype condition =  Lti of (variable * int) | Ltv of (variable * variable)
                    | Gti of (variable * int) | Gtv of (variable * variable)
                    | Eqi of (variable * int) | Eqv of (variable * variable)
                    | And of (condition * condition) | Or of (condition * condition)
                    | Implies of (condition * condition)

type triple = (condition * imp * condition)

fun mkVar s : variable = (s, (NONE, NONE))

(* used to transform into parsable characters *)
datatype token = 
    TLBrace | TRBrace       (* { } *)
  | TLParen | TRParen       (* ( ) *)
  | TSemicolon              (* ; *)
  | TLess | TPlus           (* < + *)
  | TAnd | TOr              (* & | *)
  | TAssign                 (* := *)
  | TInt of int             (* 42 *)
  | TWord of string         (* x, y, while, if... *)
  | TEof

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
          | scan (#"<" :: cs) = TLess :: scan cs
          | scan (#"&" :: cs) = TAnd :: scan cs
          | scan (#"|" :: cs) = TOr :: scan cs
          (* handle := compound token *)
          | scan (#":" :: #"=" :: cs) = TAssign :: scan cs
          | scan (c :: cs) = 
            if Char.isDigit c then
                (* separa i primi n numeri consecutivi dal resto *)
                let val (digits, rest) = List.splitWith Char.isDigit (c::cs)
                    (* Int.fromString ritorna int option quindi necessario valOf per ottenere int *)
                    val num = valOf (Int.fromString (String.implode digits))
                in TInt num :: scan rest end
            else if Char.isAlpha c then
                let val (chars, rest) = List.splitWith Char.isAlpha (c::cs)
                in TWord (String.implode chars) :: scan rest end
            else scan cs
    in scan chars end

exception ParseError of string

(* to check if a token is the first token in our list *)
fun expect (tok :: rest) expected = 
    if tok = expected then rest else raise ParseError "Unexpected token"
  | expect [] _ = raise ParseError "Unexpected End of Input"

(* --- 3. PARSE CONDITIONS (condition) --- *)
(* Handles: x < 5, x < y *)
(* Extended to handle logic could go here, keeping it basic for clarity *)
(* constructs LessThans from given condition
  if condition is word + < + int or word + < + word, it builds the datatype via the correct constructor
*)
fun parseCondition (TWord v :: TLess :: TInt i :: rest) = (Lti(mkVar v, i), rest)
  | parseCondition (TWord v1 :: TLess :: TWord v2 :: rest) = (Ltv(mkVar v1, mkVar v2), rest)
  (* Add Eqi, Gti clauses similarly... *)
  | parseCondition _ = raise ParseError "Invalid Condition"


(* analyzes a condition (x < y AND x > 5) *)
(*PROBLEMA: RITORNANDO DUE COSE, AGGIUNGIAMO TUTTA LA TUPLA ALL'AND *)
fun analyzeCondition () = ()
  | analyzeCondition (a :: b :: c :: TAnd :: rest) = (And(parseCondition [a, b, c], analyzeCondition rest), rest)
  | analyzeCondition (a :: b :: c :: TOr :: rest) = (Or(parseCondition [a, b, c], analyzeCondition rest), rest)
  | analyzeCondition (rest) = (parseCondition rest, rest)


(*possible fix: *)
fun analyzeCondition (a :: b :: c :: TAnd :: rest) = 
      let
          (* Recurse: get the parsed tree for the right side, 
             AND the tokens remaining after the brace *)
          val (rightTree, finalTokens) = analyzeCondition rest
      in
          (And(parseCondition [a,b,c], rightTree), finalTokens)
      end

  | analyzeCondition (a :: b :: c :: TOr :: rest) = 
      let 
          val (rightTree, finalTokens) = analyzeCondition rest
      in
          (Or(parseCondition [a,b,c], rightTree), finalTokens)
      end

  | analyzeCondition (a :: b :: c :: TBrace :: rest) = 
      (* Parse the last condition, and return 'rest' (the other stuff) *)
      (parseCondition [a,b,c], rest)

  | analyzeCondition _ = raise Fail "Syntax Error: malformed condition or missing }"



fun parseTriple tokens =
    let
        (* parse preconditions *)
        (* expect returns the rest of the list except for the token specified *)
        val rest1 = expect tokens TLBrace
        (* fun analyzeCondition [] = []
          | analyzeCondition (a :: b :: c :: TAnd :: rest) = (And(parseCondition a::b::c, analyzeCondition rest), rest)
          | analyzeCondition (a :: b :: c :: TOr :: rest) = (Or(parseCondition a::b::c, analyzeCondition rest), rest)
          | analyzeCondition (rest) = (parseCondition rest, rest) *)
        val (pre, rest2) = analyzeCondition rest1
        (* val (pre, rest2) = parseCondition rest1 *)
        val rest3 = expect rest2 TRBrace
        
        (* parse code *)
        val (cmd, rest4) = parseImp rest3
        
        val rest5 = expect rest4 TLBrace
        val (post, rest6) = parseCondition rest5
        val _ = expect rest6 TRBrace
    in
        (pre, cmd, post)
    end

fun readTripleStr str = parseTriple (tokenize str)

(*
  sintassi : (CONDIZIONE) (q) (p)
*)
fun parseIf tokens = 
  let 
    (* IF : parenthesis + condition + parenthesis *)
    val body = expect tokens TLParen;
    val (cond, body) = analyzeCondition rest1;
    val body = expect body TRParen;

    (* THEN : parenthesis + program + parenthesis *)
    val thn = expect body TLParen;
    val (thn, body) = parseImp body;
    val body = expect body TRParen;

    (* ELSE: parenthesis + program + parenthesis *)
    val body = expect tokens TLParen;
    val (els, body) = parseImp body;
    val body = expect body TRParen;
  in 
    (If(cond, thn, els), body)
  end

(* sintassi : (CONDIZIONE)(q) *)
fun parseWhile tokens = 
  let 
    (* WHILE : parenthesis + condition + parenthesis *)
    val body = expect tokens TLParen;
    val (cond, body) = analyzeCondition rest1;
    val body = expect body TRParen;

    (* DO: parenthesis + program + parenthesis *)
    val body = expect tokens TLParen;
    val (dom, body) = parseImp body;
    val body = expect body TRParen;
  in 
    (While(cond, dom), body)
  end

(* returns a correct "exp" exp *)
fun parseExp (TInt x :: TPlus :: rest) = (Plus(K(I(x)), parseExp rest), rest)
  | parseExp (TInt x :: TLess :: rest) = (Less(K(I(x)), parseExp rest), rest)
  | parseExp (TWord x :: TPlus :: rest) = Plus(X(x), parseExp rest)
  (* base cases: *)
  | parseExp (TInt x :: rest) = K(I(x))
  | parseExp (TWord "true" :: rest) = K(B(x))
  | parseExp (TWord "false" :: rest) = K(B(x))
  | parseExp (TWord x :: rest) = X(x)
  | parseExp _ = raise Fail "parse error"


(* x := expr (int / bool / exp *)
fun parseAssign var vl = 
  let 
    val value = parseExp vl;
  in 
    (Assign(var, value), body)
  end
  

fun parseInstruction (TWord "skip" :: rest) = (Skip, rest)
  | parseInstruction (TWord "if" :: rest) = (parseIf rest)
  | parseInstruction (TWord "while" :: rest) = (parseWhile rest)
  | parseInstruction (TWord x :: TAssign :: rest) = (parseAssign x rest)


(* very cool recursion *)
fun parseImp tokens =
    (* computes the first instruction *)
    let val (first, rest) = parseInstruction tokens
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
