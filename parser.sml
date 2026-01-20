(* ---- DATATYPES ------ *)
type domain = int option * int option
type variable = string * domain (* implementazione delle variabili *)

(* pre/post condition *)
datatype condition =  Lti of (variable * int) | Ltv of (variable * variable)
                    | Gti of (variable * int) | Gtv of (variable * variable)
                    | Eqi of (variable * int) | Eqv of (variable * variable)
                    | Neqi of (variable * int) | Neqv of (variable * variable)
                    | And of (condition * condition) | Or of (condition * condition)
                    | Implies of (condition * condition) | Not of condition;

datatype k = I of int | B of bool;
datatype exp = K of k | X of string | Plus of (exp * exp) | Less of (exp * exp);
datatype imp = Skip | Sec of (imp * imp) | If of (condition * imp * imp) |  While of (condition * imp) | Assign of (string * exp);

type triple = (condition * imp * condition)

fun mkVar s : variable = (s, (NONE, NONE))

(* used to transform into parsable characters *)
datatype token = 
    TLBrace | TRBrace       (* { } *)
  | TLParen | TRParen       (* ( ) *)
  | TSemicolon              (* ; *)
  | TLess | TPlus           (* < + *)
  | TGre | TEq | TNeq       (* > = *)
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

(* Handles: x < 5, x < y *)
(* Extended to handle logic could go here, keeping it basic for clarity *)
(* constructs LessThans from given condition
  if condition is word + < + int or word + < + word, it builds the datatype via the correct constructor
*)
fun parseCondition (TWord v :: TLess :: TInt i :: rest) = (Lti(mkVar v, i), rest)
  | parseCondition (TWord v1 :: TLess :: TWord v2 :: rest) = (Ltv(mkVar v1, mkVar v2), rest)
  | parseCondition (TWord v1 :: TEq :: TInt i :: rest) = (Eqi(mkVar v1, i), rest)
  | parseCondition (TWord v1 :: TEq :: TWord v2 :: rest) = (Eqv(mkVar v1, mkVar v2), rest)
  | parseCondition (TWord v1 :: TNeq :: TInt i :: rest) = (Neqi(mkVar v1, i), rest)
  | parseCondition (TWord v1 :: TNeq :: TWord v2 :: rest) = (Neqv(mkVar v1, mkVar v2), rest)
  | parseCondition (TWord v1 :: TGre :: TInt i :: rest) = (Gti(mkVar v1, i), rest)
  | parseCondition (TWord v1 :: TGre :: TWord v2 :: rest) = (Gtv(mkVar v1, mkVar v2), rest)
  | parseCondition _ = raise ParseError "Invalid Condition"

(* AND case: an AND between the current condition + the result of the recursion (other conditions) *)
fun analyzeCondition (a :: b :: c :: TAnd :: rest) = 
      let
          val (rightConditions, finalTokens) = analyzeCondition rest
          val (leftCond, _) = parseCondition [a,b,c]
      in
          (And(leftCond, rightConditions), finalTokens)
      end
      (* OR case: an OR between the current condition + the result of the recursion *)
  | analyzeCondition (a :: b :: c :: TOr :: rest) = 
      let 
          val (rightConditions, finalTokens) = analyzeCondition rest
          val (leftCond, _) = parseCondition [a,b,c]
      in
          (Or(leftCond, rightConditions), finalTokens)
      end
      (* base case (condition + TBrace, we're done with the conditions) *)
  | analyzeCondition (a :: b :: c :: TBrace :: rest) = 
      let 
      (* rest is in the input, we don't need it from parseCondition *)
        val (finalCondition, _) = parseCondition [a, b, c]
        val right = TBrace::rest
      (* parse the last condition, and return 'rest' (the other stuff) *)
      in
        (finalCondition, right)
      end
  | analyzeCondition _ = raise Fail "Syntax Error: malformed condition or missing }"


(* returns a correct "exp" exp *)
fun parseExp (TInt x :: TPlus :: rest) =
    let
      val (expr, rest) = parseExp rest
    in 
      (Plus(K(I(x)), expr), rest)
    end
  | parseExp (TInt x :: TLess :: rest) = 
    let 
      val (expr, rest) = parseExp rest
    in 
      (Less(K(I(x)), expr), rest)
    end
  | parseExp (TWord x :: TPlus :: rest) =
    let 
      val (expr, rest) = parseExp rest
    in 
      (Plus(X(x), expr), rest)
    end
  (* base cases: *)
  | parseExp (TInt x :: rest) = (K(I(x)), rest)
  | parseExp (TWord "true" :: rest) = (K(B(false)), rest)
  | parseExp (TWord "false" :: rest) = (K(B(true)), rest)
  | parseExp (TWord x :: rest) = (X(x), rest)
  | parseExp _ = raise Fail "parse error"

(* x := expr (int / bool / exp *)
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
    (* IF : parenthesis + condition + parenthesis *)
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
    (* WHILE : parenthesis + condition + parenthesis *)
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
stack trace smlnj
CM.make "$smlnj-tdp/back-trace.cm";
SMLofNJ.Internals.TDP.mode := true;

polyml stack trace
PolyML.Compiler.debug := true;


OS.Process.system "clear";
use "parser.sml";

readTripleStr "{ x < 5 } skip; while (x < 2) (x := 5; if (x < 3) (x := x + 1) (skip)) { x < 10 }";

readTripleStr "{x >= 0} b := x {b=x & b>=0}"
 *)