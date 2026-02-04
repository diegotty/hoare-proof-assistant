fun transExp (e: exp) : f_term =
    case e of
       K (I i) => F_Const i
     | X s => F_Var s            
     | Plus(e1, e2) => F_Plus(transExp e1, transExp e2)
     | Minus(e1, e2) => F_Minus(transExp e1, transExp e2)
     | _ => raise ParseError "issues with the implication"

fun transImp (c: condition) : f_formula =
    case c of
       Lt(e1, e2) => F_Lt(transExp e1, transExp e2)
     | Gt(e1, e2) => F_Gt(transExp e1, transExp e2)
     | Eq(e1, e2) => F_Eq(transExp e1, transExp e2)
     | Neq(e1, e2) => 
            F_Or(F_Lt(transExp e1, transExp e2), F_Gt(transExp e1, transExp e2))
     | And(c1, c2) => F_And(transImp c1, transImp c2)
     | Or(c1, c2) => F_Or(transImp c1, transImp c2)
     | Implies(c1, c2) => F_Implies(transImp c1, transImp c2)
     | Not(c1) => F_Not(transImp c1)

fun getInvariant () =
   let
        val _ = print("to properly analyse this 'while', i need an invariant!\ntype it directly (ex. 'x > 2')\n-" ^ purple ^ "invariant: " ^ resetColor);
        val input = TextIO.inputLine TextIO.stdIn
        val condi = case input of
           SOME line =>
            let
                val cleanLine = String.substring (line, 0, size line - 1);
                val (cond, _) = analyzeInvariant (tokenize cleanLine);
            in
                cond
            end
         | NONE => getInvariant ()
    in
        condi
    end

fun analyzeIf nod = 
    let
        val OpenNode(TripleNode (prec, prog, post)) = !nod
        val If (c, t, e) = prog;
        val then_triple = ref (OpenNode(TripleNode(And(prec, c), t, post)));
        val else_triple = ref (OpenNode(TripleNode(And(prec, Not(c)), e, post)));
        val me = ref (TripleNode(prec, prog, post));
        val children = [me, then_triple, else_triple];
    in
        (* val _ = node := Visited(children) *)
        OS.Process.system "clear";
        nod := Visited(children)
    end

fun analyzeWhile nod = 
    let
        val OpenNode (TripleNode (prec, prog, post)) = !nod
        val While (c, l) = prog;
        val invariant = getInvariant ();
        val _ = print("invariant is: " ^ (conditionToString invariant) ^ "\n");
        val strength = ref (OpenNode(Implication(Implies(prec, invariant))));
        val weak = ref (OpenNode(Implication(Implies(And(invariant, Not(c)), post))));
        val tri = ref (OpenNode(TripleNode (And(invariant, c), l, invariant)));
        val me = ref (TripleNode (prec, prog, post));
        val children = [me, strength, weak, tri]
    in
        OS.Process.system "clear";
        nod := Visited(children)
    end

fun analyzeImplication nod =
    let
        val _ =  print("do you want to determine the validity of this implication?")
        val input = TextIO.inputLine TextIO.stdIn 

        val OpenNode(cond) = !nod
        val Implication(imp) = cond

        val isTrue = verify (transImp imp)
    in
        (
        getConfirmationFromUser;
        if isTrue then
            nod := ProvenNode(ref cond)
        else 
            nod := WrongNode(ref cond)
        )
    end

fun swapExp (cond, targetVar, replacementVar) =
    case cond of 
            Plus (exp1, exp2) => 
                Plus(swapExp (exp1, targetVar, replacementVar),
                swapExp (exp1, targetVar, replacementVar))
        | Minus (exp1, exp2) =>
                Minus(swapExp (exp1, targetVar, replacementVar),
                swapExp (exp1, targetVar, replacementVar))
        | X s => 
            if s = targetVar then
                replacementVar
            else
                cond
        | _ => cond


fun substitute(And(cond1, cond2), variable, value) = 
        And(substitute (cond1, variable, value), substitute (cond2, variable, value))
  | substitute(Or(cond1, cond2), variable, value) =
        Or(substitute (cond1, variable, value), substitute (cond2, variable, value))
  | substitute(Implies(cond1, cond2), variable, value) =
            Implies(substitute (cond1, variable, value), substitute (cond2, variable, value))
  | substitute(Not(cond), variable, value) =
      Not(substitute (cond, variable, value))
  | substitute(cond, variable, value) =
        case cond of 
            Lt(exp1, exp2) => Lt(swapExp(exp1, variable, value), swapExp(exp2, variable, value))
            | Gt(exp1, exp2) => Gt(swapExp(exp1, variable, value), swapExp(exp2, variable, value))
            | Eq(exp1, exp2) => Eq(swapExp(exp1, variable, value), swapExp(exp2, variable, value))
            | Neq(exp1, exp2) => Neq(swapExp(exp1, variable, value), swapExp(exp2, variable, value))

fun analyzeAssign nod = 
    let
        val OpenNode (TripleNode (prec, prog, post)) = !nod
        val Assign(variable, value) = prog

        val newPrec = substitute(post, variable, value)
        val me = ref(TripleNode(prec, prog, post))
        val newMe = ref(TripleNode(newPrec, prog, post))
        
        val impl = ref(OpenNode(Implication(Implies(prec, newPrec))))

        val children = [me, impl, newMe]

    in
        analyzeImplication impl;

        case !impl of 
              ProvenNode(n) => newMe := ProvenNode(ref(TripleNode(newPrec, prog, post)))
            | WrongNode(n) => ();

        OS.Process.system "clear";

        nod := Visited(children)
    end

fun getPreconditionConsideringNodeType node =
    case !node of
      ProvenNode i => 
        let
            val TripleNode(pr1, _, _) = !i
        in
            pr1
        end
    | Visited (me::rest) =>
        let
            val OpenNode(TripleNode(pre, _, _)) = !me
        in 
            pre
        end
    | OpenNode i =>
        let
            val TripleNode(pr1, _, _) = i
        in
            pr1
        end

fun buildNodes (prog, post) =
   case prog of
        Skip => 
        let
            val new = ref (ProvenNode(ref (TripleNode(post, prog, post))))
            val _ = print("\nproved: " ^ green ^ nodeToString new ^ resetColor ^ "\n")
        in 
            new
        end
      | Assign (variable, value) => 
        let
            val new = ref (OpenNode(TripleNode(substitute(post, variable, value), prog, post)))
            (* val _ = print("\nproved: " ^ green ^ nodeToString new ^ resetColor ^ "\n") *)
        in
            new
        end
      | If (c, t, e) =>
        let 
            val node1 = buildNodes (t,c)

            val node2 = buildNodes (e,c)
            
            val pre1 = getPreconditionConsideringNodeType node1         
            val pre2 = getPreconditionConsideringNodeType node2

            val pre = And(Implies(c, pre1), Implies(Not(c), pre2))

            val me = ref(TripleNode(pre, prog, post))
            
            val new = ref(Visited([me, node1, node2]))
            (* val _ = print("\nproved: " ^ green ^ nodeToString me ^ resetColor ^ "\n") *)
        in
            new
        end
      | While (c, d) => 
        let
            val i = getInvariant ()

            val impl1 = ref(OpenNode((Implication(Implies(And(i, Not(c)), post)))))
            
            val node = buildNodes(d, i)
            val pre = getPreconditionConsideringNodeType node
            val impl2 = ref(OpenNode(Implication(Implies(And(i, c), pre))))
            
            val me = ref(OpenNode(TripleNode(i, prog, post)))
            val tri = ref (OpenNode(TripleNode (And(i, c), d, i)));


            val new = ref(Visited([me, impl1, impl2, tri]))
            val _ = print("\nproved: " ^ green ^ nodeToString me ^ resetColor ^ "\n")
        in
            new
        end
    | Sec (s1, s2) =>
        let
            val node1 = buildNodes(s2, post)
            val pre1 = getPreconditionConsideringNodeType node1
            
            val node2 = buildNodes(s1, pre1)
            val pre2 = getPreconditionConsideringNodeType node2

            val me = ref(OpenNode(TripleNode(pre2, prog, post)))
            val _ = print("\nproved: " ^ green ^ nodeToString me ^ resetColor ^ "\n")
            val new = ref(Visited([me, node1, node2]))
        in
            new
        end

fun analyzeSex nod =
    let 
        val OpenNode(TripleNode(prec, Sec(s1, s2), post)) = !nod
      
        val _ =  print("\nto solve this sec, we have to find the precondition for: \n" ^ 
         purple ^ "{" ^ orange ^ "???" ^ purple ^ "} " ^ progToString s2 ^ " {" ^ conditionToString post ^ "}\n" ^ resetColor)

        val _ = getConfirmationFromUser()

        val sec2 = buildNodes (s2, post);

        val wp = getPreconditionConsideringNodeType sec2 

        val _ = print("\nfound this precondition: " ^ conditionToString wp ^ "\n")

        val sec1 = ref(OpenNode(TripleNode(prec, s1, wp)))

        val me = ref (TripleNode(prec, Sec(s1, s2), post));
        val children = [me, sec1, sec2]
    in
        nod := Visited(children)
    end

