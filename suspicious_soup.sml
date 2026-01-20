(* In SML, i will need to do some operations on elements of a list.
the thing is:
at every step, i need to ask the user which element to use (via  CLI, they have to give me a  number in input to know what to do next).

how does that fit in with the functional style of SML? is that doable? *)

(* Helper function to safely get the nth element (0-based) *)
fun getElement ([], _) = NONE
  | getElement (x::xs, 0) = SOME x
  | getElement (x::xs, n) = getElement (xs, n - 1)

(* The main interactive loop *)
(* currentList: The list of items currently being worked on *)
fun interact (currentList : string list) =
    let
        (* 1. Display current state or instructions *)
        val _ = print "\n--- Current List ---\n"
        val _ = app (fn x => print (x ^ " ")) currentList
        val _ = print "\n\nEnter index to select (or 'q' to quit): "

        (* 2. Read input from the CLI *)
        val input = TextIO.inputLine TextIO.stdIn
    in
        case input of
             NONE => print "Stream closed.\n" (* Handle End-of-File *)
           | SOME line =>
                let
                    val cleanLine = String.substring (line, 0, size line - 1) (* Remove newline *)
                in
                    if cleanLine = "q" then
                        print "Goodbye!\n" (* Base case: Stop recursion *)
                    else
                        (* 3. Process Input *)
                        case Int.fromString cleanLine of
                             NONE => 
                                (print "Invalid number!\n"; 
                                 interact currentList) (* Recurse with same list *)
                           | SOME index =>
                                (* 4. Logic on the element *)
                                case getElement (currentList, index) of
                                     NONE => 
                                        (print "Index out of bounds!\n"; 
                                         interact currentList)
                                   | SOME item => 
                                        (print ("\nYou selected: " ^ item ^ "\n");
                                         (* 5. RECURSE: Pass the list (or a modified version) back *)
                                         interact currentList) 
                end
    end

(* Start the program *)
val _ = interact ["Apple", "Banana", "Cherry", "Date"]