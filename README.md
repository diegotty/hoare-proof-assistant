A command-line **interactive proof assistant for Hoare Logic**, written in Standard ML (SML). Parses Hoare triples, generates verification conditions, and interactively guides the user through the proof tree until the program is fully verified (or proven invalid).

----

### Features
* **non-linear proof navigation**: users can select unproven nodes by index, allowing for proof construction in any preferred order
* **proof status detection**: the system automatically detects proof completion and provides a final verdict on the initial triple's validity
* **interactive invariants**: explicitly prompts the user for loop invariants when evaluating `while` constructs
* **WP calculus**: utilizes Weakest Precondition Calculus to automatically derive missing preconditions (eg. for assignments and sequential compositions)
* **automatic implication checking**: simplifies the proof process by automatically solving implications using Fourier-Motzkin Elimination

---

### Supported Syntax
The tool supports a standard imperative grammar for expressions (`E`), conditions (`C`), and programs (`p,q`):

```
k ::= 0 | 1 | -1 | 2 | ... 
E ::= k | x | E + E | E - E | E * E
C ::= true | false | E < E | E <= E | E > E | E >= E | E = E | C & C | C | C | C => C | !C 
p, q ::= skip | p;q | if C then p else q | while C do p | while C invariant C do p | x := E
```

**current limitation**: the automated implication checker uses FME, which is restricted to linear constraints; while the parser supports multiplication (`E * E`), the prover cannot automatically solve implications involving non-linear terms (e.g., `x * y`).

---

### Usage
To verify a program, load the source into an SML REPL and pass the Hoare triple as a string to the `readTripleStr` function.

```SML
use "inferer.sml";

(* syntax: { precondition } program { postcondition } *)
readTripleStr "{ x = 5 } x := x + 1 { x = 6 }";
```
> (parser is whitespace-insensitive, `"{x=5}x:=x+1{x=6}"` would also be a valid triple)

#### Workflow:
* **parsing**: the tool reads the string and initializes the proof tree
* **node selection**: enter the index of the node you wish to prove
    * loop invariants: if prompted, provide loop invariants
* **resolution**: the tool applies Hoare rules and WP calculus until all leaves are closed or an invalidation is found
