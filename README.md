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

The parser is minimalist: it replaces traditional keywords like `then`, `else`, and `do` with parenthetical grouping. 
To avoid a `ParseError`, ensure your control structures follow these patterns:

*   **if statements:** require three sets of parentheses - one for the condition, one for the `true` branch, and one for the `false` branch
    *   **format:** `if (condition) (program_p) (program_q)`
    *   **example:** `if (x > 0) (y := 1) (y := 0)`

*   **while loops:** Requires two sets of parentheses—one for the loop condition and one for the loop body
    *   **format:** `while (condition) (loop_body)`
    *   **example:** `while (x < 10) (x := x + 1)`

*   **sequential composition:** use a semicolon `;` to separate multiple instructions

*   **boolean & arithmetic operators:**
    *   logic: `&` (AND), `|` (OR), and `!` (NOT)
    *   comparison: `=`, `<>` (not equal), `<`, `<=`, `>`, and `>=`
    *   math: `+`, `-`, and `*`
   
----

#### Workflow:
* **parsing**: the tool reads the string and initializes the proof tree
* **node selection**: enter the index of the node you wish to prove
    * loop invariants: if prompted, provide loop invariants
* **resolution**: the tool applies Hoare rules and WP calculus until all leaves are closed or an invalidation is found

----
#### Some examples & test cases

1) **simple program**

demonstrates the weakest precondition derivation for a single assignment

```SML
readTripleStr "{ x = 10 } x := x + 1 { x = 11 }";
```
*   **result**: valid
* the tool automatically calculates the precondition $x + 1 = 11$ and uses the implication checker to prove that $x = 10 \Rightarrow x + 1 = 11$

----
2) **loop invariants (interactive)**

```SML
readTripleStr "{ x = 5 } while (x > 0) (x := x - 1) { x = 0 }";
```

*   **correct invariant**: when prompted, enter `x >= 0` (or `x = 0 | x > 0`)
*   **incorrect invariant**: if you enter `x > 0`, the proof will fail - that's because the loop terminates when $x = 0$, which does not satisfy the invariant $x > 0$, making it impossible to prove the postcondition

---

3) **invalid implication**

if an implication is mathematically impossible, the Fourier-Motzkin Elimination (FME) engine will detect the contradiction and provide a counterexample

```SML
readTripleStr "{ x + y = 10 } if (x > 5) (y := 0) (y := 20) { y < 10 }";
```

*   **result**: invalid
* the system identifies that the derived implication is false and prints a counterexample
---

3) **large derivation tree**

combines sequential composition (`;`), assignment, and an if-statement to show non-linear proof navigation

```SML
readTripleStr "{ true } x := 5; if (x > 0) (y := 1) (y := 2) { y = 1 }";
```
*   **result**: valid
*   you can traverse the large proof tree with our index-based selection to prove the branches in any order you prefer

---

> this tool was developed collaboratively as the final project for the 'programming languages' course @ sapienza university of rome
