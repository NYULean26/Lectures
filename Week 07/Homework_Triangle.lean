import Mathlib

namespace TriangleGame

/-!
# Homework: The triangle game

The goal is to solve the triangle game using the Option and List monads.
For side length N, a hole is a triple ⟨a, b, c⟩ with coordinates in Fin N
and a + b + c = N - 1. We play on the board with N = 5 below.
The fifteen holes form a triangle:

                       ⟨4,0,0⟩
                  ⟨3,1,0⟩   ⟨3,0,1⟩
             ⟨2,2,0⟩   ⟨2,1,1⟩   ⟨2,0,2⟩
        ⟨1,3,0⟩   ⟨1,2,1⟩   ⟨1,1,2⟩   ⟨1,0,3⟩
   ⟨0,4,0⟩   ⟨0,3,1⟩   ⟨0,2,2⟩   ⟨0,1,3⟩   ⟨0,0,4⟩

Initially every hole except ⟨2,1,1⟩ contains a peg. The only allowed move
is to jump a peg over an adjacent peg into the opposite empty hole along
a straight line, removing the jumped peg.

For example, we can jump from ⟨0,3,1⟩ over ⟨1,2,1⟩ into ⟨2,1,1⟩.
This removes the pegs at ⟨0,3,1⟩ and ⟨1,2,1⟩ and adds one at ⟨2,1,1⟩.

The goal is to finish with exactly one peg, anywhere on the board.

We want all solutions. Two different sequences of moves count as different
solutions, even if they finish at the same hole.
-/

/-!
## 1. Points and board states

We fix N, the side length.
-/

variable (N : ℕ)

/-!
Define the following using abbrev:
* Point N: triples of coordinates, as maps from {0,1,2} to {0,...,N-1}.
* OnBoard N p: the coordinates of p sum to N - 1 in ℕ. Addition in Fin N
  is modulo N, so coerce each coordinate to ℕ before adding.
* Hole N: the subtype of points that are on the board.
* BoardState N n: the subtype of finite sets of holes with cardinality n.
  Use {x : α // P x} for a subtype.

Point is supplied. Lean adds N as a parameter to definitions that use it.
-/

abbrev Point := Fin 3 → Fin N
abbrev OnBoard (p : Point N) : Prop := sorry
abbrev Hole (N : ℕ) : Type := sorry
abbrev BoardState (N n : ℕ) : Type := sorry

-- Boards with an unspecified peg count, and with an unspecified side length.
abbrev Board (N : ℕ) := Σ n, BoardState N n
abbrev SomeBoard := Σ N, Board N

-- Uncomment the guards below to check your definitions.
-- #guard Fintype.card (Point 5) = 125
-- #guard OnBoard (N := 5) ![4, 0, 0] ∧ OnBoard (N := 5) ![2, 1, 1] ∧
--   ¬ OnBoard (N := 5) ![4, 4, 1]
-- #guard Fintype.card (Hole 5) = 15 ∧ Fintype.card (Hole 3) = 6
-- #guard Fintype.card (BoardState 5 2) = 105

-- Infer the side length and peg count from the arguments below.
variable {N n : ℕ}

-- Define this instance so that we can apply a hole as a function.
instance : CoeFun (Hole N) (fun _ => Fin 3 → Fin N) := sorry

-- Supplied: print a hole by its coordinates.
instance : Repr (Hole N) where
  reprPrec p prec := reprPrec (p 0, p 1, p 2) prec

-- Define the initial board with 14 pegs, leaving ⟨2,1,1⟩ empty.
-- Use Finset.univ.erase.
def initial : BoardState 5 14 := sorry

/-!
The following definitions work for every N. Two holes are adjacent when
the sum of their coordinate distances is 2.
A jump from p over q to r requires p and q to be adjacent, and q to be the
midpoint of p and r. For example, ⟨4,0,0⟩ → ⟨3,1,0⟩ → ⟨2,2,0⟩.

Nat.dist is absolute difference. We use natural-number coordinates below.
The adjacency condition excludes jumps that are too long.
-/

abbrev Adjacent (p q : Hole N) : Prop :=
  ∑ i : Fin 3, Nat.dist (p i) (q i) = 2

abbrev IsJump (p q r : Hole N) : Prop :=
  Adjacent p q ∧ ∀ i, (p i : ℕ) + (r i : ℕ) = 2 * (q i : ℕ)

-- Optional: prove that reversing a jump gives a jump.
theorem isJump_reverse (p q r : Hole N) : IsJump p q r ↔ IsJump r q p := by
  sorry

-- We will select jumps from these triples of holes.
structure Triple (N : ℕ) where
  start : Hole N
  jumped : Hole N
  finish : Hole N
  -- deriving DecidableEq, Repr, Fintype, Encodable
-- Uncomment deriving once the definitions above are complete.

-- Define Jump as the subtype of triples satisfying IsJump.
abbrev Jump (N : ℕ) : Type := sorry

-- Encodable.sortedUniv lists all elements of a finite type in the order
-- given by its encoding into ℕ. Use it to define allMoves.

def allMoves : List (Jump N) := sorry

-- #eval (allMoves (N := 5)).length -- 36

/-!
## 2. Playing a move

Define play by erasing the starting and jumped pegs, then adding the final
peg. Use do notation.

You will probably want to define erasePeg p b and addPeg p b first.
Erasing an empty hole fails; adding a peg to an occupied hole fails.
Otherwise return the updated board.

Hints: use Finset.erase and insert. Try grind for the cardinality proofs.
-/

def play (m : Triple N) (b : BoardState N (n + 2)) : Option (BoardState N (n + 1)) :=
  sorry

-- Iterate play to replay a sequence of moves, failing if a move is illegal.
-- With no moves left, return the current board.
-- Hint: match n, b, l with, considering n = 0, 1, or k + 2.
@[simp]
def replay {n : ℕ} (b : BoardState N n) (l : List (Jump N)) :
    Option (Finset (Hole N)) :=
  sorry

/-!
## 3. The List Monad

In the list monad, a computation returns a list of possible answers.
pure x is [x]. The expression xs >>= f applies f to each element of xs
and concatenates the resulting lists. Using `let x ← xs` explores each
choice in xs, and returning [] discards that branch.
-/

#guard ([1, 2] >>= fun x => [x, x + 10]) = [1, 11, 2, 12]

/-!
Define toList' as the natural way of mapping options into lists.
-/

def toList' {α : Type} (x : Option α) : List α :=
  sorry

-- #guard toList' (none : Option ℕ) = []
-- #guard toList' (some 7) = [7]

/-!
Lean already provides this function as Option.toList. Use the library
function from now on; you can write o.toList for an option o.
-/

-- Write a function that returns all possible next moves with their resulting boards.
def nextMoves (b : BoardState N (n + 2)) : List ((Jump N) × BoardState N (n + 1)) :=
  sorry

-- Test boards for the evaluation examples.
-- def top : Hole 5 := ⟨![4, 0, 0], by decide⟩
-- def small : BoardState 5 2 := ⟨{top, (⟨![3, 1, 0], by decide⟩ : Hole 5)}, by decide⟩

-- #eval nextMoves small -- should be one move, ending with a peg at ⟨2,2,0⟩

-- Q: What would change if the whole search returned none at the first illegal move?

-- Prove that nextMoves returns exactly the successful plays.
-- Hint: try simp or grind with the right definitions unfolded.
@[simp]
theorem mem_nextMoves {n : ℕ} (b : BoardState N (n + 2))
    (m : Jump N) (b' : BoardState N (n + 1)) :
    (m, b') ∈ nextMoves b ↔ play m b = some b' := by
  sorry

/-!
## 4. Searching for a solution

Define `solutions b` to return all winning sequences, stopping a sequence
as soon as one peg remains. Use the list monad.

Your solution should be very similar in shape to `replay`, but instead
you iterate using the List monad.

-/

def solutions {n : ℕ} (b : BoardState N n) : List (List (Jump N)) :=
  sorry

-- What does it mean for solutions to return []? And [[]]?

-- #eval solutions (⟨{top}, by decide⟩ : BoardState 5 1)
-- #eval solutions small
-- #eval solutions (⟨∅, by decide⟩ : BoardState 5 0)

-- #eval (solutions initial).length
-- #eval (solutions initial).head?

/-!
## 5. Checking the answers

State and prove `solutions_sound`: a sequence belongs to solutions b if and
only if it can be replayed successfully from b and leaves exactly one peg.

Hint: use fun_induction solutions b generalizing ms.
Try simp_all and grind.
-/

-- (x >>= f) = some y iff x = some a and f a = some y for some a.
-- Make this library lemma available to simp locally.
attribute [local simp] Option.bind_eq_some_iff

theorem solutions_sound {n : ℕ} (b : BoardState N n) (ms : List (Jump N)) :
    (sorry : Prop) := by
  sorry

/-!
**## 6. Where can the last peg be?**

Define `countEndingAt hole b` to count the solutions from b ending at hole.
Follow the recursion in solutions, but return a number: zero for an empty
board; for a one-peg board, one if its peg is at hole and zero otherwise.
For larger boards, add the counts from all successful moves. Use List.map
and List.sum. Different move sequences count separately.
-/

def countEndingAt (hole : Hole N) {n : ℕ} (b : BoardState N n) : ℕ :=
  sorry

-- #guard countEndingAt (⟨![2, 2, 0], by decide⟩ : Hole 5) small = 1
-- #guard countEndingAt top small = 0
-- Compute the count for each hole. Can the last peg be in any hole?
-- #eval (Encodable.sortedUniv (Hole 5)).map fun p => (p, countEndingAt p initial)

/-!
## 7. Reading a board (optional)

So far, a failed move returned none. For invalid input, we would also like
an error message. Except String α returns either .ok value or .error message.
Its do notation stops at the first error; pure succeeds and throw fails.

Read a board from a file and print its number of solutions. X is a peg;
O is an empty hole. For example, triangle-small.txt contains:

```text
   X
  O X
 O X X
X X O X
```

The number of rows gives N. Row k must contain k symbols. Spaces are ignored.
The supplied function below reads one symbol.
-/

namespace Input

def checkSymbol (c : Char) : Except String Bool :=
  match c with
  | 'X' => .ok true
  | 'O' => .ok false
  | _ => .error "Use X or O."

#guard checkSymbol 'X' == .ok true
#guard checkSymbol 'O' == .ok false
#guard checkSymbol '?' == .error "Use X or O."

/-!
List.mapM applies a monadic function to each entry of a list. Here the
monad is Except String: we get a list of answers or the first error.
Compare these examples with the choices in the List monad in Section 3.
-/

#guard (['X', 'O', 'X'].mapM checkSymbol) == .ok [true, false, true]
#guard (['X', '?', 'O'].mapM checkSymbol) == .error "Use X or O."

-- Remove whitespace using line.toList.filter (fun c => !c.isWhitespace).
-- Then use List.mapM and checkSymbol to read the row.
def checkRow (line : String) : Except String (List Bool) :=
  sorry

-- #guard checkRow " O X " == .ok [false, true]
-- #guard checkRow "X ?" == .error "Use X or O."

-- A triangle has rows of lengths 1, 2, ..., N.
abbrev Triangle (N : ℕ) :=
  {rows : List (List Bool) // rows.map List.length = List.range' 1 N}

/-!
Define checkTriangle using do notation. Read the rows with checkRow and
check that their lengths are 1, 2, ..., N. Return the triangle together with N,
or report s!"Expected rows of lengths 1 through {N}." if the shape is wrong.
Use text.trimAscii.toString.splitOn "\n" to split the input into lines.
-/

def checkTriangle (text : String) : Except String (Σ N, Triangle N) :=
  sorry

-- Predict the result before running this. Why is the last row not checked?
-- #eval checkTriangle "X\n? X\nO"

/-!
The next helper converts Triangle N into Board N.
The hole ⟨a,b,c⟩ is in row b + c, column c, counting from zero.
Here xs[i]! reads entry i. The shape carried by Triangle N ensures that
both indices are in range.
-/

def boardOfTriangle {N : ℕ} (triangle : Triangle N) : Board N :=
  let board : Finset (Hole N) := Finset.univ.filter fun p =>
    let row := triangle.val[(p 1 : ℕ) + (p 2 : ℕ)]!
    row[(p 2 : ℕ)]! = true
  ⟨board.card, ⟨board, rfl⟩⟩

end Input

/-!
An IO α is a computation that interacts with the outside world and returns
an α. In an IO do block, `let x ← action` runs action and names its result x.
IO.FS.readFile path reads the whole file and returns IO String.
IO.println message prints a line and returns IO Unit.
Define countFile using do notation. Read the file, then match on
Input.checkTriangle applied to its contents. If there is an error, print the message.
On success ⟨N, triangle⟩, use Input.boardOfTriangle to obtain ⟨n, b⟩.
Then print s!"Solutions: {(solutions b).length}".
-/

def countFile (path : String) : IO Unit :=
  sorry

/-!
Put triangle-small.txt beside this file, with text
```text
   X
  O X
 O X X
X X O X
```

in the course repository. After completing the definitions, run:

lake env lean --run Homework_Triangle.lean triangle-small.txt

It should print "Solutions: 3". Try replacing an X with ?, or removing a
symbol from a row. What does the program report?
-/

end TriangleGame

-- main receives the command-line arguments when Lean runs the file.
def main (args : List String) : IO Unit :=
  match args with
  | [path] => TriangleGame.countFile path
  | _ => IO.println "Usage: lake env lean --run Homework_Triangle.lean FILE"
