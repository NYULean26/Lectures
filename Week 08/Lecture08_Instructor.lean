import Mathlib

namespace Week08Validation

/- # A table of calculations -/

-- Teaching route: slides 1–8, then A–E. Open option-prime-reference.lean for
-- one representative law proof; the other proofs remain available for questions.
-- F–I are optional. Use slides 10–12 beside F and slide 9 with G or H.

structure RawInput where
  x : String
  y : String
  deriving Repr

/- ## A. Execute a program -/

-- Instructor: Start with the read checkpoint, before defining Validate.
-- Run it, change a prompt, and run it again. Ask for the types of readRow and raw.
-- IO.println returns an action; #eval or main executes it. Contrast let with ←.
-- The read checkpoint runs with all seven exercise sorries still present.

/- FPiL 4.5, The IO Monad
https://lean-lang.org/functional_programming_in_lean/Monads/The-IO-Monad/
An IO α describes an action whose successful result has type α. In readRow,
getLine has type IO String, while x and y are Strings inside the continuation.
IO also supports runtime errors; our explicit input validation is a separate layer.
For the first demonstration, `lake env lean --run <class-file> read` executes main.
Unused exercise holes are harmless here; reaching a computational sorry would fail.
-/

#check IO.println
#eval IO.println "Formula: (x + 2) / y"

def readRow : IO RawInput := do
  let stdin ← IO.getStdin
  IO.println "x?"
  let x ← stdin.getLine
  IO.println "y?"
  let y ← stdin.getLine
  pure { x, y }

-- Run the read checkpoint in a terminal; main is at the bottom.
def preview : IO Unit := do
  let raw ← readRow
  IO.println s!"x = {raw.x.trimAscii}, y = {raw.y.trimAscii}"

/- ## B. Check one field -/

-- Instructor: The input is a table of integer assignments to x and y.
-- The expression is fixed in Lean. Parsing expressions is outside this worksheet.
-- A field check returns a typed value or messages. Mapping changes only the value.
-- Use B1–B2 as the theory warm-up after IO: map, its notation, and identity.
-- B2 checks one law; it does not construct LawfulFunctor.
-- Validate follows FPiL's name; our version fixes errors to List String.
-- WithError would not distinguish accumulation from ordinary Except behavior.

/- FPiL 5.3.1, All Applicatives are Functors (frames 3 and 5)
https://lean-lang.org/functional_programming_in_lean/Functors___-Applicative-Functors___-and-Monads/The-Applicative-Contract/
Map changes the successful result without adding another check. Here the integer
parser already decides success; adding 2 computes the numerator without a new check.
Then map Input.mk row over x: the result is Validate (Int → Input), a checked
function waiting for y. This gives the application operation in C a concrete use.
In B2, split on Validate's constructors. Identity leaves both the value and the
messages unchanged. Composition is the next law to mention verbally.
-/

-- Reminder: explain BEq before deriving it. `a == b` returns Bool; `a = b` is a Prop.
-- `deriving BEq` generates comparisons of constructors and fields.
-- The #guard examples below use these Boolean comparisons.
structure Input where
  row : Nat
  x : Int
  y : Int
  deriving Repr, BEq

inductive Validate (α : Type) where
  | ok : α → Validate α
  | errors : List String → Validate α
  deriving Repr, BEq

def checkInteger (fieldName text : String) : Validate Int :=
  match text.trimAscii.toString.toInt? with
  | some n => .ok n
  | none => .errors [s!"{fieldName}: expected an integer"]

#eval checkInteger "x" " 6 "
#eval checkInteger "y" "two"

-- B1. Transform a successful value, preserving any errors.
def Validate.map (f : α → β) : Validate α → Validate β
  | .ok a => .ok (f a)
  | .errors es => .errors es

instance : Functor Validate where
  map := Validate.map

-- `f <$> a` means Functor.map f a.
#eval Int.add 2 <$> checkInteger "x" "6"
#eval Int.add 2 <$> checkInteger "x" "bad"
#check Input.mk 1 <$> checkInteger "x" "6"

-- B2. Prove the identity law for this map.
theorem validate_map_id (value : Validate α) : id <$> value = value := by
  cases value <;> rfl

/- ## C. Report both field errors -/

-- Instructor: Ask what Except would return when both field strings are invalid.
-- We want both messages. The four cases in apply make that behavior explicit.
-- Show pure and seq before <*>; the thunk permits short-circuiting, but here we
-- force it to collect errors. C2 builds Input from independently checkable fields.
-- An accumulating Applicative cannot have a compatible Monad: if the first action
-- fails, bind has no value with which to choose its continuation. This is about
-- compatibility with this application operation, not the datatype alone.
-- Use the standard LawfulApplicative slide; do not introduce another class.

/- FPiL 5.2.1, A Non-Monadic Applicative (frames 4–5)
https://lean-lang.org/functional_programming_in_lean/Functors___-Applicative-Functors___-and-Monads/Applicative-Functors/
The book validates several independent fields and accumulates their failures.
Our two-field row isolates that same choice. Input.mk row is curried: after
mapping over x, the successful result is a function waiting for y.
The expression `seq f arg := Validate.apply f (arg ())` deliberately forces
the delayed check even when f contains errors. Trace the two-error case first.
-/

-- C1. Apply the function on success; collect errors from both arguments, left first.
def Validate.apply (f : Validate (α → β)) (arg : Validate α) : Validate β :=
  match f, arg with
  | .ok g, .ok a => .ok (g a)
  | .errors es, .ok _ => .errors es
  | .ok _, .errors es => .errors es
  | .errors es, .errors fs => .errors (es ++ fs)

-- seq : f (α → β) → (Unit → f α) → f β
instance : Applicative Validate where
  pure := Validate.ok
  map := Validate.map
  seq f arg := Validate.apply f (arg ())

-- `f <*> arg` means Seq.seq f (fun () => arg).
#eval Int.add <$> checkInteger "x" "bad" <*> checkInteger "y" "bad"

-- C2. Build an Input using <$> and <*>. Include the row number in field labels.
def checkRow (row : Nat) (raw : RawInput) : Validate Input :=
  Input.mk row <$> checkInteger s!"row {row}, x" raw.x
               <*> checkInteger s!"row {row}, y" raw.y

#guard checkRow 1 ⟨"6", "2"⟩ == .ok ⟨1, 6, 2⟩
#guard checkRow 2 ⟨"bad", "?"⟩ == .errors
  ["row 2, x: expected an integer", "row 2, y: expected an integer"]

/- ## D. Check every row -/

-- Instructor: Compare List (Validate Input) with Validate (List Input).
-- LoVe's mmap uses bind; here List.cons <$> ... <*> ... needs only Applicative.
-- That weaker requirement lets the same traversal use our accumulating Validate.
-- In the Except comparison, checkRow still collects errors within the first bad
-- row; firstError then makes traversal stop before subsequent rows.
-- The check checkpoint now runs; B2, F1, and the optional proof may still be sorry.
-- Zero is a valid integer. Division by zero is a later evaluation error.

/- LoVe 7, mmap; FPiL 5.2 for the applicative interface
https://github.com/lean-forward/logical_verification_2026/blob/460f6be0846eefc3d9441e4e48d75753fcfe1709/lean/LoVe/LoVe07_EffectfulProgramming_Demo.lean
LoVe's mmap sequences one computation per list element using bind. Our traversal
can use <*> because the remaining checks do not depend on the current result.
List.cons combines the successful head with the successful tail; pure [] handles
the empty table. Choosing Validate or Except determines which errors are retained.
Ask why mapping alone yields a list of separate answers rather than one checked list.
-/

-- D1. Traverse the list using pure, <$>, and <*>; preserve result and error order.
def traverseA {f : Type → Type} [Applicative f]
    (check : α → f β) : List α → f (List β)
  | [] => pure []
  | a :: rest => List.cons <$> check a <*> traverseA check rest

def checkTable (rows : List RawInput) : Validate (List Input) :=
  traverseA (fun (raw, i) => checkRow (i + 1) raw) rows.zipIdx

def sample : List RawInput := [⟨"6", "2"⟩, ⟨"4", "1"⟩]
def invalid : List RawInput := [⟨"bad", "?"⟩, ⟨"4", "oops"⟩]

#eval invalid.zipIdx.map (fun (raw, i) => checkRow (i + 1) raw)
#eval checkTable invalid
#guard checkTable [] == .ok []
#guard checkTable [⟨"1", "0"⟩] == .ok [⟨1, 1, 0⟩]
#guard checkTable sample == .ok [⟨1, 6, 2⟩, ⟨2, 4, 1⟩]
#guard checkTable invalid == .errors
  ["row 1, x: expected an integer", "row 1, y: expected an integer",
   "row 2, y: expected an integer"]

-- The same traversal with a short-circuiting applicative.
def firstError : Validate α → Except String α
  | .ok a => .ok a
  | .errors es => .error (String.intercalate "; " es)

#eval traverseA (fun (raw, i) => firstError (checkRow (i + 1) raw)) invalid.zipIdx

/- ## E. Evaluate valid rows and retain the count -/

-- Instructor: Treat this section as a ten-minute recall and prediction exercise.
-- Read runBatch's result type: either an error or values, together with a count.
-- Its implementation and the evaluator are supplied. Save transformer order for G.
-- For earlyFailure, total evaluation returns (12, 3), while safe evaluation
-- reports an error after one attempted operation. Ask which nodes were skipped.
-- The same counted wrapper handles both policies; it counts arithmetic nodes.

/- FPiL 4.3, Example: Arithmetic in Monads
https://lean-lang.org/functional_programming_in_lean/Monads/Example___-Arithmetic-in-Monads/
The operation handler determines how evaluation proceeds after an arithmetic
failure. Our supplied evalM passes operand values through bind to that handler.
Validation has already checked the input syntax; a zero denominator remains
an evaluation error. Keep this distinction visible when running the report.
-/

-- Supplied from Week 07: arithmetic, safe evaluation, and the generic evaluator.
inductive Operation where
  | plus | minus | times | div
  deriving Repr

inductive Expr (α : Type) where
  | const : ℚ → Expr α
  | var : α → Expr α
  | prim : Operation → Expr α → Expr α → Expr α
  deriving Repr

instance : Add (Expr α) where add := Expr.prim .plus
instance : Sub (Expr α) where sub := Expr.prim .minus
instance : Mul (Expr α) where mul := Expr.prim .times
instance : Div (Expr α) where div := Expr.prim .div
instance (n : Nat) : OfNat (Expr α) n where ofNat := Expr.const n

def Operation.eval (op : Operation) (a b : ℚ) : ℚ :=
  match op with
  | .plus => a + b
  | .minus => a - b
  | .times => a * b
  | .div => a / b

def Operation.safeEval (op : Operation) (a b : ℚ) : Option ℚ :=
  match op with
  | .plus => pure (a + b)
  | .minus => pure (a - b)
  | .times => pure (a * b)
  | .div => if b = 0 then none else pure (a / b)

def Expr.evalM {m : Type → Type} [Monad m]
    (applyOp : Operation → ℚ → ℚ → m ℚ) (e : Expr α) (values : α → ℚ) : m ℚ :=
  match e with
  | .const q => pure q
  | .var x => pure (values x)
  | .prim op a b => do
    let a' ← a.evalM applyOp values
    let b' ← b.evalM applyOp values
    applyOp op a' b'

def Input.values (input : Input) : String → ℚ
  | "x" => input.x
  | "y" => input.y
  | _ => 0

def x : Expr String := .var "x"
def y : Expr String := .var "y"
def formula : Expr String := (x + 2) / y

-- Count attempted operations, including a failed division; reuse either handler.
-- Discussion: counted increments before calling its argument. Moving modify after
-- the call would count successful operations instead. In earlyFailure, the safe
-- handler stops at 1 / 0, before either x * y or the outer addition is attempted.
def counted {m : Type → Type} [Monad m] [MonadState Nat m]
    (applyOp : Operation → ℚ → ℚ → m ℚ) (op : Operation) (a b : ℚ) : m ℚ := do
  modify (· + 1)
  applyOp op a b

def safeOp {m : Type → Type} [Monad m] [MonadExcept String m]
    (row : Nat) (op : Operation) (a b : ℚ) : m ℚ :=
  match op.safeEval a b with
  | some q => pure q
  | none => throw s!"row {row}: division by zero"

def evalTable {m : Type → Type} [Monad m] [MonadState Nat m] [MonadExcept String m]
    (e : Expr String) (inputs : List Input) : m (List ℚ) :=
  traverseA (fun input => e.evalM (counted (safeOp input.row)) input.values) inputs

-- Supplied runner: retain the count even when evaluation fails.
def runBatch (e : Expr String) (inputs : List Input) : Except String (List ℚ) × Nat :=
  (evalTable (m := ExceptT String (StateM Nat)) e inputs).run.run 0

#guard runBatch formula [⟨1, 6, 2⟩, ⟨2, 4, 1⟩] == (.ok [4, 6], 4)
-- Predict the result and operation count for each policy before running it.
def earlyFailure : Expr String := (1 / 0) + (x * y)
def exampleInput : Input := ⟨1, 6, 2⟩

#eval Id.run ((earlyFailure.evalM
  (counted (fun op a b => pure (op.eval a b))) exampleInput.values : StateM Nat ℚ).run 0)
#eval runBatch earlyFailure [exampleInput]

/- ## F. Optional: print the report -/

-- Instructor: Optional after A–E. To demonstrate the report without F1, run the solution.
-- Validate the complete table first. Any input errors prevent evaluation.
-- Read the supplied report briefly; students only implement the printing loop.
-- The run checkpoint produces the completed application.
-- Place printLines and printLinesBind beside each other: the empty list becomes
-- pure (), printing becomes the first action, and the recursive call is inside
-- bind's continuation. This is the simplified expansion of list ForIn traversal,
-- with its unused Unit accumulator and pure bookkeeping removed.
-- readRows supplies while/if/let mut syntax. Trace cons and reverse for input order.
-- EOF ends input; an unmatched final x gets an empty y and a validation error.

/- FPiL 6.4, More do Features (frames 11–12)
https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/
A statement `if p then action` can omit an else branch because it is pure ().
For an effectful condition, bind its Bool before choosing the branch. In a loop,
the next iteration belongs to the body's continuation, so monadic failure can
prevent further iterations. printLinesBind makes this sequencing visible.
The current Lean reference covers while and ForIn; local mutable variables become
loop parameters, so readRows needs no explicit StateT in its type.
https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Syntax/
-/

-- Supplied: turn validation and evaluation results into report lines.
def report (rows : List RawInput) : List String :=
  match checkTable rows with
  | .errors es => es
  | .ok inputs =>
    let (result, count) := runBatch formula inputs
    let lines := match result with
      | .ok values => inputs.zipWith (fun input q => s!"row {input.row}: {q}") values
      | .error message => [message]
    lines ++ [s!"Operations: {count}"]

#guard report sample == ["row 1: 4", "row 2: 6", "Operations: 4"]
#guard report [⟨"6", "2"⟩, ⟨"4", "0"⟩, ⟨"8", "2"⟩] ==
  ["row 2: division by zero", "Operations: 4"]

-- F1 (optional). Print each line using for in IO.
def printLines (lines : List String) : IO Unit := do
  for line in lines do
    IO.println line

-- Equivalent recursive expansion of this loop.
def printLinesBind : List String → IO Unit
  | [] => pure ()
  | line :: rest => IO.println line >>= fun _ => printLinesBind rest

-- Supplied input: two lines per row (x, then y), ending at EOF.
def readRows : IO (List RawInput) := do
  let stdin ← IO.getStdin
  let mut rows := []
  while true do
    let x ← stdin.getLine
    if x.isEmpty then break
    let y ← stdin.getLine
    rows := { x, y } :: rows
  pure rows.reverse

/- ## G. Optional: where does the count go? -/

-- Instructor: Optional after E; completing F is not required.
-- Predict whether each error result can contain a count, then run the same input.
-- Row 2 fails after four operations; row 3 is never evaluated.

/- FPiL 6.2–6.3, especially Ordering Monad Transformers
https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/Ordering-Monad-Transformers/
The book runs one counter with state and exceptions in two different orders.
Except String (α × Nat) has no Nat in its error case, whereas Except String α × Nat
always contains a count. MonadState and MonadExcept describe the capabilities;
the runner chooses the stack. Losing a returned state does not undo external IO.
-/

/-
StateT Nat (Except String) α  ≃  Nat → Except String (α × Nat)
ExceptT String (StateM Nat) α ≃  Nat → (Except String α × Nat)
-/

def runDrop (e : Expr String) (inputs : List Input) : Except String (List ℚ × Nat) :=
  (evalTable (m := StateT Nat (Except String)) e inputs).run 0

-- Predict which result retains the count on failure.
#eval runDrop formula [⟨1, 6, 2⟩, ⟨2, 4, 0⟩, ⟨3, 8, 2⟩]
#eval runBatch formula [⟨1, 6, 2⟩, ⟨2, 4, 0⟩, ⟨3, 8, 2⟩]

/- ## H. Optional demonstration: an even integer -/

-- Instructor: Optional demonstration after A–E; completing F is not required.
-- Run the even checkpoint on 8, 7, and "hello"; no new exercise is needed.
-- Even is Mathlib's predicate; EvenInt pairs an Int with a proof of that predicate.
-- In the successful branch, h supplies the proof needed for ⟨n, h⟩.
-- OptionT IO α has representation IO (Option α). OptionT.mk and .run mark the
-- boundary between the two monad interfaces; IO actions lift automatically.
-- Bind handles none, so n is an Int in readEven and an EvenInt in acceptEven.
-- Ask students to expand one bind into an IO action with a match on Option.
-- A failed read/check skips the acceptance message, but does not undo earlier IO.

/- FPiL 6.2.1, Failure with OptionT; FPiL 5.2.1 for subtypes
https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/A-Monad-Construction-Kit/
OptionT takes a monad m and provides another monad, OptionT m. Its bind uses
m's bind to obtain an Option, then propagates none or calls the continuation.
The MonadLift instance lets the prompt and getLine run in OptionT IO.
In readEven, `if h : Even n` checks a decidable proposition and names its proof
in the successful branch. The subtype records that evidence in the result.
-/

-- An even integer carries a proof of evenness.
abbrev EvenInt := {n : Int // Even n}

def readInt? : OptionT IO Int := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  OptionT.mk (pure line.trimAscii.toString.toInt?)

def readEven : OptionT IO EvenInt := do
  IO.println "Enter an even integer:"
  let n ← readInt?
  if h : Even n then pure ⟨n, h⟩ else failure

def acceptEven : OptionT IO Unit := do
  let n ← readEven
  IO.println s!"Accepted {n.val}"

/- ## I. Optional: splitting a batch -/

-- Instructor: This is LoVe's mmap_append adapted to our applicative traversal
-- and Lean's standard LawfulMonad. Supply the lemma names if students need them.
-- The statement preserves sequencing and effects, including stopping on failure.
-- It does not claim that two batches can be run independently or in parallel.
-- Show pure_bind, bind_pure, and bind_assoc as the laws used by simplification.
-- The existing slides introduce the standard laws without assuming live coverage
-- of the law exercises in last week's prepared worksheet.

/- FPiL 4.2.3, The Monad Contract; LoVe 7, mmap_append
https://lean-lang.org/functional_programming_in_lean/Monads/The-Monad-Type-Class/
The base case removes pure steps. In the cons case, seq_eq_bind_map exposes
the sequencing hidden by <*>; the induction hypothesis splits the tail, and
bind_assoc aligns the continuations. No step swaps the order of effects.
The LawfulMonad assumption supplies these equations. Monad alone is enough to
run the traversal, but does not provide the proofs needed for this rewrite.
-/

-- I1. Prove that traversal respects append in a lawful monad.
-- Use list induction and the monad laws.
theorem traverseA_append {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : α → m β) (xs ys : List α) :
    traverseA f (xs ++ ys) = (do
      let left ← traverseA f xs
      let right ← traverseA f ys
      pure (left ++ right)) := by
  induction xs with
  | nil => simp [traverseA]
  | cons x xs ih =>
    simp [traverseA, ih, seq_eq_bind_map, bind_assoc]

end Week08Validation

def main (args : List String) : IO Unit := do
  match args with
  | ["read"] => Week08Validation.preview
  | ["check"] =>
    let rows ← Week08Validation.readRows
    IO.println (repr (Week08Validation.checkTable rows))
  | ["run"] =>
    let rows ← Week08Validation.readRows
    Week08Validation.printLines (Week08Validation.report rows)
  | ["even"] =>
    let result ← Week08Validation.acceptEven.run
    if result.isNone then IO.println "Invalid input"
  | _ => IO.println "Choose a checkpoint: read, check, run, or even."
