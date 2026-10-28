import Mathlib

namespace Week08Validation

/- # A table of calculations -/

structure RawInput where
  x : String
  y : String
  deriving Repr

/- ## A. Execute a program -/

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
