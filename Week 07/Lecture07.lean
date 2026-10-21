import Mathlib

namespace Week07

-- Questions. Open this file independently of the Answers and Instructor copies.
-- Uncomment each #eval after filling in the definitions it uses.

/-
# Arithmetic expressions

Based on FPiL Chapter 4, especially 4.1–4.4:
https://lean-lang.org/functional_programming_in_lean/Monads/
and LoVe Chapter 7, Effectful Programming:
https://github.com/lean-forward/logical_verification_2026/blob/460f6be0846eefc3d9441e4e48d75753fcfe1709/lean/LoVe/LoVe07_EffectfulProgramming_Demo.lean

We use rational numbers and variables indexed by α in the arithmetic example.
-/

inductive Operation where
  | plus | minus | times | div
  deriving Repr

-- We define Operations with free variables indexed by α
inductive Expr (α : Type) where
  | const : ℚ → Expr α
  | var : α → Expr α
  | prim : Operation → Expr α → Expr α → Expr α
  deriving Repr

#check Expr.const

-- For example, we can use strings to name the variables.
def x : Expr String := Expr.var "x"
def y : Expr String := Expr.var "y"

-- This is the expression x + 2, written as a tree.
def e : Expr String := Expr.prim .plus x (Expr.const 2)

#eval e

/-
## Some notation

We have already seen how typeclasses let us use + and *.
Here they just build expressions. We fill these in for you.
-/

instance (α: Type) : Add (Expr α) where add a b := Expr.prim .plus a b
instance (α: Type) : Sub (Expr α) where sub a b := Expr.prim .minus a b
instance (α: Type) : Mul (Expr α) where mul a b := Expr.prim .times a b
instance (α: Type) : Div (Expr α) where div a b := Expr.prim .div a b
instance (α: Type) (n : ℕ) : OfNat (Expr α) n where ofNat := Expr.const n
instance (α: Type) : Neg (Expr α) where neg a := 0 - a

#eval x + 2
#eval (x + 2) * y

-- The notation builds the same tree as before.
example : x + 2 = e := by
  rfl

#eval Expr.const (1 / 3) + x


/-
## Evaluating expressions

To give meaning to a variable, we need to assign it a value.
An assignment is a function α → ℚ.
-/

def values (s : String) : ℚ :=
  match s with
  | "x" => 6
  | "y" => 2
  | _ => 0

#eval values "x"
#eval values "y"

-- First, evaluate an arithmetic operation on two numbers.
def Operation.eval (op : Operation) (a b : ℚ) : ℚ := by
  sorry

-- Now we can evaluate an expression recursively.
def Expr.eval (e : Expr α) (v : α → ℚ) : ℚ := by
  sorry

-- #eval (x + 2).eval values
-- #eval ((x + 2) / y).eval values

-- Here the variables are indexed by Fin 2.
def twoVariables : Expr (Fin 2) := Expr.var 0 + Expr.var 1
-- #eval twoVariables.eval ![3, 5] -- 8

-- The same expression can have different values with different assignments.
-- #eval (x + 2).eval (fun _ => 0)


/-
## What about division by zero?
-/

-- Lean defines division at zero too. Our evaluator should report an error instead.
#eval (1 : ℚ) / 0
-- #eval ((1 : Expr String) / 0).eval values



/-
### The Option type

Remember that the Option type in Lean is as follows
-/
inductive Option' (α:Type) where
  | some : α → Option' α
  | none

#check Option

-- We start with a straightforward implementation.
def Expr.safeEval (e : Expr α) (v : α → ℚ) : Option ℚ := sorry

-- #eval ((x + 2) / y).safeEval values -- some 4
-- #eval (Expr.const (1 / 3) + x).safeEval values -- some (19/3)

-- x = 6, so this denominator is zero.
def bad : Expr String := 14 / (x - 3 * y)

-- #eval bad.eval values -- 0
-- #eval bad.safeEval values -- none

-- #eval (bad + 1).safeEval values -- none
-- #eval ((0 : Expr String) * bad).safeEval values -- none


-- The evaluator returns the value of a constant.
example (q : ℚ) (v : α → ℚ) : (Expr.const q).safeEval v = some q := by
  sorry

-- We can check small examples by computation.
example : ((x + 2) / y).safeEval values = some 4 := by
  sorry

/-
# Looking up entries in a list

Let us look at the same problem somewhere else.
We want the first, third, fifth and seventh entries of a list.
An entry might be missing. How should we handle that?

This follows FPiL 4.1.1. The indices start at zero.
-/

def entries : List ℕ := [10, 20, 30, 40, 50, 60, 70]

/-
## Accept a default, or provide a proof

What should happen if an index is out of bounds?
One choice is to return a default value. The type is still ℕ,
but the answer might be garbage: it did not come from the list.
-/

#eval entries.getD 2 0 -- 30
#eval entries.getD 7 0 -- 0, our chosen default

-- From the answer alone, we cannot tell whether the lookup succeeded.
#eval ([0, 20] : List ℕ).getD 0 0 -- 0, an actual entry
#eval ([0, 20] : List ℕ).getD 7 0 -- 0, the default

/-
Another choice is to require a proof that the index is valid.
List.get takes a Fin xs.length: an index together with that proof.
Recall that ⟨i, h⟩ packages the index i and the proof h : i < xs.length.
-/

#check List.get
#eval entries.get ⟨2, by decide⟩ -- 30

-- The ordinary indexing notation also accepts an explicit bounds proof.
#eval entries[2]'(by decide) -- 30

-- Try this: the index 7 is not less than entries.length, so the proof fails.
-- #eval entries.get ⟨7, by decide⟩

/-
## A third choice: return an Option

Option records whether the lookup succeeds:
some a gives the entry; none reports an out-of-bounds index.
The type makes us account for the missing entry.
-/

#eval entries[0]? -- some 10
#eval entries[7]? -- none

def first (xs : List α) : Option α := xs[0]?

-- We will write this together in class, using explicit matches.
def firstThird (xs : List α) : Option (α × α) := sorry

-- #eval firstThird entries -- some (10, 30)
-- #eval firstThird ([] : List ℕ) -- none
-- #eval firstThird [10, 20] -- none


/-
## The problem we are trying to solve

Compare this with safeEval. Each match does the same thing:
if we have none, return none; if we have some a, continue with a.
We want to write that part just once.
-/

def andThen (result : Option α) (next : α → Option β) : Option β := by
  sorry

-- #eval andThen (some 3) (fun n => some (n + 1)) -- some 4
-- #eval andThen (none : Option ℕ) (fun n => some (n + 1)) -- none

-- The next computation is a function: it needs the value from the previous one.
def firstThirdAndThen (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun a =>
  andThen xs[2]? fun b =>
  some (a, b)

/-
## Some infix notation

As with + and *, we can give a function an infix notation.
The number is its precedence; infixl makes it left associative.
Here each fun extends to the end of its body.
-/

local infixl:55 " ~~> " => andThen

def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun a =>
  xs[2]? ~~> fun b =>
  some (a, b)

def firstThirdFifthSeventhInfix (xs : List α) : Option (α × α × α × α) := by
  sorry

-- #eval firstThirdFifthSeventhInfix entries -- some (10, 30, 50, 70)
-- #eval firstThirdFifthSeventhInfix [10, 20] -- none


/-
# Monads

Last week, typeclasses let us use the same notation for different types.
We can do the same with andThen and some.

For a type constructor m : Type → Type, the two operations are

  pure : α → m α
  bind : m α → (α → m β) → m β

Lean supplies these through the Monad typeclass.
For Option, pure is some and bind is our andThen.
The notation for bind is >>=.
-/

#check Monad
/-
Let us give our own Option' the same operations.
pure puts a value into some. Fill in bind with the same two cases as andThen.
-/

instance : Monad Option' where
  pure := Option'.some
  bind := sorry

#synth Monad Option'

-- First, the list example again, using Lean's existing operations.
def firstThirdFifthSeventhBind (xs : List α) : Option (α × α × α × α) :=
  xs[0]? >>= fun a =>
  xs[2]? >>= fun b =>
  xs[4]? >>= fun c =>
  xs[6]? >>= fun d =>
  pure (a, b, c, d)

#eval firstThirdFifthSeventhBind entries -- some (10, 30, 50, 70)
#eval firstThirdFifthSeventhBind [10, 20] -- none

/-
## do notation

Lean has syntax for these chains:

  do
    let a ← action
    rest a

means action >>= fun a => rest a.
-/

def firstThirdFifthSeventhDo (xs : List α) : Option (α × α × α × α) := by
  sorry

-- #eval firstThirdFifthSeventhDo entries -- some (10, 30, 50, 70)
-- #eval firstThirdFifthSeventhDo [10, 20] -- none

-- := names an ordinary value. The arrow sequences a computation.
def firstPlusOne (xs : List ℕ) : Option ℕ := do
  let attempt := xs[0]? -- attempt : Option ℕ
  let a ← attempt       -- a : ℕ
  pure (a + 1)

#eval firstPlusOne [10] -- some 11
#eval firstPlusOne [] -- none

-- Both definitions compute the same results.
example (xs : List α) :
    firstThirdFifthSeventhDo xs = firstThirdFifthSeventhBind xs := by
  sorry

/-
## Back to arithmetic expressions

The list and AST examples have the same failure handling.
Use do to remove the two matches on Option in safeEval.
Keep the match on the expression: that is the actual recursion.
-/

-- Separate applying an operation from traversing the expression.
def Operation.safeEval (op : Operation) (a b : ℚ) : Option ℚ := by
  sorry

def Expr.safeEvalDo (e : Expr α) (v : α → ℚ) : Option ℚ := by
  sorry

-- #eval ((x + 2) / y).safeEvalDo values -- some 4
-- #eval (Expr.const (1 / 3) + x).safeEvalDo values -- some (19/3)
-- #eval bad.safeEvalDo values -- none
-- #eval (bad + 1).safeEvalDo values -- none
-- #eval ((0 : Expr String) * bad).safeEvalDo values -- none

-- The refactor agrees with the original evaluator for every expression.
theorem Expr.safeEvalDo_eq (e : Expr α) (v : α → ℚ) :
    e.safeEvalDo v = e.safeEval v := by
  sorry

/-
## The three laws of monads

The literature considers monads that satisfy the three laws:

**Left identity**
  pure a >>= f = f a

**Right identity**
  result >>= pure = result

**Associativity**
  (result >>= f) >>= g = result >>= (fun a => f a >>= g)

We record these three laws in our own class LawfulMonad'.
-/

class LawfulMonad' (m : Type → Type) [Monad m] : Prop where
  pure_bind {α β : Type} (a : α) (f : α → m β) :
    (pure a >>= f) = f a
  bind_pure {α : Type} (result : m α) :
    (result >>= pure) = result
  bind_assoc {α β γ : Type} (result : m α) (f : α → m β) (g : β → m γ) :
    ((result >>= f) >>= g) = (result >>= fun a => f a >>= g)

-- First prove the three laws directly for our own Option'.
theorem Option'.pure_bind (a : α) (f : α → Option' β) : (pure a >>= f) = f a := by
  sorry

theorem Option'.bind_pure (result : Option' α) : (result >>= pure) = result := by
  sorry

theorem Option'.bind_assoc (result : Option' α) (f : α → Option' β) (g : β → Option' γ) :
    ((result >>= f) >>= g) = (result >>= fun a => f a >>= g) := by
  sorry

/-
Now register the three proofs as a LawfulMonad' instance.
-/

instance : LawfulMonad' Option' where
  pure_bind := Option'.pure_bind
  bind_pure := Option'.bind_pure
  bind_assoc := Option'.bind_assoc

#synth LawfulMonad' Option'


/-
## Using the same program with different effects

Option tells us that something failed. Except can also tell us why.

  Except.ok a    : a successful result
  Except.error e : an error

We will use Lean's existing Monad instances for both.
As in FPiL 4.2, pass the list lookup as an argument.
-/

def lookupExcept (xs : List α) (i : ℕ) : Except String α :=
  match xs[i]? with
  | none => .error s!"No entry at index {i}; the list has length {xs.length}"
  | some a => .ok a

def firstThirdFifthSeventhM {α : Type} {m : Type → Type} [Monad m]
    (lookup : List α → ℕ → m α) (xs : List α) : m (α × α × α × α) := by
  sorry

-- #eval firstThirdFifthSeventhM (fun xs i => xs[i]?) entries
-- #eval firstThirdFifthSeventhM lookupExcept entries
-- #eval firstThirdFifthSeventhM lookupExcept [10, 20]
-- Except.error "No entry at index 2; the list has length 2"

/-
We can do the same with the AST (FPiL 4.3).
The operation tells us which effects are needed.
The evaluator visits the tree and sequences the operation results.
-/

def Operation.evalExcept (op : Operation) (a b : ℚ) : Except String ℚ :=
  match op with
  | .plus => pure (a + b)
  | .minus => pure (a - b)
  | .times => pure (a * b)
  | .div => if b = 0 then .error s!"Cannot divide {a} by zero" else pure (a / b)

def Expr.evalM [Monad m] (applyOp : Operation → ℚ → ℚ → m ℚ)
    (e : Expr α) (v : α → ℚ) : m ℚ := by
  sorry

-- #eval Expr.evalM Operation.safeEval ((x + 2) / y) values -- some 4
-- #eval Expr.evalM Operation.evalExcept ((x + 2) / y) values -- Except.ok 4
-- #eval Expr.evalM Operation.evalExcept bad values -- Except.error "Cannot divide 14 by zero"
-- #eval Expr.evalM Operation.evalExcept (bad + 1) values
-- #eval Expr.evalM Operation.evalExcept ((0 : Expr String) * bad) values

-- Id has no effects. The same traversal gives our ordinary evaluator.
-- #eval Expr.evalM (m := Id) (fun op a b => op.eval a b) ((x + 2) / y) values



/-
# Basic examples of Monads

We have used monads to handle failure. Let us compare that with a few
other examples. What changes is the effect that pure and bind keep track of.

Following FPiL 4.1–4.2 and LoVe 7.4–7.6.
-/

/-
## No effects: Id

Id α is just α. For this monad, pure returns its argument and bind
is ordinary function application. This lets us use an interface written
for monads with an ordinary value.
-/

#synth Monad Id

example (a : α) : (pure a : Id α) = a := by
  rfl

example (a : α) (f : α → Id β) : (a >>= f) = f a := by
  rfl

instance : LawfulMonad' Id where
  pure_bind _ _ := rfl
  bind_pure _ := rfl
  bind_assoc _ _ _ := rfl

#synth LawfulMonad' Id

-- Here is a small program that we can run in different monads.
def addOne [Monad m] (action : m ℕ) : m ℕ := do
  let n ← action
  pure (n + 1)

#eval addOne (m := Id) 4 -- 5

/-
## Failure: Option and Except

For Option, pure is some. Bind propagates none; otherwise it calls
the next computation with the value inside some.

For Except ε, pure is Except.ok. Bind propagates an error of type ε;
otherwise it calls the next computation with the value inside Except.ok.
The error type is fixed throughout a sequence of computations.
-/

#synth Monad Option
#synth Monad (Except String)

#eval addOne (some 4) -- some 5
#eval addOne none -- none
#eval addOne (Except.ok 4 : Except String ℕ) -- Except.ok 5
#eval addOne (Except.error "No number" : Except String ℕ)
-- Except.error "No number"

instance : LawfulMonad' (Except ε) where
  pure_bind _ _ := rfl
  bind_pure result := by cases result <;> rfl
  bind_assoc result _ _ := by cases result <;> rfl

#synth LawfulMonad' (Except String)

/-
## Mutable state: StateM

A program that uses a mutable variable can be represented by a function:

  StateM σ α = σ → (α × σ)

It takes the initial state and returns a pair: the result first, then the
final state. Lean provides StateM and its Monad instance.

pure returns a value without changing the state.
Bind passes the first result to the next computation, and also passes along
the new state. The following equations show exactly what this means.
-/

#synth Monad (StateM ℕ)

example (a : α) (s : σ) : (pure a : StateM σ α) s = (a, s) := by
  rfl

example (action : StateM σ α) (next : α → StateM σ β) (s : σ) :
    (action >>= next) s = (let (a, s') := action s; next a s') := by
  rfl

-- Reading returns the current state; writing replaces it.
#eval (get : StateM ℕ ℕ) 10 -- (10, 10)
#eval (set 20 : StateM ℕ Unit) 10 -- ((), 20)

-- Increase the counter by howMuch, but return its OLD value (FPiL 4.2.1).
def increment (howMuch : ℕ) : StateM ℕ ℕ := by
  sorry

-- #eval increment 2 10 -- (10, 12)

-- What value does each arrow bind? What is the state after each line?
def twoIncrements : StateM ℕ (ℕ × ℕ) := by
  sorry

-- #eval twoIncrements 10 -- ((10, 12), 15)
-- #eval twoIncrements 0 -- ((0, 2), 5)

-- The same addOne changes the returned value, while preserving the state effect.
-- #eval addOne (increment 2) 10 -- (11, 12)

instance : LawfulMonad' (StateM σ) where
  pure_bind _ _ := rfl
  bind_pure result := by
    funext s
    rfl
  bind_assoc _ _ _ := rfl

#synth LawfulMonad' (StateM ℕ)

end Week07
