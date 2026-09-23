import Mathlib

/-
Week 4 live worksheet: inductive types

Adapted and condensed from the ETHZ Formalizing Math Week 4 files:
https://github.com/jaumededios/ETHZ_Formalizing_Math/tree/main/ETHZFormalizingMath/W04

Follow the slide-to-Lean switches in the lecture. Fill the `sorry` lines in class.
Mathlib supplies the `fun_induction` and `omega` tactics used in the final example.
-/

namespace Week04

/-! A. After the first four slides: build inductive values -/

-- A small version of the Weekday example in the ETHZ worksheet.
inductive Signal where
  | red | amber | green
  deriving Repr

#check Signal.red

-- Continue here after the List and Vec slides. Lists store an element type;
-- vectors also store a length in their type.
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)

-- Construct the sequence 2, 3 once as a list and once as a vector.
def twoList : List Nat := by
  sorry

def twoVec : Vec Nat 2 := by
  sorry

/-! B. After no confusion: what can constructor equalities tell us? -/

#check Signal.noConfusion
#check Nat.noConfusion

-- Distinct constructors cannot be equal.
example : Signal.red ≠ Signal.green := by
  sorry

-- A constructor preserves enough information to recover its argument.
example (m n : Nat) (h : Nat.succ m = Nat.succ n) : m = n := by
  sorry

/-! C. After the `match` slide: write the cases directly -/

-- One branch per constructor; this version is deliberately nonrecursive.
def Signal.code (s : Signal) : Nat :=
  match s with
  | .red => 0
  | .amber => 1
  | .green => 2

#eval Signal.code .green

-- Match on zero and successor, recursing on the predecessor.
def doubleMatch (n : Nat) : Nat := by
  sorry

/-! D. After `casesOn` and `rec`: look under the hood -/

#check Signal.casesOn
#check Nat.casesOn
#check Nat.rec

-- Same branches as Signal.code, supplied as arguments to casesOn.
def codeCases (s : Signal) : Nat :=
  Signal.casesOn s 0 1 2

-- Case analysis receives the predecessor, but no recursive result.
def predecessorCases (n : Nat) : Nat := by
  sorry

-- The successor branch of Nat.rec receives the result for the predecessor.
def doubleRec (n : Nat) : Nat := by
  sorry

/-! E. After the Induction slides: follow the recursive structure -/

-- Induction itself is Nat.recOn with a Prop-valued motive.
example (P : Nat → Prop) (h0 : P 0)
    (hs : (k : Nat) → P k → P (k + 1)) (n : Nat) : P n := by
  sorry

-- Natural-number induction connects the two definitions of doubling.
theorem doubleMatch_eq_doubleRec (n : Nat) :
    doubleMatch n = doubleRec n := by
  sorry

-- Adapted from the ETHZ list-induction worksheet.
namespace List

variable {α : Type}

def append (as bs : List α) : List α :=
  match as with
  | nil => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α) :
    append (cons a as) bs = cons a (append as bs) :=
  rfl

theorem append_nil (as : List α) : append as nil = as := by
  sorry

def length (as : List α) : Nat :=
  match as with
  | nil => 0
  | cons _ as => 1 + length as

theorem len_append (as bs : List α) :
    length (append as bs) = length as + length bs := by
  sorry

end List

/-! F. Functional induction: follow a function's recursive equations -/

-- This function recurses from n + 2 to n. Functional induction creates the
-- three defining cases and supplies a hypothesis for the recursive call.
def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half n + 1

theorem half_le (n : Nat) : half n ≤ n := by
  sorry

end Week04
