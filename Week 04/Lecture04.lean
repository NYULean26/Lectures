import Mathlib

namespace Week04

/-! A. Inductive values -/

inductive Signal where
  | red | amber | green
  deriving Repr

#check Signal.red

inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)

def twoList : List Nat := by
  sorry

def twoVec : Vec Nat 2 := by
  sorry

/-! B. Constructor equalities -/

#check Signal.noConfusion
#check Nat.noConfusion

example : Signal.red ≠ Signal.green := by
  sorry

example (m n : Nat) (h : Nat.succ m = Nat.succ n) : m = n := by
  sorry

/-! C. Pattern matching -/

def Signal.code (s : Signal) : Nat :=
  match s with
  | .red => 0
  | .amber => 1
  | .green => 2

#eval Signal.code .green

def doubleMatch (n : Nat) : Nat := by
  sorry

/-! D. Case analysis and recursion -/

#check Signal.casesOn
#check Nat.casesOn
#check Nat.rec

def codeCases (s : Signal) : Nat :=
  Signal.casesOn s 0 1 2

def predecessorCases (n : Nat) : Nat := by
  sorry

def doubleRec (n : Nat) : Nat := by
  sorry

/-! E. Induction -/

example (P : Nat → Prop) (h0 : P 0)
    (hs : (k : Nat) → P k → P (k + 1)) (n : Nat) : P n := by
  sorry

theorem doubleMatch_eq_doubleRec (n : Nat) :
    doubleMatch n = doubleRec n := by
  sorry

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

/-! F. Functional induction -/

def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half n + 1

theorem half_le (n : Nat) : half n ≤ n := by
  sorry

end Week04
