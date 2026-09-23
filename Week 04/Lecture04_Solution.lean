import Mathlib

namespace Week04

/-! A. Build inductive values -/

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

def twoList : List Nat :=
  List.cons 2 (List.cons 3 List.nil)

def twoVec : Vec Nat 2 :=
  Vec.cons 2 (Vec.cons 3 Vec.nil)

/-! B. Constructor equalities -/

#check Signal.noConfusion
#check Nat.noConfusion

example : Signal.red ≠ Signal.green := by
  intro h
  cases h

example (m n : Nat) (h : Nat.succ m = Nat.succ n) : m = n := by
  injection h

/-! C. Pattern matching -/

def Signal.code (s : Signal) : Nat :=
  match s with
  | .red => 0
  | .amber => 1
  | .green => 2

#eval Signal.code .green

def doubleMatch (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => doubleMatch k + 2

/-! D. Case analysis and recursion -/

#check Signal.casesOn
#check Nat.casesOn
#check Nat.rec

def codeCases (s : Signal) : Nat :=
  Signal.casesOn s 0 1 2

def predecessorCases (n : Nat) : Nat :=
  Nat.casesOn n 0 (fun k => k)

def doubleRec (n : Nat) : Nat :=
  Nat.rec 0 (fun _k result => result + 2) n

example : doubleMatch 3 = doubleRec 3 := rfl

/-! E. Induction -/

example (P : Nat → Prop) (h0 : P 0)
    (hs : (k : Nat) → P k → P (k + 1)) (n : Nat) : P n :=
  Nat.recOn n h0 hs

theorem doubleMatch_eq_doubleRec (n : Nat) :
    doubleMatch n = doubleRec n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [doubleMatch, doubleRec, ih]

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
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [cons_append, ih]

def length (as : List α) : Nat :=
  match as with
  | nil => 0
  | cons _ as => 1 + length as

theorem len_append (as bs : List α) :
    length (append as bs) = length as + length bs := by
  induction as with
  | nil => simp [append, length]
  | cons x xs ih =>
    simp only [cons_append, length, ih, Nat.add_assoc]

end List

/-! F. Functional induction -/

def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half n + 1

theorem half_le (n : Nat) : half n ≤ n := by
  fun_induction half
  · omega
  · omega
  · omega

end Week04
