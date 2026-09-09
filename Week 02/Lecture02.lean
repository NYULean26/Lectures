import Mathlib

namespace Week02

-----------------------------------
-- Part 1. Tactics and Terms
-----------------------------------

-- See
-- https://github.com/madvorak/lean4-cheatsheet/blob/main/lean-tactics.pdf
-- for a tactic cheatsheet.

/-
**## A. Some examples of terms**
**### A.1 Implications**
-/

-- You can apply a theorem to the conclusion to reduce it to its hypotheses.

example (P Q : Prop) : P → (P → Q) → Q := by
  sorry

example (P Q : Prop) : P → (P → Q) → Q := by
  sorry

theorem implications_compose_tactic
    (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R := by
  sorry

theorem implications_compose_term
    (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R :=
  by
    sorry

/-
**### A.2 And**
-/

-- The `And` object has a constructor.

example (P : Prop) (hp : P) : P ∧ P := by
  sorry

-- The constructor can also be called explicitly as `And.intro`.

example (P : Prop) (hp : P) : P ∧ P := by
  sorry

-- Lean also accepts ⟨a₁, a₂, ...⟩ when the expected type determines
-- which constructors should be used.

example (P : Prop) (hp : P) : P ∧ P := by
  sorry

-- We can refer to the two components of an `And` proof using `.1` and `.2`.

example (P Q : Prop) : P ∧ Q → Q ∧ P :=
  by
    sorry

-- `rcases` ("recursive cases") takes a hypothesis apart by matching its
-- constructor. The pattern ⟨p, q⟩ names the two pieces stored in h.

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  sorry

/-
**### A.3 Or**
-/

-- `Or` has two cases. In the tactic world, we use `left` or `right`.

example (P Q R : Prop) : (P ∧ (P ∨ Q → R)) → R := by
  sorry

#check Or.inl
#check Or.inr

example (P Q R : Prop) : (P ∧ (P ∨ Q → R)) → R :=
  by
    sorry

-- To use `Or` as a hypothesis, we use Lean's pattern matching.

example (P Q : Prop) (hpq : P ∨ Q) : Q ∨ P :=
  by
    sorry

-- We can use `cases`.

example (P Q : Prop) (hpq : P ∨ Q) : Q ∨ P := by
  sorry

-- For an `Or` hypothesis, `rcases` creates one branch for each constructor.

example (P Q : Prop) (hpq : P ∨ Q) : Q ∨ P := by
  sorry

/-
**### A.4 First-order logic**
-/

theorem some_natural_number_is_seven_tactic :
    ∃ n : ℕ, n = 7 := by
  sorry

theorem some_natural_number_is_seven_term :
    ∃ n : ℕ, n = 7 :=
  by
    sorry

-- The smallest example of using an existential hypothesis: unpack its witness
-- and certificate, then use them to build the conclusion.

example (A : Type) (P : A → Prop) (h : ∃ x, P x) : ∃ x, P x := by
  sorry

/-
**## B. Some other tactics out there**
-/

/-
`refine` lets us write part of the proof term explicitly.
Each `?_` marks a piece that remains to be supplied.
-/

example (A : Type) (P Q : A → Prop)
    (h : ∃ x, P x ∧ Q x) :
    ∃ x, P x := by
  sorry

example (A : Type) (P Q : A → Prop) :
    (∃ x, P x ∧ Q x) → ∃ x, P x :=
  by
    sorry

-- We can use a `match` as well if the hypothesis is a named variable.

example (A : Type) (P Q : A → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, P x :=
  by
    sorry

-- Proofs by computation.

theorem zero_is_not_one_tactic : (0 : ℕ) ≠ 1 := by
  sorry

theorem zero_is_not_one_term : (0 : ℕ) ≠ 1 :=
  by
    sorry

-- Proofs by (smart!) computation.

def fib (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 1
  | k + 2 => fib k + fib (k + 1)

theorem fib_100_ne_fib_12 : fib 100 ≠ fib 12 := by
  sorry

/-
**## C. Continuity**
-/

def continuous_at (x : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε, ε > 0 → ∃ δ, δ > 0 ∧ (∀ y : ℝ, |x - y| < δ → |f x - f y| < ε)

example (x : ℝ) (f g : ℝ → ℝ)
    (hf : continuous_at x f)
    (hg : continuous_at (f x) g) :
    continuous_at x (g ∘ f) := by
  sorry

example (x : ℝ) (f g : ℝ → ℝ)
    (hf : continuous_at x f)
    (hg : continuous_at (f x) g) :
    continuous_at x (g ∘ f) :=
  by
    sorry

/-
**## D. Cantor diagonalization**
-/

-- Given any list of Boolean-valued functions, flip the nth function at n.
-- The resulting function cannot be anywhere in the list.

theorem cantor_diagonalization (family : ℕ → (ℕ → Bool)) :
    ∃ diagonal : ℕ → Bool, ∀ n, diagonal ≠ family n := by
  sorry

theorem cantor_diagonalization_term (family : ℕ → (ℕ → Bool)) :
    ∃ diagonal : ℕ → Bool, ∀ n, diagonal ≠ family n :=
  by
    sorry

end Week02
