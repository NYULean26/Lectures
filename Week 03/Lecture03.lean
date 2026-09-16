import Mathlib

namespace Week03

universe u v

/-
**## Building things from the three axioms**
-/

/-
**### A. Function extensionality from `Quot.sound`**
-/

-- The constructor of quotients in Lean
#check Quot.mk
#check Quot.sound
#check Quot.lift

-- A definitional fact in Lean
example
    {α : Sort u} {r : α → α → Prop} {β : Sort v}
    (f : α → β) (h : ∀ (a b : α), r a b → f a = f b) (x : α) :
    Quot.lift f h (Quot.mk r x) = f x := by
  rfl

-- Put functions in the same quotient class when they agree at every input.
-- `Quot.sound` will identify the two classes; evaluating those equal classes
-- will then recover equality of the original functions.
theorem fun_ext
    {α β : Type u} {f g : α → β}
    (h : ∀ x, f x = g x) : f = g := by
  sorry

#print axioms fun_ext

/-
**### B. Diaconescu's theorem**

For an arbitrary proposition `P`, consider two types whose elements are
propositions carrying evidence that

* either `P` holds or the proposition is `True`, and
* either `P` holds or the proposition is `False`.

Use `Classical.choice` once on each type. Either one of the choices already
contains evidence for `P`, or their underlying propositions differ. But under
`P` the two defining predicates are equal, so the choice function must agree.
-/

theorem excluded_middle_from_axioms (P : Prop) : P ∨ ¬ P := by
  let S := {X : Prop // P ∨ X = True}
  let T := {X : Prop // P ∨ X = False}

  -- 0. We construct elements of S and T with Choice.
  let s : S := sorry
  let t : T := sorry

  -- 1. Either we find evidence for `P`, or the two choices differ.
  have different_or_P : P ∨ s.1 ≠ t.1 := by
    sorry

  -- 2. If we already have evidence for `P`, we are done.
  rcases different_or_P with hP | hDifferent
  · sorry
  ·
    -- 3. Otherwise it is enough to show that `P` forces the choices to agree.
    let fS := fun X ↦ P ∨ X = True
    let fT := fun X ↦ P ∨ X = False

    -- 4. Under `P`, fS and fT are equal.
    have f_equal : fT = fS := by
      sorry

    -- 5. Therefore the choice function receives equal input types and agrees.
    have choices_agree :
        ∀ (hS : Nonempty {X : Prop // fS X})
          (hT : Nonempty {X : Prop // fT X}),
          (Classical.choice hS).1 = (Classical.choice hT).1 := by
      sorry

    -- 6. This finishes the proof.
    sorry

#print axioms excluded_middle_from_axioms

/-
**### C. An implication from its contrapositive**

Now use the excluded-middle theorem we just proved.
-/

theorem reverse_implication_from_negations
    (A B : Prop) (h : ¬ B → ¬ A) : A → B := by
  sorry

#print axioms reverse_implication_from_negations

/-
**## Structures in Lean**
-/

structure NatPoint where
  x : ℕ
  y : ℕ

structure Point (T : Type*) where
  x : T
  y : T
  deriving Repr

def p := Point.mk 1 2

/-
**We use structures to store algebraic data**
-/

structure Semigroup' where
  carrier : Type*
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

end Week03
