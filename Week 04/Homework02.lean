import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic

section Induction

/-!
# Homework 2: Induction and trees

## 1. Prove the strong induction principle

The goal of this exercise is to prove the strong induction principle,
using the usual "weak" induction we saw in class.

To do so, state a stronger statement, prove it by ordinary induction,
and then use it. Do not use Lean's existing strong induction principles.
-/

theorem my_strong_induction
    (p : ℕ → Prop)
    (ind : ∀ (n : ℕ), (∀ m : ℕ, m < n → p m) → p n)
    (k : ℕ) : p k := by
  -- Replace the first `sorry` with your stronger statement, then prove it.
  have my_stronger_statement : (sorry : Prop) := by
    sorry
  -- Use what you proved to show p k.
  sorry

-- Now you can use this induction principle yourself!
-- Write `induction n using my_strong_induction` to do so.

/-!
## 2. Every natural number greater than 1 is divisible by a prime
-/

def divides (x n : ℕ) : Prop := ∃ k : ℕ, n = x * k

def isPrime (n : ℕ) : Prop :=
  n > 1 ∧ ∀ m : ℕ, divides m n → (m = 1) ∨ (m = n)

/-!
### Exercise 2.1

State and prove the following auxiliary lemmas.
They may have missing hypotheses as written.

* `divides_transitive`: if a divides b and b divides c, then a divides c.
* `divides_zero`: if zero divides n, then n is zero.
* `divides_le`: if b divides n, then b < n.

### Exercise 2.2

State that if n > 1 is not prime, there is a number m strictly between
1 and n that divides n.

Optional (1): Prove it. The proof is a bit tedious. The tactic `push Not`
after unfolding makes your life easier.

Optional (2): Use your favorite LLM to prove it, and manually try to
understand and optimize the proof as much as you can through conversations
with the LLM, line by line.

You may leave this lemma's proof as `sorry` and use it in Exercise 2.3.

### Exercise 2.3

Use your newly proved strong induction principle to prove the following.
-/

theorem prime_divides (n : ℕ) (hn : n > 1) :
    ∃ p, isPrime p ∧ divides p n := by
  sorry

/-!
## 3. Some things about trees

We define a rooted binary tree as follows.
-/

inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree

/-!
### Exercise 3.1: Definitions

Define `BinaryTree.leaf_count` as the number of leaves of a binary tree.

Define `BinaryTree.height` recursively: leaves have height one, and the
height of a node is 1 plus the maximum height of its two subtrees.

Define two trees to be isomorphic if they are equal up to recursively
switching the order of the branches.

### Exercise 3.2

Show that isomorphic trees have the same leaf count and height.

Optional: Your code above quite likely has a lot of copy-pasted code.
Can you refactor it to have as little boilerplate as possible?
Hint: You could define something like
`BinaryTree.leaf_count = BinaryTree.accumulate (fun a b ↦ a + b)`.
-/

end Induction
