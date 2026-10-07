/-
Adapted from UC Berkeley CS 294-268 (Spring 2026), Lecture 6.
https://github.com/ucb-lean-course-sp26/ucb-lean-course-sp26.github.io/blob/main/LeanSource/Demos/Lec6sol.lean

Copyright (c) 2025 UCB-CS-294-268
SPDX-License-Identifier: MIT
See LICENSE-week06-ecc in this directory.
-/

/-
In this file, we introduce the basics of error-correcting codes and formalize
several fundamental results in coding theory.

Topics covered:
  1. Basic definitions: alphabets, codewords, codes, Hamming distance
  2. Example codes: repetition code, parity code
  3. Error detection and correction capability
  4. Hamming distance as a metric; recovery from minimum distance
  5. Bounds on code size

This file can serve as a starting point for formalizing more advanced results
in coding theory. For an introduction to the subject, see:

Reference: "A First Course in Coding Theory" by Raymond Hill
Reference: "The Theory of Error-Correcting Codes" by MacWilliams and Sloane
-/


import Mathlib

namespace Week06

-- Uncomment each #eval once the definitions it uses have been filled in.

/-! ─────────────────────────────────────────────────────────────────────────
## Part 1: Basic Definitions
──────────────────────────────────────────────────────────────────────────── -/

/-!
We work over an **alphabet** `α` — a finite type representing the symbols we
can use. Common choices:

* `Bool` — binary alphabet `{0, 1}`
* `Fin q` — q-ary alphabet `{0, 1, …, q-1}`
* `ZMod p` — integers modulo a prime p (a field)

A **codeword** of length n is a function `Fin n → α`.
A **code** is a set (here a `Finset`) of codewords.

### Finite objects in Lean

A `Set α` describes membership by a predicate `α → Prop`; it need not be
finite. A `Finset α` is an explicitly finite set, stored internally as a list.
-/

variable {n : ℕ} {α : Type}

/-- A codeword of length n over alphabet α is just a function Fin n → α. -/
abbrev Codeword (n : ℕ) (α : Type) := Fin n → α

/-- A code of length n over α is a finite set of codewords. -/
abbrev Code (n : ℕ) (α : Type) := Finset (Codeword n α)

/-!
### Hamming Distance

The **Hamming distance** between two codewords is the number of positions
in which they differ. For example:

    u = 0 1 1 0 1
    v = 0 0 1 1 1
          ^   ^      ← 2 positions differ

So d(u, v) = 2.

Mathlib already provides `hammingDist` in `Mathlib.InformationTheory.Hamming`.
We give a more transparent definition here for pedagogical purposes.

#### Disagreement positions

The positions at which two codewords differ form a finite set:
    {i ∈ Fin n | u i ≠ v i}.
We will define Hamming distance by counting this set.
-/

variable [DecidableEq α]

namespace Codeword

def disagreements (u v : Codeword n α) : Finset (Fin n) := by
  sorry

/-!
**Designing simp infrastructure**

What should `simp` know about disagreements?
-/

@[simp] theorem mem_disagreements (u v : Codeword n α) (i : Fin n) :
    i ∈ disagreements u v ↔ u i ≠ v i := by
  sorry

@[simp] theorem disagreements_self (u : Codeword n α) :
    disagreements u u = ∅ := by
  sorry

@[simp] theorem disagreements_eq_empty (u v : Codeword n α) :
    disagreements u v = ∅ ↔ u = v := by
  sorry

-- The positions where u and v differ do not depend on their order.
theorem disagreements_comm (u v : Codeword n α) :
    disagreements u v = disagreements v u := by
  sorry

/-- Hamming distance: the number of positions where two codewords differ. -/
def hammingDist (u v : Codeword n α) : ℕ := by
  sorry

-- Let's evaluate on a small example to see Hamming distance in action.
-- #eval hammingDist (![1, 1, 1, 1, 0] : Codeword 5 (Fin 2))
--                   ![0, 1, 1, 0, 0]
-- Expected: 2 (positions 0 and 3 differ)

/-- Hamming weight: the number of nonzero positions (distance from all-zeros). -/
def hammingWeight [Zero α] (u : Codeword n α) : ℕ := by
  sorry

@[simp] theorem hammingDist_self (u : Codeword n α) :
    hammingDist u u = 0 := by
  sorry

@[simp] theorem hammingDist_eq_zero (u v : Codeword n α) :
    hammingDist u v = 0 ↔ u = v := by
  sorry

theorem hammingDist_comm (u v : Codeword n α) :
    hammingDist u v = hammingDist v u := by
  sorry

/-!
### The Triangle Inequality

Prove that `hammingDist` satisfies the triangle inequality.

**Hint:** If u i ≠ w i, then either u i ≠ v i or v i ≠ w i (or both).
Therefore {i | u i ≠ w i} ⊆ {i | u i ≠ v i} ∪ {i | v i ≠ w i}.
Use `Finset.card_le_card` and `Finset.card_union_le`.
-/

theorem disagreements_subset_union (u v w : Codeword n α) :
    disagreements u w ⊆ disagreements u v ∪ disagreements v w := by
  sorry

theorem hammingDist_triangle (u v w : Codeword n α) :
    hammingDist u w ≤ hammingDist u v + hammingDist v w := by
  sorry

/-!
### Hamming Distance as a Metric

We have basically shown that Hamming distance is a metric: it is symmetric,
it is zero exactly when the words are equal, and it satisfies the triangle
inequality. In other words, we can make codewords into a metric space.

In Lean, a `MetricSpace` has real-valued distances. We use the same Hamming
distance, viewed as a real number.
-/

local instance : MetricSpace (Codeword n α) := by
  sorry

-- The metric distance is the Hamming distance, viewed as a real number.
@[simp] theorem dist_eq_hammingDist (u v : Codeword n α) :
    dist u v = (hammingDist u v : ℝ) := by
  sorry

#check dist_self
#check dist_comm
#check dist_triangle
#check dist_eq_zero

end Codeword


/-!
### Minimum Distance

The **minimum distance** of a code C (with at least 2 codewords) is:

    d(C) = min { d(u, v) | u, v ∈ C, u ≠ v }

This is the most important parameter of a code for error-correction purposes.
-/

/-!
We use `WithTop ℕ`: natural numbers together with an extra value `⊤`,
larger than every natural number. If there are no distinct codewords,
the minimum distance is `⊤`.

In `#eval` output, finite values appear as `some n`, and `⊤` as `none`.
-/

namespace Code

def minimumDistance (C : Code n α) : WithTop ℕ := by
  sorry

theorem minimumDistance_le {C : Code n α} {u v : Codeword n α}
    (hu : u ∈ C) (hv : v ∈ C) (hne : u ≠ v) :
    minimumDistance C ≤ ↑(Codeword.hammingDist u v) := by
  sorry

end Code

open Code



/-! ─────────────────────────────────────────────────────────────────────────
## Part 2: Example Codes
──────────────────────────────────────────────────────────────────────────── -/

section ExampleCodes

/-!
### The Repetition Code

The simplest code: to send a single bit, repeat it n times.
For n = 3 (the triple repetition code):
    0 → 000
    1 → 111

This is a (3, 2, 3)-code: length 3, two codewords, minimum distance 3.
-/

/-- Repeat a symbol n times. -/
def repeatWord (n : ℕ) (a : α) : Codeword n α := by
  sorry

-- The binary repetition code of length n.
def repetitionCode (n : ℕ) : Code n Bool := by
  sorry

-- Check the size: the repetition code has exactly 2 codewords (for n ≥ 1).
example (n : ℕ) (hn : n ≥ 1) : (repetitionCode n).card = 2 := by
  sorry

-- The repetition code of length 3 has minimum distance 3.
-- #eval Codeword.hammingDist ((fun _ => false) : Codeword 3 Bool) (fun _ => true)
-- Expected: 3
-- #eval minimumDistance (repetitionCode 3) -- Expected: some 3

/-!
### The Parity Check Code

Add a parity bit to detect single errors. A binary word x₁ x₂ … xₙ is in
the parity code iff it has an even number of 1s, i.e.,
x₁ + x₂ + … + xₙ ≡ 0 (mod 2).

We now use the field `ZMod 2` instead of `Bool`.
-/

abbrev F₂ := ZMod 2

-- The binary parity code of length n: all words with even Hamming weight.
def parityCode (n : ℕ) : Finset (Codeword n F₂) :=
  by
  sorry

@[simp] theorem mem_parityCode (x : Codeword n F₂) :
    x ∈ parityCode n ↔ ∑ i, x i = 0 := by
  sorry

-- The parity code of length 7 is a [7, 6, 2]-code (detects single errors).
-- It has 2^6 = 64 codewords (all 7-bit words with even weight).
-- #eval (parityCode 7).card  -- Expected: 64
-- #eval minimumDistance (parityCode 7) -- Expected: some 2

/-!
### The [7, 4, 3] Hamming Code

A binary word x = (x₁ … x₇) is a Hamming codeword iff Hx = 0 (mod 2),
where H is the 3×7 parity-check matrix whose columns are all nonzero
binary 3-vectors. Using column order 1..7 (in binary: 001,010,011,100,101,110,111):

    H = [ 0 0 0 1 1 1 1 ]
        [ 0 1 1 0 0 1 1 ]
        [ 1 0 1 0 1 0 1 ]

As with the parity code, we work over `ZMod 2`. Here the condition Hx = 0
is a system of three linear equations, rather than a single parity equation.
-/

def H : Matrix (Fin 3) (Fin 7) F₂ := by
  sorry

/-!
### Linear Codes

The solutions of φ x = 0 form a linear code when φ is a linear map.

Over a finite ring, we can enumerate these solutions as a finite set.
-/

def codeOfParityCheck {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {n m : ℕ} (φ : Codeword n R →ₗ[R] Codeword m R) :
    Finset (Codeword n R) := by
  sorry

def codeOfMatrix {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {n m : ℕ} (H : Matrix (Fin m) (Fin n) R) : Finset (Codeword n R) := by
  sorry

@[simp] theorem mem_codeOfParityCheck {R : Type} [CommRing R] [Fintype R]
    [DecidableEq R] {n m : ℕ}
    (φ : Codeword n R →ₗ[R] Codeword m R) (x : Codeword n R) :
    x ∈ codeOfParityCheck φ ↔ φ x = 0 := by
  sorry

def hammingCode74 : Code 7 F₂ := by
  sorry

@[simp] theorem mem_hammingCode74 (x : Codeword 7 F₂) :
    x ∈ hammingCode74 ↔ H.mulVec x = 0 := by
  sorry

-- The [7,4,3] code has 16 = 2^4 codewords.
-- #eval hammingCode74.card -- Expected: 16
-- #eval minimumDistance hammingCode74 -- Expected: some 3

-- Verify a known Hamming codeword: x = [1,1,0,1,0,0,1].
-- #eval decide (![1, 1, 0, 1, 0, 0, 1] ∈ hammingCode74) -- Expected: true

/-!
### Minimum Distance and Weight

For a linear code, we only need to compare codewords with zero:
the distance between x and y is the weight of x - y, and x - y
is again a codeword.

Therefore the minimum distance is the minimum weight of a nonzero codeword.
If zero is the only codeword, both minima are `⊤`.
-/

/-- The smallest weight of a nonzero codeword; ⊤ if there are none. -/
def minimumWeight [Zero α] (C : Code n α) : WithTop ℕ := by
  sorry

theorem Codeword.hammingDist_eq_weight_sub {R : Type} [Ring R] [DecidableEq R]
    (x y : Codeword n R) :
    Codeword.hammingDist x y = Codeword.hammingWeight (x - y) := by
  sorry

theorem minimumDistance_eq_minimumWeight {R : Type} [CommRing R] [Fintype R]
    [DecidableEq R] {m : ℕ}
    (φ : Codeword n R →ₗ[R] Codeword m R) :
    minimumDistance (codeOfParityCheck φ) =
      minimumWeight (codeOfParityCheck φ) := by
  sorry


/-!
For the Hamming code, the smallest nonzero weight is 3:
* A word of weight 1 selects one column of H, and no column is zero.
* A word of weight 2 selects two distinct columns. Their sum cannot be zero,
  since the columns are distinct and we are working over ZMod 2.
* The first three columns sum to zero, giving the word 1110000 of weight 3.
-/

-- It is enough to check the weights of the nonzero codewords.
-- #eval minimumWeight hammingCode74 -- Expected: some 3

theorem hammingCode74_minDist : minimumDistance hammingCode74 = 3 := by
  sorry


end ExampleCodes

/-! ─────────────────────────────────────────────────────────────────────────
## Part 3: Error Detection and Correction
──────────────────────────────────────────────────────────────────────────── -/

/-!
### Hamming Balls

The Hamming ball of radius r centered at c consists of all words within
Hamming distance r from c. These are the words that could have been received
if c was sent and at most r errors occurred.
-/

/-- The Hamming ball of radius r centered at u: all words within distance r. -/
def hammingBall [Fintype α] (u : Codeword n α) (r : ℕ) : Finset (Codeword n α) := by
  sorry

-- Check: how many binary words are within distance 1 from 000?
-- #eval (hammingBall (n := 3) (α := Bool) (fun _ => false) 1).card
-- Expected: 4  (000, 001, 010, 100)

@[simp] theorem mem_hammingBall [Fintype α] (u v : Codeword n α) (t : ℕ) :
    v ∈ hammingBall u t ↔ Codeword.hammingDist u v ≤ t := by
  sorry

/-!
### t-Error Correction via Ball Packing

**Key Lemma:** If a code C has minimum distance d ≥ 2t+1, then the Hamming
balls of radius t around distinct codewords are pairwise disjoint.

**Proof:** Suppose some word w ∈ B(u, t) ∩ B(v, t) for distinct u, v ∈ C.
By the triangle inequality:
    d(u, v) ≤ d(u, w) + d(w, v) ≤ t + t = 2t

But d(u, v) ≥ 2t + 1, contradiction.

**Consequence:** Nearest-neighbor decoding correctly identifies the sent
codeword from any received word with ≤ t errors.
-/

/-!
If 2t is smaller than the minimum distance, there can be at most one
codeword within distance t of a received word.
-/

theorem unique_nearby (C : Code n α) {t : ℕ}
    (ht : ↑(2 * t) < minimumDistance C) {u v r : Codeword n α}
    (hu : u ∈ C) (hv : v ∈ C)
    (hur : Codeword.hammingDist u r ≤ t) (hvr : Codeword.hammingDist v r ≤ t) : u = v := by
  sorry

/-!
### Error Correction Capability

**Theorem:** A code with minimum distance d can correct up to ⌊(d-1)/2⌋ errors.
Equivalently, if d ≥ 2t+1, the code is t-error-correcting: every received word
within distance t of a sent codeword has exactly one codeword in that radius,
so nearest-neighbor decoding succeeds.

Proof: if c was sent and r was received with d(c, r) ≤ t, then:
  • r is in the ball B(c, t)
  • any other codeword c' satisfies d(c', r) ≥ d(c, c') - d(c, r) ≥ d - t ≥ t+1 > t
    (using the reverse triangle inequality and d ≥ 2t+1)
so c is the unique closest codeword to r.
-/

/-!
A decoder returns a codeword for every received word. It corrects up to t
errors if it returns the original codeword whenever at most t symbols changed.
A code can correct t errors if such a decoder exists. Outside these balls,
the decoder may return any codeword.
-/

def IsDecoder {C : Code n α}
    (φ : Codeword n α → C) (t : ℕ) : Prop := by
  sorry

def DoesErrorRecovery (C : Code n α) (t : ℕ) : Prop := by
  sorry

-- Choose a codeword within distance t if one exists; otherwise choose any codeword.
-- The minimum-distance bound makes the nearby choice unique.
theorem exists_error_recovery (C : Code n α) (t : ℕ)
    {c : Codeword n α} (hC : c ∈ C)
    (ht : ↑(2 * t) < minimumDistance C) : DoesErrorRecovery C t := by
  sorry

theorem repetition_three_recovers : DoesErrorRecovery (repetitionCode 3) 1 := by
  sorry

-- The [7,4,3] Hamming code corrects one error.
theorem hammingCode74_recovers : DoesErrorRecovery hammingCode74 1 := by
  sorry

/-!
### Erasure Correction

An **erasure** is a position whose value is completely lost in transmission
(the receiver knows *which* positions were erased, but not what they were).
This is strictly easier than an error, where the receiver doesn't know which
positions are wrong.

**Key result:** A code with minimum distance d can correct up to d-1 erasures.

**Proof:** Suppose codeword c was sent and positions E ⊆ [n] with |E| ≤ d-1
were erased. We claim c is the unique codeword consistent with the received
word on the unerased positions.

Suppose c' ≠ c is another codeword consistent with the received word.
Then c and c' agree on all unerased positions, so they can only differ on
the erased positions. Therefore d(c, c') ≤ |E| ≤ d-1 < d, contradicting
the minimum distance of the code.

We record the erased positions as a finite set E.
-/

/-!
A code corrects up to t erasures if, after deleting at most t known positions,
the remaining symbols determine the codeword uniquely.
-/

def DoesErasureRecovery (C : Code n α) (t : ℕ) : Prop := by
  sorry

theorem Codeword.hammingDist_le_erased (u v : Codeword n α) (E : Finset (Fin n))
    (hagree : ∀ i, i ∉ E → u i = v i) : Codeword.hammingDist u v ≤ E.card := by
  sorry

theorem erasure_recovery (C : Code n α) (t : ℕ)
    (ht : ↑t < minimumDistance C) : DoesErasureRecovery C t := by
  sorry

-- Two known erasures can be recovered, compared with one unknown error.
theorem hammingCode74_erasure_recovers : DoesErasureRecovery hammingCode74 2 := by
  sorry

/-! ─────────────────────────────────────────────────────────────────────────
## Part 4: How Large Can a Code Be?
──────────────────────────────────────────────────────────────────────────── -/

/-!
### The Hamming Bound

Suppose a binary code C corrects up to t errors. The Hamming balls of
radius t around its codewords are pairwise disjoint: a word in two such
balls would have two possible sent messages.

Each ball has the same number V(n,t) of words. All the balls lie in the
space of 2^n binary words, so

    |C| · V(n,t) ≤ 2^n.

To count a ball, choose the positions at which the word changes. Over
ZMod 2 there is exactly one other symbol at each chosen position. Thus

    V(n,t) = ∑ i = 0, …, min(t,n), Nat.choose n i.

We define V(n,t) as the cardinality of the ball around zero, and prove the
bound by counting disjoint balls.
-/

def ballVolume (n t : ℕ) : ℕ := by
  sorry

-- #eval ballVolume 7 1 -- Expected: 8

theorem hammingBall_card (u : Codeword n F₂) (t : ℕ) :
    (hammingBall u t).card = ballVolume n t := by
  sorry

theorem recovery_balls_disjoint [Fintype α] (C : Code n α) (t : ℕ)
    (hrec : DoesErrorRecovery C t) {u v : Codeword n α}
    (hu : u ∈ C) (hv : v ∈ C) (hne : u ≠ v) :
    Disjoint (hammingBall u t) (hammingBall v t) := by
  sorry

theorem hamming_bound (C : Code n F₂) (t : ℕ)
    (hrec : DoesErrorRecovery C t) :
    C.card * ballVolume n t ≤ 2 ^ n := by
  sorry

-- A one-error-correcting binary code of length 7 has at most 16 codewords.
theorem one_error_length_seven_bound (C : Code 7 F₂)
    (hrec : DoesErrorRecovery C 1) : C.card ≤ 16 := by
  sorry

/-!
### The Singleton Bound for Erasures

If a code corrects any t erasures, delete t fixed positions from every
codeword. Two codewords cannot give the same remaining word, since erasure
recovery would then be impossible.

There are only q^(n-t) words on the remaining positions. Therefore

    |C| ≤ q^(n-t),

where q is the size of the alphabet and t ≤ n.
-/

theorem erasure_size_bound {α : Type} [Fintype α] (C : Code n α) (t : ℕ)
    (ht : t ≤ n) (hrec : DoesErasureRecovery C t) :
    C.card ≤ (Fintype.card α) ^ (n - t) := by
  sorry

-- For the Hamming code, the erasure bound gives 32, while the Hamming bound gives 16.
example : hammingCode74.card ≤ 2 ^ (7 - 2) := by
  sorry


end Week06
