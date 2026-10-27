import Mathlib

namespace Homework03

/-!
# Homework 3: Stating results about error-correcting codes

The goal is to translate mathematics into precise Lean definitions and
statements, and then prove the statements. Replace `sorry` in definitions
with actual definitions; in theorem declarations, replace `(sorry : Prop)`
with the statement you want to make and `by sorry` with a complete Lean proof.
Proofs are required for every theorem, but the proofs will
not be graded.

Write all definitions and theorem statements yourself, without LLM assistance.
You may use LLMs ONLY for the proofs, after writing your definitions and
statements. We encourage you to:

1. First try to write the proofs by hand.
2. Write proofs with an LLM.
3. Talk with the LLM to optimize the proofs as much as possible: simplify
   the arguments, remove unnecessary steps, and understand each remaining step.

-/

abbrev Codeword (n : ℕ) (α : Type) := Fin n → α
abbrev Code (n : ℕ) (α : Type) := Finset (Codeword n α)

variable {n : ℕ} {α : Type} [DecidableEq α]

namespace Codeword

def disagreements (u v : Codeword n α) : Finset (Fin n) :=
  {i | u i ≠ v i}

def hammingDist (u v : Codeword n α) : ℕ :=
  (disagreements u v).card

def hammingWeight [Zero α] (u : Codeword n α) : ℕ :=
  hammingDist u 0

end Codeword

/-!
## Reference: definitions from Parts 1 and 2 (no exercises)

The minimum distance is `⊤` when there are no distinct codewords.
It takes values in `WithTop ℕ`, so comparisons may require a cast `↑d`.
The repetition code of length 3 and the Hamming code below both have
minimum distance 3. You may use these facts without proving them.
-/

def minimumDistance (C : Code n α) : WithTop ℕ :=
  (C.offDiag.image (fun pair => Codeword.hammingDist pair.1 pair.2)).min

def repeatWord (n : ℕ) (a : α) : Codeword n α := fun _ => a

def repetitionCode (n : ℕ) : Code n Bool :=
  {repeatWord n false, repeatWord n true}

abbrev F₂ := ZMod 2

def codeOfParityCheck {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {n m : ℕ} (φ : Codeword n R →ₗ[R] Codeword m R) : Code n R :=
  Finset.univ.filter (fun word => φ word = 0)

def H : Matrix (Fin 3) (Fin 7) F₂ :=
  !![0, 0, 0, 1, 1, 1, 1;
     0, 1, 1, 0, 0, 1, 1;
     1, 0, 1, 0, 1, 0, 1]

def hammingCode74 : Code 7 F₂ := codeOfParityCheck H.mulVecLin

/-!
## 1. Hamming balls and uniqueness

Define the Hamming ball of radius t around u, including its boundary.
Then state its membership criterion.

Use `#eval` to count the binary words within distance 1 of 000; there
should be four. Also check radius 0 and a radius larger than the word length.
-/

def hammingBall [Fintype α] (u : Codeword n α) (t : ℕ) :
    Finset (Codeword n α) := sorry

theorem mem_hammingBall : (sorry : Prop) := by sorry

/-!
State `unique_nearby`: if 2t is strictly below the minimum distance of C,
two codewords of C within distance t of the same received word must be equal.
-/

theorem unique_nearby : (sorry : Prop) := by sorry

/-!
## 2. What does it mean to correct errors?

A decoder is a function from received words to members of C. Here `C` as
a type means the subtype of words belonging to C.

Define `IsDecoder φ t` to mean that φ returns the original sent codeword
whenever at most t coordinates changed. The same φ must work for every
sent codeword and every allowed received word.

Define `DoesErrorRecovery C t` to mean that such a decoder exists.
-/

def IsDecoder {C : Code n α} (φ : Codeword n α → C) (t : ℕ) : Prop := sorry

def DoesErrorRecovery (C : Code n α) (t : ℕ) : Prop := sorry

/-!
State that a nonempty code admits t-error recovery if and only if 2t is
strictly below its minimum distance. Include the nonemptiness hypothesis: the decoder must
return a member of C even when no codeword is nearby.

State and prove that the length-three repetition code and the Hamming code
each correct one error by applying your general result.

-/

theorem exists_error_recovery : (sorry : Prop) := by sorry

-- Given `exists_error_recovery`, each proof below should take 2–3 lines using `decide +kernel`.
theorem repetition_three_recovers : (sorry : Prop) := by sorry

theorem hammingCode74_recovers : (sorry : Prop) := by sorry

/-!
## 3. Errors versus erasures

A different error recovery model is _erasure recovery_. In this model
one knows which data (positions) were lost. We define `DoesErasureRecovery C t`
to say that any two members of C agreeing outside a set of at most t erased
positions are equal.

State that a code recovers from t erasures if and only if t is strictly
below its minimum distance. Then state that the Hamming code recovers
from two erasures.

Written check: compare the distance thresholds for errors and erasures.
Check your definitions at t = 0. Can the empty code satisfy erasure recovery?
Can the empty binary code of positive length admit a total decoder into C?
-/

def DoesErasureRecovery (C : Code n α) (t : ℕ) : Prop := sorry

theorem erasure_recovery : (sorry : Prop) := by sorry

-- Given `erasure_recovery`, the proof below should take two lines using `decide +kernel`.
theorem hammingCode74_erasure_recovers : (sorry : Prop) := by sorry

/-!
## 4. Bounds on code size

Define `ballVolume n t` as the number of binary words within distance t of
the zero word. State the following results, with their hypotheses:

* All binary Hamming balls of a fixed radius have the same cardinality.
* If a binary code corrects t errors, its size times the ball volume is at
  most the total number of binary words of length n (the Hamming bound).
* If a code over a finite alphabet corrects t erasures and t ≤ n, its size
  is at most the number of words of length n - t (the Singleton bound).

Use the error-recovery and erasure-recovery predicates you defined above.
Specialize both bounds to the length-seven Hamming code: with one error
the first gives 16; with two erasures the second gives 32. State these two
inequalities as Lean examples. Explain why these upper bounds are compatible.

For `unique_nearby`, you may use the Hamming-distance triangle inequality
from class. Formalizing a `MetricSpace` instance is not required.
-/

def ballVolume (n t : ℕ) : ℕ := sorry

theorem ball_card_invariant : (sorry : Prop) := by sorry

theorem hamming_bound : (sorry : Prop) := by sorry

theorem erasure_size_bound : (sorry : Prop) := by sorry

end Homework03
