import Mathlib

set_option linter.unusedTactic false

/- Metaprogramming III: SOS and proofs by reflection. November 18, 2026.
Open this file independently of the student and solution copies.
From Week 11, run bash setup_sos.sh once for Python setup.
-/

open Lean Lean.Meta Lean.Elab.Tactic

namespace Week11

-- (Slide 1: Proofs and computation)

/- ## 1. A proof we want to automate -/

/- Instructor: 0–10 minutes. Learning goal: identify the two facts that make
a proposed square a certificate of nonnegativity. Show the title, then begin in Lean.
The local Week 10 worksheet stops inside myIntervalCases_2 (4.2.1); later
exercises remain blank. Do not assume split_and or exactTerm was completed.
If that reflects the actual stopping point, briefly finish the two lines:
  let k := mkIdent (← a.fvarId!.getUserName)
  evalTactic (← `(tactic| my_interval_cases $k from $h))
The Name h was already converted with mkIdent in the edited file.
Keep this to three minutes; start a fresh Week 11 file for the main lesson.

Use 1.1 to ask for a proof of the inequality, then identify the square.
Show slide 2 after that proof. We can verify the answer by checking the certificate. For larger problems, finding the decomposition can be hard.
In 1.2, expose exactly what the next tactic must construct. ring proves an
algebraic identity; rfl only checks definitional equality. This connects to
last week's reduction discussion without reviewing the entire MetaM section.
-/

-- 1.1. Prove nonnegativity by identifying a square.
example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by
  have h := sq_nonneg (x-y)
  nlinarith only [h]

-- (Slide 2: Sums of squares)

theorem nonnegOfCertificate (p s : ℝ) (h : 0 ≤ s ∧ p = s) : 0 ≤ p := by
  rw [h.2]
  exact h.1

-- 1.2. Separate nonnegativity from the polynomial identity.
example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by
  apply nonnegOfCertificate _ ((x-y)^2)
  constructor
  · exact sq_nonneg (x-y)
  · ring

example (x y : ℝ) : (x-y)^2 = x^2 - 2*x*y + y^2 := by
  fail_if_success rfl
  ring

/- ## 2. Abstract the proof into a tactic -/

/- Instructor: 10–25 minutes. Learning goal: construct a tactic by abstracting
the proof we just wrote.
Write sos_step as a macro: the quotation directly expands into the refine step.
The def/elab alternative below recalls how to execute the same syntax in TacticM.
Use constructor: the custom split_and was not visibly completed in the worksheet.

Walk through exactTerm as a complete demonstration; leave its implementation
pre-filled in the student copy. Its input is term syntax; elabTerm turns it into
an Expr in the goal's context. some target guides
elaboration; inferType and isDefEq check the result; closeMainGoal submits it.
The first argument to closeMainGoal is only a name for diagnostics.
They already know monads; no monad hierarchy or recovery APIs are needed here.
Then fill square_using with the complete proof pattern from 1.2.
Show the x+y failure before the x-y success. The proposed square must match
the goal, even when it is nonnegative.
Sources: MPiL 7 and 9; LoVe 8's proof-first tactic examples.
-/

-- 2.1. Let's turn this into a "sos_step" tactic using a macro.
macro "sos_step " s:term : tactic =>
  `(tactic| refine nonnegOfCertificate _ $s ?_)

/- Alternative implementation, replacing the macro above:
def sosStep (s : TSyntax `term) : TacticM Unit := do
  evalTactic (← `(tactic| refine nonnegOfCertificate _ $s ?_))

elab "sos_step " s:term : tactic => sosStep s
-/

example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by
  sos_step ((x-y)^2)
  constructor
  · positivity
  · ring

/- Instructor: exactTerm is a completed walkthrough. The hasSorry check rejects
terms produced by error recovery when an inner proof fails, such as norm_num on
a negative weight. Keep this guard pre-filled. -/

-- 2.2. Elaborate proof syntax using the goal's context and expected type.
#check elabTerm

def exactTerm (stx : Syntax) : TacticM Unit := withMainContext do
  let target ← getMainTarget
  let proof ← elabTerm stx (some target)
  if proof.hasSorry then
    throwError "proof elaboration failed"
  let type ← inferType proof
  unless ← isDefEq type target do
    throwError "the term's type does not match the goal"
  closeMainGoal `exact_term proof

elab "exact_term " t:term : tactic => exactTerm t

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact_term ⟨hp, hq⟩

-- 2.3. Prove that the polynomial is nonnegative by showing it equals a square.
elab "square_using " q:term : tactic => do
  exactTerm (← `(nonnegOfCertificate _ ($q ^ 2) ⟨sq_nonneg $q, by ring1⟩))

/- Instructor: alternatively, use Lean's exact tactic. Replace the definition above with:

elab "square_using " q:term : tactic => do
  evalTactic (← `(tactic|
    exact nonnegOfCertificate _ ($q ^ 2) ⟨sq_nonneg $q, by ring1⟩))
-/

example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by
  fail_if_success square_using (x+y)
  square_using (x-y)

/- ## 3. A certificate with several squares -/

/- Instructor: 25–43 minutes. Learning goal: generalize a handwritten sum of
nonnegativity proofs to a theorem about any certificate. Write 3.1 first.
The list contains real values such as x-y; the induction abstracts the repeated
add_nonneg steps of the handwritten proof. The empty list is the base case.
We use ℝ throughout to keep the statements close to the examples; the same
argument generalizes to an ordered field.

The tactic constructs a list expression and applies this theorem. The simp step
expands map and sum on that concrete list, leaving the polynomial identity for ring.
In 3.3, write the weighted proof before stating weighted_squares_nonneg.
Its hypothesis requires every weight to be nonnegative. In the cons case,
extract the head's sign and the tail's hypothesis, then apply mul_nonneg and
add_nonneg. norm_num discharges the sign condition for each concrete certificate.
Use the unweighted induction as a model for the weighted proof students fill in.
The syntax wrappers are supplied macros: they only expand a fixed proof template.
The nonnegativity argument lives in ordinary theorems, outside TacticM.

The optional syntax-level implementations follow 3.4. They show how to generate
a proof term separately for each list. The main route applies a theorem whose
inductive proof has already been checked. Section 4 parses Python's
output into Lean term syntax and applies that theorem too.
-/

-- 3.1. A sum of squares is nonnegative.
example (x y z : ℝ) : 0 ≤ 2 * (x^2 + y^2 + z^2 - x*y - y*z - z*x) := by
  apply nonnegOfCertificate _ ((x-y)^2 + (y-z)^2 + (z-x)^2)
  constructor
  · exact add_nonneg
      (add_nonneg (sq_nonneg (x-y)) (sq_nonneg (y-z)))
      (sq_nonneg (z-x))
  · ring

-- 3.2. Prove nonnegativity for any list of squares.
theorem squares_nonneg (qs : List ℝ) : 0 ≤ (qs.map (fun q => q^2)).sum := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    simp
    exact add_nonneg (sq_nonneg q) ih

macro "squares_using " "[" qs:term,* "]" : tactic =>
  `(tactic| exact nonnegOfCertificate _ _ ⟨squares_nonneg [$qs,*], by
    simp <;> ring⟩)

example (x y z : ℝ) : 0 ≤ 2 * (x^2 + y^2 + z^2 - x*y - y*z - z*x) := by
  squares_using [x-y, y-z, z-x]

-- 3.3. A nonnegative weight preserves nonnegativity.
example (x : ℝ) : 0 ≤ 3*x^2 + 2*x + 3 := by
  apply nonnegOfCertificate _ (1*(x-1)^2 + 2*(x+1)^2)
  constructor
  · have h₁ : 0 ≤ 1*(x-1)^2 := mul_nonneg (by norm_num) (sq_nonneg (x-1))
    have h₂ : 0 ≤ 2*(x+1)^2 := mul_nonneg (by norm_num) (sq_nonneg (x+1))
    exact add_nonneg h₁ h₂
  · ring

-- 3.4. Nonnegative weights give a nonnegative sum.
theorem weighted_squares_nonneg (cert : List (ℝ × ℝ))
    (h : ∀ t ∈ cert, 0 ≤ t.1) :
    0 ≤ (cert.map (fun t => t.1 * t.2^2)).sum := by
  induction cert with
  | nil => simp
  | cons t ts ih =>
    have ht : 0 ≤ t.1 := h t (by simp)
    have hts : ∀ u ∈ ts, 0 ≤ u.1 := fun u hu => h u (by simp [hu])
    simpa only [List.map_cons, List.sum_cons] using
      add_nonneg (mul_nonneg ht (sq_nonneg t.2)) (ih hts)

macro "sos_using " cert:term : tactic =>
  `(tactic| exact nonnegOfCertificate _ _
    ⟨weighted_squares_nonneg $cert (by norm_num), by
     simp <;> ring⟩)

example (x : ℝ) : 0 ≤ 3*x^2 + 2*x + 3 := by
  sos_using [(1, x-1), (2, x+1)]

example (x y z : ℝ) : 0 ≤ 2 * (x^2 + y^2 + z^2 - x*y - y*z - z*x) := by
  sos_using [(1, x-y), (1, y-z), (1, z-x)]

/- Instructor: Optional proof-generating implementations.
The initial le_refl 0 lets each loop handle an empty list uniformly.
Compare their generated add_nonneg terms with the induction steps above.
These helpers only construct syntax, so they use MacroM. liftMacroM runs them
inside the tactic; exactTerm is the part that needs the goal.
-/

def squaresProofsTactic (qs : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  let mut proof ← `(le_refl (0 : ℝ))
  for q in qs do
    proof ← `(add_nonneg $proof (sq_nonneg $q))
  return proof

example (x y z : ℝ) : 0 ≤ 2 * (x^2 + y^2 + z^2 - x*y - y*z - z*x) := by
  run_tac do
    let x := mkIdent `x
    let y := mkIdent `y
    let z := mkIdent `z
    let proof ← Elab.liftMacroM do
      squaresProofsTactic #[← `($x-$y), ← `($y-$z), ← `($z-$x)]
    exactTerm (← `(nonnegOfCertificate _ _ ⟨$proof, by ring1⟩))

def sosProofsTactic (cert : Array (TSyntax `term × TSyntax `term)) :
    MacroM (TSyntax `term) := do
  let mut proof ← `(le_refl (0 : ℝ))
  for (weight, form) in cert do
    let step ← `(mul_nonneg (show (0 : ℝ) ≤ $weight from by norm_num) (sq_nonneg $form))
    proof ← `(add_nonneg $proof $step)
  return proof

example (x : ℝ) : 0 ≤ 3*x^2 + 2*x + 3 := by
  run_tac do
    let x := mkIdent `x
    let proof ← Elab.liftMacroM do
      sosProofsTactic #[(← `(1), ← `($x-1)), (← `(2), ← `($x+1))]
    exactTerm (← `(nonnegOfCertificate _ _ ⟨$proof, by ring1⟩))

/- ## 4. Ask another program for a certificate -/

/- Instructor: 43–65 minutes. Learning goal: build the external tactic through
five working stages: string, file, printed request, printed response, full proof.
Each stage reuses the preceding work. The parser, expression reader, and process
wrapper are supplied. Keep the focus on what each new tactic adds.
Break at minute 65 and resume at 70.
-/

-- (Slide 3: External search and checked evidence)

-- 4.1. Prove the goal using a certificate string.
/- Instructor: Start with the same weighted list used in section 3, now written
as a string. parseSOS is supplied and pure: it returns typed syntax or a parser
error. Students fill closeWithSOS with the ordinary exact proof from section 3.
The sos_text registration is supplied. Run its example before introducing files.
For a goal lhs ≤ rhs, sub_nonneg.mp uses the certificate for rhs - lhs.
runParserCategory checks the whole input with default parser options; exact then
elaborates in the goal's context. Lean's own tactics also use this parser helper.
-/

def parseSOS (env : Environment) (text : String) : Except String (TSyntax `term) := do
  let stx ← Parser.runParserCategory env `term text
  return ⟨stx⟩

def closeWithSOS (cert : TSyntax `term) : TacticM Unit := do
  evalTactic (← `(tactic|
    exact sub_nonneg.mp (nonnegOfCertificate _ _
      ⟨weighted_squares_nonneg $cert (by norm_num), by
        simp <;> ring⟩)))

elab "sos_text " text:str : tactic => do
  match parseSOS (← getEnv) text.getString with
  | .ok cert => closeWithSOS cert
  | .error message => throwError "{message}"

example (x y z : ℝ) : 0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  sos_text "[(1/2, x-y), (1/2, y-z), (1/2, x-z)]"

-- 4.2. Read the certificate from a file.
/- Instructor: The new step is IO.FS.readFile. Reuse sos_text with the contents.
sosDirectory is supplied to support running from the repository root or Week 11.
quote turns the runtime String into string-literal syntax for the quotation.
The saved file contains exactly the certificate from 4.1. This stage needs no
Python installation and remains the fallback if the solver is unavailable.
-/

def sosDirectory : IO System.FilePath := do
  return if ← (System.FilePath.mk "Week 11").isDir then "Week 11" else "."

elab "sos_from " path:str : tactic => do
  let text ← IO.FS.readFile ((← sosDirectory) / path.getString)
  evalTactic (← `(tactic| sos_text $(quote text)))

example (x y z : ℝ) : 0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  sos_from "triangle-sos.txt"

-- 4.3. Print the problem we want Python to solve.
/- Instructor: Keep polynomialJSON and getSOSProblem supplied and folded.
Students write the small logging tactic. Run it and inspect the request: variable
names plus the arithmetic tree for rhs - lhs. Printing leaves the goal open;
the next line uses the working tactic from 4.1 to finish the example.
-/

-- The expression reader translates arithmetic into JSON for Python.
partial def polynomialJSON (vars : Array Expr) (e : Expr) : MetaM Json := do
  let e := e.consumeMData
  if let some i := vars.idxOf? e then
    return toJson [toJson "var", toJson i]
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let some n ← getNatValue? e.getAppArgs[1]! | throwError "expected a numeral"
    return toJson [toJson "num", toJson n]
  if e.isAppOfArity ``Neg.neg 3 then
    return toJson [toJson "neg", ← polynomialJSON vars e.appArg!]
  if e.isAppOfArity ``HPow.hPow 6 then
    let args := e.getAppArgs
    let some n ← getNatValue? args[5]! | throwError "expected a numerical exponent"
    return toJson [toJson "pow", ← polynomialJSON vars args[4]!, toJson n]
  for (name, tag) in [(``HAdd.hAdd, "add"), (``HSub.hSub, "sub"),
                      (``HMul.hMul, "mul"), (``HDiv.hDiv, "div")] do
    if e.isAppOfArity name 6 then
      let args := e.getAppArgs
      return toJson [toJson tag, ← polynomialJSON vars args[4]!,
        ← polynomialJSON vars args[5]!]
  throwError "unsupported polynomial expression: {e}"

def getSOSProblem : TacticM Json := withMainContext do
  let target := (← getMainTarget).consumeMData
  unless target.isAppOfArity ``LE.le 4 do
    throwError "expected a real inequality"
  let args := target.getAppArgs
  unless ← isDefEq args[0]! (mkConst ``Real) do
    throwError "expected an inequality over ℝ"
  let vars : Array Expr := (collectFVars {} target).fvarIds.map .fvar
  for x in vars do
    unless ← isDefEq (← inferType x) (mkConst ``Real) do
      throwError "expected real variables"
  let lhs ← polynomialJSON vars args[2]!
  let rhs ← polynomialJSON vars args[3]!
  let mut names : Array String := #[]
  for x in vars do
    names := names.push (← PrettyPrinter.ppExpr x).pretty
  return Json.mkObj [("variables", toJson names),
    ("expression", toJson [toJson "sub", rhs, lhs])]

elab "sos_problem" : tactic => do
  let problem ← getSOSProblem
  logInfo problem.compress

example (x y z : ℝ) : 0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  sos_problem
  sos_text "[(1/2, x-y), (1/2, y-z), (1/2, x-z)]"

-- 4.4. Call Python and print its proposed certificate.
/- Instructor: Read the supplied askSOS wrapper: stdin, stdout, and exit status.
It is an IO computation lifted into TacticM. Students extend the previous logging
tactic by calling Python and printing its response. The goal is still open.
The final line uses the saved certificate from 4.2 to finish this demonstration.
Open find_sos.py at SOSProblem, add_sos_constraint, and solve to show the existing
SumOfSquares.py library. The binder reconstructs rationals and prints Lean syntax.
-/

-- Send the problem on stdin and read the proposed weighted list from stdout.
def askSOS (problem : Json) : IO String := do
  let dir ← sosDirectory
  let out ← IO.Process.output {
    cmd := (dir / ".." / ".venv-sos/bin/python").toString
    args := #[(dir / "find_sos.py").toString]
  } problem.compress
  if out.exitCode != 0 then
    throw <| IO.userError s!"SOS search failed ({out.exitCode}): {out.stderr.trimAscii}"
  return out.stdout

elab "sos_search" : tactic => do
  let problem ← getSOSProblem
  let text ← askSOS problem
  logInfo text

example (x y z : ℝ) : 0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  sos_search
  sos_from "triangle-sos.txt"

-- 4.5. Use Python's answer to prove the goal.
/- Instructor: Replace the logging step with the sos_text call already used
in 4.2. Students combine the working parts; no new proof pattern is needed.
Show triangle_external, the inequality with a nonzero left side, and the quartic.
Print axioms: Python contributes no native-computation axiom. The numerical search
can fail; every proposed answer still needs the nonnegativity and identity proofs.
-/

elab "external_sos" : tactic => do
  let problem ← getSOSProblem
  let text ← askSOS problem
  evalTactic (← `(tactic| sos_text $(quote text)))

theorem triangle_external (x y z : ℝ) : 0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  external_sos

example (x y : ℝ) : 2*x*y ≤ x^2 + y^2 := by
  external_sos

-- The squares can themselves be higher-degree polynomials.
theorem quartic_external (x y : ℝ) : 0 ≤ x^4 - 2*x^2*y + y^2 := by
  external_sos

example (x : ℝ) : 0 ≤ x^2 ∧ True := by
  constructor
  · external_sos
  · trivial

#print axioms triangle_external

/- ## 5. Proofs by reflection -/

/- Instructor: 70–80 minutes. Learning goal: reduce an algebraic equality with
arbitrary variables to a computation on concrete data.

Begin with the ordinary proof. rfl fails because the monoid laws are theorems;
rewriting applies those laws. Ask what algorithm could recognize all equalities
that follow from associativity and identity. Removing the 1s and recording the
remaining factors in order suggests a list as the normal form. Show slide 4.

Connect to SOS: we already used a general nonnegativity theorem to check a
certificate. We now prove a theorem that justifies a normalization algorithm,
so each new equality can be proved by computing and applying that theorem.
The monoid example isolates this idea with three constructors and one induction.

MExpr, its interpretation, the example trees, and flatten are supplied. Students
already know expression trees. Identify indices 0, 1, 2 with a, b, c and spend
at most two minutes on the representation. Run both flatten calls. Their output
is [0, 1, 2], independently of the values or even the type of a, b, c.
Ask why equal lists should imply equal products. Section 6 proves the answer.

Here normal form means a form obtained using the monoid laws. Reducing the Lean
definition flatten computes that form; it does not unfold arbitrary elements
of M. Keep this connection to last week's definitional equality explicit.
Sources: CPDT's monoid expression simplifier and Timothy Mou's Lean adaptation.
-/

example [Monoid M] (a b c : M) :
    (a * b) * (1 * c) = a * (b * c) := by
  fail_if_success rfl
  rw [one_mul, mul_assoc]

-- (Slide 4: Proofs by reflection)

-- 5.1. The indices 0, 1, 2 stand for a, b, c.
inductive MExpr where
  | var : Nat → MExpr
  | one : MExpr
  | mul : MExpr → MExpr → MExpr
  deriving Repr

def MExpr.eval [Monoid M] (ρ : Nat → M) : MExpr → M
  | .var i => ρ i
  | .one => 1
  | .mul a b => a.eval ρ * b.eval ρ

def lhs : MExpr := .mul (.mul (.var 0) (.var 1)) (.mul .one (.var 2))
def rhs : MExpr := .mul (.var 0) (.mul (.var 1) (.var 2))

example [Monoid M] (a b c : M) :
    lhs.eval (fun i => [a, b, c].getD i 1) = (a * b) * (1 * c) := by
  rfl

-- 5.2. Flattening keeps the variables in order and removes identities.
def MExpr.flatten : MExpr → List Nat
  | .var i => [i]
  | .one => []
  | .mul a b => a.flatten ++ b.flatten

#eval lhs.flatten
#eval rhs.flatten

/- ## 6. Prove that the computation justifies the goal -/

/- Instructor: 80–97 minutes. Learning goal: identify exactly which theorem
turns the algorithm's output into a proof of the original mathematical claim.

Show slide 5. Read flatten_correct's statement before its supporting lemma:
interpreting the computed list gives the same value as interpreting the tree.
evalList is supplied. Prove the cons case of evalList_append in class using
the induction hypothesis and associativity. Then fill the multiplication case of
flatten_correct, then derive reflect_sound by rewriting through that theorem.
The multiplication case is where the algebraic laws justify concatenation.

At 6.3, apply reflect_sound and STOP on the new goal. The arbitrary monoid
equality has become lhs.flatten = rhs.flatten. Use change to expose the two
concrete lists, then close by rfl. This is the main learning moment of the half:
the soundness theorem carries the algebra; reduction checks this particular input.
Print reflected only after completing the proofs, and locate the theorem
application and Eq.refl argument. The input trees still occur in the proof term.

If time slips, supply the induction step; preserve the theorem application and
the pause at its computational premise. No completeness theorem is needed.
A different factor order can make this method fail even in a commutative monoid.
-/

-- (Slide 5: The soundness theorem)

def evalList [Monoid M] (ρ : Nat → M) : List Nat → M
  | [] => 1
  | i :: is => ρ i * evalList ρ is

theorem evalList_append [Monoid M] (ρ : Nat → M) (xs ys : List Nat) :
    evalList ρ (xs ++ ys) = evalList ρ xs * evalList ρ ys := by
  induction xs with
  | nil => exact (one_mul _).symm
  | cons i xs ih =>
    change ρ i * evalList ρ (xs ++ ys) = (ρ i * evalList ρ xs) * evalList ρ ys
    rw [ih, mul_assoc]

-- 6.1. The induction follows the three constructors of MExpr.
theorem flatten_correct [Monoid M] (ρ : Nat → M) (e : MExpr) :
    evalList ρ e.flatten = e.eval ρ := by
  induction e with
  | var i => exact mul_one _
  | one => rfl
  | mul a b ha hb =>
    change evalList ρ (a.flatten ++ b.flatten) = a.eval ρ * b.eval ρ
    rw [evalList_append, ha, hb]

-- 6.2. Equality of the computed lists implies the original equality.
theorem reflect_sound [Monoid M] (ρ : Nat → M) (a b : MExpr)
    (h : a.flatten = b.flatten) : a.eval ρ = b.eval ρ := by
  rw [← flatten_correct ρ a, ← flatten_correct ρ b, h]

-- 6.3. The list comparison is closed even though a, b, and c are arbitrary.
theorem reflected [Monoid M] (a b c : M) :
    (a * b) * (1 * c) = a * (b * c) := by
  apply reflect_sound (fun i => [a, b, c].getD i 1) lhs rhs
  change [0, 1, 2] = [0, 1, 2]
  rfl

#print reflected

/- ## 7. How does Lean establish the computational equality? -/

/- Instructor: 97–112 minutes. Learning goal: explain how a computation becomes
proof evidence and what changes when it runs as compiled code.

The list equality is already familiar. Keep that same proposition for every
comparison. Show slide 6, inspect Decidable, then compare #eval and #reduce.
The displayed true is an observation. In lists_by_term, we prove the equality
and apply of_decide_eq_true to obtain a proof of the proposition. In section 6,
rfl could already prove the list equality directly; using decide here lets us
inspect a general decision procedure on the same input.

Show slide 7. On the pinned v4.34.0-rc2, decide first reduces the decision
procedure during elaboration and submits a computational proof for kernel
checking. decide +kernel asks the kernel to validate an auxiliary lemma directly.
Both lists_decide and lists_kernel have no axioms. native_decide executes
compiled code and introduces a fresh axiom asserting its Boolean result.
Print that actual axiom name. The kernel checks the finished proof relative to
its axioms; it does not replay the compiled execution.

At 7.3 replace lists_native with lists_kernel live. The mathematical soundness
theorem stays the same while the new native axiom disappears from the finished
proof's dependencies. Uncomment the last two #print commands after section 6's
proofs are complete; otherwise their output includes sorryAx.
This small example exposes the mechanism, not a speed benefit. Recall Week 6's
finite computations as a reason to care about evaluation cost. Do not claim that
all reflective proofs need native_decide or that Python SOS already uses it.
Sources: TPiL Decidable; the pinned Decide.lean and Native.lean implementations.
-/

-- (Slide 6: Decidable propositions)

#print Decidable
#check of_decide_eq_true

#eval decide (lhs.flatten = rhs.flatten)
#reduce decide (lhs.flatten = rhs.flatten)

-- 7.1. Apply of_decide_eq_true to prove the proposition.
theorem lists_by_term : lhs.flatten = rhs.flatten :=
  of_decide_eq_true rfl

-- (Slide 7: decide, decide +kernel, native_decide)

-- 7.2. Use the same proposition to compare the computation methods.
theorem lists_decide : lhs.flatten = rhs.flatten := by decide

theorem lists_kernel : lhs.flatten = rhs.flatten := by decide +kernel

theorem lists_native : lhs.flatten = rhs.flatten := by native_decide

#print axioms lists_decide
#print axioms lists_kernel
#print axioms lists_native

-- 7.3. Apply the soundness theorem with the computed evidence.
theorem reflected_native [Monoid M] (a b c : M) :
    (a * b) * (1 * c) = a * (b * c) := by
  exact reflect_sound (fun i => [a, b, c].getD i 1) lhs rhs lists_native

#print axioms reflected
#print axioms reflected_native

/- ## 8. Turn the reflection proof into a tactic -/

/- Instructor: 112–120 minutes. Learning goal: recognize the completed tactic
as an abstraction of the handwritten application of reflect_sound.

The evaluator, flatten, and their correctness proofs are ordinary Lean definitions
and theorems. reify needs MetaM for definitional equality and typed expression
construction. Only reifyGoal and reflectMonoid need access to the tactic goal.
Keep reify and reifyGoal folded. Their result is the environment and two trees
we chose by hand in 6.3. Both sides share an array of atoms; a repeated expression
gets the same index. The final proof's type must match the original goal, so the
kernel also checks the connection between this representation and that goal.
The reifier recognizes standard HMul multiplication and identities; arbitrary
other subexpressions, including a + b, can be recorded as atoms.

Write reflectMonoid by following 6.3: get the inputs, compute both lists, make
the reflexivity proof, and apply reflect_sound. isDefEq establishes that the
lists reduce to the same value. mkEqRefl constructs the equality proof, and
closeMainGoal submits the full term. Register the syntax with the one-line elab.
Run the positive examples and the rejected commutativity example. Print automated
and compare it with reflected. If short on time, show the tactic completed.

Close by returning to the SOS proof: its ring obligation is another place where
algebraic normalization is useful. A verified SOS checker could instead compute
coefficient identities and signs, then use its soundness theorem in the same way.
The Python adapter still only proposes data; no correctness theorem for the
numerical solver was assumed. The additional trust in native_decide comes from
the way we establish a computational equality, not from reflection itself.
-/

-- The reifier records atoms in a shared array and uses their positions as indices.
partial def reify (one : Expr) (e : Expr) (atoms : Array Expr) :
    MetaM (Expr × Array Expr) := do
  if ← isDefEq e one then
    return (mkConst ``MExpr.one, atoms)
  if e.isAppOfArity ``HMul.hMul 6 then
    let (a, atoms) ← reify one e.getAppArgs[4]! atoms
    let (b, atoms) ← reify one e.getAppArgs[5]! atoms
    return (mkApp2 (mkConst ``MExpr.mul) a b, atoms)
  for i in [:atoms.size] do
    if ← isDefEq e atoms[i]! then
      return (mkApp (mkConst ``MExpr.var) (mkNatLit i), atoms)
  return (mkApp (mkConst ``MExpr.var) (mkNatLit atoms.size), atoms.push e)

def reifyGoal : TacticM (Expr × Expr × Expr) := withMainContext do
  let some (type, left, right) := (← getMainTarget).eq?
    | throwError "expected an equality"
  let one ← mkAppOptM ``One.one #[some type, none]
  let (a, atoms) ← reify one left #[]
  let (b, atoms) ← reify one right atoms
  let values ← mkListLit type atoms.toList
  let ρ ← withLocalDeclD `i (mkConst ``Nat) fun i => do
    let body ← mkAppM ``List.getD #[values, i, one]
    mkLambdaFVars #[i] body
  return (ρ, a, b)

-- 8.1. Abstract the proof from 6.3.
def reflectMonoid : TacticM Unit := withMainContext do
  let (ρ, a, b) ← reifyGoal
  let left ← mkAppM ``MExpr.flatten #[a]
  let right ← mkAppM ``MExpr.flatten #[b]
  unless ← isDefEq left right do
    throwError "the flattened expressions differ"
  let proof ← mkAppM ``reflect_sound #[ρ, a, b, ← mkEqRefl left]
  closeMainGoal `reflect_monoid proof

elab "reflect_monoid" : tactic => reflectMonoid

theorem automated [Monoid M] (a b c : M) :
    (a * 1) * (b * c) = a * (b * (1 * c)) := by
  reflect_monoid

example [Monoid M] (a b c : M) :
    (a * b) * (1 * c) = a * (b * c) := by
  reflect_monoid

example (a b : Nat) : (a + b) * 1 * (a + b) = (a + b) * (a + b) := by
  reflect_monoid

example (a b : Nat) : a * b = b * a := by
  fail_if_success reflect_monoid
  exact Nat.mul_comm a b

#print automated
#print axioms automated

end Week11
