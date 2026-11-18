import Mathlib

set_option linter.unusedTactic false

/- Metaprogramming III: SOS and proofs by reflection. November 18, 2026.
Open this file independently of the student and instructor copies.
From Week 11, run bash setup_sos.sh once for Python setup.
-/

open Lean Lean.Meta Lean.Elab.Tactic

namespace Week11

-- (Slide 1: Proofs by verifying external computations || Proofs by verifying the checker)

/- ## 1. A proof we want to automate -/

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

-- 2.1. Let's turn this into a "sos_step" tactic using a macro.
macro "sos_step " s:term : tactic =>
  `(tactic| refine nonnegOfCertificate _ $s ?_)

example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by
  sos_step ((x-y)^2)
  constructor
  · positivity
  · ring

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

example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by
  fail_if_success square_using (x+y)
  square_using (x-y)

/- ## 3. A certificate with several squares -/

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

/- ## 4. Ask another program for a certificate -/

-- (Slide 3: External search and checked evidence)

-- 4.1. Prove the goal using a certificate string.
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
def sosDirectory : IO System.FilePath := do
  return if ← (System.FilePath.mk "Week 11").isDir then "Week 11" else "."

elab "sos_from " path:str : tactic => do
  let text ← IO.FS.readFile ((← sosDirectory) / path.getString)
  evalTactic (← `(tactic| sos_text $(quote text)))

example (x y z : ℝ) : 0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  sos_from "triangle-sos.txt"

-- 4.3. Print the problem we want Python to solve.
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
