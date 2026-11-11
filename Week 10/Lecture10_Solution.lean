import Mathlib

/-
Metaprogramming II: Asking another computer. Solutions. November 11, 2026.
Open independently; run from the repository root after the Python setup in README.md.
Adapted from Macbeth, MPiL, and LoVe; see README.md for sources.
-/

open Lean Lean.Meta Lean.Elab.Tactic

namespace Week10

/- # Metaprogramming II: Asking another computer -/

/- # Part 1. How a tactic builds a proof -/

/- ## 1. Warmup: interval_cases -/

-- 1.1. Use interval_cases.
example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := by
  interval_cases k <;> norm_num

theorem eq_or_le_succ_of_le {a k : Nat} (h : a ≤ k) : a = k ∨ a + 1 ≤ k :=
  Nat.eq_or_lt_of_le h

#check eq_or_le_succ_of_le

-- 1.2. Split by hand.
example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := by
  rcases eq_or_le_succ_of_le h1 with h | h1
  · subst h
    norm_num
  · rcases eq_or_le_succ_of_le h1 with h | h1
    · subst h
      norm_num
    · rcases eq_or_le_succ_of_le h1 with h | h1
      · subst h
        norm_num
      · rcases eq_or_le_succ_of_le h1 with h | h1
        · subst h
          norm_num
        · omega

-- 1.3. (optional) Automate the split.
syntax "my_interval_cases " ident " from " ident : tactic

macro_rules
  | `(tactic| my_interval_cases $k:ident from $h:ident) =>
      `(tactic|
        first
        | omega
        | rcases eq_or_le_succ_of_le $h with heq | hnext
          all_goals
            first
            | subst heq
            | my_interval_cases $k from hnext)

example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := by
  my_interval_cases k from h1
  all_goals norm_num

-- 1.4. Singleton and empty intervals.
example (k : Nat) (h1 : 3 ≤ k) (h2 : k ≤ 3) : k = 3 := by
  my_interval_cases k from h1

example (k : Nat) (h1 : 5 ≤ k) (h2 : k ≤ 4) : False := by
  my_interval_cases k from h1

/- ## 2. Expressions -/

-- 2.1. Inspect the proof term.
theorem test_constructor (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

set_option pp.structureInstances false in
#print test_constructor

/- ### 2.2. How Lean represents these terms -/

#print Lean.Expr
#check Lean.Expr.app

-- 2.3. Inspect and construct expressions.
set_option linter.unusedTactic false in
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  run_tac withMainContext do
    let target ← getMainTarget
    let localProof ← getFVarFromUserName `hp
    logInfo m!"Head: {target.getAppFn}; arguments: {target.getAppArgs}"
    logInfo m!"Local: {localProof} : {← inferType localProof}; isFVar: {localProof.isFVar}"
    let p ← getFVarFromUserName `P
    let q ← getFVarFromUserName `Q
    let conjunction : Expr := .app (.app (.const ``And []) p) q
    logInfo m!"Constructed: {conjunction}"
  exact ⟨hp, hq⟩

/- ## 3. Metavariables -/

#check Lean.Expr.mvar

-- 3.1. Named goals.
set_option pp.mvars true in
set_option linter.unusedTactic false in
theorem test_refine (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  refine And.intro ?left ?right
  -- ?g := And.intro ?left ?right
  case left =>
    run_tac withMainContext do
      let goal ← getMainGoal
      let hole : Expr := .mvar goal
      logInfo m!"Hole: {hole} : {← inferType hole}; isMVar: {hole.isMVar}"
    exact hp
  -- The proof is now And.intro hp ?right.
  case right =>
    exact hq

#print test_refine

-- Metavariables inferred for one goal propagate to other goals
example : ∃ n : Nat, n = 7 := by
  apply Exists.intro
  case h => rfl

/- ### 3.2. Working with metavariables in MetaM -/

-- MetaM gives access to metavariables and their assignments.
def metavarDemo : MetaM Unit := do
  let x ← mkFreshExprMVar (mkConst ``Nat) (userName := `x)
  logInfo m!"Hole type: {← inferType x}"
  let e : Expr := .app (mkConst ``Nat.succ) x
  logInfo m!"Before: {← instantiateMVars e}"
  x.mvarId!.assign (mkNatLit 7)
  logInfo m!"Original tree still contains a hole: {e.hasMVar}"
  let filled ← instantiateMVars e
  logInfo m!"After: {filled}; contains a hole: {filled.hasMVar}"

#eval metavarDemo

/- ### 3.3. A metavariable's local context -/

set_option linter.unusedTactic false in
example (P Q : Prop) : (P → P) ∧ (Q → Q) := by
  constructor
  all_goals intro h
  all_goals run_tac do
    let goal ← getMainGoal
    goal.withContext do
      let h ← getFVarFromUserName `h
      logInfo m!"{h} : {← inferType h}"
  all_goals assumption

/- ## 4. Inspect a goal and fill it with a hypothesis -/

-- TacticM also manages the current goal list.
#check TacticM
#check getMainGoal
#check getMainTarget
#check getUnsolvedGoals
#check MVarId.withContext

-- 4.1. Goals and local contexts.
def inspectGoals : TacticM Unit := do
  let goals ← getUnsolvedGoals
  logInfo m!"Open goals: {goals.length}"
  for goal in goals do
    goal.withContext do
      logInfo m!"Target: {← goal.getType}"
      for decl in ← getLCtx do
        if !decl.isImplementationDetail then
          logInfo m!"  {decl.userName} : {decl.type}"

set_option linter.unusedTactic false in
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  refine And.intro ?left ?right
  run_tac inspectGoals
  all_goals assumption

/- ### 4.2. Normal forms and definitional equality -/

@[irreducible] def hiddenNumber : Nat := 7
def number : Nat := hiddenNumber
abbrev numberAlias : Nat := number

def traceUnfolding (mode : TransparencyMode) : MetaM Unit := do
  let e := mkConst ``numberAlias
  logInfo m!"{← withTransparency mode (reduceAll e)}"

#eval traceUnfolding .none
#eval traceUnfolding .reducible
#eval traceUnfolding .default
#eval traceUnfolding .all

abbrev Both (P Q : Prop) : Prop := P ∧ Q

set_option linter.unusedTactic false in
example (P Q : Prop) (hp : P) (hq : Q) : Both (id P) Q := by
  run_tac withMainContext do
    let target ← getMainTarget
    let normal ← reduceAll target
    logInfo m!"Original: {target}"
    logInfo m!"WHNF: {← whnf target}"
    logInfo m!"Normal form: {normal}"
    logInfo m!"Same syntax: {target == normal}"
    logInfo m!"Definitionally equal: {← isDefEq target normal}"
  exact ⟨hp, hq⟩

-- Comparison can assign an unknown.
def inferMetavar : MetaM Unit := do
  let x ← mkFreshExprMVar (mkConst ``Nat) (userName := `x)
  let e : Expr := .app (mkConst ``Nat.succ) x
  logInfo m!"Matches 8: {← isDefEq e (mkNatLit 8)}"
  logInfo m!"x: {← instantiateMVars x}"

#eval inferMetavar

/- ### 4.2.1. Revisit interval_cases: read the bound -/

elab (priority := low) "my_interval_cases " h:ident : tactic => withMainContext do
  let proof ← getFVarFromUserName h.getId
  let type ← whnf (← inferType proof)
  let some (_, a) := type.app2? ``Nat.le
    | throwError "expected a natural-number lower bound"
  unless a.isFVar do
    throwError "expected a variable on the right of the bound"
  let k := mkIdent (← a.fvarId!.getUserName)
  evalTactic (← `(tactic| my_interval_cases $k from $h))

example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := by
  my_interval_cases h1
  all_goals norm_num

-- 4.3. Revisit hypothesis.
-- Use isDefEq to compare types up to computation.
def hypothesis : TacticM Unit := withMainContext do
  let target ← getMainTarget
  let goal ← getMainGoal
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if ← isDefEq decl.type target then
        goal.assign decl.toExpr
        replaceMainGoal []
        return
  throwError "no hypothesis has the target type"

elab "hypothesis" : tactic => hypothesis

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  refine And.intro ?left ?right
  all_goals hypothesis

example (P : Prop) (h : (fun X : Prop => X) P) : P := by
  hypothesis

example : True := by
  fail_if_success hypothesis
  trivial

/- ## 5. Create subgoals and connect them to a proof -/

#check mkFreshExprMVar
#check mkAppM
#check Lean.Expr.mvarId!
#check replaceMainGoal

#check @And.intro

set_option linter.unusedTactic false in
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  run_tac withMainContext do
    let hp ← getFVarFromUserName `hp
    let hq ← getFVarFromUserName `hq
    let proof ← mkAppM ``And.intro #[hp, hq]
    logInfo m!"All arguments: {proof.getAppArgs}"
  exact ⟨hp, hq⟩

-- 5.1. Construct the proof and return subgoals.
def splitAndCore (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  let target ← whnf (← goal.getType)
  let some (p, q) := target.and?
    | throwError "expected a conjunction"
  let left ← mkFreshExprMVar p .syntheticOpaque (userName := `left)
  let right ← mkFreshExprMVar q .syntheticOpaque (userName := `right)
  let proof ← mkAppM ``And.intro #[left, right]
  goal.assign proof
  return [left.mvarId!, right.mvarId!]

-- 5.2. Expose the subgoals.
elab "split_and" : tactic => do
  let goal ← getMainGoal
  let newGoals ← splitAndCore goal
  replaceMainGoal newGoals

set_option linter.unusedTactic false in
theorem test_split (P Q : Prop) (hp : P) (hq : Q) : Both (id P) Q := by
  run_tac withMainContext do
    let target ← getMainTarget
    logInfo m!"And before reduction: {target.and?.isSome}"
    logInfo m!"And after whnf: {(← whnf target).and?.isSome}"
  split_and
  all_goals hypothesis

#print test_split

-- 5.3. Preserve pending goals.
set_option linter.unusedTactic false in
example (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : (P ∧ Q) ∧ R := by
  split_and
  split_and
  run_tac do
    unless (← getUnsolvedGoals).length == 3 do
      throwError "expected goals P, Q, and R"
  all_goals hypothesis

example : True := by
  fail_if_success split_and
  trivial

/- ## 6. Just enough elaboration: our own exact -/

#check Lean.Elab.Tactic.elabTerm
#check Lean.Elab.Tactic.elabTermEnsuringType
#check closeMainGoal

-- 6.1. Inspect an elaborated term.
elab "inspect_term " t:term : tactic => withMainContext do
  let e ← elabTerm t none
  logInfo m!"{e} : {← inferType e}"

set_option linter.unusedTactic false in
example (n : Nat) : n = n := by
  inspect_term (n + 1)
  inspect_term (0 : Int)
  rfl

/- ### 6.1.1. Revisit interval_cases: elaborate a proof -/

elab "my_interval_cases_term " t:term : tactic => withoutRecover do
  evalTactic (← `(tactic| (have hbound := $t; my_interval_cases hbound)))

example (k : Nat) (h1 : 2 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := by
  my_interval_cases_term (Nat.le_trans (by decide : 1 ≤ 2) h1)
  all_goals norm_num

example (h : True) : True := by
  fail_if_success my_interval_cases h
  fail_if_success my_interval_cases_term (0 : Nat)
  exact h

-- 6.2. Elaborate against the target type.
def exactTerm (stx : Syntax) : TacticM Unit := withoutRecover <| withMainContext do
  let target ← getMainTarget
  let proof ← elabTermEnsuringType stx (some target)
  closeMainGoal `exact_term proof

elab "exact_term " t:term : tactic => exactTerm t

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact_term ⟨hp, hq⟩

example : Int := by
  exact_term 0

example : True := by
  fail_if_success exact_term (0 : Nat)
  fail_if_success exact_term _
  exact_term True.intro

/- # Part 2. Check a sum-of-squares certificate -/

/- ## 7. What should the other program return? -/

-- 7.1. Nonnegativity and a polynomial identity.
theorem nonnegOfCertificate (p s : ℝ) (h : 0 ≤ s ∧ p = s) : 0 ≤ p := by
  rw [h.2]
  exact h.1

example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by
  apply nonnegOfCertificate _ ((x-y)^2)
  constructor
  · exact sq_nonneg (x-y)
  · ring

-- Algebraic equality needs a proof.
example (x y : ℝ) : (x-y)^2 = x^2 - 2*x*y + y^2 := by
  fail_if_success rfl
  ring

-- 7.2. A weighted sum of squares.
example (x y z : ℝ) : 0 ≤ (1 / 2 : ℝ) * (x-y)^2 + (y-z)^2 := by
  have hxy : 0 ≤ (1 / 2 : ℝ) * (x-y)^2 :=
    mul_nonneg (by norm_num) (sq_nonneg (x-y))
  have hyz : 0 ≤ (y-z)^2 := sq_nonneg (y-z)
  exact add_nonneg hxy hyz

theorem triangle_nonneg (x y z : ℝ) : 0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  linear_combination (sq_nonneg (x-y) + sq_nonneg (y-z) + sq_nonneg (z-x)) / 2

#print axioms triangle_nonneg

/- ## 8. Check one square -/

-- 8.1. Expose the two certificate conditions.
elab "sos_step " s:term : tactic => do
  evalTactic (← `(tactic| refine nonnegOfCertificate _ $s ?_))

example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by
  sos_step ((x-y)^2)
  split_and
  · positivity
  · ring

-- 8.2. Construct proof syntax and reuse exactTerm.
elab "square_using " q:term : tactic => do
  exactTerm (← `(nonnegOfCertificate _ ($q ^ 2) ⟨sq_nonneg $q, by ring1⟩))

example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by
  square_using (x-y)

example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by
  fail_if_success square_using (x+y)
  square_using (x-y)

/- ## 9. Check a weighted sum of squares -/

structure SOSTerm where
  weight : ℚ
  form : Array ℚ

-- Coefficients are ordered as constant, x, y, z.
def triangleCertificate : Array SOSTerm := #[
  ⟨1/2, #[0, 1, -1, 0]⟩,
  ⟨1/2, #[0, 0, 1, -1]⟩,
  ⟨1/2, #[0, 1, 0, -1]⟩]

-- Convert rational data into typed syntax.
def rationalSyntax (q : ℚ) : TacticM (TSyntax `term) := do
  let n := Syntax.mkNatLit q.num.natAbs
  let d := Syntax.mkNatLit q.den
  if q.num < 0 then
    `((-($n : ℝ)) / $d)
  else
    `(($n : ℝ) / $d)

-- Each summand contributes a proof that its weighted square is nonnegative.
def certificateProof (vars : Array (TSyntax `term)) (cert : Array SOSTerm) :
    TacticM (TSyntax `term) := do
  let mut proof ← `(le_refl (0 : ℝ))
  for part in cert do
    unless part.form.size == vars.size + 1 do
      throwError "wrong number of coefficients"
    let weight ← rationalSyntax part.weight
    let mut form ← rationalSyntax part.form[0]!
    for x in vars, c in part.form.toList.drop 1 do
      if c.num != 0 then
        let coefficient ← rationalSyntax c
        form ← `($form + $coefficient * $x)
    let step ← `(mul_nonneg (show (0 : ℝ) ≤ $weight from by norm_num) (sq_nonneg $form))
    proof ← `(add_nonneg $proof $step)
  return proof

-- 9.1. Check the polynomial identity against the current goal.
def closeWithSOS (vars : Array (TSyntax `term)) (cert : Array SOSTerm) : TacticM Unit := do
  let proof ← certificateProof vars cert
  exactTerm (← `(by linear_combination ($proof)))

example (x y z : ℝ) : 0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  run_tac closeWithSOS #[mkIdent `x, mkIdent `y, mkIdent `z] triangleCertificate

/- # Part 3. Bring in IO -/

/- ## 10. Read a certificate from a file -/

-- 10.1. Decode rational pairs and affine coefficient lists.
def parseSOSRational (j : Json) : Except String ℚ := do
  let a ← j.getArr?
  unless a.size == 2 do throw "expected a numerator and denominator"
  let num ← a[0]!.getInt?
  let den ← a[1]!.getNat?
  if den == 0 then throw "zero denominator"
  return (num : ℚ) / (den : ℚ)

def parseSOS (text : String) : Except String (Array SOSTerm) := do
  let entries ← (← Json.parse text).getArr?
  entries.mapM fun j => do
    let weight ← parseSOSRational (← j.getObjVal? "weight")
    let form ← (← (← j.getObjVal? "form").getArr?).mapM parseSOSRational
    return ⟨weight, form⟩

-- 10.2. Read, parse, and check.
def readSOS (path : System.FilePath) : IO (Array SOSTerm) := do
  IO.ofExcept (parseSOS (← IO.FS.readFile path))

elab "sos_from " path:str " [" vars:term,* "]" : tactic => do
  let cert ← readSOS path.getString -- IO action lifted into TacticM.
  closeWithSOS vars.getElems cert

#eval return (← readSOS "Week 10/triangle-sos.json").size

example (x y z : ℝ) : 0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  sos_from "Week 10/triangle-sos.json" [x, y, z]

/- ## 11. Ask Python for a decomposition -/

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

def getSOSProblem : TacticM (Json × Array (TSyntax `term)) := withMainContext do
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
  let problem := Json.mkObj [("variables", toJson vars.size),
    ("expression", toJson [toJson "sub", rhs, lhs])]
  let names ← vars.mapM fun x => do return ← Lean.PrettyPrinter.delab x
  return (problem, names)

-- 11.1. Send the problem on stdin; check the exit code before parsing stdout.
def askSOS (problem : Json) : IO (Array SOSTerm) := do
  let out ← IO.Process.output {
    cmd := ".venv-sos/bin/python"
    args := #["Week 10/find_sos.py"]
  } problem.compress
  if out.exitCode != 0 then
    throw <| IO.userError s!"SOS search failed ({out.exitCode}): {out.stderr.trimAscii}"
  IO.ofExcept (parseSOS out.stdout)

-- 11.2. Read the goal, call Python, and check the certificate.
elab "external_sos" : tactic => do
  let (problem, vars) ← getSOSProblem
  let cert ← askSOS problem
  closeWithSOS vars cert

theorem triangle_external (x y z : ℝ) : 0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  external_sos

example (x y : ℝ) : 2*x*y ≤ x^2 + y^2 := by
  external_sos

example (x y : ℝ) : 0 ≤ 2*x^2 + 2*x*y + 3*y^2 - 2*x + 4*y + 5 := by
  external_sos

#print axioms triangle_external

/- ## 12. What if the other program is wrong? -/

-- 12.1. Negative weights, false identities, and malformed data.
example (x y z : ℝ) : 0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  fail_if_success sos_from "Week 10/wrong-sos.json" [x, y, z]
  external_sos

example (x : ℝ) : 0 ≤ x^2 := by
  fail_if_success run_tac closeWithSOS #[mkIdent `x] #[⟨-1, #[0, 1]⟩]
  fail_if_success run_tac closeWithSOS #[mkIdent `x] #[⟨1, #[1, 1]⟩]
  run_tac closeWithSOS #[mkIdent `x] #[⟨1, #[0, 1]⟩]

#guard (parseSOS "yes").toOption.isNone
#guard (parseSOS "[{\"weight\":[1,0],\"form\":[]}]").toOption.isNone

example : True := by
  fail_if_success have : (0 : ℝ) ≤ -1 := by external_sos
  trivial

-- Search failure says nothing about whether the goal is true.
example (x : ℝ) : 0 ≤ x^4 := by
  fail_if_success external_sos
  positivity

example (x : ℝ) : 0 ≤ x^2 ∧ True := by
  constructor
  · external_sos
  · trivial

end Week10
