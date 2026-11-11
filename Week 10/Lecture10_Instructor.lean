import Mathlib

set_option linter.unusedTactic false

/-
Metaprogramming II: Asking another computer. November 11, 2026.
Draft. Instructor copy. Open independently of the student and solution files.

Warmup adapted from Heather Macbeth's Simons 2025 metaprogramming tutorial.
Also based on Metaprogramming in Lean 4, chapters 3, 4, 7, and 9, and LoVe 8.
The IO bridge continues Week 08 and FPiL 4.5.
The quadratic SOS example is a new course adaptation; see README.md for sources.

Run from the repository root. Sections 10–12 use the accompanying files;
11–12 use the Python environment from README.md. 1–9 need no external program.
-/

open Lean Lean.Meta Lean.Elab.Tactic

namespace Week10

/- # Metaprogramming II: Asking another computer -/

/- Instructor route: 120 minutes including a five-minute break.
0–10 1.1–1.2: interval warmup. 1.3–1.4 are optional supplied reading.
10–16 2.1: the conjunction proof and its printed term, entirely in Lean.
16–23 2.2–2.3: Expr slide, then inspect the same conjunction in Lean.
23–37 3: metavariables, MetaM assignments, and local contexts.
37–49 4: reduction, unification, interval-bound lookup, and hypothesis.
49–62 5: infer implicit arguments, construct subgoals and preserve pending goals.
62–67: break. 67–78 6: slide 6, interval wrapper with have, and exact_term.
78–90 7: slide 7, one square and a weighted sum.
90–97 8: visible certificate conditions, then square_using.
97–105 9: construct the checked SOS proof using exactTerm.
105–109 10: supplied file/parser wrappers.
109–115 11: supplied expression reader and Python wrapper; connect external_sos.
115–120 12: wrong answers, process failures, and the completed proof.
Keep 2's introduction and 12's failure experiments.
If behind, skip the 1.3–1.4 walkthrough and 4's extra definitional-equality test.
Supply 9.1's quotation if necessary.

Learning checkpoints:
2: students can identify expressions for the target and a local proof.
3: they can explain a metavariable's type, context, and assignment.
5: they can explain both the parent assignment and the new goal list.
6: they can explain why syntax needs a context and an expected type.
12: they can explain why a false external answer cannot prove the theorem.

Live typing: 1.1–1.2, 2.1, 2.3, 4.2.1, 4.3, 5.1–5.2, 6.1.1, 6.2, 7.1, 8.2, 9.1, 11.2.
The remaining implementations
are supplied. Type in Lecture10.lean and uncomment each checkpoint in sequence.
Run from the repository root. Python 3.10+ is needed for 11–12; 10 is the file fallback.
-/

/- # Part 1. How a tactic builds a proof -/

/- Instructor: 0–10 minutes. Macbeth's Phase0_Model starts with a familiar tactic and asks
for its manual equivalent. Use exactly that opening: pause after interval_cases,
name the four goals, then type the first manual split. Students predict the rest.
Supply the lemma. The last branch has 5 ≤ k and k ≤ 4, hence omega closes it.
The optional macro adapts Macbeth's algorithm to last week's quotations.
Do not spend the warmup implementing it: the source's explicit MetaM proof
construction is the connection we return to in 5. Its Qq API is further reading.
If showing 1.3, explain that omega may solve the goal before any case split.
The singleton equality and contradictory bounds both close immediately.
Each rcases step splits the disjunction into an equality and a stronger bound.
subst h uses the equality proof to replace k by the lower endpoint.
The macro follows the same branches: subst heq in the equality case, and
recursion with hnext in the stronger-bound case.
Move to 2 at minute 10, even if the macro and endpoint checks are unread.
Source: Macbeth, Simons2025/Metaprogramming/Phase0_Model.lean and Phase2_Cleanup.lean.
-/

/- ## 1. Warmup: interval_cases -/

/-
Adapted from Heather Macbeth's Simons 2025 metaprogramming tutorial, phases 0–2.
Start with the proof we want to automate, then turn its repeated step into a tactic.
Adapt the source's Expr construction to last week's tactic quotations.
-/

-- 1.1. Use Mathlib's tactic first. Which values of k remain?
example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := by
  interval_cases k <;> norm_num

-- Split off the lower bound.
theorem eq_or_le_succ_of_le {a k : Nat} (h : a ≤ k) : a = k ∨ a + 1 ≤ k :=
  Nat.eq_or_lt_of_le h

#check eq_or_le_succ_of_le

-- 1.2. Write the case split by hand, without interval_cases.
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

-- 1.3 (optional). Automate the repeated split.
-- Try omega; otherwise split, substitute, and recurse.
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

-- 1.4. Check the endpoints: a singleton interval and an empty interval.
example (k : Nat) (h1 : 3 ≤ k) (h2 : k ≤ 3) : k = 3 := by
  my_interval_cases k from h1

example (k : Nat) (h1 : 5 ≤ k) (h2 : k ≤ 4) : False := by
  my_interval_cases k from h1

/-
We have automated a proof by creating cases and letting Lean check them.
Next, follow an unfinished proof before writing a program to manipulate it.
Then another program will suggest a sum of squares from which we construct a proof.

Goal → polynomial → external search → weighted squares → Lean proof.
-/

/- Instructor: 10–16 minutes. Stay in Lean for 2.1; no slides yet.
Use constructor, then finish each goal with exact.
Print test_constructor to see the resulting And.intro term. Discuss the completed
term without introducing Expr, metavariable assignments, or holes in expressions.
Set pp.structureInstances false when printing to expose And.intro hp hq.
At 2.2, show how this same term is represented as an expression tree.
-/

/- ## 2. Expressions -/

-- 2.1. Complete the proof, then inspect the term produced by constructor.
theorem test_constructor (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

set_option pp.structureInstances false in
#print test_constructor

/- Instructor: 16–23 minutes for 2.2–2.3. Switch to slide 1 here, for the first time.
Start with the printed complete proof and explain its tree representation. Connect Expr to last week's arithmetic datatype, then show
the actual constructor signatures. Identify all forms except mvar at first:
constants, applications, locals, bound variables, sorts, lambdas, function types,
let expressions, literals, and metadata. Give each a short meaning.
The printed fun binds P, Q, hp, and hq: their occurrences in its body are bound
variables. Inside the tactic, these names refer to declarations in the local
context, represented by fvar. Defer de Bruijn calculations and universe arithmetic.
Return to mvar and use it to motivate slide 2.

Return to 2.3's inspector to identify the head And, its arguments P and Q,
and the local proof hp. Construct And.intro using const and successive app nodes,
following MPiL 3, Constructing Expressions. The first two applications supply P
and Q; the last two supply hp and hq. The intermediate conjunction expression
is the constructor awaiting its proofs. And P Q itself is the target proposition.
The double backtick resolves the declaration name; And.intro needs no universe
arguments, so its level list is empty. closeMainGoal submits the final expression
as the proof. Treat this final call as a supplied operation here; no discussion
of metavariable assignments is needed yet. Section 3 introduces unfinished proofs.
Students add the last four lines inside run_tac, then remove the outer sorry.
Section 5 uses mkAppM to infer P and Q, and section 6 reuses closeMainGoal.
Sources: MPiL 3, Expressions, then MPiL 4, Metavariables.
https://leanprover-community.github.io/lean4-metaprogramming-book/main/03_expressions.html
https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html
-/

/- ### 2.2. How Lean represents these terms -/

/- Lean.Expr represents Lean terms, including types and proofs.
It is different from our arithmetic Expr and from parsed Syntax.

  And         constant        Expr.const
  hp          local variable  Expr.fvar
  And P Q     application     app (app And P) Q

The application tree is schematic. And.intro also has implicit arguments P and Q. -/

#print Lean.Expr
#check Lean.Expr.app

-- 2.3. Inspect and construct expressions.
-- Close the goal with closeMainGoal.
#check getFVarFromUserName
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  run_tac withMainContext do
    let target ← getMainTarget
    let hp ← getFVarFromUserName `hp
    logInfo m!"Head: {target.getAppFn}; arguments: {target.getAppArgs}"
    logInfo m!"Local: {hp} : {← inferType hp}; isFVar: {hp.isFVar}"
    let p ← getFVarFromUserName `P
    let q ← getFVarFromUserName `Q
    let conjunction : Expr := .app (.app (.const ``And.intro []) p) q
    logInfo m!"Constructed: {conjunction}"
    let hq ← getFVarFromUserName `hq
    let proof : Expr := .app (.app conjunction hp) hq
    closeMainGoal `example proof

/- Instructor: 23–37 minutes.
Slide 2 introduces Expr.mvar: how can the tree represent an unfinished term?
Its identity refers to a declaration with a type, context, and possible assignment.
Connect this to the familiar goal state from 2.1. Ask how hp can contribute
to filling ?g. Follow 3.1's named holes in Lean and use
show_term to see the partial proof. Compare the result with test_constructor.
Pause after apply Exists.intro: the equality goal contains the unknown witness.
rfl determines that witness as 7. The witness occurs in another goal's type;
it is not an independent puzzle. Section 4.2 will show the unification operation.
The inspector is supplied; ask students to identify the representations.
-/

/- ## 3. Metavariables -/

/- Expr.mvar refers to an expression still to be determined.
Its MVarId identifies a hole with a type, a local context, and possibly an assignment. -/

#check Lean.Expr.mvar

-- 3.1 (supplied). Revisit 2.1 with named goals and inspect the left one.
set_option pp.mvars true in
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

/- Instructor: To display the partial proof, use this layout:

  show_term
    refine And.intro ?left ?right
    case left => exact hp
  case right => exact hq

Indent refine and the left branch under show_term; keep the right branch outside.
This prints `refine ⟨hp, ?_⟩`, meaning And.intro hp with the right proof still open.
The blue [apply] is an editor button, not a tactic in the printed proof.
show_term prints the remaining hole as ?_, without preserving its name ?right.
Putting show_term only around exact hp instead prints `exact hp`: that shows
the left goal's proof, not the whole conjunction.
-/


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

/- Instructor: Show slide 3, then slide 4 with 3.2. Follow MPiL 4's Basic Operations.
Students already know monads. Use the table to explain the information available
when working with the Expr nodes they have just seen. Point to Nat.succ's type,
recall the hp lookup in 2.3, and preview creating and assigning ?x in metavarDemo.
The next slide gives the API names and follows the assignment through a term.
Keep withContext for 3.3, where the two goals make choosing a context meaningful.

Follow the recipe: create x, inspect its type, build e, assign x, instantiate e.
Predict: Nat; Nat.succ ?x; true; Nat.succ 7 with false. Assignment updates the
metavariable context, so e.hasMVar stays true. instantiateMVars returns a new tree
with the assigned hole replaced. It does not reduce Nat.succ 7 to 8.
mvarId! extracts the ID; it is valid here because mkFreshExprMVar returned a hole.
The assigned term must have the hole's type and use only locals available to it.
Defer the tactic goal list to TacticM in section 4.

-/

/- ### 3.3. A metavariable's local context -/

example (P Q : Prop) : (P → P) ∧ (Q → Q) := by
  constructor
  all_goals intro h
  all_goals run_tac do
    let goal ← getMainGoal
    goal.withContext do
      let h ← getFVarFromUserName `h
      logInfo m!"{h} : {← inferType h}"
  all_goals assumption

/- Instructor: Follow MPiL 4, Local Contexts. After intro h, ask which h the
inspector should find. Predict h : P, then h : Q. Introduce goal.withContext
as the way to select the context for that inspection.
The two hypotheses share a user-facing name but have different FVarIds.
goal.withContext temporarily selects that goal's local declarations and instances;
getFVarFromUserName and inferType use this context. It adds no hypotheses and
changes no goals. The previous ambient context is restored after the block.
Distinguish this local context from the metavariable context holding assignments
in 3.2. withMainContext is the tactic convenience for the main goal's context.
Section 4 generalizes the inspection to every hypothesis of every goal.
-/

/- Instructor: 37–49 minutes. Return to 3.1's P ∧ Q example in 4.1. LoVe traces goals before implementing hypothesis. Keep that
order, using the metavariables and MetaM operations from 3.
Compare goal : MVarId, target : Expr, and decl.toExpr : Expr.
withContext installs a goal's local context. It does not add hypotheses to it.
Compare with Week 09, section H, before typing:
4.1 combines traceGoals (goal count and first target) with trace (main context).
The extension is iterating over every goal, using each goal's withContext.
4.3 revisits the same hypothesis search: getLCtx, isDefEq, and assign were already
in last week's class file. The worksheet now retains the search loop and failure
message; fill only replaceMainGoal [] and return after the assignment.
Recall failure handling and filtering of implementation details from the Week 09 solution. Present this as a recap with small changes.
Ask students to explain the old assign line using section 3 before editing it.
Read the retained loop rather than retyping it.
isDefEq can compute and unify; it is not structural equality. In this Lean version,
a failed isDefEq call restores its state through checkpointDefEq. A successful
comparison can assign unknowns; a larger speculative search may still need to
restore those successful assignments if a later step fails.
assign does not validate arbitrary expressions: our type comparison and the local
context justify this assignment. The final declaration still gets kernel checked.
If no local type matches, throw an error. Merely returning Unit leaves the goal open.
Checkpoint: replace 3.1's two exact steps with hypothesis and inspect the result.
Sources: LoVe 8, traceGoals/hypothesis; MPiL 9, custom_assump.
-/

/- ## 4. Inspect a goal and fill it with a hypothesis -/

/- Automate the exact hp step of 3.1.
TacticM supports MetaM operations and also manages the current goal list.
Its return value is separate from that work: returning Unit alone proves nothing.
Use withMainContext before reading hypotheses or comparing their types.
-/

#check TacticM
-- getMainGoal returns an MVarId: the identity of the hole.
#check getMainGoal
-- getMainTarget returns an Expr: the type we need a term of.
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

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  refine And.intro ?left ?right
  run_tac inspectGoals
  all_goals assumption

/- Instructor: Show slide 5 alongside 4.2, following MPiL's order:
full normalisation, transparency, then weak-head normalisation.
First run traceUnfolding. Predict: numberAlias; number; hiddenNumber; 7.
The operation is always reduceAll: only the unfolding policy changes.
Use the slide's table to predict how much each transparency mode unfolds.
The same expression therefore has different normal forms at different transparencies.
The current hierarchy is none < reducible < instances < implicit < default < all.
Mention the intermediate modes for instance_reducible and implicit_reducible
definitions without adding another example. .all does not expose opaque declarations or axioms.
The All in reduceAll means include implicit arguments, types and proofs;
it does not set TransparencyMode.all. withTransparency changes the ambient policy.
Then run the Both example at default transparency. Both (id P) Q unfolds to
And (id P) Q. Continue past this weak-head normal form with full reduction
to unfold id P to P inside the arguments. P and Q have no value to unfold.
A let-bound variable does have a value that reduction can substitute.
Predict: Both (id P) Q; id P ∧ Q; P ∧ Q; false; true.
WHNF may take several steps; it does not mean one unfolding. A lambda can
be in WHNF while its body still reduces. Both whnf and reduceAll respect transparency.
reduceAll includes types and proofs, which reduce skips by default.
isDefEq does not normally fully normalise both inputs. It reduces as needed
and may assign metavariables to make the terms match. It does not search for
arbitrary equality proofs: equality by a theorem need not be definitional.
Run inferMetavar after the reduction example. The same Nat.succ ?x from 3.2
now matches 8 by assigning x := 7, without an explicit assign call. This is
unification: connect it to the existential witness in 3.1.
Connect reduction to the type comparison in 4.3 and the And match in 5.1.
Source: MPiL 4, Full Normalisation, Transparency, Weak Head Normalisation,
Definitional Equality. traceUnfolding adapts its transparency example.
-/

/- ### 4.2. Normal forms and definitional equality -/

/- The unfolding policy is a parameter that controls which definitions Lean
may unfold when reducing an expression. -/

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

/- Instructor: Spend three minutes revisiting 1.3 here. Follow the wrapper:
lookup h1, infer its type, then whnf exposes Nat.le with two arguments.
app2? checks the head constant and returns its arguments. Nat.le fixes the type
as Nat; require a local variable on the right to match the warmup's scope.
The pattern ignores the lower bound and keeps the variable a.
getUserName and mkIdent recover identifier syntax for the original macro.
The low parser priority keeps the longer "k from h" syntax available.
The lookup and matching code are prefilled; students add the last two lines.
Use this in place of repeating the extra transparency modes. Revisit the input
again in 6.1.1 once term elaboration is available.
-/

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

-- 4.3. Revisit hypothesis: update the goal list and report failure.
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

-- 4.3 checkpoint: replace the two exact steps of 3.1 with our tactic.
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  refine And.intro ?left ?right
  all_goals hypothesis

-- The types are definitionally equal even though the expressions differ.
example (P : Prop) (h : (fun X : Prop => X) P) : P := by
  hypothesis

example : True := by
  fail_if_success hypothesis
  trivial

/-
After assigning the proof, use replaceMainGoal [] to remove the solved goal
while retaining the others. Merely hiding a goal would not
fill its proof hole. assign itself is not a type checker: check the type first.
-/

/- Instructor: 49–62 minutes. 3.1 gave the intended term; now construct it.
Before typing splitAndCore, read @And.intro's type. The complete expression has
four arguments: P, Q, hp, hq. Run the mkAppM inspector, which is given only hp/hq;
it infers P/Q from their types. Relate the resulting application tree to .app in 3.2. No universe arithmetic is needed for this constructor.
Revisit slide 4: creating, assigning, and instantiating metavariables.
5.1 takes an explicit MVarId and changes metavariable assignments in MetaM. It does
not choose the current goal or decide which new goals to display. Explain MetaM
at this use, without a list of all the elaboration monads.
Revisit 4.2: whnf exposes And before target.and? inspects its arguments.
Use test_split to show that and? needs whnf to expose the conjunction in Both (id P) Q.
Temporarily remove whnf to make the need for that line visible.
Inspect the Expr values for p ∧ q and the fresh holes left/right.
Extract the hole identifiers with mvarId!. Name them left/right to match 3.1.
syntheticOpaque marks holes for explicit solution rather than ordinary unification.
mkAppM fills And.intro's implicit proposition arguments. Read its result aloud.
Pause at assign and ask how it connects the fresh holes to the parent proof.
5.2 selects the main goal and updates the work list in TacticM.
5.3 calls the handwritten split_and twice. Temporarily use setGoals instead of
replaceMainGoal in that adapter. The assertion catches
the lost R goal. Even without the assertion, hiding R would leave the proof unfinished.
Restore the adapter. Reverse the returned IDs if students need another state exercise.
Follow three steps in the code: create children, attach them with assign, then
schedule them with replaceMainGoal. The new holes still need proofs after
being attached to the parent. The goal list chooses
which holes to work on next and must retain the pending R.
Print test_split and compare with test_constructor and test_refine.
Source: MPiL 9 exercises 1–2, especially forker; Macbeth Phase1_CoreLogic's explicit
goal-to-subgoals interface; Olšák–Gerbscheid's runConstructor.
Break at minute 62. Keep the explanation of assignments even if later examples slip.
-/

/- ## 5. Create subgoals and connect them to a proof -/

/-
Now automate the refine step of 3.1.
To prove P ∧ Q, construct And.intro ?left ?right.
We must both attach that expression to the old goal and expose the two holes.
This is the proof-term construction hidden by constructor and our warmup macro.
-/

#check mkFreshExprMVar
#check mkAppM
#check Lean.Expr.mvarId!
#check replaceMainGoal

#check @And.intro

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  run_tac withMainContext do
    let hp ← getFVarFromUserName `hp
    let hq ← getFVarFromUserName `hq
    let proof ← mkAppM ``And.intro #[hp, hq]
    logInfo m!"All arguments: {proof.getAppArgs}"
  exact ⟨hp, hq⟩

-- 5.1. Work on the explicit goal, even without a current tactic goal list.
-- MetaM provides expressions, local contexts, and metavariable assignments.
-- Return the new hole identifiers so a caller can decide how to schedule them.
def splitAndCore (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  let target ← whnf (← goal.getType)
  let some (p, q) := target.and?
    | throwError "expected a conjunction"
  let left ← mkFreshExprMVar p .syntheticOpaque (userName := `left)
  let right ← mkFreshExprMVar q .syntheticOpaque (userName := `right)
  let proof ← mkAppM ``And.intro #[left, right]
  goal.assign proof
  return [left.mvarId!, right.mvarId!]

-- 5.2. TacticM connects the explicit-goal operation to the current work list.
elab "split_and" : tactic => do
  let goal ← getMainGoal
  let newGoals ← splitAndCore goal
  replaceMainGoal newGoals

theorem test_split (P Q : Prop) (hp : P) (hq : Q) : Both (id P) Q := by
  run_tac withMainContext do
    let target ← getMainTarget
    logInfo m!"And before reduction: {target.and?.isSome}"
    logInfo m!"And after whnf: {(← whnf target).and?.isSome}"
  split_and
  all_goals hypothesis

#print test_split

-- 5.3. Splitting the first goal must preserve the already pending second goal.
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

/-
A shorter implementation can call goal.apply (mkConst ``And.intro).
The explicit version shows where the new goals come from and how they become
part of the final proof. Macbeth's interval algorithm builds a larger tree
with the same ingredients: fresh goals, a constructor/eliminator, assignment.
-/

/- Instructor: 67–78 minutes. Slide 6, then 6.1's inspector. Context resolves n;
elaboration of n + 1 does not require knowing n's value. This is not evaluation.
Type 6.2. Reuse P ∧ Q, hp, hq: elaborate ⟨hp, hq⟩ instead of building And.intro
with mkAppM. The Int example shows expected-type information for numerals.
This is the focused answer to “how much ElabM?” Say TermElabM when discussing
term syntax. We use Lean.Elab.Tactic.elabTermEnsuringType, whose wrapper completes
synthetic metavariable synthesis. Explain the additional compatibility check
in elabTermEnsuringType using the wrong-type example.
withoutRecover makes failed checks raise errors instead of recovering with placeholders.
closeMainGoal rejects remaining metavariables in our small exact-like tactic.
Lean's built-in exact has more nuanced treatment of pre-existing metavariables.
Run both failure cases: a wrong type and an unresolved underscore.
Defer command elaboration, registrations, postponement, and transformer internals.
If asked, CommandElabM handles commands such as def and #check separately.
The reader needs the capabilities here, not a hierarchy of names. 9 reuses exactTerm.
Sources: MPiL 7, “Term elaboration”; Olšák–Gerbscheid's my_check.
-/

/- ## 6. Just enough elaboration: our own exact -/

/-
Slide 6. There is another way to obtain the proof expression: elaborate syntax.
The text ⟨hp, hq⟩ needs a context to resolve hp and hq, and an expected type
to determine its constructor. Elaborating it produces an Expr.
This is the work of TermElabM. We call it through TacticM's term helpers.
-/

#check Lean.Elab.Tactic.elabTerm
#check Lean.Elab.Tactic.elabTermEnsuringType
#check closeMainGoal

-- 6.1 (supplied). Predict the types before running this inspector.
-- A term argument is syntax. Elaborate it before inspecting its type.
elab "inspect_term " t:term : tactic => withMainContext do
  let e ← elabTerm t none
  logInfo m!"{e} : {← inferType e}"

example (n : Nat) : n = n := by
  inspect_term (n + 1)
  inspect_term (0 : Int)
  rfl

/- Instructor: Spend two minutes wrapping the first revisit in have.
The input is now a proof term. have elaborates it and adds a local hypothesis,
then my_interval_cases reads that hypothesis using 4.2.1 unchanged.
In the example, Nat.le_trans constructs a proof of 1 ≤ k from h1 : 2 ≤ k.
Ask students to predict the new hypothesis's type before running the tactic.
This connects the term-elaboration slide to a familiar tactic quotation.
Continue to exactTerm.
-/

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

-- 6.2. The goal's expected type helps elaborate the proof.
-- The tactic-facing helper also completes synthetic metavariable synthesis.
def exactTerm (stx : Syntax) : TacticM Unit := withoutRecover <| withMainContext do
  let target ← getMainTarget
  let proof ← elabTermEnsuringType stx (some target)
  closeMainGoal `exact_term proof

elab "exact_term " t:term : tactic => exactTerm t

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact_term ⟨hp, hq⟩

-- The same pair notation can instead elaborate to a data constructor.
-- Expected type determines which kind of number the syntax 0 represents.
example : Int := by
  exact_term 0

example : True := by
  fail_if_success exact_term (0 : Nat)
  fail_if_success exact_term _
  exact_term True.intro

/-
Syntax → elaboration with a context and expected type → Expr → kernel checking.
Elaboration is not evaluation: n + 1 can be elaborated without knowing n.
Follow the quoted syntax through evalTactic or elabTerm to the checked proof.
-/

/- # Part 2. Check a sum-of-squares certificate -/

/- Instructor: 78–90 minutes. Use slide 7 for two minutes to introduce SOS.
Ask why the displayed triangle identity proves nonnegativity, then identify the
certificate: weights and polynomial coefficients. Finding these can require
search; checking a proposed answer needs signs and a polynomial identity.
The example previews triangle_nonneg in 7.2. Build up to it from one square.
Start with (x-y)^2. nonnegOfCertificate separates the sign from the identity.
ring checks the polynomial identity; it does not search for the decomposition.
Before 7.2, try rfl on the expanded square: algebraic equality here is not
definitional equality. ring proves it using algebraic laws.
In 7.2, first prove a weighted square nonnegative with mul_nonneg, then combine
it with another square using add_nonneg. These are the steps used by the builder.
Then linear_combination combines the given inequalities and checks the identity.
Later, use it to check the squares and weights found by Python.
Source: Mathlib's linear_combination; leanprover/sos for the search/check design.
-/

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

/- Instructor: 90–97 minutes. Use slide 8 to connect the certificate to external
search and checking. sos_step leaves the two conditions visible.
Reuse split_and, then positivity and ring. Type square_using using exactTerm
from 6.2. ring1 is the finishing version: it fails if the identity is not proved.
Try x+y instead of x-y and observe rejection. The candidate is just data.
-/

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

/- Instructor: 97–105 minutes. Read triangleCertificate as three weighted squares.
Read the rational weights and the leading constant in each affine form.
The syntax-building helpers are supplied. Trace one iteration: form syntax,
sq_nonneg, multiply by a nonnegative weight, then add to the running proof.
The invariant is: proof is syntax for a proof of 0 ≤ the partial weighted sum.
Starting with a proof of 0 ≤ 0, add a nonnegative weighted square on each iteration.
The same structure was written by hand in 7.2; only the number of summands changes.
Students write closeWithSOS: obtain the proof syntax and pass a linear_combination
quotation to exactTerm. The elaborator checks it in the current local context.
mkIdent refers to the existing local names in the run_tac example.
-/

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

/- Instructor: 105–109 minutes. The parser and file wrapper are supplied.
Open triangle-sos.json: it contains only integers, coefficient arrays, and weights.
Parsing establishes the format, not positivity or the polynomial identity.
Follow the types through parseSOS, readSOS, and sos_from. IO.ofExcept converts a parse error to an IO error. The IO action lifts
automatically into TacticM, preserving its result and effects. Recall Week 08's
optional OptionT IO example, without assuming that students completed it.
The file is read during elaboration, not when the finished theorem is used.
Keep this file route as the fallback if Python is unavailable.
-/

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
  let cert ← readSOS path.getString
  closeWithSOS vars.getElems cert

#eval return (← readSOS "Week 10/triangle-sos.json").size

example (x y z : ℝ) : 0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  sos_from "Week 10/triangle-sos.json" [x, y, z]

/- Instructor: 109–115 minutes. The expression reader and process wrapper are supplied.
Follow the boundary: Lean Expr → JSON tree → Python → rational squares → proof syntax.
The Python adapter calls SumOfSquares.py with the CVXOPT solver, then converts
the numerical result to rational squares using SymPy. Open find_sos.py and show
SOSProblem, add_sos_constraint, and solve: these calls reuse existing software.
Our adapter accepts quadratics in at most eight real variables.
It receives rhs-lhs, so the tactic also accepts inequalities such as 2*x*y ≤ x^2+y^2.
We pass only the goal, not hypotheses. No external output is parsed as Lean code.
Type the final three-line tactic, observing the automatic lift of askSOS
from IO into TacticM. Inspect the
printed axioms: no sorryAx. The reader/parser implementation remains a black box;
follow its input and output rather than explaining every syntax and JSON helper.
The numerical solver can fail to produce an exact certificate; Lean checks every result.
Library: https://github.com/yuanchenyang/SumOfSquares.py .
-/

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

/- Instructor: 115–120 minutes. Keep this part even if earlier examples run long.
Run each failure example and identify where it is rejected: parsing, weight
checking, the polynomial identity, or search.
For x^4, search fails because of our degree restriction, although the goal is true.
Edit a weight in the saved certificate and re-elaborate. Then restore it.
Python is an untrusted search tool: even a mistranslated input must produce a
certificate for the original Lean goal. The Python call happens only while
elaborating the proof. A different backend could use numerical search
and rational reconstruction while keeping the same Lean certificate checker.
-/

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
