import Mathlib

/-
Metaprogramming I: Lean under the hood. November 5, 2026.
Instructor copy. Open independently of the student and solution files.

Heavily inspired by

Metaprogramming in Lean 4 (Apache-2.0) and LoVe 8 (BSD-3-Clause).

The arithmetic type and evaluator use our Week 07–08 notation.
-/

open Lean

namespace Week09

/- # Metaprogramming I: Lean under the hood -/

-- Instructor: frames 1–3, then move between the notation slides and A.
-- Recall our arithmetic trees before introducing Lean's own syntax.

/- MPiL, Overview (frames 2–3)
https://leanprover-community.github.io/lean4-metaprogramming-book/main/02_overview.html
Source text → Syntax → macro expansion → term elaboration → Lean.Expr.
Expansion can produce further macros. The kernel checks completed declarations,
including their types and proof terms. Command elaboration can also add declarations.
-/

/- # Part 1. Notation, syntax, and macros -/

/- ## A. Notation -/

-- Instructor: keep the annotated infix slide visible while adding ~~>.
-- Reuse andThen from Week 07; the new ingredient is its notation.

/- Infix notation. -/

def andThen (result : Option α) (next : α → Option β) : Option β :=
  match result with
  | none => none
  | some a => next a

#eval andThen (some 3) (fun n => some (n + 1)) -- some 4

section InfixNotation

local infixl:55 " ~~> " => andThen

#eval (some 3) ~~> (fun n => some (n + 1)) -- some 4
#eval (none : Option Nat) ~~> (fun n => some (n + 1)) -- none

end InfixNotation

/-
Prefix, infix, and postfix notation.
Lean's familiar operators use the same declarations:
infixl:65 " + " => HAdd.hAdd  -- associates to the left;
infixr:80 " ^ " => HPow.hPow -- associates to the right.
infix:50 " = " => Eq -- needs parentheses.
prefix:100 "-" => Neg.neg
postfix:max "⁻¹" => Inv.inv
The notation `+` uses HAdd.hAdd (same with HMul...)
-/
/- Infix from notation (frame 7)
For notation:p a:l " ~ " b:r => f a b, l and r are the minimum precedences
accepted for the arguments. Higher binds tighter. The three choices are:
  infixl:p   p, p,   p+1
  infixr:p   p, p+1, p
  infix:p    p, p+1, p+1
Parentheses permit either grouping. Use the two subtraction examples below.
-/

/- Precedence and associativity. -/

section LeftAssociative
local infixl:65 " ~ " => Nat.sub
#eval 5 ~ 3 ~ 3 -- 0
#guard 5 ~ 3 ~ 3 = (5 - 3) - 3
end LeftAssociative

section RightAssociative
local infixr:65 " ~ " => Nat.sub
#eval 5 ~ 3 ~ 3 -- 5
#guard 5 ~ 3 ~ 3 = 5 - (3 - 3)
end RightAssociative

/- The notation command. -/

/- Notation (frames 5–6)
The quoted delimiters and comma are literal tokens. x and y are arguments
reused in the replacement. Here the whole notation has precedence max (1024),
and each argument defaults to min (0), so x + y can occur inside the brackets.
The second version on the slides makes these defaults explicit.
-/

section GeneralNotation

-- notation lets us put arguments between several literal tokens.
local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

#check fun (x y : E) => ⟪x, y⟫

example (x y : E) : ⟪x, y⟫ = inner ℝ x y := rfl

example (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  inner_add_left x y z

-- Notation can also have no arguments.
-- Recall the type of nonnegative real numbers from Week 03.
local notation "ℝ≥0" => {x : Real // 0 ≤ x}

#check ℝ≥0
example : ℝ≥0 := ⟨0, by norm_num⟩

end GeneralNotation

/- MPiL 5, Syntax
https://leanprover-community.github.io/lean4-metaprogramming-book/main/05_syntax.html
The set-builder example introduces a binder in the expansion: fun x => p.
Use the parenthesized typed binder below to make the type explicit.
-/

/- Set-builder notation. -/
namespace SetBuilderNotation

-- The basic "all elements such that" function for the notation.
def setOf {α : Type} (p : α → Prop) : Set α := Set.ofPred p

local notation "{ " x " | " p " }" => setOf (fun x => p)

#check { (x : Nat) | x ≤ 1 }

example : { (x : Nat) | x ≤ 1 } = setOf (fun (x : Nat) => x ≤ 1) := rfl

example : 1 ∈ { (y : Nat) | y ≤ 1 } := by
  change 1 ≤ 1
  decide

example : 2 ∈ { (y : Nat) | y ≤ 3 ∧ 1 ≤ y } := by
  change 2 ≤ 3 ∧ 1 ≤ 2
  decide

end SetBuilderNotation

/- Local and scoped notation. -/

-- local notation ends with the section or namespace containing it.
-- scoped notation can be enabled again by opening its namespace's scope.
namespace OptionNotation
scoped infixl:55 " ~~> " => andThen
end OptionNotation

section UsingScopedNotation
open scoped OptionNotation
#eval (some 3) ~~> (fun n => some (n + 1)) -- some 4
end UsingScopedNotation

-- ANDNOT means l && !r.
section AndNotNotation
local notation:10 l:10 " ANDNOT " r:11 => (l && !r)
#guard (true ANDNOT true) = false
#guard (true ANDNOT false) = true
#guard (false ANDNOT true) = false
#guard (false ANDNOT false) = false
end AndNotNotation

/- ## B. Syntax -/

/-
A syntax category describes a kind of Lean input:
  term     1 + 1, Nat, a ∧ b
  command  #check Nat, def n := 3
  tactic   rfl, apply And.intro
-/
-- Instructor: frames 8–11. Declare syntax, then try the failing #check.
-- Start with isAndNot and unfold its pattern into isAndNotTree.
-- Keep the expansion rule for section C.

/- MPiL 5, Operating on Syntax (frames 9–11)
The quotation pattern captures the two term subtrees as l and r.
The simplified Syntax on the slide has missing, node, atom, and ident.
A node carries a rule kind and children; the ANDNOT token is an atom.
Identifiers carry names, such as p or Nat.add. During elaboration an identifier
can refer to a local variable or a global declaration, or introduce a binder.
Lean's actual constructors also retain source and name-resolution information.
-/

namespace AndNot
scoped syntax:10 term:10 " ANDNOT " term:11 : term

#check_failure false ANDNOT true

#check Lean.Syntax

-- We can pattern-match syntax.
def isAndNot : Syntax → Option (Syntax × Syntax)
  | `($l ANDNOT $r) => some (l, r)
  | _ => none

-- The same match in tree form.
def isAndNotTree : Syntax → Option (Syntax × Syntax)
  | Syntax.node _ `Week09.AndNot.term_ANDNOT_
      #[l, Syntax.atom _ "ANDNOT", r] => some (l, r)
  | _ => none

def andNotSyntax : Syntax :=
  mkNode `Week09.AndNot.term_ANDNOT_
    #[mkIdent `p, mkAtom "ANDNOT", mkIdent `q]

#eval (isAndNot andNotSyntax).isSome -- true
#eval (isAndNot (mkIdent `p)).isSome -- false

#guard (isAndNot andNotSyntax).isSome
#guard (isAndNot (mkIdent `p)).isNone

-- Both versions return the same captured pieces.
#guard isAndNotTree andNotSyntax == isAndNot andNotSyntax
#guard isAndNotTree (mkIdent `p) == isAndNot (mkIdent `p)

-- Instructor: `term is a Name identifying the syntax category.
-- TSyntax `term wraps syntax with that category recorded in its type.

-- TSyntax records the syntax category. It coerces to Syntax.
#check TSyntax `term

end AndNot

/- MPiL 6, Macros (frames 12–13)
https://leanprover-community.github.io/lean4-metaprogramming-book/main/06_macros.html
The syntax declaration from B makes the quotation in macro_rules parsable.
Its pattern is the one used by isAndNot. The right-hand quotation builds the
replacement, inserting the captured subtrees at $l and $r.
Further macro expansion processes any macros in that replacement.
-/

-- Instructor: compare syntax + macro_rules, macro, and A's notation.
-- infixl expands to notation, which supplies syntax and macro expansion.
-- NOTAND and the untyped function variant can be skipped if time is short.

/- ## C. Macros -/

namespace AndNot

/-
  p ANDNOT q  →  p && !q
-/

/- Constructing syntax. -/

macro_rules
  | `($l ANDNOT $r) => `($l && !$r)

#guard (true ANDNOT true) = false
#guard (true ANDNOT false) = true
#guard (false ANDNOT true) = false
#guard (false ANDNOT false) = false

example (p q : Bool) : (p ANDNOT q) = (p && !q) := rfl

-- NOTAND means !l && r.
scoped syntax:10 term:10 " NOTAND " term:11 : term
macro_rules
  | `($l NOTAND $r) => `(!$l && $r)

#guard (true NOTAND true) = false
#guard (true NOTAND false) = false
#guard (false NOTAND true) = true
#guard (false NOTAND false) = false

end AndNot

/- Syntax and expansion together. -/

namespace CombinedAndNot

-- macro combines the syntax declaration and the expansion.
scoped macro:10 l:term:10 " ANDNOT " r:term:11 : term =>
  `($l && !$r)

#guard (true ANDNOT true) = false
#guard (true ANDNOT false) = true
#guard (false ANDNOT true) = false
#guard (false ANDNOT false) = false

example (p q : Bool) : (p ANDNOT q) = (p && !q) := rfl

end CombinedAndNot

/-
infixl is a command macro. It expands to notation:
  local infixl:55 " ~~> " => andThen
  local notation:55 a:55 " ~~> " f:56 => andThen a f
-/

/- Function notation. -/
namespace FunctionNotation

macro x:ident ":" t:term " ↦ " body:term : term =>
  `(fun $x : $t => $body)

#eval (x : Nat ↦ x + 2) 2 -- 4
example : (x : Nat ↦ x + 2) = (fun x : Nat => x + 2) := rfl

macro x:ident " ↦ " body:term : term =>
  `(fun $x => $body)

#eval (x ↦ x + 2) 2 -- 4
#eval (s ↦ s.length) "Lean" -- 4

end FunctionNotation

/- # Part 2. Arithmetic expressions and tactics -/

/- MPiL 1 and 5, a small arithmetic language (frame 14)
https://leanprover-community.github.io/lean4-metaprogramming-book/main/01_intro.html
Recall the course's Expr constructors and evaluator. arith is a new syntax
category embedded into term by the outer brackets. Each macro expansion
produces Lean code for an Expr constructor. Nested brackets in the replacement
allow the same rules to handle the remaining arithmetic subtrees.
-/

-- Instructor: add minus and times beside plus in the existing rules.
-- Use the two evals after the rules; the assignment gives x = 6 and y = 2.

/- ## D. Arithmetic expressions again -/

-- Integer constants and variables indexed by α.
inductive Operation where
  | plus | minus | times
  deriving Repr

inductive Expr (α : Type) where
  | const : ℤ → Expr α
  | var : α → Expr α
  | prim : Operation → Expr α → Expr α → Expr α
  deriving Repr

instance : Add (Expr α) where add := Expr.prim .plus
instance : Sub (Expr α) where sub := Expr.prim .minus
instance : Mul (Expr α) where mul := Expr.prim .times
instance (n : Nat) : OfNat (Expr α) n where ofNat := Expr.const n

def Operation.eval (op : Operation) (a b : ℤ) : ℤ :=
  match op with
  | .plus => a + b
  | .minus => a - b
  | .times => a * b

def Expr.eval (e : Expr α) (values : α → ℤ) : ℤ :=
  match e with
  | .const n => n
  | .var x => values x
  | .prim op a b => op.eval (a.eval values) (b.eval values)

def values : String → ℤ
  | "x" => 6
  | "y" => 2
  | _ => 0

def x : Expr String := .var "x"
def y : Expr String := .var "y"

#eval ((x + 2) * y).eval values -- 16

/-
The arithmetic language has numbers, strings, +, -, *, and parentheses.
The strings "x" and "y" denote variables.
-/

declare_syntax_cat arith
syntax num : arith
syntax str : arith
syntax:50 arith:50 " + " arith:51 : arith
syntax:50 arith:50 " - " arith:51 : arith
syntax:60 arith:60 " * " arith:61 : arith
syntax "(" arith ")" : arith
syntax "⟪" arith "⟫" : term

-- These rules construct Lean syntax for the constructors of Expr.
macro_rules
  | `(⟪ $n:num ⟫) => `(Expr.const $n)
  | `(⟪ $s:str ⟫) => `(Expr.var $s)
  | `(⟪ $a:arith + $b:arith ⟫) => `(Expr.prim .plus ⟪ $a ⟫ ⟪ $b ⟫)
  | `(⟪ $a:arith - $b:arith ⟫) => `(Expr.prim .minus ⟪ $a ⟫ ⟪ $b ⟫)
  | `(⟪ $a:arith * $b:arith ⟫) => `(Expr.prim .times ⟪ $a ⟫ ⟪ $b ⟫)
  | `(⟪ ($a:arith) ⟫) => `(⟪ $a ⟫)

#eval (⟪ "x" + 2 ⟫ : Expr String)
#eval (⟪ ("x" + 2) * "y" ⟫ : Expr String).eval values -- 16

-- Instructor: optional. The inserted x retains its original binding.
-- Keep hygiene to this example.

/- ## E. A small example -/

-- The supplied x keeps its original binding.
namespace Hygiene
macro "const" e:term : term => `(fun x => $e)
def x : Nat := 42
#eval (const x) 10 -- 42
end Hygiene

/- MPiL 9, Tactics (frame 15)
https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html
Applying And.intro leaves two goals, each with its own local context.
The final proof is a pair of proofs of the two conjuncts. Use #print to inspect it.
The explicit tactic category in `(tactic| ...) selects the quotation parser.
-/

/- ## F. Tactic combinators and a tactic macro -/

example : 1 = 1 ∧ 2 = 2 := by
  apply And.intro
  all_goals rfl

-- all_goals rfl runs rfl on both goals.
-- `(tactic| ...) quotes tactic syntax.

-- a and_then b runs a, then b on every resulting goal.
syntax tactic " and_then " tactic : tactic

macro_rules
  | `(tactic| $a:tactic and_then $b:tactic) =>
      `(tactic| $a:tactic; all_goals $b:tactic)

theorem test_and_then : 1 = 1 ∧ 2 = 2 := by
  apply And.intro and_then rfl

#print test_and_then
#print axioms test_and_then


-- Instructor: follow LoVe 8's conjunction combinators.
-- Leave the final h : a ∧ b example visible: it motivates expanding hypotheses.
-- Its context contains h, while assumption needs proofs of the individual conjuncts.

/- ## G. Conjunctions -/

-- Introduce every top-level conjunction.
example (a b c d : Prop) (ha : a) (hb : b) (hc : c) (hd : d) :
    a ∧ (b ∧ c) ∧ d := by
  repeat' apply And.intro
  all_goals assumption

-- repeat' apply And.intro leaves goals a, b, c, and d.
-- assumption closes each using its corresponding hypothesis.

macro "intro_and" : tactic =>
  `(tactic| repeat' apply And.intro)

example (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : b ∧ d := by
  intro_and
  · exact h.2.1.1
  · exact h.2.2

-- Split conjunctions, then close each goal by assumption.
macro "solve_and" : tactic =>
  `(tactic| (intro_and; all_goals assumption))

theorem test_solve_and (a b c : Prop) (ha : a) (hb : b) (hc : c) :
    b ∧ (a ∧ (c ∧ b)) := by
  solve_and

#print axioms test_solve_and

example (a b : Prop) (h : a ∧ b) : b ∧ a := by
  fail_if_success solve_and
  exact ⟨h.2, h.1⟩

/- LoVe 8, The Metaprogramming Monads (frames 16–17)
https://github.com/lean-forward/logical_verification_2026/blob/460f6be0846eefc3d9441e4e48d75753fcfe1709/lean/LoVe/LoVe08_Metaprogramming_Demo.lean
TacticM α is a computation with access to the proof state, errors, and logging,
returning a value of type α. Tactics usually return Unit. Familiar do notation
still applies. withMainContext selects the main goal's local context.
getMainGoal returns its metavariable identifier; getMainTarget returns its type.
getGoals reads the goal list; getUnsolvedGoals filters out goals already assigned.
-/

-- Instructor: first run_tac traceGoals, then the trace_goals wrapper.
-- Continue with trace to inspect the local declarations.
-- In splitAndSolve, evalTactic executes quoted tactic syntax inside TacticM.
-- Stop after tracing if needed; hypothesis and expandAnd can continue next time.

/- ## H. Looking at a goal -/

open Lean.Elab.Tactic

-- Read the proof state.
def traceGoals : TacticM Unit := withMainContext do
  let goals ← getUnsolvedGoals
  logInfo m!"Number of goals: {goals.length}"
  let target ← getMainTarget
  logInfo m!"First goal's target: {target}"

-- run_tac executes a Lean computation in the current proof state.
set_option linter.unusedTactic false in
example (a b : Prop) (ha : a) (hb : b) : a ∧ b := by
  run_tac traceGoals
  apply And.intro
  all_goals assumption

#check getMainTarget
#check traceGoals

macro "trace_goals" : tactic =>
  `(tactic| run_tac traceGoals)

set_option linter.unusedTactic false in
example (a b : Prop) (ha : a) (hb : b) : a ∧ b := by
  trace_goals
  apply And.intro
  all_goals assumption

def trace : TacticM Unit := withMainContext do
  let lctx ← getLCtx
  for ldecl in lctx do
    logInfo m!"{ldecl.userName} : {ldecl.type}"

set_option linter.unusedTactic false in
example (a b : Prop) (h : a ∧ b) : b ∧ a := by
  run_tac trace
  exact ⟨h.2, h.1⟩

-- Run tactic syntax from TacticM.
def splitAndSolve : TacticM Unit := do
  evalTactic (← `(tactic| apply And.intro))
  traceGoals
  evalTactic (← `(tactic| all_goals assumption))

example (a b : Prop) (ha : a) (hb : b) : a ∧ b := by
  run_tac splitAndSolve

-- Instructor: LoVe's assumption tactic compares types using isDefEq.
-- On a match, assigning the hypothesis as a proof solves the goal.
-- The filter skips declarations marked as implementation details.
-- elab registers execution under a tactic name. The macro wrapper expands
-- to run_tac, which executes the same computation during tactic elaboration.

/- ### Finding a hypothesis -/

open Lean.Meta

-- LoVe's hypothesis tactic.
def hypothesis : TacticM Unit := withMainContext do
  let target ← getMainTarget
  let lctx ← getLCtx
  for ldecl in lctx do
    if !ldecl.isImplementationDetail then
      let eq ← isDefEq ldecl.type target
      if eq then
        let goal ← getMainGoal
        goal.assign ldecl.toExpr
        return
  failure

-- run_tac executes the function in the current proof state.
example (a : Prop) (ha : a) : a := by
  run_tac hypothesis

-- elab gives the function its own tactic syntax.
elab "hypothesis" : tactic => hypothesis

example (a : Prop) (ha : a) : a := by
  hypothesis

-- A macro can instead expand to run_tac hypothesis.
macro "hypothesis_macro" : tactic => `(tactic| run_tac hypothesis)

example (a : Prop) (ha : a) : a := by
  hypothesis_macro

/-
hypothesis_macro  →  run_tac hypothesis  →  execute hypothesis
                 macro expansion         tactic elaboration

-/

/- LoVe 8, exercise 1.2, adapted from casesAnd
The application And a b has two arguments; isAppOfArity recognizes that shape.
cases splits the chosen hypothesis and returns the resulting goals.
Replace the main goal, then restart the scan in its updated context.
The old local context is stale after the split. With no conjunction left,
expandAnd succeeds, and solve_and can use the resulting hypotheses.
-/

-- Instructor: return to G's failed example, then try the nested version.

/- ## I. Conjunctions in the hypotheses -/

-- ``And resolves the declaration name; here it equals `And, since And is in the root namespace.
partial def expandAnd : TacticM Unit := withMainContext do
  let lctx ← getLCtx
  for ldecl in lctx do
    if !ldecl.isImplementationDetail && ldecl.type.isAppOfArity ``And 2 then
      let goal ← getMainGoal
      let subgoals ← goal.cases ldecl.fvarId
      replaceMainGoal (subgoals.toList.map (·.mvarId))
      expandAnd
      return

elab "expand_and" : tactic => expandAnd

example (a b : Prop) (h : a ∧ b) : b ∧ a := by
  expand_and
  solve_and

example (a b c d : Prop) (h₁ : a ∧ (b ∧ c)) (h₂ : d ∧ a) :
    b ∧ (d ∧ c) := by
  expand_and
  solve_and

end Week09

