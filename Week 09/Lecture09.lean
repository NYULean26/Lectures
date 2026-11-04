import Mathlib

/-
Metaprogramming I: Lean under the hood. November 5, 2026.
Open this file independently of Lecture09_Solution.lean.

Heavily inspired by

Metaprogramming in Lean 4 (Apache-2.0) and LoVe 8 (BSD-3-Clause).

The arithmetic type and evaluator use our Week 07–08 notation.
-/

open Lean

namespace Week09

/- # Metaprogramming I: Lean under the hood -/

/- # Part 1. Notation, syntax, and macros -/

/- ## A. Notation -/

/- Infix notation. -/

def andThen (result : Option α) (next : α → Option β) : Option β :=
  match result with
  | none => none
  | some a => next a

#eval andThen (some 3) (fun n => some (n + 1)) -- some 4

section InfixNotation

-- #eval (some 3) ~~> (fun n => some (n + 1)) -- some 4
-- #eval (none : Option Nat) ~~> (fun n => some (n + 1)) -- none

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
/- Precedence and associativity. -/

section LeftAssociative
local infixl:65 " ~ " => Nat.sub
#eval 5 ~ 3 ~ 3 -- 0
-- #guard 5 ~ 3 ~ 3 = (5 - 3) - 3
end LeftAssociative

section RightAssociative
local infixr:65 " ~ " => Nat.sub
#eval 5 ~ 3 ~ 3 -- 5
-- #guard 5 ~ 3 ~ 3 = 5 - (3 - 3)
end RightAssociative

/- The notation command. -/

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

-- #check ℝ≥0
-- example : ℝ≥0 := ⟨0, by norm_num⟩

end GeneralNotation

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
-- #eval (some 3) ~~> (fun n => some (n + 1)) -- some 4
end UsingScopedNotation

-- ANDNOT means l && !r.
section AndNotNotation
local notation:10 l:10 " ANDNOT " r:11 => (l && !r)
-- #guard (true ANDNOT true) = false
-- #guard (true ANDNOT false) = true
-- #guard (false ANDNOT true) = false
-- #guard (false ANDNOT false) = false
end AndNotNotation

/- ## B. Syntax -/

/-
A syntax category describes a kind of Lean input:
  term     1 + 1, Nat, a ∧ b
  command  #check Nat, def n := 3
  tactic   rfl, apply And.intro
-/
namespace AndNot
scoped syntax:10 term:10 " ANDNOT " term:11 : term

#check_failure false ANDNOT true

#check Lean.Syntax

-- The pattern `($l ANDNOT $r) captures the two term subtrees.
-- Return some (l, r) for that pattern, and none otherwise.
def isAndNot : Syntax → Option (Syntax × Syntax) := by
  sorry

-- The same match in tree form.
def isAndNotTree : Syntax → Option (Syntax × Syntax)
  | Syntax.node _ `Week09.AndNot.term_ANDNOT_
      #[l, Syntax.atom _ "ANDNOT", r] => some (l, r)
  | _ => none

def andNotSyntax : Syntax :=
  mkNode `Week09.AndNot.term_ANDNOT_
    #[mkIdent `p, mkAtom "ANDNOT", mkIdent `q]

-- #eval (isAndNot andNotSyntax).isSome -- true
-- #eval (isAndNot (mkIdent `p)).isSome -- false

-- #guard (isAndNot andNotSyntax).isSome
-- #guard (isAndNot (mkIdent `p)).isNone

-- Both versions return the same captured pieces.
-- #guard isAndNotTree andNotSyntax == isAndNot andNotSyntax
-- #guard isAndNotTree (mkIdent `p) == isAndNot (mkIdent `p)

-- TSyntax records the syntax category. It coerces to Syntax.
#check TSyntax `term

end AndNot

/- ## C. Macros -/

namespace AndNot

/-
  p ANDNOT q  →  p && !q
-/

/- Constructing syntax. -/

-- macro_rules pairs a quotation pattern with a replacement quotation.
-- $l and $r insert the captured syntax into the replacement.


-- #guard (true ANDNOT true) = false
-- #guard (true ANDNOT false) = true
-- #guard (false ANDNOT true) = false
-- #guard (false ANDNOT false) = false

-- example (p q : Bool) : (p ANDNOT q) = (p && !q) := rfl

-- NOTAND means !l && r.
scoped syntax:10 term:10 " NOTAND " term:11 : term

-- #guard (true NOTAND true) = false
-- #guard (true NOTAND false) = false
-- #guard (false NOTAND true) = true
-- #guard (false NOTAND false) = false

end AndNot

/- Syntax and expansion together. -/

namespace CombinedAndNot

-- macro combines the syntax declaration and the expansion.
scoped macro:10 l:term:10 " ANDNOT " r:term:11 : term =>
  `($l && !$r)

-- #guard (true ANDNOT true) = false
-- #guard (true ANDNOT false) = true
-- #guard (false ANDNOT true) = false
-- #guard (false ANDNOT false) = false

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

-- #eval (x ↦ x + 2) 2 -- 4
-- #eval (s ↦ s.length) "Lean" -- 4

end FunctionNotation

/- # Part 2. Arithmetic expressions and tactics -/

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
  | `(⟪ ($a:arith) ⟫) => `(⟪ $a ⟫)

#eval (⟪ "x" + 2 ⟫ : Expr String)
-- #eval (⟪ ("x" + 2) * "y" ⟫ : Expr String).eval values -- 16

/- ## E. A small example -/

-- The supplied x keeps its original binding.
namespace Hygiene
macro "const" e:term : term => `(fun x => $e)
def x : Nat := 42
#eval (const x) 10 -- 42
end Hygiene

/- ## F. Tactic combinators and a tactic macro -/

example : 1 = 1 ∧ 2 = 2 := by
  apply And.intro
  all_goals rfl

-- all_goals rfl runs rfl on both goals.
-- `(tactic| ...) quotes tactic syntax.

-- a and_then b runs a, then b on every resulting goal.
syntax tactic " and_then " tactic : tactic

theorem test_and_then : 1 = 1 ∧ 2 = 2 := by
  sorry

-- #print test_and_then
-- #print axioms test_and_then


/- ## G. Conjunctions -/

-- Introduce every top-level conjunction.
example (a b c d : Prop) (ha : a) (hb : b) (hc : c) (hd : d) :
    a ∧ (b ∧ c) ∧ d := by
  repeat' apply And.intro
  all_goals assumption

-- intro_and abbreviates repeat' apply And.intro.
-- repeat' apply And.intro leaves goals a, b, c, and d.
-- assumption closes each using its corresponding hypothesis.

example (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) : b ∧ d := by
  sorry

-- solve_and combines intro_and with all_goals assumption.

theorem test_solve_and (a b c : Prop) (ha : a) (hb : b) (hc : c) :
    b ∧ (a ∧ (c ∧ b)) := by
  sorry

-- #print axioms test_solve_and

example (a b : Prop) (h : a ∧ b) : b ∧ a := by
  sorry

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


example (a b : Prop) (ha : a) (hb : b) : a ∧ b := by
  trace_goals
  apply And.intro
  all_goals assumption


def trace : TacticM Unit := withMainContext do
  let lctx ← getLCtx
  for ldecl in lctx do
    logInfo m!"{ldecl.userName} : {ldecl.type}"


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

/- ### Finding a hypothesis -/

open Lean.Meta


def hypothesis : TacticM Unit := sorry

-- run_tac executes the function in the current proof state.
-- example (a : Prop) (ha : a) : a := by
--  run_tac hypothesis



-- A macro can instead expand to run_tac hypothesis.
macro "hypothesis_macro" : tactic => `(tactic| run_tac hypothesis)

-- example (a : Prop) (ha : a) : a := by
--  hypothesis_macro

/-
hypothesis_macro  →  run_tac hypothesis  →  execute hypothesis
                 macro expansion         tactic elaboration

-/

-- elab gives the function its own tactic syntax.
elab "hypothesis" : tactic => hypothesis

--example (a : Prop) (ha : a) : a := by
--   hypothesis

/- ## I. Conjunctions in the hypotheses -/

-- isAppOfArity ``And 2 recognizes a type of the form And a b.
#check Lean.Expr.isAppOfArity
#check LocalDecl.fvarId

-- goal.cases ldecl.fvarId returns an array of resulting subgoals.
#check MVarId.cases
-- Each subgoal has a .mvarId field for the list passed to replaceMainGoal.
#check replaceMainGoal

-- Split conjunctions in the hypotheses, including nested ones.
-- After replacing the main goal, restart the scan in the new context.
-- When no conjunction remains, return successfully.
-- ``And resolves the declaration name; here it equals `And, since And is in the root namespace.
partial def expandAnd : TacticM Unit := by
  sorry

elab "expand_and" : tactic => expandAnd

example (a b : Prop) (h : a ∧ b) : b ∧ a := by
  sorry

example (a b c d : Prop) (h₁ : a ∧ (b ∧ c)) (h₂ : d ∧ a) :
    b ∧ (d ∧ c) := by
  sorry

end Week09
