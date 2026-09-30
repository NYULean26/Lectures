import Mathlib

universe u

/-
# Structures

Lean has an convenient way to store lists of information
(i.e. Σ-types) as structures, where we can name the fields.
-/

structure NatPoint where
  x : Nat
  y : Nat

-- This is equivalent to ℕ × ℕ but with named accessors.

-- A structure is an inductive type with one constructor.
inductive NatPoint2 where
  | mk : Nat → Nat → NatPoint2

#print NatPoint

-- It comes with a built in constructor
#check NatPoint.mk

-- And an eliminator
#check NatPoint.rec

-- As well as the expected projectors
#check NatPoint.x

#check NatPoint.mk 2 3

def p :=  NatPoint.mk 2 3


/-
## Convenience constructions

Structures come with a lot of conveniences.

### Projections/Methods
For an element `e` of type `T`, Lean automatically turns
`e.method` into `T.method e`.

-/

#eval p.x -- this is the same as NatPoint.x p


def NatPoint.addCoords (p : NatPoint) : Nat := sorry
#reduce p.addCoords

def NatPoint2.addCoords (p : NatPoint2) : Nat := sorry


/-
The `NatPoint.addCoords` is, in Lean, stored as `addCoords` inside of the namespace `NatPoint`
-/

namespace NatPoint -- We enter the NatPoint namespace

#check addCoords

-- Aside: Writing "namespace" opens the namespace in "editing" mode, everyting
-- you write now gets encoded there

def add (p q : NatPoint) : NatPoint := by
  sorry


end NatPoint

def NatPoint.double (p : NatPoint) : NatPoint := by
  sorry

#reduce p.double

/-
### Equality of structures
-/

-- Go back and add @[ext] above NatPoint to generate the extensionality lemma.
-- #check NatPoint.ext

-- To show that two points are equal, compare their coordinates.
theorem NatPoint.add_comm (p q : NatPoint) : p.add q = q.add p := by
  sorry


/-
### A zoo of constructors

Lean offers more ways to construct points than you would need.

-/


#check {x:=2, y:=4 :NatPoint}

def r := NatPoint.double {x:= 2, y:=3}

#reduce r

def q : NatPoint where
  x := 7
  y := 5


#check (⟨5,6⟩ : NatPoint)


-- There is a `with` keyword to modify a pre-existing structure.



-- Structures can have parameters, like everything else in Lean.

structure Point (T : Type u) where
  x : T
  y : T

#check Point.mk -- notice anything weird?


def mypoint := Point.mk (2:Nat) 3

#check mypoint


/-
We can use structures to store algebraic data.
A semigroup is a type with an associative operation.
-/
structure Semigroup' where
  carrier : Type


/-
## Extending structures
-/


inductive Color where
  | red | green | blue


-- We can define new structures by extending
-- previous structues.
structure CPoint (α : Type u) extends Point α where
  c : Color

-- You can create a `CPoint` from scratch, and using with to extend `p`

-- we can use the _with_ to extend
#check ({p with c:=Color.red } : CPoint _ )

-- We can extend two structures at the same time!

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RGBPoint (α : Type u) extends Point α, RGBValue

def origin := {x:=0, y:=0 : Point Nat}


-- Let's create a RGPoint structure which is an RGBPoint with no blue


/-
We can _layer_ definitions using `extends`.

Define a `monoid` to be a semigroup with unit, and a group
to be a monoid with inverse.
-/




-- # Classes: The problem we are trying to solve

-- We want to store that a type α has an adition operation.
structure HasAddition (α : Type u) where
  add : α → α → α


def double {α : Type u} (s : HasAddition α) (x : α) := s.add x x

-- Now we can use this to store `HasAddition` in a structure
-- that records that points have addition to use the generic `double`

-- Problem: we must pass the `HasAddition` all the time.
-- Solution: Record it automatically!

-- ## Our first typeclass

class AddType (α : Type) where
  add : α → α → α

instance PointsHaveAddition' : AddType (Point Nat) where
  add :=  sorry

def double_typeclass {α : Type} [AddType α] (a : α) :α
  := by sorry

#reduce double_typeclass (Point.mk 1 2)

-- What did Lean fill in for us?
#check @double_typeclass
#synth AddType (Point Nat)
#check (inferInstance : AddType (Point Nat))

-- Fill out @double_typeclass by hand


-- Lean implements this class, it's called `Add`
-- The `+` notation is syntactic sugar on top of HAdd.hAdd;



-- ## The power of parametrized typeclasses

instance PointAdd (α : Type u) [Add α] : Add (Point α) where
  add := by sorry

def t : Point Nat := {x:=2, y:=2}

-- You can tell Lean "If A is add and B is add, A×B is add"
instance Product_add (α : Type) (β : Type) [Add α] [Add β] : Add ((Point α)×(Point β)) where
  add := by
    sorry

-- Think about what Lean is doing!
#reduce (t,t)+(t,t)



-- # The integers

variable (n : Nat) (z : Int)

@[ext]
structure Integer where
  negative : Bool --
  abs : Nat
  no_dupl : ¬(negative ∧ (abs = 0)) -- We don't want 0  and -0

-- We compare the data, not the proofs of no_dupl.
example (a b : Integer) (hs : a.negative = b.negative) (ha : a.abs = b.abs) :
    a = b := by
  sorry

instance : OfNat Integer n where
  ofNat := { abs := n, negative := False, no_dupl := by grind}


#reduce (2 : Integer)

instance : ToString Integer where
  toString r := if r.negative then s!"-{r.abs}"else s!"{r.abs}"


#eval (2 : Integer)


instance : Neg Integer where
  neg F := by
    sorry


-- What tactic should I use?
-- 1. If the proof is "very tedious application of logical rules", use grind
-- 2. If the proof is transitivity + chaining of inequalities use gcongr
-- 3. If you want to bring things to a "normal form" use simp

instance : PartialOrder Integer where
  le x y := ((x.negative ∧ (¬ y.negative))∨
            ((¬ x.negative) ∧ (¬ y.negative) ∧ (x.abs ≤ y.abs))∨
            (x.negative ∧ y.negative ∧ (y.abs ≤ x.abs)))
  le_antisymm := by
    sorry

  le_refl := by
    sorry
  le_trans := by
    sorry



-- ## When should I use classes vs structures?

#print Semigroup
#print Semigroup'


-- ## Dependency hyerarchies

-- same as before.

class Group'' (A : Type) extends Semigroup A, Inv A where
  e : A
  left_e : ∀ (a:A), e*a = a
  right_e : ∀ (a:A), a*e = a
  inv_is_inv: ∀ a:A, a⁻¹*a = e

-- ### Dependency Hyerarchies go deep:
-- The whole hierarchy of Algebra, quite literally
-- https://github.com/leanprover-community/mathlib4/blob/a19486351878a13e2737bf5a838468e244624787/Mathlib/Algebra/Ring/Defs.lean#L142-L143


-- ## Some recurring typeclasses

-- OfNat: numeric literals; ToString: strings; Repr: printing values with #eval.
-- Inhabited: a default value; BEq: a Boolean equality test.
-- DecidableEq: an equality test carrying a proof of its answer.

/-
### Coercions
-/

-- Coe: use a value of one type where another is expected.
instance (α : Type) : Coe (Point α) (α × α) where
  coe a := by
    sorry

#check (t : Nat × Nat)

-- The @[coe] tag is for the pretty-printer; it does not register an instance.
@[coe]
def toProduct {α : Type} (a : Point α) : (α × α) := (a.x, a.y)

-- CoeSort: use a structure as a type.
instance : CoeSort Semigroup' Type where
  coe S := S.carrier

example (S : Semigroup') (a : S) : S.carrier := a

-- CoeFun: use a structure as a function.
-- A morphism of semigroups is a function preserving multiplication.
structure Morphism (S T : Semigroup') where
  toFun : S → T
  -- Add the condition that toFun preserves multiplication.

instance (S T : Semigroup') : CoeFun (Morphism S T) (fun _ => S → T) where
  coe f := by sorry

example (S T : Semigroup') (f : Morphism S T) (a : S) : T := f a

/-
### Decidable propositions
-/

#print Decidable
#check Decidable.isTrue
#check Decidable.isFalse

-- Decidable P comes with two constructors, either .isTrue or .isFalse.

def chooseIf (P : Prop) [h : Decidable P] (a b : Nat) : Nat := sorry

-- This is what `if P then a else b` does.
#reduce chooseIf (2 < 3) 10 20

/-
### Deriving instances
-/

-- Lean can generate some instances for us: Repr for printing, DecidableEq for equality.
-- Go back and add `deriving Repr, DecidableEq` below the constructors of Color.
-- #synth DecidableEq Color
-- #eval if Color.red = Color.blue then 10 else 20

-- We can also use the computation to prove something.
example : Color.red ≠ Color.blue := by
  sorry

#check Classical.propDecidable
-- Classical reasoning supplies decisions too, but not an executable test.
