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


def NatPoint.addCoords (p : NatPoint) : Nat := p.x + p.y

#eval p.addCoords

/-
The `NatPoint.addCoords` is, in Lean, stored as `addCoords` inside of the namespace `NatPoint`
-/

namespace NatPoint -- We enter the NatPoint namespace

#check addCoords

-- Aside: Writing "namespace" opens the namespace in "editing" mode, everyting
-- you write now gets engoded there

def add (p q : NatPoint) : NatPoint := by
  sorry


end NatPoint

def NatPoint.double (p : NatPoint) : NatPoint := by
  sorry

#reduce p.double


/-
### Constructors

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

def q2 := {q with x := 0}

#reduce q2

-- One can define _dependent_ structures like everything else in Lean.

structure Point (T : Type u) where
  x : T
  y : T

def mypoint := Point.mk (2:Nat) 3

#check mypoint


/-
We use structures to store algebraic data
-/
structure Semigroup' where
  carrier : Type
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)


/-
## Extending structures
-/


inductive Color where
  | red | green | blue


-- We can define new structures by extending
-- previous structues.
structure CPoint (α : Type u) extends Point α where
  c : Color

#check ({x:=2, y:=3, c:=Color.red } : CPoint _ )

-- we can use the _with_ to extend
#check ({p with c:=Color.red } : CPoint _ )

-- We can extend two structures at the same time!

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RGBPoint (α : Type u) extends Point α, RGBValue

def origin := {x:=0, y:=0 : Point Nat}

def yelloworigin : RGBPoint Nat :=
  {origin with red :=255, green := 255, blue := 0}

structure RGPoint (α : Type u) extends RGBPoint α where
  noBlue : (blue = 0)

def noblueorigin : RGPoint Nat := {yelloworigin with noBlue := by rfl }

/-
We can _layer_ definitions using `extends`.
-/
structure Group' extends Semigroup' where
  e : carrier
  e_prop: (∀ g : carrier, mul e g = g)
  inv : carrier → carrier
  inv_is : (∀ g : carrier, mul (inv g) g = e)



-- # Classes: The problem we are trying to solve

-- We want to store that a type α has an adition operation.
structure HasAddition (α : Type u) where
  add : α → α → α

def double {α : Type u} (s : HasAddition α) (x : α) := s.add x x


def PointsHaveAddition : HasAddition (Point Nat) where
  add : (Point Nat → Point Nat → Point Nat) :=
    by sorry

#reduce double (PointsHaveAddition) (Point.mk 1 2)

-- Problem: we must record the typeclass all the time.

-- ## Our first typeclass

class AddType (α : Type) where
  add : α → α → α

instance PointsHaveAddition' : AddType (Point Nat) where
  add :=  PointsHaveAddition.add

def double_typeclass {α : Type} [AddType α] (a : α) :α
  := by sorry

#reduce double_typeclass (Point.mk 1 2)

-- Lean implements this class, it's called `Add`
-- Lean implements the `+` notation as syntactic sugar for Add.add


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

structure Integer where
  negative : Bool --
  abs : Nat
  no_dupl : ¬(negative ∧ (abs = 0)) -- We don't want 0  and -0

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
-- 3. If it "should be obvious" but uses complicated lemas use aesop
-- 4. If you want to bring things to a "normal form" use simp

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

-- ## Should I use classes or records?

#print Semigroup
#print Semigroup'


-- ## Dependency hyerarchies

class Group'' (A : Type) extends Semigroup A, Inv A where
  e : A
  left_e : ∀ (a:A), e*a = a
  right_e : ∀ (a:A), a*e = a
  inv_is_inv: ∀ a:A, a⁻¹*a = e

-- ### Dependency Hyerarchies go deep:
-- The whole hierarchy of Algebra, quite literally
-- https://github.com/leanprover-community/mathlib4/blob/a19486351878a13e2737bf5a838468e244624787/Mathlib/Algebra/Ring/Defs.lean#L142-L143


-- ## Some recurring typeclasses

-- ### Coercion
-- There is a type class called Coe which records "Things that can be coerced into"
instance (α : Type) : Coe (Point α) (α × α) where
  coe a := by
    sorry

#check (t : Nat × Nat)


-- There is also a @[coe] tag whichgenerates the instance.
@[coe]
def toProduct {α : Type} (a : Point α) : (α × α ) := (a.x, a.y)
