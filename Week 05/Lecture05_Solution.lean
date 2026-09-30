import Mathlib

universe u

/-
# Structures

Lean has an convenient way to store lists of information
(i.e. Σ-types) as structures, where we can name the fields.
-/

@[ext]
structure NatPoint where
  x : Nat
  y : Nat

-- This is equivalent to ℕ × ℕ but with named accessors.

-- A structure is an inductive type with one constructor.
inductive NatPoint' where
  | mk : Nat → Nat → NatPoint'

-- Structures also generate the projections and the record syntax for us.
#print NatPoint

def NatPoint'.addCoords (p : NatPoint') : Nat :=
  match p with
  | .mk x y => x + y

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

def add (p q : NatPoint) :=  NatPoint.mk (p.x+q.x) (p.y+q.y)


end NatPoint

def NatPoint.double (p : NatPoint) :=  p.add p

#reduce p.double

/-
### Equality of structures
-/

#check NatPoint.ext

-- To show that two points are equal, compare their coordinates.
theorem NatPoint.add_comm (p q : NatPoint) : p.add q = q.add p := by
  ext <;> simp [NatPoint.add, Nat.add_comm]

-- `ext` leaves one goal for x and one for y. Each is commutativity in Nat.


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

-- Structures can have parameters, like everything else in Lean.

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
  deriving Repr, DecidableEq


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

-- An operation is not a law: HasAddition does not say that addition is associative.
#check Semigroup'.mul_assoc
-- In Semigroup', associativity is a separate field containing a proof.

def double {α : Type u} (s : HasAddition α) (x : α) := s.add x x


def PointsHaveAddition : HasAddition (Point Nat) where
  add : (Point Nat → Point Nat → Point Nat) :=
    fun a b ↦ {x:=a.x+b.x, y:= a.y+b.y}

#reduce double (PointsHaveAddition) (Point.mk 1 2)

-- Problem: we must record the typeclass all the time.

-- ## Our first typeclass

class AddType (α : Type) where
  add : α → α → α

instance PointsHaveAddition' : AddType (Point Nat) where
  add :=  PointsHaveAddition.add

def double_typeclass {α : Type} [AddType α] (a : α) :α
  := AddType.add a a

#reduce double_typeclass (Point.mk 1 2)

-- What did Lean fill in for us?
#check @double_typeclass
#synth AddType (Point Nat)

#reduce @double_typeclass (Point Nat) PointsHaveAddition' (Point.mk 1 2)

-- [AddType α] is an argument, just like the record we passed to double.
-- Lean searches for a registered instance and supplies it for us.

-- Lean implements this class, it's called `Add`
-- The `+` notation uses HAdd.hAdd; an Add instance supplies the usual case.


-- ## The power of parametrized typeclasses

instance PointAdd (α : Type u) [Add α] : Add (Point α) where
  add :=  fun a b ↦ {x:=a.x+b.x, y:= a.y+b.y}

def t : Point Nat := {x:=2, y:=2}

-- You can tell Lean "If A is add and B is add, A×B is add"
instance Product_add (α : Type) (β : Type) [Add α] [Add β] : Add ((Point α)×(Point β))  where add :=
  fun (a1,a2) (b1,b2) ↦ ⟨⟨a1.x+b1.x, a1.y+b1.y⟩,⟨a2.x+b2.x, a2.y+b2.y⟩⟩

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
  ext
  · exact hs
  · exact ha

-- Once the data agree, the proof fields prove the same proposition.
-- Proof irrelevance means they cannot distinguish the two integers.

instance : OfNat Integer n where
  ofNat := { abs := n, negative := False, no_dupl := by grind}


#reduce (2 : Integer)

instance : ToString Integer where
  toString r := if r.negative then s!"-{r.abs}"else s!"{r.abs}"


#eval (2 : Integer)


instance : Neg Integer where
  neg F :=  match F with
  | ⟨_,0,_⟩ => ⟨False, 0, by aesop⟩
  | ⟨s,a+1,_⟩ => ⟨!s, a+1, by simp⟩

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
                 intro ⟨s1,a1, p1⟩ ⟨s2, a2,p2⟩
                 simp
                 grind

  le_refl := by
              intro ⟨s,a,b⟩
              simp
  le_trans := by
              intro ⟨s1,a1, p1⟩ ⟨s2, a2,p2⟩ ⟨s3, a3,p3⟩
              simp
              grind

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

/-
### Decidable propositions
-/

#print Decidable
#check Decidable.isTrue
#check Decidable.isFalse

-- A decision is data: either a proof of P, or a proof of ¬ P.
-- Decidable P lives in Type, not Prop. We can inspect its constructor
-- to decide which branch of a program to run.

def chooseIf (P : Prop) [h : Decidable P] (a b : Nat) : Nat :=
  match h with
  | .isTrue _ => a
  | .isFalse _ => b

-- This is what `if P then a else b` does.
#eval chooseIf (2 < 3) 10 20

-- The `deriving DecidableEq` on Color generated a decision procedure.
#synth DecidableEq Color
#eval if Color.red = Color.blue then 10 else 20

-- We can also use the computation to prove something.
example : Color.red ≠ Color.blue := by
  decide

#check Classical.propDecidable
-- Classical reasoning supplies decisions too, but not an executable test.
-- P ∨ ¬ P is a proposition; Decidable P is data choosing a branch.
-- Classical.propDecidable uses choice to cross this gap and is noncomputable.
-- In contrast, the instance derived for Color computes by comparing constructors.

-- ### Coercion
-- There is a type class called Coe which records "Things that can be coerced into"
instance (α : Type) : Coe (Point α) (α × α) where
  coe a := (a.x, a.y)

#check (t : Nat × Nat)


-- The @[coe] tag helps the pretty-printer recognize a coercion; it does not register an instance.
@[coe]
def toProduct {α : Type} (a : Point α) : (α × α ) := (a.x, a.y)
