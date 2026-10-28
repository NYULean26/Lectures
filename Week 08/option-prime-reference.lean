import Mathlib

inductive Option' (α : Type) where
  | none : Option' α
  | some : α → Option' α
  deriving Repr

namespace Option'

-- Functor

instance : Functor Option' where
  map f
    | .none => .none
    | .some a => .some (f a)

instance : LawfulFunctor Option' where
  map_const := rfl
  id_map x := by cases x <;> rfl
  comp_map g h x := by cases x <;> rfl

-- Applicative: retain this map and Lean's default seqLeft / seqRight.

instance : Applicative Option' where
  toFunctor := inferInstance
  pure := .some
  seq f arg := match f with
    | .none => .none
    | .some g => g <$> arg ()

#check Nat.add <$> some 3 -- Option' (Nat → Nat)
#eval Nat.add <$> some 3 <*> some 4 -- some 7
#eval Nat.add <$> some 3 <*> none   -- none
#eval Nat.add <$> none   <*> some 4 -- none

instance : LawfulApplicative Option' where
  toLawfulFunctor := inferInstance
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  map_pure _ _ := rfl
  seq_pure f x := by cases f <;> rfl
  seq_assoc x g h := by cases h <;> cases g <;> cases x <;> rfl

-- Equivalent usual applicative laws.

theorem applicative_identity (x : Option' α) : pure id <*> x = x :=
  pure_id_seq x

theorem applicative_composition
    (u : Option' (β → γ)) (v : Option' (α → β)) (w : Option' α) :
    pure (fun f g => f ∘ g) <*> u <*> v <*> w = u <*> (v <*> w) := by
  simpa only [pure_seq] using (seq_assoc w v u).symm

theorem applicative_pure_application (f : α → β) (x : α) :
    (pure f <*> pure x : Option' β) = pure (f x) := by
  rw [pure_seq, map_pure]

theorem applicative_interchange (u : Option' (α → β)) (x : α) :
    u <*> pure x = pure (fun f => f x) <*> u := by
  rw [seq_pure, pure_seq]

-- Monad: retain the applicative above.

instance : Monad Option' where
  toApplicative := inferInstance
  bind x next := match x with
    | .none => .none
    | .some a => next a

instance : LawfulMonad Option' where
  toLawfulApplicative := inferInstance
  bind_pure_comp f x := by cases x <;> rfl
  bind_map f x := by cases f <;> rfl
  pure_bind _ _ := rfl
  bind_assoc x f g := by cases x <;> rfl

-- Right identity is a theorem derived from the class fields.

theorem monad_right_identity (x : Option' α) : x >>= pure = x :=
  bind_pure x

end Option'
