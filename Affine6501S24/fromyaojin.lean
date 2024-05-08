import Std.Data.Rat.Basic         --https://leanprover-community.github.io/mathlib4_docs/Std/Data/Rat/Basic.html#Rat
import Mathlib.Algebra.Field.Defs --https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Field/Defs.html#Field
import Mathlib.Algebra.AddTorsor
import Mathlib.Data.Vector        --https://github.com/leanprover-community/mathlib4/blob/a7ed535af2a1f78accefeaeee98233dd25714110/Mathlib/Data/Vector.lean#L20-L21




section k_affine_n


universe u
variable
  {K : Type u}  -- implicit type argument
  [Field K]     -- with an implementation of the Field typeclass
  (n : Nat)     -- the dimension of the space
  [ToString K]  -- so that we can more easily print tuples of K values


/-!
## POINT uniquely identified by n-tuple of values from a field K
-/


/-!
Note on the Vector type in Lean. Instance of this type do NOT
(necessarily) represent vectors in any sort of mathematical space
other than being fixed-length lists of values of some types.


def Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }


The notation on the second line is Lean's subtype notation. This
example defines the type of all List α values, l, whose length is
exactly n. A value of this type is a *dependent pair*, comprising
an List α value, l, and a proof that l.length = n.


A better name for this type would have been Tuple, but we're stuck
with Vector. We'll pick names that don'e conflict when we get to
defining mathematical vectors very shortly. For now the key idea
is that we can use Vector objects as representations of points and
vectors in n-dimensional (affine) spaces.
-/




/-!
We thus now have this notion of the type of n-tuples of K values,
where K is a field, and thus provides *, /, + -, etc., all of which
have been proven to behave in the expected ways (* distributes over
+, etc.).


Now we define our affine point and affine vector (as distict
from Lean Vector) types. Here we commit to the idea that the
scalar field from which tuple elements are drawn, and dimension
of an n-K-tuple, are parts of its *type*. Then when we define
operations that only make sense for, saw two same dimensional
vectors, we'll get type errors if we make mistakes like that.
-/


-- Implemented as list with a proof of length n


#check Vector K n   -- type of n-tuples of values from K represented as a list


instance : ToString (Vector K n) where
  toString : (Vector K n) -> String
    | ⟨ l, _ ⟩  => s!"{l}"     -- {} matching notation, string interpolation


def testVector : Vector Nat 3 := ⟨ [1, 2, 4], by simp ⟩


def testToString : String := toString testVector


#eval testToString


structure AffPoint (K : Type u) [Field K] (n : Nat) where
  rep : Vector K n


instance : ToString (AffPoint K n) where
  toString : (AffPoint K n) -> String
    | ⟨ l ⟩   => s!"(Pt {l})"     -- {} matching notation, string interpolation




structure AffVector (K : Type u) [Field K] (n : Nat) where
  rep : Vector K n


instance : ToString (AffVector K n) where
  toString : (AffVector K n) -> String
    | ⟨ l ⟩    => s!"(Vc {l})"      -- {} matching notation, string interpolation


#check Repr
/-!
By representing n-K-tuples as length-n lists, we can use all
of the machiner of Lean's mathlib for working with lists to
implement our point-point subtraction affine space operator
abstraction.
-/


/-!
In our earlier work we overloaded the VSub typeclass,
by providing an implementation of (vsub : P → P → G),
where P is AffinePoint and G is AffineVector. Thereafter,
point-point subtraction will be denoted as `-ᵥ`.


class VSub (G : outParam (Type*)) (P : Type*) where
  vsub : P → P → G
-/


def vsub_Aff : AffPoint K n → AffPoint K n → AffVector K n
| ⟨ l1, _ ⟩, ⟨ l2, _ ⟩ =>
  ⟨
    (List.zipWith (. - .) l1 l2),
   sorry
  ⟩


instance : VSub (AffVector K n) (AffPoint K n) :=  { vsub := vsub_Aff n}


/-!
## AddSemigroup
-/


def vadd_Aff : AffVector K n → AffPoint K n → AffPoint K n
| ⟨ l1, _ ⟩, ⟨ l2, _ ⟩ => ⟨ (List.zipWith (.+.) l1 l2), sorry ⟩


instance : VAdd (AffVector K n) (AffPoint K n) :=
{
vadd := vadd_Aff n
}


def P : AffPoint Rat 3 := ⟨ ⟨[1/2, -1/3, 1], by simp⟩ ⟩
def v : AffVector Rat 3 := ⟨ ⟨[1/3, 5/4, -3], by simp⟩ ⟩
def w : AffVector Rat 3 := ⟨ ⟨[-1/6, 2/3, 7/5], by simp⟩ ⟩
#eval toString (v +ᵥ P)           -- (Pt [5/6, 11/12, -2])
#eval toString (w +ᵥ (v +ᵥ P))    -- (Pt [2/3, 19/12, -3/5])


def add_affine_vector : AffVector K n → AffVector K n → AffVector K n
| ⟨ l1, _ ⟩, ⟨ l2, _ ⟩ => ⟨ (List.zipWith (.+.) l1 l2), sorry ⟩


instance : Add (AffVector K n) := { add := add_affine_vector n }


#eval toString ((v + w) +ᵥ P)   -- (Pt [2/3, 19/12, -3/5])




def zero_affine_vector : AffVector K n := ⟨ ⟨ List.replicate n 0, by simp [List.length_replicate] ⟩ ⟩
instance : Zero (AffVector K n) := ⟨ zero_affine_vector n ⟩
-- def zero_affine_point : AffPoint K n := ⟨ ⟨ List.replicate n 0, by simp [List.length_replicate] ⟩ ⟩
-- instance : Zero (AffPoint K n) := ⟨ zero_affine_point n ⟩
#check (0 : (AffVector K n))
#eval toString (v + 0) -- (Vc [1/3, 5/4, -3])
#eval toString (0 + v) -- (Vc [1/3, 5/4, -3])


#check AddSemigroup.mk


instance : AddSemigroup (AffVector K n) := {
  add_assoc := sorry
}


/-!
## AddMonoid
-/


#check AddMonoid.mk


def affine_vector_nsmul : ℕ → (AffVector K n) → (AffVector K n)
| 0,      _ => ⟨ ⟨ List.replicate n 0, by simp [List.length_replicate] ⟩ ⟩
| (n+1),  v => v + (affine_vector_nsmul n v)




instance : AddMonoid (AffVector K n) := {
  zero_add := sorry
  add_zero := sorry
  nsmul:= affine_vector_nsmul n
  nsmul_zero:= sorry
  nsmul_succ:=sorry
}


#eval toString (3 • w)      -- (Vc [-1/2, 2, 21/5])
#eval toString (0 • w)      -- (Vc [0, 0, 0])
#eval toString (0 + w)      -- (Vc [-1/6, 2/3, 7/5])
#eval toString (w + 0)      -- (Vc [-1/6, 2/3, 7/5])


/-!
## AddAction
-/


instance : AddAction (AffVector K n) (AffPoint K n) := {
    zero_vadd := sorry,
    add_vadd := sorry
  }


#eval ((2 • v) + (3 • w) + (0 • v)) +ᵥ P  -- (Pt [2/3, 25/6, -4/5])


/-!
## SubNegMonoid
-/


#check SubNegMonoid.mk


def neg_affine_vector : AffVector K n → AffVector K n
| ⟨ l, _ ⟩ => ⟨ (List.map (fun x => -x) l), sorry ⟩


instance : Neg (AffVector K n) := { neg := neg_affine_vector n }


#eval toString (-w)           -- (Vc [1/6, -2/3, -7/5])


instance : Sub (AffVector K n) := { sub := fun v w => v + (-w) }


#eval toString (v - w)          -- (Vc [1/2, 7/12, -22/5])
#eval toString ((v - w) +ᵥ P)   -- (Pt [1, 1/4, -17/5])
#eval toString (v - 0)          -- (Vc [1/3, 5/4, -3])




def affine_vector_zsmul : ℤ → (AffVector K n) → (AffVector K n)
| (Int.ofNat n), r => n • r
| (Int.negSucc n), r => -((n+1) • r)




instance : SubNegMonoid (AffVector K n) := {
  sub_eq_add_neg := sorry,
  zsmul:=affine_vector_zsmul n,
  zsmul_zero' := sorry,
  zsmul_succ' := sorry,
  zsmul_neg' := sorry
}


/-!
## AddGroup
-/




#check AddGroup.mk


instance : AddGroup (AffVector K n) := {
  add_left_neg := sorry
}


#eval toString (w)        -- (Vc [-1/6, 2/3, 7/5])
#eval toString (-4 • w)   -- (Vc [2/3, -8/3, -28/5])
#eval toString (-4 • w + 3 • v -5 • w)   -- (Vc [5/2, -9/4, -108/5])


/-!
## AddTorsor
-/


#check AddTorsor.mk


instance : Nonempty (AffPoint K n) := ⟨ ⟨ List.replicate n 0, by simp [List.length_replicate] ⟩ ⟩


#eval P -ᵥ P +ᵥ P


instance : AddTorsor (AffVector K n) (AffPoint K n) :=
{
  vsub_vadd' := sorry
  vadd_vsub' := sorry
}


#eval (v + (P -ᵥ P)) +ᵥ P  -- (Pt [5/6, 11/12, -2])
