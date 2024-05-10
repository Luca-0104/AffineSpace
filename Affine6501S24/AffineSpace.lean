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
| ⟨ l1, pl1 ⟩, ⟨ l2, pl2 ⟩ =>
  ⟨
    (List.zipWith (. - .) l1 l2),
    by
    rw [List.length_zipWith, pl1, pl2]
    apply min_eq_left
    exact Nat.le_refl n
  ⟩

-- def vsub_Aff : AffPoint K n → AffPoint K n → AffVector K n
-- | ⟨ l1, pl1 ⟩, ⟨ l2, pl2 ⟩ =>
--   ⟨
--     (List.zipWith (. - .) l1 l2),
--     sorry
--   ⟩


instance : VSub (AffVector K n) (AffPoint K n) :=  { vsub := vsub_Aff n}




/-!
## Check the constractor of each instance we need to define to get an AddTorsor
  To implament an AddTorsor
  We need to define the following instances
-/

#check AddTorsor.mk
/-!
AddTorsor.mk.{u_2, u_1}
  {G : outParam (Type u_1)}
  {P : Type u_2}
  [inst✝ : outParam (AddGroup G)]
  [toAddAction : AddAction G P]
  [toVSub : VSub G P]
  [nonempty : Nonempty P]
  (vsub_vadd' : ∀ (p₁ p₂ : P), p₁ -ᵥ p₂ +ᵥ p₂ = p₁)
  (vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g) :
AddTorsor G P
-/

#check AddGroup.mk
/-!
AddGroup.mk.{u}
  {A : Type u}
  [toSubNegMonoid : SubNegMonoid A]
  (add_left_neg : ∀ (a : A), -a + a = 0) :
AddGroup A
-/

#check SubNegMonoid.mk
/-!
SubNegMonoid.mk.{u}
  {G : Type u}
  [toAddMonoid : AddMonoid G]
  [toNeg : Neg G]
  [toSub : Sub G]
  (sub_eq_add_neg : ∀ (a b : G), a - b = a + -b := by intros; rfl)
  (zsmul : ℤ → G → G)
  (zsmul_zero' : ∀ (a : G), zsmul 0 a = 0 := by intros; rfl)
  (zsmul_succ' : ∀ (n : ℕ) (a : G), zsmul (Int.ofNat (Nat.succ n)) a = zsmul (Int.ofNat n) a + a := by intros; rfl)
  (zsmul_neg' : ∀ (n : ℕ) (a : G), zsmul (Int.negSucc n) a = -zsmul (↑(Nat.succ n)) a := by intros; rfl) :
SubNegMonoid G
-/

#check AddMonoid.mk
/-!
AddMonoid.mk.{u}
  {M : Type u}
  [toAddSemigroup : AddSemigroup M]
  [toZero : Zero M]
  (zero_add : ∀ (a : M), 0 + a = a)
  (add_zero : ∀ (a : M), a + 0 = a)
  (nsmul : ℕ → M → M)
  (nsmul_zero : ∀ (x : M), nsmul 0 x = 0 := by intros; rfl)
  (nsmul_succ : ∀ (n : ℕ)
  (x : M), nsmul (n + 1) x = nsmul n x + x := by intros; rfl) :
AddMonoid M
-/


#check AddSemigroup.mk
/-!
AddSemigroup.mk.{u}
  {G : Type u}
  [toAdd : Add G]
  (add_assoc : ∀ (a b c : G), a + b + c = a + (b + c)) :
AddSemigroup G
-/

#check Zero.mk
/-!
Zero.mk.{u}
  {α : Type u}
  (zero : α) :
Zero α
-/

#check Neg.mk
/-!
Neg.mk.{u}
  {α : Type u}
  (neg : α → α) :
Neg α
-/

#check Sub.mk
/-!
Sub.mk.{u}
  {α : Type u}
  (sub : α → α → α) :
Sub α
-/

#check AddAction.mk
/-!
AddAction.mk.{u_11, u_10}
  {G : Type u_10}
  {P : Type u_11}
  [inst✝ : AddMonoid G]
  [toVAdd : VAdd G P]
  (zero_vadd : ∀ (p : P), 0 +ᵥ p = p)
  (add_vadd : ∀ (g₁ g₂ : G) (p : P), g₁ + g₂ +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)) :
AddAction G P
-/

#check VAdd.mk
/-!
VAdd.mk.{u, v}
  {G : Type u}
  {P : Type v}
  (vadd : G → P → P) :
VAdd G P
-/

#check VSub.mk
/-!
VSub.mk.{u_2, u_1}
  {G : outParam (Type u_1)}
  {P : Type u_2}
  (vsub : P → P → G) :
VSub G P
-/

#check Nonempty
/-!
Nonempty.{u}
  (α : Sort u) :
Prop
-/


/-!
## Implment the required instances above for getting an AddTorsor
-/

/-!
## VAdd
  vector + point -> point
-/
def vadd_Aff : AffVector K n → AffPoint K n → AffPoint K n
| ⟨ l1, pl1 ⟩, ⟨ l2, pl2 ⟩ => ⟨ (List.zipWith (. + .) l1 l2),
    by
      have plen : List.length (List.zipWith (. + .) l1 l2) = n :=
      by
        rw [List.length_zipWith, pl1, pl2]
        apply min_eq_left
        exact Nat.le_refl n
      exact plen
 ⟩

-- def vadd_Aff : AffVector K n → AffPoint K n → AffPoint K n
-- | ⟨ l1, pl1 ⟩, ⟨ l2, pl2 ⟩ => ⟨ (List.zipWith (. + .) l1 l2),
--     sorry
--  ⟩

instance : VAdd (AffVector K n) (AffPoint K n) := { vadd := vadd_Aff n }


-- define several AffPoint and AffVector for testing
-- def P : AffPoint Rat 3 := ⟨ ⟨[1/2, -1/3, 1], by simp⟩ ⟩
-- def v : AffVector Rat 3 := ⟨ ⟨[1/3, 5/4, -3], by simp⟩ ⟩
-- def w : AffVector Rat 3 := ⟨ ⟨[-1/6, 2/3, 7/5], by simp⟩ ⟩

-- -- testint the vadd_Aff
-- #eval toString (v +ᵥ P)           -- (Pt [5/6, 11/12, -2])
-- #eval toString (w +ᵥ (v +ᵥ P))    -- (Pt [2/3, 19/12, -3/5])




/-!
## Add
  vector + vector -> vector
-/
def add_affine_vector : AffVector K n → AffVector K n → AffVector K n
| ⟨ l1, pl1 ⟩, ⟨ l2, pl2 ⟩ => ⟨ (List.zipWith (. + .) l1 l2),
  by
    have plen : List.length (List.zipWith (. + .) l1 l2) = n :=
    by
      rw [List.length_zipWith, pl1, pl2]
      apply min_eq_left
      exact Nat.le_refl n
    exact plen
 ⟩

instance : Add (AffVector K n) := { add := add_affine_vector n }

-- -- testint the add_affine_vector
-- #eval toString ((v +ᵥ w))       -- (Vc [1/6, 23/12, -8/5])
-- #eval toString ((v + w) +ᵥ P)   -- (Pt [2/3, 19/12, -3/5])




/-!
## Zero
-/
#check Zero.mk
/-!
Zero.mk.{u}
  {α : Type u}
  (zero : α) :
Zero α
-/
def zero_affine_vector : AffVector K n := ⟨ ⟨ List.replicate n 0, by simp [List.length_replicate] ⟩ ⟩

instance : Zero (AffVector K n) := ⟨ zero_affine_vector n ⟩

#check (0 : (AffVector K n))
-- #eval toString (v + 0) -- (Vc [1/3, 5/4, -3])
-- #eval toString (0 + v) -- (Vc [1/3, 5/4, -3])




/-!
## AddSemigroup
-/
#check AddSemigroup.mk
/-!
AddSemigroup.mk.{u}
  {G : Type u}
  [toAdd : Add G]
  (add_assoc : ∀ (a b c : G), a + b + c = a + (b + c)) :
AddSemigroup G
-/

-- a proof of add_assoc with a concise tactic script
-- theorem aff_add_assoc : ∀ (n : Nat) (a b c : (AffVector K n)), a + b + c = a + (b + c) :=
-- by
--   induction n with
--   | zero => rfl
--   | succ m ih =>
--     exact ih

-- theorem aff_add_assoc : ∀ (n : Nat) (a b c : (AffVector K n)), a + b + c = a + (b + c) :=
-- by
--   intros n a b c
--   induction n with
--   | zero => repeat { rfl }
--   | succ m ih => repeat { rfl }

-- theorem aff_add_assoc (a b c : (AffVector K n)) : a + b + c = a + (b + c)
-- | zero => by simp [add_affine_vector]
-- | succ n => by simp [add_affine_vector, zero_add]

-- theorem aff_add_assoc (a b c : AffVector K n): add_affine_vector n (add_affine_vector n a b) c =  add_affine_vector n a (add_affine_vector n b c)
-- | zero => by simp [add_affine_vector]
-- | succ n => by simp [add_affine_vector, zero_add]

-- theorem aff_add_assoc : ∀ (a b c : (AffVector K n)), a + b + c = a + (b + c) :=
--   match a, b, c with
--   | ⟨ l₁, h1 ⟩, ⟨ l₂, h2 ⟩, ⟨ l₃, h3 ⟩ =>
--     by
--     have plen : a + b + c = a + (b + c) :=
--     by
--       rw [List.length_zipWith, h1, h2, h3]
--       apply min_eq_left
--       exact Nat.le_refl n
--     exact plen

instance : AddSemigroup (AffVector K n) := {
  add_assoc := sorry
}




/-!
## AddMonoid
-/
#check AddMonoid.mk
/-!
AddMonoid.mk.{u}
  {M : Type u}
  [toAddSemigroup : AddSemigroup M]
  [toZero : Zero M]
  (zero_add : ∀ (a : M), 0 + a = a)
  (add_zero : ∀ (a : M), a + 0 = a)
  (nsmul : ℕ → M → M)
  (nsmul_zero : ∀ (x : M), nsmul 0 x = 0 := by intros; rfl)
  (nsmul_succ : ∀ (n : ℕ)
  (x : M), nsmul (n + 1) x = nsmul n x + x := by intros; rfl) :
AddMonoid M
-/
def affine_vector_nsmul : ℕ → (AffVector K n) → (AffVector K n)
| 0,      _ => ⟨ ⟨ List.replicate n 0, by simp [List.length_replicate] ⟩ ⟩
| (n+1),  v => v + (affine_vector_nsmul n v)

-- open AffVector

-- theorem aff_zero_add : ∀ (a : (AffVector K n)), 0 + a = a
-- | zero => rfl
-- | succ a => congrArg succ (zero_add a)

-- theorem aff_add_zero (a : (AffVector K n)) : a + 0 = a := rfl

-- theorem aff_zero_add : ∀ (a : (AffVector K n)), add_affine_vector n a zero = a
--   | zero   => by simp [add_affine_vector]
--   | succ a => by simp [add_affine_vector n, aff_zero_add]

instance : AddMonoid (AffVector K n) := {
  zero_add := sorry
  add_zero := sorry
  nsmul:= affine_vector_nsmul n
  nsmul_zero:= sorry
  nsmul_succ:=sorry
}

-- #eval toString (3 • w)      -- (Vc [-1/2, 2, 21/5])
-- #eval toString (0 • w)      -- (Vc [0, 0, 0])
-- #eval toString (0 + w)      -- (Vc [-1/6, 2/3, 7/5])
-- #eval toString (w + 0)      -- (Vc [-1/6, 2/3, 7/5])




/-!
## AddAction
-/
#check AddAction.mk
/-!
AddAction.mk.{u_11, u_10}
  {G : Type u_10}
  {P : Type u_11}
  [inst✝ : AddMonoid G]
  [toVAdd : VAdd G P]
  (zero_vadd : ∀ (p : P), 0 +ᵥ p = p)
  (add_vadd : ∀ (g₁ g₂ : G) (p : P), g₁ + g₂ +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)) :
AddAction G P
-/
instance : AddAction (AffVector K n) (AffPoint K n) := {
  zero_vadd := sorry,
  add_vadd := sorry
}

-- #eval ((2 • v) + (3 • w) + (0 • v)) +ᵥ P  -- (Pt [2/3, 25/6, -4/5])




/-!
## Neg
-/
#check Neg.mk
/-!
Neg.mk.{u}
  {α : Type u}
  (neg : α → α) :
Neg α
-/
def neg_affine_vector : AffVector K n → AffVector K n
| ⟨ l, pl ⟩ => ⟨ (List.map (fun x => -x) l),
  by
    have h₁ : List.length (List.map (fun x => -x) l) = List.length l :=
    by
      rw [List.length_map]
    exact Eq.trans h₁ pl
 ⟩

instance : Neg (AffVector K n) := { neg := neg_affine_vector n }

-- #eval toString (-w)           -- (Vc [1/6, -2/3, -7/5])




/-!
## Sub
-/
#check Sub.mk
/-!
Sub.mk.{u}
  {α : Type u}
  (sub : α → α → α) :
Sub α
-/
instance : Sub (AffVector K n) := { sub := fun v w => v + (-w) }

-- #eval toString (v - w)          -- (Vc [1/2, 7/12, -22/5])
-- #eval toString ((v - w) +ᵥ P)   -- (Pt [1, 1/4, -17/5])
-- #eval toString (v - 0)          -- (Vc [1/3, 5/4, -3])




/-!
## SubNegMonoid
-/
#check SubNegMonoid.mk
/-!
SubNegMonoid.mk.{u}
  {G : Type u}
  [toAddMonoid : AddMonoid G]
  [toNeg : Neg G]
  [toSub : Sub G]
  (sub_eq_add_neg : ∀ (a b : G), a - b = a + -b := by intros; rfl)
  (zsmul : ℤ → G → G)
  (zsmul_zero' : ∀ (a : G), zsmul 0 a = 0 := by intros; rfl)
  (zsmul_succ' : ∀ (n : ℕ) (a : G), zsmul (Int.ofNat (Nat.succ n)) a = zsmul (Int.ofNat n) a + a := by intros; rfl)
  (zsmul_neg' : ∀ (n : ℕ) (a : G), zsmul (Int.negSucc n) a = -zsmul (↑(Nat.succ n)) a := by intros; rfl) :
SubNegMonoid G
-/
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
/-!
AddGroup.mk.{u}
  {A : Type u}
  [toSubNegMonoid : SubNegMonoid A]
  (add_left_neg : ∀ (a : A), -a + a = 0) :
AddGroup A
-/
instance : AddGroup (AffVector K n) := {
  add_left_neg := sorry
}

-- #eval toString (w)        -- (Vc [-1/6, 2/3, 7/5])
-- #eval toString (-4 • w)   -- (Vc [2/3, -8/3, -28/5])
-- #eval toString (-4 • w + 3 • v -5 • w)   -- (Vc [5/2, -9/4, -108/5])




/-!
## Nonempty
-/
#check Nonempty
/-!
Nonempty.{u}
  (α : Sort u) :
Prop
-/
instance : Nonempty (AffPoint K n) := ⟨ ⟨ List.replicate n 0, by simp [List.length_replicate] ⟩ ⟩




/-!
## AddTorsor
-/
#check AddTorsor.mk
/-!
AddTorsor.mk.{u_2, u_1}
  {G : outParam (Type u_1)}
  {P : Type u_2}
  [inst✝ : outParam (AddGroup G)]
  [toAddAction : AddAction G P]
  [toVSub : VSub G P]
  [nonempty : Nonempty P]
  (vsub_vadd' : ∀ (p₁ p₂ : P), p₁ -ᵥ p₂ +ᵥ p₂ = p₁)
  (vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g) :
AddTorsor G P
-/
-- #eval P -ᵥ P +ᵥ P

instance : AddTorsor (AffVector K n) (AffPoint K n) :=
{
  vsub_vadd' := sorry
  vadd_vsub' := sorry
}

-- #eval (v + (P -ᵥ P)) +ᵥ P  -- (Pt [5/6, 11/12, -2])
