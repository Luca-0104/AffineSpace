import «Affine6501S24».AffineSpace
import Std.Data.Rat.Basic         --https://leanprover-community.github.io/mathlib4_docs/Std/Data/Rat/Basic.html#Rat
import Mathlib.Algebra.Field.Defs --https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Field/Defs.html#Field
import Mathlib.Algebra.AddTorsor
import Mathlib.Data.Vector        --https://github.com/leanprover-community/mathlib4/blob/a7ed535af2a1f78accefeaeee98233dd25714110/Mathlib/Data/Vector.lean#L20-L21

-- Define some ℚ n-tuples
def t1 : Vector ℚ 3 := ⟨ [0, (1/2:ℚ), 2], rfl ⟩
def t2 : Vector ℚ 3 := ⟨ [2, (-1/2:ℚ), -2], rfl ⟩

-- see tuple toString delegate to List toString
#eval s!"{t1}"


-- Define some rational affine 3-points
def p1 : AffPoint ℚ 3  := ⟨ t1 ⟩
def p2 : AffPoint ℚ 3  := ⟨ t2 ⟩

-- AffPt toString
#eval s!"{p1}"
def v2 := p2 -ᵥ p1

#eval s!"{v2}"


#check ToString (AffPoint ℚ 3)



-- define several AffPoint and AffVector for testing
def P : AffPoint Rat 3 := ⟨ ⟨[1/2, -1/3, 1], rfl⟩ ⟩
def P2 : AffPoint Rat 3 := ⟨ ⟨[1/2, -1/6, 3], rfl⟩ ⟩
def v : AffVector Rat 3 := ⟨ ⟨[1/3, 5/4, -3], rfl⟩ ⟩
def w : AffVector Rat 3 := ⟨ ⟨[-1/6, 2/3, 7/5], rfl⟩ ⟩


-- testint the vadd_Aff (vector + point -> point)
#eval toString (v +ᵥ P)           -- (Pt [5/6, 11/12, -2])
#eval toString (w +ᵥ (v +ᵥ P))    -- (Pt [2/3, 19/12, -3/5])
def pt1 := v +ᵥ P
def pt2 := w +ᵥ (v +ᵥ P)
#eval s!"{pt1}" -- (Pt [5/6, 11/12, -2])
#eval s!"{pt2}" -- (Pt [2/3, 19/12, -3/5])


-- testint the add_affine_vector (vector + vector -> vector)
def vc1 := v +ᵥ w
def pt3 := (v + w) +ᵥ P
#eval s!"{vc1}"   -- (Vc [1/6, 23/12, -8/5])
#eval s!"{pt3}"  -- (Pt [2/3, 19/12, -3/5])
#eval toString ((v +ᵥ w))       -- (Vc [1/6, 23/12, -8/5])
#eval toString ((v + w) +ᵥ P)   -- (Pt [2/3, 19/12, -3/5])


-- Zero
#eval toString (v + 0) -- (Vc [1/3, 5/4, -3])
#eval toString (0 + v) -- (Vc [1/3, 5/4, -3])
def vc2 := v + 0
def vc3 := 0 + v
#eval s!"{vc2}" -- (Vc [1/3, 5/4, -3])
#eval s!"{vc3}" -- (Vc [1/3, 5/4, -3])


-- AddMonoid
#eval toString (3 • w)      -- (Vc [-1/2, 2, 21/5])
#eval toString (0 • w)      -- (Vc [0, 0, 0])
#eval toString (0 + w)      -- (Vc [-1/6, 2/3, 7/5])
#eval toString (w + 0)      -- (Vc [-1/6, 2/3, 7/5])
def vc4 := 3 • w
def vc5 := 0 • w
def vc6 := 0 + w
def vc7 := w + 0
#eval s!"{vc4}"      -- (Vc [-1/2, 2, 21/5])
#eval s!"{vc5}"      -- (Vc [0, 0, 0])
#eval s!"{vc6}"      -- (Vc [-1/6, 2/3, 7/5])
#eval s!"{vc7}"      -- (Vc [-1/6, 2/3, 7/5])



-- AddAction
#eval ((2 • v) + (3 • w) + (0 • v)) +ᵥ P  -- (Pt [2/3, 25/6, -4/5])
def pt4 := ((2 • v) + (3 • w) + (0 • v)) +ᵥ P
#eval s!"{pt4}"  -- (Pt [2/3, 25/6, -4/5])



-- Neg
#eval toString (-w)           -- (Vc [1/6, -2/3, -7/5])
def vc8 := -w
def vc9 := -v
#eval s!"{vc8}"         -- (Vc [1/6, -2/3, -7/5])
#eval s!"{vc9}"         -- (Vc [-1/3, -5/4, 3])



-- Sub
#eval toString (v - w)          -- (Vc [1/2, 7/12, -22/5])
#eval toString ((v - w) +ᵥ P)   -- (Pt [1, 1/4, -17/5])
#eval toString (v - 0)          -- (Vc [1/3, 5/4, -3])
def vc10 := P -ᵥ P2
def vc11 := v - w
def pt5 := (v - w) +ᵥ P
def vc12 := v - 0
#eval s!"{vc10}"       -- "(Vc [0, -1/6, -2])"
#eval s!"{vc11}"         -- (Vc [1/2, 7/12, -22/5])
#eval s!"{pt5}"  -- (Pt [1, 1/4, -17/5])
#eval s!"{vc12}"         -- (Vc [1/3, 5/4, -3])



-- AddGroup
#eval toString (w)        -- (Vc [-1/6, 2/3, 7/5])
#eval toString (-4 • w)   -- (Vc [2/3, -8/3, -28/5])
#eval toString (-4 • w + 3 • v -5 • w)   -- (Vc [5/2, -9/4, -108/5])
def vc13 := w
def vc14 := -4 • w
def vc15 := -4 • w + 3 • v -5 • w
#eval s!"{vc13}"        -- (Vc [-1/6, 2/3, 7/5])
#eval s!"{vc14}"   -- (Vc [2/3, -8/3, -28/5])
#eval s!"{vc15}"   -- (Vc [5/2, -9/4, -108/5])


-- AddTorsor
#eval P -ᵥ P +ᵥ P
#eval (v + (P -ᵥ P)) +ᵥ P  -- (Pt [5/6, 11/12, -2])
def pt6 := P -ᵥ P +ᵥ P
def pt7 := (v + (P -ᵥ P)) +ᵥ P
#eval s!"{pt6}"     -- (Pt [1/2, -1/3, 1])
#eval s!"{pt7}"   -- (Pt [5/6, 11/12, -2])



def main : IO Unit :=
  do
    IO.println s!"t1 = {t1}"
    IO.println s!"t2 = {t2}"
    IO.println s!"p1 = {p1}"
    IO.println s!"p2 = {p2}"
    IO.println s!"v = p1 -ᵥ p2 = {v}"

    -- Our testing samples of Affine Space
    IO.println s!"pt1 = v +ᵥ P = {pt1}"
    IO.println s!"pt2 = w +ᵥ (v +ᵥ P) = {pt2}"
    IO.println s!"pt3 = (v + w) +ᵥ P = {pt3}"
    IO.println s!"pt4 = ((2 • v) + (3 • w) + (0 • v)) +ᵥ P = {pt4}"
    IO.println s!"pt5 = (v - w) +ᵥ P = {pt5}"
    IO.println s!"pt6 = P -ᵥ P +ᵥ P = {pt6}"
    IO.println s!"pt7 = (v + (P -ᵥ P)) +ᵥ P = {pt7}"

    IO.println s!"vc1  = v +ᵥ w = {vc1}"
    IO.println s!"vc2  = v + 0 = {vc2}"
    IO.println s!"vc3  = 0 + v = {vc3}"
    IO.println s!"vc4  = 3 • w = {vc4}"
    IO.println s!"vc5  = 0 • w = {vc5}"
    IO.println s!"vc6  = 0 + w = {vc6}"
    IO.println s!"vc7  = w + 0 = {vc7}"
    IO.println s!"vc8  = -w = {vc8}"
    IO.println s!"vc9  = -v = {vc9}"
    IO.println s!"vc10 = P -ᵥ P2 = {vc10}"
    IO.println s!"vc11 = v - w = {vc11}"
    IO.println s!"vc12 = v - 0 = {vc12}"
    IO.println s!"vc13 = w = {vc13}"
    IO.println s!"vc14 = -4 • w = {vc14}"
    IO.println s!"vc15 = -4 • w + 3 • v -5 • w = {vc15}"

#eval main
