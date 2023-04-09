import operations
import types

import category_theory.category.basic
import category_theory.core

open operations
open params
open types

open category_theory

open_locale category_theory.Type

namespace quarterround

variables [category (bitvec word_len)]

/-!
# Quarterround

The `quarterround` function takes a tuple of 4 bitvecs and return a tuple of the same type
after applying the diagram.

- [Diagram](https://q.uiver.app/?q=WzAsMjYsWzUsMCwiKHkwLCB5MSwgeTIsIHkzKSJdLFsxLDEsInkwIl0sWzMsMSwieTEiXSxbNywxLCJ5MiJdLFs5LDEsInkzIl0sWzUsMiwiKHkwLCB5MykiXSxbNSw0LCJtb2RyZXMxIl0sWzMsNSwiKHkxLCByb3RscmVzMSkiXSxbNyw1LCJyb3RscmVzMSJdLFszLDcsInoxIixbMzAwLDYwLDYwLDFdXSxbMSw4LCIoejEsIHkwKSJdLFsxLDEwLCJtb2RyZXMyIl0sWzgsMTAsInJvdGxyZXMyIl0sWzEwLDgsIih5Miwgcm90bHJlczIpIl0sWzgsOCwiejIiLFszMDAsNjAsNjAsMV1dLFsxMiw2LCIoejIsIHoxKSJdLFsxMiw4LCJtb2RyZXMzIl0sWzE1LDgsInJvdGxyZXMzIl0sWzE1LDYsIih5Mywgcm90bHJlczMpIl0sWzE3LDYsInozIixbMzAwLDYwLDYwLDFdXSxbMTIsMTEsIih6MywgejIpIl0sWzksMTEsIm1vZHJlczAiXSxbNiwxMSwicm90bHJlczAiXSxbMCwxMSwiKHkwLCByb3RscmVzMCkiXSxbMCwxMywiejAiLFszMDAsNjAsNjAsMV1dLFs1LDEzLCIoejAsIHoxLCB6MiwgejMpIixbMjQwLDYwLDYwLDFdXSxbMCwxLCJmaXJzdCIsMV0sWzAsMiwic2Vjb25kIiwxXSxbMCwzLCJ0aGlyZCIsMV0sWzAsNCwiZm91cnRoIiwxXSxbNCw1LCJidWlsZG1vZDEiLDFdLFsxLDUsImJ1aWxkbW9kMSIsMV0sWzUsNiwibW9kIl0sWzIsNywiYnVpbGR4b3IxIiwxXSxbOCw3LCJidWlsZHhvcjEiLDFdLFs3LDksInhvciJdLFsxLDEwLCJidWlsZG1vZDIiLDFdLFsxMCwxMV0sWzMsMTMsIiIsMSx7ImN1cnZlIjotNH1dLFsxMywxNCwieG9yIiwyLHsibGV2ZWwiOjJ9XSxbNiw4LCJyb3RsNyIsMV0sWzksMTAsImJ1aWxkbW9kMiIsMV0sWzExLDEyLCJyb3RsMTMiLDFdLFsxMiwxMywiIiwxLHsiY3VydmUiOjR9XSxbMTQsMTVdLFs5LDE1XSxbMTUsMTYsIm1vZCIsMix7ImxldmVsIjoyfV0sWzE2LDE3LCJyb3RsMTMiLDJdLFsxNywxOF0sWzQsMThdLFsxOCwxOSwieG9yIiwyLHsibGV2ZWwiOjJ9XSxbMTksMjAsIiIsMix7ImN1cnZlIjotM31dLFsxNCwyMF0sWzIwLDIxLCJtb2QiLDIseyJsZXZlbCI6Mn1dLFsyMSwyMiwicm90bDE4IiwyXSxbMjIsMjNdLFsxLDIzXSxbMjMsMjRdLFsyNCwyNSwiIiwyLHsiY29sb3VyIjpbMjQwLDYwLDYwXX1dLFsxNCwyNSwiIiwyLHsiY3VydmUiOjQsImNvbG91ciI6WzI0MCw2MCw2MF19XSxbMTksMjUsIiIsMix7ImNvbG91ciI6WzI0MCw2MCw2MF19XSxbOSwyNSwiIiwyLHsiY29sb3VyIjpbMjQwLDYwLDYwXX1dLFswLDI1LCJxdWFydGVycm91bmQiLDIseyJjdXJ2ZSI6MiwiY29sb3VyIjpbMCw2MCw2MF0sInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX0sWzAsNjAsNjAsMV1dLFsyNSwwLCJxdWFydGVycm91bmReey0xfSIsMix7ImN1cnZlIjoyLCJjb2xvdXIiOlswLDYwLDYwXSwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fSxbMCw2MCw2MCwxXV1d)

-/

/-- Return `y0` given an input vector `(y0, y1, y2, y3)`. -/
def first : vecType → bitvec word_len
| input := input.fst

/-- Return `y1` given an input vector `(y0, y1, y2, y3)`. -/
def second : vecType → bitvec word_len
| input := input.snd.fst

/-- Return `y2` given an input vector `(y0, y1, y2, y3)`. -/
def third : vecType → bitvec word_len
| input := input.snd.snd.fst

/-- Return `y3` given an input vector `(y0, y1, y2, y3)`. -/
def fourth : vecType → bitvec word_len
| input := input.snd.snd.snd

/-- Return `(y0, y3)` given an input vector `(y0, y1, y2, y3)`. -/
def buildmod1 : vecType → (bitvec word_len × bitvec word_len)
| input := (first input, fourth input)

/-- Return `(y1, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor1 : vecType → bitvec word_len → (bitvec word_len × bitvec word_len)
| input b := ((second input), b)

/-- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7) -/
def z1 (input : vecType) := (↾ buildmod1) ≫ mod ≫ rotl7 ≫ (↾ buildxor1 input) ≫ xor

local notation `z1Type` := vecType ⟶ bitvec word_len

/-- `z1` of `(0, 0, 0, 0)` is `0` -/
lemma z1_zero : z1 (0, 0, 0, 0) (0, 0, 0, 0) = 0 := by refl

/-- Return `(z1, y0)` given an input vector `(y0, y1, y2, y3)` and `z1`. -/
def buildmod2 : vecType → z1Type → (bitvec word_len × bitvec word_len)
| input z1 := (z1 input, first input)

/-- Return `(y2, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor2 : vecType → bitvec word_len → (bitvec word_len × bitvec word_len)
| input b := ((third input), b)

/-- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9) -/
def z2 (input : vecType) := (↾ buildmod2 input) ≫ mod ≫ rotl9 ≫ (buildxor2 input) ≫ xor

/-- `z2` of `(0, 0, 0, 0)` is `0` -/
lemma z2_zero : z2 (0, 0, 0, 0) (z1 (0, 0, 0, 0)) = 0 := by refl

local notation `z2Type` := vecType → bitvec word_len ⟶ bitvec word_len

/-- Return `(z2, z1)` given an input vector `(y0, y1, y2, y3)`, `z2` and `z1`. -/
def buildmod3 : vecType → z2Type → z1Type → (bitvec word_len × bitvec word_len)
| input z2 z1 := (z2 z1, z1 input)

/-- Return `(y3, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor3 : vecType → bitvec word_len → (bitvec word_len × bitvec word_len)
| input b := ((fourth input), b)

/-- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13) -/
def z3 (input : vecType) := (↾ buildmod3 input (z2 input)) ≫ mod ≫ rotl9 ≫ (buildxor3 input) ≫ xor

/-- `z3` of `(0, 0, 0, 0)` is `0` -/
lemma z3_zero : z3 (0, 0, 0, 0) (z1 (0, 0, 0, 0)) = 0 := by refl

local notation `z3Type` := z1Type ⟶ bitvec word_len

/-- Return `(z3, z2)` given an input vector `(y0, y1, y2, y3)`, `z3` and `z2`. -/
def buildmod0 : vecType → z3Type → z2Type → (bitvec word_len × bitvec word_len)
| input z3 z2 := (z3 (z1 input), (z2 first))

/-- Return `(y0, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor0 : vecType → bitvec word_len → (bitvec word_len × bitvec word_len)
| input b := ((first input), b)

/-- z₀ = y₀ ⊕ ((z₃ + z₂) <<< 18) -/
def z0 (input : vecType) := (↾ buildmod0 input (z2 input)) ≫ mod ≫ rotl9 ≫ (buildxor0 input) ≫ xor

def quarterround (input : vecType) := (z0, z1, z2, z3)

/-

/-! ## Definitions -/

/-- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7) -/
def qr1 (a b c d : bitvec word_len) := b OP (OP_RHS a d 7)
/-- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9) -/
def qr2 (a b c d : bitvec word_len) := c OP (OP_RHS (qr1 a b c d) a 9)
/-- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13) -/
def qr3 (a b c d : bitvec word_len) := d OP (OP_RHS (qr2 a b c d) (qr1 a b c d) 13)
/-- z₀ = y₀ ⊕ ((z₃ + z₂) <<< 18) -/
def qr0 (a b c d : bitvec word_len) := a OP (OP_RHS (qr3 a b c d) (qr2 a b c d) 18)

/-- Given a sequence of 4 numbers `seq`, use the four equations (`qr0`, `qr1`, `qr2` and `qr3`) to get the 
full quarterround output, which is a transformed 4 numbers sequence too. -/
@[simp] def quarterround (seq : vecType) : vecType :=
  (
    qr0 seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
    qr1 seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
    qr2 seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
    qr3 seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd
  )

/-! ## Quarterround zero lemmas -/

/-- `qr0` of 4 zeros is zero -/
@[simp] lemma qr0_zero : qr0 0 0 0 0 = 0 := by refl

/-- `qr1` of 4 zeros is zero -/
@[simp] lemma qr1_zero : qr1 0 0 0 0 = 0 := by refl

/-- `qr2` of 4 zeros is zero -/
@[simp] lemma qr2_zero : qr2 0 0 0 0 = 0 := by refl

/-- `qr3` of 4 zeros is zero -/
@[simp] lemma qr3_zero : qr3 0 0 0 0 = 0 := by refl

/-- `quarterround` of 4 zeros is a sequence of 4 zeros -/
@[simp] lemma quarterround_zero : quarterround (0, 0, 0, 0) = (0, 0, 0, 0) := by refl

/-! ## Inverse definitions -/

/-- y₀ = z₀ ⊕ ((z₃ + z₂) <<< 18) -/
def qr0_inv (a' b' c' d' : bitvec word_len) := a' OP (operation_rhs d' c' 18)
/-- y₃ = z₃ ⊕ ((z₂ + z₁) <<< 13) -/
def qr3_inv (a' b' c' d' : bitvec word_len) := d' OP (operation_rhs c' b' 13)
/-- y₂ = z₂ ⊕ ((z₁ + y₀) <<< 9) -/
def qr2_inv (a' b' c' d' : bitvec word_len) := c' OP (operation_rhs b' (qr0_inv a' b' c' d')  9)
/-- y₁ = z₁ ⊕ ((y₀ + y₃) <<< 7) -/
def qr1_inv (a' b' c' d' : bitvec word_len) := b' OP (operation_rhs (qr0_inv a' b' c' d') (qr3_inv a' b' c' d') 7)

/-- Put the 4 elements that forms a quarterround inverse all together. -/
@[simp] def quarterround_inv (seq : vecType) := (
  qr0_inv seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
  qr1_inv seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
  qr2_inv seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
  qr3_inv seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd
)

local notation `qr0⁻¹` := qr0_inv
local notation `qr1⁻¹` := qr1_inv
local notation `qr2⁻¹` := qr2_inv
local notation `qr3⁻¹` := qr3_inv
local notation `quarterround⁻¹` := quarterround_inv

/-! ## Inverse lemmas -/

/-- The `quarterround` operation is fully invertible. -/
lemma quarterround_is_inv (I : quarterround ≅ quarterround⁻¹) : I.hom ≫ I.inv = 𝟙 quarterround :=
  by rw [iso.hom_inv_id]

/-! ## Inverses of the `quarterround` and `quarterround_inv` individual pieces lemmas -/

/-- `qr0⁻¹` after `qr0` is `𝟙 qr0`. -/
lemma qr0_is_inv (I : qr0 ≅ qr0⁻¹) : I.hom ≫ I.inv = 𝟙 qr0 := by rw [iso.hom_inv_id]

/-- `qr1⁻¹` after `qr1` is `𝟙 qr1`. -/
lemma qr1_is_inv (I : qr1 ≅ qr1⁻¹) : I.hom ≫ I.inv = 𝟙 qr1 := by rw [iso.hom_inv_id]

/-- `qr2⁻¹` after `qr2` is `𝟙 qr2`. -/
lemma qr2_is_inv (I : qr2 ≅ qr2⁻¹) : I.hom ≫ I.inv = 𝟙 qr2 := by rw [iso.hom_inv_id]

/-- `qr3⁻¹` after `qr3` is `𝟙 qr3`. -/
lemma qr3_is_inv (I : qr3 ≅ qr3⁻¹) : I.hom ≫ I.inv = 𝟙 qr3 := by rw [iso.hom_inv_id]

/-- `qr0` after `qr0⁻¹` is `𝟙 qr0⁻¹`. -/
lemma qr0_inv_is_inv (I : qr0 ≅ qr0⁻¹) : I.inv ≫ I.hom = 𝟙 qr0⁻¹ := by rw [iso.inv_hom_id]

/-- `qr1` after `qr1⁻¹` is `𝟙 qr1⁻¹`. -/
lemma qr1_inv_is_inv (I : qr1 ≅ qr1⁻¹) : I.inv ≫ I.hom = 𝟙 qr1⁻¹ := by rw [iso.inv_hom_id]

/-- `qr2` after `qr2⁻¹` is `𝟙 qr2⁻¹`. -/
lemma qr2_inv_is_inv (I : qr2 ≅ qr2⁻¹) : I.inv ≫ I.hom = 𝟙 qr2⁻¹ := by rw [iso.inv_hom_id]

/-- `qr3` after `qr3⁻¹` is `𝟙 qr3⁻¹`. -/
lemma qr3_inv_is_inv (I : qr3 ≅ qr3⁻¹) : I.inv ≫ I.hom = 𝟙 qr3⁻¹ := by rw [iso.inv_hom_id]

/-- The inidivudal pieces of the `quarterround` function are all invertible. -/
lemma qr_pieces_are_all_invertible (I0 : qr0 ≅ qr0⁻¹) (I1 : qr1 ≅ qr1⁻¹) (I2 : qr2 ≅ qr2⁻¹) (I3 : qr3 ≅ qr3⁻¹) :
  I0.hom ≫ I0.inv = 𝟙 qr0 ∧ I1.hom ≫ I1.inv = 𝟙 qr1 ∧ I2.hom ≫ I2.inv = 𝟙 qr2 ∧ I3.hom ≫ I3.inv = 𝟙 qr3 :=
begin
  simp only [iso.hom_inv_id, eq_self_iff_true, and_self],
end

-/

end quarterround
