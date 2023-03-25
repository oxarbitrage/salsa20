import operations
import types

import category_theory.category.basic
import category_theory.core

open operations
open params
open types

open category_theory

namespace quarterround

variables [category (bitvec word_len)]

/-!
  # Quarterround

  The `quarterround` function, its pieces and the relation with the inverses.
-/

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

end quarterround
