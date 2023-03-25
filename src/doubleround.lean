import rowround
import columnround

import category_theory.category.basic
import category_theory.core

open params
open operations
open quarterround
open rowround
open columnround
open utils

open category_theory

namespace doubleround

variables [category (bitvec word_len)]

/-!
  # Doubleround

  The `doubleround` function and the relation with its inverse.
-/

/-- doubleround(x) = rowround(columnround(x)) -/
@[simp] def doubleround (M : matrixType) : matrixType := rowround $ columnround M

/--  doubleround_inv(x) = columnround_inv(rowround_inv(x)) -/
@[simp] def doubleround_inv (M : matrixType) : matrixType := columnround_inv $ rowround_inv M

/- Just some notation for inverses. -/
local notation `doubleround⁻¹` := doubleround_inv

/-- The `doubleround` function is invertible. -/
lemma doubleround_is_inv (I : doubleround ≅ doubleround⁻¹) : I.hom ≫ I.inv = 𝟙 doubleround :=
  by rw [iso.hom_inv_id]

/--
A special case of `doubleround` where inputs and outputs are sorted according to the salsa20 spec:
doubleround'(x) = rowround'(columnround'(x)) -/
@[simp] def doubleround_salsa20 (M : matrixType) : matrixType := rowround_salsa20 $ columnround_salsa20 M

/--
A special case of `doubleround_inv` where inputs and outputs are sorted according to the salsa20 spec:
doubleround_inv'(x) = columnround_inv'(rowround_inv'(x)) -/
@[simp] def doubleround_salsa20_inv (M : matrixType) : matrixType := columnround_salsa20_inv $ rowround_salsa20_inv M

/- Just some notation for inverses. -/
local notation `doubleround_salsa20⁻¹` := doubleround_salsa20_inv

/-- The `doubleround` function is invertible. -/
lemma doubleround_salsa20_is_inv (I : doubleround_salsa20 ≅ doubleround_salsa20⁻¹) : 
  I.hom ≫ I.inv = 𝟙 doubleround_salsa20 := by rw [iso.hom_inv_id]


end doubleround
