import rowround

import category_theory.category.basic
import category_theory.core

open params
open operations
open quarterround
open rowround
open utils

open category_theory

namespace columnround

variables [category (bitvec word_len)]

/-!
  # Columnround

  The `columnround` function and the relation with its inverse.
-/

/-!
  ## Definitions and lemmas
-/

/--  Without ordering for inputs, a `columnround` is exactly the same as a `rowround`. -/
@[simp] def columnround (M : matrixType) : matrixType := rowround M

/--  Without ordering for inputs, a `columnround_inv` is exactly the same as a `rowround_inv`. -/
@[simp] def columnround_inv (M : matrixType) : matrixType := rowround_inv M

/- Just some notation for inverses. -/
local notation `columnround⁻¹` := columnround_inv

/-- The `columnround` function is invertible. -/
lemma columnround_is_inv (I : columnround ≅ columnround⁻¹) : I.hom ≫ I.inv = 𝟙 columnround :=
  by rw [iso.hom_inv_id]

/-- This columnround call will sort all the elements of the input and the output to match salsa20.
-- It should be used in `doubleround`.-/
@[simp] def columnround_salsa20 (M : matrixType) := columnround_output (columnround (columnround_input M))

/-- This columnround inverse call will sort all the elements of the input and the output to match salsa20.
It should be used in `doubleround`. -/
@[simp] def columnround_salsa20_inv (M : matrixType) := columnround_output (columnround⁻¹ (columnround_input M))

/- Just some notation for inverses. -/
local notation `columnround_salsa20⁻¹` := columnround_salsa20_inv

/-- The `columnround` function is invertible. -/
lemma columnround_salsa20_is_inv (I : columnround_salsa20 ≅ columnround_salsa20⁻¹) : 
  I.hom ≫ I.inv = 𝟙 columnround_salsa20 := by rw [iso.hom_inv_id]

end columnround
