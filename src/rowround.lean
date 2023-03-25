import params
import quarterround
import utils

import category_theory.category.basic
import category_theory.core

open params
open operations
open quarterround
open utils

open category_theory

namespace rowround

variables [category (bitvec word_len)]

/-!
  # Rowround

  The `rowround` function and the relation with its inverse.
-/

/-!
  ## Definitions and lemmas
-/

/-- The row round of a single row. Complete `rowround` function will use 4 of this. -/
@[simp] def rowround_single (R : vecType): vecType :=
  (
    (quarterround R).fst, (quarterround R).snd.fst, 
    (quarterround R).snd.snd.fst, (quarterround R).snd.snd.snd
  )

/-- The inverse of a single row round. -/
@[simp] def rowround_single_inv (R : vecType) : vecType :=
  (
    (quarterround_inv R).fst, (quarterround_inv R).snd.fst, 
    (quarterround_inv R).snd.snd.fst, (quarterround_inv R).snd.snd.snd
  )

/- Just some notation for inverses. -/
local notation `rowround_single⁻¹` := rowround_single_inv

/-- Each row is invertible. -/
lemma rowround_single_is_inv (I : rowround_single ≅ rowround_single⁻¹) : I.hom ≫ I.inv = 𝟙 rowround_single :=
  by rw [iso.hom_inv_id]

/-- Apply `rowround_single` to get a row round matrix output -/
@[simp] def rowround (M : matrixType) : matrixType :=
  (
    rowround_single M.fst,
    rowround_single M.snd.fst,
    rowround_single M.snd.snd.fst,
    rowround_single M.snd.snd.snd
  )

/-- Reverses `rowround` by doing `rowround_single_inv` to get the original matrix output -/
@[simp] def rowround_inv (M : matrixType) : matrixType :=
  (
    rowround_single_inv M.fst,
    rowround_single_inv M.snd.fst,
    rowround_single_inv M.snd.snd.fst,
    rowround_single_inv M.snd.snd.snd
  )

/- Just some notation for inverses. -/
local notation `rowround⁻¹` := rowround_inv

/-- The full `rowround` is invertible. -/
lemma rowround_is_inv (I : rowround ≅ rowround⁻¹) : I.hom ≫ I.inv = 𝟙 rowround := by rw [iso.hom_inv_id]

/-- This rowround call will sort all the elements of the input and the output to match salsa20 spec.
It should be used in `doubleround`. -/
@[simp] def rowround_salsa20 (M : matrixType) := rowround_output (rowround (rowround_input M))

/-- This rowround inverse call will sort all the elements of the input and the output to match salsa20.
It should be used in `doubleround`. -/
@[simp] def rowround_salsa20_inv (M : matrixType) := rowround_output (rowround⁻¹ (rowround_input M))

/- Just some notation for inverses. -/
local notation `rowround_salsa20⁻¹` := rowround_salsa20_inv

/-- For any `rowround` output, we can get back to original values using the defined inverse. -/
@[simp] lemma rowround_salsa20_is_inv (I : rowround_salsa20 ≅ rowround_salsa20⁻¹) : 
  I.hom ≫ I.inv = 𝟙 rowround_salsa20 := by rw [iso.hom_inv_id]

end rowround
