import doubleround
import littleendian

import category_theory.category.basic
import category_theory.core

open doubleround
open littleendian
open operations
open params
open utils

open category_theory

namespace core

variable [category (bitvec word_len)]

/-!
  # Core

  - The `doubleround10` function and its inverse.
  - The `hash` and `core` functions, the non existing inverse.
-/

/-- Apply double round 10 times to a reduced input. -/
@[simp] def doubleround_10 (X : matrixType): matrixType :=
  doubleround_salsa20 $
  doubleround_salsa20 $
  doubleround_salsa20 $
  doubleround_salsa20 $
  doubleround_salsa20 $
  doubleround_salsa20 $
  doubleround_salsa20 $
  doubleround_salsa20 $
  doubleround_salsa20 $
  doubleround_salsa20 $
  X

/-- Inverse of `doubleround_10`. -/
@[simp] def doubleround_10_inv (X : matrixType): matrixType :=
  doubleround_salsa20_inv $
  doubleround_salsa20_inv $
  doubleround_salsa20_inv $
  doubleround_salsa20_inv $
  doubleround_salsa20_inv $
  doubleround_salsa20_inv $
  doubleround_salsa20_inv $
  doubleround_salsa20_inv $
  doubleround_salsa20_inv $
  doubleround_salsa20_inv $
  X

/- Just some notation for inverses. -/
local notation `doubleround_10⁻¹` := doubleround_10_inv

/-- The `doubleround` function is invertible. -/
lemma doubleround_is_inv (I : doubleround_10 ≅ doubleround_10⁻¹) : I.hom ≫ I.inv = 𝟙 doubleround_10 :=
  by rw [iso.hom_inv_id]

/-!
## Core and hash definitions

  - There is no isomorphism (≅) between `core` and any `core⁻¹`.
  - There is no isomorphism (≅) between `hash` and any `hash⁻¹` because the use of `core` and `core⁻¹`.
-/

/-- Do addition modulo 2^32 of the reduced input and the doubleround of the reduced input. -/
@[simp] def core (X : matrixType) : matrixType := mod_matrix (doubleround_10 X) X

/-- Do the hash. -/
def hash (X : matrix64Type) : matrix64Type := aument (core (reduce X))


end core
