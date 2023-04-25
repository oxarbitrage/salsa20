import doubleround

import category_theory.core
import category_theory.monad.basic

open doubleround
open rowround
open params
open types

open category_theory
open_locale category_theory.Type
open category_theory.monad

namespace core

variable [category (wordType)]

--
variables [is_iso( ↾ order1)] [is_iso( ↾ order2)] [is_iso( ↾ order3)] [is_iso( ↾ order4)]

/-- There is a functor between `vecType` and `wordType`. -/
variables (F1 : vecType ⥤ wordType)

/-- There is a functor between `matrixType` and `vecType`. -/
variables (F2 : matrixType ⥤ vecType)

/-!
  # Core

  The `core` function takes a `matrixType` and return a new `matrixType` after applying the diagram.

  - [Core Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/core.html)
-/

/-- Apply double round 10 times to an input. -/
noncomputable def doubleround10 (X : matrixType) :=
  (↾ doubleround F1 F2 ≫ ↾ doubleround F1 F2 ≫ ↾ doubleround F1 F2 ≫ ↾ doubleround F1 F2 ≫ ↾ doubleround F1 F2 ≫ 
  ↾ doubleround F1 F2 ≫ ↾ doubleround F1 F2 ≫ ↾ doubleround F1 F2 ≫ ↾ doubleround F1 F2 ≫ ↾ doubleround F1 F2) X

variables [is_iso (↾ doubleround10 F1 F2)]

/- The inverse of `doubleround10`. -/
noncomputable def doubleround10_inv := inv ↾ doubleround10 F1 F2

/- Just some notation for inverse. -/
local notation `doubleround10⁻¹` := doubleround10_inv

/-- `doubleround` and `doubleround⁻¹` are isomorphic. -/
variable I : doubleround10 F1 F2 ≅ doubleround10⁻¹ F1 F2

/-- `doubleround10` followed by `doubleround10⁻¹` is the identity, so `doubleround10⁻¹` is the inverse. -/
lemma is_inverse : I.hom ≫ I.inv = 𝟙 (doubleround10 F1 F2) := by rw [iso.hom_inv_id]

/-- Do modulo addition for each matrix item. -/
def mod_matrix (X Y : matrixType) := (
  (
    operations.mod (X.fst.fst, Y.fst.fst),
    operations.mod (X.fst.snd.fst, Y.fst.snd.fst),
    operations.mod (X.fst.snd.snd.fst, Y.fst.snd.snd.fst),
    operations.mod (X.fst.snd.snd.snd, Y.fst.snd.snd.snd)
  ),
  (
    operations.mod (X.snd.fst.fst, Y.snd.fst.fst),
    operations.mod (X.snd.fst.snd.fst, Y.snd.fst.snd.fst),
    operations.mod (X.snd.fst.snd.snd.fst, Y.snd.fst.snd.snd.fst),
    operations.mod (X.snd.fst.snd.snd.snd, Y.snd.fst.snd.snd.snd)
  ),
  (
    operations.mod (X.snd.snd.fst.fst, Y.snd.snd.fst.fst),
    operations.mod (X.snd.snd.fst.snd.fst, Y.snd.snd.fst.snd.fst),
    operations.mod (X.snd.snd.fst.snd.snd.fst, Y.snd.snd.fst.snd.snd.fst),
    operations.mod (X.snd.snd.fst.snd.snd.snd, Y.snd.snd.fst.snd.snd.snd)
  ),
  (
    operations.mod (X.snd.snd.snd.fst, Y.snd.snd.snd.fst),
    operations.mod (X.snd.snd.snd.snd.fst, Y.snd.snd.snd.snd.fst),
    operations.mod (X.snd.snd.snd.snd.snd.fst, Y.snd.snd.snd.snd.snd.fst),
    operations.mod (X.snd.snd.snd.snd.snd.snd, Y.snd.snd.snd.snd.snd.snd)
  )
)

-- TODO: `matrixType` with addition (`modmatrix`) form a monoid, monoids has no inverse. 

/-- Do addition modulo 2³² between the input and the `doubleround10` of the input. -/
noncomputable def core (X : matrixType) : matrixType := mod_matrix (doubleround10 F1 F2 X) X


end core
