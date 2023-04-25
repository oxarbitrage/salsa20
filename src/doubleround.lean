import columnround

import category_theory.core

open params
open rowround
open columnround

open category_theory
open_locale category_theory.Type
open_locale matrix


namespace doubleround

variables [category (wordType)]

/-!
# Double round

The `doubleround` function takes a `matrixType` and return a new `matrixType` applying the diagram.

- [Doubleround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/doubleround.html)

-/

-- 
variables [is_iso( ↾ order1)] [is_iso( ↾ order2)] [is_iso( ↾ order3)] [is_iso( ↾ order4)]


/-- There is a functor between `vecType` and `wordType`. -/
variables (F1 : vecType ⥤ wordType)

/-- There is a functor between `matrixType` and `vecType`. -/
variables (F2 : matrixType ⥤ vecType)

/-- `doubleround` is `columnround` followed by `rowround`. -/
noncomputable def doubleround := (↾ rowround F1 F2 ≫ ↾ columnround F1 F2)

variable [is_iso (↾ doubleround F1 F2)]

/-- `doubleround⁻¹` is just the inverse given `doubleround` is isomorphic. -/
noncomputable def doubleround_inv := inv ↾ doubleround F1 F2

local notation `doubleround⁻¹` := doubleround_inv

/-- `doubleround` and `doubleround⁻¹` are isomorphic. -/
variable I : doubleround F1 F2 ≅ doubleround⁻¹ F1 F2

/-- `doubleround` followed by `doubleround⁻¹` is the identity, so `doubleround⁻¹` is the inverse. -/
lemma is_inverse : I.hom ≫ I.inv = 𝟙 (doubleround F1 F2) := by rw [iso.hom_inv_id]


end doubleround
