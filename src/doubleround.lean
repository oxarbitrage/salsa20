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

/-- `doubleround` is `columnround` followed by `rowround`. -/
noncomputable def doubleround (input: matrixType) := (↾ rowround ≫ ↾ columnround) input

/-- `doubleround⁻¹` is just the inverse given `doubleround` is isomorphic. -/
noncomputable def doubleround_inv (input : matrixType) [is_iso (↾ doubleround)] := inv ↾ doubleround


end doubleround
