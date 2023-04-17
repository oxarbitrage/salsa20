import rowround

open rowround

open category_theory
open_locale category_theory.Type
open_locale matrix


namespace columnround

variables [category (wordType)]

/-!
# Column round

The `columnround` function takes a `matrixType` (tuple of 4 `vecType`s) and return a new `matrixType`
after following the diagram.

- [Columnround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/columnround.html)
-/

--
variables [is_iso( ↾ order1)] [is_iso( ↾ order2)] [is_iso( ↾ order3)] [is_iso( ↾ order4)]

/-- `columnround` is the transponse of a `rowround` output matrix. -/ 
noncomputable def columnround (input: matrixType) := rowround inputᵀ

/-- `columnround⁻¹` is just the inverse given `columnround` is isomorphic. -/
noncomputable def columnround_inv (input : matrixType) [is_iso (↾ columnround)] := inv ↾ columnround

end columnround
