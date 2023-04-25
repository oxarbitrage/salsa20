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


/-- Transpose of the input matrix. TODO: implement. -/
def transpose (input : matrixType) : matrixType := input 

--
variables [is_iso( ↾ order1)] [is_iso( ↾ order2)] [is_iso( ↾ order3)] [is_iso( ↾ order4)]

/-- There is a functor between `vecType` and `wordType`. -/
variables (F1 : vecType ⥤ wordType)

/-- There is a functor between `matrixType` and `vecType`. -/
variables (F2 : matrixType ⥤ vecType)

/-- `columnround` defined as a `rowround` of the transpose of the input. -/ 
noncomputable def columnround (input: matrixType) := (rowround F1 F2) (transpose input) 

variable [is_iso (↾ columnround F1 F2)]

/-- `columnround⁻¹` is just the inverse given `columnround` is isomorphic. -/
noncomputable def columnround_inv := inv ↾ columnround F1 F2

local notation `columnround⁻¹` := columnround_inv

/-- `columnround` and `columnround⁻¹` are isomorphic. -/
variable I : columnround F1 F2 ≅ columnround⁻¹ F1 F2

/-- `columnround` followed by `columnround⁻¹` is the identity, so `columnround⁻¹` is the inverse. -/
lemma is_inverse : I.hom ≫ I.inv = 𝟙 (columnround F1 F2) := by rw [iso.hom_inv_id]


end columnround
