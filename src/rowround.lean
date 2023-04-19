import quarterround

import category_theory.category.basic
import category_theory.core

open quarterround

open category_theory
open_locale category_theory.Type


namespace rowround

variables [category (wordType)]

/-!
# Rowround

The `rowround` function takes a `matrixType` (4 by 4 matrix) and return a new `matrixType`
after appliying the rowround diagram.

- [Rowround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/rowround.html)
-/

/-- Return the first row of a `matrixType` -/
def row1 (input : matrixType) := !![(input 0 0), (input 0 1), (input 0 2), (input 0 3)]

/-- Return the second row of a `matrixType` -/
def row2 (input : matrixType) := !![(input 0 4), (input 0 5), (input 0 6), (input 0 7)]

/-- Return the third row of a `matrixType` -/
def row3 (input : matrixType) := !![(input 0 8), (input 0 9), (input 0 10), (input 0 11)]

/-- Return the fourth row of a `matrixType` -/
def row4 (input : matrixType) := !![(input 0 12), (input 0 13), (input 0 14), (input 0 15)]

/-- Return `(y0, y1, y2, y3)` given `(y0, y1, y2, y3)`. This function is here
for completness, there is no need to use it as the output of `row1` is already in order. -/
def order1 : vecType → vecType 
| input := !![(input 0 0), (input 0 1), (input 0 2), (input 0 3)]

/-- Return `(y5, y6, y7, y4)` given `(y4, y5, y6, y7)`. -/
def order2 : vecType → vecType
| input := !![(input 1 1), (input 1 2), (input 1 3), (input 1 0)]

/-- Return `(y10, y11, y8, y9)` given `(y8, y9, y10, y11)`. -/
def order3 : vecType → vecType
| input := !![(input 2 2), (input 2 3), (input 2 0), (input 2 1)]

/-- Return `(y15, y12, y13, y14)` given `(y12, y13, y14, y15)`. -/
def order4 : vecType → vecType
| input := !![(input 3 3), (input 3 0), (input 3 1), (input 3 2)]

-- All order functions defined above have inverses.
variables [is_iso( ↾ order1)] [is_iso( ↾ order2)] [is_iso( ↾ order3)] [is_iso( ↾ order4)]

/-- Given a `matrixType` input `Y` return an output `Z` of the same type applying the rowround diagram. -/
noncomputable def rowround (input : matrixType) : matrixType := do {
  let q1 := (↾ row1 ≫ order1 ≫ quarterround ≫ inv order1) input,
  let q2 := (↾ row2 ≫ order2 ≫ quarterround ≫ inv order2) input,
  let q3 := (↾ row3 ≫ order3 ≫ quarterround ≫ inv order3) input,
  let q4 := (↾ row4 ≫ order4 ≫ quarterround ≫ inv order4) input,

  !![
    q1 0 0, q1 0 1, q1 0 2, q1 0 3;
    q2 0 0, q2 0 1, q2 0 2, q2 0 3;
    q3 0 0, q3 0 1, q3 0 2, q3 0 3;
    q4 0 0, q4 0 1, q4 0 2, q4 0 3;
  ]
}

/- `rowround` function has an inverse -/
variables [is_iso (↾ rowround)]

/- `rowround⁻¹` is the inverse given `rowround` is isomorphic. -/
noncomputable def rowround_inv := inv ↾ rowround

local notation `rowround⁻¹` := rowround_inv

/-- `matrixType` is a category. -/
variables [category (matrix (fin 4) (fin 4) wordType)]

/-- `rowround` and `rowround⁻¹` are isomorphic. -/
variable I : rowround ≅ rowround⁻¹

/-- `rowround` followed by `rowround⁻¹` is the identity, so `rowround⁻¹` is the inverse. -/
lemma is_inverse : I.hom ≫ I.inv = 𝟙 rowround := by rw [iso.hom_inv_id]


end rowround
