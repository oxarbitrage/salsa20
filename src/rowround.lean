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

/-- There is a functor between `vecType` and `wordType`. -/
variables (F1 : vecType ⥤ wordType)

/-- There is a functor between `matrixType` and `vecType`. -/
variables (F2 : matrixType ⥤ vecType)

local notation `ONE_WORD` := bitvec.one params.word_len 
local notation `ONE_VEC` := (ONE_WORD, ONE_WORD, ONE_WORD, ONE_WORD) 

/-- Get the first row of a `matrixType` and put it in on front of a new matrix, fill the rest of the matrix with ones and return it. -/
def row1_f (input : matrixType) := (input.fst, ONE_VEC, ONE_VEC, ONE_VEC)

/--  -/
def row1 (input : matrixType) := F2.obj (row1_f input)

/-- Get the second row of a `matrixType` and put it in on front of a new matrix, fill the rest of the matrix with ones and return it. -/
def row2_f (input : matrixType) := (input.snd.fst, ONE_VEC, ONE_VEC, ONE_VEC)

/--  -/
def row2 (input : matrixType) := F2.obj (row2_f input)

/-- Get the third row of a `matrixType` and put it in on front of a new matrix, fill the rest of the matrix with ones and return it. -/
def row3_f (input : matrixType) := (input.snd.snd.fst, ONE_VEC, ONE_VEC, ONE_VEC)

/--  -/
def row3 (input : matrixType) := F2.obj (row3_f input)

/-- Return the fourth row of a `matrixType` -/
def row4_f (input : matrixType) := (input.snd.snd.snd, ONE_VEC, ONE_VEC, ONE_VEC)

/--  -/
def row4 (input : matrixType) := F2.obj (row4_f input)


/-- Return `(y0, y1, y2, y3)` given `(y0, y1, y2, y3)`. This function is here
for completness, there is no need to use it as the output of `row1` is already in order. -/
def order1 : vecType → vecType 
| input := input

/-- Return `(y5, y6, y7, y4)` given `(y4, y5, y6, y7)`. -/
def order2 : vecType → vecType
| input := (input.snd.fst, input.snd.snd.fst, input.snd.snd.snd, input.fst)

/-- Return `(y10, y11, y8, y9)` given `(y8, y9, y10, y11)`. -/
def order3 : vecType → vecType
| input := (input.snd.snd.fst, input.snd.snd.snd, input.fst, input.snd.fst)

/-- Return `(y15, y12, y13, y14)` given `(y12, y13, y14, y15)`. -/
def order4 : vecType → vecType
| input := (input.snd.snd.snd, input.fst, input.snd.fst, input.snd.snd.fst)

-- All order functions defined above have inverses.
variables [is_iso( ↾ order1)] [is_iso( ↾ order2)] [is_iso( ↾ order3)] [is_iso( ↾ order4)]

/-- There is a functor between `vecType` and `wordType`. -/
variables (F : vecType ⥤ wordType)

/-- Given a `matrixType` input `Y` return an output `Z` of the same type applying the rowround diagram. -/
noncomputable def rowround (input : matrixType) : matrixType := (
  (↾ row1 F2 ≫ order1 ≫ quarterround F1 ≫ inv order1) input,
  (↾ row2 F2 ≫ order2 ≫ quarterround F1 ≫ inv order2) input,
  (↾ row3 F2 ≫ order3 ≫ quarterround F1 ≫ inv order3) input,
  (↾ row4 F2 ≫ order4 ≫ quarterround F1 ≫ inv order4) input
)

/- `rowround` function has an inverse -/
variables [is_iso (↾ rowround F1 F2)]

/- `rowround⁻¹` is the inverse given `rowround` is isomorphic. -/
noncomputable def rowround_inv := inv ↾ rowround F1 F2

local notation `rowround⁻¹` := rowround_inv

/-- `rowround` and `rowround⁻¹` are isomorphic. -/
variable I : rowround F1 F2 ≅ rowround⁻¹ F1 F2

/-- `rowround` followed by `rowround⁻¹` is the identity, so `rowround⁻¹` is the inverse. -/
lemma is_inverse : I.hom ≫ I.inv = 𝟙 (rowround F1 F2) := by rw [iso.hom_inv_id]


end rowround
