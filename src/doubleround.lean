import columnround

import category_theory.category.basic
import category_theory.core

open params
open rowround
open columnround

open category_theory
open_locale category_theory.Type
open_locale matrix


namespace doubleround

variables [category (bitvec word_len)]

/-!
# Double round

The `doubleround` function takes a `matrixType` and return a new `matrixType` applying the diagram.

- [Doubleround Diagram](https://q.uiver.app/?q=WzAsMyxbMCwwLCIoeDAsIHgxLCB4MiwgeDMpLCAoeDQsIHg1LCB4NiwgeDcpLCAoeDgsIHg5LCB4MTAsIHgxMSksICh4MTIsIHgxMywgeDE0LCB4MTUpIl0sWzAsMiwiKHkwLCB5MSwgeTIsIHkzKSwgKHk0LCB5NSwgeTYsIHk3KSwgKHk4LCB5OSwgeTEwLCB5MTEpLCAoeTEyLCB5MTMsIHkxNCwgeDE1KSJdLFswLDQsIih6MCwgejEsIHoyLCB6MyksICh6NCwgejUsIHo2LCB6NyksICh6OCwgejksIHoxMCwgejExKSwgKHoxMiwgejEzLCB6MTQsIHoxNSkiXSxbMCwxLCJjb2x1bW5yb3VuZCIsMV0sWzEsMiwicm93cm91bmQiLDFdXQ==)
 
-/

-- 
variables [is_iso( ↾ order1)] [is_iso( ↾ order2)] [is_iso( ↾ order3)] [is_iso( ↾ order4)]

/-- `doubleround` is `columnround` followed by `rowround`. -/
noncomputable def doubleround (input: matrixType) := (↾ rowround ≫ ↾ columnround) input

/-- `doubleround⁻¹` is just the inverse given `doubleround` is isomorphic. -/
noncomputable def doubleround_inv (input : matrixType) [is_iso (↾ doubleround)] := inv ↾ doubleround


end doubleround
