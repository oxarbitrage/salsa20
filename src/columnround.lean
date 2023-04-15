import rowround

import category_theory.category.basic
import category_theory.core

open params
open rowround

open category_theory

open_locale category_theory.Type
open_locale matrix


namespace columnround

variables [category (bitvec word_len)]

/-!
# Column round

The `columnround` function takes a `matrixType` (tuple of 4 `vecType`s) and return a new `matrixType`
after following the diagram.

- [Rowround Diagram](https://q.uiver.app/?q=WzAsMyxbMCwwLCIoeDAsIHgxLCB4MiwgeDMpLCAoeDQsIHg1LCB4NiwgeDcpLCAoeDgsIHg5LCB4MTAsIHgxMSksICh4MTIsIHgxMywgeDE0LCB4MTUpIl0sWzAsMiwiKHkwLCB5MSwgeTIsIHkzKSwgKHk0LCB5NSwgeTYsIHk3KSwgKHk4LCB5OSwgeTEwLCB5MTEpLCAoeTEyLCB5MTMsIHkxNCwgeTE1KSJdLFswLDQsIih6MCwgejEsIHoyLCB6MyksICh6NCwgejUsIHo2LCB6NyksICh6OCwgejksIHoxMCwgejExKSwgKHoxMiwgejEzLCB6MTQsIHoxNSkiXSxbMCwxLCJyb3dyb3VuZCIsMV0sWzEsMiwidHJhbnNwb3NlIiwxXV0=)

-/

/-- `columnround` is the transponse of a `rowround` output matrix. -/ 
noncomputable def columnround (input: matrixType) [is_iso( ↾ order1)] [is_iso( ↾ order2)] [is_iso( ↾ order3)]
  [is_iso( ↾ order4)] := (rowround input)ᵀ

/-- `columnround⁻¹` is just the inverse given `columnround` is isomorphic. -/
noncomputable def columnround_inv (input : matrixType) [is_iso (↾ columnround)] := inv ↾ columnround

end columnround
