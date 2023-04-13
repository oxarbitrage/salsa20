import params
import quarterround

import category_theory.category.basic
import category_theory.core

open params
open operations
open quarterround

open category_theory

open_locale category_theory.Type

namespace rowround

variables [category (bitvec word_len)]

/-!
# Row round diagram and it's inverse.

The `rowround` function takes a `matrixType` (tuple of 4 `vecType`s) and return a new `matrixType`
after following the diagram.

- [Rowround Diagram](https://q.uiver.app/?q=WzAsMTgsWzAsMywiKHkwLCB5MSwgeTIsIHkzKSJdLFsyLDMsIih5NSwgeTYsIHk3LCB5NCkiXSxbNCwzLCIoeTEwLCB5MTEsIHk4LCB5OSkiXSxbNiwzLCIoeTE1LCB5MTIsIHkxMywgeTE0KSJdLFswLDUsIih6MCwgejEsIHoyLCB6MykiXSxbMiw1LCIoejUsIHo2LCB6NywgejQpIl0sWzQsNSwiKHoxMCwgejExLCB6MTgsIHo5KSJdLFs2LDUsIih6MTUsIHoxMiwgejEzLCB6MTQpIl0sWzAsNywiKHowLCB6MSwgejIsIHozKSIsWzMwMCw2MCw2MCwxXV0sWzIsNywiKHo0LCB6NSwgejYsIHo3KSIsWzMwMCw2MCw2MCwxXV0sWzQsNywiKHo4LCB6OSwgejEwLCB6MTEpIixbMzAwLDYwLDYwLDFdXSxbNiw3LCIoejEyLCB6MTMsIHoxNCwgejE1KSIsWzMwMCw2MCw2MCwxXV0sWzMsOCwiKHowLCB6MSwgejIsIHozKSwgKHo0LCB6NSwgejYsIHo3KSwgKHo4LCB6OSwgejEwLCB6MTEpLCAoejEyLCB6MTMsIHoxNCwgejE1KSIsWzI0MCw2MCw2MCwxXV0sWzMsMCwiKHkwLCB5MSwgeTIsIHkzKSwgKHk0LCB5NSwgeTYsIHk3KSwgKHk4LCB5OSwgeTEwLCB5MTEpLCAoeTEyLCB5MTMsIHkxNCwgeTE1KSJdLFswLDEsIih5MCwgeTEsIHkyLCB5MykiXSxbMiwxLCIoeTQsIHk1LCB5NiwgeTcpIl0sWzQsMSwiKHk4LCB5OSwgeTEwLCB5MTEpIl0sWzYsMSwiKHkxMiwgeTEzLHkxNCx5MTUpIl0sWzAsNCwicXVhcnRlcnJvdW5kIiwxXSxbMSw1LCJxdWFydGVycm91bmQiLDFdLFsyLDYsInF1YXJ0ZXJyb3VuZCIsMV0sWzMsNywicXVhcnRlcnJvdW5kIiwxXSxbNCw4LCJvcmRlcjFeey0xfSIsMV0sWzUsOSwib3JkZXIyXnstMX0iLDFdLFs2LDEwLCJvcmRlcjNeey0xfSIsMV0sWzcsMTEsIm9yZGVyNF57LTF9IiwxXSxbOSwxMiwiam9pbiIsMSx7ImNvbG91ciI6WzI0MCw2MCw2MF19LFsyNDAsNjAsNjAsMV1dLFs4LDEyLCJqb2luIiwxLHsiY29sb3VyIjpbMjQwLDYwLDYwXX0sWzI0MCw2MCw2MCwxXV0sWzEwLDEyLCJqb2luIiwxLHsiY29sb3VyIjpbMjQwLDYwLDYwXX0sWzI0MCw2MCw2MCwxXV0sWzExLDEyLCJqb2luIiwxLHsiY29sb3VyIjpbMjQwLDYwLDYwXX0sWzI0MCw2MCw2MCwxXV0sWzEzLDE0LCJmaXJzdCIsMV0sWzEzLDE1LCJzZWNvbmQiLDFdLFsxMywxNiwidGhpcmQiLDFdLFsxMywxNywiZm91cnRoIiwxXSxbMTQsMCwib3JkZXIxIiwxXSxbMTUsMSwib3JkZXIyIiwxXSxbMTYsMiwib3JkZXIzIiwxXSxbMTcsMywib3JkZXI0IiwxXSxbMTMsMTIsInJvd3JvdW5kIiwxLHsiY3VydmUiOjQsImNvbG91ciI6WzAsNjAsNjBdLCJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19LFswLDYwLDYwLDFdXSxbMTIsMTMsInJvd3JvdW5kXnstMX0iLDEseyJjdXJ2ZSI6NCwiY29sb3VyIjpbMCw2MCw2MF0sInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX0sWzAsNjAsNjAsMV1dXQ==)

-/

/-- Return `(x0, x1, x2, x3)` given an input matrix `(x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15)`. -/
@[simp] def first : matrixType → vecType
| input := input.fst

/-- Return `(x4, x5, x6, x7)` given an input matrix `(x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15)`. -/
@[simp] def second : matrixType → vecType
| input := input.snd.fst

/-- Return `(x8, x9, x10, x11)` given an input matrix `(x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15)`. -/
@[simp] def third : matrixType → vecType
| input := input.snd.snd.fst

/-- Return `(x12, x13, x14, x15)` given an input matrix `(x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15)`. -/
@[simp] def fourth : matrixType → vecType
| input := input.snd.snd.snd

/-!
## Rowround construction

-/

/-- Return `(y0, y1, y2, y3)` given `(y0, y1, y2, y3)`. This function is here
for completness, there is no need to use it as the output of `first` is already in order. -/
@[simp] def order1 : vecType → vecType
| input := (input.fst, input.snd.fst, input.snd.snd.fst, input.snd.snd.snd)

/-- Return `(y5, y6, y7, y4)` given `(y4, y5, y6, y7)`. -/
@[simp] def order2 : vecType → vecType
| input := (input.snd.fst, input.snd.snd.fst, input.snd.snd.snd, input.fst)

/-- Return `(y10, y11, y8, y9)` given `(y8, y9, y10, y11)`. -/
@[simp] def order3 : vecType → vecType
| input := (input.snd.snd.fst, input.snd.snd.snd, input.fst, input.snd.fst)

/-- Return `(y15, y12, y13, y14)` given `(y12, y13, y14, y15)`. -/
@[simp] def order4 : vecType → vecType
| input := (input.snd.snd.snd, input.fst, input.snd.fst, input.snd.snd.fst)

/-- Given an input `(y0, y1, y2, y3), (y4, y5, y6, y7), (y8, y9, y10, y11), (y12, y13, y14, y15)` return an
output `(z0, z1, z2, z3), (z4, z5, z6, z7), (z8, z9, z10, z11), (z12, z13, z14, z15)` applying the rowround
diagram. -/
noncomputable def rowround (input : matrixType) [is_iso( ↾ order1)] [is_iso( ↾ order2)] [is_iso( ↾ order3)]
  [is_iso( ↾ order4)] :=
(
  (↾ first ≫ order1 ≫ quarterround ≫ inv order1) input,
  (↾ second ≫ order2 ≫ quarterround ≫ inv order1) input,
  (↾ third ≫ order3 ≫ quarterround ≫ inv order1) input,
  (↾ fourth ≫ order4 ≫ quarterround ≫ inv order1) input
)

/- `rowround⁻¹` is just the inverse given `rowround` is isomorphic. -/
noncomputable def rowround_inv (input : matrixType) [is_iso (↾ rowround)] := inv ↾ rowround

local notation `rowround⁻¹` := rowround_inv

end rowround
