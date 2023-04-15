
import params
import quarterround

import category_theory.category.basic
import category_theory.core

open params
open quarterround

open category_theory

open_locale category_theory.Type


namespace rowround

variables [category (bitvec word_len)]

/-!
# Row round

The `rowround` function takes a `matrixType` (tuple of 4 `vecType`s) and return a new `matrixType`
after following the diagram.

- [Rowround Diagram](https://q.uiver.app/?q=WzAsMTgsWzAsMywiKHkwLCB5MSwgeTIsIHkzKSJdLFsyLDMsIih5NSwgeTYsIHk3LCB5NCkiXSxbNCwzLCIoeTEwLCB5MTEsIHk4LCB5OSkiXSxbNiwzLCIoeTE1LCB5MTIsIHkxMywgeTE0KSJdLFswLDUsIih6MCwgejEsIHoyLCB6MykiXSxbMiw1LCIoejUsIHo2LCB6NywgejQpIl0sWzQsNSwiKHoxMCwgejExLCB6MTgsIHo5KSJdLFs2LDUsIih6MTUsIHoxMiwgejEzLCB6MTQpIl0sWzAsNywiKHowLCB6MSwgejIsIHozKSIsWzMwMCw2MCw2MCwxXV0sWzIsNywiKHo0LCB6NSwgejYsIHo3KSIsWzMwMCw2MCw2MCwxXV0sWzQsNywiKHo4LCB6OSwgejEwLCB6MTEpIixbMzAwLDYwLDYwLDFdXSxbNiw3LCIoejEyLCB6MTMsIHoxNCwgejE1KSIsWzMwMCw2MCw2MCwxXV0sWzMsOCwiKHowLCB6MSwgejIsIHozKSwgKHo0LCB6NSwgejYsIHo3KSwgKHo4LCB6OSwgejEwLCB6MTEpLCAoejEyLCB6MTMsIHoxNCwgejE1KSIsWzI0MCw2MCw2MCwxXV0sWzMsMCwiKHkwLCB5MSwgeTIsIHkzKSwgKHk0LCB5NSwgeTYsIHk3KSwgKHk4LCB5OSwgeTEwLCB5MTEpLCAoeTEyLCB5MTMsIHkxNCwgeTE1KSJdLFswLDEsIih5MCwgeTEsIHkyLCB5MykiXSxbMiwxLCIoeTQsIHk1LCB5NiwgeTcpIl0sWzQsMSwiKHk4LCB5OSwgeTEwLCB5MTEpIl0sWzYsMSwiKHkxMiwgeTEzLHkxNCx5MTUpIl0sWzAsNCwicXVhcnRlcnJvdW5kIiwxXSxbMSw1LCJxdWFydGVycm91bmQiLDFdLFsyLDYsInF1YXJ0ZXJyb3VuZCIsMV0sWzMsNywicXVhcnRlcnJvdW5kIiwxXSxbNCw4LCJvcmRlcjFeey0xfSIsMV0sWzUsOSwib3JkZXIyXnstMX0iLDFdLFs2LDEwLCJvcmRlcjNeey0xfSIsMV0sWzcsMTEsIm9yZGVyNF57LTF9IiwxXSxbOSwxMiwiam9pbiIsMSx7ImNvbG91ciI6WzI0MCw2MCw2MF19LFsyNDAsNjAsNjAsMV1dLFs4LDEyLCJqb2luIiwxLHsiY29sb3VyIjpbMjQwLDYwLDYwXX0sWzI0MCw2MCw2MCwxXV0sWzEwLDEyLCJqb2luIiwxLHsiY29sb3VyIjpbMjQwLDYwLDYwXX0sWzI0MCw2MCw2MCwxXV0sWzExLDEyLCJqb2luIiwxLHsiY29sb3VyIjpbMjQwLDYwLDYwXX0sWzI0MCw2MCw2MCwxXV0sWzEzLDE0LCJmaXJzdCIsMV0sWzEzLDE1LCJzZWNvbmQiLDFdLFsxMywxNiwidGhpcmQiLDFdLFsxMywxNywiZm91cnRoIiwxXSxbMTQsMCwib3JkZXIxIiwxXSxbMTUsMSwib3JkZXIyIiwxXSxbMTYsMiwib3JkZXIzIiwxXSxbMTcsMywib3JkZXI0IiwxXSxbMTMsMTIsInJvd3JvdW5kIiwxLHsiY3VydmUiOjQsImNvbG91ciI6WzAsNjAsNjBdLCJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19LFswLDYwLDYwLDFdXSxbMTIsMTMsInJvd3JvdW5kXnstMX0iLDEseyJjdXJ2ZSI6NCwiY29sb3VyIjpbMCw2MCw2MF0sInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX0sWzAsNjAsNjAsMV1dXQ==)

-/

/-- Return the first row of a `matrixType` -/
def row1 : matrixType → vecType
| input := !![(input 0 0), (input 0 1), (input 0 2), (input 0 3)]

/-- Return the second row of a `matrixType` -/
def row2 : matrixType → vecType
| input := !![(input 0 4), (input 0 5), (input 0 6), (input 0 7)]

/-- Return the third row of a `matrixType` -/
def row3 : matrixType → vecType
| input := !![(input 0 8), (input 0 9), (input 0 10), (input 0 11)]

/-- Return the fourth row of a `matrixType` -/
def row4 : matrixType → vecType
| input := !![(input 0 12), (input 0 13), (input 0 14), (input 0 15)]

/-- Return `(y0, y1, y2, y3)` given `(y0, y1, y2, y3)`. This function is here
for completness, there is no need to use it as the output of `first` is already in order. -/
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

/-- Given an input `(y0, y1, y2, y3), (y4, y5, y6, y7), (y8, y9, y10, y11), (y12, y13, y14, y15)` return an
output `(z0, z1, z2, z3), (z4, z5, z6, z7), (z8, z9, z10, z11), (z12, z13, z14, z15)` applying the rowround
diagram. -/
noncomputable def rowround (input : matrixType) [is_iso( ↾ order1)] [is_iso( ↾ order2)] [is_iso( ↾ order3)]
  [is_iso( ↾ order4)] :=
!![
  (↾ row1 ≫ order1 ≫ quarterround ≫ inv order1) input,
  (↾ row2 ≫ order2 ≫ quarterround ≫ inv order1) input,
  (↾ row3 ≫ order3 ≫ quarterround ≫ inv order1) input,
  (↾ row4 ≫ order4 ≫ quarterround ≫ inv order1) input
]

/- `rowround⁻¹` is just the inverse given `rowround` is isomorphic. -/
noncomputable def rowround_inv (input : matrixType) [is_iso (↾ rowround)] := inv ↾ rowround

local notation `rowround⁻¹` := rowround_inv

end rowround
