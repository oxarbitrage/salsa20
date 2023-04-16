import doubleround

import category_theory.core

open doubleround
open rowround
open params
open types

open category_theory
open_locale category_theory.Type

namespace core

variable [category (wordType)]

--
variables [is_iso( ↾ order1)] [is_iso( ↾ order2)] [is_iso( ↾ order3)] [is_iso( ↾ order4)]

/-!
  # Core

  The `core` function takes a `matrixType` and return a new `matrixType` after applying the diagram.

  - [Core Diagram](https://q.uiver.app/?q=WzAsMyxbMCwwLCIoeDAsIHgxLCB4MiwgeDMpLCAoeDQsIHg1LCB4NiwgeDcpLCAoeDgsIHg5LCB4MTAsIHgxMSksICh4MTIsIHgxMywgeDE0LCB4MTUpIl0sWzQsMCwiKHkwLCB5MSwgeTIsIHkzKSwgKHk0LCB5NSwgeTYsIHk3KSwgKHk4LCB5OSwgeTEwLCB5MTEpLCAoeTEyLCB5MTMsIHkxNCwgeDE1KSJdLFsyLDEsIih6MCwgejEsIHoyLCB6MyksICh6NCwgejUsIHo2LCB6NyksICh6OCwgejksIHoxMCwgejExKSwgKHoxMiwgejEzLCB6MTQsIHoxNSkiXSxbMCwxLCJkb3VibGVyb3VuZDEwIiwxXSxbMSwyLCJtb2RtYXRyaXgiLDFdLFswLDIsIm1vZG1hdHJpeCIsMV1d)

-/

/-- Apply double round 10 times to an input. -/
noncomputable def doubleround10 (X : matrixType) :=
  (↾ doubleround ≫ ↾ doubleround ≫ ↾ doubleround ≫ ↾ doubleround ≫ ↾ doubleround ≫ 
  ↾ doubleround ≫ ↾ doubleround ≫ ↾ doubleround ≫ ↾ doubleround ≫ ↾ doubleround) X

/- The inverse of `doubleround10`. -/
noncomputable def doubleround10_inv (input : matrixType) [is_iso (↾ doubleround10)] := inv ↾ doubleround10

/- Just some notation for inverse. -/
local notation `doubleround10⁻¹` := doubleround10_inv

/-- Do modulo addition for each matrix item. -/
def mod_matrix (X Y : matrixType) := !![
  operations.mod ((X 0 0), (Y 0 0)),
  operations.mod ((X 0 1), (Y 0 1)),
  operations.mod ((X 0 2), (Y 0 2)),
  operations.mod ((X 0 3), (Y 0 3));

  operations.mod ((X 1 0), (Y 1 0)),
  operations.mod ((X 1 1), (Y 1 1)),
  operations.mod ((X 1 2), (Y 1 2)),
  operations.mod ((X 1 3), (Y 1 3));

  operations.mod ((X 2 0), (Y 2 0)),
  operations.mod ((X 2 1), (Y 2 1)),
  operations.mod ((X 2 2), (Y 2 2)),
  operations.mod ((X 2 3), (Y 2 3));

  operations.mod ((X 3 0), (Y 3 0)),
  operations.mod ((X 3 1), (Y 3 1)),
  operations.mod ((X 3 2), (Y 3 2)),
  operations.mod ((X 3 3), (Y 3 3));
]

/-- Do addition modulo 2³² between the input and the `doubleround10` of the input. -/
noncomputable def core (X : matrixType) : matrixType := mod_matrix (doubleround10 X) X


end core
