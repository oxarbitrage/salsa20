import doubleround

open doubleround

namespace core

universe u

/-!
  # Core

  The `core` function takes a `matrixType` and return a new `matrixType` after applying the diagram.

  - [Core Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/core.html)
-/

/-- Input object. -/
variable x₀x₁x₂x₃x₄x₅x₆x₇x₈x₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ : Type u

/-- Middle state, after doubleround10 was applied but not modmatrix yet. -/
variable y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ : Type u

/-- The mod_matrix output. -/
variable z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ : Type u

/-- Do modulo operation with the input and the doubleround10 output. -/
def mod_matrix := (x₀x₁x₂x₃x₄x₅x₆x₇x₈x₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ × y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅) ⟶ 
  z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅

#check mod_matrix x₀x₁x₂x₃x₄x₅x₆x₇x₈x₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅

/-- Core is actually just calling `mod_matrix`. -/
def core := mod_matrix x₀x₁x₂x₃x₄x₅x₆x₇x₈x₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅

#check core x₀x₁x₂x₃x₄x₅x₆x₇x₈x₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅

end core
