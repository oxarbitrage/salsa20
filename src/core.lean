import doubleround

open doubleround

namespace core

universe u

/-!
# Core

Build core objects and relations using the diagram.
- [Core Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/core.html)
-/

/-- Core Input object type. -/
variable x₀x₁x₂x₃x₄x₅x₆x₇x₈x₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ : Type u

/-- Middle state, after doubleround10 was applied but not modmatrix yet. -/
variable y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ : Type u

/-- The mod_matrix output type. -/
variable z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ : Type u

/-- Create an input object. -/
variable X : x₀x₁x₂x₃x₄x₅x₆x₇x₈x₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅

/-- Create the doubleround10 input object. -/
variable Y : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅

/-- Matrix mod operation signature. -/
variable mod_matrix : (x₀x₁x₂x₃x₄x₅x₆x₇x₈x₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ × y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅) ⟶ 
  z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅

/-- Core is actually just calling `mod_matrix`. -/
def core : z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ := mod_matrix (X, Y)

end core
