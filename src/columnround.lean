import rowround

open rowround

namespace columnround

universe u

/-!
# Columnround

The `columnround` system using the equivalent formula.

- [Columnround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/columnround.html)

-/

/-- Represents a product of all columnround input objects. -/
variable x₀x₁x₂x₃x₄x₅x₆x₇x₈₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ : Type u

/-- The transpose of the input. -/
variable x₀x₄x₈x₁₂x₁x₅x₉x₁₃x₂x₆x₁₀x₁₄x₃x₇x₁₁x₁₅ : Type u

variable I1 : x₀x₁x₂x₃x₄x₅x₆x₇x₈₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ ≅ x₀x₄x₈x₁₂x₁x₅x₉x₁₃x₂x₆x₁₀x₁₄x₃x₇x₁₁x₁₅

variable y₀y₄y₈y₁₂y₁y₅y₉y₁₃y₂y₆y₁₀y₁₄y₃y₇y₁₁y₁₅ : Type u

variable I2 : x₀x₄x₈x₁₂x₁x₅x₉x₁₃x₂x₆x₁₀x₁₄x₃x₇x₁₁x₁₅ ≅ y₀y₄y₈y₁₂y₁y₅y₉y₁₃y₂y₆y₁₀y₁₄y₃y₇y₁₁y₁₅

/-- We use the equivalent formula from the spec and run `rowround` with a transposed input. 
This will return the output unsorted.  -/
def columnround_unsorted := rowround x₀x₄x₈x₁₂x₁x₅x₉x₁₃x₂x₆x₁₀x₁₄x₃x₇x₁₁x₁₅ y₀y₄y₈y₁₂y₁y₅y₉y₁₃y₂y₆y₁₀y₁₄y₃y₇y₁₁y₁₅

variable y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ : Type u

variable I3 : y₀y₄y₈y₁₂y₁y₅y₉y₁₃y₂y₆y₁₀y₁₄y₃y₇y₁₁y₁₅ ≅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅

/-- There is an isomoprhism between the unsorted and the unsorted output. We use it to return the fianl columnround output. -/
def columnround := columnround_unsorted x₀x₄x₈x₁₂x₁x₅x₉x₁₃x₂x₆x₁₀x₁₄x₃x₇x₁₁x₁₅ y₀y₄y₈y₁₂y₁y₅y₉y₁₃y₂y₆y₁₀y₁₄y₃y₇y₁₁y₁₅ I2 ≫ I3.hom

end columnround
