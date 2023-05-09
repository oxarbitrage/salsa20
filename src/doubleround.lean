import columnround

open columnround
open rowround

namespace doubleround

universe u

/-!
# Doubleround

The `doubleround` function takes a `matrixType` and return a new `matrixType` applying the diagram.

- [Doubleround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/doubleround.html)
-/

/-- Input type. -/
variable x₀x₁x₂x₃x₄x₅x₆x₇x₈x₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ : Type u

/-- Middle state type, after columnround was applied but not rowround yet. -/
variable y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ : Type u

/-- Final state type, after columnround and rowround were applied. -/
variable z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ : Type u

/-- The isomorphism between columnround input and output. -/
variable I₁ : x₀x₁x₂x₃x₄x₅x₆x₇x₈x₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ ≅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅

/-- The isomorphism between columnround output and rowround input. -/
variable I₂ : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ≅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅

/-- The isomorphism between the rowround output and the doubleround output. -/
variable I₃ : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ≅ z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅

variable I₄ : z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ ≅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅

/-- The doubleround is columnround followed by rowround. -/
def doubleround := (columnround x₀x₁x₂x₃x₄x₅x₆x₇x₈x₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅
  y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ I₁ I₂) ≫ 
  (rowround y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ I₃)

def doubleround10 := 
  (doubleround x₀x₁x₂x₃x₄x₅x₆x₇x₈x₉x₁₀x₁₁x₁₂x₁₃x₁₄x₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅
  z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ I₁ I₂ I₃) ≫
  (doubleround z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅
  z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ I₄ I₂ I₃) ≫
  (doubleround z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅
  z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ I₄ I₂ I₃) ≫
  (doubleround z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅
  z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ I₄ I₂ I₃) ≫
  (doubleround z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅
  z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ I₄ I₂ I₃) ≫
  (doubleround z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅
  z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ I₄ I₂ I₃) ≫
  (doubleround z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅
  z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ I₄ I₂ I₃) ≫
  (doubleround z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅
  z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ I₄ I₂ I₃) ≫
  (doubleround z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅
  z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ I₄ I₂ I₃) ≫
  (doubleround z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅
  z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ I₄ I₂ I₃)

end doubleround
