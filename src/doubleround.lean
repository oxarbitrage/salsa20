import columnround

open columnround
open rowround

namespace doubleround

universe u

/-!
# Doubleround

The `doubleround` applies columnround of an input and then, with the results, applies rowround to it returning a final output.

- [Doubleround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/doubleround.html)
-/

/-- Variables to form the input type. -/
variables x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ : Type u

/-- Variables to form the middle state type, after columnround was applied but not rowround yet. -/
variables y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ y₁₄ y₁₅ : Type u

/-- Variables to form the final state type, after columnround and rowround were applied. -/
variables z₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃ z₁₄ z₁₅ : Type u

local notation `typeDoubleRound` := x₀ × x₁ × x₂ × x₃ × x₄ × x₅ × x₆ × x₇ × x₈ × x₉ × x₁₀ × x₁₁ × x₁₂ × x₁₃ × x₁₄ × x₁₅ ⟶
  y₀ × y₁ × y₂ × y₃ × y₄ × y₅ × y₆ × y₇ × y₈ × y₉ × y₁₀ × y₁₁ × y₁₂ × y₁₃ × y₁₄ × y₁₅ ⟶
  z₀ × z₁ × z₂ × z₃ × z₄ × z₅ × z₆ × z₇ × z₈ × z₉ × z₁₀ × z₁₁ × z₁₂ × z₁₃ × z₁₄ × z₁₅

variable I : x₀ × x₁ × x₂ × x₃ × x₄ × x₅ × x₆ × x₇ × x₈ × x₉ × x₁₀ × x₁₁ × x₁₂ × x₁₃ × x₁₄ × x₁₅ ≅ 
  x₀ × x₁ × x₂ × x₃ × x₄ × x₅ × x₆ × x₇ × x₈ × x₉ × x₁₀ × x₁₁ × x₁₂ × x₁₃ × x₁₄ × x₁₅

def doubleround := I.hom

def doubleround10 := I.hom ≫ I.hom ≫ I.hom ≫ I.hom ≫ I.hom ≫ I.hom ≫ I.hom ≫ I.hom ≫ I.hom ≫ I.hom

#check doubleround10

end doubleround
