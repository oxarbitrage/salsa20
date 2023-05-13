import rowround

open rowround

namespace columnround

universe u

/-!
# Columnround

The `columnround` system using the equivalent formula.

- [Columnround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/columnround.html)
TODO: fix the above diagram to transpose before and after.
-/

/-- All objects to form a full input. -/
variables x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ : Type u

/-- All objects to form a full output. -/
variables y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ y₁₄ y₁₅ : Type u

local notation `typeColumnRound` := x₀ × x₁ × x₂ × x₃ × x₄ × x₅ × x₆ × x₇ × x₈ × x₉ × x₁₀ × x₁₁ × x₁₂ × x₁₃ × x₁₄ × x₁₅ ⟶
  x₀ × x₄ × x₈ × x₁₂ × x₁ × x₅ × x₉ × x₁₃ × x₂ × x₆ × x₁₀ × x₁₄ × x₃ × x₇ × x₁₁ × x₁₅ ⟶ 
  y₀ × y₄ × y₈ × y₁₂ × y₁ × y₅ × y₉ × y₁₃ × y₂ × y₆ × y₁₀ × y₁₄ × y₃ × y₇ × y₁₁ × y₁₅ ⟶ 
  y₀ × y₁ × y₂ × y₃ × y₄ × y₅ × y₆ × y₇ × y₈ × y₉ × y₁₀ × y₁₁ × y₁₂ × y₁₃ × y₁₄ × y₁₅

/-- There is an isomorphism between an input and the output. -/
variable I : x₀ × x₁ × x₂ × x₃ × x₄ × x₅ × x₆ × x₇ × x₈ × x₉ × x₁₀ × x₁₁ × x₁₂ × x₁₃ × x₁₄ × x₁₅ ≅ 
  y₀ × y₁ × y₂ × y₃ × y₄ × y₅ × y₆ × y₇ × y₈ × y₉ × y₁₀ × y₁₁ × y₁₂ × y₁₃ × y₁₄ × y₁₅



end columnround
