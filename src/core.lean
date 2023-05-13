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
variables x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ : Type u

/-- Middle state, after doubleround10 was applied but not modmatrix yet. -/
variables y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ y₁₄ y₁₅ : Type u

/-- The mod_matrix output type. -/
variables z₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃ z₁₄ z₁₅ : Type u

/-- Create an input object. -/
variable X : x₀ × x₁ × x₂ × x₃ × x₄ × x₅ × x₆ × x₇ × x₈ × x₉ × x₁₀ × x₁₁ × x₁₂ × x₁₃ × x₁₄ × x₁₅

/-- Create the doubleround10 input object. -/
variable Y : y₀ × y₁ × y₂ × y₃ × y₄ × y₅ × y₆ × y₇ × y₈ × y₉ × y₁₀ × y₁₁ × y₁₂ × y₁₃ × y₁₄ × y₁₅

/-- Matrix mod operation signature. -/
variable mod_matrix : (x₀ × x₁ × x₂ × x₃ × x₄ × x₅ × x₆ × x₇ × x₈ × x₉ × x₁₀ × x₁₁ × x₁₂ × x₁₃ × x₁₄ × x₁₅) × 
  (y₀ × y₁ × y₂ × y₃ × y₄ × y₅ × y₆ × y₇ × y₈ × y₉ × y₁₀ × y₁₁ × y₁₂ × y₁₃ × y₁₄ × y₁₅) ⟶ 
  z₀ × z₁ × z₂ × z₃ × z₄ × z₅ × z₆ × z₇ × z₈ × z₉ × z₁₀ × z₁₁ × z₁₂ × z₁₃ × z₁₄ × z₁₅

/-- Core is actually just calling `mod_matrix`. -/
def core : z₀ × z₁ × z₂ × z₃ × z₄ × z₅ × z₆ × z₇ × z₈ × z₉ × z₁₀ × z₁₁ × z₁₂ × z₁₃ × z₁₄ × z₁₅ := mod_matrix (X, Y)

end core
