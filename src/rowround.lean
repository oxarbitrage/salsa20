import category_theory.core

namespace rowround

universe u

/-!
# Rowround

We follow the flow of the rowround graph to define objects and relations.

- [Rowround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/rowround.html)
-/

-- Objects / Nodes

/-- All objects to form a full input and its sub pairs. -/
variables y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ y₁₄ y₁₅ : Type u 

/-- All objects to form a full output and its sub pairs. -/
variables z₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃ z₁₄ z₁₅ : Type u

-- Morphisms / Relations.

local notation `typeQr₁` := y₀ × y₁ × y₂ × y₃ × y₄ × y₅ × y₆ × y₇ × y₈ × y₉ × y₁₀ × y₁₁ × y₁₂ × y₁₃ × y₁₄ × y₁₅ ⟶ 
  y₀ × y₁ × y₂ × y₃ ⟶ z₀ × z₁ × z₂ × z₃
/-- Given input as 16-tuple ∃ :
- A morphism that will build the `y₀ × y₁ × y₂ × y₃` tuple. This is `first` in the diagram.
- A morphism from the above tuple to results. This `quarterround` in the diagram.  
-/
variable Qr₁ : typeQr₁

local notation `typeQr₂` := y₀ × y₁ × y₂ × y₃ × y₄ × y₅ × y₆ × y₇ × y₈ × y₉ × y₁₀ × y₁₁ × y₁₂ × y₁₃ × y₁₄ × y₁₅ ⟶ 
  y₄ × y₅ × y₆ × y₇ ⟶ y₅ × y₆ × y₇ × y₄ ⟶ z₅ × z₆ × z₇ × z₄ ⟶ z₄ × z₅ × z₆ × z₇
/-- Given input as 16-tuple ∃ :
- A morphism that will build the `y₄ × y₅ × y₆ × y₇` tuple. This is `second` in the diagram.
- A morphism that will order the `y₄ × y₅ × y₆ × y₇` tuple into `y₅ × y₆ × y₇ × y₄`. This is `order2` in the diagram.
- A morphism from the above tuple to unorded results. This `quarterround` in the diagram.  
- A morphism that will order the `z₅ × z₆ × z₇ × z₄` tuple into `z₄ × z₅ × z₆ × z₇`. This is `order2⁻¹` in the diagram.
-/
variable Qr₂ : typeQr₂

local notation `typeQr₃` := y₀ × y₁ × y₂ × y₃ × y₄ × y₅ × y₆ × y₇ × y₈ × y₉ × y₁₀ × y₁₁ × y₁₂ × y₁₃ × y₁₄ × y₁₅ ⟶ 
  y₈ × y₉ × y₁₀ × y₁₁ ⟶ y₁₀ × y₁₁ × y₈ × y₉ ⟶ z₁₀ × z₁₁ × z₈ × z₉ ⟶ z₈ × z₉ × z₁₀ × z₁₁
/-- Given input as 16-tuple ∃ :
- A morphism that will build the `y₈ × y₉ × y₁₀ × y₁₁` tuple. This is `third` in the diagram.
- A morphism that will order the `y₈ × y₉ × y₁₀ × y₁₁` tuple into `y₁₀ × y₁₁ × y₈ × y₉`. This is `order3` in the diagram.
- A morphism from the above tuple to unorded results. This `quarterround` in the diagram.  
- A morphism that will order the `z₁₀ × z₁₁ × z₈ × z₉` tuple into `z₈ × z₉ × z₁₀ × z₁₁`. This is `order3⁻¹` in the diagram.
-/
variable Qr₃ : typeQr₃

local notation `typeQr₄` := y₀ × y₁ × y₂ × y₃ × y₄ × y₅ × y₆ × y₇ × y₈ × y₉ × y₁₀ × y₁₁ × y₁₂ × y₁₃ × y₁₄ × y₁₅ ⟶ 
  y₁₂ × y₁₃ × y₁₄ × y₁₅ ⟶ y₁₅ × y₁₂ × y₁₃ × y₁₄ ⟶ z₁₅ × z₁₂ × z₁₃ × z₁₄ ⟶ z₁₂ × z₁₃ × z₁₄ × z₁₅
/-- Given input as 16-tuple ∃ :
- A morphism that will build the `y₁₂ × y₁₃ × y₁₄ × y₁₅` tuple. This is `fourth` in the diagram.
- A morphism that will order the `y₁₂ × y₁₃ × y₁₄ × y₁₅` tuple into `y₁₅ × y₁₂ × y₁₃ × y₁₄`. This is `order4` in the diagram.
- A morphism from the above tuple to unorded results. This `quarterround` in the diagram.  
- A morphism that will order the `z₁₅ × z₁₂ × z₁₃ × z₁₄` tuple into `z₁₂ × z₁₃ × z₁₄ × z₁₅`. This is `order4⁻¹` in the diagram.
-/
variable Qr₄ : typeQr₄

local notation `typeRowRound` := typeQr₁ × typeQr₂ × typeQr₃ × typeQr₄

/-- We know there is an isomorphism between the inout and the output of the quarterround system. -/
variable I : y₀ × y₁ × y₂ × y₃ × y₄ × y₅ × y₆ × y₇ × y₈ × y₉ × y₁₀ × y₁₁ × y₁₂ × y₁₃ × y₁₄ × y₁₅ ≅ 
  z₀ × z₁ × z₂ × z₃ × z₄ × z₅ × z₆ × z₇ × z₈ × z₉ × z₁₀ × z₁₁ × z₁₂ × z₁₃ × z₁₄ × z₁₅

/-- A rowround input. -/
variable input : y₀ × y₁ × y₂ × y₃ × y₄ × y₅ × y₆ × y₇ × y₈ × y₉ × y₁₀ × y₁₁ × y₁₂ × y₁₃ × y₁₄ × y₁₅
/-- The rowround function shortcut. -/
def rowround := I.hom input

/-- A rowround output. -/
variable output : z₀ × z₁ × z₂ × z₃ × z₄ × z₅ × z₆ × z₇ × z₈ × z₉ × z₁₀ × z₁₁ × z₁₂ × z₁₃ × z₁₄ × z₁₅
/-- The rowround⁻¹ function shortcut.-/
def quarterround_inv := I.inv output


end rowround
