import category_theory.core

namespace rowround

universe u

/-!
# Rowround

We follow the flow of the rowround graph to define objects and relations.
[Rowround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/rowround.html)
-/

-- Objects / Nodes

/-- All objects to form a full input and its sub tuples. -/
variables y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ y₁₄ y₁₅ : Type u 

/-- All objects to form a full output and its sub tuples. -/
variables z₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃ z₁₄ z₁₅ : Type u

local notation `Y` := y₀ × y₁ × y₂ × y₃ × y₄ × y₅ × y₆ × y₇ × y₈ × y₉ × y₁₀ × y₁₁ × y₁₂ × y₁₃ × y₁₄ × y₁₅
local notation `Z` := z₀ × z₁ × z₂ × z₃ × z₄ × z₅ × z₆ × z₇ × z₈ × z₉ × z₁₀ × z₁₁ × z₁₂ × z₁₃ × z₁₄ × z₁₅

-- Morphisms / Relations.

local notation `typeQr₁` := Y ⟶ y₀ × y₁ × y₂ × y₃ ⟶ z₀ × z₁ × z₂ × z₃
/-- Given input as 16-tuple ∃ :
A morphism that will extract the `y₀ × y₁ × y₂ × y₃` tuple. This is `first` in the diagram.
A morphism from the above tuple to results. This `quarterround` in the diagram. 
-/
variable Qr₁ : typeQr₁

local notation `typeQr₂` := Y ⟶ y₄ × y₅ × y₆ × y₇ ⟶ y₅ × y₆ × y₇ × y₄ ⟶ z₅ × z₆ × z₇ × z₄ ⟶ z₄ × z₅ × z₆ × z₇
/-- Given input as 16-tuple ∃ :
A morphism that will extract the `y₄ × y₅ × y₆ × y₇` tuple. This is `second` in the diagram.
A morphism that will change the order of the `y₄ × y₅ × y₆ × y₇` tuple into `y₅ × y₆ × y₇ × y₄`. This is `order2` in the diagram.
A morphism from the order changed tuple to results. This `quarterround` in the diagram.  
A morphism that will change the order of results from `z₅ × z₆ × z₇ × z₄` to `z₄ × z₅ × z₆ × z₇`. This is `order2⁻¹` in the diagram.
-/
variable Qr₂ : typeQr₂

local notation `typeQr₃` := Y ⟶ y₈ × y₉ × y₁₀ × y₁₁ ⟶ y₁₀ × y₁₁ × y₈ × y₉ ⟶ z₁₀ × z₁₁ × z₈ × z₉ ⟶ z₈ × z₉ × z₁₀ × z₁₁
/-- Given input as 16-tuple ∃ :
A morphism that will extract the `y₈ × y₉ × y₁₀ × y₁₁` tuple. This is `third` in the diagram.
A morphism that will change the order of the `y₈ × y₉ × y₁₀ × y₁₁` tuple into `y₁₀ × y₁₁ × y₈ × y₉`. This is `order3` in the diagram.
A morphism from the order changed tuple to results. This `quarterround` in the diagram.  
A morphism that will change the order of the results from `z₁₀ × z₁₁ × z₈ × z₉` to `z₈ × z₉ × z₁₀ × z₁₁`. This is `order3⁻¹` in the diagram. 
-/
variable Qr₃ : typeQr₃

local notation `typeQr₄` := Y ⟶ y₁₂ × y₁₃ × y₁₄ × y₁₅ ⟶ y₁₅ × y₁₂ × y₁₃ × y₁₄ ⟶ z₁₅ × z₁₂ × z₁₃ × z₁₄ ⟶ z₁₂ × z₁₃ × z₁₄ × z₁₅
/-- Given input as 16-tuple ∃ :
A morphism that will exatrct the `y₁₂ × y₁₃ × y₁₄ × y₁₅` tuple. This is `fourth` in the diagram.
A morphism that will change the order of the `y₁₂ × y₁₃ × y₁₄ × y₁₅` tuple into `y₁₅ × y₁₂ × y₁₃ × y₁₄`. This is `order4` in the diagram.
A morphism from the order changed tuple results. This `quarterround` in the diagram.  
A morphism that will change the order of the results from `z₁₅ × z₁₂ × z₁₃ × z₁₄` to `z₁₂ × z₁₃ × z₁₄ × z₁₅`. This is `order4⁻¹` in the diagram. 
-/
variable Qr₄ : typeQr₄

local notation `typeRowRound` := typeQr₁ × typeQr₂ × typeQr₃ × typeQr₄
/-- The rowround is the product of the four qr types (`typeQr₁`, `typeQr₂`, `typeQr₃` and `typeQr₄`).
This qr types can run in parallel. -/
variable RowRound : typeRowRound

#check RowRound

/-- We know there is an isomorphism between the input and the output of the quarterround system. -/
variable I : Y ≅ Z

/-- A rowround input. -/
variable input : Y
/-- The rowround function shortcut. -/
def rowround := I.hom input

/-- A rowround output. -/
variable output : Z
/-- The rowround⁻¹ function shortcut.-/
def rowround_inv := I.inv output


end rowround
