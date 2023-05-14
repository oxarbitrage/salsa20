import category_theory.core
import category_theory.endofunctor.algebra

open category_theory

namespace quarterround

universe u

/-!
# Quarterround

We follow the flow of the quarterround graph to define objects and relations.

- [Quarterround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/quarterround.html)
-/

-- Objects / Nodes

/-- The type of the four random input objects. -/
variables y₀ y₁ y₂ y₃ : Type u

/-- The response type of the modulo addition operations. -/
variables m₀ m₁ m₂ m₃ : Type u

/-- The response type of the rotation operation. -/
variables r₀ r₁ r₂ r₃ : Type u

/-- The response type of the xor operations. -/
variables z₀ z₁ z₂ z₃ : Type u

-- Morphisms / Relations

local notation `typeZ₁` := y₀ × y₁ × y₂ × y₃ ⟶ y₀ × y₃ ⟶ m₁ ⟶ r₁ ⟶ y₁ × r₁ ⟶ z₁ 
/-- Given an input `y₀ × y₁ × y₂ × y₃` ∃ :
A morphism that will build the `y₀ × y₃` pair. This is `buildmod1` in the diagram.
A morphism from the pair to `m₁`. This `mod1` in the diagram.  
A morphism from `m₁` to `r₁`. This `rotl7` in the diagram.
A morphism to build the `y₁ × r₁` pair. This `buildxor1` in the diagram.  
A morphism from the pair to `z₁`. This `xor1` in the diagram. 
-/
variable Z₁ : typeZ₁

/-- The implementation of the `buildmod1` as a function. -/
def buildmod1 (input : y₀ × y₁ × y₂ × y₃) := (input.fst, input.snd.snd.snd)  
#check buildmod1 y₀ y₁ y₂ y₃

local notation `typeZ₂` := z₁ × y₀ ⟶ m₂ ⟶ r₂ ⟶ y₂ × r₂ ⟶ z₂
/-- Given `z₁` ∃ :
A morphism that will build the `z₀ × y₀` pair. This is `buildmod2` in the diagram.
A morphism from the pair to `m₂`. This `mod2` in the diagram.  
A morphism from `m₂` to `r₂`. This `rotl9` in the diagram.
A morphism to build the `y₂ × r₂` pair. This `buildxor2` in the diagram.  
A morphism from the pair to `z₂`. This `xor2` in the diagram. 
-/
variable Z₂ : typeZ₂

local notation `typeZ₃` := z₂ × z₁ ⟶ m₃ ⟶ r₃ ⟶ y₃ × r₃ ⟶ z₃
/-- Given `z₂` ∃ :
A morphism that will build the `z₂ × z₁` pair. This is `buildmod3` in the diagram.
A morphism from the pair to `m₃`. This `mod3` in the diagram.  
A morphism from `m₃` to `r₃`. This `rot13` in the diagram.
A morphism to build the `y₃ × r₃` pair. This `buildxor3` in the diagram.  
A morphism from the pair to `z₃`. This `xor3` in the diagram. 
-/
variable Z₃ : typeZ₃

local notation `typeZ₀` := z₃ × z₂ ⟶ m₀ ⟶ r₀ ⟶ y₀ × r₀ ⟶ z₀
/-- Given `z₃` ∃ :
A morphism that will build the `z₃ × z₂` pair. This is `buildmod0` in the diagram.
A morphism from the pair to `m₀`. This `mod0` in the diagram.  
A morphism from `m₀` to `r₀`. This `rot18` in the diagram.
A morphism to build the `y₀ × r₀` pair. This `buildxor0` in the diagram.  
A morphism from the pair to `z₀`. This `xor0` in the diagram. 
-/
variable Z₀ : typeZ₀

local notation `typeQr` := typeZ₁ ⟶ typeZ₂ ⟶ typeZ₃ ⟶ typeZ₀ ⟶ z₀ × z₁ × z₂ × z₃

variable Qr : typeQr

#check Qr

/-- We know there is an isomorphism between the inout and the output of the quarterround system. -/
variable I : y₀ × y₁ × y₂ × y₃ ≅ z₀ × z₁ × z₂ × z₃

/-- A quarterround input. -/
variable input : y₀ × y₁ × y₂ × y₃
/-- The quarterround function shortcut. -/
def quarterround := I.hom input

/-- A quarterround output. -/
variable output : z₀ × z₁ × z₂ × z₃
/-- The quarterround⁻¹ function shortcut.-/
def quarterround_inv := I.inv output

#check quarterround y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ I input
#check quarterround_inv y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ I output

variable [category (typeQr)]
/-- An endofunctor of `typeQr` type is our recursion. -/
variable EF : typeQr ⥤ typeQr

#check EF.obj
#check EF.map

variable Algebra : endofunctor.algebra EF

#check Algebra.A
#check Algebra.str

variables A₀ A₁ : endofunctor.algebra EF

variable TT : endofunctor.algebra.hom A₀ A₁

#check TT.f

end quarterround
