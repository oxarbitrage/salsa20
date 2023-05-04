import category_theory.core

namespace quarterround

universe u

/-!
# Quarterround

We follow the flow of the quarterround graph to define objects and relations.

We don't care what the functions do but just the objects and relations between them.

- [Quarterround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/quarterround.html)
-/

/-- 4 objects that form a quarterround input. -/ 
variables y₀ y₁ y₂ y₃ : Type u

/-- Represents a product of input objects. -/ 
variable y₀y₁y₂y₃ : Type u

/-- The response of the `mod1` operation as an object of the `Type u` category. -/
variable m₁ : Type u

variables (I₀ : y₀y₁y₂y₃ ≅ y₀) (I₁ : y₀y₁y₂y₃ ≅ y₁) (I₂ : y₀y₁y₂y₃ ≅ y₂) (I₃ : y₀y₁y₂y₃ ≅ y₃)

/-- Create an object of type input. -/
variable A : y₀y₁y₂y₃

/-- The `mod1` input is formed from morphisms of two given isomorphisms. -/
def mod1_input := (I₀.hom A, I₃.hom A)

/-- The signture of the mod1 operation. -/
variable mod1 : y₀ × y₃ ⟶ m₁

def mod1_output : m₁ := mod1 (mod1_input y₀ y₃ y₀y₁y₂y₃ I₀ I₃ A)

#check mod1_output y₀ y₃ y₀y₁y₂y₃

#check mod1_output y₀ y₃ y₀y₁y₂y₃ m₁ I₀ I₃ A

/-- The response of a `rotl7` operation as an object of the `Type u` category. -/
variable r₁ : Type u

/-- The `rotl7` operation will get the result of `mod1` as an input and return an `r₁` object of 
the `Type u` category. -/
def rotl7 (I : m₁ ≅ r₁) := I.hom

/-- The result of `xor1` operation betwen `y₁` and `r₁` is an object of the `Type u` category. -/
variable z₁ : Type u

def xor1_input := (I₁.hom, r₁)

/-- The `xor1` operation takes `y1` and `r₁` to return `z₁`. -/
variable xor1 : y₁ × r₁ ⟶ z₁

variable R₁ : r₁
def xor1_output : z₁ := xor1 ((xor1_input y₁ y₀y₁y₂y₃ I₁ r₁).fst A, R₁)

/-- The response of the `mod2` operation as an object of the `Type u` category. -/
constant m₂ : Type u

/-- The `mod2` input is formed from morphism of two given isomorphisms. -/
def mod2_input := (z₁, I₀.hom A)

/-- TODO : this should be z₁ × y₀ -/
variable mod2 : Type u × y₀ ⟶ m₂

def mod2_output : m₂ := mod2 (mod2_input y₀ y₀y₁y₂y₃ I₀ A z₁)

#check mod2_input y₀ y₀y₁y₂y₃ I₀ A z₁

/-- The response of a `rotl9` operation as an object of the `Type u` category. -/
variable r₂ : Type u

/-- The `rotl9` operation will get the result of `mod2` as an input and return an `r₂` object of 
the `Type u` category. -/
noncomputable def rotl9 (I : m₂ ≅ r₂) := I.hom

/-- The result of `xor2` operation betwen `y₁` and `r₂` is an object of the `Type u` category. -/
constant z₂ : Type u

def xor2_input := (I₂.hom, r₂)

/-- The `xor2` operation takes `y₂` and `r₂` to return `z₂`. -/
variable xor2 : y₂ × r₂ ⟶ z₂

variable R₂ : r₂
/-- The `xor2` operation return `z₂`. -/
def xor2_output : z₂ := xor2 ((xor2_input y₂ y₀y₁y₂y₃ I₂ r₂).fst A, R₂)

/-- The response of the `mod3` operation as an object of the `Type u` category. -/
constant m₃ : Type u

/-- The `mod2` input is formed from morphism of two given isomorphisms. -/
noncomputable def mod3_input := (z₂, z₁)

/-- TODO : this should be z₂ × z₁ -/
variable mod3 : Type u × Type u ⟶ m₃

noncomputable def mod3_output : m₃ := mod3 (mod3_input y₀y₁y₂y₃)

/-- The response of a `rotl13` operation as an object of the `Type u` category. -/
variable r₃ : Type u

/-- The `rotl13` operation will get the result of `mod3` as an input and return an `r₃` object of 
the `Type u` category. -/
noncomputable def rotl13 (I : m₃ ≅ r₃) := I.hom

/-- The result of `xor3` operation betwen `y₃` and `r₃` is an object of the `Type u` category. -/
variable z₃ : Type u

def xor3_input := (I₃.hom, r₃)

/-- The `xor3` operation takes `y₃` and `r₃` to return `z₃`. -/
variable xor3 : y₃ × r₃ ⟶ z₃

variable R₃ : r₃
/-- The `xor3` operation return `z₃`. -/
def xor3_output : z₃ := xor3 ((xor3_input y₃ y₀y₁y₂y₃ I₃ r₃).fst A, R₃)

/-- The response of the `mod0` operation as an object of the `Type u` category. -/
constant m₀ : Type u

/-- The `mod2` input is formed from morphism of two given isomorphisms. -/
noncomputable def mod0_input := (z₂, z₁)

/-- TODO : this should be z₃ × z₂ -/
variable mod0 : Type u × Type u ⟶ m₀

noncomputable def mod0_output : m₀ := mod0 (mod0_input z₂)

/-- The response of a `rotl18` operation as an object of the `Type u` category. -/
variable r₀ : Type u

/-- The `rotl18` operation will get the result of `mod0` as an input and return an `r₀` object of 
the `Type u` category. -/
noncomputable def rotl18 (I : m₀ ≅ r₀) := I.hom

/-- The result of `xor0` operation betwen `y₀` and `r₀` is an object of the `Type u` category. -/
variable z₀ : Type u

def xor0_input := (I₀.hom, r₀)

/-- The `xor3` operation takes `y₀` and `r₀` to return `z₀`. -/
variable xor0 : y₀ × r₀ ⟶ z₀

variable R₀ : r₀
/-- The `xor0` operation return `z₀`. -/
def xor0_output : z₀ := xor0 ((xor0_input y₀ y₀y₁y₂y₃ I₀ r₀).fst A, R₀)

/-- The result of a full `quarterround` operation. -/
variable z₀z₁z₂z₃ : Type u

/-- Convert an object of `Type u` into another object of `Type u`. -/
def quarterround (I : y₀y₁y₂y₃ ≅ z₀z₁z₂z₃) := I.hom

/-- Quarterround inverse. -/
def quarterround_inv (I : y₀y₁y₂y₃ ≅ z₀z₁z₂z₃) := I.inv

end quarterround
