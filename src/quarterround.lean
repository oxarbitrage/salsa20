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
constant m₁ : Type u

/-- The `mod1` relation given `y₀` and `y₃` objects. -/
def mod1 (I0 : y₀y₁y₂y₃ ≅ y₀) (I3 : y₀y₁y₂y₃ ≅ y₃) := m₁

/-- The response of a `rotl7` operation as an object of the `Type u` category. -/
variable r₁ : Type u

/-- The `rotl7` operation will get the result of `mod1` as an input and return an `r₁` object of 
the `Type u` category. -/
noncomputable def rotl7 (I : m₁ ≅ r₁) := I.hom

/-- The result of `xor1` operation betwen `y₁` and `r₁` is an object of the `Type u` category. -/
constant z₁ : Type u

/-- The `xor1` operation return `z₁`. -/
def xor1 (I0 : y₀y₁y₂y₃ ≅ y₁) := z₁

/-- The response of the `mod2` operation as an object of the `Type u` category. -/
constant m₂ : Type u

/-- The `mod2` relation given `z₁` and `y₀` objects. -/
def mod2 (I : y₀y₁y₂y₃ ≅ y₀) := m₂

/-- The response of a `rotl9` operation as an object of the `Type u` category. -/
variable r₂ : Type u

/-- The `rotl9` operation will get the result of `mod2` as an input and return an `r₂` object of 
the `Type u` category. -/
noncomputable def rotl9 (I : m₂ ≅ r₂) := I.hom

/-- The result of `xor2` operation betwen `y₁` and `r₂` is an object of the `Type u` category. -/
constant z₂ : Type u

/-- The `xor2` operation return `z₂`. -/
def xor2 (I : y₀y₁y₂y₃ ≅ y₂) := z₂

/-- The response of the `mod3` operation as an object of the `Type u` category. -/
constant m₃ : Type u

/-- The `mod3` relation given `z₂` and `z₁` objects. -/
noncomputable def mod3 := m₃

/-- The response of a `rotl13` operation as an object of the `Type u` category. -/
variable r₃ : Type u

/-- The `rotl13` operation will get the result of `mod3` as an input and return an `r₃` object of 
the `Type u` category. -/
noncomputable def rotl13 (I : m₃ ≅ r₃) := I.hom

/-- The result of `xor3` operation betwen `y₃` and `r₃` is an object of the `Type u` category. -/
variable z₃ : Type u

/-- The `xor3` operation return `z₃`. -/
def xor3 (I : y₀y₁y₂y₃ ≅ y₃) := z₃

/-- The response of the `mod0` operation as an object of the `Type u` category. -/
constant m₀ : Type u

/-- The `mod0` relation given `z₃` and `z₂` objects. -/
noncomputable def mod0 := m₀

/-- The response of a `rotl18` operation as an object of the `Type u` category. -/
variable r₀ : Type u

/-- The `rotl18` operation will get the result of `mod0` as an input and return an `r₀` object of 
the `Type u` category. -/
noncomputable def rotl18 (I : m₀ ≅ r₀) := I.hom

/-- The result of `xor0` operation betwen `y₀` and `r₀` is an object of the `Type u` category. -/
variable z₀ : Type u

/-- The `xor0` operation return `z₀`. -/
def xor0 (I : y₀y₁y₂y₃ ⟶ y₀) := z₀ 

/-- The result of a full `quarterround` operation. -/
variable z₀z₁z₂z₃ : Type u

/-- Convert an object of `Type u` into another object of `Type u`. -/
def quarterround (I : y₀y₁y₂y₃ ≅ z₀z₁z₂z₃) := I.hom

/-- Quarterround inverse. -/
def quarterround_inv (I : y₀y₁y₂y₃ ≅ z₀z₁z₂z₃) := I.inv

end quarterround
