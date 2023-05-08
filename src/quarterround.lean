import category_theory.core

namespace quarterround

universe u

/-!
# Quarterround

We follow the flow of the quarterround graph to define objects and relations.

- [Quarterround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/quarterround.html)
-/

/-- The type of the four random input objects. -/
variables y₀ y₁ y₂ y₃ : Type u

/-- The input type as the product of four random input objects. -/
variable y₀y₁y₂y₃ : Type u

/-- The response type of the modulo addition operations. -/
variables m₀ m₁ m₂ m₃ : Type u

/-- The response type of the rotation operation. -/
variables r₀ r₁ r₂ r₃ : Type u

/-- The response type of the xor operations. -/
variables z₀ z₁ z₂ z₃ : Type u

/-- The result type of a full `quarterround` operation. -/
variable z₀z₁z₂z₃ : Type u

/-- The four isomorphisms that exists between the product object and the four individual objects. -/
variables (I₀ : y₀y₁y₂y₃ ≅ y₀) (I₁ : y₀y₁y₂y₃ ≅ y₁) (I₂ : y₀y₁y₂y₃ ≅ y₂) (I₃ : y₀y₁y₂y₃ ≅ y₃)

/-- The four isomorphisms that exists between the output objects of the mod and the rotl operations. -/
variables (I'₀ : m₀ ≅ r₀) (I'₁ : m₁ ≅ r₁) (I'₂ : m₂ ≅ r₂) (I'₃ : m₃ ≅ r₃)

/-- The isomorphism that exists between an input and an output object. -/
variable I'' : y₀y₁y₂y₃ ≅ z₀z₁z₂z₃

/-- Create an object of type input. -/
variable Y : y₀y₁y₂y₃

/-- Create rotation response objects. -/
variables (R₀ : r₀) (R₁ : r₁) (R₂ : r₂) (R₃ : r₃)

/-- Create quarterround output objects. -/
variables (Z₀ : z₀) (Z₁ : z₁) (Z₂ : z₂) (Z₃ : z₃)

/-- The `mod1` input is a pair formed from morphisms of `I₀` and `I₃` isomorphisms. -/
def mod1_input := (I₀.hom Y, I₃.hom Y)

/-- The signture of the `mod1` operation. -/
variable mod1 : y₀ × y₃ ⟶ m₁

/-- The output of the `mod1` operation is with the proper arguments a `m₁` object. -/
def mod1_output : m₁ := mod1 (mod1_input y₀ y₃ y₀y₁y₂y₃ I₀ I₃ Y)

#check mod1_output y₀ y₃ y₀y₁y₂y₃
#check mod1_output y₀ y₃ y₀y₁y₂y₃ m₁ I₀ I₃ Y

/-- The `rotl7` operation. -/
def rotl7 := I'₁.hom

/-- The input of the `xor1` operation. -/
def xor1_input := (I₁.hom, r₁)

/-- The signture of the `xor1` operation. -/
variable xor1 : y₁ × r₁ ⟶ z₁

/-- The output of the `xor1` operation is with the proper arguments a `z₁` object. -/
def xor1_output : z₁ := xor1 ((xor1_input y₁ y₀y₁y₂y₃ r₁ I₁).fst Y, R₁)

/-- The `mod2` input is a pair formed with `z₁` and the `I₀` isomorphism. -/
def mod2_input : z₁ × y₀ := (Z₁, I₀.hom Y)

/-- The signture of the `mod2` operation. -/
variable mod2 : z₁ × y₀ ⟶ m₂

/-- The output of the `mod2` operation is with the proper arguments a `m₂` object. -/
def mod2_output : m₂ := mod2 (mod2_input y₀ y₀y₁y₂y₃ z₁ I₀ Y Z₁)

#check mod2_input y₀ y₀y₁y₂y₃ z₁ I₀ Y Z₁

/-- The `rotl9` operation. -/
def rotl9 := I'₂.hom

/-- The input of the `xor2` operation. -/
def xor2_input := (I₂.hom, r₂)

/-- The signture of the `xor2` operation. -/
variable xor2 : y₂ × r₂ ⟶ z₂

/-- The output of the `xor2` operation is with the proper arguments a `z₂` object. -/
def xor2_output : z₂ := xor2 ((xor2_input y₂ y₀y₁y₂y₃ r₂ I₂).fst Y, R₂)

/-- The `mod3` input is a pair formed of `z₂` and `z₁` objects. -/
def mod3_input := (Z₂, Z₁)

/-- The signature of the `mod3` operation. -/
variable mod3 : z₂ × z₁ ⟶ m₃

/-- The output of the `mod3` operation is with the proper arguments a `m₃` object. -/
def mod3_output : m₃ := mod3 (mod3_input z₁ z₂ Z₁ Z₂)

#check mod3_input z₁ z₂ Z₁ Z₂

/-- The `rotl13` operation. -/
def rotl13 := I'₃.hom

/-- The input of the `xor3` operation. -/
def xor3_input := (I₃.hom, r₃)

/-- The signture of the `xor3` operation. -/
variable xor3 : y₃ × r₃ ⟶ z₃

/-- The output of the `xor3` operation is with the proper arguments a `z₃` object. -/
def xor3_output : z₃ := xor3 ((xor3_input y₃ y₀y₁y₂y₃ r₃ I₃).fst Y, R₃)

/-- The `mod0` input is a pair formed of `z₃` and `z₂` objects. -/
def mod0_input := (Z₃, Z₂)

/-- The `mod0` signature -/
variable mod0 : z₃ × z₂ ⟶ m₀

/-- The output of the `mod0` operation is with the proper arguments a `m₀` object. -/
def mod0_output : m₀ := mod0 (mod0_input z₂ z₃ Z₂ Z₃)

/-- The `rotl13` operation. -/
def rotl18 (I : m₀ ≅ r₀) := I.hom

/-- The input of the `xor0` operation. -/
def xor0_input := (I₀.hom, r₀)

/-- The signture of the `xor0` operation. -/
variable xor0 : y₀ × r₀ ⟶ z₀

/-- The output of the `xor0` operation is with the proper arguments a `z₀` object. -/
def xor0_output : z₀ := xor0 ((xor0_input y₀ y₀y₁y₂y₃ r₀ I₀).fst Y, R₀)

/-- The quarterround function as the morphism of the existing isomorphism between input and output. -/
def quarterround := I''.hom

/-- The quarterround inverse function as the inverse morphism of the existing isomorphism between input and output. -/
def quarterround_inv := I''.inv

end quarterround
