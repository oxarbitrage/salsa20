import category_theory.core

namespace rowround

universe u

/-!
# Rowround

We follow the flow of the rowround graph to define objects and relations.

- [Rowround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/rowround.html)
-/

-- Object types.

/-- Represents a product of all rowround input objects. -/
variable y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ : Type u

/-- Represent the object formed by the first part of the input. -/
variables y₀y₁y₂y₃ y₄y₅y₆y₇ y₈y₉y₁₀y₁₁ y₁₂y₁₃y₁₄y₁₅ : Type u

/-- The result of an `order2`, `order3` and `order4` operation.
The result of `order1` is not here as it is the same as its input `y₀y₁y₂y₃`.
-/
variables y₅y₆y₇y₄ y₁₀y₁₁y₈y₉ y₁₅y₁₂y₁₃y₁₄ : Type u

/-- The result of `quarterround1`, `quarterround2`, `quarterround3` and `quarterround4`  operations. -/
variables z₀z₁z₂z₃ z₅z₆z₇z₄ z₁₀z₁₁z₈z₉ z₁₅z₁₂z₁₃z₁₄ : Type u

/-- Output of `order2⁻¹`, `order3⁻¹` and `order4⁻¹`.
The result of `order1⁻¹` is not here as it is the same as its input `z₀z₁z₂z₃`.
-/
variables z₄z₅z₆z₇ z₈z₉z₁₀z₁₁ z₁₂z₁₃z₁₄z₁₅ : Type u

/-- The type of the rowround output as a product. -/
variable z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ : Type u

-- Isomorphisms.

/-- Isomorphisms between the input and its pieces. -/
variables (I₁ : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ≅ y₀y₁y₂y₃)
  (I₂ : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ≅ y₄y₅y₆y₇)
  (I₃ : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ≅ y₈y₉y₁₀y₁₁)
  (I₄ : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ≅ y₁₂y₁₃y₁₄y₁₅)

/-- Isomorphisms between input ordered and unordered pieces. -/
variables (I'₁ : y₀y₁y₂y₃ ≅ y₀y₁y₂y₃) (I'₂ : y₄y₅y₆y₇ ≅ y₅y₆y₇y₄) (I'₃ : y₈y₉y₁₀y₁₁ ≅ y₁₀y₁₁y₈y₉) 
  (I'₄ : y₁₂y₁₃y₁₄y₁₅ ≅ y₁₅y₁₂y₁₃y₁₄)

/-- Isomorphisms between the unordered input pieces and output unordered results. -/
variables (I''₁ : y₀y₁y₂y₃ ≅ z₀z₁z₂z₃) (I''₂ : y₅y₆y₇y₄ ≅ z₅z₆z₇z₄) (I''₃ : y₁₀y₁₁y₈y₉ ≅ z₁₀z₁₁z₈z₉)
  (I''₄ : y₁₅y₁₂y₁₃y₁₄ ≅ z₁₅z₁₂z₁₃z₁₄)

/-- Isomorphisms between the unordered outputs and ordered ones. -/
variables (I'''₁ : z₀z₁z₂z₃ ≅ z₀z₁z₂z₃) (I'''₂ : z₅z₆z₇z₄ ≅ z₄z₅z₆z₇) (I'''₃ : z₁₀z₁₁z₈z₉ ≅ z₈z₉z₁₀z₁₁)
  (I'''₄ : z₁₅z₁₂z₁₃z₁₄ ≅ z₁₂z₁₃z₁₄z₁₅)

/-- Isomorphism between a product of output ordered pieces and a full output. -/
variable Ij : z₀z₁z₂z₃ × z₄z₅z₆z₇ × z₈z₉z₁₀z₁₁ × z₁₂z₁₃z₁₄z₁₅ ≅ z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅

/-- The isomorphisms between the input and the output of rowround. -/
variable Ir : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ≅ z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅

/-- Create an object of the type input. -/
variable Y : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅

-- Relations.

/-- Given the rowround input as a product of 16, get the first 4 objects from it. -/
def first := I₁.hom

lemma first_is_invertible : I₁.hom ≫ I₁.inv = 𝟙 y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ :=
  by simp only [category_theory.iso.hom_inv_id]

/-- Given the rowround input as a product of 16, get the second 4 objects from it. -/
def second := I₂.hom

/-- Given the rowround input as a product of 16, get the third 4 objects from it. -/
def third := I₃.hom

/-- Given the rowround input as a product of 16, get the fourth 4 objects from it. -/
def fourth := I₄.hom

/-!
Before we send the objects to `quarterround` we need to put them in specific orders.

Again here we define the order morphisms from the isomorphisms between the input 4 objects product and
ordered output. 
-/

/-- Order the first product of objects in the needed position.
This is here for completness as the first product is already in the right order.  -/
def order1 := I'₁.hom

/-- Order the second product of objects in the needed position. -/
def order2 := I'₂.hom

/-- Order the third product of objects in the needed position. -/
def order3 := I'₃.hom

/-- Order the fourth product objects in the needed position. -/
def order4 := I'₄.hom

/-!
We now send ordered objects into `quarterround` operations and get the outputs.

Here we use the isomrphism property of the `quarterround` operation assumed in `quarterround.lean`.
-/

/-- Apply `quarterround` to the first collection of object. -/
def quarterround1 : y₀y₁y₂y₃ ⟶ z₀z₁z₂z₃ := I''₁.hom

/-- Apply `quarterround` to the second collection of object. -/
def quarterround2 : y₅y₆y₇y₄ ⟶ z₅z₆z₇z₄ := I''₂.hom

/-- Apply `quarterround` to the third collection of object. -/
def quarterround3 : y₁₀y₁₁y₈y₉ ⟶ z₁₀z₁₁z₈z₉ := I''₃.hom

/-- Apply `quarterround` to the fourth collection of object. -/
def quarterround4 : y₁₅y₁₂y₁₃y₁₄ ⟶ z₁₅z₁₂z₁₃z₁₄ := I''₄.hom

/-!
  Inverses of the order operations.

  After quarterround is applied we need to revert the positions modifictions we did in order functions.
-/

/-- The inverse of the `order1` operation. -/
def order1_inv := I'''₁.hom

/-- The inverse of the `order2` operation. -/
def order2_inv := I'''₂.hom

/-- The inverse of the `order3` operation. -/
def order3_inv := I'''₃.hom

/-- The inverse of the `order4` operation. -/
def order4_inv := I'''₄.hom

/-!
Finally we join all the pieces together to form the 16 objects product that represent the output of
the rowround system.
-/

/-- Join the four paralell pieces together to form the rowround output. -/
def join := Ij.hom

def rowround := Ir.hom

def rowround_inv := Ir.inv

lemma rowround_is_invertible : Ir.hom ≫ Ir.inv = 𝟙 y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ :=
  by simp only [category_theory.iso.hom_inv_id]

end rowround
