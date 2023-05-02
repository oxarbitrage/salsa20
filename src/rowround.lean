import category_theory.core

namespace rowround

universe u

/-!
# Rowround


We follow the flow of the rowround graph to define objects and relations.

- [Rowround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/rowround.html)
-/

/-- Stand alone 16 objects that form a rowround input. -/
variables y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ y₁₄ : Type u

/-- Represents a product of all rowround input objects. -/ 
variable y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ : Type u

/-!
Rowround can be done in paralell. 

First we define objects and morphisms that will split the input of 16 objects 
into 4 sub products of 4 objects each.

The full input `y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅` is isomorphic with each of its 4 slices.
This is because the inverse can be done by just putting the slice back in the input without doing
anything else.
-/

/-- Represent the object formed by the first part of the input. -/
variable y₀y₁y₂y₃ : Type u

/-- Given the rowround input as a product of 16, get the first 4 objects from it. -/
def first (I : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ≅ y₀y₁y₂y₃) := I.hom

/-- Represent the object formed by the second part of the input. -/
variable y₄y₅y₆y₇ : Type u

/-- Given the rowround input as a product of 16, get the second 4 objects from it. -/
def second (I : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ≅ y₄y₅y₆y₇) := I.hom

/-- Represent the object formed by the third part of the input. -/
variable y₈y₉y₁₀y₁₁ : Type u

/-- Given the rowround input as a product of 16, get the third 4 objects from it. -/
def third (I : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ≅ y₈y₉y₁₀y₁₁) := I.hom

/-- Represent the object formed by the fourth part of the input. -/
variable y₁₂y₁₃y₁₄y₁₅ : Type u

/-- Given the rowround input as a product of 16, get the third 4 objects from it. -/
def fourth (I : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ≅ y₁₂y₁₃y₁₄y₁₅) := I.hom

/-!
Before we send the objects to `quarterround` we need to put them in specific orders.

Again here we define the order morphisms from the isomorphisms between the input 4 objects product and
ordered output. 
-/

/-- Order the first product of objects in the needed position. 
This is here for completness as the first product is already in the right order.  -/
def order1 (I : y₀y₁y₂y₃ ≅ y₀y₁y₂y₃) := I.hom

/-- The result of an `order2` operation. -/
variable y₅y₆y₇y₄ : Type u

/-- Order the second product of objects in the needed position. -/
def order2 (I : y₄y₅y₆y₇ ≅ y₅y₆y₇y₄) := I.hom

/-- The result of an `order3` operation. -/
variable y₁₀y₁₁y₈y₉ : Type u

/-- Order the third product of objects in the needed position. -/
def order3 (I : y₈y₉y₁₀y₁₁ ≅ y₁₀y₁₁y₈y₉) := I.hom

/-- The result of an `order4` operation. -/
variable y₁₅y₁₂y₁₃y₁₄ : Type u

/-- Order the fourth product objects in the needed position. -/
def order4 (I : y₁₂y₁₃y₁₄y₁₅ ≅ y₁₅y₁₂y₁₃y₁₄) := I.hom

/-!
We now send ordered objects into `quarterround` operations and get the outputs.

Here we use the isomrphic property of the `quarterround` operation assumed in `quarterround.lean`.
-/

/-- The result of `quarterround1` operation. -/
variable z₀z₁z₂z₃ : Type u

/-- Apply `quarterround` to the first collection of object. -/
def quarterround1 (I : y₀y₁y₂y₃ ≅ z₀z₁z₂z₃) : y₀y₁y₂y₃ ⟶ z₀z₁z₂z₃ := I.hom

/-- The result of `quarterround2` operation. -/
variable z₅z₆z₇z₄ : Type u

/-- Apply `quarterround` to the second collection of object. -/
def quarterround2 (I : y₅y₆y₇y₄ ≅ z₅z₆z₇z₄) : y₅y₆y₇y₄ ⟶ z₅z₆z₇z₄ := I.hom

/-- The result of `quarterround3` operation. -/
variable z₁₀z₁₁z₈z₉ : Type u

/-- Apply `quarterround` to the third collection of object. -/
def quarterround3 (I : y₁₀y₁₁y₈y₉ ≅ z₁₀z₁₁z₈z₉) : y₁₀y₁₁y₈y₉ ⟶ z₁₀z₁₁z₈z₉ := I.hom

/-- The result of `quarterround4` operation. -/
variable z₁₅z₁₂z₁₃z₁₄ : Type u

/-- Apply `quarterround` to the fourth collection of object. -/
def quarterround4 (I : y₁₅y₁₂y₁₃y₁₄ ≅ z₁₅z₁₂z₁₃z₁₄) : y₁₅y₁₂y₁₃y₁₄ ⟶ z₁₅z₁₂z₁₃z₁₄ := I.hom

/-!
  Inverses of the order operations.

  After quarterround is applied we need to revert the positions modifictions we created in order functions.
-/

/-- The inverse of the `order1` operation given by the isomorphism. -/
def order1_inv (I : z₀z₁z₂z₃ ≅ z₀z₁z₂z₃) := I.hom

/-- Output of `order2⁻¹` -/
variable z₄z₅z₆z₇ : Type u

/-- The inverse of the `order2` operation given by the isomorphism. -/
def order2_inv (I : z₅z₆z₇z₄ ≅ z₄z₅z₆z₇) := I.hom

/-- Output of `order3⁻¹` -/
variable z₈z₉z₁₀z₁₁ : Type u

/-- The inverse of the `order3` operation given by the isomorphism. -/
def order3_inv (I : z₁₀z₁₁z₈z₉ ≅ z₈z₉z₁₀z₁₁) := I.hom

/-- Output of `order4⁻¹` -/
variable z₁₂z₁₃z₁₄z₁₅ : Type u

/-- The inverse of the `order4` operation given by the isomorphism. -/
def order4_inv (I : z₁₅z₁₂z₁₃z₁₄ ≅ z₁₂z₁₃z₁₄z₁₅) := I.hom

/-!
Finally we join all the pieces together to form the 16 objects product that represent the output of
the rowround system.
-/

/-- The rowround complete output as a product. -/
variable z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ : Type u

/-- Join the four paralell pieces together to form the rowround output. -/
def join (I : z₀z₁z₂z₃ × z₄z₅z₆z₇ × z₈z₉z₁₀z₁₁ × z₁₂z₁₃z₁₄z₁₅ ≅ z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅) :=
  I.hom


end rowround
