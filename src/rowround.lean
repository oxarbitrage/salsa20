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
-/

/-- Represent the object formed by the first part of the input. -/
variable y₀y₁y₂y₃ : Type u

/-- Given the full input as a product of 16, get the first 4 objects of it. -/
variable first : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ⟶ y₀y₁y₂y₃

/-- Represent the object formed by the second part of the input. -/
variable y₄y₅y₆y₇ : Type u

/-- Given the full input as a product of 16, get the second 4 objects of it. -/
variable second : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ⟶ y₄y₅y₆y₇

/-- Represent the object formed by the third part of the input. -/
variable y₈y₉y₁₀y₁₁ : Type u

/-- Given the full input as a product of 16, get the third 4 objects of it. -/
variable third : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ⟶ y₈y₉y₁₀y₁₁

/-- Represent the object formed by the fourth part of the input. -/
variable y₁₂y₁₃y₁₄y₁₅ : Type u

/-- Given the full input as a product of 16, get the third 4 objects of it. -/
variable fourth : y₀y₁y₂y₃y₄y₅y₆y₇y₈y₉y₁₀y₁₁y₁₂y₁₃y₁₄y₁₅ ⟶ y₁₂y₁₃y₁₄y₁₅

/-!
Before we send the objects to `quarterround` we need to put them in specific orders.
-/

/-- Order the first product of objects in the needed position. 
This is here for completness as the first product is already in the right order.  -/
variable order1 : y₀y₁y₂y₃ ⟶ y₀y₁y₂y₃

/-- The result of an `order2` operation. -/
variable y₅y₆y₇y₄ : Type u

/-- Order the second product of objects in the needed position. -/
variable order2 : y₄y₅y₆y₇ ⟶ y₅y₆y₇y₄

/-- The result of an `order3` operation. -/
variable y₁₀y₁₁y₈y₉ : Type u

/-- Order the third product of objects in the needed position. -/
variable order3 : y₈y₉y₁₀y₁₁ ⟶ y₁₀y₁₁y₈y₉

/-- The result of an `order4` operation. -/
variable y₁₅y₁₂y₁₃y₁₄ : Type u

/-- Order the fourth product objects in the needed position. -/
variable order4 : y₁₂y₁₃y₁₄y₁₅ ⟶ y₁₅y₁₂y₁₃y₁₄

/-!
We now send ordered objects into `quarterround` operations and get the outputs.
-/

/-- The result of `quarterround1` operation. -/
variable z₀z₁z₂z₃ : Type u

/-- Apply `quarterround` to the first collection of object. -/
variable quarterround1 : y₀y₁y₂y₃ ⟶ z₀z₁z₂z₃

/-- Isomorphism between input and output `quarterround1` objects. -/
variable quarterround1_is_iso : y₀y₁y₂y₃ ≅ z₀z₁z₂z₃

/-- The result of `quarterround2` operation. -/
variable z₅z₆z₇z₄ : Type u

/-- Apply `quarterround` to the second collection of object. -/
variable quarterround2 : y₅y₆y₇y₄ ⟶ z₅z₆z₇z₄

/-- Isomorphism between input and output `quarterround2` objects. -/
variable quarterround2_is_iso : y₅y₆y₇y₄ ≅ z₅z₆z₇z₄

/-- The result of `quarterround3` operation. -/
variable z₁₀z₁₁z₈z₉ : Type u

/-- Apply `quarterround` to the third collection of object. -/
variable quarterround3 : y₁₀y₁₁y₈y₉ ⟶ z₁₀z₁₁z₈z₉

/-- Isomorphism between input and output `quarterround3` objects. -/
variable quarterround3_is_iso : y₁₀y₁₁y₈y₉ ≅ z₁₀z₁₁z₈z₉

/-- The result of `quarterround4` operation. -/
variable z₁₅z₁₂z₁₃z₁₄ : Type u

/-- Apply `quarterround` to the fourth collection of object. -/
variable quarterround4 : y₁₅y₁₂y₁₃y₁₄ ⟶ z₁₅z₁₂z₁₃z₁₄

/-- Isomorphism between input and output `quarterround4` objects. -/
variable quarterround4_is_iso : z₁₅z₁₂z₁₃z₁₄ ≅ y₁₅y₁₂y₁₃y₁₄

/-!
  Inverses of the order operations.

  After quarterround is applied we need to revert the positions modifictions we created in order functions.
-/


/-- `order1` and `order1⁻¹` outputs are isomrphic. -/
variable order1_iso : z₀z₁z₂z₃ ≅ y₀y₁y₂y₃

/-- The inverse of the `order1` operation given by the isomorphism. -/
def order1_inv := order1_iso.inv

/-- Output of `order2⁻¹` -/
variable z₄z₅z₆z₇ : Type u

/-- `order2` and `order2⁻¹` outputs are isomrphic. -/
variable order2_iso : z₄z₅z₆z₇ ≅ y₄y₅y₆y₇

/-- The inverse of the `order2` operation given by the isomorphism. -/
def order2_inv := order2_iso.inv

/-- Output of `order3⁻¹` -/
variable z₈z₉z₁₀z₁₁ : Type u

/-- `order3` and `order3⁻¹` outputs are isomrphic. -/
variable order3_iso : z₈z₉z₁₀z₁₁ ≅ y₈y₉y₁₀y₁₁

/-- The inverse of the `order3` operation given by the isomorphism. -/
def order3_inv := order3_iso.inv

/-- Output of `order4⁻¹` -/
variable z₁₂z₁₃z₁₄z₁₅ : Type u

/-- `order4` and `order4⁻¹` outputs are isomrphic. -/
variable order4_iso : z₁₂z₁₃z₁₄z₁₅ ≅ y₁₂y₁₃y₁₄y₁₅

/-- The inverse of the `order4` operation given by the isomorphism. -/
def order4_inv := order4_iso.inv

/-!
Finally we join all the pieces together to form the 16 objects product that represent the output of
the rowround system.
-/

/-- The rowround complete output as a product. -/
variable z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅ : Type u

/-- Join the four paralell pieces together to form the rowround output. -/
variable join : (z₀z₁z₂z₃ × z₄z₅z₆z₇ × z₈z₉z₁₀z₁₁ × z₁₂z₁₃z₁₄z₁₅) ⟶ z₀z₁z₂z₃z₄z₅z₆z₇z₈z₉z₁₀z₁₁z₁₂z₁₃z₁₄z₁₅


end rowround
