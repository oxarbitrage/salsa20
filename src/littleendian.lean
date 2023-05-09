import category_theory.core
import data.nat.digits

open category_theory
open nat

namespace littleendian

/-!
  # Littleendian

  The `littleendian` function and its inverse.
-/

/- Needed for `littleendian`, `of_digits`. -/
variables [semiring (list ℕ)]

/-- Lean library has `of_digits` code for this so we use it. 
TODO : Explain why it works with base 256.
-/
def littleendian (l : list ℕ) : list ℕ := of_digits 256 l

/-- Lean library has `digits` code for this so we use it. 
TODO : Explain why it works with base 256.
-/
def littleendian_inv (l : list ℕ) : list ℕ := digits 256 (l.nth 0).iget

/-- Define a category for functions from `list ℕ` to `list ℕ`-/
variable [category (list ℕ → list ℕ)]

/- Just some notation for inverse. -/
local notation `littleendian⁻¹` := littleendian_inv

/-- We assume there is an isomorphism between `littleindian` and `littleendian⁻¹`.
In other words, `littleendian` function is invertible and the inverse is `littleendian⁻¹`. -/
lemma littleendian_is_inv (I : littleendian ≅ littleendian⁻¹) : I.hom ≫ I.inv = 𝟙 littleendian :=
  by rw [iso.hom_inv_id]


end littleendian
