import operations
import params

import category_theory.category.basic

open operations
open params

open category_theory

namespace operations_examples

variable [category (bitvec word_len)]

/-!
  # Formalized examples from the spec

  https://cr.yp.to/snuffle/spec.pdf

  Notes:

  - Examples are formalized as `lemma`s instead of `example`
  so they show up in the documentation.
-/

/-- 0xc0a8787e ⊕ 0x9fd1161d = 0x5f796e63 -/
lemma example_xor : xor (0xc0a8787e, 0x9fd1161d) = 0x5f796e63 := by refl

/-- 0xc0a8787e + 0x9fd1161d = 0x60798e9b -/
lemma example_mod : mod (0xc0a8787e, 0x9fd1161d) = 0x60798e9b :=
begin
  rw [operations.mod, params.max_bitvec, params.mod, word_len],
  unfold bitvec.of_nat,
  norm_num1,
  refl,
end

/-- 0xc0a8787e <<< 5 = 0x150f0fd8 -/
lemma example_rotl : rotl5 0xc0a8787e = 0x150f0fd8 := by refl

/-! # Inverse examples -/

/-- 0x5f796e63 ⊕ 0x9fd1161d = 0xc0a8787e -/
lemma example_inverse_xor : xor (0x5f796e63, 0x9fd1161d) = 0xc0a8787e := by refl

/-- 0x150f0fd8 <<<⁻¹ 5 = 0xc0a8787e -/
lemma example_rotl_inv : rotl5_inv 0x150f0fd8 = 0xc0a8787e := by refl

end operations_examples
