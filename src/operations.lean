import params

import category_theory.category.basic
import category_theory.core

open params

open category_theory

namespace operations

variable [category (bitvec word_len)]

/-!
# Operations

Building blocks operations.

The salsa20 cipher is built fully with add-rotate-XOR operations.

## Rotate

Converts a bitvec into another bitvec of the same length by appling rotation operations at the bit level. 

- [Example implementation](https://github.com/alexwebr/salsa20/blob/master/salsa20.c#L6)
- [Diagram](https://q.uiver.app/?q=WzAsMixbMCwwLCJhIl0sWzAsMywiYiJdLFswLDEsInJvdGwiLDIseyJjdXJ2ZSI6Mn1dLFsxLDAsInJvdGxeey0xfSIsMix7ImN1cnZlIjoyfV1d)
- Input and output objects of any rotate operations are isomorphic.
-/

/-- The rotate operation in a bitvec with a shift of 5. Only used in an example. -/
def rotl5 : bitvec word_len → bitvec word_len
| a := (a.shl 5).or (a.ushr (word_len - 5))

/-- The rotate operation in a bitvec with a shift of 7. -/
@[simp] def rotl7 : bitvec word_len → bitvec word_len
| a := (a.shl 7).or (a.ushr (word_len - 7))

/-- The rotate operation in a bitvec with a shift of 9. -/
@[simp] def rotl9 : bitvec word_len → bitvec word_len
| a := (a.shl 9).or (a.ushr (word_len - 9))

/-- The rotate operation in a bitvec with a shift of 13. -/
@[simp] def rotl13 : bitvec word_len → bitvec word_len
| a := (a.shl 13).or (a.ushr (word_len - 13))

/-- The rotate operation in a bitvec with a shift of 18. -/
@[simp] def rotl18 : bitvec word_len → bitvec word_len
| a := (a.shl 18).or (a.ushr (word_len - 18))

/-- Inverse of the `rotl5` operation. Only used in an example. -/
def rotl5_inv : bitvec word_len → bitvec word_len
| a := (a.ushr 5).or (a.shl (word_len - 5))

/-- Inverse of the `rotl7` operation. -/
def rotl7_inv : bitvec word_len → bitvec word_len
| a := (a.ushr 7).or (a.shl (word_len - 7))

/-- Inverse of the `rotl9` operation. -/
def rotl9_inv : bitvec word_len → bitvec word_len
| a := (a.ushr 9).or (a.shl (word_len - 9))

/-- Inverse of the `rotl13` operation. -/
def rotl13_inv : bitvec word_len → bitvec word_len
| a := (a.ushr 13).or (a.shl (word_len - 13))

/-- Inverse of the `rotl18` operation. -/
def rotl18_inv : bitvec word_len → bitvec word_len
| a := (a.ushr 18).or (a.shl (word_len - 18))

-- Notation for the inverses.
local notation `rotl5⁻¹` := rotl5_inv
local notation `rotl7⁻¹` := rotl7_inv
local notation `rotl9⁻¹` := rotl9_inv
local notation `rotl13⁻¹` := rotl13_inv
local notation `rotl18⁻¹` := rotl18_inv

/-- `rotl5⁻¹` after `rotl5` produces the identity given isomorphism.  -/
lemma rotl5_inv_is_inverse_of_rotl5 (I : rotl5 ≅ rotl5⁻¹): I.hom ≫ I.inv = 𝟙 rotl5 := 
  by exact I.hom_inv_id'

/-- `rotl7⁻¹` after `rotl7` produces the identity given isomorphism.  -/
lemma rotl7_inv_is_inverse_of_rotl7 (I : rotl7 ≅ rotl7⁻¹): I.hom ≫ I.inv = 𝟙 rotl7 := 
  by exact I.hom_inv_id'

/-- `rotl9⁻¹` after `rotl9` produces the identity given isomorphism.  -/
lemma rotl9_inv_is_inverse_of_rotl9 (I : rotl9 ≅ rotl9⁻¹): I.hom ≫ I.inv = 𝟙 rotl9 := 
  by exact I.hom_inv_id'

/-- `rotl13⁻¹` after `rotl13` produces the identity given isomorphism.  -/
lemma rotl13_inv_is_inverse_of_rotl13 (I : rotl13 ≅ rotl13⁻¹): I.hom ≫ I.inv = 𝟙 rotl13 := 
  by exact I.hom_inv_id'

/-- `rotl18⁻¹` after `rotl18` produces the identity given isomorphism.  -/
lemma rotl18_inv_is_inverse_of_rotl18 (I : rotl18 ≅ rotl18⁻¹): I.hom ≫ I.inv = 𝟙 rotl18 :=
  by exact I.hom_inv_id'

/-!
## Add

Converts a pair of bitvecs into a single bitvec of the same length by appling bitwise modulo addition. 

- [Example implementation](https://stackoverflow.com/a/19760152)
- [Diagram](https://q.uiver.app/?q=WzAsMixbMCwwLCIoYSwgYikiXSxbMCwzLCJjIl0sWzAsMSwibW9kIl1d)
- Input and output objects of the mod operation are not isomoprhic. No inverse exist.
-/

/-- Modulo addition operation. -/
@[simp] def mod : (bitvec word_len × bitvec word_len) → bitvec word_len
| (a, b) := (bitvec.and (a + b) (max_bitvec))

/-!
## XOR

Converts a pair of bitvecs into a single bitvec of the same length by appling bitwise XOR. 

- [Diagram](https://q.uiver.app/?q=WzAsMixbMCwwLCIoYSwgYikiXSxbMCwzLCJjIl0sWzAsMSwibW9kIl1d)
- Input and output objects of the xor operation are isomoprhic. XOR is its own inverse.
-/

/-- The salsa20 xor operation is just bitwise xor. -/
@[simp] def xor : (bitvec word_len × bitvec word_len) → bitvec word_len
| (a, b) := a.xor b

/-- `xor` after `xor` produces the identity.  -/
lemma xor_is_inverse_of_xor (I : xor ≅ xor): I.hom ≫ I.inv = 𝟙 xor :=
begin
  exact I.hom_inv_id',
end

end operations
