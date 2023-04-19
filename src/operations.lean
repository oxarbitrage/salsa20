import types

import category_theory.core

open types
open params

open category_theory

open_locale category_theory.Type

namespace operations

variable [category (wordType)]

/-!
# Operations

Building blocks operations.

The salsa20 cipher is built fully with add-rotate-XOR operations.

## Rotate

Converts a bitvec into another bitvec of the same length by appling left rotations at the bit level. 

- [Example implementation](https://github.com/alexwebr/salsa20/blob/master/salsa20.c#L6)
- [Rotate Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/rotate.html)
-/

/-- The rotate operation in a bitvec with a shift of 7. -/
def rotl7 : wordType → wordType
| a := (a.shl 7).or (a.ushr (word_len - 7))

/-- The rotate operation in a bitvec with a shift of 9. -/
def rotl9 : wordType → wordType
| a := (a.shl 9).or (a.ushr (word_len - 9))

/-- The rotate operation in a bitvec with a shift of 13. -/
def rotl13 : wordType → wordType
| a := (a.shl 13).or (a.ushr (word_len - 13))

/-- The rotate operation in a bitvec with a shift of 18. -/
def rotl18 : wordType → wordType
| a := (a.shl 18).or (a.ushr (word_len - 18))

/-- All rotation operation has inverses. -/
--variables [is_iso (↾ rotl7)] [is_iso (↾ rotl9)] [is_iso (↾ rotl13)] [is_iso (↾ rotl18)]

/- `rotl7⁻¹` is just the inverse given `rotl7` is isomorphic. -/
noncomputable def rotl7_inv [is_iso (↾ rotl7)] := inv ↾ rotl7

/- `rotl9⁻¹` is just the inverse given `rotl9` is isomorphic. -/
noncomputable def rotl9_inv [is_iso (↾ rotl9)] := inv ↾ rotl9

/- `rotl13⁻¹` is just the inverse given `rotl13` is isomorphic. -/
noncomputable def rotl13_inv [is_iso (↾ rotl13)] := inv ↾ rotl13

/- `rotl18⁻¹` is just the inverse given `rotl18` is isomorphic. -/
noncomputable def rotl18_inv [is_iso (↾ rotl18)] := inv ↾ rotl18

-- Notation for the inverses.
local notation `rotl7⁻¹` := rotl7_inv
local notation `rotl9⁻¹` := rotl9_inv
local notation `rotl13⁻¹` := rotl13_inv
local notation `rotl18⁻¹` := rotl18_inv

/-- `rotl7⁻¹` is the inverse of `rotl7`.  -/
lemma rotl7_is_inverse (a : wordType) [is_iso (↾ rotl7)] (I : rotl7 a ≅ rotl7⁻¹ a) : I.hom ≫ I.inv = 𝟙 (rotl7 a) :=
  by exact I.hom_inv_id'

/-- `rotl9⁻¹` is the inverse of `rotl9`.  -/
lemma rotl9_is_inverse (a : wordType) [is_iso (↾ rotl9)] (I : rotl9 a ≅ rotl9⁻¹ a) : I.hom ≫ I.inv = 𝟙 (rotl9 a) :=
  by exact I.hom_inv_id'

/-- `rotl13⁻¹` is the inverse of `rotl13`.  -/
lemma rotl13_is_inverse (a : wordType) [is_iso (↾ rotl13)] (I : rotl13 a ≅ rotl13⁻¹ a) : I.hom ≫ I.inv = 𝟙 (rotl13 a) :=
  by exact I.hom_inv_id'

/-- `rotl18⁻¹` is the inverse of `rotl18`.  -/
lemma rot18_is_inverse (a : wordType) [is_iso (↾ rotl18)] (I : rotl18 a ≅ rotl18⁻¹ a) : I.hom ≫ I.inv = 𝟙 (rotl18 a) :=
  by exact I.hom_inv_id'


/-!
## Add

Converts a pair of bitvecs into a single bitvec of the same length by appling bitwise modulo addition. 

- [Example implementation](https://stackoverflow.com/a/19760152)
- [Modulo addition diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/mod.html)
- No inverse exist.
-/

/-- Modulo addition operation. -/
def mod : (wordType × wordType) → wordType
| (a, b) := (bitvec.and (a + b) (max_bitvec))

/-!
## XOR

Converts a pair of bitvecs into a single bitvec of the same length by appling bitwise XOR. 

- [XOR diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/xor.html)
- XOR is its own inverse.
-/

/-- The salsa20 xor operation is just bitwise xor. -/
def xor : (wordType × wordType) → wordType
| (a, b) := a.xor b

/-- `xor` after `xor` produces the identity.  -/
lemma xor_is_inverse_of_xor (I : xor ≅ xor): I.hom ≫ I.inv = 𝟙 xor :=
begin
  exact I.hom_inv_id',
end

end operations
