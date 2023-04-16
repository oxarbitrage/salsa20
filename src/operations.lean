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
- [Diagram](https://q.uiver.app/?q=WzAsMixbMCwwLCJhIl0sWzAsMywiYiJdLFswLDEsInJvdGwiLDIseyJjdXJ2ZSI6Mn1dLFsxLDAsInJvdGxeey0xfSIsMix7ImN1cnZlIjoyfV1d)
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

/- `rotl7⁻¹` is just the inverse given `rotl7` is isomorphic. -/
noncomputable def rotl7_inv (a : wordType) [is_iso (↾ rotl7)] := inv ↾ rotl7

/- `rotl9⁻¹` is just the inverse given `rotl9` is isomorphic. -/
noncomputable def rotl9_inv (a : wordType) [is_iso (↾ rotl9)] := inv ↾ rotl9

/- `rotl13⁻¹` is just the inverse given `rotl13` is isomorphic. -/
noncomputable def rotl13_inv (a : wordType) [is_iso (↾ rotl13)] := inv ↾ rotl13

/- `rotl18⁻¹` is just the inverse given `rotl18` is isomorphic. -/
noncomputable def rotl18_inv (a : wordType) [is_iso (↾ rotl18)] := inv ↾ rotl18

-- Notation for the inverses.
local notation `rotl7⁻¹` := rotl7_inv
local notation `rotl9⁻¹` := rotl9_inv
local notation `rotl13⁻¹` := rotl13_inv
local notation `rotl18⁻¹` := rotl18_inv

/-!
## Add

Converts a pair of bitvecs into a single bitvec of the same length by appling bitwise modulo addition. 

- [Example implementation](https://stackoverflow.com/a/19760152)
- [Diagram](https://q.uiver.app/?q=WzAsMixbMCwwLCIoYSwgYikiXSxbMCwzLCJjIl0sWzAsMSwibW9kIl1d)
- No inverse exist.
-/

/-- Modulo addition operation. -/
def mod : (wordType × wordType) → wordType
| (a, b) := (bitvec.and (a + b) (max_bitvec))

/-!
## XOR

Converts a pair of bitvecs into a single bitvec of the same length by appling bitwise XOR. 

- [Diagram](https://q.uiver.app/?q=WzAsMixbMCwwLCIoYSwgYikiXSxbMCwzLCJjIl0sWzAsMSwibW9kIl1d)
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
