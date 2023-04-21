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
def rotl7_f : wordType → wordType
| a := (a.shl 7).or (a.ushr (word_len - 7))

/-- The `rotl7_f` function as a morphism. -/
def rotl7 := ↾ rotl7_f

/-- The rotate operation in a bitvec with a shift of 9. -/
def rotl9_f : wordType → wordType
| a := (a.shl 9).or (a.ushr (word_len - 9))

/-- The `rotl9_f` function as a morphism. -/
def rotl9 := ↾ rotl9_f

/-- The rotate operation in a bitvec with a shift of 13. -/
def rotl13_f : wordType → wordType
| a := (a.shl 13).or (a.ushr (word_len - 13))

/-- The `rotl13_f` function as a morphism. -/
def rotl13 := ↾ rotl13_f

/-- The rotate operation in a bitvec with a shift of 18. -/
def rotl18_f : wordType → wordType
| a := (a.shl 18).or (a.ushr (word_len - 18))

/-- The `rotl18_f` function as a morphism. -/
def rotl18 := ↾ rotl18_f

/- `rotl7⁻¹` is just the inverse given `rotl7` is isomorphic. -/
noncomputable def rotl7_inv [is_iso (rotl7)] := inv rotl7

/- `rotl9⁻¹` is just the inverse given `rotl9` is isomorphic. -/
noncomputable def rotl9_inv [is_iso (rotl9)] := inv rotl9

/- `rotl13⁻¹` is just the inverse given `rotl13` is isomorphic. -/
noncomputable def rotl13_inv [is_iso (rotl13)] := inv rotl13

/- `rotl18⁻¹` is just the inverse given `rotl18` is isomorphic. -/
noncomputable def rotl18_inv [is_iso (rotl18)] := inv rotl18

-- Notation for the inverses.
local notation `rotl7⁻¹` := rotl7_inv
local notation `rotl9⁻¹` := rotl9_inv
local notation `rotl13⁻¹` := rotl13_inv
local notation `rotl18⁻¹` := rotl18_inv

/-- `rotl7⁻¹` is the inverse of `rotl7`.  -/
lemma rotl7_is_inverse [is_iso (rotl7)] (I : rotl7 ≅ rotl7⁻¹) : I.hom ≫ I.inv = 𝟙 rotl7 :=
  by exact I.hom_inv_id'

/-- `rotl9⁻¹` is the inverse of `rotl9`.  -/
lemma rotl9_is_inverse [is_iso (rotl9)] (I : rotl9 ≅ rotl9⁻¹) : I.hom ≫ I.inv = 𝟙 rotl9 :=
  by exact I.hom_inv_id'

/-- `rotl13⁻¹` is the inverse of `rotl13`.  -/
lemma rotl13_is_inverse [is_iso (rotl13)] (I : rotl13 ≅ rotl13⁻¹) : I.hom ≫ I.inv = 𝟙 rotl13 :=
  by exact I.hom_inv_id'

/-- `rotl18⁻¹` is the inverse of `rotl18`.  -/
lemma rot18_is_inverse [is_iso (rotl18)] (I : rotl18 ≅ rotl18⁻¹) : I.hom ≫ I.inv = 𝟙 rotl18 :=
  by exact I.hom_inv_id'


/-!
## Add

Converts a pair of bitvecs into a single bitvec of the same length by appling bitwise modulo addition. 

- [Example implementation](https://stackoverflow.com/a/19760152)
- [Modulo addition diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/mod.html)
- No inverse exist.
-/

/-- Modulo addition operation. -/
def mod_f : (wordType × wordType) → wordType
| (a, b) := (bitvec.and (a + b) (max_bitvec))

/-- The `mod_f` function as a morphism. -/
def mod := ↾ mod_f

/-!
## XOR

Converts a pair of bitvecs into a single bitvec of the same length by appling bitwise XOR. 

- [XOR diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/xor.html)
- XOR is its own inverse.
-/

/-- The salsa20 xor operation is just bitwise xor. -/
def xor_f : (wordType × wordType) → wordType
| (a, b) := a.xor b

/-- The `xor_f` function as a morphism. -/
def xor := ↾ xor_f

/-- `xor` after `xor` produces the identity.  -/
lemma xor_is_inverse (I : xor ≅ xor): I.hom ≫ I.inv = 𝟙 xor := by exact I.hom_inv_id'


end operations
