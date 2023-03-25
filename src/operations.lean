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

  ## Building blocks operations and the relation with their inverses
-/

/-- Rotate operation implemented as https://github.com/alexwebr/salsa20/blob/master/salsa20.c#L6 -/
def rotl : bitvec word_len → ℕ → bitvec word_len
| a shift := (a.shl shift).or (a.ushr (word_len - shift))

/-- Inverse of the rotate operation (`rotl`). -/
def rotl_inv : bitvec word_len → ℕ → bitvec word_len
| a shift := (a.ushr shift).or (a.shl (word_len - shift))

local notation `rotl⁻¹` := rotl_inv

/-- `rotl⁻¹` after `rotl` produces the identity.  -/
lemma rotl_inv_is_inverse_of_rotl (I : rotl ≅ rotl⁻¹): I.hom ≫ I.inv = 𝟙 rotl :=
begin
  exact I.hom_inv_id',
end

/-- Bitwise modulo addition implemented as https://stackoverflow.com/a/19760152 -/
def mod : bitvec word_len → bitvec word_len → bitvec word_len
| a b := (bitvec.and (a + b) (max_bitvec))

/-- The salsa20 xor operation is just bitwise xor. -/
def xor : bitvec word_len → bitvec word_len → bitvec word_len
| a b := a.xor b

/-- `xor` after `xor` produces the identity.  -/
lemma xor_is_inverse_of_xor (I : xor ≅ xor): I.hom ≫ I.inv = 𝟙 xor :=
begin
  exact I.hom_inv_id',
end

-- Some notation:
notation  ` ZERO `        := bitvec.zero word_len
infix     ` ROTL `  : 90  := rotl
infix     ` ROTL⁻¹ `: 90  := rotl_inv

infix     ` MOD `   : 90  := mod

infix     ` XOR `   : 90  := xor

/-! ## Operation as a combination of building block operations -/

/-- We split the salsa20 operations in 2 terms, one at each side of the XOR. This is the right hand side. -/
def operation_rhs (b c : bitvec word_len) (shift : ℕ ): bitvec word_len := (b MOD c) ROTL shift

/-- With the split done in `operation_rhs`, an operation is just a XOR of 2 bitvectors. -/
def operation : bitvec word_len → bitvec word_len → bitvec word_len
| a b := a XOR b

/-! ## Operation lemmas -/

-- some notation for operations:
infix   ` OP `   : 90   := operation
notation `OP_RHS`       := operation_rhs

/-- OP is just XOR, so each operation is its own inverse. -/
lemma operation_inverse (I : operation ≅ operation) : I.hom ≫ I.inv = 𝟙 operation :=
  by rw [iso.hom_inv_id]

end operations
