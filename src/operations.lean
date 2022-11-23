/-
  Building blocks operations and axioms.
-/

import data.bitvec.basic
import data.zmod.basic

import params

open params

namespace operations

-- Implements DJB's definition of '<<<' : https://github.com/alexwebr/salsa20/blob/master/salsa20.c#L6
def rotl : bitvec word_len → ℕ → bitvec word_len
| a shift := (a.shl shift).or (a.ushr (word_len - shift))

-- Inverse of rotl
def rotl_inv : bitvec word_len → ℕ → bitvec word_len
| a shift := (a.ushr shift).or (a.shl (32 - shift))

-- Bitwise modulo : https://stackoverflow.com/a/19760152
def mod : bitvec word_len → bitvec word_len → bitvec word_len
| a b := (bitvec.and (a + b) (max_bitvec))

-- The inverse of mod operation.
def mod_inv : bitvec word_len → bitvec word_len → bitvec word_len
| a b := (bitvec.and (a - b) (max_bitvec))

-- Just bitwise xor.
def xor : bitvec word_len → bitvec word_len → bitvec word_len
| a b := a.xor b

-- Some notation:

notation  ` ZERO `        := bitvec.zero word_len
infix     ` ROTL `  : 90  := rotl
infix     ` ROTL⁻¹ `: 90  := rotl_inv

infix     ` MOD `   : 90  := mod
infix     ` MOD⁻¹ ` : 90  := mod_inv

infix     ` XOR `   : 90  := xor

-- Have a few random bitvectors and a shift.
variables a b c : bitvec word_len
variable shift : ℕ

-- ROTL axioms

axiom zero_rotl : ZERO ROTL shift = ZERO
axiom inv_rotl_self : a ROTL⁻¹ shift = a

-- MOD axioms

axiom zero_mod : ZERO MOD a = a
axiom inv_mod_self : a MOD⁻¹ (a MOD b) = a

-- XOR axioms

axiom zero_xor : ZERO XOR a = a
axiom xor_zero : a XOR ZERO = a
axiom xor_inv : a XOR a  = ZERO
axiom xor_assoc : (a XOR b) XOR c = a XOR (b XOR c)

-- We split the operation in 2 terms, one at each side of the XOR. This is the left hand side.
def operation_rhs : bitvec word_len := (b MOD c) ROTL shift

-- Then an operation is just a XOR of 2 bitvectors.
def operation : bitvec word_len → bitvec word_len → bitvec word_len
| a b := a XOR b

-- Notation for operations:

infix   ` OP `   : 90   := operation
notation `OP_RHS`       := operation_rhs

-- The finite set of all the possible values a bitvector can be.
def S : set (bitvec word_len) := {n : (bitvec word_len) | n ≤ max_bitvec}

-- All bitvectors are in the set.
axiom bitvector_in_set : ∀ a, a ∈ S

-- The right hand side of the operation is in the set.
lemma rhs_is_in_set : OP_RHS b c shift ∈ S :=
begin
  apply bitvector_in_set,
end

-- More random bitvectors and another random shift value for equality proofs.
variables a' b' c' : bitvec word_len
variable shift' : ℕ

-- Two operations are equal if both sides of the XOR are equal.
lemma op_eq (h : a = a' ∧ b = b') : 
  a OP b = a' OP b' :=
begin
  finish,
end

-- Two operations are different if any side of the XOR is different.
lemma op_neq 
  (h : a OP b ≠ a' OP b') : a ≠ a' ∨ b ≠ b' :=
begin
  finish,
end

-- OP is just XOR, so each operation is its own inverse.
lemma operation_inverse (d : bitvec word_len) : 
  (a OP b) OP b = a :=
begin
  unfold operation,
  rw xor_assoc,
  rw xor_inv,
  rw xor_zero,
end

end operations
