import params

open params

namespace operations

/-!
  # Operations

  Building blocks operations and axioms.

  The salsa20 cipher is built with add-rotate-XOR operations.
-/


/-- Rotate operation.
Implements DJB's definition of '<<<' : https://github.com/alexwebr/salsa20/blob/master/salsa20.c#L6
-/
def rotl : bitvec word_len → ℕ → bitvec word_len
| a shift := (a.shl shift).or (a.ushr (word_len - shift))

/-- Inverse of the rotate operation (`rotl`). -/
def rotl_inv : bitvec word_len → ℕ → bitvec word_len
| a shift := (a.ushr shift).or (a.shl (word_len - shift))

/-- Bitwise modulo addition implemented as detailed in
https://stackoverflow.com/a/19760152 -/
def mod : bitvec word_len → bitvec word_len → bitvec word_len
| a b := (bitvec.and (a + b) (max_bitvec))

/-- The salsa20 xor operation is just bitwise xor. -/
def xor : bitvec word_len → bitvec word_len → bitvec word_len
| a b := a.xor b

-- Some notation:

notation  ` ZERO `        := bitvec.zero word_len
infix     ` ROTL `  : 90  := rotl
infix     ` ROTL⁻¹ `: 90  := rotl_inv

infix     ` MOD `   : 90  := mod

infix     ` XOR `   : 90  := xor

-- Have a few random bitvectors and a shift.
variables a b c : bitvec word_len
variable shift : ℕ

/-! ## ROTL axioms -/

axiom zero_rotl : ZERO ROTL shift = ZERO

/-! ## MOD axioms -/

axiom mod_neg : a MOD -a = bitvec.zero word_len
axiom neg_mod : (-a) MOD a = bitvec.zero word_len
axiom double_mod : ∀ a, a MOD a = 2 * a

axiom modular_magic (h1 : a < two_31) (h2 : b = a MOD two_31) : 2 * a = 2 * b
axiom mod_self : a MOD a = 2 * a

lemma inv_of_mod_is_not_a_function : ∃ (a b c d : bitvec word_len), a MOD b = c MOD d :=
begin
  use (bitvec.of_nat word_len 1),
  use (bitvec.of_nat word_len 5),
  use (bitvec.of_nat word_len 3),
  use (bitvec.of_nat word_len 3),

  unfold mod,
  unfold max_bitvec,
  unfold params.mod,
  rw word_len,
  unfold bitvec.of_nat,
  norm_num,
  refl,
end

/-! ## XOR axioms -/

axiom xor_zero : a XOR ZERO = a
axiom xor_inv : a XOR a  = ZERO
axiom xor_assoc : (a XOR b) XOR c = a XOR (b XOR c)

-- Tag all axioms with simp
attribute [simp] zero_rotl mod_neg neg_mod double_mod modular_magic mod_self xor_zero xor_inv xor_assoc inv_of_mod_is_not_a_function

/-! ## Operation definitions -/

/-- We split the salsa20 operations in 2 terms, one
at each side of the XOR. This is the right hand side. -/
def operation_rhs : bitvec word_len := (b MOD c) ROTL shift

/-- With the split done in `operation_rhs`, an operation is just
a XOR of 2 bitvectors. -/
def operation : bitvec word_len → bitvec word_len → bitvec word_len
| a b := a XOR b

/-! ## Operation lemmas -/

-- some notation for operations:

infix   ` OP `   : 90   := operation
notation `OP_RHS`       := operation_rhs

-- More random bitvectors and another random shift value for equality proofs.
variables a' b' c' : bitvec word_len
variable shift' : ℕ


/-- Two operations are equal if both sides of the XOR are equal. -/
@[simp] lemma op_eq (h : a = a' ∧ b = b') :  a OP b = a' OP b' :=
begin
  finish,
end

/-- Two operations are different if any side of the XOR is different. -/
@[simp] lemma op_neq (h : a OP b ≠ a' OP b') : a ≠ a' ∨ b ≠ b' :=
begin
  finish,
end

/-- OP is just XOR, so each operation is its own inverse. -/
lemma operation_inverse (d : bitvec word_len) : (a OP b) OP b = a :=
begin
  unfold operation,
  simp only [xor_assoc, xor_inv, xor_zero],
end

end operations
