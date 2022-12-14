/-
  The `columnround` function and its inverse
-/

import rowround

open params
open operations
open quarterround
open rowround

namespace columnround

-- A random input matrix to be used as inputs and outputs of `columnround` and `columnround_inv`.
variable M : matrixType

--  Without ordering for inputs, a `columnround` is exactly the same as a `rowround`.
def columnround : matrixType := rowround M

--  Without ordering for inputs, a `columnround_inv` is exactly the same as a `rowround_inv`.
def columnround_inv : matrixType := rowround_inv M

-- For any `columnround` output, we can get back to original values using the defined inverse.
@[simp] lemma columnround_is_inv : columnround_inv (columnround M) = M :=
begin
  unfold columnround_inv,
  unfold columnround,

  apply rowround_is_inv,
end

/-
  Left invariance of the columnround function: https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

  Theorem 3 of the paper.
-/

-- Have a few numbers to form the invariant input.
variables A B C D : bitvec word_len

-- An input of this form should be invariant.
def input : matrixType := (
  (A, -B, C, -D),
  (-A, B, -C, D),
  (A, -B, C, -D),
  (-A, B, -C, D)
)

-- `columnround` is left invariant. 
@[simp] theorem columnround_is_left_invariant : 
  utils.columnround_output (columnround (utils.columnround_input (input A B C D))) = input A B C D :=
begin
  unfold columnround,
  unfold input,
  unfold utils.columnround_input,
  unfold utils.columnround_output,
  unfold rowround,
  unfold rowround_single,

  simp only [prod.mk.inj_iff],

  repeat { rw quarterround_is_left_invariant },

  simp only [eq_self_iff_true, and_self],
end


end columnround
