/-
  The `doubleround` function and its inverse
-/

import rowround
import columnround

open params
open operations
open quarterround
open rowround
open columnround
open utils

namespace doubleround

-- An random input matrix to be used as inputs and outputs of `doubleround` and `doubleround_inv`.
variable M : matrixType

-- doubleround(x) = rowround(columnround(x))
def doubleround : matrixType := 
  rowround_output $ rowround $ rowround_input $ columnround_output $ columnround $ columnround_input M

--  doubleround_inv(x) = columnround_inv(rowround_inv(x))
def doubleround_inv : matrixType := 
  columnround_output $ columnround_inv $ columnround_input $ rowround_output $ rowround_inv $ rowround_input M

-- For any `doubleround` output, we can get back to original values using the defined inverse.
@[simp] lemma doubleround_is_inv : doubleround_inv (doubleround M) = M :=
begin
  unfold doubleround_inv,
  unfold doubleround,

  unfold columnround_inv,
  unfold columnround,
  unfold rowround,
  unfold rowround_inv,

  unfold columnround_input,
  unfold columnround_output,

  unfold rowround_input,
  unfold rowround_output,

  simp only [prod.mk.eta],

  repeat { rw columnround_single_is_inv },
  repeat { rw rowround_single_is_inv },

  simp only [prod.mk.eta],

  repeat { rw columnround_single_is_inv },
  repeat { rw rowround_single_is_inv },

  simp only [prod.mk.eta],
end

/-
  Left invariance of the doubleround function: https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

  Theorem 4 of the paper.
-/

-- Have a few numbers to form the invariant input.
variable A : bitvec word_len

-- An input of this form should be invariant.
def input : matrixType := (
  (A, -A, A, -A),
  (-A, A, -A, A),
  (A, -A, A, -A),
  (-A, A, -A, A)
)

-- `doubleround` is left invariant. 
@[simp] theorem doubleround_is_left_invariant : doubleround (input A) = input A :=
begin
  unfold doubleround,
  unfold columnround,
  unfold input,
  unfold utils.columnround_input,
  unfold utils.columnround_output,
  unfold utils.rowround_input,
  unfold utils.rowround_output,
  unfold rowround,
  unfold rowround_single,

  -- same proof as `columnround_is_left_invariant`
  simp only [prod.mk.inj_iff],

  repeat { rw quarterround_is_left_invariant },

  simp only [eq_self_iff_true, and_self],
end


end doubleround
