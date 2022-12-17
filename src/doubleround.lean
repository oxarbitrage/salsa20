/-
  The `doubleround` function, its inverse and the invariance theorem.
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
@[simp] def doubleround : matrixType := 
  rowround_output $ rowround $ rowround_input $ columnround_output $ columnround $ columnround_input M

--  doubleround_inv(x) = columnround_inv(rowround_inv(x))
@[simp] def doubleround_inv : matrixType := 
  columnround_output $ columnround_inv $ columnround_input $ rowround_output $ rowround_inv $ rowround_input M

-- For any `doubleround` output, we can get back to original values using the defined inverse.
@[simp] lemma doubleround_is_inv : doubleround_inv (doubleround M) = M :=
begin
  simp only [doubleround_inv, doubleround, columnround_output, columnround_inv, columnround_input, rowround_output, rowround_inv,
    rowround_input, rowround, columnround, prod.mk.eta, rowround_single_is_inv],
end

/-
  Left invariance of the doubleround function: https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

  Theorem 4 of the paper.
-/

-- Have a number to form the invariant input.
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
  simp only [doubleround, rowround_output, rowround, rowround_input, columnround_output, columnround, columnround_input,
    rowround_single, prod.mk.eta],
  
  unfold input,
  simp only [quarterround_is_left_invariant],
end


end doubleround
