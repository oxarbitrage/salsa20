import rowround
import columnround

open params
open operations
open quarterround
open rowround
open columnround
open utils

namespace doubleround

/-!
  # DoubleRound

  The `doubleround` function, its inverse and the invariance theorem.
-/

-- An random input matrix to be used as inputs and outputs of `doubleround` and `doubleround_inv`.
variable M : matrixType

/-- doubleround(x) = rowround(columnround(x)) -/
@[simp] def doubleround : matrixType :=
  rowround $ columnround M

/--
A special case of `doubleround` where inputs and outputs are sorted according to the salsa20 spec:
doubleround'(x) = rowround'(columnround'(x)) -/
@[simp] def doubleround' : matrixType :=
  rowround' $ columnround' M

/--  doubleround_inv(x) = columnround_inv(rowround_inv(x)) -/
@[simp] def doubleround_inv : matrixType :=
  columnround_inv $ rowround_inv M

/--
A special case of `doubleround_inv` where inputs and outputs are sorted according to the salsa20 spec:
doubleround_inv'(x) = columnround_inv'(rowround_inv'(x)) -/
@[simp] def doubleround_inv' : matrixType :=
  columnround_inv' $ rowround_inv' M

/-- For any `doubleround` output, we can get back to original values using the defined inverse. -/
@[simp] lemma doubleround_is_inv : doubleround_inv (doubleround M) = M :=
begin
  simp only [doubleround_inv, doubleround, rowround_single_inv, rowround_inv, columnround_inv, rowround_single, rowround,
  columnround, quarterround, quarterround_inv, qr0_is_inv, qr1_is_inv, qr2_is_inv, qr3_is_inv, prod.mk.eta],
end

/-- For any `doubleround'` output, we can get back to original values using the defined inverse. -/
@[simp] lemma doubleround_is_inv' : doubleround_inv' (doubleround' M) = M :=
begin
  simp only [doubleround_inv', doubleround', columnround_output, columnround_inv, columnround_input, columnround_inv', rowround_inv',
  rowround_output, rowround, rowround_input, rowround', columnround', columnround, rowround_single, quarterround,
  rowround_inv, rowround_single_inv, quarterround_inv, qr0_is_inv, qr1_is_inv, qr2_is_inv, qr3_is_inv, prod.mk.eta],
end

/-!
  ## Invariance

  Left invariance of the doubleround function: https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

  Theorem 4 of the paper.
-/

-- Have a number to form the invariant input.
variable a : bitvec word_len

/-- An input of this form should be invariant. -/
def input : matrixType := (
  (a, -a, a, -a),
  (-a, a, -a, a),
  (a, -a, a, -a),
  (-a, a, -a, a)
)

/-- `doubleround` is left invariant. -/
@[simp] theorem doubleround_is_left_invariant : doubleround' (input a) = input a :=
begin
  simp only [doubleround', rowround_output, rowround', rowround, rowround_input, columnround_output, 
    columnround', columnround, columnround_input, rowround_single, prod.mk.eta],
  
  unfold input,
  simp only [quarterround_is_left_invariant],
end

/-!
  ## Known variance

  In this section we want to prove that a crafted input difference is carried when `doubleround`
  function is applied.
-/

-- Have 16 random vectors to be used as `doubleround` inputs.
variables m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅: bitvec word_len

-- Alias for a random input with 16 random arguments.
local notation `RANDOM_INPUT` := input_random m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅

-- Alias for crafted input with 16 random arguments.
local notation `CRAFTED_INPUT` := input_crafted m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅

/-!
  ### Property

  Differences are carried iff the `msb` of each input is flipped when `doubleround`
  inputs are random and crafted. Also, the `rest` of the input must be equal for random and crafted inputs.

  We prove that given a random and a crafted matrix for `doubleround` as input, the output of each element has
  the property defined above.
-/
/-
Prove that the difference is carried for the first output from the first row of the matrix for random and
crafted inputs when `rowround` is applied after `columnround`.

Note:

- It can be repeated or generalized for all matrix positions.
-/
lemma rowround_after_columnround_difference_is_carried :
  (msb (rowround (columnround RANDOM_INPUT)).fst.fst ≠ msb (rowround (columnround CRAFTED_INPUT)).fst.fst) ∧
  (rest (rowround (columnround RANDOM_INPUT)).fst.fst = rest (rowround (columnround CRAFTED_INPUT)).fst.fst) :=
begin
  unfold input_random,
  unfold input_crafted,
  unfold columnround,
  unfold rowround,
  unfold rowround_single,
  unfold quarterround,

  simp only [ne.def],
  apply qrX_after_quarterround_difference_is_carried,
  repeat { tauto },

  rw ← craft_distrib m₀ m₁ m₂ m₃ qr0,
  rw ← craft_distrib m₀ m₁ m₂ m₃ qr1,
  rw ← craft_distrib m₀ m₁ m₂ m₃ qr2,
  rw ← craft_distrib m₀ m₁ m₂ m₃ qr3,
end

/-- Proof that the difference is carried after `doubleround` for any row and any value of the input matrices.

Note:

- This lemma just prove this for the first row and the first value but it can be generalized after `rowround_after_columnround_difference_is_carried`.
-/
lemma carry_diff_doubleround_for_any_row_and_value (n : fin 16) (h : n = 0) :
  diff_carried_prop_n (matrix_to_list (doubleround RANDOM_INPUT)) (matrix_to_list (doubleround CRAFTED_INPUT)) n :=
begin
  unfold diff_carried_prop_n,
  unfold matrix_to_list,
  unfold doubleround,
  rw h,
  simp only [list.nth, fin.coe_zero, option.iget_some, ne.def],
  apply rowround_after_columnround_difference_is_carried,
end

end doubleround
