import params
import quarterround
import utils

open params
open operations
open quarterround
open utils

namespace rowround

/-!
  # Rowround

  The `rowround` function, its inverse and the invariance theorem.
-/

-- A random row or column of a matrix
variable R : vecType

-- A random input matrix
variable M : matrixType

/-!
  # Definitions and lemmas
-/

/-- The row round of a single row. Complete `rowround` function will use 4 of this. -/
@[simp] def rowround_single : vecType :=
  (
    (quarterround R).fst, (quarterround R).snd.fst, 
    (quarterround R).snd.snd.fst, (quarterround R).snd.snd.snd
  )

/-- The inverse of a single row round. -/
@[simp] def rowround_single_inv : vecType :=
  (
    (quarterround_inv R).fst, (quarterround_inv R).snd.fst, 
    (quarterround_inv R).snd.snd.fst, (quarterround_inv R).snd.snd.snd
  )

/-- Each row is invertible. -/
@[simp] lemma rowround_single_is_inv : rowround_single_inv (rowround_single R) = R :=
begin
  simp only [rowround_single_inv, rowround_single, quarterround_inv, quarterround, qr0_is_inv, qr1_is_inv, qr2_is_inv, qr3_is_inv,
    prod.mk.eta],
end

/-- Apply `rowround_single` to get a row round matrix output -/
@[simp] def rowround : matrixType :=
  (
    rowround_single M.fst,
    rowround_single M.snd.fst,
    rowround_single M.snd.snd.fst,
    rowround_single M.snd.snd.snd
  )

/-- This rowround call will sort all the elements of the input and the output to match salsa 20.
It should be used in `doubleround`. -/
@[simp] def rowround' := 
  rowround_output (rowround (rowround_input M))

/-- Reverses `rowround` by doing `rowround_single_inv` to get the original matrix output -/
@[simp] def rowround_inv : matrixType :=
  (
    rowround_single_inv M.fst,
    rowround_single_inv M.snd.fst,
    rowround_single_inv M.snd.snd.fst,
    rowround_single_inv M.snd.snd.snd
  )

/-- For any `rowround` output, we can get back to original values using the defined inverse. -/
@[simp] lemma rowround_is_inv : rowround_inv (rowround M) = M :=
begin
  simp only [rowround_inv, rowround, rowround_single_inv, rowround_single, quarterround, quarterround_inv, qr0_is_inv, qr1_is_inv,
    qr2_is_inv, qr3_is_inv, prod.mk.eta],
end

/-- This rowround inverse call will sort all the elements of the input and the output to match salsa 20.
It should be used in `doubleround`. -/
@[simp] def rowround_inv' := 
  rowround_output (rowround_inv (rowround_input M))

/-!
  ## Invariance

  Left invariance of the rowround function: https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

  Theorem 2 of the paper.
-/

-- Have a few numbers to form the invariant input.
variables a b c d : bitvec word_len

/-- An input of this form should be invariant. -/
def input : matrixType := (
  (a, -a, a, -a),
  (b, -b, b, -b),
  (c, -c, c, -c),
  (d, -d, d, -d)
)

/-- `rowround` is left invariant. -/
@[simp] theorem rowround_is_left_invariant : rowround (input a b c d) = input a b c d :=
begin
  simp only [rowround, rowround_single, quarterround],
  unfold input,
  simp only [qr0_is_left_invariant, qr1_is_left_invariant, qr2_is_left_invariant, qr3_is_left_invariant],
end

/-!
  # Known variance

  In this section we want to prove that a crafted input difference is carried when `rowround`
  function is applied.
-/

-- Have 16 random vectors to be used as rowround inputs.
variables m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅: bitvec word_len

/-- Define a random input as a 4x4 matrix. -/
def input_random : matrixType := (
  (m₀, m₁, m₂, m₃),
  (m₄, m₅, m₆, m₇),
  (m₈, m₉, m₁₀, m₁₁),
  (m₁₂, m₁₃, m₁₄, m₁₅)
)

/-- Define a crafted input based on the random input as a 4x4 matrix. -/
def input_crafted : matrixType := (
  (craft m₀, craft m₁, craft m₂, craft m₃),
  (craft m₄, craft m₅, craft m₆, craft m₇),
  (craft m₈, craft m₉, craft m₁₀, craft m₁₁),
  (craft m₁₂, craft m₁₃, craft m₁₄, craft m₁₅)
)

-- Alias for a random input with 16 random arguments.
local notation `RANDOM_INPUT` := input_random m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅

-- Alias for crafted input with 16 random arguments.
local notation `CRAFTED_INPUT` := input_crafted m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅

/-!

  ## Property

  Differences are carried iff the `msb` of each input is flipped when `rowround` is
  executed in a random input comprared with a crafted one. In addition, the `rest` of the input must be equal.

  We prove this in the following section that given a random and a crafted matrix for `rowround` as input, the output of each element has the property defined bewlow.
-/

-- Alias for a carry difference property, first row and first value.
local notation `CARRY_PROP_ROW1_VALUE1` :=
  msb (rowround RANDOM_INPUT).fst.fst ≠ msb (rowround CRAFTED_INPUT).fst.fst ∧
  rest (rowround RANDOM_INPUT).fst.fst = rest (rowround CRAFTED_INPUT).fst.fst

-- Alias for a carry difference property, first row and second value.
local notation `CARRY_PROP_ROW1_VALUE2` :=
  msb (rowround RANDOM_INPUT).fst.snd.fst ≠ msb (rowround CRAFTED_INPUT).fst.snd.fst ∧
  rest (rowround RANDOM_INPUT).fst.snd.fst = rest (rowround CRAFTED_INPUT).fst.snd.fst

-- Alias for a carry difference property, first row and third value.
local notation `CARRY_PROP_ROW1_VALUE3` :=
  msb (rowround RANDOM_INPUT).fst.snd.snd.fst ≠ msb (rowround CRAFTED_INPUT).fst.snd.snd.fst ∧
  rest (rowround RANDOM_INPUT).fst.snd.snd.fst = rest (rowround CRAFTED_INPUT).fst.snd.snd.fst

-- Alias for a carry difference property, first row and fourth value.
local notation `CARRY_PROP_ROW1_VALUE4` :=
  msb (rowround RANDOM_INPUT).fst.snd.snd.snd ≠ msb (rowround CRAFTED_INPUT).fst.snd.snd.snd ∧
  rest (rowround RANDOM_INPUT).fst.snd.snd.snd = rest (rowround CRAFTED_INPUT).fst.snd.snd.snd

-- Alias for a carry difference property, second row and first value.
local notation `CARRY_PROP_ROW2_VALUE1` :=
  msb (rowround RANDOM_INPUT).snd.fst.fst ≠ msb (rowround CRAFTED_INPUT).snd.fst.fst ∧
  rest (rowround RANDOM_INPUT).snd.fst.fst = rest (rowround CRAFTED_INPUT).snd.fst.fst

-- Alias for a carry difference property, second row and second value.
local notation `CARRY_PROP_ROW2_VALUE2` :=
  msb (rowround RANDOM_INPUT).snd.fst.snd.fst ≠ msb (rowround CRAFTED_INPUT).snd.fst.snd.fst ∧
  rest (rowround RANDOM_INPUT).snd.fst.snd.fst = rest (rowround CRAFTED_INPUT).snd.fst.snd.fst

-- Alias for a carry difference property, second row and third value.
local notation `CARRY_PROP_ROW2_VALUE3` :=
  msb (rowround RANDOM_INPUT).snd.fst.snd.snd.fst ≠ msb (rowround CRAFTED_INPUT).snd.fst.snd.snd.fst ∧
  rest (rowround RANDOM_INPUT).snd.fst.snd.snd.fst = rest (rowround CRAFTED_INPUT).snd.fst.snd.snd.fst

-- Alias for a carry difference property, second row and fourth value.
local notation `CARRY_PROP_ROW2_VALUE4` :=
  msb (rowround RANDOM_INPUT).snd.fst.snd.snd.snd ≠ msb (rowround CRAFTED_INPUT).snd.fst.snd.snd.snd ∧
  rest (rowround RANDOM_INPUT).snd.fst.snd.snd.snd = rest (rowround CRAFTED_INPUT).snd.fst.snd.snd.snd

-- Alias for a carry difference property, third row and first value.
local notation `CARRY_PROP_ROW3_VALUE1` :=
  msb (rowround RANDOM_INPUT).snd.snd.fst.fst ≠ msb (rowround CRAFTED_INPUT).snd.snd.fst.fst ∧
  rest (rowround RANDOM_INPUT).snd.snd.fst.fst = rest (rowround CRAFTED_INPUT).snd.snd.fst.fst

-- Alias for a carry difference property, third row and second value.
local notation `CARRY_PROP_ROW3_VALUE2` :=
  msb (rowround RANDOM_INPUT).snd.snd.fst.snd.fst ≠ msb (rowround CRAFTED_INPUT).snd.snd.fst.snd.fst ∧
  rest (rowround RANDOM_INPUT).snd.snd.fst.snd.fst = rest (rowround CRAFTED_INPUT).snd.snd.fst.snd.fst

-- Alias for a carry difference property, third row and third value.
local notation `CARRY_PROP_ROW3_VALUE3` :=
  msb (rowround RANDOM_INPUT).snd.snd.fst.snd.snd.fst ≠ msb (rowround CRAFTED_INPUT).snd.snd.fst.snd.snd.fst ∧
  rest (rowround RANDOM_INPUT).snd.snd.fst.snd.snd.fst = rest (rowround CRAFTED_INPUT).snd.snd.fst.snd.snd.fst

-- Alias for a carry difference property, third row and fourth value.
local notation `CARRY_PROP_ROW3_VALUE4` :=
  msb (rowround RANDOM_INPUT).snd.snd.fst.snd.snd.snd ≠ msb (rowround CRAFTED_INPUT).snd.snd.fst.snd.snd.snd ∧
  rest (rowround RANDOM_INPUT).snd.snd.fst.snd.snd.snd = rest (rowround CRAFTED_INPUT).snd.snd.fst.snd.snd.snd

-- Alias for a carry difference property, fourth row and first value.
local notation `CARRY_PROP_ROW4_VALUE1` :=
  msb (rowround RANDOM_INPUT).snd.snd.snd.fst ≠ msb (rowround CRAFTED_INPUT).snd.snd.snd.fst ∧
  rest (rowround RANDOM_INPUT).snd.snd.snd.fst = rest (rowround CRAFTED_INPUT).snd.snd.snd.fst

-- Alias for a carry difference property, fourth row and second value.
local notation `CARRY_PROP_ROW4_VALUE2` :=
  msb (rowround RANDOM_INPUT).snd.snd.snd.snd.fst ≠ msb (rowround CRAFTED_INPUT).snd.snd.snd.snd.fst ∧
  rest (rowround RANDOM_INPUT).snd.snd.snd.snd.fst = rest (rowround CRAFTED_INPUT).snd.snd.snd.snd.fst

-- Alias for a carry difference property, fourth row and third value.
local notation `CARRY_PROP_ROW4_VALUE3` :=
  msb (rowround RANDOM_INPUT).snd.snd.snd.snd.snd.fst ≠ msb (rowround CRAFTED_INPUT).snd.snd.snd.snd.snd.fst ∧
  rest (rowround RANDOM_INPUT).snd.snd.snd.snd.snd.fst = rest (rowround CRAFTED_INPUT).snd.snd.snd.snd.snd.fst

-- Alias for a carry difference property, fourth row and fourth value.
local notation `CARRY_PROP_ROW4_VALUE4` :=
  msb (rowround RANDOM_INPUT).snd.snd.snd.snd.snd.snd ≠ msb (rowround CRAFTED_INPUT).snd.snd.snd.snd.snd.snd ∧
  rest (rowround RANDOM_INPUT).snd.snd.snd.snd.snd.snd = rest (rowround CRAFTED_INPUT).snd.snd.snd.snd.snd.snd

/-- Proof that the difference is carried for the first row and the first value. -/
lemma carry_diff_row1_value1 : CARRY_PROP_ROW1_VALUE1 :=
begin
  unfold input_random,
  unfold input_crafted,
  unfold rowround,
  unfold rowround_single,
  simp only [quarterround, ne.def],

  apply qr0_difference_is_carried,
end

/-- Proof that the difference is carried for the first row and the second value. -/
lemma carry_diff_row1_value2 : CARRY_PROP_ROW1_VALUE2 :=
begin
  unfold input_random,
  unfold input_crafted,
  unfold rowround,
  unfold rowround_single,
  simp only [quarterround, ne.def],

  apply qr1_difference_is_carried,
end

/-- Proof that the difference is carried for the first row and the third value. -/
lemma carry_diff_row1_value3 : CARRY_PROP_ROW1_VALUE3 :=
begin
  unfold input_random,
  unfold input_crafted,
  unfold rowround,
  unfold rowround_single,
  simp only [quarterround, ne.def],

  apply qr2_difference_is_carried,
end

/-- Proof that the difference is carried for the first row and the third value. -/
lemma carry_diff_row1_value4 : CARRY_PROP_ROW1_VALUE4 :=
begin
  unfold input_random,
  unfold input_crafted,
  unfold rowround,
  unfold rowround_single,
  simp only [quarterround, ne.def],

  apply qr3_difference_is_carried,
end

/-- Proof that the difference is carried for the second row and the first value. -/
lemma carry_diff_row2_value1 : CARRY_PROP_ROW2_VALUE1 :=
begin
  apply carry_diff_row1_value1,
  repeat { tauto },
end

/-- Proof that the difference is carried for the second row and the second value. -/
lemma carry_diff_row2_value2 : CARRY_PROP_ROW2_VALUE2 :=
begin
  apply carry_diff_row1_value2,
  repeat { tauto },
end

/-- Proof that the difference is carried for the second row and the third value. -/
lemma carry_diff_row2_value3 : CARRY_PROP_ROW2_VALUE3 :=
begin
  apply carry_diff_row1_value3,
  repeat { tauto },
end

/-- Proof that the difference is carried for the second row and the fourth value. -/
lemma carry_diff_row2_value4 : CARRY_PROP_ROW2_VALUE4 :=
begin
  apply carry_diff_row1_value4,
  repeat { tauto },
end

/-- Proof that the difference is carried for the third row and the first value. -/
lemma carry_diff_row3_value1 : CARRY_PROP_ROW3_VALUE1 :=
begin
  apply carry_diff_row1_value1,
  repeat { tauto },
end

/-- Proof that the difference is carried for the third row and the second value. -/
lemma carry_diff_row3_value2 : CARRY_PROP_ROW3_VALUE2 :=
begin
  apply carry_diff_row1_value2,
  repeat { tauto },
end

/-- Proof that the difference is carried for the third row and the third value. -/
lemma carry_diff_row3_value3 : CARRY_PROP_ROW3_VALUE3 :=
begin
  apply carry_diff_row1_value3,
  repeat { tauto },
end

/-- Proof that the difference is carried for the third row and the fourth value. -/
lemma carry_diff_row3_value4 : CARRY_PROP_ROW3_VALUE4 :=
begin
  apply carry_diff_row1_value4,
  repeat { tauto },
end

/-- Proof that the difference is carried for the fourth row and the first value. -/
lemma carry_diff_row4_value1 : CARRY_PROP_ROW4_VALUE1 :=
begin
  apply carry_diff_row1_value1,
  repeat { tauto },
end

/-- Proof that the difference is carried for the fourth row and the second value. -/
lemma carry_diff_row4_value2 : CARRY_PROP_ROW4_VALUE2 :=
begin
  apply carry_diff_row1_value2,
  repeat { tauto },
end

/-- Proof that the difference is carried for the fourth row and the third value. -/
lemma carry_diff_row4_value3 : CARRY_PROP_ROW4_VALUE3 :=
begin
  apply carry_diff_row1_value3,
  repeat { tauto },
end

/-- Proof that the difference is carried for the fourth row and the fourth value. -/
lemma carry_diff_row4_value4 : CARRY_PROP_ROW4_VALUE4 :=
begin
  apply carry_diff_row1_value4,
  repeat { tauto },
end

/-- Each number produced by the `rowround` function when feeded with crafted and uncrafted inputs carries
the difference. We need to prove this is true for all the 16 output values of the rowround.
-/
lemma rowround_difference_is_carried :
  (CARRY_PROP_ROW1_VALUE1) ∧ (CARRY_PROP_ROW1_VALUE2) ∧ (CARRY_PROP_ROW1_VALUE3) ∧(CARRY_PROP_ROW1_VALUE4) ∧
  (CARRY_PROP_ROW2_VALUE1) ∧ (CARRY_PROP_ROW2_VALUE2) ∧ (CARRY_PROP_ROW2_VALUE3) ∧ (CARRY_PROP_ROW2_VALUE4) ∧
  (CARRY_PROP_ROW3_VALUE1) ∧ (CARRY_PROP_ROW3_VALUE2) ∧ (CARRY_PROP_ROW3_VALUE3) ∧ (CARRY_PROP_ROW3_VALUE4) ∧
  (CARRY_PROP_ROW4_VALUE1) ∧ (CARRY_PROP_ROW4_VALUE2) ∧ (CARRY_PROP_ROW4_VALUE3) ∧ (CARRY_PROP_ROW4_VALUE4)
:=
begin
  apply and.intro,
  apply carry_diff_row1_value1,
  apply and.intro,
  apply carry_diff_row1_value2,
  apply and.intro,
  apply carry_diff_row1_value3,
  apply and.intro,
  apply carry_diff_row1_value4,
  apply and.intro,
  apply carry_diff_row2_value1,
  apply and.intro,
  apply carry_diff_row2_value2,
  apply and.intro,
  apply carry_diff_row2_value3,
  apply and.intro,
  apply carry_diff_row2_value4,
  apply and.intro,
  apply carry_diff_row3_value1,
  apply and.intro,
  apply carry_diff_row3_value2,
  apply and.intro,
  apply carry_diff_row3_value3,
  apply and.intro,
  apply carry_diff_row3_value4,
  apply and.intro,
  apply carry_diff_row4_value1,
  apply and.intro,
  apply carry_diff_row4_value2,
  apply and.intro,
  apply carry_diff_row4_value3,
  apply carry_diff_row4_value4,
end

end rowround
