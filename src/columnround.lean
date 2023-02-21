import rowround

open params
open operations
open quarterround
open rowround
open utils

namespace columnround

/-!
  # ColumnRound

  The `columnround` function, its inverse and the invariance theorem.
-/

-- A random input matrix to be used as inputs and outputs of `columnround` and `columnround_inv`.
variable M : matrixType

/-!
  ## Definitions and lemmas
-/

/--  Without ordering for inputs, a `columnround` is exactly the same as a `rowround`. -/
@[simp] def columnround : matrixType := rowround M

/-- This columnround call will sort all the elements of the input and the output to match salsa20.
-- It should be used in `doubleround`.-/
@[simp] def columnround' := 
  columnround_output (columnround (columnround_input M))

/--  Without ordering for inputs, a `columnround_inv` is exactly the same as a `rowround_inv`. -/
@[simp] def columnround_inv : matrixType := rowround_inv M

/-- For any `columnround` output, we can get back to original values using the defined inverse. -/
@[simp] lemma columnround_is_inv : columnround_inv (columnround M) = M :=
begin
  simp only [columnround_inv, columnround, rowround_inv, rowround_single, rowround, prod.mk.eta],
  apply rowround_is_inv,
end

/-- This columnround inverse call will sort all the elements of the input and the output to match salsa20.
It should be used in `doubleround`. -/
@[simp] def columnround_inv' := 
  columnround_output (columnround_inv (columnround_input M))


/-!
  ## Invariance

  Left invariance of the columnround function: https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

  Theorem 3 of the paper.
-/

-- Have a few numbers to form the invariant input.
variables a b c d : bitvec word_len

/-- An input of this form should be invariant. -/
def input : matrixType := (
  (a, -b, c, -d),
  (-a, b, -c, d),
  (a, -b, c, -d),
  (-a, b, -c, d)
)

/-- `columnround` is left invariant. -/
@[simp] theorem columnround_is_left_invariant : 
  utils.columnround_output (columnround (utils.columnround_input (input a b c d))) = input a b c d :=
begin
  simp only [utils.columnround_output, columnround, utils.columnround_input, rowround_single, rowround],
  unfold input,
  simp only [quarterround_is_left_invariant],
end


/-!
  ## Known variance

  In this section we want to prove that a crafted input difference is carried when `columnround`
  function is applied.
-/

-- Have 16 random vectors to be used as `columnround` inputs.
variables m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅: bitvec word_len

-- Alias for a random input with 16 random arguments.
local notation `RANDOM_INPUT` := input_random m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅

-- Alias for crafted input with 16 random arguments.
local notation `CRAFTED_INPUT` := input_crafted m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅

/-!
  ## Property

  Differences are carried iff the `msb` of each input is flipped when `columnround`
  inputs are random and crafted. Also, the `rest` of the input must be equal for random and crafted inputs.

  We prove that given a random and a crafted matrix for `columnround` as input, the output of each element has
  the property defined above.

  Given that `rowround` = `columnround` by definition proofs are trivial using `rowround` lemmas.
-/

/-- Proof that the difference is carried for any row and any value of the input matrices. -/
lemma carry_diff_columnround_for_any_row_and_value (n : fin 16) :
  diff_carried_prop_n (matrix_to_list (columnround RANDOM_INPUT)) (matrix_to_list (columnround CRAFTED_INPUT)) n :=
begin
  unfold columnround,
  apply carry_diff_rowround_for_any_row_and_value,
end

/-- Get the difference property of `columnround` given a position `n` for a random and crafted inputs. -/
def diff_carried_columnround : matrixType → matrixType → fin 16 → Prop
| r c n := diff_carried_prop_n (matrix_to_list (columnround r)) (matrix_to_list (columnround c)) n

/-- Put together all the properties needed to prove that `columnround` carries the differfence for random and
crafted inputs. -/
lemma columnround_difference_is_carried :
  diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 0 ∧ diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 1 ∧
  diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 2 ∧ diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 3 ∧
  diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 4 ∧ diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 5 ∧
  diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 6 ∧ diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 7 ∧
  diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 8 ∧ diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 9 ∧
  diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 10 ∧ diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 11 ∧
  diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 12 ∧ diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 13 ∧
  diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 14 ∧ diff_carried_columnround RANDOM_INPUT CRAFTED_INPUT 15 :=
begin
  unfold diff_carried_columnround,
  unfold columnround,
  apply rowround_difference_is_carried,
end

/-!
### Note

- We don't need to prove that the difference is carried theorems hold using `columnround'` because the
difference properties are on each element, independent of the order they have in the output matrix.
-/

end columnround
