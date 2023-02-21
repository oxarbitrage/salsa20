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
  ## Known variance

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

  Differences are carried iff the `msb` of each input is flipped when `rowround`
  inputs are random and crafted. Also, the `rest` of the input must be equal for random and crafted inputs.

  We prove that given a random and a crafted matrix for `rowround` as input, the output of each element has
  the property defined bewlow.
-/

/- General form of the carry property. -/
def diff_carried_prop_n (a b : list (bitvec word_len)) (n : ℕ) : Prop :=
  msb (a.nth n).iget ≠ msb (b.nth n).iget ∧ rest (a.nth n).iget = rest (b.nth n).iget

/-- A helper proposition that should be "easy" to prove but i don't know how yet. -/
constant n_succ_16 (n : ℕ) :
  n.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ < 16 = false

/-- Proof that the difference is carried for any row and any value of the input matrices. -/
lemma carry_diff_for_any_row_and_value (n : fin 16) :
  diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) n :=
begin
  unfold diff_carried_prop_n,
  unfold matrix_to_list,
  unfold input_random,
  unfold input_crafted,
  unfold rowround,
  unfold rowround_single,
  simp only [list.nth, quarterround, option.iget_some, ne.def],

  cases n,
  repeat {
    cases n_val,
    apply qr0_difference_is_carried,
    cases n_val,
    apply qr1_difference_is_carried,
    cases n_val,
    apply qr2_difference_is_carried,
    cases n_val,
    apply qr3_difference_is_carried,
  },
  norm_num at *,
  rw n_succ_16 at n_property,
  exact n_property,
end

/-- Put together all the properties needed to prove that `rowround` carries the differfence for random and
crafted inputs. -/
lemma rowround_difference_is_carried :
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 0) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 1) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 2) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 3) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 4) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 5) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 6) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 7) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 8) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 9) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 10) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 11) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 12) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 13) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 14) ∧
  (diff_carried_prop_n (matrix_to_list (rowround RANDOM_INPUT)) (matrix_to_list (rowround CRAFTED_INPUT)) 15) :=
begin

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 0,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 1,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 2,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 3,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 4,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 5,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 6,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 7,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 8,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 9,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 10,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 11,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 12,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 13,

  apply and.intro,
  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 14,

  apply carry_diff_for_any_row_and_value m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ m₁₅ 15,
end


end rowround
