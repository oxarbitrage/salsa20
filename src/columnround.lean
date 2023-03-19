import rowround

import category_theory.category.basic
import category_theory.core

open params
open operations
open quarterround
open rowround
open utils

open category_theory

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


/-! ## Isomorphism -/

/-- The identity of a `columnround` function given a sequence is the sequence. -/
@[simp] def id_columnround (seq : matrixType) := seq

/-- The identity of a `columnround_inv` function given a sequence is the sequence. -/
@[simp] def id_columnround_inv (seq : matrixType) := seq

/-- Isomorphism condition 1 : `f ∘ g = id_f` -/
@[simp] lemma isomorphism_left (seq : matrixType) : (columnround_inv ∘ columnround) seq = id_columnround seq :=
begin
  simp only [columnround_inv, columnround, id_columnround, rowround_single_inv, rowround_inv, function.comp_app, rowround_single,
  rowround, quarterround, quarterround_inv, qr0_is_inv, qr1_is_inv, qr2_is_inv, qr3_is_inv, prod.mk.eta],
end

/-- Isomorphism condition 2 : `g ∘ f = id_g` -/
@[simp] lemma isomorphism_right (seq : matrixType) : (columnround ∘ columnround_inv) seq = id_columnround_inv seq :=
begin
  simp only [columnround, columnround_inv, id_columnround_inv, rowround_single, rowround, function.comp_app, rowround_single_inv,
  rowround_inv, quarterround_inv, quarterround, qr0_inv_is_inv, qr1_inv_is_inv, qr2_inv_is_inv, qr3_inv_is_inv,
  prod.mk.eta],
end

/-- Two categories are isomrphic if `f ∘ g = id_f` and `g ∘ f = id_g`. -/
@[simp] theorem columnround_is_isomorphic (seq : matrixType) :
  (columnround_inv ∘ columnround) seq = id_columnround seq ∧
  (columnround ∘ columnround_inv) seq = id_columnround_inv seq :=
begin
  simp only [isomorphism_left, eq_self_iff_true, isomorphism_right, and_self],
end


/-! ## Category theory

-/

namespace category

universes u

/- A `MAT` is 16 numbers. -/
variables {MAT : Type u} [category (MAT)]

/-- `columnround` is a morphism, takes 16 numbers and output 16. -/
variable columnround : MAT → MAT

/-- `columnround` is a morphism, takes 16 numbers and output 16. -/
variable columnround_inv : MAT → MAT

/- Notation for inverse. -/
local notation `columnround⁻¹` := columnround_inv

/-- There is an isomoprhism between `columnround` and `columnround⁻¹`. -/
variable I : columnround ≅ columnround⁻¹

/-- It is easy to see that `columnround⁻¹` after `columnround` produces the original object. -/
lemma columnround_inv_is_inverse_of_columnround : I.hom ≫ I.inv = 𝟙 (columnround) :=
begin
  exact I.hom_inv_id',
end

end category

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
  ### Property

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

/--
This is the same lemma as `carry_diff_columnround_for_any_row_and_value` but using the sorted salsa20 matrix
from the `columnround'` function.
-/
lemma carry_diff_columnround_for_any_row_and_value' (n : fin 16) :
  diff_carried_prop_n (matrix_to_list (columnround' RANDOM_INPUT)) (matrix_to_list (columnround' CRAFTED_INPUT)) n :=
begin
  unfold diff_carried_prop_n,
  unfold matrix_to_list,
  unfold input_random,
  unfold input_crafted,
  unfold columnround',
  unfold columnround_input,
  unfold columnround_output,
  unfold columnround,
  unfold rowround,
  unfold rowround_single,

  cases n,

  cases n_val,
  apply qr0_difference_is_carried,
  cases n_val,
  apply qr3_difference_is_carried,
  cases n_val,
  apply qr2_difference_is_carried,
  cases n_val,
  apply qr1_difference_is_carried,
  tauto,
  cases n_val,
  apply qr1_difference_is_carried,
  tauto,
  cases n_val,
  apply qr0_difference_is_carried,
  cases n_val,
  apply qr3_difference_is_carried,
  cases n_val,
  apply qr2_difference_is_carried,
  cases n_val,
  apply qr2_difference_is_carried,
  cases n_val,
  apply qr1_difference_is_carried,
  tauto,
  cases n_val,
  apply qr0_difference_is_carried,
  cases n_val,
  apply qr3_difference_is_carried,
  cases n_val,
  apply qr3_difference_is_carried,
  cases n_val,
  apply qr2_difference_is_carried,
  cases n_val,
  apply qr1_difference_is_carried,
  tauto,
  cases n_val,
  apply qr0_difference_is_carried,

  norm_num at *,
  rw n_succ_16 at n_property,
  exact n_property,
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


end columnround
