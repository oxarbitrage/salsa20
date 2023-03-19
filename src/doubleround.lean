import rowround
import columnround

import category_theory.category.basic
import category_theory.core

open params
open operations
open quarterround
open rowround
open columnround
open utils

open category_theory

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
## Isomorphism

https://en.wikipedia.org/wiki/Isomorphism#Category_theoretic_view

> In category theory, given a category C, an isomorphism is a morphism `f : a ⟶ b` that has an inverse
> morphism `g : b ⟶  a` , that is, `f ∘ g = 𝟙 b` and `g ∘ f = 𝟙 a`.

-/

/-- The identity of a `doubleround` morphism given a sequence is the sequence. -/
@[simp] def id_doubleround (seq : matrixType) := seq

/-- The identity of a `doubleround⁻¹` morphism given a sequence is the sequence. -/
@[simp] def id_doubleround_inv (seq : matrixType) := seq

/-- Isomorphism condition 1 : `doubleround ∘ doubleround⁻¹ = 𝟙 doubleround` -/
@[simp] lemma isomorphism_left (seq : matrixType) : (doubleround_inv ∘ doubleround) seq = id_doubleround seq :=
begin
  simp only [doubleround_inv, doubleround, id_doubleround, rowround_single_inv, rowround_inv, columnround_inv, function.comp_app,
  rowround_single, rowround, columnround, quarterround, quarterround_inv, qr0_is_inv, qr1_is_inv, qr2_is_inv,
  qr3_is_inv, prod.mk.eta],
end

/-- Isomorphism condition 2 : `doubleround⁻¹ ∘ doubleround = 𝟙 doubleround⁻¹` -/
@[simp] lemma isomorphism_right (seq : matrixType) : (doubleround ∘ doubleround_inv) seq = id_doubleround_inv seq :=
begin
  simp only [doubleround, doubleround_inv, id_doubleround_inv, rowround_single, rowround, columnround, function.comp_app,
  rowround_single_inv, rowround_inv, columnround_inv, quarterround_inv, quarterround, qr0_inv_is_inv, qr1_inv_is_inv,
  qr2_inv_is_inv, qr3_inv_is_inv, prod.mk.eta],
end

/-- Two morphism `doubleround` and `doubleround⁻¹` are isomorphic if:
- `doubleround ∘ doubleround⁻¹ = 𝟙 doubleround`, and
- `doubleround⁻¹ ∘ doubleround = 𝟙 doubleround⁻¹`.
-/
@[simp] theorem doubleround_is_isomorphic (seq : matrixType) :
  (doubleround_inv ∘ doubleround) seq = id_doubleround seq ∧
  (doubleround ∘ doubleround_inv) seq = id_doubleround_inv seq :=
begin
  simp only [isomorphism_left, eq_self_iff_true, isomorphism_right, and_self],
end

/-! ## Category theory

-/

namespace category

universes u

/- A `MAT` is 16 numbers. -/
variables {MAT : Type u} [category (MAT)]

/-- These are all morphisms from `X` to `X`. -/
variables rowround columnround rowround_inv columnround_inv : MAT → MAT

/- Notation for inverse. -/
local notation `rowround⁻¹` := rowround_inv

/- Notation for inverse. -/
local notation `columnround⁻¹` := columnround_inv

/-- `doubleround` is `rowround` followed by `columnround`. -/
def doubleround := rowround ∘ columnround

/-- `doubleround_inv` is `columnround⁻¹` followed by `rowround⁻¹`. -/
def doubleround_inv := columnround⁻¹ ∘ rowround⁻¹

/- Notation for inverse. -/
local notation `doubleround⁻¹` := doubleround_inv

/-- There is an isomoprhism between `doubleround` and `doubleround⁻¹`. -/
variable I : doubleround rowround columnround ≅ doubleround⁻¹ columnround rowround

/-- It is easy to see that `dubleround⁻¹` after `doubleround` produces the original object. -/
lemma doubleround_inv_is_inverse_of_doubleround : I.hom ≫ I.inv = 𝟙 (doubleround rowround columnround) :=
begin
  exact I.hom_inv_id',
end

end category

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

/--
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

/--
Proof that the difference is carried after `doubleround` for any row and any value of the input matrices.
Note:
- This lemma just prove this for the first row and the first value but it can be generalized after
`rowround_after_columnround_difference_is_carried`.
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
