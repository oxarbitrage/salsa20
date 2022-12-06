/-
  Utility types and functions
-/

import params

open params

namespace utils

-- We define a row or a column to be a tuple of 4 bit vectors.
-- This is the input and output of the `quarterround` function. 
notation `vecType` := (bitvec word_len) × (bitvec word_len) × (bitvec word_len) × (bitvec word_len) 

-- A 16 elements matrix type used as `rowround` and `rowround_inv` input and output.
notation `matrixType` := vecType × vecType × vecType × vecType

-- 
notation `matrix64Type` := matrixType × matrixType × matrixType × matrixType

variable M : matrixType

/-
  Prepare the `rowround` matrix input

  Any `rowround` input matrix is in the form:

  (y₀, y₁, y₂, y₃)
  (y₄, y₅, y₆, y₇)
  (y₈, y₉, y₁₀, y₁₁)
  (y₁₂, y₁₃, y₁₄, y₁₅)

  But we need this to be converted to:

  (y₀, y₁, y₂, y₃)
  (y₅, y₆, y₇, y₄)
  (y₁₀, y₁₁, y₈, y₉)
  (y₁₅, y₁₂, y₁₃, y₁₄)  
-/
def rowround_input : matrixType :=
  (
    ((M.fst).fst,                 (M.fst).snd.fst,              (M.fst).snd.snd.fst,      (M.fst).snd.snd.snd),
    ((M.snd.fst).snd.fst,         (M.snd.fst).snd.snd.fst,      (M.snd.fst).snd.snd.snd,  (M.snd.fst).fst),
    ((M.snd.snd.fst).snd.snd.fst, (M.snd.snd.fst).snd.snd.snd,  (M.snd.snd.fst).fst,      (M.snd.snd.fst).snd.fst),
    ((M.snd.snd.snd).snd.snd.snd, (M.snd.snd.snd).fst,          (M.snd.snd.snd).snd.fst,  (M.snd.snd.snd).snd.snd.fst)
  )

/-
  Prepare the `rowround` matrix output

  Any `rowround` output matrix is of the form:

  (z₀, z₁, z₂, z₃)
  (z₅, z₆, z₇, z₄)
  (z₁₀, z₁₁, z₈, z₉)
  (z₁₅, z₁₂, z₁₃, z₁₄)  

  But we need this to be converted to:

  (z₀, z₁, z₂, z₃)
  (z₄, z₅, z₆, z₇)
  (z₈, z₉, z₁₀, z₁₁)
  (z₁₂, z₁₃, z₁₄, z₁₅)

-/
def rowround_output : matrixType :=
  (
    ((M.fst).fst,                 (M.fst).snd.fst,              (M.fst).snd.snd.fst,          (M.fst).snd.snd.snd),
    ((M.snd.fst).snd.snd.snd,     (M.snd.fst).fst,              (M.snd.fst).snd.fst,          (M.snd.fst).snd.snd.fst),
    ((M.snd.snd.fst).snd.snd.fst, (M.snd.snd.fst).snd.snd.snd,  (M.snd.snd.fst).fst,          (M.snd.snd.fst).snd.fst),
    ((M.snd.snd.snd).snd.fst,     (M.snd.snd.snd).snd.snd.fst,  (M.snd.snd.snd).snd.snd.snd,  (M.snd.snd.snd).fst)
  )

-- The `rowround_output` function is the inverse of the `rowround_input` function.
lemma rowround_output_is_inv_of_input : rowround_output (rowround_input M) = M :=
begin
  unfold rowround_input,
  unfold rowround_output,
  simp only [prod.mk.eta],
end

/-
  Prepare the `columnround` matrix input

  Any `columnround` input matrix is in the form:

  (x₀, x₁, x₂, x₃)
  (x₄, x₅, x₆, x₇)
  (x₈, x₉, x₁₀, x₁₁)
  (x₁₂, x₁₃, x₁₄, x₁₅)

  But we need this to be converted to:

  (x₀, x₄, x₈, x₁₂)
  (x₅, x₉, x₁₃, x₁)
  (x₁₀, x₁₄, x₂, x₆)
  (x₁₅, x₃, x₇, x₁₁)
-/
def columnround_input : matrixType :=
  (
    ((M.fst).fst,                 (M.snd.fst).fst,              (M.snd.snd.fst).fst,      (M.snd.snd.snd).fst),
    ((M.snd.fst).snd.fst,         (M.snd.snd.fst).snd.fst,      (M.snd.snd.snd).snd.fst,  (M.fst).snd.fst),
    ((M.snd.snd.fst).snd.snd.fst, (M.snd.snd.snd).snd.snd.fst,  (M.fst).snd.snd.fst,      (M.snd.fst).snd.snd.fst),
    ((M.snd.snd.snd).snd.snd.snd, (M.fst).snd.snd.snd,          (M.snd.fst).snd.snd.snd,  (M.snd.snd.fst).snd.snd.snd)
  )

/-
  Prepare the `columnround` matrix output

  Any `columnround` output matrix is in the form:

  (y₀, y₄, y₈, y₁₂)
  (y₅, y₉, y₁₃, y₁)
  (y₁₀, y₁₄, y₂, y₆)
  (y₁₅, y₃, y₇, y₁₁)

  But we need this to be converted to:

  (y₀, y₁, y₂, y₃)
  (y₄, y₅, y₆, y₇)
  (y₈, y₉, y₁₀, y₁₁)
  (y₁₂, y₁₃, y₁₄, y₁₅)  
-/
def columnround_output : matrixType :=
  (
    ((M.fst).fst,         (M.snd.fst).snd.snd.snd,  (M.snd.snd.fst).snd.snd.fst,  (M.snd.snd.snd).snd.fst),
    ((M.fst).snd.fst,     (M.snd.fst).fst,          (M.snd.snd.fst).snd.snd.snd,  (M.snd.snd.snd).snd.snd.fst),
    ((M.fst).snd.snd.fst, (M.snd.fst).snd.fst,      (M.snd.snd.fst).fst,          (M.snd.snd.snd).snd.snd.snd),
    ((M.fst).snd.snd.snd, (M.snd.fst).snd.snd.fst,  (M.snd.snd.fst).snd.fst,      (M.snd.snd.snd).fst)
  )

-- The `columnround_output` function is the inverse of the `columnround_input` function.
lemma columnround_output_is_inv_of_input : columnround_output (columnround_input M) = M :=
begin
  unfold columnround_input,
  unfold columnround_output,
  simp only [prod.mk.eta],
end

end utils