/-
  The `rowround` function and its inverse
-/

import params
import quarterround

open params
open operations
open quarterround

namespace rowround

-- A random row or column of a matrix
variable R : vecType

-- A 16 elements matrix type used as `rowround` and `rowround_inv` input and output.
notation `matrixType` := vecType × vecType × vecType × vecType

-- A random input matrix
variable M : matrixType

-- The row round of a single row. Complete `rowround` function will use 4 of this.
def rowround_single : vecType :=
  (
    (quarterround R).fst, (quarterround R).snd.fst, 
    (quarterround R).snd.snd.fst, (quarterround R).snd.snd.snd
  )

-- The inverse of a single row round.
def rowround_single_inv : vecType :=
  (
    (quarterround_inv R).fst, (quarterround_inv R).snd.fst, 
    (quarterround_inv R).snd.snd.fst, (quarterround_inv R).snd.snd.snd
  )

-- Each row is invertible.
lemma rowround_single_is_inv : rowround_single_inv (rowround_single R) = R :=
begin
  unfold rowround_single_inv,
  unfold rowround_single,
  unfold quarterround_inv,
  unfold quarterround,

  rw [qr0_is_inv, qr1_is_inv, qr2_is_inv, qr3_is_inv],

  finish,
end

/-
  Apply 4 single row rounds with a 16 byte input sequence separated in 4 rows.
  For salsa20 each row is as:

  (z₀, z₁, z₂, z₃) = quarterround(y₀, y₁, y₂, y₃)
  (z₅, z₆, z₇, z₄) = quarterround(y₅, y₆, y₇, y₄)
  (z₁₀, z₁₁, z₈, z₉) = quarterround(y₁₀, y₁₁, y₈, y₉)
  (z₁₅, z₁₂, z₁₃, z₁₄) = quarterround(y₁₅, y₁₂, y₁₃, y₁₄)
-/
def rowround : matrixType :=
  (
    rowround_single M.fst,
    rowround_single M.snd.fst,
    rowround_single M.snd.snd.fst,
    rowround_single M.snd.snd.snd
  )

/-
  Apply 4 single inverse row rounds with a 16 byte input sequence separated in 4 rows.
  For salsa20 each row is as:

  (y₀, y₁, y₂, y₃) = quarterround_inv(z₀, z₁, z₂, z₃)
  (y₅, y₆, y₇, y₄) = quarterround_inv(z₅, z₆, z₇, z₄)
  (y₁₀, y₁₁, y₈, y₉) = quarterround_inv(z₁₀, z₁₁, z₈, z₉)
  (y₁₅, y₁₂, y₁₃, y₁₄) = quarterround_inv(z₁₅, z₁₂, z₁₃, z₁₄)
-/
def rowround_inv : matrixType :=
  (
    rowround_single_inv M.fst,
    rowround_single_inv M.snd.fst,
    rowround_single_inv M.snd.snd.fst,
    rowround_single_inv M.snd.snd.snd
  )

-- For any `rowround` output, we can get back to original values using the defined inverse.
lemma rowround_is_inv : rowround_inv (rowround M) = M :=
begin
  unfold rowround_inv,
  unfold rowround,

  repeat { rw rowround_single_is_inv },

  simp only [prod.mk.eta],
end

end rowround
