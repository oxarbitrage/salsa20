/-
  The `rowround` function and its inverse
-/

import params
import quarterround

open params
open operations
open quarterround

namespace rowround

-- We define a row or a column to be a tuple of 4 bit vectors.
-- This is the input and output of the `quarterround` function. 
notation `matrixType` := vecType × vecType × vecType × vecType

-- Have some random rows to use in proofs and definitions.
variables R R1 R2 R3 R4 : vecType

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
    rowround_single R1,
    rowround_single R2,
    rowround_single R3,
    rowround_single R4
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
    rowround_single_inv R1,
    rowround_single_inv R2,
    rowround_single_inv R3,
    rowround_single_inv R4
  )

-- For any `rowround` output, we can get back to original values using the defined inverse.
lemma rowround_is_inv : rowround_inv (rowround R1 R2 R3 R4).fst
  (rowround R1 R2 R3 R4).snd.fst (rowround R1 R2 R3 R4).snd.snd.fst (rowround R1 R2 R3 R4).snd.snd.snd =
  (R1, R2, R3, R4) :=
begin
  unfold rowround_inv,
  unfold rowround,

  repeat { rw rowround_single_is_inv },
end

end rowround
