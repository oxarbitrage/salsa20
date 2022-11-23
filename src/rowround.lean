
import data.matrix.basic

import params
import quarterround

open params
open operations
open quarterround

namespace rowround

-- We define a row to be a tuple of 4 bit vectors.
notation `rowType` := (bitvec word_len) × (bitvec word_len) × (bitvec word_len) × (bitvec word_len) 

-- Have some random rows to use in proofs and definitions.
variable R : rowType
variable R1 : rowType
variable R2 : rowType
variable R3 : rowType
variable R4 : rowType

-- The row round of a single row. Complete `rowround` function will use 4 of this.
def rowround_single : rowType :=
  (
    (quarterround R).fst, (quarterround R).snd.fst, 
    (quarterround R).snd.snd.fst, (quarterround R).snd.snd.snd
  )

-- The inverse of a single row round.
def rowround_single_inv : rowType :=
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

  rw qr0_is_inv,
  rw qr1_is_inv,
  rw qr2_is_inv,
  rw qr3_is_inv,

  finish,
end

/-
  Do the 4 rowrounds with the 16 bytes input sequence separated in 4 rows:

  (z₀, z₁, z₂, z₃) = quarterround(y₀, y₁, y₂, y₃)
  (z₅, z₆, z₇, z₄) = quarterround(y₅, y₆, y₇, y₄)
  (z₁₀, z₁₁, z₈, z₉) = quarterround(y₁₀, y₁₁, y₈, y₉)
  (z₁₅, z₁₂, z₁₃, z₁₄) = quarterround(y₁₅, y₁₂, y₁₃, y₁₄)

  Callers need to call in the right order for salsa20. For example, if the second row provided is
  in the order (y₁₀, y₁₁, y₈, y₉), then the output will be (z₁₀, z₁₁, z₈, z₉) as the second row of 
  the response, in that order. 
-/
def rowround :
  rowType × rowType × rowType × rowType :=
  (
    rowround_single R1,
    rowround_single R2,
    rowround_single R3,
    rowround_single R4
  )

/-
  Do the 4 inverse rowrounds with the 16 bytes input sequence separated in 4 rows:

  (y₀, y₁, y₂, y₃) = quarterround_inv(z₀, z₁, z₂, z₃)
  (y₅, y₆, y₇, y₄) = quarterround_inv(z₅, z₆, z₇, z₄)
  (y₁₀, y₁₁, y₈, y₉) = quarterround_inv(z₁₀, z₁₁, z₈, z₉)
  (y₁₅, y₁₂, y₁₃, y₁₄) = quarterround_inv(z₁₅, z₁₂, z₁₃, z₁₄)

  Callers need to call in the right order for salsa20. For example, if the second row provided is
  in the order (z₁₀, z₁₁, z₈, z₉), then the output will be (y₁₀, y₁₁, y₈, y₉) as the second row of 
  the response, in that order. 
-/
def rowround_inv : rowType × rowType × rowType × rowType :=
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
