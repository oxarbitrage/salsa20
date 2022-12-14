/-
  The `rowround` function and its inverse
-/

import params
import quarterround
import utils

open params
open operations
open quarterround
open utils

namespace rowround

-- A random row or column of a matrix
variable R : vecType

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
@[simp] lemma rowround_single_is_inv : rowround_single_inv (rowround_single R) = R :=
begin
  unfold rowround_single_inv,
  unfold rowround_single,
  unfold quarterround_inv,
  unfold quarterround,

  rw [qr0_is_inv, qr1_is_inv, qr2_is_inv, qr3_is_inv],

  finish,
end

/- Apply `rowround_single` to get a row round matrix output -/
def rowround : matrixType :=
  (
    rowround_single M.fst,
    rowround_single M.snd.fst,
    rowround_single M.snd.snd.fst,
    rowround_single M.snd.snd.snd
  )

/- Reverses `rowround` by doing `rowround_single_inv` to get the original matrix output -/
def rowround_inv : matrixType :=
  (
    rowround_single_inv M.fst,
    rowround_single_inv M.snd.fst,
    rowround_single_inv M.snd.snd.fst,
    rowround_single_inv M.snd.snd.snd
  )

-- For any `rowround` output, we can get back to original values using the defined inverse.
@[simp] lemma rowround_is_inv : rowround_inv (rowround M) = M :=
begin
  unfold rowround_inv,
  unfold rowround,

  repeat { rw rowround_single_is_inv },

  simp only [prod.mk.eta],
end

/-
  Left invariance of the rowround function: https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

  Theorem 2 of the paper.
-/

-- Have a few numbers to form the invariant input.
variables A B C D : bitvec word_len

-- An input of this form should be invariant.
def input : matrixType := (
  (A, -A, A, -A),
  (B, -B, B, -B),
  (C, -C, C, -C),
  (D, -D, D, -D)
)

-- `rowround` is left invariant. 
@[simp] theorem rowround_is_left_invariant : rowround (input A B C D) = input A B C D :=
begin
  unfold rowround,
  unfold rowround_single,
  unfold input,
  simp only [
    quarterround_is_left_invariant, quarterround_is_left_invariant, 
    quarterround_is_left_invariant, quarterround_is_left_invariant
  ],
end

end rowround
