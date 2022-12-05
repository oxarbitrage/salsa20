/-
  The `columnround` function and its inverse
-/

import rowround

open params
open operations
open quarterround
open rowround

namespace columnround

-- A random input matrix to be used as inputs and outputs of `columnround` and `columnround_inv`.
variable M : matrixType

--  Without ordering for inputs, a `columnround` is exactly the same as a `rowround`.
def columnround : matrixType := rowround M

--  Without ordering for inputs, a `columnround_inv` is exactly the same as a `rowround_inv`.
def columnround_inv : matrixType := rowround_inv M

-- For any `columnround` output, we can get back to original values using the defined inverse.
lemma columnround_is_inv : columnround_inv (columnround M) = M :=
begin
  unfold columnround_inv,
  unfold columnround,

  apply rowround_is_inv,
end

/-
  Left invariance of the columnround function: https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

-/

--
variables A B C D : bitvec word_len

--
def input : matrixType := (
  (A, -B, C, -D),
  (-A, B, -C, D),
  (A, -B, C, -D),
  (-A, B, -C, D)
)

--
variable X : bitvec word_len

-- TODO: move this to operations axioms and use them in `quarterround`, `rowround` and here.
def mod_neg : Prop := ∀ X, X MOD (-X) = ZERO
def neg_mod : Prop := ∀ X, (-X) MOD X = ZERO

-- `columnround` is left invariant. 
theorem columnround_is_left_invariant (h1 : mod_neg) (h2 : neg_mod) : 
  utils.columnround_output (columnround (utils.columnround_input (input A B C D))) = input A B C D :=
begin
  unfold columnround,
  unfold input,
  unfold utils.columnround_input,
  unfold utils.columnround_output,
  unfold mod_neg at h1,
  unfold neg_mod at h2,
  unfold rowround,
  unfold rowround_single,

  simp only [prod.mk.inj_iff],

  repeat { rw quarterround_is_left_invariant },

  simp only [eq_self_iff_true, and_self],

  any_goals { apply h1 },
  any_goals { apply h2 },
end


end columnround
