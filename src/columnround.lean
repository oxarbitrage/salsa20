/-
  The `columnround` function and its inverse
-/

import rowround

open params
open operations
open quarterround
open rowround

namespace columnround

-- Have some random columns to use in proofs and definitions.
variables C1 C2 C3 C4 : vecType

/-
  Apply 4 single column rounds with a 16 byte input sequence separated in 4 columns.
  For salsa20 each row is as:

  (y₀, y₄, y₈, y₁₂) = quarterround(x₀, x₄, x₈, x₁₂)
  (y₅, y₉, y₁₃, y₁) = quarterround(x₅, x₉, x₁₃, x₁)
  (y₁₀, y₁₄, y₂, y₆) = quarterround(x₁₀, x₁₄, x₂, x₆)
  (y₁₅, y₃, y₇, y₁₁) = quarterround(x₁₅, x₃, x₇, x₁₁)
-/
def columnround : matrixType := rowround C1 C2 C3 C4

/-
  Apply 4 single column rounds with a 16 byte input sequence separated in 4 columns.
  For salsa20 each row is as:

  (y₀, y₄, y₈, y₁₂) = quarterround(x₀, x₄, x₈, x₁₂)
  (y₅, y₉, y₁₃, y₁) = quarterround(x₅, x₉, x₁₃, x₁)
  (y₁₀, y₁₄, y₂, y₆) = quarterround(x₁₀, x₁₄, x₂, x₆)
  (y₁₅, y₃, y₇, y₁₁) = quarterround(x₁₅, x₃, x₇, x₁₁)
-/
def columnround_inv : matrixType := rowround_inv C1 C2 C3 C4

-- For any `columnround` output, we can get back to original values using the defined inverse.
lemma columnround_is_inv : columnround_inv (columnround C1 C2 C3 C4).fst
  (columnround C1 C2 C3 C4).snd.fst (columnround C1 C2 C3 C4).snd.snd.fst (columnround C1 C2 C3 C4).snd.snd.snd =
  (C1, C2, C3, C4) :=
begin
  unfold columnround_inv,
  unfold columnround,

  apply rowround_is_inv,
end

end columnround
