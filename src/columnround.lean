/-
  The `columnround` function and its inverse
-/

import rowround

open params
open operations
open quarterround
open rowround

namespace columnround

-- An random input matrix to be used as inputs and outputs of `columnround` and `columnround_inv`.
variable M : matrixType

/-
  Apply 4 single column rounds with a 16 byte input sequence separated in 4 columns.
  For salsa20 each row is as:

  (y₀, y₄, y₈, y₁₂) = quarterround(x₀, x₄, x₈, x₁₂)
  (y₅, y₉, y₁₃, y₁) = quarterround(x₅, x₉, x₁₃, x₁)
  (y₁₀, y₁₄, y₂, y₆) = quarterround(x₁₀, x₁₄, x₂, x₆)
  (y₁₅, y₃, y₇, y₁₁) = quarterround(x₁₅, x₃, x₇, x₁₁)
-/
def columnround : matrixType := rowround M

/-
  Apply 4 single column rounds with a 16 byte input sequence separated in 4 columns.
  For salsa20 each row is as:

  (y₀, y₄, y₈, y₁₂) = quarterround(x₀, x₄, x₈, x₁₂)
  (y₅, y₉, y₁₃, y₁) = quarterround(x₅, x₉, x₁₃, x₁)
  (y₁₀, y₁₄, y₂, y₆) = quarterround(x₁₀, x₁₄, x₂, x₆)
  (y₁₅, y₃, y₇, y₁₁) = quarterround(x₁₅, x₃, x₇, x₁₁)
-/
def columnround_inv : matrixType := rowround_inv M

-- For any `columnround` output, we can get back to original values using the defined inverse.
lemma columnround_is_inv : columnround_inv (columnround M) = M :=
begin
  unfold columnround_inv,
  unfold columnround,

  apply rowround_is_inv,
end

end columnround
