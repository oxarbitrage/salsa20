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

end columnround
