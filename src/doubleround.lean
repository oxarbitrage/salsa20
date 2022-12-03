/-
  The `doubleround` function and its inverse
-/

import rowround
import columnround

open params
open operations
open quarterround
open rowround
open columnround
open utils

namespace doubleround

-- An random input matrix to be used as inputs and outputs of `doubleround` and `doubleround_inv`.
variable M : matrixType

-- doubleround(x) = rowround(columnround(x))
def doubleround : matrixType := 
  rowround_output $ rowround $ rowround_input $ columnround_output $ columnround $ columnround_input M


--  doubleround_inv(x) = columnround_inv(rowround_inv(x))
def doubleround_inv : matrixType := 
  columnround_output $ columnround_inv $ columnround_input $ rowround_output $ rowround_inv $ rowround_input M

-- For any `doubleround` output, we can get back to original values using the defined inverse.
lemma doubleround_is_inv : doubleround_inv (doubleround M) = M :=
begin
  unfold doubleround_inv,
  unfold doubleround,

  unfold columnround_inv,
  unfold columnround,
  unfold rowround,
  unfold rowround_inv,

  unfold columnround_input,
  unfold columnround_output,

  unfold rowround_input,
  unfold rowround_output,

  simp only [prod.mk.eta],

  repeat { rw columnround_single_is_inv },
  repeat { rw rowround_single_is_inv },

  simp only [prod.mk.eta],

  repeat { rw columnround_single_is_inv },
  repeat { rw rowround_single_is_inv },

  simp only [prod.mk.eta],
end

end doubleround
