/-
  Types
-/

import params

open params

namespace types

-- We define a row or a column to be a tuple of 4 bit vectors.
notation `vecType` := (bitvec word_len) × (bitvec word_len) × (bitvec word_len) × (bitvec word_len) 

-- A 16 elements matrix type.
notation `matrixType` := vecType × vecType × vecType × vecType

-- A 64 elements matrix type.
notation `matrix64Type` := matrixType × matrixType × matrixType × matrixType

end types
