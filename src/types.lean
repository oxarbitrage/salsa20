/-
  Types
-/
import data.matrix.basic
import data.matrix.notation
import data.fin.vec_notation

import params

open params

namespace types

-- A bitvec 32
notation `wordType` := bitvec word_len

-- A 1 x 4 matrix.
notation `vecType` := wordType × wordType × wordType × wordType

-- A 4 x 4 matrix.
notation `matrixType` := vecType × vecType × vecType × vecType


end types
