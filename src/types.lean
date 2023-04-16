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
notation `vecType` := matrix (fin 1) (fin 4) (bitvec word_len)

-- A 4 x 4 matrix.
notation `matrixType` := matrix (fin 4) (fin 4) (bitvec word_len)

end types
