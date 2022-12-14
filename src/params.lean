/-
  Constants used in salsa20.
-/
import data.bitvec.basic
import tactic

namespace params

-- A byte is a bitvec of 8 bits.
def byte_len : ℕ := 8
-- A word is a bitvec of 32 bits.
def word_len : ℕ := 32 

-- sums are done modulo 2^32
def mod : ℕ := (2^word_len)

-- the maxumum valuea bitvec can be.
def max_bitvec : bitvec word_len := bitvec.of_nat word_len (mod - 1)

-- 2³² as a bitvector of 32 bits.
def two_31 := bitvec.of_nat word_len (2^(word_len - 1))

end params
