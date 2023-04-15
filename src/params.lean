
import data.bitvec.basic

namespace params

/-!
  # Parameters

  Constants used in salsa20.
-/

/-- A byte is a bitvec of 8 bits. -/
def byte_len : ℕ := 8
/-- A word is a bitvec of 32 bits. -/
@[simp] def word_len : ℕ := 32

/-- Sums are all done modulo 2³². -/
@[simp] def mod : ℕ := (2^word_len)

/-- The maxumum value a bitvec of `word_len` can take. -/
@[simp] def max_bitvec : bitvec word_len := bitvec.of_nat word_len (mod - 1)

/-- 2³¹ as a bitvector of 32 bits. -/
def two_31 := bitvec.of_nat word_len (2^(word_len - 1))

end params
