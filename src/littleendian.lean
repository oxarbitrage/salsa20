/-
  The `littleendian` function and its inverse
-/
import params
import utils

open params
open utils

namespace littleendian

-- An random sequence of 4 words.
variable b : vecType

-- If b = (b₀, b₁, b₂, b₃) then 
-- littleendian(b) = b₀ + (2^8)*b₁ + (2^16)*b₂ + (2^24)*b₃
def littleendian : bitvec word_len := 
  bitvec.of_nat word_len (
    b.fst.to_nat + (2^8) * b.snd.fst.to_nat + (2^16) * b.snd.snd.fst.to_nat + (2^24) * b.snd.snd.snd.to_nat
  )

/-
  The inverse of little-endian is indeed the function that sends a word (32 bits) 
  back to the sequence of 4 bytes in a little endian way, so the least significant
  byte goes first, and the most significant byte goes last. 
  So it maps 𝑤 to w & 0xff, (w >> 8) & 0xff, (w >> 16) & 0xff, (w >> 24) & 0xff

  https://crypto.stackexchange.com/a/22314
-/
def littleendian_inv (w : bitvec word_len) : vecType :=
  (
    bitvec.of_nat word_len $ bitvec.to_nat $ bitvec.and w 0xff,
    bitvec.of_nat word_len $ bitvec.to_nat $ (bitvec.ushr w 8).and 0xff,
    bitvec.of_nat word_len $ bitvec.to_nat $ (bitvec.ushr w 16).and 0xff, 
    bitvec.of_nat word_len $ bitvec.to_nat $ (bitvec.ushr w 24).and 0xff
  )

-- The `littleendian` function is invertible and its inverse is `littleendian_inv`.
axiom littleendian_is_inv : littleendian_inv (littleendian b) = b



-- An random input 64 bytes matrix to be used as inputs and outputs of `hash` and `hash_inv`.
variable X : matrix64Type

--
variable Y : matrixType

-- Reduce the 64 bytes sequence to a 16 bytes one by using little endian.
def reduce : matrixType :=
  (
    (
      littleendian (((X.fst).fst).fst,          ((X.fst).fst).snd.fst,          ((X.fst).fst).snd.snd.fst,          ((X.fst).fst).snd.snd.snd), 
      littleendian (((X.fst).snd.fst).fst,      ((X.fst).snd.fst).snd.fst,      ((X.fst).snd.fst).snd.snd.fst,      ((X.fst).snd.fst).snd.snd.snd),
      littleendian (((X.fst).snd.snd.fst).fst,  ((X.fst).snd.snd.fst).snd.fst,  ((X.fst).snd.snd.fst).snd.snd.fst,  ((X.fst).snd.snd.fst).snd.snd.snd),
      littleendian (((X.fst).snd.snd.snd).fst,  ((X.fst).snd.snd.snd).snd.fst,  ((X.fst).snd.snd.snd).snd.snd.fst,  ((X.fst).snd.snd.snd).snd.snd.snd)
    ),
    (
      littleendian (((X.snd.fst).fst).fst,          ((X.snd.fst).fst).snd.fst,          ((X.snd.fst).fst).snd.snd.fst,          ((X.snd.fst).fst).snd.snd.snd), 
      littleendian (((X.snd.fst).snd.fst).fst,      ((X.snd.fst).snd.fst).snd.fst,      ((X.snd.fst).snd.fst).snd.snd.fst,      ((X.snd.fst).snd.fst).snd.snd.snd),
      littleendian (((X.snd.fst).snd.snd.fst).fst,  ((X.snd.fst).snd.snd.fst).snd.fst,  ((X.snd.fst).snd.snd.fst).snd.snd.fst,  ((X.snd.fst).snd.snd.fst).snd.snd.snd),
      littleendian (((X.snd.fst).snd.snd.snd).fst,  ((X.snd.fst).snd.snd.snd).snd.fst,  ((X.snd.fst).snd.snd.snd).snd.snd.fst,  ((X.snd.fst).snd.snd.snd).snd.snd.snd)
    ),
    (
      littleendian (((X.snd.snd.fst).fst).fst,          ((X.snd.snd.fst).fst).snd.fst,          ((X.snd.snd.fst).fst).snd.snd.fst,          ((X.snd.snd.fst).fst).snd.snd.snd), 
      littleendian (((X.snd.snd.fst).snd.fst).fst,      ((X.snd.snd.fst).snd.fst).snd.fst,      ((X.snd.snd.fst).snd.fst).snd.snd.fst,      ((X.snd.snd.fst).snd.fst).snd.snd.snd),
      littleendian (((X.snd.snd.fst).snd.snd.fst).fst,  ((X.snd.snd.fst).snd.snd.fst).snd.fst,  ((X.snd.snd.fst).snd.snd.fst).snd.snd.fst,  ((X.snd.snd.fst).snd.snd.fst).snd.snd.snd),
      littleendian (((X.snd.snd.fst).snd.snd.snd).fst,  ((X.snd.snd.fst).snd.snd.snd).snd.fst,  ((X.snd.snd.fst).snd.snd.snd).snd.snd.fst,  ((X.snd.snd.fst).snd.snd.snd).snd.snd.snd)
    ),
    (
      littleendian (((X.snd.snd.snd).fst).fst,          ((X.snd.snd.snd).fst).snd.fst,          ((X.snd.snd.snd).fst).snd.snd.fst,          ((X.snd.snd.snd).fst).snd.snd.snd), 
      littleendian (((X.snd.snd.snd).snd.fst).fst,      ((X.snd.snd.snd).snd.fst).snd.fst,      ((X.snd.snd.snd).snd.fst).snd.snd.fst,      ((X.snd.snd.snd).snd.fst).snd.snd.snd),
      littleendian (((X.snd.snd.snd).snd.snd.fst).fst,  ((X.snd.snd.snd).snd.snd.fst).snd.fst,  ((X.snd.snd.snd).snd.snd.fst).snd.snd.fst,  ((X.snd.snd.snd).snd.snd.fst).snd.snd.snd),
      littleendian (((X.snd.snd.snd).snd.snd.snd).fst,  ((X.snd.snd.snd).snd.snd.snd).snd.fst,  ((X.snd.snd.snd).snd.snd.snd).snd.snd.fst,  ((X.snd.snd.snd).snd.snd.snd).snd.snd.snd)
    )
  )

-- 
def aument : matrix64Type := (
  (
    littleendian_inv Y.fst.fst,
    littleendian_inv Y.fst.snd.fst,
    littleendian_inv Y.fst.snd.snd.fst,
    littleendian_inv Y.fst.snd.snd.snd
  ),
  (
    littleendian_inv Y.snd.fst.fst,
    littleendian_inv Y.snd.fst.snd.fst,
    littleendian_inv Y.snd.fst.snd.snd.fst,
    littleendian_inv Y.snd.fst.snd.snd.snd
  ),
  (
    littleendian_inv Y.snd.snd.fst.fst,
    littleendian_inv Y.snd.snd.fst.snd.fst,
    littleendian_inv Y.snd.snd.fst.snd.snd.fst,
    littleendian_inv Y.snd.snd.fst.snd.snd.snd
  ),
  (
    littleendian_inv Y.snd.snd.snd.fst,
    littleendian_inv Y.snd.snd.snd.snd.fst,
    littleendian_inv Y.snd.snd.snd.snd.snd.fst,
    littleendian_inv Y.snd.snd.snd.snd.snd.snd
  )
)


end littleendian