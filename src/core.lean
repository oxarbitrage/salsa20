/-
  The `hash` function and its inverse
-/

import doubleround
import littleendian

open doubleround
open littleendian
open utils

namespace core

-- Apply double round 10 times to a reduced input.
def doubleround_10 (X : matrix64Type): matrixType := 
  doubleround $ doubleround $ doubleround $ doubleround $ doubleround $ doubleround $ doubleround 
    $ doubleround $ doubleround $ doubleround $ reduce X 

-- Modular 2^32 addition of 4x4 matrices by doing Aᵢⱼ + Bᵢⱼ
-- The `MOD` operation (modulo 2^32 addition) is the key to make the hash function irreversible.
-- Everything is reversible excect for this addition.
def mod_matrix (A B : matrixType) : matrixType := (
  (
    A.fst.fst          MOD B.fst.fst,
    A.fst.snd.fst      MOD B.fst.snd.fst,
    A.fst.snd.snd.fst  MOD B.fst.snd.snd.fst,
    A.fst.snd.snd.snd  MOD B.fst.snd.snd.snd
  ),
  (
    A.snd.fst.fst          MOD B.snd.fst.fst,
    A.snd.fst.snd.fst      MOD B.snd.fst.snd.fst,
    A.snd.fst.snd.snd.fst  MOD B.snd.fst.snd.snd.fst,
    A.snd.fst.snd.snd.snd  MOD B.snd.fst.snd.snd.snd
  ),
  (
    A.snd.snd.fst.fst          MOD B.snd.snd.fst.fst,
    A.snd.snd.fst.snd.fst      MOD B.snd.snd.fst.snd.fst,
    A.snd.snd.fst.snd.snd.fst  MOD B.snd.snd.fst.snd.snd.fst,
    A.snd.snd.fst.snd.snd.snd  MOD B.snd.snd.fst.snd.snd.snd
  ),
  (
    A.snd.snd.snd.fst          MOD B.snd.snd.snd.fst,
    A.snd.snd.snd.snd.fst      MOD B.snd.snd.snd.snd.fst,
    A.snd.snd.snd.snd.snd.fst  MOD B.snd.snd.snd.snd.snd.fst,
    A.snd.snd.snd.snd.snd.snd  MOD B.snd.snd.snd.snd.snd.snd
  )
)

-- Do addition modulo 2^32 of the reduced input and the doubleround of the reduced input.
def hash_inner (X : matrix64Type) : matrixType := mod_matrix (doubleround_10 X) (reduce X)

-- Do the hash.
def hash (X : matrix64Type) : matrix64Type := aument (hash_inner X)


/-
  Hash does not have an inverse.

  The above definitions are good for computation. For proving stuff we might have to go more generic.

  TODO: It should be easy to prove or assume the MOD operation is not reversible. 
        Then `mod_as_matrix` is irreversible and `hash` is irreverisble.
        I was not able to make this proof in lean yet.
-/

/-
  Another approach will be to 
-/

-- Hash as a generic function that returns the same type as its input.
variable hash' : matrix64Type → matrix64Type 

-- A potential generic inverse of the hash that returns the same type as its input.
variable hash_inv : matrix64Type → matrix64Type 

-- Hash function is not bijective then inverse does not exist.
-- TODO: prove hash is not bijective ?
-- TODO: if a function is not bijective then it does not have an inverse ?
axiom no_bijective_no_inverse' (A : matrix64Type) : ¬ hash'.bijective → ¬hash_inv (hash' A) = A  


end core
