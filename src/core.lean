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
def doubleround_10 (X : matrixType): matrixType := 
  doubleround $ doubleround $ doubleround $ doubleround $ doubleround $ doubleround $ doubleround 
    $ doubleround $ doubleround $ doubleround $ X 

-- Modular 2^32 addition of 4x4 matrices by doing Aᵢⱼ + Bᵢⱼ
-- The `MOD` operation (modulo 2^32 addition) is the key to make the hash function irreversible.
-- Everything is reversible except for this addition.
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
def core (X : matrixType) : matrixType := mod_matrix (doubleround_10 X) X

-- Do the hash.
def hash (X : matrix64Type) : matrix64Type := aument (core (reduce X))


/-
  Hash does not have an inverse.

  TODO: It should be easy to prove or assume the MOD operation is not reversible. 
        Then `mod_as_matrix` is irreversible and `hash` is irreverisble.
        I was not able to make this proof in lean yet.
-/

/-
  Another approach will be to treat `hash` and `hash_inv` as a generic function, assume or prove they are not
  bijective and then assume or prove not bijective functions does not have an inverse. 
-/

-- Hash as a generic function that returns the same type as its input.
variable hash' : matrix64Type → matrix64Type 

-- A potential generic inverse of the hash that returns the same type as its input.
variable hash_inv : matrix64Type → matrix64Type 

-- Hash function is not bijective then inverse does not exist.
-- TODO: prove hash is not bijective.
-- TODO: prove a non bijective function does not have an inverse.
axiom hash_has_no_inverse (A : matrix64Type) : ¬ hash'.bijective → ¬hash_inv (hash' A) = A  


/-
  Salsa20 core function can behave as a linear transformation: https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

-/

--
variable A : bitvec params.word_len

--
def input : matrixType := (
  (A, -A, A, -A),
  (-A, A, -A, A),
  (A, -A, A, -A),
  (-A, A, -A, A)
)

--
variable X : bitvec params.word_len

-- TODO: move this to operations axioms and use them in `quarterround`, `rowround`, `columnround` and here.
def mod_neg : Prop := ∀ X, X MOD (-X) = ZERO
def neg_mod : Prop := ∀ X, (-X) MOD X = ZERO

-- TODO: make this axioms
def double_mod : Prop := ∀ X, X MOD X = 2 * X
def double_neg_mod : Prop := ∀ X, (-X) MOD -X = 2 * (-X)

-- `core` behaves as a linear transformation of the form 2 * A. 
theorem salsa20_core_linear_transformation (h1 : mod_neg) (h2 : neg_mod) (h3 : double_mod) (h4 : double_neg_mod) : 
  core (doubleround.input A) = 2 * (doubleround.input A) :=
begin
  unfold core,
  unfold doubleround_10,
  unfold mod_matrix,
  repeat { rw doubleround_is_left_invariant },
  unfold doubleround.input,
  {
    simp,
    unfold double_mod at h3,
    unfold double_neg_mod at h4,
    rw h3,
    rw h4,
    refl,
  },
  any_goals { apply h1 },
  any_goals { apply h2 },
end


end core
