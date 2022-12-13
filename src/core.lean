/-
  The `hash` function and its inverse
-/

import doubleround
import littleendian

open doubleround
open littleendian
open operations
open utils


namespace core

-- Apply double round 10 times to a reduced input.
def doubleround_10 (X : matrixType): matrixType := 
  doubleround $ doubleround $ doubleround $ doubleround $ doubleround $ doubleround $ doubleround 
    $ doubleround $ doubleround $ doubleround $ X

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
  Theorem `doubleround_is_left_invariant` is independent of the number of rounds performed.

  `doubleround_10_is_left_invariant` is created proving the invariance for 10 rounds.
-/

--
variable A : bitvec params.word_len

-- `doubleround_10` is left invariant. 
@[simp] theorem doubleround_10_is_left_invariant : doubleround_10 (doubleround.input A) = doubleround.input A :=
begin
  unfold doubleround_10,
  simp only [doubleround_is_left_invariant],
end


/-
  Salsa20 core function can behave as a linear transformation: https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

-/

-- `core` behaves as a linear transformation of the form 2 * A. 
@[simp] theorem salsa20_core_linear_transformation : core (doubleround.input A) = 2 * (doubleround.input A) :=
begin
  unfold core,
  unfold doubleround_10,
  unfold mod_matrix,
  repeat { rw doubleround_is_left_invariant },
  unfold doubleround.input,
  simp only [double_mod],
  refl,
end

/-
  Collisions
-/

--
variable z : fin (2^31)

def Z : bitvec 32 := bitvec.of_nat 32 z.val
def Z' : bitvec 32 := (Z z) MOD bitvec.of_nat 32 (2^31)

variable X : matrixType

-- Have 16 random numbers.
variables A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ A₁₀ A₁₁ A₁₂ A₁₃ A₁₄ A₁₅ : bitvec 32 

-- Distribute 2 * Matrix.
@[simp] lemma matrix_distribute_two :
  2 * ((A₀, A₁, A₂, A₃), (A₄, A₅, A₆, A₇), (A₈, A₉, A₁₀, A₁₁), (A₁₂, A₁₃, A₁₄, A₁₅)) = 
  (
    (2 * A₀, 2 * A₁, 2 * A₂, 2 * A₃),
    (2 * A₄, 2 * A₅, 2 * A₆, 2 * A₇),
    (2 * A₈, 2 * A₉, 2 * A₁₀, 2 * A₁₁),
    (2 * A₁₂, 2 * A₁₃, 2 * A₁₄, 2 * A₁₅)
  ) := rfl

-- The MOD sum of two equal matrices X is 2 times X. 
@[simp] lemma mod_matrix_double : mod_matrix X X = 2 * X :=
begin
  unfold mod_matrix,
  simp only [mod_self],

  rw ← matrix_distribute_two 
    X.fst.fst         X.fst.snd.fst         X.fst.snd.snd.fst         X.fst.snd.snd.snd
    X.snd.fst.fst     X.snd.fst.snd.fst     X.snd.fst.snd.snd.fst     X.snd.fst.snd.snd.snd
    X.snd.snd.fst.fst X.snd.snd.fst.snd.fst X.snd.snd.fst.snd.snd.fst X.snd.snd.fst.snd.snd.snd
    X.snd.snd.snd.fst X.snd.snd.snd.snd.fst X.snd.snd.snd.snd.snd.fst X.snd.snd.snd.snd.snd.snd,
  refl,
end

-- An output of a `core` function where the inputs were collision inputs.
def output : matrixType := do 
  let x := Z z,
  (
    (2 * x, 2 *-x, 2 * x, 2 * -x),
    (2 *-x, 2 * x, 2 *-x, 2 * x),
    (2 * x, 2 *-x, 2 * x, 2 * -x),
    (2 *-x, 2 * x, 2 *-x, 2 * x)
  )

--
@[simp] theorem collision 
  (h1 : Z' z < two_31) (h2 : Z z = Z' z MOD two_31) (h3 : -Z' z < two_31) (h4 : -Z z = (-Z' z) MOD two_31) :
  core (doubleround.input (Z' z)) = output z ∧ core (doubleround.input (Z z)) = output z :=
begin
  unfold core,
  split,
  {
    rw doubleround_10_is_left_invariant,
    {
      rw mod_matrix_double,
      unfold doubleround.input,

      -- aliases for `Z' z` and `-(Z' z)`
      let x' := Z' z,
      let neg_x' := -(Z' z),

      rw matrix_distribute_two 
        x'      neg_x'    x'      neg_x'
        neg_x'  x'        neg_x'  x'
        x'      neg_x'    x'      neg_x'
        neg_x'  x'        neg_x'  x',

      unfold output,

      have h5 : 2 * (Z' z) = 2 * (Z z),
      {
        rw modular_magic,
        { exact h1 },
        { exact h2 },
      },
      have h6 : 2 * (-Z' z) = 2 * (-Z z),
      {
        rw modular_magic,
        { exact h3 },
        { exact h4 },
      },
      rw h5,
      rw h6,
    },
  },
  {
    rw doubleround_10_is_left_invariant,
    {
      rw mod_matrix_double,
      unfold doubleround.input,

      -- aliases for `Z z` and `-(Z z)`
      let x := Z z,
      let neg_x := -(Z z),

      rw matrix_distribute_two 
        x     neg_x   x     neg_x
        neg_x x       neg_x x
        x     neg_x   x     neg_x
        neg_x x       neg_x x,

      unfold output,
    },
  }
end


end core
