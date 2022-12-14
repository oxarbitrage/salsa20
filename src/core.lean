/-
  The `hash` and `core` functions, the non existing inverse and the `collision` theorems.
-/

import doubleround
import littleendian

open doubleround
open littleendian
open operations
open params
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

  Another approach will be to treat `hash` and `hash_inv` as a generic function, assume or prove they are not
  bijective and then assume or prove no bijective functions does not have an inverse. 

  -- Hash as a generic function that returns the same type as its input.
  variable hash' : matrix64Type → matrix64Type 

  -- A potential generic inverse of the hash that returns the same type as its input.
  variable hash_inv : matrix64Type → matrix64Type 

  -- Hash function is not bijective then inverse does not exist.
  -- TODO: prove or assume hash is not bijective.
  -- TODO: prove or assume a non bijective function does not have an inverse.
  lemma hash_has_no_inverse (A : matrix64Type) : ¬ hash'.bijective → ¬hash_inv (hash' A) = A  
-/

/-
  Theorem `doubleround_is_left_invariant` is independent of the number of rounds performed.

  `doubleround_10_is_left_invariant` is created proving the invariance for 10 rounds.
-/

-- Have a random number that we will use in some of the proofs below.
variable A : bitvec params.word_len

-- `doubleround_10` is left invariant. 
@[simp] theorem doubleround_10_is_left_invariant : doubleround_10 (doubleround.input A) = doubleround.input A :=
begin
  unfold doubleround_10,
  simp only [doubleround_is_left_invariant],
end


/-
  Salsa20 core function can behave as a linear transformation of the form 2 * A
  
  https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

  Theorem 5 of the paper.
-/
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

  https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

  Theorem 6 of the paper.
-/

-- the maximum value Z can be.
variable z : fin (bitvec.to_nat two_31)

-- Z < 2³¹
def Z : bitvec word_len := bitvec.of_nat word_len z.val
-- Z′ = Z + 2³¹
def Z' : bitvec word_len := (Z z) MOD two_31

/- An hypotetical collission output of the `core` function where the inputs are:
  
  Z −Z Z −Z
  −Z Z −Z Z
  Z −Z Z −Z
  −Z Z −Z Z

  or

  Z' −Z' Z' −Z'
  −Z' Z' −Z' Z'
  Z' −Z' Z' −Z'
  −Z' Z' −Z' Z'

  Where Z and Z' are of the form of the definitions above.

  Note : This type of input is not allowed in Salsa20. 
  When expansion matrix us used, diagonal constants are added that mitigates this problem.

  https://www.ecrypt.eu.org/stream/papersdir/2008/011.pdf

  However, at the `core` function level, wthout the constants added, this inputs are possible.
-/
def output : matrixType := do 
  let x := Z z,
  (
    (2 * x, 2 *-x, 2 * x, 2 * -x),
    (2 *-x, 2 * x, 2 *-x, 2 * x),
    (2 * x, 2 *-x, 2 * x, 2 * -x),
    (2 *-x, 2 * x, 2 *-x, 2 * x)
  )

-- Two different specially crafted inputs produces the same output.
@[simp] theorem collision 
  -- TODO: this 4 assumptions should be true by definition as they can be proved easily for nat numbers and
  -- fintypes however the bitvec conversions makes them a bit trickier.
  (h1 : Z z < two_31) (h2 : Z' z = Z z MOD two_31) (h3 : -Z z < two_31) (h4 : -Z' z = (-Z z) MOD two_31) :
  -- Two different inputs will produce the same output.
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
        rw ← modular_magic,
        { exact h1 },
        { exact h2 },
      },
      have h6 : 2 * (-Z' z) = 2 * (-Z z),
      {
        rw ← modular_magic,
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

-- Random numbers to form a random input matrix
variables a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ : bitvec word_len

-- A random input matrix.
def Input : matrixType := (
  (a₀, a₁, a₂, a₃),
  (a₄, a₅, a₆, a₇),
  (a₈, a₉, a₁₀, a₁₁),
  (a₁₂, a₁₃, a₁₄, a₁₅)
)

-- A matrix consisting of all 2³¹ (0x80000000) bit vectors.
def Delta : matrixType :=
  (
    (0x80000000, 0x80000000, 0x80000000, 0x80000000),
    (0x80000000, 0x80000000, 0x80000000, 0x80000000),
    (0x80000000, 0x80000000, 0x80000000, 0x80000000),
    (0x80000000, 0x80000000, 0x80000000, 0x80000000)
  )

-- A matrix where all its elements are zero.
def Zero : matrixType :=
  (
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)
  )

-- core of delta is always zero.
lemma core_of_delta: core Delta = Zero := rfl

-- core of zero is always zero.
lemma core_of_zero: core Zero = Zero := rfl

--
local notation `INPUT` := Input a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅

/-
  The specially crafted input based in some random input produces the same result as the original input. 

  TODO: prove.

  - quarterrround conserves the difference.
  - rowround conserves the difference.
  - columnround conserves the difference.
  - doubleround conserves the difference.
  - doubleround_10 conserves the difference.
  - mod_matrix cancel the difference.

  https://crypto.stackexchange.com/questions/26437/collision-or-second-preimage-for-the-chacha-core
  https://www.iacr.org/archive/fse2008/50860470/50860470.pdf
-/
lemma differences_cancel : mod_matrix (doubleround_10 (xor_matrix INPUT Delta)) (xor_matrix INPUT Delta) = 
  mod_matrix (doubleround_10 INPUT) INPUT :=
begin
  unfold doubleround_10,
  sorry,
end

/-
  As stated in https://www.ecrypt.eu.org/stream/papersdir/2008/011.pdf there are known collissions in salsa20 core
  in the form of salsa20(x) = salsa20 (x + Δ), where Δ = (0x80000000, ...).

  This is also Theorem 7 of https://www.iacr.org/archive/fse2008/50860470/50860470.pdf
-/
theorem known_collissions : core (xor_matrix INPUT Delta) = core INPUT :=
begin
  unfold core,
  rw differences_cancel,
end


end core
