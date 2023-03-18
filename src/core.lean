import doubleround
import littleendian

import category_theory.category.basic
import category_theory.core

open doubleround
open littleendian
open operations
open params
open utils

open category_theory

namespace core

/-!
  # Core

  - The `doubleround10` function and its inverse.
  - The `hash` and `core` functions, the non existing inverse.
  - The `collision` theorems.
-/

/-- Apply double round 10 times to a reduced input. -/
@[simp] def doubleround_10 (X : matrixType): matrixType :=
  doubleround' $ doubleround' $ doubleround' $ doubleround' $ doubleround' $ doubleround' $ doubleround'
    $ doubleround' $ doubleround' $ doubleround' $ X

/-- Inverse of `doubleround_10`. -/
@[simp] def doubleround_10_inv (X : matrixType): matrixType :=
  doubleround_inv' $ doubleround_inv' $ doubleround_inv' $ doubleround_inv' $ doubleround_inv'
  $ doubleround_inv' $ doubleround_inv' $ doubleround_inv' $ doubleround_inv' $ doubleround_inv' $ X

/-!
## Isomorphism of the doubleround_10 function

https://en.wikipedia.org/wiki/Isomorphism#Category_theoretic_view

> In category theory, given a category C, an isomorphism is a morphism `f : a ⟶ b` that has an inverse
> morphism `g : b ⟶  a` , that is, `f ∘ g = 𝟙 b` and `g ∘ f = 𝟙 a`.

-/

/-- The identity of a `doubleround_10` morphism given a sequence is the sequence. -/
@[simp] def id_doubleround_10 (seq : matrixType) := seq

/-- The identity of a `doubleround⁻¹` morphism given a sequence is the sequence. -/
@[simp] def id_doubleround_10_inv (seq : matrixType) := seq

/-- Isomorphism condition 1 : `doubleround_10⁻¹ ∘ doubleround_10 = 𝟙 doubleround_10` -/
@[simp] lemma isomorphism_left (seq : matrixType) : (doubleround_10_inv ∘ doubleround_10) seq =
  id_doubleround_10 seq :=
begin
  simp only [doubleround_10_inv, doubleround_10, id_doubleround_10, columnround_output, columnround.columnround_inv,
  columnround_input, columnround.columnround_inv', rowround.rowround_inv', doubleround_inv', function.comp_app,
  rowround_output, rowround.rowround, rowround_input, rowround.rowround', columnround.columnround', doubleround',
  columnround.columnround, rowround.rowround_single, quarterround.quarterround, rowround.rowround_inv,
  rowround.rowround_single_inv, quarterround.quarterround_inv, quarterround.qr0_is_inv, quarterround.qr1_is_inv,
  quarterround.qr2_is_inv, quarterround.qr3_is_inv, prod.mk.eta],
end

/-- Isomorphism condition 2 : `doubleround_10 ∘ doubleround_10⁻¹ = 𝟙 doubleround_10⁻¹` -/
@[simp] lemma isomorphism_right (seq : matrixType) : (doubleround_10 ∘ doubleround_10_inv) seq =
  id_doubleround_10_inv seq :=
begin
  simp only [doubleround_10, doubleround_10_inv, id_doubleround_10_inv, rowround_output, rowround.rowround, rowround_input,
  rowround.rowround', columnround.columnround', doubleround', function.comp_app, columnround_output,
  columnround.columnround_inv, columnround_input, columnround.columnround_inv', rowround.rowround_inv',
  doubleround_inv', rowround.rowround_inv, rowround.rowround_single_inv, prod.mk.eta, quarterround.quarterround_inv,
  columnround.columnround, rowround.rowround_single, quarterround.quarterround, quarterround.qr0_inv_is_inv,
  quarterround.qr1_inv_is_inv, quarterround.qr2_inv_is_inv, quarterround.qr3_inv_is_inv],
end

/-- Two morphism `doubleround_10` and `doubleround_10⁻¹` are isomorphic if:
- `doubleround_10 ∘ doubleround_10⁻¹ = 𝟙 doubleround_10`, and
- `doubleround_10⁻¹ ∘ doubleround_10 = 𝟙 doubleround_10⁻¹`.
-/
@[simp] theorem doubleround_10_is_isomorphic (seq : matrixType) :
  (doubleround_10_inv ∘ doubleround_10) seq = id_doubleround_10 seq ∧
  (doubleround_10 ∘ doubleround_10_inv) seq = id_doubleround_10_inv seq :=
begin
  simp only [isomorphism_left, eq_self_iff_true, isomorphism_right, and_self],
end


/-!
## Core and hash definitions
-/
/-- Do addition modulo 2^32 of the reduced input and the doubleround of the reduced input. -/
@[simp] def core (X : matrixType) : matrixType := mod_matrix (doubleround_10 X) X

/-- Do the hash. -/
def hash (X : matrix64Type) : matrix64Type := aument (core (reduce X))

/-! ## Category theory

-/

namespace category

universes u

/- A `MAT` is 16 numbers. -/
variables {MAT : Type u} [category (MAT)]

/-- `X` is an element of the category. `X ⟶ X` is also a category. -/
variables (X : MAT) [category (X ⟶ X)]

/-- These are all morphisms from `X` to `X`. -/
variables rowround columnround rowround_inv columnround_inv : X ⟶ X

/- Notation for inverse. -/
local notation `rowround⁻¹` := rowround_inv

/- Notation for inverse. -/
local notation `columnround⁻¹` := columnround_inv

def doubleround10 := category.doubleround X rowround columnround ≫ 
  category.doubleround X rowround columnround ≫ 
  category.doubleround X rowround columnround ≫
  category.doubleround X rowround columnround ≫
  category.doubleround X rowround columnround ≫
  category.doubleround X rowround columnround ≫
  category.doubleround X rowround columnround ≫
  category.doubleround X rowround columnround ≫
  category.doubleround X rowround columnround ≫
  category.doubleround X rowround columnround 

def doubleround10_inv := category.doubleround_inv X columnround⁻¹ rowround⁻¹ ≫
  category.doubleround_inv X columnround⁻¹ rowround⁻¹ ≫
  category.doubleround_inv X columnround⁻¹ rowround⁻¹ ≫
  category.doubleround_inv X columnround⁻¹ rowround⁻¹ ≫
  category.doubleround_inv X columnround⁻¹ rowround⁻¹ ≫
  category.doubleround_inv X columnround⁻¹ rowround⁻¹ ≫
  category.doubleround_inv X columnround⁻¹ rowround⁻¹ ≫
  category.doubleround_inv X columnround⁻¹ rowround⁻¹ ≫
  category.doubleround_inv X columnround⁻¹ rowround⁻¹ ≫
  category.doubleround_inv X columnround⁻¹ rowround⁻¹

/- Notation for inverse. -/
local notation `doubleround10⁻¹` := doubleround10_inv

/-- There is an isomoprhism between `doubleround10` and `doubleround10⁻¹`. -/
variable I : doubleround10 X rowround columnround ≅ doubleround10⁻¹ X columnround_inv rowround_inv

/-- It is easy to see that `doubleround10⁻¹` after `doubleround10` produces the original object. -/
lemma doubleround10_inv_is_inverse_of_doubleround10 : I.hom ≫ I.inv = 𝟙 (doubleround10 X rowround columnround) :=
begin
  exact I.hom_inv_id',
end

variable mod_matrix : (MAT → (X ⟶ X)) → MAT

def core := mod_matrix (λ a : MAT, doubleround10 X rowround columnround)

lemma no_inverse : ¬ ∃ core_inv : MAT → MAT, core_inv (core X rowround columnround mod_matrix) = X :=
begin
  sorry,
end

end category

/-!
## Isomorphism of the core function do not exists

### TODO:

We know `mod_matrix⁻¹` is not a function (proved in `inv_of_mod_matrix_is_not_a_function`) but
i was not able to use that for formalization of `core⁻¹` yet.
-/

/-- The identity of a `core` morphism given a sequence is the sequence. -/
@[simp] def id_core (seq : matrixType) := seq

/-- The identity of a `core⁻¹` morphism given a sequence is the sequence. -/
@[simp] def id_core_inv (seq : matrixType) := seq

/-- No isomrphism exists as none of the conditions apply :
- `core⁻¹ ∘ core = 𝟙 core` = false
- `core ∘ core⁻¹ = 𝟙 core` = false
-/
@[simp] lemma no_isomorphism_core (seq : matrixType) : ¬ ∃ (core_inv1 core_inv2 : matrixType → matrixType),
  (core_inv1 ∘ core) seq = id_core seq ∧ (core ∘ core_inv2) seq = id_core seq :=
begin
  sorry,
end

/-!
  ## Invariance

  Theorem `doubleround_is_left_invariant` is independent of the number of rounds performed.

  `doubleround_10_is_left_invariant` is created proving the invariance for 10 rounds.
-/

-- Have a random number that we will use in some of the proofs below.
variable A : bitvec params.word_len

/-- `doubleround_10` is left invariant. -/
@[simp] theorem doubleround_10_is_left_invariant : doubleround_10 (doubleround.input A) = doubleround.input A :=
begin
  unfold doubleround_10,
  simp only [doubleround_is_left_invariant],
end


/-!
  ## Linear transformation

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

/-!
  ## Collissions

  https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

  Theorem 6 of the paper.
-/

-- the maximum value Z can be.
variable z : fin (bitvec.to_nat two_31)

/-- Z < 2³¹ -/
def Z : bitvec word_len := bitvec.of_nat word_len z.val
/-- Z′ = Z + 2³¹ -/
def Z' : bitvec word_len := (Z z) MOD two_31

/-- An hypotetical collission output of the `core` function where the inputs are:
  
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

/-- Two different specially crafted inputs produces the same output. -/
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

/-- A random input matrix. -/
def Input : matrixType := (
  (a₀, a₁, a₂, a₃),
  (a₄, a₅, a₆, a₇),
  (a₈, a₉, a₁₀, a₁₁),
  (a₁₂, a₁₃, a₁₄, a₁₅)
)

/-- A matrix consisting of all 2³¹ (0x80000000) bit vectors. -/
def Delta : matrixType :=
  (
    (0x80000000, 0x80000000, 0x80000000, 0x80000000),
    (0x80000000, 0x80000000, 0x80000000, 0x80000000),
    (0x80000000, 0x80000000, 0x80000000, 0x80000000),
    (0x80000000, 0x80000000, 0x80000000, 0x80000000)
  )

/-- A matrix where all its elements are zero. -/
def Zero : matrixType :=
  (
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)
  )

/-- `core` of delta is always zero. -/
lemma core_of_delta: core Delta = Zero := rfl

/-- `core` of zero is always zero. -/
lemma core_of_zero: core Zero = Zero := rfl

--
local notation `INPUT` := Input a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅

/--
  The specially crafted input based in some random input produces the same result as the original input. 

  ### TODO:

  Prove:

  - `quarterrround` conserves the difference. ✓
  - `rowround` conserves the difference.
  - `columnround` conserves the difference.
  - `doubleround` conserves the difference.
  - `doubleround`_10 conserves the difference.
  - `mod_matrix` cancel the difference.

  https://crypto.stackexchange.com/questions/26437/collision-or-second-preimage-for-the-chacha-core
  https://www.iacr.org/archive/fse2008/50860470/50860470.pdf
-/
lemma differences_cancel : mod_matrix (doubleround_10 (xor_matrix INPUT Delta)) (xor_matrix INPUT Delta) = 
  mod_matrix (doubleround_10 INPUT) INPUT :=
begin
  unfold doubleround_10,
  sorry,
end

/--
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
