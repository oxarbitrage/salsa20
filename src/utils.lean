import operations
import params
import littleendian

open operations
open params
open littleendian

namespace utils

/-!
  # Utilities
-/


-- A random input matrix to be used as `rowround` and `columnround` inputs. 
variable M : matrixType

/--
  Prepare the `rowround` matrix input.

  Any `rowround` input matrix is in the form:

  (y₀, y₁, y₂, y₃)
  (y₄, y₅, y₆, y₇)
  (y₈, y₉, y₁₀, y₁₁)
  (y₁₂, y₁₃, y₁₄, y₁₅)

  But we need this to be converted to:

  (y₀, y₁, y₂, y₃)
  (y₅, y₆, y₇, y₄)
  (y₁₀, y₁₁, y₈, y₉)
  (y₁₅, y₁₂, y₁₃, y₁₄)  
-/
@[simp] def rowround_input : matrixType :=
  (
    ((M.fst).fst,                 (M.fst).snd.fst,              (M.fst).snd.snd.fst,      (M.fst).snd.snd.snd),
    ((M.snd.fst).snd.fst,         (M.snd.fst).snd.snd.fst,      (M.snd.fst).snd.snd.snd,  (M.snd.fst).fst),
    ((M.snd.snd.fst).snd.snd.fst, (M.snd.snd.fst).snd.snd.snd,  (M.snd.snd.fst).fst,      (M.snd.snd.fst).snd.fst),
    ((M.snd.snd.snd).snd.snd.snd, (M.snd.snd.snd).fst,          (M.snd.snd.snd).snd.fst,  (M.snd.snd.snd).snd.snd.fst)
  )

/--
  Prepare the `rowround` matrix output.

  Any `rowround` output matrix is of the form:

  (z₀, z₁, z₂, z₃)
  (z₅, z₆, z₇, z₄)
  (z₁₀, z₁₁, z₈, z₉)
  (z₁₅, z₁₂, z₁₃, z₁₄)  

  But we need this to be converted to:

  (z₀, z₁, z₂, z₃)
  (z₄, z₅, z₆, z₇)
  (z₈, z₉, z₁₀, z₁₁)
  (z₁₂, z₁₃, z₁₄, z₁₅)
-/
@[simp] def rowround_output : matrixType :=
  (
    ((M.fst).fst,                 (M.fst).snd.fst,              (M.fst).snd.snd.fst,          (M.fst).snd.snd.snd),
    ((M.snd.fst).snd.snd.snd,     (M.snd.fst).fst,              (M.snd.fst).snd.fst,          (M.snd.fst).snd.snd.fst),
    ((M.snd.snd.fst).snd.snd.fst, (M.snd.snd.fst).snd.snd.snd,  (M.snd.snd.fst).fst,          (M.snd.snd.fst).snd.fst),
    ((M.snd.snd.snd).snd.fst,     (M.snd.snd.snd).snd.snd.fst,  (M.snd.snd.snd).snd.snd.snd,  (M.snd.snd.snd).fst)
  )

/-- The `rowround_output` function is the inverse of the `rowround_input` function. -/
lemma rowround_output_is_inv_of_input : rowround_output (rowround_input M) = M :=
begin
  unfold rowround_input,
  unfold rowround_output,
  simp only [prod.mk.eta],
end

/--
  Prepare the `columnround` matrix input.

  Any `columnround` input matrix is in the form:

  (x₀, x₁, x₂, x₃)
  (x₄, x₅, x₆, x₇)
  (x₈, x₉, x₁₀, x₁₁)
  (x₁₂, x₁₃, x₁₄, x₁₅)

  But we need this to be converted to:

  (x₀, x₄, x₈, x₁₂)
  (x₅, x₉, x₁₃, x₁)
  (x₁₀, x₁₄, x₂, x₆)
  (x₁₅, x₃, x₇, x₁₁)
-/
@[simp] def columnround_input : matrixType :=
  (
    ((M.fst).fst,                 (M.snd.fst).fst,              (M.snd.snd.fst).fst,      (M.snd.snd.snd).fst),
    ((M.snd.fst).snd.fst,         (M.snd.snd.fst).snd.fst,      (M.snd.snd.snd).snd.fst,  (M.fst).snd.fst),
    ((M.snd.snd.fst).snd.snd.fst, (M.snd.snd.snd).snd.snd.fst,  (M.fst).snd.snd.fst,      (M.snd.fst).snd.snd.fst),
    ((M.snd.snd.snd).snd.snd.snd, (M.fst).snd.snd.snd,          (M.snd.fst).snd.snd.snd,  (M.snd.snd.fst).snd.snd.snd)
  )

/--
  Prepare the `columnround` matrix output.

  Any `columnround` output matrix is in the form:

  (y₀, y₄, y₈, y₁₂)
  (y₅, y₉, y₁₃, y₁)
  (y₁₀, y₁₄, y₂, y₆)
  (y₁₅, y₃, y₇, y₁₁)

  But we need this to be converted to:

  (y₀, y₁, y₂, y₃)
  (y₄, y₅, y₆, y₇)
  (y₈, y₉, y₁₀, y₁₁)
  (y₁₂, y₁₃, y₁₄, y₁₅)  
-/
@[simp] def columnround_output : matrixType :=
  (
    ((M.fst).fst,         (M.snd.fst).snd.snd.snd,  (M.snd.snd.fst).snd.snd.fst,  (M.snd.snd.snd).snd.fst),
    ((M.fst).snd.fst,     (M.snd.fst).fst,          (M.snd.snd.fst).snd.snd.snd,  (M.snd.snd.snd).snd.snd.fst),
    ((M.fst).snd.snd.fst, (M.snd.fst).snd.fst,      (M.snd.snd.fst).fst,          (M.snd.snd.snd).snd.snd.snd),
    ((M.fst).snd.snd.snd, (M.snd.fst).snd.snd.fst,  (M.snd.snd.fst).snd.fst,      (M.snd.snd.snd).fst)
  )

/-- The `columnround_output` function is the inverse of the `columnround_input` function. -/
lemma columnround_output_is_inv_of_input : columnround_output (columnround_input M) = M :=
begin
  unfold columnround_input,
  unfold columnround_output,
  simp only [prod.mk.eta],
end

-- A random input 64 bytes matrix that we can reduce using `littleendian` function.
variable X : matrix64Type

-- A random input 16 bytes matrix that we can aument using the `littleendian_inv` function.
variable Y : matrixType

/-- Reduce the 64 bytes sequence to a 16 bytes one by using little endian. -/
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

/-- Aument a given 16 bytes sequence to a 64 bytes one using `littleenedian_inv`. -/
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

/-- 
Modular 2^32 addition of 4x4 matrices by doing Aᵢⱼ + Bᵢⱼ

The `MOD` operation (modulo 2^32 addition) is the key to make the salsa20 hash function irreversible.
Everything is reversible except for this addition.
-/
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

/-- We define the xor of a matrix to be the xor of each individual bitvector of matrix A and matrix B. -/
def xor_matrix (A B : matrixType) : matrixType := (
  (
    A.fst.fst          XOR B.fst.fst,
    A.fst.snd.fst      XOR B.fst.snd.fst,
    A.fst.snd.snd.fst  XOR B.fst.snd.snd.fst,
    A.fst.snd.snd.snd  XOR B.fst.snd.snd.snd
  ),
  (
    A.snd.fst.fst          XOR B.snd.fst.fst,
    A.snd.fst.snd.fst      XOR B.snd.fst.snd.fst,
    A.snd.fst.snd.snd.fst  XOR B.snd.fst.snd.snd.fst,
    A.snd.fst.snd.snd.snd  XOR B.snd.fst.snd.snd.snd
  ),
  (
    A.snd.snd.fst.fst          XOR B.snd.snd.fst.fst,
    A.snd.snd.fst.snd.fst      XOR B.snd.snd.fst.snd.fst,
    A.snd.snd.fst.snd.snd.fst  XOR B.snd.snd.fst.snd.snd.fst,
    A.snd.snd.fst.snd.snd.snd  XOR B.snd.snd.fst.snd.snd.snd
  ),
  (
    A.snd.snd.snd.fst          XOR B.snd.snd.snd.fst,
    A.snd.snd.snd.snd.fst      XOR B.snd.snd.snd.snd.fst,
    A.snd.snd.snd.snd.snd.fst  XOR B.snd.snd.snd.snd.snd.fst,
    A.snd.snd.snd.snd.snd.snd  XOR B.snd.snd.snd.snd.snd.snd
  )
)

-- Have 16 random numbers.
variables a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ : bitvec word_len

/-- Distribute 2 * Matrix. -/
@[simp] lemma matrix_distribute_two :
  2 * ((a₀, a₁, a₂, a₃), (a₄, a₅, a₆, a₇), (a₈, a₉, a₁₀, a₁₁), (a₁₂, a₁₃, a₁₄, a₁₅)) =
  (
    (2 * a₀, 2 * a₁, 2 * a₂, 2 * a₃),
    (2 * a₄, 2 * a₅, 2 * a₆, 2 * a₇),
    (2 * a₈, 2 * a₉, 2 * a₁₀, 2 * a₁₁),
    (2 * a₁₂, 2 * a₁₃, 2 * a₁₄, 2 * a₁₅)
  ) := rfl

/-- The MOD sum of two equal matrices X is 2 times X. -/
@[simp] lemma mod_matrix_double : mod_matrix M M = 2 * M :=
begin
  unfold mod_matrix,
  simp only [mod_self],

  rw ← matrix_distribute_two
    M.fst.fst         M.fst.snd.fst         M.fst.snd.snd.fst         M.fst.snd.snd.snd
    M.snd.fst.fst     M.snd.fst.snd.fst     M.snd.fst.snd.snd.fst     M.snd.fst.snd.snd.snd
    M.snd.snd.fst.fst M.snd.snd.fst.snd.fst M.snd.snd.fst.snd.snd.fst M.snd.snd.fst.snd.snd.snd
    M.snd.snd.snd.fst M.snd.snd.snd.snd.fst M.snd.snd.snd.snd.snd.fst M.snd.snd.snd.snd.snd.snd,
  refl,
end


end utils
