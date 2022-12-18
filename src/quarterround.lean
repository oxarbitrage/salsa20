/-
  The `quarterround` function, its inverse and the invariance theorem.
-/
import operations
import utils

open operations
open params
open utils

namespace quarterround

-- `a` `b` `c` and `d` are random elements of the 4 words starting sequence
variables a b c d : bitvec word_len
-- a new set of random elements that might or might not be the same than the ones above
variables a' b' c' d' : bitvec word_len

-- Quarter round definitions

-- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7)
def qr1 (a b c d : bitvec word_len) := b OP (OP_RHS a d 7)
-- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9)
def qr2 (a b c d : bitvec word_len) := c OP (OP_RHS (qr1 a b c d) a 9)
-- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13)
def qr3 (a b c d : bitvec word_len) := d OP (OP_RHS (qr2 a b c d) (qr1 a b c d) 13)
-- z₀ = y₀ ⊕ ((z₃ + z₂) <<< 18)
def qr0 (a b c d : bitvec word_len) := a OP (OP_RHS (qr3 a b c d) (qr2 a b c d) 18)

-- Puts the 4 elements that form a quarterround all together
@[simp] def quarterround (seq : vecType) : vecType :=
  (
    qr0 seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
    qr1 seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
    qr2 seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
    qr3 seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd
  )

-- Quarter round inverse definitions

-- y₀ = z₀ ⊕ ((z₃ + z₂) <<< 18)
def qr0_inv (a' b' c' d' : bitvec word_len) := a' OP (operation_rhs d' c' 18)
-- y₃ = z₃ ⊕ ((z₂ + z₁) <<< 13)
def qr3_inv (a' b' c' d' : bitvec word_len) := d' OP (operation_rhs c' b' 13)
-- y₂ = z₂ ⊕ ((z₁ + y₀) <<< 9)
def qr2_inv (a' b' c' d' : bitvec word_len) := c' OP (operation_rhs b' (qr0_inv a' b' c' d')  9)
-- y₁ = z₁ ⊕ ((y₀ + y₃) <<< 7)
def qr1_inv (a' b' c' d' : bitvec word_len) := b' OP (operation_rhs (qr0_inv a' b' c' d') (qr3_inv a' b' c' d') 7)

-- Puts the 4 elements that forms a quarterround inverse all together.
@[simp] def quarterround_inv (seq : vecType) := (
  qr0_inv seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
  qr1_inv seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
  qr2_inv seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
  qr3_inv seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd
)

-- The quarterround operation is fully invertible.
@[simp] lemma quarterround_is_invertible : 
  qr0_inv (qr0 a b c d) (qr1 a b c d) (qr2 a b c d) (qr3 a b c d) = a ∧
  qr3_inv (qr0 a b c d) (qr1 a b c d) (qr2 a b c d) (qr3 a b c d) = d ∧ 
  qr2_inv (qr0 a b c d) (qr1 a b c d) (qr2 a b c d) (qr3 a b c d) = c ∧
  qr1_inv (qr0 a b c d) (qr1 a b c d) (qr2 a b c d) (qr3 a b c d) = b
:=
begin
  split,
  {
    rw [qr0, qr1, qr2, qr3, qr0_inv],
    unfold operation,
    simp only [xor_assoc, xor_inv, xor_zero],
  },
  {
    split,
    {
      rw [qr0, qr3, qr2, qr1, qr3_inv],
      unfold operation,
      simp only [xor_assoc, xor_inv, xor_zero],
    },
    {
      split,
      {
        rw [qr0, qr3, qr2, qr1, qr2_inv, qr0_inv],
        unfold operation,
        simp only [xor_assoc, xor_assoc, xor_inv, xor_zero, xor_inv, xor_zero],
      },

      rw [qr0, qr3, qr2, qr1, qr1_inv, qr0_inv, qr3_inv],
      unfold operation,
      simp only [xor_assoc, xor_assoc, xor_inv, xor_zero, xor_assoc, xor_inv, xor_zero, xor_inv, xor_zero],
    }
  }
end

-- Inverse of quarterround exists.
@[simp] lemma inverse_exists : ∀ (a b c d : bitvec word_len), ∃ (a' b' c' d' : bitvec word_len), 
  quarterround_inv (a', b', c', d') = (a, b, c, d) :=
begin
  intros h1 h2 h3 h4,
  use (qr0 h1 h2 h3 h4),
  use (qr1 h1 h2 h3 h4), 
  use (qr2 h1 h2 h3 h4),
  use (qr3 h1 h2 h3 h4),
  unfold quarterround_inv,
  rw [qr0, qr1, qr2, qr3, qr0_inv, qr1_inv, qr2_inv, qr3_inv, qr1, qr2, qr0_inv, qr1],
  unfold operation,
  simp only [xor_assoc, xor_inv, xor_zero],
end

@[simp] lemma qr0_is_inv : 
  qr0_inv (qr0 a b c d) (qr1 a b c d) (qr2 a b c d) (qr3 a b c d) = a :=
begin
    rw [qr0, qr1, qr2, qr3, qr0_inv],
    unfold operation,
    simp only [xor_assoc, xor_inv, xor_zero],
end

@[simp] lemma qr1_is_inv : 
  qr1_inv (qr0 a b c d) (qr1 a b c d) (qr2 a b c d) (qr3 a b c d) = b :=
begin  
    rw [qr0, qr1, qr2, qr3, qr1_inv, qr0_inv, qr2, qr1, qr3_inv],
    unfold operation,
    simp only [xor_assoc, xor_assoc, xor_assoc, xor_inv, xor_inv, xor_zero, xor_zero, xor_inv, xor_zero]
end

@[simp] lemma qr2_is_inv : 
  qr2_inv (qr0 a b c d) (qr1 a b c d) (qr2 a b c d) (qr3 a b c d) = c :=
begin
    rw [qr0, qr1, qr2, qr3, qr2_inv, qr0_inv, qr2, qr1],
    unfold operation,
    simp only [xor_assoc, xor_assoc, xor_inv, xor_zero, xor_inv, xor_zero],
end

@[simp] lemma qr3_is_inv : 
  qr3_inv (qr0 a b c d) (qr1 a b c d) (qr2 a b c d) (qr3 a b c d) = d :=
begin
    rw [qr0, qr1, qr2, qr3, qr3_inv, qr2, qr1],
    unfold operation,
    simp only [xor_assoc, xor_inv, xor_zero],
end

/-
  Left invariance of the quarterround function: https://www.iacr.org/archive/fse2008/50860470/50860470.pdf

  We prove each single `qr{0..3}` is invariant to the left and derive that the full quarterround
  function is left invariant.

  Theorem 1 of the paper.
-/

--
variable A : bitvec word_len

--
@[simp] lemma qr1_is_left_invariant : qr1 A (-A) A (-A) = -A := 
begin
  unfold qr1,
  unfold operation_rhs,
  unfold operation,
  simp only [mod_neg, zero_rotl, xor_zero],
end

--
@[simp] lemma qr2_is_left_invariant : qr2 A (-A) A (-A) = A := 
begin
  unfold qr2,
  rw qr1_is_left_invariant,
  unfold operation_rhs,
  unfold operation,
  simp only [neg_mod, zero_rotl, xor_zero],
end

--
@[simp] lemma qr3_is_left_invariant : qr3 A (-A) A (-A) = -A := 
begin
  unfold qr3,
  rw [qr1_is_left_invariant, qr2_is_left_invariant],
  
  unfold operation_rhs,
  unfold operation,
    
  rw [mod_neg, zero_rotl, xor_zero],
end

--
@[simp] lemma qr0_is_left_invariant : qr0 A (-A) A (-A) = A := 
begin
  unfold qr0,
  rw [qr3_is_left_invariant, qr2_is_left_invariant],
  
  unfold operation_rhs,
  unfold operation,
    
  simp only [neg_mod, zero_rotl, xor_zero],
end

--
@[simp] theorem quarterround_is_left_invariant : quarterround (A, -A, A, -A) = (A, -A, A, -A) :=
begin
  simp only [quarterround, qr0_is_left_invariant, qr1_is_left_invariant, qr2_is_left_invariant, qr3_is_left_invariant],
end


end quarterround
