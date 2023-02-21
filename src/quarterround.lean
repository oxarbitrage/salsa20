import operations
import utils

open operations
open params
open utils

namespace quarterround

/-!
  # Quarterround

  The `quarterround` function and its properties.
-/

/-- `a` `b` `c` and `d` are random elements of the 4 words starting sequence -/
variables a b c d : bitvec word_len
-- A new set of random elements that might or might not be the same than the ones above
variables a' b' c' d' : bitvec word_len

/-! ## Definitions -/

-- TODO: We are sending the 4 numbers `a` `b` `c` and `d` to each qr function but this is not
-- always needed (example: `qr1` will just use `b` `a` and `d`)

/-- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7) -/
def qr1 (a b c d : bitvec word_len) := b OP (OP_RHS a d 7)
/-- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9) -/
def qr2 (a b c d : bitvec word_len) := c OP (OP_RHS (qr1 a b c d) a 9)
/-- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13) -/
def qr3 (a b c d : bitvec word_len) := d OP (OP_RHS (qr2 a b c d) (qr1 a b c d) 13)
/-- z₀ = y₀ ⊕ ((z₃ + z₂) <<< 18) -/
def qr0 (a b c d : bitvec word_len) := a OP (OP_RHS (qr3 a b c d) (qr2 a b c d) 18)

/-- Given a sequence of 4 numbers `seq`, use the four equations above to get the quarterround
output, which is a 4 numbers sequence too. -/
@[simp] def quarterround (seq : vecType) : vecType :=
  (
    qr0 seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
    qr1 seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
    qr2 seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
    qr3 seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd
  )

/-! ## Quarterround zero lemmas -/

/-- `qr0` of 4 zeros is zero -/
@[simp] lemma qr0_zero : qr0 0 0 0 0 = 0 := by refl

/-- `qr1` of 4 zeros is zero -/
@[simp] lemma qr1_zero : qr1 0 0 0 0 = 0 := by refl

/-- `qr2` of 4 zeros is zero -/
@[simp] lemma qr2_zero : qr2 0 0 0 0 = 0 := by refl

/-- `qr3` of 4 zeros is zero -/
@[simp] lemma qr3_zero : qr3 0 0 0 0 = 0 := by refl

/-- `quarterround` of 4 zeros is a sequence of 4 zeros -/
@[simp] lemma quarterround_zero : quarterround (0, 0, 0, 0) = (0, 0, 0, 0) := by refl

/-! ## Inverse definitions -/

/-- y₀ = z₀ ⊕ ((z₃ + z₂) <<< 18) -/
def qr0_inv (a' b' c' d' : bitvec word_len) := a' OP (operation_rhs d' c' 18)
/-- y₃ = z₃ ⊕ ((z₂ + z₁) <<< 13) -/
def qr3_inv (a' b' c' d' : bitvec word_len) := d' OP (operation_rhs c' b' 13)
/-- y₂ = z₂ ⊕ ((z₁ + y₀) <<< 9) -/
def qr2_inv (a' b' c' d' : bitvec word_len) := c' OP (operation_rhs b' (qr0_inv a' b' c' d')  9)
/-- y₁ = z₁ ⊕ ((y₀ + y₃) <<< 7) -/
def qr1_inv (a' b' c' d' : bitvec word_len) := b' OP (operation_rhs (qr0_inv a' b' c' d') (qr3_inv a' b' c' d') 7)

/-- Puts the 4 elements that forms a quarterround inverse all together. -/
@[simp] def quarterround_inv (seq : vecType) := (
  qr0_inv seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
  qr1_inv seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
  qr2_inv seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd,
  qr3_inv seq.fst seq.snd.fst seq.snd.snd.fst seq.snd.snd.snd
)

/-! ## Inverse lemmas -/

/-- The quarterround operation is fully invertible. -/
@[simp] lemma quarterround_is_invertible (a b c d : bitvec word_len) : 
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

/-- Inverse of quarterround exists. -/
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

/-! ## Inverses of the `quarterround` and `quarterround_inv` individual pieces lemmas -/

/-- Inverse of `qr0` given the sequence `a, b, c, d` is `a`. -/
@[simp] lemma qr0_is_inv : 
  qr0_inv (qr0 a b c d) (qr1 a b c d) (qr2 a b c d) (qr3 a b c d) = a :=
begin
    rw [qr0, qr1, qr2, qr3, qr0_inv],
    unfold operation,
    simp only [xor_assoc, xor_inv, xor_zero],
end

/-- Inverse of `qr1` given the sequence `a, b, c, d` is `b`. -/
@[simp] lemma qr1_is_inv : 
  qr1_inv (qr0 a b c d) (qr1 a b c d) (qr2 a b c d) (qr3 a b c d) = b :=
begin  
    rw [qr0, qr1, qr2, qr3, qr1_inv, qr0_inv, qr2, qr1, qr3_inv],
    unfold operation,
    simp only [xor_assoc, xor_assoc, xor_assoc, xor_inv, xor_inv, xor_zero, xor_zero, xor_inv, xor_zero]
end

/-- Inverse of `qr2` given the sequence `a, b, c, d` is `c`. -/
@[simp] lemma qr2_is_inv : 
  qr2_inv (qr0 a b c d) (qr1 a b c d) (qr2 a b c d) (qr3 a b c d) = c :=
begin
    rw [qr0, qr1, qr2, qr3, qr2_inv, qr0_inv, qr2, qr1],
    unfold operation,
    simp only [xor_assoc, xor_assoc, xor_inv, xor_zero, xor_inv, xor_zero],
end

/-- Inverse of `qr3` given the sequence `a, b, c, d` is `d`. -/
@[simp] lemma qr3_is_inv : 
  qr3_inv (qr0 a b c d) (qr1 a b c d) (qr2 a b c d) (qr3 a b c d) = d :=
begin
    rw [qr0, qr1, qr2, qr3, qr3_inv, qr2, qr1],
    unfold operation,
    simp only [xor_assoc, xor_inv, xor_zero],
end

/-- Inverse of `qr0_inv` given the sequence `a, b, c, d` is `a`. -/
@[simp] lemma qr0_inv_is_inv :
  qr0 (qr0_inv a b c d) (qr1_inv a b c d) (qr2_inv a b c d) (qr3_inv a b c d) = a :=
begin
    rw [qr0_inv, qr1_inv, qr2_inv, qr3_inv, qr0],
    rw [qr3, qr0_inv, qr2, qr1],
    unfold operation,
    simp only [xor_assoc, xor_inv, xor_zero],
end

/-- Inverse of `qr1_inv` given the sequence `a, b, c, d` is `b`. -/
@[simp] lemma qr1_inv_is_inv :
  qr1 (qr0_inv a b c d) (qr1_inv a b c d) (qr2_inv a b c d) (qr3_inv a b c d) = b :=
begin
    rw [qr1, qr0_inv, qr1_inv, qr3_inv, qr0_inv],
    unfold operation,
    simp only [xor_assoc, xor_inv, xor_zero],
end

/-- Inverse of `qr2_inv` given the sequence `a, b, c, d` is `c`. -/
@[simp] lemma qr2_inv_is_inv :
  qr2 (qr0_inv a b c d) (qr1_inv a b c d) (qr2_inv a b c d) (qr3_inv a b c d) = c :=
begin
    rw [qr2, qr0_inv, qr1_inv, qr2_inv, qr3_inv, qr1, qr0_inv],
    unfold operation,
    simp only [xor_assoc, xor_inv, xor_zero],
end

/-- Inverse of `qr3_inv` given the sequence `a, b, c, d` is `d`. -/
@[simp] lemma qr3_inv_is_inv :
  qr3 (qr0_inv a b c d) (qr1_inv a b c d) (qr2_inv a b c d) (qr3_inv a b c d) = d :=
begin
    rw [qr3, qr0_inv, qr1_inv, qr2_inv, qr3_inv, qr1, qr0_inv, qr2, qr1],
    unfold operation,
    simp only [xor_assoc, xor_inv, xor_zero],
end

/-! ## Isomorphism -/

/-- The identity of a `quarterround` function given a sequence is the sequence. -/
@[simp] def id_quarterround (seq : vecType) := seq

/-- The identity of a `quarterround_inv` function given a sequence is the sequence. -/
@[simp] def id_quarterround_inv (seq : vecType) := seq

/-- Isomorphism condition 1 `f ∘ g = id_f` -/
@[simp] lemma isomorphism1 (seq : vecType) : (quarterround_inv ∘ quarterround) seq = id_quarterround seq :=
begin
  finish,
end

/-- Isomorphism condition 2 `g ∘ f = id_g` -/
@[simp] lemma isomorphism2 (seq : vecType) : (quarterround ∘ quarterround_inv) seq = id_quarterround_inv seq :=
begin
  finish,
end

/-- Two categories are isomrphic if `f ∘ g = id_f` and `g ∘ f = id_g`. -/
@[simp] theorem quarterround_is_isomorphic (seq : vecType) :
  (quarterround_inv ∘ quarterround) seq = id_quarterround seq ∧
  (quarterround ∘ quarterround_inv) seq = id_quarterround_inv seq :=
begin
  simp only [isomorphism1, eq_self_iff_true, isomorphism2, and_self],
end

/-!
  ## Invariance

  We prove each single `qr{0..3}` is invariant to the left
  when fed with a crafted sequence and by this derive that the
  full quarterround function is left invariant.

  Theorem 1 of the paper:

  > For any 32-bit value A, an input of the form (A −A A −A) is left invariant by the
  > quarterround function, where −A represents the only 32-bit integer satisfying A + (−A) = 0 (mod 232).

  https://www.iacr.org/archive/fse2008/50860470/50860470.pdf
-/

/-- `qr1` of `a, -a, a, -a` is `-a`. -/
@[simp] lemma qr1_is_left_invariant : qr1 a (-a) a (-a) = -a := 
begin
  unfold qr1,
  unfold operation_rhs,
  unfold operation,
  simp only [mod_neg, zero_rotl, xor_zero],
end

/-- `qr1` of `-a, a, -a, a` is `a`. -/
@[simp] lemma qr1_is_left_invariant' : qr1 (-a) a (-a) a = a := 
begin
  unfold qr1,
  unfold operation_rhs,
  unfold operation,
  simp only [neg_mod, zero_rotl, xor_zero],
end

/-- `qr2` of `a, -a, a, -a` is `a`. -/
@[simp] lemma qr2_is_left_invariant : qr2 a (-a) a (-a) = a := 
begin
  unfold qr2,
  rw qr1_is_left_invariant,
  unfold operation_rhs,
  unfold operation,
  simp only [neg_mod, zero_rotl, xor_zero],
end

/-- `qr2` of `-a, a, -a, a` is `-a`. -/
@[simp] lemma qr2_is_left_invariant' : qr2 (-a) a (-a) a = -a := 
begin
  unfold qr2,
  rw qr1_is_left_invariant',
  unfold operation_rhs,
  unfold operation,
  simp only [mod_neg, zero_rotl, xor_zero],
end

/-- `qr3` of `a, -a, a, -a` is `-a`. -/
@[simp] lemma qr3_is_left_invariant : qr3 a (-a) a (-a) = -a := 
begin
  unfold qr3,
  rw [qr1_is_left_invariant, qr2_is_left_invariant],
  
  unfold operation_rhs,
  unfold operation,
    
  simp only [mod_neg, zero_rotl, xor_zero],
end

/-- `qr3` of `-a, a, -a, a` is `a`. -/
@[simp] lemma qr3_is_left_invariant' : qr3 (-a) a (-a) a = a := 
begin
  unfold qr3,
  rw [qr1_is_left_invariant', qr2_is_left_invariant'],
  
  unfold operation_rhs,
  unfold operation,
    
  simp only [neg_mod, zero_rotl, xor_zero],
end

/-- `qr0` of `a, -a, a, -a` is `a`. -/
@[simp] lemma qr0_is_left_invariant : qr0 a (-a) a (-a) = a := 
begin
  unfold qr0,
  rw [qr3_is_left_invariant, qr2_is_left_invariant],
  
  unfold operation_rhs,
  unfold operation,
    
  simp only [neg_mod, zero_rotl, xor_zero],
end

/-- `qr0` of `-a, a, -a, a` is `-a`. -/
@[simp] lemma qr0_is_left_invariant' : qr0 (-a) a (-a) a = -a := 
begin
  unfold qr0,
  rw [qr3_is_left_invariant', qr2_is_left_invariant'],
  
  unfold operation_rhs,
  unfold operation,

  simp only [mod_neg, zero_rotl, xor_zero],
end

/-- The full `quarterround` function produces `a, -a, a, -a` when fed with `a, -a, a, -a` -/
@[simp] theorem quarterround_is_left_invariant : quarterround (a, -a, a, -a) = (a, -a, a, -a) :=
begin
  simp only [quarterround, qr0_is_left_invariant, qr1_is_left_invariant, qr2_is_left_invariant, qr3_is_left_invariant],
end

/-- The full `quarterround` function produces `-a, a, -a, a` when fed with `-a, a, -a, a` -/
@[simp] theorem quarterround_is_left_invariant' : quarterround (-a, a, -a, a) = (-a, a, -a, a) :=
begin
  simp only [quarterround, qr0_is_left_invariant', qr1_is_left_invariant', qr2_is_left_invariant', qr3_is_left_invariant'],
end

/-!
  ## Known variance of `quarterround` if diff of each input is 2³¹

  `quarterround` function will only flip the most significant bit when two set of elements is
  provided where the difference (or xor) between each element is 2³¹.
-/

-- Have 4 random vectors to be used as quarterround inputs.
variables m n o p : bitvec 32

/--
Define that x xor 2³¹ = flip msb bit only, leave the rest as is.

### TODO:

This could be proved.
-/
def craft (m : bitvec word_len) : bitvec word_len :=
  if m.head = ff then (bitvec.one 1).append m.tail else (bitvec.zero 1).append m.tail

/-- a shortcut to a vector head. -/
def msb (m : bitvec word_len) : bool := m.head
/-- a shortcut for a vector tail. -/
def rest (m : bitvec word_len) : bitvec (word_len - 1) := m.tail
/--
Lets suppose the msb of any uncrafted bitvec that we will send to quarterround is always `ff`.

### TODO:

This does not need to be the case, everything should work in a very similar way if the head is 1
as it will gets flipped to 0 but we do this for simplicity by now.
Basically by restricting the msb to be 0 we are saying that the number is smaller than 2^31. -/
constant h_msb : m.head = ff

-- Define a type notation which is an abstract function that can represent `qr0` `qr1` `qr2` `qr3`
local notation `qrX` := bitvec word_len → bitvec word_len → bitvec word_len → bitvec word_len → bitvec word_len

/--
Assumes that any qrX function that is feeded with crafted numbers will result in a head of 1
and the rest or tail equal to the tail of the uncrafted number.

### TODO:

This needs to be proved.
-/
constant qrX_crafted (f : qrX) :
  f (craft m) (craft n) (craft o) (craft p) = (bitvec.one 1).append (f m n o p).tail

/--
A random bitvector of size `word_len - 1` representing the tail of a bitvector of size `word_len`.
-/
variable tail_placeholder : bitvec (word_len - 1)
/--
The head (msb) of anything that starts with a 1 and then stuff is appended should be always 1.

### TODO:

Should be easy to prove ? -/
constant msb_of_one_append : vector.head ((bitvec.one 1).append tail_placeholder) = tt
/-- The rest of the bitvector where 1 gets appended with the tail of the bitvector is the tail of the bitvector.

### TODO:

should be easy to prove ?
-/
constant rest_of_one_append : vector.tail m = ((bitvec.one 1).append (m).tail).tail

/-- For any individual qrX function, when feeded with crafted data the difference is carried. -/
lemma qrX_difference_is_carried (f : qrX) :
  msb (f m n o p) ≠ msb (f (craft m) (craft n) (craft o) (craft p)) ∧
    rest (f m n o p) = rest (f (craft m) (craft n) (craft o) (craft p)) :=
begin
  rw qrX_crafted m n o p f,
  split,
  {
    unfold msb,
    rw h_msb,
    rw msb_of_one_append (vector.tail (f m n o p)),
    finish,
  },
  {
    unfold rest,
    rw ← rest_of_one_append,
  }
end

/-- `qr1` difference is carried when fed with crafted data. -/
lemma qr1_difference_is_carried :
  msb (qr1 m n o p) ≠ msb (qr1 (craft m) (craft n) (craft o) (craft p)) ∧
    rest (qr1 m n o p) = rest (qr1 (craft m) (craft n) (craft o) (craft p)) :=
by apply qrX_difference_is_carried m n o p qr1

/-- `qr2` difference is carried when fed with crafted data. -/
lemma qr2_difference_is_carried :
  msb (qr2 m n o p) ≠ msb (qr2 (craft m) (craft n) (craft o) (craft p)) ∧
    rest (qr2 m n o p) = rest (qr2 (craft m) (craft n) (craft o) (craft p)) :=
by apply qrX_difference_is_carried m n o p qr2

/-- `qr3` difference is carried when fed with crafted data. -/
lemma qr3_difference_is_carried :
  msb (qr3 m n o p) ≠ msb (qr3 (craft m) (craft n) (craft o) (craft p)) ∧
    rest (qr3 m n o p) = rest (qr3 (craft m) (craft n) (craft o) (craft p)) :=
by apply qrX_difference_is_carried m n o p qr3

/-- `qr0` difference is carried when fed with crafted data. -/
lemma qr0_difference_is_carried :
  msb (qr0 m n o p) ≠ msb (qr0 (craft m) (craft n) (craft o) (craft p)) ∧
    rest (qr0 m n o p) = rest (qr0 (craft m) (craft n) (craft o) (craft p)) :=
by apply qrX_difference_is_carried m n o p qr0

/-- Full `quarterround` carries the difference when fed with crafted data. -/
lemma quarterround_difference_is_carried :
  -- z0 only changes in the msb
  (msb (quarterround (m, n, o, p)).fst ≠ msb (quarterround ((craft m), (craft n), (craft o), (craft p))).fst ∧
    rest (quarterround (m, n, o, p)).fst = rest (quarterround ((craft m), (craft n), (craft o), (craft p))).fst) ∧
  -- z1 only changes in the msb
  (msb (quarterround (m, n, o, p)).snd.fst ≠ msb (quarterround ((craft m), (craft n), (craft o), (craft p))).snd.fst ∧
    rest (quarterround (m, n, o, p)).snd.fst = rest (quarterround ((craft m), (craft n), (craft o), (craft p))).snd.fst) ∧
  -- z2 only changes in the msb
  (msb (quarterround (m, n, o, p)).snd.snd.fst ≠ msb (quarterround ((craft m), (craft n), (craft o), (craft p))).snd.snd.fst ∧
    rest (quarterround (m, n, o, p)).snd.snd.fst = rest (quarterround ((craft m), (craft n), (craft o), (craft p))).snd.snd.fst) ∧
  -- z3 only changes in the msb
  (msb (quarterround (m, n, o, p)).snd.snd.snd ≠ msb (quarterround ((craft m), (craft n), (craft o), (craft p))).snd.snd.snd ∧
    rest (quarterround (m, n, o, p)).snd.snd.snd = rest (quarterround ((craft m), (craft n), (craft o), (craft p))).snd.snd.snd) :=
begin
  apply and.intro,
  apply qr0_difference_is_carried,
  apply and.intro,
  apply qr1_difference_is_carried,
  tauto,
  apply and.intro,
  apply qr2_difference_is_carried,
  apply qr3_difference_is_carried,
end


end quarterround
