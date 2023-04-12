import quarterround

import category_theory.category.basic

open quarterround

open category_theory

namespace quarterround_examples

variable [category (bitvec params.word_len)]

/-!
  # Examples from the spec.

  https://cr.yp.to/snuffle/spec.pdf
-/

/-!
## Example 1 : 

> quarterround(0x00000000, 0x00000000, 0x00000000, 0x00000000) = (0x00000000, 0x00000000, 0x00000000, 0x00000000)
-/

/-- `z1 (0, 0, 0, 0) = 0` -/
lemma example1_z1 : z1 (0, 0, 0, 0) 0 = 0 := by rw z1_zero 

/-- `z2 (0, 0, 0, 0) = 0` -/
lemma example1_z2 : z2 (0, 0, 0, 0) 0 = 0 := by rw z2_zero 

/-- `z3 (0, 0, 0, 0) = 0` -/
lemma example1_z3 : z3 (0, 0, 0, 0) 0 = 0 := by rw z3_zero 

/-- `z0 (0, 0, 0, 0) = 0` -/
lemma example1_z0 : z0 (0, 0, 0, 0) 0 = 0 := by rw z0_zero 

/-- `quarterround (0, 0, 0, 0) = (0, 0, 0, 0)` -/
lemma example1_quarterround : quarterround (0, 0, 0, 0) = (0, 0, 0, 0) := 
begin
  norm_num,
end

/-!
## Example 2 : 

> quarterround(0x00000001, 0x00000000, 0x00000000, 0x00000000) = (0x08008145, 0x00000080, 0x00010200, 0x20500000)
-/

universe u

@[simp] def as_fun {α β : Type u} (h : α ⟶ β) : α → β := h
@[simp] lemma as_hom_remove {α β : Type u} (h : α ⟶ β): as_hom h = as_fun h := by refl

attribute [simp] bitvec.shl bitvec.ushr bitvec.fill_shr bitvec.xor bitvec.of_nat bitvec.or

/-- `z1 (1, 0, 0, 0) = 128` -/
lemma example2_z1 : z1 (1, 0, 0, 0) 0 = 128 := 
begin
  simp,
  dunfold params.word_len,
  norm_num,
  refl,
end

/-- `z2 (1, 0, 0, 0) = 66048` -/
lemma example2_z2 : z2 (1, 0, 0, 0) 128 = 66048 := 
begin
  simp,
  dunfold params.word_len,
  norm_num,
  refl,
end

/-- `z0 (1, 0, 0, 0) = 542113792` -/
lemma example2_z3 : z3 (1, 0, 0, 0) 128 = 542113792 := 
begin
  simp,
  dunfold params.word_len,
  norm_num,
  refl,
end

/-- `z0 (1, 0, 0, 0) = 134250821` -/
lemma example2_z0 : z0 (1, 0, 0, 0) 542113792 = 134250821 := 
begin
  simp,
  dunfold params.word_len,
  norm_num,
  refl,
end

/-- `quarterround (1, 0, 0, 0) = (134250821, 128, 66048, 542113792)` -/
lemma example2_quarterround : quarterround (1, 0, 0, 0) = (134250821, 128, 66048, 542113792) :=
  by rw [quarterround, example2_z1, example2_z2, example2_z3, example2_z0]

/-!
## Example 3 : 

> quarterround(0x00000000, 0x00000001, 0x00000000, 0x00000000) = (0x88000100, 0x00000001, 0x00000200, 0x00402000)

-/

/-- `z1 (0, 1, 0, 0) = 1` -/
lemma example3_z1 : z1 (0, 1, 0, 0) 0 = 1 := 
begin
  simp,
  dunfold params.word_len,
  norm_num,
  refl,
end

/-- `z2 (0, 1, 0, 0) = 512` -/
lemma example3_z2 : z2 (0, 1, 0, 0) 1 = 512 := 
begin
  simp,
  dunfold params.word_len,
  norm_num,
  refl,
end

/-- `z3 (0, 1, 0, 0) = 4202496` -/
lemma example3_z3 : z3 (0, 1, 0, 0) 1 = 4202496 := 
begin
  simp,
  dunfold params.word_len,
  norm_num,
  refl,
end

/-- `z0 (0, 1, 0, 0) = 2281701632` -/
lemma example3_z0 : z0 (0, 1, 0, 0) 4202496 = 2281701632 := 
begin
  simp,
  dunfold params.word_len,
  norm_num,
  refl,
end

/-- `quarterround (0, 1, 0, 0) = (2281701632, 1, 512, 4202496)` -/
lemma example3_quarterround : quarterround (0, 1, 0, 0) = (2281701632, 1, 512, 4202496) :=
  by rw [quarterround, example3_z1, example3_z2, example3_z3, example3_z0]


/-
TODO: 
- Add the rest of the spec examples.
- Add inverse examples.
-/


end quarterround_examples
