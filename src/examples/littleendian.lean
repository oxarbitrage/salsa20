import littleendian
import category_theory.category.basic
import data.nat.digits

open littleendian

open category_theory
open nat

namespace littleendian_examples

variables [category (bitvec params.word_len)] [semiring (list ℕ)]

/- 
  Examples from the spec.

  https://cr.yp.to/snuffle/spec.pdf

  ## Straight examples
-/

/-- `littleendian(0, 0, 0, 0) = 0x00000000` -/
lemma example1 : littleendian [0, 0, 0, 0] = 0 := 
begin
  unfold littleendian,
  unfold of_digits,
  norm_num,
end

/-- `littleendian(86, 75, 30, 9) = 0x091e4b56` -/
lemma example2 : littleendian [86, 75, 30, 9] = 0x091e4b56 := 
begin
  unfold littleendian,
  unfold of_digits,
  norm_num,  
end

/-- `littleendian(255, 255, 255, 250) = 0xfaffffff` -/
lemma example3 : littleendian [255, 255, 255, 250] = 0xfaffffff := 
begin
  unfold littleendian,
  unfold of_digits,
  norm_num,
end

/- 
  ## Inverse examples 
-/

/-- `littleendian⁻¹ 0 = (0, 0, 0, 0)` -/
lemma example1_inv : littleendian_inv [0] = list.nil := 
begin
  unfold littleendian_inv,
  norm_num,
end

/-- `littleendian⁻¹ 152980310 = (86, 75, 30, 9)` -/
lemma example2_inv : littleendian_inv [0x091e4b56] = [86, 75, 30, 9] := 
begin
  unfold littleendian_inv,
  norm_num,
end

/-- `littleendian⁻¹ 4211081215 = (255, 255, 255, 250)` -/
lemma example3_inv : littleendian_inv [0xfaffffff] = [255, 255, 255, 250] := 
begin
  unfold littleendian_inv,
  norm_num,
end

end littleendian_examples
