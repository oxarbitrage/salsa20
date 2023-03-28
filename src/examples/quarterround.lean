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

/-- `quarterround (0, 0, 0, 0) = (0, 0, 0, 0)` -/
lemma example1_quarterround : quarterround (0x00000000, 0x00000000, 0x00000000, 0x00000000) =
    (0x000000000, 0x00000000, 0x00000000, 0x00000000) := by refl

/-!
## Example 2 : 

> quarterround(0x00000001, 0x00000000, 0x00000000, 0x00000000) = (0x08008145, 0x00000080, 0x00010200, 0x20500000)
-/

/-- `qr1 (1, 0, 0, 0) = 128` -/
lemma example2_qr1 : qr1 0x00000001 0x00000000 0x00000000 0x00000000 = 0x00000080 :=
begin
  rw [qr1, operations.operation, operations.operation_rhs, operations.xor, operations.mod,
    operations.rotl, params.max_bitvec, params.mod, params.word_len, bitvec.of_nat,
    bitvec.shl, bitvec.ushr, bitvec.fill_shr],
  dunfold bitvec.of_nat,
  norm_num1,
  refl,
end

/-- `qr2 (1, 0, 0, 0) = 66048` -/
lemma example2_qr2 : qr2 0x00000001 0x00000000 0x00000000 0x00000000 = 0x00010200 :=
begin
  rw [qr2, qr1],
  repeat { 
    rw [operations.operation, operations.operation_rhs, operations.xor, operations.mod, operations.rotl] 
  },
  rw [params.max_bitvec, params.mod, params.word_len, bitvec.of_nat, bitvec.shl, bitvec.ushr, bitvec.fill_shr],
  dunfold bitvec.of_nat,
  norm_num,
  refl,
end

/-- `qr3 (1, 0, 0, 0) = 542113792` -/
lemma example2_qr3 : qr3 0x00000001 0x00000000 0x00000000 0x00000000 = 0x20500000 :=
begin
  rw [qr3, qr1, qr2, qr1],
  -- TODO: This is the same as `example2_qr2`
  repeat { 
    rw [operations.operation, operations.operation_rhs, operations.xor, operations.mod, operations.rotl] 
  },
  rw [params.max_bitvec, params.mod, params.word_len, bitvec.of_nat, bitvec.shl, bitvec.ushr, bitvec.fill_shr],
  dunfold bitvec.of_nat,
  norm_num,
  refl,
end

/-- `qr0 (1, 0, 0, 0) = 134250821` -/
lemma example2_qr0 : qr0 0x00000001 0x00000000 0x00000000 0x00000000 = 0x08008145 :=
begin
  rw [qr0, qr3, qr2, qr1],
  -- TODO: This is the same as `example2_qr2`
  repeat { 
    rw [operations.operation, operations.operation_rhs, operations.xor, operations.mod, operations.rotl] 
  },
  rw [params.max_bitvec, params.mod, params.word_len, bitvec.of_nat, bitvec.shl, bitvec.ushr, bitvec.fill_shr],
  dunfold bitvec.of_nat,
  norm_num,
  refl,
end

/-- `quarterround (1, 0, 0, 0) = (134250821, 128, 66048, 542113792)` -/
lemma example2_quarterround : quarterround (0x00000001, 0x00000000, 0x00000000, 0x00000000) =
    (0x08008145, 0x00000080, 0x00010200, 0x20500000) :=
begin
  rw [quarterround, example2_qr0, example2_qr1, example2_qr2, example2_qr3],
end

/-!
## Example 3 : 

> quarterround(0x00000000, 0x00000001, 0x00000000, 0x00000000) = (0x88000100, 0x00000001, 0x00000200, 0x00402000)

-/

/-- `qr1 (0, 1, 0, 0) = 1` -/
lemma example3_qr1 : qr1 0x00000000 0x00000001 0x00000000 0x00000000 = 0x00000001 :=
begin
  -- TODO: this is the exact same proof as `example2_qr1`.
  rw [qr1, operations.operation, operations.operation_rhs, operations.xor, operations.mod,
    operations.rotl, params.max_bitvec, params.mod, params.word_len, bitvec.of_nat,
    bitvec.shl, bitvec.ushr, bitvec.fill_shr],
  dunfold bitvec.of_nat,
  norm_num1,
  refl,
end

/-- `qr2 (0, 1, 0, 0) = 512` -/
lemma example3_qr2 : qr2 0x00000000 0x00000001 0x00000000 0x00000000 = 0x00000200 :=
begin
  -- TODO: this is the exact same proof as `example2_qr2`.
  rw [qr2, qr1],
  repeat { 
    rw [operations.operation, operations.operation_rhs, operations.xor, operations.mod, operations.rotl] 
  },
  rw [params.max_bitvec, params.mod, params.word_len, bitvec.of_nat, bitvec.shl, bitvec.ushr, bitvec.fill_shr],
  dunfold bitvec.of_nat,
  norm_num,
  refl,
end

/-- `qr3 (0, 1, 0, 0) = 4202496` -/
lemma example3_qr3 : qr3 0x00000000 0x00000001 0x00000000 0x00000000 = 0x00402000 :=
begin
  -- TODO: this is the exact same proof as `example2_qr3`.
  rw [qr3, qr1, qr2, qr1],
  repeat { 
    rw [operations.operation, operations.operation_rhs, operations.xor, operations.mod, operations.rotl] 
  },
  rw [params.max_bitvec, params.mod, params.word_len, bitvec.of_nat, bitvec.shl, bitvec.ushr, bitvec.fill_shr],
  dunfold bitvec.of_nat,
  norm_num,
  refl,
end

/-- `qr0 (0, 1, 0, 0) = 2281701632` -/
lemma example3_qr0 : qr0 0x00000000 0x00000001 0x00000000 0x00000000 = 0x88000100 :=
begin
  -- TODO: This is the same as `example2_qr0`
  rw [qr0, qr3, qr2, qr1],
  repeat { 
    rw [operations.operation, operations.operation_rhs, operations.xor, operations.mod, operations.rotl] 
  },
  rw [params.max_bitvec, params.mod, params.word_len, bitvec.of_nat, bitvec.shl, bitvec.ushr, bitvec.fill_shr],
  dunfold bitvec.of_nat,
  norm_num,
  refl,
end

/-- `quarterround (0, 1, 0, 0) = (2281701632, 1, 512, 4202496)` -/
lemma example3_quarterround : quarterround (0x00000000, 0x00000001, 0x00000000, 0x00000000) =
    (0x88000100, 0x00000001, 0x00000200, 0x00402000) :=
begin
  rw [quarterround, example3_qr0, example3_qr1, example3_qr2, example3_qr3],
end

/-!
  ## TODO

  - find a way that can make this shorter.
  - continue the examples from the spec.
  - add inverse examples.
-/

end quarterround_examples
