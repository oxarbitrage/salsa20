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
lemma example2_qr1 :
  qr1 0x00000001 0x00000000 0x00000000 0x00000000 = 0x00000080 :=
begin
  rw qr1,
  rw operations.operation,
  rw operations.operation_rhs,
  rw operations.xor,
  rw operations.mod,
  rw operations.rotl,
  rw params.max_bitvec,
  rw params.mod,
  rw params.word_len,
  rw bitvec.of_nat,
  rw bitvec.shl,
  rw bitvec.ushr,
  rw bitvec.fill_shr,
  repeat { rw bitvec.of_nat },

  norm_num,

  refl,
end

/-- `qr2 (1, 0, 0, 0) = 66048` -/
lemma example2_qr2 :
  qr2 0x00000001 0x00000000 0x00000000 0x00000000 = 0x00010200 :=
begin
  rw qr2,
  rw qr1,
  repeat { rw operations.operation },
  repeat { rw operations.operation_rhs },
  repeat { rw operations.xor },
  repeat { rw operations.mod },
  repeat { rw operations.rotl },
  rw params.max_bitvec,
  rw params.mod,
  rw params.word_len,
  rw bitvec.of_nat,
  rw bitvec.shl,
  rw bitvec.ushr,
  rw bitvec.fill_shr,
  repeat { rw bitvec.of_nat },

  norm_num,

  refl,
end

/-- `qr3 (1, 0, 0, 0) = 542113792` -/
lemma example2_qr3 :
  qr3 0x00000001 0x00000000 0x00000000 0x00000000 = 0x20500000 :=
begin
  rw qr3,
  rw qr1,
  rw qr2,
  rw qr1,
  repeat { rw operations.operation },
  repeat { rw operations.operation_rhs },
  repeat { rw operations.xor },
  repeat { rw operations.mod },
  repeat { rw operations.rotl },
  rw params.max_bitvec,
  rw params.mod,
  rw params.word_len,
  rw bitvec.of_nat,
  rw bitvec.shl,
  rw bitvec.ushr,
  rw bitvec.fill_shr,
  repeat { rw bitvec.of_nat },

  norm_num,

  refl,
end

/-- `qr0 (1, 0, 0, 0) = 134250821` -/
lemma example2_qr0 :
  qr0 0x00000001 0x00000000 0x00000000 0x00000000 = 0x08008145 :=
begin
  rw qr0,
  rw qr3,
  rw qr2,
  rw qr1,
  repeat { rw operations.operation },
  repeat { rw operations.operation_rhs },
  repeat { rw operations.xor },
  repeat { rw operations.mod },
  repeat { rw operations.rotl },
  rw params.max_bitvec,
  rw params.mod,
  rw params.word_len,
  rw bitvec.of_nat,
  rw bitvec.shl,
  rw bitvec.ushr,
  rw bitvec.fill_shr,
  repeat { rw bitvec.of_nat },

  norm_num,

  refl,
end

/-- `quarterround (1, 0, 0, 0) = (134250821, 128, 66048, 542113792)` -/
lemma example2_quarterround : quarterround (0x00000001, 0x00000000, 0x00000000, 0x00000000) =
    (0x08008145, 0x00000080, 0x00010200, 0x20500000) :=
begin
  rw quarterround,
  rw example2_qr0,
  rw example2_qr1,
  rw example2_qr2,
  rw example2_qr3,
end

/-!
## Example 3 : 

> quarterround(0x00000000, 0x00000001, 0x00000000, 0x00000000) = (0x88000100, 0x00000001, 0x00000200, 0x00402000)

-/

/-- `qr1 (0, 1, 0, 0) = 1` -/
lemma example3_qr1 :
  qr1 0x00000000 0x00000001 0x00000000 0x00000000 = 0x00000001 :=
begin
  rw qr1,
  rw operations.operation,
  rw operations.operation_rhs,
  rw operations.xor,
  rw operations.mod,
  rw operations.rotl,
  rw params.max_bitvec,
  rw params.mod,
  rw params.word_len,
  rw bitvec.of_nat,
  rw bitvec.shl,
  rw bitvec.ushr,
  rw bitvec.fill_shr,
  repeat { rw bitvec.of_nat },

  norm_num,

  refl,
end

/-!
  ## TODO

  - find a way that can make this shorter.
  - continue the examples from the spec.
  - add inverse examples.
-/


end quarterround_examples