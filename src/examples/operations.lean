import operations

open operations

namespace operations_examples

/-!
  # Examples from the spec.

  https://cr.yp.to/snuffle/spec.pdf
-/

/-- example xor -/
example : bitvec.xor (bitvec.of_nat params.word_len 0xc0a8787e)
  (bitvec.of_nat params.word_len 0x9fd1161d) = 0x5f796e63 :=
begin
  rw params.word_len,
  unfold bitvec.of_nat,
  norm_num,
  refl,
end

/-- example modular addition -/
example : 0xc0a8787e MOD 0x9fd1161d = 0x60798e9b :=
begin
  unfold operations.mod,
  unfold params.max_bitvec,
  rw params.mod,
  rw params.word_len,
  unfold bitvec.of_nat,
  norm_num,
  refl,
end

/-- example rotl --/
example : (rotl (bitvec.of_nat params.word_len 0xc0a8787e) 5) = 0x150f0fd8 :=
begin
  unfold operations.rotl,
  unfold bitvec.shl,
  unfold bitvec.ushr,
  rw params.word_len,
  unfold bitvec.of_nat,
  unfold bitvec.fill_shr,
  norm_num,
  refl,
end

/-! # Inverse examples -/

/-- example inverse xor -/
example : bitvec.xor (bitvec.of_nat params.word_len 0x5f796e63)
  (bitvec.of_nat params.word_len 0x9fd1161d) = 0xc0a8787e :=
begin
  rw params.word_len,
  unfold bitvec.of_nat,
  norm_num,
  refl,
end

/-- example rotl_inv -/
example : rotl_inv (bitvec.of_nat params.word_len 0x150f0fd8) 5 =
  0xc0a8787e :=
begin
  unfold rotl_inv,
  unfold bitvec.shl,
  unfold bitvec.ushr,
  rw params.word_len,
  unfold bitvec.of_nat,
  unfold bitvec.fill_shr,
  norm_num,
  refl,
end

/-!
## TODO
- mod does not have an inverse
- prove mod is not isomorphic and by this prove it does not has an inverse ?
-/

end operations_examples
