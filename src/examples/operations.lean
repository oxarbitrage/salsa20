import operations

open operations

/-
  Operations
-/

-- example from the spec for xor: 0xc0a8787e XOR 0x9fd1161d = 0x5f796e63
#eval if bitvec.xor (bitvec.of_nat 32 0xc0a8787e) (bitvec.of_nat 32 0x9fd1161d) = 0x5f796e63 
  then "pass" else "fail"

-- example from the spec for sum: 0xc0a8787e + 0x9fd1161d = 0x60798e9b
#eval if 0xc0a8787e MOD 0x9fd1161d = 0x60798e9b then "pass" else "fail"

-- example from the spec for rot : 0xc0a8787e <<< 5 = 0x150f0fd8
#eval if (rotl (bitvec.of_nat 32 0xc0a8787e) 5).to_nat = 0x150f0fd8 then "pass" else "fail"

/-
  Do inverse using the same numbers as the spec examples.
-/