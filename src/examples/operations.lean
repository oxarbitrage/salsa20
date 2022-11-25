import operations

open operations

/- 
  Examples from the spec.
-/

-- example xor
#eval if bitvec.xor (bitvec.of_nat 32 0xc0a8787e) (bitvec.of_nat 32 0x9fd1161d) = 0x5f796e63 
  then "pass" else "fail"

-- example modular addition
#eval if 0xc0a8787e MOD 0x9fd1161d = 0x60798e9b then "pass" else "fail"

-- example rotl
#eval if (rotl (bitvec.of_nat 32 0xc0a8787e) 5).to_nat = 0x150f0fd8 then "pass" else "fail"

-- TODO: inverse examples
