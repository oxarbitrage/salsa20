import operations

open operations

namespace operations_examples

/- 
  Examples from the spec.

  https://cr.yp.to/snuffle/spec.pdf
-/

-- example xor
#eval if bitvec.xor (bitvec.of_nat 32 0xc0a8787e) (bitvec.of_nat 32 0x9fd1161d) = 0x5f796e63 
  then "pass" else "fail"

-- example modular addition
#eval if 0xc0a8787e MOD 0x9fd1161d = 0x60798e9b then "pass" else "fail"

-- example rotl
#eval if (rotl (bitvec.of_nat 32 0xc0a8787e) 5).to_nat = 0x150f0fd8 then "pass" else "fail"

-- Inverse examples

-- example xor:
#eval if bitvec.xor (bitvec.of_nat 32 0x5f796e63) (bitvec.of_nat 32 0x9fd1161d) = 0xc0a8787e
  then "pass" else "fail"

-- mod does not have an inverse
-- TODO: prove mod is not bijective and by this prove it does not has an inverse ? 

-- example rotl
#eval if (rotl_inv (bitvec.of_nat 32 0x150f0fd8) 5).to_nat = 0xc0a8787e then "pass" else "fail"

end operations_examples