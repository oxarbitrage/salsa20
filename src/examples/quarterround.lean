import quarterround

open quarterround

namespace quarterround_examples
/- 
  Examples from the spec.

  https://cr.yp.to/snuffle/spec.pdf
-/

-- example 1
#eval if 
  quarterround (0x00000000, 0x00000000, 0x00000000, 0x00000000) =  
    (0x000000000, 0x00000000, 0x00000000, 0x00000000) then "pass" else "fail"

-- example 2
#eval if 
  quarterround (0x00000001, 0x00000000, 0x00000000, 0x00000000) =  
    (0x08008145, 0x00000080, 0x00010200, 0x20500000) then "pass" else "fail"

-- example 3
#eval if 
  quarterround (0x00000000, 0x00000001, 0x00000000, 0x00000000) =  
    (0x88000100, 0x00000001, 0x00000200, 0x00402000) then "pass" else "fail"

-- example 4
#eval if 
  quarterround (0x00000000, 0x00000000, 0x00000001, 0x00000000) =  
    (0x80040000, 0x00000000, 0x00000001, 0x00002000) then "pass" else "fail"

-- example 5
#eval if 
  quarterround (0x00000000, 0x00000000, 0x00000000, 0x00000001) =  
    (0x00048044, 0x00000080, 0x00010000, 0x20100001) then "pass" else "fail"

-- example 6
#eval if 
  quarterround (0xe7e8c006, 0xc4f9417d, 0x6479b4b2, 0x68c67137) =  
    (0xe876d72b, 0x9361dfd5, 0xf1460244, 0x948541a3) then "pass" else "fail"

-- example 7
#eval if 
  quarterround (0xd3917c5b, 0x55f1c407, 0x52a58a7a, 0x8f887a3b) =  
    (0x3e2f308c, 0xd90a8f36, 0x6ab2a923, 0x2883524c) then "pass" else "fail"

/- 
  Inverse examples, using the same numbers as the spec examples but appling the inverse
  operation.
-/

-- example 1
#eval if 
  quarterround_inv (0x00000000, 0x00000000, 0x00000000, 0x00000000) =  
    (0x000000000, 0x00000000, 0x00000000, 0x00000000) then "pass" else "fail"

-- example 2
#eval if 
  quarterround_inv (0x08008145, 0x00000080, 0x00010200, 0x20500000) =  
    (0x00000001, 0x00000000, 0x00000000, 0x00000000) then "pass" else "fail"

-- example 3
#eval if 
  quarterround_inv (0x88000100, 0x00000001, 0x00000200, 0x00402000) =  
    (0x00000000, 0x00000001, 0x00000000, 0x00000000) then "pass" else "fail"

-- example 4
#eval if 
  quarterround_inv (0x80040000, 0x00000000, 0x00000001, 0x00002000) =  
    (0x00000000, 0x00000000, 0x00000001, 0x00000000) then "pass" else "fail"

-- example 5
#eval if 
  quarterround_inv (0x00048044, 0x00000080, 0x00010000, 0x20100001) =  
    (0x00000000, 0x00000000, 0x00000000, 0x00000001) then "pass" else "fail"

-- example 6
#eval if 
  quarterround_inv (0xe876d72b, 0x9361dfd5, 0xf1460244, 0x948541a3) =  
    (0xe7e8c006, 0xc4f9417d, 0x6479b4b2, 0x68c67137) then "pass" else "fail"

-- example 7
#eval if 
  quarterround_inv (0x3e2f308c, 0xd90a8f36, 0x6ab2a923, 0x2883524c) =
    (0xd3917c5b, 0x55f1c407, 0x52a58a7a, 0x8f887a3b) then "pass" else "fail"


/-
  Some tests for carried difference of the `quarterround` function.
-/

-- The most significant bit of the result is never equal
#eval if (quarterround (30, 12, 44, 124)).fst.head ≠
  (quarterround (30 XOR 0x80000000, 12 XOR 0x80000000, 44 XOR 0x80000000, 124 XOR 0x80000000)).fst.head
    then "pass" else "fail"

-- But the rest of the bitstring is always the same
#eval if (quarterround (30, 12, 44, 124)).fst.tail =
  (quarterround (30 XOR 0x80000000, 12 XOR 0x80000000, 44 XOR 0x80000000, 124 XOR 0x80000000)).fst.tail
    then "pass" else "fail"

-- 
#eval if 50 XOR (50 XOR 0x80000000) = 0x80000000 then "pass" else "fail"

end quarterround_examples