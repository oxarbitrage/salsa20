import littleendian

open littleendian
open utils

/- 
  Examples from the spec. 
-/

-- example 1
#eval if littleendian (0, 0, 0, 0) = 0 then "pass" else "fail"

-- example2
#eval if littleendian (86, 75, 30, 9) = 0x091e4b56 then "pass" else "fail"

-- example 3
#eval if littleendian (255, 255, 255, 250) = 0xfaffffff then "pass" else "fail"

/- 
  Inverses. 
-/

-- example 1
#eval if littleendian_inv 0 = (0, 0, 0, 0) then "pass" else "fail"

-- example2
#eval if littleendian_inv 0x091e4b56 = (86, 75, 30, 9) then "pass" else "fail"

-- example 3
#eval if littleendian_inv 0xfaffffff = (255, 255, 255, 250) then "pass" else "fail"
