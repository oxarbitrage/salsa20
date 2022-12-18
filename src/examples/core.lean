import core

open core
open utils

/- 
  Examples from the spec. 
-/

-- example 1

def input : matrix64Type := (
  ((0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)),
  ((0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)),
  ((0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)),
  ((0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0))
)

def output : matrix64Type := (
  ((0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)),
  ((0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)),
  ((0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)),
  ((0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0))
)

set_option class.instance_max_depth 128

#eval if hash input = output then "pass" else "fail"

-- example 2

def input' : matrix64Type := (
  ((211, 159, 13, 115), (76, 55, 82, 183), (3, 117, 222, 37), (191, 187, 234, 136)),
  ((49, 237, 179, 48), (1, 106, 178, 219), (175, 199, 166, 48), (86, 16, 179, 207)),
  ((31, 240, 32, 63), (15, 83, 93, 161), (116, 147, 48, 113), (238, 55, 204, 36)),
  ((79, 201, 235, 79), (3, 81, 156, 47), (203, 26, 244, 243), (88, 118, 104, 54))
)

def output' : matrix64Type := (
  ((109, 42, 178, 168), (156, 240, 248, 238), (168, 196, 190, 203), (26, 110, 170, 154)),
  ((29, 29, 150, 26), (150, 30, 235, 249), (190, 163, 251, 48), (69, 144, 51, 57)),
  ((118, 40, 152, 157), (180, 57, 27, 94), (107, 42, 236, 35), (27, 111, 114, 114)),
  ((219, 236, 232, 135), (111, 155, 110, 18), (24, 232, 95, 158), (179, 19, 48, 202))
)

#eval if hash input' = output' then "pass" else "fail"

-- example 3

def input'' : matrix64Type := (
  ((88, 118, 104, 54), (79, 201, 235, 79), (3, 81, 156, 47), (203, 26, 244, 243)),
  ((191, 187, 234, 136), (211, 159, 13, 115), (76, 55, 82, 183), (3, 117, 222, 37)),
  ((86, 16, 179, 207), (49, 237, 179, 48), (1, 106, 178, 219), (175, 199, 166, 48)),
  ((238, 55, 204, 36), (31, 240, 32, 63), (15, 83, 93, 161), (116, 147, 48, 113))
)

def output'' : matrix64Type := (
  ((179, 19, 48, 202), (219, 236, 232, 135), (111, 155, 110, 18), (24, 232, 95, 158)),
  ((26,110,170,154), (109, 42, 178, 168), (156, 240, 248, 238), (168, 196, 190, 203)),
  ((69, 144, 51, 57), (29, 29, 150, 26), (150, 30, 235, 249), (190, 163, 251, 48)),
  ((27, 111, 114, 114), (118, 40, 152, 157), (180, 57, 27, 94), (107, 42, 236, 35))
)

#eval if hash input'' = output'' then "pass" else "fail"

/-
  Test collisions, from appendix https://www.iacr.org/archive/fse2008/50860470/50860470.pdf
-/

-- test vector 1

def Z : matrixType :=
  (
    (0xAAAAAAAA, 0x55555556, 0xAAAAAAAA, 0x55555556),
    (0x55555556, 0xAAAAAAAA, 0x55555556, 0xAAAAAAAA),
    (0xAAAAAAAA, 0x55555556, 0xAAAAAAAA, 0x55555556),
    (0x55555556, 0xAAAAAAAA, 0x55555556, 0xAAAAAAAA)
  )

def Z' : matrixType :=
  (
    (0x2AAAAAAA, 0xD5555556, 0x2AAAAAAA, 0xD5555556),
    (0xD5555556, 0x2AAAAAAA, 0xD5555556, 0x2AAAAAAA),
    (0x2AAAAAAA, 0xD5555556, 0x2AAAAAAA, 0xD5555556),
    (0xD5555556, 0x2AAAAAAA, 0xD5555556, 0x2AAAAAAA)
  )

def result : matrixType :=
  (
    (0x55555554, 0xAAAAAAAC, 0x55555554, 0xAAAAAAAC),
    (0xAAAAAAAC, 0x55555554, 0xAAAAAAAC, 0x55555554),
    (0x55555554, 0xAAAAAAAC, 0x55555554, 0xAAAAAAAC),
    (0xAAAAAAAC, 0x55555554, 0xAAAAAAAC, 0x55555554)
  )

#eval if (core Z = core Z' ∧ core Z = result) then "pass" else "fail"

-- test vector 2

def W : matrixType :=
  (
    (0xFFFFFFFF, 0x00000001, 0xFFFFFFFF, 0x00000001),
    (0x00000001, 0xFFFFFFFF, 0x00000001, 0xFFFFFFFF),
    (0xFFFFFFFF, 0x00000001, 0xFFFFFFFF, 0x00000001),
    (0x00000001, 0xFFFFFFFF, 0x00000001, 0xFFFFFFFF)
  )

def W' : matrixType :=
  (
    (0x7FFFFFFF, 0x80000001, 0x7FFFFFFF, 0x80000001),
    (0x80000001, 0x7FFFFFFF, 0x80000001, 0x7FFFFFFF),
    (0x7FFFFFFF, 0x80000001, 0x7FFFFFFF, 0x80000001),
    (0x80000001, 0x7FFFFFFF, 0x80000001, 0x7FFFFFFF)
  )

def result' : matrixType :=
  (
    (0xFFFFFFFE, 0x00000002, 0xFFFFFFFE, 0x00000002),
    (0x00000002, 0xFFFFFFFE, 0x00000002, 0xFFFFFFFE),
    (0xFFFFFFFE, 0x00000002, 0xFFFFFFFE, 0x00000002),
    (0x00000002, 0xFFFFFFFE, 0x00000002, 0xFFFFFFFE)
  )

#eval if (core W = core W' ∧ core W = result') then "pass" else "fail"

-- For any given input, the core function of the difference with 0x80000000 produces the same
-- output as without it.

-- A demo input.
def U : matrixType :=
  (
    (0x00000001, 0xF0000001, 0x00000001, 0x00000001),
    (0x60000001, 0x00000001, 0x00000001, 0x00000001),
    (0x00000001, 0x00000001, 0x00000001, 0x00000001),
    (0x00000001, 0x00000001, 0x00000001, 0x00000001)
  )

-- Another input consisting of U XOR 0x80000000
def U' : matrixType :=
  (
    (0x00000001 XOR 0x80000000, 0xF0000001 XOR 0x80000000, 0x00000001 XOR 0x80000000, 0x00000001 XOR 0x80000000),
    (0x60000001 XOR 0x80000000, 0x00000001 XOR 0x80000000, 0x00000001 XOR 0x80000000, 0x00000001 XOR 0x80000000),
    (0x00000001 XOR 0x80000000, 0x00000001 XOR 0x80000000, 0x00000001 XOR 0x80000000, 0x00000001 XOR 0x80000000),
    (0x00000001 XOR 0x80000000, 0x00000001 XOR 0x80000000, 0x00000001 XOR 0x80000000, 0x00000001 XOR 0x80000000)
  )

#eval if core U = core U' then "pass" else "fail"
