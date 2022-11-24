import rowround

open rowround

/- 
  Examples from the spec. Note the order of the numbers used here is not the same as the spec. 
  We use this order for calls:

  (z₀, z₁, z₂, z₃) = quarterround(y₀, y₁, y₂, y₃)
  (z₅, z₆, z₇, z₄) = quarterround(y₅, y₆, y₇, y₄)
  (z₁₀, z₁₁, z₈, z₉) = quarterround(y₁₀, y₁₁, y₈, y₉)
  (z₁₅, z₁₂, z₁₃, z₁₄) = quarterround(y₁₅, y₁₂, y₁₃, y₁₄)
-/

-- example 1

def input : matrixType :=
  (
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000001),
    (0x00000000, 0x00000000, 0x00000001, 0x00000000),
    (0x00000000, 0x00000001, 0x00000000, 0x00000000)
  )

def output : matrixType :=
  (
    (0x08008145, 0x00000080, 0x00010200, 0x20500000),
    (0x00048044, 0x00000080, 0x00010000, 0x20100001),
    (0x80040000, 0x00000000, 0x00000001, 0x00002000),
    (0x88000100, 0x00000001, 0x00000200, 0x00402000)
  )

#eval if rowround input = output then "pass" else "fail"

-- example 2

def input' : matrixType :=
  (
    (0x08521bd6, 0x1fe88837, 0xbb2aa576, 0x3aa26365),
    (0x2fc74c2f, 0x6dd39cc3, 0xda0a64f6, 0xc54c6a5b),
    (0x06b35f61, 0x41e4732e, 0x90a2f23d, 0x067f95a6),
    (0xbc6e965a, 0xe859c100, 0xea4d84b7, 0x0f619bff)
  )

def output' : matrixType :=
  (
    (0xa890d39d, 0x65d71596, 0xe9487daa, 0xc8ca6a86),
    (0x764b7754, 0xe408d9b9, 0x7a41b4d1, 0x949d2192),
    (0x50669f96, 0xd89ef0a8, 0x3402e183, 0x3c3af432),
    (0x1818882d, 0x0040ede5, 0xb545fbce, 0xd257ed4f)
  )

#eval if rowround input' = output' then "pass" else "fail"

/- 
  Inverse examples using the same numbers as the spec ones. 
  Just as with `rowround` we have to give the right order to the inputs:

  (y₀, y₁, y₂, y₃) = quarterround_inv(z₀, z₁, z₂, z₃)
  (y₅, y₆, y₇, y₄) = quarterround_inv(z₅, z₆, z₇, z₄)
  (y₁₀, y₁₁, y₈, y₉) = quarterround_inv(z₁₀, z₁₁, z₈, z₉)
  (y₁₅, y₁₂, y₁₃, y₁₄) = quarterround_inv(z₁₅, z₁₂, z₁₃, z₁₄)
-/

-- TODO: add inverse examples
