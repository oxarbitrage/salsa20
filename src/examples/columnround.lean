import columnround

open columnround

/- 
  Examples from the spec. Note the order of the numbers used here is not the same as the spec. 
  We use this order for calls:

  (y₀, y₄, y₈, y₁₂) = quarterround(x₀, x₄, x₈, x₁₂)
  (y₅, y₉, y₁₃, y₁) = quarterround(x₅, x₉, x₁₃, x₁)
  (y₁₀, y₁₄, y₂, y₆) = quarterround(x₁₀, x₁₄, x₂, x₆)
  (y₁₅, y₃, y₇, y₁₁) = quarterround(x₁₅, x₃, x₇, x₁₁)
-/

-- example 1
def input1 : vecType := (0x00000001, 0x00000001, 0x00000001, 0x00000001)
def input2 : vecType := (0x00000000, 0x00000000, 0x00000000, 0x00000000)
def input3 : vecType := (0x00000000, 0x00000000, 0x00000000, 0x00000000)
def input4 : vecType := (0x00000000, 0x00000000, 0x00000000, 0x00000000)

def output : matrixType :=
  (
    (0x10090288, 0x00000101, 0x00020401, 0x40a04001),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)
  )

#eval if 
  columnround input1 input2 input3 input4 = output then "pass" else "fail"

-- example 2
def input1' : vecType := (0x08521bd6, 0xc54c6a5b, 0x90a2f23d, 0xe859c100)
def input2' : vecType := (0x2fc74c2f, 0x067f95a6, 0xea4d84b7, 0x1fe88837)
def input3' : vecType := (0x06b35f61, 0x0f619bff, 0xbb2aa576, 0x6dd39cc3)
def input4' : vecType := (0xbc6e965a, 0x3aa26365, 0xda0a64f6, 0x41e4732e)

def output' : matrixType :=
  (
    (0x8c9d190a, 0x90a20123, 0x789b010c, 0x481c2027),
    (0xead3c4f3, 0xd195a681, 0x53a8e4b5, 0xce8e4c90),
    (0xeb7d5504, 0x4c1f89c5, 0x1ef8e9d3, 0x63a091a0),
    (0x3f78c9c8, 0x1326a71a, 0xf0708d69, 0xa774135c)
  )

#eval if 
  columnround input1' input2' input3' input4' = output' then "pass" else "fail"


/- 
  Inverse examples using the same numbers as the spec ones. 
  Just as with `columnround` we have to give the right order to the inputs:

  (y₀, y₄, y₈, y₁₂) = quarterround(x₀, x₄, x₈, x₁₂)
  (y₅, y₉, y₁₃, y₁) = quarterround(x₅, x₉, x₁₃, x₁)
  (y₁₀, y₁₄, y₂, y₆) = quarterround(x₁₀, x₁₄, x₂, x₆)
  (y₁₅, y₃, y₇, y₁₁) = quarterround(x₁₅, x₃, x₇, x₁₁)

-/

-- TODO: add inverse examples
