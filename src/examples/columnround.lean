import columnround

open columnround
open utils

namespace columnround_examples

/-!
  # Columnround examples

  ## Spec examples
-/

/-! ### Example 1 -/

/-- Input for example 1 --/
def input1 : matrixType :=
  (
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000)
  )

/-- Output for example 1 --/
def output1 : matrixType :=
  (
    (0x10090288, 0x00000000, 0x00000000, 0x00000000),
    (0x00000101, 0x00000000, 0x00000000, 0x00000000),
    (0x00020401, 0x00000000, 0x00000000, 0x00000000),
    (0x40a04001, 0x00000000, 0x00000000, 0x00000000)
  )

#eval if columnround_output (columnround (columnround_input input1)) = output1 then "pass" else "fail"

/-! ### Example 2 -/

/- Input for example 2 -/
def input2 : matrixType :=
  (
    (0x08521bd6, 0x1fe88837, 0xbb2aa576, 0x3aa26365),
    (0xc54c6a5b, 0x2fc74c2f, 0x6dd39cc3, 0xda0a64f6),
    (0x90a2f23d, 0x067f95a6, 0x06b35f61, 0x41e4732e),
    (0xe859c100, 0xea4d84b7, 0x0f619bff, 0xbc6e965a)
  )

/-- Output for example 2 -/
def output2 : matrixType :=
  (
    (0x8c9d190a, 0xce8e4c90, 0x1ef8e9d3, 0x1326a71a),
    (0x90a20123, 0xead3c4f3, 0x63a091a0, 0xf0708d69),
    (0x789b010c, 0xd195a681, 0xeb7d5504, 0xa774135c),
    (0x481c2027, 0x53a8e4b5, 0x4c1f89c5, 0x3f78c9c8)
  )

#eval if columnround_output (columnround (columnround_input input2)) = output2 then "pass" else "fail"

/-!
  ## Inverse examples

  We use the same test vectors as the spec but going backwards.
-/

-- example 1
#eval if columnround_output (columnround_inv (columnround_input output1)) = input1 then "pass" else "fail"

-- example 2
#eval if columnround_output (columnround_inv (columnround_input output2)) = input2 then "pass" else "fail"

end columnround_examples
