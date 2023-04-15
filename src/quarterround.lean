import operations
import types

open operations
open params
open types

open category_theory
open_locale category_theory.Type


namespace quarterround

variables [category (bitvec word_len)]

/-!
# Quarter round

The `quarterround` function takes a 4 bitvec sequence and return a sequence of the same type by applying the 
quarterround diagram.

- [Quarterround Diagram](https://q.uiver.app/?q=WzAsMjYsWzUsMCwiKHkwLCB5MSwgeTIsIHkzKSJdLFsxLDEsInkwIl0sWzMsMSwieTEiXSxbNywxLCJ5MiJdLFs5LDEsInkzIl0sWzUsMiwiKHkwLCB5MykiXSxbNSw0LCJtb2RyZXMxIl0sWzMsNSwiKHkxLCByb3RscmVzMSkiXSxbNyw1LCJyb3RscmVzMSJdLFszLDcsInoxIixbMzAwLDYwLDYwLDFdXSxbMSw4LCIoejEsIHkwKSJdLFsxLDEwLCJtb2RyZXMyIl0sWzgsMTAsInJvdGxyZXMyIl0sWzEwLDgsIih5Miwgcm90bHJlczIpIl0sWzgsOCwiejIiLFszMDAsNjAsNjAsMV1dLFsxMiw2LCIoejIsIHoxKSJdLFsxMiw4LCJtb2RyZXMzIl0sWzE1LDgsInJvdGxyZXMzIl0sWzE1LDYsIih5Mywgcm90bHJlczMpIl0sWzE3LDYsInozIixbMzAwLDYwLDYwLDFdXSxbMTIsMTEsIih6MywgejIpIl0sWzksMTEsIm1vZHJlczAiXSxbNiwxMSwicm90bHJlczAiXSxbMCwxMSwiKHkwLCByb3RscmVzMCkiXSxbMCwxMywiejAiLFszMDAsNjAsNjAsMV1dLFs1LDEzLCIoejAsIHoxLCB6MiwgejMpIixbMjQwLDYwLDYwLDFdXSxbMCwxLCJmaXJzdCIsMV0sWzAsMiwic2Vjb25kIiwxXSxbMCwzLCJ0aGlyZCIsMV0sWzAsNCwiZm91cnRoIiwxXSxbNCw1LCJidWlsZG1vZDEiLDFdLFsxLDUsImJ1aWxkbW9kMSIsMV0sWzUsNiwibW9kIiwxXSxbMiw3LCJidWlsZHhvcjEiLDFdLFs4LDcsImJ1aWxkeG9yMSIsMV0sWzcsOSwieG9yIiwxXSxbMSwxMCwiYnVpbGRtb2QyIiwxXSxbMTAsMTFdLFszLDEzLCJidWlsZHhvcjIiLDEseyJjdXJ2ZSI6LTR9XSxbMTMsMTQsInhvciIsMV0sWzYsOCwicm90bDciLDFdLFs5LDEwLCJidWlsZG1vZDIiLDFdLFsxMSwxMiwicm90bDEzIiwxXSxbMTIsMTMsImJ1aWxkeG9yMiIsMSx7ImN1cnZlIjo0fV0sWzE0LDE1LCJidWlsZG1vZDMiLDFdLFs5LDE1LCJidWlsZG1vZDMiLDFdLFsxNSwxNiwibW9kIiwxXSxbMTYsMTcsInJvdGwxMyIsMV0sWzE3LDE4LCJidWlsZHhvcjMiLDFdLFs0LDE4LCJidWlsZHhvcjMiLDFdLFsxOCwxOSwieG9yIiwxXSxbMTksMjAsImJ1aWxkbW9kMCIsMSx7ImN1cnZlIjotM31dLFsxNCwyMCwiYnVpbGRtb2QwIiwxLHsiY3VydmUiOjV9XSxbMjAsMjEsIm1vZCIsMV0sWzIxLDIyLCJyb3RsMTgiLDJdLFsyMiwyMywiYnVpbGR4b3IwIiwxXSxbMSwyMywiYnVpbGR4b3IwIiwxXSxbMjMsMjQsInhvciIsMV0sWzI0LDI1LCJqb2luIiwxLHsiY29sb3VyIjpbMjQwLDYwLDYwXX0sWzI0MCw2MCw2MCwxXV0sWzE0LDI1LCJqb2luIiwxLHsiY3VydmUiOjIsImNvbG91ciI6WzI0MCw2MCw2MF19LFsyNDAsNjAsNjAsMV1dLFsxOSwyNSwiam9pbiIsMSx7ImNvbG91ciI6WzI0MCw2MCw2MF19LFsyNDAsNjAsNjAsMV1dLFs5LDI1LCJqb2luIiwxLHsiY3VydmUiOjQsImNvbG91ciI6WzI0MCw2MCw2MF19LFsyNDAsNjAsNjAsMV1dLFswLDI1LCJxdWFydGVycm91bmQiLDEseyJjdXJ2ZSI6NSwiY29sb3VyIjpbMCw2MCw2MF0sInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX0sWzAsNjAsNjAsMV1dLFsyNSwwLCJxdWFydGVycm91bmReey0xfSIsMSx7ImN1cnZlIjo1LCJjb2xvdXIiOlswLDYwLDYwXSwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fSxbMCw2MCw2MCwxXV1d)

-/

/-- Return `x0` given an input vector `(x0, x1, x2, x3)`. -/
def first : vecType → bitvec word_len
| input := input 0 0

/-- Return `x1` given an input vector `(x0, x1, x2, x3)`. -/
def second : vecType → bitvec word_len
| input := input 0 1

/-- Return `x2` given an input vector `(x0, x1, x2, x3)`. -/
def third : vecType → bitvec word_len
| input := input 0 2

/-- Return `x3` given an input vector `(x0, x1, x2, x3)`. -/
def fourth : vecType → bitvec word_len
| input := input 0 3

/-- Return `(y0, y3)` given an input vector `(y0, y1, y2, y3)`. -/
def buildmod1 : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input _ := (first input, fourth input)

/-- Return `(y1, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor1 : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input b := (second input, b)

/-- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7) -/
def z1 (input : vecType) := ↾ buildmod1 input ≫ mod ≫ rotl7 ≫ buildxor1 input ≫ xor

/-- `z1` of `(0, 0, 0, 0)` is `0` -/
lemma z1_zero : z1 !![0, 0, 0, 0] 0 = 0 := by refl

/-- Return `(z1, y0)` given an input vector `(y0, y1, y2, y3)` and `z1`. -/
def buildmod2 : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input z1 := (z1, first input)

/-- Return `(y2, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor2 : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input b := (third input, b)

/-- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9) -/
def z2 (input : vecType) := ↾ buildmod2 input ≫ mod ≫ rotl9 ≫ buildxor2 input ≫ xor

/-- `z2` of `(0, 0, 0, 0)` is `0` -/
lemma z2_zero : z2 !![0, 0, 0, 0] 0 = 0 := by refl

/-- Return `(z2, z1)` given an input vector `(y0, y1, y2, y3)`, `z2` and `z1`. -/
def buildmod3 : vecType → bitvec word_len → bitvec word_len → bitvec word_len × bitvec word_len
| input z2 z1 := (z2, z1)

/-- Return `(y3, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor3 : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input b := (fourth input, b)

/-- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13) -/
def z3 (input : vecType) := 
  ↾ buildmod3 input (z2 input (z1 input (bitvec.zero word_len))) ≫ mod ≫ rotl13 ≫ buildxor3 input ≫ xor

/-- `z3` of `(0, 0, 0, 0)` is `0` -/
lemma z3_zero : z3 !![0, 0, 0, 0] 0 = 0 := by refl

/-- Return `(z3, z2)` given an input vector `(y0, y1, y2, y3)`, `z3` and `z2`. -/
def buildmod0 : vecType → bitvec word_len → bitvec word_len → bitvec word_len × bitvec word_len
| input z3 z2 := (z3 , z2)

/-- Return `(y0, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor0 : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input b := (first input, b)

/-- z₀ = y₀ ⊕ ((z₃ + z₂) <<< 18) -/
def z0 (input : vecType) := 
  ↾ buildmod0 input (z2 input (z1 input (bitvec.zero word_len))) ≫ mod ≫ rotl18 ≫ buildxor0 input ≫ xor

/-- `z0` of `(0, 0, 0, 0)` is `0` -/
lemma z0_zero : z0 !![0, 0, 0, 0] 0 = 0 := by refl

/- The full quarterround output built from its components in index order. -/
def quarterround (input : vecType) := !![
  z0 input (z3 input (z1 input 0)),
  z1 input 0,
  z2 input (z1 input 0),
  z3 input (z1 input 0)
]

/-- `quarterround` of `(0, 0, 0, 0)` is `(0, 0, 0, 0)` -/
lemma quarterround_zero : quarterround !![0, 0, 0, 0] = !![0, 0, 0, 0] := by refl

/- `quarterround⁻¹` is just the inverse given `quarterround` is isomorphic. -/
noncomputable def quarterround_inv [is_iso (↾ quarterround)] := inv ↾ quarterround

local notation `quarterround⁻¹` := quarterround_inv

end quarterround
