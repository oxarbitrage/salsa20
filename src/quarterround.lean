import operations
import types

import category_theory.category.basic
import category_theory.core

open operations
open params
open types

open category_theory

open_locale category_theory.Type

namespace quarterround

variables [category (bitvec word_len)]

/-!
# Quarter round diagram and it's inverse.

The `quarterround` function takes a tuple of 4 bitvecs and return a tuple of the same type
after applying the diagram.

- [Quarterround Diagram](https://q.uiver.app/?q=WzAsMjYsWzUsMCwiKHkwLCB5MSwgeTIsIHkzKSJdLFsxLDEsInkwIl0sWzMsMSwieTEiXSxbNywxLCJ5MiJdLFs5LDEsInkzIl0sWzUsMiwiKHkwLCB5MykiXSxbNSw0LCJtb2RyZXMxIl0sWzMsNSwiKHkxLCByb3RscmVzMSkiXSxbNyw1LCJyb3RscmVzMSJdLFszLDcsInoxIixbMzAwLDYwLDYwLDFdXSxbMSw4LCIoejEsIHkwKSJdLFsxLDEwLCJtb2RyZXMyIl0sWzgsMTAsInJvdGxyZXMyIl0sWzEwLDgsIih5Miwgcm90bHJlczIpIl0sWzgsOCwiejIiLFszMDAsNjAsNjAsMV1dLFsxMiw2LCIoejIsIHoxKSJdLFsxMiw4LCJtb2RyZXMzIl0sWzE1LDgsInJvdGxyZXMzIl0sWzE1LDYsIih5Mywgcm90bHJlczMpIl0sWzE3LDYsInozIixbMzAwLDYwLDYwLDFdXSxbMTIsMTEsIih6MywgejIpIl0sWzksMTEsIm1vZHJlczAiXSxbNiwxMSwicm90bHJlczAiXSxbMCwxMSwiKHkwLCByb3RscmVzMCkiXSxbMCwxMywiejAiLFszMDAsNjAsNjAsMV1dLFs1LDEzLCIoejAsIHoxLCB6MiwgejMpIixbMjQwLDYwLDYwLDFdXSxbMCwxLCJmaXJzdCIsMV0sWzAsMiwic2Vjb25kIiwxXSxbMCwzLCJ0aGlyZCIsMV0sWzAsNCwiZm91cnRoIiwxXSxbNCw1LCJidWlsZG1vZDEiLDFdLFsxLDUsImJ1aWxkbW9kMSIsMV0sWzUsNiwibW9kIiwxXSxbMiw3LCJidWlsZHhvcjEiLDFdLFs4LDcsImJ1aWxkeG9yMSIsMV0sWzcsOSwieG9yIiwxXSxbMSwxMCwiYnVpbGRtb2QyIiwxXSxbMTAsMTFdLFszLDEzLCJidWlsZHhvcjIiLDEseyJjdXJ2ZSI6LTR9XSxbMTMsMTQsInhvciIsMV0sWzYsOCwicm90bDciLDFdLFs5LDEwLCJidWlsZG1vZDIiLDFdLFsxMSwxMiwicm90bDEzIiwxXSxbMTIsMTMsImJ1aWxkeG9yMiIsMSx7ImN1cnZlIjo0fV0sWzE0LDE1LCJidWlsZG1vZDMiLDFdLFs5LDE1LCJidWlsZG1vZDMiLDFdLFsxNSwxNiwibW9kIiwxXSxbMTYsMTcsInJvdGwxMyIsMV0sWzE3LDE4LCJidWlsZHhvcjMiLDFdLFs0LDE4LCJidWlsZHhvcjMiLDFdLFsxOCwxOSwieG9yIiwxXSxbMTksMjAsImJ1aWxkbW9kMCIsMSx7ImN1cnZlIjotM31dLFsxNCwyMCwiYnVpbGRtb2QwIiwxLHsiY3VydmUiOjV9XSxbMjAsMjEsIm1vZCIsMV0sWzIxLDIyLCJyb3RsMTgiLDJdLFsyMiwyMywiYnVpbGR4b3IwIiwxXSxbMSwyMywiYnVpbGR4b3IwIiwxXSxbMjMsMjQsInhvciIsMV0sWzI0LDI1LCJxdWFydGVycm91bmQiLDEseyJjb2xvdXIiOlsyNDAsNjAsNjBdfSxbMjQwLDYwLDYwLDFdXSxbMTQsMjUsInF1YXJ0ZXJyb3VuZCIsMSx7ImN1cnZlIjoyLCJjb2xvdXIiOlsyNDAsNjAsNjBdfSxbMjQwLDYwLDYwLDFdXSxbMTksMjUsInF1YXJ0ZXJyb3VuZCIsMSx7ImNvbG91ciI6WzI0MCw2MCw2MF19LFsyNDAsNjAsNjAsMV1dLFs5LDI1LCJxdWFydGVycm91bmQiLDEseyJjdXJ2ZSI6NCwiY29sb3VyIjpbMjQwLDYwLDYwXX0sWzI0MCw2MCw2MCwxXV1d)

The `quarterround⁻¹` is of the same type.

- [Quarterround inverse diagram](https://q.uiver.app/?q=WzAsMjYsWzYsMCwiKHowLCB6MSwgejIsIHozKSJdLFs4LDEsInoyIl0sWzEwLDEsInozIl0sWzIsMSwiejAiXSxbNCwxLCJ6MSJdLFs5LDMsIih6MiwgejMpIl0sWzksNSwibW9kcmVzMCJdLFs2LDUsInJvdGxyZXMwIl0sWzMsNSwiKHowLCByb3RscmVzMCkiXSxbMyw3LCJ5MCIsWzMwMCw2MCw2MCwxXV0sWzYsMywiKHoyLCB6MSkiXSxbNiw2LCJtb2RyZXMzIl0sWzgsNiwicm90bHJlczMiXSxbMTAsNiwiKHozLCByb3RscmVzMykiXSxbMTAsOCwieTMiLFszMDAsNjAsNjAsMV1dLFs1LDgsIih6MSwgeTApIl0sWzcsOCwibW9kcmVzMiJdLFs5LDgsInJvdGxyZXMyIl0sWzgsMTAsIih6Miwgcm90bHJlczIpIl0sWzEwLDEwLCJ5MiIsWzMwMCw2MCw2MCwxXV0sWzcsMTEsIih5MCwgeTMpIl0sWzUsMTEsIm1vZHJlczEiXSxbMywxMSwicm90bHJlczEiXSxbMiw5LCIoejEsIHJvdGxyZXMxKSJdLFswLDksInkxIixbMzAwLDYwLDYwLDFdXSxbNiwxMywiKHkwLCB5MSwgeTIsIHkzKSIsWzI0MCw2MCw2MCwxXV0sWzAsMSwidGhpcmQiLDFdLFswLDIsImZvdXJ0aCIsMV0sWzAsMywiZmlyc3QiLDFdLFswLDQsInNlY29uZCIsMV0sWzEsNSwiYnVpbGRtb2QwJyIsMV0sWzIsNSwiYnVpbGRtb2QwJyIsMV0sWzUsNiwibW9kIiwxXSxbNiw3LCJyb3RsMTgiLDFdLFszLDgsImJ1aWxkeG9yMCIsMV0sWzcsOCwiYnVpbGR4b3IwIiwxXSxbOCw5LCJ4b3IiLDFdLFs0LDEwLCJidWlsZG1vZDMnIiwxXSxbMSwxMCwiYnVpbGRtb2QzJyIsMV0sWzEwLDExLCJtb2QiLDEseyJjdXJ2ZSI6M31dLFsxMSwxMiwicm90bDEzIiwxXSxbMTIsMTMsImJ1aWxkeG9yMyIsMV0sWzIsMTMsImJ1aWxkeG9yMyIsMV0sWzEzLDE0LCJ4b3IiLDFdLFs5LDE1LCJidWlsZG1vZDIiLDFdLFs0LDE1LCJidWlsZG1vZDIiLDEseyJjdXJ2ZSI6M31dLFsxNSwxNiwibW9kIiwxXSxbMTYsMTcsInJvdGw5IiwxXSxbMTcsMTgsImJ1aWxkeG9yMiIsMV0sWzEsMTgsImJ1aWxkeG9yMiIsMSx7ImN1cnZlIjo1fV0sWzE4LDE5LCJ4b3IiLDFdLFs5LDIwLCJidWlsZG1vZDEiLDFdLFsxNCwyMCwiYnVpbGRtb2QxIiwxLHsiY3VydmUiOi01fV0sWzIwLDIxLCJtb2QiLDFdLFsyMSwyMiwicm90bDciLDFdLFsyMiwyMywiYnVpbGR4b3IxIiwxXSxbNCwyMywiYnVpbGR4b3IxIiwxLHsiY3VydmUiOjV9XSxbMjMsMjQsInhvciIsMV0sWzI0LDI1LCJxdWFydGVycm91bmReey0xfSIsMSx7ImN1cnZlIjozLCJjb2xvdXIiOlsyNDAsNjAsNjBdfSxbMjQwLDYwLDYwLDFdXSxbMTksMjUsInF1YXJ0ZXJyb3VuZF57LTF9IiwxLHsiY3VydmUiOi0zLCJjb2xvdXIiOlsyNDAsNjAsNjBdfSxbMjQwLDYwLDYwLDFdXSxbOSwyNSwicXVhcnRlcnJvdW5kXnstMX0iLDEseyJjdXJ2ZSI6LTMsImNvbG91ciI6WzI0MCw2MCw2MF19LFsyNDAsNjAsNjAsMV1dLFsxNCwyNSwicXVhcnRlcnJvdW5kXnstMX0iLDEseyJjdXJ2ZSI6LTEsImNvbG91ciI6WzI0MCw2MCw2MF19LFsyNDAsNjAsNjAsMV1dXQ==)

-/

/-- Return `x0` given an input vector `(x0, x1, x2, x3)`. -/
@[simp] def first : vecType → bitvec word_len
| input := input.fst

/-- Return `x1` given an input vector `(x0, x1, x2, x3)`. -/
@[simp] def second : vecType → bitvec word_len
| input := input.snd.fst

/-- Return `x2` given an input vector `(x0, x1, x2, x3)`. -/
@[simp] def third : vecType → bitvec word_len
| input := input.snd.snd.fst

/-- Return `x3` given an input vector `(x0, x1, x2, x3)`. -/
@[simp] def fourth : vecType → bitvec word_len
| input := input.snd.snd.snd

/-!
## Quarterround construction

-/

/-- Return `(y0, y3)` given an input vector `(y0, y1, y2, y3)`. -/
@[simp] def buildmod1 : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input _ := (first input, fourth input)

/-- Return `(y1, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
@[simp] def buildxor1 : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input b := (second input, b)

/-- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7) -/
@[simp] def z1 (input : vecType) := ↾ buildmod1 input ≫ mod ≫ rotl7 ≫ buildxor1 input ≫ xor

/-- `z1` of `(0, 0, 0, 0)` is `0` -/
@[simp] lemma z1_zero : z1 (0, 0, 0, 0) 0 = 0 := by refl

/-- Return `(z1, y0)` given an input vector `(y0, y1, y2, y3)` and `z1`. -/
@[simp] def buildmod2 : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input z1 := (z1, first input)

/-- Return `(y2, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
@[simp] def buildxor2 : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input b := (third input, b)

/-- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9) -/
@[simp] def z2 (input : vecType) := ↾ buildmod2 input ≫ mod ≫ rotl9 ≫ buildxor2 input ≫ xor

/-- `z2` of `(0, 0, 0, 0)` is `0` -/
@[simp] lemma z2_zero : z2 (0, 0, 0, 0) 0 = 0 := by refl

/-- Return `(z2, z1)` given an input vector `(y0, y1, y2, y3)`, `z2` and `z1`. -/
@[simp] def buildmod3 : vecType → bitvec word_len → bitvec word_len → bitvec word_len × bitvec word_len
| input z2 z1 := (z2, z1)

/-- Return `(y3, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
@[simp] def buildxor3 : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input b := (fourth input, b)

/-- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13) -/
@[simp] def z3 (input : vecType) := 
  ↾ buildmod3 input (z2 input (z1 input (bitvec.zero word_len))) ≫ mod ≫ rotl13 ≫ buildxor3 input ≫ xor

/-- `z3` of `(0, 0, 0, 0)` is `0` -/
@[simp] lemma z3_zero : z3 (0, 0, 0, 0) 0 = 0 := by refl

/-- Return `(z3, z2)` given an input vector `(y0, y1, y2, y3)`, `z3` and `z2`. -/
@[simp] def buildmod0 : vecType → bitvec word_len → bitvec word_len → bitvec word_len × bitvec word_len
| input z3 z2 := (z3 , z2)

/-- Return `(y0, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
@[simp] def buildxor0 : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input b := (first input, b)

/-- z₀ = y₀ ⊕ ((z₃ + z₂) <<< 18) -/
@[simp] def z0 (input : vecType) := 
  ↾ buildmod0 input (z2 input (z1 input (bitvec.zero word_len))) ≫ mod ≫ rotl18 ≫ buildxor0 input ≫ xor

/-- `z0` of `(0, 0, 0, 0)` is `0` -/
@[simp] lemma z0_zero : z0 (0, 0, 0, 0) 0 = 0 := by refl

/- The full quarterround output built from its components in index order. -/
@[simp] def quarterround (input : vecType) := (
  z0 input (z3 input (z1 input 0)),
  z1 input 0,
  z2 input (z1 input 0),
  z3 input (z1 input 0)
)

/-- `quarterround` of `(0, 0, 0, 0)` is `(0, 0, 0, 0)` -/
@[simp] lemma quarterround_zero : quarterround (0, 0, 0, 0) = (0, 0, 0, 0) := by refl

/-!
## Inverse construction
-/

/-- Return `(z2, z3)` given an input vector `(z0, z1, z2, z3)`. -/
def buildmod0' : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input _ := (third input, fourth input)

/-- y₀ = z₀ ⊕ ((z₃ + z₂) <<< 18) -/
def y0 (input : vecType) := ↾ buildmod0' input ≫ mod ≫ rotl18 ≫ ↾ buildxor0 input ≫ xor

/-- `y0` of `(0, 0, 0, 0)` is `0` -/
@[simp] lemma y0_zero : y0 (0, 0, 0, 0) 0 = 0 := by refl

/-- Return `(z2, z1)` given an input vector `(z0, z1, z2, z3)`. -/
def buildmod3' : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input _ := (third input, second input)

/-- y₃ = z₃ ⊕ ((z₂ + z₁) <<< 13) -/
def y3 (input : vecType) := ↾ buildmod3' input ≫ mod ≫ rotl13 ≫ ↾ buildxor3 input ≫ xor

/-- `y3` of `(0, 0, 0, 0)` is `0` -/
@[simp] lemma y3_zero : y3 (0, 0, 0, 0) 0 = 0 := by refl

/-- Return `(z1, y0)` given an input vector `(z0, z1, z2, z3)` and `y0`. -/
def buildmod2' : vecType → bitvec word_len → bitvec word_len × bitvec word_len
| input y0 := (second input, y0)

/-- y₂ = z₂ ⊕ ((z₁ + y₀) <<< 9) -/
def y2 (input : vecType) := ↾ buildmod2' input ≫ mod ≫ rotl9 ≫ ↾ buildxor2 input ≫ xor

/-- `y2` of `(0, 0, 0, 0)` is `0` -/
@[simp] lemma y2_zero : y2 (0, 0, 0, 0) 0 = 0 := by refl

/-- Return `(y0, y3)` given an input vector `(z0, z1, z2, z3)`, `y0` and `y3`. -/
def buildmod1' : vecType → bitvec word_len → bitvec word_len → bitvec word_len × bitvec word_len
| input y0 y3 := (y0, y3)

/-- y₁ = z₁ ⊕ ((y₀ + y₃) <<< 7) -/
def y1 (input : vecType) := (↾ buildmod1' input (y0 input (bitvec.zero word_len))) ≫ mod ≫ rotl7 ≫ (↾ buildxor1 input) ≫ xor

/-- `y1` of `(0, 0, 0, 0)` is `0` -/
@[simp] lemma y1_zero : y1 (0, 0, 0, 0) 0 = 0 := by refl

/- The full quarterround⁻¹ output built from its components in index order. -/
def quarterround_inv (input : vecType) := (
  y0 input 0,
  y1 input (y0 input (y3 input 0)),
  y2 input (y0 input 0),
  y3 input 0
)

local notation `quarterround⁻¹` := quarterround_inv

/-- `quarterround⁻¹` of `(0, 0, 0, 0)` is `(0, 0, 0, 0)` -/
lemma quarterround_inv_zero : quarterround⁻¹ (0, 0, 0, 0) = 0 := by refl

/-!
## Isomorphisms
-/


/- The `quarterround` operation is invertible. -/
lemma quarterround_is_inv (input : vecType) (I : quarterround ≅ quarterround⁻¹) : I.hom ≫ I.inv = 𝟙 quarterround :=
  by rw [iso.hom_inv_id]

/- `z1` has an inverse and this inverse is `y1`. -/
lemma z1_is_inv (I : z1 ≅ y1) : I.hom ≫ I.inv = 𝟙 z1 := by rw [iso.hom_inv_id]

/- `z2` has an inverse and this inverse is `y2`. -/
lemma z2_is_inv (I : z2 ≅ y2) : I.hom ≫ I.inv = 𝟙 z2 := by rw [iso.hom_inv_id]

/- `z3` has an inverse and this inverse is `y3`. -/
lemma z3_is_inv (I : z3 ≅ y3) : I.hom ≫ I.inv = 𝟙 z3 := by rw [iso.hom_inv_id]

/- `z0` has an inverse and this inverse is `y0`. -/
lemma z0_is_inv (I : z0 ≅ y0) : I.hom ≫ I.inv = 𝟙 z0 := by rw [iso.hom_inv_id]

/- The `quarterround⁻¹` operation is invertible. -/
lemma quarterround_inv_is_inv (input : vecType) (I : quarterround⁻¹ ≅ quarterround) : I.hom ≫ I.inv = 𝟙 quarterround⁻¹ :=
  by rw [iso.hom_inv_id]

/- `y0` has an inverse and this inverse is `z0`. -/
lemma y0_is_inv (I : y0 ≅ z0) : I.hom ≫ I.inv = 𝟙 y0 := by rw [iso.hom_inv_id]

/- `y2` has an inverse and this inverse is `z2`. -/
lemma y2_is_inv (I : y2 ≅ z2) : I.hom ≫ I.inv = 𝟙 y2 := by rw [iso.hom_inv_id]

/- `y3` has an inverse and this inverse is `z3`. -/
lemma y3_is_inv (I : y3 ≅ z3) : I.hom ≫ I.inv = 𝟙 y3 := by rw [iso.hom_inv_id]

/- `y1` has an inverse and this inverse is `z1`. -/
lemma y1_is_inv (I : y1 ≅ z1) : I.hom ≫ I.inv = 𝟙 y1 := by rw [iso.hom_inv_id]


end quarterround
