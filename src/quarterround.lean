import operations

open category_theory
open_locale category_theory.Type

open operations
open params
open types


namespace quarterround

variables [category (wordType)]

/-!
# Quarter round

The `quarterround` function takes `vecType` (1 by 4 matrix) and return a new `vecType`
after appliying the quarterround diagram.

- [Quarterround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/quarterround.html)

-/

/-- Return `x0` given an input vector `(x0, x1, x2, x3)`. -/
def first : vecType → wordType
| input := input 0 0

/-- Return `x1` given an input vector `(x0, x1, x2, x3)`. -/
def second : vecType → wordType
| input := input 0 1

/-- Return `x2` given an input vector `(x0, x1, x2, x3)`. -/
def third : vecType → wordType
| input := input 0 2

/-- Return `x3` given an input vector `(x0, x1, x2, x3)`. -/
def fourth : vecType → wordType
| input := input 0 3

/-- Return `(y0, y3)` given an input vector `(y0, y1, y2, y3)` and a `wordType` that in this case 
will be ignored but it is here to be compatible with other buildmod functions. -/
def buildmod1 : vecType → wordType → wordType × wordType
| input _ := (first input, fourth input)

/-- Return `(y1, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor1 : vecType → wordType → wordType × wordType
| input b := (second input, b)

/-- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7) -/
def z1 (input : vecType) := ↾ buildmod1 input ≫ mod ≫ rotl7 ≫ buildxor1 input ≫ xor

/-- `z1` of `(0, 0, 0, 0)` is `0` -/
lemma z1_zero : z1 !![0, 0, 0, 0] 0 = 0 := by refl

/-- Return `(z1, y0)` given an input vector `(y0, y1, y2, y3)` and `z1`. -/
def buildmod2 : vecType → wordType → wordType × wordType
| input z1 := (z1, first input)

/-- Return `(y2, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor2 : vecType → wordType → wordType × wordType
| input b := (third input, b)

/-- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9) -/
def z2 (input : vecType) := ↾ buildmod2 input ≫ mod ≫ rotl9 ≫ buildxor2 input ≫ xor

/-- `z2` of `(0, 0, 0, 0)` is `0` -/
lemma z2_zero : z2 !![0, 0, 0, 0] 0 = 0 := by refl

/-- Return `(z2, z1)` given an input vector `(y0, y1, y2, y3)`, `z2` and `z1`. -/
def buildmod3 : vecType → wordType → wordType → wordType × wordType
| input z2 z1 := (z2, z1)

/-- Return `(y3, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor3 : vecType → wordType → wordType × wordType
| input b := (fourth input, b)

/-- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13) -/
def z3 (input : vecType) :=
  ↾ buildmod3 input (z2 input (z1 input (bitvec.zero word_len))) ≫ mod ≫ rotl13 ≫ buildxor3 input ≫ xor

/-- `z3` of `(0, 0, 0, 0)` is `0` -/
lemma z3_zero : z3 !![0, 0, 0, 0] 0 = 0 := by refl

/-- Return `(z3, z2)` given an input vector `(y0, y1, y2, y3)`, `z3` and `z2`. -/
def buildmod0 : vecType → wordType → wordType → wordType × wordType
| input z3 z2 := (z3 , z2)

/-- Return `(y0, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor0 : vecType → wordType → wordType × wordType
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

-- The `quarterround` function has an inverse.
variable [is_iso (↾ quarterround)]

/- `quarterround⁻¹` is the inverse function given `quarterround` is isomorphic. -/
noncomputable def quarterround_inv := inv ↾ quarterround

local notation `quarterround⁻¹` := quarterround_inv

/-- Vector is a category -/
variable [category (matrix (fin 1) (fin 4) wordType)]

/-- `quarterround` and `quarterround⁻¹` are isomorphic when fed with same `input`. -/
variable I : quarterround ≅ quarterround_inv

/-- `quarterround` followed by `quarterround⁻¹` is the identity, so `quarterround⁻¹` is the inverse. -/
lemma is_inverse : I.hom ≫ I.inv = 𝟙 quarterround := by rw [iso.hom_inv_id]

end quarterround
