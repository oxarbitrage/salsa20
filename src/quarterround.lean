import operations

open category_theory
open_locale category_theory.Type

open operations
open params
open types


namespace quarterround

/-- We have 2 categories, the single bitvectors (`wordType`) and the product of 4 of them (`vecType`). -/
variables [category (wordType)] [category (vecType)]

/-!
# Quarter round

The `quarterround` function takes `vecType` and return a new `vecType` after appliying the quarterround 
diagram.

- [Quarterround Diagram](https://oxarbitrage.github.io/salsa20-docs/diagrams/quarterround.html)

-/

/-- There is a functor between `vecType` and `wordType`. -/
variables (F : vecType ⥤ wordType)

/-- Return `(x0, 1, 1, 1)` given an input vector `(x0, x1, x2, x3)`. -/
@[simp] def first_f : vecType → vecType
| input := (input.fst, 1, 1, 1)

/-- Get the first object of the `vecType` product. -/
@[simp] def first (input : vecType) := F.obj (first_f input)
 
/-- Given `(input, 1, 1, 1)` it is safe for us to ignore all the ones and return just `input` as this is a product. -/
constant shrink (input: wordType) : F.obj (input, 1, 1, 1) = input

/-- -/
lemma just_first (input: wordType) : first F (input, 1, 1, 1) = input :=
begin
  norm_num,
  rw shrink,
end

@[simp] def id_wordType := 𝟙 wordType

/-- Given `a`, `b`, `c` and `d` objects of the `wordType` category:
- Form `(a, b, c, d)` in the `vecType` category. 
- The first element of `(a, b, c, d)` in the `vecType` category correspond to `a` in the `wordType` one.  -/
lemma first_shrink (a b c d : wordType) : (first F) (a, b, c, d) = id_wordType a :=
begin
  simp only [first, id_wordType, first_f, types_id_apply],
  apply just_first,
end

/-- Return `(x1, 1, 1, 1)` given an input vector `(x0, x1, x2, x3)`. -/
@[simp] def second_f : vecType → vecType
| input := (input.snd.fst, 1, 1, 1)

/-- Get the second object of the `vecType` product. -/
@[simp] def second (input : vecType) := F.obj (second_f input)

/-- -/
lemma just_second (input: wordType) : second F (1, input, 1, 1) = input :=
begin
  norm_num,
  rw shrink,
end

/-- Given `a`, `b`, `c` and `d` objects of the `wordType` category:
- Form `(a, b, c, d)` in the `vecType` category. 
- The second element of `(a, b, c, d)` in the `vecType` category correspond to `b` in the `wordType` one.  -/
lemma second_shrink (a b c d : wordType) : (second F) (a, b, c, d) = id_wordType b :=
begin
simp only [second, id_wordType, second_f, types_id_apply],
  apply just_second,
end

/-- Return `(x2, 0, 0, 0)` given an input vector `(x0, x1, x2, x3)`. -/
def third_f : vecType → vecType
| input := (input.snd.snd.fst, 0, 0, 0)

/-- Get the third object of the `vecType` product. -/
def third (input : vecType) := F.obj (third_f input)

/-- Return `(x3, 0, 0, 0)` given an input vector `(x0, x1, x2, x3)`. -/
def fourth_f : vecType → vecType
| input := (input.snd.snd.snd, 0, 0, 0)

/-- Get the fourth object of the `vecType` product. -/
def fourth (input : vecType) := F.obj (third_f input)

/-- Return `(y0, y3)` given an input vector `(y0, y1, y2, y3)` and a `wordType` that in this case 
will be ignored but it is here to be compatible with other buildmod functions. -/
def buildmod1 : vecType → wordType → wordType × wordType
| input _ := (first F input, fourth F input)

/-- Return `(y1, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor1 : vecType → wordType → wordType × wordType
| input b := (second F input, b)

/-- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7) -/
def z1 (input : vecType) := ↾ buildmod1 F input ≫ mod ≫ rotl7 ≫ buildxor1 F input ≫ xor

/-- Return `(z1, y0)` given an input vector `(y0, y1, y2, y3)` and `z1`. -/
def buildmod2 : vecType → wordType → wordType × wordType
| input z1 := (z1, first F input)

/-- Return `(y2, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor2 : vecType → wordType → wordType × wordType
| input b := (third F input, b)

/-- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9) -/
def z2 (input : vecType) := ↾ buildmod2 F input ≫ mod ≫ rotl9 ≫ buildxor2 F input ≫ xor

/-- Return `(z2, z1)` given an input vector `(y0, y1, y2, y3)`, `z2` and `z1`. -/
def buildmod3 : vecType → wordType → wordType → wordType × wordType
| input z2 z1 := (z2, z1)

/-- Return `(y3, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor3 : vecType → wordType → wordType × wordType
| input b := (fourth F input, b)

/-- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13) -/
def z3 (input : vecType) :=
  ↾ buildmod3 input (z2 F input (z1 F input (bitvec.zero word_len))) ≫ mod ≫ rotl13 ≫ buildxor3 F input ≫ xor

/-- Return `(z3, z2)` given an input vector `(y0, y1, y2, y3)`, `z3` and `z2`. -/
def buildmod0 : vecType → wordType → wordType → wordType × wordType
| input z3 z2 := (z3 , z2)

/-- Return `(y0, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor0 : vecType → wordType → wordType × wordType
| input b := (first F input, b)

/-- z₀ = y₀ ⊕ ((z₃ + z₂) <<< 18) -/
def z0 (input : vecType) := 
  ↾ buildmod0 input (z2 F input (z1 F input (bitvec.zero word_len))) ≫ mod ≫ rotl18 ≫ buildxor0 F input ≫ xor

/- The full quarterround output built from its components in index order. -/
def quarterround (input : vecType) := (
  z0 F input (z3 F input (z1 F input 0)),
  z1 F input 0,
  z2 F input (z1 F input 0),
  z3 F input (z1 F input 0)
)

-- The `quarterround` function has an inverse.
variable [is_iso (↾ quarterround F)]

/- `quarterround⁻¹` is the inverse function given `quarterround` is isomorphic. -/
noncomputable def quarterround_inv := inv ↾ quarterround F

local notation `quarterround⁻¹` := quarterround_inv

/-- `quarterround` and `quarterround⁻¹` are isomorphic. -/
variable I : quarterround F ≅ quarterround_inv F

/-- `quarterround` followed by `quarterround⁻¹` is the identity, so `quarterround⁻¹` is the inverse. -/
lemma is_inverse : I.hom ≫ I.inv = 𝟙 (quarterround F) := by rw [iso.hom_inv_id]

end quarterround
