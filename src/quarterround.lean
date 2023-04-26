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

/-- Return `(xᵢ, 1, 1, 1)` given an input vector `(x₀, x₁, x₂, x₃)` and a position `i`. -/
def value_at_position (input : vecType) (i : fin 3) : vecType :=
match i.val with
| 0 := (input.fst, 1, 1, 1)
| 1 := (input.snd.fst, 1, 1, 1)
| 2 := (input.snd.snd.fst, 1, 1, 1)
| 3 := (input.snd.snd.snd, 1, 1, 1)
| _ := (1, 1, 1, 1)
end

/-- Make `value_at_position` the functor morphism. -/
def value_at_functor (input : vecType) (pos : fin 3) := F.obj (value_at_position input pos)

/-- Given `(a, o, p, q)` it is safe for us to ignore `o`, `p`, `q` and return just `a`
if `value_at_position` was used, `o`, `p` and `q` will be all `1` (product identity). -/
constant shrink (a o p q: wordType) (pos : fin 3) : F.obj (value_at_position (a, o, p, q) pos) = a

/-- The identity in the `wordType` category. -/
def id_wordType := 𝟙 wordType

/-- Make sure `value_at_functor` just return the identity of the first number of the product in the `wordType` category. -/
lemma just_first (a : wordType) (pos : fin 3) : value_at_functor F (a, 1, 1, 1) pos = id_wordType a :=
begin
  rw [value_at_functor, id_wordType],
  norm_num,
  rw shrink,
end

/-- Return `(y0, y3)` given an input vector `(y0, y1, y2, y3)` and a `wordType` that in this case 
will be ignored but it is here to be compatible with other buildmod functions. -/
def buildmod1 : vecType → wordType → wordType × wordType
| input _ := (value_at_functor F input 0, value_at_functor F input 3)

/-- Return `(y1, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor1 : vecType → wordType → wordType × wordType
| input b := (value_at_functor F input 1, b)

/-- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7) -/
def z1 (input : vecType) := ↾ buildmod1 F input ≫ mod ≫ rotl7 ≫ buildxor1 F input ≫ xor

/-- Return `(z1, y0)` given an input vector `(y0, y1, y2, y3)` and `z1`. -/
def buildmod2 : vecType → wordType → wordType × wordType
| input z1 := (z1, value_at_functor F input 0)

/-- Return `(y2, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor2 : vecType → wordType → wordType × wordType
| input b := (value_at_functor F input 2, b)

/-- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9) -/
def z2 (input : vecType) := ↾ buildmod2 F input ≫ mod ≫ rotl9 ≫ buildxor2 F input ≫ xor

/-- Return `(z2, z1)` given an input vector `(y0, y1, y2, y3)`, `z2` and `z1`. -/
def buildmod3 : vecType → wordType → wordType → wordType × wordType
| input z2 z1 := (z2, z1)

/-- Return `(y3, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor3 : vecType → wordType → wordType × wordType
| input b := (value_at_functor F input 3, b)

/-- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13) -/
def z3 (input : vecType) :=
  ↾ buildmod3 input (z2 F input (z1 F input (bitvec.zero word_len))) ≫ mod ≫ rotl13 ≫ buildxor3 F input ≫ xor

/-- Return `(z3, z2)` given an input vector `(y0, y1, y2, y3)`, `z3` and `z2`. -/
def buildmod0 : vecType → wordType → wordType → wordType × wordType
| input z3 z2 := (z3 , z2)

/-- Return `(y0, rotlres)` given an input vector `(y0, y1, y2, y3)` and `rotlres`. -/
def buildxor0 : vecType → wordType → wordType × wordType
| input b := (value_at_functor F input 0, b)

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
