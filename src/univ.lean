import category_theory.core

namespace univ

/-!
# Universal property of the product

Taken from category theory : a framework for reasoning

for every set C and functions: f : C → A and g : C → B there is a unique function h : C → A × B such that:

triangles commute:

fst ∘ h = f 
snd ∘ h = g

so the idea is to replace sets by objects of a category and functions with morphisms.

lets do it for a single product of 2 pieces first:
-/

universe u

variables A B : Type u

variable AB : Type u

variable pi_a : AB ⟶ A
variable pi_b : AB ⟶ B

variable P : Type u

variable f : P ⟶ A

variable g : P ⟶ B

variable product_universal_property : ∃ unique h : P ⟶ AB, h ≫ pi_a = f ∧ h ≫ pi_b = g

/-!
Now lets try to do the same but with a 4-tuple product.
The idea is the same, just extend everything.
-/

variables C D : Type u

variable ABCD : Type u

variable pi_a' : ABCD ⟶ A
variable pi_b' : ABCD ⟶ B
variable pi_c' : ABCD ⟶ C
variable pi_d' : ABCD ⟶ D

variable f' : P ⟶ A
variable g' : P ⟶ B
variable h' : P ⟶ C
variable i' : P ⟶ D

variable tuple_universal_property : ∃ unique k : P ⟶ ABCD, k ≫ pi_a' = f' ∧ k ≫ pi_b' = g'
  ∧ k ≫ pi_c' = h' ∧ k ≫ pi_d' = i'


end univ
