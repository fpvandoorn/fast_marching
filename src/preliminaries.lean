-- begin header
import topology.instances.ereal
import algebra.big_operators.norm_num
import algebra.big_operators.fin
import tactic
import tactic.norm_fin
import analysis.calculus.fderiv
noncomputable theory
open topological_space partial_order finset matrix
open_locale big_operators

-- end

/- Some basic things that might be missing in mathlib -/

/- Allowing `≺` to be used in calc-proofs together  -/

variables {ι : Type*} {π : ι → Type*} [Π i, preorder (π i)] {a b c d e : Π i, π i}

attribute [trans] strong_lt.trans_le has_le.le.trans_strong_lt

local infix ` ≺ `:50 := strong_lt

@[trans] lemma strong_lt.trans_lt (hab : a ≺ b) (hbc : b < c) : a ≺ c :=
hab.trans_le hbc.le

@[trans] lemma strong_lt_of_lt_of_strong_lt (hab : a < b) (hbc : b ≺ c) : a ≺ c :=
hab.le.trans_strong_lt hbc

@[trans] lemma strong_lt.trans (hab : a ≺ b) (hbc : b ≺ c) : a ≺ c :=
hab.trans_le hbc.le

example (hab : a < b) (hbc : b ≺ c) (hcd : c ≺ d) (hde : d ≤ e) : a ≺ e :=
calc
    a < b : hab
  ... ≺ c : hbc
  ... ≺ d : hcd
  ... ≤ e : hde

/- A useful lemma about vector sums -/

@[simp]
lemma sum_vec_cons {n α} [add_comm_monoid α] (x : α) (f : fin n → α) :
  ∑ i, vec_cons x f i = x + ∑ i, f i :=
fin.sum_cons x f

example : (2 : fin 3).succ = 3 :=
by norm_fin

variables {α : Type*} [add_comm_monoid α]
lemma sum_fin_three (f : fin 3 → α) : ∑ i, f i = f 0 + f 1 + f 2 :=
by { norm_num, simp_rw [← add_assoc] }

@[simp] def third_element_aux (i j : fin 3) (h : i ≠ j) : {x : fin 3 | x ≠ i ∧ x ≠ j} :=
by { apply fintype.choose_x, revert i j, dsimp [exists_unique], dec_trivial }

@[simp] def third_element (i j : fin 3) (h : i ≠ j) : fin 3 := third_element_aux i j h
lemma third_element_ne_left (i j : fin 3) (h : i ≠ j) : third_element i j h ≠ i :=
(third_element_aux i j h).prop.1
lemma third_element_ne_right (i j : fin 3) (h : i ≠ j) : third_element i j h ≠ j :=
(third_element_aux i j h).prop.2

@[simp] lemma third_element_0_1 : third_element 0 1 (by norm_num) = 2 := rfl
@[simp] lemma third_element_0_2 : third_element 0 2 (by norm_num) = 1 := rfl
@[simp] lemma third_element_1_2 : third_element 1 2 (by norm_num) = 0 := rfl
@[simp] lemma third_element_1_0 : third_element 1 0 (by norm_num) = 2 := rfl
@[simp] lemma third_element_2_0 : third_element 2 0 (by norm_num) = 1 := rfl
@[simp] lemma third_element_2_1 : third_element 2 1 (by norm_num) = 0 := rfl

/- We could work with our own type, reals extended with infinity. -/

open with_top function
@[derive [nontrivial, comm_monoid_with_zero,
  has_Sup, has_Inf, add_comm_monoid_with_one, linear_ordered_add_comm_monoid_with_top,
  densely_ordered, has_sub, mul_zero_class]]
def real_with_infty := with_top ℝ

notation `ℝ∞` := real_with_infty
notation `∞` := ⊤

namespace real_with_infty

instance : has_coe ℝ ℝ∞ := ⟨some⟩

lemma coe_strict_mono : strict_mono (coe : ℝ → ℝ∞) :=
with_top.coe_strict_mono

lemma coe_injective : injective (coe : ℝ → ℝ∞) := coe_strict_mono.injective

@[simp, norm_cast] protected lemma coe_le_coe_iff {x y : ℝ} : (x : ℝ∞) ≤ (y : ℝ∞) ↔ x ≤ y :=
coe_strict_mono.le_iff_le
@[simp, norm_cast] protected lemma coe_lt_coe_iff {x y : ℝ} : (x : ℝ∞) < (y : ℝ∞) ↔ x < y :=
coe_strict_mono.lt_iff_lt
@[simp, norm_cast] protected lemma coe_eq_coe_iff {x y : ℝ} : (x : ℝ∞) = (y : ℝ∞) ↔ x = y :=
coe_injective.eq_iff

@[simp, norm_cast] lemma coe_add (x y : ℝ) : (↑(x + y) : ℝ∞) = x + y := rfl
@[simp, norm_cast] lemma coe_mul (x y : ℝ) : (↑(x * y) : ℝ∞) = x * y := with_top.coe_mul
@[norm_cast] lemma coe_nsmul (n : ℕ) (x : ℝ) : (↑(n • x) : ℝ∞) = n • x :=
map_nsmul (⟨coe, coe_zero, coe_add⟩ : ℝ →+ ℝ∞) _ _

@[simp, norm_cast] lemma coe_bit0 (x : ℝ) : (↑(bit0 x) : ℝ∞) = bit0 x := rfl
@[simp, norm_cast] lemma coe_bit1 (x : ℝ) : (↑(bit1 x) : ℝ∞) = bit1 x := rfl
@[simp, norm_cast] lemma coe_one (x : ℝ) : (↑(1 : ℝ) : ℝ∞) = 1 := rfl

@[simp, norm_cast] lemma coe_eq_zero {x : ℝ} : (x : ℝ∞) = 0 ↔ x = 0 :=
real_with_infty.coe_eq_coe_iff
@[simp, norm_cast] lemma coe_eq_one {x : ℝ} : (x : ℝ∞) = 1 ↔ x = 1 :=
real_with_infty.coe_eq_coe_iff

-- if we want to work with multiplication on `ℝ∞`, we have to make sure to not to multiply with
-- negative numbers, as the following examples show
example (x y : ℝ∞) : x * y = y * x := mul_comm x y
example (x : ℝ∞) (hx : x ≠ 0) : ∞ * x = ∞ := top_mul hx
example (x : ℝ∞) (hx : x ≠ 0) : x * ∞ = ∞ := mul_top hx

-- multiplication does not distribute over addition if we use negative numbers
example : ∞ * (((-1 : ℝ) : ℝ∞) + 1) ≠ ∞ * ((-1 : ℝ) : ℝ∞) + ∞ * 1 :=
begin
  norm_num,
  norm_cast,
  norm_num,
end

/- Note: we need to do some work if we want to prove lemmas about suprema and infima in this type.
-/

end real_with_infty
