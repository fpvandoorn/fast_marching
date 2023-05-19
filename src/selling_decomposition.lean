import linear_algebra.matrix.pos_def
import data.complex.basic
import preliminaries
open nat

/--
Following appendix B of the paper
A LINEAR FINITE-DIFFERENCE SCHEME FOR APPROXIMATING RANDERS
DISTANCES ON CARTESIAN GRIDS

It is likely useful to adapt the statements a little bit, to be a bit more flexible about the
type in which we consider these operations, so that the coefficients in `D` and `v` live in the same
type (`ℝ`) for most of the argument. We can still construct a superbase in `ℤ` at the end.
leanproject get mathematics_in_lean
example

-/
variables {d : ℕ} {R : Type*} [linear_ordered_comm_ring R]

noncomputable theory
open matrix finset
open_locale classical big_operators matrix

/-- The Kronecker-delta `δᵢⱼ` as an element of `E`. -/
def kronecker_delta (E) [has_zero E] [has_one E] {ι} (i j : ι) : E :=
if i = j then (1 : E) else (0 : E)

/-- def B.1 -/
def is_superbase (v : matrix (fin (d+1)) (fin d) R) : Prop :=
∑ i, v i = 0 ∧ |(v.submatrix fin.succ id).det| = 1

-- begin scratchpad
example (v : matrix (fin (d+1)) (fin d) R) : ∑ i, (fun j, v j i) = 0 :=
begin
  sorry
end

def is_integer (r : ℝ) := ∃ n : ℤ, r = n

example (n m : ℕ) : 10^5 + 10^5 = 2 * 10^5 :=
begin
  norm_num,
end
-- end scratchpad

/- Example 1: show that `((-1,-1), (1, 0), (0, 1))` is a superbase. -/
example : is_superbase !![(-1 : ℤ), -1; 1, 0; 0, 1] :=
begin
  simp only [is_superbase],
  split,
  { ext,
    fin_cases x, refl, refl, },
  refl,

end

/- Lemma: if `(e₀, e₁, e₂)` is a superbase, then so is `(- e₀, e₁, e₀ - e₁)`. -/

lemma exercise (e : matrix (fin 3) (fin 2) R) (he : is_superbase e) :
  is_superbase ![- e 0, e 1, e 0 - e 1] :=
begin
  simp only [is_superbase],
  split,
  {simp},
  have h: e 0 - e 1 = -2 * e 1 - e 2,
  {begin
    sorry
  end},
rw det_fin_two,
rw h,
simp,
unfold is_superbase at he,
rw det_fin_two at he,
simp at he,
rw ← he.2,
ring_nf,
rw abs_eq_abs,
right,
ring,
end


#check @function.funext_iff

lemma exercise_part_one (e : matrix (fin 3) (fin 2) R) (he : is_superbase e) :
  e 0 = - e 1 - e 2 :=

  begin
    have h:=he.1,
    simp at h,
    have h2 : univ.sum e = e 0 + e 1 + e 2,
    {rw fin.sum_univ_def,simp[sum_range_succ],
    have m: list.fin_range 3 = [0,1,2],
    refl,rw m,simp,rw add_assoc,},
    rw h2 at h,
    rw [← sub_zero (e 2), ← h],
    ring,
    rw function.funext_iff at h,
    simp at h,
    ext,
    have := h x,
    simp, 
    linarith,
  end

lemma exercise_lemma (e : matrix (fin 4) (fin 3) R) (he : is_superbase e) :
  univ.sum e = e 0 + (e 1 + (e 2 + e 3)) :=
  begin
    rw fin.sum_univ_def,simp[sum_range_succ],
    have m : list.fin_range 4 = [0,1,2,3],
    refl, rw m,simp,
  end

lemma fin_two_simp :
  fin.succ (2 : fin 3) = 3 :=
  begin
    refl,
  end
#check fin_two_simp
lemma exercise_bis (e : matrix (fin 4) (fin 3) R) (he : is_superbase e) :
  is_superbase ![- e 0, e 1, e 2 + e 0, e 3 + e 0] :=

  begin
    simp only [is_superbase],
    split,
    {simp,
    ring,
    have h : univ.sum e = e 0 + (e 1 + (e 2 + e 3)),
    apply exercise_lemma,
    apply he,
    rw ← h,
    apply he.1,
    },
    rw det_fin_three,
    have g : e 1 = - e 0 - e 2 - e 3,
    {have k:= exercise_lemma e he,
    have h:=he.1,
    rw k at h,
    rw [← sub_zero (e 0),←h ],
    ring,
    },
    rw g,
    simp,
    unfold is_superbase at he,
    rw det_fin_three at he,
    simp at he,
    have h:=he.2,
    rw ← he.2,
    rw fin_two_simp,
    
    --rw e 2.succ 0 at h,
    --rw [nat.succ 2, nat.succ 1, nat.succ 0],
    rw abs_eq_abs,
    rw g,
    right,
    simp,
    simp [add_mul,mul_add,sub_mul,mul_sub],
    linarith,



  end

#check [0,1,1].succ 0

/-- def B.1 -/
def is_obtuse (v : matrix (fin (d+1)) (fin d) R) (D : matrix (fin d) (fin d) R) : Prop :=
∀ i j : fin (d+1), i < j → v i ⬝ᵥ D.mul_vec (v j) ≤ 0


section Z_or_R
/-! In this section we work in any linear ordered ring, so we can use it for both `ℤ` and `ℝ`. -/



example {D : matrix (fin d) (fin d) ℝ} (Dposdef : D.pos_def) : 0 < D.det := Dposdef.det_pos

/-- The definition of the norm D ; careful, vector taken not superbase-/

def norm_D (v : matrix (fin d) unit R) (D : matrix (fin d) (fin d) R) := (transpose (v)).mul(D.mul v)


variables {A : matrix (fin d) (fin d) R} {B : matrix (fin d) (fin d) R}{C : fin d → R}
#check(vec_mul_mul_vec C A)


def E_D (v : matrix (fin (d+1)) (fin d) R) (D : matrix (fin d) (fin d) R) := ∑ i , norm_D (matrix.col (v i)) (D)

lemma mul_add_col (v : matrix (fin 3) (fin 2) R) (D : matrix (fin d) (fin 2) R) (i : nat)(j : nat): 
  D ⬝ (col (v i) + col (v j)) = D.mul(col (v i)) + D.mul(col (v j)) :=
  begin
    apply matrix.mul_add,
  end

lemma add_mul_row (v : matrix (fin 3) (fin 2) R) (D : matrix (fin 2) (fin d) R) (i : nat)(j : nat): 
  (row (v i) + row (v j)).mul D = (row (v i)).mul D + (row(v j)).mul D :=
  begin
    apply matrix.add_mul,
  end





lemma E_D_superbase (v : matrix (fin 3) (fin 2) R) (D : matrix (fin 2) (fin 2) R) (he : is_superbase v) :
  E_D (![- v 0, v 1, v 0 - v 1]) (D) = E_D(v) (D) - 4 * (transpose (matrix.col (v 0))).mul(D.mul (matrix.col (v 1))) :=
  begin
    unfold E_D,
    ring_nf,
    unfold norm_D,
    rw exercise_part_one (v) (he),
    --have g := (col (![-(-v 1 - v 2), v 1, -v 1 - v 2 - v 1] x))ᵀ ⬝ (D ⬝ col (![-(-v 1 - v 2), v 1, -v 1 - v 2 - v 1] x)),
    have h2 : univ.sum v = v 0 + v 1 + v 2,
    {rw fin.sum_univ_def,simp[sum_range_succ],
    have m: list.fin_range 3 = [0,1,2],
    refl,rw m,simp only [list.sum_cons, add_zero, list.sum_nil, list.map.equations._eqn_2, list.map_nil],rw add_assoc,},
    rw fin.sum_univ_def,
    rw fin.sum_univ_def,
    simp only [neg_sub, sub_neg_eq_add, transpose_col, mul_eq_mul],
    have m: list.fin_range 3 = [0,1,2],
    refl,
    rw m,
    simp,
    ring_nf,
    have m1 : D ⬝ (col (v 2) + col (v 1)) = D.mul(col (v 2)) + D.mul(col (v 1)),
    {apply mul_add_col,},
    rw m1,
    have H := (D ⬝ col (v 2) + D ⬝ col (v 1)),
    have m2 : (row (v 2) + row (v 1)).mul((D ⬝ col (v 2) + D ⬝ col (v 1)))= (row (v 2)).mul((D ⬝ col (v 2) + D ⬝ col (v 1))) + (row (v 1)).mul((D ⬝ col (v 2) + D ⬝ col (v 1))),
    {apply add_mul_row,},
    rw m2,
    apply mul_add_col,
    have m3 : row (v 2) ⬝ (D ⬝ col (v 2) + D ⬝ col (v 1)) + row (v 1) ⬝ (D ⬝ col (v 2) + D ⬝ col (v 1)) + (row (v 1) ⬝ (D ⬝ col (v 1)) + row (-(2 * v 1) - v 2) ⬝ (D ⬝ col (-(2 * v 1) - v 2))) = row (v 2).mul(D ⬝ col (v 2)) + row (v 2).mul(D ⬝ col (v 1)) + row (v 1) ⬝ (D ⬝ col (v 2)) + row (v 1) ⬝ D ⬝ col (v 1) + (row (v 1) ⬝ (D ⬝ col (v 1)) + row (-(2 * v 1) - v 2) ⬝ (D ⬝ col (-(2 * v 1) - v 2))),
    {repeat {apply mul_add_col,},}


  end 

/-- second try with vectors-/

lemma exercise_part_one_var (e : matrix (fin 3) (fin 2) R) (he : is_superbase e) :
  e 2 = - e 0 - e 1 :=

  begin
    have h:=he.1,
    simp at h,
    have h2 : univ.sum e = e 0 + e 1 + e 2,
    {rw fin.sum_univ_def,simp[sum_range_succ],
    have m: list.fin_range 3 = [0,1,2],
    refl,rw m,simp,rw add_assoc,},
    rw h2 at h,
    rw [← sub_zero (e 2), ← h],
    ring,
  end

def norm_D_vec (v : fin d → R) (D : matrix (fin d) (fin d) R) := v ⬝ᵥ mul_vec D v
def E_D_vec (v : matrix (fin (d+1)) (fin d) R) (D : matrix (fin d) (fin d) R) := ∑ i , norm_D_vec (v i) (D)

lemma E_D_superbase_vec (v : matrix (fin 3) (fin 2) R) (D : matrix (fin 2) (fin 2) R) (he : is_superbase v) (hd : D.is_symm):
  E_D_vec (![- v 0, v 1, v 0 - v 1]) (D) = E_D_vec(v) (D) - 4 * v 0 ⬝ᵥ mul_vec D (v 1 ):=
  begin
    unfold E_D_vec,
    rw sum_fin_three,
    rw sum_fin_three,
    simp only [matrix.head_cons,
 list.sum_cons,
 add_zero,
 list.sum_nil,
 matrix.cons_vec_bit0_eq_alt0,
 list.map.equations._eqn_2,
 matrix.empty_vec_alt0,
 matrix.vec2_dot_product,
 list.map_nil,
 matrix.empty_vec_append,
 matrix.cons_val_one,
 matrix.cons_vec_append,
 matrix.cons_vec_alt0,
 matrix.cons_val_zero],
    rw exercise_part_one_var (v) (he),
    unfold norm_D_vec,
    simp only [neg_mul, matrix.vec2_dot_product, pi.neg_apply, pi.sub_apply],
    unfold mul_vec,
    simp only [matrix.vec2_dot_product, pi.neg_apply, mul_neg, pi.sub_apply],
    rw hd.apply 1 0,
    ring,


  end 
def k_i_j (i j : fin(3)) (he : (i : ℕ )  ≠ (j : ℕ) ) : fin (3) := 
begin
  refine ⟨ (3 - (i : ℕ ) - (j : ℕ )) , _⟩ ,
  by_contra,
  simp at h,
  rw nat.sub_sub at h,
  simp at h,
  
end
lemma zero_un :
  ¬ 0 = 1 := 
  by sorry
#check (k_i_j (0.fin(3) 1.fin(3))(zero_un))

/-- The definition of the `e_{i,j}` -/
def associated_vectors (v : matrix (fin (3)) (fin 2) R) (i j : fin (3)) : fin 2 → R := 
if h : i = j then 0 else 
let k := third_element i j h in 
![- v k 1, v k 0]

variables {v : matrix (fin (3)) (fin 2) R} {D : matrix (fin 2) (fin 2) R}
/- to check normalization and sign-/
local notation `e` := associated_vectors v

lemma associated_vectors_def (i j k : fin (3)) (hij : i < j) :
  e i j ⬝ᵥ v k = kronecker_delta R i k - kronecker_delta R j k :=
  begin
  fin_cases i;
  fin_cases j,
  all_goals{norm_num at hij},
  fin_cases k,
  norm_num,
  unfold kronecker_delta,
  unfold associated_vectors,
  norm_num,
  
    
  end

/-- Lemma B.2. The right-hand side sums over all `i` and all `j > i`. -/
lemma selling_formula (vsb : is_superbase v) (Dsymm : D.is_symm) :
  D = - ∑ i, ∑ j in Ioi i, (v i ⬝ᵥ D.mul_vec (v j)) • vec_mul_vec (e i j) (e i j) :=
sorry


end Z_or_R

section real

variables {v : matrix (fin (d+1)) (fin d) ℝ} {D : matrix (fin d) (fin d) ℝ}

local notation `e` := associated_vectors v
local notation `Z` := set.range (coe : ℤ → ℝ)

/-- The Selling algorithm, position B.3.

Note that the current statement doesn't encode the precise algorithm used. To do this, we
should just define a sequence of matrices (separately for `d = 2` and `d = 3`)
and show that we reach one that satisfies the obtuseness.
-/
theorem selling_algorithm (vsb : is_superbase v) (vint : ∀ i j, v i j ∈ Z)
  (Dsymm : D.is_symm) (Dposdef : D.pos_def) (hd : d = 2 ∨ d = 3) :
  ∃ v' : matrix (fin (d+1)) (fin d) ℝ,
    is_superbase v' ∧ is_obtuse v' D ∧ ∀ i j, v' i j ∈ Z :=
sorry

end real