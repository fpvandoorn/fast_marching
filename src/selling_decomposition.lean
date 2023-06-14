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

def is_direct_superbase (v : matrix (fin (d+1)) (fin d) R) : Prop :=
∑ i, v i = 0 ∧ (v.submatrix fin.succ id).det = 1


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

def canonical_superbase : matrix (fin 2) (fin 3) ℤ := !![(-1 : ℤ ) , 1 , 0 ; - 1 , 0 , 1] 
def canonical_superbase_b : matrix (fin 2) (fin 3) ℤ := 
![ [(-1 : ℤ ) , - 1] , matrix.col ![(1 : ℤ ) , 0] ,matrix.col ![(0 : ℤ ) ,  1] ]

#check (!![1, 2 ; 3 , 4] )

lemma canonical_superbase_is_sb : is_direct_superbase canonical_superbase :=
begin
  simp only [is_direct_superbase],
  split,
  { ext,
    fin_cases x, refl, refl, },
  refl,

end
 /- Expression of a superbase with the canonical one-/

lemma superbase_with_canonical (e : matrix (fin 3) (fin 2) ℤ ) (he : is_direct_superbase e) :
  e = matrix.mul (!![e 1 0, e 1 1 ; e 2 0 , e 2 1] : matrix (fin 2) (fin 2) ℤ ) ( !![(-1 : ℤ ), 1, 0 ; - 1, 0, 1] : matrix (fin 2) (fin 3) ℤ ):=

example : (!![1, 2 ; 3 , 4]).mul (!![(-1 : ℤ ), 1, 0 ; - 1, 0, 1]) = !![- 3 , 1 , 2 ; - 7 , 3 , 4] :=
begin
  simp,
  norm_num,
end 

/- Lemma: if `(e₀, e₁, e₂)` is a superbase, then so is `(- e₀, e₁, e₀ - e₁)`. -/

lemma exercise (e : matrix (fin 3) (fin 2) R) (he : is_direct_superbase e) :
  is_direct_superbase ![e 1, - e 0, e 0 - e 1] :=
  begin
  sorry
  end


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

lemma exercise_part_one (e : matrix (fin 3) (fin 2) R) (he : is_direct_superbase e) :
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
    ring
  end


lemma exercise_part_one_v (e : matrix (fin 3) (fin 2) R) (he : is_superbase e) :
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


/-- essai non nécessaire pour la suite car nous avons trouvé un meilleur moyen-/

lemma E_D_superbase (v : matrix (fin 3) (fin 2) R) (D : matrix (fin 2) (fin 2) R) (he : is_superbase v) :
  E_D (![- v 0, v 1, v 0 - v 1]) (D) = E_D(v) (D) - 4 * (transpose (matrix.col (v 0))).mul(D.mul (matrix.col (v 1))) :=
  begin
    unfold E_D,
    ring_nf,
    unfold norm_D,
    rw exercise_part_one_v (v) (he),
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

lemma exercise_part_one_var (e : matrix (fin 3) (fin 2) R) (he : is_direct_superbase e) :
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
#check finset.min 
#check finset.min'
local notation `Z` := set.range (coe : ℤ → ℝ)
/--
Exercise : forall v0 : R^2 there exists v : Z^2 which minimizes |v-v0|
Desired proof : 
We can restrict our attention to v such that |v-v0|<=|0-v0|.
There are a finite number of them, so one is minimal.
--/
example (v₀ : fin 3 → ℝ) : ∃ v : fin 3 → ℝ, (∀ i, v i ∈ Z) ∧ ∀ v' : fin 3 → ℝ, (∀ i, v' i ∈ Z) →  
  ‖ v - v₀ ‖ ≤ ‖ v' - v₀ ‖ :=
begin




end

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


/-- The definition of the `e_{i,j}` with a direct superbase-/

def signature_perm_3 (l : list ℤ ) : ℤ :=
if l = [0,1,2] then 1 else 
if l = [0,2,1] then - 1 else
if l = [1,2,0] then 1 else
if l = [1,0,2] then - 1 else
if l = [2,0,1] then 1 else
- 1


def associated_vectors_direct (v : matrix (fin (3)) (fin 2) R) (i j : fin (3)) 
(he : is_direct_superbase v) : fin 2 → R := 
if h : i = j then 0 else
let k := third_element i j h 
in 
if g : signature_perm_3 ( [i,j,k]) = 1 then ![ - v k 1, v k 0] else ![  v k 1, - v k 0]

example : equiv.perm.sign (list.form_perm([(0:fin 3) ,1,2])) = 1 :=
begin
simp,norm_num,
end

example : equiv.perm.sign (list.form_perm([(0:fin 3),2,1])) = 1 :=
begin
simp,norm_num,
end

example : equiv.perm.sign (![(0:fin 3),2,1]) = 1 :=
begin
simp,norm_num,
end

#check equiv.perm


#check equiv.perm.sign (list.form_perm([0,1,2]))
/-- The definition of the `e_{i,j}` -/
def associated_vectors (v : matrix (fin (3)) (fin 2) R) (i j : fin (3)) (he : is_superbase v) : fin 2 → R := 
if h : i = j then 0 else
if (v.submatrix fin.succ id).det = 1 then
let k := third_element i j h in 
![ - v k 1, v k 0]
else 
let k := third_element i j h in 
![ v k 1, - v k 0]

variables {v : matrix (fin (3)) (fin 2) R} {D : matrix (fin 2) (fin 2) R}
/- to check normalization and sign-/
local notation `e` := associated_vectors_direct v
#check (associated_vectors v 0 1 )

/-- Lemma permutation of a superbase for d=2 -/

lemma superbase_permutation (v : matrix (fin 3) (fin 2) R) (he : is_superbase v) :
  is_superbase ![ v 2, v 0, v 1] :=
  begin
    split,
    norm_num,
    rw exercise_part_one_var (v) (he),
    simp only [sub_add_add_cancel, eq_self_iff_true, add_left_neg],
    rw det_fin_two,
    rw exercise_part_one (v) (he),
    unfold is_superbase at he,
    rw det_fin_two at he,
    simp,
    norm_num at he,
    ring_nf,
    rw mul_comm (v 2 1) (v 1 0),
    apply he.2,

  end

lemma associated_vectors_def (i j k : fin (3)) (hij : i < j)(vsb : is_direct_superbase v) :
  e i j vsb ⬝ᵥ v k = kronecker_delta R i k - kronecker_delta R j k :=
  begin
  fin_cases i;
  fin_cases j,
  all_goals{norm_num at hij},
  fin_cases k,
  {
  unfold kronecker_delta,
  unfold associated_vectors_direct,
  split_ifs,
  exfalso,
  simp only [nat.one_ne_zero, nat.bit1_eq_one, fin.zero_eq_one_iff] at h,
  apply h,
  norm_num at h,
  norm_num at h_2,
  simp only [tsub_zero,
 matrix.head_cons,
 neg_mul,
 matrix.vec2_dot_product,
 matrix.cons_val_one,
 third_element_0_1,
 matrix.cons_val_zero],
  rw exercise_part_one (v) (vsb),
  unfold is_direct_superbase at vsb,
  rw det_fin_two at vsb,
  simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'] at vsb,
  simp only [pi.neg_apply, pi.sub_apply],
  linarith,
  norm_num at h_2,
  simp only [tsub_zero,
 matrix.head_cons,
 neg_mul,
 matrix.vec2_dot_product,
 matrix.cons_val_one,
 third_element_0_1,
 matrix.cons_val_zero],
 norm_num at h_1,
  },
  {
  unfold kronecker_delta,
  unfold associated_vectors_direct,
  split_ifs,
  exfalso,
  simp only [nat.one_ne_zero, nat.bit1_eq_one, fin.zero_eq_one_iff] at h,
  apply h,
  norm_num at h,
  simp only [matrix.head_cons,
 neg_mul,
 matrix.vec2_dot_product,
 zero_sub,
 matrix.cons_val_one,
 third_element_0_1,
 matrix.cons_val_zero],
  unfold is_direct_superbase at vsb,
  rw det_fin_two at vsb,
  simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'] at vsb,
  linarith,
  norm_num at h_1,
  },
  {
  unfold kronecker_delta,
  unfold associated_vectors_direct,
  split_ifs,
  exfalso,
  repeat{
  simp only [nat.one_ne_zero, nat.bit1_eq_one, fin.zero_eq_one_iff] at h,
  apply h,},
  repeat{
  norm_num at h_2,},
  exfalso,
  simp only [nat.one_ne_zero, nat.bit1_eq_one, fin.zero_eq_one_iff] at h,
  apply h,
  exfalso,
  simp only [nat.one_ne_zero, nat.bit1_eq_one, fin.zero_eq_one_iff] at h,
  apply h,
  exfalso,
  norm_num at h_3,
  norm_num at h_3,
  norm_num at h_1,
  norm_num,
  unfold is_direct_superbase at vsb,
  rw det_fin_two at vsb,
  simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'] at vsb,
  linarith,
  },
  {
    unfold kronecker_delta,
    unfold associated_vectors_direct,
    split_ifs,
    exfalso,
    norm_num at h,
    exfalso, 
    norm_num at h,
        exfalso, 
    norm_num at h,
        exfalso, 
    norm_num at h,
    exfalso,
    rw ← h_2 at h_3,
    norm_num at h_3,
    norm_num,
    rw ← h_2,
  rw exercise_part_one (v) (vsb),
  unfold is_direct_superbase at vsb,
  rw det_fin_two at vsb,
  simp at h_1,
  norm_num at h_1,
  simp only [matrix.head_cons,
 neg_mul,
 matrix.vec2_dot_product,
 third_element_0_2,
 zero_sub,
 matrix.cons_val_one,
 matrix.cons_val_zero],
  rw ← h_3,
  unfold is_direct_superbase at vsb,
  rw det_fin_two at vsb,
  simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'] at vsb,
  exfalso,
  simp only [algebra_map.coe_one,
 fin.coe_zero,
 third_element_0_2,
 fin.coe_one,
 fin.coe_two,
 int.coe_nat_bit0,
 zmod.nat_cast_self,
 coe_coe] at h_1,
  norm_num at h_1,
  norm_num,
  have p : k=1,
  by_contra,
  fin_cases k,
  simp only [eq_self_iff_true, not_true] at h_2, 
  apply h_2,
  simp only [eq_self_iff_true, not_true] at h,
  apply h,
  simp only [eq_self_iff_true, not_true] at h_3,
  apply h_3,
  rw p,
  ring,
  exfalso,
  rw ← h_2 at h_3,
  norm_num at h_3,
  rw ← h_2,
  rw exercise_part_one (v) (vsb),
  simp only [tsub_zero,
 matrix.head_cons,
 neg_mul,
 matrix.vec2_dot_product,
 third_element_0_2,
 matrix.cons_val_one,
 matrix.cons_val_zero],
 unfold is_direct_superbase at vsb,
 rw det_fin_two at vsb,
 simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'] at vsb,
 norm_num,
 ring_nf,
 rw add_comm,
 linarith,
 rw ← h_3, 
 simp only [matrix.head_cons,
 neg_mul,
 matrix.vec2_dot_product,
 third_element_0_2,
 zero_sub,
 matrix.cons_val_one,
 matrix.cons_val_zero],
 unfold is_direct_superbase at vsb,
 rw det_fin_two at vsb,
 simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'] at vsb,
 ring_nf,
 linarith,
 simp only [tsub_zero,
 matrix.head_cons,
 neg_mul,
 matrix.vec2_dot_product,
 third_element_0_2,
 matrix.cons_val_one,
 matrix.cons_val_zero],
 have p : k=1,
  by_contra,
  fin_cases k,
  simp only [eq_self_iff_true, not_true] at h_2, 
  apply h_2,
  simp only [eq_self_iff_true, not_true] at h,
  apply h,
  simp only [eq_self_iff_true, not_true] at h_3,
  apply h_3,
  rw p,
  ring,
  },
  {
  unfold kronecker_delta,
  unfold associated_vectors_direct,
  split_ifs,
  exfalso,
  norm_num at h,
  exfalso,
  norm_num at h,
  exfalso,
  norm_num at h,
  exfalso,
  norm_num at h,
  exfalso,
  rw ← h_2 at h_3,
  norm_num at h_3,
  rw ← h_2, 
  simp only [tsub_zero,
 matrix.head_cons,
 neg_mul,
 matrix.vec2_dot_product,
 third_element_1_2,
 matrix.cons_val_one,
 matrix.cons_val_zero],
 rw exercise_part_one (v) (vsb),
  unfold is_direct_superbase at vsb,
  rw det_fin_two at vsb,
  simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'] at vsb,
  simp only [pi.neg_apply, pi.sub_apply],
  linarith,
  rw ← h_3,
    simp only [matrix.head_cons,
 neg_mul,
 matrix.vec2_dot_product,
 zero_sub,
 third_element_1_2,
 matrix.cons_val_one,
 matrix.cons_val_zero],
 rw exercise_part_one (v) (vsb),
  unfold is_direct_superbase at vsb,
  rw det_fin_two at vsb,
  simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'] at vsb,
  simp only [pi.neg_apply, pi.sub_apply],
  linarith,
  have p : k=0,
  by_contra,
  fin_cases k,
  simp only [eq_self_iff_true, not_true] at h, 
  apply h,
  simp only [eq_self_iff_true, not_true] at h_2,
  apply h_2,
  simp only [eq_self_iff_true, not_true] at h_3,
  apply h_3,
  rw p,
  simp only [tsub_zero,
 matrix.head_cons,
 neg_mul,
 matrix.vec2_dot_product,
 third_element_1_2,
 matrix.cons_val_one,
 matrix.cons_val_zero],
  linarith,
  exfalso,
  rw ← h_2 at h_3,
  norm_num at h_3,
  simp only [tsub_zero,
 matrix.head_cons,
 neg_mul,
 matrix.vec2_dot_product,
 third_element_1_2,
 matrix.cons_val_one,
 matrix.cons_val_zero],
 rw ← h_2,
 rw exercise_part_one v vsb,
 simp only [pi.neg_apply, pi.sub_apply],
 unfold is_direct_superbase at vsb,
 rw det_fin_two at vsb,
 simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'] at vsb,
 exfalso,
 norm_num at h_1,
 rw ← h_3,
 simp,
 rw exercise_part_one v vsb,
 unfold is_direct_superbase at vsb,
 rw det_fin_two at vsb,
 simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'] at vsb,
 exfalso,
 norm_num at vsb,
 exfalso,
 norm_num at h_1,
  },
  end

lemma associated_vectors_def (i j k : fin (3)) (hij : i < j)(vsb : is_superbase v) :
  e i j vsb ⬝ᵥ v k = kronecker_delta R i k - kronecker_delta R j k :=
  begin
  fin_cases i;
  fin_cases j,
  all_goals{norm_num at hij},
  fin_cases k,
  norm_num,
  unfold kronecker_delta,
  unfold associated_vectors,
  norm_num,
  have g := (superbase_permutation (v) (vsb)),
  have l := (superbase_permutation (![ v 2, v 0, v 1]) (g)),
  split_ifs,
  rw exercise_part_one (v) (vsb),
  unfold is_superbase at vsb,
  rw abs_eq at vsb,
  rw det_fin_two at h,
  simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'] at h,
  simp only [matrix.head_cons, neg_mul, pi.neg_apply, matrix.cons_val_one, matrix.cons_val_zero, pi.sub_apply],
  ring_nf, 
  rw h,
  linarith,
  unfold is_superbase at l,
  rw abs_eq at l,
  cases l.2 with l1 l2,
  rw det_fin_two at l1,
  simp only [fin.succ_zero_eq_one',
 matrix.head_cons,
 matrix.cons_vec_bit0_eq_alt0,
 matrix.empty_vec_alt0,
 matrix.vec_append_apply_zero,
 id.def,
 matrix.cons_val',
 matrix.empty_vec_append,
 matrix.cons_val_one,
 matrix.cons_vec_append,
 matrix.cons_vec_alt0,
 matrix.vec_head_vec_alt0,
 matrix.submatrix_apply,
 matrix.cons_val_zero,
 fin.succ_one_eq_two'] at l1,
  simp only [matrix.head_cons, neg_mul, matrix.cons_val_one, matrix.cons_val_zero],
  exfalso,
  apply h,
  rw det_fin_two,
  simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'],
  rw exercise_part_one (v) (vsb) at l1,
  norm_num at l1,
  ring_nf at l1,
  linarith,
  rw det_fin_two at l2,
  norm_num at l2,
  simp only [matrix.head_cons, neg_mul, matrix.cons_val_one, matrix.cons_val_zero],
  linarith,
  linarith,


  norm_num,
  unfold kronecker_delta,
  unfold associated_vectors,
  norm_num,
  have g := (superbase_permutation (v) (vsb)),
  have l := (superbase_permutation (![ v 2, v 0, v 1]) (g)),
  split_ifs,
  unfold is_superbase at vsb,
  rw abs_eq at vsb,
  rw det_fin_two at h,
  simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'] at h,
  simp only [matrix.head_cons, neg_mul, pi.neg_apply, matrix.cons_val_one, matrix.cons_val_zero, pi.sub_apply],
  ring_nf, 
  linarith,
  linarith,
  unfold is_superbase at l,
  rw abs_eq at l,
  cases l.2 with l1 l2,
  rw det_fin_two at l1,
  simp only [fin.succ_zero_eq_one',
 matrix.head_cons,
 matrix.cons_vec_bit0_eq_alt0,
 matrix.empty_vec_alt0,
 matrix.vec_append_apply_zero,
 id.def,
 matrix.cons_val',
 matrix.empty_vec_append,
 matrix.cons_val_one,
 matrix.cons_vec_append,
 matrix.cons_vec_alt0,
 matrix.vec_head_vec_alt0,
 matrix.submatrix_apply,
 matrix.cons_val_zero,
 fin.succ_one_eq_two'] at l1,
  simp only [matrix.head_cons, neg_mul, matrix.cons_val_one, matrix.cons_val_zero],
  exfalso,
  apply h,
  rw det_fin_two,
  simp only [fin.succ_zero_eq_one', id.def, matrix.submatrix_apply, fin.succ_one_eq_two'],
  rw exercise_part_one (v) (vsb) at l1,
  norm_num at l1,
  ring_nf at l1,
  linarith,
  rw exercise_part_one (v) at l2,
  rw det_fin_two at l2,
  norm_num at l2,
  rw mul_add at l2,
  norm_num,
  sorry

  end


/-- Lemma B.2. The right-hand side sums over all `i` and all `j > i`. -/
@[simp]lemma Ioi_0 (f : fin 3 → R) : ∑ i in Ioi 0, f i = f 1 + f 2 :=
begin
  simp,
end

@[simp]lemma Ioi_1 (f : fin 3 → R) : ∑ i in Ioi 1, f i = f 2 :=
begin
  rw [← add_zero (f 2)], refl,
end 

@[simp]lemma Ioi_2 (f : fin 3 → R) : ∑ i in Ioi 2, f i = 0 :=
begin
  refl,
end 

@[simp]lemma double_sum  (f : matrix (fin (3)) (fin 3) R) : ∑ i, ∑ j in Ioi i, f i j = f 0 1 + f 0 2 + f 1 2 :=
begin

  repeat { rw fin.Ioi_eq_finset_subtype},
  rw sum_fin_three,
  simp,
end
@[simp]

lemma selling_formula (vsb : is_direct_superbase v) (Dsymm : D.is_symm) :
  D = - ∑ i, ∑ j in Ioi i, (v i ⬝ᵥ D.mul_vec (v j)) • vec_mul_vec (e i j vsb) (e i j vsb) :=
begin
  have B := - ∑ i, ∑ j in Ioi i, (v i ⬝ᵥ D.mul_vec (v j)) • vec_mul_vec (e i j vsb) (e i j vsb) ,
  have h :  ∀ k l : nat, v k ⬝ᵥ (- ∑ i, ∑ j in Ioi i, (v i ⬝ᵥ D.mul_vec (v j)) • vec_mul_vec (e i j vsb) (e i j vsb) ).mul_vec (v l) = v k ⬝ᵥ D.mul_vec (v l),
  intros k l,
  by_cases h2 : k < l ∧ l ≤ 2,
  by_cases h3 : k = 0 ∧ l = 1,
  rw h3.1,
  rw h3.2,
  have p : ∑ (i : fin 3), ∑ (j : fin 3) in Ioi i, (v i ⬝ᵥ D.mul_vec (v j)) • vec_mul_vec (associated_vectors_direct v i j vsb) (associated_vectors_direct v i j vsb) = 
  rw dot_product,
  repeat { rw fin.Ioi_eq_finset_subtype},
  rw sum_fin_three,
  simp,
  repeat { rw fin.Ioi_eq_finset_subtype},
  rw double_sum,
  rw sum_fin_two,
  rw finset.sum,
  apply associated_vectors_def (2),
  sorry
    






end

lemma simp_dot_product (vsb : is_direct_superbase v) (k i j l : fin (3)): 
  v k ⬝ᵥ ((vec_mul_vec (e i j vsb) (e i j vsb) ).mul_vec (v l)) =( v k ⬝ᵥ e i j vsb) * (e i j vsb ⬝ᵥ v l) :=
  begin
  simp,
  ring_nf,
  rw vec_mul_vec_eq,
  rw mul_vec,
  ring_nf,
  simp,



  end


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
theorem selling_algorithm (vsb : is_direct_superbase v) (vint : ∀ i j, v i j ∈ Z)
  (Dsymm : D.is_symm) (Dposdef : D.pos_def) (hd : d = 2 ∨ d = 3) :
  ∃ v' : matrix (fin (d+1)) (fin d) ℝ,
    is_direct_superbase v' ∧ is_obtuse v' D ∧ ∀ i j, v' i j ∈ Z :=
sorry

example (a b : ℤ) : set.finite (set.Icc a b) := set.finite_Icc a b
#check @set.finite.image 

local notation `coeZR` := (coe : ℤ → ℝ)

#check int.floor 
lemma int_symm {K : ℝ} : coeZR '' (set.Icc (-int.floor K) (int.floor K)) = { v : ℝ | v ∈ Z ∧ |v| ≤ K } :=
begin
ext,simp, rw abs_le,
split,
intro p,
split,
cases p with l hl,
use l,
apply hl.2,
split,
cases p with l hl,
rw ← neg_neg x,
apply neg_le_neg,
rw ← hl.2,
rw ← neg_neg K,
apply neg_le_neg,
rw int.ceil_le.symm,
rw int.ceil_neg,
apply hl.1.1,
cases p with l hl,
rw ← hl.2,
rw int.le_floor.symm,
apply hl.1.2,
intro p,
cases p with l hl,
cases l with y hy,
use y,
split,
split,
rw ← int.ceil_neg,
rw int.ceil_le,
rw hy,
apply hl.1,
rw int.le_floor,
rw hy,
apply hl.2,
apply hy,
end


example {K : ℝ} : Z '' (set.Icc (-int.floor K) (int.floor K)) = { v : ℝ | v ∈ Z ∧ |v| ≤ K } :=
begin
ext,simp,
end


lemma int_fin {K : ℝ} : set.finite { v : ℝ | v ∈ Z ∧ |v| ≤ K } :=
begin
  rw ← int_symm,
  exact (coe '' set.Icc (-⌊K⌋) ⌊K⌋).to_finite,
end


/--
Preliminary exercise: {v in R^2 | forall i, v i in Z and |v i| <= K} 
is a nonempty finite set, for any K>=0.
--/

lemma vec_symm {K : ℝ} : (set.univ).pi (λ i : fin 2, { v : ℝ | v ∈ Z ∧ |v| ≤ K }) = 
  { v : fin 2 → ℝ | ∀ i, v i ∈ Z ∧ |v i| ≤ K } :=
begin
  ext,
  simp,
end

example {K : ℝ} : set.finite { v : fin 2 → ℝ | ∀ i, v i ∈ Z ∧ |v i| ≤ K } :=
begin
  rw ← vec_symm,
  refine set.finite.pi _,
  intro v,
  apply int_fin,

end



example (v₀ : fin 2 → ℝ) : ∃ v : fin 2 → ℤ, ∀ v' : fin 2 → ℤ,  
  ‖ coeZR ∘ v - v₀ ‖ ≤ ‖ coeZR ∘ v' - v₀ ‖ :=
begin

end 
/--
Exercise : forall v0 : R^2 there exists v : Z^2 which minimizes |v-v0|
Desired proof : 
We can restrict our attention to v such that |v-v0|<=|0-v0|.
There are a finite number of them, so one is minimal.
--/
example (v₀ : fin 3 → ℝ) : ∃ v : fin 3 → ℝ, (∀ i, v i ∈ Z) ∧ ∀ v' : fin 3 → ℝ, (∀ i, v' i ∈ Z) →  
  ‖ v - v₀ ‖ ≤ ‖ v' - v₀ ‖ :=
sorry 
#check @finset.pi
#check @set.finite.pi 
#check @set.finite.to_finset
#check @set.pi 
end real