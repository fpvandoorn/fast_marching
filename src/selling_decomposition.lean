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
  /-
  rw h,
  rw ← he.2,
  by_cases j : (e.submatrix fin.succ id).det > 0,
  {
  by_cases p : (submatrix ![-e 0, e 1, (-2) * e 1 - e 2] fin.succ id).det > 0,
  have k : (submatrix ![-e 0, e 1, (-2) * e 1 - e 2] fin.succ id).det = (e.submatrix fin.succ id).det ∨ (submatrix ![-e 0, e 1, (-2) * e 1 - e 2] fin.succ id).det = -(e.submatrix fin.succ id).det,
  {
    left,
    have k1 : (submatrix ![-e 0, e 1, (-2) * e 1 - e 2] fin.succ id).det = (submatrix ![-e 0, e 1, (-2) * e 1 ] fin.succ id).det + (submatrix ![-e 0, e 1, - e 2] fin.succ id).det,
    {by rw basis.det,}
  }
  
  }
-/
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
    --rw e 2.succ 0 at h,
    --rw [nat.succ 2, nat.succ 1, nat.succ 0],
    rw abs_eq_abs,



  end

#check [0,1,1].succ 0

/-- def B.1 -/
def is_obtuse (v : matrix (fin (d+1)) (fin d) R) (D : matrix (fin d) (fin d) R) : Prop :=
∀ i j : fin (d+1), i < j → v i ⬝ᵥ D.mul_vec (v j) ≤ 0


section Z_or_R
/-! In this section we work in any linear ordered ring, so we can use it for both `ℤ` and `ℝ`. -/

variables {v : matrix (fin (d+1)) (fin d) R} {D : matrix (fin d) (fin d) R}

example {D : matrix (fin d) (fin d) ℝ} (Dposdef : D.pos_def) : 0 < D.det := Dposdef.det_pos

/-- The definition of the norm D ; careful, vector taken not superbase-/

def norm_D (v : matrix (fin d) unit R) (D : matrix (fin d) (fin d) R) := (transpose (v)).mul(D.mul v)


variables {A : matrix (fin d) (fin d) R} {B : matrix (fin d) (fin d) R}
#check(A.mul B)


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
    refl,rw m,simp,rw add_assoc,},
    rw fin.sum_univ_def,
    rw fin.sum_univ_def,
    simp[sum_range_succ],
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



/-- The definition of the `e_{i,j}` -/
def associated_vectors (v : matrix (fin (d+1)) (fin d) R) (i j : fin (d+1)) (l : fin d) : R :=
sorry

local notation `e` := associated_vectors v

lemma associated_vectors_def (i j k : fin (d+1)) (hij : i < j) :
  e i j ⬝ᵥ v k = kronecker_delta R i k - kronecker_delta R j k :=
sorry

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