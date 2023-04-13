import linear_algebra.matrix.pos_def
import data.complex.basic
import preliminaries

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
  sorry
end

/-- def B.1 -/
def is_obtuse (v : matrix (fin (d+1)) (fin d) R) (D : matrix (fin d) (fin d) R) : Prop :=
∀ i j : fin (d+1), i < j → v i ⬝ᵥ D.mul_vec (v j) ≤ 0


section Z_or_R
/-! In this section we work in any linear ordered ring, so we can use it for both `ℤ` and `ℝ`. -/

variables {v : matrix (fin (d+1)) (fin d) R} {D : matrix (fin d) (fin d) R}

example {D : matrix (fin d) (fin d) ℝ} (Dposdef : D.pos_def) : 0 < D.det := Dposdef.det_pos

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

/-- The Selling algorithm, position B.3.

Note that the current statement doesn't encode the precise algorithm used. To do this, we
should just define a sequence of matrices (separately for `d = 2` and `d = 3`)
and show that we reach one that satisfies the obtuseness.
-/
theorem selling_algorithm {Z : add_subgroup ℝ} (vsb : is_superbase v) (vint : ∀ i j, v i j ∈ Z)
  (Dsymm : D.is_symm) (Dposdef : D.pos_def) (hd : d = 2 ∨ d = 3) :
  ∃ v' : matrix (fin (d+1)) (fin d) ℝ,
    is_superbase v' ∧ is_obtuse v' D ∧ ∀ i j, v' i j ∈ Z :=
sorry

end real