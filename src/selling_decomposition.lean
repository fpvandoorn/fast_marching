import linear_algebra.matrix.pos_def
import data.complex.basic

/--
Following appendix B of the paper
A LINEAR FINITE-DIFFERENCE SCHEME FOR APPROXIMATING RANDERS
DISTANCES ON CARTESIAN GRIDS

It is likely useful to adapt the statements a little bit, to be a bit more flexible about the
type in which we consider these operations:
-/
variables {d : ℕ}

noncomputable theory
open matrix finset
open_locale classical big_operators matrix

/-- The Kronecker-delta `δᵢⱼ` as an element of `E`. -/
def kronecker_delta (E) [has_zero E] [has_one E] {ι} (i j : ι) : E :=
if i = j then (1 : E) else (0 : E)

/-- def B.1 -/
def is_superbase (v : matrix (fin (d+1)) (fin d) ℤ) : Prop :=
∑ i, v i = 0 ∧ |(v.submatrix fin.succ id).det| = 1


/-- def B.1 -/
def is_obtuse (v : matrix (fin (d+1)) (fin d) ℤ) (D : matrix (fin d) (fin d) ℝ) : Prop :=
∀ i j : fin (d+1), i < j → (coe ∘ v i) ⬝ᵥ (D.mul_vec (coe ∘ v j)) ≤ 0

variables {v : matrix (fin (d+1)) (fin d) ℤ} {D : matrix (fin d) (fin d) ℝ}
  -- (Dsymm : D.is_symm) (Dposdef : D.pos_def)
  -- (vsb : is_superbase v) (vDobtuse : is_obtuse v D)

example (Dposdef : D.pos_def) : 0 < D.det := Dposdef.det_pos

/-- The definition of the `e_{i,j}` -/
def associated_vectors (v : matrix (fin (d+1)) (fin d) ℤ) (i j : fin (d+1)) (l : fin d) : ℤ :=
sorry

local notation `e` := associated_vectors v

lemma associated_vectors_def (i j k : fin (d+1)) (hij : i < j) :
  e i j ⬝ᵥ v k = kronecker_delta ℤ i k - kronecker_delta ℤ j k :=
sorry

/-- Lemma B.2. The right-hand side sums over all `i` and all `j > i`. -/
lemma selling_formula (Dsymm : D.is_symm) (vsb : is_superbase v) :
  D = - ∑ i, ∑ j in Ioi i, ((coe ∘ v i) ⬝ᵥ D.mul_vec (coe ∘ v j)) • (vec_mul_vec (e i j) (e i j)).map coe :=
sorry