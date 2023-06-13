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


/-- def B.1 -/

def is_direct_superbase (v : matrix (fin (d+1)) (fin d) R) : Prop :=
∑ i, v i = 0 ∧ (v.submatrix fin.succ id).det = 1

format_lean --inpath limits.lean --outdir build --lib-path /usr/lib/lean-mathlib/src