-- begin header

import topology.instances.real
import fixed_point
noncomputable theory
open topological_space
open partial_order


variables {X : Type*} [finite X] [nonempty X]
local notation `𝕌` := X → ℝ
variables {X} (Λ : 𝕌 → 𝕌) (F : X → ℝ → 𝕌 → ℝ) (u v w : 𝕌) (x : X) (s t : ℝ)
local notation `𝕀` := (1:𝕌)
local infix ` ≺ `:50 := strong_lt

-- end header

/-
# Formalisation of the fast marching algorithm.
# Finite differences formalism

-/

namespace finite_difference

/- Definition
A finite difference scheme takes the form
$$
  𝔽 u(x) := F(x, (u x), (u y - u x)_{y ∈ X})
$$
-/
def eval_scheme := λ x, F x (u x) (λ y, u y-u x)
local notation `𝔽` := eval_scheme F


/- Definition
A finite differences scheme is degenerate elliptic if it is non-decreasing w.r.t. 
the second variable, and non-decreasing w.r.t. the third 
-/
def is_degenerate_elliptic := ∀ (x : X) (s t : ℝ) (s≤t) (u v : 𝕌) (u≥v), F x s u ≤ F x t v 

/- Definition
A finite differences scheme is causal if it only depends on the positive part 
of the third argument.
-/
def is_causal (F : X → ℝ → (X → ℝ) → ℝ) : Prop :=
∀ x v p, F x v p = F x v (λ x', max 0 (p x'))

/-
## Sub-solutions and super-solutions.
-/


/- Theorem
Weak comparison principle
-/
theorem strict_subsol_lt_supsol (F_DE : is_degenerate_elliptic F) 
(u_strict_subsol : 𝔽 u ≺ 0  ) (v_supsol : 0 ≤ 𝔽 v) : u ≺ v :=
begin
  sorry
end

/- Theorem
Perron solution
-/

/-
## The Gauss-Siedel/Jacobi update  
-/

/-
Relation with the fixed point formalism
-/
def is_update := F x t (u-t•𝕀) = 0
def exists_update := ∃ (t:ℝ), is_update F u x t
def unique_update := is_update F u x s ∧ is_update F u x t → (s=t)

end finite_difference