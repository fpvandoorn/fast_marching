/-
# Formalisation of the fast marching algorithm.
# Semi-Lagrangian discretizations

-/

import topology.instances.real
import fixed_point
open topological_space
open partial_order
open fixed_point

variables {X : Type*} [finite X] [nonempty X] (Γ : set X)
local notation `𝕌` := X → ℝ
variables {X} (Λ Λ0 Λ1 : 𝕌 → 𝕌) (u v w : 𝕌) (x : X) (s t : ℝ) 
local notation `𝕀` := (1:𝕌)
local infix ` ≺ `:50 := strong_lt

def piecewise := λ x, if Γ x then Λ0 x else Λ1 x

-- is_causal_with 

namespace boundary_condition

/-

-/

end boundary_condition

namespace graph_setting 

end graph_setting