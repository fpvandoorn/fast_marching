/-
# Formalisation of the fast marching algorithm.
# Semi-Lagrangian discretizations

-/

import topology.instances.real
import fixed_point
noncomputable theory
open topological_space
open partial_order
open fixed_point

/-
We declare the some common variables. 

**TODO** Understand why the boundary $Γ$ of $X$ must be implemented as  
a mapping X→bool, rather than a subset of X.
-/
variables {X : Type*} [finite X] [nonempty X] (Γ : X → bool)
local notation `𝕌` := X → ℝ
variables {X} (Λ Λ0 Λ1 : 𝕌 → 𝕌) (u v w : 𝕌) (x : X) (s t : ℝ) 
variables (vlv : ℝ) (h_vlv : ∃ u ≤ vlv•1, Λ u ≤ u)
local infix ` ≺ `:50 := strong_lt

/- Maybe using metaclasses, or some inheritance mechanism, would be better ? -/
namespace piecewise
/--/
def switch : bool → ℝ 
| tt := Λ0 u x
| ff := Λ1 u x
def mk : ℝ := switch Λ0 Λ1 u x (Γ x) 
-/
def mk : ℝ := if (Γ x) then Λ0 u x else Λ1 u x
example : 𝕌 → 𝕌 := mk Γ Λ0 Λ1 

lemma monotone_of_piecewise 
(h0 : monotone Λ0) (h1 : monotone Λ1) (h : Λ = mk Γ Λ0 Λ1)
: monotone Λ := 
begin
  unfold monotone at *, 
  intros u v huv,
  specialize h0 huv, specialize h1 huv,
  rw pi.le_def at h0 h1 ⊢, simp_rw function.funext_iff at h,
  intro x, specialize h0 x, specialize h1 x,
  let hu := h u x, let hv := h v x,
  unfold mk at hu hv,
  cases Γ x; simp at hu hv; linarith,
end

lemma subadditive_of_piecewise 
(h0: is_subadditive Λ0) (h1: is_subadditive Λ1) (h : Λ = mk Γ Λ0 Λ1) 
: is_subadditive Λ :=
begin
  unfold is_subadditive at *,
  intros u t t_pos, specialize h0 u t t_pos, specialize h1 u t t_pos,
  rw pi.le_def at h0 h1 ⊢, simp_rw [function.funext_iff,mk] at h,
  intro x, specialize h0 x, specialize h1 x, 
  simp at h0 h1 ⊢, simp_rw [h u x, h (u+t•1) x],
  cases Γ x; simp, 
  exact h1, exact h0,
end

/- Lemma
A scheme defined piecewise from causal schemes is causal.
-/
lemma causal_of_piecewise (δ : ℝ) 
(h0 : is_causal_with vlv δ Λ0 ) (h1 : is_causal_with vlv δ Λ1) (h : Λ = mk Γ Λ0 Λ1) 
: (is_causal_with vlv δ Λ):=
begin
  unfold is_causal_with at *,
  intros u v t h_lt, specialize h0 u v t h_lt, specialize h1 u v t h_lt, 
  rw function.funext_iff at h0 h1 ⊢,
  intro x, specialize h0 x, specialize h1 x,   
  simp_rw [function.funext_iff,mk] at h,
  let hu := h u x, let hv := h v x,
  unfold cut_le at *,
  simp_rw [h u x, h v x],
/- Comment
--  TODO : find why I cannot use one of the following lines (have is silly here)
-- cases Γ x, -- todo : why does not this work ? 
-- cases bool.dichotomy (Γ x) with hx hx, -- todo : why does not this work ? 
--  let hx := bool.dichotomy (Γ x), -- todo : why does not this work ? 
-/
  have hx := bool.dichotomy (Γ x), cases hx; -- todo : is there a single instruction for this ?
  rw hx at ⊢ hu hv; simp at ⊢ hu hv; assumption,
end

end piecewise


namespace boundary_condition

def mk (u0 u : 𝕌) := u0

lemma monotone_of_boundary_condition (u0 : 𝕌) : monotone (mk u0) := 
begin
  unfold monotone mk, intros, exact partial_order.le_refl u0,
end

lemma subadditive_of_boundary_condition (u0 : 𝕌) : is_subadditive (mk u0) := 
begin
  unfold is_subadditive mk, intros u t t_pos, 
  exact le_add_of_nonneg_right (order_embeds t t_pos),
end

lemma causal_of_boundary_condition (u0 : 𝕌) (δ : ℝ) : is_causal_with vlv δ  (mk u0) := 
begin
  simp_rw [is_causal_with,cut_le,function.funext_iff,mk], intros _ _ _ h x, 
  refl,
end 

end boundary_condition

namespace graph_setting 

variable c : X → X → ℝ
def mk (u:𝕌) (x:X):= infi (λ y, c x y + u y) -- works, but could be a pain to use ?

/- Comment
def mk (c: X → X → ℝ) (u:𝕌) (x:X) : ℝ := 
begin
  have h:= finite.exists_min (λ y, c x y + u y),
--  split h,
  use 0
end

--infi (λ y, c x y + u y) -- works, but could be a pain to use ?


-- variables (Y : finset X) (HY:Y.nonempty) (y:Y) -- (f : Y → ℝ)
-- #check Y.inf' HY u



#check finite.exists_min

lemma monotone_of_graph : monotone (mk c) := 
begin
  simp_rw [monotone,pi.le_def,mk],
  intros u v huv x,
  apply finite.exists_min,
--    cases finite.exists_max (u-v) with x hx,


end
-/

end graph_setting