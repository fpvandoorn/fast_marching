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

**TODO** Understand why the boundary $Î$ of $X$ must be implemented as  
a mapping Xâbool, rather than a subset of X.
-/
variables {X : Type*} [finite X] [nonempty X] (Î : X â bool)
local notation `ð` := X â â
variables {X} (Î Î0 Î1 : ð â ð) (u v w : ð) (x : X) (s t : â) 
variables (vlv : â) (h_vlv : â u â¤ vlvâ¢1, Î u â¤ u)
local infix ` âº `:50 := strong_lt

/- Maybe using metaclasses, or some inheritance mechanism, would be better ? -/
namespace piecewise
/--/
def switch : bool â â 
| tt := Î0 u x
| ff := Î1 u x
def mk : â := switch Î0 Î1 u x (Î x) 
-/
def mk : â := if (Î x) then Î0 u x else Î1 u x
example : ð â ð := mk Î Î0 Î1 

lemma monotone_of_piecewise 
(h0 : monotone Î0) (h1 : monotone Î1) (h : Î = mk Î Î0 Î1)
: monotone Î := 
begin
  unfold monotone at *, 
  intros u v huv,
  specialize h0 huv, specialize h1 huv,
  rw pi.le_def at h0 h1 â¢, simp_rw function.funext_iff at h,
  intro x, specialize h0 x, specialize h1 x,
  let hu := h u x, let hv := h v x,
  unfold mk at hu hv,
  cases Î x; simp at hu hv; linarith,
end

lemma subadditive_of_piecewise 
(h0: is_subadditive Î0) (h1: is_subadditive Î1) (h : Î = mk Î Î0 Î1) 
: is_subadditive Î :=
begin
  unfold is_subadditive at *,
  intros u t t_pos, specialize h0 u t t_pos, specialize h1 u t t_pos,
  rw pi.le_def at h0 h1 â¢, simp_rw [function.funext_iff,mk] at h,
  intro x, specialize h0 x, specialize h1 x, 
  simp at h0 h1 â¢, simp_rw [h u x, h (u+tâ¢1) x],
  cases Î x; simp, 
  exact h1, exact h0,
end

/- Lemma
A scheme defined piecewise from causal schemes is causal.
-/
lemma causal_of_piecewise (Î´ : â) 
(h0 : is_causal_with vlv Î´ Î0 ) (h1 : is_causal_with vlv Î´ Î1) (h : Î = mk Î Î0 Î1) 
: (is_causal_with vlv Î´ Î):=
begin
  unfold is_causal_with at *,
  intros u v t h_lt, specialize h0 u v t h_lt, specialize h1 u v t h_lt, 
  rw function.funext_iff at h0 h1 â¢,
  intro x, specialize h0 x, specialize h1 x,   
  simp_rw [function.funext_iff,mk] at h,
  let hu := h u x, let hv := h v x,
  unfold cut_le at *,
  simp_rw [h u x, h v x],
/- Comment
--  TODO : find why I cannot use one of the following lines (have is silly here)
-- cases Î x, -- todo : why does not this work ? 
-- cases bool.dichotomy (Î x) with hx hx, -- todo : why does not this work ? 
--  let hx := bool.dichotomy (Î x), -- todo : why does not this work ? 
-/
  have hx := bool.dichotomy (Î x), cases hx; -- todo : is there a single instruction for this ?
  rw hx at â¢ hu hv; simp at â¢ hu hv; assumption,
end

end piecewise


namespace boundary_condition

def mk (u0 u : ð) := u0

lemma monotone_of_boundary_condition (u0 : ð) : monotone (mk u0) := 
begin
  unfold monotone mk, intros, exact partial_order.le_refl u0,
end

lemma subadditive_of_boundary_condition (u0 : ð) : is_subadditive (mk u0) := 
begin
  unfold is_subadditive mk, intros u t t_pos, 
  exact le_add_of_nonneg_right (order_embeds t t_pos),
end

lemma causal_of_boundary_condition (u0 : ð) (Î´ : â) : is_causal_with vlv Î´  (mk u0) := 
begin
  simp_rw [is_causal_with,cut_le,function.funext_iff,mk], intros _ _ _ h x, 
  refl,
end 

end boundary_condition

namespace graph_setting 

variable c : X â X â â
def mk (u:ð) (x:X):= infi (Î» y, c x y + u y) -- works, but could be a pain to use ?

/- Comment
def mk (c: X â X â â) (u:ð) (x:X) : â := 
begin
  have h:= finite.exists_min (Î» y, c x y + u y),
--  split h,
  use 0
end

--infi (Î» y, c x y + u y) -- works, but could be a pain to use ?


-- variables (Y : finset X) (HY:Y.nonempty) (y:Y) -- (f : Y â â)
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