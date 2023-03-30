-- begin header

import topology.instances.ereal
import preliminaries
import data.real.ereal
noncomputable theory
open topological_space
open partial_order


-- end header

/-
This file was an another attempt at using the ereal type.

Pros :
- Appropriate as an initial condition for the fast marching algorithm.
- Appropriate for outflow boundary conditions.
- More generally, appropriate for working with the max-plus semiring, 
 which underlies some of these works.

Cons :
- Elementary proofs become painful, because the algebraic structure of (ereal, +, *) is so poor,
 as opposed to (ereal, max, +). We constantly need to check that quantities are not infty.
- Tactics such as linarith cannot work in this setting.
-/

/-
# Formalisation of the fast marching algorithm.
# Fixed point formalism

The fast marching algorithm can be described abstractly as a "single pass" method
for solving a fixed point equation. In this file, we present the fixed point formalism,
related results such as the comparison principle, and the fast marching algorithm.

Specific instantiations of the fast marching algorithm are described later.
-/

/- Comment
- Use the Comment tag to remove from the lean_project output.
- Leave a line before bullet lists, or it fails to compile.
- We can define Latex macros as follows : (for illustration, these ones are useless)
$
\def\bR{\mathbb{R}}
\def\bU{\mathbb{U}}
$
-/

/- Comment
TODO : Find out if the following is possible with lean_project, or can be added.

* (automatically) numbering sections, subsections, and making links/references.
* (automatically) numbering and naming definitions, lemmas, theorems, and making links.
  (Could put both a common name, and the lean name.)
* Add a references.bib file and refer to some bibliography
* Allow basic markdown (*emphasis*, **bold**), in Definitions and lemmas.
* Add an Example environment. Also Variable, Assumption.
* Remove the Proof QED in the html output if it is empty. (e.g. inline proof)
-/


namespace fixed_point

/-
## Underlying algebra structure

**Lack of extended reals.**
We choose to limit our attention to mappings $u : X → ℝ$, whereas the description and the
numerical implementation of FMM often allow $u : X → ]-∞,+∞]$, i.e. positive infinity may
be in the range of the function. There are some tradeoffs to this choice, discussed below.
-/

/- Definition
(Note : Notation would be more appropriate)
In all this document, $X$ denotes a non-empty finite set, and $𝕌 := ℝ^X$ is the type of all
mappings from $X$ to $ℝ$.

(Alternatively, we could try extended reals)
-/
local notation `ℛ` := ereal 
example : mul_pos_mono ereal := by apply_instance
variables {X : Type*} [finite X] [nonempty X]
local notation `𝕌` := X → ℛ
variables {X} (Λ : 𝕌 → 𝕌) (F : X → ℛ → 𝕌 → ℛ) (u v w : 𝕌) (x : X) (s t : ℛ)

lemma ereal.finite_add_inverse : ∀ {t : ℛ}, t ≠ ∞ → t ≠ -∞ → 0 = t-t := 
begin
  intros t hp hm,
  let k := ereal.can_lift.prf t,
  simp at k,
  cases (k hp hm) with tt htt,
  let w := ereal.coe_sub tt tt,
  simp at w,
  rw htt at w,
  exact w,
end

lemma ereal.finite_add_sub : ∀ {s t : ℛ}, t ≠ ∞ → t ≠ -∞  → s=t+(s-t) := 
begin
  intros s t hp hm,
  let k:=ereal.finite_add_inverse hp hm, 
  calc 
  s = s+0 : by simp
  ... = s+(t-t) : by rw k
  ... = (s+t)-t : add_sub s t t
  ... = (t+s)-t : by rw [add_comm s t]
  ... = t+(s-t) : by rw [add_sub t s t],
end

/- Example
A real valued function which is defined on a finite and non-empty set, attains its bounds.
-/
example : ∃ (x : X), ∀ (y : X), u x ≥ u y := finite.exists_max u

/- Example 
The type $𝕌 = ℝ^X$ as a product space is equipped with the usual partial order and
topology. Recall that $u≤v$ iff $u x ≤ v x$ for all $x∈X$. We must distinguish
weak-less-than $u < v$, i.e. $u≤v$ and $u≠v$, from strong-less-than $u≺v$, i.e.
iff $u x < v x$ for all $x∈X$.
-/
example : topological_space 𝕌 := by apply_instance
example : partial_order 𝕌 := by apply_instance
example : has_mul 𝕌 := by apply_instance
example : preorder 𝕌 := by apply_instance
local infix ` ≺ `:50 := strong_lt
example : has_smul ℛ 𝕌 := by apply_instance

/-
Curiously, the pos_mul_mono instance of ereal does not transfer to 𝕌 := X -> ereal
using the standard instance mechanism.
-/
/-
example : ∀ (a b c : ℛ), b ≤ c → a+b ≤ a+c := 
begin
  library_search,
end 
-/

lemma mul_le_mul_of_nonneg_left  : ∀ {a b c : 𝕌}, a ≤ b → 0 ≤ c → c * a ≤ c * b := 
begin
  intros a b c hab hc x,
  exact mul_le_mul_of_nonneg_left (hab x) (hc x),
end

instance 𝕌.to_pos_mul_mono : pos_mul_mono 𝕌 := 
begin
  refine {elim := _},
  intros m n1 n2 h,
  exact mul_le_mul_of_nonneg_left h m.2,
end

instance 𝕌.to_mul_pos_mono : mul_pos_mono 𝕌 := 
begin
  refine pos_mul_mono_iff_mul_pos_mono.mp _,
  apply_instance,
end

example : pos_mul_mono 𝕌 := by apply_instance
example : mul_pos_mono 𝕌 := by apply_instance

/- Example
The type $𝕌 = ℝ^X$ also has a an algebra structure over the field $ℝ$.
In particular, 0:𝕌 and 1:𝕌 are defined.
-/
-- example : ring 𝕌 := by apply_instance -- not a ring with extended reals
example : 𝕌 := 1
example : 𝕌 := 0

/- Example
The order structure on 𝕌 is compatible with the group structure
-/
example (h :u ≤ v) : ∀ x, u x ≤ v x := h -- order relation 
example (h : u ≤ v) : u + w ≤ v + w := add_le_add_right h w
example (h : u ≤ v) : w + u ≤ w + v := add_le_add_left h w

example (a b c : ℛ) (hab: a≤b) (hc : 0≤c) : a*c ≤ b*c := mul_le_mul_of_nonneg_right hab hc


example (h : u ≤ v) (k : 0 ≤ t) : t • u ≤ t • v := mul_le_mul_of_nonneg_left h (λ x,k)

example (h : 0 ≤ t) : (0: 𝕌) ≤ (λ x,t) := λ x, h
example : t • (1:𝕌) = (λ x,t) :=
begin
  funext,
  simp,
end
lemma order_embeds (t_pos : t ≥ (0 : ℝ)) : (0 : 𝕌) ≤ t • 1 :=
begin
  simp at t_pos, simp [pi.le_def, t_pos],
end



/-
## Solutions, sub-solutions, super-solutions.

The main interest of allowing the value $+∞$ (which is not our convention here), is that
in that case there exists a canonical super-solution, namely the mapping identically equal
to $+∞$. Here, instead, we'll have to assume the existence of a finite-valued super-solution.
-/

/-Definition
We say that a mapping $u ∈ 𝕌$ is a **solution** to the operator $Λ$ if it is a fixed point.
-/
def is_sol := Λ u = u

/-Definition
A super-solution is a mapping $u ∈ 𝕌$ such that $Λ u ≤ u$.
-/
def is_supsol := Λ u ≤ u

/-Definition
A sub-solution is a mapping  $u ∈ 𝕌$ such that $Λ u ≥ u$.
-/
def is_subsol := u ≤ Λ u

/- Lemma
Clearly, a mapping u is a solution iff it is both a sub-solution and a super solution.
-/
lemma sol_iff_subsol_supsol : is_sol Λ u ↔ is_supsol Λ u ∧ is_subsol Λ u :=
begin
  -- We first unfold the definitions and split the objective
  unfold is_sol is_supsol is_subsol at *,
  split,
  intro h_sol,

  -- Equality implies the upper and lower inequalities
  split,
  exact le_of_eq h_sol,
  exact ge_of_eq h_sol,

  -- Since $𝕌$ is equipped with a partial order, anti-symmetry holds
  -- and the upper and lower inequalities imply equality
  rintro ⟨h_supsol,h_subsol⟩,
  exact le_antisymm h_supsol h_subsol,
end

/-
## The comparison principle
-/

/- Definition
An operator $Λ$ is monotone iff $u ≤ v$ implies $Λ u ≤ Λ v$.
This definition is already known to Lean.
-/
example : Prop := monotone Λ

/- Definition
An operator $Λ$ is said sub-additive if $Λ (u+t) ≤ (Λ u)+t$ for all $u ∈ 𝕌$
and all $t ≥ 0$.
-/
def is_subadditive := ∀ (u : 𝕌) (t ≥ (0 : ℛ)), Λ (u + t • 1) ≤ Λ(u) + t • 1

/- Theorem
The weak comparison principle shows that, for a monotone and sub-additive operator,
strict-subsolutions are bounded by super-solutions.

-- We need that v is finite, otherwise the result is false.
(Consider Λ u = u+1, which admits the "supersolution" u = -∞)

-- We can add the finiteness assumption. However, the proof becomes painful, because 
we cannot use linarith, and all inequalities must be done by hand.

-- Alternatively, we can assume that u and v take real values, and use a coercion. 

-- TODO : finish this.
-/
theorem strict_subsol_lt_supsol (Λ_mon : monotone Λ) (Λ_sadd : is_subadditive Λ)
  (u_strict_subsol : u ≺ Λ u) (v_supsol : Λ v ≤ v) (finite_v : ∀ x:X, v x≠∞ ∧ v x≠-∞) : u ≺ v :=
begin
  -- Lean only has few lemmas for strong-less-than, hence we unfold this definition.
  unfold strong_lt at *,
  -- Consider the point $x$ where $u-v$ is largest, thus $u≤v+t$ with $t:=u x - v x$
  cases finite.exists_max (u-v) with x hx,
  let t := (u - v) x,
  have t_eq : t = u x - v x, refl,
  have t_ge : u ≤ v + t • 1,
  rw pi.le_def, simp at *,
  intro y, specialize hx y, 
  rw t_eq, 
  calc 
  u y = v y + (u y - v y) : ereal.finite_add_sub (finite_v y).1 (finite_v y).2 -- !! needs that v y is finite
  ... ≤ v y + (u x - v x) : sorry, -- addi

  -- We distinguish two cases : either t<0, or t≥0.
  cases le_or_lt 0 t with t_pos t_neg,
  -- In the case $t ≥ 0$, we can use sub-additivity and monotony to establish $Λ u ≤ v+t$
  { have h : Λ u ≤ v + t • 1,
    calc
    Λ u ≤ Λ (v + t • 1) : by exact Λ_mon t_ge
    ... ≤ Λ v + t • 1 : by exact Λ_sadd v t t_pos
    ... ≤ v + t • 1 : add_le_add_right v_supsol (t • 1),
    -- Combining with the definition of t, we obtain u x < Λ u x ≤ v x + t = u x, contradiction
    specialize h x,
    specialize u_strict_subsol x,
    dsimp at h, simp at h,
    have contra : u x < u x, 
    calc 
    u x < Λ u x : u_strict_subsol
    ... ≤ v x + t : h
    ... = v x + (u x - v x): by rw t_eq
    ... = u x : by rw [←ereal.finite_add_sub (finite_v x).1 (finite_v x).2], -- !! needs that v x is finite
    let k:= lt_irrefl (u x) contra, tauto,
    },
  -- The case where $t < 0$ is trivial
  { intro y,
    have hy := hx y,
    simp at hy,
    -- Also needs that v is finite here
    sorry,
    linarith }
end

/-
### Global iteration
-/
noncomputable def global_iter: ℕ → 𝕌
| 0 := u
| (n+1) :=  Λ (global_iter n)

lemma global_iter_subsol (Λ_mon : monotone Λ) (u_subsol : u ≤ Λ u) (n : ℕ) :
  global_iter Λ u n ≤ global_iter Λ u (n+1) :=
begin
  induction n with n ih,
  unfold global_iter, exact u_subsol,
  unfold global_iter at *, apply Λ_mon ih,
end


/- Lemma
If the global iteration converges, then the limit is a fixed point.
-/

/- Lemma
An increasing bounded sequence is converging.
-/

/- Lemma
We can obtain a solution as a limit of a sequence of sub-solutions, or super-solutions.
-/


-- lemma sol_by_global_iteration (Λ_mon : monotone Λ)
-- (u_subsol : u ≤ Λ u) (v_supsol : Λ v ≤ v) (u ≤ v)

/-
### Fast marching
-/

/- Definition
We define $u^{< t}(x)$ as $u x$ if $u x < t$ else vlv (the very large value).
We define similarly $u^{\leq t} (x)$.
-/
def cut_lt (u : 𝕌) (t : ℝ) : 𝕌 := λ x, if u x < t then u x else ⊤
def cut_le (u : 𝕌) (t : ℝ) : 𝕌 := λ x, if u x ≤ t then u x else ⊤

/- Definition
Informally, a scheme is δ-causal iff the arrival times until t+δ (included), only depend
on the arrival times until t (excluded).
-/
def is_causal_with (δ : ℝ) (Λ : 𝕌 → 𝕌) :=
∀ (u v : 𝕌) (t : ℝ), cut_lt u t = cut_lt v t →
  cut_le (Λ u) (t + δ) = cut_le (Λ v) (t + δ)

end fixed_point