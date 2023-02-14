-- begin header 

import topology.instances.real
noncomputable theory
open topological_space
open partial_order

-- end header

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
variables {X : Type*} [finite X] [nonempty X]
local notation `𝕌` := X → ℝ
variables {X} (Λ : 𝕌 → 𝕌) (F : X → ℝ → 𝕌 → ℝ) (u v w : 𝕌) (x : X) (s t : ℝ)

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
local infix ` ≺ `:50 := strong_lt

/- Example
The type $𝕌 = ℝ^X$ also has a an algebra structure over the field $ℝ$.
In particular, 0:𝕌 and 1:𝕌 are defined.
-/
example : ring 𝕌 := by apply_instance
example : 𝕌 := 1
example : 𝕌 := 0

/- Example 
The order structure on 𝕌 is compatible with the algebra structure 
-/
example (h:u≤v) : (u+w ≤ v+w) := add_le_add_right h w
example (h:u≤v) : (w+u ≤ w+v) := add_le_add_left h w
lemma mul_le_mul (h:u≤v) (k:0≤w) : (u*w≤v*w) := begin
  rw pi.le_def at *,
  intro x, specialize h x, specialize k x, 
  simp at *, nlinarith,
end
example (h:u≤v) (k:0≤t) :  (t•u ≤ t•v) := begin 
  rw pi.le_def at *, -- Alternatively, we could try to apply the previous lemma to w=t•𝕀
  intro x, specialize h x,
  simp at *, nlinarith,
end
lemma order_embeds (t_pos:t≥(0:ℝ)): (0:𝕌) ≤ t•1 :=
begin
  rw pi.le_def at *, intro x, simp,exact t_pos,
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
lemma sol_iff_subsol_supsol : (is_sol Λ u) ↔ (is_supsol Λ u) ∧ (is_subsol Λ u) := 
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
def is_subadditive := ∀ (u:𝕌) (t≥(0:ℝ)), Λ (u+t•1) ≤ (Λ u)+t•1

/- Theorem
The weak comparison principle shows that, for a monotone and sub-additive operator,
strict-subsolutions are bounded by super-solutions.
-/
theorem strict_subsol_lt_supsol (Λ_mon : monotone Λ) (Λ_sadd : is_subadditive Λ) 
(u_strict_subsol : u ≺ Λ u) (v_supsol : Λ v ≤ v) : u ≺ v :=
begin
-- Lean only has few lemmas for strong-less-than, hence we unfold this definition.
  unfold strong_lt at *,
-- Consider the point $x$ where $u-v$ is largest, thus $u≤v+t$ with $t:=u x - v x$
  cases finite.exists_max (u-v) with x hx,
  let t := (u-v) x, 
  have t_eq : t = u x - v x,refl,
  have t_ge : u≤v+t•1,  
    rw pi.le_def, simp at *, 
    intro y, linarith [hx y],
-- We distinguish two cases : either t<0, or t≥0.
  cases (le_or_lt 0 t) with t_pos t_neg,
-- In the case $t≥0$, we can use sub-additivity and monotony to establish $Λ u ≤ v+t$
  have h : Λ u ≤ v+t•1,
  calc -- Note : strong-less-than not usable here in Lean (no transitivity ?)
  Λ u ≤ Λ (v+t•1) : by exact Λ_mon t_ge
  ... ≤ Λ v + t•1 : by exact Λ_sadd v t t_pos
  ... ≤ v+t•1 : (add_le_add_right v_supsol (t•1)),
-- Combining with the definition of t, we obtain u x < Λ u x ≤ v x + t = u x, contradiction
  let zz := h x, simp at zz, 
  have contra : u x < u x, -- Note : unclear why linarith does not conclude this alone
  calc u x < Λ u x : u_strict_subsol x
  ...  ≤ v x + t : zz
  ... = v x + (u x - v x) : by rw t_eq
  ... = u x : by ring,
  linarith,
-- The case where $t<0$ is trivial
  intro y,
  have hy := hx y,
  simp at hy,
  linarith,  
end  

/-
### Global iteration
-/
noncomputable def global_iter: ℕ → 𝕌 
| 0 := u
| (n+1) :=  Λ (global_iter n) 

lemma global_iter_subsol (Λ_mon : monotone Λ) (u_subsol : u ≤ Λ u) (n:ℕ) : 
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
We need a very-large-value vlv, since +∞ is not allowed in our setting. 
The required assumption is that there exists a super-solution to the scheme 
which is bounded above by vlv.
-/
variables (vlv : ℝ) (h_vlv : ∃ u ≤ vlv•1, Λ u ≤ u)

/- Definition
We define $u^{< t}(x)$ as $u x$ if $u x < t$ else vlv (the very large value).
We define similarly $u^{\leq t} (x)$.  
-/
def cut_lt (u : 𝕌) (t : ℝ) : 𝕌 := λ x, if u x < t then u x else vlv
def cut_le (u : 𝕌) (t : ℝ) : 𝕌 := λ x, if u x ≤ t then u x else vlv

/- Definition
Informally, a scheme is δ-causal iff the arrival times until t+δ (included), only depend 
on the arrival times until t (excluded).
-/
def is_causal_with (δ : ℝ) (Λ : 𝕌 → 𝕌) :=
∀ (u v : 𝕌) (t : ℝ), cut_lt vlv u t = cut_lt vlv v t →
  cut_le vlv (Λ u) (t + δ) = cut_le vlv (Λ v) (t + δ)

end fixed_point