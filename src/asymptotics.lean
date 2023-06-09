import analysis.calculus.cont_diff

open filter asymptotics
open_locale topology

/- These are the basic concepts of differentiability and asymptotics.
You can go to their definition and try to read the documentation.
It uses filters, which are explained in the topology chapter of Mathematics in Lean, and I can tell
you about them in our meeting.
Note that mathlib has two notions of derivative:
* `fderiv` stands for Fréchet derivative, which you can think of as the total derivative of a
  multivariate map.
* `deriv` stands for the ordinary derivative of a univariate function.
-/
#check @is_o
#check @is_O
#check @has_fderiv_at
#check @has_deriv_at
#check @differentiable_at
#check @fderiv
#check @deriv

/- Useful equivalences when working with `is_o`, and `is_O`. The last is the characterization of
  `∀ᶠ x in 𝓝 a, p x`, which you should read as "`p(x)` holds for `x` sufficiently close to `a`". -/
#check @is_O_iff
#check @is_o_iff
#check @eventually_nhds_iff

namespace asymptotics

variables {u v f g : ℝ → ℝ} {x y : ℝ}

/- This is a useful lemma in mathlib, where `|·|` denoted the absolute value  -/
example : | max x y | ≤ max (|x|) (|y|) :=
abs_max_le_max_abs_abs

/- Now prove the following variant. Find the lemma in mathlib that states that the norm of a real
number is the same as its absolute value (either use `library_search` or the mathlib documentation
search function. -/
lemma norm_max_le_max_norm_norm : ‖ max x y ‖ ≤ max (‖x‖) (‖y‖) :=
begin
  sorry
end

/- Prove the following lemma. This requires some basic topology, in addition to the mentioned
lemmas. -/
lemma is_o.max (hu : u =o[𝓝 x] f) (hv : v =o[𝓝 x] f) : (λ x, max (u x) (v x)) =o[𝓝 x] f :=
begin
  rw is_o_iff at hu hv ⊢ ,
  intros y hy,
  rw eventually_nhds_iff,
  specialize hu hy,
  specialize hv hy,
  rw eventually_nhds_iff at hu hv,
  cases hu with tu pu,
  cases hv with tv pv,
  use tu∩tv,
  cases pv with dv jv,
  cases pu with du ju,
  cases ju with opu inu,
  cases jv with opv inv,
  split,
  intros x hx,
  specialize du x hx.1,
  specialize dv x hx.2,
  transitivity ,
  apply norm_max_le_max_norm_norm,
  apply max_le du dv,
  split,
  apply is_open.inter opu opv,
  split,
  apply inu,
  apply inv,
end
lemma my_lemma (f: ℝ→ℝ) (f':ℝ)(x:ℝ):
has_deriv_at f f' x ↔ (λ (h : ℝ), f (x+h) - f x - h * f') =o[𝓝 0] λ (h : ℝ), h:=
begin
  rw has_deriv_at_iff_is_o,
  rw ← map_add_left_nhds_zero x,
  rw is_o_map,
  simp [(∘)],
end

lemma my_lemma2 {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} :
  has_deriv_at f f' x ↔ (λ (h : ℝ), f x - f (x+h) + h * f') =o[𝓝 0] λ (h : ℝ), h:=
begin
  rw [my_lemma, ← is_o_neg_left],
  congr', ext x, ring,
end

/- Harder: prove the following result. It might be useful to first take a look at the following
theorems in mathlib, and to prove a variant of `has_deriv_at_iff_is_o` that is closer to
`has_fderiv_at_iff_is_o_nhds_zero`, where instead of working with `x` and `x - x'` you work with
`x + h` and `x`. -/
#check @has_deriv_at_iff_is_o
#check @has_fderiv_at_iff_is_o_nhds_zero

-- abs_max_sub_max_le_max

/- This is false: fix the statement and then prove it with `lipschitz_with_max`,
  `lipschitz_with_iff_dist_le_mul`, `prod.dist_eq`, `real.dist_eq` -/
lemma max_1_lip (a b c d :ℝ ) : |(max a b)-(max c d)|≤ max (|a-c|) (|b-d|) :=
begin
-- exact match dans librarie
exact abs_max_sub_max_le_max a b c d,

-- Question : how to go from edist (used in Lipschitz_max) to dist ?
repeat{rw ← real.dist_eq},
let k := lipschitz_with_max,
unfold lipschitz_with at k,

simp at k,
unfold edist at k,
rw real.dist_eq at k,
unfold pseudo_metric_space.edist at k,
 
-- rw ← prod.dist_eq [abs] [abs],



by_cases ha: (a<b),
by_cases hb: (c<d),
rw max_eq_right,
rw max_eq_right,
rw le_max_iff,
right,
simp,
rw lt_iff_le_and_ne at hb,
exact hb.1,
rw lt_iff_le_and_ne at ha,
exact ha.1,

rw max_eq_right,
let hc:= not_lt.1 hb,
rw max_eq_left,
rw le_max_iff,
left,
simp, -- this is not provable, what if a = c = 0, b = 1?
-- I gave some hints of useful lemmas in mathlib above the lemma statement. Use those.
-- Or alternatively prove this lemma (carefully!) on paper first, and then try to repeat that
-- proof in Lean. Feel free to delete comments like these in your next submission.

repeat{rw abs_eq_max_neg},
rw max_eq_left ,
rw max_eq_right,
simp,
linarith,


end

#check max_1_lip


lemma max_o (u : ℝ → ℝ) (x u' : ℝ) (hu : has_deriv_at u u' x) :
  (λ h,  max (u x - u (x - h)) (u x - u (x + h)) - |h * u'|)
  =o[𝓝 0] λ h, h :=
begin
rw is_o_iff,
  intros c hc,
  rw eventually_nhds_iff,  
let h1 := (my_lemma u u' x).1 hu,
rw is_o_iff at h1,
specialize h1 hc,
rw eventually_nhds_iff at h1,
rcases h1 with ⟨V,  ⟨H, V_open, V0⟩⟩,
let W:= V ∩ -V,
use W,
split,
{intros h Wh,
  rw abs_eq_max_neg,
  repeat{rw real.norm_eq_abs},
  let max_diff := max_1_lip (u x - u (x - h))  (u x - u (x + h)) (h*u') (-(h * u')) ,
  let diffp := H h Wh.1,
  repeat{rw real.norm_eq_abs at diffp},
  let diffm := H (-h) Wh.2,
  repeat{rw real.norm_eq_abs at diffm},
  rw abs_neg at diffm,
  rw ← abs_neg at diffm,
  rw ← abs_neg at diffp,
  let F := max_le diffp diffm,
  rw max_comm at F,
  apply le_trans max_diff _,
  apply le_trans _ F,
  simp only [← sub_eq_add_neg],
  apply le_of_eq,
  congr' 2; ring },
split,
{
  have V_neg_open := V_open.neg,
  apply is_open.inter V_open V_neg_open,},
{simp,
exact V0,},
end

lemma max_0_u (u : ℝ → ℝ) (x u': ℝ) (hu : has_deriv_at u u' x) :
  (λ h,  max 0 (max ((u x - u (x - h)) ) ((u x - u (x + h) ))) - |h  *u'|)
  =o[𝓝 0] λ h, h :=
begin
  have h : (λ (h : ℝ), (max ((u x - u (x - h))) (u x - u (x + h)))- |h*u'|  ) =o[𝓝 0] λ (h : ℝ),h,
  {
    apply max_o u x u' hu,},

  have ho : (λ (ho : ℝ), (0:ℝ) ) =o[𝓝 0] λ (ho : ℝ), ho ,
  {simp, },  
  let k:= is_o.max ho h,
  simp at k,
  exact k,
  sorry,
end



end asymptotics

