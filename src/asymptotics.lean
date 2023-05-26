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
lemma my_lemma (f: ℝ→ℝ) (f':ℝ)(x:ℝ): has_deriv_at f f' x ↔ (λ (h : ℝ), f (x+h) - f x - h * f') =o[𝓝 0] λ (h : ℝ), h:=
begin
  rw has_deriv_at_iff_is_o,
  rw ← map_add_left_nhds_zero x,
  rw is_o_map,
  simp [(∘)],

end

/- Harder: prove the following result. It might be useful to first take a look at the following
theorems in mathlib, and to prove a variant of `has_deriv_at_iff_is_o` that is closer to
`has_fderiv_at_iff_is_o_nhds_zero`, where instead of working with `x` and `x - x'` you work with
`x + h` and `x`. -/
#check @has_deriv_at_iff_is_o
#check @has_fderiv_at_iff_is_o_nhds_zero

lemma max_1_lip (a b c d :ℝ ) : |(max a b)-(max c d)|≤ max (|a-b|) (|c-d|) :=
begin
sorry

end

#check max_1_lip


example (u : ℝ → ℝ) (x : ℝ) (hu : differentiable_at ℝ u x) :
  (λ h,  max 0 (max ((u x - u (x - h)) / h) ((u x - u (x + h) / h))) - |deriv u x|)
  =o[𝓝 0] λ h, h :=
begin
  have h : (λ (h : ℝ), (max ((u x - u (x - h)) / h) (u x - u (x + h) / h))- |deriv u x|  ) =o[𝓝 0] λ (h : ℝ),h,
  {rw is_o_iff,
  intros c hc,
  rw eventually_nhds_iff,
  split,
  split,
  intro y,
  rw ← max_sub_sub_right ((u x - u (x - y)) / y)  (u x - u (x + y) / y) (deriv u x),
  sorry,
  sorry,
  sorry,}
  have ho :  (λ (ho : ℝ) 0) =o[𝓝 0] λ (ho : ℝ),ho, 
  {}

end

end asymptotics

