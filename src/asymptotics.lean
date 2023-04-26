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
by { simp_rw [real.norm_eq_abs], exact abs_max_le_max_abs_abs }

/- Prove the following lemma. This requires some basic topology, in addition to the mentioned
lemmas. -/
lemma is_o.max (hu : u =o[𝓝 x] f) (hv : v =o[𝓝 x] f) : (λ x, max (u x) (v x)) =o[𝓝 x] f :=
begin
  simp_rw [is_o_iff, eventually_nhds_iff] at hu hv ⊢,
  intros c hc,
  rcases hu hc with ⟨t, ht, h2t, hxt⟩,
  rcases hv hc with ⟨s, hs, h2s, hxs⟩,
  refine ⟨t ∩ s, λ x hx, _, h2t.inter h2s, ⟨hxt, hxs⟩⟩,
  refine norm_max_le_max_norm_norm.trans _,
  rw [max_le_iff],
  exact ⟨ht x hx.1, hs x hx.2⟩,
end

/- Harder: prove the following result. It might be useful to first take a look at the following
theorems in mathlib, and to prove a variant of `has_deriv_at_iff_is_o` that is closer to
`has_fderiv_at_iff_is_o_nhds_zero`, where instead of working with `x` and `x - x'` you work with
`x + h` and `x`. -/
#check @has_deriv_at_iff_is_o
#check @has_fderiv_at_iff_is_o_nhds_zero
example (u : ℝ → ℝ) (x : ℝ) (hu : differentiable_at ℝ u x) :
  (λ h,  max 0 (max ((u x - u (x - h)) / h) ((u x - u (x + h) / h))) - deriv u x)
  =o[𝓝 x] λ h, h :=
begin
  sorry
end

end asymptotics