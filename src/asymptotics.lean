import analysis.calculus.cont_diff
import linear_algebra.matrix.pos_def
open_locale big_operators matrix
noncomputable theory 

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


lemma max_1_lip (a b c d :ℝ ) : |(max 0 (max a b))-(max 0 (max c d))|≤ max (|a-c|) (|b-d|) :=
begin

let h1 := abs_max_sub_max_le_abs (max a b) (max c d) 0,
let h2 := abs_max_sub_max_le_max a b c d,
rw max_comm,
rw max_comm 0 (max c d),
exact le_trans h1 h2,
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
  let max_diff := abs_max_sub_max_le_max (u x - u (x - h))  (u x - u (x + h)) (h*u') (-(h * u')) ,
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
rw is_o_iff,-- réécriture de la definition de o dans l'objectif:
--f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → (∀ᶠ (x : α) in l, ‖f x‖ ≤ c * ‖g x‖).
  intros c hc,-- On fixe une constante de domination c avec l'hypothèse hc qu'elle est positive.
  rw eventually_nhds_iff,--on explicité plus précisément l'objectif avec la propriété eventually_nhds_iff:
  --(∀ᶠ (x : α) in 𝓝 a, p x) ↔ ∃ (t : set α), (∀ (x : α), x ∈ t → p x) ∧ is_open t ∧ a ∈ t.
  -- les o sont définit a partir du filtre de l'ensemble des voisinage de a.
let h1 := (my_lemma u u' x).1 hu,-- A patir de la dérivabilité de u, on definit h1: u(x)-u(x+h)-hu'(x)=o(h).
rw is_o_iff at h1,-- réecriture de h1
-- Après simplification, on a h1:
-- ∀ ⦃c : ℝ⦄, 0 < c → (∀ᶠ (x_1 : ℝ) in 𝓝 0, ‖u (x + x_1) - u x - x_1 * u'‖ ≤ c * ‖x_1‖).
specialize h1 hc,-- on applique h1 à c.
rw eventually_nhds_iff at h1,-- simplification dans h1 avec eventually_nhds_iff(voir si dessus); h1 se réécrit:
-- ∃ (t : set ℝ), (∀ (x_1 : ℝ), x_1 ∈ t → ‖u (x + x_1) - u x - x_1 * u'‖ ≤ c * ‖x_1‖) ∧ is_open t ∧ 0 ∈ t.
rcases h1 with ⟨V,  ⟨H, V_open, V0⟩⟩,-- on fixe V l'enseble dont h1 donne l'existance. 
-- On definit la proposition H: ∀ (x_1 : ℝ), x_1 ∈ V → ‖u (x + x_1) - u x - x_1 * u'‖ ≤ c * ‖x_1‖.
let W:= V ∩ -V,--On définit un nouvel ensemble W sur lequel on a les diffférences finis à droite et à gauche.
-- On cherche à prouver: (t : set ℝ), (∀ (x_1 : ℝ), x_1 ∈ t 
-- → ‖max 0 (max (u x - u (x - x_1)) (u x - u (x + x_1))) - |x_1 * u'|‖ ≤ c * ‖x_1‖) ∧ is_open t ∧ 0 ∈ t.
use W,-- On utilise W dans l'objectif.
split,-- On sépare les propositions à prouver.
{intros h Wh,
--Dans cette partie on doit démontrer: ‖max 0 (max (u x - u (x - h)) (u x - u (x + h))) - |h * u'|‖ ≤ c * ‖h‖.
  rw abs_eq_max_neg, -- On utilise  |a| = max a (-a).
  repeat{rw real.norm_eq_abs},  -- On utilise ‖r‖ = |r|.
  --On utilise la 1-lip du max aux bons éléments.
  let max_diff := max_1_lip (u x - u (x - h))  (u x - u (x + h)) (h*u') (-(h * u')) ,
  --On effectue plusieur récriture pour remplacer max 0 (max (h * u') (-(h * u')) par max (h * u') (-(h * u') dans max_diff.
  -- C'est laborieu, je n'ai pas trouvé de preuve plus courte.
  rw ← abs_eq_max_neg at max_diff,
  let P:= abs_nonneg (h * u'),
  rw max_eq_right P at max_diff,
  rw abs_eq_max_neg at max_diff,
  rw abs_eq_max_neg at max_diff,
  rw ← abs_eq_max_neg at max_diff,
  let diffp := H h Wh.1,-- On definit diffp comme H(voir ligne 180) appliqué à h.
  repeat{rw real.norm_eq_abs at diffp},-- On utilise ‖r‖ = |r| dans diffp.
  let diffm := H (-h) Wh.2,---- On definit diffp comme H appliqué à -h.
  repeat{rw real.norm_eq_abs at diffm},-- On utilise ‖r‖ = |r| dans diffm.
  rw abs_neg at diffm,-- On utilise  | -a| = |a| dans diffm.
  rw ← abs_neg at diffm,-- On utilise  | -a| = |a| dans diffm.
  rw ← abs_neg at diffp,-- On utilise  | -a| = |a| dans diffp.
  -- On utilise la propriété a ≤ c → b ≤ c → max a b ≤ c pour définir une nouvelle proposition.
  -- F:max |-(u (x + h) - u x - h * u')| |-(u (x + -h) - u x - -h * u')| ≤ c * |h|
  let F := max_le diffp diffm,
  rw max_comm at F,-- On utilise la commutativité du max dans F.
  apply le_trans max_diff _,-- On ulitise la transitivité de la relation d'ordre pour conclure
  apply le_trans _ F,
  --Après quelques réécriture cette partie de la preuve est finie.
  simp only [← sub_eq_add_neg],
  apply le_of_eq,
  congr' 2; ring },
split,
{-- Dans cette parti on démontre que W est ouvert.
  have V_neg_open := V_open.neg,-- On montre que -V est ouvert.
  apply is_open.inter V_open V_neg_open,-- L'intersection de deux ouverts est ouvert.
  },
{-- Dans cette partie on montre que 0∈W.
  simp,-- On utilise la tactique simp pour que Lean prouve par lui même le résultats, c'est un succé.
exact V0,},
end



open finset matrix
local notation `ℝ2` := (fin 2) → ℝ 

#check has_fderiv_at

 def upwind_fd (u : ℝ2 → ℝ) (x v:ℝ2) :=
max (0:ℝ) (max ((u x - u (x - v)) ) ((u x - u (x + v) )))

def j (u : ℝ2 → ℝ) (x e:ℝ2) (t: ℝ):= u(x+t•e)




-- TODO : replace du : ℝ2 →L[ℝ] ℝ with gradu : ℝ2

lemma max_o_u_2D (u : ℝ2 → ℝ) (x e : ℝ2) (du : ℝ2 →L[ℝ] ℝ) (hu : has_fderiv_at u du x) :
(λ (h :ℝ), upwind_fd u x (h•e) - |h *(du e)|  )
 =o[𝓝 0] λ (h : ℝ), h :=
begin
let v : ℝ → ℝ2 := λ t:ℝ,  x+t•e,
have hv : has_deriv_at v e 0,
{
  unfold has_deriv_at,
  unfold has_deriv_at_filter,
  unfold has_fderiv_at_filter,
  simp,
},
have hubis : has_fderiv_at u du (v 0), {
simp [v],simp,exact hu,
},
let k1:= has_fderiv_at.comp_has_deriv_at 0 hubis hv,
let h:= max_0_u (u.comp v) 0 (du e) k1,
simp only [v, function.comp_app, zero_smul, add_zero, zero_sub, neg_smul, zero_add] at h,
simp_rw ← sub_eq_add_neg at h,
unfold upwind_fd,
exact h,
end


variables (μ : fin 3 → ℝ) (e : (fin 3) → ℝ2) (D : matrix (fin 2) (fin 2) ℝ) 
variables (Dsymm : D.is_symm)

-- TODO : how to write that D admits this decomposition ?
example : D = ∑ i , μ i • vec_mul_vec (e i) (e i) :=sorry
variable (hD : D = ∑ i : (fin 3), μ i • vec_mul_vec (e i) (e i) )

-- example (du:ℝ2) : is_bounded_linear_map 

example (f g:ℝ→ ℝ)(hdiff : (f-g) =o[𝓝 0] λ h,h) (hsum : (f+g)  =O[𝓝 (0:ℝ)] (1:ℝ→ℝ)) : 
( f^2-g^2) =o[𝓝 0] λ h,h :=
begin
let h:= is_o.mul_is_O hdiff hsum,
simp at h,
simp_rw[] at h,
end

-- MAIN OBJECTIVE --
example (u:ℝ2 → ℝ) (x : ℝ2) (du : ℝ2 →L[ℝ] ℝ) (gradu : ℝ2)
(hu : has_fderiv_at u du x ) (comp : ∀ x, du x = gradu ⬝ᵥ x):
(λ h, (∑ i, μ i * (upwind_fd u x (h•e i))^2) - h^2 * gradu ⬝ᵥ D.mul_vec gradu)
=o[𝓝 (0 : ℝ)] λ h, h^2
:= begin
sorry,
end

/- Deja fait
example (u : ℝ2 → ℝ) (x e : ℝ2) (l:ℝ2 →L[ℝ] ℝ) (hu : has_fderiv_at u l x) :
(λ (h :ℝ), max 0 (max ((u x - u (x - h • e)) ) ((u x - u (x + h • e) ))) - |h *(l e)|  )
=o[𝓝 0] λ (h : ℝ), h :=
begin
sorry,
end
-/


end asymptotics

