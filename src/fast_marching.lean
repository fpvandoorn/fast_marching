import topology.instances.ereal

noncomputable theory
open topological_space

variables {X : Type*} [finite X]

local notation `U` := X → ereal
local notation `∞` := (⊤ : ereal)

def cut_lt (u : U) (t : ereal) : X → ereal :=
λ x, if u x < t then u x else ∞

def cut_le (u : U) (t : ereal) : X → ereal :=
λ x, if u x ≤ t then u x else ∞

def is_causal_with (Λ : U → U) (δ : ereal) :=
∀ (u v : U) (t : ereal), cut_lt u t = cut_lt v t →
  cut_le (Λ u) (t + δ) = cut_le (Λ v) (t + δ)

---

variables {X} (Λ : U → U) (δ : ereal) (hδ : δ > 0)

def t : ℕ → ereal :=
λ n, (⨅ x, Λ (λ x', ∞) x) + n • δ

noncomputable def u : ℕ → U
| 0 := λ x, ∞
| (n + 1) := Λ (cut_le (u n) (t Λ δ n))

----

def monotone2 (F : X → ℝ → (X → ℝ) → ℝ) : Prop :=
∀ x v₁ v₂ p₁ p₂, v₁ ≤ v₂ → p₁ ≤ p₂ → F x v₁ p₁ ≤ F x v₂ p₂

def is_causal (F : X → ℝ → (X → ℝ) → ℝ) : Prop :=
∀ x v p, F x v p = F x v (λ x', max 0 (p x'))

def F_to_Λ (F : X → ℝ → (X → ℝ) → ℝ) (u : X → ℝ) (x : X) : ℝ :=
Sup { l | F x l (λ y, l - u y) ≤ 0 }

lemma monotone_iff (F : X → ℝ → (X → ℝ) → ℝ) : monotone2 F ↔ monotone (F_to_Λ F) :=
sorry

-- not sure if this is true - this is just to show how we can talk about continuity
-- note, if `f : A → B → C` then `f.uncurry : A × B → C`
lemma continuous_iff (F : X → ℝ → (X → ℝ) → ℝ) :
  (∀ x, continuous ((F x).uncurry)) ↔ continuous (F_to_Λ F) :=
sorry
