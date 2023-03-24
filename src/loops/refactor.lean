import to_mathlib.data.set.prod
import to_mathlib.data.set.lattice
import to_mathlib.data.nat.basic
import to_mathlib.topology.constructions
import to_mathlib.topology.germ

import global.indexing
import global.localized_construction
import loops.surrounding

open set filter  metric prod
open_locale topology unit_interval

/-!
Notes by Patrick:

The goal of this file is to explore how to prove `exists_surrounding_loops` (or rather its version
with `C = U = univ` which is the only needed case) in a way that uncouples the general
topological argument from the things specific to loops. The general lemma is meant to
be something like `inductive_construction'` below.
-/


section inductive_construction
/-!
Notes by Patrick:

In this section, I took lemmas that used to exist when I worked on the inductive construction
refactor. In particular there is the lemma which can't quite be used to prove
`inductive_htpy_construction`, namely `inductive_construction`.

In that lemma, the covering is fixed. Lemma `inductive_construction'`, to be proven, is meant
to combine this with an argument using local existence and exhaustions.
-/

lemma index_type.tendsto_coe_at_top (N : ℕ) : tendsto (coe : ℕ → index_type N) at_top at_top :=
tendsto_at_top_at_top.mpr
  (λ i, ⟨indexing.to_nat i, λ n hn,(indexing.from_to i) ▸ indexing.coe_mono hn⟩)

lemma locally_finite.exists_forall_eventually_of_indexing
  {α X ι : Type*} [topological_space X] [linear_order ι] [indexing ι] {f : ℕ → X → α}
  {V : ι → set X} (hV : locally_finite V)
  (h : ∀ n : ℕ, ∀ x ∉ V ((n + 1) : ℕ), f (n + 1) x = f n x)
  (h' : ∀ n : ℕ, ((n+1 : ℕ) : ι) = n → f (n + 1) = f n) :
  ∃ (F : X → α), ∀ (x : X), ∀ᶠ (n : ℕ) in filter.at_top, f n =ᶠ[𝓝 x] F :=
begin
  let π :  ℕ → ι := indexing.from_nat,
  choose U hUx hU using hV,
  choose i₀ hi₀ using λ x, (hU x).bdd_above,
  let n₀ : X → ℕ := indexing.to_nat ∘ i₀,
  have key : ∀ {x} {n}, n ≥ n₀ x → ∀ {y}, y ∈ U x → f n y = f (n₀ x) y,
  { intros x n hn,
    rcases le_iff_exists_add.mp hn with ⟨k, rfl⟩, clear hn,
    intros y hy,
    induction k with k hk,
    { simp },
    { rw ← hk, clear hk,
      have : ∀ n, π n < π (n+1) ∨ π n = π (n+1),
      exact λ n, lt_or_eq_of_le (indexing.mono_from n.le_succ),
      rcases this (n₀ x + k) with H | H ; clear this,
      { have ineq : π (n₀ x + k + 1) > i₀ x,
        { suffices : i₀ x ≤ π (n₀ x + k), from lt_of_le_of_lt this H,
          rw ← indexing.from_to (i₀ x),
          exact indexing.mono_from le_self_add },
        apply h,
        rintro (hy' : y ∈ V (π (n₀ x + k + 1))),
        have := hi₀ x ⟨y, ⟨hy', hy⟩⟩, clear hy hy',
        exact lt_irrefl _ (lt_of_le_of_lt this ineq) },
      { erw [← (h' _ H.symm)],
        refl } } },
  refine ⟨λ x, f (n₀ x) x, λ x, _⟩,
  change ∀ᶠ (n : ℕ) in at_top, f n =ᶠ[𝓝 x] λ (y : X), f (n₀ y) y,
  apply (eventually_gt_at_top (n₀ x)).mono (λ n hn, _),
  apply mem_of_superset (hUx x) (λ y hy, _),
  change f n y = f (n₀ y) y,
  calc f n y = f (n₀ x) y : key hn.le hy
  ... = f (max (n₀ x) (n₀ y)) y : (key (le_max_left _ _) hy).symm
  ... = f (n₀ y) y : key (le_max_right _ _) (mem_of_mem_nhds $ hUx y)
end

lemma inductive_construction {X Y : Type*} [topological_space X]
  {N : ℕ} {U K : index_type N → set X}
  (P₀ P₁ : Π x : X, germ (𝓝 x) Y → Prop)
  (U_fin : locally_finite U) (K_cover : (⋃ i, K i) = univ)
  (init : ∃ f : X → Y, ∀ x, P₀ x f)
  (ind : ∀ (i : index_type N) (f : X → Y), (∀ x, P₀ x f) → (∀ x ∈ ⋃ j < i, K j, P₁ x f) →
    ∃ f' : X → Y, (∀ x, P₀ x f') ∧ (∀ x ∈ ⋃ j ≤ i, K j, P₁ x f') ∧ ∀ x ∉ U i, f' x = f x) :
    ∃ f : X → Y, ∀ x, P₀ x f ∧ P₁ x f :=
begin
  let P : ℕ → (X → Y) → Prop :=
    λ n f, (∀ x, P₀ x f) ∧ ∀ x ∈ (⋃ i ≤ (n : index_type N) , K i), P₁ x f,
  let Q : ℕ → (X → Y) → (X → Y) → Prop :=
    λ n f f', ((((n+1:ℕ) : index_type N) = n) → f' = f) ∧ ∀ x ∉ U (n + 1 : ℕ), f' x = f x,
  obtain ⟨f, hf⟩ : ∃ f : ℕ → X → Y, ∀ n, P n (f n) ∧ Q n (f n) (f $ n + 1),
  { apply exists_by_induction',
    { dsimp [P],
      cases init with f₀ hf₀,
      rcases ind 0 f₀ hf₀ _ with ⟨f', h₀f', h₁f', hf'⟩,
      use [f', h₀f'],
      intros x hx,
      apply h₁f' _ hx,
      have : (⋃ (j : index_type N) (H : j < 0), K j) = ∅,
      { simp [index_type.not_lt_zero] },
      simp only [this, mem_empty_iff_false, is_empty.forall_iff, implies_true_iff] },
    { rintros n f ⟨h₀f, h₁f⟩,
      rcases index_type.lt_or_eq_succ N n with hn | hn,
      { simp_rw index_type.le_or_lt_succ hn at h₁f,
        rcases ind (n+1 : ℕ) f h₀f h₁f with ⟨f', h₀f', h₁f', hf'⟩,
        exact ⟨f', ⟨h₀f', h₁f'⟩, ⟨λ hn', (hn.ne hn'.symm).elim, hf'⟩⟩ },
      { simp only [hn] at h₁f,
        exact ⟨f, ⟨h₀f, h₁f⟩, λ hn, rfl, λ x hx, rfl⟩ } } },
  dsimp only [P, Q] at hf,
  simp only [forall_and_distrib] at hf,
  rcases hf with ⟨⟨h₀f, h₁f⟩, hf, hf'⟩,
  rcases U_fin.exists_forall_eventually_of_indexing hf' hf with ⟨F, hF⟩,
  refine ⟨F, λ x, _⟩,
  have : ∀ᶠ (n : ℕ) in at_top, x ∈ ⋃ i ≤ (n : index_type N), K i,
  { have : x ∈ ⋃ (i : index_type N), K i := K_cover.symm ▸ (mem_univ x),
    rcases mem_Union.mp this with ⟨i, hi⟩,
    apply (filter.tendsto_at_top.mp (index_type.tendsto_coe_at_top N) i).mono,
    intros n hn,
    exact mem_Union₂.mpr ⟨i, hn, hi⟩ },
  rcases eventually_at_top.mp ((hF x).and this) with ⟨n₀, hn₀⟩,
  rcases hn₀ n₀ le_rfl with ⟨hx, hx'⟩,
  rw germ.coe_eq.mpr hx.symm,
  exact ⟨h₀f n₀ x, h₁f n₀ x hx'⟩
end

/-- We are given a suitably nice topological space `X` and two local constraints `P₀` and `P₁`
on maps from `X` to some type `Y`. All maps entering the discussion are required to statisfy `P₀`
everywhere. The goal is to turn a map `f₀` satisfying `P₁` near a compact set `K` into
one satisfying everywhere without changing `f₀` near `K`. The assumptions are:
* For every `x` in `X` there is a map which satisfies `P₁` near `x`
* One can patch two maps `f₁ f₂` satisfying `P₁` on open sets `U₁` and `U₂` respectively
  into a map satisfying `P₁` on `K₁ ∪ K₂` for any compact sets `Kᵢ ⊆ Uᵢ`.
One can probably deduce this version from the version where `K` is empty for some
other `P₀`. -/
lemma inductive_construction' {X Y : Type*} [topological_space X]
  [t2_space X] [locally_compact_space X] [sigma_compact_space X]
  (P₀ P₁ : Π x : X, germ (𝓝 x) Y → Prop)
  {K : set X} (hK : is_compact K)
  {f₀ : X → Y} (hP₀f₀ : ∀ x, P₀ x f₀) (hP₁f₀ : ∀ᶠ x near K, P₁ x f₀)
  (loc : ∀ x, ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ᶠ x' in 𝓝 x, P₁ x f)
  (ind : ∀ {U₁ U₂ K₁ K₂ : set X} {f₁ f₂ : X → Y}, is_open U₁ → is_open U₂ →
     is_compact K₁ → is_compact K₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ → (∀ x, P₀ x f₁) → (∀ x, P₀ x f₂) →
     (∀ x ∈ U₁, P₁ x f₁) → (∀ x ∈ U₂, P₁ x f₂) →
     ∃ f : X → Y, (∀ x, P₀ x f₁) ∧ (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ (∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x)) :
    ∃ f : X → Y, (∀ x, P₀ x f ∧ P₁ x f) ∧ ∀ᶠ x near K, f x = f₀ x :=
begin

  sorry
end

end inductive_construction

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] {F : Type*}
  [normed_add_comm_group F] [normed_space ℝ F] {g b : E → F} {U K C : set E} {Ω : set (E × F)}
  [finite_dimensional ℝ E] [finite_dimensional ℝ F]

-- Patrick doesn't understand why `apply_instance` doesn't work in the next example.
-- Because of this issue, the next definition can't use `↿γ`.
example : function.has_uncurry (E → ℝ → loop F) (E × ℝ × ℝ) F :=
begin
  apply function.has_uncurry_induction,
end

def continuous_germ {x : E} (φ : germ (𝓝 x) (ℝ → loop F)) : Prop :=
quotient.lift_on' φ (λ γ, ∀ (t s : ℝ), continuous_at (λ p : E × ℝ × ℝ, γ p.1 p.2.1 p.2.2) (x, t, s))
sorry

variables (g b Ω)

structure loop_family_germ (x : E) (φ : germ (𝓝 x) (ℝ → loop F)) : Prop :=
(base : ∀ t, φ.value t 0 = b x)
(t₀ : ∀ s, φ.value 0 s = b x)
(proj_I : ∀ (t : ℝ) (s : ℝ), φ.value (proj_I t) s = φ.value t s)
(cont : continuous_germ φ)

structure surrounding_family_germ (x : E) (φ : germ (𝓝 x) (ℝ → loop F)) : Prop :=
(surrounds : (φ.value 1).surrounds $ g x)
(val_in' : ∀ (t ∈ I) (s ∈ I), (x, φ.value t s) ∈ Ω)

variables {g b Ω}

lemma surrounding_family_in_iff_germ {γ : E → ℝ → loop F} :
  surrounding_family_in g b γ C Ω ↔ (∀ x, loop_family_germ b x γ) ∧
                                    (∀ x ∈ C, surrounding_family_germ g Ω x γ) :=
sorry

lemma exists_surrounding_loops'
  (hK : is_compact K)
  (hΩ_op : is_open Ω)
  (hg : ∀ x, continuous_at g x) (hb : continuous b)
  (hconv : ∀ x, g x ∈ convex_hull ℝ (connected_component_in (prod.mk x ⁻¹' Ω) $ b x))
  {γ₀ :  E → ℝ → loop F}
  (hγ₀_surr : ∃ V ∈ 𝓝ˢ K, surrounding_family_in g b γ₀ V Ω) :
  ∃ γ : E → ℝ → loop F, surrounding_family_in g b γ univ Ω ∧ ∀ᶠ x in 𝓝ˢ K, γ x = γ₀ x :=
begin
  simp only [surrounding_family_in_iff_germ, mem_univ, forall_true_left, ← forall_and_distrib],
  apply inductive_construction' (loop_family_germ b) (surrounding_family_germ g Ω) hK,
  {
    sorry },
  {
    sorry },
  { -- This is meant to use a version of `local_loops`.
    sorry },
  { intros U₁ U₂ K₁  K₂ γ₁ γ₂ hU₁ hU₂ hK₁ hK₂ hKU₁ hKU₂ hγ₁ hγ₂ h'γ₁ h'γ₂,
    -- Note: `extend_loops` isn't good enough because it says nothing outside U₁ and U₂, not
    -- even `loop_family_germ`
    sorry },
end