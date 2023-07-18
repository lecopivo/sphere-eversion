import SphereEversion.ToMathlib.Partition

noncomputable section

open scoped Topology Filter Manifold BigOperators

open Set Function Filter

section

variable {ι : Type _}

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type _}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type _} [TopologicalSpace M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M] [SigmaCompactSpace M] [T2Space M]

section

variable {F : Type _} [AddCommGroup F] [Module ℝ F]

theorem exists_of_convex {P : (Σ x : M, Germ (𝓝 x) F) → Prop}
    (hP : ∀ x, ReallyConvex (smoothGerm I x) {φ | P ⟨x, φ⟩})
    (hP' : ∀ x : M, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, P ⟨x', f⟩) : ∃ f : M → F, ∀ x, P ⟨x, f⟩ :=
  by
  replace hP' : ∀ x : M, ∃ f : M → F, ∃ U ∈ 𝓝 x, ∀ x' ∈ U, P ⟨x', f⟩
  · intro x
    rcases hP' x with ⟨f, hf⟩
    exact ⟨f, {x' | P ⟨x', ↑f⟩}, hf, fun _ => id⟩
  choose φ U hU hφ using hP'
  rcases SmoothBumpCovering.exists_isSubordinate I isClosed_univ fun x h => hU x with ⟨ι, b, hb⟩
  let ρ := b.to_smooth_partition_of_unity
  refine' ⟨fun x : M => ∑ᶠ i, ρ i x • φ (b.c i) x, fun x₀ => _⟩
  let g : ι → germ (𝓝 x₀) F := fun i => φ (b.c i)
  have :
    (fun x : M => ∑ᶠ i, ρ i x • φ (b.c i) x : germ (𝓝 x₀) F) ∈
      reallyConvexHull (smoothGerm I x₀) (g '' ρ.fintsupport x₀) :=
    ρ.germ_combine_mem fun i x => φ (b.c i) x
  simp_rw [reallyConvex_iff_hull] at hP
  apply hP x₀; clear hP
  have H : g '' ↑(ρ.fintsupport x₀) ⊆ {φ : (𝓝 x₀).Germ F | P ⟨x₀, φ⟩} :=
    by
    rintro _ ⟨i, hi, rfl⟩
    exact
      hφ _ _
        (SmoothBumpCovering.IsSubordinate.toSmoothPartitionOfUnity hb i <|
          (ρ.mem_fintsupport_iff _ i).mp hi)
  exact reallyConvexHull_mono H this

end

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G : Type _} [NormedAddCommGroup G] [NormedSpace ℝ G] {HG : Type _} [TopologicalSpace HG]
  (IG : ModelWithCorners ℝ G HG) {N : Type _} [TopologicalSpace N] [ChartedSpace HG N]
  [SmoothManifoldWithCorners IG N]

local notation "𝓒" => ContMDiff I 𝓘(ℝ, F)

local notation "𝓒_on" => ContMDiffOn I 𝓘(ℝ, F)

variable (I)

theorem reallyConvex_contMDiffAt (x : M) (n : ℕ∞) :
    ReallyConvex (smoothGerm I x) {φ : Germ (𝓝 x) F | φ.ContMDiffAt I n} := by
  classical
  rw [Nontrivial.reallyConvex_iff]
  rintro w w_pos w_supp w_sum
  have : (support w).Finite := support_finite_of_finsum_eq_one w_sum
  let fin_supp := this.to_finset
  have : (support fun i : (𝓝 x).Germ F => w i • i) ⊆ fin_supp := by rw [Set.Finite.coe_toFinset];
    exact support_smul_subset_left w id
  rw [finsum_eq_sum_of_support_subset _ this]
  clear this
  apply Filter.Germ.ContMDiffAt.sum
  intro φ hφ
  refine' (smoothGerm.contMDiffAt _).smul (w_supp _)
  simpa [fin_supp] using hφ

theorem exists_contMDiff_of_convex {P : M → F → Prop} (hP : ∀ x, Convex ℝ {y | P x y}) {n : ℕ∞}
    (hP' : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ f : M → F, 𝓒_on n f U ∧ ∀ x ∈ U, P x (f x)) :
    ∃ f : M → F, 𝓒 n f ∧ ∀ x, P x (f x) :=
  by
  let PP : (Σ x : M, germ (𝓝 x) F) → Prop := fun p => p.2.ContMDiffAt I n ∧ P p.1 p.2.value
  have hPP : ∀ x, ReallyConvex (smoothGerm I x) {φ | PP ⟨x, φ⟩} :=
    by
    intro x
    apply ReallyConvex.inter
    apply reallyConvex_contMDiffAt
    dsimp only
    let v : germ (𝓝 x) F →ₛₗ[smoothGerm.valueRingHom I x] F := Filter.Germ.valueₛₗ I x
    change ReallyConvex (smoothGerm I x) (v ⁻¹' {y | P x y})
    dsimp only [← smoothGerm.valueOrderRingHom_toRingHom] at v
    apply ReallyConvex.preimageₛₗ
    rw [reallyConvex_iff_convex]
    apply hP
  have hPP' : ∀ x, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩ :=
    by
    intro x
    rcases hP' x with ⟨U, U_in, f, hf, hf'⟩
    use f
    filter_upwards [eventually_mem_nhds.mpr U_in] with y hy
    exact ⟨hf.cont_mdiff_at hy, hf' y (mem_of_mem_nhds hy)⟩
  rcases exists_of_convex hPP hPP' with ⟨f, hf⟩
  exact ⟨f, fun x => (hf x).1, fun x => (hf x).2⟩

theorem exists_contDiff_of_convex {P : E → F → Prop} (hP : ∀ x, Convex ℝ {y | P x y}) {n : ℕ∞}
    (hP' : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ f : E → F, ContDiffOn ℝ n f U ∧ ∀ x ∈ U, P x (f x)) :
    ∃ f : E → F, ContDiff ℝ n f ∧ ∀ x, P x (f x) :=
  by
  simp_rw [← contMDiff_iff_contDiff]
  simp_rw [← contMDiffOn_iff_contDiffOn] at hP' ⊢
  exact exists_contMDiff_of_convex hP hP'

end

section

variable {E₁ E₂ E₃ E₄ F : Type _}

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]

variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]

variable [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]

variable [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [FiniteDimensional ℝ E₄]

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {H₁ M₁ H₂ M₂ H₃ M₃ H₄ M₄ : Type _}

variable [TopologicalSpace H₁] (I₁ : ModelWithCorners ℝ E₁ H₁)

variable [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [SmoothManifoldWithCorners I₁ M₁]

variable [SigmaCompactSpace M₁] [T2Space M₁]

variable [TopologicalSpace H₂] (I₂ : ModelWithCorners ℝ E₂ H₂)

variable [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [SmoothManifoldWithCorners I₂ M₂]

variable [TopologicalSpace H₃] (I₃ : ModelWithCorners ℝ E₃ H₃)

variable [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [SmoothManifoldWithCorners I₃ M₃]

variable [TopologicalSpace H₄] (I₄ : ModelWithCorners ℝ E₄ H₄)

variable [TopologicalSpace M₄] [ChartedSpace H₄ M₄] [SmoothManifoldWithCorners I₄ M₄]

local notation "𝓒" => ContMDiff (I₁.prod I₂) 𝓘(ℝ, F)

local notation "𝓒_on" => ContMDiffOn (I₁.prod I₂) 𝓘(ℝ, F)

theorem reallyConvex_contMDiffAtProd {x : M₁} (n : ℕ∞) :
    ReallyConvex (smoothGerm I₁ x) {φ : Germ (𝓝 x) (M₂ → F) | φ.ContMDiffAtProd I₁ I₂ n} := by
  classical
  rw [Nontrivial.reallyConvex_iff]
  rintro w w_pos w_supp w_sum
  have : (support w).Finite := support_finite_of_finsum_eq_one w_sum
  let fin_supp := this.to_finset
  have : (support fun i : (𝓝 x).Germ (M₂ → F) => w i • i) ⊆ fin_supp :=
    by
    rw [Set.Finite.coe_toFinset]
    exact support_smul_subset_left w id
  rw [finsum_eq_sum_of_support_subset _ this]
  clear this
  apply Filter.Germ.ContMDiffAtProd.sum
  intro φ hφ
  refine' (smoothGerm.contMDiffAt _).smul_prod (w_supp _)
  simpa [fin_supp] using hφ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[main_declaration]
theorem exists_contMDiff_of_convex₂ {P : M₁ → (M₂ → F) → Prop} (hP : ∀ x, Convex ℝ {f | P x f})
    {n : ℕ∞}
    (hP' :
      ∀ x : M₁,
        ∃ U ∈ 𝓝 x,
          ∃ f : M₁ → M₂ → F, 𝓒_on n (uncurry f) (U ×ˢ (univ : Set M₂)) ∧ ∀ y ∈ U, P y (f y)) :
    ∃ f : M₁ → M₂ → F, 𝓒 n (uncurry f) ∧ ∀ x, P x (f x) :=
  by
  let PP : (Σ x : M₁, germ (𝓝 x) (M₂ → F)) → Prop := fun p =>
    p.2.ContMDiffAtProd I₁ I₂ n ∧ P p.1 p.2.value
  have hPP : ∀ x, ReallyConvex (smoothGerm I₁ x) {φ | PP ⟨x, φ⟩} :=
    by
    intro x
    apply ReallyConvex.inter
    apply reallyConvex_contMDiffAtProd
    dsimp only
    let v : germ (𝓝 x) (M₂ → F) →ₛₗ[smoothGerm.valueRingHom I₁ x] M₂ → F := Filter.Germ.valueₛₗ I₁ x
    change ReallyConvex (smoothGerm I₁ x) (v ⁻¹' {y | P x y})
    dsimp only [← smoothGerm.valueOrderRingHom_toRingHom] at v
    apply ReallyConvex.preimageₛₗ
    rw [reallyConvex_iff_convex]
    apply hP
  have hPP' : ∀ x, ∃ f : M₁ → M₂ → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩ :=
    by
    intro x
    rcases hP' x with ⟨U, U_in, f, hf, hf'⟩
    use f
    filter_upwards [eventually_mem_nhds.mpr U_in] with y hy
    refine' ⟨fun z => hf.cont_mdiff_at (prod_mem_nhds hy univ_mem), hf' y (mem_of_mem_nhds hy)⟩
  rcases exists_of_convex hPP hPP' with ⟨f, hf⟩
  exact ⟨f, fun ⟨x, y⟩ => (hf x).1 y, fun x => (hf x).2⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem exists_contDiff_of_convex₂ {P : E₁ → (E₂ → F) → Prop} (hP : ∀ x, Convex ℝ {f | P x f})
    {n : ℕ∞}
    (hP' :
      ∀ x : E₁,
        ∃ U ∈ 𝓝 x,
          ∃ f : E₁ → E₂ → F,
            ContDiffOn ℝ n (uncurry f) (U ×ˢ (univ : Set E₂)) ∧ ∀ y ∈ U, P y (f y)) :
    ∃ f : E₁ → E₂ → F, ContDiff ℝ n (uncurry f) ∧ ∀ x, P x (f x) :=
  by
  simp_rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod] at hP'
  simp_rw [← contMDiff_iff_contDiff, modelWithCornersSelf_prod]
  rw [← chartedSpaceSelf_prod] at hP' ⊢
  -- Why does `simp_rw` not succeed here?
  exact exists_contMDiff_of_convex₂ 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) hP hP'

end

section

variable {ι : Type _}

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type _}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type _} [TopologicalSpace M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M] [SigmaCompactSpace M] [T2Space M]

open TopologicalSpace

example {f : E → ℝ} (h : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ ε : ℝ, ∀ x' ∈ U, 0 < ε ∧ ε ≤ f x') :
    ∃ f' : E → ℝ, ContDiff ℝ ⊤ f' ∧ ∀ x, 0 < f' x ∧ f' x ≤ f x :=
  by
  let P : E → ℝ → Prop := fun x t => 0 < t ∧ t ≤ f x
  have hP : ∀ x, Convex ℝ {y | P x y} := fun x => convex_Ioc _ _
  apply exists_contDiff_of_convex hP
  intro x
  rcases h x with ⟨U, U_in, ε, hU⟩
  exact ⟨U, U_in, fun x => ε, contDiffOn_const, hU⟩

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem convex_setOf_imp_eq (P : Prop) (y : F) : Convex ℝ {x : F | P → x = y} := by
  by_cases hP : P <;> simp [hP, convex_singleton, convex_univ]

-- lemma exists_smooth_and_eq_on_aux1 {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x) (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (is_open_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end
-- lemma exists_smooth_and_eq_on_aux2 {n : ℕ∞} {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x)
--   {s : set E} (hs : is_closed s) (hfs : ∃ U ∈ 𝓝ˢ s, cont_diff_on ℝ n f U)
--   (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (is_open_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end
theorem exists_smooth_and_eqOn {n : ℕ∞} {f : E → F} {ε : E → ℝ} (hf : Continuous f)
    (hε : Continuous ε) (h2ε : ∀ x, 0 < ε x) {s : Set E} (hs : IsClosed s)
    (hfs : ∃ U ∈ 𝓝ˢ s, ContDiffOn ℝ n f U) :
    ∃ f' : E → F, ContDiff ℝ n f' ∧ (∀ x, dist (f' x) (f x) < ε x) ∧ EqOn f' f s :=
  by
  have h0 : ∀ x, dist (f x) (f x) < ε x := fun x => by simp_rw [dist_self, h2ε]
  let P : E → F → Prop := fun x t => dist t (f x) < ε x ∧ (x ∈ s → t = f x)
  have hP : ∀ x, Convex ℝ {y | P x y} := fun x =>
    (convex_ball (f x) (ε x)).inter (convex_setOf_imp_eq _ _)
  obtain ⟨f', hf', hPf'⟩ := exists_contDiff_of_convex hP _
  · exact ⟨f', hf', fun x => (hPf' x).1, fun x => (hPf' x).2⟩
  · intro x
    obtain ⟨U, hU, hfU⟩ := hfs
    by_cases hx : x ∈ s
    · refine' ⟨U, mem_nhdsSet_iff_forall.mp hU x hx, _⟩
      refine' ⟨f, hfU, fun y _ => ⟨h0 y, fun _ => rfl⟩⟩
    · have : IsOpen {y : E | dist (f x) (f y) < ε y} := isOpen_lt (continuous_const.dist hf) hε
      exact
        ⟨_, (this.sdiff hs).mem_nhds ⟨h0 x, hx⟩, fun _ => f x, contDiffOn_const, fun y hy =>
          ⟨hy.1, fun h2y => (hy.2 h2y).elim⟩⟩

end

