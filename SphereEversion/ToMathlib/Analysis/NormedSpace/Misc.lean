import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import SphereEversion.ToMathlib.Analysis.Calculus.AffineMap

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]

open Set Function Metric AffineMap

open scoped Classical

noncomputable section

variable [FiniteDimensional ℝ F]

theorem LocalHomeomorph.exists_contDiff_source_univ_target_subset_ball (c : F) (r : ℝ) :
    ∃ f : LocalHomeomorph F F, ContDiff ℝ ⊤ f ∧ ContDiffOn ℝ ⊤ f.symm f.target ∧
      f.source = univ ∧ (0 < r → f.target ⊆ ball c r) ∧ f 0 = c := by
  by_cases hr : 0 < r
  · let e := toEuclidean (E := F)
    let e' := e.toHomeomorph
    rcases Euclidean.nhds_basis_ball.mem_iff.1 (ball_mem_nhds c hr) with ⟨ε, ε₀, hε⟩
    set f := (e'.transLocalHomeomorph (.univBall (e c) ε)).transHomeomorph e'.symm
    have hf : f.target = Euclidean.ball c ε
    · rw [transHomeomorph_target, Homeomorph.transLocalHomeomorph_target, univBall_target _ ε₀]
      rfl
    refine ⟨f, ?_, ?_, ?_, fun _ ↦ ?_, ?_⟩
    · exact e.symm.contDiff.comp <| contDiff_univBall.comp e.contDiff
    · exact e.symm.contDiff.comp_contDiffOn <| contDiffOn_univBall_symm.comp
        e.contDiff.contDiffOn hf.subset
    · rw [transHomeomorph_source, Homeomorph.transLocalHomeomorph_source, univBall_source]; rfl
    · rwa [hf]
    · simp
  · use (IsometryEquiv.vaddConst c).toHomeomorph.toLocalHomeomorph, contDiff_id.add contDiff_const,
      contDiffOn_id.sub contDiffOn_const
    simp [hr]

/-- A variant of `inner_product_space.diffeomorph_to_nhd` which provides a function satisfying the
weaker condition `range_diffeomorph_to_nhd_subset_ball` but which applies to any `normed_space`.

In fact one could demand this stronger property but it would be more work and we don't need it. -/
def diffeomorphToNhd (c : F) (r : ℝ) : LocalHomeomorph F F :=
  (LocalHomeomorph.exists_contDiff_source_univ_target_subset_ball c r).choose

@[simp]
theorem diffeomorphToNhd_source (c : F) (r : ℝ) : (diffeomorphToNhd c r).source = univ :=
  (LocalHomeomorph.exists_contDiff_source_univ_target_subset_ball c r).choose_spec.2.2.1

@[simp]
theorem diffeomorphToNhd_apply_zero (c : F) (r : ℝ) : diffeomorphToNhd c r 0 = c :=
  (LocalHomeomorph.exists_contDiff_source_univ_target_subset_ball c r).choose_spec.2.2.2.2

theorem target_diffeomorphToNhd_subset_ball (c : F) {r : ℝ} (hr : 0 < r) :
    (diffeomorphToNhd c r).target ⊆ ball c r :=
  (LocalHomeomorph.exists_contDiff_source_univ_target_subset_ball c r).choose_spec.2.2.2.1 hr

@[simp]
theorem range_diffeomorphToNhd_subset_ball (c : F) {r : ℝ} (hr : 0 < r) :
    range (diffeomorphToNhd c r) ⊆ ball c r := by
  erw [← image_univ, ← diffeomorphToNhd_source c r, LocalEquiv.image_source_eq_target]
  exact target_diffeomorphToNhd_subset_ball c hr

@[simp]
theorem contDiff_diffeomorphToNhd (c : F) (r : ℝ) {n : ℕ∞} :
    ContDiff ℝ n <| diffeomorphToNhd c r :=
  (LocalHomeomorph.exists_contDiff_source_univ_target_subset_ball c r).choose_spec.1.of_le le_top

@[simp]
theorem contDiffOn_diffeomorphToNhd_inv (c : F) (r : ℝ) {n : ℕ∞} :
    ContDiffOn ℝ n (diffeomorphToNhd c r).symm (diffeomorphToNhd c r).target :=
  (LocalHomeomorph.exists_contDiff_source_univ_target_subset_ball c r).choose_spec.2.1.of_le le_top
