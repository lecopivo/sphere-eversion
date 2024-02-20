import Mathlib.Tactic.FunProp.ContDiff

/-!
# fun_prop configuration (about differentiability)
Additional mathlib lemmas which should be tagged @[fun_prop].

TODO: PR them to mathlib, to their appropriate files
-/

attribute [fun_prop] ContDiff.clm_apply
attribute [fun_prop] IsBoundedBilinearMap.contDiff
attribute [fun_prop] Differentiable.continuous
attribute [fun_prop] ContDiff.continuous



section ForgotToUnfoldFunctionUncurry

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E₁ : Type _} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] {E₂ : Type _}
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] {E' : Type _} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : ℕ∞}


-- I forgot to mark `Function.uncurry` to be reducible in `fun_prop` so I have
protected theorem ContDiff.fderiv' {f : E → F → G} {g : E → F} {n m : ℕ∞}
    (hf : ContDiff 𝕜 m ↿f) (hg : ContDiff 𝕜 n g) (hnm : n + 1 ≤ m) :
    ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt hnm

theorem ContDiff.fderiv_apply' {f : E → F → G} {g k : E → F} {n m : ℕ∞}
    (hf : ContDiff 𝕜 m ↿f) (hg : ContDiff 𝕜 n g) (hk : ContDiff 𝕜 n k)
    (hnm : n + 1 ≤ m) : ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) (k x) :=
  (hf.fderiv hg hnm).clm_apply hk

theorem Continuous.fderiv' {f : E → F → G} {g : E → F} {n : ℕ∞}
    (hf : ContDiff 𝕜 n ↿f) (hg : Continuous g) (hn : 1 ≤ n) :
    Continuous fun x => _root_.fderiv 𝕜 (f x) (g x) :=
  (hf.fderiv (contDiff_zero.mpr hg) hn).continuous

end ForgotToUnfoldFunctionUncurry


attribute [fun_prop]
  Continuous.fderiv
  Continuous.fderiv'
  ContDiff.fderiv
  ContDiff.fderiv
  ContDiff.fderiv'
  ContDiff.fderiv_apply
  ContDiff.fderiv_apply'
  ContDiff.fderiv_right
