module

public import Feec.ForMathlib.Calculus.Partial
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Time slices of space-time fields

Space-time `𝕜¹⁺ⁿ = Fin (n + 1) → 𝕜` splits as time times space through `Fin.cons t x = (t, x)`:
derivatives of space-time fields along time and on their time slices.
-/

open Set Filter Topology

@[expose] public noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem continuous_finCons :
    Continuous fun p : 𝕜 × (Fin n → 𝕜) => (Fin.cons p.1 p.2 : Fin (n + 1) → 𝕜) :=
  (Fin.consEquivL 𝕜 fun _ : Fin (n + 1) => 𝕜).continuous

theorem contDiff_finCons {k : WithTop ℕ∞} :
    ContDiff 𝕜 k fun p : 𝕜 × (Fin n → 𝕜) => (Fin.cons p.1 p.2 : Fin (n + 1) → 𝕜) :=
  (Fin.consEquivL 𝕜 fun _ : Fin (n + 1) => 𝕜).contDiff

theorem contDiff_finCons_right {k : WithTop ℕ∞} (t : 𝕜) :
    ContDiff 𝕜 k fun x : Fin n → 𝕜 => (Fin.cons t x : Fin (n + 1) → 𝕜) :=
  contDiff_finCons.comp (contDiff_const.prodMk contDiff_id)

theorem hasDerivAt_finCons_left (x : Fin n → 𝕜) (t : 𝕜) :
    HasDerivAt (fun s => (Fin.cons s x : Fin (n + 1) → 𝕜)) (Pi.single 0 1) t := by
  rw [hasDerivAt_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero, Pi.single_eq_same]
    exact hasDerivAt_id' t
  · simp only [Fin.cons_succ]
    simpa using hasDerivAt_const t (x j)

theorem hasDerivAt_finCons_right_add_smul (t : 𝕜) (x : Fin n → 𝕜) (c : Fin n) (s₀ : 𝕜) :
    HasDerivAt (fun s : 𝕜 => (Fin.cons t (x + s • Pi.single c 1) : Fin (n + 1) → 𝕜))
      (Pi.single c.succ 1) s₀ := by
  rw [hasDerivAt_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hasDerivAt_const s₀ t
  · have h := ((hasDerivAt_id s₀).mul_const ((Pi.single c (1 : 𝕜) : Fin n → 𝕜) j)).const_add
      (x j)
    convert h using 1
    · funext r; simp
    · simp [Pi.single_apply, Fin.succ_inj]

theorem DifferentiableAt.hasDerivAt_finCons_left {φ : (Fin (n + 1) → 𝕜) → F} {t : 𝕜}
    {x : Fin n → 𝕜} (hφ : DifferentiableAt 𝕜 φ (Fin.cons t x)) :
    HasDerivAt (fun s => φ (Fin.cons s x)) (partialDeriv 0 φ (Fin.cons t x)) t :=
  hφ.hasFDerivAt.comp_hasDerivAt t (_root_.hasDerivAt_finCons_left x t)

theorem partialDeriv_comp_finCons {φ : (Fin (n + 1) → 𝕜) → F} {t : 𝕜} {x : Fin n → 𝕜}
    (hφ : DifferentiableAt 𝕜 φ (Fin.cons t x)) (c : Fin n) :
    partialDeriv c (fun y => φ (Fin.cons t y)) x = partialDeriv c.succ φ (Fin.cons t x) := by
  have hg : DifferentiableAt 𝕜 (fun y => φ (Fin.cons t y)) x :=
    hφ.comp x ((contDiff_finCons_right (k := 1) t).differentiable one_ne_zero x)
  have h1 := hg.hasDerivAt_partialDeriv c
  have h2 : HasDerivAt (fun s : 𝕜 => φ (Fin.cons t (x + s • Pi.single c 1)))
      (partialDeriv c.succ φ (Fin.cons t x)) 0 :=
    hφ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_finCons_right_add_smul t x c 0)
      (by simp)
  exact h1.unique h2

variable (𝕜 n) in
/-- The spatial projection `(t, x) ↦ x` (`Fin.tail`) as a continuous linear map. -/
def spatialProj : (Fin (n + 1) → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
  ContinuousLinearMap.pi fun c => ContinuousLinearMap.proj c.succ

@[simp] theorem spatialProj_apply (Y : Fin (n + 1) → 𝕜) : spatialProj 𝕜 n Y = Fin.tail Y := rfl

@[simp] theorem spatialProj_finCons (t : 𝕜) (x : Fin n → 𝕜) :
    spatialProj 𝕜 n (Fin.cons t x) = x := rfl

theorem partialDeriv_succ_comp_spatialProj {f : (Fin n → 𝕜) → F} {Y : Fin (n + 1) → 𝕜}
    (hf : DifferentiableAt 𝕜 f (spatialProj 𝕜 n Y)) (c : Fin n) :
    partialDeriv c.succ (fun Y => f (spatialProj 𝕜 n Y)) Y =
      partialDeriv c f (spatialProj 𝕜 n Y) := by
  rw [show (fun Y => f (spatialProj 𝕜 n Y)) = f ∘ spatialProj 𝕜 n from rfl,
    (hf.hasFDerivAt.comp Y (spatialProj 𝕜 n).hasFDerivAt).partialDeriv_eq, partialDeriv]
  have : spatialProj 𝕜 n (Pi.single c.succ 1) = Pi.single c 1 := by
    ext j; simp [Fin.tail, Pi.single_apply, Fin.succ_inj]
  simp [this]

theorem partialDeriv_zero_comp_spatialProj {f : (Fin n → 𝕜) → F} {Y : Fin (n + 1) → 𝕜}
    (hf : DifferentiableAt 𝕜 f (spatialProj 𝕜 n Y)) :
    partialDeriv 0 (fun Y => f (spatialProj 𝕜 n Y)) Y = 0 := by
  rw [show (fun Y => f (spatialProj 𝕜 n Y)) = f ∘ spatialProj 𝕜 n from rfl,
    (hf.hasFDerivAt.comp Y (spatialProj 𝕜 n).hasFDerivAt).partialDeriv_eq]
  have : spatialProj 𝕜 n (Pi.single 0 1) = 0 := by
    ext j; simp [Fin.tail, Fin.succ_ne_zero]
  simp [this]
