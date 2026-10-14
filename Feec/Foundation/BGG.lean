module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Prod

/-!
# Feec foundation §F: BGG data

Two algebraic complexes linked by anticommuting maps `S₀, S₁`, and the complex (5.1).

## References

* [QuennevilleBelair2015], §5.1 (BGG data, complex (5.1))
* [ArnoldHu2021] (complexes from complexes: the BGG-type construction behind `BGGData`)
-/

@[expose] public noncomputable section

namespace Feec

/-! ## §F. BGG data (Ch 5–6): two complexes linked by `S₀, S₁` -/

/-- Top complex `V0 → V1 → W2`, bottom complex `Ṽ0 → Ṽ1 → W̃2`, connecting maps
`S0 : Ṽ0 → V1`, `S1 : Ṽ1 → W2`, anticommuting. Algebraic core only; analytic hypotheses
(closed ranges, continuity, completeness, regularity `d¹V¹ ⊆ d¹S₀Ṽ⁰`) are added per theorem.
See [QuennevilleBelair2015, §5.1]; cf. [ArnoldHu2021]. -/
structure BGGData (V0 V1 W2 Vt0 Vt1 Wt2 : Type*)
    [AddCommGroup V0] [Module ℝ V0] [AddCommGroup V1] [Module ℝ V1]
    [AddCommGroup W2] [Module ℝ W2] [AddCommGroup Vt0] [Module ℝ Vt0]
    [AddCommGroup Vt1] [Module ℝ Vt1] [AddCommGroup Wt2] [Module ℝ Wt2] where
  d0 : V0 →ₗ[ℝ] V1
  d1 : V1 →ₗ[ℝ] W2
  dt0 : Vt0 →ₗ[ℝ] Vt1
  dt1 : Vt1 →ₗ[ℝ] Wt2
  S0 : Vt0 →ₗ[ℝ] V1
  S1 : Vt1 →ₗ[ℝ] W2
  d1_d0 : ∀ σ, d1 (d0 σ) = 0
  dt1_dt0 : ∀ φ, dt1 (dt0 φ) = 0
  anticomm : ∀ φ, d1 (S0 φ) = -S1 (dt0 φ)

namespace BGGData

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [AddCommGroup V0] [Module ℝ V0] [AddCommGroup V1] [Module ℝ V1]
  [AddCommGroup W2] [Module ℝ W2] [AddCommGroup Vt0] [Module ℝ Vt0]
  [AddCommGroup Vt1] [Module ℝ Vt1] [AddCommGroup Wt2] [Module ℝ Wt2]
  (D : BGGData V0 V1 W2 Vt0 Vt1 Wt2)

/-- exactness hypotheses, stated separately so that they appear explicitly in theorems.
See [QuennevilleBelair2015, §5.1] (both complexes assumed exact). -/
def ExactTop : Prop := LinearMap.ker D.d1 = LinearMap.range D.d0
def ExactBot : Prop := LinearMap.ker D.dt1 = LinearMap.range D.dt0

/-- `Γ = {(σ, φ) | d σ = S φ}`. See [QuennevilleBelair2015, §5.1, (5.1)]. -/
def Γ : Submodule ℝ (V0 × Vt0) :=
  LinearMap.ker (D.d0.comp (LinearMap.fst ℝ V0 Vt0) - D.S0.comp (LinearMap.snd ℝ V0 Vt0))

theorem mem_Γ {x : V0 × Vt0} : x ∈ D.Γ ↔ D.d0 x.1 = D.S0 x.2 := by
  simp [Γ, sub_eq_zero]

/-- first operator `(0 d) : Γ → Ṽ¹` of the complex (5.1).
See [QuennevilleBelair2015, §5.1, (5.1)]. -/
def D0 : D.Γ →ₗ[ℝ] Vt1 := D.dt0.comp ((LinearMap.snd ℝ V0 Vt0).comp D.Γ.subtype)

/-- second operator `(S, d) : Ṽ¹ → W² × W̃²` of the complex (5.1).
See [QuennevilleBelair2015, §5.1, (5.1)]. -/
def D1 : Vt1 →ₗ[ℝ] W2 × Wt2 := D.S1.prod D.dt1

/-- (5.1) is a complex. See [QuennevilleBelair2015, §5.1]; cf. [ArnoldHu2021]. -/
theorem D1_D0 (x : D.Γ) : D.D1 (D.D0 x) = 0 := by
  obtain ⟨⟨σ, φ⟩, hx⟩ := x
  have h := D.d1_d0 σ
  rw [(D.mem_Γ).1 hx, D.anticomm] at h
  simp [D0, D1, neg_eq_zero.mp h, D.dt1_dt0]

end BGGData

end Feec
