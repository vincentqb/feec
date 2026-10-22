module

public import Feec.Instances.EinsteinBianchiFEMComplex
public import Feec.Instances.EinsteinBianchiGauss

/-!
# The cochain defect of the scheme (6.5)

The scheme (6.5) of [QuennevilleBelair2015], §6.3, is an approximating family of discrete
differential spaces (`Feec.HilbertComplex.ApproxComplexCrime`) whose discrete BGG differential
`𝐝ₕ (σ, u, M, ρ) = (0, -d̃ Φ(σ, 0), S₁,ₕ u, d̃ u)` (`Feec.Instances.EinsteinBianchi.FEM.diffGen`) is
built with `S₀,ₕ = π¹S⁰` and `S₁,ₕ = π²S¹`, so the reading maps are not cochain maps
(`Feec.Instances.EinsteinBianchiFEMComplex`, where the cochain defect is absorbed by the Galerkin
identity of (6.4) and not computed). This file computes it.

**The formula.** Along a source-free classical solution `(σ, φ, u, M, ρ, ℓ)` of (6.2), the
cochain defect pairs with a hidden state `v = (σᵥ, uᵥ, Mᵥ, ρᵥ)` as
`⟪κₕ, v⟫ = -ℓ((S₀ - S₀,ₕ) Φ(σᵥ, 0)) - ⟪M, (S₁ - S₁,ₕ) uᵥ⟫`, `S₀ - S₀,ₕ = (I - π¹) S⁰`,
`S₁ - S₁,ₕ = (I - π²) S¹` (`cochainDefectForm`): it is exactly the pair of consistency
functionals whose norms `K₀`, `K₁` enter the Strang bound of (6.4)
(`Feec.BGG.Discrete.strangData`), evaluated at the discrete potential `Φ(σᵥ, 0)` of `Γₕ`
(`S₀,ₕ Φ(σᵥ, 0) = dσᵥ`, `defectPhi`) and at `uᵥ`. At the energy level this is the identity
`⟪ξ, 𝐝ₕ v⟫ + ⟪σ', σᵥ⟫ + ⟪d̃ φ + u', uᵥ⟫ = κ(v)` (`cochainDefectForm_eq`, from (6.2a) at
`(σᵥ, Φ(σᵥ, 0))` and (6.2b) at `uᵥ`), whose middle terms are `-⟪𝐝* ξ, v⟫` in the energy
components; on a three-term complex `⟪𝐝* y, z⟫ = -⟪(L y)₀, z₀⟫ + ⟪(𝐝 y)₁ - (L y)₁, z₁⟫`
(`Feec.HilbertComplex.inner_dual_totalD_fin3`).

## Main results

* `cochainDefectForm_eq`: the weak cochain defect identity, for any discrete BGG segment.
* `abs_cochainDefectForm_le`: `|κ(v)| ≤ (K₀ √(1 + C_P²) + K₁) (‖v‖ + ‖𝐝ₕ v‖)` (dual discrete
  graph norm), with the consistency constants of the Strang bound and a Poincaré constant of `d̃`;
  `cochainDefectForm_eq_zero`, `cochainDefectForm_eq_zero_of`: it vanishes when the consistency
  functionals vanish, in particular when `ℓ(t) = 0` and `M(t) = 0`.
* **The thesis' boundary conditions** (`standardCubeComplex`):
  `inner_standardCube_cochainDefect`: the cochain defect
  `Feec.HilbertComplex.ApproxComplexCrime.Family.cochainDefect` of the family at the exact state
  `e^{tL} x`, `x ∈ D(L²)`, **is** the formula, for the classical solution `cubeExact` of the
  orbit (the degree-`1` part of `𝐝` goes through the forms model, `inner_formsTotalD_part1`, and
  the unitary transport `Feec.HilbertComplex.inner_totalD_map_of_eq`);
  `exists_standardCube_cochainDefect_le_mesh`: it is `O(h)` in the dual discrete graph norm,
  `|⟪κₙ, v⟫| ≤ (C₀ Λ + K c) h_N (‖v‖ + ‖𝐝ₙ v‖)`, at every time at which the multiplier is an `L²`
  functional (`|ℓ(t) μ| ≤ Λ ‖μ‖`) and `M(t) ∈ D(d₁*)` with `‖M(t)‖, ‖d₁* M(t)‖ ≤ c` (these
  regularity hypotheses are assumed, not derived from the datum);
  `eventually_standardCube_cochainDefect_le`: it tends to `0` uniformly on `[0, T]` for every
  datum of `D(L²)` (`K₀, K₁ → 0`).

That the cochain defect is **nonzero** for some mesh and datum is not proved: by the formula it
would need `ℓ(t)((I - π¹) S⁰ Φ(σᵥ, 0)) ≠ 0` or `⟪M(t), (I - π²) S¹ uᵥ⟫ ≠ 0` for the smoothed
cochain projections, an explicit finite element computation.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2 ((6.2), (6.4)), §6.3 ((6.5))
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (§3.3, Thm 3.10)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

/-! ### The graded pieces of `𝐝* y` on a three-term complex -/

namespace Feec.HilbertComplex

section Fin3

variable {𝕜 : Type*} [RCLike 𝕜] {W : Fin 3 → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 ComplexShape.fin3 W)

/-- `𝐝` has no degree-`0` component on a three-term complex. -/
theorem totalD_apply_zero_fin3 (x : H.totalD.domain) : (H.totalD x) 0 = 0 := by
  rw [totalD_apply]
  exact Finset.sum_eq_zero fun i _ => H.apply_eq_zero_of_not_rel (by simp) _

/-- The degree-`1` component of `𝐝` on a three-term complex: `(𝐝 x)₁ = d₀₁ x₀`. -/
theorem totalD_apply_one_fin3 (x : H.totalD.domain) :
    (H.totalD x) 1 = H.d 0 1 ⟨(x : PiLp 2 W) 0, x.2 0 1⟩ := by
  rw [totalD_apply, Fin.sum_univ_three, H.apply_eq_zero_of_not_rel (i := 1) (j := 1) (by simp),
    H.apply_eq_zero_of_not_rel (i := 2) (j := 1) (by simp), add_zero, add_zero]

/-- `𝐝*` has no degree-`2` component on a three-term complex. -/
theorem dual_totalD_apply_two_fin3 (y : H.dual.totalD.domain) : (H.dual.totalD y) 2 = 0 := by
  rw [totalD_apply]
  refine Finset.sum_eq_zero fun i _ => H.dual.apply_eq_zero_of_not_rel ?_ _
  change ¬ ComplexShape.fin3.Rel 2 i
  simp only [ComplexShape.window_rel]
  omega

omit [∀ i, CompleteSpace (W i)] in
/-- The inner product of `PiLp 2 W` over three degrees. -/
theorem inner_fin3 (z w : PiLp 2 W) : ⟪z, w⟫_𝕜 = ⟪z 0, w 0⟫_𝕜 + ⟪z 1, w 1⟫_𝕜 + ⟪z 2, w 2⟫_𝕜 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]

omit [∀ i, CompleteSpace (W i)] in
/-- Testing against a vector of degree `1`. -/
theorem inner_eq_of_deg1_fin3 {z w : PiLp 2 W} (h0 : w 0 = 0) (h2 : w 2 = 0) :
    ⟪z, w⟫_𝕜 = ⟪z 1, w 1⟫_𝕜 := by
  rw [inner_fin3, h0, h2, inner_zero_right, inner_zero_right, zero_add, add_zero]

omit [∀ i, CompleteSpace (W i)] in
/-- Testing against a vector of degree `0`. -/
theorem inner_eq_of_deg0_fin3 {z w : PiLp 2 W} (h1 : w 1 = 0) (h2 : w 2 = 0) :
    ⟪z, w⟫_𝕜 = ⟪z 0, w 0⟫_𝕜 := by
  rw [inner_fin3, h1, h2, inner_zero_right, inner_zero_right, add_zero, add_zero]

/-- **`𝐝* y` from `L y` and `𝐝 y`** on a three-term complex, for `y ∈ D(L)`:
`⟪𝐝* y, z⟫ = -⟪(L y)₀, z₀⟫ + ⟪(𝐝 y)₁ - (L y)₁, z₁⟫` (`L = 𝐝 - 𝐝*`, `(𝐝 y)₀ = 0`,
`(𝐝* y)₂ = 0`). -/
theorem inner_dual_totalD_fin3 (y : H.wave.domain) (z : PiLp 2 W) :
    ⟪H.dual.totalD ⟨y, y.2.2⟩, z⟫_𝕜 = -⟪(H.wave y) 0, z 0⟫_𝕜 +
      ⟪(H.totalD ⟨y, y.2.1⟩) 1 - (H.wave y) 1, z 1⟫_𝕜 := by
  have e : H.dual.totalD ⟨y, y.2.2⟩ = H.totalD ⟨y, y.2.1⟩ - H.wave y := by
    rw [wave_eq_sub]; abel
  rw [inner_fin3, dual_totalD_apply_two_fin3, inner_zero_left, add_zero, e, PiLp.sub_apply,
    PiLp.sub_apply, totalD_apply_zero_fin3, zero_sub, inner_neg_left]

/-- `⟪𝐝* y, z⟫ = -⟪(L y)₁, z₁⟫` when `(L y)₀ = 0` and `(𝐝 y)₁ = 0`. -/
theorem inner_dual_totalD_fin3_of (y : H.wave.domain) (h0 : (H.wave y) 0 = 0)
    (h1 : (H.totalD ⟨y, y.2.1⟩) 1 = 0) (z : PiLp 2 W) :
    ⟪H.dual.totalD ⟨y, y.2.2⟩, z⟫_𝕜 = -⟪(H.wave y) 1, z 1⟫_𝕜 := by
  rw [inner_dual_totalD_fin3, h0, h1, inner_zero_left, neg_zero, zero_add, zero_sub,
    inner_neg_left]

end Fin3

/-! ### The total differential of a unitarily transported complex -/

section Map

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W W' : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)] [∀ i, CompleteSpace (W' i)]

/-- **Unitary transport conjugates the total differentials**, weakly: for `H' = H.map u`,
`⟪𝐝' y, u z⟫ = ⟪𝐝 (u⁻¹ y), z⟫`. -/
theorem inner_totalD_map_of_eq {H : HilbertComplex 𝕜 c W} {H' : HilbertComplex 𝕜 c W'}
    {u : ∀ i, W i ≃ₗᵢ[𝕜] W' i} (hH : H' = H.map u) (y : H'.totalD.domain) (z : PiLp 2 W) :
    ∃ hy : (totalIso u).symm (y : PiLp 2 W') ∈ H.totalD.domain,
      ⟪H'.totalD y, totalIso u z⟫_𝕜 = ⟪H.totalD ⟨_, hy⟩, z⟫_𝕜 := by
  subst hH
  refine ⟨fun i j => y.2 i j, ?_⟩
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [totalD_apply, totalD_apply]
  change ⟪∑ i, (1 : 𝕜) • u j (H.d i j ⟨(u i).symm ((y : PiLp 2 W') i), y.2 i j⟩), u j (z j)⟫_𝕜 = _
  simp only [one_smul, ← map_sum, LinearIsometryEquiv.inner_map_map]
  rfl

end Map

end Feec.HilbertComplex

namespace Feec.Instances.EinsteinBianchi.FEM

open Feec.BGG Feec.BGG.Discrete Feec.HilbertComplex

/-! ### The graded parts of a hidden state -/

section Parts

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}

/-- The degree-`0` part `(σ, 0, 0, 0)` of a hidden state. -/
def HiddenState.part0 (x : HiddenState D) : HiddenState D :=
  (⟨EState.mk x.toEState.σ 0 0 0, fun ψ _ => by rw [EState.u_mk, inner_zero_left]⟩ :
    hiddenSpace D)

/-- The degree-`1` part `(0, u, 0, 0)` of a hidden state. -/
def HiddenState.part1 (x : HiddenState D) : HiddenState D :=
  (⟨EState.mk 0 x.toEState.u 0 0, fun ψ hψ => x.toEState_mem ψ hψ⟩ : hiddenSpace D)

@[simp] theorem HiddenState.part0_toEState (x : HiddenState D) :
    x.part0.toEState = EState.mk x.toEState.σ 0 0 0 := rfl

@[simp] theorem HiddenState.part1_toEState (x : HiddenState D) :
    x.part1.toEState = EState.mk 0 x.toEState.u 0 0 := rfl

end Parts

/-! ### The cochain defect form of a discrete BGG segment -/

section Energy

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} (Q : Discrete D)
  [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.W2h]
  [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h] [FiniteDimensional ℝ Q.Wt2h]
  (hdinj : Function.Injective Q.toSegmentH.dt0) (hS : Function.Surjective Q.toSegmentH.S0)

/-- The discrete potential `Φ(σ, 0) ∈ Ṽₕ⁰` of the degree-`0` part of a hidden state:
`S₀,ₕ Φ(σ, 0) = dσ` (`S0_phiMap`), `d̃ Φ(σ, 0) ⊥ d̃(ker S₀,ₕ)`. -/
def defectPhi (v : HiddenState Q.toSegmentH) : Q.Vt0h :=
  phiMap Q.toSegmentH hdinj hS (v.toEState.σ, 0)

omit [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.W2h] [FiniteDimensional ℝ Q.Wt2h] in
theorem S0h_defectPhi (v : HiddenState Q.toSegmentH) :
    Q.S0h (defectPhi Q hdinj hS v : Vt0) = D.d0 (v.toEState.σ : V0) :=
  congrArg Subtype.val (S0_phiMap hdinj hS (v.toEState.σ, (0 : Q.Vt1h)))

variable {T : ℝ} {g : ℝ → Vt1 →ₗ[ℝ] ℝ}

/-- **The cochain defect form** of the discrete BGG differential `𝐝ₕ` against an exact solution
of (6.2): `κ(v) = -ℓ((S₀ - S₀,ₕ) Φ(σᵥ, 0)) - ⟪M, (S₁ - S₁,ₕ) uᵥ⟫`, with `S₀,ₕ = π¹S⁰`,
`S₁,ₕ = π²S¹`, so `S₀ - S₀,ₕ = (I - π¹) S⁰`, `S₁ - S₁,ₕ = (I - π²) S¹`. -/
def cochainDefectForm (s : ExactWave D T g) (t : ℝ) (v : HiddenState Q.toSegmentH) : ℝ :=
  -s.ℓ t ((D.S0 - Q.S0h) (defectPhi Q hdinj hS v : Vt0)) -
    ⟪s.M t, (D.S1 - Q.S1h) (v.toEState.u : Vt1)⟫

/-- **The weak cochain defect identity**: along a source-free exact solution of (6.2), for every
hidden state `v`,
`⟪ξ, 𝐝ₕ v⟫ + ⟪σ', σᵥ⟫ + ⟪d̃ φ + u', uᵥ⟫ = -ℓ((S₀ - S₀,ₕ) Φ(σᵥ, 0)) - ⟪M, (S₁ - S₁,ₕ) uᵥ⟫`
(from (6.2a) at `(σᵥ, Φ(σᵥ, 0))`, (6.2b) at `uᵥ`, and `S₀,ₕ Φ(σᵥ, 0) = dσᵥ`). The middle terms
are `-⟪𝐝* ξ, v⟫` read in the energy components (`(𝐝* ξ)₀ = -σ'`, `(𝐝* ξ)₁ = -d̃ φ - u'`), so
the left side is the pairing of the cochain defect with `v`. -/
theorem cochainDefectForm_eq (s : ExactWave D T g) (hg : ∀ t ∈ Ico 0 T, ∀ v, g t v = 0)
    {t : ℝ} (ht : t ∈ Ico 0 T) (v : HiddenState Q.toSegmentH) :
    ⟪exState s t, coeH Q (diffGen Q.toSegmentH hdinj hS v).toEState⟫ +
        ⟪s.σ' t, (v.toEState.σ : V0)⟫ + ⟪D.dt0 (s.φ t) + s.u' t, (v.toEState.u : Vt1)⟫ =
      cochainDefectForm Q hdinj hS s t v := by
  have ha := s.ea t ht (v.toEState.σ : V0) (defectPhi Q hdinj hS v : Vt0)
  have hb := s.eb t ht (v.toEState.u : Vt1)
  rw [hg t ht] at hb
  have hℓ : s.ℓ t (D.d0 (v.toEState.σ : V0) - D.S0 (defectPhi Q hdinj hS v : Vt0)) =
      -s.ℓ t ((D.S0 - Q.S0h) (defectPhi Q hdinj hS v : Vt0)) := by
    rw [← S0h_defectPhi Q hdinj hS v, LinearMap.sub_apply, ← neg_sub, map_neg]
  rw [EState.inner_def, coeH_apply, diffGen_toEState]
  simp only [exState, EState.σ_mk, EState.u_mk, EState.M_mk, EState.ρ_mk, diffOp_σ, diffOp_u,
    diffOp_M, diffOp_ρ]
  unfold cochainDefectForm
  have e1 : ((-Q.toSegmentH.dt0 (phiMap Q.toSegmentH hdinj hS (v.toEState.σ, 0)) : Q.Vt1h) :
      Vt1) = -D.dt0 (defectPhi Q hdinj hS v : Vt0) := rfl
  have e2 : ((Q.toSegmentH.S1 v.toEState.u : Q.W2h) : W2) = Q.S1h (v.toEState.u : Vt1) := rfl
  have e3 : ((Q.toSegmentH.dt1 v.toEState.u : Q.Wt2h) : Wt2) = D.dt1 (v.toEState.u : Vt1) := rfl
  rw [e1, e2, e3, Submodule.coe_zero, inner_zero_right, zero_add, inner_neg_right]
  simp only [LinearMap.sub_apply, inner_sub_right, inner_add_left, map_sub] at hℓ ha ⊢
  linarith

/-- The components of `𝐝ₕ v = (0, -d̃ Φ(σᵥ, 0), S₁,ₕ uᵥ, d̃ uᵥ)`, in norms. -/
theorem norm_diffGen_sq (v : HiddenState Q.toSegmentH) :
    ‖diffGen Q.toSegmentH hdinj hS v‖ ^ 2 = ‖D.dt0 (defectPhi Q hdinj hS v : Vt0)‖ ^ 2 +
      ‖Q.S1h (v.toEState.u : Vt1)‖ ^ 2 + ‖D.dt1 (v.toEState.u : Vt1)‖ ^ 2 := by
  rw [← HiddenState.norm_toEState, EState.norm_sq, diffGen_toEState, diffOp_σ, diffOp_u, diffOp_M,
    diffOp_ρ, norm_zero, norm_neg]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  rfl

theorem norm_dt0_defectPhi_le (v : HiddenState Q.toSegmentH) :
    ‖D.dt0 (defectPhi Q hdinj hS v : Vt0)‖ ≤ ‖diffGen Q.toSegmentH hdinj hS v‖ := by
  have h := norm_diffGen_sq Q hdinj hS v
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [h]; nlinarith [sq_nonneg ‖Q.S1h (v.toEState.u : Vt1)‖, sq_nonneg ‖D.dt1 (v.toEState.u : Vt1)‖]

/-- The `h`-dependent graph norm of `uᵥ` is at most the discrete graph norm of `v`:
`‖uᵥ‖² + ‖S₁,ₕ uᵥ‖² + ‖d̃ uᵥ‖² ≤ ‖v‖² + ‖𝐝ₕ v‖²`. -/
theorem gnSq_le (v : HiddenState Q.toSegmentH) :
    Q.gnSq (v.toEState.u : Vt1) ≤ ‖v‖ ^ 2 + ‖diffGen Q.toSegmentH hdinj hS v‖ ^ 2 := by
  have h := norm_diffGen_sq Q hdinj hS v
  have hv := EState.norm_sq v.toEState
  rw [HiddenState.norm_toEState] at hv
  have hu : ‖(v.toEState.u : Vt1)‖ = ‖v.toEState.u‖ := rfl
  unfold Discrete.gnSq
  rw [hu, h, hv]
  nlinarith [sq_nonneg ‖v.toEState.σ‖, sq_nonneg ‖v.toEState.M‖, sq_nonneg ‖v.toEState.ρ‖,
    sq_nonneg ‖D.dt0 (defectPhi Q hdinj hS v : Vt0)‖]

/-- **The cochain defect form is bounded by the consistency constants** of the Strang bound of
(6.4), in the dual discrete graph norm: with a Poincaré inequality `‖φ‖ ≤ C_P ‖d̃ φ‖` on `Ṽ⁰`
and `|ℓ((S₀ - S₀,ₕ) ψ)| ≤ K₀ ‖ψ‖_{H(d̃)}`, `|⟪M, (S₁ - S₁,ₕ) w⟫| ≤ K₁ ‖w‖_{Γₕ}` on the finite
element spaces, `|κ(v)| ≤ (K₀ √(1 + C_P²) + K₁) (‖v‖ + ‖𝐝ₕ v‖)`. -/
theorem abs_cochainDefectForm_le (s : ExactWave D T g) (t : ℝ) {Cp K0 K1 : ℝ} (hK0' : 0 ≤ K0)
    (hK1' : 0 ≤ K1) (hP : ∀ φ : Vt0, ‖φ‖ ≤ Cp * ‖D.dt0 φ‖)
    (hK0 : ∀ ψ ∈ Q.Vt0h, |s.ℓ t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ w ∈ Q.Vt1h, |⟪s.M t, (D.S1 - Q.S1h) w⟫| ≤ K1 * √(Q.gnSq w))
    (v : HiddenState Q.toSegmentH) :
    |cochainDefectForm Q hdinj hS s t v| ≤
      (K0 * √(1 + Cp ^ 2) + K1) * (‖v‖ + ‖diffGen Q.toSegmentH hdinj hS v‖) := by
  set φ : Vt0 := (defectPhi Q hdinj hS v : Vt0)
  set n := ‖v‖ + ‖diffGen Q.toSegmentH hdinj hS v‖
  have hn0 : 0 ≤ ‖v‖ := norm_nonneg _
  have hn1 : 0 ≤ ‖diffGen Q.toSegmentH hdinj hS v‖ := norm_nonneg _
  have hd := norm_dt0_defectPhi_le Q hdinj hS v
  have hφ : graphSq D.dt0 φ ≤ (√(1 + Cp ^ 2) * ‖D.dt0 φ‖) ^ 2 := by
    have h1 := hP φ
    have h2 : ‖φ‖ ^ 2 ≤ (Cp * ‖D.dt0 φ‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    unfold graphSq
    nlinarith
  have hA : √(graphSq D.dt0 φ) ≤ √(1 + Cp ^ 2) * n := by
    refine (Real.sqrt_le_sqrt hφ).trans ?_
    rw [Real.sqrt_sq (by positivity)]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
  have hB : √(Q.gnSq (v.toEState.u : Vt1)) ≤ n := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, (gnSq_le Q hdinj hS v).trans ?_⟩
    nlinarith
  have h0 := hK0 φ (defectPhi Q hdinj hS v).2
  have h1 := hK1 _ v.toEState.u.2
  unfold cochainDefectForm
  calc |-s.ℓ t ((D.S0 - Q.S0h) φ) - ⟪s.M t, (D.S1 - Q.S1h) (v.toEState.u : Vt1)⟫|
      ≤ |s.ℓ t ((D.S0 - Q.S0h) φ)| + |⟪s.M t, (D.S1 - Q.S1h) (v.toEState.u : Vt1)⟫| := by
        rw [sub_eq_add_neg, ← neg_add]
        rw [abs_neg]
        exact abs_add_le _ _
    _ ≤ K0 * (√(1 + Cp ^ 2) * n) + K1 * n :=
        add_le_add (h0.trans (mul_le_mul_of_nonneg_left hA hK0'))
          (h1.trans (mul_le_mul_of_nonneg_left hB hK1'))
    _ = (K0 * √(1 + Cp ^ 2) + K1) * n := by ring

omit [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.W2h] [FiniteDimensional ℝ Q.Wt2h] in
/-- **The cochain defect form vanishes when the consistency functionals vanish**:
`ℓ((S₀ - S₀,ₕ) ψ) = 0` on `Ṽₕ⁰` and `⟪M, (S₁ - S₁,ₕ) w⟫ = 0` on `Ṽₕ¹`. -/
theorem cochainDefectForm_eq_zero (s : ExactWave D T g) (t : ℝ)
    (hℓ : ∀ ψ ∈ Q.Vt0h, s.ℓ t ((D.S0 - Q.S0h) ψ) = 0)
    (hM : ∀ w ∈ Q.Vt1h, ⟪s.M t, (D.S1 - Q.S1h) w⟫ = 0) (v : HiddenState Q.toSegmentH) :
    cochainDefectForm Q hdinj hS s t v = 0 := by
  unfold cochainDefectForm
  rw [hℓ _ (defectPhi Q hdinj hS v).2, hM _ v.toEState.u.2, neg_zero, sub_zero]

omit [FiniteDimensional ℝ Q.V0h] [FiniteDimensional ℝ Q.W2h] [FiniteDimensional ℝ Q.Wt2h] in
/-- In particular **it vanishes when the multiplier and `M` vanish** (`ℓ(t) = 0`, `M(t) = 0`), as
for the mirror TSD solutions. -/
theorem cochainDefectForm_eq_zero_of (s : ExactWave D T g) {t : ℝ} (hℓ : s.ℓ t = 0)
    (hM : s.M t = 0) (v : HiddenState Q.toSegmentH) :
    cochainDefectForm Q hdinj hS s t v = 0 :=
  cochainDefectForm_eq_zero Q hdinj hS s t (fun ψ _ => by rw [hℓ, LinearMap.zero_apply])
    (fun w _ => by rw [hM, inner_zero_left]) v

end Energy

/-! ### The thesis' boundary conditions: the cochain defect of `standardCubeComplex` -/

section Cube

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM
  Feec.EinsteinBianchi.MatrixModel Feec.EinsteinBianchi.BoundedFailure
  Feec.EinsteinBianchi.BoundedConvergence

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

set_option maxHeartbeats 1000000 in
theorem cubeEmb_part0_zero (N : ℕ) (v : cubeHidden hT hB N) :
    (cubeEmb hT hB N v.part0) 0 = (cubeEmb hT hB N v) 0 := rfl

set_option maxHeartbeats 1000000 in
theorem cubeEmb_part0_one (N : ℕ) (v : cubeHidden hT hB N) :
    (cubeEmb hT hB N v.part0) 1 = 0 := by
  change rowsEquiv (incl1CLM (((0 : (cubeFEM hT hB N).Vt1h) : Wv U1))) = 0
  rw [Submodule.coe_zero, map_zero, map_zero]

set_option maxHeartbeats 1000000 in
theorem cubeEmb_part0_two (N : ℕ) (v : cubeHidden hT hB N) :
    (cubeEmb hT hB N v.part0) 2 = 0 := by
  change topEquiv (WithLp.toLp 2 (((0 : (cubeFEM hT hB N).W2h) : W2),
    ((0 : (cubeFEM hT hB N).Wt2h) : Wv W2))) = 0
  rw [Submodule.coe_zero, Submodule.coe_zero]
  exact map_zero _

set_option maxHeartbeats 1000000 in
theorem cubeEmb_part1_zero (N : ℕ) (v : cubeHidden hT hB N) :
    (cubeEmb hT hB N v.part1) 0 = 0 := by
  change zeroEquiv (-(gammaTop.symm (((((0 : (cubeFEM hT hB N).V0h) : U0)) : W0)))) = 0
  rw [Submodule.coe_zero, Submodule.coe_zero, map_zero, neg_zero, map_zero]

set_option maxHeartbeats 1000000 in
theorem cubeEmb_part1_one (N : ℕ) (v : cubeHidden hT hB N) :
    (cubeEmb hT hB N v.part1) 1 = (cubeEmb hT hB N v) 1 := rfl

set_option maxHeartbeats 1000000 in
theorem cubeEmb_part1_two (N : ℕ) (v : cubeHidden hT hB N) :
    (cubeEmb hT hB N v.part1) 2 = 0 := cubeEmb_part0_two hT hB N v

set_option maxHeartbeats 4000000 in
/-- **The degree-`1` part of `𝐝` in the forms model, against a discrete reading**: for
`V ∈ D(L)`, `⟪𝐝 V, ι(0, uᵥ, 0, 0)⟫ = -⟪d̃ φ(V), uᵥ⟫` (`(𝐝 V)₁ = d₀ V₀ = -d̃ φ(V)`,
`projK_comp1_waveOf`, `incl1_dt0_φOf`). -/
theorem inner_formsTotalD_part1 {V : WS} (hV : V ∈ formsShort.wave.domain)
    (hV' : V ∈ formsComplex.totalD.domain) (N : ℕ) (v : cubeHidden hT hB N) :
    ⟪formsComplex.totalD ⟨V, hV'⟩, vecInv (cubeFE hT hB N v.part1)⟫ =
      -⟪bggSegment.dt0 (rp (φOf V)), ((v.toEState.u : (cubeFEM hT hB N).Vt1h) : Wv U1)⟫ := by
  have h0 : (vecInv (cubeFE hT hB N v.part1)) 0 = 0 := by
    change -(gammaTop.symm (((((0 : (cubeFEM hT hB N).V0h) : U0)) : W0))) = 0
    rw [Submodule.coe_zero, Submodule.coe_zero, map_zero, neg_zero]
  have h2 : (vecInv (cubeFE hT hB N v.part1)) 2 = 0 := by
    change WithLp.toLp 2 (((0 : (cubeFEM hT hB N).W2h) : W2),
      ((0 : (cubeFEM hT hB N).Wt2h) : Wv W2)) = 0
    rw [Submodule.coe_zero, Submodule.coe_zero]
    rfl
  have h1 : (vecInv (cubeFE hT hB N v.part1)) 1 =
      incl1 ((v.toEState.u : (cubeFEM hT hB N).Vt1h) : Wv U1) := rfl
  have hd : (formsComplex.totalD ⟨V, hV'⟩) 1 = bggHilb.D0Γ ⟨comp0 V, dom0 hV⟩ := by
    rw [totalD_apply_one_fin3]
    rfl
  have hφ : bggHilb.D0Γ ⟨comp0 V, dom0 hV⟩ = -incl1 (bggSegment.dt0 (rp (φOf V))) := by
    rw [incl1_dt0_φOf hV, projK_comp1_waveOf hV, neg_neg]
  rw [inner_eq_of_deg1_fin3 h0 h2, h1, hd, hφ]
  exact (inner_neg_left (𝕜 := ℝ) (incl1 (bggSegment.dt0 (rp (φOf V)))) _).trans
    (congrArg Neg.neg (inner_wv_U1 _ _).symm)

set_option maxHeartbeats 4000000 in
/-- The exact orbit stays in `D(L)`. -/
theorem matrix_waveGroup_mem_domain {x : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))} (hx : x ∈ matrixComplex.wave.domainSq)
    (t : ℝ) : matrixComplex.waveGroup.S t x ∈ matrixComplex.wave.domain :=
  waveGroup_mem_domain matrixComplex (LinearPMap.domainSq_le_domain hx) t

set_option maxHeartbeats 4000000 in
/-- `L e^{tL} x = e^{tL} L x`. -/
theorem matrix_wave_waveGroup {x : PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))}
    (hx : x ∈ matrixComplex.wave.domainSq) (t : ℝ) :
    matrixComplex.wave ⟨matrixComplex.waveGroup.S t x, matrix_waveGroup_mem_domain hx t⟩ =
      matrixComplex.waveGroup.S t (waveExt matrixComplex x) :=
  (waveExt_of_mem (matrix_waveGroup_mem_domain hx t)).symm.trans
    (waveExt_waveGroup matrixComplex (LinearPMap.domainSq_le_domain hx) t)

set_option maxHeartbeats 4000000 in
/-- **The degree-`0` part of `L y`** against the reading: `⟪(L y)₀, (ι v)₀⟫ = ⟪σ', σᵥ⟫`. -/
theorem inner_matrix_wave_cubeEmb_zero (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))}
    (hx : x ∈ matrixComplex.wave.domainSq) {T t : ℝ} (ht : t ∈ Icc 0 T)
    (v : cubeHidden hT hB N) :
    ⟪(matrixComplex.wave ⟨matrixComplex.waveGroup.S t x, matrix_waveGroup_mem_domain hx t⟩) 0,
        (cubeEmb hT hB N v) 0⟫ =
      ⟪(cubeExact hx (T + 1)).σ' t, (((v.toEState.σ : (cubeFEM hT hB N).V0h)) : U0)⟫ := by
  rw [← cubeEmb_part0_zero, ← inner_eq_of_deg0_fin3 (cubeEmb_part0_one hT hB N v)
    (cubeEmb_part0_two hT hB N v), matrix_wave_waveGroup hx,
    ← inner_exState'_coeH_cube hT hB N hx (Icc_sub_Ico_add_one ht), EState.inner_def, coeH_apply]
  simp [exState']

set_option maxHeartbeats 4000000 in
/-- **The degree-`1` part of `L y`** against the reading: `⟪(L y)₁, (ι v)₁⟫ = ⟪u', uᵥ⟫`. -/
theorem inner_matrix_wave_cubeEmb_one (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))}
    (hx : x ∈ matrixComplex.wave.domainSq) {T t : ℝ} (ht : t ∈ Icc 0 T)
    (v : cubeHidden hT hB N) :
    ⟪(matrixComplex.wave ⟨matrixComplex.waveGroup.S t x, matrix_waveGroup_mem_domain hx t⟩) 1,
        (cubeEmb hT hB N v) 1⟫ =
      ⟪(cubeExact hx (T + 1)).u' t, (((v.toEState.u : (cubeFEM hT hB N).Vt1h)) : Wv U1)⟫ := by
  rw [← cubeEmb_part1_one, ← inner_eq_of_deg1_fin3 (cubeEmb_part1_zero hT hB N v)
    (cubeEmb_part1_two hT hB N v), matrix_wave_waveGroup hx,
    ← inner_exState'_coeH_cube hT hB N hx (Icc_sub_Ico_add_one ht), EState.inner_def, coeH_apply]
  simp [exState']

set_option maxHeartbeats 8000000 in
/-- **The degree-`1` part of `𝐝 y`** against the reading, through the forms model:
`⟪(𝐝 y)₁, (ι v)₁⟫ = -⟪d̃ φ, uᵥ⟫`. -/
theorem inner_matrix_totalD_cubeEmb_one (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))}
    (hx : x ∈ matrixComplex.wave.domainSq) {T t : ℝ} (ht : t ∈ Icc 0 T)
    (v : cubeHidden hT hB N) :
    ⟪(matrixComplex.totalD ⟨matrixComplex.waveGroup.S t x,
        (matrix_waveGroup_mem_domain hx t).1⟩) 1, (cubeEmb hT hB N v) 1⟫ =
      -⟪bggSegment.dt0 ((cubeExact hx (T + 1)).φ t),
        (((v.toEState.u : (cubeFEM hT hB N).Vt1h)) : Wv U1)⟫ := by
  have ht' : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
  have hy := matrix_waveGroup_mem_domain hx t
  rw [← cubeEmb_part1_one, ← inner_eq_of_deg1_fin3 (cubeEmb_part1_zero hT hB N v)
    (cubeEmb_part1_two hT hB N v)]
  obtain ⟨hy', e⟩ := inner_totalD_map_of_eq matrixComplex_eq_map
    ⟨matrixComplex.waveGroup.S t x, hy.1⟩ (vecInv (cubeFE hT hB N v.part1))
  have hV : totalE.symm (matrixComplex.waveGroup.S t x) ∈ formsShort.wave.domain :=
    wave_intertwines_symm.mapsTo ⟨_, hy⟩
  have hspec := (cubeOrbit_spec hx (T + 1)).2.2.2 t ht'
  refine e.trans ((inner_formsTotalD_part1 hT hB hV hy' N v).trans ?_)
  change -⟪bggSegment.dt0 (rp (φOf (totalE.symm (matrixComplex.waveGroup.S t x)))), _⟫ =
    -⟪bggSegment.dt0 (rp (φOf (cubeOrbit hx (T + 1) t))), _⟫
  rw [hspec]

set_option maxHeartbeats 8000000 in
/-- **The cochain defect of the thesis' scheme (6.5)**, computed: for the discrete BGG differential
`𝐝ₕ = cubeD` (with `S₀,ₕ = π¹S⁰`) and the reading map `cubeEmb`, along the exact orbit
`y = e^{tL} x` of `x ∈ D(L²)`, for every hidden state `v`,
`⟪κₕ(y), v⟫ = -ℓ(t)((S₀ - S₀,ₕ) Φ(σᵥ, 0)) - ⟪M(t), (S₁ - S₁,ₕ) uᵥ⟫`, where `(σ, φ, u, M, ρ, ℓ)` is
the classical solution of (6.2) of the orbit (`cubeExact`, horizon `T + 1`). -/
theorem inner_standardCube_cochainDefect (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))}
    (hx : x ∈ matrixComplex.wave.domainSq) {T t : ℝ} (ht : t ∈ Icc 0 T)
    (v : cubeHidden hT hB N) :
    ⟪(standardCubeComplex hT hB).toFamily.cochainDefect N
        ⟨matrixComplex.waveGroup.S t x, matrix_waveGroup_mem_domain hx t⟩, v⟫ =
      cochainDefectForm (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
        (cubeWave_S0_surjective hT hB N) (cubeExact hx (T + 1)) t v := by
  have ht' : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
  have hy := matrix_waveGroup_mem_domain hx t
  have hE : ⟪exState (cubeExact hx (T + 1)) t,
        coeH (cubeFEM hT hB N) (cubeD hT hB N v).toEState⟫ +
        ⟪(cubeExact hx (T + 1)).σ' t, (((v.toEState.σ : (cubeFEM hT hB N).V0h)) : U0)⟫ +
        ⟪bggSegment.dt0 ((cubeExact hx (T + 1)).φ t) + (cubeExact hx (T + 1)).u' t,
          (((v.toEState.u : (cubeFEM hT hB N).Vt1h)) : Wv U1)⟫ =
      cochainDefectForm (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
        (cubeWave_S0_surjective hT hB N) (cubeExact hx (T + 1)) t v :=
    cochainDefectForm_eq (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N) (cubeExact hx (T + 1))
      (fun t _ v => srcFun_zero_apply t v) (Icc_sub_Ico_add_one ht) v
  have h1 := (standardCubeComplex hT hB).toFamily.inner_cochainDefect N ⟨_, hy⟩ v
  have h2 := inner_dual_totalD_fin3 matrixComplex ⟨_, hy⟩ (cubeEmb hT hB N v)
  have hA := (inner_exState_coeH_cube hT hB N hx ht' (cubeD hT hB N v)).symm
  have hB0 := inner_matrix_wave_cubeEmb_zero hT hB N hx ht v
  have hB1 := inner_matrix_wave_cubeEmb_one hT hB N hx ht v
  have hD1 := inner_matrix_totalD_cubeEmb_one hT hB N hx ht v
  have hsplit := inner_sub_left (𝕜 := ℝ) ((matrixComplex.totalD ⟨_, hy.1⟩) 1)
    ((matrixComplex.wave ⟨_, hy⟩) 1) ((cubeEmb hT hB N v) 1)
  have hadd := inner_add_left (𝕜 := ℝ) (bggSegment.dt0 ((cubeExact hx (T + 1)).φ t))
    ((cubeExact hx (T + 1)).u' t) (((v.toEState.u : (cubeFEM hT hB N).Vt1h)) : Wv U1)
  refine h1.trans (Eq.trans (congrArg (fun z => ⟪matrixComplex.waveGroup.S t x,
    cubeEmb hT hB N (cubeD hT hB N v)⟫ - z) h2) ?_)
  change ⟪matrixComplex.waveGroup.S t x, cubeEmb hT hB N (cubeD hT hB N v)⟫ -
    (-⟪(matrixComplex.wave ⟨_, hy⟩) 0, (cubeEmb hT hB N v) 0⟫ +
      ⟪(matrixComplex.totalD ⟨_, hy.1⟩) 1 - (matrixComplex.wave ⟨_, hy⟩) 1,
        (cubeEmb hT hB N v) 1⟫) = _
  linarith [hsplit, hB0, hB1, hD1, hA, hE, hadd]

set_option synthInstance.maxHeartbeats 400000 in
/-- Shortcut instance (synthesis under the removed `W3` instances is expensive). -/
local instance instNormedSpaceWvU0 : NormedSpace ℝ (Wv U0) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Shortcut instance. -/
local instance instNormedSpaceWvU1 : NormedSpace ℝ (Wv U1) := inferInstance

/-- The Poincaré constant `(2π)⁻¹` of `d̃` on the cube enters as `√(1 + (2π)⁻²)`. -/
abbrev cubeDefectConst : ℝ := √(1 + ((2 * Real.pi)⁻¹) ^ 2)

set_option maxHeartbeats 4000000 in
/-- **The cochain defect of (6.5) is bounded by the consistency constants**: if
`|ℓ((S₀ - S₀,ₕ) ψ)| ≤ K₀ ‖ψ‖_{H(d̃)}` and `|⟪M, (S₁ - S₁,ₕ) w⟫| ≤ K₁ ‖w‖_{Γₕ}` at time `t`, then
`|⟪κₕ(e^{tL} x), v⟫| ≤ (K₀ √(1 + (2π)⁻²) + K₁) (‖v‖ + ‖𝐝ₕ v‖)`. -/
theorem abs_inner_standardCube_cochainDefect_le (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))}
    (hx : x ∈ matrixComplex.wave.domainSq) {T t : ℝ} (ht : t ∈ Icc 0 T)
    {K0 K1 : ℝ} (hK0' : 0 ≤ K0) (hK1' : 0 ≤ K1)
    (hK0 : ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
      |(cubeExact hx (T + 1)).ℓ t ((bggSegment.S0 - (cubeFEM hT hB N).S0h) ψ)| ≤
        K0 * √(graphSq bggSegment.dt0 ψ))
    (hK1 : ∀ w ∈ (cubeFEM hT hB N).Vt1h,
      |⟪(cubeExact hx (T + 1)).M t, (bggSegment.S1 - (cubeFEM hT hB N).S1h) w⟫| ≤
        K1 * √((cubeFEM hT hB N).gnSq w))
    (v : cubeHidden hT hB N) :
    |⟪(standardCubeComplex hT hB).toFamily.cochainDefect N
        ⟨matrixComplex.waveGroup.S t x, matrix_waveGroup_mem_domain hx t⟩, v⟫| ≤
      (K0 * cubeDefectConst + K1) * (‖v‖ + ‖cubeD hT hB N v‖) := by
  rw [inner_standardCube_cochainDefect hT hB N hx ht v]
  exact abs_cochainDefectForm_le (cubeFEM hT hB N) (cubeWave_dt0_injective hT hB N)
    (cubeWave_S0_surjective hT hB N) (cubeExact hx (T + 1)) t hK0' hK1' seg_poinct0 hK0 hK1 v

set_option maxHeartbeats 4000000 in
/-- **The `O(h)` weak bound of the cochain defect of (6.5) along smooth exact solutions** (thesis'
boundary conditions): there are constants `C₀, K ≥ 0` such that, whenever at time `t` the
multiplier of the exact solution is an `L²` functional, `|ℓ(t) μ| ≤ Λ ‖μ‖`, and `M(t) ∈ D(d₁*)`
with `‖M(t)‖ ≤ c`, `|⟪M(t), d₁ w⟫| ≤ c ‖w‖`, the cochain defect of the exact state
`e^{tL} x` is `O(h)` in the dual discrete graph norm:
`|⟪κₙ(e^{tL} x), v⟫| ≤ (C₀ Λ + K c) h_N (‖v‖ + ‖𝐝ₙ v‖)`. The constants come from
`‖(S₀ - S₀,ₕ) ψ‖ ≤ C h ‖ψ‖_{H(d̃)}` (`cubeFEM_happ0`, `(I - π¹)S⁰` on the smoothed
projections) and `exists_cubeFEM_K1` (`(I - π²)S¹`), with the Poincaré constant `(2π)⁻¹` of `d̃`
(`seg_poinct0`). The regularity of `ℓ(t)` and `M(t)` is assumed, not derived from the datum. -/
theorem exists_standardCube_cochainDefect_le_mesh :
    ∃ C₀ K : ℝ, 0 ≤ C₀ ∧ 0 ≤ K ∧ ∀ (N : ℕ) {x : PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))}
    (hx : x ∈ matrixComplex.wave.domainSq) {T t : ℝ} (_ : t ∈ Icc 0 T) {Λ c : ℝ},
      0 ≤ Λ → 0 ≤ c →
      (∀ μ : U1, |(cubeExact hx (T + 1)).ℓ t μ| ≤ Λ * ‖μ‖) →
      ‖(cubeExact hx (T + 1)).M t‖ ≤ c →
      (∀ w : U1, |⟪(cubeExact hx (T + 1)).M t, segD1 w⟫| ≤ c * ‖w‖) →
      ∀ v : cubeHidden hT hB N,
        |⟪(standardCubeComplex hT hB).toFamily.cochainDefect N
            ⟨matrixComplex.waveGroup.S t x, matrix_waveGroup_mem_domain hx t⟩, v⟫| ≤
          (C₀ * Λ + K * c) * meshSize N * (‖v‖ + ‖cubeD hT hB N v‖) := by
  obtain ⟨Capp, hC0, happ⟩ := cubeFEM_happ0 hT hB
  obtain ⟨K, hK0, hK⟩ := exists_cubeFEM_K1 hT hB
  refine ⟨Capp * cubeDefectConst, K, by positivity, hK0,
    fun N x hx T t ht Λ c hΛ hc hℓ hM hMd v => ?_⟩
  have hm := (meshSize_pos N).le
  have h := abs_inner_standardCube_cochainDefect_le hT hB N hx ht
    (K0 := Λ * (Capp * meshSize N)) (K1 := K * meshSize N * c) (by positivity) (by positivity)
    (fun ψ hψ => by
      have h1 := hℓ ((bggSegment.S0 - (cubeFEM hT hB N).S0h) ψ)
      have h2 : ‖(bggSegment.S0 - (cubeFEM hT hB N).S0h) ψ‖ ≤
          Capp * meshSize N * √(graphSq bggSegment.dt0 ψ) := by
        rw [LinearMap.sub_apply, ← Real.sqrt_sq (norm_nonneg _),
          ← Real.sqrt_sq (by positivity : 0 ≤ Capp * meshSize N), ← Real.sqrt_mul (sq_nonneg _)]
        exact Real.sqrt_le_sqrt (happ N ψ hψ)
      calc _ ≤ Λ * ‖(bggSegment.S0 - (cubeFEM hT hB N).S0h) ψ‖ := h1
        _ ≤ Λ * (Capp * meshSize N * √(graphSq bggSegment.dt0 ψ)) :=
          mul_le_mul_of_nonneg_left h2 hΛ
        _ = _ := by ring)
    (fun w hw => hK N _ c hc hM hMd w hw) v
  refine h.trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 4000000 in
/-- **The cochain defect of (6.5) tends to `0`** at every exact state of a datum of `D(L²)`,
uniformly on `[0, T]`, in the dual discrete graph norm (the consistency constants tend to `0`:
`eventually_cubeFEM_K0` on the represented multipliers, `eventually_cubeFEM_K1` on the compact
trajectory of `M`). -/
theorem eventually_standardCube_cochainDefect_le {x : PiLp 2 (ShortHilbertComplex.W3
    (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))}
    (hx : x ∈ matrixComplex.wave.domainSq) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, ∀ v : cubeHidden hT hB N,
      ‖⟪(standardCubeComplex hT hB).toFamily.cochainDefect N
          ⟨matrixComplex.waveGroup.S t x, matrix_waveGroup_mem_domain hx t⟩, v⟫‖ ≤
        ε * (‖v‖ + ‖cubeD hT hB N v‖) := by
  set s := cubeExact hx (T + 1)
  obtain ⟨hV, hW, hX, -⟩ := cubeOrbit_spec hx (T + 1)
  have hK : 0 ≤ cubeDefectConst := Real.sqrt_nonneg _
  set θ := ε / (cubeDefectConst + 1) with hθ
  have hθ0 : 0 < θ := div_pos hε (by positivity)
  have hθε : θ * cubeDefectConst + θ = ε := by
    rw [hθ, ← mul_add_one, div_mul_cancel₀ _ (by positivity)]
  have hKc : IsCompact (s.M '' Icc 0 (T + 1)) := isCompact_Icc.image_of_continuousOn s.cM
  have ev0 := eventually_cubeFEM_K0 hT hB (ℓ := s.ℓ)
    (a := fun t => aOf (cubeOrbit hx (T + 1) t)) (b := fun t => bOf (cubeOrbit hx (T + 1) t))
    (negComp0L.continuous.comp_continuousOn hW.continuousOn)
    (comp1L.continuous.comp_continuousOn hV.continuousOn)
    (exactOfStrong_isMultRep hV hW hX) hθ0
  have ev2 := eventually_cubeFEM_K1 hT hB hKc hθ0
  filter_upwards [ev0, ev2] with N h0 h2 t ht v
  have ht' : t ∈ Icc 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
  have h := abs_inner_standardCube_cochainDefect_le hT hB N hx ht hθ0.le hθ0.le (h0 t ht')
    (fun w hw => h2 _ (mem_image_of_mem _ ht') w hw) v
  rw [Real.norm_eq_abs]
  refine h.trans (le_of_eq ?_)
  rw [← hθε]

end Cube


/-! ### Mirror boundary conditions: the cochain defect of `mirrorComplex` vanishes on TSD -/

section Mirror

open Feec.Models.Cube.MirrorWeakSymmetry Feec.Models.Cube.RowWise
open Feec.Models.Cube.MirrorBGG (SpaceQ W2Q complexQ tsdQ)
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

set_option maxHeartbeats 2000000 in
/-- **The real pairing with a real state, by slots**:
`⟪y, Rt z⟫ = ⟪Re y₀, z_σ⟫ + ⟪Re y₁, z_u⟫ + ⟪Re y_M, z_M⟫ + ⟪Re y_B, z_ρ⟫`. -/
theorem inner_mirrorReEmb_right (y : PiLp 2 SpaceQ) (z : REnergy) :
    ⟪y, mirrorReEmb z⟫_ℝ = ⟪re0 (slot0 y), z.σ⟫ + ⟪rowsW1L (slot1 y), z.u⟫ +
      ⟪reM (slotM y), z.M⟫ + ⟪rowsW2L (slotB y), z.ρ⟫ := by
  have h1 := norm_sq_sub_mirrorReEmb y z 0
  have h0 := norm_sq_sub_mirrorReEmb y 0 0
  simp only [map_zero, smul_zero, sub_zero] at h1 h0
  have hz := EState.norm_sq z
  have hn := norm_mirrorReEmb z
  have e := norm_sub_sq_real y (mirrorReEmb z)
  have e0 := norm_sub_sq_real (re0 (slot0 y)) z.σ
  have e1 := norm_sub_sq_real (rowsW1L (slot1 y)) z.u
  have e2 := norm_sub_sq_real (reM (slotM y)) z.M
  have e3 := norm_sub_sq_real (rowsW2L (slotB y)) z.ρ
  have q0 : (0 : REnergy).σ = 0 := rfl
  have q1 : (0 : REnergy).u = 0 := rfl
  have q2 : (0 : REnergy).M = 0 := rfl
  have q3 : (0 : REnergy).ρ = 0 := rfl
  rw [hn] at e
  rw [q0, q1, q2, q3] at h1 h0
  simp only [sub_zero] at h1 h0
  rw [hz] at e
  linarith

/-- **`⟪u', v⟫ + ⟪ρ, d̃ v⟫ = 0` at every TSD state of `D(L)`**, in `L²` form (the equation
`E' = -d₁† (0, B)`; `Feec.Models.Cube.MirrorWeakSymmetry.inner_rowsBU_wave_add` without
`L x ∈ D(L)`). -/
theorem inner_rowsW1L_wave_add (x : complexQ.wave.domain)
    (hx : (x : PiLp 2 SpaceQ) ∈ totalSub tsdQ) (v : BU1) :
    ⟪rowsW1L (stEL (complexQ.wave x)), bIncl1 v⟫_ℝ + ⟪rowsW2L (stBL x), bD1 v⟫_ℝ = 0 := by
  rw [inner_rowsW1L, inner_rowsW2L]
  obtain ⟨hX, eX⟩ := ofRealRows_BU1_mem v
  have hM : (WithLp.ofLp (stW2 x)).1 = 0 := (Feec.Models.Cube.MirrorBGG.mem_tsdQ_iff.1 hx).2.2.1
  rw [stEL_apply, inner_waveQ_one x hx _ hX, eX, WithLp.prod_inner_apply, WithLp.ofLp_toLp, hM,
    inner_zero_left, zero_add, map_neg, stBL_apply]
  exact neg_add_cancel _

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 ∅
    Feec.FiniteElement.PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3,
    Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 {a} Feec.FiniteElement.PolySeq.lagrangeP2 ρ C)

set_option maxHeartbeats 1000000 in
theorem mirrorEmb_part1_one (N : ℕ) (v : mirrorHidden hT hB N) :
    (mirrorEmb hT hB N v.part1) 1 = (mirrorEmb hT hB N v) 1 := rfl

set_option maxHeartbeats 1000000 in
theorem mirrorEmb_part1_zero (N : ℕ) (v : mirrorHidden hT hB N) :
    (mirrorEmb hT hB N v.part1) 0 = 0 := by
  change emb0 (((((0 : (mirrorFEM hT hB N).V0h) : TU0)) : W0)) = 0
  rw [Submodule.coe_zero, Submodule.coe_zero, map_zero]

set_option maxHeartbeats 1000000 in
theorem mirrorEmb_part1_two (N : ℕ) (v : mirrorHidden hT hB N) :
    (mirrorEmb hT hB N v.part1) 2 = 0 := by
  change WithLp.toLp 2 (embM (((0 : (mirrorFEM hT hB N).W2h) : W2)),
    emb2 (((0 : (mirrorFEM hT hB N).Wt2h) : Wv W2))) = 0
  rw [Submodule.coe_zero, Submodule.coe_zero, map_zero, map_zero]
  rfl


set_option maxHeartbeats 1000000 in
/-- The real pairing with a read hidden state, by slots. -/
theorem inner_mirrorEmb_right (N : ℕ) (y : PiLp 2 SpaceQ) (v : mirrorHidden hT hB N) :
    ⟪y, mirrorEmb hT hB N v⟫_ℝ =
      ⟪re0 (slot0 y), (((v.toEState.σ : (mirrorFEM hT hB N).V0h) : TU0) : W0)⟫_ℝ +
      ⟪rowsW1L (slot1 y), bIncl1 ((v.toEState.u : (mirrorFEM hT hB N).Vt1h) : BU1)⟫_ℝ +
      ⟪reM (slotM y), ((v.toEState.M : (mirrorFEM hT hB N).W2h) : W2)⟫_ℝ +
      ⟪rowsW2L (slotB y), ((v.toEState.ρ : (mirrorFEM hT hB N).Wt2h) : Wv W2)⟫_ℝ :=
  inner_mirrorReEmb_right y (mirrorFE hT hB N v)

set_option maxHeartbeats 2000000 in
theorem mirrorDiffGen_σ (N : ℕ) (a : mirrorHidden hT hB N) :
    ((((HiddenState.toEState (mirrorDiffGen hT hB N a)).σ : (mirrorFEM hT hB N).V0h) : TU0) :
      W0) = 0 := rfl

set_option maxHeartbeats 2000000 in
theorem mirrorDiffGen_u (N : ℕ) (a : mirrorHidden hT hB N) :
    (((HiddenState.toEState (mirrorDiffGen hT hB N a)).u : (mirrorFEM hT hB N).Vt1h) : BU1) =
      -bD0 (((defectPhi (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
        (mirrorWave_S0_surjective hT hB N) a) : (mirrorFEM hT hB N).Vt0h) : BU0) := rfl

set_option maxHeartbeats 2000000 in
theorem mirrorDiffGen_ρ (N : ℕ) (a : mirrorHidden hT hB N) :
    (((HiddenState.toEState (mirrorDiffGen hT hB N a)).ρ : (mirrorFEM hT hB N).Wt2h) : Wv W2) =
      bD1 ((a.toEState.u : (mirrorFEM hT hB N).Vt1h) : BU1) := rfl

set_option maxHeartbeats 4000000 in
/-- The pairing of a state with `M`-slot `0` and divergence-free `E` with `ι 𝐝ₕ a`. -/
theorem inner_mirrorEmb_mirrorDiffGen (N : ℕ) (y : PiLp 2 SpaceQ)
    (hM : (WithLp.ofLp (y 2 : W2Q)).1 = 0) (a : mirrorHidden hT hB N) :
    ⟪y, mirrorEmb hT hB N (mirrorDiffGen hT hB N a)⟫_ℝ =
      -⟪rowsW1L (slot1 y), bIncl1 (bD0 (((defectPhi (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
        (mirrorWave_S0_surjective hT hB N) a) : (mirrorFEM hT hB N).Vt0h) : BU0))⟫_ℝ +
        ⟪rowsW2L (slotB y), bD1 ((a.toEState.u : (mirrorFEM hT hB N).Vt1h) : BU1)⟫_ℝ := by
  have e1 := inner_mirrorEmb_right hT hB N y (mirrorDiffGen hT hB N a)
  have hM' : reM (slotM y) = 0 := by
    change reM (WithLp.ofLp (y 2 : W2Q)).1 = 0
    rw [hM, map_zero]
  rw [mirrorDiffGen_σ, mirrorDiffGen_u, mirrorDiffGen_ρ, hM'] at e1
  have f0 : ⟪re0 (slot0 y), (0 : W0)⟫_ℝ = 0 := inner_zero_right _
  have fM : ⟪(0 : W2), (((HiddenState.toEState (mirrorDiffGen hT hB N a)).M :
      (mirrorFEM hT hB N).W2h) : W2)⟫_ℝ = 0 := inner_zero_left _
  have fu : ⟪rowsW1L (slot1 y), bIncl1 (-bD0 (((defectPhi (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
        (mirrorWave_S0_surjective hT hB N) a) : (mirrorFEM hT hB N).Vt0h) : BU0))⟫_ℝ =
      -⟪rowsW1L (slot1 y), bIncl1 (bD0 (((defectPhi (mirrorFEM hT hB N) (mirrorWave_dt0_injective hT hB N)
        (mirrorWave_S0_surjective hT hB N) a) : (mirrorFEM hT hB N).Vt0h) : BU0))⟫_ℝ := by
    rw [map_neg, inner_neg_right]
  linarith

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- **The real part of the cochain defect of the mirror scheme vanishes at TSD states**: for
`y ∈ D(L) ∩ tsdQℝ` and every real hidden state `a`, `⟪y, ι 𝐝ₕ a⟫ + ⟪(L y)₁, (ι a)₁⟫ = 0`
(`ι = mirrorEmb`). The degree-`1` part of `𝐝ₕ a` is a gradient `-d̃ Φ(σₐ, 0)`, orthogonal to the
divergence-free `E` of `y`; the `M`-slot of `y` vanishes; and the remaining terms cancel by
`E' = -d₁† (0, B)` (`inner_rowsW1L_wave_add`). -/
theorem mirror_realDefect_eq_zero (N : ℕ) (y : complexQℝ.wave.domain)
    (hyK : (y : PiLp 2 SpaceQ) ∈ tsdQℝ) (a : mirrorHidden hT hB N) :
    ⟪(y : PiLp 2 SpaceQ), mirrorEmb hT hB N (mirrorDiffGen hT hB N a)⟫_ℝ +
      ⟪(complexQℝ.wave y) 1, (mirrorEmb hT hB N a) 1⟫_ℝ = 0 := by
  have hy' : (y : PiLp 2 SpaceQ) ∈ complexQ.wave.domain := mem_complexQℝ_domain.1 y.2
  have hw : complexQℝ.wave y = complexQ.wave ⟨y, hy'⟩ := complexQℝ_wave_apply y
  obtain ⟨-, hE, hM, -⟩ := Feec.Models.Cube.MirrorBGG.mem_tsdQ_iff.1 hyK
  have hpt : ⟪rowsW1L (slot1 (complexQℝ.wave y)),
        bIncl1 ((a.toEState.u : (mirrorFEM hT hB N).Vt1h) : BU1)⟫_ℝ +
      ⟪rowsW2L (slotB (y : PiLp 2 SpaceQ)),
        bD1 ((a.toEState.u : (mirrorFEM hT hB N).Vt1h) : BU1)⟫_ℝ = 0 := by
    rw [hw]
    exact inner_rowsW1L_wave_add ⟨y, hy'⟩ hyK ((a.toEState.u : (mirrorFEM hT hB N).Vt1h) : BU1)
  have hgr : ⟪rowsW1L (slot1 (y : PiLp 2 SpaceQ)), bIncl1 (bD0 ((defectPhi (mirrorFEM hT hB N)
      (mirrorWave_dt0_injective hT hB N) (mirrorWave_S0_surjective hT hB N) a :
        (mirrorFEM hT hB N).Vt0h) : BU0))⟫_ℝ = 0 := inner_rowsW1L_bD0 hE _
  have t2 : ⟪(complexQℝ.wave y) 1, (mirrorEmb hT hB N a) 1⟫_ℝ =
      ⟪rowsW1L (slot1 (complexQℝ.wave y)),
        bIncl1 ((a.toEState.u : (mirrorFEM hT hB N).Vt1h) : BU1)⟫_ℝ := by
    rw [← mirrorEmb_part1_one, ← inner_eq_of_deg1_fin3 (mirrorEmb_part1_zero hT hB N a)
      (mirrorEmb_part1_two hT hB N a), inner_mirrorEmb_right]
    simp only [HiddenState.part1_toEState, EState.σ_mk, EState.u_mk, EState.M_mk, EState.ρ_mk,
      Submodule.coe_zero, inner_zero_right, zero_add, add_zero]
  have e1 := inner_mirrorEmb_mirrorDiffGen hT hB N (y : PiLp 2 SpaceQ) hM a
  linarith [e1, t2, hpt, hgr]

/-- Multiplication by `i` moves across the real inner product of a mirror slot:
`⟪x, i y⟫_ℝ = ⟪-i x, y⟫_ℝ`. -/
theorem real_inner_I_smul_spaceQ (i : Fin 3) (x y : SpaceQ i) :
    ⟪x, Complex.I • y⟫_ℝ = ⟪-Complex.I • x, y⟫_ℝ := by
  rw [real_inner_eq_re_inner_spaceQ, real_inner_eq_re_inner_spaceQ, inner_smul_right,
    inner_smul_left]
  simp

/-- The same on mirror states. -/
theorem real_inner_I_smul (x y : PiLp 2 SpaceQ) :
    ⟪x, Complex.I • y⟫_ℝ = ⟪-Complex.I • x, y⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => real_inner_I_smul_spaceQ i (x i) (y i)

set_option maxHeartbeats 4000000 in
/-- `L (-i y) = -i L y` on the real mirror complex. -/
theorem complexQℝ_wave_negI (y : complexQℝ.wave.domain) :
    ∃ h : -Complex.I • (y : PiLp 2 SpaceQ) ∈ complexQℝ.wave.domain,
      complexQℝ.wave ⟨_, h⟩ = -Complex.I • complexQℝ.wave y := by
  have hy' : (y : PiLp 2 SpaceQ) ∈ complexQ.wave.domain := mem_complexQℝ_domain.1 y.2
  have hs : -Complex.I • (y : PiLp 2 SpaceQ) ∈ complexQ.wave.domain :=
    complexQ.wave.domain.smul_mem _ hy'
  refine ⟨mem_complexQℝ_domain.2 hs, ?_⟩
  rw [complexQℝ_wave_apply, complexQℝ_wave_apply]
  exact complexQ.wave.map_smul (-Complex.I) ⟨_, hy'⟩


set_option maxHeartbeats 2000000 in
theorem negI_smul_mem_tsdQℝ {y : PiLp 2 SpaceQ} (hy : y ∈ tsdQℝ) : -Complex.I • y ∈ tsdQℝ :=
  (totalSub tsdQ).smul_mem (-Complex.I) hy

set_option maxHeartbeats 2000000 in
/-- A TSD state of `D(L)` has no degree-`1` part of `𝐝 y` (its degree-`0` part vanishes). -/
theorem complexQℝ_totalD_one_of_tsd (y : complexQℝ.wave.domain) (hyK : (y : PiLp 2 SpaceQ) ∈ tsdQℝ) :
    (complexQℝ.totalD ⟨y, y.2.1⟩) 1 = 0 := by
  obtain ⟨h0, -, -, -⟩ := Feec.Models.Cube.MirrorBGG.mem_tsdQ_iff.1 hyK
  rw [totalD_apply_one_fin3]
  exact LinearPMap.apply_mk_eq_zero _ _ h0

set_option maxHeartbeats 2000000 in
/-- `L y` of a TSD state of `D(L)` has no degree-`0` part (TSD reduces `L`). -/
theorem complexQℝ_wave_zero_of_tsd (y : complexQℝ.wave.domain) (hyK : (y : PiLp 2 SpaceQ) ∈ tsdQℝ) :
    (complexQℝ.wave y) 0 = 0 :=
  (Feec.Models.Cube.MirrorBGG.mem_tsdQ_iff.1 (isReducing_tsdQℝ.mapsTo y hyK)).1

set_option maxHeartbeats 4000000 in
/-- The reading and the differential of the complexified family on a pair. -/
theorem mirrorComplex_incl_D (N : ℕ) (a b : mirrorHidden hT hB N) :
    (mirrorComplex hT hB).toFamily.incl N (WithLp.toLp 2 (a, b)) =
        mirrorEmb hT hB N a + mulI (mirrorEmb hT hB N b) ∧
      (mirrorComplex hT hB).toFamily.incl N ((mirrorComplex hT hB).toFamily.D N
        (WithLp.toLp 2 (a, b))) = mirrorEmb hT hB N (mirrorDiffGen hT hB N a) +
          mulI (mirrorEmb hT hB N (mirrorDiffGen hT hB N b)) := ⟨rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **The cochain defect of the mirror scheme vanishes at every TSD state of `D(L)`**: for the
family `mirrorComplex` (the discrete BGG differential `𝐝ₕ ⊕ 𝐝ₕ` with `S₀,ₕ = π¹S⁰` on real and
imaginary parts, the reading `ι(a, b) = mirrorEmb a + i mirrorEmb b`), `κₙ(y) = 0` for
`y ∈ D(L) ∩ tsdQℝ`. The reason: a TSD state has no degree-`0` part and no `M`-slot, and its `E`
is divergence-free; so `𝐝 y` has no degree-`1` part, `L y` (again TSD) no degree-`0` part, the
gradient `-d̃ Φ(σᵥ, 0)` of `𝐝ₕ v` pairs to `0` with `E`, the crime `S₁ - S₁,ₕ` only meets the
vanishing `M`-slot, and the rest cancels by `E' = -d₁† (0, B)` (`mirror_realDefect_eq_zero`). In
the language of the formula (`cochainDefectForm`): TSD solutions have `ℓ ≡ 0` and `M ≡ 0`. -/
theorem mirrorComplex_cochainDefect_eq_zero (N : ℕ) (y : complexQℝ.wave.domain)
    (hyK : (y : PiLp 2 SpaceQ) ∈ tsdQℝ) :
    (mirrorComplex hT hB).toFamily.cochainDefect N y = 0 := by
  obtain ⟨hs, hLs⟩ := complexQℝ_wave_negI y
  have hsK := negI_smul_mem_tsdQℝ hyK
  have hd1 := complexQℝ_totalD_one_of_tsd y hyK
  have hL0 := complexQℝ_wave_zero_of_tsd y hyK
  refine ext_inner_right ℝ fun w => ?_
  obtain ⟨⟨a, b⟩⟩ := w
  obtain ⟨hi1, hi2⟩ := mirrorComplex_incl_D hT hB N a b
  have hA := mirror_realDefect_eq_zero hT hB N y hyK a
  have hB' := mirror_realDefect_eq_zero hT hB N ⟨_, hs⟩ hsK b
  have hk := (mirrorComplex hT hB).toFamily.inner_cochainDefect N y (WithLp.toLp 2 (a, b))
  rw [hi1, hi2] at hk
  have hd := inner_dual_totalD_fin3_of complexQℝ y hL0 hd1
    (mirrorEmb hT hB N a + mulI (mirrorEmb hT hB N b))
  have hz1 : (mirrorEmb hT hB N a + mulI (mirrorEmb hT hB N b)) 1 =
      (mirrorEmb hT hB N a) 1 + Complex.I • (mirrorEmb hT hB N b) 1 := rfl
  have h1 : ⟪(complexQℝ.wave y) 1, (mirrorEmb hT hB N a + mulI (mirrorEmb hT hB N b)) 1⟫_ℝ =
      ⟪(complexQℝ.wave y) 1, (mirrorEmb hT hB N a) 1⟫_ℝ +
        ⟪(-Complex.I • complexQℝ.wave y) 1, (mirrorEmb hT hB N b) 1⟫_ℝ := by
    rw [hz1, inner_add_right, real_inner_I_smul_spaceQ]
    rfl
  have hB2 := congrArg (fun z : PiLp 2 SpaceQ => ⟪z 1, (mirrorEmb hT hB N b) 1⟫_ℝ) hLs
  have h2 : ⟪(y : PiLp 2 SpaceQ), mirrorEmb hT hB N (mirrorDiffGen hT hB N a) +
      mulI (mirrorEmb hT hB N (mirrorDiffGen hT hB N b))⟫_ℝ =
      ⟪(y : PiLp 2 SpaceQ), mirrorEmb hT hB N (mirrorDiffGen hT hB N a)⟫_ℝ +
        ⟪-Complex.I • (y : PiLp 2 SpaceQ), mirrorEmb hT hB N (mirrorDiffGen hT hB N b)⟫_ℝ := by
    rw [inner_add_right]
    exact congrArg (_ + ·) (real_inner_I_smul (y : PiLp 2 SpaceQ)
      (mirrorEmb hT hB N (mirrorDiffGen hT hB N b)))
  refine Eq.trans ?_ (inner_zero_left (𝕜 := ℝ) _).symm
  linarith

end Mirror

end Feec.Instances.EinsteinBianchi.FEM
