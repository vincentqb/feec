module

public import Solution.Convert
public import Solution.HighMode
public import Solution.Witness
public import Solution.Lumped

/-!
# Variational crimes for Hilbert complexes (solution)

The theorems of `Challenge.lean`. `FEEC.crimeFEEC` from the static, cochain and
heat verdicts of `Solution.Crime` (through `Feec.HilbertComplex.ApproxComplexCrime.Family.staticFEEC`,
the cochain case `Feec.HilbertComplex.Approximation.StaticCochain` and
`Feec.HilbertComplex.ApproxComplexCrime.HeatFamily.heatFEEC`), converted by `Solution.Convert`;
`FEEC.crime_nonvacuous` from the shear family of `Solution.Witness` and the cochain clause of
`FEEC.crimeFEEC`; `FEEC.crime_defect_nonvacuous` from the family of `Solution.HighMode` (an
unbounded diagonal `d⁰` on `ℓ²`, reading maps that double the square norm of the highest mode) and
the cochain clause; `FEEC.crime_massLumping` from `Feec.FiniteElement.LumpedMassDefect` through
the bridge `Solution.Lumped` (meshes, `P₁` gradients and interpolants, the consistent and the
lumped mass of the challenge are those of `Feec`).

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 15

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace LinearPMap
open Filter Topology Set

universe u

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

variable [∀ i, NormedSpace ℝ (W i)]

/-- **Variational crimes** ([HolstStern2012], §3; [AFW2010], Thm 3.8): on a window with
closed ranges (degrees `a + 1, …, a + m - 1`), the static, cochain and heat verdicts of
`Solution.Crime` (`HilbertComplex.CrimeFamily.staticVerdict`, `cochainVerdict`, `heatVerdict`). -/
theorem crimeFEEC {κ : Type*} {H : HilbertComplex 𝕜 W} {a : ℤ} {m : ℕ} (S : H.CrimeFamily a m κ)
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) →
      IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ))))) :
    (∀ {cP : ℝ}, S.IsPoincare cP → ∃ C, S.StaticVerdict C) ∧
    (S.IsCochain → ∀ {Cπ : ℝ} (P : S.CochainProj Cπ), S.CochainVerdict P) ∧
    ∀ {cP : ℝ}, S.IsPoincare cP → Tendsto S.defect S.l (𝓝 0) → (∀ f, S.ConvergesAt f) →
      ∃ U, EvolutionVerdict (sq (H.wave a m)) S.l S.X S.incl
        (fun h => (S.D h - (S.D h).adjoint) ^ 2) U :=
  have : ∀ i, IsScalarTower ℝ 𝕜 (W i) := fun _ => RCLike.isScalarTower_of_normedSpace
  ⟨fun hP => (S.staticVerdict hcr hP).imp fun _ V => V.toStaticVerdict,
    fun hi _ P => (S.cochainVerdict hcr hi P).toCochainVerdict,
    fun hP hJ hconv => S.heatVerdict hcr hP hJ hconv⟩

/-- **Non-vacuity of `FEEC.crimeFEEC`** ([HolstStern2012], §3): on the complex `ℝ` in every degree
with `d⁰ = id` and all other differentials `0`, on the window `ℝ --id--> ℝ --0--> ℝ` (harmonic forms
`ℝ (0, 0, 1) ≠ 0`), the shear family of cochain reading maps `iₙ` with cochain projections `πₙ`,
`iₙ πₙ = 1`, of `Solution.Witness` satisfies the hypotheses of the cochain clause: closed ranges,
`iₙ* iₙ ≠ 1` (not isometric) but `‖1 - iₙ* iₙ‖ → 0`, so the defect, at most `‖1 - iₙ* iₙ‖`
(`HilbertComplex.CrimeFamily.defect_le`), tends to `0`; that clause gives the discrete Poincaré
inequality and convergence for every datum, the hypotheses of the two other clauses. Some discrete
harmonic form is read off `ℌ`, and the error at some datum is positive at every level. -/
theorem crime_nonvacuous : ∃ (H : HilbertComplex ℝ fun _ : ℤ => ℝ)
    (S : H.CrimeFamily.{0} 0 3 ℕ) (P : S.CochainProj 2),
    (∀ i : Fin 3, 0 < (i : ℕ) → IsClosed (H.boundaries (0 + (i : ℕ)) : Set ℝ)) ∧
    S.l = atTop ∧ S.IsCochain ∧ (∃ cP, S.IsPoincare cP) ∧
    (∀ n, (S.incl n).adjoint ∘L S.incl n ≠ 1) ∧
    Tendsto (fun n => ‖1 - (S.incl n).adjoint ∘L S.incl n‖) atTop (𝓝 0) ∧
    Tendsto S.defect atTop (𝓝 0) ∧ (∀ n (x : (H.totalD 0 3).domain), S.incl n (P.π n x) = x) ∧
    (∀ f, S.ConvergesAt f) ∧
    (∃ q ∈ H.totalHarmonic 0 3, q ≠ 0) ∧
    (∀ n, ∃ q ∈ S.harmonic n, S.incl n q ∉ H.totalHarmonic 0 3) ∧
    ∃ f, ∀ x, IsMixedSolution (H.totalMixedSpace 0 3) f x → ∀ n xh,
      S.IsSolution n f xh → 0 < S.readError n x xh := by
  have hcr : ∀ i : Fin 3, 0 < (i : ℕ) →
      IsClosed (Witness.complex.boundaries (0 + (i : ℕ)) : Set ℝ) :=
    fun _ _ => Submodule.closed_of_finiteDimensional _
  have hcr' := Witness.complex.closedRangeAt_win 0 3 hcr
  have hπ : ∀ n (x : (Witness.complex.totalD 0 3).domain),
      Witness.family.incl n (Witness.proj.π n x) = x := fun n x => Witness.incl_projL n x
  have V := (crimeFEEC Witness.family hcr).2.1 Witness.isCochain Witness.proj
  have hJ : Tendsto Witness.family.defect atTop (𝓝 0) :=
    Witness.family.tendsto_defect_of_tendsto Witness.tendsto_one_sub_J
  refine ⟨Witness.complex, Witness.family, Witness.proj, hcr, rfl, Witness.isCochain, V.poincare,
    Witness.J_ne_one, Witness.tendsto_one_sub_J, hJ, hπ,
    V.converges hJ fun x => by
      simp only [hπ, sub_self, norm_zero]; exact tendsto_const_nhds,
    ⟨Witness.e2, Witness.mem_totalHarmonic_e2, fun h0 => by
      have := congrArg (fun y : Witness.T3 => y 2) h0
      exact one_ne_zero this⟩,
    fun n => ⟨Witness.e2, Witness.mem_harmonic_e2 n, Witness.incl_e2_not_mem n⟩,
    Witness.e2, fun ⟨σ, u, p⟩ hs n ⟨σh, uh, ph⟩ hsh => ?_⟩
  replace hs := HilbertComplex.isMixedSolution_total_iff.1 hs
  replace hsh := (Witness.family.isSolution_iff).1 hsh
  rw [HilbertComplex.CrimeFamily.readError_eq₀]
  obtain ⟨-, -, hp⟩ := Witness.complex.eq_totalSol 0 3 hcr' hs
  obtain ⟨-, -, hp'⟩ := Witness.complex.eq_totalSol 0 3 hcr' Witness.isTotalMixedSolution_e2
  obtain ⟨-, -, hph⟩ := Witness.family.eq_mixedSol hsh
  obtain ⟨-, -, hph'⟩ := Witness.family.eq_mixedSol (Witness.isMixedSolution_e2 n)
  have e1 : p = Witness.e2 := hp.trans hp'.symm
  have e2 : ph = Witness.e2 := hph.trans hph'.symm
  have hpos : 0 < ‖p - Witness.family.incl n ph‖ := by
    rw [e1, e2]
    refine norm_pos_iff.2 fun h0 => ?_
    have h1 := congrArg (fun y : Witness.T3 => y 1) h0
    change Witness.e2 1 - Witness.incl n Witness.e2 1 = 0 at h1
    rw [Witness.incl_e2] at h1
    change (0 : ℝ) - Witness.mesh n = 0 at h1
    linarith [Witness.mesh_pos n]
  unfold HilbertComplex.CrimeFamily.readError₀
  positivity

open scoped lp in
/-- **Non-vacuity of the defect in the graph norm**: on the complex `ℓ²(ℕ, ℝ)` in every degree
with `d⁰ = diag(k + 1)` and all other differentials `0` (unbounded, `HighMode.not_bounded_totalD`;
closed ranges: `d⁰` is onto), the family of `Solution.HighMode` (the modes `k ≤ n` of both
degrees, reading maps doubling the square norm of the highest mode `k = n` of degree `0`, cochain
projections bounded by `1` in the graph norm, with `iₙ πₙ` the truncation to the modes `k ≤ n`)
has `‖1 - iₙ* iₙ‖ = 1` and `‖(1 - iₙ* iₙ) v‖ ≤ (‖v‖ + ‖𝐝ₙ v‖) / (n + 1)`
(`HighMode.norm_one_sub_J`, `HighMode.norm_one_sub_J_apply_le`); the cochain clause of
`FEEC.crimeFEEC` then gives the discrete Poincaré inequality and convergence for every datum. -/
theorem crime_defect_nonvacuous : ∃ (H : HilbertComplex ℝ fun _ : ℤ => ℓ²(ℕ, ℝ))
    (S : H.CrimeFamily.{0} 0 2 ℕ) (P : S.CochainProj 1),
    (¬ ∃ C, ∀ x : (H.totalD 0 2).domain,
      ‖H.totalD 0 2 x‖ ≤ C * ‖(x : Total (fun _ : ℤ => ℓ²(ℕ, ℝ)) 0 2)‖) ∧
    (∀ i : Fin 2, 0 < (i : ℕ) → IsClosed (H.boundaries (0 + (i : ℕ)) : Set ℓ²(ℕ, ℝ))) ∧
    S.l = atTop ∧ S.IsCochain ∧ (∃ cP, S.IsPoincare cP) ∧
    (∀ n, ‖1 - (S.incl n).adjoint ∘L S.incl n‖ = 1) ∧ Tendsto S.defect atTop (𝓝 0) ∧
    (∀ x : (H.totalD 0 2).domain, Tendsto (fun n =>
      ‖(x : Total (fun _ : ℤ => ℓ²(ℕ, ℝ)) 0 2) - S.incl n (P.π n x)‖) atTop (𝓝 0)) ∧
    ∀ f, S.ConvergesAt f := by
  have hcr := HighMode.isClosed_boundaries
  have V := (crimeFEEC HighMode.family hcr).2.1 HighMode.isCochain HighMode.proj
  have hJ : Tendsto HighMode.family.defect atTop (𝓝 0) :=
    squeeze_zero (fun n => HighMode.family.defect_nonneg n)
      (fun n => HighMode.family.defect_le_of_forall n (by positivity)
        (HighMode.norm_one_sub_J_apply_le n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hπ : ∀ x : (HighMode.complex.totalD 0 2).domain, Tendsto (fun n =>
      ‖(x : HighMode.T) - HighMode.family.incl n (HighMode.proj.π n x)‖) atTop (𝓝 0) :=
    fun x => HighMode.tendsto_incl_proj (x : HighMode.T)
  exact ⟨HighMode.complex, HighMode.family, HighMode.proj, HighMode.not_bounded_totalD, hcr, rfl,
    HighMode.isCochain, V.poincare, HighMode.norm_one_sub_J, hJ, hπ, V.converges hJ hπ⟩

/-- **Mass lumping of `P₁` elements** ([Thomee2006], Ch. 15): the bounds of
`Feec.FiniteElement.LumpedMassDefect` through the bridge `Solution.Lumped`: mass equivalence
(`Feec.FiniteElement.p1Mass_le_lumpedInner`, `Feec.FiniteElement.lumpedInner_le_mul_p1Mass`),
the hat functions (`Feec.FiniteElement.lumpedInner_nodalIndicator`,
`Feec.FiniteElement.lumpedMass_pos`, `Feec.FiniteElement.p1Mass_nodalIndicator`:
`⟨φₓ, φₓ⟩_L = m(x) > 0`, `⟨φₓ, φₓ⟩ = 2 m(x) / (n + 2)`), the defect from the graph norm
(`Feec.FiniteElement.abs_lumpedInner_sub_p1Mass_le`), and for lumped readings
(`Feec.FiniteElement.IsLumpedReading`) the operator bounds
`Feec.FiniteElement.IsLumpedReading.le_opNorm_one_sub_adjoint_comp_self` and
`Feec.FiniteElement.IsLumpedReading.norm_one_sub_adjoint_comp_self_apply_le`. -/
theorem crime_massLumping {n : ℕ} (M : SimplicialMesh n) :
    (∀ u, p1Mass M u u ≤ lumpedInner M u u ∧ lumpedInner M u u ≤ (n + 2) * p1Mass M u u) ∧
    (∀ T ∈ M.simplices, ∀ x ∈ vertexSet T,
      let φ : (Fin n → ℝ) → ℝ := fun z => if z = x then 1 else 0
      0 < lumpedInner M φ φ ∧
        lumpedInner M φ φ - p1Mass M φ φ = n / (n + 2) * lumpedInner M φ φ) ∧
    (∀ h : ℝ, 0 ≤ h →
      (∀ T ∈ M.simplices, ∀ i j, (T.points i - T.points j) ⬝ᵥ (T.points i - T.points j) ≤ h ^ 2) →
      ∀ u w, |lumpedInner M u w - p1Mass M u w| ≤
        √(n * (n + 1) / 2) / (n + 2) * h * √(p1Stiffness M u u) * √(lumpedInner M w w)) ∧
    ∀ {X E : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (ν : X → (Fin n → ℝ) → ℝ) (ι : X →L[ℝ] E),
      (∀ v w, ⟪v, w⟫_ℝ = lumpedInner M (ν v) (ν w)) →
      (∀ v w, ⟪ι v, ι w⟫_ℝ = p1Mass M (ν v) (ν w)) →
      (∀ T ∈ M.simplices, ∀ x ∈ vertexSet T, ∀ v, (ν v = fun z => if z = x then 1 else 0) →
        n / (n + 2) ≤ ‖1 - ι.adjoint ∘L ι‖) ∧
      ∀ h : ℝ, 0 ≤ h →
        (∀ T ∈ M.simplices, ∀ i j,
          (T.points i - T.points j) ⬝ᵥ (T.points i - T.points j) ≤ h ^ 2) →
        ∀ v, ‖(1 - ι.adjoint ∘L ι) v‖ ≤
          √(n * (n + 1) / 2) / (n + 2) * h * √(p1Stiffness M (ν v) (ν v)) := by
  refine ⟨fun u => ?_, fun T hT x hx => ?_, fun h hh hM u w => ?_,
    fun {X E} _ _ _ _ _ _ ν ι hν hι => ?_⟩
  · rw [p1Mass_eq, lumpedInner_eq]
    exact ⟨Feec.FiniteElement.p1Mass_le_lumpedInner _ u,
      Feec.FiniteElement.lumpedInner_le_mul_p1Mass _ u⟩
  · show 0 < lumpedInner M (Feec.FiniteElement.nodalIndicator x)
        (Feec.FiniteElement.nodalIndicator x) ∧
      lumpedInner M (Feec.FiniteElement.nodalIndicator x) (Feec.FiniteElement.nodalIndicator x) -
          p1Mass M (Feec.FiniteElement.nodalIndicator x) (Feec.FiniteElement.nodalIndicator x) =
        n / (n + 2) *
          lumpedInner M (Feec.FiniteElement.nodalIndicator x) (Feec.FiniteElement.nodalIndicator x)
    rw [p1Mass_eq, lumpedInner_eq, Feec.FiniteElement.lumpedInner_nodalIndicator,
      Feec.FiniteElement.p1Mass_nodalIndicator]
    refine ⟨Feec.FiniteElement.lumpedMass_pos M.toFeec hT (by rwa [← vertexSet_eq]), ?_⟩
    field_simp
    ring
  · rw [p1Mass_eq, lumpedInner_eq, lumpedInner_eq, p1Stiffness_eq]
    exact Feec.FiniteElement.abs_lumpedInner_sub_p1Mass_le M.toFeec hh hM u w
  · have hr : Feec.FiniteElement.IsLumpedReading M.toFeec ν ι :=
      ⟨fun v w => (hν v w).trans (lumpedInner_eq M _ _),
        fun v w => (hι v w).trans (p1Mass_eq M _ _)⟩
    refine ⟨fun T hT x hx v hv => hr.le_opNorm_one_sub_adjoint_comp_self hT
      (by rwa [← vertexSet_eq]) hv, fun h hh hM v => ?_⟩
    rw [p1Stiffness_eq]
    exact hr.norm_one_sub_adjoint_comp_self_apply_le hh hM v

end FEEC
