module

public import Feec.HilbertComplex.Approximation.DiscreteCohomology
public import Feec.HilbertComplex.Approximation.GraphApprox
public import Feec.HilbertComplex.Approximation.ImprovedEstimate
public import Feec.Variational.Fortin

/-!
# The static FEEC theorem

The approximation theory of [AFW2010], §3.3–§3.5 for the mixed Hodge Laplacian, for families of
subcomplexes bounded and approximating in the graph norm and for conforming families.

## Main results

* `SubcomplexFamily.staticFEEC`: stability, harmonic forms, cohomology and quasi-optimality.
* `ConformingFamily.staticFEEC`: the same for conforming families, closed range, finite `ℌʲ`.
* `ConformingFamily.StaticVerdict.rate`: the rate from a Jackson estimate.
* `ConformingFamily.rate_static_L2`: the improved `L²` rate.
* `SubcomplexFamily.closedRangeAt_of_discretePoincare`: closed range is necessary.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

/-! ### The constraint form and its continuous inf-sup condition -/

variable (H) in
/-- The constraint form `b(τ, q) = ⟪q, d τ⟫` of the mixed method on `Vʲ × Wᵏ`. -/
def constraintForm (j k : ι) : H.domainSpace j →L[𝕜] W k →L⋆[𝕜] 𝕜 :=
  innerSLFlip 𝕜 ∘L (H.domainIncl k ∘L H.domainD j k)

theorem constraintForm_apply (j k : ι) (τ : H.domainSpace j) (q : W k) :
    H.constraintForm j k τ q = ⟪q, H.d j k (H.domainCoord j k τ)⟫_𝕜 := rfl

theorem norm_le_norm_constraintForm_flip {j k : ι} (hjk : c.Rel j k) {cP : ℝ} (hcP : 0 ≤ cP)
    (hP : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    {q : W k} (hq : q ∈ H.boundaries k) :
    ‖q‖ ≤ (cP + 1) * ‖(H.constraintForm j k).flip q‖ := by
  obtain ⟨ρ, -, hdρ, hρ⟩ := H.exists_poincare_preimage hjk hP hq
  obtain rfl := c.next_eq' hjk
  set τ := (H.d j (c.next j)).toGraphSpace ρ
  have hτ : ‖τ‖ ≤ (cP + 1) * ‖q‖ := by
    have := LinearPMap.norm_toGraphSpace_le _ ρ
    rw [hdρ] at this
    linarith
  have hb : (H.constraintForm j (c.next j)).flip q τ = ⟪q, q⟫_𝕜 := by
    rw [ContinuousLinearMap.flip_apply, constraintForm_apply, ← hdρ]; rfl
  have h1 : ‖q‖ ^ 2 ≤ ‖(H.constraintForm j (c.next j)).flip q‖ * ((cP + 1) * ‖q‖) := by
    calc ‖q‖ ^ 2 = ‖(H.constraintForm j (c.next j)).flip q τ‖ := by
          rw [hb, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]
      _ ≤ ‖(H.constraintForm j (c.next j)).flip q‖ * ‖τ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by gcongr
  rcases (norm_nonneg q).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith [norm_nonneg ((H.constraintForm j (c.next j)).flip q)]

namespace Subcomplex

/-! ### The error of the mixed method -/

/-- The error `‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖` of the mixed method with data `f`. -/
def mixedError (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)] {i j k : ι}
    (hij : c.Rel i j) (hjk : c.Rel j k) (f : W j) (σ : H.domainSpace i) (u : H.domainSpace j)
    (p : H.harmonic j) : ℝ :=
  ‖σ - S.embD i (CochainProjection.discreteMixedSolution S hij hjk f).fst‖ +
    ‖u - S.embD j (CochainProjection.discreteMixedSolution S hij hjk f).snd.fst‖ +
    ‖(p : W j) - (((CochainProjection.discreteMixedSolution S hij hjk f).snd.snd : S.V j) : W j)‖

theorem mixedError_nonneg (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)] {i j k : ι}
    (hij : c.Rel i j) (hjk : c.Rel j k) (f : W j) (σ : H.domainSpace i) (u : H.domainSpace j)
    (p : H.harmonic j) : 0 ≤ S.mixedError hij hjk f σ u p := by
  unfold mixedError; positivity

/-! ### The rate for one cochain projection -/

namespace CochainProjection

variable {S : H.Subcomplex} [∀ i, FiniteDimensional 𝕜 (S.V i)] (P : S.CochainProjection)

theorem mixedApprox_le {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {C : ℝ} (hC : 0 ≤ C)
    (hπ : P.IsGraphBounded j k C) {Reg : ∀ l, W l → Prop} {ε : ι → ℝ}
    (happ : ∀ l (x : W l), Reg l x → ∃ v, ∃ hv : v ∈ S.V l, ‖x - v‖ ≤ ε l ∧
      ∀ j' (hx : x ∈ (H.d l j').domain),
        ‖H.d l j' ⟨x - v, Submodule.sub_mem _ hx (S.le_domain l j' hv)⟩‖ ≤ ε l)
    {σ : H.domainSpace i} {u : H.domainSpace j} {q : H.harmonic j}
    (hσ : Reg i (H.domainIncl i σ)) (hu : Reg j (H.domainIncl j u))
    (hb : Reg j (H.domainIncl j (H.boundaryPart j (H.domainIncl j u)))) (hq : Reg j (q : W j))
    {μ : ℝ} (hμ : μ ≤ 1 + C) :
    infDist σ (S.domainSub i) + infDist u (S.domainSub j) + infDist (q : W j) (S.harmonicW j) +
        μ * infDist (H.boundaryPart j (H.domainIncl j u)) (S.domainSub j) ≤
      2 * (ε i + (3 + 2 * C) * ε j) := by
  have dist_of : ∀ {l l' : ι}, c.Rel l l' → ∀ {τ : H.domainSpace l}, Reg l (H.domainIncl l τ) →
      infDist τ (S.domainSub l) ≤ 2 * ε l := fun {l l'} hl {τ} hτ => by
    obtain ⟨v, hv, h1, h2⟩ := happ _ _ hτ
    exact S.infDist_domainSub_le_two_mul hl τ hv h1 (h2 _)
  have d1 := dist_of hij hσ
  have d2 := dist_of hjk hu
  have d3 := mul_le_mul hμ (dist_of hjk hb) infDist_nonneg (by linarith)
  have d4 := (P.infDist_harmonicW_le hjk hC hπ q.2).trans (mul_le_mul_of_nonneg_left
    (dist_of hjk (τ := cyclesToDomainSpace (H.harmonic_le_cycles j q.2)) hq) (by linarith))
  linarith

theorem norm_sub_le_rate {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {cP C : ℝ}
    (hC : 1 ≤ C)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : P.IsGraphBounded i j C) (hπj : P.IsGraphBounded j k C) {Reg : ∀ l, W l → Prop}
    {B : ι → ℝ} (hB : ∀ l, 0 ≤ B l) {r : ℝ} (hr : 0 ≤ r)
    (happ : ∀ l (x : W l), Reg l x → ∃ v, ∃ hv : v ∈ S.V l, ‖x - v‖ ≤ B l * r ∧
      ∀ j' (hx : x ∈ (H.d l j').domain),
        ‖H.d l j' ⟨x - v, Submodule.sub_mem _ hx (S.le_domain l j' hv)⟩‖ ≤ B l * r)
    {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {q : H.harmonic j}
    (hs : H.IsMixedSolution i j k f σ u q) (hσ : Reg i (H.domainIncl i σ))
    (hu : Reg j (H.domainIncl j u))
    (hb : Reg j (H.domainIncl j (H.boundaryPart j (H.domainIncl j u))))
    (hq : Reg j (q : W j)) :
    S.mixedError hij hjk f σ u q ≤
      (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) * (2 * (B i + B j) * (3 + 2 * C)) * r := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hK : 0 ≤ (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) := by positivity
  refine (P.norm_sub_le_infDist hij hjk hC (by linarith) hPi hPj hπi hπj
    (fun _ hq' => P.norm_sub_π_harmonic_le hjk hC0 hπj hq') hs).trans ?_
  have h := P.mixedApprox_le hij hjk hC0 hπj (ε := fun l => B l * r) happ hσ hu hb hq
    (μ := 1 + C) le_rfl
  have hBi := mul_nonneg (hB i) hr
  have hBj := mul_nonneg (hB j) hr
  have : 2 * (B i * r + (3 + 2 * C) * (B j * r)) ≤ 2 * (B i + B j) * (3 + 2 * C) * r := by
    nlinarith
  calc _ ≤ (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) * (2 * (B i + B j) * (3 + 2 * C) * r) :=
        mul_le_mul_of_nonneg_left (h.trans this) hK
    _ = _ := by ring

/-! ### Fortin operators from the cochain projections -/

theorem exists_isFortinOperator {j k : ι} (hjk : c.Rel j k) {cP C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπ : P.IsGraphBounded j k C) :
    ∃ Pf : H.domainSpace j → H.domainSpace j, Variational.IsFortinOperator
      (H.constraintForm j k) (S.domainSub j) (S.boundariesW k) Pf (C * √(1 + cP ^ 2) + 1) := by
  have : FiniteDimensional 𝕜 (S.boundariesW k) :=
    Submodule.finiteDimensional_of_le (S.boundariesW_le_V k)
  set D : H.domainSpace j → W k := fun τ => H.d j k (H.domainCoord j k τ)
  set Q := (S.boundariesW k).starProjection
  choose ρ _ hdρ hρ using fun τ => H.exists_poincare_preimage hjk hP
    (S.boundariesW_le k (Submodule.starProjection_apply_mem _ (D τ)))
  obtain rfl := c.next_eq' hjk
  have hd : ∀ τ, H.d j (c.next j) ⟨P.π j (ρ τ), S.le_domain j _ (P.mem j _)⟩ = Q (D τ) :=
    fun τ => by
      rw [P.comm, hdρ, P.proj _ _ (S.boundariesW_le_V _ (Submodule.starProjection_apply_mem _ _))]
  refine ⟨fun τ => (H.d j (c.next j)).toGraphSpace ⟨P.π j (ρ τ), S.le_domain j _ (P.mem j _)⟩,
    ⟨fun τ => ⟨(S.toHilbertComplex.d j (c.next j)).toGraphSpace
      ⟨⟨P.π j (ρ τ), P.mem j _⟩, Submodule.mem_top⟩, rfl⟩, fun τ q hq => ?_, fun τ => ?_⟩⟩
  · change ⟪q, H.d j (c.next j) ⟨P.π j (ρ τ), _⟩⟫_𝕜 = ⟪q, D τ⟫_𝕜
    rw [hd, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 hq]
  · refine (LinearPMap.norm_toGraphSpace_le _ _).trans ?_
    rw [hd]
    set a := ‖P.π j (ρ τ)‖
    set q := ‖Q (D τ)‖
    have h1 : a ≤ C * √(1 + cP ^ 2) * q := by
      have h := hπ (ρ τ)
      rw [hdρ] at h
      have h2 := hρ τ
      have hr := norm_nonneg ((ρ τ : (H.d j (c.next j)).domain) : W j)
      have hq := norm_nonneg (Q (D τ))
      have hs : (C * √(1 + cP ^ 2) * q) ^ 2 = C ^ 2 * ((1 + cP ^ 2) * q ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
      have hsq : a ^ 2 ≤ (C * √(1 + cP ^ 2) * q) ^ 2 := by
        rw [hs]
        have h3 : ‖((ρ τ : (H.d j (c.next j)).domain) : W j)‖ ^ 2 ≤ cP ^ 2 * q ^ 2 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ hr h2 2
        nlinarith [sq_nonneg ‖H.d j (c.next j) ⟨P.π j (ρ τ), S.le_domain j _ (P.mem j _)⟩‖,
          sq_nonneg C]
      exact (abs_le_of_sq_le_sq' hsq (by positivity)).2
    have h3 := (S.boundariesW _).norm_starProjection_apply_le (D τ)
    have h4 := H.norm_d_domainCoord_le j (c.next j) τ
    calc a + q ≤ C * √(1 + cP ^ 2) * q + q := add_le_add_left h1 _
      _ = (C * √(1 + cP ^ 2) + 1) * q := by ring
      _ ≤ (C * √(1 + cP ^ 2) + 1) * ‖τ‖ := by gcongr; exact h3.trans h4

theorem infSup {j k : ι} (hjk : c.Rel j k) {cP C : ℝ} (hcP : 0 ≤ cP) (hC : 0 ≤ C)
    (hP : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπ : P.IsGraphBounded j k C) {q : W k} (hq : q ∈ S.boundariesW k) :
    ((cP + 1) * (C * √(1 + cP ^ 2) + 1))⁻¹ * ‖q‖ ≤
      ‖((H.constraintForm j k).flip q).comp (S.domainSub j).subtypeL‖ := by
  obtain ⟨Pf, hPf⟩ := P.exists_isFortinOperator hjk hC hP hπ
  have h := hPf.discrete_infSup (by positivity) (β := (cP + 1)⁻¹) (fun q hq => by
    rw [inv_mul_le_iff₀ (by positivity)]
    exact norm_le_norm_constraintForm_flip hjk hcP hP (S.boundariesW_le k hq)) q hq
  rwa [mul_inv, ← div_eq_mul_inv]

theorem exists_isFortinOperator_of_norm_le {j k : ι} (hjk : c.Rel j k) {cP C : ℝ} (hcP : 0 ≤ cP)
    (hC : 0 ≤ C)
    (hP : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπ : ∀ x, ‖P.π j x‖ ≤ C * ‖x‖) :
    ∃ Pf : H.domainSpace j → H.domainSpace j, Variational.IsFortinOperator
      (H.constraintForm j k) (S.domainSub j) (S.boundariesW k) Pf (C * cP + 1) := by
  have : FiniteDimensional 𝕜 (S.boundariesW k) :=
    Submodule.finiteDimensional_of_le (S.boundariesW_le_V k)
  set D : H.domainSpace j → W k := fun τ => H.d j k (H.domainCoord j k τ)
  set Q := (S.boundariesW k).starProjection
  choose ρ _ hdρ hρ using fun τ => H.exists_poincare_preimage hjk hP
    (S.boundariesW_le k (Submodule.starProjection_apply_mem _ (D τ)))
  obtain rfl := c.next_eq' hjk
  have hd : ∀ τ, H.d j (c.next j) ⟨P.π j (ρ τ), S.le_domain j _ (P.mem j _)⟩ = Q (D τ) :=
    fun τ => by
      rw [P.comm, hdρ, P.proj _ _ (S.boundariesW_le_V _ (Submodule.starProjection_apply_mem _ _))]
  refine ⟨fun τ => (H.d j (c.next j)).toGraphSpace ⟨P.π j (ρ τ), S.le_domain j _ (P.mem j _)⟩,
    ⟨fun τ => ⟨(S.toHilbertComplex.d j (c.next j)).toGraphSpace
      ⟨⟨P.π j (ρ τ), P.mem j _⟩, Submodule.mem_top⟩, rfl⟩, fun τ q hq => ?_, fun τ => ?_⟩⟩
  · change ⟪q, H.d j (c.next j) ⟨P.π j (ρ τ), _⟩⟫_𝕜 = ⟪q, D τ⟫_𝕜
    rw [hd, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 hq]
  · refine (LinearPMap.norm_toGraphSpace_le _ _).trans ?_
    rw [hd]
    have h1 := hπ (ρ τ)
    have h2 := hρ τ
    have h3 := (S.boundariesW _).norm_starProjection_apply_le (D τ)
    have h4 := H.norm_d_domainCoord_le j (c.next j) τ
    calc ‖P.π j (ρ τ)‖ + ‖Q (D τ)‖ ≤ C * (cP * ‖Q (D τ)‖) + ‖Q (D τ)‖ :=
          add_le_add_left (h1.trans (mul_le_mul_of_nonneg_left h2 hC)) _
      _ = (C * cP + 1) * ‖Q (D τ)‖ := by ring
      _ ≤ (C * cP + 1) * ‖τ‖ := by gcongr; exact h3.trans h4

theorem infSup_of_norm_le {j k : ι} (hjk : c.Rel j k) {cP C : ℝ} (hcP : 0 ≤ cP) (hC : 0 ≤ C)
    (hP : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπ : ∀ x, ‖P.π j x‖ ≤ C * ‖x‖) {q : W k} (hq : q ∈ S.boundariesW k) :
    ((cP + 1) * (C * cP + 1))⁻¹ * ‖q‖ ≤
      ‖((H.constraintForm j k).flip q).comp (S.domainSub j).subtypeL‖ := by
  obtain ⟨Pf, hPf⟩ := P.exists_isFortinOperator_of_norm_le hjk hcP hC hP hπ
  have h := hPf.discrete_infSup (by positivity) (β := (cP + 1)⁻¹) (fun q hq => by
    rw [inv_mul_le_iff₀ (by positivity)]
    exact norm_le_norm_constraintForm_flip hjk hcP hP (S.boundariesW_le k hq)) q hq
  rwa [mul_inv, ← div_eq_mul_inv]

end CochainProjection

/-! ### Families of subcomplexes with uniformly bounded projections -/

variable {κ : Type*}

/-- Uniformly bounded cochain projections onto `S h` with harmonic gaps tending to `0`. -/
def HasUniformProj (l : Filter κ) (S : κ → H.Subcomplex) : Prop :=
  ∃ (C : ℝ) (π : ∀ h, (S h).CochainProjection), 1 ≤ C ∧ (∀ h i x, ‖(π h).π i x‖ ≤ C * ‖x‖) ∧
    (∀ h i j, (π h).IsGraphBounded i j C) ∧
    ∀ j, Tendsto (fun h => (π h).harmonicGap j) l (𝓝 0)

namespace HasUniformProj

variable {l : Filter κ} {S : κ → H.Subcomplex} {cP : ℝ}
  (hP : ∀ i j, c.Rel i j → ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ →
    ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
include hP

theorem discretePoincare (hU : HasUniformProj l S) : ∃ C : ℝ, ∀ {i j : ι}, c.Rel i j →
    ∀ (h : κ) {x : W i} (hx : x ∈ (S h).V i), (∀ y ∈ (S h).cyclesW i, ⟪y, x⟫_𝕜 = 0) →
      ‖x‖ ≤ C * ‖H.d i j ⟨x, (S h).le_domain i j hx⟩‖ := by
  obtain ⟨C, π, hC, hπ, -, -⟩ := hU
  exact ⟨C * cP, fun {i j} hij h x hx hxo =>
    (π h).norm_le_of_forall_inner_eq_zero hij (hP i j hij) (zero_le_one.trans hC) (hπ h i) hx hxo⟩

theorem mixed_wellPosed [∀ h i, FiniteDimensional 𝕜 ((S h).V i)] (hcP : 1 ≤ cP)
    (hU : HasUniformProj l S) : ∃ C : ℝ, ∀ {i j k : ι}, c.Rel i j → c.Rel j k →
    ∀ (h : κ) (f : (S h).V j),
    (∃! x, (S h).toHilbertComplex.mixedForm i j k x = (S h).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (S h).toHilbertComplex.MixedSpace i j,
      (S h).toHilbertComplex.mixedForm i j k x = (S h).toHilbertComplex.mixedRHS i j f →
        ‖x‖ ≤ C * ‖f‖ := by
  obtain ⟨C, π, hC1, hb, -, -⟩ := hU
  refine ⟨16 * (C * cP) ^ 2, fun {i j k} hij hjk h f => ⟨?_, fun x hx => ?_⟩⟩
  · exact (π h).existsUnique_mixed hij hjk hcP hC1 (hP i j hij) (hP j k hjk) (hb h i) (hb h j) f
  · exact (π h).norm_le_of_mixed hij hjk hcP hC1 (hP i j hij) (hP j k hjk) (hb h i) (hb h j) hx

theorem mixed_quasiOptimal [∀ h i, FiniteDimensional 𝕜 ((S h).V i)] (hU : HasUniformProj l S) :
    ∃ (K : ℝ) (μ : ι → κ → ℝ), (∀ j, Tendsto (μ j) l (𝓝 0)) ∧
    ∀ {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k)
    {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {q : H.harmonic j},
    H.IsMixedSolution i j k f σ u q → ∀ h : κ,
    (S h).mixedError hij hjk f σ u q ≤
      K * (infDist σ ((S h).domainSub i) + infDist u ((S h).domainSub j) +
        infDist (q : W j) ((S h).harmonicW j) +
        μ j h * infDist (H.boundaryPart j (H.domainIncl j u)) ((S h).domainSub j)) := by
  obtain ⟨C, π, hC1, -, hg, hgap⟩ := hU
  exact ⟨(1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C), fun j h => (π h).harmonicGap j, hgap,
    fun {i j k} hij hjk _ _ _ _ hs h => (π h).norm_sub_le_infDist_harmonicGap hij hjk hC1
      (hP i j hij) (hP j k hjk) (hg h i j) (hg h j k) hs⟩

end HasUniformProj

end Subcomplex

/-! ### Families of subcomplexes, bounded and approximating in the graph norm -/

namespace SubcomplexFamily

variable {κ : Type*} (G : SubcomplexFamily H κ)

/-- The projections are bounded in the graph norm of `Vⁱ`, uniformly in `h`. -/
def IsGraphBounded (i : ι) : Prop := ∃ C, ∀ h, (G.π h).IsGraphBounded i (c.next i) C

/-- `Vₕ` **approximates** `Vⁱ` in the graph norm: `dist_V(σ, Vₕⁱ) → 0` for every `σ ∈ Vⁱ`. -/
def Approximates (i : ι) : Prop :=
  ∀ σ : H.domainSpace i, Tendsto (fun h => infDist σ ((G.V h).domainSub i)) G.l (𝓝 0)

variable {G}

theorem IsGraphBounded.exists_bound {i j : ι} (hi : G.IsGraphBounded i) (hj : G.IsGraphBounded j) :
    ∃ C, 1 ≤ C ∧ (∀ h, (G.π h).IsGraphBounded i (c.next i) C) ∧
      ∀ h, (G.π h).IsGraphBounded j (c.next j) C := by
  obtain ⟨Ci, hCi⟩ := hi
  obtain ⟨Cj, hCj⟩ := hj
  have mono : ∀ {l : ι} {C₀ C : ℝ}, |C₀| ≤ C → ∀ h, (G.π h).IsGraphBounded l (c.next l) C₀ →
      (G.π h).IsGraphBounded l (c.next l) C := fun hC h hb x =>
    (hb x).trans (mul_le_mul_of_nonneg_right
      (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hC 2) (by positivity))
  exact ⟨max (max |Ci| |Cj|) 1, le_max_right _ _,
    fun h => mono (le_max_of_le_left (le_max_left _ _)) h (hCi h),
    fun h => mono (le_max_of_le_left (le_max_right _ _)) h (hCj h)⟩

theorem IsGraphBounded.exists_bound_one {i : ι} (hi : G.IsGraphBounded i) :
    ∃ C, 1 ≤ C ∧ ∀ h, (G.π h).IsGraphBounded i (c.next i) C := by
  obtain ⟨C, hC, h1, -⟩ := hi.exists_bound hi
  exact ⟨C, hC, h1⟩

theorem _root_.Feec.HilbertComplex.Subcomplex.CochainProjection.IsGraphBounded.of_next
    {S : H.Subcomplex} {P : S.CochainProjection} {i j : ι} {C : ℝ}
    (h : P.IsGraphBounded i (c.next i) C) (hij : c.Rel i j) : P.IsGraphBounded i j C := by
  obtain rfl := c.next_eq' hij
  exact h

theorem tendsto_sub_π_of_mem_cycles {j : ι} (hb : G.IsGraphBounded j) (ha : G.Approximates j)
    {b : W j} (hbz : b ∈ H.cycles j) : Tendsto (fun h => ‖b - (G.π h).π j b‖) G.l (𝓝 0) := by
  obtain ⟨C, hC1, hC⟩ := hb.exists_bound_one
  have hC' : 0 < 1 + C := by linarith
  have h0 := (ha (cyclesToDomainSpace hbz)).const_mul (1 + C)
  rw [mul_zero] at h0
  refine squeeze_zero (fun _ => norm_nonneg _) (fun h => ?_) h0
  rw [← div_le_iff₀' hC']
  refine (le_infDist ⟨0, zero_mem _⟩).2 fun y hy => ?_
  obtain ⟨w, rfl⟩ := hy
  rw [div_le_iff₀' hC', dist_eq_norm]
  exact (G.π h).norm_sub_π_le_of_mem_cycles_of_next (by linarith) (hC h) hbz w

theorem tendsto_harmonicGap {j : ι} [FiniteDimensional 𝕜 (H.harmonic j)]
    (hb : G.IsGraphBounded j) (ha : G.Approximates j) :
    Tendsto (fun h => (G.π h).harmonicGap j) G.l (𝓝 0) :=
  Subcomplex.CochainProjection.tendsto_harmonicGap_of_tendsto G.π fun _ hq =>
    tendsto_sub_π_of_mem_cycles hb ha (H.harmonic_le_cycles _ hq)

theorem eventually_bijective_cohomologyMap {i : ι} [FiniteDimensional 𝕜 (H.harmonic i)]
    (hb : G.IsGraphBounded i) (ha : G.Approximates i) (hi : H.ClosedRangeAt i) :
    ∀ᶠ h in G.l, Function.Bijective ((G.π h).cohomologyMap i) := by
  obtain ⟨C, hC1, hC⟩ := hb.exists_bound_one
  exact ((tendsto_harmonicGap hb ha).eventually (gt_mem_nhds one_pos)).mono fun h h1 =>
    ⟨(G.π h).cohomologyMap_injective hi fun _ hq hq0 =>
      (G.π h).norm_sub_π_lt_of_harmonicGap_lt_one (fun _ hq' =>
        (G.π h).norm_sub_π_harmonic_le_of_next (zero_le_one.trans hC1) (hC h) hq') h1 hq hq0,
      (G.π h).cohomologyMap_surjective i⟩

theorem quasiOptimal {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) (hbi : G.IsGraphBounded i)
    (hbj : G.IsGraphBounded j) (hj : H.ClosedRangeAt j) (hk : H.ClosedRangeAt k) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j},
    H.IsMixedSolution i j k f σ u p → ∀ h : κ,
    (G.V h).mixedError hij hjk f σ u p ≤
      K * (infDist σ ((G.V h).domainSub i) + infDist u ((G.V h).domainSub j) +
        infDist (p : W j) ((G.V h).harmonicW j) +
        (G.π h).harmonicGap j *
          infDist (H.boundaryPart j (H.domainIncl j u)) ((G.V h).domainSub j)) := by
  obtain ⟨C, hC, hCi, hCj⟩ := hbi.exists_bound hbj
  obtain ⟨cP, -, hPi, hPj⟩ := H.exists_poincare_pair hij hjk hj hk
  exact ⟨_, by have := zero_le_one.trans hC; positivity, fun hs h =>
    (G.π h).norm_sub_le_infDist_harmonicGap hij hjk hC hPi hPj ((hCi h).of_next hij)
      ((hCj h).of_next hjk) hs⟩

/-! ### The static FEEC theorem -/

variable (G)

/-- The conclusions of the static FEEC theorem for a family of subcomplexes at the degree `j`. -/
structure StaticVerdict (j : ι) : Prop where
  /-- the uniform discrete Poincaré inequality on `Vₕʲ ⊥ 𝔷ₕʲ` -/
  poincare {k : ι} (hjk : c.Rel j k) : ∃ C : ℝ, ∀ (h : κ) {x : W j} (hx : x ∈ (G.V h).V j),
    (∀ y ∈ (G.V h).cyclesW j, ⟪y, x⟫_𝕜 = 0) → ‖x‖ ≤ C * ‖H.d j k ⟨x, (G.V h).le_domain j k hx⟩‖
  /-- the uniform well-posedness of the discrete mixed problem -/
  wellPosed {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) : ∃ C : ℝ, ∀ (h : κ) (f : (G.V h).V j),
    (∃! x, (G.V h).toHilbertComplex.mixedForm i j k x = (G.V h).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (G.V h).toHilbertComplex.MixedSpace i j,
      (G.V h).toHilbertComplex.mixedForm i j k x = (G.V h).toHilbertComplex.mixedRHS i j f →
        ‖x‖ ≤ C * ‖f‖
  /-- `‖q - P_{ℌₕ} q‖ ≤ ‖q - πₕ q‖` on `ℌʲ` -/
  harmonicDist (h : κ) {q : W j} (hq : q ∈ H.harmonic j) :
    ‖q - ((G.V h).harmonicW j).starProjection q‖ ≤ ‖q - (G.π h).π j q‖
  /-- the harmonic gap tends to `0` -/
  harmonicGap (ha : G.Approximates j) [FiniteDimensional 𝕜 (H.harmonic j)] :
    Tendsto (fun h => (G.π h).harmonicGap j) G.l (𝓝 0)
  /-- `πₕ` eventually induces isomorphisms `Hʲ(H) ≅ Hʲ(Vₕ)` -/
  cohomology (ha : G.Approximates j) [FiniteDimensional 𝕜 (H.harmonic j)] :
    ∀ᶠ h in G.l, Function.Bijective ((G.π h).cohomologyMap j)
  /-- quasi-optimality of the mixed method -/
  quasiOptimal {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j},
    H.IsMixedSolution i j k f σ u p → ∀ h : κ,
    (G.V h).mixedError hij hjk f σ u p ≤
      K * (infDist σ ((G.V h).domainSub i) + infDist u ((G.V h).domainSub j) +
        infDist (p : W j) ((G.V h).harmonicW j) +
        (G.π h).harmonicGap j * infDist (H.boundaryPart j (H.domainIncl j u)) ((G.V h).domainSub j))
  /-- the discrete solutions converge -/
  converges {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) (hai : G.Approximates i)
    (haj : G.Approximates j) {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j}
    {p : H.harmonic j} (hs : H.IsMixedSolution i j k f σ u p) :
    Tendsto (fun h => (G.V h).mixedError hij hjk f σ u p) G.l (𝓝 0)
  /-- the uniform discrete inf-sup condition of `d` on `𝔅ₕᵏ` -/
  infSup {k : ι} (hjk : c.Rel j k) : ∃ β : ℝ, 0 < β ∧ ∀ (h : κ), ∀ q ∈ (G.V h).boundariesW k,
    β * ‖q‖ ≤ ‖((H.constraintForm j k).flip q).comp ((G.V h).domainSub j).subtypeL‖

/-- **The static FEEC theorem**: graph-bounded projections in degrees `c.prev j`, `j` and closed
range at `j` and the next degree give `StaticVerdict G j`. [AFW2010], Thms 3.4–3.6, 3.8, 3.9 -/
theorem staticFEEC (j : ι) (hbi : G.IsGraphBounded (c.prev j)) (hbj : G.IsGraphBounded j)
    (hj : H.ClosedRangeAt j) (hk : ∀ k, c.Rel j k → H.ClosedRangeAt k) : G.StaticVerdict j := by
  obtain ⟨C, hC, hCi, hCj⟩ := hbi.exists_bound hbj
  have hC0 := zero_le_one.trans hC
  refine ⟨fun {k} hjk => ?_, fun {i k} hij hjk => ?_, fun h q hq => ?_,
    fun ha _ => tendsto_harmonicGap hbj ha, fun ha _ => eventually_bijective_cohomologyMap hbj ha hj,
    fun {i k} hij hjk => ?_, fun {i k} hij hjk hai haj f σ u p hs => ?_, fun {k} hjk => ?_⟩
  · obtain ⟨cP, -, hP⟩ := H.exists_poincare_of_closedRangeAt hjk (hk k hjk)
    exact ⟨C * √(1 + cP ^ 2), fun h x hx hxo =>
      (G.π h).norm_le_of_forall_inner_eq_zero_of_graph hjk hP hC0 ((hCj h).of_next hjk) hx hxo⟩
  · obtain rfl := c.prev_eq' hij
    obtain ⟨cP, -, hPi, hPj⟩ := H.exists_poincare_pair hij hjk hj (hk k hjk)
    have p1 := fun h => (G.π h).poincare_toHilbertComplex_of_graph hij hPi hC0 ((hCi h).of_next hij)
    have p2 := fun h => (G.π h).poincare_toHilbertComplex_of_graph hjk hPj hC0 ((hCj h).of_next hjk)
    exact ⟨16 * (C * √(1 + cP ^ 2)) ^ 2, fun h f =>
      ⟨(G.V h).toHilbertComplex.existsUnique_mixed hij hjk
          (Subcomplex.CochainProjection.one_le_mul_sqrt hC) (p1 h) (p2 h) f,
        fun x hx => (G.V h).toHilbertComplex.norm_le_of_mixed hij hjk
          (Subcomplex.CochainProjection.one_le_mul_sqrt hC) (p1 h) (p2 h) hx⟩⟩
  · exact (G.π h).norm_sub_starProjection_harmonicW_le hq
  · obtain rfl := c.prev_eq' hij
    exact quasiOptimal hij hjk hbi hbj hj (hk k hjk)
  · -- the distances tend to `0`; the harmonic gap stays below `1 + C`
    obtain rfl := c.prev_eq' hij
    obtain ⟨K, -, hK⟩ := quasiOptimal hij hjk hbi hbj hj (hk k hjk)
    have hq : Tendsto (fun h => infDist (p : W j) ((G.V h).harmonicW j)) G.l (𝓝 0) := by
      have h0 := (haj (cyclesToDomainSpace (H.harmonic_le_cycles j p.2))).const_mul (1 + C)
      rw [mul_zero] at h0
      exact squeeze_zero (fun _ => infDist_nonneg) (fun h => (G.π h).infDist_harmonicW_le hjk
        hC0 ((hCj h).of_next hjk) p.2) h0
    have hμ : ∀ h, (G.π h).harmonicGap j ≤ 1 + C := fun h => (G.π h).harmonicGap_le (by linarith)
      fun _ hq' => (G.π h).norm_sub_π_harmonic_le_of_next hC0 (hCj h) hq'
    have hb : Tendsto (fun h => (G.π h).harmonicGap j *
        infDist (H.boundaryPart j (H.domainIncl j u)) ((G.V h).domainSub j)) G.l (𝓝 0) := by
      have h0 := (haj (H.boundaryPart j (H.domainIncl j u))).const_mul (1 + C)
      rw [mul_zero] at h0
      exact squeeze_zero (fun h => mul_nonneg ((G.π h).harmonicGap_nonneg j) infDist_nonneg)
        (fun h => mul_le_mul_of_nonneg_right (hμ h) infDist_nonneg) h0
    have h0 := ((((hai σ).add (haj u)).add hq).add hb).const_mul K
    simp only [add_zero, mul_zero] at h0
    exact squeeze_zero (fun h => (G.V h).mixedError_nonneg hij hjk f σ u p) (fun h => hK hs h) h0
  · -- Fortin's criterion with the Fortin operators of the projections
    obtain ⟨cP, hcP, hP⟩ := H.exists_poincare_of_closedRangeAt hjk (hk k hjk)
    have hcP0 : 0 ≤ cP := by linarith
    exact ⟨_, by positivity, fun h q hq => (G.π h).infSup hjk hcP0 hC0 hP
      ((hCj h).of_next hjk) hq⟩

theorem _root_.Feec.HilbertComplex.SubcomplexFamily.Jackson.approx_le {G : SubcomplexFamily H κ}
    {ρ : Type*} (J : G.Jackson ρ) (s : ρ) (h : κ) {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k)
    {C : ℝ} (hC : 0 ≤ C) (hπ : (G.π h).IsGraphBounded j k C) {L : ℝ} (hL : 0 ≤ L)
    {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j}
    (hσ : J.Reg s i L (H.domainIncl i σ)) (hu : J.Reg s j L (H.domainIncl j u))
    (hb : J.Reg s j L (H.domainIncl j (H.boundaryPart j (H.domainIncl j u))))
    (hp : J.Reg s j L (p : W j)) :
    infDist σ ((G.V h).domainSub i) + infDist u ((G.V h).domainSub j) +
        infDist (p : W j) ((G.V h).harmonicW j) +
        (G.π h).harmonicGap j *
          infDist (H.boundaryPart j (H.domainIncl j u)) ((G.V h).domainSub j) ≤
      2 * (J.B s i + (3 + 2 * C) * J.B s j) * (L * J.meshSize h ^ J.ord s) := by
  have hgap : (G.π h).harmonicGap j ≤ 1 + C := (G.π h).harmonicGap_le (by linarith)
    fun _ hq => (G.π h).norm_sub_π_harmonic_le hjk hC hπ hq
  refine ((G.π h).mixedApprox_le hij hjk hC hπ
    (Reg := fun l x => J.Reg s l L x) (ε := fun l => J.B s l * (L * J.meshSize h ^ J.ord s))
    (fun l x hx => J.jackson s h l x hL hx) hσ hu hb hp hgap).trans_eq ?_
  ring

theorem StaticVerdict.rate {G : SubcomplexFamily H κ} {j : ι} (V : G.StaticVerdict j) {ρ : Type*}
    (J : G.Jackson ρ) (s : ρ) {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {C : ℝ} (hC : 0 ≤ C)
    (hπ : ∀ h, (G.π h).IsGraphBounded j k C) :
    ∃ K : ℝ, ∀ {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j},
    H.IsMixedSolution i j k f σ u p → ∀ {L : ℝ}, 0 ≤ L →
    J.Reg s i L (H.domainIncl i σ) → J.Reg s j L (H.domainIncl j u) →
    J.Reg s j L (H.domainIncl j (H.boundaryPart j (H.domainIncl j u))) →
    J.Reg s j L (p : W j) → ∀ h : κ,
    (G.V h).mixedError hij hjk f σ u p ≤ K * L * J.meshSize h ^ J.ord s := by
  obtain ⟨K, hK, hqo⟩ := V.quasiOptimal hij hjk
  exact ⟨K * (2 * (J.B s i + (3 + 2 * C) * J.B s j)), fun hs L hL hσ hu hb hp h =>
    ((hqo hs h).trans (mul_le_mul_of_nonneg_left
      (J.approx_le s h hij hjk hC (hπ h) hL hσ hu hb hp) hK)).trans_eq (by ring)⟩

/-! ### Closed range is necessary -/

variable {G}

theorem eventually_exists_orthogonal_cyclesW {j k : ι} (hjk : c.Rel j k) (ha : G.Approximates j)
    {z : (H.d j k).domain} (hz : (z : W j) ∈ (H.cycles j)ᗮ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in G.l, ∃ (y : W j) (hy : y ∈ (G.V h).V j), (∀ q ∈ (G.V h).cyclesW j, ⟪q, y⟫_𝕜 = 0) ∧
      ‖(z : W j) - y‖ < ε ∧ ‖H.d j k z - H.d j k ⟨y, (G.V h).le_domain j k hy⟩‖ < ε := by
  obtain rfl := c.next_eq' hjk
  filter_upwards [(tendsto_order.1 (ha ((H.d j (c.next j)).toGraphSpace z))).2 (ε / 2)
    (half_pos hε)] with h hh
  obtain ⟨_, ⟨a, rfl⟩, hwd⟩ := (infDist_lt_iff ⟨0, zero_mem _⟩).1 hh
  set Z := (G.V h).cyclesW j
  set v : W j := (G.V h).toW j a
  have hv : v ∈ (G.V h).V j := ((G.V h).toHilbertComplex.domainIncl j a).2
  set σ : H.domainSpace j := (H.d j (c.next j)).toGraphSpace z
  change dist σ ((G.V h).embD j a) < ε / 2 at hwd
  have hσ := norm_domainIncl_le H j (σ - (G.V h).embD j a)
  have hσd := norm_d_domainCoord_le H j (c.next j) (σ - (G.V h).embD j a)
  rw [← dist_eq_norm] at hσ hσd
  rw [_root_.map_sub] at hσ
  rw [_root_.map_sub, LinearPMap.map_sub] at hσd
  change ‖(z : W j) - v‖ ≤ _ at hσ
  have e : H.domainCoord j (c.next j) ((G.V h).embD j a) =
      ⟨v, (G.V h).le_domain j (c.next j) hv⟩ := rfl
  have e' : H.domainCoord j (c.next j) σ = z := rfl
  rw [e, e'] at hσd
  have hp : Z.starProjection v ∈ Z := Z.starProjection_apply_mem v
  have hy : v - Z.starProjection v ∈ (G.V h).V j := sub_mem hv ((G.V h).cyclesW_le j hp)
  have hdy : H.d j (c.next j) ⟨v - Z.starProjection v, (G.V h).le_domain j _ hy⟩ =
      H.d j (c.next j) ⟨v, (G.V h).le_domain j _ hv⟩ := by
    have hpk : (Z.starProjection v : W j) ∈ (H.d j (c.next j)).ker := by
      rw [← H.cycles_eq hjk]; exact (G.V h).cyclesW_le_cycles j hp
    obtain ⟨p, hp1, hp2⟩ := LinearPMap.mem_ker_iff.1 hpk
    have e : (⟨v - Z.starProjection v, (G.V h).le_domain j _ hy⟩ : (H.d j (c.next j)).domain) =
        ⟨v, (G.V h).le_domain j _ hv⟩ - p := Subtype.ext (by simp [hp1])
    rw [e, LinearPMap.map_sub, hp2, sub_zero]
  -- the discrete cycle part is `P_Z (v - z)`, since `z ⊥ 𝔷ʲ ⊇ Z`
  have hzZ : Z.starProjection (z : W j) = 0 :=
    (Z.starProjection_apply_eq_zero_iff).2
      (Submodule.orthogonal_le ((G.V h).cyclesW_le_cycles j) hz)
  have hpn : ‖Z.starProjection v‖ ≤ ‖(z : W j) - v‖ := by
    calc ‖Z.starProjection v‖ = ‖Z.starProjection (v - z)‖ := by rw [map_sub, hzZ, sub_zero]
      _ ≤ ‖v - z‖ := Z.norm_starProjection_apply_le _
      _ = _ := norm_sub_rev _ _
  refine ⟨_, hy, fun q hq =>
    Submodule.inner_right_of_mem_orthogonal hq (Z.sub_starProjection_mem_orthogonal v), ?_, ?_⟩
  · calc ‖(z : W j) - (v - Z.starProjection v)‖ ≤ ‖(z : W j) - v‖ + ‖Z.starProjection v‖ := by
          rw [sub_sub_eq_add_sub, add_sub_right_comm]; exact norm_add_le _ _
      _ < ε := by linarith
  · rw [hdy]; linarith

theorem le_of_eventually_orthogonal_cyclesW [G.l.NeBot] {j k : ι} (hjk : c.Rel j k)
    (ha : G.Approximates j) {φ : W j × W k → ℝ} (hφ : Continuous φ)
    (hC : ∀ᶠ h in G.l, ∀ {y : W j} (hy : y ∈ (G.V h).V j),
      (∀ q ∈ (G.V h).cyclesW j, ⟪q, y⟫_𝕜 = 0) → φ (y, H.d j k ⟨y, (G.V h).le_domain j k hy⟩) ≤ 0)
    {z : (H.d j k).domain} (hz : (z : W j) ∈ (H.cycles j)ᗮ) : φ ((z : W j), H.d j k z) ≤ 0 := by
  by_contra hneg
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
    (hφ.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (not_le.1 hneg)))
  obtain ⟨h, hCh, y, hy, hyo, h1, h2⟩ :=
    (hC.and (eventually_exists_orthogonal_cyclesW hjk ha hz hε)).exists
  have hmem : (y, H.d j k ⟨y, (G.V h).le_domain j k hy⟩) ∈ Metric.ball ((z : W j), H.d j k z) ε := by
    rw [Metric.mem_ball, Prod.dist_eq, dist_comm, dist_eq_norm, dist_comm, dist_eq_norm]
    exact max_lt h1 h2
  exact (not_le.2 (hball hmem)) (hCh hy hyo)

/-- **A uniform discrete Poincaré inequality forces closed range**: if `Vₕ` approximates in degree
`j` along a nontrivial filter and eventually `‖x‖ ≤ C ‖d x‖` on `Vₕʲ ⊥ 𝔷ₕʲ`, `𝔅ᵏ` is closed. -/
theorem closedRangeAt_of_discretePoincare [G.l.NeBot] {j k : ι} (hjk : c.Rel j k)
    (ha : G.Approximates j) {C : ℝ}
    (hC : ∀ᶠ h in G.l, ∀ {x : W j} (hx : x ∈ (G.V h).V j),
      (∀ y ∈ (G.V h).cyclesW j, ⟪y, x⟫_𝕜 = 0) →
      ‖x‖ ≤ C * ‖H.d j k ⟨x, (G.V h).le_domain j k hx⟩‖) :
    H.ClosedRangeAt k :=
  (H.closedRangeAt_iff_poincare_of_rel hjk).2 ⟨C, fun z hz => sub_nonpos.1
    (le_of_eventually_orthogonal_cyclesW hjk ha (φ := fun p => ‖p.1‖ - C * ‖p.2‖)
      (by fun_prop) (hC.mono fun _ hCh _ hy hyo => sub_nonpos.2 (hCh hy hyo)) hz)⟩

end SubcomplexFamily

/-! ### Conforming families -/

namespace ConformingFamily

variable {κ : Type*} (F : ConformingFamily H κ)

theorem isGraphBounded (h : κ) (i j : ι) : (F.π h).IsGraphBounded i j F.projBound :=
  (F.π h).isGraphBounded_of_norm_le (F.norm_π_le h i) (F.norm_π_le h j)

theorem infDist_domainSub_le (h : κ) {i : ι} (σ : H.domainSpace i) :
    infDist σ ((F.V h).domainSub i) ≤ (1 + F.projBound) *
      (infDist (H.domainIncl i σ) ((F.V h).V i : Set (W i)) +
        infDist (H.d i (c.next i) (H.domainCoord i _ σ)) ((F.V h).V (c.next i) : Set (W _))) := by
  have hC := zero_le_one.trans F.one_le_projBound
  refine ((F.V h).infDist_domainSub_le_of_next σ ((F.π h).mem i (H.domainIncl i σ))).trans ?_
  have e : H.d i (c.next i) ⟨(F.π h).π i (H.domainIncl i σ),
      (F.V h).le_domain i _ ((F.π h).mem i _)⟩ =
      (F.π h).π (c.next i) (H.d i (c.next i) (H.domainCoord i _ σ)) :=
    (F.π h).comm i _ (H.domainCoord i _ σ)
  rw [e, mul_add]
  exact add_le_add ((F.π h).norm_sub_π_le_infDist hC (F.norm_π_le h i) _)
    ((F.π h).norm_sub_π_le_infDist hC (F.norm_π_le h _) _)

theorem tendsto_infDist_domainSub {i : ι} (σ : H.domainSpace i) :
    Tendsto (fun h => infDist σ ((F.V h).domainSub i)) F.l (𝓝 0) := by
  have h0 : Tendsto (fun h => (1 + F.projBound) *
      (infDist (H.domainIncl i σ) ((F.V h).V i : Set (W i)) +
        infDist (H.d i (c.next i) (H.domainCoord i _ σ))
          ((F.V h).V (c.next i) : Set (W _)))) F.l (𝓝 0) := by
    simpa using ((F.approx i _).add (F.approx _ _)).const_mul (1 + F.projBound)
  exact squeeze_zero (fun _ => infDist_nonneg) (fun h => F.infDist_domainSub_le h σ) h0

theorem isGraphBounded_toSubcomplexFamily (i : ι) : F.toSubcomplexFamily.IsGraphBounded i :=
  ⟨F.projBound, fun h => F.isGraphBounded h i _⟩

theorem approximates_toSubcomplexFamily (i : ι) : F.toSubcomplexFamily.Approximates i :=
  fun σ => F.tendsto_infDist_domainSub σ

theorem hasUniformProj [∀ j, FiniteDimensional 𝕜 (H.harmonic j)] :
    Subcomplex.HasUniformProj F.l F.V :=
  ⟨F.projBound, F.π, F.one_le_projBound, F.norm_π_le, F.isGraphBounded,
    fun _ => F.tendsto_harmonicGap⟩

theorem quasiOptimal {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) (hj : H.ClosedRangeAt j)
    (hk : H.ClosedRangeAt k) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j},
    H.IsMixedSolution i j k f σ u p → ∀ h : κ,
    (F.V h).mixedError hij hjk f σ u p ≤
      K * (infDist σ ((F.V h).domainSub i) + infDist u ((F.V h).domainSub j) +
        infDist (p : W j) ((F.V h).harmonicW j) +
        (F.π h).harmonicGap j *
          infDist (H.boundaryPart j (H.domainIncl j u)) ((F.V h).domainSub j)) := by
  have hC := F.one_le_projBound
  obtain ⟨cP, -, hPi, hPj⟩ := H.exists_poincare_pair hij hjk hj hk
  exact ⟨_, by have := zero_le_one.trans hC; positivity, fun hs h =>
    (F.π h).norm_sub_le_infDist_harmonicGap hij hjk hC hPi hPj (F.isGraphBounded h i j)
      (F.isGraphBounded h j k) hs⟩

/-! ### The static FEEC theorem -/

/-- The conclusions of the static FEEC theorem for a conforming family at the degree `j`. -/
structure StaticVerdict (j : ι) : Prop where
  /-- the uniform discrete Poincaré inequality on `Vₕʲ ⊥ 𝔷ₕʲ` -/
  poincare {k : ι} (hjk : c.Rel j k) : ∃ C : ℝ, ∀ (h : κ) {x : W j} (hx : x ∈ (F.V h).V j),
    (∀ y ∈ (F.V h).cyclesW j, ⟪y, x⟫_𝕜 = 0) → ‖x‖ ≤ C * ‖H.d j k ⟨x, (F.V h).le_domain j k hx⟩‖
  /-- the uniform well-posedness of the discrete mixed problem -/
  wellPosed {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) : ∃ C : ℝ, ∀ (h : κ) (f : (F.V h).V j),
    (∃! x, (F.V h).toHilbertComplex.mixedForm i j k x = (F.V h).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (F.V h).toHilbertComplex.MixedSpace i j,
      (F.V h).toHilbertComplex.mixedForm i j k x = (F.V h).toHilbertComplex.mixedRHS i j f →
        ‖x‖ ≤ C * ‖f‖
  /-- the harmonic gap tends to `0` -/
  harmonicGap : Tendsto (fun h => (F.π h).harmonicGap j) F.l (𝓝 0)
  /-- `πₕ` eventually induces isomorphisms `Hʲ(H) ≅ Hʲ(Vₕ)` -/
  cohomology : ∀ᶠ h in F.l, Function.Bijective ((F.π h).cohomologyMap j)
  /-- quasi-optimality of the mixed method -/
  quasiOptimal {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j},
    H.IsMixedSolution i j k f σ u p → ∀ h : κ,
    (F.V h).mixedError hij hjk f σ u p ≤
      K * (infDist σ ((F.V h).domainSub i) + infDist u ((F.V h).domainSub j) +
        infDist (p : W j) ((F.V h).harmonicW j) +
        (F.π h).harmonicGap j * infDist (H.boundaryPart j (H.domainIncl j u)) ((F.V h).domainSub j))
  /-- the discrete solutions converge -/
  converges {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {f : W j} {σ : H.domainSpace i}
    {u : H.domainSpace j} {p : H.harmonic j} (hs : H.IsMixedSolution i j k f σ u p) :
    Tendsto (fun h => (F.V h).mixedError hij hjk f σ u p) F.l (𝓝 0)
  /-- the uniform discrete inf-sup condition of `d` on `𝔅ₕᵏ` -/
  infSup {k : ι} (hjk : c.Rel j k) : ∃ β : ℝ, 0 < β ∧ ∀ (h : κ), ∀ q ∈ (F.V h).boundariesW k,
    β * ‖q‖ ≤ ‖((H.constraintForm j k).flip q).comp ((F.V h).domainSub j).subtypeL‖

/-! ### Rates from Jackson estimates -/

variable {F}

/-- A Jackson estimate of `F` from best approximation in `W`. -/
def _root_.Feec.HilbertComplex.SubcomplexFamily.Jackson.ofInfDist (F : ConformingFamily H κ) {ρ : Type*} (meshSize : κ → ℝ)
    (meshSize_nonneg : ∀ h, 0 ≤ meshSize h) (tendsto_meshSize : Tendsto meshSize F.l (𝓝 0))
    (Reg : ρ → ∀ i, ℝ → W i → Prop) (ord : ρ → ℝ) (B : ρ → ι → ℝ) (B_nonneg : ∀ s i, 0 ≤ B s i)
    (happ : ∀ s h i {L : ℝ} (x : W i), 0 ≤ L → Reg s i L x →
      infDist x ((F.V h).V i : Set (W i)) ≤ B s i * (L * meshSize h ^ ord s) ∧
      ∀ j, c.Rel i j → ∀ hx : x ∈ (H.d i j).domain,
        infDist (H.d i j ⟨x, hx⟩) ((F.V h).V j : Set (W j)) ≤ B s i * (L * meshSize h ^ ord s)) :
    F.Jackson ρ where
  meshSize := meshSize
  meshSize_nonneg := meshSize_nonneg
  tendsto_meshSize := tendsto_meshSize
  Reg := Reg
  ord := ord
  B s i := (1 + F.projBound) * B s i
  B_nonneg s i := mul_nonneg (by linarith [F.one_le_projBound]) (B_nonneg s i)
  jackson s h i L x hL hx := by
    have hC : 0 ≤ F.projBound := zero_le_one.trans F.one_le_projBound
    have hC1 : 0 ≤ 1 + F.projBound := by linarith
    have hε : 0 ≤ (1 + F.projBound) * B s i * (L * meshSize h ^ ord s) :=
      mul_nonneg (mul_nonneg hC1 (B_nonneg s i))
        (mul_nonneg hL (Real.rpow_nonneg (meshSize_nonneg h) _))
    obtain ⟨h0, h1⟩ := happ s h i x hL hx
    refine ⟨(F.π h).π i x, (F.π h).mem i x, ?_, fun j hxj => ?_⟩
    · rw [mul_assoc]
      exact ((F.π h).norm_sub_π_le_infDist hC (F.norm_π_le h i) x).trans
        (mul_le_mul_of_nonneg_left h0 hC1)
    by_cases hij : c.Rel i j
    · have e : H.d i j ⟨x - (F.π h).π i x,
          Submodule.sub_mem _ hxj ((F.V h).le_domain i j ((F.π h).mem i x))⟩ =
          H.d i j ⟨x, hxj⟩ - (F.π h).π j (H.d i j ⟨x, hxj⟩) := by
        rw [← (F.π h).comm i j ⟨x, hxj⟩, ← LinearPMap.map_sub]; rfl
      rw [e, mul_assoc]
      exact ((F.π h).norm_sub_π_le_infDist hC (F.norm_π_le h j) _).trans
        (mul_le_mul_of_nonneg_left (h1 j hij hxj) hC1)
    · rw [H.apply_eq_zero_of_not_rel hij, norm_zero]
      exact hε

/-- **The rate of the static FEEC theorem**: for `σ`, `u`, `P_𝔅 u`, `p` `s`-regular with bound
`L`, the error of the mixed method is at most `K L hₕ^{ord s}`. [AFW2010], Thm 3.9 -/
theorem StaticVerdict.rate {j : ι} (V : F.StaticVerdict j) {ρ : Type*} (J : F.Jackson ρ) (s : ρ)
    {i k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) :
    ∃ K : ℝ, ∀ {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j},
    H.IsMixedSolution i j k f σ u p → ∀ {L : ℝ}, 0 ≤ L →
    J.Reg s i L (H.domainIncl i σ) → J.Reg s j L (H.domainIncl j u) →
    J.Reg s j L (H.domainIncl j (H.boundaryPart j (H.domainIncl j u))) →
    J.Reg s j L (p : W j) → ∀ h : κ,
    (F.V h).mixedError hij hjk f σ u p ≤ K * L * J.meshSize h ^ J.ord s := by
  obtain ⟨K, hK, hqo⟩ := V.quasiOptimal hij hjk
  exact ⟨K * (2 * (J.B s i + (3 + 2 * F.projBound) * J.B s j)), fun hs L hL hσ hu hb hp h =>
    ((hqo hs h).trans (mul_le_mul_of_nonneg_left
      (J.approx_le s h hij hjk (zero_le_one.trans F.one_le_projBound) (F.isGraphBounded h j k)
        hL hσ hu hb hp) hK)).trans_eq (by ring)⟩

variable (F) in
theorem rate {ρ : Type*} (J : F.Jackson ρ) (s : ρ) {i j k : ι} (hij : c.Rel i j)
    (hjk : c.Rel j k) (hj : H.ClosedRangeAt j) (hk : H.ClosedRangeAt k) :
    ∃ K : ℝ, ∀ {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j},
    H.IsMixedSolution i j k f σ u p → ∀ {L : ℝ}, 0 ≤ L →
    J.Reg s i L (H.domainIncl i σ) → J.Reg s j L (H.domainIncl j u) →
    J.Reg s j L (H.domainIncl j (H.boundaryPart j (H.domainIncl j u))) →
    J.Reg s j L (p : W j) → ∀ h : κ,
    (F.V h).mixedError hij hjk f σ u p ≤ K * L * J.meshSize h ^ J.ord s := by
  obtain ⟨K, hK, hqo⟩ := F.quasiOptimal hij hjk hj hk
  exact ⟨K * (2 * (J.B s i + (3 + 2 * F.projBound) * J.B s j)), fun hs L hL hσ hu hb hp h =>
    ((hqo hs h).trans (mul_le_mul_of_nonneg_left
      (J.approx_le s h hij hjk (zero_le_one.trans F.one_le_projBound) (F.isGraphBounded h j k)
        hL hσ hu hb hp) hK)).trans_eq (by ring)⟩

variable (F)

/-- **The static FEEC theorem** for a conforming family, with closed range and finite-dimensional
`ℌʲ`: `StaticVerdict F j`. [AFW2010], Thms 3.4–3.6, 3.8, 3.9 -/
theorem staticFEEC (hcr : ∀ i, H.ClosedRangeAt i) (j : ι) [FiniteDimensional 𝕜 (H.harmonic j)] :
    F.StaticVerdict j :=
  have V := F.toSubcomplexFamily.staticFEEC j (F.isGraphBounded_toSubcomplexFamily _)
    (F.isGraphBounded_toSubcomplexFamily j) (hcr j) fun k _ => hcr k
  ⟨V.poincare, V.wellPosed, V.harmonicGap (F.approximates_toSubcomplexFamily j),
    V.cohomology (F.approximates_toSubcomplexFamily j), V.quasiOptimal,
    fun hij hjk => V.converges hij hjk (F.approximates_toSubcomplexFamily _)
      (F.approximates_toSubcomplexFamily j), V.infSup⟩

/-! ### Closed range is necessary -/

theorem tendsto_π (i : ι) (w : W i) : Tendsto (fun h => (F.π h).π i w) F.l (𝓝 w) := by
  have hC := zero_le_one.trans F.one_le_projBound
  have h0 := (F.approx i w).const_mul (1 + F.projBound)
  rw [mul_zero] at h0
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun h => ?_) h0)
  rw [norm_sub_rev]
  exact (F.π h).norm_sub_π_le_infDist hC (F.norm_π_le h i) w

theorem closedRangeAt_of_discretePoincare [F.l.NeBot] {j k : ι} (hjk : c.Rel j k) {C : ℝ}
    (hC : ∀ᶠ h in F.l, ∀ {x : W j} (hx : x ∈ (F.V h).V j),
      (∀ y ∈ (F.V h).cyclesW j, ⟪y, x⟫_𝕜 = 0) →
      ‖x‖ ≤ C * ‖H.d j k ⟨x, (F.V h).le_domain j k hx⟩‖) :
    H.ClosedRangeAt k :=
  haveI : F.toSubcomplexFamily.l.NeBot := ‹F.l.NeBot›
  SubcomplexFamily.closedRangeAt_of_discretePoincare hjk (F.approximates_toSubcomplexFamily j) hC

theorem StaticVerdict.closedRangeAt {F : ConformingFamily H κ} [F.l.NeBot] {j : ι}
    (hV : F.StaticVerdict j) {k : ι} (hjk : c.Rel j k) : H.ClosedRangeAt k := by
  obtain ⟨C, hC⟩ := hV.poincare hjk
  exact F.closedRangeAt_of_discretePoincare hjk (Eventually.of_forall hC)

/-! ### The improved `L²` rate -/

/-- **The improved `L²` rate**: `η ≤ a hₕ`, `δ ≤ b hₕ²`, `μ ≤ m hₕ` and best approximation errors
`e hₕ^r`, `e hₕ^{r+1}`, `e hₕ^{r+2}` give `‖u - uₕ‖ = O(e hₕ^{r+2})`. [AFW2010], Thm 3.11 -/
theorem rate_static_L2 {ρ : Type*} (J : F.Jackson ρ) {i j k : ι} (hij : c.Rel i j)
    (hjk : c.Rel j k) (hj : H.ClosedRangeAt j) (hk : H.ClosedRangeAt k) (h : κ) {a b m e : ℝ}
    {r : ℕ} (ha : 0 ≤ a) (hm : 0 ≤ m)
    (hη : (F.π h).improvedEta hij hjk hj hk ≤ a * J.meshSize h)
    (hδ : (F.π h).improvedDelta hij hjk hj hk ≤ b * J.meshSize h ^ 2)
    (hμ : (F.π h).harmonicGap j ≤ m * J.meshSize h) {f : W j} (X : H.ContinuousSolution i j k f)
    (Y : (F.V h).DiscreteSolution i j k f)
    (hE₀ : (F.V h).bestApprox X.dσ + (F.V h).bestApprox X.p ≤ e * J.meshSize h ^ r)
    (hE₁ : (F.V h).bestApprox X.du + (F.V h).bestApprox (X.σ : W i) ≤ e * J.meshSize h ^ (r + 1))
    (hEb : (F.V h).bestApprox ((H.boundaries j).topologicalClosure.starProjection (X.u : W j)) ≤
      e * J.meshSize h ^ (r + 1))
    (hE₂ : (F.V h).bestApprox (X.u : W j) ≤ e * J.meshSize h ^ (r + 2)) :
    ‖(X.u : W j) - Y.u‖ ≤
      4 * (1 + F.projBound) ^ 2 * (1 + a + a ^ 2 + b + m) * e * J.meshSize h ^ (r + 2) := by
  obtain ⟨cP, hcP, hPi, hPj⟩ := H.exists_poincare_pair hij hjk hj hk
  have hC := zero_le_one.trans F.one_le_projBound
  have hmain := (F.π h).norm_sub_u_le_improved hij hjk hj hk hC (zero_le_one.trans hcP) hPi hPj
    (F.norm_π_le h i) (F.norm_π_le h j) (F.norm_π_le h k) X Y
  set t := J.meshSize h
  have ht := J.meshSize_nonneg h
  have hη0 := (F.π h).improvedEta_nonneg hij hjk hj hk
  have hδ0 := (F.π h).improvedDelta_nonneg hij hjk hj hk
  have hμ0 := (F.π h).harmonicGap_nonneg j
  have hE0 := add_nonneg ((F.V h).bestApprox_nonneg X.dσ) ((F.V h).bestApprox_nonneg X.p)
  have hE1 := add_nonneg ((F.V h).bestApprox_nonneg X.du)
    ((F.V h).bestApprox_nonneg (X.σ : W i))
  have hEb0 := (F.V h).bestApprox_nonneg
    ((H.boundaries j).topologicalClosure.starProjection (X.u : W j))
  have hη2 : (F.π h).improvedEta hij hjk hj hk ^ 2 ≤ a ^ 2 * t ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hη0 hη 2
  have k1 := mul_le_mul hη hE₁ hE1 (mul_nonneg ha ht)
  have k2 := mul_le_mul (add_le_add hη2 hδ) hE₀ hE0 (by nlinarith)
  have k3 := mul_le_mul hμ hEb hEb0 (mul_nonneg hm ht)
  have key : e * t ^ (r + 2) + a * t * (e * t ^ (r + 1)) + (a ^ 2 * t ^ 2 + b * t ^ 2) *
      (e * t ^ r) + m * t * (e * t ^ (r + 1)) = (1 + a + a ^ 2 + b + m) * e * t ^ (r + 2) := by
    ring
  calc _ ≤ _ := hmain
    _ ≤ 4 * (1 + F.projBound) ^ 2 * (e * t ^ (r + 2) + a * t * (e * t ^ (r + 1)) +
        (a ^ 2 * t ^ 2 + b * t ^ 2) * (e * t ^ r) + m * t * (e * t ^ (r + 1))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by rw [key]; ring

end ConformingFamily

end Feec.HilbertComplex
