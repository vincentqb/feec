module

public import Feec.Models.Cube.SmoothingEstimates
public import Feec.FiniteElement.PolyInterpolation
public import Feec.FiniteElement.PolyComplex

/-!
# Smoothed-projection estimates for the higher-order families on the cube

For every admissible sequence `S` (`Feec.FiniteElement.PolySeq`: `P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` in
degree `k`) and the level-`(N + 1)` Freudenthal meshes `FEM.mesh n N` of `Q = (0, ½)ⁿ`
(`h_N = 1 / (2 (N + 1))`), the smoothed canonical interpolants `Q_N = Π_h R_N` of the complexes
`FEM.poly n S N ⊆ HΛ(Q)` and `FEM.polyMin n S N ⊆ H̊Λ(Q)` (vanishing boundary DOFs) satisfy the
estimates of [AFW2010], §5.5 and [ChristiansenWinther2008], **for every `γ ∈ (0, γ₀]`**, `γ₀`
depending only on `n` and `S` (`FEM.polySmoothingEstimates_pMax`,
`FEM.polySmoothingEstimatesMin_pMin`): the parameters `pMax γ` (dilation factor `1 - γ h_N`) and
`pMin γ` (factor `1 + γ h_N`) of `Feec.Models.Cube.SmoothingEstimates` give uniformly
`L²`-bounded `Q_N` with `‖v - Q_N v‖ ≤ ½ ‖v‖` on `Vₕ` (`FEM.PolySmoothingEstimates`,
`FEM.PolySmoothingEstimatesMin`). The same "for all small `γ`" form holds for the Whitney family
(`FEM.smoothingEstimates_pMax_forall`, `FEM.smoothingEstimatesMin_pMin_forall` of
`Feec.Models.Cube.SmoothingEstimates`), so that one smoother serves finitely many
families at once (`FEM.exists_common_gamma`).

The geometry of `Feec.Models.Cube.SmoothingEstimates` (Kuhn homotheties `h_N (m + K_σ)`, lattice
separation, faces through nearby points, bounded overlap, boundary layers, the sampling argument
of the minimal family, `IsAdm`) is reused; the Whitney-specific local estimates are replaced by
the polynomial ones of `Feec.FiniteElement.PolyInverseEstimate` and
`Feec.FiniteElement.PolyInterpolation`:

* **Degrees of freedom as integrals of the values** (`PolySeq.dof_eq_integral`): the moment DOF
  `ℓ_{g,i}(ω) = ∫_{T̂_m} F_q^* ω_k ∧ ηᵢ` (`q` the lexicographic parametrization of the face `g`) is
  `∫_{T̂_m} Σₛ ω(F_q ξ)ₛ cₛ(ξ) dξ` with a coefficient vector `c = dofCoeff` of size `O(h_Nᵏ)` on the
  mesh (`Poly.CoeffBound`, from `sum_abs_dofCoeff_le`: `k × k` minors of the edge matrix and the
  test forms), which only sees the trace on `g` (`sum_mul_dofCoeff_eq_of_pullback_eq`). Hence
  `|ℓ_{g,i}(ω)| ≤ D h_Nᵏ sup_T |ω|` (`Poly.abs_dof_le`).
* **Trace determination on every face** (`PolySeq.affinePullback_lexEnum_eq_of_dof_eq`, the
  facet case being `PolySeq.tangentialTraceEq_of_dof_eq`): fields of the global space have the
  same trace on every common face of two simplices (`Poly.pullback_eq_of_mem_globalSpace`).
* **Uniform constants** on the Kuhn simplices: the DOF bound `h_Nᵏ ‖z‖ ≤ B Σ |ℓ(z)|`
  (`Poly.DofBound`) and the inverse estimates `h_N^{n/2} ‖z‖ ≲ ‖z‖_{L²(T)}`,
  `h_N^{n/2} h_N Lip_T(z) ≲ ‖z‖_{L²(T)}` (`Poly.InvBound`).
* **Uniform `L²` bound** (`Poly.exists_norm_smoothedInterp_le`): as for the Whitney forms, through
  the DOF stability, the DOF bound and Jensen's inequality for the mollifier.
* **Closeness on `Vₕ`** (`Poly.sqrt_mul_abs_integrand_le`, `Poly.sqrt_mul_abs_dof_err_le`,
  `Poly.norm_sq_sub_smoothedInterp_le`): at points of a face `g` with barycentric weights `≥ γ`,
  every simplex sampled by the smoother contains `g` (`Poly.subset_vertexSet_of_near_lex`), where
  the traces agree; the error integrand is `O(γ)` there, and the boundary layer of `g` has measure
  `O(γ)`. Samples outside `Q` are controlled by `Poly.SampleOK`, vacuous for the maximal family
  (`Poly.sampleOK_pMax`) and the vanishing of the boundary DOFs for the minimal family
  (`Poly.sampleOK_pMin`). Since the bound `‖v - Q_N v‖² ≲ γ² ‖v‖²` is monotone in `γ`, every
  `γ ≤ γ₀` works (`Poly.exists_gamma₀`).

## Main definitions

* `FEM.poly n S N`, `FEM.polyMin n S N`: the complexes of `S` on the cube.
* `FEM.polySmoothed`, `FEM.polySmoothedMin`: the smoothed interpolants as commuting maps.
* `FEM.PolySmoothingEstimates`, `FEM.PolySmoothingEstimatesMin`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5 (smoothed projections: the estimates for `ε ≈ h`)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §4.5–4.6 (the moment degrees of freedom)
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [H. W. Kuhn, *Some combinatorial lemmas in topology*][Kuhn1960]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter

/-! ### Traces on the faces of a simplex -/

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh

variable {n : ℕ}

namespace PolySeq

variable (S : PolySeq)

/-- **Trace determination on any face**: two fields of `P_{r_k}Λᵏ` (resp. `P_{r_k}⁻Λᵏ`) with the
same degrees of freedom on the subfaces of a face `g` of an `n`-simplex `T` have the same pullback
along the lexicographic parametrization of `g` (the facet case is
`PolySeq.tangentialTraceEq_of_dof_eq`). -/
theorem affinePullback_lexEnum_eq_of_dof_eq {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {g : Finset (Fin n → ℝ)} {k m : ℕ} (hT : g ⊆ vertexSet T) (hc : #g = m + 1)
    {w η : FormField n} (hw : w ∈ S.space n k) (hη : η ∈ S.space n k)
    (hdof : ∀ g' ⊆ g, ∀ i : S.DofIdx g' k, S.dof g' k i ⟨w, S.space_le_contForms n k hw⟩ =
      S.dof g' k i ⟨η, S.space_le_contForms n k hη⟩) :
    affinePullback (simplexMatrix (lexEnum g m)) (lexEnum g m 0) w =
      affinePullback (simplexMatrix (lexEnum g m)) (lexEnum g m 0) η := by
  set p' := lexEnum (vertexSet T) n
  have hp' := isUnit_det_edgeMatrix_lexEnum T
  have hmono := strictMono_lexEnum (card_vertexSet T)
  obtain ⟨eF, heF⟩ := exists_orderEmb_comp_eq_lexEnum hmono hc fun x hx =>
    exists_lexEnum_eq_of_mem_vertexSet T (hT hx)
  have htr := PolyKind.faceTrace_eq (S.kind k) hp' (S.one_le_deg k) (Face.ofEmb eF) hw hη
    fun g'' hg ζ hζ => by
      obtain ⟨hcard, hG⟩ := lexEnum_image_comp hmono g''.emb.strictMono
      have hGF : Finset.univ.image (p' ∘ g''.emb) ⊆ g := fun x hx => by
        obtain ⟨j, -, rfl⟩ := mem_image.1 hx
        have hj := hg (orderEmbOfFin_mem g''.2.1 g''.2.2 j)
        obtain ⟨a, -, ha⟩ := mem_map.1 hj
        change p' (g''.2.1.orderEmbOfFin g''.2.2 j) ∈ g
        rw [← ha]
        change (p' ∘ eF) a ∈ g
        rw [heF]
        exact lexEnum_mem hc a
      have h := S.degMoment_eq_of_dof_eq hcard (fun i => hdof _ hGF i) hζ
      rw [hG, degField_eq_self (PolyKind.isDeg_of_mem_space hw),
        degField_eq_self (PolyKind.isDeg_of_mem_space hη)] at h
      exact h
  rw [Face.emb_ofEmb, faceTrace_apply, faceTrace_apply] at htr
  rw [heF, show lexEnum (vertexSet T) n (eF 0) = lexEnum g m 0 from congrFun heF 0] at htr
  exact htr

/-- The pointwise form of `affinePullback_lexEnum_eq_of_dof_eq`: at every point of the
parametrized face, the pullbacks of the values agree. -/
theorem pullback_eq_of_dof_eq {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {g : Finset (Fin n → ℝ)} {k m : ℕ} (hT : g ⊆ vertexSet T) (hc : #g = m + 1)
    {w η : FormField n} (hw : w ∈ S.space n k) (hη : η ∈ S.space n k)
    (hdof : ∀ g' ⊆ g, ∀ i : S.DofIdx g' k, S.dof g' k i ⟨w, S.space_le_contForms n k hw⟩ =
      S.dof g' k i ⟨η, S.space_le_contForms n k hη⟩) (ξ : Fin m → ℝ) :
    pullback (simplexMatrix (lexEnum g m)) (w (simplexMap (lexEnum g m) ξ)) =
      pullback (simplexMatrix (lexEnum g m)) (η (simplexMap (lexEnum g m) ξ)) :=
  congrFun (S.affinePullback_lexEnum_eq_of_dof_eq hT hc hw hη hdof) ξ

end PolySeq

/-! ### The degrees of freedom as integrals of the values against coefficient fields -/

/-- The coefficient vector of the moment `∫_{T̂_m} F_q^* ω ∧ η` at `ξ ∈ T̂_m`, on degree-`k`
fields: `ω ↦ Σₛ ω(F_q ξ)ₛ cₛ(ξ)`. -/
def dofCoeff {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) (η : FormField m) (k : ℕ) (ξ : Fin m → ℝ) :
    Finset (Fin n) → ℝ := fun s =>
  if #s = k then wedgeForm (wedgeProd (simplexMatrix q) s) (η ξ) univ else 0

theorem wedgeField_affinePullback_degField_eq {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ)
    (η : FormField m) (k : ℕ) (ω : FormField n) (ξ : Fin m → ℝ) :
    wedgeField (affinePullback (simplexMatrix q) (q 0) (degField k ω)) η ξ univ =
      ∑ s, ω (simplexMap q ξ) s * dofCoeff q η k ξ s := by
  simp only [wedgeField, affinePullback_apply, wedgeForm_pullback_apply, degField, dofCoeff]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [simplexMap]

/-- **The moment as an integral of the values**: `∫_{T̂_m} F_q^* ω_k ∧ η = ∫_{T̂_m} Σₛ ω(F_q ξ)ₛ
cₛ(ξ) dξ`. -/
theorem vertexMoment_degField_eq {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ) (η : FormField m)
    (k : ℕ) (ω : FormField n) :
    vertexMoment q η (degField k ω) =
      ∫ ξ in FiniteElement.refSimplex m, ∑ s, ω (simplexMap q ξ) s * dofCoeff q η k ξ s := by
  rw [vertexMoment_eq_integral]
  exact setIntegral_congr_fun (measurableSet_refSimplex m) fun ξ _ =>
    wedgeField_affinePullback_degField_eq q η k ω ξ

/-- **The coefficient vector only sees the trace**: for degree-`k` vectors with the same pullback
along the edge matrix, the pairings with `c(ξ)` agree. -/
theorem sum_mul_dofCoeff_eq_of_pullback_eq {m : ℕ} (q : Fin (m + 1) → Fin n → ℝ)
    (η : FormField m) {k : ℕ} (ξ : Fin m → ℝ) {α β : Finset (Fin n) → ℝ} (hα : IsDeg k α)
    (hβ : IsDeg k β) (h : pullback (simplexMatrix q) α = pullback (simplexMatrix q) β) :
    ∑ s, α s * dofCoeff q η k ξ s = ∑ s, β s * dofCoeff q η k ξ s := by
  have key : ∀ γ : Finset (Fin n) → ℝ, IsDeg k γ →
      ∑ s, γ s * dofCoeff q η k ξ s = wedgeForm (pullback (simplexMatrix q) γ) (η ξ) univ := by
    intro γ hγ
    rw [wedgeForm_pullback_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [dofCoeff]
    split_ifs with hs
    · rfl
    · rw [hγ s hs]; ring
  rw [key α hα, key β hβ, h]

theorem abs_shuffleSgn {d : Type*} [LinearOrder d] (s t : Finset d) :
    |(shuffleSgn s t : ℝ)| = 1 := by
  have h := shuffleSgn_mul_self (R := ℝ) s t
  have h2 : |(shuffleSgn s t : ℝ)| * |(shuffleSgn s t : ℝ)| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith [abs_nonneg (shuffleSgn s t : ℝ)]

/-- `|(α ∧ β)_{univ}| ≤ Σ_a |α_a| ‖β‖`. -/
theorem abs_wedgeForm_univ_le {m : ℕ} (α β : Finset (Fin m) → ℝ) :
    |wedgeForm α β univ| ≤ (∑ a, |α a|) * ‖β‖ := by
  rw [wedgeForm_apply, Finset.powerset_univ, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul, abs_mul, abs_shuffleSgn, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := norm_le_pi_norm β (univ \ a)
  rwa [Real.norm_eq_abs] at this

/-- **Size of the coefficient vector**: if the edge vectors of `q` have entries `≤ a`, then
`Σₛ |cₛ(ξ)| ≤ 2ⁿ 2ᵐ k! aᵏ ‖η(ξ)‖`. -/
theorem sum_abs_dofCoeff_le {m : ℕ} {q : Fin (m + 1) → Fin n → ℝ} {a : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ i l, |simplexMatrix q i l| ≤ a) (η : FormField m) (k : ℕ) (ξ : Fin m → ℝ) :
    ∑ s, |dofCoeff q η k ξ s| ≤ 2 ^ n * (2 ^ m * (k.factorial * a ^ k)) * ‖η ξ‖ := by
  have hminor : ∀ s : Finset (Fin n), #s = k → ∀ t : Finset (Fin m),
      |wedgeProd (simplexMatrix q) s t| ≤ k.factorial * a ^ k := by
    intro s hs t
    by_cases ht : #t = k
    · rw [wedgeProd_apply_eq_det_submatrix (simplexMatrix q) hs ht]
      have := Matrix.det_le (abv := AbsoluteValue.abs) (x := a)
        (A := Matrix.of fun i j : Fin k => simplexMatrix q (s.orderEmbOfFin hs i)
          (t.orderEmbOfFin ht j)) fun i j => ha _ _
      simpa [Fintype.card_fin, nsmul_eq_mul] using this
    · rw [isDeg_wedgeProd (simplexMatrix q) s t (by rw [hs]; exact ht)]
      simp only [abs_zero]
      positivity
  have h1 : ∀ s : Finset (Fin n), |dofCoeff q η k ξ s| ≤ 2 ^ m * (k.factorial * a ^ k) * ‖η ξ‖ := by
    intro s
    simp only [dofCoeff]
    split_ifs with hs
    · refine (abs_wedgeForm_univ_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      calc ∑ t, |wedgeProd (simplexMatrix q) s t| ≤ ∑ _t : Finset (Fin m), k.factorial * a ^ k :=
            Finset.sum_le_sum fun t _ => hminor s hs t
        _ = 2 ^ m * (k.factorial * a ^ k) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
              nsmul_eq_mul]; push_cast; ring
    · rw [abs_zero]; positivity
  calc ∑ s, |dofCoeff q η k ξ s| ≤ ∑ _s : Finset (Fin n), 2 ^ m * (k.factorial * a ^ k) * ‖η ξ‖ :=
        Finset.sum_le_sum fun s _ => h1 s
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
          nsmul_eq_mul]; push_cast; ring

namespace PolySeq

variable (S : PolySeq)

/-- **The degrees of freedom as integrals of the values**: `ℓ_{g,i}(ω) = ∫_{T̂_m} Σₛ ω(F_q ξ)ₛ
cₛ(ξ) dξ`, `q = lexEnum g m`, `m = #g - 1`, `cₛ = dofCoeff q ηᵢ k`. -/
theorem dof_eq_integral (g : Finset (Fin n → ℝ)) (k : ℕ) (i : S.DofIdx g k) (ω : contForms n) :
    S.dof g k i ω = ∫ ξ in FiniteElement.refSimplex (#g - 1),
      ∑ s, (ω : FormField n) (simplexMap (lexEnum g (#g - 1)) ξ) s *
        dofCoeff (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) k ξ s := by
  rw [dof_apply, vertexMoment_degField_eq]

end PolySeq

end Feec.FiniteElement

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre

variable {n : ℕ}

namespace Poly

variable (S : PolySeq)

/-! ### Uniform local estimates on the mesh simplices -/

theorem abs_simplexMatrix_lexEnum_le {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) {m : ℕ}
    (hg : #g = m + 1) (i : Fin n) (l : Fin m) :
    |simplexMatrix (lexEnum g m) i l| ≤ hN N := by
  obtain ⟨m', σ, rfl⟩ := mem_mesh_simplices.1 hT
  have hmem : ∀ a, lexEnum g m a ∈ (cubeSimplex N m' σ).closedInterior := fun a =>
    vertexSet_subset_closedInterior _ (hgT (lexEnum_mem hg a))
  have := norm_sub_le_of_mem_cubeSimplex (hmem l.succ) (hmem 0)
  refine le_trans ?_ this
  have h := norm_le_pi_norm (lexEnum g m l.succ - lexEnum g m 0) i
  rwa [Real.norm_eq_abs, Pi.sub_apply] at h

theorem simplexMap_lexEnum_mem {T : Affine.Simplex ℝ (Fin n → ℝ) n} {g : Finset (Fin n → ℝ)}
    (hgT : g ⊆ vertexSet T) {m : ℕ} (hg : #g = m + 1) {ξ : Fin m → ℝ}
    (hξ : ξ ∈ FiniteElement.refSimplex m) :
    simplexMap (lexEnum g m) ξ ∈ T.closedInterior := by
  rw [← convexHull_vertexSet]
  refine convexHull_mono ?_ (simplexMap_mem_convexHull _ hξ)
  rw [range_lexEnum hg]; exact Finset.coe_subset.2 hgT

/-- A uniform bound of the test forms on the reference simplices. -/
theorem exists_testBound (k : ℕ) : ∃ M, 0 ≤ M ∧ ∀ m ≤ n,
    ∀ (i : Fin (Module.finrank ℝ (S.test k m))), ∀ ξ ∈ FiniteElement.refSimplex m,
      ‖(S.testBasis k m i : FormField m) ξ‖ ≤ M := by
  have hb : ∀ m (i : Fin (Module.finrank ℝ (S.test k m))), ∃ M, 0 ≤ M ∧
      ∀ ξ ∈ FiniteElement.refSimplex m, ‖(S.testBasis k m i : FormField m) ξ‖ ≤ M := by
    intro m i
    obtain ⟨M, hM⟩ := (isCompact_refSimplex m).exists_bound_of_continuousOn
      (S.continuous_testBasis k m i).continuousOn
    exact ⟨max M 0, le_max_right _ _, fun ξ hξ => (hM ξ hξ).trans (le_max_left _ _)⟩
  choose M hM0 hM using hb
  refine ⟨∑ m ∈ Finset.range (n + 1), ∑ i, M m i, Finset.sum_nonneg fun m _ =>
    Finset.sum_nonneg fun i _ => hM0 m i, fun m hm i ξ hξ => (hM m i ξ hξ).trans ?_⟩
  calc M m i ≤ ∑ i, M m i := Finset.single_le_sum (f := M m) (fun i _ => hM0 m i)
        (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun m => ∑ i, M m i)
        (fun m _ => Finset.sum_nonneg fun i _ => hM0 m i) (Finset.mem_range.2 (by omega))

/-- **The coefficient fields of the degrees of freedom are `O(hᵏ)`** on every simplex whose edge
vectors are bounded by `h`, with one constant. -/
theorem exists_coeffBound_of_le (k : ℕ) : ∃ D, 0 ≤ D ∧
    ∀ {T : Affine.Simplex ℝ (Fin n → ℝ) n} {g : Finset (Fin n → ℝ)}, g ⊆ vertexSet T →
      ∀ (i : S.DofIdx g k) {h : ℝ}, 0 ≤ h →
        (∀ j l, |simplexMatrix (lexEnum g (#g - 1)) j l| ≤ h) →
        ∀ ξ ∈ FiniteElement.refSimplex (#g - 1),
          ∑ s, |dofCoeff (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 :
            FormField (#g - 1)) k ξ s| ≤ D * h ^ k := by
  obtain ⟨M, hM0, hM⟩ := exists_testBound S k
  refine ⟨2 ^ n * (2 ^ n * k.factorial) * M, by positivity,
    fun {T g} hgT i h hh hle ξ hξ => ?_⟩
  have hgn : #g - 1 ≤ n := by
    have := Finset.card_le_card hgT
    rw [card_vertexSet] at this; omega
  refine (sum_abs_dofCoeff_le hh hle _ k ξ).trans ?_
  have h2 : (2 : ℝ) ^ (#g - 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hgn
  have hη := hM (#g - 1) hgn i.1 ξ hξ
  have hhk := pow_nonneg hh k
  calc 2 ^ n * (2 ^ (#g - 1) * (k.factorial * h ^ k)) *
        ‖(S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) ξ‖
      ≤ 2 ^ n * (2 ^ n * (k.factorial * h ^ k)) * M := by
        gcongr
    _ = _ := by ring

/-- **Stability of the degrees of freedom in the sup norm**: if the coefficient fields of the
moment `ℓ_{g,i}` of a face `g` of `T` satisfy `Σₛ |cₛ| ≤ K` on the reference simplex, then
`|ℓ_{g,i}(ω)| ≤ K sup_T |ω|` for every continuous form `ω`. -/
theorem abs_dof_le_of_coeff_le {k : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (i : S.DofIdx g k) (ω : contForms n)
    {K B : ℝ} (hK : ∀ ξ ∈ FiniteElement.refSimplex (#g - 1),
      ∑ s, |dofCoeff (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) k
        ξ s| ≤ K) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ T.closedInterior, ∀ s, |(ω : FormField n) x s| ≤ B) :
    |S.dof g k i ω| ≤ K * B := by
  have hne := i.2
  have hg : #g = (#g - 1) + 1 := (Nat.succ_pred_eq_of_pos (card_pos.2 hne)).symm
  set q := lexEnum g (#g - 1)
  set η := (S.testBasis k (#g - 1) i.1 : FormField (#g - 1))
  rw [S.dof_eq_integral]
  have h0 : (0 : Fin (#g - 1) → ℝ) ∈ FiniteElement.refSimplex (#g - 1) := fun a => by
    refine Fin.cases ?_ (fun l => ?_) a
    · simp
    · simp [refBary]
  have hK0 : 0 ≤ K := (Finset.sum_nonneg fun s _ => abs_nonneg _).trans (hK 0 h0)
  have hpt : ∀ ξ ∈ FiniteElement.refSimplex (#g - 1),
      ‖∑ s, (ω : FormField n) (simplexMap q ξ) s * dofCoeff q η k ξ s‖ ≤ K * B := by
    intro ξ hξ
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s, |(ω : FormField n) (simplexMap q ξ) s * dofCoeff q η k ξ s|
        ≤ ∑ s, B * |dofCoeff q η k ξ s| := Finset.sum_le_sum fun s _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hB _ (simplexMap_lexEnum_mem hgT hg hξ) s)
            (abs_nonneg _)
      _ = B * ∑ s, |dofCoeff q η k ξ s| := by rw [Finset.mul_sum]
      _ ≤ B * K := mul_le_mul_of_nonneg_left (hK ξ hξ) hB0
      _ = K * B := by ring
  rw [← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le_const (volume_refSimplex_lt_top _) hpt).trans ?_
  calc K * B * volume.real (FiniteElement.refSimplex (#g - 1)) ≤ K * B * 1 :=
        mul_le_mul_of_nonneg_left (volume_real_refSimplex_le_one _) (mul_nonneg hK0 hB0)
    _ = _ := mul_one _

/-- **The coefficient fields of the degrees of freedom are `O(h_Nᵏ)`** on the mesh simplices,
with one constant. -/
def CoeffBound (n k : ℕ) (D : ℝ) : Prop :=
  ∀ (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}, T ∈ (mesh n N).simplices →
    ∀ {g : Finset (Fin n → ℝ)}, g ⊆ vertexSet T → ∀ (i : S.DofIdx g k),
      ∀ ξ ∈ FiniteElement.refSimplex (#g - 1),
        ∑ s, |dofCoeff (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) k
          ξ s| ≤ D * hN N ^ k

theorem exists_coeffBound (k : ℕ) : ∃ D, 0 ≤ D ∧ CoeffBound S n k D := by
  obtain ⟨D, hD0, hD⟩ := exists_coeffBound_of_le S k
  exact ⟨D, hD0, fun N T hT g hgT i => hD hgT i (hN_pos N).le
    (abs_simplexMatrix_lexEnum_le hT hgT (Nat.succ_pred_eq_of_pos (card_pos.2 i.2)).symm)⟩

/-- **Stability of the degrees of freedom in the sup norm**: `|ℓ_{g,i}(ω)| ≤ D h_Nᵏ sup_T |ω|`
for a face `g` of a mesh simplex `T` and a continuous form `ω`. -/
theorem abs_dof_le {k : ℕ} {D : ℝ} (hD : CoeffBound S n k D) {N : ℕ}
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (i : S.DofIdx g k) (ω : contForms n)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ T.closedInterior, ∀ s, |(ω : FormField n) x s| ≤ B) :
    |S.dof g k i ω| ≤ D * hN N ^ k * B :=
  abs_dof_le_of_coeff_le S hgT i ω (hD N hT hgT i) hB0 hB

/-- **The local DOF estimate on the mesh simplices**, with one constant:
`h_Nᵏ ‖z(x)‖ ≤ B Σ_{g ⊆ T, i} |ℓ_{g,i}(z)|` for `z ∈ P_{r_k}Λᵏ` (resp. `P_{r_k}⁻Λᵏ`). -/
def DofBound (n k : ℕ) (B : ℝ) : Prop :=
  ∀ (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}, T ∈ (mesh n N).simplices →
    ∀ {z : FormField n} (hz : z ∈ S.space n k), ∀ x ∈ T.closedInterior,
      hN N ^ k * ‖z x‖ ≤ B * ∑ p : Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k,
        |S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ⟨z, S.space_le_contForms n k hz⟩|

theorem exists_dofBound (k : ℕ) : ∃ B, 0 ≤ B ∧ DofBound S n k B := by
  obtain ⟨B, hB0, hB⟩ := S.exists_local_dof_bound_uniform (n := n) kuhnSimplex k
  refine ⟨B, hB0, fun N T hT z hz x hx => ?_⟩
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  rw [cubeSimplex_eq] at hx ⊢
  exact hB σ (hN_pos N) _ hz x hx

/-- **The local inverse estimates on the mesh simplices**, with one constant:
`h_N^{n/2} ‖z(x)‖ ≤ A ‖z‖_{L²(T)}` and `h_N^{n/2} h_N ‖z(x) - z(x')‖ ≤ A ‖x - x'‖ ‖z‖_{L²(T)}`. -/
def InvBound (n k : ℕ) (A : ℝ) : Prop :=
  ∀ (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}, T ∈ (mesh n N).simplices →
    ∀ z ∈ S.space n k,
      (∀ x ∈ T.closedInterior, √(hN N) ^ n * ‖z x‖ ≤ A * √(formL2Sq T.closedInterior z)) ∧
      (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior,
        √(hN N) ^ n * hN N * ‖z x - z x'‖ ≤ A * ‖x - x'‖ * √(formL2Sq T.closedInterior z))

theorem exists_invBound (k : ℕ) : ∃ A, 0 ≤ A ∧ InvBound S n k A := by
  choose A hA0 hA using fun σ : Equiv.Perm (Fin n) =>
    exists_local_inverse_bound_of_le_polySpace (S.space_le_polySpace k)
      (fun h t _ hu => S.affinePullback_mem_space_scalarMat k h t hu) (kuhnSimplex σ)
  have hle : ∀ σ, A σ ≤ ∑ σ, A σ := fun σ =>
    Finset.single_le_sum (fun σ _ => hA0 σ) (Finset.mem_univ σ)
  refine ⟨∑ σ, A σ, Finset.sum_nonneg fun σ _ => hA0 σ, fun N T hT z hz => ?_⟩
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  rw [cubeSimplex_eq]
  obtain ⟨h1, h2⟩ := hA σ (hN_pos N) _ z hz
  exact ⟨fun x hx => (h1 x hx).trans (mul_le_mul_of_nonneg_right (hle σ) (Real.sqrt_nonneg _)),
    fun x hx x' hx' => (h2 x hx x' hx').trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hle σ) (norm_nonneg _)) (Real.sqrt_nonneg _))⟩

/-! ### The uniform `L²` bound -/

theorem card_dofs_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    (Fintype.card (Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k) : ℝ) =
      Module.finrank ℝ (S.space n k) := by
  exact_mod_cast S.card_sigma_dofIdx T k

/-- A bound on all the degrees of freedom bounds the local field:
`|z(x)ₛ| ≤ B dim(P) D'` if `h_Nᵏ`-scaled DOFs are `≤ h_Nᵏ D'`. -/
theorem abs_le_of_abs_dof_le {k : ℕ} {B : ℝ} (hB : DofBound S n k B) (hB0 : 0 ≤ B) {N : ℕ}
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices) {z : FormField n}
    (hz : z ∈ S.space n k) {D' : ℝ}
    (hD : ∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ hN N ^ k * D')
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) (s : Finset (Fin n)) :
    |z x s| ≤ B * Module.finrank ℝ (S.space n k) * D' := by
  have hhk : 0 < hN N ^ k := pow_pos (hN_pos N) k
  have h1 := hB N hT hz x hx
  have h2 : ∑ p : Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k,
      |S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ⟨z, S.space_le_contForms n k hz⟩| ≤
      Module.finrank ℝ (S.space n k) * (hN N ^ k * D') := by
    calc _ ≤ ∑ _p : Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k,
          hN N ^ k * D' := Finset.sum_le_sum fun p _ => hD _ (Finset.mem_powerset.1 p.1.2) p.2
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_dofs_eq]
  have h3 : |z x s| ≤ ‖z x‖ := by
    have := norm_le_pi_norm (z x) s; rwa [Real.norm_eq_abs] at this
  refine le_of_mul_le_mul_left ?_ hhk
  calc hN N ^ k * |z x s| ≤ hN N ^ k * ‖z x‖ := mul_le_mul_of_nonneg_left h3 hhk.le
    _ ≤ B * (Module.finrank ℝ (S.space n k) * (hN N ^ k * D')) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hB0)
    _ = hN N ^ k * (B * Module.finrank ℝ (S.space n k) * D') := by ring

/-- **The local `L²` bound of the canonical interpolant** of a continuous form bounded by `A` on a
mesh simplex: `‖Π_h w‖²_{L²(T)} ≤ 2ⁿ h_Nⁿ (B dim(P) D A)²`. -/
theorem sum_integral_sq_globalInterp_le {N k : ℕ} {B D : ℝ} (hB : DofBound S n k B)
    (hB0 : 0 ≤ B) (hD : CoeffBound S n k D) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {w : contForms n} {A : ℝ} (hA0 : 0 ≤ A)
    (hw : ∀ y ∈ T.closedInterior, ∀ s, |(w : FormField n) y s| ≤ A) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((((polyElement n S).globalInterp (mesh n N) k w :
        (polyElement n S).Piecewise (mesh n N) k) ⟨T, hT⟩ : (polyElement n S).space T k) :
          FormField n) y s.1) ^ 2 ≤
      2 ^ n * hN N ^ n * (B * Module.finrank ℝ (S.space n k) * (D * A)) ^ 2 := by
  set h := hN N
  have hh : 0 < h := hN_pos N
  set z : FormField n := ((((polyElement n S).globalInterp (mesh n N) k w :
    (polyElement n S).Piecewise (mesh n N) k) ⟨T, hT⟩ : (polyElement n S).space T k) :
      FormField n)
  have hz : z ∈ S.space n k := (((polyElement n S).globalInterp (mesh n N) k w :
      (polyElement n S).Piecewise (mesh n N) k) ⟨T, hT⟩).2
  have hdof : ∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ h ^ k * (D * A) := by
    intro g hgT i
    have e : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ = S.dof g k i w :=
      (polyElement n S).localDof_globalInterp (mesh n N) k w ⟨T, hT⟩ g hgT i
    rw [e]
    refine (abs_dof_le S hD hT hgT i _ hA0 hw).trans (le_of_eq ?_)
    ring
  have hzb : ∀ y ∈ T.closedInterior, ∀ s,
      |z y s| ≤ B * Module.finrank ℝ (S.space n k) * (D * A) :=
    fun y hy s => abs_le_of_abs_dof_le S hB hB0 hT hz hdof hy s
  exact (sum_integral_sq_le_of_abs_le hT (PolyKind.contDiff_of_mem_space hz).continuous
    hzb).trans (le_of_eq (by ring))

/-- **The local `L²` bound of `Q_N = Π_h R`** for the higher-order families:
`‖Q_N x‖²_{L²(T)} ≲ m_T(x)`. -/
theorem sum_integral_sq_interp_le {N k : ℕ} {B D : ℝ} (hB : DofBound S n k B) (hB0 : 0 ≤ B)
    (hD : CoeffBound S n k D) {γ : ℝ}
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p) (hγ1 : γ ≤ 1)
    (x : L2F ℝ (mesh n N).domain (formIdx n k)) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((((polyElement n S).globalInterp (mesh n N) k
        (Submodule.inclusion c1Forms_le_contForms
          (smoothForm p (isOpen_mesh_domain n N).measurableSet k x)) :
          (polyElement n S).Piecewise (mesh n N) k) ⟨T, hT⟩ : (polyElement n S).space T k) :
          FormField n) y s.1) ^ 2 ≤
      2 ^ n * (B * Module.finrank ℝ (S.space n k) * D * 2 ^ k) ^ 2 * (32 / γ) ^ n *
        locMass x T := by
  have hh := hN_pos N
  have hγ0 : 0 < γ := hp.gamma_pos
  have hL := locMass_nonneg x T
  refine (sum_integral_sq_globalInterp_le S hB hB0 hD hT (by positivity)
    (hp.abs_smoothForm_le_locMass hγ1 x hT)).trans (le_of_eq ?_)
  have hr2 : √((32 / (γ * hN N)) ^ n * locMass x T) ^ 2 = (32 / (γ * hN N)) ^ n * locMass x T :=
    Real.sq_sqrt (by positivity)
  rw [show (32 / γ) ^ n = hN N ^ n * (32 / (γ * hN N)) ^ n by rw [← mul_pow]; congr 1; field_simp]
  linear_combination (2 ^ n * hN N ^ n * (B * Module.finrank ℝ (S.space n k) * D * 2 ^ k) ^ 2) *
    hr2

/-- **The uniform `L²` bound of the smoothed interpolants** `Q_N = Π_h R_N` of the higher-order
families, for any admissible parameters (`IsAdm`, either family): `‖Q_N x‖ ≤ C ‖x‖` for all `N`,
all degrees and all `x`, with `C` depending only on `n`, `S` and `γ`. -/
theorem exists_norm_smoothedInterp_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ (N k : ℕ) (p : SmoothingParam (Fin n → ℝ)), IsAdm γ N p →
      ∀ x : L2F ℝ (mesh n N).domain (formIdx n k),
        ‖(polyElement n S).smoothedInterp (mesh n N) p
          (isOpen_mesh_domain n N).measurableSet k x‖ ≤ C * ‖x‖ := by
  choose B hB0 hB using fun k : ℕ => exists_dofBound (n := n) S k
  choose D hD0 hD using fun k : ℕ => exists_coeffBound (n := n) S k
  have hK : ∀ k, 0 ≤ 2 ^ n * (B k * Module.finrank ℝ (S.space n k) * D k * 2 ^ k) ^ 2 *
      (32 / γ) ^ n * ((6 ^ n * n.factorial : ℕ) : ℝ) := fun k => by
    have := hB0 k; have := hD0 k; positivity
  refine ⟨_, Real.sqrt_nonneg _, fun N k p hp x => norm_le_sqrt_sum_of_sq_le hK fun _ => ?_⟩
  rw [(polyElement n S).smoothedInterp_natCast, mul_assoc]
  exact norm_sq_glue_le_locMass _ x _ (by have := hB0 k; have := hD0 k; positivity)
    fun T hT => sum_integral_sq_interp_le S (hB k) (hB0 k) (hD k) hp hγ1 x hT

/-! ### The closeness estimate on `Vₕ` -/

/-- **Faces through nearby points** (`subset_vertexSet_of_near`, for the lexicographic
parametrization of the face). -/
theorem subset_vertexSet_of_near_lex {N : ℕ} {T T' : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) (hT' : T' ∈ (mesh n N).simplices) {m : ℕ}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (hg : #g = m + 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) {μ : Fin (m + 1) → ℝ} (hμ : ∀ a, θ ≤ μ a)
    (hμ1 : ∑ a, μ a = 1) {t : Fin n → ℝ} (ht : t ∈ T'.closedInterior)
    (hxt : ‖∑ a, μ a • lexEnum g m a - t‖ < θ * hN N / 2) : g ⊆ vertexSet T' := by
  classical
  set q := lexEnum g m
  have hq := lexEnum_injective hg
  have hqT : ∀ a, q a ∈ vertexSet T := fun a => hgT (lexEnum_mem hg a)
  obtain ⟨m₀, σ, rfl⟩ := mem_mesh_simplices.1 hT
  obtain ⟨m', σ', rfl⟩ := mem_mesh_simplices.1 hT'
  have hj : ∀ a, ∃ j, q a = hN N • (latticePoint (finLattice m₀) + kuhnVertex σ j) := fun a => by
    obtain ⟨j, hj⟩ := mem_vertexSet.1 (hqT a)
    exact ⟨j, by rw [← hj, cubeSimplex_points]⟩
  choose j hj using hj
  set x := ∑ a, μ a • q a
  have hxs : (hN N)⁻¹ • x = latticePoint (finLattice m₀) + ∑ a, μ a • kuhnVertex σ (j a) := by
    have hh := hN_ne_zero N
    simp only [x, hj, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib,
      ← Finset.sum_smul]
    have e1 : (hN N)⁻¹ * ∑ i, μ i * hN N = 1 := by
      rw [← Finset.sum_mul, hμ1]; field_simp
    have e2 : ∀ a, (hN N)⁻¹ * (μ a * hN N) = μ a := fun a => by field_simp
    simp only [e1, e2, one_smul]
  have hsep := isSep_latticePoint_add_sum hθ0.le hθ (finLattice m₀) σ j hμ hμ1
  rw [← hxs] at hsep
  have hx' : x ∈ (cubeSimplex N m' σ').closedInterior := by
    rw [mem_closedInterior_cubeSimplex] at ht ⊢
    refine mem_freudenthalSet_of_isSep hsep ht fun l => ?_
    have h := hN_pos N
    have : ‖(hN N)⁻¹ • x - (hN N)⁻¹ • t‖ < θ / 2 := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 h.le), inv_mul_lt_iff₀ h]
      linarith
    exact lt_of_le_of_lt (by
      have := norm_le_pi_norm ((hN N)⁻¹ • x - (hN N)⁻¹ • t) l
      rwa [Real.norm_eq_abs, Pi.sub_apply] at this) this
  intro v hv
  have : v ∈ Set.range q := by rw [range_lexEnum hg]; exact hv
  obtain ⟨a, rfl⟩ := this
  exact SimplicialMesh.subset_vertexSet_of_mem hT hT' hq hqT
    (fun a => hθ0.trans_le (hμ a)) hμ1 hx' a

/-- **The sampling condition** for the higher-order families: every sample of the smoother outside
`Ω`, near a point of a face `g` with barycentric weights `≥ γ`, forces the degrees of freedom of
the subfaces of `g` to vanish (vacuous for the maximal family; for the minimal family the
vanishing of the boundary DOFs). -/
def SampleOK {N k : ℕ} (γ : ℝ) (p : SmoothingParam (Fin n → ℝ))
    (u : (polyElement n S).Piecewise (mesh n N) k) : Prop :=
  ∀ (T : (mesh n N).simplices) (g : Finset (Fin n → ℝ)),
    g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) → ∀ {m : ℕ}, #g = m + 1 →
    ∀ ξ ∈ FiniteElement.refSimplex m, ξ ∉ nearBdry m γ →
      ∀ t, dist t (p.center + p.factor • (simplexMap (lexEnum g m) ξ - p.center)) <
        p.bump.rOut → t ∉ (mesh n N).domain →
        ∀ g' ⊆ g, ∀ i : S.DofIdx g' k,
          (polyElement n S).localDof T k g' i (u T) = 0

variable {S} in
/-- Global fields have the same pullback along a common face (`pullback_eq_of_dof_eq`). -/
theorem pullback_eq_of_mem_globalSpace {M : SimplicialMesh n} {k : ℕ}
    {u : (polyElement n S).Piecewise M k} (hu : u ∈ (polyElement n S).globalSpace M k)
    (T T' : M.simplices) {g : Finset (Fin n → ℝ)} {m : ℕ}
    (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n)) (hg : #g = m + 1)
    (ξ : Fin m → ℝ) :
    pullback (simplexMatrix (lexEnum g m))
        (((u T : (polyElement n S).space T k) : FormField n) (simplexMap (lexEnum g m) ξ)) =
      pullback (simplexMatrix (lexEnum g m))
        (((u T' : (polyElement n S).space T' k) : FormField n) (simplexMap (lexEnum g m) ξ)) :=
  S.pullback_eq_of_dof_eq hgT hg (u T).2 (u T').2
    (fun g' hg' i => hu T T' g' (hg'.trans hgT) (hg'.trans hgT') i) ξ

variable {γ : ℝ}

open Classical in
/-- **The pointwise estimate of the DOF integrand of `v - Q_N v`** (`v ∈ Vₕ`) for the
higher-order families: at a point `x = F_q(ξ)` of a face `g` of `T` (`q` its lexicographic
parametrization) and for any coefficient vector `c` that only sees the trace on `g`,
`h^{n/2} |Σₛ (v_T - R v)(x)ₛ cₛ| ≤ (Σₛ |cₛ|) A m_T(v)^{1/2} 2^{k+1} · (1 or (k + 1) γ)`,
with the factor `(k + 1) γ` when all barycentric coordinates of `ξ` are `≥ γ`: then every
simplex sampled by the smoother inside `Ω` contains `g`, where the traces of the local fields
agree (`pullback_eq_of_mem_globalSpace`). -/
theorem sqrt_mul_abs_integrand_le {N k : ℕ} {A : ℝ} (hA0 : 0 ≤ A) (hA : InvBound S n k A)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpace (mesh n N) k) (hs : SampleOK S γ p u)
    (T : (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) {m : ℕ}
    (hg : #g = m + 1) {ξ : Fin m → ℝ} (hξ : ξ ∈ FiniteElement.refSimplex m)
    (c : Finset (Fin n) → ℝ)
    (hc : ∀ α β : Finset (Fin n) → ℝ, IsDeg k α → IsDeg k β →
      pullback (simplexMatrix (lexEnum g m)) α = pullback (simplexMatrix (lexEnum g m)) β →
        ∑ s, α s * c s = ∑ s, β s * c s) :
    √(hN N) ^ n * |∑ s, (((u T : (polyElement n S).space T k) : FormField n)
        (simplexMap (lexEnum g m) ξ) s -
      (smoothForm p (isOpen_mesh_domain n N).measurableSet k
        ((polyElement n S).glue (mesh n N) k u) : FormField n)
        (simplexMap (lexEnum g m) ξ) s) * c s| ≤
      (∑ s, |c s|) * A *
        √(locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)) *
        2 ^ (k + 1) * (if ξ ∈ nearBdry m γ then 1 else (k + 1) * γ) := by
  have hγ := hp.gamma_pos
  have hγ1 : γ ≤ 1 := by linarith
  set h := hN N
  have hh : 0 < h := hN_pos N
  have hh2 : h ≤ 1 / 2 := hN_le N
  set hΩ := (isOpen_mesh_domain n N).measurableSet
  set q := lexEnum g m
  set x := simplexMap q ξ
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  set L := locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
    simplexMap_lexEnum_mem hgT hg hξ
  have hxc : x ∈ closure (cubeDomain n) := by
    rw [← mesh_domain n N]; exact (mesh n N).closedInterior_subset_closure T.2 hxT
  -- the local fields near `x` obey the inverse estimates against the local mass of `T`
  have hinv : ∀ T' : (mesh n N).simplices, (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
      Metric.cthickening (2 * h) (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior →
      (∀ y ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
        √h ^ n * |((u T' : (polyElement n S).space T' k) : FormField n) y s| ≤ A * √L) ∧
      ∀ y ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        ∀ y' ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
        √h ^ n * h * |((u T' : (polyElement n S).space T' k) : FormField n) y s -
          ((u T' : (polyElement n S).space T' k) : FormField n) y' s| ≤
          A * ‖y - y'‖ * √L := by
    intro T' hsub
    have hL' := Real.sqrt_le_sqrt (sum_integral_sq_le_locMass (polyElement n S) u T' hsub)
    obtain ⟨h1, h2⟩ := hA N T'.2 _ (u T').2
    refine ⟨fun y hy s => ?_, fun y hy y' hy' s => ?_⟩
    · refine (mul_le_mul_of_nonneg_left ?_ hsq.le).trans ((h1 y hy).trans
        (mul_le_mul_of_nonneg_left hL' hA0))
      have := norm_le_pi_norm (((u T' : (polyElement n S).space T' k) : FormField n) y) s
      rwa [Real.norm_eq_abs] at this
    · refine (mul_le_mul_of_nonneg_left ?_ (by positivity)).trans ((h2 y hy y' hy').trans
        (mul_le_mul_of_nonneg_left hL' (by positivity)))
      have := norm_le_pi_norm (((u T' : (polyElement n S).space T' k) : FormField n) y -
        ((u T' : (polyElement n S).space T' k) : FormField n) y') s
      rwa [Real.norm_eq_abs, Pi.sub_apply] at this
  refine sqrt_mul_abs_sum_sub_smoothForm_le hΩ p _ x (uT x) c (ξ ∈ nearBdry m γ) hsq hA0 hγ.le
    (hp.pow_factor_le hγ1 k) ((hp.abs_one_sub_pow_le hγ1 k).trans
      (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)))
    (fun s => (hinv T (self_subset_cthickening _ (by positivity))).1 x hxT s) ?_ ?_
  · filter_upwards [ae_extField_glue_eq (polyElement n S) u hΩ] with t ht hdist htΩ
    obtain ⟨T', htT', hext⟩ := ht htΩ
    set u' : FormField n := ((u T' : (polyElement n S).space T' k) : FormField n)
    have hu' : u' ∈ S.space n k := (u T').2
    have htT'c : t ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := interior_subset htT'
    obtain ⟨hxt, hT'sub⟩ := hp.norm_sub_lt_and_subset hγ1 T'.2 hxT hxc htT'c hdist
    obtain ⟨hb1, hb2⟩ := hinv T' hT'sub
    refine ⟨u', hext, fun s => hb1 t htT'c s, fun hbad => ?_⟩
    have hμ : ∀ a, γ ≤ refBary ξ a := by
      intro a; by_contra hlt; push Not at hlt; exact hbad ⟨a, hlt⟩
    have hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) :=
      subset_vertexSet_of_near_lex T.2 T'.2 hgT hg hγ hγ2 hμ (sum_refBary ξ) htT'c
        (by rw [← simplexMap_eq_sum q ξ]; exact hxt)
    have hxT' := simplexMap_lexEnum_mem hgT' hg hξ
    refine ⟨hc _ _ (PolyKind.isDeg_of_mem_space huT x) (PolyKind.isDeg_of_mem_space hu' x)
      (pullback_eq_of_mem_globalSpace hu T T' hgT hgT' hg ξ), fun s => hb1 x hxT' s,
      fun s => ?_⟩
    refine le_of_mul_le_mul_right ?_ hh
    calc √h ^ n * |u' x s - u' t s| * h = √h ^ n * h * |u' x s - u' t s| := by ring
      _ ≤ A * ‖x - t‖ * √L := hb2 x hxT' t htT'c s
      _ ≤ A * (γ * h) * √L := by gcongr; linarith [norm_nonneg (x - t)]
      _ = γ * (A * √L) * h := by ring
  · intro hbad t hdist htΩ
    have h0 := hs T g hgT hg ξ hξ hbad t hdist htΩ
    have hpb : pullback (simplexMatrix q) (uT x) =
        pullback (simplexMatrix q) ((0 : FormField n) x) :=
      S.pullback_eq_of_dof_eq hgT hg huT (Submodule.zero_mem _) (fun g' hg' i => by
        rw [show (⟨(0 : FormField n), S.space_le_contForms n k (Submodule.zero_mem _)⟩ :
          contForms n) = 0 from rfl, map_zero]
        exact h0 g' hg' i) ξ
    rw [hc _ _ (PolyKind.isDeg_of_mem_space huT x) (fun s _ => rfl) hpb]
    simp

theorem card_le_of_dofIdx {g : Finset (Fin n → ℝ)} {k : ℕ} (i : S.DofIdx g k) : k + 1 ≤ #g := by
  by_contra h
  exact (S.isEmpty_dofIdx_of_card_lt (by omega)).false i

/-- **The DOF error of `Q_N` on `Vₕ`** for the higher-order families: for `v ∈ Vₕ`, a face `g`
of `T` and a degree of freedom `i` of `g`,
`h^{n/2} |ℓ_{g,i}(v_T - R v)| ≤ 3 (n + 1) D 2^{k+1} A γ hᵏ m_T(v)^{1/2}`. -/
theorem sqrt_mul_abs_dof_err_le {N k : ℕ} {A D : ℝ} (hA0 : 0 ≤ A) (hA : InvBound S n k A)
    (hD : CoeffBound S n k D) {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpace (mesh n N) k) (hs : SampleOK S γ p u)
    (T : (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (i : S.DofIdx g k) :
    √(hN N) ^ n * |S.dof g k i ⟨((u T : (polyElement n S).space T k) : FormField n),
        S.space_le_contForms n k (u T).2⟩ -
      S.dof g k i (Submodule.inclusion c1Forms_le_contForms
        (smoothForm p (isOpen_mesh_domain n N).measurableSet k
          ((polyElement n S).glue (mesh n N) k u)))| ≤
      3 * (n + 1) * D * 2 ^ (k + 1) * A * γ * hN N ^ k *
        √(locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)) := by
  classical
  have hγ := hp.gamma_pos
  have hne := i.2
  set m := #g - 1
  have hg : #g = m + 1 := (Nat.succ_pred_eq_of_pos (card_pos.2 hne)).symm
  have hkm : k ≤ m := by have := card_le_of_dofIdx S i; omega
  have hmn : m ≤ n := by
    have := Finset.card_le_card hgT
    rw [card_vertexSet] at this; omega
  set q := lexEnum g m
  set η := (S.testBasis k m i.1 : FormField m)
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  set w : c1Forms n := smoothForm p (isOpen_mesh_domain n N).measurableSet k
    ((polyElement n S).glue (mesh n N) k u)
  set L := locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have huc : Continuous uT := (PolyKind.contDiff_of_mem_space huT).continuous
  have hwc : Continuous (w : FormField n) := (mem_c1Forms.1 w.2).continuous
  set F : (Fin m → ℝ) → ℝ := fun ξ =>
    ∑ s, (uT (simplexMap q ξ) s - (w : FormField n) (simplexMap q ξ) s) * dofCoeff q η k ξ s
  have hdc : Continuous fun ξ : Fin m → ℝ => η ξ := S.continuous_testBasis k m i.1
  have hcoef : ∀ s, Continuous fun ξ => dofCoeff q η k ξ s := fun s => by
    simp only [dofCoeff]
    split_ifs
    · simp only [wedgeForm_apply]
      exact continuous_finsetSum _ fun a _ => continuous_const.mul
        ((continuous_apply _).comp hdc)
    · exact continuous_const
  have hFc : Continuous F := continuous_finsetSum _ fun s _ =>
    ((((continuous_apply s).comp (huc.comp (continuous_simplexMap q))).sub
      ((continuous_apply s).comp (hwc.comp (continuous_simplexMap q)))).mul (hcoef s))
  have herr : S.dof g k i ⟨uT, S.space_le_contForms n k huT⟩ -
      S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) =
        ∫ ξ in FiniteElement.refSimplex m, F ξ := by
    rw [← map_sub, S.dof_eq_integral]
    refine setIntegral_congr_fun (measurableSet_refSimplex _) fun ξ _ => ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    rfl
  set Mc := D * hN N ^ k
  have hMc : ∀ ξ ∈ FiniteElement.refSimplex m, ∑ s, |dofCoeff q η k ξ s| ≤ Mc :=
    fun ξ hξ => hD N T.2 hgT i ξ hξ
  have hMc0 : 0 ≤ Mc := by
    have h0 : (0 : Fin m → ℝ) ∈ FiniteElement.refSimplex m := fun a => by
      refine Fin.cases ?_ (fun l => ?_) a
      · simp
      · simp [refBary]
    exact (Finset.sum_nonneg fun s _ => abs_nonneg _).trans (hMc 0 h0)
  set c := Mc * A * √L * 2 ^ (k + 1)
  have hc0 : 0 ≤ c := by positivity
  rw [herr]
  refine (mul_abs_integral_refSimplex_le hFc (pow_nonneg (Real.sqrt_nonneg _) n) hc0
    (by positivity) hγ.le (by linarith) fun ξ hξ =>
      (sqrt_mul_abs_integrand_le S hA0 hA hp hγ2 hu hs T hgT hg hξ (dofCoeff q η k ξ)
        (fun α β hα hβ hαβ => sum_mul_dofCoeff_eq_of_pullback_eq q η ξ hα hβ hαβ)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hMc ξ hξ) hA0) (Real.sqrt_nonneg _)) (by positivity))
        (by split_ifs <;> positivity))).trans ?_
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hkm.trans hmn
  have hm' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  calc c * ((k + 1) * γ + (m + 1) * γ) ≤ c * (3 * (n + 1) * γ) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hc0
    _ = _ := by simp only [c, Mc]; ring

/-- **The local `L²` error of `Q_N` on `Vₕ`** for the higher-order families:
`‖v - Q_N v‖²_{L²(T)} ≲ γ² m_T(v)`. -/
theorem sum_integral_sq_sub_interp_le {N k : ℕ} {A B D : ℝ} (hA0 : 0 ≤ A) (hA : InvBound S n k A)
    (hB0 : 0 ≤ B) (hB : DofBound S n k B) (hD0 : 0 ≤ D) (hD : CoeffBound S n k D)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpace (mesh n N) k) (hs : SampleOK S γ p u)
    (T : (mesh n N).simplices) :
    ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      ((((u T : (polyElement n S).space T k) : FormField n) -
        ((((polyElement n S).globalInterp (mesh n N) k
          (Submodule.inclusion c1Forms_le_contForms
            (smoothForm p (isOpen_mesh_domain n N).measurableSet k
              ((polyElement n S).glue (mesh n N) k u))) :
            (polyElement n S).Piecewise (mesh n N) k) T : (polyElement n S).space T k) :
              FormField n)) y s.1) ^ 2 ≤
      2 ^ n * (B * Module.finrank ℝ (S.space n k) *
        (3 * (n + 1) * D * 2 ^ (k + 1) * A) * γ) ^ 2 *
        locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n) := by
  set h := hN N
  have hh : 0 < h := hN_pos N
  set w := smoothForm p (isOpen_mesh_domain n N).measurableSet k
    ((polyElement n S).glue (mesh n N) k u)
  set Pw : (polyElement n S).space T k := (((polyElement n S).globalInterp (mesh n N) k
    (Submodule.inclusion c1Forms_le_contForms w) : (polyElement n S).Piecewise (mesh n N) k) T)
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  have hPw : (Pw : FormField n) ∈ S.space n k := Pw.2
  set z : FormField n := uT - (Pw : FormField n)
  have hz : z ∈ S.space n k := Submodule.sub_mem _ huT hPw
  set L := locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _
  have hγ := hp.gamma_pos
  set C₁ := 3 * (n + 1) * D * 2 ^ (k + 1) * A
  have hC₁ : 0 ≤ C₁ := by positivity
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  set D' := C₁ * γ * √L / √h ^ n
  have hD'0 : 0 ≤ D' := by positivity
  have hdof : ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ h ^ k * D' := by
    intro g hgT i
    have e1 : S.dof g k i ⟨(Pw : FormField n), S.space_le_contForms n k hPw⟩ =
        S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) :=
      (polyElement n S).localDof_globalInterp (mesh n N) k
        (Submodule.inclusion c1Forms_le_contForms w) T g hgT i
    have e : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ =
        S.dof g k i ⟨uT, S.space_le_contForms n k huT⟩ -
          S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) := by
      rw [← e1, ← map_sub]; rfl
    rw [e]
    have h1 := sqrt_mul_abs_dof_err_le S hA0 hA hD hp hγ2 hu hs T hgT i
    have e2 : h ^ k * D' = C₁ * γ * h ^ k * √L / √h ^ n := by
      simp only [D']; ring
    rw [e2, le_div_iff₀ hsq, mul_comm]
    exact h1
  have hzb : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
      |z y s| ≤ B * Module.finrank ℝ (S.space n k) * D' :=
    fun y hy s => abs_le_of_abs_dof_le S hB hB0 T.2 hz hdof hy s
  set P := (Module.finrank ℝ (S.space n k) : ℝ)
  have hhn : h ^ n = (√h ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hh.le]
  calc ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        (z y s.1) ^ 2
      ≤ 2 ^ n * (h ^ n * (B * P * D') ^ 2) :=
        sum_integral_sq_le_of_abs_le T.2 (PolyKind.contDiff_of_mem_space hz).continuous hzb
    _ = 2 ^ n * (B * P * C₁ * γ) ^ 2 * (√L) ^ 2 := by
        rw [hhn]; simp only [D']; field_simp
    _ = 2 ^ n * (B * P * C₁ * γ) ^ 2 * L := by rw [Real.sq_sqrt hL0]

/-- **`Q_N` is close to the identity on `Vₕ`** for the higher-order families:
`‖v - Q_N v‖² ≤ 2ⁿ (B dim(P) C₁ γ)² 6ⁿ n! ‖v‖²`, `C₁ = 3 (n + 1) D 2^{k+1} A`. -/
theorem norm_sq_sub_smoothedInterp_le {N k : ℕ} {A B D : ℝ} (hA0 : 0 ≤ A) (hA : InvBound S n k A)
    (hB0 : 0 ≤ B) (hB : DofBound S n k B) (hD0 : 0 ≤ D) (hD : CoeffBound S n k D)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpace (mesh n N) k) (hs : SampleOK S γ p u) :
    ‖(polyElement n S).glue (mesh n N) k u - (polyElement n S).smoothedInterp (mesh n N)
        p (isOpen_mesh_domain n N).measurableSet k
        ((polyElement n S).glue (mesh n N) k u)‖ ^ 2 ≤
      2 ^ n * (B * Module.finrank ℝ (S.space n k) *
        (3 * (n + 1) * D * 2 ^ (k + 1) * A) * γ) ^ 2 *
        ((6 ^ n * n.factorial : ℕ) * ‖(polyElement n S).glue (mesh n N) k u‖ ^ 2) := by
  set v := (polyElement n S).glue (mesh n N) k u
  have hQ := (polyElement n S).smoothedInterp_natCast (mesh n N) p
    (isOpen_mesh_domain n N).measurableSet k v
  set Pw := (polyElement n S).globalInterp (mesh n N) k (Submodule.inclusion c1Forms_le_contForms
    (smoothForm p (isOpen_mesh_domain n N).measurableSet k v))
  set d : (polyElement n S).Piecewise (mesh n N) k :=
    u - (Pw : (polyElement n S).Piecewise (mesh n N) k)
  have hsub : v - (polyElement n S).smoothedInterp (mesh n N) p
      (isOpen_mesh_domain n N).measurableSet k v = (polyElement n S).glue (mesh n N) k d := by
    rw [hQ, map_sub]
  rw [hsub]
  exact norm_sq_glue_le_locMass _ v d (by positivity)
    fun T hT => sum_integral_sq_sub_interp_le S hA0 hA hB0 hB hD0 hD hp hγ2 hu hs ⟨T, hT⟩

/-! ### The smoothing scale, uniformly for all small `γ` -/

/-- `K (x γ)² ≤ ¼` for every `0 ≤ γ ≤ 1 / (2 (1 + S K))` and `0 ≤ x ≤ S`. -/
theorem sq_le_quarter_of_le {S K x γ : ℝ} (hS : 0 ≤ S) (hK : 1 ≤ K) (hx0 : 0 ≤ x) (hx : x ≤ S)
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / (2 * (1 + S * K))) : K * (x * γ) ^ 2 ≤ 1 / 4 := by
  refine le_trans ?_ (sq_le_quarter hS hK hx0 hx)
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  exact pow_le_pow_left₀ (mul_nonneg hx0 hγ0) (mul_le_mul_of_nonneg_left hγ hx0) 2

variable (n) in
/-- **The smoothing scale for the higher-order families, for all small `γ`**: there is
`γ₀ ∈ (0, ½]`, depending only on `n` and the sequence `S`, such that for **every** `γ ∈ (0, γ₀]`,
every admissible parameter at scale `γ` (either family) and every global field satisfying the
sampling condition, `‖v - Q_N v‖ ≤ ½ ‖v‖`. -/
theorem exists_gamma₀ :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ γ : ℝ, γ ≤ γ₀ → ∀ (N k : ℕ)
      (p : SmoothingParam (Fin n → ℝ)), IsAdm γ N p →
      ∀ u ∈ (polyElement n S).globalSpace (mesh n N) k, SampleOK S γ p u →
        ‖(polyElement n S).glue (mesh n N) k u - (polyElement n S).smoothedInterp (mesh n N) p
          (isOpen_mesh_domain n N).measurableSet k ((polyElement n S).glue (mesh n N) k u)‖ ≤
          1 / 2 * ‖(polyElement n S).glue (mesh n N) k u‖ := by
  classical
  choose A hA0 hA using fun k : ℕ => exists_invBound (n := n) S k
  choose B hB0 hB using fun k : ℕ => exists_dofBound (n := n) S k
  choose D hD0 hD using fun k : ℕ => exists_coeffBound (n := n) S k
  set x : ℕ → ℝ := fun k => B k * Module.finrank ℝ (S.space n k) *
    (3 * (n + 1) * D k * 2 ^ (k + 1) * A k)
  have hx0 : ∀ k, 0 ≤ x k := fun k => by
    have := hA0 k; have := hB0 k; have := hD0 k; positivity
  set S' := ∑ k ∈ Finset.range (n + 1), x k
  have hS : 0 ≤ S' := Finset.sum_nonneg fun k _ => hx0 k
  set K : ℝ := 2 ^ n * ((6 ^ n * n.factorial : ℕ) : ℝ)
  have hK : 1 ≤ K := one_le_cov
  set γ₀ := 1 / (2 * (1 + S' * K)) with hγe
  have hpos : 0 < 1 + S' * K := by nlinarith
  have hγ₀ : 0 < γ₀ := by positivity
  have hγ₀2 : γ₀ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ N k p hp u hu hs => ?_⟩
  have hγ0 := hp.gamma_pos
  by_cases hk : n < k
  · have := subsingleton_L2F_of_lt (Ω := (mesh n N).domain) hk
    rw [Subsingleton.elim ((polyElement n S).glue (mesh n N) k u) 0]; simp
  push Not at hk
  have hxk : x k ≤ S' := Finset.single_le_sum (fun k _ => hx0 k) (Finset.mem_range.2 (by omega))
  have h := norm_sq_sub_smoothedInterp_le S (hA0 k) (hA k) (hB0 k) (hB k) (hD0 k) (hD k) hp
    (hγ.trans hγ₀2) hu hs
  have hq := sq_le_quarter_of_le hS hK (hx0 k) hxk hγ0.le hγ
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (h.trans ?_)
  calc 2 ^ n * (x k * γ) ^ 2 *
        (((6 ^ n * n.factorial : ℕ) : ℝ) * ‖(polyElement n S).glue (mesh n N) k u‖ ^ 2)
      = K * (x k * γ) ^ 2 * ‖(polyElement n S).glue (mesh n N) k u‖ ^ 2 := by ring
    _ ≤ 1 / 4 * ‖(polyElement n S).glue (mesh n N) k u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hq (sq_nonneg _)
    _ = (1 / 2 * ‖(polyElement n S).glue (mesh n N) k u‖) ^ 2 := by ring

/-! ### The sampling condition for both families -/

/-- **The maximal family samples only inside `Ω`** (`pMax_samples_mem`), so the sampling
condition holds for every field. -/
theorem sampleOK_pMax {γ : ℝ} {hγ : 0 < γ} {hγ1 : γ ≤ 1} {N k : ℕ}
    (u : (polyElement n S).Piecewise (mesh n N) k) :
    SampleOK S γ (pMax (n := n) γ hγ hγ1 N) u := by
  intro T g hgT m hg ξ hξ _ t ht htΩ
  exact absurd (pMax_samples_mem N _ ((mesh n N).closedInterior_subset_closure T.2
    (simplexMap_lexEnum_mem hgT hg hξ)) t ht) htΩ

/-- **The minimal family satisfies the sampling condition on `V̊ₕ`** (higher-order families): a
sample outside `Ω` near a point of a face with weights `≥ γ` forces the face to lie in a boundary
facet, where the DOFs of fields with vanishing boundary DOFs vanish. -/
theorem sampleOK_pMin {γ : ℝ} {hγ : 0 < γ} (hγ2 : γ ≤ 1 / 2) {N k : ℕ}
    {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpace₀ (mesh n N) k) :
    SampleOK S γ (pMin (n := n) γ hγ N) u := by
  classical
  intro T g hgT m hg ξ hξ hgood t ht htΩ
  set q := lexEnum g m
  have hμ : ∀ a, γ ≤ refBary ξ a := by
    intro a; by_contra hlt; push Not at hlt; exact hgood ⟨a, hlt⟩
  have hxc : simplexMap q ξ ∈ closure (cubeDomain n) := by
    rw [← mesh_domain n N]
    exact (mesh n N).closedInterior_subset_closure T.2 (simplexMap_lexEnum_mem hgT hg hξ)
  obtain ⟨T'', hT'', F, hF, hFT'', hgF⟩ := exists_boundaryFacet_of_near T.2 hgT
    (Finset.card_pos.1 (by rw [hg]; omega)) (q := q) (fun a => hgT (lexEnum_mem hg a))
    (fun v hv => by
      have : v ∈ Set.range q := by rw [range_lexEnum hg]; exact hv
      exact this) hγ hγ2 hμ (sum_refBary ξ)
    (by rw [← simplexMap_eq_sum q ξ]; exact (pMin_isAdm N).norm_sub_lt hxc ht) htΩ
  -- the boundary DOFs vanish
  intro g' hg' j
  have h0 := hu.2 ⟨T'', hT''⟩ F hF hFT'' g' (hg'.trans hgF) j
  rw [hu.1 T ⟨T'', hT''⟩ g' (hg'.trans hgT) ((hg'.trans hgF).trans hFT'') j]
  exact h0

end Poly

/-! ### The higher-order complexes of the cube and their smoothed interpolants -/

variable [NeZero n]

instance (S : PolySeq) (M : SimplicialMesh n) (hΩ : IsOpen M.domain) (k : ℤ) :
    FiniteDimensional ℝ ((S.subcomplex M hΩ).V k) :=
  inferInstanceAs (FiniteDimensional ℝ ((polyElement n S).V M k))

instance (S : PolySeq) (M : SimplicialMesh n) (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    (k : ℤ) : FiniteDimensional ℝ ((S.subcomplexMin M hΩ x₀ hstar).V k) :=
  inferInstanceAs (FiniteDimensional ℝ ((polyElement n S).V₀ M k))

variable (n) in
/-- **The finite element complex of the admissible sequence `S`** on the level-`(N + 1)`
Freudenthal mesh of the cube (`P_{r_k}Λᵏ` / `P_{r_k}⁻Λᵏ` in degree `k`), as a subcomplex of
`HΛ(Q)`. -/
def poly (S : PolySeq) (N : ℕ) : (complex n).Subcomplex :=
  (deRham ℝ n).maximalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (S.subcomplex (mesh n N) (isOpen_mesh_domain n N))

instance (S : PolySeq) (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((poly n S N).V k) :=
  (deRham ℝ n).finiteDimensional_maximalSubcomplexOfEq _ _ _ _ k

variable (n) in
/-- **The finite element complex of `S` with vanishing boundary DOFs** on the level-`(N + 1)`
Freudenthal mesh of the cube, as a subcomplex of `H̊Λ(Q)`. -/
def polyMin (S : PolySeq) (N : ℕ) : (complexMin n).Subcomplex :=
  (deRham ℝ n).minimalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    (S.subcomplexMin (mesh n N) (isOpen_mesh_domain n N) (center n) (strictStar_mesh n N))

instance (S : PolySeq) (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((polyMin n S N).V k) :=
  (deRham ℝ n).finiteDimensional_minimalSubcomplexOfEq _ _ _ _ k

variable (n) in
/-- **The smoothed canonical interpolant** `Q_N = Π_h R` of the complex of `S` on the cube, for
maximal-family smoothing parameters centred at the centre of the cube. -/
def polySmoothed (S : PolySeq) (N : ℕ) (p : SmoothingParam (Fin n → ℝ))
    (hp : p.IsMaximal (center n) (1 / 4)) : (poly n S N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEq (mesh_domain n N) (isOpen_mesh_domain n N) (isOpen_cubeDomain n)
    ((polyElement n S).smoothedCommutingMap (mesh n N) p (isOpen_mesh_domain n N)
      (starBall_mesh n N) hp)

variable (n) in
/-- **The smoothed canonical interpolant with vanishing boundary DOFs** `Q̊_N = Π_h R` of the
complex of `S` on the cube, for minimal-family smoothing parameters. -/
def polySmoothedMin (S : PolySeq) (N : ℕ) (p : SmoothingParam (Fin n → ℝ))
    (hp : p.IsMinimal (center n) (1 / 4)) : (polyMin n S N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEqMin (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    ((polyElement n S).smoothedCommutingMapMin (mesh n N) p (isOpen_mesh_domain n N)
      (mesh_domain n N ▸ isBounded_cubeDomain n) (starBall_mesh n N) hp (center n)
      (strictStar_mesh n N))

variable (n) in
/-- **The estimates of the smoothed interpolants of the complex of `S`** ([AFW2010], §5.5;
[ChristiansenWinther2008]): for maximal-family parameters `p N`, uniform `L²` bounds of `Q_N`
and `‖v - Q_N v‖ ≤ ½ ‖v‖` on `Vₕ`, normalized by `½ ≤ C` (the analogue of
`FEM.SmoothingEstimates` for the Whitney complex). -/
structure PolySmoothingEstimates (S : PolySeq) (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ) :
    Prop where
  isMaximal : ∀ N, (p N).IsMaximal (center n) (1 / 4)
  half_le : 1 / 2 ≤ C
  bound : ∀ N i x, ‖(polySmoothed n S N (p N) (isMaximal N)).Q i x‖ ≤ C * ‖x‖
  close : ∀ N i, ∀ v ∈ (poly n S N).V i,
    ‖v - (polySmoothed n S N (p N) (isMaximal N)).Q i v‖ ≤ 1 / 2 * ‖v‖

variable (n) in
/-- **The estimates of the smoothed interpolants with vanishing boundary DOFs** of the complex of
`S` (the analogue of `FEM.SmoothingEstimatesMin`). -/
structure PolySmoothingEstimatesMin (S : PolySeq) (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ) :
    Prop where
  isMinimal : ∀ N, (p N).IsMinimal (center n) (1 / 4)
  half_le : 1 / 2 ≤ C
  bound : ∀ N i x, ‖(polySmoothedMin n S N (p N) (isMinimal N)).Q i x‖ ≤ C * ‖x‖
  close : ∀ N i, ∀ v ∈ (polyMin n S N).V i,
    ‖v - (polySmoothedMin n S N (p N) (isMinimal N)).Q i v‖ ≤ 1 / 2 * ‖v‖

theorem smoothedCommutingMapMin_Q_eq (E : LocalElement n) {M : SimplicialMesh n}
    (p : SmoothingParam (Fin n → ℝ))
    (hΩo : IsOpen M.domain) (hb : Bornology.IsBounded M.domain) {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMinimal x₀ s₀) (y₀ : Fin n → ℝ)
    (hstar' : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → y₀ + t • (x - y₀) ∈ M.domain)
    (i : ℤ) :
    (E.smoothedCommutingMapMin M p hΩo hb hstar hp y₀ hstar').Q i =
      E.smoothedInterp M p hΩo.measurableSet i := rfl

/-- **The smoothed-projection estimates hold for every admissible sequence, for all small `γ`**
([AFW2010], §5.5; [ChristiansenWinther2008]): there is `γ₀ ∈ (0, ½]` depending only on `n` and
`S` such that for **every** `γ ∈ (0, γ₀]` the parameters `pMax γ` (dilation factor
`1 - γ h_N` about the centre, bump radii `γ h_N / 64 < γ h_N / 32`) satisfy the estimates, with
a constant `C` depending on `γ`. -/
theorem polySmoothingEstimates_pMax (S : PolySeq) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1), γ ≤ γ₀ →
      ∃ C, PolySmoothingEstimates n S (pMax γ hγ hγ1) C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, hclose⟩ := Poly.exists_gamma₀ n S
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγ1 hγγ₀ => ?_⟩
  obtain ⟨C, hC0, hbound⟩ := Poly.exists_norm_smoothedInterp_le (n := n) S hγ hγ1
  refine ⟨max C (1 / 2), ?_⟩
  have hest : ∀ N, (∀ i x, ‖(polySmoothed n S N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (poly n S N).V i,
        ‖v - (polySmoothed n S N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i v‖ ≤
          1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEq_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · exact (hbound N k _ (pMax_isAdm N) x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact hclose γ hγγ₀ N k _ (pMax_isAdm N) u.1 u.2 (Poly.sampleOK_pMax S _)
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  exact ⟨fun N => pMax_isMaximal N, le_max_right _ _, fun N => (hest N).1,
    fun N => (hest N).2⟩

/-- **The smoothed-projection estimates with vanishing boundary DOFs hold for every admissible
sequence, for all small `γ`**: as `polySmoothingEstimates_pMax`, for the parameters `pMin γ`
(dilation factor `1 + γ h_N` towards the centre). -/
theorem polySmoothingEstimatesMin_pMin (S : PolySeq) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ), γ ≤ γ₀ →
      ∃ C, PolySmoothingEstimatesMin n S (pMin γ hγ) C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, hclose⟩ := Poly.exists_gamma₀ n S
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγγ₀ => ?_⟩
  have hγ2 : γ ≤ 1 / 2 := hγγ₀.trans hγ₀2
  have hγ1 : γ ≤ 1 := by linarith
  obtain ⟨C, hC0, hbound⟩ := Poly.exists_norm_smoothedInterp_le (n := n) S hγ hγ1
  refine ⟨max C (1 / 2), ?_⟩
  have hest : ∀ N, (∀ i x, ‖(polySmoothedMin n S N (pMin γ hγ N) (pMin_isMinimal N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (polyMin n S N).V i,
        ‖v - (polySmoothedMin n S N (pMin γ hγ N) (pMin_isMinimal N)).Q i v‖ ≤
          1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEqMin_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [smoothedCommutingMapMin_Q_eq]
      rcases i with k | k
      · exact (hbound N k _ (pMin_isAdm N) x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
    · rw [smoothedCommutingMapMin_Q_eq]
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact hclose γ hγγ₀ N k _ (pMin_isAdm N) u.1
          ((polyElement n S).globalSpace₀_le (mesh n N) k u.2) (Poly.sampleOK_pMin S hγ2 u.2)
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  exact ⟨fun N => pMin_isMinimal N, le_max_right _ _, fun N => (hest N).1,
    fun N => (hest N).2⟩

/-- **One smoother for finitely many families at once**: for a finite family of admissible
sequences `S i` there is `γ₀ > 0` such that for every `γ ∈ (0, γ₀]` the same parameters `pMax γ`
(resp. `pMin γ`) satisfy the smoothing estimates of the Whitney complex and of every complex
`S i`, in both boundary-condition families. -/
theorem exists_common_gamma {ι : Type*} [Finite ι] (S : ι → PolySeq) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1), γ ≤ γ₀ →
      (∃ C, SmoothingEstimates n (pMax γ hγ hγ1) C) ∧
      (∃ C, SmoothingEstimatesMin n (pMin γ hγ) C) ∧
      ∀ i, (∃ C, PolySmoothingEstimates n (S i) (pMax γ hγ hγ1) C) ∧
        ∃ C, PolySmoothingEstimatesMin n (S i) (pMin γ hγ) C := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨γw, hγw, hγw2, hw⟩ := smoothingEstimates_pMax_forall (n := n)
  obtain ⟨γw', hγw', hγw'2, hw'⟩ := smoothingEstimatesMin_pMin_forall (n := n)
  choose γp hγp hγp2 hp using fun i => polySmoothingEstimates_pMax (n := n) (S i)
  choose γq hγq hγq2 hq using fun i => polySmoothingEstimatesMin_pMin (n := n) (S i)
  set G : Finset ℝ := insert γw (insert γw' (Finset.univ.image γp ∪ Finset.univ.image γq))
  have hGne : G.Nonempty := Finset.insert_nonempty _ _
  set γ₀ := G.min' hGne
  have hmem : γ₀ ∈ G := Finset.min'_mem G hGne
  have hle : ∀ x ∈ G, γ₀ ≤ x := fun x hx => Finset.min'_le G x hx
  have hpos : ∀ x ∈ G, 0 < x ∧ x ≤ 1 / 2 := by
    intro x hx
    simp only [G, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hx
    rcases hx with rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨hγw, hγw2⟩
    · exact ⟨hγw', hγw'2⟩
    · exact ⟨hγp i, hγp2 i⟩
    · exact ⟨hγq i, hγq2 i⟩
  refine ⟨γ₀, (hpos _ hmem).1, (hpos _ hmem).2, fun γ hγ hγ1 hγγ₀ => ⟨hw γ hγ hγ1
    (hγγ₀.trans (hle _ (by simp [G]))), hw' γ hγ (hγγ₀.trans (hle _ (by simp [G]))),
    fun i => ⟨hp i γ hγ hγ1 (hγγ₀.trans (hle _ (by simp [G]))),
      hq i γ hγ (hγγ₀.trans (hle _ (by simp [G])))⟩⟩⟩

end Feec.Models.Cube.FEM
