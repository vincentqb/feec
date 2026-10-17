module

public import Feec.Legacy.MirrorCube.Cube

/-!
# The mirror complex on `Q` contains the thesis' Dirichlet complex

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

For the repaired Prop 4.17 on the box (`Feec.Legacy.MirrorCube.Cube`) this file shows that the mirror
boundary conditions are weaker than the thesis' ones: `H̊¹(Q; ℝ³) ⊆ D(d0)` and
`H̊(curl, Q; ℝ³ˣ³) ⊆ D(d1)`, with `d0 = grad`, `d1 = curl` there
(`gradClosure_le_mirror`, `curlClosure_le_mirror`). Together with `D(d1) ⊆ H(curl, Q)`
(`Feec.Legacy.MirrorCube.mirrorCxQ_d1_domain_le`) the domain of the mirror curl lies between the
Dirichlet and the free space: `H̊(curl, Q) ⊆ D(d1) ⊆ H(curl, Q)`.

Proof: the mirror extension of a test field is `8 · avg (per Φ)` (`Jm_testField`, `Jv_testFieldV`),
whose curl (gradient) is the mirror extension of `curl Φ` (`grad φ`); the graph relation
`curl (Jm₁ B) = Jm₋₁ C` is closed and contains the test graph, hence its closure.

## References

* [QuennevilleBelair2015], §4.10
* [Brezis2011], §9.2 (extension by reflection)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace InnerProductSpace ComplexConjugate
open MeasureTheory Set Filter Topology LinearPMap

namespace Feec.Legacy.MirrorCube

open Feec.Legacy.Torus Feec.Legacy.TorusWeak Feec.Legacy.Box Feec.Legacy.BoxIdent Feec.Legacy.Constraints Feec.Legacy.HilbertComplex2
open Feec.Legacy.BoundedDomain (R3 Ix IsTest curlM)

attribute [local instance] Feec.Legacy.Torus.instMeasureSpaceUnitAddCircle_feec

section Cfield

/-- **The mirror reflection on continuous fields**: `R_i` acts on the field with entries `F_{ab}`
by `F_{ab} ↦ ε s_i(a) s_i(b) · F_{ab} ∘ R_i`. -/
theorem mirror_R_cField (ε : ℝ) (hε : ε * ε = 1) (i : Fin 3) (F : Ix → C(T3, ℂ)) :
    (mirrorM ε hε).R i (cField F) = cField fun p => sR (cM ε p i) i (F p) := by
  refine lp.ext (funext fun k => ?_)
  ext ⟨a, b⟩
  change matSgn ε i (cField F (Box.refl i k)) (a, b) = _
  rw [matSgn_apply, cField_apply, cField_apply, mFourierCoeff_sR]
  simp only [cM]

theorem mirror_half_cField (ε : ℝ) (hε : ε * ε = 1) (i : Fin 3) (F : Ix → C(T3, ℂ)) :
    (mirrorM ε hε).half i (cField F) = cField fun p => halfC (cM ε p i) i (F p) := by
  rw [Refl3.half_apply, mirror_R_cField, ← cField_add, ← cField_smul]
  rfl

theorem mirror_avg_cField (ε : ℝ) (hε : ε * ε = 1) (F : Ix → C(T3, ℂ)) :
    (mirrorM ε hε).avg (cField F) = cField fun p => avgC (cM ε p) (F p) := by
  rw [Refl3.avg_apply, mirror_half_cField, mirror_half_cField, mirror_half_cField]
  rfl

/-- The mirror extension of a test field, `8 · avg (per Φ)`. -/
def mextF (ε : ℝ) (hε : ε * ε = 1) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) : L2M :=
  (8 : ℝ) • (mirrorM ε hε).avg (cField fun p => perC (hΦ p))

theorem resB_mextF (ε : ℝ) (hε : ε * ε = 1) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    resB (mextF ε hε hΦ) = BoundedDomain.testField hΦ := by
  ext1 p
  refine Lp.ext ?_
  rw [mextF, _root_.map_smul, mirror_avg_cField]
  filter_upwards [Lp.coeFn_smul (8 : ℝ) (resB (cField fun p =>
      avgC (cM ε p) (perC (hΦ p))) p),
    coeFn_resB_cField (fun p => avgC (cM ε p) (perC (hΦ p))) p,
    BoundedDomain.coeFn_testField hΦ p, ae_restrict_mem measurableSet_Qr] with y h1 h2 h3 h4
  change ((8 : ℝ) • resB _) p y = _
  rw [PiLp.smul_apply, h1, Pi.smul_apply, h2, h3,
    avgC_of_mem_boxSet _ (fun x hx => per_eq_zero_of_notMem (hΦ p) hx)
      (proj_mem_boxSet fun i => h4 i (mem_univ i)),
    perC_apply, per_proj_of_mem h4]
  simp only [smul_eq_mul]
  rw [show ((1 / 8 : ℂ) * (Φ p y : ℂ)) = (((1 / 8 : ℝ) * Φ p y : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]
  ring

theorem isRealM_mextF (ε : ℝ) (hε : ε * ε = 1) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    IsRealM (mextF ε hε hΦ) := by
  rw [mextF, mirror_avg_cField, ← cField_smul]
  refine isRealM_cField fun p x => ?_
  change conj ((8 : ℝ) • avgC _ (perC (hΦ p)) x) = (8 : ℝ) • avgC _ (perC (hΦ p)) x
  rw [Complex.real_smul, map_mul, Complex.conj_ofReal, conj_avgC _ (conj_perC (hΦ p))]

/-- **The mirror extension of a test field is `8 · avg (per Φ)`.** -/
theorem Jm_testField (ε : ℝ) (hε : ε * ε = 1) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    Jm ε hε (BoundedDomain.testField hΦ) = mextF ε hε hΦ := by
  rw [← resB_mextF ε hε hΦ]
  exact Jm_resB hε (Submodule.smul_mem _ _ ((mirrorM ε hε).avg_mem _)) (isRealM_mextF ε hε hΦ)

/-- **`curl ∘ Jm₁ = Jm₋₁ ∘ curl` on test fields.** -/
theorem curl_Jm_testField {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Qr (Φ ij)) :
    ∃ h : Jm 1 one_mul_one (BoundedDomain.testField hΦ) ∈ Hcurl,
      curlT ⟨_, h⟩ = Jm (-1) neg_one_mul_neg_one (BoundedDomain.testField (isTest_curl hΦ)) := by
  rw [Jm_testField, Jm_testField]
  obtain ⟨h, e⟩ := intertwines_curl.avg ⟨_, cField_per_mem_Hcurl hΦ⟩
  refine ⟨Submodule.smul_mem _ (8 : ℝ) h, ?_⟩
  have : (⟨mextF 1 one_mul_one hΦ, Submodule.smul_mem _ (8 : ℝ) h⟩ : curlT.domain) =
      (8 : ℝ) • ⟨_, h⟩ := rfl
  rw [this, LinearPMap.map_smul]
  change (8 : ℝ) • periodicComplex.d1 ⟨_, h⟩ = _
  rw [e]
  change (8 : ℝ) • (mirrorM (-1) neg_one_mul_neg_one).avg
    (curlT ⟨_, cField_per_mem_Hcurl hΦ⟩) = _
  rw [curlT_cField_per]
  rfl

end Cfield

section Vfield

theorem mirror_R_vField (i : Fin 3) (F : Fin 3 → C(T3, ℂ)) :
    mirrorV.R i (vField F) = vField fun a => sR (cV a i) i (F a) := by
  refine lp.ext (funext fun k => ?_)
  ext a
  change vecSgn i (vField F (Box.refl i k)) a = _
  rw [vecSgn_apply, vField_apply, vField_apply, mFourierCoeff_sR]
  simp only [cV]

theorem mirror_half_vField (i : Fin 3) (F : Fin 3 → C(T3, ℂ)) :
    mirrorV.half i (vField F) = vField fun a => halfC (cV a i) i (F a) := by
  rw [Refl3.half_apply, mirror_R_vField, ← vField_add, ← vField_smul]
  rfl

theorem mirror_avg_vField (F : Fin 3 → C(T3, ℂ)) :
    mirrorV.avg (vField F) = vField fun a => avgC (cV a) (F a) := by
  rw [Refl3.avg_apply, mirror_half_vField, mirror_half_vField, mirror_half_vField]
  rfl

/-- The mirror extension of a test vector field, `8 · avg (per φ)`. -/
def mextV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) : L2V :=
  (8 : ℝ) • mirrorV.avg (vField fun a => perC (hφ a))

theorem resBV_mextV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) :
    resBV (mextV hφ) = BoundedDomain.testFieldV hφ := by
  ext1 a
  refine Lp.ext ?_
  rw [mextV, _root_.map_smul, mirror_avg_vField]
  filter_upwards [Lp.coeFn_smul (8 : ℝ) (resBV (vField fun a =>
      avgC (cV a) (perC (hφ a))) a),
    coeFn_resBV_vField (fun a => avgC (cV a) (perC (hφ a))) a,
    (hφ a).memLp.coeFn_toLp, ae_restrict_mem measurableSet_Qr] with y h1 h2 h3 h4
  change ((8 : ℝ) • resBV _) a y = ((hφ a).memLp.toLp (φ a) : R3 → ℝ) y
  rw [PiLp.smul_apply, h1, Pi.smul_apply, h2, h3,
    avgC_of_mem_boxSet _ (fun x hx => per_eq_zero_of_notMem (hφ a) hx)
      (proj_mem_boxSet fun i => h4 i (mem_univ i)),
    perC_apply, per_proj_of_mem h4]
  simp only [smul_eq_mul]
  rw [show ((1 / 8 : ℂ) * (φ a y : ℂ)) = (((1 / 8 : ℝ) * φ a y : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]
  ring

theorem isRealV_mextV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) : IsRealV (mextV hφ) := by
  rw [mextV, mirror_avg_vField, ← vField_smul]
  refine isRealV_vField fun a x => ?_
  change conj ((8 : ℝ) • avgC _ (perC (hφ a)) x) = (8 : ℝ) • avgC _ (perC (hφ a)) x
  rw [Complex.real_smul, map_mul, Complex.conj_ofReal, conj_avgC _ (conj_perC (hφ a))]

theorem Jv_testFieldV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) :
    Jv (BoundedDomain.testFieldV hφ) = mextV hφ := by
  rw [← resBV_mextV hφ]
  exact Jv_resBV (Submodule.smul_mem _ _ (mirrorV.avg_mem _)) (isRealV_mextV hφ)

/-- **`grad ∘ Jv = Jm₁ ∘ grad` on test vector fields.** -/
theorem grad_Jv_testFieldV {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, IsTest Qr (φ i)) :
    ∃ h : Jv (BoundedDomain.testFieldV hφ) ∈ gradT.domain,
      gradT ⟨_, h⟩ = Jm 1 one_mul_one (BoundedDomain.testField (isTest_grad hφ)) := by
  rw [Jv_testFieldV, Jm_testField]
  obtain ⟨h, e⟩ := intertwines_grad.avg ⟨_, vField_per_mem_gradT_domain hφ⟩
  refine ⟨Submodule.smul_mem _ (8 : ℝ) h, ?_⟩
  have : (⟨mextV hφ, Submodule.smul_mem _ (8 : ℝ) h⟩ : gradT.domain) = (8 : ℝ) • ⟨_, h⟩ := rfl
  rw [this, LinearPMap.map_smul]
  change (8 : ℝ) • periodicComplex.d0 ⟨_, h⟩ = _
  rw [e]
  change (8 : ℝ) • (mirrorM 1 one_mul_one).avg (gradT ⟨_, vField_per_mem_gradT_domain hφ⟩) = _
  rw [gradT_vField_per]
  rfl

end Vfield

/-! ## The Dirichlet complex is a subcomplex -/

section Sub

/-- The relation `curl (Jm₁ B) = Jm₋₁ C` is closed. -/
theorem isClosed_curlRel : IsClosed {p : MQ × MQ |
    (Jm 1 one_mul_one p.1, Jm (-1) neg_one_mul_neg_one p.2) ∈ curlT.graph} :=
  (periodicComplex.closed1 : IsClosed (curlT.graph : Set (L2M × L2M))).preimage
    ((Jm 1 one_mul_one).continuous.prodMap (Jm (-1) neg_one_mul_neg_one).continuous)

/-- The relation `grad (Jv σ) = Jm₁ G` is closed. -/
theorem isClosed_gradRel : IsClosed {p : VQ × MQ |
    (Jv p.1, Jm 1 one_mul_one p.2) ∈ gradT.graph} :=
  (periodicComplex.closed0 : IsClosed (gradT.graph : Set (L2V × L2M))).preimage
    (Jv.continuous.prodMap (Jm 1 one_mul_one).continuous)

/-- **`H̊(curl, Q) ⊆ D(d1)` and `d1 = curl` there**: the thesis' Dirichlet curl is a restriction of
the mirror curl. -/
theorem curlClosure_le_mirror (u : cxQ.d1.domain) :
    ∃ h : (u : MQ) ∈ mirrorCxQ.d1.domain, mirrorCxQ.d1 ⟨u, h⟩ = cxQ.d1 u := by
  have hsub : BoundedDomain.curlGraph Qr ⊆ {p : MQ × MQ |
      (Jm 1 one_mul_one p.1, Jm (-1) neg_one_mul_neg_one p.2) ∈ curlT.graph} := by
    rintro ⟨B, C⟩ ⟨Φ, hΦ, hp⟩
    obtain ⟨rfl, rfl⟩ := BoundedDomain.eq_of_mem_curlGraph hΦ hp
    obtain ⟨h, e⟩ := curl_Jm_testField hΦ
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, h⟩, rfl, e⟩
  have hcl := closure_minimal hsub isClosed_curlRel
    (BoundedDomain.mem_closure_curlClosure isOpen_Qr isBounded_Qr u)
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1 hcl
  dsimp only at hz1 hz2
  have h : (u : MQ) ∈ mirrorCxQ.d1.domain := by
    change Jm 1 one_mul_one u ∈ curlT.domain
    rw [← hz1]; exact z.2
  refine ⟨h, ?_⟩
  rw [mirrorCxQ_d1_apply]
  have e : curlT ⟨Jm 1 one_mul_one u, h⟩ = Jm (-1) neg_one_mul_neg_one (cxQ.d1 u) := by
    exact (lpmap_congr' _ _ z.2 hz1.symm).trans hz2
  rw [e, resB_Jm]

/-- **`H̊¹(Q) ⊆ D(d0)` and `d0 = grad` there**: the thesis' Dirichlet gradient is a restriction of
the mirror gradient. -/
theorem gradClosure_le_mirror (u : cxQ.d0.domain) :
    ∃ h : (u : VQ) ∈ mirrorCxQ.d0.domain, mirrorCxQ.d0 ⟨u, h⟩ = cxQ.d0 u := by
  have hsub : BoundedDomain.gradGraph Qr ⊆ {p : VQ × MQ |
      (Jv p.1, Jm 1 one_mul_one p.2) ∈ gradT.graph} := by
    rintro ⟨v, G⟩ ⟨φ, hφ, hp1, hp2⟩
    obtain ⟨rfl, rfl⟩ := BoundedDomain.eq_of_mem_gradGraph hφ hp1 hp2
    obtain ⟨h, e⟩ := grad_Jv_testFieldV hφ
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, h⟩, rfl, e⟩
  have hcl := closure_minimal hsub isClosed_gradRel
    (BoundedDomain.mem_closure_gradClosure isOpen_Qr isBounded_Qr u)
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1 hcl
  dsimp only at hz1 hz2
  have h : (u : VQ) ∈ mirrorCxQ.d0.domain := by
    change Jv u ∈ gradT.domain
    rw [← hz1]; exact z.2
  refine ⟨h, ?_⟩
  rw [mirrorCxQ_d0_apply]
  have e : gradT ⟨Jv u, h⟩ = Jm 1 one_mul_one (cxQ.d0 u) := by
    exact (lpmap_congr' _ _ z.2 hz1.symm).trans hz2
  rw [e, resB_Jm]

/-- **The mirror curl lies between the Dirichlet and the free curl**:
`H̊(curl, Q) ⊆ D(d1) ⊆ H(curl, Q)`. -/
theorem HcurlZero_le_d1_le_HcurlM :
    BoundedDomain.HcurlZero Qr ⊆ (mirrorCxQ.d1.domain : Set MQ) ∧
      (mirrorCxQ.d1.domain : Set MQ) ⊆ BoundedDomain.HcurlM Qr :=
  ⟨fun u hu => (curlClosure_le_mirror ⟨u, BoundedDomain.mem_domain_curlClosure.2 hu⟩).1,
    fun _ hE => mirrorCxQ_d1_domain_le hE⟩

end Sub

end Feec.Legacy.MirrorCube
