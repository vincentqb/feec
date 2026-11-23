module

public import Feec.FiniteElement.FormBGGElasticity
public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.Models.Cube.MaximalRegularDecomposition

/-!
# The Hessian, elasticity and div–div complexes of forms on the cube: closed range and cohomology

On the cube `Q = (0, ½)ⁿ` (`Feec.Models.Cube.FEM.cubeDomain n`) the analytic BGG theorem for
Hilbert complexes (`Feec.BGG.HilbertData.bggVerdict`, Theorem 6 of [ArnoldHu2021]) applies to the
BGG diagrams of differential forms of `Feec.FiniteElement.FormBGG` and
`Feec.FiniteElement.FormBGGElasticity` with no hypothesis left:

* **the regular decompositions**: `HΛ(Q)` has the `H¹`-regular decompositions from `0` on
  (`deRham_hasRegularDecomposition_cube`, from
  `Feec.Models.Cube.Sobolev.deRham_hasRegularDecomposition_Q`, Gaffney's identity on the torus), so
  the Hessian diagram (`J = 0`), the elasticity diagram (`n = 3`, `J = 1`) and the div–div diagram
  (`J = n − 1`) have the regular decompositions of [ArnoldHu2021], §2, Theorem 3;
* **the cohomology of the rows is that of a point**: `dim Hᵏ(HΛ(Q)) = [k = 0]`
  (`Feec.Models.Cube.FEM.finrank_cohomology`), and `dim Hᵏ(HΛ(Q) ⊗ ℝⁿ) = n [k = 0]`
  (`Feec.HilbertComplex.finrank_pi_cohomology`).

So **the Hessian, elasticity and div–div complexes of `Q` have closed range in every degree and
finite-dimensional cohomology, concentrated in degree `0`**: `S` induces zero on cohomology, so
(27) of [ArnoldHu2021], Theorem 6 is an equality
(`Feec.BGG.HilbertData.finrank_bgg_homology_eq_ite`), and `dim H⁰ = n + 1` for the Hessian and
div–div complexes (the dimension of the affine functions, resp. of the fields `a + b x`), `6` for
the elasticity complex on `Q ⊆ ℝ³` (the dimension of the rigid motions), `Hⁱ = 0` for `i ≠ 0`
(`hessianBGG_Q`, `elasticityBGG_Q`, `divDivBGG_Q`).

**`H⁰` is identified**: `[(σ, φ)] ↦ σ` is a linear isomorphism of `H⁰` onto the affine functions
`a + b ⬝ᵥ x`, the rigid motions `a + b ⨯₃ x` of `Q ⊆ ℝ³` and the fields `a + b x`
(`hessianBGG_Q_homology_zero`, `elasticityBGG_Q_homology_zero`, `divDivBGG_Q_homology_zero`). In
the lowest degree of the rows the cohomology of the BGG complex is the space of the `u ∈ HΛ⁰` with
`d u = S⁰ v` for a closed `v` (`Feec.BGG.HilbertData.homologyIs_lowest`); the closed fields of
degree `0` are the constants (`ker_maximal_zero_eq_span`, from `ℌ⁰(HΛ(Q)) = ℝ · 1`), `S⁰` maps
them to constant `1`-forms, and a `0`-form with constant weak gradient `Σ_c b_c dx_c` is the
affine function `a + b ⬝ᵥ x` (`exists_maximal_eq_sum_dxL2_iff`). So these `u` are the functions
with constant weak gradient (the kernel of the Hessian on `H²(Q)`), the vector fields whose weak
gradient is a constant skew matrix, and those whose weak gradient is a constant multiple of the
identity (`hessian_lowest_iff`, `elasticity_lowest_iff`, `divDiv_lowest_iff`).

## Main results

* `deRham_hasRegularDecomposition_cube`, `finrank_formRow_cohomology`,
  `finrank_vecRow_cohomology`.
* **`hessianBGG_Q`**, **`elasticityBGG_Q`**, **`divDivBGG_Q`**.
* `ker_maximal_zero_eq_span`, `exists_maximal_eq_sum_dxL2_iff`; `hessian_lowest_iff`,
  `elasticity_lowest_iff`, `divDiv_lowest_iff`.
* **`hessianBGG_Q_homology_zero`**, **`elasticityBGG_Q_homology_zero`**,
  **`divDivBGG_Q_homology_zero`**.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §2 (Theorem 3), §4.1, Theorem 6
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1 (closed range, harmonic forms and cohomology)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

namespace Feec.Models.Cube.FormBGG

open MeasureTheory
open Feec.Domain Feec.FiniteElement Feec.HilbertComplex
open Feec.Models.Cube.FEM (cubeDomain isOpen_cubeDomain isBounded_cubeDomain cubeDomain_eq_Q
  oneForm)

variable {n : ℕ}

/-- **The `H¹`-regular decompositions of `HΛ(Q)`** from `0` on, on `cubeDomain n`. -/
theorem deRham_hasRegularDecomposition_cube :
    (deRham ℝ n).HasRegularDecomposition (cubeDomain n) 0 :=
  (cubeDomain_eq_Q n) ▸ Sobolev.deRham_hasRegularDecomposition_Q

instance finiteDimensional_formRow_cohomology (k : ℤ) :
    FiniteDimensional ℝ ((formRow n (isOpen_cubeDomain n)).cohomology k) :=
  ((FEM.complex n).cohomologyEquivHarmonic (FEM.closedRangeAt k)).symm.finiteDimensional

/-- `dim Hᵏ(HΛ(Q)) = [k = 0]`. -/
theorem finrank_formRow_cohomology (k : ℤ) :
    Module.finrank ℝ ((formRow n (isOpen_cubeDomain n)).cohomology k) = if k = 0 then 1 else 0 :=
  FEM.finrank_cohomology k

/-- `dim Hᵏ(HΛ(Q) ⊗ ℝⁿ) = n [k = 0]`. -/
theorem finrank_vecRow_cohomology (k : ℤ) :
    Module.finrank ℝ ((vecRow n (isOpen_cubeDomain n)).cohomology k) = if k = 0 then n else 0 := by
  rw [finrank_pi_cohomology, finrank_formRow_cohomology, Fintype.card_fin]
  split_ifs <;> simp

/-- **The Hessian complex of forms on the cube** `Q = (0, ½)ⁿ` ([ArnoldHu2021], §4.1,
Theorem 6): the BGG complex `bgg 0` of the domain complexes of `HΛ(Q)` over `HΛ(Q) ⊗ ℝⁿ` has
closed range and finite-dimensional cohomology (`Feec.BGG.HilbertData.BGGVerdict`), of dimension
`n + 1` in degree `0` and `0` in the other degrees. -/
theorem hessianBGG_Q (i : ℤ) :
    (hessianFormData (isOpen_cubeDomain n)).BGGVerdict 0 i ∧
      Module.finrank ℝ (((hessianFormData (isOpen_cubeDomain n)).domainData.bgg 0).homology i) =
        if i = 0 then n + 1 else 0 := by
  set D := hessianFormData (isOpen_cubeDomain n)
  have : ∀ k, FiniteDimensional ℝ (D.H.cohomology k) := finiteDimensional_formRow_cohomology
  have : ∀ k, FiniteDimensional ℝ (D.Ht.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow n (isOpen_cubeDomain n)).cohomology k))
  have hS := hessianFormData_antilipschitz (isOpen_cubeDomain n)
  have htop := hessianFormData_regularDecomposition (isOpen_cubeDomain n)
    deRham_hasRegularDecomposition_cube
  refine ⟨D.bggVerdict hS htop i, ?_⟩
  rw [D.finrank_bgg_homology_eq_ite hS htop finrank_formRow_cohomology finrank_vecRow_cohomology,
    Nat.add_comm]

/-- **The elasticity complex of forms on the cube** `Q = (0, ½)³` ([ArnoldHu2021], §4.1,
Theorem 6): the BGG complex `bgg 1` of `HΛ(Q) ⊗ ℝ³` over itself has closed range and
finite-dimensional cohomology, of dimension `6` in degree `0` and `0` in the other degrees. -/
theorem elasticityBGG_Q (i : ℤ) :
    (elasticityFormData (isOpen_cubeDomain 3)).BGGVerdict 1 i ∧
      Module.finrank ℝ (((elasticityFormData (isOpen_cubeDomain 3)).domainData.bgg 1).homology i) =
        if i = 0 then 6 else 0 := by
  set D := elasticityFormData (isOpen_cubeDomain 3)
  have : ∀ k, FiniteDimensional ℝ (D.H.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow 3 (isOpen_cubeDomain 3)).cohomology k))
  have : ∀ k, FiniteDimensional ℝ (D.Ht.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow 3 (isOpen_cubeDomain 3)).cohomology k))
  have hS := elasticityFormData_antilipschitz (isOpen_cubeDomain 3)
  have htop := elasticityFormData_regularDecomposition (isOpen_cubeDomain 3)
    (deRham_hasRegularDecomposition_cube.mono zero_le_one)
  exact ⟨D.bggVerdict hS htop i,
    D.finrank_bgg_homology_eq_ite hS htop finrank_vecRow_cohomology finrank_vecRow_cohomology i⟩

/-- **The div–div complex of forms on the cube** `Q = (0, ½)ⁿ`, `n ≥ 1` ([ArnoldHu2021], §4.1,
Theorem 6): the BGG complex `bgg (n - 1)` of `HΛ(Q) ⊗ ℝⁿ` over `HΛ(Q)` has closed range and
finite-dimensional cohomology, of dimension `n + 1` in degree `0` and `0` in the other degrees. -/
theorem divDivBGG_Q [NeZero n] (i : ℤ) :
    (divDivFormData (isOpen_cubeDomain n)).BGGVerdict ((n : ℤ) - 1) i ∧
      Module.finrank ℝ
        (((divDivFormData (isOpen_cubeDomain n)).domainData.bgg ((n : ℤ) - 1)).homology i) =
          if i = 0 then n + 1 else 0 := by
  set D := divDivFormData (isOpen_cubeDomain n)
  have : ∀ k, FiniteDimensional ℝ (D.Ht.cohomology k) := finiteDimensional_formRow_cohomology
  have : ∀ k, FiniteDimensional ℝ (D.H.cohomology k) := fun k =>
    (inferInstance : FiniteDimensional ℝ ((vecRow n (isOpen_cubeDomain n)).cohomology k))
  have hn := NeZero.pos n
  have hS := divDivFormData_antilipschitz (isOpen_cubeDomain n)
  have htop := divDivFormData_regularDecomposition (isOpen_cubeDomain n)
    ((deRham_hasRegularDecomposition_cube (n := n)).mono (by omega))
  exact ⟨D.bggVerdict hS htop i,
    D.finrank_bgg_homology_eq_ite hS htop finrank_vecRow_cohomology finrank_formRow_cohomology i⟩

/-! ### The cohomology in degree `0`: affine functions, rigid motions, the fields `a + b x` -/

/-- **The closed `0`-forms of `HΛ(Q)` are the constants**: in degree `0` there are no boundaries,
so the cycles are the harmonic forms `ℌ⁰ = ℝ · 1` (`FEM.harmonic_zero_eq_span`). -/
theorem formRow_cycles_zero :
    (formRow n (isOpen_cubeDomain n)).cycles 0 = ℝ ∙ oneForm n := by
  rw [← FEM.harmonic_zero_eq_span, harmonic_eq]
  have : (formRow n (isOpen_cubeDomain n)).boundaries 0 = ⊥ := by
    have := LocalElement.subsingleton_L2F_of_neg (cubeDomain n) (n := n)
      (j := (ComplexShape.up ℤ).prev 0) (by rw [CochainComplex.prev]; norm_num)
    refine eq_bot_iff.2 ?_
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y 0, map_zero]
    exact Submodule.zero_mem _
  rw [this, Submodule.bot_orthogonal_eq_top, inf_top_eq]

/-- **A `0`-form with zero weak gradient on the connected `Q` is constant.** -/
theorem ker_maximal_zero_eq_span :
    ((extDerivOp ℝ n 0).maximal (cubeDomain n)).ker = ℝ ∙ oneForm n := by
  rw [← formRow_cycles_zero,
    (formRow n _).cycles_eq (show (ComplexShape.up ℤ).Rel (0 : ℤ) (0 + 1) from rfl), formRow_d]

/-- `dxₐ ∧ 1 = dxₐ`, the constant `1`-form: its coefficient at `{l}` is `[a = l]`. -/
theorem dxL2_oneForm_apply (a : Fin n) (t : formIdx n (0 + 1)) :
    dxL2 0 a (oneForm n) t = if a ∈ t.1 then oneForm n ⟨∅, by simp⟩ else 0 := by
  rw [dxL2_apply, Fintype.sum_eq_single ⟨∅, by simp⟩ fun r hr => absurd (formIdx_zero_eq r _) hr,
    wsCoeff_eq]
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 (by have := t.2; omega : t.1.card = 1)
  by_cases ha : a ∈ t.1
  · have hal : a = l := by rw [hl, Finset.mem_singleton] at ha; exact ha
    subst hal
    rw [ite_eq_left ⟨ha, by rw [hl, Finset.erase_singleton]⟩, ite_eq_left ha, hl]
    rw [Feec.ExteriorFibre.sgn, Finset.filter_singleton, ite_eq_right (lt_irrefl a)]
    simp
  · rw [ite_eq_right fun h => ha h.1, ite_eq_right ha, zero_smul]

/-- The `0`-form `1` is the constant function `1`. -/
theorem coeFn_oneForm (s : formIdx n 0) :
    ⇑(oneForm n s) =ᵐ[volume.restrict (cubeDomain n)] fun _ => (1 : ℝ) := by
  have hc := DeRhamIdent.memLp_constFun (isOpen_cubeDomain n).measurableSet
    (isBounded_cubeDomain n) (⟨∅, by simp⟩ : formIdx n 0) s
  have e : oneForm n s = hc.toLp _ := rfl
  filter_upwards [hc.coeFn_toLp] with x hx
  rw [e, hx, DeRhamIdent.constFun, ite_eq_left (formIdx_zero_eq _ _)]

/-- **The `0`-forms of `HΛ(Q)` with constant weak gradient are the affine functions**:
`u ∈ HΛ⁰(Q)` with `d u = Σ_c b_c dx_c` iff `u = a + b ⬝ᵥ x` a.e. on `Q` for some `a` (`u - b ⬝ᵥ x`
has zero weak gradient, `ker_maximal_zero_eq_span`). -/
theorem exists_maximal_eq_sum_dxL2_iff (b : Fin n → ℝ) (u : L2F ℝ (cubeDomain n) (formIdx n 0)) :
    (∃ hu : u ∈ ((extDerivOp ℝ n 0).maximal (cubeDomain n)).domain,
      (extDerivOp ℝ n 0).maximal (cubeDomain n) ⟨u, hu⟩ = ∑ c, b c • dxL2 0 c (oneForm n)) ↔
      ∃ a : ℝ, ∀ s, ⇑(u s) =ᵐ[volume.restrict (cubeDomain n)] fun x => a + b ⬝ᵥ x := by
  have hQ := isOpen_cubeDomain n
  have hm := hQ.measurableSet
  have hb := isBounded_cubeDomain n
  set A := (extDerivOp ℝ n 0).maximal (cubeDomain n)
  set w : formIdx n 0 → (Fin n → ℝ) → ℝ := fun _ x => b ⬝ᵥ x
  set L : (Fin n → ℝ) →L[ℝ] ℝ := ∑ c, b c • ContinuousLinearMap.proj c
  have hL : ∀ x, L x = b ⬝ᵥ x := fun x => by simp [L, dotProduct]
  have hws : ∀ s, ContDiff ℝ 1 (w s) := fun s => by
    have : w s = L := funext fun x => (hL x).symm
    rw [this]; exact L.contDiff
  have hw : ∀ s, MemLp (w s) 2 (volume.restrict (cubeDomain n)) := fun s =>
    memLp_of_continuous hm hb (hws s).continuous
  have hdw : ∀ t, MemLp ((extDerivOp ℝ n 0).apply w t) 2 (volume.restrict (cubeDomain n)) :=
    fun t => memLp_of_continuous hm hb
      ((extDerivOp ℝ n 0).continuous_apply (extDerivOp_isOrderLE 0) hws t)
  obtain ⟨hℓ, eℓ⟩ := extDerivOp_smooth_mem_maximal_domain hQ hws hw hdw
  have hdℓ : A ⟨_, hℓ⟩ = ∑ c, b c • dxL2 0 c (oneForm n) := by
    rw [eℓ]
    refine PiLp.ext fun t => ?_
    obtain ⟨l, hl⟩ := Finset.card_eq_one.1 (by have := t.2; omega : t.1.card = 1)
    have hsum : (∑ c, b c • dxL2 0 c (oneForm n)) t = b l • oneForm n ⟨∅, by simp⟩ := by
      rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single l (fun c _ hc => by
        rw [WithLp.ofLp_smul, Pi.smul_apply, dxL2_oneForm_apply, hl,
          ite_eq_right (by simpa using hc), smul_zero]) (by simp)]
      rw [WithLp.ofLp_smul, Pi.smul_apply, dxL2_oneForm_apply, hl,
        ite_eq_left (Finset.mem_singleton_self l)]
    rw [hsum]
    have ht : t = ⟨{l}, by simp⟩ := Subtype.ext hl
    refine Lp.ext ?_
    filter_upwards [(hdw t).coeFn_toLp, Lp.coeFn_smul (b l) (oneForm n ⟨∅, by simp⟩),
      coeFn_oneForm (n := n) ⟨∅, by simp⟩] with x h1 h2 h3
    change ((hdw t).toLp _ : (Fin n → ℝ) → ℝ) x = _
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, mul_one]
    subst ht
    rw [extDerivOp_zero_apply]
    have : w ⟨∅, by simp⟩ = L := funext fun x => (hL x).symm
    rw [this, L.fderiv]
    simp [L, coordDir, Pi.single_apply]
  have h1 : oneForm n ∈ A.ker := by
    rw [ker_maximal_zero_eq_span]; exact Submodule.mem_span_singleton_self _
  obtain ⟨y₁, hy₁, hy₁0⟩ := LinearPMap.mem_ker_iff.1 h1
  constructor
  · rintro ⟨hu, hdu⟩
    have hk : u - toL2F hw ∈ A.ker := LinearPMap.mem_ker_iff.2
      ⟨⟨u, hu⟩ - ⟨_, hℓ⟩, rfl, by rw [A.map_sub, hdu, hdℓ, sub_self]⟩
    rw [ker_maximal_zero_eq_span, Submodule.mem_span_singleton] at hk
    obtain ⟨a, ha⟩ := hk
    refine ⟨a, fun s => ?_⟩
    have hu' : u = a • oneForm n + toL2F hw := by rw [ha, sub_add_cancel]
    filter_upwards [show ⇑(u s) =ᵐ[volume.restrict (cubeDomain n)] _ from by rw [hu'],
      Lp.coeFn_add (a • oneForm n s) (toL2F hw s), Lp.coeFn_smul a (oneForm n s),
      coeFn_oneForm (n := n) s, (hw s).coeFn_toLp] with x h0 h1 h2 h3 h4
    rw [h0]
    change ((a • oneForm n s + toL2F hw s : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x = _
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, smul_eq_mul, mul_one]
    change a + ((hw s).toLp (w s) : (Fin n → ℝ) → ℝ) x = _
    rw [h4]
  · rintro ⟨a, ha⟩
    have hu : u = a • oneForm n + toL2F hw := by
      refine PiLp.ext fun s => Lp.ext ?_
      filter_upwards [ha s, Lp.coeFn_add (a • oneForm n s) (toL2F hw s),
        Lp.coeFn_smul a (oneForm n s), coeFn_oneForm (n := n) s, (hw s).coeFn_toLp]
        with x h0 h1 h2 h3 h4
      rw [h0]
      change _ = ((a • oneForm n s + toL2F hw s : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, smul_eq_mul, mul_one]
      change _ = a + ((hw s).toLp (w s) : (Fin n → ℝ) → ℝ) x
      rw [h4]
    have hmem : u ∈ A.domain := by
      rw [hu, hy₁]; exact A.domain.add_mem (A.domain.smul_mem a y₁.2) hℓ
    refine ⟨hmem, ?_⟩
    have : (⟨u, hmem⟩ : A.domain) = a • y₁ + ⟨_, hℓ⟩ := Subtype.ext (show u = _ by
      rw [hu, hy₁]; rfl)
    rw [this, A.map_add, A.map_smul, hy₁0, smul_zero]
    exact (zero_add _).trans hdℓ

/-- **The closed `0`-forms of `HΛ(Q)` are the constants.** -/
theorem mem_formRow_ker_zero_iff {f : L2F ℝ (cubeDomain n) (formIdx n 0)} :
    f ∈ ((formRow n (isOpen_cubeDomain n)).d 0 (0 + 1)).ker ↔ ∃ c : ℝ, c • oneForm n = f := by
  rw [formRow_d, ker_maximal_zero_eq_span, Submodule.mem_span_singleton]

/-- **The closed vectors of `0`-forms of `HΛ(Q) ⊗ ℝⁿ` are the constant vectors.** -/
theorem mem_vecRow_ker_zero_iff
    {v : PiLp 2 (fun _ : Fin n => L2F ℝ (cubeDomain n) (formIdx n 0))} :
    v ∈ ((vecRow n (isOpen_cubeDomain n)).d 0 (0 + 1)).ker ↔
      ∃ c : Fin n → ℝ, WithLp.toLp 2 (fun a => c a • oneForm n) = v := by
  have hQ := isOpen_cubeDomain n
  constructor
  · intro hv
    obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hv
    have h : ∀ a, ∃ c : ℝ, c • oneForm n =
        (y : PiLp 2 (fun _ : Fin n => L2F ℝ (cubeDomain n) (formIdx n 0))) a := fun a => by
      refine Submodule.mem_span_singleton.1 ?_
      rw [← ker_maximal_zero_eq_span (n := n)]
      refine LinearPMap.mem_ker_iff.2 ⟨⟨_, (mem_vecRow_domain hQ).1 y.2 a⟩, rfl, ?_⟩
      rw [← vecRow_d_apply hQ y a, hy]; rfl
    choose c hc using h
    exact ⟨c, PiLp.ext hc⟩
  · rintro ⟨c, rfl⟩
    have h1 : oneForm n ∈ ((extDerivOp ℝ n 0).maximal (cubeDomain n)).ker := by
      rw [ker_maximal_zero_eq_span]; exact Submodule.mem_span_singleton_self _
    obtain ⟨y₁, hy₁, hy₁0⟩ := LinearPMap.mem_ker_iff.1 h1
    have hmem : (WithLp.toLp 2 (fun a => c a • oneForm n) :
        PiLp 2 (fun _ : Fin n => L2F ℝ (cubeDomain n) (formIdx n 0))) ∈
        ((vecRow n hQ).d 0 (0 + 1)).domain :=
      (mem_vecRow_domain hQ).2 fun a => by
        rw [PiLp.toLp_apply, hy₁]; exact Submodule.smul_mem _ _ y₁.2
    refine LinearPMap.mem_ker_iff.2 ⟨⟨_, hmem⟩, rfl, PiLp.ext fun a => ?_⟩
    rw [vecRow_d_apply hQ]
    have : (⟨_, (mem_vecRow_domain hQ).1 hmem a⟩ :
        ((extDerivOp ℝ n 0).maximal (cubeDomain n)).domain) = c a • y₁ :=
      Subtype.ext (show (c a • oneForm n : L2F ℝ (cubeDomain n) (formIdx n 0)) =
        c a • (y₁ : L2F ℝ (cubeDomain n) (formIdx n 0)) by rw [hy₁])
    rw [this, LinearPMap.map_smul, hy₁0, smul_zero]; rfl

/-- `S v = Σ_c dx_c ∧ v_c` on a constant vector `(b_c)_c` of `0`-forms is `Σ_c b_c dx_c`. -/
theorem wsL2_const (b : Fin n → ℝ) :
    wsL2 (Ω := cubeDomain n) 0 (WithLp.toLp 2 fun c => b c • oneForm n) =
      ∑ c, b c • dxL2 0 c (oneForm n) := by
  rw [wsL2_eq_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [PiLp.toLp_apply, map_smul]

/-- **The lowest cocycles of the Hessian diagram of `Q` are the affine functions**: `u ∈ HΛ⁰(Q)`
with `d u = S v` for a closed (constant) vector `v` iff `u = a + b ⬝ᵥ x`. -/
theorem hessian_lowest_iff (u : L2F ℝ (cubeDomain n) (formIdx n 0)) :
    (∃ hu : u ∈ ((formRow n (isOpen_cubeDomain n)).d 0 (0 + 1)).domain,
      ∃ v ∈ ((vecRow n (isOpen_cubeDomain n)).d 0 (0 + 1)).ker,
        wsL2 0 v = (formRow n (isOpen_cubeDomain n)).d 0 (0 + 1) ⟨u, hu⟩) ↔
      ∃ (a : ℝ) (b : Fin n → ℝ),
        ∀ s, ⇑(u s) =ᵐ[volume.restrict (cubeDomain n)] fun x => a + b ⬝ᵥ x := by
  simp only [mem_vecRow_ker_zero_iff]
  rw [formRow_d]
  constructor
  · rintro ⟨hu, _, ⟨b, rfl⟩, h⟩
    obtain ⟨a, ha⟩ := (exists_maximal_eq_sum_dxL2_iff b u).1 ⟨hu, h.symm.trans (wsL2_const b)⟩
    exact ⟨a, b, ha⟩
  · rintro ⟨a, b, ha⟩
    obtain ⟨hu, h⟩ := (exists_maximal_eq_sum_dxL2_iff b u).2 ⟨a, ha⟩
    exact ⟨hu, _, ⟨b, rfl⟩, (wsL2_const b).trans h.symm⟩

/-- `Σᵢ (r e_c)ᵢ dxᵢ = r dx_c`. -/
theorem sum_single_smul_dxL2 (c : Fin n) (r : ℝ) :
    ∑ i, (r • Pi.single c 1 : Fin n → ℝ) i • dxL2 (Ω := cubeDomain n) 0 i (oneForm n) =
      r • dxL2 0 c (oneForm n) := by
  rw [Finset.sum_eq_single c (fun i _ hi => by simp [hi]) (by simp)]
  simp

/-- **The vectors of `0`-forms of `HΛ(Q) ⊗ ℝⁿ` with constant weak gradients are affine**:
`d uₐ = Σ_c (βₐ)_c dx_c` for every `a` iff `uₐ = αₐ + βₐ ⬝ᵥ x` (`exists_maximal_eq_sum_dxL2_iff`
componentwise). -/
theorem exists_vecRow_d_eq_sum_dxL2_iff (β : Fin n → Fin n → ℝ)
    (u : PiLp 2 (fun _ : Fin n => L2F ℝ (cubeDomain n) (formIdx n 0))) :
    (∃ hu : u ∈ ((vecRow n (isOpen_cubeDomain n)).d 0 (0 + 1)).domain,
      (vecRow n (isOpen_cubeDomain n)).d 0 (0 + 1) ⟨u, hu⟩ =
        WithLp.toLp 2 fun a => ∑ c, β a c • dxL2 0 c (oneForm n)) ↔
      ∃ α : Fin n → ℝ, ∀ a s, ⇑(u a s) =ᵐ[volume.restrict (cubeDomain n)]
        fun x => α a + β a ⬝ᵥ x := by
  have hQ := isOpen_cubeDomain n
  constructor
  · rintro ⟨hu, h⟩
    have : ∀ a, ∃ α : ℝ, ∀ s, ⇑(u a s) =ᵐ[volume.restrict (cubeDomain n)]
        fun x => α + β a ⬝ᵥ x := fun a =>
      (exists_maximal_eq_sum_dxL2_iff (β a) (u a)).1 ⟨(mem_vecRow_domain hQ).1 hu a, by
        rw [← vecRow_d_apply hQ ⟨u, hu⟩ a, h]⟩
    choose α hα using this
    exact ⟨α, hα⟩
  · rintro ⟨α, hα⟩
    have h : ∀ a, ∃ hu : u a ∈ ((extDerivOp ℝ n 0).maximal (cubeDomain n)).domain,
        (extDerivOp ℝ n 0).maximal (cubeDomain n) ⟨u a, hu⟩ = ∑ c, β a c • dxL2 0 c (oneForm n) :=
      fun a => (exists_maximal_eq_sum_dxL2_iff (β a) (u a)).2 ⟨α a, hα a⟩
    have hu : u ∈ ((vecRow n hQ).d 0 (0 + 1)).domain :=
      (mem_vecRow_domain hQ).2 fun a => (h a).1
    exact ⟨hu, PiLp.ext fun a => by rw [vecRow_d_apply hQ]; exact (h a).2⟩

open scoped Matrix in
/-- `(b ⨯₃ x)_c = b_{c+1} x_{c+2} - b_{c+2} x_{c+1}` (indices mod `3`). -/
theorem cross_apply_eq_sub (b x : Fin 3 → ℝ) (c : Fin 3) :
    (b ⨯₃ x) c = b (c + 1) * x (c + 2) - b (c + 2) * x (c + 1) := by
  fin_cases c <;> simp [cross_apply]

open scoped Matrix in
/-- **The lowest cocycles of the elasticity diagram of `Q ⊆ ℝ³` are the rigid motions**: `u ∈ HΛ⁰(Q)
⊗ ℝ³` with `d u = S v` for a closed (constant) vector `v` iff `u = a + b × x`. -/
theorem elasticity_lowest_iff (u : PiLp 2 (fun _ : Fin 3 => L2F ℝ (cubeDomain 3) (formIdx 3 0))) :
    (∃ hu : u ∈ ((vecRow 3 (isOpen_cubeDomain 3)).d 0 (0 + 1)).domain,
      ∃ v ∈ ((vecRow 3 (isOpen_cubeDomain 3)).d 0 (0 + 1)).ker,
        crossL2 0 v = (vecRow 3 (isOpen_cubeDomain 3)).d 0 (0 + 1) ⟨u, hu⟩) ↔
      ∃ a b : Fin 3 → ℝ, ∀ c s, ⇑(u c s) =ᵐ[volume.restrict (cubeDomain 3)]
        fun x => a c + (b ⨯₃ x) c := by
  set β : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ := fun b c =>
    b (c + 1) • Pi.single (c + 2) 1 - b (c + 2) • Pi.single (c + 1) 1
  have hβ : ∀ b c x, β b c ⬝ᵥ x = (b ⨯₃ x) c := fun b c x => by
    rw [cross_apply_eq_sub]
    simp [β, dotProduct, Pi.single_apply, Finset.sum_sub_distrib, sub_mul]
  have hS : ∀ b, crossL2 (Ω := cubeDomain 3) 0 (WithLp.toLp 2 fun c => b c • oneForm 3) =
      WithLp.toLp 2 fun c => ∑ i, β b c i • dxL2 0 i (oneForm 3) := fun b =>
    PiLp.ext fun c => by
      simp only [β, crossL2_apply, map_smul, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      rw [← sum_single_smul_dxL2, ← sum_single_smul_dxL2]
  simp only [mem_vecRow_ker_zero_iff]
  constructor
  · rintro ⟨hu, _, ⟨b, rfl⟩, h⟩
    obtain ⟨α, hα⟩ := (exists_vecRow_d_eq_sum_dxL2_iff (β b) u).1 ⟨hu, h.symm.trans (hS b)⟩
    exact ⟨α, b, fun c s => by simpa only [hβ] using hα c s⟩
  · rintro ⟨a, b, ha⟩
    obtain ⟨hu, h⟩ := (exists_vecRow_d_eq_sum_dxL2_iff (β b) u).2
      ⟨a, fun c s => by simpa only [hβ] using ha c s⟩
    exact ⟨hu, _, ⟨b, rfl⟩, (hS b).trans h.symm⟩

/-- **The lowest cocycles of the div–div diagram of `Q` are the fields `a + b x`**:
`u ∈ HΛ⁰(Q) ⊗ ℝⁿ` with `d u = S f` for a closed (constant) `0`-form `f` iff `u = a + b x`. -/
theorem divDiv_lowest_iff (u : PiLp 2 (fun _ : Fin n => L2F ℝ (cubeDomain n) (formIdx n 0))) :
    (∃ hu : u ∈ ((vecRow n (isOpen_cubeDomain n)).d 0 (0 + 1)).domain,
      ∃ f ∈ ((formRow n (isOpen_cubeDomain n)).d 0 (0 + 1)).ker,
        dxVecL2 0 f = (vecRow n (isOpen_cubeDomain n)).d 0 (0 + 1) ⟨u, hu⟩) ↔
      ∃ (a : Fin n → ℝ) (b : ℝ), ∀ c s, ⇑(u c s) =ᵐ[volume.restrict (cubeDomain n)]
        fun x => a c + b * x c := by
  set β : ℝ → Fin n → Fin n → ℝ := fun b c => b • Pi.single c 1
  have hβ : ∀ b c x, β b c ⬝ᵥ x = b * x c := fun b c x => by
    simp [β, dotProduct, Pi.single_apply]
  have hS : ∀ b, dxVecL2 (Ω := cubeDomain n) 0 (b • oneForm n) =
      WithLp.toLp 2 fun c => ∑ i, β b c i • dxL2 0 i (oneForm n) := fun b =>
    PiLp.ext fun c => by
      rw [dxVecL2_apply, PiLp.toLp_apply, sum_single_smul_dxL2, map_smul]
  simp only [mem_formRow_ker_zero_iff]
  constructor
  · rintro ⟨hu, _, ⟨b, rfl⟩, h⟩
    obtain ⟨α, hα⟩ := (exists_vecRow_d_eq_sum_dxL2_iff (β b) u).1 ⟨hu, h.symm.trans (hS b)⟩
    exact ⟨α, b, fun c s => by simpa only [hβ] using hα c s⟩
  · rintro ⟨a, b, ha⟩
    obtain ⟨hu, h⟩ := (exists_vecRow_d_eq_sum_dxL2_iff (β b) u).2
      ⟨a, fun c s => by simpa only [hβ] using ha c s⟩
    exact ⟨hu, _, ⟨b, rfl⟩, (hS b).trans h.symm⟩

/-- **`H⁰` of the Hessian complex of forms on `Q = (0, ½)ⁿ` is the space of affine functions**:
`[(σ, φ)] ↦ σ` is a linear isomorphism of `H⁰(bgg 0)` onto `{a + b ⬝ᵥ x}`. -/
theorem hessianBGG_Q_homology_zero :
    (hessianFormData (isOpen_cubeDomain n)).HomologyIs 0 0
      {u | ∃ (a : ℝ) (b : Fin n → ℝ),
        ∀ s, ⇑(u s) =ᵐ[volume.restrict (cubeDomain n)] fun x => a + b ⬝ᵥ x} := by
  have := LocalElement.subsingleton_L2F_of_neg (cubeDomain n) (n := n) (j := 0 - 1) (by norm_num)
  have := subsingleton_vec_formIdx (Ω := cubeDomain n) (n := n) (k := 0 - 1) (by norm_num)
  have h := (hessianFormData (isOpen_cubeDomain n)).homologyIs_lowest le_rfl
    (fun _ =>
      ((hessianFormData_antilipschitz (isOpen_cubeDomain n)) 0 le_rfl).choose_spec.injective)
    (fun h => absurd h (by norm_num))
  convert h using 1
  ext u
  rw [Set.mem_ofPred_eq, ← hessian_lowest_iff, Set.mem_ofPred_eq]
  simp only [hessianFormData_S]
  rfl

open scoped Matrix in
/-- **`H⁰` of the elasticity complex of forms on `Q = (0, ½)³` is the space of rigid motions**:
`[(σ, φ)] ↦ σ` is a linear isomorphism of `H⁰(bgg 1)` onto `{a + b ⨯₃ x}`. -/
theorem elasticityBGG_Q_homology_zero :
    (elasticityFormData (isOpen_cubeDomain 3)).HomologyIs 1 0
      {u | ∃ a b : Fin 3 → ℝ,
        ∀ c s, ⇑(u c s) =ᵐ[volume.restrict (cubeDomain 3)] fun x => a c + (b ⨯₃ x) c} := by
  have := subsingleton_vec_formIdx (Ω := cubeDomain 3) (n := 3) (k := 0 - 1) (by norm_num)
  have h := (elasticityFormData (isOpen_cubeDomain 3)).homologyIs_lowest (i := 0) (J := 1)
    zero_le_one (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
  convert h using 1
  ext u
  rw [Set.mem_ofPred_eq, ← elasticity_lowest_iff, Set.mem_ofPred_eq]
  simp only [elasticityFormData_S]
  rfl

/-- **`H⁰` of the div–div complex of forms on `Q = (0, ½)ⁿ`, `n ≥ 1`, is the space of the fields
`a + b x`**: `[(σ, φ)] ↦ σ` is a linear isomorphism of `H⁰(bgg (n - 1))` onto `{a + b x}`. -/
theorem divDivBGG_Q_homology_zero [NeZero n] :
    (divDivFormData (isOpen_cubeDomain n)).HomologyIs ((n : ℤ) - 1) 0
      {u | ∃ (a : Fin n → ℝ) (b : ℝ),
        ∀ c s, ⇑(u c s) =ᵐ[volume.restrict (cubeDomain n)] fun x => a c + b * x c} := by
  have := LocalElement.subsingleton_L2F_of_neg (cubeDomain n) (n := n) (j := 0 - 1) (by norm_num)
  have := subsingleton_vec_formIdx (Ω := cubeDomain n) (n := n) (k := 0 - 1) (by norm_num)
  have hn := NeZero.pos n
  have hS := divDivFormData_antilipschitz (isOpen_cubeDomain n)
  have h := (divDivFormData (isOpen_cubeDomain n)).homologyIs_lowest (i := 0)
    (J := (n : ℤ) - 1) (by omega)
    (fun _ => (hS 0 (by omega)).choose_spec.injective)
    (fun h => (hS (0 + 1) (by omega)).choose_spec.injective)
  convert h using 1
  ext u
  rw [Set.mem_ofPred_eq, ← divDiv_lowest_iff, Set.mem_ofPred_eq]
  simp only [divDivFormData_S]
  rfl

end Feec.Models.Cube.FormBGG
