module

public import Solution
public import Feec.Models.Cube.TangentialH1

/-!
# The `C²` rates of the thesis are corollaries of the `H¹` rates

[QuennevilleBelair2015] states the rates of the method on the cube `Q = (0, ½)³` for states `C²`
up to `∂Q` with vanishing tangential traces: the classes `IsTangentialC2` and `IsRegularState`
below, those of the `C²` clauses of the former statement of this entry, verbatim.
`IsTangentialC2 j L` is `Feec`'s class `Feec.Models.Cube.FEM.IsCsFormTr 0 j L`
(`isTangentialC2_iff`), which lies, with the minimal exterior derivative, in the `H¹` class of
the challenge with bound `c L`, `c ≥ 1` universal (`exists_isSobolevForm_of_isTangentialC2`, from
`Feec.Models.Cube.FEM.IsCsFormTr.exists_h1Data`). Hence, on every family of discretizations of
`bggData Q`, the `H¹` static and wave clauses of `FEEC.weakSymmetry_electric` with a constant `K`
imply the former `C²` clauses with the constant `c K` (`c2_rates_of_h1_rates`), and the
discretizations of `FEEC.weakSymmetry_electric` satisfy the former `C²` clauses
(`weakSymmetry_electric_c2`): the challenge states the `H¹` rates only. The former non-vacuity
statement, with nontrivial solutions meeting the hypotheses of both the `C²` and the `H¹` clauses,
holds verbatim (`weakSymmetry_electric_nonvacuous_c2`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 5.5, §6.3
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set Filter

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.ExteriorFibre

variable {n : ℕ}

/-- `x ∈ L²(Q; Λʲ)` on the cube `Q = (0, ½)ⁿ` is (almost everywhere) a `C²` form `w` on `ℝⁿ` of
degree `j` whose **tangential components vanish on `∂Q`** (`(w y)_t = 0` for `y ∈ cl Q` on a face
`y_i ∈ {0, ½}` with `i ∉ t`; no condition on the normal components), the values and first
derivatives of `w` and `dw` being bounded by `L` on `cl Q`. -/
def IsTangentialC2 (j : ℤ) (L : ℝ) (x : L2Form (cube n) j) : Prop :=
  ∃ w : FormField n, ContDiff ℝ 2 w ∧ (∀ y (t : Finset (Fin n)), (t.card : ℤ) ≠ j → w y t = 0) ∧
    (∀ y ∈ closure (cube n), ∀ (i : Fin n) (t : Finset (Fin n)), i ∉ t →
      (y i = 0 ∨ y i = 1 / 2) → w y t = 0) ∧
    (∀ m ≤ 1, ∀ y ∈ closure (cube n),
      ‖iteratedFDeriv ℝ m w y‖ ≤ L ∧ ‖iteratedFDeriv ℝ m (extDeriv w) y‖ ≤ L) ∧
    ∀ t : FormIdx n j, ⇑(x t) =ᵐ[volume.restrict (cube n)] fun y => w y t.1

/-- A state `(σ, φ, u, M, ρ)` of the cube is **regular with bound `L`**: all components are
`IsTangentialC2` with bound `L`. -/
def IsRegularState (L : ℝ) (σ : L2Form (cube 3) 0) (φ : L2Vec (cube 3) 0) (u : L2Vec (cube 3) 1)
    (M : L2Form (cube 3) 2) (ρ : L2Vec (cube 3) 2) : Prop :=
  IsTangentialC2 0 L σ ∧ (∀ a, IsTangentialC2 0 L (φ a)) ∧ (∀ a, IsTangentialC2 1 L (u a)) ∧
    IsTangentialC2 2 L M ∧ ∀ a, IsTangentialC2 2 L (ρ a)

theorem isDeg_iff {j : ℤ} {k : ℕ} (hk : (k : ℤ) = j) (w : FormField n) :
    (∀ y, IsDeg k (w y)) ↔ ∀ y (t : Finset (Fin n)), (t.card : ℤ) ≠ j → w y t = 0 := by
  subst hk
  exact forall_congr' fun y => forall_congr' fun t => by
    rw [Ne, Ne, Nat.cast_inj]

theorem eq_formL2_iff {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    {j : ℤ} (x : L2Form Ω j) (w : contForms n) :
    x = formL2 hΩ hb j w ↔ ∀ t : FormIdx n j,
      ⇑(x t) =ᵐ[volume.restrict Ω] fun y => (w : FormField n) y t.1 := by
  constructor
  · rintro rfl t; exact coeFn_formL2 hΩ hb j w t
  · intro h
    refine PiLp.ext fun t => Lp.ext ?_
    exact (h t).trans (coeFn_formL2 hΩ hb j w t).symm

/-- **The tangential `C²` class is `Feec`'s `IsCsFormTr 0`** on the cube, in the degrees
`j ≥ 0`. -/
theorem isTangentialC2_iff {j : ℤ} (hj : 0 ≤ j) (L : ℝ) (x : L2Form (cube n) j) :
    IsTangentialC2 j L x ↔ Feec.Models.Cube.FEM.IsCsFormTr 0 j L x := by
  unfold IsTangentialC2 Feec.Models.Cube.FEM.IsCsFormTr
  have hj' : ¬ j < 0 := not_lt.2 hj
  simp only [hj', false_or]
  have h2 : ((0 + 2 : ℕ) : WithTop ℕ∞) = 2 := rfl
  constructor
  · rintro ⟨w, hw, hdeg, htan, hL, hx⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j := ⟨j.toNat, Int.toNat_of_nonneg hj⟩
    have hw' : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) w := by rw [h2]; exact hw
    exact ⟨k, hk, w, hw', (isDeg_iff hk w).2 hdeg, htan, fun i hi y hy => hL i hi y hy,
      (eq_formL2_iff _ _ x ⟨w, hw'.continuous⟩).2 hx⟩
  · rintro ⟨k, hk, w, hw, hdeg, htan, hL, hx⟩
    exact ⟨w, by rw [← h2]; exact hw, (isDeg_iff hk w).1 hdeg, htan, fun i hi y hy => hL i hi y hy,
      (eq_formL2_iff _ _ x _).1 hx⟩

open Feec.Models.Cube.FEM in
/-- `IsCsFormTr 0 k L` gives the `H¹(Q)` class with bound `16 c L`, also for `d̊`. -/
theorem exists_isSobolevForm_of_isCsFormTr : ∃ c : ℝ, 0 ≤ c ∧ ∀ {k : ℕ} {L : ℝ}
    {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)}, IsCsFormTr 0 k L x →
    IsSobolevForm (cube 3) 1 k (c * L) x ∧ x ∈ (dMin (cube 3) k).domain ∧
      ∀ h : x ∈ (dMin (cube 3) k).domain,
        IsSobolevForm (cube 3) 1 (k + 1) (c * L) (dMin (cube 3) k ⟨x, h⟩) := by
  obtain ⟨c, hc, H⟩ := IsCsFormTr.exists_h1Data 3
  refine ⟨16 * c, by positivity, fun {k L x} hx => ?_⟩
  obtain ⟨⟨h0⟩, h1⟩ := H hx
  have hm := hx.mem_domain
  rw [deRham_minimalComplex_d] at hm
  have e : (dMin (cube 3) k : L2Form (cube 3) k →ₗ.[ℝ] L2Form (cube 3) (k + 1)) =
      (complexMin 3).d k (k + 1) := by
    rw [dMin_eq, deRham_minimalComplex_d]; rfl
  refine ⟨mul_assoc 16 c L ▸ isSobolevForm_of_h1Data h0, by rw [dMin_eq]; exact hm, fun h => ?_⟩
  have h' : x ∈ ((complexMin 3).d k (k + 1)).domain := e ▸ h
  obtain ⟨hd⟩ := h1 h'
  have e2 : dMin (cube 3) k ⟨x, h⟩ = (complexMin 3).d k (k + 1) ⟨x, h'⟩ :=
    LinearPMap.apply_of_eq' e ⟨x, h⟩
  rw [e2]
  exact mul_assoc 16 c L ▸ isSobolevForm_of_h1Data hd

/-- The bound of a tangential `C²` form on the cube is nonnegative. -/
theorem IsTangentialC2.nonneg {j : ℤ} {L : ℝ} {x : L2Form (cube 3) j}
    (h : IsTangentialC2 j L x) : 0 ≤ L := by
  obtain ⟨w, -, -, -, hL, -⟩ := h
  have hy : (fun _ => (1 / 4 : ℝ)) ∈ closure (cube 3) :=
    subset_closure (Set.mem_univ_pi.2 fun _ => ⟨by norm_num, by norm_num⟩)
  exact (norm_nonneg _).trans (hL 0 (Nat.zero_le _) _ hy).1

/-- **The tangential `C²` class lies in the `H¹` class with bound `c L`**, also for `d̊`, `c ≥ 1`
universal (from `Feec.Models.Cube.FEM.IsCsFormTr.exists_h1Data`). -/
theorem exists_isSobolevForm_of_isTangentialC2 : ∃ c : ℝ, 1 ≤ c ∧ ∀ {k : ℕ} {L : ℝ}
    {x : L2Form (cube 3) k}, IsTangentialC2 k L x →
    IsSobolevForm (cube 3) 1 k (c * L) x ∧ x ∈ (dMin (cube 3) k).domain ∧
      ∀ h : x ∈ (dMin (cube 3) k).domain,
        IsSobolevForm (cube 3) 1 (k + 1) (c * L) (dMin (cube 3) k ⟨x, h⟩) := by
  obtain ⟨c, hc, H⟩ := exists_isSobolevForm_of_isCsFormTr
  refine ⟨max c 1, le_max_right _ _, fun {k L x} hx => ?_⟩
  have hL0 := hx.nonneg
  have hm : c * L ≤ max c 1 * L := mul_le_mul_of_nonneg_right (le_max_left _ _) hL0
  obtain ⟨h0, hd, h1⟩ := H ((isTangentialC2_iff (Nat.cast_nonneg k) L x).1 hx)
  exact ⟨isSobolevForm_mono (mul_nonneg hc hL0) hm h0, hd,
    fun h => isSobolevForm_mono (mul_nonneg hc hL0) hm (h1 h)⟩

/-- **A regular state is an `H¹` state** with bound `c L`. -/
theorem isH1State_of_isRegularState {c L : ℝ} (H : ∀ {k : ℕ} {L : ℝ} {x : L2Form (cube 3) k},
      IsTangentialC2 k L x → IsSobolevForm (cube 3) 1 k (c * L) x ∧
        x ∈ (dMin (cube 3) k).domain ∧ ∀ h : x ∈ (dMin (cube 3) k).domain,
          IsSobolevForm (cube 3) 1 (k + 1) (c * L) (dMin (cube 3) k ⟨x, h⟩))
    {σ : L2Form (cube 3) 0} {φ : L2Vec (cube 3) 0} {u : L2Vec (cube 3) 1} {M : L2Form (cube 3) 2}
    {ρ : L2Vec (cube 3) 2} (h : IsRegularState L σ φ u M ρ) : IsH1State (c * L) σ φ u M ρ := by
  obtain ⟨hσ, hφ, hu, hM, hρ⟩ := h
  exact ⟨(H (k := 0) hσ).1, fun a ha => (H (k := 0) (hφ a)).2.2 ha,
    fun a => (H (k := 1) (hu a)).1, fun a ha => (H (k := 1) (hu a)).2.2 ha,
    (H (k := 2) hM).1, fun a => (H (k := 2) (hρ a)).1, (H (k := 2) hM).2.1,
    fun a => (H (k := 2) (hρ a)).2.1⟩

/-- **The `C²` rate clauses follow from the `H¹` ones**, with the same quantifiers: for every
family `Q_N` of discretizations of `bggData Q` on meshes `𝒯_N` and every `K`, if the `H¹` static
and wave clauses of `FEEC.weakSymmetry_electric` hold with `K`, the `C²` static and wave clauses
of the former statement (the rates of [QuennevilleBelair2015], Thm 5.5, §6.3) hold on the same
discretizations with `c K`, `c` universal. -/
theorem c2_rates_of_h1_rates : ∃ c : ℝ, ∀ (𝒯 : ℕ → SimplicialMesh 3)
    (Q : ℕ → (bggData (cube 3)).Discretization) (K : ℝ),
    (∀ N F σ φ u lam σh φh uh lamh L, (bggData (cube 3)).IsSolution F σ φ u lam →
      IsSobolevForm (cube 3) 1 0 L (σ : L2Form (cube 3) 0) →
      (∀ a, IsSobolevForm (cube 3) 1 0 L ((φ : L2Vec (cube 3) 0) a)) →
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((bggData (cube 3)).dt0 φ a)) →
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((u : L2Vec (cube 3) 1) a)) →
      (∀ a, IsSobolevForm (cube 3) 1 2 L ((bggData (cube 3)).dt1 u a)) → ‖lam‖ ≤ L →
      (Q N).IsDiscreteSolution F σh φh uh lamh →
      (Q N).errorSq σ σh φ φh u uh ≤ (K * L * meshSize (𝒯 N)) ^ 2) →
    (∀ N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, 0 < T → ContinuousOn f (Icc 0 T) →
      (bggData (cube 3)).IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' →
      (∀ t ∈ Icc 0 T, IsH1State L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsH1State L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) →
      ∃ Uh ∈ (Q N).trajectories T f, ∀ t ∈ Icc 0 T,
        stateNorm (((σ t : L2Form (cube 3) 0), (u t : L2Vec (cube 3) 1), M t, ρ t) - Uh t) ≤
          K * L * (1 + t) * meshSize (𝒯 N)) →
    (∀ N F σ φ u lam σh φh uh lamh L, (bggData (cube 3)).IsSolution F σ φ u lam →
      IsTangentialC2 0 L (σ : L2Form (cube 3) 0) →
      (∀ a, IsTangentialC2 0 L ((φ : L2Vec (cube 3) 0) a)) →
      (∀ a, IsTangentialC2 1 L ((u : L2Vec (cube 3) 1) a)) → ‖lam‖ ≤ L →
      (Q N).IsDiscreteSolution F σh φh uh lamh →
      (Q N).errorSq σ σh φ φh u uh ≤ (c * K * L * meshSize (𝒯 N)) ^ 2) ∧
    ∀ N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, 0 < T → ContinuousOn f (Icc 0 T) →
      (bggData (cube 3)).IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' →
      (∀ t ∈ Icc 0 T, IsRegularState L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsRegularState L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) →
      ∃ σh φh uh Mh ρh lamh, (Q N).IsDiscreteWave T f σh φh uh Mh ρh lamh ∧
        ∀ t ∈ Icc 0 T, √(‖(σ t : L2Form (cube 3) 0) - σh t‖ ^ 2 +
          ‖(u t : L2Vec (cube 3) 1) - uh t‖ ^ 2 + ‖M t - Mh t‖ ^ 2 + ‖ρ t - ρh t‖ ^ 2) ≤
            c * K * L * (1 + t) * meshSize (𝒯 N) := by
  obtain ⟨c, hc1, H⟩ := exists_isSobolevForm_of_isTangentialC2
  refine ⟨c, fun 𝒯 Q K hs hw => ⟨fun N F σ φ u lam σh φh uh lamh L hsol hσ hφ hu hl hd => ?_,
    fun N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L hT hf hws hreg => ?_⟩⟩
  · have hL0 : 0 ≤ L := (norm_nonneg _).trans hl
    have e := hs N F σ φ u lam σh φh uh lamh (c * L) hsol (H (k := 0) hσ).1
      (fun a => (H (k := 0) (hφ a)).1) (fun a => (H (k := 0) (hφ a)).2.2 (φ.2 a))
      (fun a => (H (k := 1) (hu a)).1) (fun a => (H (k := 1) (hu a)).2.2 (u.2 a))
      (hl.trans (le_mul_of_one_le_left hL0 hc1)) hd
    exact e.trans_eq (by ring)
  · have hL0 : 0 ≤ L := (norm_nonneg _).trans (hreg 0 ⟨le_rfl, hT.le⟩).2.2.1
    obtain ⟨Uh, ⟨σh, φh, uh, Mh, ρh, lamh, hW, hU⟩, hb⟩ :=
      hw N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' (c * L) hT hf hws fun t ht =>
        ⟨isH1State_of_isRegularState H (hreg t ht).1, isH1State_of_isRegularState H (hreg t ht).2.1,
          (hreg t ht).2.2.1.trans (le_mul_of_one_le_left hL0 hc1),
          (hreg t ht).2.2.2.trans (le_mul_of_one_le_left hL0 hc1)⟩
    refine ⟨σh, φh, uh, Mh, ρh, lamh, hW, fun t ht => ?_⟩
    have e := hb t ht
    rw [hU t] at e
    simp only [stateNorm, Prod.fst_sub, Prod.snd_sub] at e
    exact e.trans_eq (by ring)

/-- **`FEEC.weakSymmetry_electric` gives the `C²` rates of [QuennevilleBelair2015]**: its
discretizations satisfy the `C²` static and wave clauses of the former statement, with one
constant. -/
theorem weakSymmetry_electric_c2 : ∃ (𝒯 : ℕ → SimplicialMesh 3)
    (Q : ℕ → (bggData (cube 3)).Discretization) (C K : ℝ),
    IsTable51 𝒯 Q C Finset.univ (fun _ => Finset.univ) ∧
    (∀ N F σ φ u lam σh φh uh lamh L, (bggData (cube 3)).IsSolution F σ φ u lam →
      IsTangentialC2 0 L (σ : L2Form (cube 3) 0) →
      (∀ a, IsTangentialC2 0 L ((φ : L2Vec (cube 3) 0) a)) →
      (∀ a, IsTangentialC2 1 L ((u : L2Vec (cube 3) 1) a)) → ‖lam‖ ≤ L →
      (Q N).IsDiscreteSolution F σh φh uh lamh →
      (Q N).errorSq σ σh φ φh u uh ≤ (K * L * meshSize (𝒯 N)) ^ 2) ∧
    ∀ N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, 0 < T → ContinuousOn f (Icc 0 T) →
      (bggData (cube 3)).IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' →
      (∀ t ∈ Icc 0 T, IsRegularState L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsRegularState L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) →
      ∃ σh φh uh Mh ρh lamh, (Q N).IsDiscreteWave T f σh φh uh Mh ρh lamh ∧
        ∀ t ∈ Icc 0 T, √(‖(σ t : L2Form (cube 3) 0) - σh t‖ ^ 2 +
          ‖(u t : L2Vec (cube 3) 1) - uh t‖ ^ 2 + ‖M t - Mh t‖ ^ 2 + ‖ρ t - ρh t‖ ^ 2) ≤
            K * L * (1 + t) * meshSize (𝒯 N) := by
  obtain ⟨𝒯, Q, C, K, h51, -, -, -, -, -, hs, hw, -⟩ := weakSymmetry_electric
  obtain ⟨c, hc⟩ := c2_rates_of_h1_rates
  exact ⟨𝒯, Q, C, c * K, h51, hc 𝒯 Q K hs hw⟩

section Nonvacuous

open Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

/-- `Feec`'s class `IsSmoothStateTr` of states of the cube is the regular class. -/
theorem isRegularState_of_isSmoothStateTr {L : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2}
    {ρ : Wv W2} (h : IsSmoothStateTr L σ φ u M ρ) :
    IsRegularState L (σ : W0) (incl0 φ) (incl1 u) M ρ :=
  ⟨(isTangentialC2_iff le_rfl L _).2 h.1, fun a => (isTangentialC2_iff le_rfl L _).2 (h.2.1 a),
    fun a => (isTangentialC2_iff zero_le_one L _).2 (h.2.2.1 a),
    (isTangentialC2_iff zero_le_two L _).2 h.2.2.2.1,
    fun a => (isTangentialC2_iff zero_le_two L _).2 (h.2.2.2.2 a)⟩

/-- **The former non-vacuity statement, with its `C²` classes**, verbatim: nontrivial solutions of
(5.3) and (6.2) on the cube meet the hypotheses of both the `C²` clauses of the former statement
(`IsTangentialC2`, `IsRegularState`) and the `H¹` clauses of `FEEC.weakSymmetry_electric`. -/
theorem weakSymmetry_electric_nonvacuous_c2 :
    (∃ F σ φ u lam L, (bggData (cube 3)).IsSolution F σ φ u lam ∧
      (σ : L2Form (cube 3) 0) ≠ 0 ∧ (φ : L2Vec (cube 3) 0) ≠ 0 ∧ (u : L2Vec (cube 3) 1) ≠ 0 ∧
      lam ≠ 0 ∧ IsTangentialC2 0 L (σ : L2Form (cube 3) 0) ∧
      (∀ a, IsTangentialC2 0 L ((φ : L2Vec (cube 3) 0) a)) ∧
      (∀ a, IsTangentialC2 1 L ((u : L2Vec (cube 3) 1) a)) ∧ ‖lam‖ ≤ L ∧
      IsSobolevForm (cube 3) 1 0 L (σ : L2Form (cube 3) 0) ∧
      (∀ a, IsSobolevForm (cube 3) 1 0 L ((φ : L2Vec (cube 3) 0) a)) ∧
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((bggData (cube 3)).dt0 φ a)) ∧
      (∀ a, IsSobolevForm (cube 3) 1 1 L ((u : L2Vec (cube 3) 1) a)) ∧
      ∀ a, IsSobolevForm (cube 3) 1 2 L ((bggData (cube 3)).dt1 u a)) ∧
    ∀ T, 0 < T → ∃ f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, ContinuousOn f (Icc 0 T) ∧
      (bggData (cube 3)).IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' ∧
      (∀ t ∈ Icc 0 T, IsRegularState L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsRegularState L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧
        IsH1State L (σ t) (φ t) (u t) (M t) (ρ t) ∧
        IsH1State L (σ' t) (φ' t) (u' t) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧ ‖lam' t‖ ≤ L) ∧
      (∀ t, (u t : L2Vec (cube 3) 1) ≠ 0) ∧
      ∀ t ∈ Ioc 0 T, (σ t : L2Form (cube 3) 0) ≠ 0 ∧ (φ t : L2Vec (cube 3) 0) ≠ 0 := by
  rw [bggData_cube_eq]
  obtain ⟨L, hs, h1, h2, h3, h4, c1, c2, c3, c4⟩ := cube_static_nonvacuous
  obtain ⟨L₁, hL₁, s1, s2, s3, s4, s5⟩ := cube_static_h1
  have m := fun {j : ℤ} {x : L2Form (cube 3) j} (h : IsSobolevForm (cube 3) 1 j L₁ x) =>
    isSobolevForm_mono hL₁ (le_max_right L L₁) h
  refine ⟨⟨_, _, _, _, _, max L L₁, hs, h1, h2, h3, h4,
    (isTangentialC2_iff le_rfl _ _).2 (c1.mono (le_max_left _ _)),
    fun a => (isTangentialC2_iff le_rfl _ _).2 ((c2 a).mono (le_max_left _ _)),
    fun a => (isTangentialC2_iff zero_le_one _ _).2 ((c3 a).mono (le_max_left _ _)),
    c4.trans (le_max_left _ _), m s1, fun a => m (s2 a), fun a => m (s3 a), fun a => m (s4 a),
    fun a => m (s5 a)⟩, fun T hT => ?_⟩
  obtain ⟨L', hf, hw, hreg, hu, hne⟩ := cube_wave_nonvacuous hT
  obtain ⟨L₂, hL₂, hH⟩ := cube_wave_h1 T
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, max L' L₂, hf, hw, fun t ht =>
    ⟨isRegularState_of_isSmoothStateTr ((hreg t ht).1.mono (le_max_left _ _)),
      isRegularState_of_isSmoothStateTr ((hreg t ht).2.1.mono (le_max_left _ _)),
      (hH t ht).1.mono hL₂ (le_max_right _ _), (hH t ht).2.mono hL₂ (le_max_right _ _),
      (hreg t ht).2.2.1.trans (le_max_left _ _), (hreg t ht).2.2.2.trans (le_max_left _ _)⟩,
    hu, hne⟩

end Nonvacuous

end FEEC
