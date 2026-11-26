module

public import Feec.Models.Cube.WhitneyApprox

/-!
# `O(h)` approximation of smooth forms by the Whitney forms of the cube

On the Freudenthal meshes of `Q = (0, ½)ⁿ`, `C²` forms are approximated at rate `h_N` by the
Whitney forms ([Arnold2018], Ch. 7), so the semi-discrete Hodge wave equation converges at rate
`h_N` for smooth solutions ([QuennevilleBelair2015], Thm 4.14).

## Main results

* `FEM.IsC2Form.exists_mem_whitney_le`: the degreewise interpolation error `B_j L h_N`.
* `FEM.IsC2FormMin.exists_mem_whitneyMin_le`: the same with vanishing boundary DOFs.
* `FEM.norm_sub_le_meshSize_window_smooth`: `O(h)` convergence of the Hodge wave equation.
* `FEM.norm_sub_le_meshSize_windowMin_smooth`: the same in `H̊Λ(Q)` for forms vanishing outside `Q`.

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.ExteriorFibre

variable {n : ℕ}

/-- `x` is a `C²` `j`-form whose derivative and that of `dx` are bounded by `L` on `cl Q`. -/
def IsC2Form (j : ℤ) (L : ℝ) (x : L2F ℝ (cubeDomain n) (formIdx n j)) : Prop :=
  j < 0 ∨ ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n, ∃ hw : ContDiff ℝ 2 w, (∀ y, IsDeg k (w y)) ∧
    (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L) ∧
    (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ (extDeriv w) y‖ ≤ L) ∧
    x = formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j ⟨w, hw.continuous⟩

variable (n) in
/-- The constant `B_j = A_j + A_{j+1}` of the graph-norm interpolation error in degree `j`. -/
def interpBound (j : ℤ) : ℝ := interpConst n j.toNat + interpConst n (j.toNat + 1)

variable (n) in
theorem interpBound_nonneg (j : ℤ) : 0 ≤ interpBound n j :=
  add_nonneg (interpConst_nonneg n _) (interpConst_nonneg n _)

theorem IsC2Form.mono {j : ℤ} {L L' : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)}
    (hx : IsC2Form j L x) (hLL' : L ≤ L') : IsC2Form j L' x := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, hL, hL', he⟩
  · exact Or.inl hj
  · exact Or.inr ⟨k, hk, w, hw, hdeg, fun y hy => (hL y hy).trans hLL',
      fun y hy => (hL' y hy).trans hLL', he⟩

variable [NeZero n]

/-- **Degreewise interpolation error for `C²` forms**: `‖x - v‖, ‖d (x - v)‖ ≤ B_j L h_N`. -/
theorem IsC2Form.exists_mem_whitney_le {j : ℤ} {L : ℝ} {x : L2F ℝ (cubeDomain n) (formIdx n j)}
    (hx : IsC2Form j L x) (hL0 : 0 ≤ L) (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (whitney n N).V j, ‖x - v‖ ≤ interpBound n j * L * meshSize N ∧
      ∀ j' (hxj : x ∈ ((complex n).d j j').domain),
        ‖(complex n).d j j' ⟨x - v, Submodule.sub_mem _ hxj ((whitney n N).le_domain j j' hv)⟩‖ ≤
          interpBound n j * L * meshSize N := by
  have hB0 := mul_nonneg (mul_nonneg (interpBound_nonneg n j) hL0) (meshSize_pos N).le
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hL, hL', rfl⟩
  · have := LocalElement.subsingleton_L2F_of_neg (cubeDomain n) (n := n) hj
    exact (whitney n N).exists_mem_le_of_subsingleton hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := FEM.exists_mem_whitney_le N k hw hL0 hL0 hL hL'
  obtain ⟨hdom, hval⟩ := formL2_mem_domain k (hw.of_le (by norm_num)) hdeg
  have hh := (meshSize_pos N).le
  have hA0 := mul_nonneg (interpConst_nonneg n k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (interpConst_nonneg n (k + 1)) (mul_nonneg hh hL0)
  have e : interpBound n k * L * meshSize N =
      interpConst n k * (meshSize N * L) + interpConst n (k + 1) * (meshSize N * L) := by
    simp only [interpBound, Int.toNat_natCast]; ring
  refine HilbertComplex.Subcomplex.exists_mem_le_of_succ _ hv hB0 (by rw [e]; linarith)
    fun hxj => ?_
  rw [hval, e]
  linarith

theorem IsC2Form.infDist_domainSub_whitney_le {j : ℤ} {L : ℝ} {σ : (complex n).domainSpace j}
    (hσ : IsC2Form j L ((complex n).domainIncl j σ)) (hL0 : 0 ≤ L) (N : ℕ) :
    Metric.infDist σ ((whitney n N).domainSub j) ≤ interpBound n j * L * meshSize N := by
  rcases hσ with hj | ⟨k, rfl, w, hw, hdeg, hL, hL', he⟩
  · have hB0 := mul_nonneg (mul_nonneg (interpBound_nonneg n j) hL0) (meshSize_pos N).le
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = Int.negSucc k := ⟨(-j - 1).toNat, by omega⟩
    have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    refine (Subcomplex.infDist_domainSub_le (S := whitney n N)
      (rfl : (ComplexShape.up ℤ).Rel (Int.negSucc k) (Int.negSucc k + 1)) σ
      (Submodule.zero_mem _)).trans ?_
    rw [Subsingleton.elim (_ - 0) 0, norm_zero, ← LinearPMap.map_sub,
      Subsingleton.elim (_ - _ : ((complex n).d _ _).domain) 0, LinearPMap.map_zero, norm_zero,
      add_zero]
    exact hB0
  refine (FEM.infDist_domainSub_whitney_le N k hw hdeg hL0 hL0 hL hL' σ he).trans (le_of_eq ?_)
  simp only [interpBound, Int.toNat_natCast]; ring

theorem exists_mem_window_le (a : ℤ) (m : ℕ) (ζ : ((complex n).window a m).totalD.GraphSpace)
    {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m, IsC2Form (a + i) L (((complex n).window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((whitney n N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N :=
  ((whitney n N).exists_mem_window_graphSub_le ζ (fun i => interpBound n (a + i))
    (fun _ => interpBound_nonneg n _) (mul_nonneg hL0 (meshSize_pos N).le)
    fun i => by
      obtain ⟨v, hv, h1, h2⟩ := (hζ i).exists_mem_whitney_le hL0 N
      exact ⟨v, hv, h1.trans_eq (mul_assoc _ _ _),
        fun j hx => (h2 j hx).trans_eq (mul_assoc _ _ _)⟩).imp
    fun _ h => ⟨h.1, h.2.trans_eq (mul_assoc _ _ _).symm⟩

/-- **`O(h)` convergence for `ξ`, `ξ'` in `IsC2Form`** ([QuennevilleBelair2015], Thm 4.14). -/
theorem norm_sub_le_meshSize_window_smooth (a : ℤ) (m : ℕ) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((whitney n N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney n N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ s ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      IsC2Form (a + i) L (((complex n).window a m).totalD.graphFst (ξ s) i) ∧
        IsC2Form (a + i) L (((complex n).window a m).totalD.graphFst (ξ' s) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complex n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complex n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((m : ℝ) + m * m) * (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N) := by
  have e : ((m : ℝ) + m * m) * (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N =
      (((m : ℝ) + m * m) * (∑ i : Fin m, interpBound n (a + i)) * L) * meshSize N := rfl
  rw [e]
  exact norm_sub_le_meshSize_window n a m hξ hξh h0 (fun N s hs =>
    ⟨exists_mem_window_le a m (ξ s) hL0 (fun i => (hreg s hs i).1) N,
      exists_mem_window_le a m (ξ' s) hL0 (fun i => (hreg s hs i).2) N⟩) N ht

/-! ## The vanishing-trace family `H̊Λ(Q)` -/

/-- `IsC2Form` with a representative vanishing outside `Q`. -/
def IsC2FormMin (j : ℤ) (L : ℝ) (x : L2F ℝ (cubeDomain n) (formIdx n j)) : Prop :=
  j < 0 ∨ ∃ k : ℕ, (k : ℤ) = j ∧ ∃ w : FormField n, ∃ hw : ContDiff ℝ 2 w, (∀ y, IsDeg k (w y)) ∧
    (∀ y ∉ cubeDomain n, w y = 0) ∧
    (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ w y‖ ≤ L) ∧
    (∀ y ∈ closure (cubeDomain n), ‖fderiv ℝ (extDeriv w) y‖ ≤ L) ∧
    x = formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) j ⟨w, hw.continuous⟩

omit [NeZero n] in
theorem complexMin_d_formL2 [NeZero n] (k : ℕ) {w : FormField n} (hw : ContDiff ℝ 1 w)
    (hdeg : ∀ y, IsDeg k (w y)) (x : ((complexMin n).d k (k + 1)).domain)
    (hx : (x : L2F ℝ (cubeDomain n) (formIdx n k)) =
      formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw.continuous⟩) :
    (complexMin n).d k (k + 1) x =
      formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) ((k : ℤ) + 1)
        ⟨extDeriv w, continuous_extDeriv hw⟩ := by
  have hd := deRham_minimalComplex_d (𝕜 := ℝ) (n := n) (isOpen_cubeDomain n) (k : ℤ)
  have hD := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) (isOpen_cubeDomain n) (k : ℤ)
  obtain ⟨h, hval⟩ := formL2_mem_domain k hw hdeg
  refine (LinearPMap.apply_eq_of_eq' hd x).trans
    (((extDerivOp_minimal_le_maximal (𝕜 := ℝ) (n := n) (isOpen_cubeDomain n) (k : ℤ)).2
      (y := ⟨_, hD ▸ h⟩) hx).trans ?_)
  rw [← hval]
  exact (LinearPMap.apply_eq_of_eq' hD ⟨_, h⟩).symm

/-- **Degreewise interpolation error for `C²` forms vanishing outside `Q`**, in `H̊Λ(Q)`. -/
theorem IsC2FormMin.exists_mem_whitneyMin_le {j : ℤ} {L : ℝ}
    {x : L2F ℝ (cubeDomain n) (formIdx n j)} (hx : IsC2FormMin j L x) (hL0 : 0 ≤ L) (N : ℕ) :
    ∃ v, ∃ hv : v ∈ (whitneyMin n N).V j, ‖x - v‖ ≤ interpBound n j * L * meshSize N ∧
      ∀ j' (hxj : x ∈ ((complexMin n).d j j').domain),
        ‖(complexMin n).d j j'
            ⟨x - v, Submodule.sub_mem _ hxj ((whitneyMin n N).le_domain j j' hv)⟩‖ ≤
          interpBound n j * L * meshSize N := by
  have hB0 := mul_nonneg (mul_nonneg (interpBound_nonneg n j) hL0) (meshSize_pos N).le
  rcases hx with hj | ⟨k, rfl, w, hw, hdeg, hsupp, hL, hL', rfl⟩
  · have := LocalElement.subsingleton_L2F_of_neg (cubeDomain n) (n := n) hj
    exact (whitneyMin n N).exists_mem_le_of_subsingleton hB0
  obtain ⟨v, hv, hv1, hdv, hv2⟩ := FEM.exists_mem_whitneyMin_le N k hw hsupp hL0 hL0 hL hL'
  have hh := (meshSize_pos N).le
  have hA0 := mul_nonneg (interpConst_nonneg n k) (mul_nonneg hh hL0)
  have hA1 := mul_nonneg (interpConst_nonneg n (k + 1)) (mul_nonneg hh hL0)
  have e : interpBound n k * L * meshSize N =
      interpConst n k * (meshSize N * L) + interpConst n (k + 1) * (meshSize N * L) := by
    simp only [interpBound, Int.toNat_natCast]; ring
  refine HilbertComplex.Subcomplex.exists_mem_le_of_succ _ hv hB0 (by rw [e]; linarith)
    fun hxj => ?_
  rw [complexMin_d_formL2 k (hw.of_le (by norm_num)) hdeg ⟨_, hxj⟩ rfl, e]
  linarith

theorem IsC2FormMin.infDist_domainSub_whitneyMin_le {j : ℤ} {L : ℝ}
    {σ : (complexMin n).domainSpace j} (hσ : IsC2FormMin j L ((complexMin n).domainIncl j σ))
    (hL0 : 0 ≤ L) (N : ℕ) :
    Metric.infDist σ ((whitneyMin n N).domainSub j) ≤ 2 * (interpBound n j * L * meshSize N) := by
  obtain ⟨v, hv, h1, h2⟩ := hσ.exists_mem_whitneyMin_le hL0 N
  exact Subcomplex.infDist_domainSub_le_two_mul _ rfl σ hv h1 (h2 _)

instance (N : ℕ) (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional ℝ (((whitneyMin n N).window a m).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((whitneyMin n N).V (a + i)))

instance (N : ℕ) (a : ℤ) (m : ℕ) :
    FiniteDimensional ℝ ((whitneyMin n N).window a m).graphSub :=
  inferInstance

theorem exists_mem_windowMin_le (a : ℤ) (m : ℕ)
    (ζ : ((complexMin n).window a m).totalD.GraphSpace) {L : ℝ} (hL0 : 0 ≤ L)
    (hζ : ∀ i : Fin m, IsC2FormMin (a + i) L (((complexMin n).window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((whitneyMin n N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N :=
  ((whitneyMin n N).exists_mem_window_graphSub_le ζ (fun i => interpBound n (a + i))
    (fun _ => interpBound_nonneg n _) (mul_nonneg hL0 (meshSize_pos N).le)
    fun i => by
      obtain ⟨v, hv, h1, h2⟩ := (hζ i).exists_mem_whitneyMin_le hL0 N
      exact ⟨v, hv, h1.trans_eq (mul_assoc _ _ _),
        fun j hx => (h2 j hx).trans_eq (mul_assoc _ _ _)⟩).imp
    fun _ h => ⟨h.1, h.2.trans_eq (mul_assoc _ _ _).symm⟩

/-- **`O(h)` convergence in `H̊Λ(Q)` for `ξ`, `ξ'` in `IsC2FormMin`** ([QuennevilleBelair2015],
Thm 4.14). -/
theorem norm_sub_le_meshSize_windowMin_smooth (a : ℤ) (m : ℕ) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complexMin n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complexMin n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((whitneyMin n N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ =
      HodgeWave.ellipticProjection (((whitneyMin n N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ s ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      IsC2FormMin (a + i) L (((complexMin n).window a m).totalD.graphFst (ξ s) i) ∧
        IsC2FormMin (a + i) L (((complexMin n).window a m).totalD.graphFst (ξ' s) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complexMin n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complexMin n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          (((m : ℝ) + m * m) * (∑ i : Fin m, interpBound n (a + i)) * L * meshSize N) :=
  ((whitneyMin n N).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (fun s hs =>
    ⟨exists_mem_windowMin_le a m (ξ s) hL0 (fun i => (hreg s hs i).1) N,
      exists_mem_windowMin_le a m (ξ' s) hL0 (fun i => (hreg s hs i).2) N⟩) ht

end Feec.Models.Cube.FEM
