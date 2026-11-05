module

public import Solution.Crime

/-!
# The witness of the crimes

The complex `ℝ` in every degree with `d⁰ = id` and all other differentials `0`
(`Witness.complex`), on the window `ℝ --id--> ℝ --0--> ℝ` (`𝐝 (a, b, c) = (0, a, 0)`, harmonic
forms `ℝ (0, 0, 1)`), with the discrete spaces `Xₙ = W`, `𝐝ₙ = 𝐝`, read by the cochain maps
`iₙ = 1 + hₙ N`, `N (a, b, c) = (0, c, 0)`, `hₙ = 1/(n+1)`, with the left inverses and cochain
projections `πₙ = 1 - hₙ N` (`Witness.family`, `Witness.proj`): the shear family of
`Feec.HilbertComplex.Approximation.StaticCochainWitness`, built here over the challenge. The
reading maps are not isometric (`iₙ* iₙ ≠ 1`), `‖1 - iₙ* iₙ‖ ≤ 3 hₙ → 0`, `iₙ πₙ = 1`, the discrete
harmonic form `(0, 0, 1)` is read as `(0, hₙ, 1) ∉ ℌ`, and the error at the datum `(0, 0, 1)` is
at least `hₙ > 0`.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012], §3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC.Witness

/-- The differentials `d⁰ = id`, all others `0`. -/
def δ (i j : ℤ) : ℝ →L[ℝ] ℝ := if i = 0 ∧ j = 1 then ContinuousLinearMap.id ℝ ℝ else 0

/-- The witness complex as a `Feec` complex of bounded operators. -/
def feecComplex : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) (fun _ : ℤ => ℝ) :=
  Feec.HilbertComplex.ofBounded δ
    (fun i j h => by
      have hij : ¬ (i = 0 ∧ j = 1) := by
        rintro ⟨rfl, rfl⟩
        exact h rfl
      simp [δ, hij])
    (fun i j k x => by
      by_cases hij : i = 0 ∧ j = 1
      · simp [δ, hij.2]
      · simp [δ, hij])

/-- **The witness complex**: `ℝ` in every degree, `d⁰ = id`, all other differentials `0`. -/
def complex : HilbertComplex ℝ fun _ : ℤ => ℝ :=
  ⟨feecComplex.d, feecComplex.shape, feecComplex.dense, feecComplex.closed, feecComplex.mapsTo,
    feecComplex.d_comp_d⟩

/-- The window `[0, 3)`: `ℝ³`. -/
abbrev T3 : Type := Total (fun _ : ℤ => ℝ) 0 3

theorem mem_domain (y : T3) : y ∈ (complex.totalD 0 3).domain := fun _ _ => Submodule.mem_top

/-- The vector `(a, b, c)`. -/
abbrev vec (a b c : ℝ) : T3 := WithLp.toLp 2 ![a, b, c]

theorem eq_vec (y : T3) : y = vec (y 0) (y 1) (y 2) := by
  ext i; fin_cases i <;> rfl

theorem norm_sq_vec (a b c : ℝ) : ‖vec a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

theorem inner_vec (a b c a' b' c' : ℝ) :
    ⟪vec a b c, vec a' b' c'⟫_ℝ = a * a' + b * b' + c * c' := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp [mul_comm]

/-- **The total differential** `𝐝 (a, b, c) = (0, a, 0)`. -/
theorem totalD_apply (y : (complex.totalD 0 3).domain) :
    complex.totalD 0 3 y = vec 0 ((y : T3) 0) 0 := by
  ext j
  change ∑ i : Fin 3, δ (0 + ((i : ℕ) : ℤ)) (0 + ((j : ℕ) : ℤ)) ((y : T3) i) = _
  rw [Fin.sum_univ_three]
  fin_cases j <;> simp [δ]

/-- `𝐝` as a bounded operator. -/
def dL : T3 →L[ℝ] T3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => vec 0 (y 0) 0
      map_add' := fun x y => by ext i; fin_cases i <;> simp
      map_smul' := fun c x => by ext i; fin_cases i <;> simp }

theorem dL_apply (y : T3) : dL y = vec 0 (y 0) 0 := rfl

theorem totalD_eq_dL (y : (complex.totalD 0 3).domain) : complex.totalD 0 3 y = dL y :=
  totalD_apply y

/-- `N (a, b, c) = (0, c, 0)`. -/
def N : T3 →L[ℝ] T3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => vec 0 (y 2) 0
      map_add' := fun x y => by ext i; fin_cases i <;> simp
      map_smul' := fun c x => by ext i; fin_cases i <;> simp }

theorem N_apply (y : T3) : N y = vec 0 (y 2) 0 := rfl

theorem N_N (y : T3) : N (N y) = 0 := by
  rw [N_apply, N_apply]; ext i; fin_cases i <;> rfl

theorem dL_N (y : T3) : dL (N y) = 0 := by
  rw [N_apply, dL_apply]; ext i; fin_cases i <;> rfl

theorem N_dL (y : T3) : N (dL y) = 0 := by
  rw [N_apply, dL_apply]; ext i; fin_cases i <;> rfl

theorem dL_dL (y : T3) : dL (dL y) = 0 := by
  rw [dL_apply, dL_apply]; ext i; fin_cases i <;> rfl

theorem norm_N_le : ‖N‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  have hy := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) y
  rw [Fin.sum_univ_three] at hy
  simp only [Real.norm_eq_abs, sq_abs] at hy
  rw [N_apply, norm_sq_vec]
  change (0 : ℝ) ^ 2 + y 2 ^ 2 + 0 ^ 2 ≤ _
  nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]

/-- The mesh `hₙ = 1/(n+1)`. -/
def mesh (n : ℕ) : ℝ := 1 / (n + 1)

theorem mesh_pos (n : ℕ) : 0 < mesh n := by unfold mesh; positivity

theorem mesh_le_one (n : ℕ) : mesh n ≤ 1 := by
  unfold mesh
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem tendsto_mesh : Tendsto mesh atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- The reading maps `iₙ = 1 + hₙ N`. -/
def incl (n : ℕ) : T3 →L[ℝ] T3 := 1 + mesh n • N

/-- Their left inverses `πₙ = 1 - hₙ N`. -/
def projL (n : ℕ) : T3 →L[ℝ] T3 := 1 - mesh n • N

theorem incl_apply (n : ℕ) (y : T3) : incl n y = y + mesh n • N y := rfl

theorem projL_apply (n : ℕ) (y : T3) : projL n y = y - mesh n • N y := rfl

theorem projL_incl (n : ℕ) (y : T3) : projL n (incl n y) = y := by
  rw [incl_apply, projL_apply, _root_.map_add, _root_.map_smul, N_N, smul_zero, add_zero,
    add_sub_cancel_right]

theorem incl_projL (n : ℕ) (y : T3) : incl n (projL n y) = y := by
  rw [incl_apply, projL_apply, _root_.map_sub, _root_.map_smul, N_N, smul_zero, sub_zero,
    sub_add_cancel]

theorem norm_mesh_smul_N_le (n : ℕ) : ‖mesh n • N‖ ≤ 1 :=
  (norm_smul_le (mesh n) N).trans (by
    rw [Real.norm_eq_abs, abs_of_pos (mesh_pos n)]
    nlinarith [mesh_le_one n, norm_N_le, mesh_pos n, norm_nonneg N])

/-- **The witness family**: `Xₙ = ℝ³`, `𝐝ₙ = 𝐝`, read by `iₙ = 1 + hₙ N`. -/
def family : complex.CrimeFamily 0 3 ℕ where
  l := atTop
  X _ := T3
  D _ := dL
  D_D _ := dL_dL
  incl := incl
  proj := projL
  proj_incl := projL_incl
  bound := ⟨2, fun n => ⟨(norm_add_le _ _).trans (by
      have := norm_mesh_smul_N_le n
      have : ‖(1 : T3 →L[ℝ] T3)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      linarith),
    (norm_sub_le _ _).trans (by
      have := norm_mesh_smul_N_le n
      have : ‖(1 : T3 →L[ℝ] T3)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      linarith)⟩⟩

theorem totalD_incl (n : ℕ) (v : T3) :
    complex.totalD 0 3 ⟨incl n v, mem_domain _⟩ = incl n (dL v) := by
  rw [totalD_eq_dL, incl_apply, incl_apply, _root_.map_add, _root_.map_smul, dL_N, N_dL]

theorem isCochain : family.IsCochain :=
  ⟨fun _ v => mem_domain v, fun n v => totalD_incl n v⟩

/-- **The cochain projections** `πₙ = 1 - hₙ N`, bounded by `2` in the graph norm. -/
def proj : family.CochainProj 2 where
  π n := (projL n : T3 →ₗ[ℝ] T3)
  π_incl := projL_incl
  norm_π_le n x := by
    have h1 : ‖projL n (x : T3)‖ ≤ 2 * ‖(x : T3)‖ :=
      ((projL n).le_opNorm _).trans (mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (by
        have := norm_mesh_smul_N_le n
        have : ‖(1 : T3 →L[ℝ] T3)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        linarith)) (norm_nonneg _))
    have := norm_nonneg (complex.totalD 0 3 x)
    change ‖projL n (x : T3)‖ ≤ _
    nlinarith
  π_totalD n z := by
    change projL n (complex.totalD 0 3 z) = dL (projL n (z : T3))
    rw [totalD_eq_dL, projL_apply, projL_apply, _root_.map_sub, _root_.map_smul, dL_N, N_dL]

/-- The harmonic datum `(0, 0, 1)`. -/
abbrev e2 : T3 := vec 0 0 1

theorem dL_e2 : dL e2 = 0 := by rw [dL_apply]; ext i; fin_cases i <;> rfl

theorem N_e2 : N e2 = vec 0 1 0 := rfl

theorem inner_dL_e2 (y : T3) : ⟪dL y, e2⟫_ℝ = 0 := by
  rw [dL_apply, inner_vec]; ring

theorem mem_totalHarmonic_e2 : e2 ∈ complex.totalHarmonic 0 3 := by
  refine ⟨LinearPMap.mem_ker_iff.2 ⟨⟨e2, mem_domain _⟩, rfl, by rw [totalD_eq_dL, dL_e2]⟩, ?_⟩
  have hd : Dense ((complex.totalD 0 3).domain : Set T3) := by
    rw [show ((complex.totalD 0 3).domain : Set T3) = univ from
      eq_univ_of_forall fun y => mem_domain y]
    exact dense_univ
  have hmem : e2 ∈ (complex.totalD 0 3)†.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨0, fun y => by
      rw [inner_zero_left, ← inner_conj_symm, totalD_eq_dL, inner_dL_e2, _root_.map_zero]⟩
  refine LinearPMap.mem_ker_iff.2 ⟨⟨e2, hmem⟩, rfl, ?_⟩
  exact LinearPMap.adjoint_apply_eq hd _ fun y => by
    rw [inner_zero_left, ← inner_conj_symm, totalD_eq_dL, inner_dL_e2, _root_.map_zero]

theorem adjoint_dL_e2 : dL.adjoint e2 = 0 := by
  refine ext_inner_right ℝ fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, ← inner_conj_symm,
    inner_dL_e2, _root_.map_zero]

theorem mem_harmonic_e2 (n : ℕ) : e2 ∈ family.harmonic n :=
  ⟨dL_e2, adjoint_dL_e2⟩

theorem incl_e2 (n : ℕ) : incl n e2 = vec 0 (mesh n) 1 := by
  rw [incl_apply, N_e2]; ext i; fin_cases i <;> simp

theorem incl_e2_not_mem (n : ℕ) : incl n e2 ∉ complex.totalHarmonic 0 3 := by
  rintro ⟨-, hk⟩
  obtain ⟨z, hz, hz0⟩ := LinearPMap.mem_ker_iff.1 hk
  have hd : Dense ((complex.totalD 0 3).domain : Set T3) := by
    rw [show ((complex.totalD 0 3).domain : Set T3) = univ from
      eq_univ_of_forall fun y => mem_domain y]
    exact dense_univ
  have h := LinearPMap.adjoint_isFormalAdjoint hd z ⟨vec 1 0 0, mem_domain _⟩
  rw [hz0, inner_zero_left, ← hz, totalD_eq_dL, incl_e2, dL_apply, inner_vec] at h
  change (0 : ℝ) = 0 * 0 + mesh n * 1 + 1 * 0 at h
  have := mesh_pos n
  linarith

/-- `‖iₙ e₂‖² = 1 + hₙ²`, so `iₙ* iₙ ≠ 1`. -/
theorem J_ne_one (n : ℕ) : (incl n).adjoint ∘L incl n ≠ 1 := fun hJ => by
  have h := congrArg (fun A : T3 →L[ℝ] T3 => ⟪A e2, e2⟫_ℝ) hJ
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    one_apply_eq_self] at h
  rw [incl_e2, inner_vec, inner_vec] at h
  have := mesh_pos n
  nlinarith

theorem one_sub_J_eq (n : ℕ) : 1 - (incl n).adjoint ∘L incl n =
    -(mesh n • N + mesh n • N.adjoint + (mesh n * mesh n) • (N.adjoint ∘L N)) := by
  have ha : (incl n).adjoint = 1 + mesh n • N.adjoint := by
    rw [incl, _root_.map_add, MulActionSemiHomClass.map_smulₛₗ, starRingEnd_apply, star_trivial]
    congr 1
    exact ContinuousLinearMap.adjoint_id
  rw [ha, incl]
  ext y
  simp only [_root_.sub_apply, _root_.neg_apply, _root_.add_apply, ContinuousLinearMap.comp_apply,
    _root_.smul_apply, one_apply_eq_self, _root_.map_add, _root_.map_smul, smul_add, smul_smul]
  abel_nf

theorem norm_one_sub_J_le (n : ℕ) : ‖1 - (incl n).adjoint ∘L incl n‖ ≤ 3 * mesh n := by
  rw [one_sub_J_eq, norm_neg]
  have hN := norm_N_le
  have hNa : ‖N.adjoint‖ ≤ 1 := by rw [LinearIsometryEquiv.norm_map]; exact hN
  have hm := mesh_pos n
  have hm1 := mesh_le_one n
  have e1 : ‖mesh n • N‖ ≤ mesh n := (norm_smul_le (mesh n) N).trans (by
    rw [Real.norm_eq_abs, abs_of_pos hm]; nlinarith [norm_nonneg N])
  have e2' : ‖mesh n • N.adjoint‖ ≤ mesh n := (norm_smul_le (mesh n) N.adjoint).trans (by
    rw [Real.norm_eq_abs, abs_of_pos hm]; nlinarith [norm_nonneg N.adjoint])
  have e3 : ‖(mesh n * mesh n) • (N.adjoint ∘L N)‖ ≤ mesh n :=
    (norm_smul_le (mesh n * mesh n) (N.adjoint ∘L N)).trans (by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hm hm)]
    have := (ContinuousLinearMap.opNorm_comp_le N.adjoint N).trans
      (mul_le_mul hNa hN (norm_nonneg _) zero_le_one)
    nlinarith [norm_nonneg (N.adjoint ∘L N)])
  exact (norm_add_le _ _).trans (by linarith [norm_add_le (mesh n • N) (mesh n • N.adjoint)])

theorem tendsto_one_sub_J :
    Tendsto (fun n => ‖1 - (incl n).adjoint ∘L incl n‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) norm_one_sub_J_le (by
    simpa using tendsto_mesh.const_mul 3)

/-- `(0, 0, e₂)` solves the mixed problem of the window with data `e₂`. -/
theorem isTotalMixedSolution_e2 :
    complex.IsTotalMixedSolution 0 3 e2 0 0 e2 where
  mem := mem_totalHarmonic_e2
  fst τ := by simp
  snd v := by simp
  harm q _ := by simp

/-- `(0, 0, e₂)` solves the discrete mixed problem with the load `iₙ* e₂`. -/
theorem residual_e2 (n : ℕ) (τ v q : T3) :
    ⟪τ, (0 : T3)⟫_ℝ - ⟪dL τ, (0 : T3)⟫_ℝ + ⟪v, dL 0⟫_ℝ + ⟪dL v, dL 0⟫_ℝ + ⟪v, e2⟫_ℝ -
      ⟪q, (0 : T3)⟫_ℝ - ⟪incl n v, e2⟫_ℝ = 0 := by
  rw [incl_apply, inner_add_left, inner_smul_left, N_apply, inner_vec]
  simp

theorem isMixedSolution_e2 (n : ℕ) : family.IsMixedSolution n e2 0 0 e2 :=
  ⟨mem_harmonic_e2 n, fun τ v q _ => residual_e2 n τ v q⟩

end FEEC.Witness
