module

public import Feec.Models.Cube.AbsorbingTSD

/-!
# Finite speed of propagation for the absorbing problem on the cube

The absorbing semigroup of `Feec.Models.Cube.Absorbing` solves the row-wise Einstein–Bianchi system
`Ė = -curl B`, `Ḃ = curl E` weakly in `Q` (`IsWeakRowEB`). This system is symmetric hyperbolic of
unit speed (`isSymmHyperbolic_ebDir`), so the domain-of-dependence theorem of
`Feec.Domain.FiniteSpeed` applies to the difference of two weak solutions:

* **`absorbingSemigroup_eq_depDomain`**: for every weak solution `W` of the system in `Q` with
  `W(0) = u₀` — for instance the restriction to `Q` of a solution on `ℝ³` — the absorbing
  solution `S(t) u₀` equals `W(t)` a.e. on `depDomain Q t`, the points at Euclidean distance
  `> t` from `ℝ³ \ Q`: the boundary condition is felt only after the boundary is reached.
* `IsWeakRowEB.ae_eq_zero_depDomain`: every weak solution with zero data vanishes on the domain
  of dependence (applied to the difference). The statement is non-empty for `t < ¼` only
  (`depDomain Q t = ∅` for `t ≥ ¼`), and no weak solution other than the absorbing orbits is
  constructed here.

## References

* [L. C. Evans, *Partial Differential Equations*][Evans2010], §7.3.2 (symmetric hyperbolic systems,
  domain of dependence)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.4 (the system)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Set MeasureTheory Filter Topology Feec.Domain Feec.Models.BoundedDomain

@[expose] public noncomputable section

namespace Feec.Models.Cube.Absorbing

open Geometry

/-! ### Weak solutions of the row-wise system -/

/-- `W` is a **weak solution** of `Ė = -curl B`, `Ḃ = curl E` in `Q` on `[0, T]`: continuous,
with `⟪E(t), Φ⟫ = ⟪E(0), Φ⟫ - ∫₀ᵗ ⟪B, curl Φ⟫` and `⟪B(t), Φ⟫ = ⟪B(0), Φ⟫ + ∫₀ᵗ ⟪E, curl Φ⟫`
for every test field `Φ` (no boundary condition). -/
structure IsWeakRowEB (T : ℝ) (W : ℝ → State) : Prop where
  continuousOn : ContinuousOn W (Icc 0 T)
  fst : ∀ {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (Q (Fin 3)) Φ), ∀ t ∈ Icc 0 T,
    ⟪(W t).fst, testField hΦ⟫_ℝ = ⟪(W 0).fst, testField hΦ⟫_ℝ -
      ∫ s in (0 : ℝ)..t, ⟪(W s).snd, (C1Field.ofTest hΦ).curlL2⟫_ℝ
  snd : ∀ {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (Q (Fin 3)) Φ), ∀ t ∈ Icc 0 T,
    ⟪(W t).snd, testField hΦ⟫_ℝ = ⟪(W 0).snd, testField hΦ⟫_ℝ +
      ∫ s in (0 : ℝ)..t, ⟪(W s).fst, (C1Field.ofTest hΦ).curlL2⟫_ℝ

/-- **The absorbing orbits are weak solutions** (every datum). -/
theorem isWeakRowEB_absorbingSemigroup (u₀ : State) (T : ℝ) :
    IsWeakRowEB T fun t => absorbingSemigroup.S t u₀ :=
  ⟨(absorbingSemigroup.strongCont u₀).mono Icc_subset_Ici_self,
    fun hΦ t ht => by
      rw [C0Semigroup.S_zero_apply]; exact inner_fst_absorbingSemigroup u₀ hΦ ht.1,
    fun hΦ t ht => by
      rw [C0Semigroup.S_zero_apply]; exact inner_snd_absorbingSemigroup u₀ hΦ ht.1⟩

theorem intervalIntegrable_of_continuousOn {g : ℝ → ℝ} {T t : ℝ}
    (hg : ContinuousOn g (Icc 0 T)) (ht : t ∈ Icc 0 T) : IntervalIntegrable g volume 0 t :=
  (hg.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1

/-- Weak solutions form a vector space: differences. -/
theorem IsWeakRowEB.sub {T : ℝ} {W W' : ℝ → State} (h : IsWeakRowEB T W)
    (h' : IsWeakRowEB T W') : IsWeakRowEB T (W - W') := by
  have hcs : ∀ (V : ℝ → State), ContinuousOn V (Icc 0 T) → ∀ (z : MQ),
      ContinuousOn (fun s => ⟪(V s).snd, z⟫_ℝ) (Icc 0 T) ∧
        ContinuousOn (fun s => ⟪(V s).fst, z⟫_ℝ) (Icc 0 T) := fun V hV z =>
    ⟨((WithLp.sndL 2 ℝ MQ MQ).continuous.comp_continuousOn hV).inner continuousOn_const,
      ((WithLp.fstL 2 ℝ MQ MQ).continuous.comp_continuousOn hV).inner continuousOn_const⟩
  refine ⟨h.continuousOn.sub h'.continuousOn, fun hΦ t ht => ?_, fun hΦ t ht => ?_⟩
  · have e1 := h.fst hΦ t ht
    have e2 := h'.fst hΦ t ht
    have i1 := intervalIntegrable_of_continuousOn
      (hcs W h.continuousOn (C1Field.ofTest hΦ).curlL2).1 ht
    have i2 := intervalIntegrable_of_continuousOn
      (hcs W' h'.continuousOn (C1Field.ofTest hΦ).curlL2).1 ht
    simp only [Pi.sub_apply, WithLp.sub_fst, WithLp.sub_snd, inner_sub_left]
    rw [intervalIntegral.integral_sub i1 i2, e1, e2]
    ring
  · have e1 := h.snd hΦ t ht
    have e2 := h'.snd hΦ t ht
    have i1 := intervalIntegrable_of_continuousOn
      (hcs W h.continuousOn (C1Field.ofTest hΦ).curlL2).2 ht
    have i2 := intervalIntegrable_of_continuousOn
      (hcs W' h'.continuousOn (C1Field.ofTest hΦ).curlL2).2 ht
    simp only [Pi.sub_apply, WithLp.sub_fst, WithLp.sub_snd, inner_sub_left]
    rw [intervalIntegral.integral_sub i1 i2, e1, e2]
    ring

/-! ### The system is symmetric hyperbolic of unit speed -/

/-- The state components `(E, B)`. -/
abbrev FIdx := Ix ⊕ Ix

/-- `∂_{k+1} X_{m}` with sign: the coefficient of
`∂ₜ E_{ik} = -∂_{k+1} B_{i,k+2} + ∂_{k+2} B_{i,k+1}`. -/
def rowCurlDir (k m : Fin 3) : R3 :=
  if m = k + 2 then -Pi.single (k + 1) 1 else if m = k + 1 then Pi.single (k + 2) 1 else 0

/-- The coefficients `β j i` of the row-wise system `∂ₜ wⱼ = Σᵢ ∂_{β j i} wᵢ`, `w = (E, B)`:
`∂ₜ E = -curl B`, `∂ₜ B = curl E`. -/
def ebDir : FIdx → FIdx → R3
  | .inl a, .inr b => if a.1 = b.1 then rowCurlDir a.2 b.2 else 0
  | .inr b, .inl a => if a.1 = b.1 then rowCurlDir a.2 b.2 else 0
  | _, _ => 0

theorem ebDir_symm (j i : FIdx) : ebDir j i = ebDir i j := by
  rcases j with a | b <;> rcases i with a' | b' <;> rfl

/-- Cauchy–Schwarz for the triple product: `(e · (b × x))² ≤ |e|² |x|² |b|²`. -/
theorem sq_triple_le (e0 e1 e2 b0 b1 b2 x0 x1 x2 : ℝ) :
    (e0 * (b1 * x2 - b2 * x1) + e1 * (b2 * x0 - b0 * x2) + e2 * (b0 * x1 - b1 * x0)) ^ 2 ≤
      (e0 ^ 2 + e1 ^ 2 + e2 ^ 2) * ((x0 ^ 2 + x1 ^ 2 + x2 ^ 2) * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2)) := by
  have h1 := sq_dot4_le e0 e1 e2 0 (b1 * x2 - b2 * x1) (b2 * x0 - b0 * x2) (b0 * x1 - b1 * x0) 0
  have h2 : (b1 * x2 - b2 * x1) ^ 2 + (b2 * x0 - b0 * x2) ^ 2 + (b0 * x1 - b1 * x0) ^ 2 ≤
      (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2) := by
    nlinarith [sq_nonneg (b0 * x0 + b1 * x1 + b2 * x2)]
  have h3 : 0 ≤ e0 ^ 2 + e1 ^ 2 + e2 ^ 2 := by positivity
  simp only [mul_zero, add_zero, zero_pow two_ne_zero] at h1
  calc _ ≤ (e0 ^ 2 + e1 ^ 2 + e2 ^ 2) * ((b1 * x2 - b2 * x1) ^ 2 + (b2 * x0 - b0 * x2) ^ 2 +
        (b0 * x1 - b1 * x0) ^ 2) := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 h3

/-- **The row-wise Einstein–Bianchi system is symmetric hyperbolic of unit speed** for the
Euclidean norm. -/
theorem isSymmHyperbolic_ebDir :
    FiniteSpeed.IsSymmHyperbolic (fun j i => euc (ebDir j i)) 1 := by
  refine ⟨fun j i => by rw [ebDir_symm], zero_le_one, fun L w => ?_⟩
  set ξ : Fin 3 → ℝ := fun c => L (euc (Pi.single c 1))
  have hL : ∀ v : R3, L (euc v) = ∑ c, v c * ξ c := fun v => by
    have e : v = ∑ c, v c • (Pi.single c 1 : R3) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [e]
    simp [map_sum, map_smul, ξ]
  set P : Fin 3 → ℝ := fun i =>
    w (.inl (i, 0)) * (w (.inr (i, 1)) * ξ 2 - w (.inr (i, 2)) * ξ 1) +
    w (.inl (i, 1)) * (w (.inr (i, 2)) * ξ 0 - w (.inr (i, 0)) * ξ 2) +
    w (.inl (i, 2)) * (w (.inr (i, 0)) * ξ 1 - w (.inr (i, 1)) * ξ 0)
  have key : ∑ j, ∑ i, w j * w i * L (euc (ebDir j i)) = ∑ i, 2 * P i := by
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_three, ebDir,
      rowCurlDir, hL]
    simp [P, ξ]
    ring
  have hU : ∀ i : Fin 3, |2 * P i| ≤ 1 * ‖L‖ * ((∑ k, w (.inl (i, k)) ^ 2) +
      ∑ k, w (.inr (i, k)) ^ 2) := fun i => by
    rw [one_mul]
    refine abs_two_le_of_sq_le (s := ∑ c, ξ c ^ 2) ?_ (sum_sq_le_opNorm_sq L) (by positivity)
      (by positivity) (norm_nonneg _)
    simp only [Fin.sum_univ_three, P]
    exact sq_triple_le _ _ _ _ _ _ _ _ _
  rw [key]
  calc |∑ i, 2 * P i| ≤ ∑ i, |2 * P i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, 1 * ‖L‖ * ((∑ k, w (.inl (i, k)) ^ 2) + ∑ k, w (.inr (i, k)) ^ 2) :=
        Finset.sum_le_sum fun i _ => hU i
    _ = 1 * ‖L‖ * ∑ j, w j ^ 2 := by
        rw [← Finset.mul_sum, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type,
          Finset.sum_add_distrib]

/-! ### Weak solutions in the form of `Feec.Domain.FiniteSpeed` -/

/-- The state `(E, B)` as one field with components `FIdx = Ix ⊕ Ix`. -/
def toField (u : State) : L2F ℝ (Q (Fin 3)) FIdx := WithLp.toLp 2 (Sum.elim u.fst u.snd)

theorem continuous_toField : Continuous toField := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
  rcases j with a | b
  · exact (L2F.continuous_apply a).comp (WithLp.fstL 2 ℝ MQ MQ).continuous
  · exact (L2F.continuous_apply b).comp (WithLp.sndL 2 ℝ MQ MQ).continuous

theorem fderiv_rowCurlDir {f : R3 → ℝ} (x : R3) (k m : Fin 3) :
    fderiv ℝ f x (rowCurlDir k m) =
      if m = k + 2 then -pd (k + 1) f x else if m = k + 1 then pd (k + 2) f x else 0 := by
  unfold rowCurlDir
  split_ifs <;> simp [pd]

/-- The formal adjoint of the system on test fields: `(curl ψ_B, -curl ψ_E)`. -/
theorem formalAdj_ebDir (ψ : FIdx → R3 → ℝ) (x : R3) :
    (∀ a, (FiniteSpeed.hypOp ebDir).formalAdj.apply ψ (.inl a) x =
      curlM (fun b => ψ (.inr b)) a x) ∧
    ∀ b, (FiniteSpeed.hypOp ebDir).formalAdj.apply ψ (.inr b) x =
      -curlM (fun a => ψ (.inl a)) b x := by
  constructor
  · rintro ⟨i, k⟩
    rw [FiniteSpeed.hypOp_formalAdj_apply]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, ebDir]
    fin_cases i <;> fin_cases k <;> simp [curlM, Fin.sum_univ_three, fderiv_rowCurlDir] <;> ring
  · rintro ⟨i, m⟩
    rw [FiniteSpeed.hypOp_formalAdj_apply]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, ebDir]
    fin_cases i <;> fin_cases m <;> simp [curlM, Fin.sum_univ_three, fderiv_rowCurlDir] <;> ring

/-- A function of `[0, T]` that is an integral of a function continuous on `[0, T]` has that
function as derivative within `[0, T]`. -/
theorem hasDerivWithinAt_of_eq_add_integral_Icc {f g : ℝ → ℝ} {T : ℝ}
    (hg : ContinuousOn g (Icc 0 T)) (hf : ∀ s ∈ Icc 0 T, f s = f 0 + ∫ σ in (0 : ℝ)..s, g σ) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt f (g t) (Icc 0 T) t := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  set g' : ℝ → ℝ := fun σ => g (min (max σ 0) T)
  have hg' : Continuous g' :=
    hg.comp_continuous ((continuous_id.max continuous_const).min continuous_const) fun σ =>
      ⟨le_min (le_max_right σ 0) hT, min_le_right _ _⟩
  have hd : HasDerivAt (fun s => f 0 + ∫ σ in (0 : ℝ)..s, g' σ) (g' t) t :=
    ((hg'.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add _
  have he : g' t = g t := by simp [g', max_eq_left ht.1, min_eq_left ht.2]
  rw [he] at hd
  refine hd.hasDerivWithinAt.congr_of_mem (fun s hs => ?_) ht
  rw [hf s hs]
  congr 1
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [uIcc_of_le hs.1] at hσ
  simp [g', max_eq_left hσ.1, min_eq_left (hσ.2.trans hs.2)]

theorem inner_toField_testField (u : State) {ψ : FIdx → R3 → ℝ}
    (hψ : IsTestField (Q (Fin 3)) ψ) :
    ⟪toField u, testField hψ⟫_ℝ = ⟪u.fst, testField (fun a => hψ (.inl a) :
        IsTestField (Q (Fin 3)) fun a => ψ (.inl a))⟫_ℝ +
      ⟪u.snd, testField (fun b => hψ (.inr b) :
        IsTestField (Q (Fin 3)) fun b => ψ (.inr b))⟫_ℝ := by
  rw [L2F.inner_def, L2F.inner_def, L2F.inner_def, Fintype.sum_sum_type]
  rfl

/-- **Weak solutions of the row-wise system are weak solutions of the symmetric hyperbolic system
`ebDir`** in the sense of `Feec.Domain.FiniteSpeed`. -/
theorem IsWeakRowEB.isWeakSolution {T : ℝ} {W : ℝ → State} (h : IsWeakRowEB T W) :
    FiniteSpeed.IsWeakSolution ebDir (Q (Fin 3)) T fun s => toField (W s) := by
  refine ⟨continuous_toField.comp_continuousOn h.continuousOn, fun t ht ψ hψ => ?_⟩
  set hψE : IsTestField (Q (Fin 3)) fun a => ψ (.inl a) := fun a => hψ (.inl a)
  set hψB : IsTestField (Q (Fin 3)) fun b => ψ (.inr b) := fun b => hψ (.inr b)
  have hadj : ⟪toField (W t),
      testField ((FiniteSpeed.hypOp ebDir).formalAdj.isTestField_apply hψ)⟫_ℝ =
      ⟪(W t).fst, (C1Field.ofTest hψB).curlL2⟫_ℝ - ⟪(W t).snd, (C1Field.ofTest hψE).curlL2⟫_ℝ := by
    rw [L2F.inner_def, Fintype.sum_sum_type, inner_curlL2_eq, inner_curlL2_eq,
      sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      change ⟪(W t).fst a, toL2 ((FiniteSpeed.hypOp ebDir).formalAdj.isTestField_apply hψ
        (Sum.inl a))⟫_ℝ = _
      rw [inner_toL2]
      simp only [RCLike.conj_to_real, (formalAdj_ebDir ψ _).1]
      rfl
    · refine Finset.sum_congr rfl fun b _ => ?_
      change ⟪(W t).snd b, toL2 ((FiniteSpeed.hypOp ebDir).formalAdj.isTestField_apply hψ
        (Sum.inr b))⟫_ℝ = _
      rw [inner_toL2, ← integral_neg]
      simp only [RCLike.conj_to_real, (formalAdj_ebDir ψ _).2]
      congr 1; funext x; rw [mul_neg]; rfl
  rw [hadj]
  have hcE : ContinuousOn (fun s => ⟪(W s).fst, (C1Field.ofTest hψB).curlL2⟫_ℝ) (Icc 0 T) :=
    ((WithLp.fstL 2 ℝ MQ MQ).continuous.comp_continuousOn h.continuousOn).inner continuousOn_const
  have hcB : ContinuousOn (fun s => ⟪(W s).snd, (C1Field.ofTest hψE).curlL2⟫_ℝ) (Icc 0 T) :=
    ((WithLp.sndL 2 ℝ MQ MQ).continuous.comp_continuousOn h.continuousOn).inner continuousOn_const
  refine hasDerivWithinAt_of_eq_add_integral_Icc (hcE.sub hcB) (fun s hs => ?_) t ht
  rw [inner_toField_testField, inner_toField_testField, h.fst hψE s hs, h.snd hψB s hs]
  simp only [Pi.sub_apply]
  rw [intervalIntegral.integral_sub (intervalIntegrable_of_continuousOn hcE hs)
      (intervalIntegrable_of_continuousOn hcB hs)]
  ring

/-! ### The domain of dependence -/

/-- **Finite speed for weak solutions of the row-wise system in `Q`**: a weak solution with zero
data vanishes a.e. on `depDomain Q t`. -/
theorem IsWeakRowEB.ae_eq_zero_depDomain {T : ℝ} {W : ℝ → State} (h : IsWeakRowEB T W)
    (h0 : W 0 = 0) {t : ℝ} (ht : t ∈ Icc 0 T) (j : FIdx) :
    ∀ᵐ y ∂volume.restrict (depDomain (Q (Fin 3)) t), toField (W t) j y = 0 := by
  have hW := h.isWeakSolution
  set s : {p : R3 × ℝ // ∀ z, dist (euc z) (euc p.1) < p.2 → z ∈ Q (Fin 3)} → Set R3 :=
    fun p => {y | dist (euc y) (euc p.1.1) < p.1.2 - t}
  obtain ⟨I, hI, hIU⟩ := TopologicalSpace.isOpen_iUnion_countable s
    fun p => isOpen_ball_euc _ _
  rw [depDomain_eq_iUnion, ← hIU, ae_restrict_biUnion_iff _ hI]
  intro p _
  have hz : ∀ i, ∀ᵐ y ∂volume.restrict (euc ⁻¹' Metric.ball (euc p.1.1) p.1.2),
      toField (W 0) i y = 0 := fun i => by
    rw [h0]
    have : toField 0 = 0 := by
      refine (WithLp.ext_iff 2).2 (funext fun j => ?_)
      rcases j with a | b <;> rfl
    rw [this, PiLp.zero_apply]
    exact ae_restrict_of_ae_restrict_of_subset (fun z hz => p.2 z hz)
      ((Lp.coeFn_zero ℝ 2 (volume.restrict (Q (Fin 3)))).mono fun x hx => hx)
  have := hW.ae_eq_zero_of_preimage_ball euc (PiLp.volume_preserving_toLp (Fin 3))
    (PiLp.volume_preserving_ofLp (Fin 3)) isSymmHyperbolic_ebDir isOpen_Q
    (x := p.1.1) (R := p.1.2) (fun z hz => p.2 z hz) hz ht j
  simpa [s, Metric.ball, one_mul] using this

/-- **The absorbing solution coincides with every weak solution of the system in `Q` with the same
data on the domain of dependence** — for instance with the restriction to `Q` of a whole-space
solution: the boundary condition acts only after the boundary is reached. -/
theorem absorbingSemigroup_eq_depDomain {T : ℝ} {u₀ : State} {W : ℝ → State}
    (hW : IsWeakRowEB T W) (hW0 : W 0 = u₀) {t : ℝ} (ht : t ∈ Icc 0 T) (j : FIdx) :
    ∀ᵐ y ∂volume.restrict (depDomain (Q (Fin 3)) t),
      toField (absorbingSemigroup.S t u₀) j y = toField (W t) j y := by
  have hD := (isWeakRowEB_absorbingSemigroup u₀ T).sub hW
  have h0 : ((fun s => absorbingSemigroup.S s u₀) - W) 0 = 0 := by
    simp [hW0]
  have := hD.ae_eq_zero_depDomain h0 ht j
  have hsub : toField (((fun s => absorbingSemigroup.S s u₀) - W) t) j =
      toField (absorbingSemigroup.S t u₀) j - toField (W t) j := by
    rcases j with a | b <;> rfl
  rw [hsub] at this
  have hc := Lp.coeFn_sub (toField (absorbingSemigroup.S t u₀) j) (toField (W t) j)
  filter_upwards [this, ae_restrict_of_ae_restrict_of_subset (depDomain_subset ht.1) hc]
    with y h1 h2
  rw [h2, Pi.sub_apply, sub_eq_zero] at h1
  exact h1

end Feec.Models.Cube.Absorbing
