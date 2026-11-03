module

public import Feec.Models.Cube.TorusHelmholtz
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Feec.Models.Cube.WeakSymmetryWave

/-!
# The regular decomposition on the cube: `CurlPotential` is a theorem

The regularity hypothesis of [QuennevilleBelair2015], §5.3
(`Feec.Models.Cube.WeakSymmetry.CurlPotential`) holds on `Q = (0, ½)³`: **every `d u`,
`u ∈ H̊Λ¹(Q) = H̊(curl, Q)`, is `d (S⁰ φ)` for some `φ ∈ H̊Λ⁰(Q)³ = H̊¹(Q; ℝ³)`**
(`Feec.Models.Cube.WeakSymmetry.curlPotential`), i.e.
`curl H̊(curl) = curl H̊¹(Q; ℝ³)`, the regular decomposition
`H̊(curl) = H̊¹(Q; ℝ³) + grad H̊¹(Q)` ([Hiptmair2002], Lemma 2.4; [HiptmairXu2007], §3) at the
level of `curl`. Consequently the hypotheses (H1)–(H3), (H6) of §5.1, the constants of Prop 5.3,
Props 5.1, 5.2, 5.4 and the rates of Thm 5.5 and of the scheme (6.5) on the cube hold
unconditionally (`bggHilb_hyps`, `bggStability'`, `bggShort_closedRange_exact'`,
`bgg_existsUnique_isSaddle'`, `cubeFEM_existsUnique'`, `cubeFEM_rate'`, `cubeFEM_rate_C2'`,
`cubeWave_rate'`).

**Proof.** The parity model of the cube alone does not give it: the potential must vanish on
`∂Q` in every component, a parity class different from that of `H̊Λ¹`. The argument goes
through a larger cell and an extension from the outside (as for the vector potentials of
[GiraultRaviart1986], Ch. I, §3):

1. (`Feec.Models.Cube.TorusHelmholtz.exists_helmholtz`) For a test `1`-form `u` on `Q`, on the
   cell `(-¼, ¾]³ ⊇ Q̄`, `u = ∇q + w` with `q = p + c · x`, `‖q‖, ‖w‖ ≲ ‖u‖`,
   `‖∇w‖ ≲ ‖u‖ + ‖curl u‖` (Fourier series on `𝕋³` and Gaffney's identity); on the shell
   `S = (-¼, ¾)³ ∖ Q̄`, where `u = 0`, `∇q = -w`, so `‖q‖_{H²(S)} ≲ ‖u‖_{H(curl)}`.
2. (`Feec.Models.Cube.ShellExtension.exists_n2_lift_le`) The Hestenes extension `s` of `q|_S`
   into `Q` agrees with `q` to first order on the faces and `‖s‖_{H²(Q)} ≲ ‖q‖_{H²(S)}`.
3. (`exists_fields`) `Φ = Θ (w + ∇s) = Θ (u - ∇r)`, `r = q - s`, `Θ` a cut-off equal to `1` near
   `Q̄`, is smooth, compactly supported, vanishes on the faces, has `curl Φ = curl u` on `Q`
   (`Φ = u - ∇r` near `Q̄`) and `‖Φ‖_{H¹(Q)} ≤ K ‖u‖_{H(curl)}`, `K` independent of `u`.
4. (`exists_potential_test`) By the cut-off lemma
   (`Feec.Models.Cube.DeRhamIdent.mem_closure_extDerivOp_of_tangential`), `Φ ∈ H̊Λ⁰(Q)³` and,
   as a `1`-form, `Φ = S⁰Φ ∈ H̊Λ¹(Q)` with `d_min Φ = curl u` (`mem_graph_minimal`).
5. (`exists_preimage_of_mem_closure`, `mem_closure_test`) Bounded preimages on the dense
   subspace of test fields give preimages on all of `H̊Λ¹(Q)`: choose them in
   `(ker (d ∘ S⁰))ᗮ`, where they are unique, so additive, so Cauchy along a sequence of test
   fields converging in the graph norm.

No hypothesis remains.

## Main results

* `exists_fields`, `mem_graph_minimal`, **`exists_potential_test`**.
* `exists_preimage_of_mem_closure`, `mem_closure_test`.
* **`Feec.Models.Cube.WeakSymmetry.curlPotential`**, `exists_curlPotential_bound`,
  `bggHilb_hyps`, `bggStability'`, `bggShort_closedRange_exact'`, `bgg_existsUnique_isSaddle'`;
  `cubeFEM_rate'`, `cubeFEM_rate_C2'`, `cubeFEM_existsUnique'`,
  `cubeWave_rate'`; `curlPotentialConst`, `bggStability_curlPotentialConst`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.1 (Props 5.1–5.3), §5.3 (the regularity hypothesis, Prop 5.4, Thm 5.5), §6.3 ((6.5))
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
  (regular decomposition)
* [R. Hiptmair, J. Xu, *Nodal auxiliary space preconditioning in H(curl) and H(div) spaces*][HiptmairXu2007],
  §3 (regular decomposition)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.4 (cut-off arguments in `W₀^{1,p}`)
* [V. Girault, P.-A. Raviart, *Finite Element Methods for Navier–Stokes Equations*][GiraultRaviart1986],
  Ch. I, §3 (vector potentials, extension from the outside)
* [M. R. Hestenes, *Extension of the Range of a Differentiable Function*][Hestenes1941]
  (the extension of step 2)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace Feec.Models.Cube.RegularDecomposition

open Feec.Models.Cube.ShellExtension Feec.Models.Cube.TorusHelmholtz Feec.Models.Cube.Geometry

/-! ### The cut-off near `Q̄` -/

/-- The centre `(¼, ¼, ¼)` of `Q`. -/
def ctr : Fin 3 → ℝ := fun _ => 1 / 4

/-- The cut-off `Θ`: `1` on the sup-norm ball `B(c, ⅜) ⊇ Q̄`, supported in `B(c, ½) = (-¼, ¾)³`. -/
def bump : ContDiffBump ctr := ⟨3 / 8, 1 / 2, by norm_num, by norm_num⟩

theorem mem_ball_ctr_iff {y : Fin 3 → ℝ} {r : ℝ} (hr : 0 < r) :
    y ∈ Metric.ball ctr r ↔ ∀ i, |y i - 1 / 4| < r := by
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  simp [ctr, Real.dist_eq]

theorem Q_subset_ball : Q (Fin 3) ⊆ Metric.ball ctr (3 / 8) := by
  intro y hy
  rw [mem_ball_ctr_iff (by norm_num)]
  intro i
  have := mem_Q.1 hy i
  rw [abs_lt]; constructor <;> linarith [this.1, this.2]

theorem bump_eq_one {y : Fin 3 → ℝ} (hy : y ∈ Metric.ball ctr (3 / 8)) : bump y = 1 :=
  bump.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)

theorem ball_subset_cell {r : ℝ} (hr : r ≤ 1 / 2) : Metric.ball ctr r ⊆ cell := by
  intro y hy
  have hr0 : 0 < r := lt_of_le_of_lt dist_nonneg hy
  rw [mem_ball_ctr_iff hr0] at hy
  intro i _
  have := abs_lt.1 (hy i)
  constructor <;> linarith [this.1, this.2]

/-! ### The shell and the linear part of the potential -/

theorem isOpen_shell : IsOpen shell := by
  have h1 : IsOpen {x : Fin 3 → ℝ | ∀ i, x i ∈ Ioo (-1 / 4 : ℝ) (3 / 4)} := by
    have : {x : Fin 3 → ℝ | ∀ i, x i ∈ Ioo (-1 / 4 : ℝ) (3 / 4)} =
        univ.pi fun _ => Ioo (-1 / 4 : ℝ) (3 / 4) := by ext; simp
    rw [this]; exact isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have h2 : IsOpen {x : Fin 3 → ℝ | ∃ i, x i ∉ Icc (0 : ℝ) (1 / 2)} := by
    have : {x : Fin 3 → ℝ | ∃ i, x i ∉ Icc (0 : ℝ) (1 / 2)} =
        (univ.pi fun _ => Icc (0 : ℝ) (1 / 2))ᶜ := by
      ext x; simp only [mem_ofPred_eq, mem_compl_iff, mem_univ_pi, not_forall]
    rw [this]; exact (isClosed_set_pi fun _ _ => isClosed_Icc).isOpen_compl
  exact h1.inter h2

theorem shell_subset_cell : shell ⊆ cell := fun _y hy i _ => ⟨(hy.1 i).1, (hy.1 i).2.le⟩

theorem notMem_Q_of_shell {y : Fin 3 → ℝ} (hy : y ∈ shell) : y ∉ Q (Fin 3) := by
  intro hQ
  obtain ⟨i, hi⟩ := hy.2
  exact hi ⟨(mem_Q.1 hQ i).1.le, (mem_Q.1 hQ i).2.le⟩

theorem notMem_Q_of_onFace {y : Fin 3 → ℝ} (hy : OnFace y) : y ∉ Q (Fin 3) := by
  intro hQ
  obtain ⟨i, hi⟩ := hy
  have := mem_Q.1 hQ i
  rcases hi with h | h <;> rw [h] at this <;> norm_num at this

/-- The linear function `y ↦ c · y`. -/
def lin (c : Fin 3 → ℝ) (y : Fin 3 → ℝ) : ℝ := ∑ a, c a * y a

theorem contDiff_lin (c : Fin 3 → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (lin c) := by
  unfold lin; fun_prop

theorem pd_lin (c : Fin 3 → ℝ) (j : Fin 3) (y : Fin 3 → ℝ) : partialDeriv j (lin c) y = c j := by
  have hl := ((contDiff_lin c).differentiable (by simp) (y + Pi.single j 0)).hasDerivAt_comp_add_single
  rw [Pi.single_zero, add_zero] at hl
  refine hl.unique ?_
  have : (fun s : ℝ => lin c (y + Pi.single j s)) = fun s => lin c y + c j * s := by
    funext s
    simp only [lin, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp
  rw [this]
  simpa using (HasDerivAt.const_mul (c j) (hasDerivAt_id (0 : ℝ))).const_add (lin c y)

theorem volume_shell_le : volume shell ≤ 1 := by
  calc volume shell ≤ volume (univ.pi fun _ : Fin 3 => Ioo (-1 / 4 : ℝ) (3 / 4)) :=
        measure_mono fun y hy => fun i _ => hy.1 i
    _ = 1 := by
        rw [Real.volume_pi_Ioo]
        norm_num

theorem eLpNorm_lin_shell_le (c : Fin 3 → ℝ) {M : ℝ} (hM : ∀ a, |c a| ≤ M) :
    eLpNorm (lin c) 2 (volume.restrict shell) ≤ ENNReal.ofReal (3 * M) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hb : ∀ᵐ y ∂volume.restrict shell, ‖lin c y‖ ≤ 3 * M := by
    refine ae_restrict_of_forall_mem isOpen_shell.measurableSet fun y hy => ?_
    rw [Real.norm_eq_abs, lin]
    calc |∑ a, c a * y a| ≤ ∑ a, |c a * y a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin 3, M := Finset.sum_le_sum fun a _ => by
          rw [abs_mul]
          have hya : |y a| ≤ 1 := by
            have := hy.1 a; rw [abs_le]; constructor <;> linarith [this.1, this.2]
          calc |c a| * |y a| ≤ M * 1 := mul_le_mul (hM a) hya (abs_nonneg _) hM0
            _ = M := mul_one M
      _ = 3 * M := by simp
  refine (eLpNorm_le_of_ae_bound (contDiff_lin c).continuous.aestronglyMeasurable hb).trans ?_
  rw [Measure.restrict_apply_univ]
  calc volume shell ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (3 * M)
      ≤ 1 * ENNReal.ofReal (3 * M) := by
        gcongr
        exact ENNReal.rpow_le_one volume_shell_le (by norm_num)
    _ = _ := one_mul _

/-! ### The potential of a test field -/

theorem Q_eq_pi : Q (Fin 3) = univ.pi fun _ => Ioo (0 : ℝ) (1 / 2) := by
  ext y; simp [mem_Q]

theorem NcurlQ_nonneg (u : Fin 3 → (Fin 3 → ℝ) → ℝ) : 0 ≤ NcurlQ u := by
  unfold NcurlQ
  have h : ∀ j l, 0 ≤ ∫ y in Q (Fin 3), curlR u j l y ^ 2 := fun j l =>
    integral_nonneg fun y => sq_nonneg _
  linarith [h 0 1, h 0 2, h 1 2]

theorem eLpNorm_restrict_mono {F : (Fin 3 → ℝ) → ℝ} {B B' : Set (Fin 3 → ℝ)} (h : B ⊆ B') :
    eLpNorm F 2 (volume.restrict B) ≤ eLpNorm F 2 (volume.restrict B') :=
  eLpNorm_mono_measure _ (Measure.restrict_mono h le_rfl)

theorem eLpNorm_congr_on {F G : (Fin 3 → ℝ) → ℝ} {B : Set (Fin 3 → ℝ)} (hB : MeasurableSet B)
    (h : ∀ y ∈ B, F y = G y) : eLpNorm F 2 (volume.restrict B) = eLpNorm G 2 (volume.restrict B) :=
  eLpNorm_congr_ae ((ae_restrict_iff' hB).2 (Eventually.of_forall h))

/-- **The potential of a test field** (the analytic core of the regular decomposition): for
test functions `uₐ` on `Q` there are smooth, compactly supported `Φₐ`, vanishing on the faces
`xᵢ ∈ {0, ½}`, with `Φ = u - ∇r` near `Q̄` (so `curl Φ = curl u` on `Q`) and
`‖Φₐ‖, ‖∂ⱼ Φₐ‖ ≤ K ‖u‖_{H(curl)}` in `L²(Q)`,
with a constant `K` independent of `u`.

Construction: `u = ∇q + w` on the cell `(-¼, ¾]³` (`TorusHelmholtz.exists_helmholtz`,
`q = p + c · x`), so `∇q = -w` on the shell; `s` is the shell extension of `q`
(`ShellExtension.lift`) and `Φ = Θ (w + ∇s) = Θ (u - ∇r)`, `r = q - s`, with `Θ` a cut-off equal
to `1` near `Q̄`. -/
theorem exists_fields : ∃ K : ℝ≥0, ∀ {u : Fin 3 → (Fin 3 → ℝ) → ℝ},
    (∀ a, Domain.IsTest (Q (Fin 3)) (u a)) →
    ∃ Φ : Fin 3 → (Fin 3 → ℝ) → ℝ,
      (∀ a, ContDiff ℝ (⊤ : ℕ∞) (Φ a)) ∧ (∀ a, HasCompactSupport (Φ a)) ∧
      (∀ a y, OnFace y → Φ a y = 0) ∧
      (∃ r : (Fin 3 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) r ∧
        ∀ y ∈ Q (Fin 3), ∀ a, Φ a =ᶠ[𝓝 y] fun z => u a z - partialDeriv a r z) ∧
      (∀ a, eLpNorm (Φ a) 2 (volume.restrict (Q (Fin 3))) ≤
        K * ENNReal.ofReal (Real.sqrt (NuQ u + NcurlQ u))) ∧
      (∀ j a, eLpNorm (partialDeriv j (Φ a)) 2 (volume.restrict (Q (Fin 3))) ≤
        K * ENNReal.ofReal (Real.sqrt (NuQ u + NcurlQ u))) := by
  obtain ⟨C, hC⟩ := exists_n2_lift_le
  refine ⟨1 + 16 * C, fun {u} hu => ?_⟩
  obtain ⟨p, c, w, hp, hw, hweq, hpb, hcb, hwb, hdwb⟩ := exists_helmholtz hu
  set R := ENNReal.ofReal (Real.sqrt (NuQ u + NcurlQ u))
  have hR1 : ENNReal.ofReal (Real.sqrt (NuQ u)) ≤ R :=
    ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (by linarith [NcurlQ_nonneg u]))
  have hR2 : ENNReal.ofReal (Real.sqrt (NcurlQ u + NuQ u)) = R := by rw [add_comm]
  have d1 : ∀ {H : (Fin 3 → ℝ) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) H → Differentiable ℝ H := fun h =>
    h.differentiable (by simp)
  -- the potential `q = p + c · x`
  set q : (Fin 3 → ℝ) → ℝ := p + lin c
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := hp.add (contDiff_lin c)
  have hpdq : ∀ j y, partialDeriv j q y = partialDeriv j p y + c j := fun j y => by
    rw [partialDeriv_add' (d1 hp) (d1 (contDiff_lin c)), Pi.add_apply, pd_lin]
  have hsh1 : ∀ j, ∀ y ∈ shell, partialDeriv j q y = -w j y := fun j y hy => by
    rw [hweq j y (shell_subset_cell hy), (hu j).eq_zero_of_notMem (notMem_Q_of_shell hy), hpdq]
    ring
  have hsh2 : ∀ j k, ∀ y ∈ shell, partialDeriv k (partialDeriv j q) y = -partialDeriv k (w j) y := fun j k y hy => by
    have hev : partialDeriv j q =ᶠ[𝓝 y] fun z => -w j z :=
      Filter.eventually_of_mem (isOpen_shell.mem_nhds hy) fun z hz => hsh1 j z hz
    rw [hev.partialDeriv_eq, partialDeriv]
    change fderiv ℝ (-w j) y (Pi.single k 1) = _
    rw [fderiv_neg]
    rfl
  -- the bound of `q` on the shell
  have hwsh : ∀ a, eLpNorm (w a) 2 (volume.restrict shell) ≤ R := fun a =>
    (eLpNorm_restrict_mono shell_subset_cell).trans ((hwb a).trans hR1)
  have hdwsh : ∀ j a, eLpNorm (partialDeriv j (w a)) 2 (volume.restrict shell) ≤ R := fun j a =>
    (eLpNorm_restrict_mono shell_subset_cell).trans ((hdwb j a).trans hR2.le)
  have n2q : n2 q shell ≤ 16 * R := by
    have h0 : eLpNorm q 2 (volume.restrict shell) ≤ 4 * R := by
      calc eLpNorm q 2 (volume.restrict shell)
          ≤ eLpNorm p 2 (volume.restrict shell) + eLpNorm (lin c) 2 (volume.restrict shell) :=
            eLpNorm_add_le one_le_two
        _ ≤ R + 3 * R := by
            gcongr
            · exact (eLpNorm_restrict_mono shell_subset_cell).trans (hpb.trans hR1)
            · refine (eLpNorm_lin_shell_le c hcb).trans ?_
              rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
              gcongr
        _ = 4 * R := by ring
    have h1 : ∀ j, eLpNorm (partialDeriv j q) 2 (volume.restrict shell) ≤ R := fun j => by
      rw [eLpNorm_congr_on isOpen_shell.measurableSet (hsh1 j)]
      change eLpNorm (-w j) 2 _ ≤ R
      rw [eLpNorm_neg]
      exact hwsh j
    have h2 : ∀ j k, eLpNorm (partialDeriv k (partialDeriv j q)) 2 (volume.restrict shell) ≤ R := fun j k => by
      rw [eLpNorm_congr_on isOpen_shell.measurableSet (hsh2 j k)]
      rw [show (fun y => -partialDeriv k (w j) y) = -partialDeriv k (w j) from rfl, eLpNorm_neg]
      exact hdwsh k j
    unfold n2
    calc _ ≤ 4 * R + ∑ _j : Fin 3, R + ∑ _j : Fin 3, ∑ _k : Fin 3, R :=
          add_le_add (add_le_add h0 (Finset.sum_le_sum fun j _ => h1 j))
            (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h2 j k)
      _ = 16 * R := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hlift : n2 (lift q) (Q (Fin 3)) ≤ C * (16 * R) := by
    rw [Q_eq_pi]
    exact (hC hq).trans (by gcongr)
  -- the fields
  set Φ : Fin 3 → (Fin 3 → ℝ) → ℝ := fun a y => bump y * (u a y - partialDeriv a (rem q) y)
  have hrem : ContDiff ℝ (⊤ : ℕ∞) (rem q) := contDiff_rem hq
  have hpdlift : ∀ a, partialDeriv a (lift q) = partialDeriv a q - partialDeriv a (rem q) := fun a =>
    partialDeriv_sub' (d1 hq) (d1 hrem) a
  have hloc : ∀ a, ∀ y ∈ Metric.ball ctr (3 / 8), Φ a y = w a y + partialDeriv a (lift q) y := by
    intro a y hy
    simp only [Φ, bump_eq_one hy, one_mul, hpdlift, Pi.sub_apply,
      hweq a y (ball_subset_cell (by norm_num) hy), hpdq]
    ring
  have hlocW : ∀ a, ∀ y ∈ Q (Fin 3), Φ a =ᶠ[𝓝 y] fun z => w a z + partialDeriv a (lift q) z :=
    fun a y hy => Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (Q_subset_ball hy))
      fun z hz => hloc a z hz
  have hlocU : ∀ a, ∀ y ∈ Q (Fin 3), Φ a =ᶠ[𝓝 y] fun z => u a z - partialDeriv a (rem q) z :=
    fun a y hy => Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (Q_subset_ball hy))
      fun z hz => by simp only [Φ, bump_eq_one hz, one_mul]
  have hΦs : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (Φ a) := fun a =>
    bump.contDiff.mul ((hu a).contDiff.sub (ContDiff.partialDeriv_infty hrem a))
  have hlift' : ContDiff ℝ (⊤ : ℕ∞) (lift q) := contDiff_lift hq
  refine ⟨Φ, hΦs, fun a => ?_, fun a y hy => ?_, ?_, fun a => ?_, fun j a => ?_⟩
  · exact bump.hasCompactSupport.mul_right
  · simp only [Φ, (hu a).eq_zero_of_notMem (notMem_Q_of_onFace hy), pd_rem_of_face hy
      (hq.of_le (by exact_mod_cast le_top)), sub_zero, mul_zero]
  · exact ⟨rem q, hrem, fun y hy a => hlocU a y hy⟩
  · rw [eLpNorm_congr_on measurableSet_Q fun y hy => hloc a y (Q_subset_ball hy)]
    calc eLpNorm (fun y => w a y + partialDeriv a (lift q) y) 2 (volume.restrict (Q (Fin 3)))
        ≤ eLpNorm (w a) 2 (volume.restrict (Q (Fin 3))) +
            eLpNorm (partialDeriv a (lift q)) 2 (volume.restrict (Q (Fin 3))) :=
          eLpNorm_add_le (f := w a) (g := partialDeriv a (lift q)) one_le_two
      _ ≤ R + C * (16 * R) := by
          gcongr
          · exact (eLpNorm_restrict_mono (fun y hy => (ball_subset_cell (by norm_num)
              (Q_subset_ball hy)))).trans ((hwb a).trans hR1)
          · exact (eLpNorm_pd_le_n2 _ _ a).trans hlift
      _ = (1 + 16 * C : ℝ≥0) * R := by push_cast; ring
  · have hpdΦ : ∀ y ∈ Q (Fin 3), partialDeriv j (Φ a) y = partialDeriv j (w a) y + partialDeriv j (partialDeriv a (lift q)) y :=
      fun y hy => by
        rw [(hlocW a y hy).partialDeriv_eq,
          show (fun z => w a z + partialDeriv a (lift q) z) = w a + partialDeriv a (lift q) from rfl,
          partialDeriv_add' (d1 (hw a)) (d1 (ContDiff.partialDeriv_infty hlift' a)), Pi.add_apply]
    rw [eLpNorm_congr_on measurableSet_Q hpdΦ]
    calc eLpNorm (fun y => partialDeriv j (w a) y + partialDeriv j (partialDeriv a (lift q)) y) 2 (volume.restrict (Q (Fin 3)))
        ≤ eLpNorm (partialDeriv j (w a)) 2 (volume.restrict (Q (Fin 3))) +
            eLpNorm (partialDeriv j (partialDeriv a (lift q))) 2 (volume.restrict (Q (Fin 3))) :=
          eLpNorm_add_le (f := partialDeriv j (w a)) (g := partialDeriv j (partialDeriv a (lift q))) one_le_two
      _ ≤ R + C * (16 * R) := by
          gcongr
          · exact (eLpNorm_restrict_mono (fun y hy => (ball_subset_cell (by norm_num)
              (Q_subset_ball hy)))).trans ((hdwb j a).trans hR2.le)
          · exact (eLpNorm_pd_pd_le_n2 _ _ a j).trans hlift
      _ = (1 + 16 * C : ℝ≥0) * R := by push_cast; ring

/-! ### Forms on the cube -/

section Bridge

open Feec.Domain Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

theorem univ_formIdx_zero : (Finset.univ : Finset (formIdx 3 0)) = {⟨∅, by decide⟩} := by decide

theorem univ_formIdx_one : (Finset.univ : Finset (formIdx 3 1)) =
    {⟨{0}, by decide⟩, ⟨{1}, by decide⟩, ⟨{2}, by decide⟩} := by decide

theorem univ_formIdx_two : (Finset.univ : Finset (formIdx 3 2)) =
    {⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{1, 2}, by decide⟩} := by decide

/-- The index `{a}` of the component `a` of a `1`-form. -/
abbrev sg (a : Fin 3) : formIdx 3 1 := ⟨{a}, by simp⟩

theorem sg_injective : Function.Injective sg := fun a b h => by
  simpa using congrArg Subtype.val h

theorem formIdx_one_cases (t : formIdx 3 1) : ∃ a, t = sg a := by
  have : t ∈ (Finset.univ : Finset (formIdx 3 1)) := Finset.mem_univ t
  rw [univ_formIdx_one] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h | h <;> exact ⟨_, h⟩

/-- The component of a `1`-form index. -/
def idx1 (t : formIdx 3 1) : Fin 3 := (formIdx_one_cases t).choose

theorem eq_sg_idx1 (t : formIdx 3 1) : t = sg (idx1 t) := (formIdx_one_cases t).choose_spec

@[simp] theorem idx1_sg (a : Fin 3) : idx1 (sg a) = a := sg_injective (eq_sg_idx1 (sg a)).symm

theorem sum_formIdx_zero {M : Type*} [AddCommMonoid M] (f : formIdx 3 0 → M) :
    ∑ s, f s = f ⟨∅, by decide⟩ := by
  rw [univ_formIdx_zero, Finset.sum_singleton]

theorem sum_formIdx_one {M : Type*} [AddCommMonoid M] (f : formIdx 3 1 → M) :
    ∑ t, f t = ∑ a, f (sg a) := by
  rw [univ_formIdx_one, Fin.sum_univ_three, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

theorem sum_formIdx_two {M : Type*} [AddCommMonoid M] (f : formIdx 3 (1 + 1) → M) :
    ∑ t, f t = f ⟨{0, 1}, by decide⟩ + f ⟨{0, 2}, by decide⟩ + f ⟨{1, 2}, by decide⟩ := by
  rw [univ_formIdx_two, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, add_assoc]

theorem isBounded_cubeDomain : Bornology.IsBounded (cubeDomain 3) := by
  rw [cubeDomain_eq_Q]; exact isBounded_openCube _ _

theorem memLp_cube {f : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (cubeDomain 3)) :=
  memLp_of_continuous (isOpen_cubeDomain 3).measurableSet isBounded_cubeDomain hf

theorem norm_toLp_cube {f : (Fin 3 → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict (cubeDomain 3))) :
    ‖hf.toLp f‖ = (eLpNorm f 2 (volume.restrict (Q (Fin 3)))).toReal := by
  rw [Lp.norm_toLp, cubeDomain_eq_Q]

theorem norm_toLp_sq {Ω : Set (Fin 3 → ℝ)} {f : (Fin 3 → ℝ) → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) : ‖hf.toLp f‖ ^ 2 = ∫ y in Ω, f y ^ 2 := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  have h0 : 0 ≤ ∫ y in Ω, ‖f y‖ ^ (2 : ℝ≥0∞).toReal := integral_nonneg fun y => by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

theorem exists_bound_family {ι : Type*} [Fintype ι] {f : ι → (Fin 3 → ℝ) → ℝ}
    (hf : ∀ i, Continuous (f i)) (hc : ∀ i, HasCompactSupport (f i)) :
    ∃ M, 0 ≤ M ∧ ∀ i y, |f i y| ≤ M := by
  choose M hM using fun i => (hc i).exists_bound_of_continuous (hf i)
  refine ⟨∑ i, |M i|, by positivity, fun i y => ?_⟩
  calc |f i y| = ‖f i y‖ := (Real.norm_eq_abs _).symm
    _ ≤ M i := hM i y
    _ ≤ |M i| := le_abs_self _
    _ ≤ ∑ i, |M i| := Finset.single_le_sum (f := fun i => |M i|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ i)

/-- **Smooth compactly supported forms vanishing on the faces lie in `H̊Λᵏ(Q)`**, with `d_min`
the classical exterior derivative ([Brezis2011], §9.4: cut-off). -/
theorem mem_graph_minimal {k : ℤ} {ψ : formIdx 3 k → (Fin 3 → ℝ) → ℝ}
    (hψ : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (ψ s)) (hc : ∀ s, HasCompactSupport (ψ s))
    (hV : ∀ s y, OnFace y → ψ s y = 0) :
    (toL2F (fun s => memLp_cube (hψ s).continuous),
      toL2F (fun t => memLp_cube
        ((ConstCoeffOp.contDiff_apply (extDerivOp ℝ 3 k) hψ t).continuous))) ∈
      ((extDerivOp ℝ 3 k).minimal (cubeDomain 3)).graph := by
  obtain ⟨M, -, hM⟩ := exists_bound_family (fun s => (hψ s).continuous) hc
  have hd : ∀ (sj : formIdx 3 k × Fin 3),
      Continuous fun y => fderiv ℝ (ψ sj.1) y (Pi.single sj.2 1) :=
    fun sj => ((hψ sj.1).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : ∀ (sj : formIdx 3 k × Fin 3),
      HasCompactSupport fun y => fderiv ℝ (ψ sj.1) y (Pi.single sj.2 1) :=
    fun sj => (hc sj.1).fderiv_apply (𝕜 := ℝ) _
  obtain ⟨L, hL0, hL⟩ := exists_bound_family hd hdc
  rw [ConstCoeffOp.minimal_graph _ (isOpen_cubeDomain 3), ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe]
  have key : ∀ Ω, Ω = Q (Fin 3) → ∀ (h1 : ∀ s, MemLp (ψ s) 2 (volume.restrict Ω))
      (h2 : ∀ t, MemLp ((extDerivOp ℝ 3 k).apply ψ t) 2 (volume.restrict Ω)),
      (toL2F h1, toL2F h2) ∈ closure ((extDerivOp ℝ 3 k).testGraph Ω :
        Set (L2F ℝ Ω (formIdx 3 k) × L2F ℝ Ω (formIdx 3 (k + 1)))) := by
    rintro Ω rfl h1 h2
    exact DeRhamIdent.mem_closure_extDerivOp_of_tangential hψ hM hL0 (fun s j y => hL (s, j) y)
      (fun s j _ y hy => hV s y ⟨j, hy⟩) h1 h2
  exact key _ (cubeDomain_eq_Q 3) _ _

theorem extDerivOp_zero_const (f : (Fin 3 → ℝ) → ℝ) (j : Fin 3) (y : Fin 3 → ℝ) :
    (extDerivOp ℝ 3 0).apply (fun _ => f) (sg j) y = partialDeriv j f y := by
  rw [extDerivOp_zero_apply]; rfl

theorem curlR_eq (φ : formIdx 3 1 → (Fin 3 → ℝ) → ℝ) {j l : Fin 3} (hjl : j < l)
    (y : Fin 3 → ℝ) :
    (extDerivOp ℝ 3 1).apply φ ⟨{j, l}, by rw [Finset.card_pair hjl.ne]; norm_num⟩ y =
      curlR (fun a => φ (sg a)) j l y := by
  rw [extDerivOp_one_apply_pair φ hjl]; rfl

theorem toReal_le_of_eLpNorm_le {f : (Fin 3 → ℝ) → ℝ} {K : ℝ≥0} {S : ℝ}
    (h : eLpNorm f 2 (volume.restrict (Q (Fin 3))) ≤ K * ENNReal.ofReal (Real.sqrt S)) :
    (eLpNorm f 2 (volume.restrict (Q (Fin 3)))).toReal ≤ K * Real.sqrt S := by
  have hfin : (K : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt S) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  calc (eLpNorm f 2 (volume.restrict (Q (Fin 3)))).toReal
      ≤ ((K : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt S)).toReal := ENNReal.toReal_mono hfin h
    _ = K * Real.sqrt S := by
        rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- **The potential of a test `1`-form**: for every test `1`-form `u` on `Q` there is
`Φ ∈ H̊Λ⁰(Q)³` with `curl S⁰Φ = curl u` and `‖Φ‖ ≤ C ‖u‖_{H(curl)}`, `C` independent of `u`. -/
theorem exists_potential_test : ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : formIdx 3 1 → (Fin 3 → ℝ) → ℝ)
    (hφ : IsTestField (cubeDomain 3) φ), ∃ Φ : Vt0,
      bggD1 (bggS0 Φ) = testField ((extDerivOp ℝ 3 1).isTestField_apply hφ) ∧
      ‖Φ‖ ≤ C * Real.sqrt (‖testField hφ‖ ^ 2 +
        ‖testField ((extDerivOp ℝ 3 1).isTestField_apply hφ)‖ ^ 2) := by
  obtain ⟨K, hK⟩ := exists_fields
  refine ⟨4 * K, by positivity, fun φ hφ => ?_⟩
  set u : Fin 3 → (Fin 3 → ℝ) → ℝ := fun a => φ (sg a) with hu_def
  have hu : ∀ a, IsTest (Q (Fin 3)) (u a) := fun a => cubeDomain_eq_Q 3 ▸ hφ (sg a)
  obtain ⟨Φ, hΦs, hΦc, hΦV, ⟨r, hr, hloc⟩, hΦb, hdΦb⟩ := hK hu
  set S := NuQ u + NcurlQ u
  -- the components of `Φ` in `H̊Λ⁰(Q)`
  have hmem0 := fun a => mem_graph_minimal (k := 0) (ψ := fun _ => Φ a) (fun _ => hΦs a)
    (fun _ => hΦc a) (fun _ y hy => hΦV a y hy)
  have hdom0 := fun a => LinearPMap.mem_domain_of_mem_graph (hmem0 a)
  set Φv : Fin 3 → V0 := fun a => D0.toGraphSpace ⟨_, hdom0 a⟩
  set Φt : Vt0 := WithLp.toLp 2 Φv
  -- the `1`-form `Φ` in `H̊Λ¹(Q)`
  set Φ1 : formIdx 3 1 → (Fin 3 → ℝ) → ℝ := fun t => Φ (idx1 t)
  have hmem1 := mem_graph_minimal (k := 1) (ψ := Φ1) (fun t => hΦs _) (fun t => hΦc _)
    (fun t y hy => hΦV _ y hy)
  have hS0 : D1.graphFst (bggS0 Φt) = toL2F (fun t => memLp_cube (hΦs (idx1 t)).continuous) := by
    rw [graphFst_bggS0]
    refine PiLp.ext fun t => ?_
    obtain ⟨a, rfl⟩ := formIdx_one_cases t
    rw [wsL2_zero_apply]
    change (memLp_cube (hΦs a).continuous).toLp (Φ a) =
      (memLp_cube (hΦs (idx1 (sg a))).continuous).toLp (Φ (idx1 (sg a)))
    exact MemLp.toLp_congr _ _ (by rw [idx1_sg])
  have hD : bggD1 (bggS0 Φt) = toL2F (fun t => memLp_cube
      ((ConstCoeffOp.contDiff_apply (extDerivOp ℝ 3 1) (fun t => hΦs (idx1 t)) t).continuous)) := by
    have h1 : (D1.graphFst (bggS0 Φt), D1.graphSnd (bggS0 Φt)) ∈ D1.graph :=
      LinearPMap.mem_graphL2.1 (bggS0 Φt).2
    exact LinearPMap.mem_graph_snd_inj D1 h1 hmem1 hS0
  -- `curl Φ = curl u` on `Q`
  have hcurl : ∀ y ∈ cubeDomain 3, ∀ t,
      (extDerivOp ℝ 3 1).apply Φ1 t y = (extDerivOp ℝ 3 1).apply φ t y := by
    intro y hy t
    have hyQ : y ∈ Q (Fin 3) := cubeDomain_eq_Q 3 ▸ hy
    set dr : formIdx 3 1 → (Fin 3 → ℝ) → ℝ := fun s => (extDerivOp ℝ 3 0).apply (fun _ => r) s
    have hdr : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (dr s) :=
      ConstCoeffOp.contDiff_apply _ fun _ => hr
    set G : formIdx 3 1 → (Fin 3 → ℝ) → ℝ := φ + (-1 : ℝ) • dr
    have hG : ∀ s, Φ1 s =ᶠ[𝓝 y] G s := by
      intro s
      obtain ⟨a, rfl⟩ := formIdx_one_cases s
      filter_upwards [hloc y hyQ a] with z hz
      simp only [Φ1, idx1_sg, hz, G, dr, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        extDerivOp_zero_const, u]
      ring
    rw [DeRhamIdent.apply_congr_of_eventuallyEq _ hG t, show G = φ + (-1 : ℝ) • dr from rfl,
      ConstCoeffOp.apply_add _ (f := φ) (g := (-1 : ℝ) • dr)
      (fun s => (hφ s).contDiff) (fun s => (hdr s).const_smul (-1 : ℝ)),
      ConstCoeffOp.apply_smul _ _ hdr]
    have hcp : (extDerivOp ℝ 3 1).apply dr = 0 :=
      isComplexPair_extDerivOp 0 _ fun _ => hr
    rw [hcp]
    simp
  have hT : toL2F (fun t => memLp_cube
      ((ConstCoeffOp.contDiff_apply (extDerivOp ℝ 3 1) (fun t => hΦs (idx1 t)) t).continuous)) =
      testField ((extDerivOp ℝ 3 1).isTestField_apply hφ) := by
    refine PiLp.ext fun t => ?_
    rw [testField_apply]
    exact MemLp.toLp_congr (memLp_cube ((ConstCoeffOp.contDiff_apply (extDerivOp ℝ 3 1)
      (fun t => hΦs (idx1 t)) t).continuous)) ((extDerivOp ℝ 3 1).isTestField_apply hφ t).memLp
      ((ae_restrict_iff' (isOpen_cubeDomain 3).measurableSet).2
        (Eventually.of_forall fun y hy => hcurl y hy t))
  refine ⟨Φt, hD.trans hT, ?_⟩
  -- the bound
  have hb0 : ∀ a, ‖(memLp_cube (hΦs a).continuous).toLp (Φ a)‖ ≤ K * Real.sqrt S := fun a => by
    rw [norm_toLp_cube]; exact toReal_le_of_eLpNorm_le (hΦb a)
  have hb1 : ∀ j a, ‖(memLp_cube ((ContDiff.partialDeriv_infty (hΦs a) j).continuous)).toLp (partialDeriv j (Φ a))‖ ≤
      K * Real.sqrt S := fun j a => by
    rw [norm_toLp_cube]; exact toReal_le_of_eLpNorm_le (hdΦb j a)
  have hKS : 0 ≤ K * Real.sqrt S := by positivity
  have hv : ∀ a, ‖Φv a‖ ^ 2 ≤ 4 * (K * Real.sqrt S) ^ 2 := by
    intro a
    have hD0 := ((LinearPMap.image_iff (hdom0 a)).2 (hmem0 a)).symm
    rw [norm_toGraphSpace_sq, hD0, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
      sum_formIdx_zero]
    erw [sum_formIdx_one]
    rw [Fin.sum_univ_three]
    have e : ∀ j, ‖(toL2F (fun t => memLp_cube ((ConstCoeffOp.contDiff_apply (extDerivOp ℝ 3 0)
        (fun _ => hΦs a) t).continuous)) : L2F ℝ (cubeDomain 3) (formIdx 3 1)) (sg j)‖ =
        ‖(memLp_cube ((ContDiff.partialDeriv_infty (hΦs a) j).continuous)).toLp (partialDeriv j (Φ a))‖ := fun j =>
      congrArg norm (MemLp.toLp_congr (memLp_cube ((ConstCoeffOp.contDiff_apply
        (extDerivOp ℝ 3 0) (fun _ => hΦs a) (sg j)).continuous))
        (memLp_cube ((ContDiff.partialDeriv_infty (hΦs a) j).continuous))
        (Eventually.of_forall fun y => extDerivOp_zero_const (Φ a) j y))
    rw [e, e, e]
    change ‖(memLp_cube (hΦs a).continuous).toLp (Φ a)‖ ^ 2 + _ ≤ _
    have h0 := hb0 a; have h1 := hb1 0 a; have h2 := hb1 1 a; have h3 := hb1 2 a
    have p0 := pow_le_pow_left₀ (norm_nonneg _) h0 2
    have p1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have p2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have p3 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    linarith
  have hΦt : ‖Φt‖ ^ 2 ≤ (4 * K * Real.sqrt S) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
    change ‖Φv 0‖ ^ 2 + ‖Φv 1‖ ^ 2 + ‖Φv 2‖ ^ 2 ≤ _
    nlinarith [hv 0, hv 1, hv 2]
  have hS : S = ‖testField hφ‖ ^ 2 + ‖testField ((extDerivOp ℝ 3 1).isTestField_apply hφ)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, sum_formIdx_one, sum_formIdx_two]
    simp only [testField_apply, toL2, norm_toLp_sq, cubeDomain_eq_Q]
    simp only [S, NuQ, NcurlQ, u]
    simp only [curlR_eq φ (show (0 : Fin 3) < 1 by decide),
      curlR_eq φ (show (0 : Fin 3) < 2 by decide), curlR_eq φ (show (1 : Fin 3) < 2 by decide)]
  rw [← hS]
  have h4 : 0 ≤ 4 * K * Real.sqrt S := by positivity
  calc ‖Φt‖ ≤ 4 * K * Real.sqrt S := (pow_le_pow_iff_left₀ (norm_nonneg _) h4 two_ne_zero).1 hΦt
    _ = (4 * K : ℝ≥0) * Real.sqrt S := by push_cast; ring

end Bridge

/-! ### From test fields to `CurlPotential` -/

/-- **Bounded preimages on a dense subspace give preimages on its closure** (Hilbert space
`X`): if every `M z`, `z ∈ S`, has an `L`-preimage of norm `≤ C ‖z‖`, then so does every `M z`
with `z ∈ cl S`. The preimages are taken in `(ker L)ᗮ`, where they are unique, hence additive
in `z`, hence Cauchy along any sequence `zₙ → z` of `S`. -/
theorem exists_preimage_of_mem_closure {X Y Z : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : X →L[ℝ] Y) (M : Z →L[ℝ] Y) (S : Submodule ℝ Z)
    {C : ℝ} (h : ∀ z ∈ S, ∃ x, L x = M z ∧ ‖x‖ ≤ C * ‖z‖) {z : Z}
    (hz : z ∈ closure (S : Set Z)) : ∃ x, L x = M z := by
  set K := LinearMap.ker (L : X →ₗ[ℝ] Y)
  have hK : IsClosed (K : Set X) := L.isClosed_ker
  have : CompleteSpace K := hK.completeSpace_coe
  have hpre : ∀ z ∈ S, ∃ x ∈ Kᗮ, L x = M z ∧ ‖x‖ ≤ C * ‖z‖ := by
    intro z hz
    obtain ⟨x, hx, hn⟩ := h z hz
    have h1 : K.starProjection x ∈ K := K.starProjection_apply_mem x
    have h2 : x - K.starProjection x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
    refine ⟨x - K.starProjection x, h2, ?_, ?_⟩
    · have : L (K.starProjection x) = 0 := h1
      rw [map_sub, this, sub_zero, hx]
    · refine le_trans ?_ hn
      have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (K.starProjection x)
        (x - K.starProjection x) (K.inner_right_of_mem_orthogonal h1 h2)
      rw [add_sub_cancel] at hpy
      nlinarith [norm_nonneg (K.starProjection x), norm_nonneg (x - K.starProjection x),
        norm_nonneg x]
  have huniq : ∀ a ∈ Kᗮ, ∀ b ∈ Kᗮ, L a = L b → a = b := by
    intro a ha b hb hab
    have h1 : a - b ∈ K := by
      change L (a - b) = 0
      rw [map_sub, hab, sub_self]
    have h2 : a - b ∈ Kᗮ := Kᗮ.sub_mem ha hb
    have := K.inner_right_of_mem_orthogonal h1 h2
    rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at this
    exact this
  obtain ⟨zs, hzs, hlim⟩ := mem_closure_iff_seq_limit.1 hz
  choose x hxK hxL hxn using fun n => hpre (zs n) (hzs n)
  have hdiff : ∀ m n, ‖x m - x n‖ ≤ C * ‖zs m - zs n‖ := by
    intro m n
    obtain ⟨y, hyK, hyL, hyn⟩ := hpre (zs m - zs n) (S.sub_mem (hzs m) (hzs n))
    have : x m - x n = y := huniq _ (Kᗮ.sub_mem (hxK m) (hxK n)) _ hyK
      (by rw [map_sub, hxL, hxL, hyL, map_sub])
    rw [this]; exact hyn
  have hcz : CauchySeq zs := hlim.cauchySeq
  have hcx : CauchySeq x := by
    rw [Metric.cauchySeq_iff] at hcz ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcz (ε / (|C| + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [dist_eq_norm] at h1 ⊢
    calc ‖x m - x n‖ ≤ C * ‖zs m - zs n‖ := hdiff m n
      _ ≤ |C| * ‖zs m - zs n‖ := by gcongr; exact le_abs_self C
      _ ≤ |C| * (ε / (|C| + 1)) := by gcongr
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [abs_nonneg C]
  obtain ⟨x0, hx0⟩ := cauchySeq_tendsto_of_complete hcx
  refine ⟨x0, tendsto_nhds_unique ((L.continuous.tendsto x0).comp hx0) ?_⟩
  have : (L ∘ x) = M ∘ zs := funext fun n => hxL n
  rw [this]
  exact (M.continuous.tendsto z).comp hlim

open Feec.Domain Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry in
/-- **The test `1`-forms are dense in `H̊Λ¹(Q)`** (with the graph norm). -/
theorem mem_closure_test (v : V1) :
    v ∈ closure ((testFieldSub ℝ (cubeDomain 3) (formIdx 3 1)).comap
      (D1.graphFst : V1 →ₗ[ℝ] W1) : Set V1) := by
  have hQ := isOpen_cubeDomain 3
  have hmem := ConstCoeffOp.mem_closure_minimal (extDerivOp ℝ 3 1) hQ (graphDom D1 v)
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hmem
  obtain ⟨ps, hps, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
  choose φ hφ hpφ using hps
  set zs : ℕ → V1 := fun n =>
    D1.toGraphSpace ⟨testField (hφ n), ConstCoeffOp.testField_mem_minimal_domain _ hQ (hφ n)⟩
  have hzs : ∀ n, zs n ∈ (testFieldSub ℝ (cubeDomain 3) (formIdx 3 1)).comap
      (D1.graphFst : V1 →ₗ[ℝ] W1) := fun n => testField_mem_testFieldSub (hφ n)
  refine mem_closure_of_tendsto (b := atTop) ?_ (Eventually.of_forall hzs)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set x2 : L2F ℝ (cubeDomain 3) (formIdx 3 (1 + 1)) := D1 (graphDom D1 v)
  have h1 : Tendsto (fun n => ‖(ps n).1 - (graphDom D1 v : W1)‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      ((continuous_fst.tendsto ((graphDom D1 v : W1), x2)).comp hlim)
  have h2 : Tendsto (fun n => ‖(ps n).2 - x2‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      ((continuous_snd.tendsto ((graphDom D1 v : W1), x2)).comp hlim)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using h1.add h2)
  have hfst : D1.graphFst (zs n - v) = (ps n).1 - (graphDom D1 v : W1) := by
    rw [map_sub, hpφ n]; rfl
  have hsnd : D1.graphSnd (zs n - v) = (ps n).2 - x2 := by
    rw [map_sub, hpφ n, ← apply_graphDom D1 v]
    simp only [zs, LinearPMap.graphSnd_toGraphSpace]
    rw [ConstCoeffOp.minimal_testField _ hQ (hφ n)]
  have hn := norm_sq_graphSpace D1 (zs n - v)
  rw [hfst, hsnd] at hn
  set a := ‖(ps n).1 - (graphDom D1 v : W1)‖
  set b := ‖(ps n).2 - x2‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have e : ‖zs n - v‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
    rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  rw [e]
  calc Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt ((a + b) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = a + b := Real.sqrt_sq (by positivity)


end Feec.Models.Cube.RegularDecomposition

/-! ### `CurlPotential` and the unconditional theorems of Chapter 5 and §6.3 on the cube -/

namespace Feec.Models.Cube.WeakSymmetry

open scoped InnerProductSpace RealInnerProductSpace
open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.RegularDecomposition

/-- **The regularity hypothesis holds on the cube**: `curl H̊(curl, Q) = curl S⁰ H̊¹(Q; ℝ³)`, i.e.
every `d u`, `u ∈ H̊Λ¹(Q)`, is `d (S⁰ φ)` for some `φ ∈ H̊Λ⁰(Q)³` (the regular decomposition
`H̊(curl) = H̊¹(Q; ℝ³) + grad H̊¹(Q)` of [Hiptmair2002], Lemma 2.4 and [HiptmairXu2007], §3 at the
level of `curl`; [GiraultRaviart1986], Ch. I, §3 for the extension argument). -/
theorem curlPotential : CurlPotential := by
  obtain ⟨C, -, hC⟩ := exists_potential_test
  set S : Submodule ℝ V1 :=
    (testFieldSub ℝ (cubeDomain 3) (formIdx 3 1)).comap (D1.graphFst : V1 →ₗ[ℝ] W1)
  have hS : ∀ z ∈ S, ∃ Φ, (bggD1 ∘L bggS0) Φ = bggD1 z ∧ ‖Φ‖ ≤ C * ‖z‖ := by
    intro z hz
    obtain ⟨φ, hφ, hφz⟩ := hz
    obtain ⟨Φ, h1, h2⟩ := hC φ hφ
    have hdom : graphDom D1 z = ⟨testField hφ,
        ConstCoeffOp.testField_mem_minimal_domain _ (isOpen_cubeDomain 3) hφ⟩ :=
      Subtype.ext hφz
    have hz2 : bggD1 z = testField ((extDerivOp ℝ 3 1).isTestField_apply hφ) := by
      change D1.graphSnd z = _
      rw [← apply_graphDom D1 z, hdom, ConstCoeffOp.minimal_testField _ (isOpen_cubeDomain 3) hφ]
    have hzn : ‖z‖ = Real.sqrt (‖testField hφ‖ ^ 2 +
        ‖testField ((extDerivOp ℝ 3 1).isTestField_apply hφ)‖ ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg z), norm_sq_graphSpace, ← hz2, ← hφz]
      rfl
    exact ⟨Φ, h1.trans hz2.symm, by rwa [hzn]⟩
  rintro _ ⟨v, rfl⟩
  obtain ⟨Φ, hΦ⟩ := exists_preimage_of_mem_closure (bggD1 ∘L bggS0) bggD1 S hS
    (mem_closure_test v)
  exact ⟨Φ, hΦ⟩

/-- **The constant of the regularity hypothesis**: a potential can be chosen with
`‖φ‖_{H̊Λ⁰(Q)³} ≤ C_R ‖d u‖` (`CurlPotential.exists_bound` with `curlPotential`). -/
theorem exists_curlPotential_bound :
    ∃ CR, 0 ≤ CR ∧ ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖ :=
  curlPotential.exists_bound

/-- **A regularity constant `C_R` of the cube**, chosen from `exists_curlPotential_bound`; it lets
callers of the constructions parameterized by `C_R` (`cubeFEMReg`, `bggStability_of`) use them
without threading the constant (`bggStability_curlPotentialConst`). -/
def curlPotentialConst : ℝ := Classical.choose exists_curlPotential_bound

theorem curlPotentialConst_nonneg : 0 ≤ curlPotentialConst :=
  (Classical.choose_spec exists_curlPotential_bound).1

/-- Every `d u`, `u ∈ H̊Λ¹(Q)`, is `d (S⁰ φ)` with `‖φ‖ ≤ curlPotentialConst · ‖d u‖`. -/
theorem exists_curlPotential_le (u : V1) :
    ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ curlPotentialConst * ‖bggD1 u‖ :=
  (Classical.choose_spec exists_curlPotential_bound).2 u

/-- **The continuous constants of [QuennevilleBelair2015], Prop 5.3 on the cube** with the
regularity constant `curlPotentialConst` (`bggStability_of` with `exists_curlPotential_le`). -/
theorem bggStability_curlPotentialConst :
    Feec.BGG.Stability bggSegment (2 * Real.pi)⁻¹ curlPotentialConst (Real.sqrt 2) :=
  bggStability_of curlPotentialConst_nonneg exists_curlPotential_le

/-- **The hypotheses (H1)–(H3), (H6) of [QuennevilleBelair2015], §5.1 on the cube hold**
(`bggHyps` with `curlPotential`). -/
theorem bggHilb_hyps : bggHilb.Hyps := bggHyps curlPotential

/-- **The continuous constants of [QuennevilleBelair2015], Prop 5.3 on the cube**, `C_p = (2π)⁻¹`,
`C_S = √2` and the regularity constant `C_R` (`bggStability` with `curlPotential`). -/
theorem bggStability' : ∃ CR, Feec.BGG.Stability bggSegment (2 * Real.pi)⁻¹ CR (Real.sqrt 2) :=
  bggStability curlPotential

/-- **[QuennevilleBelair2015], Prop 5.1 on the cube, unconditionally**: the complex (5.1)
`Γ̄ → W̃¹ → W² × W̃²` built from (4.16) is a closed, exact short Hilbert complex
(`bggShort_closedRange_exact` with `curlPotential`). -/
theorem bggShort_closedRange_exact' :
    IsClosed (LinearMap.range (bggHilb.toShort bggHilb_hyps bggS0_injective).d₀.toFun :
      Set (Wv W1)) ∧
    IsClosed (LinearMap.range (bggHilb.toShort bggHilb_hyps bggS0_injective).d₁.toFun :
      Set (WithLp 2 (W2 × Wv W2))) ∧
    (bggHilb.toShort bggHilb_hyps bggS0_injective).d₁.ker =
      LinearMap.range (bggHilb.toShort bggHilb_hyps bggS0_injective).d₀.toFun ∧
    (bggHilb.toShort bggHilb_hyps bggS0_injective).d₀.ker = ⊥ :=
  bggShort_closedRange_exact curlPotential

/-- **[QuennevilleBelair2015], Prop 5.2 on the cube, unconditionally**: the saddle point problem
(5.3) for (4.16) is well posed (`bgg_existsUnique_isSaddle` with `curlPotential`). -/
theorem bgg_existsUnique_isSaddle' :
    (∀ f : Wv W1, ∃! xl : Feec.BGG.Xsp V0 Vt0 Vt1 × bggHilb.Wcheck,
      bggHilb.IsSaddle f xl.1 xl.2) ∧
    ∃ C, ∀ (f : Wv W1) (x : Feec.BGG.Xsp V0 Vt0 Vt1) (l : bggHilb.Wcheck),
      bggHilb.IsSaddle f x l → ‖x‖ + ‖l‖ ≤ C * ‖f‖ :=
  bgg_existsUnique_isSaddle curlPotential


section Rate

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- **[QuennevilleBelair2015], Thm 5.5 on the cube with the elements of Table 5.1, with rate,
unconditionally** (`cubeFEM_rate` with the constant of `curlPotential`). -/
theorem cubeFEM_rate' :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {lam : W1}
      {F : Wv U1 →ₗ[ℝ] ℝ} {L : ℝ}, 0 ≤ L →
      (∀ τ ψ, ⟪σ, τ⟫ - ⟪u, bggSegment.dt0 ψ⟫ -
        ⟪lam, ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) →
      (∀ v, ⟪bggSegment.dt0 φ, v⟫ + ⟪bggSegment.S1 u, bggSegment.S1 v⟫ +
        ⟪bggSegment.dt1 u, bggSegment.dt1 v⟫ = F v) →
      bggSegment.d0 σ = bggSegment.S0 φ →
      IsCsFormMin 0 0 L (σ : W0) → (∀ a, IsCsFormMin 0 0 L (φ a : W0)) →
      (∀ a, IsCsFormMin 0 1 L (u a : W1)) → IsCsFormMin 0 2 L (bggSegment.S1 u) →
      ‖lam‖ ≤ L → ‖bggSegment.S1 u‖ ≤ L →
      (∀ w : U1, |⟪bggSegment.S1 u, bggSegment.d1 w⟫| ≤ L * ‖w‖) →
      ∀ {σh : U0} {φh : Wv U0} {uh : Wv U1} {lh : U1},
      σh ∈ (cubeFEM hT hB N).V0h → φh ∈ (cubeFEM hT hB N).Vt0h →
      uh ∈ (cubeFEM hT hB N).Vt1h →
      (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
        ⟪σh, τ⟫ - ⟪uh, bggSegment.dt0 ψ⟫ -
          ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) →
      (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
        ⟪(cubeFEM hT hB N).S1h uh, (cubeFEM hT hB N).S1h v⟫ +
          ⟪bggSegment.dt1 uh, bggSegment.dt1 v⟫ = F v) →
      (∀ μ ∈ (cubeFEM hT hB N).V1h, ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) →
      Feec.BGG.graphSq bggSegment.d0 (σ - σh) + Feec.BGG.graphSq bggSegment.dt0 (φ - φh) +
        (cubeFEM hT hB N).gnSq (u - uh) ≤ (K * L * meshSize N) ^ 2 :=
  exists_curlPotential_bound.elim fun _ h => cubeFEM_rate hT hB h.1 h.2

/-- **[QuennevilleBelair2015], Thm 5.5 for `C²` solutions, unconditionally** (`cubeFEM_rate_C2`
with the constant of `curlPotential`). -/
theorem cubeFEM_rate_C2' :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {lam : W1}
      {F : Wv U1 →ₗ[ℝ] ℝ} {L : ℝ}, 0 ≤ L →
      (∀ τ ψ, ⟪σ, τ⟫ - ⟪u, bggSegment.dt0 ψ⟫ -
        ⟪lam, ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) →
      (∀ v, ⟪bggSegment.dt0 φ, v⟫ + ⟪bggSegment.S1 u, bggSegment.S1 v⟫ +
        ⟪bggSegment.dt1 u, bggSegment.dt1 v⟫ = F v) →
      bggSegment.d0 σ = bggSegment.S0 φ →
      IsCsFormMin 0 0 L (σ : W0) → (∀ a, IsCsFormMin 0 0 L (φ a : W0)) →
      (∀ a, IsCsFormMin 0 1 L (u a : W1)) → ‖lam‖ ≤ L →
      IsCsFormMin 0 2 L (bggSegment.S1 u) →
      ∀ {σh : U0} {φh : Wv U0} {uh : Wv U1} {lh : U1},
      σh ∈ (cubeFEM hT hB N).V0h → φh ∈ (cubeFEM hT hB N).Vt0h →
      uh ∈ (cubeFEM hT hB N).Vt1h →
      (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
        ⟪σh, τ⟫ - ⟪uh, bggSegment.dt0 ψ⟫ -
          ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) →
      (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
        ⟪(cubeFEM hT hB N).S1h uh, (cubeFEM hT hB N).S1h v⟫ +
          ⟪bggSegment.dt1 uh, bggSegment.dt1 v⟫ = F v) →
      (∀ μ ∈ (cubeFEM hT hB N).V1h, ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) →
      Feec.BGG.graphSq bggSegment.d0 (σ - σh) + Feec.BGG.graphSq bggSegment.dt0 (φ - φh) +
        (cubeFEM hT hB N).gnSq (u - uh) ≤ (K * L * meshSize N) ^ 2 :=
  exists_curlPotential_bound.elim fun _ h => cubeFEM_rate_C2 hT hB h.1 h.2

/-- **[QuennevilleBelair2015], Prop 5.4 for Table 5.1, unconditionally**: for every `N` and every
datum `F` the discrete system (5.6) has exactly one solution (`cubeFEM_existsUnique` with the
constant of `curlPotential`). -/
theorem cubeFEM_existsUnique' (N : ℕ) (F : Wv U1 →ₗ[ℝ] ℝ) :
    ∃! x : (cubeFEM hT hB N).V0h × (cubeFEM hT hB N).Vt0h × (cubeFEM hT hB N).Vt1h ×
        (cubeFEM hT hB N).V1h,
      (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
        ⟪(x.1 : U0), τ⟫ - ⟪(x.2.2.1 : Wv U1), bggSegment.dt0 ψ⟫
          - ⟪(x.2.2.2 : U1), bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) ∧
      (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 x.2.1, v⟫ +
        ⟪(cubeFEM hT hB N).S1h x.2.2.1, (cubeFEM hT hB N).S1h v⟫ +
          ⟪bggSegment.dt1 x.2.2.1, bggSegment.dt1 v⟫ = F v) ∧
      (∀ μ ∈ (cubeFEM hT hB N).V1h, ⟪bggSegment.d0 x.1 - (cubeFEM hT hB N).S0h x.2.1, μ⟫ = 0) :=
  exists_curlPotential_bound.elim fun _ h => cubeFEM_existsUnique hT hB h.1 h.2 N F

/-- **The `O(h)` rate of the semi-discrete scheme (6.5), unconditionally** (`cubeWave_rate` with
the constant of `curlPotential`; [QuennevilleBelair2015], §6.3, Table 6.1). -/
theorem cubeWave_rate' :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T) {f : ℝ → Wv W1}
      (_hf : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) {L : ℝ},
      0 ≤ L →
      (∀ t ∈ Icc 0 T, IsSmoothState L (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) ∧
        IsSmoothState L (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t)) →
      (∀ t ∈ Icc 0 T, ∀ μ : U1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖) →
      ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N f),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH (s.σ 0) (s.φ 0) (s.u 0)
              (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 +
          ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ K * L * (1 + t) * meshSize N :=
  exists_curlPotential_bound.elim fun _ h => cubeWave_rate hT hB h.1 h.2


end Rate

end Feec.Models.Cube.WeakSymmetry
