module

public import Feec.Models.Cube.SobolevRate
public import Feec.Models.Cube.PolyRate
public import Feec.Models.Cube.SobolevWeak
public import Feec.FiniteElement.BrambleHilbertL2

/-!
# Optimal finite element rates for Sobolev data on the cube

(Module docstring written at the end.)
-/

open scoped InnerProductSpace Topology ContDiff ENNReal
open Set MeasureTheory Filter Finset

@[expose] public noncomputable section

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.HilbertComplex Feec.FiniteElement Feec.ExteriorFibre
open Feec.Models.Cube.Sobolev
open Feec.Models.Cube.DeRhamIdent (dPart Jinvf JfJ trunc)
open Feec.Models.Cube.Geometry (Q)

variable {n : ℕ}

/-! ### The local interpolation error from `L²` derivatives -/

namespace Poly

variable (S : PolySeq)

/-- **`C⁰` quasi-optimality of the canonical interpolant** on a mesh simplex: if a polynomial form
`P ∈ P(T)ᵏ` is `e`-close to `w` on `T`, then `|w - Π_T w| ≤ (1 + B dim D) e` on `T` (the DOF
bound `DofBound` and the DOF stability `abs_dof_le`; the argument of `abs_sub_globalInterp_le`
for an arbitrary approximant). -/
theorem abs_sub_globalInterp_le_of_near {N k : ℕ} {B D : ℝ} (hB : DofBound S n k B)
    (hB0 : 0 ≤ B) (hD : CoeffBound S n k D) (T : (mesh n N).simplices) {w : FormField n}
    (hw : Continuous w) {P : FormField n} (hPS : P ∈ S.space n k) {e : ℝ} (he : 0 ≤ e)
    (hwP : ∀ x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ‖w x - P x‖ ≤ e)
    {x : Fin n → ℝ} (hx : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior)
    (t : Finset (Fin n)) :
    |w x t - ((((polyElement n S).globalInterp (mesh n N) k ⟨w, hw⟩ :
      (polyElement n S).Piecewise (mesh n N) k) T : (polyElement n S).space T k) :
        FormField n) x t| ≤
      (1 + B * Module.finrank ℝ (S.space n k) * D) * e := by
  set Iw : (polyElement n S).space T k := (((polyElement n S).globalInterp (mesh n N) k
    ⟨w, hw⟩ : (polyElement n S).Piecewise (mesh n N) k) T)
  have hIw : (Iw : FormField n) ∈ S.space n k := Iw.2
  set z : FormField n := (Iw : FormField n) - P
  have hz : z ∈ S.space n k := Submodule.sub_mem _ hIw hPS
  have hwPc : Continuous (w - P) := hw.sub (PolyKind.contDiff_of_mem_space hPS).continuous
  have hdof : ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ hN N ^ k * (D * e) := by
    intro g hgT i
    have e1 : S.dof g k i ⟨(Iw : FormField n), S.space_le_contForms n k hIw⟩ =
        S.dof g k i ⟨w, hw⟩ :=
      (polyElement n S).localDof_globalInterp (mesh n N) k ⟨w, hw⟩ T g hgT i
    have e2 : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ = S.dof g k i ⟨w - P, hwPc⟩ := by
      have : (⟨z, S.space_le_contForms n k hz⟩ : contForms n) =
          ⟨(Iw : FormField n), S.space_le_contForms n k hIw⟩ -
            ⟨P, S.space_le_contForms n k hPS⟩ := rfl
      have : (⟨w - P, hwPc⟩ : contForms n) = ⟨w, hw⟩ -
          ⟨P, S.space_le_contForms n k hPS⟩ := rfl
      rw [‹(⟨z, _⟩ : contForms n) = _›, this, map_sub, map_sub, e1]
    rw [e2]
    refine (abs_dof_le S hD T.2 hgT i _ he fun y hy t => ?_).trans (le_of_eq (by ring))
    have := norm_le_pi_norm ((w - P) y) t
    rw [Real.norm_eq_abs] at this
    exact this.trans (hwP y hy)
  have hzb := abs_le_of_abs_dof_le S hB hB0 T.2 hz hdof hx t
  have h1 : |w x t - P x t| ≤ e := by
    have := norm_le_pi_norm (w x - P x) t
    rw [Real.norm_eq_abs, Pi.sub_apply] at this
    exact this.trans (hwP x hx)
  calc |w x t - (Iw : FormField n) x t| = |(w x t - P x t) - z x t| := by
        simp only [z, Pi.sub_apply]; ring_nf
    _ ≤ |w x t - P x t| + |z x t| := abs_sub _ _
    _ ≤ e + B * Module.finrank ℝ (S.space n k) * (D * e) := add_le_add h1 hzb
    _ = (1 + B * Module.finrank ℝ (S.space n k) * D) * e := by ring

end Poly

/-! #### Sobolev embedding on the mesh simplices -/

variable (n) in
/-- The Riesz constant `n |B₁| h^{2(p+1) - n} / (2(p+1) - n)` of the Sobolev embedding at scale
`h` (`Feec.FiniteElement.rieszConst`, as a real number). -/
def rieszR (p : ℕ) (h : ℝ) : ℝ :=
  n * volume.real (Metric.ball (0 : Fin n → ℝ) 1) *
    (h ^ ((n : ℝ) + ((2 * (p + 1) : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ)) /
      ((n : ℝ) + ((2 * (p + 1) : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ)))

variable (n) in
/-- `n |B₁| / (2(p+1) - n)`. -/
def rieszC (p : ℕ) : ℝ :=
  n * volume.real (Metric.ball (0 : Fin n → ℝ) 1) /
    ((n : ℝ) + ((2 * (p + 1) : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ))

theorem denom_pos {p : ℕ} (hns : n < 2 * (p + 1)) :
    0 < (n : ℝ) + ((2 * (p + 1) : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ) := by
  have : (n : ℝ) < ((2 * (p + 1) : ℕ) : ℝ) := by exact_mod_cast hns
  push_cast at this ⊢
  linarith

theorem rieszR_nonneg {p : ℕ} (hns : n < 2 * (p + 1)) {h : ℝ} (hh : 0 ≤ h) : 0 ≤ rieszR n p h := by
  have := denom_pos hns
  unfold rieszR
  have : 0 ≤ h ^ ((n : ℝ) + ((2 * (p + 1) : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ)) :=
    Real.rpow_nonneg hh _
  positivity

theorem rieszC_nonneg {p : ℕ} (hns : n < 2 * (p + 1)) : 0 ≤ rieszC n p := by
  have := denom_pos hns
  unfold rieszC; positivity

theorem pow_mul_rieszR {p : ℕ} {h : ℝ} (hh : 0 < h) :
    h ^ n * rieszR n p h = rieszC n p * h ^ (2 * (p + 1)) := by
  unfold rieszR rieszC
  have e : h ^ n * h ^ ((n : ℝ) + ((2 * (p + 1) : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ)) =
      h ^ (2 * (p + 1)) := by
    rw [← Real.rpow_natCast h n, ← Real.rpow_add hh, ← Real.rpow_natCast h (2 * (p + 1))]
    congr 1
    push_cast; ring
  rw [div_eq_mul_inv, div_eq_mul_inv, ← e]
  ring

variable (n) in
/-- `n! / (n p!)`, the constant `dⁿ / (n p! |T|)` of the Riesz bound on a Freudenthal simplex
(`|T| = h_Nⁿ / n!`, `d = h_N`). -/
def embA (p : ℕ) : ℝ := n.factorial / (n * p.factorial)

theorem embA_nonneg (p : ℕ) : 0 ≤ embA n p := by unfold embA; positivity

/-- `|T| = h_Nⁿ / n!` for the simplices of the Freudenthal meshes. -/
theorem volume_closedInterior_mesh {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) :
    volume T.closedInterior = ENNReal.ofReal (hN N ^ n / n.factorial) := by
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  have hfin := ((cubeSimplex N m σ).isCompact_closedInterior.measure_lt_top (μ := volume)).ne
  rw [← ENNReal.ofReal_toReal hfin]
  congr 1
  have h1 := integral_closedInterior_mapEquiv_boxMap (kuhnSimplex σ)
    (hN N • latticePoint (finLattice m)) (hN_pos N) (fun _ => (1 : ℝ))
  rw [← cubeSimplex_eq, setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at h1
  rw [← Measure.real, h1, Measure.real, volume_closedInterior_kuhnSimplex]
  simp [div_eq_mul_inv]

/-- **Sobolev embedding on a Freudenthal simplex** (`2(p + 1) > n`): the degree-`k` part `P` of
the averaged Taylor polynomial of order `p + 1` (`avgTaylorPoly`, a form of `P_pΛᵏ`) satisfies
`sup_T ‖w - P‖ ≤ (n!/(n p!)) (R(h_N))^{1/2} (∫_T ‖D^{p+1} w‖²)^{1/2}`
(`Feec.FiniteElement.enorm_sub_avgTaylorPoly_le_L2`, `|T| = h_Nⁿ/n!`, `d = h_N`). -/
theorem norm_sub_degPart_avgTaylorPoly_le [NeZero n] {N k p : ℕ} (hns : n < 2 * (p + 1))
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices) {w : FormField n}
    (hw : ContDiff ℝ (p + 1) w) (hdeg : ∀ x, IsDeg k (w x)) {x : Fin n → ℝ}
    (hx : x ∈ T.closedInterior) :
    ‖w x - degPartField k (avgTaylorPoly T.closedInterior w (p + 1)) x‖ ≤
      embA n p * √(rieszR n p (hN N)) *
        √(∫ y in T.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hh := hN_pos N
  have hTc : IsCompact T.closedInterior := T.isCompact_closedInterior
  have hTm : MeasurableSet T.closedInterior := hTc.isClosed.measurableSet
  have hd : ∀ x ∈ T.closedInterior, ∀ y ∈ T.closedInterior, ‖x - y‖ ≤ hN N := by
    obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
    exact fun x hx y hy => norm_sub_le_of_mem_cubeSimplex hx hy
  have h := enorm_sub_avgTaylorPoly_le_L2 hn hTc (convex_closedInterior T)
    (volume_closedInterior_ne_zero T) isOpen_univ (subset_univ _) hns hw.contDiffOn hd hx
  -- the three factors as real numbers
  have hA : avgTaylorConst n p (hN N) T.closedInterior = ENNReal.ofReal (embA n p) := by
    rw [avgTaylorConst, volume_closedInterior_mesh hT,
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    unfold embA
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    have : (p.factorial : ℝ) ≠ 0 := by positivity
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hR : rieszConst n (2 * (p + 1)) (2 * n) (hN N) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (√(rieszR n p (hN N))) := by
    rw [show rieszConst n (2 * (p + 1)) (2 * n) (hN N) = ENNReal.ofReal (rieszR n p (hN N)) from
      rfl, ENNReal.ofReal_rpow_of_nonneg (rieszR_nonneg hns hh.le) (by norm_num),
      Real.sqrt_eq_rpow]
  have hDc : ContinuousOn (iteratedFDeriv ℝ (p + 1) w) T.closedInterior :=
    (hw.continuous_iteratedFDeriv le_rfl).continuousOn
  have hI : (∫⁻ z in T.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w z‖ₑ ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (√(∫ y in T.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2)) := by
    rw [integral_norm_sq_eq_toReal_lintegral hTm hDc, Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal (setLIntegral_enorm_sq_lt_top hTc hDc).ne]
  rw [hA, hR, hI, ← ENNReal.ofReal_mul (embA_nonneg p), ← ENNReal.ofReal_mul
    (mul_nonneg (embA_nonneg p) (Real.sqrt_nonneg _))] at h
  have e : w x - degPartField k (avgTaylorPoly T.closedInterior w (p + 1)) x =
      degPart k (w x - avgTaylorPoly T.closedInterior w (p + 1) x) := by
    have h2 := congrFun (degPartField_sub k w (avgTaylorPoly T.closedInterior w (p + 1))) x
    rw [degPartField_of_isDeg hdeg] at h2
    exact h2.symm
  rw [e]
  refine (norm_degPart_le k _).trans ?_
  rw [← ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (embA_nonneg p)
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))).1 h

/-! #### The local and global `L²` interpolation errors -/

variable (n) in
/-- The `C⁰`-stability constant `1 + B_k dim(P(T)ᵏ) D_k` of the canonical interpolant of `S`. -/
def interpCi (S : PolySeq) (k : ℕ) : ℝ :=
  1 + dofConst n S k * Module.finrank ℝ (S.space n k) * coeffConst n S k

theorem interpCi_nonneg (S : PolySeq) (k : ℕ) : 0 ≤ interpCi n S k := by
  have := dofConst_nonneg (n := n) S k; have := coeffConst_nonneg (n := n) S k
  unfold interpCi; positivity

variable (n) in
/-- The constant of the local `L²` interpolation error from `L²` derivatives. -/
def localL2Const (S : PolySeq) (k p : ℕ) : ℝ :=
  2 ^ n * (interpCi n S k * embA n p) ^ 2 * rieszC n p

theorem localL2Const_nonneg (S : PolySeq) (k : ℕ) {p : ℕ} (hns : n < 2 * (p + 1)) :
    0 ≤ localL2Const n S k p := by
  have := rieszC_nonneg hns
  unfold localL2Const; positivity

/-- **The local `L²` interpolation error from `L²` derivatives** on a Freudenthal simplex
([Arnold2018], Ch. 7; [Ciarlet2002], Thm 3.1.4, Sobolev form): for `P_pΛᵏ ⊆ P(T)ᵏ`,
`2(p + 1) > n` and a smooth degree-`k` form `w`,
`‖w - Π_T w‖²_{L²(T)} ≤ C h_N^{2(p+1)} ∫_T ‖D^{p+1} w‖²`, `C = localL2Const n S k p`
independent of `N` and `T` (Sobolev embedding on `T` and `C⁰` stability of `Π_T`). -/
theorem sum_integral_sq_sub_globalInterp_le [NeZero n] (S : PolySeq) {N k p : ℕ}
    (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1)) (T : (mesh n N).simplices)
    {w : FormField n} (hw : ContDiff ℝ ∞ w) (hdeg : ∀ x, IsDeg k (w x)) :
    ∑ t : formIdx n k, ∫ x in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (w x t.1 - ((((polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩ :
        (polyElement n S).Piecewise (mesh n N) k) T : (polyElement n S).space T k) :
          FormField n) x t.1) ^ 2 ≤
      localL2Const n S k p * hN N ^ (2 * (p + 1)) *
        ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
          ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2 := by
  set T' : Affine.Simplex ℝ (Fin n → ℝ) n := T.1
  have hT : T' ∈ (mesh n N).simplices := T.2
  have hh := hN_pos N
  have hw1 : ContDiff ℝ (p + 1) w := hw.of_le (by exact_mod_cast le_top)
  set I := ∫ y in T'.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2
  have hI : 0 ≤ I := setIntegral_nonneg T'.isCompact_closedInterior.isClosed.measurableSet
    fun _ _ => sq_nonneg _
  set e := embA n p * √(rieszR n p (hN N)) * √I
  have he : 0 ≤ e := mul_nonneg (mul_nonneg (embA_nonneg p) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
  set P := degPartField k (avgTaylorPoly T'.closedInterior w (p + 1))
  have hP : P ∈ S.space n k := hs (degPartField_mem_polySpace (avgTaylorPoly_mem_polyFunctions
    T'.isCompact_closedInterior isOpen_univ (subset_univ _)
      (hw.of_le (by exact_mod_cast le_top)).contDiffOn) k)
  have hwP : ∀ x ∈ T'.closedInterior, ‖w x - P x‖ ≤ e := fun x hx =>
    norm_sub_degPart_avgTaylorPoly_le hns hT hw1 hdeg hx
  set Iw : (polyElement n S).space T k := (((polyElement n S).globalInterp (mesh n N) k
    ⟨w, hw.continuous⟩ : (polyElement n S).Piecewise (mesh n N) k) T)
  have hIwc : Continuous (Iw : FormField n) :=
    (PolyKind.contDiff_of_mem_space Iw.2).continuous
  have hpt : ∀ x ∈ T'.closedInterior, ∀ t : Finset (Fin n),
      |w x t - (Iw : FormField n) x t| ≤ interpCi n S k * e := fun x hx t =>
    Poly.abs_sub_globalInterp_le_of_near S (dofBound_dofConst S k) (dofConst_nonneg S k)
      (coeffBound_coeffConst S k) T hw.continuous hP he hwP hx t
  obtain ⟨m, σ, hmσ⟩ := mem_mesh_simplices.1 hT
  have hone : ∀ t : formIdx n k, ∫ x in T'.closedInterior, (w x t.1 - (Iw : FormField n) x t.1) ^ 2
      ≤ hN N ^ n * (interpCi n S k * e) ^ 2 := by
    intro t
    have hc : Continuous fun x => (w x t.1 - (Iw : FormField n) x t.1) ^ 2 :=
      (((continuous_apply t.1).comp hw.continuous).sub ((continuous_apply t.1).comp hIwc)).pow 2
    have := integral_cubeSimplex_le m σ hc (fun x hx => by
      rw [hmσ] at hx
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hpt x hx t.1) 2) (fun x => sq_nonneg _)
    rwa [hmσ] at this
  have hsq : (interpCi n S k * e) ^ 2 = (interpCi n S k * embA n p) ^ 2 * rieszR n p (hN N) * I := by
    simp only [e]
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (rieszR_nonneg hns hh.le), Real.sq_sqrt hI]
    ring
  calc ∑ t : formIdx n k, ∫ x in T'.closedInterior, (w x t.1 - (Iw : FormField n) x t.1) ^ 2
      ≤ ∑ _t : formIdx n k, hN N ^ n * (interpCi n S k * e) ^ 2 := Finset.sum_le_sum fun t _ => hone t
    _ = Fintype.card (formIdx n k) * (hN N ^ n * (interpCi n S k * e) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * (hN N ^ n * (interpCi n S k * e) ^ 2) :=
        mul_le_mul_of_nonneg_right (card_formIdx_le _) (by positivity)
    _ = 2 ^ n * (interpCi n S k * embA n p) ^ 2 * (hN N ^ n * rieszR n p (hN N)) * I := by
        rw [hsq]; ring
    _ = _ := by rw [pow_mul_rieszR hh, localL2Const]; ring

/-- **Bounded overlap of the closed simplices**: `Σ_T ∫_T F ≤ 6ⁿ n! ∫_Q F` for `F ≥ 0`
continuous. -/
theorem sum_integral_closedInterior_le (N : ℕ) {F : (Fin n → ℝ) → ℝ} (hF : Continuous F)
    (hF0 : ∀ x, 0 ≤ F x) :
    ∑ T ∈ (mesh n N).simplices, ∫ x in T.closedInterior, F x ≤
      (6 ^ n * n.factorial : ℕ) * ∫ x in cubeDomain n, F x := by
  set C := closure (cubeDomain n)
  have hCc : IsCompact C := (isBounded_cubeDomain (n := n)).isCompact_closure
  have hCm : MeasurableSet C := isClosed_closure.measurableSet
  set f := C.indicator F
  have hfi : Integrable f := (integrable_indicator_iff hCm).2 (hF.continuousOn.integrableOn_compact hCc)
  have hf0 : ∀ x, 0 ≤ f x := fun x => Set.indicator_nonneg (fun x _ => hF0 x) x
  have h1 : ∀ T ∈ (mesh n N).simplices, ∫ x in T.closedInterior, F x ≤
      ∫ x in Metric.cthickening (2 * hN N) T.closedInterior, f x := by
    intro T hT
    have hTC : T.closedInterior ⊆ C := by
      have := (mesh n N).closedInterior_subset_closure hT
      rwa [mesh_domain n N] at this
    have e : ∫ x in T.closedInterior, F x = ∫ x in T.closedInterior, f x :=
      setIntegral_congr_fun T.isCompact_closedInterior.isClosed.measurableSet fun x hx =>
        (Set.indicator_of_mem (hTC hx) F).symm
    rw [e]
    exact setIntegral_mono_set hfi.integrableOn (Eventually.of_forall hf0)
      (Eventually.of_forall (Metric.self_subset_cthickening _))
  refine (Finset.sum_le_sum h1).trans ((sum_integral_cthickening_le N hfi hf0).trans
    (le_of_eq ?_))
  congr 1
  rw [integral_indicator hCm]
  have hnull : volume (frontier (cubeDomain n)) = 0 :=
    Convex.addHaar_frontier volume (convex_cubeDomain n)
  rw [Measure.restrict_congr_set (closure_ae_eq_of_null_frontier hnull)]

variable (n) in
/-- The constant of the global `L²` interpolation error from `L²` derivatives. -/
def globalL2Const (S : PolySeq) (k p : ℕ) : ℝ :=
  √(localL2Const n S k p * (6 ^ n * n.factorial : ℕ))

theorem globalL2Const_nonneg (S : PolySeq) (k p : ℕ) : 0 ≤ globalL2Const n S k p :=
  Real.sqrt_nonneg _

/-- **The global `L²` interpolation error from `L²` derivatives** on the Freudenthal meshes:
`‖w - Π_h w‖_{L²(Q)} ≤ C h_N^{p+1} ‖D^{p+1} w‖_{L²(Q)}` for `P_pΛᵏ ⊆ P(T)ᵏ`, `2(p + 1) > n`,
`C = globalL2Const n S k p`. -/
theorem norm_formL2_sub_glue_globalInterp_le [NeZero n] (S : PolySeq) {N k p : ℕ}
    (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1)) {w : FormField n}
    (hw : ContDiff ℝ ∞ w) (hdeg : ∀ x, IsDeg k (w x)) :
    ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
        ⟨w, hw.continuous⟩ - (polyElement n S).glue (mesh n N) k
          ((polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩ :
            (polyElement n S).Piecewise (mesh n N) k)‖ ≤
      globalL2Const n S k p * hN N ^ (p + 1) *
        √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2) := by
  set u := ((polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩ :
    (polyElement n S).Piecewise (mesh n N) k)
  have hK := localL2Const_nonneg (n := n) S k hns
  have hh := (hN_pos N).le
  have hDc : Continuous fun y => ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2 :=
    ((hw.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm).pow 2
  have hsq := norm_sq_formL2_sub_glue_le (polyElement n S) (mesh n N)
    (isOpen_mesh_domain n N).measurableSet k ⟨w, hw.continuous⟩ u
  have h2 : ∑ T ∈ (mesh n N).simplices, ∑ s : formIdx n k, ∫ x in T.closedInterior,
      (w x s.1 - (polyElement n S).extendPW (mesh n N) u T x s.1) ^ 2 ≤
      localL2Const n S k p * hN N ^ (2 * (p + 1)) *
        ∑ T ∈ (mesh n N).simplices, ∫ y in T.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun T hT => ?_
    have e : ∀ x, (polyElement n S).extendPW (mesh n N) u T x =
        ((u (⟨T, hT⟩ : (mesh n N).simplices) : (polyElement n S).space
          (⟨T, hT⟩ : (mesh n N).simplices) k) : FormField n) x := fun x => by
      rw [(polyElement n S).extendPW_of_mem (mesh n N) u hT]
    simp_rw [e]
    exact sum_integral_sq_sub_globalInterp_le S hs hns (⟨T, hT⟩ : (mesh n N).simplices) hw hdeg
  have h3 := sum_integral_closedInterior_le N hDc (fun _ => sq_nonneg _)
  have hJ : 0 ≤ ∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2 :=
    setIntegral_nonneg (isOpen_cubeDomain n).measurableSet fun _ _ => sq_nonneg _
  have h4 : ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
        ⟨w, hw.continuous⟩ - (polyElement n S).glue (mesh n N) k u‖ ^ 2 ≤
      (globalL2Const n S k p * hN N ^ (p + 1) *
        √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2)) ^ 2 := by
    refine hsq.trans (h2.trans ?_)
    rw [mul_pow, mul_pow, globalL2Const, Real.sq_sqrt (by positivity), Real.sq_sqrt hJ, ← pow_mul,
      mul_comm (p + 1) 2]
    calc localL2Const n S k p * hN N ^ (2 * (p + 1)) * ∑ T ∈ (mesh n N).simplices,
          ∫ y in T.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2
        ≤ localL2Const n S k p * hN N ^ (2 * (p + 1)) * (((6 ^ n * n.factorial : ℕ) : ℝ) *
          ∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by have := globalL2Const_nonneg (n := n) S k p; positivity)).1 h4

/-! #### In the finite element spaces of the cube -/

/-- **`L²` interpolation from `L²` derivatives in `Vₕᵏ ⊆ HΛᵏ(Q)`**: for a smooth degree-`k` form
`w`, some `v ∈ (poly n S N).V k` has
`‖w - v‖ ≤ C h_N^{p+1} ‖D^{p+1} w‖_{L²(Q)}` (`P_pΛᵏ ⊆ P(T)ᵏ`, `2(p + 1) > n`). -/
theorem exists_mem_poly_le_L2 [NeZero n] (S : PolySeq) (N k p : ℕ)
    (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1)) {w : FormField n}
    (hw : ContDiff ℝ ∞ w) (hdeg : ∀ x, IsDeg k (w x)) :
    ∃ v ∈ (poly n S N).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ - v‖ ≤ globalL2Const n S k p * meshSize N ^ (p + 1) *
        √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2) := by
  refine (deRham ℝ n).maximalSubcomplexOfEq_induction (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (S.subcomplex (mesh n N) (isOpen_mesh_domain n N))
    (fun Θ hΘ S' => ∀ hb : Bornology.IsBounded Θ,
      ∃ v ∈ S'.V k,
        ‖formL2 hΘ.measurableSet hb k ⟨w, hw.continuous⟩ - asForm n v‖ ≤
          globalL2Const n S k p * meshSize N ^ (p + 1) *
            √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2)) ?_
    (isBounded_cubeDomain n)
  intro hb
  set M := mesh n N
  set u := (polyElement n S).globalInterp M k ⟨w, hw.continuous⟩
  refine ⟨(polyElement n S).glue M k (u : (polyElement n S).Piecewise M k), ⟨u, rfl⟩, ?_⟩
  have h := norm_formL2_sub_glue_globalInterp_le S (N := N) hs hns hw hdeg
  rwa [hN_eq_meshSize] at h

/-- **`L²` interpolation from `L²` derivatives in `V_{h,Γ_J}ᵏ ⊆ HΛ_Jᵏ(Q)`**: as
`exists_mem_poly_le_L2`, for a form whose tangential components vanish on the faces normal to
`J`, with the interpolant in `(polyPartial n S N J).V k` (vanishing boundary DOFs on those
faces). -/
theorem exists_mem_polyPartial_le_L2 [NeZero n] (S : PolySeq) (J : Finset (Fin n)) (N k p : ℕ)
    (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1)) {w : FormField n}
    (hw : ContDiff ℝ ∞ w) (hdeg : ∀ x, IsDeg k (w x))
    (hJ : ∀ x : Fin n → ℝ, ∀ j ∈ J, (x j = 0 ∨ x j = 1 / 2) → ∀ t : Finset (Fin n), j ∉ t →
      w x t = 0) :
    ∃ v ∈ (polyPartial n S N J).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ - v‖ ≤ globalL2Const n S k p * meshSize N ^ (p + 1) *
        √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2) := by
  have hV : ∃ v ∈ (polyElement n S).VPartial (mesh n N) (partialFaces n J) k,
      ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
          ⟨w, hw.continuous⟩ - v‖ ≤ globalL2Const n S k p * meshSize N ^ (p + 1) *
        √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2) := by
    set u := (polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩
    refine ⟨(polyElement n S).glue (mesh n N) k (u : (polyElement n S).Piecewise (mesh n N) k),
      ⟨⟨_, globalInterp_mem_globalSpacePartial_of_face (polyElement n S) (mesh n N) J k _ hJ⟩,
        rfl⟩, ?_⟩
    have h := norm_formL2_sub_glue_globalInterp_le S (N := N) hs hns hw hdeg
    rwa [hN_eq_meshSize] at h
  have key : ∀ (Ω' : Set (Fin n → ℝ)) (h : (mesh n N).domain = Ω') (hΩ' : IsOpen Ω')
      (hΩQ' : Ω' ⊆ Geometry.Q (Fin n)) (hb : Bornology.IsBounded Ω'),
      ∃ v ∈ (partialSubcomplexOfEq h (isOpen_of_eq_Q (mesh_domain_eq_Q N))
          (mesh_domain_eq_Q N).le hΩ' hΩQ' J
          (subcomplexPart (polyElement n S) (mesh n N) (mesh_domain_eq_Q N) J)).V k,
        ‖formL2 hΩ'.measurableSet hb k ⟨w, hw.continuous⟩ - v‖ ≤
          globalL2Const n S k p * meshSize N ^ (p + 1) *
            √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2) := by
    rintro Ω' rfl hΩ' hΩQ' hb
    exact hV
  exact key _ (mesh_domain n N) (isOpen_cubeDomain n) (cubeDomain_subset_Q n)
    (isBounded_cubeDomain n)

/-! ### The truncations as smooth forms on the cube -/

theorem castL2F_apply_ae {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') {ι : Type} [Fintype ι]
    (u : L2F ℝ Ω ι) (t : ι) :
    ((castL2F h ι u t : L2 ℝ Ω') : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω']
      ((u t : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) := by
  subst h; rfl

theorem integral_cubeDomain_eq (f : (Fin n → ℝ) → ℝ) :
    ∫ y in cubeDomain n, f y = ∫ y in Q (Fin n), f y := by
  rw [cubeDomain_eq_Q]

/-- **The truncation as a smooth form**: `(x_M)|_Q` is the form `truncField k x M` of the finite
element method, transported to `Q` (`toQ`). -/
theorem toQ_formL2_truncField (k : ℕ) (x : Seq n k) (M : ℕ) :
    toQ k (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
      ⟨truncField k x M, (contDiff_truncField x M).continuous⟩) = Jinvf k (trunc M k x) := by
  rw [Jinvf_trunc_eq_toL2F]
  refine PiLp.ext fun t => Lp.ext ?_
  have h2 := ae_restrict_of_ae_restrict_of_subset (cubeDomain_eq_Q n).symm.le
    (coeFn_formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
      ⟨truncField k x M, (contDiff_truncField x M).continuous⟩ t)
  filter_upwards [castL2F_apply_ae (cubeDomain_eq_Q n) _ t, h2,
    (DeRhamIdent.memLp_trigLift k (trunc M k x) (DeRhamIdent.bandS M) t).coeFn_toLp] with y h1 h2 h3
  rw [h1, h2]
  rw [truncField_val]
  exact h3.symm

theorem isDeg_truncField (k : ℕ) (x : Seq n k) (M : ℕ) (y : Fin n → ℝ) :
    IsDeg k (truncField k x M y) := fun _ hs => truncField_of_ne x M y hs

/-- **The parity truncation has vanishing tangential components on the faces normal to `J`**. -/
theorem truncField_face (J : Finset (Fin n)) (k : ℕ)
    (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) (M : ℕ) :
    ∀ y : Fin n → ℝ, ∀ j ∈ J, (y j = 0 ∨ y j = 1 / 2) → ∀ t : Finset (Fin n), j ∉ t →
      truncField k (JfJ J k u) M y t = 0 := by
  intro y j hj hy t ht
  by_cases hk : #t = k
  · have hk' : (#t : ℤ) = k := by exact_mod_cast hk
    rw [show t = (⟨t, hk'⟩ : formIdx n (k : ℤ)).1 from rfl, truncField_val]
    exact DeRhamIdent.trigLift_eq_zero_of_faceJ
      (DeRhamIdent.realParJ_trunc (DeRhamIdent.JfJ_realParJ J k u) M)
      (fun j m hm => DeRhamIdent.flipAt_mem_bandS j hm) hj ht hy
  · exact truncField_of_ne _ M y hk

/-! ### Best approximation of `Hˢ` data at the optimal rate -/

/-- `h_N^r (1 + n (2π(N+1))²)^{(r-q)/2} ≤ ((1 + n) π²)^r h_N^q` for `0 ≤ q ≤ r`. -/
theorem meshSize_pow_mul_rpow_le {q : ℝ} {r : ℕ} (hq0 : 0 ≤ q) (hqr : q ≤ r) (N : ℕ) :
    meshSize N ^ r * (1 + n * (2 * Real.pi * ((N + 1 : ℕ) : ℝ)) ^ 2) ^ (((r : ℝ) - q) / 2) ≤
      ((1 + n) * Real.pi ^ 2) ^ r * meshSize N ^ q := by
  set h := meshSize N
  have hh : 0 < h := meshSize_pos N
  set A : ℝ := (1 + n) * Real.pi ^ 2
  have hA1 : 1 ≤ A := by
    have h4 : 4 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    calc (1 : ℝ) ≤ 1 * Real.pi ^ 2 := by linarith
      _ ≤ A := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have he0 : 0 ≤ ((r : ℝ) - q) / 2 := by linarith
  rw [two_pi_mul_succ_eq]
  have hb : 1 + n * (Real.pi / h) ^ 2 ≤ A / h ^ 2 := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
    have : h ^ 2 ≤ Real.pi ^ 2 := by
      have := Real.two_le_pi
      have := meshSize_le_half N
      exact pow_le_pow_left₀ hh.le (by linarith) 2
    have : 0 ≤ (n : ℝ) := n.cast_nonneg
    rw [add_mul, one_mul, div_mul_cancel₀ _ (by positivity)]
    nlinarith
  have h1 := Real.rpow_le_rpow (by positivity) hb he0
  have h2 : (A / h ^ 2) ^ (((r : ℝ) - q) / 2) = A ^ (((r : ℝ) - q) / 2) / h ^ ((r : ℝ) - q) := by
    rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast h 2,
      ← Real.rpow_mul hh.le]
    norm_num
    ring_nf
  have h3 : A ^ (((r : ℝ) - q) / 2) ≤ A ^ r := by
    rw [← Real.rpow_natCast A r]
    exact Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
  have h4 : h ^ r / h ^ ((r : ℝ) - q) = h ^ q := by
    rw [← Real.rpow_natCast h r, ← Real.rpow_sub hh]
    ring_nf
  calc h ^ r * (1 + n * (Real.pi / h) ^ 2) ^ (((r : ℝ) - q) / 2) ≤
        h ^ r * (A ^ (((r : ℝ) - q) / 2) / h ^ ((r : ℝ) - q)) :=
        mul_le_mul_of_nonneg_left (h1.trans (le_of_eq h2)) (by positivity)
    _ = A ^ (((r : ℝ) - q) / 2) * (h ^ r / h ^ ((r : ℝ) - q)) := by ring
    _ ≤ A ^ r * h ^ q := by
        rw [h4]; exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hh.le _)

variable (n) in
/-- The constant of the optimal-rate best-approximation estimate in degree `k` for an order-`p`
sequence (`r_eff = p + 1`): `1 + C_glob (2ⁿ n^{p+1})^{1/2} ((1 + n) π²)^{p+1}`. -/
def sobConstHigh (S : PolySeq) (k p : ℕ) : ℝ :=
  1 + globalL2Const n S k p * √(2 ^ n * (n : ℝ) ^ (p + 1)) * ((1 + n) * Real.pi ^ 2) ^ (p + 1)

theorem sobConstHigh_nonneg (S : PolySeq) (k p : ℕ) : 0 ≤ sobConstHigh n S k p := by
  have := globalL2Const_nonneg (n := n) S k p
  unfold sobConstHigh; positivity

/-- The interpolation step of the optimal rate: for an extension `x ∈ Hˢ(𝕋ⁿ)`, `0 ≤ q ≤ p + 1`
and `q ≤ s`, the truncation `u_M` (`M = N + 1`) has a finite element approximation with
`‖u_M - v‖ ≤ (sobConstHigh - 1) h_N^q ‖x‖_{Hˢ(𝕋ⁿ)}`. -/
theorem exists_mem_near_truncField_le (S : PolySeq) {k p : ℕ} {q s : ℝ} (hq0 : 0 ≤ q) (hqp : q ≤ p + 1) (hqs : q ≤ s)
    {x : Seq n k} (hx : MemSob s x) (N : ℕ) :
    √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) (truncField k x (N + 1)) y‖ ^ 2) *
        meshSize N ^ (p + 1) * globalL2Const n S k p ≤
      (sobConstHigh n S k p - 1) * meshSize N ^ q * √(sobSum s x) := by
  have hq : MemSob q x := hx.mono hqs
  have hB := sum_norm_iteratedFDeriv_truncQ_sq_le (p := p + 1) (by exact_mod_cast hqp) hq (N + 1)
  rw [← integral_cubeDomain_eq] at hB
  have hK := globalL2Const_nonneg (n := n) S k p
  have hh := (meshSize_pos N).le
  set A : ℝ := (1 + n * (2 * Real.pi * ((N + 1 : ℕ) : ℝ)) ^ 2)
  have hA : 0 ≤ A := by positivity
  have hsq : √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) (truncField k x (N + 1)) y‖ ^ 2) ≤
      √(2 ^ n * (n : ℝ) ^ (p + 1)) * A ^ ((((p + 1 : ℕ) : ℝ) - q) / 2) * √(sobSum s x) := by
    refine (Real.sqrt_le_sqrt hB).trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (sobSum_mono hqs hx)) (by positivity)))
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (Real.rpow_nonneg hA _),
      Real.sqrt_eq_rpow (A ^ _), ← Real.rpow_mul hA]
    push_cast
    ring_nf
  have hm := meshSize_pow_mul_rpow_le (n := n) hq0 (r := p + 1) (by exact_mod_cast hqp) N
  calc √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) (truncField k x (N + 1)) y‖ ^ 2) *
        meshSize N ^ (p + 1) * globalL2Const n S k p
      ≤ √(2 ^ n * (n : ℝ) ^ (p + 1)) * A ^ ((((p + 1 : ℕ) : ℝ) - q) / 2) * √(sobSum s x) *
        meshSize N ^ (p + 1) * globalL2Const n S k p := by gcongr
    _ = globalL2Const n S k p * √(2 ^ n * (n : ℝ) ^ (p + 1)) * √(sobSum s x) *
        (meshSize N ^ (p + 1) * A ^ ((((p + 1 : ℕ) : ℝ) - q) / 2)) := by ring
    _ ≤ globalL2Const n S k p * √(2 ^ n * (n : ℝ) ^ (p + 1)) * √(sobSum s x) *
        (((1 + n) * Real.pi ^ 2) ^ (p + 1) * meshSize N ^ q) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by unfold sobConstHigh; ring

/-- **Best approximation of `Hˢ(Q)` forms at the optimal rate**
(`infDist_poly_le_sobolevQ_high`; [AFW2010], §5; [Arnold2018], Ch. 7): for a sequence `S`
reproducing `P_pΛᵏ` in degree `k` (`r_eff = p + 1`, e.g. `FEM.PolyOrder n S p`) with
`2 r_eff > n` (every `r_eff ≥ 2` for `n ≤ 3`), and every real `s ≥ 0`,
`dist(y, Vₕᵏ) ≤ C h_N^{min(s, r_eff)} ‖y‖_{Hˢ(Q)}`, `C = sobConstHigh n S k p` independent of
`N` and `s`. The proof truncates an extension at `M = N + 1 ≈ 1/(2h_N)`
(`norm_sub_Jinvf_trunc_le`), bounds `‖D^{r_eff} u_M‖_{L²(Q)}` by the Bernstein inequality
(`sum_norm_iteratedFDeriv_truncQ_sq_le`) and interpolates `u_M` with the `L²` estimate of the
canonical interpolant (`exists_mem_poly_le_L2`). -/
theorem infDist_poly_le_sobolevQ_high [NeZero n] (S : PolySeq) (k p : ℕ)
    (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1)) {s : ℝ} (hs0 : 0 ≤ s)
    (N : ℕ) (y : L2F ℝ (cubeDomain n) (formIdx n k)) (hy : toQ k y ∈ sobolevQ n k s) :
    Metric.infDist y ((poly n S N).V k) ≤
      sobConstHigh n S k p * meshSize N ^ min s (p + 1) * qNorm k s (toQ k y) := by
  have hh := meshSize_pos N
  set q := min s (p + 1)
  have hq0 : 0 ≤ q := le_min hs0 (by positivity)
  refine le_mul_qNorm hy (mul_nonneg (sobConstHigh_nonneg S k p) (Real.rpow_nonneg hh.le q))
    fun x hx hxu => ?_
  set M := N + 1
  set w := truncField k x M
  have hw := contDiff_truncField x M
  set z' := formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw.continuous⟩
  have hz : toQ k z' = Jinvf k (trunc M k x) := toQ_formL2_truncField k x M
  obtain ⟨v, hv, hzv⟩ := exists_mem_poly_le_L2 S N k p hs hns hw (isDeg_truncField k x M)
  set σ := √(sobSum s x)
  have h1 : ‖y - z'‖ ≤ meshSize N ^ q * σ := by
    have e : ‖y - z'‖ = ‖Jinvf k x - Jinvf k (trunc M k x)‖ := by
      rw [← (toQ k).norm_map, map_sub, hz, hxu]
    rw [e]
    refine (norm_sub_Jinvf_trunc_le hq0 (hx.mono (min_le_left _ _)) M).trans ?_
    exact mul_le_mul (rpow_neg_le_meshSize_rpow hq0 N)
      (Real.sqrt_le_sqrt (sobSum_mono (min_le_left _ _) hx)) (Real.sqrt_nonneg _)
      (Real.rpow_nonneg hh.le _)
  have h2 : ‖z' - v‖ ≤ (sobConstHigh n S k p - 1) * meshSize N ^ q * σ := by
    refine hzv.trans ?_
    have := exists_mem_near_truncField_le S hq0 (min_le_right _ _) (min_le_left _ _) hx N
    linarith
  calc Metric.infDist y ((poly n S N).V k) ≤ dist y v := Metric.infDist_le_dist_of_mem hv
    _ = ‖y - v‖ := dist_eq_norm y v
    _ ≤ ‖y - z'‖ + ‖z' - v‖ := norm_sub_le_norm_sub_add_norm_sub y z' v
    _ ≤ meshSize N ^ q * σ + (sobConstHigh n S k p - 1) * meshSize N ^ q * σ := add_le_add h1 h2
    _ = sobConstHigh n S k p * meshSize N ^ q * σ := by ring

/-- **Best approximation of the parity classes at the optimal rate**
(`infDist_polyPartial_le_sobolevPar_high`): for `y ∈ Hˢ_J(Q; Λᵏ)`, every class `J`,
`dist(y, V_{h,Γ_J}ᵏ) ≤ C' h_N^{min(s, r_eff)} ‖y‖_{s,J}`, `C' = 2^{n/2} sobConstHigh n S k p`.
The parity truncation `truncPar` stays in the class, its tangential components vanish on the faces
normal to `J` (`truncField_face`), and the canonical interpolant has vanishing boundary DOFs
there (`exists_mem_polyPartial_le_L2`). -/
theorem infDist_polyPartial_le_sobolevPar_high [NeZero n] (S : PolySeq) (J : Finset (Fin n))
    (k p : ℕ) (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1)) {s : ℝ}
    (hs0 : 0 ≤ s) (N : ℕ) (y : L2F ℝ (cubeDomain n) (formIdx n k))
    (hy : toQ k y ∈ sobolevPar J k s) :
    Metric.infDist y ((polyPartial n S N J).V k) ≤
      √(2 ^ n) * sobConstHigh n S k p * meshSize N ^ min s (p + 1) *
        parNorm J k s (toQ k y) := by
  have hh := meshSize_pos N
  set q := min s (p + 1)
  have hq0 : 0 ≤ q := le_min hs0 (by positivity)
  set u := toQ k y
  set x := JfJ J k u
  have hx : MemSob s x := (mem_sobolevPar J k).1 hy
  have hxu : Jinvf k x = u := DeRhamIdent.Jinvf_JfJ J k u
  set M := N + 1
  set w := truncField k x M
  have hw := contDiff_truncField x M
  set z' := formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw.continuous⟩
  have hz : toQ k z' = Jinvf k (trunc M k x) := toQ_formL2_truncField k x M
  obtain ⟨v, hv, hzv⟩ := exists_mem_polyPartial_le_L2 S J N k p hs hns hw
    (isDeg_truncField k x M) (truncField_face J k u M)
  set σ := √(sobSum s x)
  have hσ : σ = √(2 ^ n) * parNorm J k s u := by
    show √(sobSum s (JfJ J k u)) = _
    rw [show sobSum s (JfJ J k u) = 2 ^ n * parNorm J k s u ^ 2 by rw [parNorm_sq]; field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (parNorm_nonneg J k s u)]
  have h1 : ‖y - z'‖ ≤ meshSize N ^ q * σ := by
    have e : ‖y - z'‖ = ‖Jinvf k x - Jinvf k (trunc M k x)‖ := by
      rw [← (toQ k).norm_map, map_sub, hz, hxu]
    rw [e]
    refine (norm_sub_Jinvf_trunc_le hq0 (hx.mono (min_le_left _ _)) M).trans ?_
    exact mul_le_mul (rpow_neg_le_meshSize_rpow hq0 N)
      (Real.sqrt_le_sqrt (sobSum_mono (min_le_left _ _) hx)) (Real.sqrt_nonneg _)
      (Real.rpow_nonneg hh.le _)
  have h2 : ‖z' - v‖ ≤ (sobConstHigh n S k p - 1) * meshSize N ^ q * σ := by
    refine hzv.trans ?_
    have := exists_mem_near_truncField_le S hq0 (min_le_right _ _) (min_le_left _ _) hx N
    linarith
  calc Metric.infDist y ((polyPartial n S N J).V k) ≤ dist y v := Metric.infDist_le_dist_of_mem hv
    _ = ‖y - v‖ := dist_eq_norm y v
    _ ≤ ‖y - z'‖ + ‖z' - v‖ := norm_sub_le_norm_sub_add_norm_sub y z' v
    _ ≤ meshSize N ^ q * σ + (sobConstHigh n S k p - 1) * meshSize N ^ q * σ := add_le_add h1 h2
    _ = _ := by rw [hσ]; ring

end Feec.Models.Cube.FEM
