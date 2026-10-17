module

public import Feec.Legacy.MirrorCube.Cube
public import Feec.Legacy.BoundedDomain.Sym

/-!
# Thesis Prop 4.19 on the box `Q = (0, ½)³` with tensorial mirror boundary conditions

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

**Thesis claim** ([QuennevilleBelair2015, §4.11, Prop 4.19, p. 70]). For the complex (4.16)
`H̊²(R) --grad grad--> H̊(curl, S) --curl--> L²(T)` on a bounded domain, under projection and
density conjectures, data `(0, E₀, B₀)` with `E₀`, `B₀` TSD give a solution of (4.18) with
`σ ≡ 0` and `E`, `B` TSD for all time.

**Defect.** On every bounded domain the conjectures are false and the conclusion fails
(`Feec.Legacy.BoundedSym.symComplexB_tsd_not_propagates`; for the boundary conditions as
printed, `Feec.Counterexamples.BallSymTSD`). The mirror repair of `Feec.Legacy.Box.Mirror`
(`Feec.Models.Cube.MirrorSym.existsUnique_mem`) lives in the parity model on `ℓ²(ℤ³)`.

**Repair (this file).** A Hilbert complex of genuine fields on `Q`,
`mirrorSymCxQ : L²(Q) → L²(Q; S) → L²(Q; T)`, the compression of the periodic complex
`Feec.Legacy.TorusSym.symComplex` by the mirror extensions (`u` even in every variable, i.e.
`∂_n u = 0`; `S` with the tensor parities of `Feec.Legacy.MirrorCube.Jm 1`, i.e. `S_{nτ} = 0`; `T` with
the pseudo-tensor parities, `T_{ττ} = 0` for `D(d1*)`):
* `d0 u` is the weak Hessian of `u` on `Q` (`mirrorSymCxQ_d0_weakHess`);
* `d1 E` is the weak curl of `E` on `Q`, the mirror curl of Prop 4.17 restricted to symmetric
  fields (`mirrorSymCxQ_d1_eq`);
* the constraint spaces `TSDSm`, `TSDTm` consist of TSD fields on `Q`
  (`TSDSm_le_TSDS`, `TSDTm_le_TSDT`), with the wall conditions `S_{τn} = 0`, `T_{nn} = 0`.
For it, Prop 4.19 holds with existence and uniqueness (`Feec.Models.Cube.MirrorSym.existsUnique_memQ`), the
projection hypothesis holds (`Feec.Models.Cube.MirrorSym.reducingSubcomplexQ`), `K* = K` for every group
(`Feec.Models.Cube.MirrorSym.invariantCore_eqQ`), and `(0, 2 cos(2π x₃) diag(1, -1, 0), 0)` is a non-stationary TSD
datum (`Feec.Models.Cube.MirrorSym.exists_nonstationaryQ`).

The boundary conditions are encoded by the method of images (see `Feec.Legacy.MirrorCube.Cube`); the
identification of `D(d0)` with an `H²` space with `∂_n u = 0` and of `D(d0*)` with a weak
`div div` space is not formalized here.

## References

* [QuennevilleBelair2015], §4.11 (Prop 4.19, (4.16)–(4.18))
* [ArnoldHu2021] (the complex (4.16)), [AFW2010] (Hilbert complexes)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace InnerProductSpace ComplexConjugate
open MeasureTheory Set Filter Topology LinearPMap

namespace Feec.Legacy.MirrorCube

open Feec.Legacy.Torus Feec.Legacy.TorusWeak UnitAddTorus Feec.Legacy.Box Feec.Legacy.BoxIdent Feec.Legacy.Constraints
open Feec.Legacy.HilbertComplex2
open Feec.Legacy.BoundedDomain (R3 Ix IsTest curlM)

/-- The partial derivative of `Feec.Legacy.BoundedDomain`. -/
local notation "pd" => Feec.Legacy.BoundedDomain.pd

attribute [local instance] Feec.Legacy.Torus.instMeasureSpaceUnitAddCircle_feec

/-! ## Restricting compression data to subspaces -/

section Restrict

variable {c : ℝ} {W' W V : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℝ W']
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Restriction of compression data**: from `A : Compr c W' W`, a subspace `U' ≤ W'` and an
isometric embedding `ι : V → W` onto a subspace `Uw` with left inverse `π`, such that `J`, `P`, `R`
respect the subspaces, the data `π J`, `R ι`, `π P ι` for `U' → V`. -/
def Compr.restrict (A : Compr c W' W) (U' : Submodule ℝ W') (Uw : Submodule ℝ W)
    (ι : V →ₗᵢ[ℝ] W) (π : W →L[ℝ] V) (hι : ∀ v, ι v ∈ Uw) (hπ : ∀ v, π (ι v) = v)
    (hιπ : ∀ w ∈ Uw, ι (π w) = w) (hJ : ∀ u ∈ U', A.J u ∈ Uw) (hP : ∀ w ∈ Uw, A.P w ∈ Uw)
    (hR : ∀ w ∈ Uw, A.R w ∈ U') : Compr c U' V where
  J := π ∘L A.J ∘L U'.subtypeL
  R := (A.R ∘L ι.toContinuousLinearMap).codRestrict U' fun v => hR _ (hι v)
  P := π ∘L A.P ∘L ι.toContinuousLinearMap
  inner_J x y := by
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    rw [← ι.inner_map_map, hιπ _ (hJ _ x.2), hιπ _ (hJ _ y.2), A.inner_J, Submodule.coe_inner]
  RJ x := by
    apply Subtype.ext
    change A.R (ι (π (A.J x))) = x
    rw [hιπ _ (hJ _ x.2), A.RJ]
  JRP v := by
    change π (A.J (A.R (ι (π (A.P (ι v)))))) = π (A.P (ι v))
    rw [hιπ _ (hP _ (hι v)), A.JRP]
  PJ x := by
    change π (A.P (ι (π (A.J x)))) = π (A.J x)
    rw [hιπ _ (hJ _ x.2), A.PJ]
  P_sa v w := by
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    rw [← ι.inner_map_map, hιπ _ (hP _ (hι v)), A.P_sa, ← hιπ _ (hP _ (hι w)), ι.inner_map_map,
      hπ]

end Restrict

/-! ## Fibrewise projection onto a matrix subspace -/

section ProjU

/-- The fibrewise orthogonal projection `ℓ²(ℤ³; ℂ³ˣ³) → ℓ²(ℤ³; U)`. -/
def projL2 (U : Submodule ℝ Mat3) : L2M →L[ℝ] L2 Z3 U :=
  LinearMap.mkContinuous
    { toFun := fun A => ⟨fun k => U.orthogonalProjectionOnto (A k),
        (lp.memℓp A).mono' fun k => U.norm_orthogonalProjectionOnto_apply_le _⟩
      map_add' := fun A B => lp.ext (funext fun k => by
        change U.orthogonalProjectionOnto ((A + B : L2M) k) = _
        rw [lp.coeFn_add, Pi.add_apply, _root_.map_add]; rfl)
      map_smul' := fun r A => lp.ext (funext fun k => by
        change U.orthogonalProjectionOnto ((r • A : L2M) k) = _
        rw [lp.coeFn_smul, Pi.smul_apply, _root_.map_smul]; rfl) }
    1 fun A => by
      rw [one_mul]
      refine lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg _) fun s => ?_
      calc ∑ k ∈ s, ‖(U.orthogonalProjectionOnto (A k) : U)‖ ^ (2 : ENNReal).toReal
          ≤ ∑ k ∈ s, ‖A k‖ ^ (2 : ENNReal).toReal := Finset.sum_le_sum fun k _ => by
            gcongr; exact U.norm_orthogonalProjectionOnto_apply_le _
        _ ≤ ‖A‖ ^ (2 : ENNReal).toReal := lp.sum_rpow_le_norm_rpow (by norm_num) A s

theorem projL2_apply (U : Submodule ℝ Mat3) (A : L2M) (k : Z3) :
    projL2 U A k = U.orthogonalProjectionOnto (A k) := rfl

theorem projL2_embL2 (U : Submodule ℝ Mat3) (v : L2 Z3 U) : projL2 U (TorusSym.embL2 U v) = v :=
  lp.ext (funext fun k => by
    rw [projL2_apply, TorusSym.embL2_apply]
    exact U.orthogonalProjectionOnto_mem_subspace_eq_self (v k))

theorem embL2_projL2 (U : Submodule ℝ Mat3) {A : L2M} (hA : A ∈ fibreSub fun _ : Z3 => U) :
    TorusSym.embL2 U (projL2 U A) = A :=
  lp.ext (funext fun k => by
    rw [TorusSym.embL2_apply, projL2_apply]
    exact congrArg Subtype.val (U.orthogonalProjectionOnto_mem_subspace_eq_self ⟨A k, hA k⟩))

theorem embL2_mem_fibreSub (U : Submodule ℝ Mat3) (v : L2 Z3 U) :
    TorusSym.embL2 U v ∈ fibreSub fun _ : Z3 => U := fun k => (v k).2

end ProjU

/-! ## The scalar slot: even functions -/

section Scalar

open TorusSym in
/-- The reflection-conjugation `u ↦ conj u(-·)` on `L2R`, as a continuous map. -/
def reflRc : TorusSym.L2R →L[ℝ] TorusSym.L2R :=
  LinearMap.mkContinuous TorusSym.reflR 1 fun u => by
    rw [one_mul]
    refine le_of_eq ?_
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_sq_L2, norm_sq_L2]
    simp only [reflL2_apply, norm_conjC]
    exact (Equiv.neg Z3).tsum_eq fun k => ‖(u : Z3 → ℂ) k‖ ^ 2

theorem reflRc_apply (u : TorusSym.L2R) (k : Z3) : reflRc u k = conj (u (-k)) := rfl

theorem inner_reflRc (u v : TorusSym.L2R) : ⟪reflRc u, v⟫_ℝ = ⟪u, reflRc v⟫_ℝ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have e : ∀ k, ⟪reflRc u k, v k⟫_ℝ = ⟪u (-k), reflRc v (-k)⟫_ℝ := fun k => by
    simp only [reflRc_apply, neg_neg, Complex.inner, Complex.conj_conj]
    rw [← map_mul, Complex.conj_re, mul_comm]
  simp_rw [e]
  exact (Equiv.neg Z3).tsum_eq fun k => ⟪u k, reflRc v k⟫_ℝ

theorem reflRc_reflRc (u : TorusSym.L2R) : reflRc (reflRc u) = u :=
  lp.ext (funext fun k => by simp [reflRc_apply])

theorem reflRc_R (i : Fin 3) (u : TorusSym.L2R) :
    reflRc (mirrorR.R i u) = mirrorR.R i (reflRc u) :=
  lp.ext (funext fun k => by
    change conj (u (Box.refl i (-k))) = conj (u (-Box.refl i k))
    rw [refl_neg'])

/-- `Re u = (u + conj u(-·))/2` on `L2R`. -/
def reR : TorusSym.L2R →L[ℝ] TorusSym.L2R := (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ _ + reflRc)

theorem reR_apply (u : TorusSym.L2R) : reR u = (1 / 2 : ℝ) • (u + reflRc u) := rfl

theorem reflRc_avg (u : TorusSym.L2R) : reflRc (mirrorR.avg u) = mirrorR.avg (reflRc u) := by
  simp only [Refl3.avg_apply, Refl3.half_apply, _root_.map_smul, _root_.map_add, reflRc_R]

theorem reR_avg (u : TorusSym.L2R) : reR (mirrorR.avg u) = mirrorR.avg (reR u) := by
  rw [reR_apply, reR_apply, _root_.map_smul, _root_.map_add, reflRc_avg]

/-- The projection onto the real even scalar fields. -/
def Pr : TorusSym.L2R →L[ℝ] TorusSym.L2R := reR ∘L mirrorR.avg

theorem Pr_apply (u : TorusSym.L2R) : Pr u = reR (mirrorR.avg u) := rfl

theorem inner_Pr (u v : TorusSym.L2R) : ⟪Pr u, v⟫_ℝ = ⟪u, Pr v⟫_ℝ := by
  rw [Pr_apply, Pr_apply, reR_apply, reR_apply, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, inner_reflRc, mirrorR.inner_avg, mirrorR.inner_avg,
    ← reflRc_avg]

theorem Pr_mem_fix (u : TorusSym.L2R) : Pr u ∈ mirrorR.fix := by
  have h := mirrorR.avg_mem u
  have h' : reflRc (mirrorR.avg u) ∈ mirrorR.fix := fun i => by rw [← reflRc_R, h i]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ h h')

theorem reflRc_Pr (u : TorusSym.L2R) : reflRc (Pr u) = Pr u := by
  rw [Pr_apply, reR_apply, _root_.map_smul, _root_.map_add, reflRc_reflRc, add_comm]

/-- Constant parity `+1` in every variable. -/
def cOne : Fin 3 → ℝ := fun _ => 1

theorem cOne_sq (i : Fin 3) : cOne i * cOne i = 1 := by simp [cOne]

/-- `Lp → ℓ²` Fourier coefficients of scalar functions, as a real map. -/
def sF : L2T →L[ℝ] TorusSym.L2R :=
  (TorusSym.scalarFourier.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ

/-- The inverse. -/
def sFi : TorusSym.L2R →L[ℝ] L2T :=
  (TorusSym.scalarFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ

theorem sF_apply (f : L2T) (k : Z3) : sF f k = mFourierCoeff (f : T3 → ℂ) k :=
  TorusSym.scalarFourier_apply f k

theorem sFi_sF (f : L2T) : sFi (sF f) = f := TorusSym.scalarFourier.symm_apply_apply f

theorem sF_sFi (u : TorusSym.L2R) : sF (sFi u) = u := TorusSym.scalarFourier.apply_symm_apply u

theorem norm_sF (f : L2T) : ‖sF f‖ = ‖f‖ := TorusSym.scalarFourier.norm_map f

theorem inner_sF (f g : L2T) : ⟪sF f, sF g⟫_ℝ = ⟪f, g⟫_ℝ := by
  have e2 : ‖sF (f + g)‖ ^ 2 = ‖f + g‖ ^ 2 := by rw [norm_sF]
  rw [_root_.map_add, norm_add_sq_real, norm_add_sq_real, norm_sF, norm_sF] at e2
  linarith

/-- The mirror extension of scalar fields (`u` even in every variable). -/
def Jr : BoundedDomain.L2 Qr →L[ℝ] TorusSym.L2R := sF ∘L extS cOne_sq

theorem Jr_apply (u : BoundedDomain.L2 Qr) : Jr u = sF (extS cOne_sq u) := rfl

theorem Jr_resQ {v : TorusSym.L2R} (hv : v ∈ mirrorR.fix) (hr : reflRc v = v) :
    Jr (resQ (sFi v)) = v := by
  rw [Jr_apply, extS_resQ cOne_sq (fun i k => ?_) (fun k => ?_), sF_sFi]
  · rw [← sF_apply, ← sF_apply, sF_sFi]
    have h := congrArg (fun w : TorusSym.L2R => w k) (hv i)
    change v (Box.refl i k) = v k at h
    rw [h]; simp [cOne]
  · rw [← sF_apply, ← sF_apply, sF_sFi]
    have h := congrArg (fun w : TorusSym.L2R => w k) hr
    change conj (v (-k)) = v k at h
    rw [← h, Complex.conj_conj]

theorem Jr_mem_fix (u : BoundedDomain.L2 Qr) : Jr u ∈ mirrorR.fix := fun i => by
  ext k
  change Jr u (Box.refl i k) = Jr u k
  rw [Jr_apply, sF_apply, sF_apply, hasPar_extS cOne_sq u i k]
  simp [cOne]

theorem reflRc_Jr (u : BoundedDomain.L2 Qr) : reflRc (Jr u) = Jr u := by
  ext k
  rw [reflRc_apply, Jr_apply, sF_apply, sF_apply, isRealT_extS cOne_sq u, Complex.conj_conj]

/-- **The compression data of the even scalar class**: `J = Jr`, `R = res_Q`, `P = Pr`. -/
def comprR : Compr 8 (BoundedDomain.L2 Qr) TorusSym.L2R where
  J := Jr
  R := resQ ∘L sFi
  P := Pr
  inner_J u v := by rw [Jr_apply, Jr_apply, inner_sF, inner_extS]
  RJ u := by
    change resQ (sFi (sF (extS cOne_sq u))) = u
    rw [sFi_sF, resQ_extS]
  JRP z := Jr_resQ (Pr_mem_fix z) (reflRc_Pr z)
  PJ u := by
    rw [Pr_apply, mirrorR.avg_of_mem (Jr_mem_fix u), reR_apply, reflRc_Jr, ← two_smul ℝ (Jr u),
      smul_smul]
    norm_num
  P_sa := inner_Pr

end Scalar

/-! ## The symmetric and trace-free slots -/

section SymTr

open TorusSym (embL2 symSub trSub Sym3 Tr3 mem_symSub mem_trSub)

theorem extS_congr {c c' : Fin 3 → ℝ} (h : c = c') (hc : ∀ i, c i * c i = 1)
    (hc' : ∀ i, c' i * c' i = 1) (g : BoundedDomain.L2 Qr) : extS hc g = extS hc' g := by
  subst h; rfl

theorem cM_swap (ε : ℝ) (a b : Fin 3) : cM ε (a, b) = cM ε (b, a) := by
  funext i; simp only [cM]; ring

theorem cM_diag (ε : ℝ) (a : Fin 3) : cM ε (a, a) = fun _ => ε := by
  funext i; simp only [cM]; rw [mul_assoc, sgn_mul_self, mul_one]

theorem mFourierCoeff_sum' {ι : Type*} (s : Finset ι) (f : ι → L2T) (k : Z3) :
    mFourierCoeff ((∑ i ∈ s, f i : L2T) : T3 → ℂ) k = ∑ i ∈ s, mFourierCoeff (f i : T3 → ℂ) k := by
  simp only [← mFourierBasis_repr, map_sum]
  rw [lp.coeFn_sum, Finset.sum_apply]

/-- The mirror extension of a symmetric field is fibrewise symmetric. -/
theorem Jm_mem_sym {ε : ℝ} (hε : ε * ε = 1) {E : MQ} (hE : E ∈ BoundedSym.symL2 Qr) :
    Jm ε hε E ∈ fibreSub fun _ : Z3 => symSub := fun k => mem_symSub.2 fun a b => by
  rw [Jm_coeff, Jm_coeff, extS_congr (cM_swap ε a b) _ (cM_sq hε (b, a)), hE a b]

/-- The mirror extension of a trace-free field is fibrewise trace-free. -/
theorem Jm_mem_tr {ε : ℝ} (hε : ε * ε = 1) {E : MQ} (hE : E ∈ BoundedSym.trL2 Qr) :
    Jm ε hε E ∈ fibreSub fun _ : Z3 => trSub := fun k => mem_trSub.2 (by
  have hc0 : ∀ i : Fin 3, (fun _ : Fin 3 => ε) i * (fun _ : Fin 3 => ε) i = 1 := fun _ => hε
  have e : ∀ a, Jm ε hε E k (a, a) = mFourierCoeff (extS hc0 (E (a, a)) : T3 → ℂ) k := fun a => by
    rw [Jm_coeff, extS_congr (cM_diag ε a) _ hc0]
  simp only [e]
  rw [← mFourierCoeff_sum', ← map_sum]
  have : ∑ a, E (a, a) = 0 := hE
  rw [this, _root_.map_zero, ← mFourierBasis_repr, _root_.map_zero]
  rfl)

theorem matSgn_mem_sym_fibre (ε : ℝ) (hε : ε * ε = 1) {U : Submodule ℝ Mat3}
    (hU : ∀ i (M : Mat3), M ∈ U → matSgn ε i M ∈ U) (hcU : ∀ M : Mat3, M ∈ U → conjM M ∈ U)
    {A : L2M} (hA : A ∈ fibreSub fun _ : Z3 => U) : Pm ε hε A ∈ fibreSub fun _ : Z3 => U := by
  have hR : ∀ i, ∀ B ∈ fibreSub (fun _ : Z3 => U), (mirrorM ε hε).R i B ∈
      fibreSub (fun _ : Z3 => U) := fun i B hB k => hU i _ (hB (Box.refl i k))
  have hh : ∀ i, ∀ B ∈ fibreSub (fun _ : Z3 => U), (mirrorM ε hε).half i B ∈
      fibreSub (fun _ : Z3 => U) := fun i B hB =>
    Submodule.smul_mem _ _ (Submodule.add_mem _ hB (hR i B hB))
  have hav : (mirrorM ε hε).avg A ∈ fibreSub fun _ : Z3 => U := by
    rw [Refl3.avg_apply]; exact hh 2 _ (hh 1 _ (hh 0 _ hA))
  have hcj : cjM ((mirrorM ε hε).avg A) ∈ fibreSub fun _ : Z3 => U := fun k => hcU _ (hav (-k))
  rw [Pm_apply, reM_apply]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hav hcj)

theorem resB_mem_symL2 {A : L2M} (hA : A ∈ fibreSub fun _ : Z3 => symSub) :
    resB A ∈ BoundedSym.symL2 Qr := fun i j => by
  rw [resB_apply, resB_apply]
  congr 2
  ext k
  exact mem_symSub.1 (hA k) i j

theorem resB_mem_trL2 {A : L2M} (hA : A ∈ fibreSub fun _ : Z3 => trSub) :
    resB A ∈ BoundedSym.trL2 Qr := by
  change ∑ i, resB A (i, i) = 0
  simp only [resB_apply, ← map_sum, ← ofCoeff_sum]
  have : (∑ i, entry (i, i) A) = 0 := by
    ext k
    simp only [lp.coeFn_sum, Finset.sum_apply, entry_apply, lp.coeFn_zero, Pi.zero_apply]
    exact mem_trSub.1 (hA k)
  rw [this]
  simp [ofCoeff]

/-- **The compression data of the symmetric mirror class** `L²(Q; S) → ℓ²(ℤ³; S)`. -/
def comprS : Compr 8 (BoundedSym.L2S Qr) TorusSym.L2S :=
  (comprM 1 one_mul_one).restrict (BoundedSym.symL2 Qr) (fibreSub fun _ : Z3 => symSub)
    (embL2 symSub) (projL2 symSub) (embL2_mem_fibreSub symSub) (projL2_embL2 symSub)
    (fun _ hw => embL2_projL2 symSub hw) (fun _ hu => Jm_mem_sym one_mul_one hu)
    (fun _ hw => matSgn_mem_sym_fibre 1 one_mul_one
      (fun i _ hM => Box.matSgn_mem_symSub 1 i hM) (fun _ hM => TorusSym.conjM_mem_symSub hM) hw)
    (fun _ hw => resB_mem_symL2 hw)

/-- **The compression data of the trace-free mirror class** (pseudo-tensors). -/
def comprT : Compr 8 (BoundedSym.L2T Qr) TorusSym.L2T :=
  (comprM (-1) neg_one_mul_neg_one).restrict (BoundedSym.trL2 Qr) (fibreSub fun _ : Z3 => trSub)
    (embL2 trSub) (projL2 trSub) (embL2_mem_fibreSub trSub) (projL2_embL2 trSub)
    (fun _ hw => embL2_projL2 trSub hw) (fun _ hu => Jm_mem_tr neg_one_mul_neg_one hu)
    (fun _ hw => matSgn_mem_sym_fibre (-1) neg_one_mul_neg_one
      (fun i _ hM => Box.matSgn_mem_trSub (-1) i hM) (fun _ hM => TorusSym.conjM_mem_trSub hM) hw)
    (fun _ hw => resB_mem_trL2 hw)

theorem embL2_comprS_J (E : BoundedSym.L2S Qr) :
    embL2 symSub (comprS.J E) = Jm 1 one_mul_one E :=
  embL2_projL2 symSub (Jm_mem_sym one_mul_one E.2)

theorem embL2_comprT_J (B : BoundedSym.L2T Qr) :
    embL2 trSub (comprT.J B) = Jm (-1) neg_one_mul_neg_one B :=
  embL2_projL2 trSub (Jm_mem_tr neg_one_mul_neg_one B.2)

theorem embL2_comprS_P (A : TorusSym.L2S) :
    embL2 symSub (comprS.P A) = Pm 1 one_mul_one (embL2 symSub A) :=
  embL2_projL2 symSub (matSgn_mem_sym_fibre 1 one_mul_one
    (fun i _ hM => Box.matSgn_mem_symSub 1 i hM) (fun _ hM => TorusSym.conjM_mem_symSub hM)
    (embL2_mem_fibreSub symSub A))

theorem embL2_comprT_P (A : TorusSym.L2T) :
    embL2 trSub (comprT.P A) = Pm (-1) neg_one_mul_neg_one (embL2 trSub A) :=
  embL2_projL2 trSub (matSgn_mem_sym_fibre (-1) neg_one_mul_neg_one
    (fun i _ hM => Box.matSgn_mem_trSub (-1) i hM) (fun _ hM => TorusSym.conjM_mem_trSub hM)
    (embL2_mem_fibreSub trSub A))

theorem embL2_injective (U : Submodule ℝ Mat3) : Function.Injective (embL2 U) :=
  (embL2 U).injective

/-- `ι (R_i A) = R_i (ι A)` for the even action on `S`. -/
theorem embL2_mirrorS (i : Fin 3) (A : TorusSym.L2S) :
    embL2 symSub (mirrorS.R i A) = (mirrorM 1 one_mul_one).R i (embL2 symSub A) := rfl

theorem embL2_mirrorT (i : Fin 3) (A : TorusSym.L2T) :
    embL2 trSub (mirrorT.R i A) = (mirrorM (-1) neg_one_mul_neg_one).R i (embL2 trSub A) := rfl

theorem embL2_reflS (A : TorusSym.L2S) : embL2 symSub (TorusSym.reflS A) = cjM (embL2 symSub A) :=
  rfl

theorem embL2_reflT (A : TorusSym.L2T) : embL2 trSub (TorusSym.reflT A) = cjM (embL2 trSub A) :=
  rfl

theorem embL2_avgS (A : TorusSym.L2S) :
    embL2 symSub (mirrorS.avg A) = (mirrorM 1 one_mul_one).avg (embL2 symSub A) := by
  simp only [Refl3.avg_apply, Refl3.half_apply, LinearIsometry.map_smul, LinearIsometry.map_add,
    embL2_mirrorS]

theorem embL2_avgT (A : TorusSym.L2T) :
    embL2 trSub (mirrorT.avg A) = (mirrorM (-1) neg_one_mul_neg_one).avg (embL2 trSub A) := by
  simp only [Refl3.avg_apply, Refl3.half_apply, LinearIsometry.map_smul, LinearIsometry.map_add,
    embL2_mirrorT]

/-- `P_S = Re ∘ avg` on `ℓ²(ℤ³; S)`. -/
theorem comprS_P_eq (A : TorusSym.L2S) :
    comprS.P A = (1 / 2 : ℝ) • (mirrorS.avg A + TorusSym.reflS (mirrorS.avg A)) := by
  apply embL2_injective symSub
  rw [embL2_comprS_P, LinearIsometry.map_smul, LinearIsometry.map_add, embL2_reflS, embL2_avgS,
    Pm_apply, reM_apply]

theorem comprT_P_eq (A : TorusSym.L2T) :
    comprT.P A = (1 / 2 : ℝ) • (mirrorT.avg A + TorusSym.reflT (mirrorT.avg A)) := by
  apply embL2_injective trSub
  rw [embL2_comprT_P, LinearIsometry.map_smul, LinearIsometry.map_add, embL2_reflT, embL2_avgT,
    Pm_apply, reM_apply]

/-- `P` commutes with `grad grad`. -/
theorem comprComm_hess : ComprComm TorusSym.symComplex.d0 comprR comprS := by
  have hav : CommOp TorusSym.symComplex.d0 (mirrorR.avg : TorusSym.L2R →ₗ[ℝ] TorusSym.L2R)
      (mirrorS.avg : TorusSym.L2S →ₗ[ℝ] TorusSym.L2S) := fun z => intertwines_hess.avg z
  have hcj : CommOp TorusSym.symComplex.d0 TorusSym.reflR TorusSym.reflS := fun z =>
    ⟨TorusSym.reflL2_mem_mulDomain TorusSym.norm_conjC TorusSym.norm_conjS TorusSym.hessS_conj
      z.2, TorusSym.mulOp_reflL2 TorusSym.norm_conjC TorusSym.norm_conjS TorusSym.hessS_conj z⟩
  intro z
  obtain ⟨h, e⟩ := (hcj.half.comp hav) z
  refine ⟨h, e.trans ?_⟩
  rw [comprS_P_eq]
  rfl

/-- `P` commutes with `curl` on `S`. -/
theorem comprComm_curlS : ComprComm TorusSym.symComplex.d1 comprS comprT := by
  have hav : CommOp TorusSym.symComplex.d1 (mirrorS.avg : TorusSym.L2S →ₗ[ℝ] TorusSym.L2S)
      (mirrorT.avg : TorusSym.L2T →ₗ[ℝ] TorusSym.L2T) := fun z => intertwines_curlS.avg z
  have hcj : CommOp TorusSym.symComplex.d1 TorusSym.reflS TorusSym.reflT := fun z =>
    ⟨TorusSym.reflL2_mem_mulDomain TorusSym.norm_conjS TorusSym.norm_conjT TorusSym.curlS_conj
      z.2, TorusSym.mulOp_reflL2 TorusSym.norm_conjS TorusSym.norm_conjT TorusSym.curlS_conj z⟩
  intro z
  obtain ⟨h, e⟩ := (hcj.half.comp hav) z
  have hz : comprS.P z = (1 / 2 : ℝ) • (mirrorS.avg z + TorusSym.reflS (mirrorS.avg z)) :=
    comprS_P_eq z
  refine ⟨hz ▸ h, ?_⟩
  rw [comprT_P_eq]
  exact (lpmap_congr' _ _ _ hz).trans e

/-- `P_TSD` commutes with `P` on `S`. -/
theorem starProjection_comprS (A : TorusSym.L2S) :
    TorusSym.L2TSDS.starProjection (comprS.P A) = comprS.P (TorusSym.L2TSDS.starProjection A) :=
  starProjection_comm_of_selfAdj TorusSym.L2TSDS comprS.P comprS.P_sa (fun B hB => by
    change embL2 symSub (comprS.P B) ∈ L2TSD
    rw [embL2_comprS_P]
    exact Pm_mem_L2TSD 1 one_mul_one hB) A

/-- `P_TSD` commutes with `P` on `T`. -/
theorem starProjection_comprT (A : TorusSym.L2T) :
    TorusSym.L2TSDT.starProjection (comprT.P A) = comprT.P (TorusSym.L2TSDT.starProjection A) :=
  starProjection_comm_of_selfAdj TorusSym.L2TSDT comprT.P comprT.P_sa (fun B hB => by
    change embL2 trSub (comprT.P B) ∈ L2TSD
    rw [embL2_comprT_P]
    exact Pm_mem_L2TSD (-1) neg_one_mul_neg_one hB) A

end SymTr

/-! ## The complex (4.16) on `Q` with mirror conditions and Prop 4.19 -/

section SymPropagation

open TorusSym (embL2 symSub trSub)

/-- `L²(Q; S)`. -/
abbrev SQ := BoundedSym.L2S Qr
/-- `L²(Q; T)`. -/
abbrev TQ := BoundedSym.L2T Qr
/-- `L²(Q)`. -/
abbrev RQ := BoundedDomain.L2 Qr

/-- **The complex (4.16) on the box with tensorial mirror boundary conditions**,
`H²_N(Q) --grad grad--> H_{nτ}(curl, Q; S) --curl--> L²(Q; T)` (`∂_n u = 0`, `S_{nτ} = 0`), the
compression of the periodic complex `Feec.Legacy.TorusSym.symComplex`. -/
def mirrorSymCxQ : HilbertComplex2 RQ SQ TQ :=
  comprComplex TorusSym.symComplex comprR comprS comprT comprComm_hess comprComm_curlS

/-- The constraint space in `L²(Q; S)`: TSD fields whose mirror extension is TSD on `𝕋³`. -/
abbrev TSDSm : Submodule ℝ SQ := TorusSym.L2TSDS.comap (comprS.J : SQ →ₗ[ℝ] TorusSym.L2S)

/-- The constraint space in `L²(Q; T)`. -/
abbrev TSDTm : Submodule ℝ TQ := TorusSym.L2TSDT.comap (comprT.J : TQ →ₗ[ℝ] TorusSym.L2T)

/-! ### The operators are the weak derivatives on `Q` -/

/-- **`d1` is the mirror curl of Prop 4.17 on symmetric fields**, hence the weak curl on `Q`
(`Feec.Legacy.MirrorCube.mirrorCxQ_d1_eq`). -/
theorem mirrorSymCxQ_d1_eq (E : mirrorSymCxQ.d1.domain) :
    ∃ h : ((E : SQ) : MQ) ∈ mirrorCxQ.d1.domain,
      ((mirrorSymCxQ.d1 E : TQ) : MQ) = mirrorCxQ.d1 ⟨E, h⟩ := by
  have hS : comprS.J E ∈ TorusSym.HcurlS := E.2
  have hc : embL2 symSub (comprS.J E) ∈ Hcurl := (TorusSym.embL2_sym_mem_Hcurl_iff _).2 hS
  rw [embL2_comprS_J] at hc
  refine ⟨hc, ?_⟩
  change resB (embL2 trSub (TorusSym.curlST ⟨comprS.J E, hS⟩)) = resB (curlT ⟨_, hc⟩)
  rw [← TorusSym.curlT_embL2]
  congr 1
  exact lpmap_congr' _ _ _ (embL2_comprS_J E)

/-- **`d0` is the weak Hessian on `Q`**: `∫_Q u ∂_a ∂_b φ = ∫_Q (d0 u)_{ab} φ` for
`φ ∈ C_c^∞(Q)`. -/
theorem mirrorSymCxQ_d0_weakHess (u : mirrorSymCxQ.d0.domain) (a b : Fin 3) {φ : R3 → ℝ}
    (hφ : IsTest Qr φ) :
    ∫ x, (u : RQ) x * pd a (pd b φ) x ∂volume.restrict Qr =
      ∫ x, ((mirrorSymCxQ.d0 u : SQ) : MQ) (a, b) x * φ x ∂volume.restrict Qr := by
  set F : L2T := extS cOne_sq (u : RQ)
  set v : TorusSym.L2R := Jr u
  have hv : v ∈ TorusSym.hessT.domain := u.2
  set Hs := TorusSym.hessT ⟨v, hv⟩
  have hHk : ∀ k p q, (embL2 symSub Hs) k (p, q) = -(v k * freq k p * freq k q) :=
    fun k p q => rfl
  -- the first derivative `∂_a F`
  have hbd : ∀ k, ‖(2 * Real.pi * Complex.I * (k a : ℂ)) * v k‖ ≤ ‖v k‖ + ‖Hs k‖ := by
    intro k
    have h1 : ‖((Hs k : TorusSym.Sym3) : Mat3) (a, a)‖ ≤ ‖Hs k‖ := by
      rw [← Submodule.norm_coe]; exact PiLp.norm_apply_le _ _
    have h2 : ((Hs k : TorusSym.Sym3) : Mat3) (a, a) = -(v k * freq k a * freq k a) := hHk k a a
    rw [h2, norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
    have hf : freq k a = 2 * Real.pi * k a := rfl
    have e : ‖(2 * Real.pi * Complex.I * (k a : ℂ)) * v k‖ = |freq k a| * ‖v k‖ := by
      rw [norm_mul, hf]
      simp [Complex.norm_I, abs_mul, abs_of_pos Real.pi_pos]
    rw [e]
    have ht : |freq k a| ≤ 1 + |freq k a| * |freq k a| := by
      nlinarith [abs_nonneg (freq k a), sq_nonneg (|freq k a| - 1)]
    nlinarith [norm_nonneg (v k), abs_nonneg (freq k a)]
  have hmem : Memℓp (fun k => (2 * Real.pi * Complex.I * (k a : ℂ)) * v k) 2 := by
    have hg : Memℓp (fun k => ‖v k‖ + ‖Hs k‖) 2 :=
      (memℓp_norm_iff.2 (lp.memℓp v)).add (memℓp_norm_iff.2 (lp.memℓp Hs))
    refine hg.mono' fun k => ?_
    refine (hbd k).trans (le_of_eq ?_)
    rw [Real.norm_of_nonneg (by positivity)]
  set Ga : L2T := ofCoeff ⟨_, hmem⟩
  have hF : ∀ k, mFourierCoeff (F : T3 → ℂ) k = v k := fun k => (sF_apply F k).symm
  have h1 : HasWeakPartial a F Ga := (hasWeakPartial_iff a F Ga).2 fun k => by
    rw [mFourierCoeff_ofCoeff, hF]
  set Hab : L2T := ofCoeff (entry (a, b) (embL2 symSub Hs))
  have h2 : HasWeakPartial b Ga Hab := (hasWeakPartial_iff b Ga Hab).2 fun k => by
    rw [mFourierCoeff_ofCoeff, mFourierCoeff_ofCoeff, entry_apply, hHk]
    change -(v k * ((2 * Real.pi * k a : ℝ) : ℂ) * ((2 * Real.pi * k b : ℝ) : ℂ)) =
      2 * Real.pi * Complex.I * (k b : ℂ) * ((2 * Real.pi * Complex.I * (k a : ℂ)) * v k)
    push_cast
    linear_combination (-(4 * Real.pi ^ 2 * (k a : ℂ) * (k b : ℂ) * v k)) * Complex.I_mul_I
  have s1 := resQ_hasWeakPartial h1 (hφ.pdiff b)
  have s2 := resQ_hasWeakPartial h2 hφ
  have hu : resQ F = (u : RQ) := resQ_extS cOne_sq _
  have hd : resQ Hab = ((mirrorSymCxQ.d0 u : SQ) : MQ) (a, b) := rfl
  rw [hu] at s1
  rw [hd] at s2
  rw [s1, s2, neg_neg]

/-! ### Constraint spaces -/

theorem TSDSm_le_TSDS {E : SQ} (hE : E ∈ TSDSm) : E ∈ BoundedSym.TSDS Qr := by
  have h : embL2 symSub (comprS.J E) ∈ L2TSD := hE
  rw [embL2_comprS_J] at h
  exact TSDmE_le_TSD h

theorem TSDTm_le_TSDT {B : TQ} (hB : B ∈ TSDTm) : B ∈ BoundedSym.TSDT Qr := by
  have h : embL2 trSub (comprT.J B) ∈ L2TSD := hB
  rw [embL2_comprT_J] at h
  exact TSDmB_le_TSD h

/-! ### A non-stationary TSD datum -/

theorem cosE_mem_sym : cosE ∈ fibreSub fun _ : Z3 => symSub := fun k =>
  TorusSym.mem_symSub.2 fun a b => by
    change cosField k (a, b) = cosField k (b, a)
    unfold cosField
    split_ifs
    · simp only [M0, mat_apply]; split_ifs <;> simp_all
    · rfl

/-- `E₀ = (2 cos(2π x₃) diag(1, -1, 0))|_Q` as a symmetric field. -/
def cosSQ : SQ := ⟨cosEQ, resB_mem_symL2 cosE_mem_sym⟩

theorem embL2_comprS_cosSQ : embL2 symSub (comprS.J cosSQ) = cosE := by
  rw [embL2_comprS_J]; exact Jm_cosEQ

theorem cosSQ_mem_TSDSm : cosSQ ∈ TSDSm := by
  change embL2 symSub (comprS.J cosSQ) ∈ L2TSD
  rw [embL2_comprS_cosSQ]; exact cosE_mem_L2TSD

/-- The datum `(0, E₀, 0)` for (4.18). -/
def cosStateS : Tot RQ SQ TQ := ini RQ cosSQ 0

theorem cosStateS_mem_Kc : cosStateS ∈ Kc RQ TSDSm TSDTm := by
  rw [mem_Kc, cosStateS, tot_ini]
  exact ⟨rfl, cosSQ_mem_TSDSm, TSDTm.zero_mem⟩

theorem comprS_cosSQ_mem_HcurlS : comprS.J cosSQ ∈ TorusSym.HcurlS :=
  (TorusSym.embL2_sym_mem_Hcurl_iff _).1 (embL2_comprS_cosSQ ▸ cosE_mem_Hcurl)

theorem tot_totJ_cosStateS :
    tot TorusSym.L2R TorusSym.L2S TorusSym.L2T (totJ comprR comprS comprT cosStateS) =
      (0, comprS.J cosSQ, 0) := by
  rw [tot_totJ, cosStateS, tot_ini]
  simp only [_root_.map_zero]

theorem cosStateS_mem_domL : cosStateS ∈ mirrorSymCxQ.domL := by
  rw [mirrorSymCxQ, mem_domL_compr_iff eight_pos, Constraints.mem_domL, tot_totJ_cosStateS]
  refine ⟨TorusSym.symComplex.d0.domain.zero_mem, ⟨comprS_cosSQ_mem_HcurlS, ?_⟩,
    TorusSym.symComplex.d1†.domain.zero_mem⟩
  exact (LinearPMap.mem_ker_iff.1 (TorusSym.L2TSDS_le_ker cosSQ_mem_TSDSm)).elim
    fun y hy => hy.1 ▸ y.2

theorem cosStateS_waveOp_ne : mirrorSymCxQ.waveOp ⟨cosStateS, cosStateS_mem_domL⟩ ≠ 0 := by
  intro h0
  have hi := totJ_waveOp (h0 := comprComm_hess) (h1 := comprComm_curlS) eight_pos cosStateS
    cosStateS_mem_domL
  change totJ _ _ _ (mirrorSymCxQ.waveOp ⟨cosStateS, cosStateS_mem_domL⟩) = _ at hi
  rw [h0, _root_.map_zero] at hi
  have h3 := congrArg (fun y => embL2 trSub
    (tot TorusSym.L2R TorusSym.L2S TorusSym.L2T y).2.2 k0) hi
  simp only [Constraints.tot_waveOp, _root_.map_zero, Prod.snd_zero, lp.coeFn_zero,
    Pi.zero_apply] at h3
  rw [LinearIsometry.map_neg, lp.coeFn_neg, Pi.neg_apply, eq_comm, neg_eq_zero] at h3
  apply curlSym_cosE_ne
  rw [← h3]
  have e : TorusSym.symComplex.d1 (TorusSym.symComplex.prV1 ⟨totJ comprR comprS comprT cosStateS,
      (mem_domL_compr_iff (h0 := comprComm_hess) (h1 := comprComm_curlS) eight_pos _).1
        cosStateS_mem_domL⟩) = TorusSym.curlST ⟨comprS.J cosSQ, comprS_cosSQ_mem_HcurlS⟩ :=
    lpmap_congr' _ _ _ (by simp [tot_totJ_cosStateS])
  rw [e, ← TorusSym.curlT_embL2]
  change curlSym (freq k0) (cosE k0) = curlSym (freq k0) (embL2 symSub (comprS.J cosSQ) k0)
  rw [embL2_comprS_cosSQ]

end SymPropagation

end Feec.Legacy.MirrorCube
