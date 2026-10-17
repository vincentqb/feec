module

public import Feec.Models.Cube.MirrorSym
public import Feec.Models.Torus.BGG

/-!
# The BGG complex (5.1) on the cube with mirror boundary conditions

The method of Thesis Ch. 6 solves the linearized Einstein–Bianchi system through the Hodge wave
equation of the BGG complex (5.1), `grad grad → (S₁, curl)`, imposing the symmetry of `E` weakly
through a multiplier `M`. On the torus the constraint `{0} × L²(TSD) × ({0} × L²(TSD))` reduces
the complex (`Feec.Models.Torus.BGG.reducingSubcomplex`). The torus complex carries the mirror
symmetries: `u` even, `E` with the tensor parities, the multiplier with the pseudo-vector parities
`M(R_k x) = -D_k M(x)` (forced by `S₁ (D M D) = -D S₁ M`, `axialL_sgn`), `B` with the
pseudo-tensor parities (`MirrorBGG.symmetries`). The constraint is invariant, so it descends to

* the **parity model** `MirrorBGG.complex` (the fixed complex);
* the **cube `Q = (0, ½)³`** `MirrorBGG.complexQ`: `L²(Q) → L²(Q; ℂ³ˣ³) → L²(Q; ℂ³) × L²(Q; ℂ³ˣ³)`,
  the compression of the torus complex along the mirror extensions, whose second operator is
  `u ↦ (S₁ u, curl u)` with `S₁ = 2 vskw` pointwise and `curl` the mirror curl of Prop 4.17
  (`MirrorBGG.complexQ_d₁_eq`).

TSD data give solutions with `σ ≡ 0`, `u` TSD (the weakly imposed symmetry holds strongly),
`M ≡ 0` and `B` TSD, in particular symmetric (`MirrorBGG.mem_tsdQ_iff`,
`MirrorBGG.tsd_of_mem_tsdQ`). This is the repair of the Ch. 6 claim; with the boundary conditions
of Thesis §6.3 it fails on every bounded domain (`Feec.Counterexamples.BoundedBGG`).

## Main results

* **`MirrorBGG.reducingSubcomplex`**, `MirrorBGG.propagates`, `MirrorBGG.existsUnique_mem`,
  `MirrorBGG.invariantCore_eq`, `MirrorBGG.exists_nonstationary` (parity model).
* **`MirrorBGG.reducingSubcomplexQ`**, `MirrorBGG.propagatesQ`, `MirrorBGG.existsUnique_memQ`,
  `MirrorBGG.invariantCore_eqQ`, `MirrorBGG.exists_nonstationaryQ`, `MirrorBGG.mem_tsdQ_iff`,
  `MirrorBGG.tsd_of_mem_tsdQ`, `MirrorBGG.complexQ_d₁_eq`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5 (§5.1), Ch. 6 (§6.1, §6.3)
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021] (BGG)
* [D. N. Arnold, R. S. Falk, R. Winther, *Mixed finite element methods for linear elasticity with weakly imposed symmetry*][AFW2007]
  (weak symmetry)
-/

open scoped InnerProductSpace
open Set LinearPMap MeasureTheory

@[expose] public noncomputable section

namespace Feec.Models.Cube.MirrorBGG

open Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.SymCurl Feec.Fourier.BGG
  Feec.ShortHilbertComplex
open Feec.Models.Cube.MirrorExt
open Feec.Models.Cube.Mirror (sgn sgn_mul_self conj_sgn cE cB cPV cE_sq cB_sq cPV_sq conj_cE
  conj_cB freq_flipAt curl_flip matR_mem_tsd leviCivita3_sgn)
open Feec.Models.Cube.MirrorSym (cU cU_sq)
open Feec.HilbertComplex (ScaledEmbedding totalSub ReducingSubcomplex)

/-! ### The mirror symmetries of the torus BGG complex -/

theorem conj_cPV (a k : Fin 3) : (starRingEnd ℂ) (cPV a k) = cPV a k := by
  simp [cPV, conj_sgn]

/-- **`S₁ (D_k M D_k) = -D_k S₁ M`**: the axial vector of a reflected matrix is the reflected
pseudo-vector. -/
theorem axialL_sgn (k : Fin 3) (M : Mat) :
    axialL (sgnCLM (Fin 3 × Fin 3) (fun p => cE p k) M) =
      sgnCLM (Fin 3) (fun a => cPV a k) (axialL M) := by
  ext a
  simp only [axialL_apply, sgnCLM_apply, PiLp.toLp_apply, MatrixSymbol.axial, toMatrix_apply,
    Finset.mul_sum, cE, cPV]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  linear_combination M (b, c) * leviCivita3_sgn k a b c

/-- `(v, M) ↦ (-D_k v, -D_k M D_k)` on the target fibre `ℂ³ × ℂ³ˣ³`. -/
def vmR (k : Fin 3) : VM →L[ℂ] VM :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ Vec Mat).symm.toContinuousLinearMap ∘L
    ((sgnCLM (Fin 3) (fun a => cPV a k)).prodMap (sgnCLM (Fin 3 × Fin 3) (fun p => cB p k))) ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℂ Vec Mat).toContinuousLinearMap

theorem vmR_apply (k : Fin 3) (w : VM) :
    vmR k w = WithLp.toLp 2 (sgnCLM (Fin 3) (fun a => cPV a k) (WithLp.ofLp w).1,
      sgnCLM (Fin 3 × Fin 3) (fun p => cB p k) (WithLp.ofLp w).2) := rfl

theorem vmR_vmR (k : Fin 3) (w : VM) : vmR k (vmR k w) = w := by
  rw [vmR_apply, vmR_apply, WithLp.ofLp_toLp, sgnCLM_sgnCLM (fun a => cPV_sq a k),
    sgnCLM_sgnCLM (fun p => cB_sq p k), Prod.mk.eta, WithLp.toLp_ofLp]

theorem inner_vmR (k : Fin 3) (v w : VM) : ⟪vmR k v, vmR k w⟫_ℂ = ⟪v, w⟫_ℂ := by
  rw [inner_VM, inner_VM, vmR_apply, vmR_apply, WithLp.ofLp_toLp, WithLp.ofLp_toLp,
    inner_sgnCLM (fun a => cPV_sq a k) (fun a => conj_cPV a k),
    inner_sgnCLM (fun p => cB_sq p k) (fun p => conj_cB p k)]

theorem vmR_comm (k l : Fin 3) (w : VM) : vmR k (vmR l w) = vmR l (vmR k w) := by
  simp only [vmR_apply]
  rw [sgnCLM_comm _ _ (WithLp.ofLp w).1, sgnCLM_comm _ _ (WithLp.ofLp w).2]

theorem hessM_flip (k : Fin 3) (n : Fin 3 → ℤ) (c : ℂ) :
    hessM (Fourier.Torus.freq (flipAt k n)) c =
      sgnCLM (Fin 3 × Fin 3) (fun p => cE p k) (hessM (Fourier.Torus.freq n) c) := by
  ext ⟨a, b⟩
  rw [sgnCLM_apply, hessM_apply, hessM_apply, freq_flipAt, freq_flipAt]
  simp only [cE]; ring

theorem bgg_flip (k : Fin 3) (n : Fin 3 → ℤ) (M : Mat) :
    bgg (Fourier.Torus.freq (flipAt k n)) (sgnCLM (Fin 3 × Fin 3) (fun p => cE p k) M) =
      vmR k (bgg (Fourier.Torus.freq n) M) := by
  rw [bgg_apply, bgg_apply, vmR_apply, WithLp.ofLp_toLp, axialL_sgn, curl_flip]

/-- The fibre maps of the `k`-th reflection on the three spaces. -/
def fib (k : Fin 3) : ∀ i : Fin 3, W3 ℂ Mat VM i →L[ℂ] W3 ℂ Mat VM i
  | 0 => ContinuousLinearMap.id ℂ ℂ
  | 1 => sgnCLM (Fin 3 × Fin 3) fun p => cE p k
  | 2 => vmR k

/-- **The mirror reflections of the torus BGG complex (5.1)**, as fibre symmetries. -/
def symmetries : (Fourier.Torus.symbolComplex bggFamily).Symmetries (Fin 3) where
  R := flipRefl
  ρ := fib
  invol k i v := by
    fin_cases i
    · rfl
    · exact sgnCLM_sgnCLM (fun p => cE_sq p k) v
    · exact vmR_vmR k v
  inner_ρ k i v w := by
    fin_cases i
    · rfl
    · exact inner_sgnCLM (fun p => cE_sq p k) (fun p => conj_cE p k) v w
    · exact inner_vmR k v w
  symm k i j n v := by
    change bggFamily.m i j (Fourier.Torus.freq (flipAt k n)) (fib k i v) =
      fib k j (bggFamily.m i j _ v)
    fin_cases i <;> fin_cases j
    all_goals first
      | (change (0 : _ →L[ℂ] _) _ = fib k _ ((0 : _ →L[ℂ] _) v); simp)
      | exact hessM_flip k n v
      | exact bgg_flip k n v
  comm_σ k l n := flipAt_comm k l n
  comm_ρ k l i v := by
    fin_cases i
    · rfl
    · exact sgnCLM_comm _ _ v
    · exact vmR_comm k l v

/-- **The mirror action of `(ℤ/2)³`** on the torus BGG complex. -/
abbrev action : Models.Torus.BGG.complex.Action (Multiplicative (Fin 3 → ZMod 2)) :=
  symmetries.toAction

/-- **The mirror cube BGG complex (5.1)** (parity model). -/
abbrev complex := action.fixedComplex

theorem mem_fixed_iff {i : Fin 3} {x : Models.Torus.BGG.Space i} :
    x ∈ action.fixed i ↔ ∀ k, symLp (symmetries.R k) (fib k i) x = x :=
  symmetries.mem_fixed_toAction

theorem mem_fixed_zero {u : Models.Torus.BGG.Space 0} :
    u ∈ action.fixed 0 ↔ u ∈ scalarParity (Fin 3) cU := by
  have h := mem_scalarParity_iff_symLp (d := Fin 3) cU_sq
    (u := (u : Lp ℂ 2 (Measure.count : Measure (Fin 3 → ℤ))))
  simp only [cU, one_smul] at h
  exact mem_fixed_iff.trans h.symm

theorem mem_fixed_one {u : Models.Torus.BGG.Space 1} :
    u ∈ action.fixed 1 ↔ u ∈ fieldParity cE :=
  mem_fixed_iff.trans (mem_fieldParity_iff_symLp cE_sq).symm

/-- The reflection of a sequence of pairs acts componentwise. -/
theorem prodLp_symm_symLp_vmR (k : Fin 3)
    (u : Lp VM 2 (Measure.count : Measure (Fin 3 → ℤ))) :
    prodLp.symm (symLp (flipRefl k) (vmR k) u) =
      WithLp.toLp 2 (symLp (flipRefl k) (sgnCLM (Fin 3) fun a => cPV a k) (prodLp.symm u).fst,
        symLp (flipRefl k) (sgnCLM (Fin 3 × Fin 3) fun p => cB p k) (prodLp.symm u).snd) := by
  refine (WithLp.ext_iff _).2 (Prod.ext ?_ ?_)
  · refine Lp.ext_count fun n => ?_
    have h1 := prodLp_symm_fst (symLp (flipRefl k) (vmR k) u) n
    have h2 := Measure.ae_count_iff.1 (coeFn_symLp (flipRefl k) (vmR k) u) n
    have h3 := Measure.ae_count_iff.1 (coeFn_symLp (flipRefl k)
      (sgnCLM (Fin 3) fun a => cPV a k) (prodLp.symm u).fst) n
    have h4 := prodLp_symm_fst u ((flipRefl k).σ n)
    change (((prodLp.symm (symLp (flipRefl k) (vmR k) u)).fst : Lp Vec 2 _) : _ → Vec) n =
      ((symLp (flipRefl k) (sgnCLM (Fin 3) fun a => cPV a k) (prodLp.symm u).fst :
        Lp Vec 2 _) : _ → Vec) n
    rw [h1, h2, h3]
    beta_reduce
    rw [h4]
    rfl
  · refine Lp.ext_count fun n => ?_
    have h1 := prodLp_symm_snd (symLp (flipRefl k) (vmR k) u) n
    have h2 := Measure.ae_count_iff.1 (coeFn_symLp (flipRefl k) (vmR k) u) n
    have h3 := Measure.ae_count_iff.1 (coeFn_symLp (flipRefl k)
      (sgnCLM (Fin 3 × Fin 3) fun p => cB p k) (prodLp.symm u).snd) n
    have h4 := prodLp_symm_snd u ((flipRefl k).σ n)
    change (((prodLp.symm (symLp (flipRefl k) (vmR k) u)).snd : Lp Mat 2 _) : _ → Mat) n =
      ((symLp (flipRefl k) (sgnCLM (Fin 3 × Fin 3) fun p => cB p k) (prodLp.symm u).snd :
        Lp Mat 2 _) : _ → Mat) n
    rw [h1, h2, h3]
    beta_reduce
    rw [h4]
    rfl

theorem symLp_vmR_eq_iff (k : Fin 3) (u : Lp VM 2 (Measure.count : Measure (Fin 3 → ℤ))) :
    symLp (flipRefl k) (vmR k) u = u ↔
      symLp (flipRefl k) (sgnCLM (Fin 3) fun a => cPV a k) (prodLp.symm u).fst =
          (prodLp.symm u).fst ∧
        symLp (flipRefl k) (sgnCLM (Fin 3 × Fin 3) fun p => cB p k) (prodLp.symm u).snd =
          (prodLp.symm u).snd := by
  rw [← prodLp.symm.injective.eq_iff, prodLp_symm_symLp_vmR]
  constructor
  · intro h
    exact ⟨congrArg WithLp.fst h, congrArg WithLp.snd h⟩
  · rintro ⟨h1, h2⟩
    exact (WithLp.ext_iff _).2 (Prod.ext h1 h2)

/-- The fixed fields of the third slot: the multiplier with the pseudo-vector parities `cPV`, the
magnetic field with the pseudo-tensor parities `cB`. -/
theorem mem_fixed_two {u : Models.Torus.BGG.Space 2} :
    u ∈ action.fixed 2 ↔
      (prodLp.symm u).fst ∈ fieldParity cPV ∧ (prodLp.symm u).snd ∈ fieldParity cB := by
  rw [mem_fixed_iff, mem_fieldParity_iff_symLp cPV_sq, mem_fieldParity_iff_symLp cB_sq,
    ← forall_and]
  exact forall_congr' fun k => symLp_vmR_eq_iff k u

theorem vmR_mem_tsdB (k : Fin 3) (n : Fin 3 → ℤ) {w : VM}
    (hw : w ∈ tsdB (Fourier.Torus.freq (flipAt k n))) : vmR k w ∈ tsdB (Fourier.Torus.freq n) := by
  obtain ⟨h1, h2⟩ := mem_tsdB.1 hw
  rw [vmR_apply, mem_tsdB, WithLp.ofLp_toLp, h1, _root_.map_zero]
  exact ⟨rfl, matR_mem_tsd k n (s := fun p => cB p k) (fun p => by simp only [cB]; ring)
    (fun a => by simp only [cB, sgn_mul_self]) (fun p => by simp only [cB, sgn_mul_self]; ring) h2⟩

theorem fib_mem_bggK (k i : Fin 3) (n : Fin 3 → ℤ) {v : W3 ℂ Mat VM i}
    (hv : v ∈ bggK i (Fourier.Torus.freq (flipAt k n))) :
    fib k i v ∈ bggK i (Fourier.Torus.freq n) := by
  fin_cases i
  · have h0 : (v : ℂ) = 0 := (Submodule.mem_bot ℂ).1 hv
    exact (Submodule.mem_bot ℂ).2 h0
  · exact matR_mem_tsd k n (s := fun p => cE p k) (fun p => by simp only [cE]; ring)
      (fun a => by simp only [cE, sgn_mul_self]) (fun p => by simp only [cE, sgn_mul_self]; ring) hv
  · exact vmR_mem_tsdB k n hv

theorem act_mem_constraint (g : Multiplicative (Fin 3 → ZMod 2)) (i : Fin 3)
    {x : Models.Torus.BGG.Space i} (hx : x ∈ Models.Torus.BGG.constraint i) :
    action.act g i x ∈ Models.Torus.BGG.constraint i :=
  symmetries.act_mem_fibreSub (K := fun i n => bggK i (Fourier.Torus.freq n))
    (fun k i n _ hv => fib_mem_bggK k i n hv) g i hx

/-- The TSD constraint of the mirror cube BGG complex. -/
abbrev constraint (i : Fin 3) : Submodule ℂ (action.fixed i) :=
  (Models.Torus.BGG.constraint i).comap (action.fixed i).subtype

/-- **The TSD constraint reduces the mirror cube BGG complex.**
See [QuennevilleBelair2015], Ch. 6 (corrected). -/
theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  action.reducingSubcomplex_comap_fixed Models.Torus.BGG.reducingSubcomplex act_mem_constraint

/-- **The Ch. 6 method on the mirror cube keeps TSD data TSD** (parity model).
See [QuennevilleBelair2015], Ch. 6 (corrected). -/
theorem propagates {a b : ℝ} {F U : ℝ → PiLp 2 fun i => action.fixed i}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ totalSub constraint) (hF : ∀ t ∈ Icc a b, F t ∈ totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ totalSub constraint :=
  reducingSubcomplex.propagates hU h0 hF

/-- The Ch. 6 system on the mirror cube with existence and uniqueness (parity model).
See [QuennevilleBelair2015], Ch. 6 (corrected). -/
theorem existsUnique_mem {U₀ : PiLp 2 fun i => action.fixed i} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀K : U₀ ∈ totalSub constraint) {F : ℝ → PiLp 2 fun i => action.fixed i} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFK : ∀ t ∈ Icc a b, F t ∈ totalSub constraint) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub constraint) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  reducingSubcomplex.existsUnique_mem hU₀ hU₀K hF hFK

/-- `K* = K` for the Ch. 6 system on the mirror cube (parity model).
See [QuennevilleBelair2015], Ch. 6 (corrected). -/
theorem invariantCore_eq :
    complex.waveGroup.invariantCore (totalSub constraint) = totalSub constraint :=
  reducingSubcomplex.invariantCore_eq

/-! ### A non-stationary TSD datum -/

open Feec.Models.Cube.Mirror (k0 M0 cosCoeff cosCoeff_eq_zero cosE coe_cosE cosE_mem_fixed
  cosE_mem_constraint curl_M0_ne)

theorem cosE_mem_domain : cosE ∈ (Models.Torus.BGG.complex.d 1 2).domain :=
  mem_mulDomain_of_finite _ {k0, -k0} fun _ hn => (coe_cosE _).trans (cosCoeff_eq_zero hn)

theorem cosE_mem_constraint' : cosE ∈ Models.Torus.BGG.constraint 1 := cosE_mem_constraint

/-- The datum `(0, E₀, 0)`, `E₀ = 2 cos(2π x₃) diag(1, -1, 0)`, on the torus. -/
def cosState : PiLp 2 Models.Torus.BGG.Space := WithLp.toLp 2 (Pi.single 1 cosE)

theorem cosState_zero : cosState 0 = 0 :=
  Pi.single_eq_of_ne (M := Models.Torus.BGG.Space) (by decide : (0 : Fin 3) ≠ 1) cosE
theorem cosState_one : cosState 1 = cosE :=
  Pi.single_eq_same (M := Models.Torus.BGG.Space) (1 : Fin 3) cosE
theorem cosState_two : cosState 2 = 0 :=
  Pi.single_eq_of_ne (M := Models.Torus.BGG.Space) (by decide : (2 : Fin 3) ≠ 1) cosE

theorem cosState_mem_domain : cosState ∈ Models.Torus.BGG.complex.wave.domain :=
  HilbertComplex.mem_wave_domain_fin3 _
    (by rw [cosState_zero]; exact Submodule.zero_mem _)
    (by rw [cosState_one]; exact cosE_mem_domain)
    (by rw [cosState_one]
        exact Models.Torus.BGG.mem_domain_adjoint_of_mem_constraint cosE_mem_constraint')
    (by rw [cosState_two]; exact Submodule.zero_mem _)

theorem bgg_cosE_apply :
    ((Models.Torus.BGG.complex.d 1 2 ⟨cosE, cosE_mem_domain⟩ :
      Lp VM 2 (Measure.count : Measure (Fin 3 → ℤ))) : (Fin 3 → ℤ) → VM) k0 =
      bgg (Fourier.Torus.freq k0) M0 := by
  refine (Operator.coeFn_mulOp_count (fun n => bggFamily.m 1 2 (Fourier.Torus.freq n))
    ⟨cosE, cosE_mem_domain⟩ k0).trans ?_
  change bgg (Fourier.Torus.freq k0) ((cosE : (Fin 3 → ℤ) → Mat) k0) = _
  rw [coe_cosE]
  simp [cosCoeff]

/-- **`(S₁, curl) E₀ ≠ 0`**: its curl component at the frequency `k0` is `curl M0 ≠ 0`. -/
theorem bgg_cosE_ne : Models.Torus.BGG.complex.d 1 2 ⟨cosE, cosE_mem_domain⟩ ≠ 0 := by
  intro h
  apply curl_M0_ne
  have e := congrArg (fun w : VM => (WithLp.ofLp w).2) bgg_cosE_apply
  simp only [bgg_apply, WithLp.ofLp_toLp] at e
  rw [← e, h, Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) k0]
  rfl

theorem wave_cosState_ne :
    Models.Torus.BGG.complex.wave ⟨cosState, cosState_mem_domain⟩ ≠ 0 := by
  intro h
  have h2 := congrArg (fun y : PiLp 2 Models.Torus.BGG.Space => y 2) h
  rw [HilbertComplex.wave_apply_fin3_two] at h2
  exact bgg_cosE_ne ((apply_congr' _ _ _ cosState_one.symm).trans h2)

theorem cosState_mem_fixed (i : Fin 3) : cosState i ∈ action.fixed i := by
  fin_cases i
  · change cosState 0 ∈ _; rw [cosState_zero]; exact Submodule.zero_mem _
  · change cosState 1 ∈ _; rw [cosState_one]
    exact mem_fixed_one.2 (Mirror.mem_fixed_one.1 cosE_mem_fixed)
  · change cosState 2 ∈ _; rw [cosState_two]; exact Submodule.zero_mem _

theorem cosState_mem_constraint (i : Fin 3) : cosState i ∈ Models.Torus.BGG.constraint i := by
  fin_cases i
  · change cosState 0 ∈ _; rw [cosState_zero]; exact Submodule.zero_mem _
  · change cosState 1 ∈ _; rw [cosState_one]; exact cosE_mem_constraint'
  · change cosState 2 ∈ _; rw [cosState_two]; exact Submodule.zero_mem _

/-- **A non-stationary TSD datum for the Ch. 6 system on the mirror cube** (parity model).
See [QuennevilleBelair2015], Ch. 6 (corrected). -/
theorem exists_nonstationary :
    ∃ y ∈ complex.wave.domain, y ∈ totalSub constraint ∧ y ∉ complex.waveGroup.stationary := by
  obtain ⟨h1, h2⟩ := action.reducingSubcomplex_fixed.not_mem_stationary
    (y := WithLp.toLp 2 fun i => ⟨cosState i, cosState_mem_fixed i⟩) cosState_mem_domain
    wave_cosState_ne
  exact ⟨_, h1, fun i => cosState_mem_constraint i, h2⟩

/-! ### The second operator on the torus: `(S₁, curl)` -/

/-- `S₁ = 2 vskw` pointwise on coefficient sequences. -/
def axialLp : Lp Mat 2 (Measure.count : Measure (Fin 3 → ℤ)) →L[ℂ]
    Lp Vec 2 (Measure.count : Measure (Fin 3 → ℤ)) :=
  axialL.compLpL 2 Measure.count

theorem axialLp_apply (v : Lp Mat 2 (Measure.count : Measure (Fin 3 → ℤ))) (n : Fin 3 → ℤ) :
    (axialLp v : (Fin 3 → ℤ) → Vec) n = axialL ((v : (Fin 3 → ℤ) → Mat) n) :=
  Measure.ae_count_iff.1 (axialL.coeFn_compLpL (p := 2) (μ := Measure.count) v) n

/-- **`(S₁, curl)` on the torus**: `D((S₁, curl)) ⊆ H(curl)` and `(S₁, curl) u = (S₁ u, curl u)`. -/
theorem torus_d₁_eq (v : Models.Torus.BGG.Space 1)
    (hv : v ∈ (Models.Torus.BGG.complex.d 1 2).domain) :
    ∃ h : v ∈ (Models.Torus.GradCurl.complex.d 1 2).domain,
      prodLp.symm (Models.Torus.BGG.complex.d 1 2 ⟨v, hv⟩) =
        WithLp.toLp 2 (axialLp v, Models.Torus.GradCurl.complex.d 1 2 ⟨v, h⟩) := by
  have hw : ∀ n, ((Models.Torus.BGG.complex.d 1 2 ⟨v, hv⟩ :
      Lp VM 2 (Measure.count : Measure (Fin 3 → ℤ))) : (Fin 3 → ℤ) → VM) n =
        bgg (Fourier.Torus.freq n) ((v : (Fin 3 → ℤ) → Mat) n) := fun n =>
    Operator.coeFn_mulOp_count (fun n => bggFamily.m 1 2 (Fourier.Torus.freq n)) ⟨v, hv⟩ n
  obtain ⟨h, e⟩ := exists_mulOp_count_eq (fun n => gradCurl.m 1 2 (Fourier.Torus.freq n))
    (u := v) (v := (prodLp.symm (Models.Torus.BGG.complex.d 1 2 ⟨v, hv⟩)).snd) fun n =>
      ((prodLp_symm_snd (E := Vec) (F := Mat) (Models.Torus.BGG.complex.d 1 2 ⟨v, hv⟩) n).trans
        (congrArg WithLp.snd (hw n))).symm
  refine ⟨h, (WithLp.ext_iff _).2 (Prod.ext ?_ ?_)⟩
  · exact Lp.ext_count fun n =>
      (prodLp_symm_fst (E := Vec) (F := Mat) (Models.Torus.BGG.complex.d 1 2 ⟨v, hv⟩) n).trans
        ((congrArg WithLp.fst (hw n)).trans (axialLp_apply v n).symm)
  · exact e.symm

/-! ### The cube `Q = (0, ½)³` -/

open Geometry (Q)
open UnitAddTorus (mFourierCoeff)
open Feec.Models.Cube.Mirror (VQ MQ extL2_congr eight_pos two_pow_card cosEQ J_cosEQ)
open Feec.Models.Cube.MirrorSym (RQ J₀)

/-- `L²(Q; ℂ³) × L²(Q; ℂ³ˣ³)`, the space of pairs `(M, B)`. -/
abbrev W2Q : Type := WithLp 2 (VQ × MQ)

/-- The spaces `L²(Q)`, `L²(Q; ℂ³ˣ³)`, `L²(Q; ℂ³) × L²(Q; ℂ³ˣ³)` of the BGG complex on `Q`. -/
abbrev SpaceQ (i : Fin 3) : Type := W3 RQ MQ W2Q i

/-- The mirror extension of tensors, `L²(Q; ℂ³ˣ³) → ℓ²(ℤ³; ℂ³ˣ³)`. -/
abbrev J₁ : MQ →L[ℂ] Lp Mat 2 (Measure.count : Measure (Fin 3 → ℤ)) := extF (c := cE) cE_sq

/-- The mirror extension of pairs (pseudo-vector, pseudo-tensor),
`L²(Q; ℂ³) × L²(Q; ℂ³ˣ³) → ℓ²(ℤ³; ℂ³ × ℂ³ˣ³)`. -/
def J₂ : W2Q →L[ℂ] Lp VM 2 (Measure.count : Measure (Fin 3 → ℤ)) :=
  pairLp (extF (c := cPV) cPV_sq) (extF (c := cB) cB_sq)

theorem prodLp_symm_J₂ (w : W2Q) :
    prodLp.symm (J₂ w) =
      WithLp.toLp 2 (extF (c := cPV) cPV_sq (WithLp.ofLp w).1,
        extF (c := cB) cB_sq (WithLp.ofLp w).2) := by
  rw [J₂, pairLp_apply, LinearIsometryEquiv.symm_apply_apply]

/-- **The mirror extensions** of the BGG complex on `Q`: `u` even in every variable, `E` with the
tensor parities, `(M, B)` with the pseudo-vector and pseudo-tensor parities. -/
def J : ∀ i : Fin 3, SpaceQ i →L[ℂ] Models.Torus.BGG.Space i
  | 0 => J₀
  | 1 => J₁
  | 2 => J₂

theorem inner_J (i : Fin 3) (x y : SpaceQ i) :
    ⟪J i x, J i y⟫_ℂ = ((8 : ℝ) : ℂ) * ⟪x, y⟫_ℂ := by
  fin_cases i
  · exact (inner_extS cU_sq x y).trans (by rw [two_pow_card]; rfl)
  · exact (inner_extF cE_sq x y).trans (by rw [two_pow_card]; rfl)
  · exact (inner_pairLp (fun u v => inner_extF cPV_sq u v) (fun u v => inner_extF cB_sq u v)
      x y).trans (by rw [two_pow_card]; rfl)

theorem mem_range_J₂ (u : Lp VM 2 (Measure.count : Measure (Fin 3 → ℤ))) :
    u ∈ LinearMap.range (J₂ : W2Q →ₗ[ℂ] _) ↔
      (prodLp.symm u).fst ∈ fieldParity cPV ∧ (prodLp.symm u).snd ∈ fieldParity cB := by
  constructor
  · rintro ⟨w, rfl⟩
    change (prodLp.symm (J₂ w)).fst ∈ _ ∧ (prodLp.symm (J₂ w)).snd ∈ _
    rw [prodLp_symm_J₂]
    exact ⟨extF_mem cPV_sq _, extF_mem cB_sq _⟩
  · rintro ⟨h1, h2⟩
    refine ⟨WithLp.toLp 2
      (Geometry.resQF ((Fourier.Torus.fieldFourier (Fin 3) (Fin 3)).symm (prodLp.symm u).fst),
        Geometry.resQF ((Fourier.Torus.fieldFourier (Fin 3) (Fin 3 × Fin 3)).symm
          (prodLp.symm u).snd)), ?_⟩
    change J₂ _ = u
    rw [← prodLp.symm.injective.eq_iff, prodLp_symm_J₂, WithLp.ofLp_toLp, extF_resQF cPV_sq h1,
      extF_resQF cB_sq h2]
    rfl

theorem range_J (i : Fin 3) :
    LinearMap.range (J i : SpaceQ i →ₗ[ℂ] Models.Torus.BGG.Space i) = action.fixed i := by
  ext u
  fin_cases i
  · exact (Iff.of_eq (congrArg (u ∈ ·) (range_extS cU_sq))).trans mem_fixed_zero.symm
  · exact (Iff.of_eq (congrArg (u ∈ ·) (range_extF cE_sq))).trans mem_fixed_one.symm
  · exact (mem_range_J₂ u).trans mem_fixed_two.symm

instance (i : Fin 3) :
    (LinearMap.range (J i : SpaceQ i →ₗ[ℂ] Models.Torus.BGG.Space i)).HasOrthogonalProjection := by
  rw [range_J]; infer_instance

theorem reducingSubcomplex_range :
    Models.Torus.BGG.complex.ReducingSubcomplex fun i =>
      LinearMap.range (J i : SpaceQ i →ₗ[ℂ] Models.Torus.BGG.Space i) := by
  convert action.reducingSubcomplex_fixed using 1
  exact funext range_J

/-- **The BGG complex (5.1) of genuine fields on `Q` with mirror boundary conditions**:
`L²(Q) --grad grad--> L²(Q; ℂ³ˣ³) --(S₁, curl)--> L²(Q; ℂ³) × L²(Q; ℂ³ˣ³)`, the compression of the
torus complex along the mirror extensions. -/
abbrev complexQ : HilbertComplex ℂ ComplexShape.fin3 SpaceQ :=
  Models.Torus.BGG.complex.compress J eight_pos inner_J reducingSubcomplex_range

/-- The mirror extensions embed the cube BGG complex in the torus complex (scale `8`). -/
def embeddingQ : ScaledEmbedding complexQ Models.Torus.BGG.complex :=
  ScaledEmbedding.ofCompress eight_pos inner_J reducingSubcomplex_range

theorem J_complexQ_d {i j : Fin 3} (x : (complexQ.d i j).domain) :
    J j (complexQ.d i j x) = Models.Torus.BGG.complex.d i j
      ⟨J i x, (HilbertComplex.mem_compress_domain_iff eight_pos inner_J _).1 x.2⟩ :=
  HilbertComplex.J_compress_d eight_pos inner_J reducingSubcomplex_range x

theorem mem_complexQ_domain_iff {i j : Fin 3} {x : SpaceQ i} :
    x ∈ (complexQ.d i j).domain ↔ J i x ∈ (Models.Torus.BGG.complex.d i j).domain :=
  HilbertComplex.mem_compress_domain_iff eight_pos inner_J reducingSubcomplex_range

/-! #### The second operator on `Q` -/

/-- `S₁ = 2 vskw` pointwise on `L²(Q; ℂ³ˣ³)`: `(S₁ u)_a = ε_{abc} u_{bc}`. -/
def axialQ : MQ →L[ℂ] VQ :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => RQ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun a => ∑ b, ∑ c,
      leviCivita3 ℂ a b c • PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 × Fin 3 => RQ) (b, c)

theorem axialQ_apply (u : MQ) (a : Fin 3) :
    axialQ u a = ∑ b, ∑ c, leviCivita3 ℂ a b c • u (b, c) := by
  simp [axialQ]

theorem cPV_eq_cE {a b c : Fin 3} (h : leviCivita3 ℂ a b c ≠ 0) : cPV a = cE (b, c) := by
  funext k
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases k <;>
    simp_all [leviCivita3_apply, cPV, cE, sgn]

/-- The mirror extension intertwines `S₁`: pseudo-vector parities on the axial vector. -/
theorem extF_axialQ (u : MQ) : extF (c := cPV) cPV_sq (axialQ u) = axialLp (J₁ u) := by
  refine Lp.ext_count fun n => ?_
  ext a
  rw [extF_coeff, axialLp_apply, axialL_apply, PiLp.toLp_apply, ← coeffCLM_apply, axialQ_apply]
  simp only [map_sum, _root_.map_smul, coeffCLM_apply, smul_eq_mul, MatrixSymbol.axial,
    toMatrix_apply, extF_coeff]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  by_cases hε : leviCivita3 ℂ a b c = 0
  · rw [hε, zero_mul, zero_mul]
  · rw [extL2_congr (cPV_eq_cE hε) (cPV_sq a) (cE_sq (b, c))]

/-- **`d₁ u = (S₁ u, curl u)`**: the pointwise skew part `S₁ = 2 vskw` and the mirror curl of
Prop 4.17 (the weak curl on `Q`, `Feec.Models.Cube.Mirror.d₁_le_maximal`). -/
theorem complexQ_d₁_eq (u : (complexQ.d 1 2).domain) :
    ∃ h : (u.1 : MQ) ∈ (Mirror.complexQ.d 1 2).domain,
      (complexQ.d 1 2 u : W2Q) =
        WithLp.toLp 2 (axialQ (u.1 : MQ), Mirror.complexQ.d 1 2 ⟨u.1, h⟩) := by
  have hu : J₁ (u.1 : MQ) ∈ (Models.Torus.BGG.complex.d 1 2).domain :=
    mem_complexQ_domain_iff.1 u.2
  obtain ⟨h, e⟩ := torus_d₁_eq _ hu
  have hQ : (u.1 : MQ) ∈ (Mirror.complexQ.d 1 2).domain := Mirror.mem_complexQ_domain_iff.2 h
  refine ⟨hQ, embeddingQ.J_injective 2 ?_⟩
  change J₂ (complexQ.d 1 2 u) = J₂ _
  have h1 : J₂ (complexQ.d 1 2 u) = Models.Torus.BGG.complex.d 1 2 ⟨J₁ u.1, hu⟩ := J_complexQ_d u
  rw [h1]
  refine prodLp.symm.injective (e.trans (Eq.trans ?_ (prodLp_symm_J₂ _).symm))
  have h2 := Mirror.J_complexQ_d (i := 1) (j := 2) ⟨u.1, hQ⟩
  exact congrArg (WithLp.toLp 2) (Prod.ext (extF_axialQ _).symm h2.symm)

/-! #### The constraint on `Q` -/

/-- The constraint on `Q`: the pull-back of `{0} × L²(TSD) × ({0} × L²(TSD))`. -/
abbrev tsdQ (i : Fin 3) : Submodule ℂ (SpaceQ i) :=
  (Models.Torus.BGG.constraint i).comap (J i : SpaceQ i →ₗ[ℂ] Models.Torus.BGG.Space i)

instance (i : Fin 3) : (tsdQ i).HasOrthogonalProjection :=
  embeddingQ.comap_hasOrthogonalProjection i _

theorem mem_tsdQ_zero {σ : RQ} : σ ∈ tsdQ 0 ↔ σ = 0 := by
  refine (Models.Torus.BGG.mem_constraint_zero_iff (u := J₀ σ)).trans
    ⟨fun h => extS_injective cU_sq (h.trans (_root_.map_zero _).symm),
    fun h => h ▸ _root_.map_zero _⟩

/-- The electric slot of the constraint is the electric constraint of the mirror complex of
Prop 4.17. -/
theorem mem_tsdQ_one {u : MQ} : u ∈ tsdQ 1 ↔ u ∈ Mirror.tsdQ 1 := Iff.rfl

/-- **The third slot of the constraint**: `(M, B) ∈ tsdQ 2` iff `M = 0` and `B` lies in the
magnetic constraint of the mirror complex of Prop 4.17. -/
theorem mem_tsdQ_two {w : W2Q} :
    w ∈ tsdQ 2 ↔ (WithLp.ofLp w).1 = 0 ∧ (WithLp.ofLp w).2 ∈ Mirror.tsdQ 2 := by
  refine (Models.Torus.BGG.mem_constraint_two_iff (ρ := J₂ w)).trans ?_
  have e : ∀ n, ((J₂ w : Lp VM 2 _) : (Fin 3 → ℤ) → VM) n =
      WithLp.toLp 2 ((extF (c := cPV) cPV_sq (WithLp.ofLp w).1 : (Fin 3 → ℤ) → Vec) n,
        (extF (c := cB) cB_sq (WithLp.ofLp w).2 : (Fin 3 → ℤ) → Mat) n) := fun n =>
    pairLp_coeff _ _ w n
  change (∀ n, (WithLp.ofLp (((J₂ w : Lp VM 2 _) : _ → VM) n)).1 = 0 ∧
    (WithLp.ofLp (((J₂ w : Lp VM 2 _) : _ → VM) n)).2 ∈ tsd (Fourier.Torus.freq n)) ↔ _
  simp only [e, WithLp.ofLp_toLp]
  rw [forall_and]
  refine and_congr ⟨fun h => injective_extF cPV_sq (Lp.ext_count fun n => ?_), fun h n => ?_⟩ ?_
  · rw [h n, _root_.map_zero, Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) n]; rfl
  · rw [h, _root_.map_zero, Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) n]; rfl
  · exact ⟨fun h => Operator.mem_fibreSub.2 (Measure.ae_count_iff.2 h),
      fun h => Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 h)⟩

/-- **The constraint on `Q`**: `σ = 0`, `u` in the electric constraint, `M = 0`, and `B` in the
magnetic constraint of the mirror complex of Prop 4.17. -/
theorem mem_tsdQ_iff {x : PiLp 2 SpaceQ} :
    x ∈ totalSub tsdQ ↔ (x 0 : RQ) = 0 ∧ (x 1 : MQ) ∈ Mirror.tsdQ 1 ∧
      (WithLp.ofLp (x 2 : W2Q)).1 = 0 ∧ (WithLp.ofLp (x 2 : W2Q)).2 ∈ Mirror.tsdQ 2 := by
  refine ⟨fun h => ⟨mem_tsdQ_zero.1 (h 0), h 1, mem_tsdQ_two.1 (h 2)⟩, ?_⟩
  rintro ⟨h0, h1, h2⟩ i
  fin_cases i
  · exact mem_tsdQ_zero.2 h0
  · exact h1
  · exact mem_tsdQ_two.2 h2

/-- **Constrained states consist of TSD fields**: in a state of the constraint, `σ = 0`, the
multiplier vanishes, and `u` and `B` are symmetric, trace-free and weakly divergence-free on `Q`.
See [QuennevilleBelair2015], Ch. 6 (corrected). -/
theorem tsd_of_mem_tsdQ {x : PiLp 2 SpaceQ} (hx : x ∈ totalSub tsdQ) :
    (x 0 : RQ) = 0 ∧ (WithLp.ofLp (x 2 : W2Q)).1 = 0 ∧
      ((∀ i j, (show MQ from x 1) (i, j) = (show MQ from x 1) (j, i)) ∧
        ∑ i, (show MQ from x 1) (i, i) = 0 ∧
        ∀ φ : Fin 3 → Feec.Models.BoundedDomain.R3 → ℂ,
          ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
            ⟪(x 1 : MQ), Domain.testField
              ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply hφ)⟫_ℂ = 0) ∧
      ((∀ i j, (WithLp.ofLp (x 2 : W2Q)).2 (i, j) = (WithLp.ofLp (x 2 : W2Q)).2 (j, i)) ∧
        ∑ i, (WithLp.ofLp (x 2 : W2Q)).2 (i, i) = 0 ∧
        ∀ φ : Fin 3 → Feec.Models.BoundedDomain.R3 → ℂ,
          ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
            ⟪(WithLp.ofLp (x 2 : W2Q)).2, Domain.testField
              ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply hφ)⟫_ℂ = 0) := by
  obtain ⟨h0, h1, h2, h3⟩ := mem_tsdQ_iff.1 hx
  exact ⟨h0, h2, Mirror.mem_tsdQ_one h1, Mirror.mem_tsdQ_two h3⟩

theorem exists_J_eq_starProjection (i : Fin 3) (x : SpaceQ i) :
    ∃ y, J i y = (Models.Torus.BGG.constraint i).starProjection (J i x) := by
  have hx : J i x ∈ action.fixed i := range_J i ▸ LinearMap.mem_range_self _ x
  have h := action.starProjection_mem_fixed (fun g y hy => act_mem_constraint g i hy) hx
  rw [← range_J] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy⟩

/-- **TSD reduces the BGG complex on `Q`.**
See [QuennevilleBelair2015], Ch. 6 (corrected). -/
theorem reducingSubcomplexQ : complexQ.ReducingSubcomplex tsdQ :=
  embeddingQ.reducingSubcomplex_comap Models.Torus.BGG.reducingSubcomplex
    exists_J_eq_starProjection

/-- **The Ch. 6 method on `Q` with mirror boundary conditions keeps TSD data TSD**: strong
solutions of the BGG Hodge wave equation with data and forcing in the constraint stay there, so
`σ ≡ 0`, `u` is TSD, the multiplier vanishes and `B` is TSD (`tsd_of_mem_tsdQ`).
See [QuennevilleBelair2015], Ch. 6 (corrected). -/
theorem propagatesQ {a b : ℝ} {F U : ℝ → PiLp 2 SpaceQ}
    (hU : Evolution.IsStrongSolution complexQ.wave (Icc a b) F U) (h0 : U a ∈ totalSub tsdQ)
    (hF : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) : ∀ t ∈ Icc a b, U t ∈ totalSub tsdQ :=
  reducingSubcomplexQ.propagates hU h0 hF

/-- The Ch. 6 system on `Q` with existence and uniqueness.
See [QuennevilleBelair2015], Ch. 6 (corrected). -/
theorem existsUnique_memQ {U₀ : PiLp 2 SpaceQ} (hU₀ : U₀ ∈ complexQ.wave.domain)
    (hU₀S : U₀ ∈ totalSub tsdQ) {F : ℝ → PiLp 2 SpaceQ} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complexQ.wave a b F)
    (hFS : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complexQ.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub tsdQ) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complexQ.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  reducingSubcomplexQ.existsUnique_mem hU₀ hU₀S hF hFS

/-- `K* = K` for the Ch. 6 system on `Q`.
See [QuennevilleBelair2015], Ch. 6 (corrected). -/
theorem invariantCore_eqQ : complexQ.waveGroup.invariantCore (totalSub tsdQ) = totalSub tsdQ :=
  reducingSubcomplexQ.invariantCore_eq

/-! #### A non-stationary datum on `Q` -/

/-- The datum `(0, E₀, (0, 0))`, `E₀ = (2 cos(2π x₃) diag(1, -1, 0))|_Q`. -/
def cosStateQ : PiLp 2 SpaceQ := WithLp.toLp 2 (Pi.single 1 cosEQ)

theorem cosStateQ_zero : cosStateQ 0 = 0 :=
  Pi.single_eq_of_ne (M := SpaceQ) (by decide : (0 : Fin 3) ≠ 1) cosEQ
theorem cosStateQ_one : cosStateQ 1 = cosEQ := Pi.single_eq_same (M := SpaceQ) (1 : Fin 3) cosEQ
theorem cosStateQ_two : cosStateQ 2 = 0 :=
  Pi.single_eq_of_ne (M := SpaceQ) (by decide : (2 : Fin 3) ≠ 1) cosEQ

theorem totalJ_cosStateQ : HilbertComplex.totalJ J cosStateQ = cosState := by
  refine PiLp.ext fun i => ?_
  rw [HilbertComplex.totalJ_apply]
  fin_cases i
  · change J 0 (cosStateQ 0) = cosState 0
    rw [cosStateQ_zero, _root_.map_zero, cosState_zero]
  · change J₁ (cosStateQ 1) = cosState 1
    rw [cosStateQ_one, cosState_one]
    exact J_cosEQ
  · change J 2 (cosStateQ 2) = cosState 2
    rw [cosStateQ_two, _root_.map_zero, cosState_two]

/-- **A non-stationary TSD datum for the Ch. 6 system on `Q`**.
See [QuennevilleBelair2015], Ch. 6 (corrected). -/
theorem exists_nonstationaryQ :
    ∃ y ∈ complexQ.wave.domain, y ∈ totalSub tsdQ ∧ y ∉ complexQ.waveGroup.stationary := by
  have hd : HilbertComplex.totalJ J cosStateQ ∈ Models.Torus.BGG.complex.wave.domain :=
    totalJ_cosStateQ ▸ cosState_mem_domain
  obtain ⟨h1, h2⟩ := HilbertComplex.not_mem_stationary_compress eight_pos inner_J
    reducingSubcomplex_range hd fun h0 =>
      wave_cosState_ne ((apply_congr' _ _ _ totalJ_cosStateQ.symm).trans h0)
  refine ⟨cosStateQ, h1, fun i => ?_, h2⟩
  change J i (cosStateQ i) ∈ Models.Torus.BGG.constraint i
  rw [← HilbertComplex.totalJ_apply, totalJ_cosStateQ]
  exact cosState_mem_constraint i

end Feec.Models.Cube.MirrorBGG
