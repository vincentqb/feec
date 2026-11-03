module

public import Feec.Models.Cube.Mirror
public import Feec.Models.Torus.SymCurl
public import Feec.Models.BoundedDomain.SymCurl

/-!
# The strong-symmetry complex (4.16) on the cube with mirror boundary conditions

The complex `H²(R) --grad grad--> H(curl, S) --curl--> L²(T)` of Thesis (4.16) on the torus
(`Feec.Models.Torus.SymCurl.complex`, Fourier side) carries the mirror symmetries of
`Feec.Models.Cube.Mirror`: `u` even, `S(R_k x) = D_k S(x) D_k`, `T(R_k x) = -D_k T(x) D_k`
(`MirrorSym.symmetries`). The TSD constraint `{0} × L²(TSD ∩ S) × L²(TSD ∩ T)` is invariant, so
it descends, by the same general mechanism as for `Feec.Models.Cube.Mirror`, to

* the **parity model** `MirrorSym.complex` (the fixed complex);
* the **cube `Q = (0, ½)³`** `MirrorSym.complexQ`: `L²(Q) → L²(Q; S) → L²(Q; T)` (the
  bounded-domain spaces `Feec.Models.BoundedDomain.symSub`, `trSub`), the compression of the torus
  complex along the mirror extensions (`∂_n u = 0`, `S_{nτ} = 0`); the constraint spaces consist
  of TSD fields (`mem_tsdQ_one`,
  `mem_tsdQ_two`, with the wall conditions `S_{τn} = 0`, `T_{nn} = 0`);
* **every open cube** `∏ (bᵢ, bᵢ + s)` (`MirrorSym.complexCube`), with the chain-rule factors
  `(2s)⁻²` on the Hessian and `(2s)⁻¹` on the curl.

This is Thesis Prop 4.19 with mirror boundary conditions; with the thesis' conditions it fails on
every bounded domain (`Feec.Counterexamples.BoundedSymTSD`).

## Main results

* **`MirrorSym.reducingSubcomplex`**, `MirrorSym.propagates`, `MirrorSym.existsUnique_mem`,
  `MirrorSym.invariantCore_eq`, `MirrorSym.exists_nonstationary`.
* **`MirrorSym.reducingSubcomplexQ`**, `MirrorSym.propagatesQ`, `MirrorSym.existsUnique_memQ`,
  `MirrorSym.invariantCore_eqQ`, `MirrorSym.exists_nonstationaryQ`,
  `MirrorSym.complexQ_d₁_eq`.
* **`MirrorSym.reducingSubcomplexCube`**, `MirrorSym.propagatesCube`,
  `MirrorSym.existsUnique_memCube`, `MirrorSym.invariantCore_eqCube`,
  `MirrorSym.exists_nonstationaryCube`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.11 (Prop 4.19, (4.16)–(4.18))
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021] (the complex (4.16))

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap MeasureTheory

@[expose] public noncomputable section

namespace Feec.Models.Cube.MirrorSym

open Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.SymCurl Feec.ShortHilbertComplex
open Feec.Models.Cube.MirrorExt
open Feec.Models.Cube.Mirror (cE cB cE_sq cB_sq conj_cE conj_cB curl_flip matR_mem_tsd)
open Feec.Models.Cube.MirrorTorus (sgn sgn_mul_self freq_flipAt)
open Feec.Fourier.Torus (flipAt flipAt_comm)
open Feec.HilbertComplex (ScaledEmbedding totalSub ReducingSubcomplex)

/-! ### The mirror symmetries of the torus complex (4.16) -/

/-- `S ↪ ℂ³ˣ³`. -/
def symι : Sym →ₗᵢ[ℂ] Mat := symSub.subtypeₗᵢ

/-- `T ↪ ℂ³ˣ³`. -/
def trι : Tr →ₗᵢ[ℂ] Mat := trSub.subtypeₗᵢ

@[simp] theorem symι_apply (M : Sym) : symι M = (M : Mat) := rfl

theorem range_symι : LinearMap.range symι.toLinearMap = symSub := Submodule.range_subtype _
theorem range_trι : LinearMap.range trι.toLinearMap = trSub := Submodule.range_subtype _

theorem sgnCLM_cE_mem_symSub (k : Fin 3) {M : Mat} (hM : M ∈ symSub) :
    sgnCLM (Fin 3 × Fin 3) (fun p => cE p k) M ∈ symSub := fun a b => by
  rw [sgnCLM_apply, sgnCLM_apply, hM a b]; simp only [cE]; ring

theorem sgnCLM_cB_mem_trSub (k : Fin 3) {M : Mat} (hM : M ∈ trSub) :
    sgnCLM (Fin 3 × Fin 3) (fun p => cB p k) M ∈ trSub := by
  change ∑ a, _ = 0
  simp only [sgnCLM_apply, cB, sgn_mul_self, neg_mul, one_mul, Finset.sum_neg_distrib]
  rw [show ∑ a, M (a, a) = 0 from hM, neg_zero]

/-- `S ↦ D_k S D_k` on symmetric matrices. -/
def symR (k : Fin 3) : SymCurl.Sym →L[ℂ] SymCurl.Sym :=
  (sgnCLM (Fin 3 × Fin 3) (fun p => cE p k) ∘L symSub.subtypeL).codRestrict symSub fun M =>
    sgnCLM_cE_mem_symSub k M.2

/-- `T ↦ -D_k T D_k` on trace-free matrices. -/
def trR (k : Fin 3) : SymCurl.Tr →L[ℂ] SymCurl.Tr :=
  (sgnCLM (Fin 3 × Fin 3) (fun p => cB p k) ∘L trSub.subtypeL).codRestrict trSub fun M =>
    sgnCLM_cB_mem_trSub k M.2

@[simp] theorem coe_symR (k : Fin 3) (M : SymCurl.Sym) :
    (symR k M : Mat) = sgnCLM (Fin 3 × Fin 3) (fun p => cE p k) M := rfl

theorem symR_symR (k : Fin 3) (M : SymCurl.Sym) : symR k (symR k M) = M :=
  SymCurl.Sym.ext (sgnCLM_sgnCLM (fun p => cE_sq p k) (M : Mat))

theorem trR_trR (k : Fin 3) (M : SymCurl.Tr) : trR k (trR k M) = M :=
  SymCurl.Tr.ext (sgnCLM_sgnCLM (fun p => cB_sq p k) (M : Mat))

theorem inner_symR (k : Fin 3) (M N : SymCurl.Sym) : ⟪symR k M, symR k N⟫_ℂ = ⟪M, N⟫_ℂ :=
  (SymCurl.Sym.inner_val _ _).trans
    ((inner_sgnCLM (fun p => cE_sq p k) (fun p => conj_cE p k) (M : Mat) (N : Mat)).trans
      (SymCurl.Sym.inner_val _ _).symm)

theorem inner_trR (k : Fin 3) (M N : SymCurl.Tr) : ⟪trR k M, trR k N⟫_ℂ = ⟪M, N⟫_ℂ :=
  (SymCurl.Tr.inner_val _ _).trans
    ((inner_sgnCLM (fun p => cB_sq p k) (fun p => conj_cB p k) (M : Mat) (N : Mat)).trans
      (SymCurl.Tr.inner_val _ _).symm)

theorem symR_comm (k l : Fin 3) (M : SymCurl.Sym) : symR k (symR l M) = symR l (symR k M) :=
  SymCurl.Sym.ext (sgnCLM_comm _ _ (M : Mat))

theorem trR_comm (k l : Fin 3) (M : SymCurl.Tr) : trR k (trR l M) = trR l (trR k M) :=
  SymCurl.Tr.ext (sgnCLM_comm _ _ (M : Mat))

/-- The parity `+1` of the even scalar `u` in every variable (`∂_n u = 0`). -/
def cU : Fin 3 → ℂ := fun _ => 1

theorem cU_sq (k : Fin 3) : cU k * cU k = 1 := by simp [cU]

/-- The fibre maps of the `k`-th reflection on the three spaces. -/
def fib (k : Fin 3) : ∀ i : Fin 3, W3 ℂ SymCurl.Sym SymCurl.Tr i →L[ℂ] W3 ℂ SymCurl.Sym SymCurl.Tr i
  | 0 => ContinuousLinearMap.id ℂ ℂ
  | 1 => symR k
  | 2 => trR k

theorem hess_flip (k : Fin 3) (n : Fin 3 → ℤ) (c : ℂ) :
    hess (Fourier.Torus.freq (flipAt k n)) c = symR k (hess (Fourier.Torus.freq n) c) := by
  refine SymCurl.Sym.ext (PiLp.ext fun p => ?_)
  obtain ⟨a, b⟩ := p
  rw [coe_hess, coe_symR, sgnCLM_apply, coe_hess, hessM_apply, hessM_apply,
    freq_flipAt, freq_flipAt]
  simp only [cE]; ring

theorem curlS_flip (k : Fin 3) (n : Fin 3 → ℤ) (M : SymCurl.Sym) :
    curlS (Fourier.Torus.freq (flipAt k n)) (symR k M) =
      trR k (curlS (Fourier.Torus.freq n) M) :=
  SymCurl.Tr.ext (curl_flip k n (M : Mat))

/-- **The mirror reflections of the torus complex (4.16)**, as fibre symmetries. -/
def symmetries : (Fourier.Torus.symbolComplex symCurl).Symmetries (Fin 3) where
  R := flipRefl
  ρ := fib
  invol k i v := by
    fin_cases i
    · rfl
    · exact symR_symR k v
    · exact trR_trR k v
  inner_ρ k i v w := by
    fin_cases i
    · rfl
    · exact inner_symR k v w
    · exact inner_trR k v w
  symm k i j n v := by
    change symCurl.m i j (Fourier.Torus.freq (flipAt k n)) (fib k i v) =
      fib k j (symCurl.m i j _ v)
    fin_cases i <;> fin_cases j
    all_goals first
      | (change (0 : _ →L[ℂ] _) _ = fib k _ ((0 : _ →L[ℂ] _) v); simp)
      | exact hess_flip k n v
      | exact curlS_flip k n v
  comm_σ k l n := flipAt_comm k l n
  comm_ρ k l i v := by
    fin_cases i
    · rfl
    · exact symR_comm k l v
    · exact trR_comm k l v

/-- **The mirror action of `(ℤ/2)³`** on the torus complex (4.16). -/
abbrev action : Models.Torus.SymCurl.complex.Action (Multiplicative (Fin 3 → ZMod 2)) :=
  symmetries.toAction

/-- **The mirror cube complex (4.16)** (parity model). -/
abbrev complex := action.fixedComplex

theorem mem_fixed_iff {i : Fin 3} {x : Models.Torus.SymCurl.Space i} :
    x ∈ action.fixed i ↔ ∀ k, symLp (symmetries.R k) (fib k i) x = x :=
  symmetries.mem_fixed_toAction

theorem mem_fixed_zero {u : Models.Torus.SymCurl.Space 0} :
    u ∈ action.fixed 0 ↔ u ∈ scalarParity (Fin 3) cU := by
  have h := mem_scalarParity_iff_symLp (d := Fin 3) cU_sq
    (u := (u : Lp ℂ 2 (Measure.count : Measure (Fin 3 → ℤ))))
  simp only [cU, one_smul] at h
  exact mem_fixed_iff.trans h.symm

theorem symLp_symR_iff (k : Fin 3) (u : Lp SymCurl.Sym 2 (Measure.count : Measure (Fin 3 → ℤ))) :
    symLp (flipRefl k) (symR k) u = u ↔
      symLp (flipRefl k) (sgnCLM (Fin 3 × Fin 3) fun p => cE p k) (liftLp symι u) =
        liftLp symι u := by
  rw [← liftLp_symLp symι (flipRefl k) (ρ := symR k) (fun v => rfl)]
  exact (liftLp symι).injective.eq_iff.symm

theorem symLp_trR_iff (k : Fin 3) (u : Lp SymCurl.Tr 2 (Measure.count : Measure (Fin 3 → ℤ))) :
    symLp (flipRefl k) (trR k) u = u ↔
      symLp (flipRefl k) (sgnCLM (Fin 3 × Fin 3) fun p => cB p k) (liftLp trι u) =
        liftLp trι u := by
  rw [← liftLp_symLp trι (flipRefl k) (ρ := trR k) (fun v => rfl)]
  exact (liftLp trι).injective.eq_iff.symm

theorem mem_fixed_one {u : Models.Torus.SymCurl.Space 1} :
    u ∈ action.fixed 1 ↔ liftLp symι u ∈ fieldParity cE :=
  mem_fixed_iff.trans ((forall_congr' fun k => symLp_symR_iff k u).trans
    (mem_fieldParity_iff_symLp cE_sq).symm)

theorem mem_fixed_two {u : Models.Torus.SymCurl.Space 2} :
    u ∈ action.fixed 2 ↔ liftLp trι u ∈ fieldParity cB :=
  mem_fixed_iff.trans ((forall_congr' fun k => symLp_trR_iff k u).trans
    (mem_fieldParity_iff_symLp cB_sq).symm)

theorem fib_mem_tsdK (k i : Fin 3) (n : Fin 3 → ℤ) {v : W3 ℂ Sym Tr i}
    (hv : v ∈ SymCurl.tsdK i (Fourier.Torus.freq (flipAt k n))) :
    fib k i v ∈ SymCurl.tsdK i (Fourier.Torus.freq n) := by
  fin_cases i
  · have h0 : (v : ℂ) = 0 := (Submodule.mem_bot ℂ).1 hv
    exact (Submodule.mem_bot ℂ).2 h0
  · exact matR_mem_tsd k n (s := fun p => cE p k) (fun p => by simp only [cE]; ring)
      (fun a => by simp only [cE, sgn_mul_self]) (fun p => by simp only [cE, sgn_mul_self]; ring) hv
  · exact matR_mem_tsd k n (s := fun p => cB p k) (fun p => by simp only [cB]; ring)
      (fun a => by simp only [cB, sgn_mul_self]) (fun p => by simp only [cB, sgn_mul_self]; ring) hv

theorem act_mem_constraint (g : Multiplicative (Fin 3 → ZMod 2)) (i : Fin 3)
    {x : Models.Torus.SymCurl.Space i} (hx : x ∈ Models.Torus.SymCurl.constraint i) :
    action.act g i x ∈ Models.Torus.SymCurl.constraint i :=
  symmetries.act_mem_fibreSub (K := fun i n => SymCurl.tsdK i (Fourier.Torus.freq n))
    (fun k i n _ hv => fib_mem_tsdK k i n hv) g i hx

/-- The TSD constraint of the mirror cube complex (4.16). -/
abbrev constraint (i : Fin 3) : Submodule ℂ (action.fixed i) :=
  (Models.Torus.SymCurl.constraint i).comap (action.fixed i).subtype

/-- **The TSD constraint reduces the mirror cube complex (4.16).**
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  action.reducingSubcomplex_comap_fixed Models.Torus.SymCurl.reducingSubcomplex act_mem_constraint

/-- **Prop 4.19 on the cube with mirror boundary conditions** (parity model).
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem propagates {a b : ℝ} {F U : ℝ → PiLp 2 fun i => action.fixed i}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ totalSub constraint) (hF : ∀ t ∈ Icc a b, F t ∈ totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ totalSub constraint :=
  reducingSubcomplex.propagates hU h0 hF

/-- Prop 4.19 on the mirror cube with existence and uniqueness (parity model).
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem existsUnique_mem {U₀ : PiLp 2 fun i => action.fixed i} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀K : U₀ ∈ totalSub constraint) {F : ℝ → PiLp 2 fun i => action.fixed i} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFK : ∀ t ∈ Icc a b, F t ∈ totalSub constraint) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub constraint) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  reducingSubcomplex.existsUnique_mem hU₀ hU₀K hF hFK

/-- `K* = K` on the mirror cube (4.16) (parity model).
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem invariantCore_eq :
    complex.waveGroup.invariantCore (totalSub constraint) = totalSub constraint :=
  reducingSubcomplex.invariantCore_eq

/-! ### A non-stationary TSD datum -/

open Feec.Models.Cube.Mirror (k0 M0 M0_apply cosCoeff cosCoeff_eq_zero cosE coe_cosE
  cosE_mem_fieldParity M0_mem_tsd curl_M0_ne)

theorem cosCoeff_mem_symSub (n : Fin 3 → ℤ) : cosCoeff n ∈ symSub := fun a b => by
  unfold cosCoeff
  split_ifs
  · simp only [M0_apply]; split_ifs <;> simp_all
  · rfl

/-- The coefficients of `E₀ = 2 cos(2π x₃) diag(1, -1, 0)` as symmetric matrices. -/
def cosSCoeff (n : Fin 3 → ℤ) : SymCurl.Sym := SymCurl.Sym.mk (cosCoeff n) (cosCoeff_mem_symSub n)

theorem memLp_cosSCoeff : MemLp cosSCoeff 2 (Measure.count : Measure (Fin 3 → ℤ)) :=
  memLp_count_of_finite {k0, -k0} fun _ hn => SymCurl.Sym.ext (cosCoeff_eq_zero hn)

/-- **The electric datum** `E₀ = 2 cos(2π x₃) diag(1, -1, 0)` in `L²(𝕋³; S)` (Fourier side). -/
def cosS : Lp SymCurl.Sym 2 (Measure.count : Measure (Fin 3 → ℤ)) := memLp_cosSCoeff.toLp _

theorem coe_cosS (n : Fin 3 → ℤ) :
    ((cosS : (Fin 3 → ℤ) → SymCurl.Sym) n : Mat) = cosCoeff n := by
  rw [cosS, MemLp.coeFn_toLp_count]; rfl

theorem liftLp_cosS : liftLp symι cosS = cosE :=
  Lp.ext_count fun n => by rw [liftLp_apply, symι_apply, coe_cosS, coe_cosE]

theorem cosS_mem_fixed : cosS ∈ action.fixed 1 :=
  mem_fixed_one.2 (liftLp_cosS ▸ cosE_mem_fieldParity)

theorem cosS_mem_constraint : cosS ∈ Models.Torus.SymCurl.constraint 1 := by
  refine Operator.mem_fibreSub.2 (Measure.ae_count_iff.2 fun n => ?_)
  change (((cosS : (Fin 3 → ℤ) → SymCurl.Sym) n : SymCurl.Sym) : Mat) ∈ tsd (Fourier.Torus.freq n)
  rw [coe_cosS]
  unfold cosCoeff
  split_ifs with h
  · exact M0_mem_tsd h
  · exact Submodule.zero_mem _

theorem cosS_eq_zero {n : Fin 3 → ℤ} (hn : n ∉ ({k0, -k0} : Finset (Fin 3 → ℤ))) :
    (cosS : (Fin 3 → ℤ) → SymCurl.Sym) n = 0 :=
  SymCurl.Sym.ext ((coe_cosS n).trans (cosCoeff_eq_zero hn))

theorem cosS_mem_domain : cosS ∈ (Models.Torus.SymCurl.complex.d 1 2).domain :=
  mem_mulDomain_of_finite _ {k0, -k0} fun _ hn => cosS_eq_zero hn

theorem cosS_mem_adjoint_domain : cosS ∈ ((Models.Torus.SymCurl.complex.d 0 1)†).domain := by
  rw [Models.Torus.SymCurl.adjoint_d 0 1]
  exact mem_mulDomain_of_finite _ {k0, -k0} fun _ hn => cosS_eq_zero hn

/-- The datum `(0, E₀, 0)` of (4.18) on the torus. -/
def cosState : PiLp 2 Models.Torus.SymCurl.Space := WithLp.toLp 2 (Pi.single 1 cosS)

theorem cosState_zero : cosState 0 = 0 :=
  Pi.single_eq_of_ne (M := Models.Torus.SymCurl.Space) (by decide : (0 : Fin 3) ≠ 1) cosS
theorem cosState_one : cosState 1 = cosS :=
  Pi.single_eq_same (M := Models.Torus.SymCurl.Space) (1 : Fin 3) cosS
theorem cosState_two : cosState 2 = 0 :=
  Pi.single_eq_of_ne (M := Models.Torus.SymCurl.Space) (by decide : (2 : Fin 3) ≠ 1) cosS

theorem cosState_mem_domain : cosState ∈ Models.Torus.SymCurl.complex.wave.domain :=
  HilbertComplex.mem_wave_domain_fin3 _
    (by rw [cosState_zero]; exact Submodule.zero_mem _)
    (by rw [cosState_one]; exact cosS_mem_domain)
    (by rw [cosState_one]; exact cosS_mem_adjoint_domain)
    (by rw [cosState_two]; exact Submodule.zero_mem _)

theorem curlS_cosS_apply :
    SymCurl.Tr.val ((Models.Torus.SymCurl.complex.d 1 2 ⟨cosS, cosS_mem_domain⟩ :
      Lp SymCurl.Tr 2 (Measure.count : Measure (Fin 3 → ℤ))) k0) =
        curl (Fourier.Torus.freq k0) M0 := by
  have h := Operator.coeFn_mulOp_count (fun n => symCurl.m 1 2 (Fourier.Torus.freq n))
    ⟨cosS, cosS_mem_domain⟩ k0
  refine (congrArg SymCurl.Tr.val h).trans ?_
  change curl (Fourier.Torus.freq k0) (SymCurl.Sym.val ((cosS : (Fin 3 → ℤ) → SymCurl.Sym) k0)) = _
  rw [show SymCurl.Sym.val ((cosS : (Fin 3 → ℤ) → SymCurl.Sym) k0) = cosCoeff k0 from coe_cosS k0]
  simp [cosCoeff]

theorem curlS_cosS_ne : Models.Torus.SymCurl.complex.d 1 2 ⟨cosS, cosS_mem_domain⟩ ≠ 0 := by
  intro h
  apply curl_M0_ne
  rw [← curlS_cosS_apply, h]
  rw [Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) k0]
  rfl

theorem wave_cosState_ne :
    Models.Torus.SymCurl.complex.wave ⟨cosState, cosState_mem_domain⟩ ≠ 0 := by
  intro h
  have h2 := congrArg (fun y : PiLp 2 Models.Torus.SymCurl.Space => y 2) h
  rw [HilbertComplex.wave_apply_fin3_two] at h2
  exact curlS_cosS_ne ((apply_congr' _ _ _ cosState_one.symm).trans h2)

theorem cosState_mem_fixed (i : Fin 3) : cosState i ∈ action.fixed i := by
  fin_cases i
  · change cosState 0 ∈ _; rw [cosState_zero]; exact Submodule.zero_mem _
  · change cosState 1 ∈ _; rw [cosState_one]; exact cosS_mem_fixed
  · change cosState 2 ∈ _; rw [cosState_two]; exact Submodule.zero_mem _

theorem cosState_mem_constraint (i : Fin 3) :
    cosState i ∈ Models.Torus.SymCurl.constraint i := by
  fin_cases i
  · change cosState 0 ∈ _; rw [cosState_zero]; exact Submodule.zero_mem _
  · change cosState 1 ∈ _; rw [cosState_one]; exact cosS_mem_constraint
  · change cosState 2 ∈ _; rw [cosState_two]; exact Submodule.zero_mem _

/-- **A non-stationary TSD datum on the mirror cube (4.16)** (parity model).
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem exists_nonstationary :
    ∃ y ∈ complex.wave.domain, y ∈ totalSub constraint ∧ y ∉ complex.waveGroup.stationary := by
  obtain ⟨h1, h2⟩ := action.reducingSubcomplex_fixed.not_mem_stationary
    (y := WithLp.toLp 2 fun i => ⟨cosState i, cosState_mem_fixed i⟩) cosState_mem_domain
    wave_cosState_ne
  exact ⟨_, h1, fun i => cosState_mem_constraint i, h2⟩

/-! ### The cube `Q = (0, ½)³` -/

open Geometry (Q)
open UnitAddTorus (mFourierCoeff)
open Feec.Models.Cube.Mirror (MQ VQ cE_eq_update cB_eq_update cPV_sq extL2_congr tsd_of_extF_mem
  eight_pos two_pow_card cosEQ J_cosEQ)

/-- `L²(Q)`. -/
abbrev RQ : Type := Domain.L2 ℂ (Q (Fin 3))

/-- `L²(Q; S)`. -/
abbrev SQ : Type := Models.BoundedDomain.symSub ℂ (Q (Fin 3))

/-- `L²(Q; T)`. -/
abbrev TQ : Type := Models.BoundedDomain.trSub ℂ (Q (Fin 3))

/-- The spaces `L²(Q)`, `L²(Q; S)`, `L²(Q; T)` of the mirror complex (4.16) on `Q`. -/
abbrev SpaceQ (i : Fin 3) : Type := W3 RQ SQ TQ i

theorem extF_cE_mem_symSub (x : SQ) (n : Fin 3 → ℤ) :
    (extF cE_sq (x : MQ) : (Fin 3 → ℤ) → Mat) n ∈ LinearMap.range symι.toLinearMap := by
  rw [range_symι]
  intro a b
  rw [extF_coeff, extF_coeff, Models.BoundedDomain.mem_symSub.1 x.2 a b,
    extL2_congr (show cE (a, b) = cE (b, a) from funext fun k => by simp only [cE]; ring)
      (cE_sq (a, b)) (cE_sq (b, a))]

theorem extF_cB_mem_trSub (x : TQ) (n : Fin 3 → ℤ) :
    (extF cB_sq (x : MQ) : (Fin 3 → ℤ) → Mat) n ∈ LinearMap.range trι.toLinearMap := by
  rw [range_trι]
  have hc0 : ∀ j, cB (0, 0) j * cB (0, 0) j = 1 := cB_sq (0, 0)
  change ∑ a, _ = 0
  have e : ∀ a, (extF cB_sq (x : MQ) : (Fin 3 → ℤ) → Mat) n (a, a) =
      coeffCLM n (extL2 hc0 ((x : MQ) (a, a))) := fun a => by
    rw [extF_coeff, coeffCLM_apply, extL2_congr (show cB (a, a) = cB (0, 0) from
      funext fun k => by simp only [cB, sgn_mul_self]) (cB_sq (a, a)) hc0]
  simp only [e]
  rw [← map_sum, ← map_sum, show ∑ a, (x : MQ) (a, a) = 0 from
    Models.BoundedDomain.mem_trSub.1 x.2, _root_.map_zero, _root_.map_zero]

/-- The mirror extension of even scalars, `L²(Q) → ℓ²(ℤ³)`. -/
abbrev J₀ : RQ →L[ℂ] Lp ℂ 2 (Measure.count : Measure (Fin 3 → ℤ)) := extS (d := Fin 3) cU_sq

/-- The mirror extension of symmetric tensors, `L²(Q; S) → ℓ²(ℤ³; S)`. -/
def J₁ : SQ →L[ℂ] Lp SymCurl.Sym 2 (Measure.count : Measure (Fin 3 → ℤ)) :=
  corestrictLp symι ((extF cE_sq).comp (Models.BoundedDomain.symSub ℂ (Q (Fin 3))).subtypeL)
    extF_cE_mem_symSub

/-- The mirror extension of trace-free pseudo-tensors, `L²(Q; T) → ℓ²(ℤ³; T)`. -/
def J₂ : TQ →L[ℂ] Lp SymCurl.Tr 2 (Measure.count : Measure (Fin 3 → ℤ)) :=
  corestrictLp trι ((extF cB_sq).comp (Models.BoundedDomain.trSub ℂ (Q (Fin 3))).subtypeL)
    extF_cB_mem_trSub

/-- **The mirror extensions** `L²(Q) → ℓ²(ℤ³)`, `L²(Q; S) → ℓ²(ℤ³; S)`, `L²(Q; T) → ℓ²(ℤ³; T)`:
`u` even in every variable, `S` with the tensor parities, `T` with the pseudo-tensor parities. -/
def J : ∀ i : Fin 3, SpaceQ i →L[ℂ] Models.Torus.SymCurl.Space i
  | 0 => J₀
  | 1 => J₁
  | 2 => J₂

theorem liftLp_J₁ (x : SQ) : liftLp symι (J₁ x) = extF cE_sq (x : MQ) :=
  liftLp_corestrictLp symι _ extF_cE_mem_symSub x

theorem liftLp_J₂ (x : TQ) : liftLp trι (J₂ x) = extF cB_sq (x : MQ) :=
  liftLp_corestrictLp trι _ extF_cB_mem_trSub x

theorem inner_J (i : Fin 3) (x y : SpaceQ i) :
    ⟪J i x, J i y⟫_ℂ = ((8 : ℝ) : ℂ) * ⟪x, y⟫_ℂ := by
  fin_cases i
  · exact (inner_extS cU_sq x y).trans (by rw [two_pow_card]; rfl)
  · exact (inner_corestrictLp symι _ extF_cE_mem_symSub x y).trans
      ((inner_extF cE_sq _ _).trans (by rw [two_pow_card]; rfl))
  · exact (inner_corestrictLp trι _ extF_cB_mem_trSub x y).trans
      ((inner_extF cB_sq _ _).trans (by rw [two_pow_card]; rfl))

theorem mem_range_J₁ (u : Lp SymCurl.Sym 2 (Measure.count : Measure (Fin 3 → ℤ))) :
    u ∈ LinearMap.range (J₁ : SQ →ₗ[ℂ] _) ↔ liftLp symι u ∈ fieldParity cE := by
  constructor
  · rintro ⟨x, rfl⟩
    change liftLp symι (J₁ x) ∈ _
    rw [liftLp_J₁]
    exact extF_mem cE_sq _
  · intro hw
    set f := (Fourier.Torus.fieldFourier (Fin 3) (Fin 3 × Fin 3)).symm (liftLp symι u)
    have hsym : Geometry.resQF f ∈ Models.BoundedDomain.symSub ℂ (Q (Fin 3)) := fun a b => by
      rw [Geometry.resQF_apply, Geometry.resQF_apply]
      congr 1
      refine TorusWeak.eq_of_mFourierCoeff_eq fun n => ?_
      rw [coeff_fieldFourier_symm, coeff_fieldFourier_symm, liftLp_apply]
      exact SymCurl.Sym.val_mem _ a b
    refine ⟨⟨_, hsym⟩, (liftLp symι).injective ?_⟩
    change liftLp symι (J₁ ⟨_, hsym⟩) = liftLp symι u
    rw [liftLp_J₁]
    exact extF_resQF cE_sq hw

theorem mem_range_J₂ (u : Lp SymCurl.Tr 2 (Measure.count : Measure (Fin 3 → ℤ))) :
    u ∈ LinearMap.range (J₂ : TQ →ₗ[ℂ] _) ↔ liftLp trι u ∈ fieldParity cB := by
  constructor
  · rintro ⟨x, rfl⟩
    change liftLp trι (J₂ x) ∈ _
    rw [liftLp_J₂]
    exact extF_mem cB_sq _
  · intro hw
    set f := (Fourier.Torus.fieldFourier (Fin 3) (Fin 3 × Fin 3)).symm (liftLp trι u)
    have htr : Geometry.resQF f ∈ Models.BoundedDomain.trSub ℂ (Q (Fin 3)) := by
      change ∑ a, Geometry.resQF f (a, a) = 0
      simp only [Geometry.resQF_apply]
      rw [← map_sum]
      have h0 : ∑ a, f (a, a) = 0 := by
        refine TorusWeak.eq_of_mFourierCoeff_eq fun n => ?_
        rw [← coeffCLM_apply, map_sum, ← coeffCLM_apply, (coeffCLM n).map_zero]
        simp only [coeffCLM_apply]
        simp only [f, coeff_fieldFourier_symm, liftLp_apply]
        exact SymCurl.Tr.val_mem _
      rw [h0, _root_.map_zero]
    refine ⟨⟨_, htr⟩, (liftLp trι).injective ?_⟩
    change liftLp trι (J₂ ⟨_, htr⟩) = liftLp trι u
    rw [liftLp_J₂]
    exact extF_resQF cB_sq hw

theorem range_J (i : Fin 3) :
    LinearMap.range (J i : SpaceQ i →ₗ[ℂ] Models.Torus.SymCurl.Space i) = action.fixed i := by
  ext u
  fin_cases i
  · exact (Iff.of_eq (congrArg (u ∈ ·) (range_extS cU_sq))).trans mem_fixed_zero.symm
  · exact (mem_range_J₁ u).trans mem_fixed_one.symm
  · exact (mem_range_J₂ u).trans mem_fixed_two.symm

instance (i : Fin 3) : (LinearMap.range
    (J i : SpaceQ i →ₗ[ℂ] Models.Torus.SymCurl.Space i)).HasOrthogonalProjection := by
  rw [range_J]; infer_instance

theorem reducingSubcomplex_range :
    Models.Torus.SymCurl.complex.ReducingSubcomplex fun i =>
      LinearMap.range (J i : SpaceQ i →ₗ[ℂ] Models.Torus.SymCurl.Space i) := by
  convert action.reducingSubcomplex_fixed using 1
  exact funext range_J

/-- **The mirror complex (4.16) of genuine fields on `Q`**:
`L²(Q) --grad grad--> L²(Q; S) --curl--> L²(Q; T)` with `∂_n u = 0` and `S_{nτ} = 0`, the
compression of the torus complex along the mirror extensions. -/
abbrev complexQ : HilbertComplex ℂ ComplexShape.fin3 SpaceQ :=
  Models.Torus.SymCurl.complex.compress J eight_pos inner_J reducingSubcomplex_range

/-- The mirror extensions embed the cube complex in the torus complex (scale `8`). -/
def embeddingQ : ScaledEmbedding complexQ Models.Torus.SymCurl.complex :=
  ScaledEmbedding.ofCompress eight_pos inner_J reducingSubcomplex_range

theorem J_complexQ_d {i j : Fin 3} (x : (complexQ.d i j).domain) :
    J j (complexQ.d i j x) = Models.Torus.SymCurl.complex.d i j
      ⟨J i x, (HilbertComplex.mem_compress_domain_iff eight_pos inner_J _).1 x.2⟩ :=
  HilbertComplex.J_compress_d eight_pos inner_J reducingSubcomplex_range x

theorem mem_complexQ_domain_iff {i j : Fin 3} {x : SpaceQ i} :
    x ∈ (complexQ.d i j).domain ↔ J i x ∈ (Models.Torus.SymCurl.complex.d i j).domain :=
  HilbertComplex.mem_compress_domain_iff eight_pos inner_J reducingSubcomplex_range

/-- The constraint on `Q`: the pull-back of `{0} × L²(TSD ∩ S) × L²(TSD ∩ T)`. -/
abbrev tsdQ (i : Fin 3) : Submodule ℂ (SpaceQ i) :=
  (Models.Torus.SymCurl.constraint i).comap (J i : SpaceQ i →ₗ[ℂ] Models.Torus.SymCurl.Space i)

instance (i : Fin 3) : (tsdQ i).HasOrthogonalProjection :=
  embeddingQ.comap_hasOrthogonalProjection i _

theorem exists_J_eq_starProjection (i : Fin 3) (x : SpaceQ i) :
    ∃ y, J i y = (Models.Torus.SymCurl.constraint i).starProjection (J i x) := by
  have hx : J i x ∈ action.fixed i := range_J i ▸ LinearMap.mem_range_self _ x
  have h := action.starProjection_mem_fixed (fun g y hy => act_mem_constraint g i hy) hx
  rw [← range_J] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy⟩

/-- **TSD reduces the mirror complex (4.16) on `Q`.**
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem reducingSubcomplexQ : complexQ.ReducingSubcomplex tsdQ :=
  embeddingQ.reducingSubcomplex_comap Models.Torus.SymCurl.reducingSubcomplex
    exists_J_eq_starProjection

/-- **Prop 4.19 on `Q` with mirror boundary conditions.**
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem propagatesQ {a b : ℝ} {F U : ℝ → PiLp 2 SpaceQ}
    (hU : Evolution.IsStrongSolution complexQ.wave (Icc a b) F U) (h0 : U a ∈ totalSub tsdQ)
    (hF : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) : ∀ t ∈ Icc a b, U t ∈ totalSub tsdQ :=
  reducingSubcomplexQ.propagates hU h0 hF

/-- Prop 4.19 on `Q` with existence and uniqueness.
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem existsUnique_memQ {U₀ : PiLp 2 SpaceQ} (hU₀ : U₀ ∈ complexQ.wave.domain)
    (hU₀S : U₀ ∈ totalSub tsdQ) {F : ℝ → PiLp 2 SpaceQ} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complexQ.wave a b F)
    (hFS : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complexQ.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub tsdQ) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complexQ.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  reducingSubcomplexQ.existsUnique_mem hU₀ hU₀S hF hFS

/-- `K* = K` on `Q` for (4.16).
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem invariantCore_eqQ : complexQ.waveGroup.invariantCore (totalSub tsdQ) = totalSub tsdQ :=
  reducingSubcomplexQ.invariantCore_eq

/-- **The constraint on `Q` consists of TSD fields** (symmetric, trace-free, weakly
divergence-free), for `S`. -/
theorem mem_tsdQ_one {S : SQ} (hS : S ∈ tsdQ 1) :
    (∀ i j, (S : MQ) (i, j) = (S : MQ) (j, i)) ∧ ∑ i, (S : MQ) (i, i) = 0 ∧
      ∀ φ : Fin 3 → Feec.Models.BoundedDomain.R3 → ℂ, ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
        ⟪(S : MQ), Domain.testField
          ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply hφ)⟫_ℂ = 0 := by
  have hS' : J₁ S ∈ Models.Torus.SymCurl.constraint 1 := hS
  have hE : extF cE_sq (S : MQ) ∈ Models.Torus.GradCurl.constraint 1 := by
    rw [← liftLp_J₁]
    refine Operator.mem_fibreSub.2 (Measure.ae_count_iff.2 fun n => ?_)
    change ((liftLp symι (J₁ S) : Lp Mat 2 Measure.count) : (Fin 3 → ℤ) → Mat) n ∈
      tsd (Fourier.Torus.freq n)
    rw [liftLp_apply]
    exact Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 hS') n
  exact tsd_of_extF_mem Mirror.cV_sq cE_sq (fun a b => funext fun k => by simp only [cE]; ring)
    (fun a => funext fun k => by simp only [cE, sgn_mul_self]) cE_eq_update hE

/-- **The constraint on `Q` consists of TSD fields**, for `T`. -/
theorem mem_tsdQ_two {T : TQ} (hT : T ∈ tsdQ 2) :
    (∀ i j, (T : MQ) (i, j) = (T : MQ) (j, i)) ∧ ∑ i, (T : MQ) (i, i) = 0 ∧
      ∀ φ : Fin 3 → Feec.Models.BoundedDomain.R3 → ℂ, ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
        ⟪(T : MQ), Domain.testField
          ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply hφ)⟫_ℂ = 0 := by
  have hT' : J₂ T ∈ Models.Torus.SymCurl.constraint 2 := hT
  have hE : extF cB_sq (T : MQ) ∈ Models.Torus.GradCurl.constraint 1 := by
    rw [← liftLp_J₂]
    refine Operator.mem_fibreSub.2 (Measure.ae_count_iff.2 fun n => ?_)
    change ((liftLp trι (J₂ T) : Lp Mat 2 Measure.count) : (Fin 3 → ℤ) → Mat) n ∈
      tsd (Fourier.Torus.freq n)
    rw [liftLp_apply]
    exact Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 hT') n
  exact tsd_of_extF_mem cPV_sq cB_sq (fun a b => funext fun k => by simp only [cB]; ring)
    (fun a => funext fun k => by simp only [cB, sgn_mul_self]) cB_eq_update hE

/-! #### `d₁` is the mirror curl -/

/-- **The curl on symmetric coefficient sequences** is the curl of the underlying matrix fields:
`D(curl_S) ⊆ H(curl)` on `𝕋³`. -/
theorem torus_d₁_eq (v : Models.Torus.SymCurl.Space 1)
    (hv : v ∈ (Models.Torus.SymCurl.complex.d 1 2).domain) :
    ∃ h : liftLp symι v ∈ (Models.Torus.GradCurl.complex.d 1 2).domain,
      liftLp trι (Models.Torus.SymCurl.complex.d 1 2 ⟨v, hv⟩) =
        Models.Torus.GradCurl.complex.d 1 2 ⟨liftLp symι v, h⟩ := by
  obtain ⟨h, e⟩ := exists_mulOp_count_eq (fun n => gradCurl.m 1 2 (Fourier.Torus.freq n))
    (u := liftLp symι v) (v := liftLp trι (Models.Torus.SymCurl.complex.d 1 2 ⟨v, hv⟩))
    fun n =>
      (congrArg (gradCurl.m 1 2 (Fourier.Torus.freq n)) (liftLp_apply symι v n)).trans
        ((congrArg Subtype.val (Operator.coeFn_mulOp_count
          (fun n => symCurl.m 1 2 (Fourier.Torus.freq n)) ⟨v, hv⟩ n)).symm.trans
          (liftLp_apply trι (Models.Torus.SymCurl.complex.d 1 2 ⟨v, hv⟩) n).symm)
  exact ⟨h, e.symm⟩

/-- **`d₁` is the mirror curl of Prop 4.17**: `D(d₁) ⊆ D(d₁^{mirror})` and `d₁ S = curl S`
(`Feec.Models.Cube.Mirror.complexQ`, the weak curl on `Q`). -/
theorem complexQ_d₁_eq (S : (complexQ.d 1 2).domain) :
    ∃ h : Subtype.val (S.1 : SQ) ∈ (Mirror.complexQ.d 1 2).domain,
      Subtype.val (complexQ.d 1 2 S : TQ) = Mirror.complexQ.d 1 2 ⟨_, h⟩ := by
  have hS : J₁ (S.1 : SQ) ∈ (Models.Torus.SymCurl.complex.d 1 2).domain :=
    mem_complexQ_domain_iff.1 S.2
  obtain ⟨h, e⟩ := torus_d₁_eq _ hS
  have hQ : Subtype.val (S.1 : SQ) ∈ (Mirror.complexQ.d 1 2).domain :=
    Mirror.mem_complexQ_domain_iff.2 (liftLp_J₁ S.1 ▸ h)
  refine ⟨hQ, injective_extF cB_sq ?_⟩
  have h1 := Mirror.J_complexQ_d (i := 1) (j := 2) ⟨_, hQ⟩
  have h2 : J₂ (complexQ.d 1 2 S) = Models.Torus.SymCurl.complex.d 1 2 ⟨J₁ S.1, hS⟩ :=
    J_complexQ_d S
  refine (liftLp_J₂ (complexQ.d 1 2 S)).symm.trans ?_
  rw [h2, e]
  exact (apply_congr' (Models.Torus.GradCurl.complex.d 1 2) _ _ (liftLp_J₁ S.1)).trans h1.symm

/-! #### A non-stationary datum on `Q` -/

theorem cosEQ_mem_symSub : cosEQ ∈ Models.BoundedDomain.symSub ℂ (Q (Fin 3)) := fun a b => by
  simp only [cosEQ, Geometry.resQF_apply]
  congr 1
  refine TorusWeak.eq_of_mFourierCoeff_eq fun n => ?_
  rw [coeff_fieldFourier_symm, coeff_fieldFourier_symm, coe_cosE]
  exact cosCoeff_mem_symSub n a b

/-- The electric datum on `Q` as a symmetric field. -/
def cosSQ : SQ := ⟨cosEQ, cosEQ_mem_symSub⟩

theorem J_cosSQ : J₁ cosSQ = cosS :=
  (liftLp symι).injective ((liftLp_J₁ cosSQ).trans (J_cosEQ.trans liftLp_cosS.symm))

/-- The datum `(0, E₀, 0)` of (4.18) on `Q`. -/
def cosStateQ : PiLp 2 SpaceQ := WithLp.toLp 2 (Pi.single 1 cosSQ)

theorem cosStateQ_zero : cosStateQ 0 = 0 :=
  Pi.single_eq_of_ne (M := SpaceQ) (by decide : (0 : Fin 3) ≠ 1) cosSQ
theorem cosStateQ_one : cosStateQ 1 = cosSQ := Pi.single_eq_same (M := SpaceQ) (1 : Fin 3) cosSQ
theorem cosStateQ_two : cosStateQ 2 = 0 :=
  Pi.single_eq_of_ne (M := SpaceQ) (by decide : (2 : Fin 3) ≠ 1) cosSQ

theorem totalJ_cosStateQ : HilbertComplex.totalJ J cosStateQ = cosState := by
  refine PiLp.ext fun i => ?_
  rw [HilbertComplex.totalJ_apply]
  fin_cases i
  · change J 0 (cosStateQ 0) = cosState 0
    rw [cosStateQ_zero, _root_.map_zero, cosState_zero]
  · exact (congrArg J₁ cosStateQ_one).trans (J_cosSQ.trans cosState_one.symm)
  · change J 2 (cosStateQ 2) = cosState 2
    rw [cosStateQ_two, _root_.map_zero, cosState_two]

theorem cosStateQ_mem_domain : cosStateQ ∈ complexQ.wave.domain :=
  (HilbertComplex.mem_wave_domain_compress_iff eight_pos inner_J reducingSubcomplex_range).2
    (totalJ_cosStateQ ▸ cosState_mem_domain)

theorem cosSQ_mem_domain : cosSQ ∈ (complexQ.d 1 2).domain := by
  rw [← cosStateQ_one]; exact cosStateQ_mem_domain.1 1 2

theorem complexQ_d_cosSQ_ne : complexQ.d 1 2 ⟨cosSQ, cosSQ_mem_domain⟩ ≠ 0 := by
  intro h
  have h1 := J_complexQ_d (i := 1) (j := 2) ⟨cosSQ, cosSQ_mem_domain⟩
  rw [h, _root_.map_zero] at h1
  exact curlS_cosS_ne ((apply_congr' _ _ _ J_cosSQ.symm).trans h1.symm)

/-- **A non-stationary TSD datum on `Q`** for (4.18).
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem exists_nonstationaryQ :
    ∃ y ∈ complexQ.wave.domain, y ∈ totalSub tsdQ ∧ y ∉ complexQ.waveGroup.stationary := by
  have hd : HilbertComplex.totalJ J cosStateQ ∈ Models.Torus.SymCurl.complex.wave.domain :=
    totalJ_cosStateQ ▸ cosState_mem_domain
  obtain ⟨h1, h2⟩ := HilbertComplex.not_mem_stationary_compress eight_pos inner_J
    reducingSubcomplex_range hd fun h0 =>
      wave_cosState_ne ((apply_congr' _ _ _ totalJ_cosStateQ.symm).trans h0)
  refine ⟨cosStateQ, h1, fun i => ?_, h2⟩
  change J i (cosStateQ i) ∈ Models.Torus.SymCurl.constraint i
  rw [← HilbertComplex.totalJ_apply, totalJ_cosStateQ]
  exact cosState_mem_constraint i

/-! ### Every open cube -/

section Cube

open Geometry (openCube)
open Feec.Models.BoundedDomain (R3)
open Feec.Models.Cube.Mirror (inv_two_mul_ne preimage_aff_Q pullCube inner_pullCube jac_inv_pos
  tsd_of_pullCube)

variable {b : R3} {s : ℝ} (hs : 0 < s)

/-- The pull-back `u ↦ u ∘ T` of scalar functions from `Q` to the cube `∏ (bᵢ, bᵢ + s)`. -/
def pullScalar (b : R3) (s : ℝ) (hs : 0 < s) : RQ ≃L[ℂ] Domain.L2 ℂ (openCube b s) :=
  ContinuousLinearEquiv.equivOfInverse
    (Domain.pull (inv_two_mul_ne hs) (-((2 * s)⁻¹ • b)) Geometry.measurableSet_Q
      (preimage_aff_Q hs b))
    (Domain.pull (inv_ne_zero (inv_two_mul_ne hs)) (-((2 * s)⁻¹⁻¹ • -((2 * s)⁻¹ • b)))
      (Domain.measurableSet_of_aff _ Geometry.measurableSet_Q (preimage_aff_Q hs b))
      (Domain.preimage_inv_of_aff (inv_two_mul_ne hs) _ (preimage_aff_Q hs b)))
    (Domain.pull_pull _ _ _ _ _ _ (Domain.aff_inv' (inv_two_mul_ne hs) _))
    (Domain.pull_pull _ _ _ _ _ _ (Domain.aff_inv (inv_two_mul_ne hs) _))

theorem inner_pullScalar (f g : RQ) :
    ⟪pullScalar b s hs f, pullScalar b s hs g⟫_ℂ =
      (((Domain.jac (E := R3) (2 * s)⁻¹)⁻¹ : ℝ) : ℂ) * ⟪f, g⟫_ℂ :=
  Domain.inner_pullₗ (inv_two_mul_ne hs) (-((2 * s)⁻¹ • b)) Geometry.measurableSet_Q
    (preimage_aff_Q hs b) f g

theorem pullCube_mem_symSub {x : MQ} (hx : x ∈ Models.BoundedDomain.symSub ℂ (Q (Fin 3))) :
    pullCube b s hs (Fin 3 × Fin 3) x ∈ Models.BoundedDomain.symSub ℂ (openCube b s) :=
  fun i j => by rw [Domain.pullF_apply, Domain.pullF_apply, hx i j]

theorem pullCube_symm_mem_symSub {y : Domain.L2F ℂ (openCube b s) (Fin 3 × Fin 3)}
    (hy : y ∈ Models.BoundedDomain.symSub ℂ (openCube b s)) :
    (pullCube b s hs (Fin 3 × Fin 3)).symm y ∈ Models.BoundedDomain.symSub ℂ (Q (Fin 3)) :=
  fun i j => by rw [Domain.pullF_symm_apply, Domain.pullF_apply, Domain.pullF_apply, hy i j]

theorem pullCube_mem_trSub {x : MQ} (hx : x ∈ Models.BoundedDomain.trSub ℂ (Q (Fin 3))) :
    pullCube b s hs (Fin 3 × Fin 3) x ∈ Models.BoundedDomain.trSub ℂ (openCube b s) := by
  change ∑ i, pullCube b s hs (Fin 3 × Fin 3) x (i, i) = 0
  simp only [Domain.pullF_apply]
  rw [← map_sum, show ∑ i, x (i, i) = 0 from hx, _root_.map_zero]

theorem pullCube_symm_mem_trSub {y : Domain.L2F ℂ (openCube b s) (Fin 3 × Fin 3)}
    (hy : y ∈ Models.BoundedDomain.trSub ℂ (openCube b s)) :
    (pullCube b s hs (Fin 3 × Fin 3)).symm y ∈ Models.BoundedDomain.trSub ℂ (Q (Fin 3)) := by
  change ∑ i, (pullCube b s hs (Fin 3 × Fin 3)).symm y (i, i) = 0
  simp only [Domain.pullF_symm_apply, Domain.pullF_apply]
  rw [← map_sum, show ∑ i, y (i, i) = 0 from hy, _root_.map_zero]

/-- The pull-back of symmetric fields. -/
def pullSym (b : R3) (s : ℝ) (hs : 0 < s) : SQ ≃L[ℂ] Models.BoundedDomain.symSub ℂ (openCube b s) :=
  (pullCube b s hs (Fin 3 × Fin 3)).restrictSub _ _ (fun _ hx => pullCube_mem_symSub hs hx)
    fun _ hy => pullCube_symm_mem_symSub hs hy

/-- The pull-back of trace-free fields. -/
def pullTr (b : R3) (s : ℝ) (hs : 0 < s) : TQ ≃L[ℂ] Models.BoundedDomain.trSub ℂ (openCube b s) :=
  (pullCube b s hs (Fin 3 × Fin 3)).restrictSub _ _ (fun _ hx => pullCube_mem_trSub hs hx)
    fun _ hy => pullCube_symm_mem_trSub hs hy

theorem inner_pullSym (u v : SQ) :
    ⟪pullSym b s hs u, pullSym b s hs v⟫_ℂ =
      (((Domain.jac (E := R3) (2 * s)⁻¹)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner]
  exact inner_pullCube hs (u : MQ) (v : MQ)

theorem inner_pullTr (u v : TQ) :
    ⟪pullTr b s hs u, pullTr b s hs v⟫_ℂ =
      (((Domain.jac (E := R3) (2 * s)⁻¹)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner]
  exact inner_pullCube hs (u : MQ) (v : MQ)

instance (b : R3) (s : ℝ) :
    IsScalarTower ℝ ℂ (Models.BoundedDomain.symSub ℂ (openCube b s)) :=
  Submodule.isScalarTower _

instance (b : R3) (s : ℝ) :
    IsScalarTower ℝ ℂ (Models.BoundedDomain.trSub ℂ (openCube b s)) :=
  Submodule.isScalarTower _

/-- The spaces `L²(C)`, `L²(C; S)`, `L²(C; T)` on the cube `C = ∏ (bᵢ, bᵢ + s)`. -/
abbrev SpaceCube (b : R3) (s : ℝ) (i : Fin 3) : Type :=
  W3 (Domain.L2 ℂ (openCube b s)) (Models.BoundedDomain.symSub ℂ (openCube b s))
    (Models.BoundedDomain.trSub ℂ (openCube b s)) i

/-- The pull-backs on the three spaces. -/
def eCube (b : R3) (s : ℝ) (hs : 0 < s) : ∀ i : Fin 3, SpaceQ i ≃L[ℂ] SpaceCube b s i
  | 0 => pullScalar b s hs
  | 1 => pullSym b s hs
  | 2 => pullTr b s hs

theorem inner_eCube (i : Fin 3) (u v : SpaceQ i) :
    ⟪eCube b s hs i u, eCube b s hs i v⟫_ℂ =
      (((Domain.jac (E := R3) (2 * s)⁻¹)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  fin_cases i
  · exact inner_pullScalar hs u v
  · exact inner_pullSym hs u v
  · exact inner_pullTr hs u v

/-- The chain-rule factors `(2s)⁻²` of the Hessian and `(2s)⁻¹` of the curl. -/
def kappa (s : ℝ) : Fin 3 → Fin 3 → ℂ := fun i _ =>
  if i = 0 then ((((2 * s)⁻¹) ^ 2 : ℝ) : ℂ) else (((2 * s)⁻¹ : ℝ) : ℂ)

theorem kappa_ne_zero (hs : 0 < s) (i j : Fin 3) : kappa s i j ≠ 0 := by
  unfold kappa
  split_ifs
  · exact RCLike.ofReal_ne_zero.2 (pow_ne_zero 2 (inv_two_mul_ne hs))
  · exact RCLike.ofReal_ne_zero.2 (inv_two_mul_ne hs)

/-- **The mirror complex (4.16) on the open cube** `∏ (bᵢ, bᵢ + s)`: the transport of `complexQ`
along the pull-back by `x ↦ (x - b)/(2s)`, with the chain-rule factors `(2s)⁻²` (Hessian) and
`(2s)⁻¹` (curl). -/
abbrev complexCube (b : R3) (s : ℝ) (hs : 0 < s) :
    HilbertComplex ℂ ComplexShape.fin3 (SpaceCube b s) :=
  complexQ.transport (eCube b s hs) (kappa s) (kappa_ne_zero hs)

/-- The pull-back to `Q` embeds the cube complex in the complex on `Q`. -/
def embeddingCube : ScaledEmbedding (complexCube b s hs) complexQ :=
  ScaledEmbedding.ofTransportSymm (eCube b s hs) (kappa s) (kappa_ne_zero hs)
    (fun _ => (Domain.jac (E := R3) (2 * s)⁻¹)⁻¹) (fun _ => jac_inv_pos hs) (inner_eCube hs)

/-- The constraint on the cube. -/
abbrev tsdCube (b : R3) (s : ℝ) (hs : 0 < s) (i : Fin 3) : Submodule ℂ (SpaceCube b s i) :=
  (tsdQ i).comap ((embeddingCube (b := b) hs).J i : SpaceCube b s i →ₗ[ℂ] SpaceQ i)

instance (i : Fin 3) : (tsdCube b s hs i).HasOrthogonalProjection :=
  (embeddingCube hs).comap_hasOrthogonalProjection i _

/-- **TSD reduces the mirror complex (4.16) on every open cube.**
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem reducingSubcomplexCube : (complexCube b s hs).ReducingSubcomplex (tsdCube b s hs) :=
  (embeddingCube hs).reducingSubcomplex_comap reducingSubcomplexQ fun i x =>
    ⟨eCube b s hs i ((tsdQ i).starProjection ((eCube b s hs i).symm x)),
      (eCube b s hs i).symm_apply_apply _⟩

/-- **Prop 4.19 on every open cube with mirror boundary conditions.**
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem propagatesCube {a c : ℝ} {F U : ℝ → PiLp 2 (SpaceCube b s)}
    (hU : Evolution.IsStrongSolution (complexCube b s hs).wave (Icc a c) F U)
    (h0 : U a ∈ totalSub (tsdCube b s hs)) (hF : ∀ t ∈ Icc a c, F t ∈ totalSub (tsdCube b s hs)) :
    ∀ t ∈ Icc a c, U t ∈ totalSub (tsdCube b s hs) :=
  (reducingSubcomplexCube hs).propagates hU h0 hF

/-- Prop 4.19 on every open cube, with existence and uniqueness (e.g. on `(0, π)³`, `(0, 1)³`).
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem existsUnique_memCube {U₀ : PiLp 2 (SpaceCube b s)}
    (hU₀ : U₀ ∈ (complexCube b s hs).wave.domain) (hU₀S : U₀ ∈ totalSub (tsdCube b s hs))
    {F : ℝ → PiLp 2 (SpaceCube b s)} {a c : ℝ}
    (hF : Evolution.ForcingClass.admissible (complexCube b s hs).wave a c F)
    (hFS : ∀ t ∈ Icc a c, F t ∈ totalSub (tsdCube b s hs)) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (complexCube b s hs).wave (Icc a c) F U ∧
      (∀ t ∈ Icc a c, U t ∈ totalSub (tsdCube b s hs)) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (complexCube b s hs).wave (Icc a c) F V →
        EqOn V U (Icc a c) :=
  (reducingSubcomplexCube hs).existsUnique_mem hU₀ hU₀S hF hFS

/-- `K* = K` on every open cube for (4.16).
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem invariantCore_eqCube :
    (complexCube b s hs).waveGroup.invariantCore (totalSub (tsdCube b s hs)) =
      totalSub (tsdCube b s hs) :=
  (reducingSubcomplexCube hs).invariantCore_eq

/-- The datum `(0, E₀ ∘ T, 0)` of (4.18) on the cube. -/
def cosStateCube (b : R3) (s : ℝ) (hs : 0 < s) : PiLp 2 (SpaceCube b s) :=
  HilbertComplex.totalMap (eCube b s hs) cosStateQ

theorem mem_totalSub_tsdCube_iff {y : PiLp 2 (SpaceCube b s)} :
    y ∈ totalSub (tsdCube b s hs) ↔
      HilbertComplex.totalMap (fun i => (eCube b s hs i).symm) y ∈ totalSub tsdQ := by
  refine forall_congr' fun i => ?_
  rw [HilbertComplex.totalMap_apply]
  rfl

theorem cosStateQ_mem_tsdQ : cosStateQ ∈ totalSub tsdQ := fun i => by
  show J i (cosStateQ i) ∈ Models.Torus.SymCurl.constraint i
  rw [← HilbertComplex.totalJ_apply, totalJ_cosStateQ]
  exact cosState_mem_constraint i

theorem totalMap_symm_cosStateCube :
    HilbertComplex.totalMap (fun i => (eCube b s hs i).symm) (cosStateCube b s hs) = cosStateQ :=
  PiLp.ext fun i => (eCube b s hs i).symm_apply_apply _

theorem cosStateCube_mem_domain : cosStateCube b s hs ∈ (complexCube b s hs).wave.domain := by
  refine (HilbertComplex.mem_wave_domain_transport_iff (kappa_ne_zero hs) (jac_inv_pos hs)
    (inner_eCube hs)).2 ?_
  rw [totalMap_symm_cosStateCube]
  exact cosStateQ_mem_domain

theorem cosStateCube_mem_tsdCube : cosStateCube b s hs ∈ totalSub (tsdCube b s hs) := by
  refine (mem_totalSub_tsdCube_iff hs).2 ?_
  rw [totalMap_symm_cosStateCube]
  exact cosStateQ_mem_tsdQ

theorem wave_cosStateCube_ne :
    (complexCube b s hs).wave ⟨_, cosStateCube_mem_domain hs⟩ ≠ 0 := by
  intro h
  have h2 := congrArg (fun y : PiLp 2 (SpaceCube b s) => y 2) h
  rw [HilbertComplex.wave_apply_fin3_two] at h2
  have h4 : (complexCube b s hs).d 1 2 ⟨cosStateCube b s hs 1,
      (cosStateCube_mem_domain hs).1 1 2⟩ = 0 := (apply_congr' _ _ _ rfl).trans h2
  have h3 := (embeddingCube (b := b) hs).apply_eq_zero _ h4
  apply complexQ_d_cosSQ_ne
  refine (apply_congr' _ _ _ ?_).trans h3
  show cosSQ = (eCube b s hs 1).symm (eCube b s hs 1 (cosStateQ 1))
  rw [ContinuousLinearEquiv.symm_apply_apply, cosStateQ_one]

/-- **A non-stationary TSD datum on every open cube** for (4.18).
See [QuennevilleBelair2015], §4.11 (Prop 4.19, corrected). -/
theorem exists_nonstationaryCube :
    ∃ y ∈ (complexCube b s hs).wave.domain, y ∈ totalSub (tsdCube b s hs) ∧
      y ∉ (complexCube b s hs).waveGroup.stationary :=
  ⟨cosStateCube b s hs, cosStateCube_mem_domain hs, cosStateCube_mem_tsdCube hs,
    HilbertComplex.not_mem_stationary_of_wave_ne_zero _ (wave_cosStateCube_ne hs)⟩

end Cube

end Feec.Models.Cube.MirrorSym
