module

public import Solution.MirrorProp
public import Solution.Wave

/-!
# Mirror boundary conditions: the system (4.14)

The challenge's system (4.14) with the mirror boundary conditions (`gradCurlMirror`, the bottom
row `gd0`, `gd1` of `mirrorData`) is compared with `Feec`'s mirror grad–curl complex
`Feec.Models.Cube.Mirror.complexQ` (complex scalars, matrix fields) as `Solution.MirrorProp` does
for the system (6.1):

* the real part `realG x = (0, rows of Re E, rows of ⋆ Re B)` of a constrained state of `D(L)`
  solves the challenge's equations with `realG (L x)` (`isHodgeWave_realG`): the rows of `Re E`
  lie in `D(d̃¹)` with `d̃¹` the rows of `curl E` (`rowsW1L_mem_curl`), they are orthogonal to
  `d̃⁰ D(d̃⁰)` for TSD coefficients (`inner_rowsW1L_gd0`), and `E' = -curl† B` gives the second
  equation against the complexified real rows;
* the complexification `cplxG X = (0, E, B)` of a TSD state `X` of `D(L)` lies in `D(L)` and in
  the constraint, with `L (cplxG X) = cplxG (L X)` (`forwardG`): `E ∈ D(curl)` from the rows,
  `B ∈ D(curl†)` by splitting the pairings into real and imaginary parts (`mem_adjoint_cplxB`),
  the wall conditions of the constraint from the domain conditions
  (`Feec.Models.Cube.Mirror.mem_tsdQ_one_of_tsd`, `mem_tsdQ_two_of_tsd`), and `E ∈ D(grad†)`
  with `grad† E = 0` (`Feec.Models.Cube.Mirror.mem_adjoint_d₀_of_mem_tsdQ`).

So the strong solutions from TSD data of `D(L)` are the real parts of the orbits of `complexQ`
(`isStrongSolution_realG`; uniqueness by energy, `IsHodgeWave.isStrongSolution_unique`), which
stay in the constraint (`Feec.Models.Cube.Mirror.propagatesQ`), and `cosStateQ` (or
`-i cosStateQ`) gives a moving TSD solution (`exists_mirrorG_chain`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 ((4.14), Prop 4.17)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec Feec.Domain Feec.Models.BoundedDomain
open Feec.Models.Cube.FEM (cubeDomain cubeDomain_eq_Q)
open Feec.Models.Cube.Geometry (Q)
open Feec.Models.Cube.RowWise (ofRealL reL)
open Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.Mirror (MQ VQ SpaceQ complexQ tsdQ)
open Feec.Models.Cube.WeakSymmetry (W1 Wv)
open Feec.HilbertComplex (totalSub)

/-- A state `(σ, u, ρ)` of the system (4.14) on the cube. -/
abbrev GState : Type := L2Vec (cube 3) 0 × L2Vec (cube 3) 1 × L2Vec (cube 3) 2

/-- The first operator `∏ₐ H_{a}Λ⁰(Q) → ∏ₐ H_{a}Λ¹(Q)` of the system (4.14) with the mirror
boundary conditions. -/
abbrev gd0 : L2Vec (cube 3) 0 →ₗ.[ℝ] L2Vec (cube 3) 1 := vecOp fun a => dPart {a} 0

/-- The second operator `∏ₐ H_{a}Λ¹(Q) → (L²Λ²(Q))³`. -/
abbrev gd1 : L2Vec (cube 3) 1 →ₗ.[ℝ] L2Vec (cube 3) 2 := vecOp fun a => dPart {a} 1

/-! ### The real part and the complexification -/

/-- **The real state of a mirror state** `(σ, E, B)`: `(0, rows of Re E, rows of ⋆ Re B)`. -/
def realG : PiLp 2 SpaceQ →L[ℝ] GState :=
  (0 : PiLp 2 SpaceQ →L[ℝ] L2Vec (cube 3) 0).prod
    ((rowsW1L.comp ((PiLp.proj (𝕜 := ℂ) 2 SpaceQ (1 : Fin 3)).restrictScalars ℝ)).prod
      (rowsW2L.comp ((PiLp.proj (𝕜 := ℂ) 2 SpaceQ (2 : Fin 3)).restrictScalars ℝ)))

/-- **The complexification** `(0, E, B)` of a state `(σ, u, ρ)`: rows of `E` the `uₐ`, rows of
`⋆B` the `ρₐ`. -/
def cplxG (X : GState) : PiLp 2 SpaceQ :=
  ShortHilbertComplex.mk3 0 (cplxE X.2.1) (cplxB X.2.2)

theorem realG_cplxG {X : GState} (h0 : X.1 = 0) : realG (cplxG X) = X := by
  obtain ⟨σ, u, ρ⟩ := X
  simp only at h0
  subst h0
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · refine PiLp.ext fun a => ?_
    change (cQ _).symm (rowRe (cplxE u) a) = u a
    rw [cplxE, rowRe_ofRealRows]
    exact LinearIsometryEquiv.symm_apply_apply _ _
  · refine PiLp.ext fun a => ?_
    change (cQ _).symm (rowRe2 (cplxB ρ) a) = ρ a
    rw [cplxB, rowRe2_ofRealRows2]
    exact LinearIsometryEquiv.symm_apply_apply _ _

/-- **Constrained mirror states have TSD real parts.** -/
theorem isTSD_realG {x : PiLp 2 SpaceQ} (hx : x ∈ totalSub tsdQ) :
    realG x ∈ tsdConstraint (cube 3) := by
  obtain ⟨hEs, hEt, hEv⟩ := Feec.Models.Cube.Mirror.mem_tsdQ_one (hx 1)
  obtain ⟨hBs, hBt, hBv⟩ := Feec.Models.Cube.Mirror.mem_tsdQ_two (hx 2)
  refine ⟨rfl, ?_, ?_⟩
  · rw [isTSD_iff, toIx_mat1]
    change fieldE (rowsW1L (show MQ from x 1)) ∈ tsd (cube 3)
    rw [fieldE_rowsW1L]
    exact (mem_tsd_castL2_symm (cubeDomain_eq_Q 3) _).2 (reF_mem_tsd hEs hEt hEv)
  · rw [isTSD_iff, toIx_mat2]
    change fieldB (rowsW2L (show MQ from x 2)) ∈ tsd (cube 3)
    rw [fieldB_rowsW2L]
    exact (mem_tsd_castL2_symm (cubeDomain_eq_Q 3) _).2 (reF_mem_tsd hBs hBt hBv)

/-! ### The operators on real rows -/

/-- **The real rows of a field of `D(curl)` lie in `D(d̃¹)`**, with `d̃¹` of them the real rows
of `curl E` (Hodge star). -/
theorem rowsW1L_mem_curl (Z : (complexQ.d 1 2).domain) :
    ∃ h : rowsW1L (show MQ from Z.1) ∈ gd1.domain,
      gd1 ⟨_, h⟩ = rowsW2L (show MQ from complexQ.d 1 2 Z) := by
  have hc : ∀ a, ∃ h : (cQ _).symm (rowRe (show MQ from Z.1) a) ∈ (BD1 a).domain,
      BD1 a ⟨_, h⟩ = (cQ _).symm (rowRe2 (show MQ from complexQ.d 1 2 Z) a) := fun a => by
    obtain ⟨h, e⟩ := rowRe_mem_curl Z a
    have hg := (Feec.Models.Cube.DeRhamIdent.dPart (Q (Fin 3)) {a} ((1 : ℕ) : ℤ)).mem_graph
      ⟨_, h⟩
    rw [e] at hg
    exact dPart_cube_of_Q hg
  have hm : rowsW1L (show MQ from Z.1) ∈ gd1.domain := fun a => by
    change _ ∈ (dPart {a} 1).domain
    rw [dPart_eq]
    exact (hc a).1
  refine ⟨hm, PiLp.ext fun a => ?_⟩
  change dPart {a} 1 ⟨_, hm a⟩ = (cQ _).symm (rowRe2 (show MQ from complexQ.d 1 2 Z) a)
  rw [dPart_apply_eq]
  exact (hc a).2

/-- **`E` of a state of `D(d̃¹)` lies in `D(curl)`**, with `curl E` the rows of `d̃u`. -/
theorem cplxE_mem_curl {u : L2Vec (cube 3) 1} (hu : u ∈ gd1.domain) :
    ∃ h : cplxE u ∈ (complexQ.d 1 2).domain, complexQ.d 1 2 ⟨_, h⟩ = cplxB (gd1 ⟨u, hu⟩) := by
  have hc : ∀ a, u a ∈ (BD1 a).domain := fun a => by
    have h := hu a
    change _ ∈ (dPart {a} 1).domain at h
    rw [dPart_eq] at h
    exact h
  have hv : ∀ a, cQ _ (u a) ∈ (Feec.Models.Cube.DeRhamIdent.dPart (Q (Fin 3)) {a}
      ((1 : ℕ) : ℤ)).domain := fun a => (dPart_Q_of_cube ⟨_, hc a⟩).1
  obtain ⟨h, e⟩ := ofRealRows_mem_curl _ hv
  refine ⟨h, e.trans ?_⟩
  change ofRealRows2 _ = ofRealRows2 fun a => cQ _ (gd1 ⟨u, hu⟩ a)
  congr 1
  funext a
  exact (dPart_Q_of_cube ⟨_, hc a⟩).2.trans (congrArg (cQ _) (dPart_apply_eq ⟨_, hu a⟩).symm)

/-- `⟪Re-rows of E, u⟫` is the real part of the complex pairing with `cplxE u`. -/
theorem inner_rowsW1L_eq (E : MQ) (u : L2Vec (cube 3) 1) :
    ⟪rowsW1L E, u⟫ = RCLike.re ⟪E, cplxE u⟫_ℂ := by
  have h : ∀ w : Wv W1, ⟪rowsW1L E, w⟫ = RCLike.re ⟪E, ofRealRows fun a => cQ _ (w a)⟫_ℂ := by
    intro w
    rw [re_inner_ofRealRows, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [rowsW1L_apply, ← LinearIsometryEquiv.inner_map_map (cQ _),
      LinearIsometryEquiv.apply_symm_apply]
  exact h u

/-- `⟪⋆Re-rows of B, ρ⟫` is the real part of the complex pairing with `cplxB ρ`. -/
theorem inner_rowsW2L_eq (B : MQ) (ρ : L2Vec (cube 3) 2) :
    ⟪rowsW2L B, ρ⟫ = RCLike.re ⟪B, cplxB ρ⟫_ℂ :=
  inner_rowsW2L B ρ

/-- **`⟪u, d̃⁰ψ⟫ = 0` for the real rows `u` of a field of the electric constraint**, for every
`ψ ∈ ∏ₐ H_{a}Λ⁰(Q)`: the Fourier coefficients are TSD. -/
theorem inner_rowsW1L_gd0 {E : MQ} (hE : E ∈ tsdQ 1) (ψ : gd0.domain) :
    ⟪rowsW1L E, gd0 ψ⟫ = 0 := by
  have hE' : ∀ n, (Feec.Models.Cube.MirrorBGG.J₁ E : (Fin 3 → ℤ) → Fourier.GradCurl.Mat) n ∈
      Fourier.GradCurl.tsd (Fourier.Torus.freq n) := fun n =>
    Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 hE) n
  have h : ⟪rowsW1L E, bIncl1 (bD0 (toBU0 ψ))⟫_ℝ = 0 := by
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [rowsW1L_apply, bIncl1_apply, bD0_apply, ← LinearIsometryEquiv.inner_map_map (cQ _),
      LinearIsometryEquiv.apply_symm_apply]
    obtain ⟨hψ, eψ⟩ := dPart_Q_of_cube (toBU0 ψ a)
    calc _ = ⟪rowRe E a, (Feec.Models.Cube.DeRhamIdent.dPart (Q (Fin 3)) {a} ((0 : ℕ) : ℤ)
          ⟨_, hψ⟩ : L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ)))⟫_ℝ :=
          congrArg (fun z => ⟪rowRe E a, z⟫_ℝ) eψ.symm
      _ = 0 := inner_rowRe_dPart_zero E hE' a ⟨_, hψ⟩
  exact (congrArg (fun z => ⟪rowsW1L E, z⟫) (bIncl1_bD0_toBU0 ψ)).symm.trans h

/-! ### The wave operators -/

/-- **`realG` intertwines the wave operators on the constraint.** -/
theorem isHodgeWave_realG {x : complexQ.wave.domain} (hx : (x : PiLp 2 SpaceQ) ∈ totalSub tsdQ) :
    IsHodgeWave gd0 gd1 (realG x) (realG (complexQ.wave x)) := by
  obtain ⟨hr, er⟩ := rowsW1L_mem_curl ⟨_, x.2.1 1 2⟩
  have hx0 : ((x : PiLp 2 SpaceQ) 0 : VQ) = 0 := Feec.Models.Cube.Mirror.mem_tsdQ_zero.1 (hx 0)
  refine ⟨0, ⟨_, hr⟩, rfl, rfl, fun τ => ?_, fun v => ?_, ?_⟩
  · change ⟪(0 : L2Vec (cube 3) 0), (τ : L2Vec (cube 3) 0)⟫ =
      ⟪rowsW1L (show MQ from (x : PiLp 2 SpaceQ) 1), gd0 τ⟫
    rw [inner_zero_left]
    exact (inner_rowsW1L_gd0 (hx 1) τ).symm
  · obtain ⟨hv, ev⟩ := cplxE_mem_curl v.2
    have e1 : (complexQ.wave x) 1 =
        -(complexQ.d 1 2)† ⟨(x : PiLp 2 SpaceQ) 2, x.2.2 2 1⟩ := by
      rw [HilbertComplex.wave_apply_fin3_one]
      have e : complexQ.d 0 1 ⟨(x : PiLp 2 SpaceQ) 0, x.2.1 0 1⟩ = 0 := by
        rw [LinearPMap.apply_congr' _ _ (Submodule.zero_mem _) hx0]
        exact LinearPMap.map_zero _
      rw [e, zero_sub]
    have hA := LinearPMap.adjoint_isFormalAdjoint (complexQ.dense 1 2)
      ⟨(x : PiLp 2 SpaceQ) 2, x.2.2 2 1⟩ ⟨_, hv⟩
    have e1' : (show MQ from (complexQ.wave x) 1) =
        -(show MQ from (complexQ.d 1 2)† ⟨(x : PiLp 2 SpaceQ) 2, x.2.2 2 1⟩) := e1
    have hA' : ⟪(show MQ from (complexQ.d 1 2)† ⟨(x : PiLp 2 SpaceQ) 2, x.2.2 2 1⟩),
        cplxE v⟫_ℂ = ⟪(show MQ from (x : PiLp 2 SpaceQ) 2), cplxB (gd1 v)⟫_ℂ :=
      hA.trans (congrArg (fun z : MQ => ⟪(show MQ from (x : PiLp 2 SpaceQ) 2), z⟫_ℂ) ev)
    have k : ⟪(show MQ from (complexQ.wave x) 1), cplxE v⟫_ℂ =
        -⟪(show MQ from (x : PiLp 2 SpaceQ) 2), cplxB (gd1 v)⟫_ℂ := by
      rw [e1', inner_neg_left, hA']
    change ⟪rowsW1L (show MQ from (complexQ.wave x) 1), (v : L2Vec (cube 3) 1)⟫ =
      -⟪gd0 0, (v : L2Vec (cube 3) 1)⟫ -
        ⟪rowsW2L (show MQ from (x : PiLp 2 SpaceQ) 2), gd1 v⟫
    rw [LinearPMap.map_zero, inner_zero_left, inner_rowsW1L_eq, inner_rowsW2L_eq, k, map_neg]
    ring
  · change rowsW2L (show MQ from (complexQ.wave x) 2) = gd1 ⟨_, hr⟩
    exact (congrArg rowsW2L (complexQ.wave_apply_fin3_two x)).trans er.symm

/-! ### TSD states as constrained states -/

/-- **`B` lies in the domain of `curl†`, with `-curl† B = E_Y`**, when `L X = Y` with `σ = 0`. -/
theorem mem_adjoint_cplxB {X Y : GState} (h : IsHodgeWave gd0 gd1 X Y) (h0 : X.1 = 0) :
    ∃ hB : cplxB X.2.2 ∈ ((complexQ.d 1 2)†).domain,
      (complexQ.d 1 2)† ⟨_, hB⟩ = -cplxE Y.2.1 := by
  obtain ⟨σ, u, hσ, hu, -, h2, -⟩ := h
  have hσ0 : σ = 0 := Subtype.ext (hσ.trans h0)
  have key : ∀ r : gd1.domain, ⟪Y.2.1, (r : L2Vec (cube 3) 1)⟫ = -⟪X.2.2, gd1 r⟫ := by
    intro r
    have e := h2 r
    rw [hσ0, LinearPMap.map_zero, inner_zero_left] at e
    linarith
  have hre : ∀ Z : (complexQ.d 1 2).domain, RCLike.re ⟪-cplxE Y.2.1, (show MQ from Z.1)⟫_ℂ =
      RCLike.re ⟪cplxB X.2.2, (show MQ from complexQ.d 1 2 Z)⟫_ℂ := by
    intro Z
    obtain ⟨hr, er⟩ := rowsW1L_mem_curl Z
    have e1 : RCLike.re ⟪(show MQ from Z.1), cplxE Y.2.1⟫_ℂ =
        ⟪rowsW1L (show MQ from Z.1), Y.2.1⟫ := (inner_rowsW1L_eq _ _).symm
    have e2 : RCLike.re ⟪(show MQ from complexQ.d 1 2 Z), cplxB X.2.2⟫_ℂ =
        ⟪rowsW2L (show MQ from complexQ.d 1 2 Z), X.2.2⟫ := (inner_rowsW2L_eq _ _).symm
    set r : gd1.domain := ⟨_, hr⟩
    calc RCLike.re ⟪-cplxE Y.2.1, (show MQ from Z.1)⟫_ℂ
        = -RCLike.re ⟪(show MQ from Z.1), cplxE Y.2.1⟫_ℂ := by
          rw [inner_neg_left, map_neg, inner_re_symm]
      _ = -⟪rowsW1L (show MQ from Z.1), Y.2.1⟫ := by rw [e1]
      _ = -⟪Y.2.1, (r : L2Vec (cube 3) 1)⟫ := congrArg Neg.neg (real_inner_comm _ _)
      _ = ⟪X.2.2, gd1 r⟫ := by rw [key r, neg_neg]
      _ = ⟪gd1 r, X.2.2⟫ := real_inner_comm _ _
      _ = ⟪rowsW2L (show MQ from complexQ.d 1 2 Z), X.2.2⟫ :=
          congrArg (fun y : L2Vec (cube 3) 2 => ⟪y, X.2.2⟫) er
      _ = RCLike.re ⟪(show MQ from complexQ.d 1 2 Z), cplxB X.2.2⟫_ℂ := e2.symm
      _ = RCLike.re ⟪cplxB X.2.2, (show MQ from complexQ.d 1 2 Z)⟫_ℂ := inner_re_symm _ _
  have hw : ∀ Z : (complexQ.d 1 2).domain, ⟪-cplxE Y.2.1, (show MQ from Z.1)⟫_ℂ =
      ⟪cplxB X.2.2, (show MQ from complexQ.d 1 2 Z)⟫_ℂ := by
    intro Z
    have hr := hre Z
    have hi := hre (-Complex.I • Z)
    have e1 : (show MQ from (-Complex.I • Z).1) = -Complex.I • (show MQ from Z.1) := rfl
    have e2 : (show MQ from complexQ.d 1 2 (-Complex.I • Z)) =
        -Complex.I • (show MQ from complexQ.d 1 2 Z) :=
      (LinearPMap.map_smul (complexQ.d 1 2) (-Complex.I) Z :)
    rw [e1, e2, inner_smul_right, inner_smul_right] at hi
    refine Complex.ext hr ?_
    simpa [Complex.mul_re] using hi
  have hB := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, hw⟩
  exact ⟨hB, LinearPMap.adjoint_apply_eq (complexQ.dense 1 2) ⟨_, hB⟩ hw⟩

/-- **TSD states of `D(L)` are constrained states of `D(L)` of the mirror complex**, with
`L (cplxG X) = cplxG (L X)`, and `L X` is TSD. -/
theorem forwardG {X Y : GState} (h : IsHodgeWave gd0 gd1 X Y)
    (hX : X ∈ tsdConstraint (cube 3)) :
    ∃ hd : cplxG X ∈ complexQ.wave.domain, cplxG X ∈ totalSub tsdQ ∧
      complexQ.wave ⟨_, hd⟩ = cplxG Y ∧ Y ∈ tsdConstraint (cube 3) := by
  obtain ⟨h0, hE, hB⟩ := hX
  obtain ⟨σ, u, -, hu, h1, -, hd1⟩ := id h
  have hum : X.2.1 ∈ gd1.domain := hu ▸ u.2
  obtain ⟨hEd, eE⟩ := cplxE_mem_curl hum
  obtain ⟨hBd, eB⟩ := mem_adjoint_cplxB h h0
  rw [isTSD_iff, toIx_mat1] at hE
  rw [isTSD_iff, toIx_mat2] at hB
  have hEc := ofRealF_tsd (mem_tsd_cQ (show fieldE (Ω := cubeDomain 3) X.2.1 ∈ tsd (cubeDomain 3)
    from hE))
  have hBc := ofRealF_tsd (mem_tsd_cQ (show fieldB (Ω := cubeDomain 3) X.2.2 ∈ tsd (cubeDomain 3)
    from hB))
  rw [← cplxE_eq] at hEc
  rw [← cplxB_eq] at hBc
  obtain ⟨hEs, hEt, hEv⟩ := hEc
  obtain ⟨hBs, hBt, hBv⟩ := hBc
  have hE1 := Feec.Models.Cube.Mirror.mem_tsdQ_one_of_tsd hEd hEs hEt hEv
  have hB2 := Feec.Models.Cube.Mirror.mem_tsdQ_two_of_tsd hBd hBs hBt hBv
  obtain ⟨hEa, eEa⟩ := Feec.Models.Cube.Mirror.mem_adjoint_d₀_of_mem_tsdQ hE1
  have hc : cplxG X ∈ totalSub tsdQ := fun i => by
    fin_cases i
    · exact Submodule.zero_mem _
    · exact hE1
    · exact hB2
  have hd : cplxG X ∈ complexQ.wave.domain :=
    complexQ.mem_wave_domain_fin3 (Submodule.zero_mem _) hEd hEa hBd
  set x : complexQ.wave.domain := ⟨_, hd⟩
  have hred : complexQ.wave x ∈ totalSub tsdQ :=
    Feec.Models.Cube.Mirror.reducingSubcomplexQ.isReducing_wave.mapsTo x hc
  have hreal : realG (cplxG X) = X := realG_cplxG h0
  have hY1 : Y.1 = 0 := by
    refine eq_zero_of_inner_dense (dense_vecOp_pi (T := fun a => dPart {a} 0) fun a => ?_)
      fun τ hτ => ?_
    · change Dense ((dPart {a} 0).domain : Set (L2Form (cube 3) 0))
      rw [dPart_eq]
      exact Feec.Models.Cube.DeRhamIdent.dense_dPart (Feec.Models.Cube.FEM.isOpen_cubeDomain 3)
        (Feec.Models.Cube.FEM.cubeDomain_subset_Q 3) {a} 0
    · rw [h1 ⟨τ, hτ⟩, hu, ← show rowsW1L (cplxE X.2.1) = X.2.1 from
        congrArg (fun Z : GState => Z.2.1) hreal]
      exact inner_rowsW1L_gd0 hE1 ⟨τ, hτ⟩
  have hw : complexQ.wave x = cplxG Y := by
    refine PiLp.ext fun i => ?_
    fin_cases i
    · refine (complexQ.wave_apply_fin3_zero x).trans ?_
      change _ = (0 : SpaceQ 0)
      rw [neg_eq_zero]
      exact (LinearPMap.apply_congr' _ _ _ rfl).trans eEa
    · refine (complexQ.wave_apply_fin3_one x).trans ?_
      have e0 : complexQ.d 0 1 ⟨(x : PiLp 2 SpaceQ) 0, x.2.1 0 1⟩ = 0 :=
        LinearPMap.map_zero _
      rw [e0, zero_sub, show (complexQ.d 1 2)† ⟨(x : PiLp 2 SpaceQ) 2, x.2.2 2 1⟩ =
        -cplxE Y.2.1 from (LinearPMap.apply_congr' _ _ _ rfl).trans eB]
      exact neg_neg (cplxE Y.2.1)
    · refine (complexQ.wave_apply_fin3_two x).trans ?_
      refine ((LinearPMap.apply_congr' _ _ _ rfl).trans eE).trans ?_
      change cplxB (gd1 ⟨X.2.1, hum⟩) = cplxB Y.2.2
      rw [hd1]
      exact congrArg (fun z => cplxB (gd1 z)) (Subtype.ext hu.symm)
  refine ⟨hd, hc, hw, ?_⟩
  rw [← realG_cplxG hY1, ← hw]
  exact isTSD_realG hred

/-! ### Solutions -/

/-- **The real part of an orbit from the constraint is a strong solution** of the system
(4.14). -/
theorem isStrongSolution_realG {x : PiLp 2 SpaceQ} (hx : x ∈ complexQ.wave.domain)
    (hc : x ∈ totalSub tsdQ) (T : ℝ) :
    IsStrongSolution gradCurlMirror (Icc 0 T) fun t => realG (complexQ.waveGroup.S t x) := by
  have hX := complexQ.isStrongSolution_waveGroup hx T
  refine ⟨realG.continuous.comp_continuousOn hX.continuousOn, fun t ht => ⟨_,
    isHodgeWave_realG (x := ⟨_, hX.mem_domain ht⟩)
      (Feec.Models.Cube.Mirror.propagatesQ hX (by simpa using hc)
        (fun _ _ => Submodule.zero_mem _) t ht),
    realG.hasFDerivAt.comp_hasDerivWithinAt t
      ((hX.hasDerivWithinAt ht).congr_deriv (add_zero _))⟩⟩

/-- **A constrained state is zero if the real parts of it and of `-i` times it vanish.** -/
theorem eq_zero_of_realG {y : PiLp 2 SpaceQ} (hc : y ∈ totalSub tsdQ) (h : realG y = 0)
    (h' : realG (-Complex.I • y) = 0) : y = 0 := by
  have h0 : ((y 0 : VQ)) = 0 := Feec.Models.Cube.Mirror.mem_tsdQ_zero.1 (hc 0)
  have hre1 : ∀ (z : PiLp 2 SpaceQ), realG z = 0 → ∀ p : Fin 3 × Fin 3,
      reL _ ((show MQ from z 1) p) = 0 := fun z hz p => by
    have hE : ∀ a, rowRe (show MQ from z 1) a = 0 := fun a =>
      (cQ _).symm.injective ((congrArg (fun Z : GState => Z.2.1 a) hz).trans (map_zero _).symm)
    rw [← rowRe_eq1, hE]; rfl
  have hre2 : ∀ (z : PiLp 2 SpaceQ), realG z = 0 → ∀ p : Fin 3 × Fin 3,
      reL _ ((show MQ from z 2) p) = 0 := fun z hz p => by
    have hB : ∀ a, rowRe2 (show MQ from z 2) a = 0 := fun a =>
      (cQ _).symm.injective ((congrArg (fun Z : GState => Z.2.2 a) hz).trans (map_zero _).symm)
    have e := rowRe2_eq2 (show MQ from z 2) p.1 p.2
    rw [hB] at e
    have hs : sg2 p.2 ≠ 0 := fun h0 => by simpa [h0] using sg2_mul_self p.2
    exact ((smul_eq_zero.1 e.symm).resolve_left hs)
  have h1 : (show MQ from y 1) = 0 := by
    refine PiLp.ext fun p => ?_
    rw [ofReal_decomp ((show MQ from y 1) p), hre1 y h p]
    have e := hre1 _ h' p
    change reL _ (-Complex.I • (show MQ from y 1) p) = 0 at e
    rw [e, map_zero, smul_zero, add_zero]
    rfl
  have h2 : (show MQ from y 2) = 0 := by
    refine PiLp.ext fun p => ?_
    rw [ofReal_decomp ((show MQ from y 2) p), hre2 y h p]
    have e := hre2 _ h' p
    change reL _ (-Complex.I • (show MQ from y 2) p) = 0 at e
    rw [e, map_zero, smul_zero, add_zero]
    rfl
  refine PiLp.ext fun i => ?_
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- A chain `x, L x, L² x, L³ x` of constrained states with `Re L x ≠ 0` gives the non-vacuity
clause. -/
theorem exists_chainG (x : complexQ.wave.domain) (hc : (x : PiLp 2 SpaceQ) ∈ totalSub tsdQ)
    (h1 : complexQ.wave x ∈ complexQ.wave.domain)
    (h2 : complexQ.wave ⟨_, h1⟩ ∈ complexQ.wave.domain) (hne : realG (complexQ.wave x) ≠ 0) :
    ∃ U₀ V₁ V₂ V₃, (U₀, V₁) ∈ gradCurlMirror ∧ (V₁, V₂) ∈ gradCurlMirror ∧
      (V₂, V₃) ∈ gradCurlMirror ∧ U₀ ∈ tsdConstraint (cube 3) ∧ V₁ ≠ 0 := by
  have hc1 := Feec.Models.Cube.Mirror.reducingSubcomplexQ.isReducing_wave.mapsTo x hc
  have hc2 := Feec.Models.Cube.Mirror.reducingSubcomplexQ.isReducing_wave.mapsTo ⟨_, h1⟩ hc1
  exact ⟨_, _, _, _, isHodgeWave_realG hc, isHodgeWave_realG (x := ⟨_, h1⟩) hc1,
    isHodgeWave_realG (x := ⟨_, h2⟩) hc2, isTSD_realG hc, hne⟩

/-- **A moving TSD solution of (4.14)**: from `cosStateQ` or `-i cosStateQ`. -/
theorem exists_mirrorG_chain : ∃ U₀ V₁ V₂ V₃, (U₀, V₁) ∈ gradCurlMirror ∧
    (V₁, V₂) ∈ gradCurlMirror ∧ (V₂, V₃) ∈ gradCurlMirror ∧ U₀ ∈ tsdConstraint (cube 3) ∧
      V₁ ≠ 0 := by
  set x : complexQ.wave.domain := ⟨_, Feec.Models.Cube.Mirror.cosStateQ_mem_domain⟩
  have hc : (x : PiLp 2 SpaceQ) ∈ totalSub tsdQ := mirror_cosStateQ_mem_tsd
  have h1 : complexQ.wave x ∈ complexQ.wave.domain := mirror_cosStateQ_wave_mem
  have h2 : complexQ.wave ⟨_, h1⟩ ∈ complexQ.wave.domain := mirror_cosStateQ_wave_wave_mem
  have hne : complexQ.wave x ≠ 0 :=
    (HilbertComplex.wave_compress Feec.Models.Cube.Mirror.eight_pos
      Feec.Models.Cube.Mirror.inner_J
      Feec.Models.Cube.Mirror.reducingSubcomplex_range).apply_ne_zero x fun h0 =>
        Feec.Models.Cube.Mirror.wave_cosState_ne ((LinearPMap.apply_congr' _ _ _
          Feec.Models.Cube.Mirror.totalJ_cosStateQ.symm).trans h0)
  by_cases hr : realG (complexQ.wave x) = 0
  · set c : ℂ := -Complex.I
    have hcx : c • (x : PiLp 2 SpaceQ) ∈ totalSub tsdQ := Submodule.smul_mem _ c hc
    have ew : complexQ.wave (c • x) = c • complexQ.wave x := LinearPMap.map_smul _ _ _
    have h1' : complexQ.wave (c • x) ∈ complexQ.wave.domain := ew ▸ Submodule.smul_mem _ c h1
    have ew2 : complexQ.wave ⟨_, h1'⟩ = c • complexQ.wave ⟨_, h1⟩ :=
      (LinearPMap.apply_congr' _ _ (Submodule.smul_mem _ c h1) ew).trans
        (LinearPMap.map_smul _ c ⟨_, h1⟩)
    have h2' : complexQ.wave ⟨_, h1'⟩ ∈ complexQ.wave.domain := ew2 ▸ Submodule.smul_mem _ c h2
    refine exists_chainG (c • x) hcx h1' h2' fun h0 => hne ?_
    have hc1 := Feec.Models.Cube.Mirror.reducingSubcomplexQ.isReducing_wave.mapsTo x hc
    exact eq_zero_of_realG hc1 hr (by rw [← ew]; exact h0)
  · exact exists_chainG x hc h1 h2 hr

/-- **The mirror boundary conditions keep TSD for the system (4.14)** (the first conjunct of the
mirror clause of `FEEC.tsd_boundary_conditions`). -/
theorem mirror_gradCurl_of : MirrorVerdict gradCurlMirror (tsdConstraint (cube 3)) where
  unique _ _ _ hU hU' h0 := IsHodgeWave.isStrongSolution_unique hU hU' h0
  exists_solution U₀ V h hT T := by
    obtain ⟨hd, hc, -, -⟩ := forwardG h hT
    exact ⟨_, by simpa using realG_cplxG hT.1, isStrongSolution_realG hd hc T⟩
  propagates T U hU hT t ht := by
    obtain ⟨V, hV, -⟩ := hU.2 0 (left_mem_Icc.2 (ht.1.trans ht.2))
    obtain ⟨hd, hc, -, -⟩ := forwardG hV hT
    have e := IsHodgeWave.isStrongSolution_unique hU (isStrongSolution_realG hd hc T)
      (by simpa using (realG_cplxG hT.1).symm) ht
    rw [e]
    exact isTSD_realG (Feec.Models.Cube.Mirror.propagatesQ
      (complexQ.isStrongSolution_waveGroup hd T) (by simpa using hc)
      (fun _ _ => Submodule.zero_mem _) t ht)
  moving := exists_mirrorG_chain

end FEEC
