module

public import Solution.MirrorState

/-!
# States of the challenge as constrained states of `Feec`'s mirror complex

The complexification `cplx X = (0, E, (0, B))` of a state `X = (0, u, 0, ρ)` (rows of `E` the
`uₐ`, rows of `⋆B` the `ρₐ`). For `L X = Y` (the challenge's operator), `E` lies in the domain of
the second operator `(S₁, curl)` (`ofRealRows_mem`) and `(0, B)` in the domain of its adjoint,
with `-d₁† (0, B) = Y_u` (`mem_adjoint_cplx`): the pairing with a complex field splits into real
and imaginary parts (`ofReal_rows_decomp`), each a real field of the domain, on which it is the
challenge's Green identity. The fields of a TSD state are complex TSD fields (`tsd_cplx_E`,
`tsd_cplx_B`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate LinearPMap
open Set MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec Feec.Domain Feec.Models.BoundedDomain
open Feec.Models.Cube.FEM (cubeDomain cubeDomain_eq_Q)
open Feec.Models.Cube.Geometry (Q)
open Feec.Models.Cube.RowWise (ofRealL reL ofRealF ofRealF_apply inner_ofRealL reL_ofRealL
  coeFn_ofRealL coeFn_reL)
open Feec.Models.Cube.MirrorWeakSymmetry
open Feec.Models.Cube.Mirror (MQ)
open Feec.Models.Cube.MirrorBGG (SpaceQ complexQ tsdQ W2Q)
open Feec.HilbertComplex (totalSub)

/-! ### Pairings of real rows -/

theorem inner_ofRealRows_ofRealRows (v w : Fin 3 → L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ))) :
    ⟪ofRealRows v, ofRealRows w⟫_ℂ = ((∑ a, ⟪v a, w a⟫_ℝ : ℝ) : ℂ) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [PiLp.inner_apply (v a), Complex.ofReal_sum,
    ← Fintype.sum_equiv (κ := formIdx 3 ((1 : ℕ) : ℤ)) eq1
      (fun b => ((⟪v a (eq1 b), w a (eq1 b)⟫_ℝ : ℝ) : ℂ)) _ fun _ => rfl]
  exact Finset.sum_congr rfl fun b _ => inner_ofRealL _ _

theorem inner_ofRealRows2_ofRealRows2
    (v w : Fin 3 → L2F ℝ (Q (Fin 3)) (formIdx 3 ((2 : ℕ) : ℤ))) :
    ⟪ofRealRows2 v, ofRealRows2 w⟫_ℂ = ((∑ a, ⟪v a, w a⟫_ℝ : ℝ) : ℂ) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [PiLp.inner_apply (v a), Complex.ofReal_sum,
    ← Fintype.sum_equiv (κ := formIdx 3 ((2 : ℕ) : ℤ)) eq2
      (fun i => ((⟪v a (eq2 i), w a (eq2 i)⟫_ℝ : ℝ) : ℂ)) _ fun _ => rfl]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ⟪(sg2 i : ℂ) • ofRealL _ (v a (eq2 i)), (sg2 i : ℂ) • ofRealL _ (w a (eq2 i))⟫_ℂ = _
  rw [inner_smul_left, inner_smul_right, inner_ofRealL, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, sg2_mul_self, Complex.ofReal_one, one_mul]

theorem rowRe_ofRealRows (v : Fin 3 → L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ))) (a : Fin 3) :
    rowRe (ofRealRows v) a = v a := by
  refine PiLp.ext fun s => ?_
  obtain ⟨b, rfl⟩ := eq1.surjective s
  rw [rowRe_eq1]
  exact reL_ofRealL _

theorem rowRe2_ofRealRows2 (w : Fin 3 → L2F ℝ (Q (Fin 3)) (formIdx 3 ((2 : ℕ) : ℤ))) (a : Fin 3) :
    rowRe2 (ofRealRows2 w) a = w a := by
  refine PiLp.ext fun s => ?_
  obtain ⟨i, rfl⟩ := eq2.surjective s
  rw [rowRe2_eq2]
  change sg2 i • reL _ ((sg2 i : ℂ) • ofRealL _ (w a (eq2 i))) = _
  rw [← real_smul_Lp, (reL _).map_smul, reL_ofRealL, smul_smul, sg2_mul_self, one_smul]

/-- **A complex function is the sum of its real and imaginary parts**:
`f = Re f + i Re(-i f)`. -/
theorem ofReal_decomp {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℂ 2 μ) :
    f = ofRealL μ (reL μ f) + Complex.I • ofRealL μ (reL μ (-Complex.I • f)) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (ofRealL μ (reL μ f))
      (Complex.I • ofRealL μ (reL μ (-Complex.I • f))), coeFn_ofRealL (reL μ f), coeFn_reL f,
    Lp.coeFn_smul Complex.I (ofRealL μ (reL μ (-Complex.I • f))),
    coeFn_ofRealL (reL μ (-Complex.I • f)), coeFn_reL (-Complex.I • f),
    Lp.coeFn_smul (-Complex.I) f] with x h1 h2 h3 h4 h5 h6 h7
  rw [h1, Pi.add_apply, h2, h3, h4, Pi.smul_apply, h5, h6, h7, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul]
  apply Complex.ext <;> simp

theorem ofRealRows_apply (v : Fin 3 → L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ)))
    (p : Fin 3 × Fin 3) :
    ofRealRows v p = ofRealL _ (v p.1 (eq1 p.2)) := rfl

/-- **A complex matrix field is its real rows plus `i` times the real rows of `-i E`.** -/
theorem ofReal_rows_decomp (Z : MQ) :
    Z = ofRealRows (rowRe Z) + Complex.I • ofRealRows (rowRe (-Complex.I • Z)) := by
  refine PiLp.ext fun p => ?_
  rw [PiLp.add_apply, PiLp.smul_apply, ofRealRows_apply, ofRealRows_apply, rowRe_eq1, rowRe_eq1]
  exact ofReal_decomp (Z p)

/-! ### The complexification -/

/-- The electric field `E` of a state, rows `uₐ`, as a complex matrix field on `Q`. -/
def cplxE (X : MState) : MQ := ofRealRows fun a => cQ _ (X.2.1 a)

/-- The magnetic field `B` of a state, rows `⋆ρₐ`, as a complex matrix field on `Q`. -/
def cplxB (X : MState) : MQ := ofRealRows2 fun a => cQ _ (X.2.2.2 a)

/-- **The complexification** `(0, E, (0, B))` of a state. -/
def cplx (X : MState) : PiLp 2 SpaceQ :=
  ShortHilbertComplex.mk3 0 (cplxE X) (WithLp.toLp 2 (0, cplxB X))

theorem realL_cplx {X : MState} (h0 : X.1 = 0) (hM : X.2.2.1 = 0) : realL (cplx X) = X := by
  obtain ⟨σ, u, M, ρ⟩ := X
  simp only at h0 hM
  subst h0 hM
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
  · refine PiLp.ext fun a => ?_
    change (cQ _).symm (rowRe (cplxE _) a) = u a
    rw [cplxE, rowRe_ofRealRows]
    exact LinearIsometryEquiv.symm_apply_apply _ _
  · refine PiLp.ext fun a => ?_
    change (cQ _).symm (rowRe2 (cplxB _) a) = ρ a
    rw [cplxB, rowRe2_ofRealRows2]
    exact LinearIsometryEquiv.symm_apply_apply _ _

/-- The rows of a field of `D((S₁, curl))` lie in the domain of `d̃¹`. -/
theorem rowsW1L_mem' (Z : (complexQ.d 1 2).domain) :
    rowsW1L (show MQ from Z.1) ∈ mirrorData.dt1.domain := fun a => by
  change _ ∈ (dPart {a} 1).domain
  rw [dPart_eq]
  exact (rowsBU_mem Z a).1

/-- `E` of a state of `D(d̃¹)` lies in the domain of `(S₁, curl)`, with `curl E` the rows of
`d̃u`. -/
theorem cplxE_mem (X : MState) (hu : X.2.1 ∈ mirrorData.dt1.domain) :
    ∃ h : cplxE X ∈ (complexQ.d 1 2).domain, (complexQ.d 1 2 ⟨_, h⟩ : W2Q) = WithLp.toLp 2
      (Feec.Models.Cube.MirrorBGG.axialQ (cplxE X),
        ofRealRows2 fun a => cQ _ (mirrorData.dt1 ⟨X.2.1, hu⟩ a)) := by
  have hc : ∀ a, X.2.1 a ∈ (BD1 a).domain := fun a => by
    have h := hu a
    change _ ∈ (dPart {a} 1).domain at h
    rw [dPart_eq] at h
    exact h
  have hv : ∀ a, cQ _ (X.2.1 a) ∈ (Feec.Models.Cube.DeRhamIdent.dPart (Q (Fin 3)) {a}
      ((1 : ℕ) : ℤ)).domain := fun a => (dPart_Q_of_cube ⟨_, hc a⟩).1
  obtain ⟨h, e⟩ := ofRealRows_mem _ hv
  refine ⟨h, e.trans ?_⟩
  congr 3
  funext a
  exact (dPart_Q_of_cube ⟨_, hc a⟩).2.trans (congrArg (cQ _) (dPart_apply_eq ⟨_, hu a⟩).symm)

/-- **`(0, B)` lies in the domain of `d₁†`, with `-d₁† (0, B) = E_Y`**, when `L X = Y` with
`σ = 0` and `M = 0`. -/
theorem mem_adjoint_cplx {X Y : MState} (h : mirrorData.IsWave X Y) (h0 : X.1 = 0)
    (hM : X.2.2.1 = 0) :
    ∃ hB : (WithLp.toLp 2 (0, cplxB X) : W2Q) ∈ ((complexQ.d 1 2)†).domain,
      (complexQ.d 1 2)† ⟨_, hB⟩ = -cplxE Y := by
  obtain ⟨σ, φ, u, hσ, hu, hc, -, h2, -, -⟩ := h
  have hσ0 : σ = 0 := Subtype.ext (hσ.trans h0)
  rw [hσ0, LinearPMap.map_zero] at hc
  have hφ : φ = 0 := Subtype.ext (wedge_zero_injective hc.symm)
  have key : ∀ r : mirrorData.dt1.domain,
      ⟪Y.2.1, (r : L2Vec (cube 3) 1)⟫ = -⟪X.2.2.2, mirrorData.dt1 r⟫ := by
    intro r
    have e := h2 r
    rw [hφ, LinearPMap.map_zero, hM, inner_zero_left, inner_zero_left] at e
    linarith
  have hpair : ∀ Z : (complexQ.d 1 2).domain,
      ⟪(WithLp.toLp 2 (0, cplxB X) : W2Q), (complexQ.d 1 2 Z : W2Q)⟫_ℂ =
        ⟪cplxB X, (WithLp.ofLp (complexQ.d 1 2 Z : W2Q)).2⟫_ℂ := fun Z => by
    erw [WithLp.prod_inner_apply]
    rw [WithLp.ofLp_toLp, inner_zero_left, zero_add]
  have hre : ∀ Z : (complexQ.d 1 2).domain, RCLike.re ⟪-cplxE Y, (show MQ from Z.1)⟫_ℂ =
      RCLike.re ⟪(WithLp.toLp 2 (0, cplxB X) : W2Q), (complexQ.d 1 2 Z : W2Q)⟫_ℂ := by
    intro Z
    set r : mirrorData.dt1.domain := ⟨_, rowsW1L_mem' Z⟩
    have e3 : ∀ a, ⟪rowRe2 (WithLp.ofLp (complexQ.d 1 2 Z : W2Q)).2 a, cQ _ (X.2.2.2 a)⟫_ℝ =
        ⟪mirrorData.dt1 r a, X.2.2.2 a⟫_ℝ := fun a => by
      obtain ⟨hm, em⟩ := rowRe_mem Z a
      have hg := (Feec.Models.Cube.DeRhamIdent.dPart (Q (Fin 3)) {a} ((1 : ℕ) : ℤ)).mem_graph
        ⟨_, hm⟩
      obtain ⟨hx, ex⟩ := dPart_cube_of_Q hg
      have hi := (cQ (formIdx 3 ((2 : ℕ) : ℤ))).inner_map_map
        ((cQ _).symm (Feec.Models.Cube.DeRhamIdent.dPart (Q (Fin 3)) {a} ((1 : ℕ) : ℤ) ⟨_, hm⟩))
        (X.2.2.2 a)
      rw [LinearIsometryEquiv.apply_symm_apply] at hi
      rw [← em]
      exact hi.trans (congrArg (⟪·, X.2.2.2 a⟫_ℝ)
        (ex.symm.trans (dPart_apply_eq ⟨_, r.2 a⟩).symm))
    have e4 : ∀ a, ⟪rowRe (show MQ from Z.1) a, cQ _ (Y.2.1 a)⟫_ℝ =
        ⟪(r : L2Vec (cube 3) 1) a, Y.2.1 a⟫_ℝ := fun a => by
      have hi := (cQ (formIdx 3 ((1 : ℕ) : ℤ))).inner_map_map
        ((cQ _).symm (rowRe (show MQ from Z.1) a)) (Y.2.1 a)
      rw [LinearIsometryEquiv.apply_symm_apply] at hi
      exact hi
    rw [inner_neg_left, map_neg, ← inner_conj_symm, RCLike.conj_re, cplxE,
      re_inner_ofRealRows, hpair, ← inner_conj_symm, RCLike.conj_re, cplxB, re_inner_ofRealRows2]
    rw [Finset.sum_congr rfl fun a _ => e3 a, Finset.sum_congr rfl fun a _ => e4 a,
      ← PiLp.inner_apply, ← PiLp.inner_apply, real_inner_comm, key r, neg_neg, real_inner_comm]
  have hw : ∀ Z : (complexQ.d 1 2).domain, ⟪-cplxE Y, (show MQ from Z.1)⟫_ℂ =
      ⟪(WithLp.toLp 2 (0, cplxB X) : W2Q), (complexQ.d 1 2 Z : W2Q)⟫_ℂ := by
    intro Z
    rw [hpair]
    have hr := hre Z
    rw [hpair] at hr
    have hi := hre (-Complex.I • Z)
    rw [hpair] at hi
    have e1 : (show MQ from (-Complex.I • Z).1) = -Complex.I • (show MQ from Z.1) := rfl
    have e2 : (WithLp.ofLp (complexQ.d 1 2 (-Complex.I • Z) : W2Q)).2 =
        -Complex.I • (WithLp.ofLp (complexQ.d 1 2 Z : W2Q)).2 := by
      rw [LinearPMap.map_smul]; rfl
    rw [e1, e2, inner_smul_right, inner_smul_right] at hi
    refine Complex.ext hr ?_
    simpa [Complex.mul_re] using hi
  have hB := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, hw⟩
  exact ⟨hB, LinearPMap.adjoint_apply_eq (complexQ.dense 1 2) ⟨_, hB⟩ hw⟩

/-! ### The Gauss component -/

theorem wedge_zero_apply {Ω : Set (Fin 3 → ℝ)} (φ : L2Vec Ω 0) (a : Fin 3) :
    wedge Ω 0 φ (ix1 a) = φ a ⟨∅, by simp⟩ := by
  simp only [wedge_eq]
  change Feec.FiniteElement.wsL2 0 φ (ix1 a) = _
  rw [Feec.FiniteElement.wsL2_apply, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single ⟨∅, by simp⟩]
    · rw [wsCoeff_eq]
      simp [ix1, f1, sgn, Finset.filter_singleton]
    · intro r _ hr
      exact absurd (Subtype.ext (Finset.card_eq_zero.1 (by have := r.2; omega))) hr
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [wsCoeff_eq]
    simp [ix1, f1, hb]
  · simp

/-- **Test functions `τ` lie in `Γ`** for the mirror data: `dτ = S⁰ψ`, `ψ = (∂ₐτ)ₐ` (the bottom
`0`-forms of compact support lie in every `H_{a}Λ⁰`). -/
theorem exists_gamma (φ : formIdx 3 0 → R3 → ℝ) (hφ : IsTestField (cube 3) φ) :
    ∃ (τ : mirrorData.d0.domain) (ψ : mirrorData.dt0.domain),
      (τ : L2Form (cube 3) 0) = testField hφ ∧ mirrorData.d0 τ = mirrorData.S0 ψ := by
  have hΩ := Feec.Models.Cube.FEM.isOpen_cubeDomain 3
  set G := testField ((extDerivOp ℝ 3 0).isTestField_apply hφ)
  have hm := (extDerivOp ℝ 3 0).testField_mem_minimal_domain hΩ hφ
  have hM := ((extDerivOp ℝ 3 0).minimal_le_maximal hΩ).1 hm
  have hτ : testField hφ ∈ (dMax (cube 3) 0).domain := by rw [dMax_eq]; exact hM
  have hψ : ∀ a : Fin 3, IsTestField (cube 3)
      (fun _ : formIdx 3 0 => (extDerivOp ℝ 3 0).apply φ (ix1 a)) := fun a _ =>
    (extDerivOp ℝ 3 0).isTestField_apply hφ (ix1 a)
  set ψ : L2Vec (cube 3) 0 := WithLp.toLp 2 fun a => testField (hψ a)
  have hψm : ψ ∈ mirrorData.dt0.domain := fun a => by
    change testField (hψ a) ∈ (dPart {a} 0).domain
    rw [dPart_eq]
    exact (Feec.Models.Cube.DeRhamIdent.minimal_le_dPart hΩ
      (Feec.Models.Cube.FEM.cubeDomain_subset_Q 3) {a} 0).1
      ((extDerivOp ℝ 3 0).testField_mem_minimal_domain hΩ (hψ a))
  refine ⟨⟨_, hτ⟩, ⟨ψ, hψm⟩, rfl, ?_⟩
  have e1 : dMax (cube 3) 0 ⟨_, hτ⟩ = G :=
    (LinearPMap.apply_of_eq' (dMax_eq (cube 3) 0) ⟨_, hτ⟩).trans
      ((((extDerivOp ℝ 3 0).minimal_le_maximal hΩ).2 (x := ⟨_, hm⟩) (y := ⟨_, hM⟩)
        rfl).symm.trans ((extDerivOp ℝ 3 0).minimal_testField hΩ hφ))
  change dMax (cube 3) 0 ⟨_, hτ⟩ = wedge (cube 3) 0 ψ
  rw [e1]
  refine PiLp.ext fun s => ?_
  obtain ⟨b, rfl⟩ := ix1.surjective s
  rw [wedge_zero_apply]
  rfl

/-- **The Gauss component of `L X` vanishes** when `u ⊥ d̃ψ` on `Γ`. -/
theorem fst_eq_zero_of_isWave {X Y : MState} (h : mirrorData.IsWave X Y)
    (hg : ∀ (τ : mirrorData.d0.domain) (ψ : mirrorData.dt0.domain),
      mirrorData.d0 τ = mirrorData.S0 ψ → ⟪X.2.1, mirrorData.dt0 ψ⟫ = 0) : Y.1 = 0 := by
  obtain ⟨σ, φ, u, -, hu, -, h1, -⟩ := h
  refine L2F.eq_zero_of_forall_inner_testField (Feec.Models.Cube.FEM.isOpen_cubeDomain 3) _
    fun φ' hφ' => ?_
  obtain ⟨τ, ψ, hτ, hτψ⟩ := exists_gamma φ' hφ'
  have e := h1 τ ψ hτψ
  rw [hτ, hu, hg τ ψ hτψ] at e
  exact e

end FEEC
