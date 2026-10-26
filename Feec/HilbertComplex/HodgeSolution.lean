module

public import Feec.HilbertComplex.Mixed
public import Feec.HilbertComplex.Compactness
public import Feec.HilbertComplex.HodgeLaplacian
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The solution operator of the Hodge Laplacian

Let `H` be a Hilbert complex and `i → j → k` two consecutive arrows with closed range at `j` and
`k`. The mixed Hodge Laplacian at `j` is well posed (`Feec.HilbertComplex.existsUnique_mixed`);
its solution `(σ, u, p)` depends linearly and boundedly on the data `f ∈ Wʲ`. The **solution
operator** `K = solutionOp : Wʲ → Wʲ`, `f ↦ u`, is the inverse of the Hodge Laplacian on the
orthogonal complement of the harmonic forms, extended by zero on `ℌʲ`:

* `K f ⊥ ℌʲ`, `K = 0` on `ℌʲ`;
* `K f ∈ D(d) ∩ D(d†)`, `d K f ∈ D(d†)`, `d† K f ∈ D(d)` and `(d d† + d† d) K f = f - P_ℌ f`;
  `K f` is the unique such element orthogonal to `ℌʲ` (`eq_solutionOp`);
* `K` is self-adjoint and positive, `⟪K f, g⟫ = ⟪d† K f, d† K g⟫ + ⟪d K f, d K g⟫`;
* for any Poincaré constant `c_P ≥ 0` of `d i j` and `d j k`: `‖K f‖ ≤ c_P² ‖f‖`,
  `‖d K f‖² + ‖d† K f‖² ≤ c_P² ‖f‖²`, and
  `‖d d† K f‖² + ‖d† d K f‖² ≤ ‖f‖²` (so each is `≤ ‖f‖`);
* `K` commutes with `d` and `d†`: `d K f = K (d f)` on `D(d)` and `d† K f = K (d† f)` on
  `D(d†)`, with the solution operators at the neighbouring indices;
* `K` is compact under the compactness property at `j`;
* on a finite window, `(Δ x) j = (d d† + d† d) (x j)` for `x ∈ D(Δ)`, and
  `x = Pi.single j (K f) ∈ D(Δ)` has `(Δ x) j = f - P_ℌ f`.

## Main definitions

* `HilbertComplex.mixedSolution`: the solution map `f ↦ (σ, u, p)` of the mixed problem.
* `HilbertComplex.solutionOp`: the solution operator `K`; `HilbertComplex.solutionSigma = d† K`.

## Main results

* `solutionOp_mem_orthogonal_harmonic`.
* `hodgeLaplacian_solutionOp`, `eq_solutionOp`: the strong form and uniqueness.
* `inner_solutionOp_left`.
* `norm_solutionOp_le`, `norm_sq_solutionSigma_add_norm_sq_d_le`, `norm_solutionSigma_le`,
  `norm_d_solutionOp_le`, `norm_sq_d_solutionSigma_add_norm_sq_adjoint_d_le`,
  `norm_d_solutionSigma_add_norm_adjoint_d_le`: the a priori bounds of [AFW2010], §3.2.
* `d_solutionOp`, `solutionSigma_eq_solutionOp`: `d K = K d` and `d† K = K d†`.
* `d_solutionSigma` (`d d† K f = P_𝔅 f`), `solutionSigma_mem_orthogonal_cycles`,
  `eq_solutionSigma_of_d_eq` (`d† K` inverts `d` from `𝔷ᗮ` onto `𝔅`), `solutionOp_mem_boundaries`,
  `solutionOp_mem_orthogonal_cycles`, `adjoint_d_solutionOp_of_mem_orthogonal`,
  `norm_sq_eq_re_inner_solutionOp_d`: `K` on `𝔅` and `𝔷ᗮ` (used by the duality arguments of
  [AFW2010], §3.5).
* `isCompactOperator_solutionOp`.
* `hodgeLaplacian_apply_of_rel`, `single_mem_hodgeLaplacian_domain`,
  `hodgeLaplacian_apply_of_apply_eq_solutionOp`, `hodgeLaplacian_single_solutionOp`: `K` and the
  window Hodge Laplacian `Δ = -L²` of `Feec.HilbertComplex.HodgeLaplacian`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.2 (the Hodge Laplacian, its solution operator `K` and the bounds (3.11))
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Thm 4.9, Thm 4.10 (well-posedness
  of the Hodge Laplacian and the solution operator)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
  (the Hodge Laplacian in mixed form)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open LinearPMap Feec.Variational

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### The solution map -/

/-- The data map `f ↦ F_f = ⟪·, f⟫`, as a bounded linear map into the antidual. -/
def mixedRHSL (i j : ι) : W j →L[𝕜] (H.MixedSpace i j →L⋆[𝕜] 𝕜) :=
  LinearMap.mkContinuous
    { toFun := H.mixedRHS i j
      map_add' := fun f g => ContinuousLinearMap.ext fun y => by
        simp only [mixedRHS_apply, _root_.add_apply, inner_add_right]
      map_smul' := fun a f => ContinuousLinearMap.ext fun y => by
        simp only [mixedRHS_apply, _root_.smul_apply, inner_smul_right,
          RingHom.id_apply, smul_eq_mul] }
    1 fun f => by rw [one_mul]; exact H.norm_mixedRHS_le f

variable {i j k : ι}

/-- A common Poincaré constant `c_P ≥ 1` for `d i j` and `d j k`, from closed range at `j`, `k`. -/
theorem exists_poincare_pair (hij : c.Rel i j) (hjk : c.Rel j k) (hj : H.ClosedRangeAt j)
    (hk : H.ClosedRangeAt k) :
    ∃ cP : ℝ, 1 ≤ cP ∧
      (∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖) ∧
      (∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖) := by
  obtain ⟨c₁, hc₁, h₁⟩ := H.exists_poincare_of_closedRangeAt hij hj
  obtain ⟨c₂, -, h₂⟩ := H.exists_poincare_of_closedRangeAt hjk hk
  refine ⟨max c₁ c₂, hc₁.trans (le_max_left _ _), fun z hz => (h₁ z hz).trans ?_,
    fun z hz => (h₂ z hz).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- The mixed form is an isomorphism onto the antidual (closed range at `j` and `k`). -/
def mixedFormEquiv (hij : c.Rel i j) (hjk : c.Rel j k) (hj : H.ClosedRangeAt j)
    (hk : H.ClosedRangeAt k) : H.MixedSpace i j ≃L[𝕜] (H.MixedSpace i j →L⋆[𝕜] 𝕜) :=
  have h := H.exists_poincare_pair hij hjk hj hk
  equivOfInfSup (H.infSup_mixedForm hij hjk h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2)
    (H.separatingRight_mixedForm hij hjk h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2)

@[simp] theorem mixedFormEquiv_apply (hij : c.Rel i j) (hjk : c.Rel j k) (hj : H.ClosedRangeAt j)
    (hk : H.ClosedRangeAt k) (x : H.MixedSpace i j) :
    H.mixedFormEquiv hij hjk hj hk x = H.mixedForm i j k x := rfl

/-- **The solution map of the mixed Hodge Laplacian**, `f ↦ (σ, u, p)`. -/
def mixedSolution (hij : c.Rel i j) (hjk : c.Rel j k) (hj : H.ClosedRangeAt j)
    (hk : H.ClosedRangeAt k) : W j →L[𝕜] H.MixedSpace i j :=
  ((H.mixedFormEquiv hij hjk hj hk).symm : (H.MixedSpace i j →L⋆[𝕜] 𝕜) →L[𝕜] H.MixedSpace i j).comp
    (H.mixedRHSL i j)

variable (hij : c.Rel i j) (hjk : c.Rel j k) (hj : H.ClosedRangeAt j) (hk : H.ClosedRangeAt k)

theorem mixedForm_mixedSolution (f : W j) :
    H.mixedForm i j k (H.mixedSolution hij hjk hj hk f) = H.mixedRHS i j f := by
  rw [← mixedFormEquiv_apply H hij hjk hj hk]
  exact (H.mixedFormEquiv hij hjk hj hk).apply_symm_apply _

theorem isMixedSolution_mixedSolution (f : W j) :
    H.IsMixedSolution i j k f (H.mixedSolution hij hjk hj hk f).fst
      (H.mixedSolution hij hjk hj hk f).snd.fst (H.mixedSolution hij hjk hj hk f).snd.snd :=
  mixedForm_eq_mixedRHS_iff.1 (by
    rw [MixedSpace.eta]; exact H.mixedForm_mixedSolution hij hjk hj hk f)

/-- Every solution of the mixed problem is the value of the solution map. -/
theorem mixedSolution_eq {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j}
    {p : H.harmonic j} (hs : H.IsMixedSolution i j k f σ u p) :
    H.mixedSolution hij hjk hj hk f = MixedSpace.mk σ u p :=
  (H.mixedFormEquiv hij hjk hj hk).injective (by
    rw [mixedFormEquiv_apply, mixedFormEquiv_apply, H.mixedForm_mixedSolution hij hjk hj hk,
      mixedForm_eq_mixedRHS_iff.2 hs])

/-! ### The solution operator -/

/-- The solution operator as a map into the domain space `Vʲ`. -/
def solutionOpV : W j →L[𝕜] H.domainSpace j :=
  (WithLp.fstL 2 𝕜 _ _).comp ((WithLp.sndL 2 𝕜 _ _).comp (H.mixedSolution hij hjk hj hk))

/-- **The solution operator `K` of the Hodge Laplacian** at `j`: `K f = u`, where `(σ, u, p)`
solves the mixed problem with data `f`. See [AFW2010], §3.2; [Arnold2018], Thm 4.10. -/
def solutionOp : W j →L[𝕜] W j := (H.domainIncl j).comp (H.solutionOpV hij hjk hj hk)

/-- `d† K`, the `σ` component of the mixed solution, as a map into `Vⁱ`. -/
def solutionSigmaV : W j →L[𝕜] H.domainSpace i :=
  (WithLp.fstL 2 𝕜 _ _).comp (H.mixedSolution hij hjk hj hk)

/-- `σ = d† K f`, as a map into `Wⁱ`. -/
def solutionSigma : W j →L[𝕜] W i := (H.domainIncl i).comp (H.solutionSigmaV hij hjk hj hk)

theorem solutionOp_apply (f : W j) :
    H.solutionOp hij hjk hj hk f = H.domainIncl j (H.solutionOpV hij hjk hj hk f) := rfl

/-- `‖K f‖` is at most the norm of the mixed solution. -/
theorem norm_solutionOp_le_norm_mixedSolution (f : W j) :
    ‖H.solutionOp hij hjk hj hk f‖ ≤ ‖H.mixedSolution hij hjk hj hk f‖ :=
  (H.norm_domainIncl_le j _).trans
    ((WithLp.norm_fst_le (x := _)).trans (WithLp.norm_snd_le (x := _)))

/-- The mixed solution is `(d† K f, K f, P_ℌ f)`. -/
theorem harmonic_mixedSolution (f : W j) :
    ((H.mixedSolution hij hjk hj hk f).snd.snd : W j) = (H.harmonic j).starProjection f :=
  ((H.isMixedSolution_mixedSolution hij hjk hj hk f).harmonic_eq hij).symm

theorem isMixedSolution_solutionOp (f : W j) :
    H.IsMixedSolution i j k f (H.solutionSigmaV hij hjk hj hk f) (H.solutionOpV hij hjk hj hk f)
      (H.mixedSolution hij hjk hj hk f).snd.snd :=
  H.isMixedSolution_mixedSolution hij hjk hj hk f

/-- **`K f ⊥ ℌʲ`.** -/
theorem inner_harmonic_solutionOp (f : W j) {q : W j} (hq : q ∈ H.harmonic j) :
    ⟪q, H.solutionOp hij hjk hj hk f⟫ = 0 :=
  (H.isMixedSolution_solutionOp hij hjk hj hk f).harm q hq

theorem solutionOp_mem_orthogonal_harmonic (f : W j) :
    H.solutionOp hij hjk hj hk f ∈ (H.harmonic j)ᗮ :=
  (Submodule.mem_orthogonal _ _).2 fun _ hq => H.inner_harmonic_solutionOp hij hjk hj hk f hq

/-! ### Domains and the strong form -/

/-- `K f ∈ D(d j k)`. -/
theorem solutionOp_mem_domain (f : W j) : H.solutionOp hij hjk hj hk f ∈ (H.d j k).domain :=
  H.domain_next_le j k (H.domainIncl_mem j _)

/-- `d† K f = σ ∈ D(d i j)`. -/
theorem solutionSigma_mem_domain (f : W j) :
    H.solutionSigma hij hjk hj hk f ∈ (H.d i j).domain :=
  H.domain_next_le i j (H.domainIncl_mem i _)

/-- `K f ∈ D((d i j)†)`. -/
theorem solutionOp_mem_adjoint_domain (f : W j) :
    H.solutionOp hij hjk hj hk f ∈ ((H.d i j)†).domain :=
  ((H.isMixedSolution_solutionOp hij hjk hj hk f).mem_adjoint_domain hij).1

/-- **`d† K f = σ`**: the first unknown of the mixed problem is `d† u`. -/
theorem adjoint_solutionOp (f : W j) (h : H.solutionOp hij hjk hj hk f ∈ ((H.d i j)†).domain) :
    (H.d i j)† ⟨_, h⟩ = H.solutionSigma hij hjk hj hk f :=
  ((H.isMixedSolution_solutionOp hij hjk hj hk f).mem_adjoint_domain hij).2

/-- `d K f ∈ D((d j k)†)`. -/
theorem d_solutionOp_mem_adjoint_domain (f : W j) :
    H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f)) ∈ ((H.d j k)†).domain :=
  ((H.isMixedSolution_solutionOp hij hjk hj hk f).mem_adjoint_domain_d hjk).1

/-- **`d† d K f = f - P_ℌ f - d σ`.** -/
theorem adjoint_d_solutionOp (f : W j)
    (h : H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f)) ∈ ((H.d j k)†).domain) :
    (H.d j k)† ⟨_, h⟩ = f - (H.harmonic j).starProjection f -
      H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk f)) := by
  rw [((H.isMixedSolution_solutionOp hij hjk hj hk f).mem_adjoint_domain_d hjk).2,
    H.harmonic_mixedSolution]

/-- **The strong form**: `K f ∈ D(d) ∩ D(d†)`, `d K f ∈ D(d†)`, `d† K f ∈ D(d)` and
`(d d† + d† d) K f = f - P_ℌ f`. See [AFW2010], §3.2; [Arnold2018], Thm 4.10. -/
theorem hodgeLaplacian_solutionOp (f : W j) :
    ∃ (h₁ : H.solutionOp hij hjk hj hk f ∈ (H.d j k).domain)
      (h₂ : H.solutionOp hij hjk hj hk f ∈ ((H.d i j)†).domain)
      (h₃ : H.d j k ⟨_, h₁⟩ ∈ ((H.d j k)†).domain)
      (h₄ : ((H.d i j)† ⟨_, h₂⟩ : W i) ∈ (H.d i j).domain),
      H.d i j ⟨_, h₄⟩ + (H.d j k)† ⟨_, h₃⟩ = f - (H.harmonic j).starProjection f := by
  have h₂ := H.solutionOp_mem_adjoint_domain hij hjk hj hk f
  have e := H.adjoint_solutionOp hij hjk hj hk f h₂
  have h₄ : ((H.d i j)† ⟨_, h₂⟩ : W i) ∈ (H.d i j).domain := by
    rw [e]; exact H.solutionSigma_mem_domain hij hjk hj hk f
  have h₁ := H.solutionOp_mem_domain hij hjk hj hk f
  have h₃ : H.d j k ⟨_, h₁⟩ ∈ ((H.d j k)†).domain :=
    H.d_solutionOp_mem_adjoint_domain hij hjk hj hk f
  refine ⟨h₁, h₂, h₃, h₄, ?_⟩
  have e'' : (H.d j k)† ⟨H.d j k ⟨_, h₁⟩, h₃⟩ = f - (H.harmonic j).starProjection f -
      H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk f)) :=
    H.adjoint_d_solutionOp hij hjk hj hk f h₃
  have e' : H.d i j ⟨_, h₄⟩ = H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk f)) :=
    congrArg (H.d i j) (Subtype.ext e)
  rw [e', e'']
  abel

/-- **Uniqueness**: `K f` is the only `u ⊥ ℌʲ` in `D(d) ∩ D(d†)` with `d u ∈ D(d†)`,
`d† u ∈ D(d)` and `(d d† + d† d) u = f - P_ℌ f`. -/
theorem eq_solutionOp {f u : W j} (hu : u ∈ (H.harmonic j)ᗮ) (h₁ : u ∈ (H.d j k).domain)
    (h₂ : u ∈ ((H.d i j)†).domain) (h₃ : H.d j k ⟨u, h₁⟩ ∈ ((H.d j k)†).domain)
    (h₄ : ((H.d i j)† ⟨u, h₂⟩ : W i) ∈ (H.d i j).domain)
    (heq : H.d i j ⟨_, h₄⟩ + (H.d j k)† ⟨_, h₃⟩ = f - (H.harmonic j).starProjection f) :
    u = H.solutionOp hij hjk hj hk f := by
  set σ := H.toDomainSpace hij ⟨_, h₄⟩
  set uV := H.toDomainSpace hjk ⟨u, h₁⟩
  set p : H.harmonic j := ⟨_, Submodule.starProjection_apply_mem (H.harmonic j) f⟩
  have hs : H.IsMixedSolution i j k f σ uV p := by
    refine ⟨fun τ => ?_, fun v => ?_, fun q hq => ?_⟩
    · have e := adjoint_isFormalAdjoint (H.dense i j) ⟨u, h₂⟩ (H.domainCoord i j τ)
      rw [domainIncl_toDomainSpace, sub_eq_zero, ← inner_conj_symm]
      change starRingEnd 𝕜 ⟪(H.d i j)† ⟨u, h₂⟩, H.domainIncl i τ⟫ = _
      rw [show H.domainIncl i τ = (H.domainCoord i j τ : W i) from rfl, e, inner_conj_symm]
      rfl
    · have e := adjoint_isFormalAdjoint (H.dense j k) ⟨_, h₃⟩ (H.domainCoord j k v)
      have e2 : ⟪H.d j k (H.domainCoord j k v), H.d j k (H.domainCoord j k uV)⟫ =
          ⟪H.domainIncl j v, (H.d j k)† ⟨_, h₃⟩⟫ := by
        rw [← inner_conj_symm, ← inner_conj_symm (H.domainIncl j v),
          show H.domainIncl j v = (H.domainCoord j k v : W j) from rfl, e]
        rfl
      rw [d_domainCoord_toDomainSpace, e2, ← inner_add_right, ← inner_add_right, heq,
        sub_add_cancel]
    · exact Submodule.inner_right_of_mem_orthogonal hq hu
  have := congrArg (fun x : H.MixedSpace i j => H.domainIncl j x.snd.fst)
    (H.mixedSolution_eq hij hjk hj hk hs)
  exact this.symm

/-! ### Self-adjointness and positivity -/

/-- **The energy identity** `⟪K f, g⟫ = ⟪d† K f, d† K g⟫ + ⟪d K f, d K g⟫`. -/
theorem inner_solutionOp_left (f g : W j) :
    ⟪H.solutionOp hij hjk hj hk f, g⟫ =
      ⟪H.solutionSigma hij hjk hj hk f, H.solutionSigma hij hjk hj hk g⟫ +
        ⟪H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f)),
          H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk g))⟫ := by
  have sf := H.isMixedSolution_solutionOp hij hjk hj hk f
  have sg := H.isMixedSolution_solutionOp hij hjk hj hk g
  have e2 := sg.snd (H.solutionOpV hij hjk hj hk f)
  have e1 := sub_eq_zero.1 (sf.fst (H.solutionSigmaV hij hjk hj hk g))
  have e3 := sf.harm _ (H.mixedSolution hij hjk hj hk g).snd.snd.2
  have e1' : ⟪H.domainIncl j (H.solutionOpV hij hjk hj hk f),
      H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk g))⟫ =
      ⟪H.solutionSigma hij hjk hj hk f, H.solutionSigma hij hjk hj hk g⟫ := by
    rw [← inner_conj_symm, ← e1, inner_conj_symm]; rfl
  have e3' : ⟪H.domainIncl j (H.solutionOpV hij hjk hj hk f),
      ((H.mixedSolution hij hjk hj hk g).snd.snd : W j)⟫ = 0 := by
    rw [← inner_conj_symm, e3, _root_.map_zero]
  rw [e1', e3', add_zero] at e2
  rw [solutionOp_apply, ← e2]

/-- **`K` is self-adjoint.** -/
theorem isSymmetric_solutionOp :
    (H.solutionOp hij hjk hj hk : W j →ₗ[𝕜] W j).IsSymmetric := fun f g => by
  change ⟪H.solutionOp hij hjk hj hk f, g⟫ = ⟪f, H.solutionOp hij hjk hj hk g⟫
  rw [← inner_conj_symm f, H.inner_solutionOp_left, H.inner_solutionOp_left, _root_.map_add,
    inner_conj_symm, inner_conj_symm]

/-- `re ⟪K f, f⟫ = ‖d† K f‖² + ‖d K f‖²`. -/
theorem re_inner_solutionOp_self (f : W j) :
    RCLike.re ⟪H.solutionOp hij hjk hj hk f, f⟫ =
      ‖H.solutionSigma hij hjk hj hk f‖ ^ 2 +
        ‖H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f))‖ ^ 2 := by
  rw [H.inner_solutionOp_left, _root_.map_add, inner_self_eq_norm_sq, inner_self_eq_norm_sq]

/-! ### The a priori bounds -/

omit [∀ i, CompleteSpace (W i)] in
/-- `‖x - P_K x‖ ≤ ‖x - y‖` for `y ∈ K`. -/
theorem _root_.Submodule.norm_sub_starProjection_le_of_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] {x y : E}
    (hy : y ∈ K) : ‖x - K.starProjection x‖ ≤ ‖x - y‖ := by
  rw [← dist_eq_norm, ← dist_eq_norm, Submodule.dist_starProjection_eq_infDist]
  exact Metric.infDist_le_dist_of_mem hy

/-- **`‖d d† K f‖² + ‖d† d K f‖² ≤ ‖f‖²`** (no Poincaré constant): `d σ` and `d† d u` are the
orthogonal `𝔅` and `𝔅*` parts of `f - P_ℌ f`. -/
theorem norm_sq_d_solutionSigma_add_norm_sq_adjoint_d_le (f : W j)
    (h : H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f)) ∈ ((H.d j k)†).domain) :
    ‖H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk f))‖ ^ 2 +
      ‖(H.d j k)† ⟨_, h⟩‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [H.adjoint_d_solutionOp hij hjk hj hk f h]
  set s := H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk f))
  set P := (H.harmonic j).starProjection f
  have hs := H.isMixedSolution_solutionOp hij hjk hj hk f
  have e := hs.snd (H.domainD i j (H.solutionSigmaV hij hjk hj hk f))
  rw [domainIncl_domainD, d_domainCoord_domainD, inner_zero_left, add_zero,
    H.harmonic_mixedSolution] at e
  have hsB : s ∈ H.boundaries j := by rw [H.boundaries_eq hij]; exact ⟨_, rfl⟩
  have hsP : ⟪s, P⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hsB
    (H.mem_harmonic_iff.1 (Submodule.starProjection_apply_mem _ f)).2
  rw [hsP, add_zero] at e
  have horth : ⟪s, f - P - s⟫ = 0 := by
    rw [inner_sub_right, inner_sub_right, hsP, ← e, sub_zero, sub_self]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) s (f - P - s) horth
  rw [add_sub_cancel] at hpy
  have hle : ‖f - P‖ ≤ ‖f‖ := by
    simpa using Submodule.norm_sub_starProjection_le_of_mem (x := f) (H.harmonic j) (zero_mem _)
  nlinarith [norm_nonneg (f - P), norm_nonneg f]

theorem norm_d_solutionSigma_le (f : W j) :
    ‖H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk f))‖ ≤ ‖f‖ := by
  have := H.norm_sq_d_solutionSigma_add_norm_sq_adjoint_d_le hij hjk hj hk f
    (H.d_solutionOp_mem_adjoint_domain hij hjk hj hk f)
  nlinarith [norm_nonneg f, norm_nonneg (H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk f))),
    sq_nonneg ‖(H.d j k)† ⟨_, H.d_solutionOp_mem_adjoint_domain hij hjk hj hk f⟩‖]

theorem norm_adjoint_d_solutionOp_le (f : W j)
    (h : H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f)) ∈ ((H.d j k)†).domain) :
    ‖(H.d j k)† ⟨_, h⟩‖ ≤ ‖f‖ := by
  have := H.norm_sq_d_solutionSigma_add_norm_sq_adjoint_d_le hij hjk hj hk f h
  nlinarith [norm_nonneg f, norm_nonneg ((H.d j k)† ⟨_, h⟩),
    sq_nonneg ‖H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk f))‖]

/-- `‖d d† K f‖ + ‖d† d K f‖ ≤ 2 ‖f‖`. See [AFW2010], (3.11). -/
theorem norm_d_solutionSigma_add_norm_adjoint_d_le (f : W j)
    (h : H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f)) ∈ ((H.d j k)†).domain) :
    ‖H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk f))‖ + ‖(H.d j k)† ⟨_, h⟩‖ ≤
      2 * ‖f‖ := by
  linarith [H.norm_d_solutionSigma_le hij hjk hj hk f,
    H.norm_adjoint_d_solutionOp_le hij hjk hj hk f h]

section Poincare

variable {cP : ℝ} (hcP : 0 ≤ cP)
  (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
  (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
include hcP hPi hPj

/-- **`‖K f‖ ≤ c_P² ‖f‖`**, with `c_P` a Poincaré constant for `d i j` and `d j k`.
See [AFW2010], §3.2, (3.11). -/
theorem norm_solutionOp_le (f : W j) : ‖H.solutionOp hij hjk hj hk f‖ ≤ cP ^ 2 * ‖f‖ := by
  set u := H.solutionOp hij hjk hj hk f
  set σ := H.solutionSigma hij hjk hj hk f
  set du := H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f))
  have hs := H.isMixedSolution_solutionOp hij hjk hj hk f
  obtain ⟨b, h, w, hb, hh, hw, hu⟩ := H.exists_hodge_split hj u
  have hbz : b ∈ H.cycles j := H.boundaries_le_cycles j hb
  have hhz : h ∈ H.cycles j := H.harmonic_le_cycles j hh
  have hbw : ⟪b, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hbz hw
  have hhw : ⟪h, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hhz hw
  have hhb : ⟪h, b⟫ = 0 := Submodule.inner_left_of_mem_orthogonal hb (H.mem_harmonic_iff.1 hh).2
  have hhu : ⟪h, u⟫ = 0 := hs.harm h hh
  have h0 : h = 0 := by
    rw [hu, inner_add_right, inner_add_right, hhb, hhw, zero_add, add_zero] at hhu
    exact inner_self_eq_zero.1 hhu
  rw [h0, add_zero] at hu
  -- the `𝔷ᗮ` part
  have hu1 : u ∈ (H.d j k).domain := H.solutionOp_mem_domain hij hjk hj hk f
  have hb1 : b ∈ (H.d j k).domain := H.domain_next_le j k (H.cycles_le_domain j hbz)
  set wd : (H.d j k).domain := ⟨u, hu1⟩ - ⟨b, hb1⟩
  have hwd : (wd : W j) = w := by
    change u - b = w; rw [hu, add_sub_cancel_left]
  have hdw : H.d j k wd = du := by
    rw [LinearPMap.map_sub, H.d_eq_zero_of_mem_cycles hbz, sub_zero]; rfl
  have hw' := hPj wd (hwd ▸ hw)
  rw [hwd, hdw] at hw'
  -- the `𝔅` part
  obtain ⟨ρ, -, hρ, hρn⟩ := H.exists_poincare_preimage hij hPi hb
  have e := sub_eq_zero.1 (hs.fst (H.toDomainSpace hij ρ))
  rw [domainIncl_toDomainSpace, d_domainCoord_toDomainSpace, hρ] at e
  have hbu : ⟪b, u⟫ = (‖b‖ : 𝕜) ^ 2 := by
    rw [hu, inner_add_right, hbw, add_zero, inner_self_eq_norm_sq_to_K]
  have hb2 : ‖b‖ ^ 2 ≤ cP * ‖b‖ * ‖σ‖ := by
    have h1 : ‖⟪b, u⟫‖ ≤ ‖(ρ : W i)‖ * ‖σ‖ := by
      rw [show ⟪b, u⟫ = ⟪(ρ : W i), σ⟫ from e.symm]; exact norm_inner_le_norm _ _
    rw [hbu, norm_pow, RCLike.norm_ofReal, abs_norm] at h1
    calc ‖b‖ ^ 2 ≤ ‖(ρ : W i)‖ * ‖σ‖ := h1
      _ ≤ cP * ‖b‖ * ‖σ‖ := mul_le_mul_of_nonneg_right hρn (norm_nonneg _)
  have hbσ : ‖b‖ ≤ cP * ‖σ‖ := by
    nlinarith [norm_nonneg b, norm_nonneg σ, mul_nonneg hcP (norm_nonneg σ)]
  -- assemble
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) b w hbw
  rw [← hu] at hpy
  have hen := H.re_inner_solutionOp_self hij hjk hj hk f
  have hre : RCLike.re ⟪u, f⟫ ≤ ‖u‖ * ‖f‖ := re_inner_le_norm u f
  have hu2 : ‖u‖ ^ 2 ≤ cP ^ 2 * ‖u‖ * ‖f‖ := by
    have hw2 : ‖w‖ ^ 2 ≤ cP ^ 2 * ‖du‖ ^ 2 := by
      have := norm_nonneg w; rw [← mul_pow]; exact pow_le_pow_left₀ this hw' 2
    have hb2' : ‖b‖ ^ 2 ≤ cP ^ 2 * ‖σ‖ ^ 2 := by
      have := norm_nonneg b; rw [← mul_pow]; exact pow_le_pow_left₀ this hbσ 2
    have : ‖u‖ ^ 2 ≤ cP ^ 2 * RCLike.re ⟪u, f⟫ := by
      change ‖u‖ ^ 2 ≤ cP ^ 2 * RCLike.re ⟪H.solutionOp hij hjk hj hk f, f⟫
      rw [hen]; nlinarith
    nlinarith [sq_nonneg cP]
  nlinarith [norm_nonneg u, norm_nonneg f, sq_nonneg cP, mul_nonneg (sq_nonneg cP) (norm_nonneg f)]

/-- **`‖d† K f‖² + ‖d K f‖² ≤ c_P² ‖f‖²`.** See [AFW2010], §3.2, (3.11). -/
theorem norm_sq_solutionSigma_add_norm_sq_d_le (f : W j) :
    ‖H.solutionSigma hij hjk hj hk f‖ ^ 2 +
        ‖H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f))‖ ^ 2 ≤ cP ^ 2 * ‖f‖ ^ 2 := by
  rw [← H.re_inner_solutionOp_self]
  have h1 := re_inner_le_norm (𝕜 := 𝕜) (H.solutionOp hij hjk hj hk f) f
  have h2 := H.norm_solutionOp_le hij hjk hj hk hcP hPi hPj f
  nlinarith [norm_nonneg f]

/-- `‖d† K f‖ ≤ c_P ‖f‖`. -/
theorem norm_solutionSigma_le (f : W j) :
    ‖H.solutionSigma hij hjk hj hk f‖ ≤ cP * ‖f‖ := by
  have h := H.norm_sq_solutionSigma_add_norm_sq_d_le hij hjk hj hk hcP hPi hPj f
  have : ‖H.solutionSigma hij hjk hj hk f‖ ^ 2 ≤ (cP * ‖f‖) ^ 2 := by
    rw [mul_pow]; nlinarith [sq_nonneg ‖H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f))‖]
  exact (abs_le_of_sq_le_sq' this (mul_nonneg hcP (norm_nonneg f))).2

/-- `‖d K f‖ ≤ c_P ‖f‖`. -/
theorem norm_d_solutionOp_le (f : W j) :
    ‖H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f))‖ ≤ cP * ‖f‖ := by
  have h := H.norm_sq_solutionSigma_add_norm_sq_d_le hij hjk hj hk hcP hPi hPj f
  have : ‖H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f))‖ ^ 2 ≤ (cP * ‖f‖) ^ 2 := by
    rw [mul_pow]; nlinarith [sq_nonneg ‖H.solutionSigma hij hjk hj hk f‖]
  exact (abs_le_of_sq_le_sq' this (mul_nonneg hcP (norm_nonneg f))).2

/-- **`‖K (d τ)‖ ≤ c_P ‖τ‖`** on `D(d i j)`: `⟪K d τ, g⟫ = ⟪τ, d† K g⟫` (so `K d` extends to a
bounded operator `Wⁱ → Wʲ`, the operator `d K` at `i` of [AFW2010], §3.5). -/
theorem norm_solutionOp_d_le (τ : (H.d i j).domain) :
    ‖H.solutionOp hij hjk hj hk (H.d i j τ)‖ ≤ cP * ‖(τ : W i)‖ := by
  set v := H.solutionOp hij hjk hj hk (H.d i j τ)
  have h₂ := H.solutionOp_mem_adjoint_domain hij hjk hj hk v
  have e2 := adjoint_isFormalAdjoint (H.dense i j) ⟨_, h₂⟩ τ
  rw [H.adjoint_solutionOp hij hjk hj hk _ h₂] at e2
  have e2' : ⟪H.solutionSigma hij hjk hj hk v, (τ : W i)⟫ =
      ⟪H.solutionOp hij hjk hj hk v, (H.d i j τ : W j)⟫ := e2
  have e : ⟪v, v⟫ = ⟪(H.d i j τ : W j), H.solutionOp hij hjk hj hk v⟫ :=
    H.isSymmetric_solutionOp hij hjk hj hk _ _
  have hσ := H.norm_solutionSigma_le hij hjk hj hk hcP hPi hPj v
  have hsq : ‖v‖ ^ 2 ≤ ‖(τ : W i)‖ * (cP * ‖v‖) := by
    rw [← @inner_self_eq_norm_sq 𝕜, e, ← inner_conj_symm, RCLike.conj_re, ← e2']
    refine (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hσ (norm_nonneg _)
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith [norm_nonneg (τ : W i)]

end Poincare

/-! ### Commuting with `d` and `d†` -/

/-- Boundaries are orthogonal to harmonic forms: `P_ℌ b = 0` and `⟪q, b⟫ = 0`. -/
theorem inner_harmonic_eq_zero_of_mem_boundaries {l : ι} {q b : W l} (hq : q ∈ H.harmonic l)
    (hb : b ∈ H.boundaries l) : ⟪q, b⟫ = 0 :=
  Submodule.inner_left_of_mem_orthogonal hb (H.mem_harmonic_iff.1 hq).2

theorem mem_orthogonal_harmonic_of_mem_boundaries {l : ι} {b : W l} (hb : b ∈ H.boundaries l) :
    b ∈ (H.harmonic l)ᗮ :=
  (Submodule.mem_orthogonal _ _).2 fun _ hq => H.inner_harmonic_eq_zero_of_mem_boundaries hq hb

/-- **`K` commutes with `d`**: `d K f = K (d f)` for `f ∈ D(d j k)`, where the second `K` is the
solution operator at `k` (arrows `j → k → l`). See [AFW2010], §3.2. -/
theorem d_solutionOp {l : ι} (hkl : c.Rel k l) (hl : H.ClosedRangeAt l) {f : W j}
    (hf : f ∈ (H.d j k).domain) :
    H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f)) =
      H.solutionOp hjk hkl hk hl (H.d j k ⟨f, hf⟩) := by
  set u := H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk f))
  have huB : u ∈ H.boundaries k := by rw [H.boundaries_eq hjk]; exact ⟨_, rfl⟩
  have h₁ : u ∈ (H.d k l).domain := H.mapsTo j k l _
  have h₂ : u ∈ ((H.d j k)†).domain := H.d_solutionOp_mem_adjoint_domain hij hjk hj hk f
  have h₃ : H.d k l ⟨u, h₁⟩ ∈ ((H.d k l)†).domain := by
    rw [H.d_comp_d j k l]; exact Submodule.zero_mem _
  have eA := H.adjoint_d_solutionOp hij hjk hj hk f h₂
  set P := (H.harmonic j).starProjection f
  set s := H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk f))
  have hP : P ∈ (H.d j k).domain := H.domain_next_le j k
    (H.cycles_le_domain j (H.harmonic_le_cycles j (Submodule.starProjection_apply_mem _ f)))
  have hs : s ∈ (H.d j k).domain := H.mapsTo i j k _
  have h₄ : ((H.d j k)† ⟨u, h₂⟩ : W j) ∈ (H.d j k).domain := by
    rw [eA]; exact Submodule.sub_mem _ (Submodule.sub_mem _ hf hP) hs
  refine H.eq_solutionOp hjk hkl hk hl (H.mem_orthogonal_harmonic_of_mem_boundaries huB) h₁ h₂ h₃
    h₄ ?_
  have e1 : (⟨_, h₄⟩ : (H.d j k).domain) = ⟨f, hf⟩ - ⟨P, hP⟩ - ⟨s, hs⟩ := Subtype.ext eA
  have e2 : (⟨_, h₃⟩ : ((H.d k l)†).domain) = 0 := Subtype.ext (H.d_comp_d j k l _)
  have hdB : H.d j k ⟨f, hf⟩ ∈ H.boundaries k := by rw [H.boundaries_eq hjk]; exact ⟨_, rfl⟩
  have hP0 : (H.harmonic k).starProjection (H.d j k ⟨f, hf⟩) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).2
      (H.mem_orthogonal_harmonic_of_mem_boundaries hdB)
  rw [e1, e2, LinearPMap.map_zero, LinearPMap.map_sub, LinearPMap.map_sub, hP0,
    H.d_eq_zero_of_mem_cycles (H.harmonic_le_cycles j (Submodule.starProjection_apply_mem _ f)),
    show H.d j k ⟨s, hs⟩ = 0 from H.d_comp_d i j k _]
  simp

/-- **`K` commutes with `d†`**: `d† K f = K (d† f)` for `f ∈ D((d i j)†)`, where the second `K`
is the solution operator at `i` (arrows `h → i → j`). See [AFW2010], §3.2. -/
theorem solutionSigma_eq_solutionOp {h : ι} (hhi : c.Rel h i) (hi : H.ClosedRangeAt i) {f : W j}
    (hf : f ∈ ((H.d i j)†).domain) :
    H.solutionSigma hij hjk hj hk f = H.solutionOp hhi hij hi hj ((H.d i j)† ⟨f, hf⟩) := by
  have hK := H.solutionOp_mem_adjoint_domain hij hjk hj hk f
  have eσ := H.adjoint_solutionOp hij hjk hj hk f hK
  set σ := H.solutionSigma hij hjk hj hk f
  -- range of `(d i j)†` is orthogonal to `ℌⁱ`
  have horth : ∀ (y : ((H.d i j)†).domain), (H.d i j)† y ∈ (H.harmonic i)ᗮ := fun y =>
    (Submodule.mem_orthogonal _ _).2 fun q hq => by
      have hqd : q ∈ (H.d i j).domain := H.domain_next_le i j
        (H.cycles_le_domain i (H.harmonic_le_cycles i hq))
      have e := adjoint_isFormalAdjoint (H.dense i j) y ⟨q, hqd⟩
      rw [H.d_eq_zero_of_mem_cycles (H.harmonic_le_cycles i hq), inner_zero_right] at e
      rw [← inner_conj_symm, e, _root_.map_zero]
  have hu : σ ∈ (H.harmonic i)ᗮ := eσ ▸ horth _
  have h₁ : σ ∈ (H.d i j).domain := H.solutionSigma_mem_domain hij hjk hj hk f
  have h₂ : σ ∈ ((H.d h i)†).domain := eσ ▸ H.adjoint_mapsTo h i j ⟨_, hK⟩
  have hz : (H.d h i)† ⟨σ, h₂⟩ = 0 := by
    have := H.adjoint_comp_eq_zero h i j ⟨_, hK⟩
    rw [← this]; exact congrArg _ (Subtype.ext eσ.symm)
  have h₄ : ((H.d h i)† ⟨σ, h₂⟩ : W h) ∈ (H.d h i).domain := by
    rw [hz]; exact Submodule.zero_mem _
  -- `d σ = f - P_ℌ f - d† d u`
  have hdK := H.d_solutionOp_mem_adjoint_domain hij hjk hj hk f
  have eA := H.adjoint_d_solutionOp hij hjk hj hk f hdK
  set P := (H.harmonic j).starProjection f
  set t := (H.d j k)† ⟨_, hdK⟩
  have hdσ : H.d i j ⟨σ, h₁⟩ = f - P - t := by
    change H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk f)) = _
    rw [eA]; abel
  obtain rfl := c.prev_eq' hij
  have hPmem := (Submodule.starProjection_apply_mem (H.harmonic j) f).2
  obtain ⟨Pd, hPd, hP0⟩ := mem_ker_iff.1 hPmem
  have hP : P ∈ ((H.d (c.prev j) j)†).domain := by
    rw [show P = (Pd : W j) from hPd]; exact Pd.2
  have ht : t ∈ ((H.d (c.prev j) j)†).domain := H.adjoint_mapsTo (c.prev j) j k ⟨_, hdK⟩
  have h₃ : H.d (c.prev j) j ⟨σ, h₁⟩ ∈ ((H.d (c.prev j) j)†).domain := by
    rw [hdσ]; exact Submodule.sub_mem _ (Submodule.sub_mem _ hf hP) ht
  refine H.eq_solutionOp hhi hij hi hj hu h₁ h₂ h₃ h₄ ?_
  have e1 : (⟨_, h₃⟩ : ((H.d (c.prev j) j)†).domain) = ⟨f, hf⟩ - ⟨P, hP⟩ - ⟨t, ht⟩ :=
    Subtype.ext hdσ
  have e2 : (⟨_, h₄⟩ : (H.d h (c.prev j)).domain) = 0 := Subtype.ext hz
  have hP0' : (H.d (c.prev j) j)† ⟨P, hP⟩ = 0 := by
    rw [← hP0]; exact congrArg _ (Subtype.ext hPd)
  have ht0 : (H.d (c.prev j) j)† ⟨t, ht⟩ = 0 := H.adjoint_comp_eq_zero (c.prev j) j k ⟨_, hdK⟩
  have hPi0 : (H.harmonic (c.prev j)).starProjection ((H.d (c.prev j) j)† ⟨f, hf⟩) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).2 (horth _)
  rw [e1, e2, LinearPMap.map_zero, LinearPMap.map_sub, LinearPMap.map_sub, hP0', ht0, hPi0]
  simp

/-! ### `K` on boundaries and on `𝔷ᗮ` -/

/-- Under closed range, a cycle orthogonal to `ℌ` is a boundary. -/
theorem mem_boundaries_of_mem_cycles {l : ι} (hl : H.ClosedRangeAt l) {z : W l}
    (hz : z ∈ H.cycles l) (ho : z ∈ (H.harmonic l)ᗮ) : z ∈ H.boundaries l := by
  rw [← H.boundaries_sup_harmonic hl] at hz
  obtain ⟨b, hb, h, hh, rfl⟩ := Submodule.mem_sup.1 hz
  have h1 : ⟪h, b + h⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hh ho
  rw [inner_add_right, Submodule.inner_left_of_mem_orthogonal hb (H.mem_harmonic_iff.1 hh).2,
    zero_add] at h1
  rw [inner_self_eq_zero.1 h1, add_zero]
  exact hb

/-- Under closed range, `𝔅ᗮ ∩ ℌᗮ = 𝔷ᗮ`. -/
theorem mem_orthogonal_cycles_of {l : ι} (hl : H.ClosedRangeAt l) {x : W l}
    (hB : x ∈ (H.boundaries l)ᗮ) (hH : x ∈ (H.harmonic l)ᗮ) : x ∈ (H.cycles l)ᗮ := by
  rw [← H.boundaries_sup_harmonic hl]
  refine (Submodule.mem_orthogonal _ _).2 fun z hz => ?_
  obtain ⟨b, hb, h, hh, rfl⟩ := Submodule.mem_sup.1 hz
  rw [inner_add_left, Submodule.inner_right_of_mem_orthogonal hb hB,
    Submodule.inner_right_of_mem_orthogonal hh hH, add_zero]

/-- **The `𝔷ᗮ`-preimage under `d` is unique.** -/
theorem eq_of_mem_orthogonal_cycles {l m : ι} (hlm : c.Rel l m) {φ ψ : (H.d l m).domain}
    (hφ : (φ : W l) ∈ (H.cycles l)ᗮ) (hψ : (ψ : W l) ∈ (H.cycles l)ᗮ)
    (hd : H.d l m φ = H.d l m ψ) : (φ : W l) = ψ := by
  have hz : ((φ - ψ : (H.d l m).domain) : W l) ∈ H.cycles l := by
    rw [H.cycles_eq hlm]
    exact mem_ker_iff.2 ⟨φ - ψ, rfl, by rw [LinearPMap.map_sub, hd, sub_self]⟩
  have ho : ((φ - ψ : (H.d l m).domain) : W l) ∈ (H.cycles l)ᗮ := sub_mem hφ hψ
  have h0 := Submodule.inner_right_of_mem_orthogonal hz ho
  rw [inner_self_eq_zero] at h0
  exact sub_eq_zero.1 h0

/-- **`d σ = P_𝔅 f`**: `d d† K f` is the projection of `f` onto the (closed) boundaries. -/
theorem d_solutionSigma (f : W j) :
    H.d i j (H.domainCoord i j (H.solutionSigmaV hij hjk hj hk f)) =
      (H.boundaries j).topologicalClosure.starProjection f := by
  have hBc : (H.boundaries j).topologicalClosure = H.boundaries j :=
    IsClosed.submodule_topologicalClosure_eq hj
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
  · rw [hBc, H.boundaries_eq hij]; exact ⟨_, rfl⟩
  · rw [hBc, H.boundaries_eq hij] at hw
    obtain ⟨τ, rfl⟩ := hw
    have hs := H.isMixedSolution_solutionOp hij hjk hj hk f
    have e := hs.snd (H.domainD i j (H.toDomainSpace hij τ))
    rw [domainIncl_domainD, d_domainCoord_domainD, inner_zero_left, add_zero,
      d_domainCoord_toDomainSpace] at e
    have hp : ⟪H.d i j τ, ((H.mixedSolution hij hjk hj hk f).snd.snd : W j)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (by rw [H.boundaries_eq hij]; exact ⟨_, rfl⟩)
        (H.mem_harmonic_iff.1 (H.mixedSolution hij hjk hj hk f).snd.snd.2).2
    rw [hp, add_zero] at e
    rw [← inner_conj_symm]
    change starRingEnd 𝕜 ⟪H.d i j τ, f - _⟫ = 0
    rw [inner_sub_right, ← e, sub_self, _root_.map_zero]

/-- **`σ = d† K f ⊥ 𝔷ⁱ`.** -/
theorem solutionSigma_mem_orthogonal_cycles (f : W j) :
    H.solutionSigma hij hjk hj hk f ∈ (H.cycles i)ᗮ := by
  refine (Submodule.mem_orthogonal _ _).2 fun z hz => ?_
  have hzd : z ∈ (H.d i j).domain := H.domain_next_le i j (H.cycles_le_domain i hz)
  have e := (H.isMixedSolution_solutionOp hij hjk hj hk f).fst (H.toDomainSpace hij ⟨z, hzd⟩)
  rw [domainIncl_toDomainSpace, d_domainCoord_toDomainSpace,
    H.d_eq_zero_of_mem_cycles hz, inner_zero_left, sub_zero] at e
  exact e

/-- For `g ∈ 𝔅ʲ`, `d† K g` is the `𝔷ᗮ`-preimage of `g`: every `φ ⊥ 𝔷ⁱ` with `d φ = g` equals it. -/
theorem eq_solutionSigma_of_d_eq {g : W j} (hg : g ∈ H.boundaries j) {φ : (H.d i j).domain}
    (hφ : (φ : W i) ∈ (H.cycles i)ᗮ) (hd : H.d i j φ = g) :
    (φ : W i) = H.solutionSigma hij hjk hj hk g := by
  have hBc : (H.boundaries j).topologicalClosure = H.boundaries j :=
    IsClosed.submodule_topologicalClosure_eq hj
  refine H.eq_of_mem_orthogonal_cycles hij (ψ := H.domainCoord i j (H.solutionSigmaV hij hjk hj hk g))
    hφ (H.solutionSigma_mem_orthogonal_cycles hij hjk hj hk g) ?_
  rw [hd, H.d_solutionSigma hij hjk hj hk, Submodule.starProjection_eq_self_iff.2]
  rw [hBc]; exact hg

/-- **`K` preserves the boundaries.** -/
theorem solutionOp_mem_boundaries {g : W j} (hg : g ∈ H.boundaries j) :
    H.solutionOp hij hjk hj hk g ∈ H.boundaries j := by
  have hBc : (H.boundaries j).topologicalClosure = H.boundaries j :=
    IsClosed.submodule_topologicalClosure_eq hj
  have hdK := H.d_solutionOp_mem_adjoint_domain hij hjk hj hk g
  have e := H.adjoint_d_solutionOp hij hjk hj hk g hdK
  have hP : (H.boundaries j).topologicalClosure.starProjection g = g :=
    Submodule.starProjection_eq_self_iff.2 (by rw [hBc]; exact hg)
  rw [H.d_solutionSigma hij hjk hj hk, hP,
    (Submodule.starProjection_apply_eq_zero_iff _).2
      (H.mem_orthogonal_harmonic_of_mem_boundaries hg), sub_zero, sub_self] at e
  have h0 : H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk g)) = 0 := by
    have := adjoint_isFormalAdjoint (H.dense j k) ⟨_, hdK⟩
      (H.domainCoord j k (H.solutionOpV hij hjk hj hk g))
    rw [e, inner_zero_left] at this
    exact inner_self_eq_zero.1 this.symm
  refine H.mem_boundaries_of_mem_cycles hj ?_ (H.solutionOp_mem_orthogonal_harmonic hij hjk hj hk g)
  rw [H.cycles_eq hjk]
  exact mem_ker_iff.2 ⟨_, rfl, h0⟩

/-- **`d† d K v = v` for `v ⊥ 𝔷ʲ`.** -/
theorem adjoint_d_solutionOp_of_mem_orthogonal {v : W j} (hv : v ∈ (H.cycles j)ᗮ)
    (h : H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk v)) ∈ ((H.d j k)†).domain) :
    (H.d j k)† ⟨_, h⟩ = v := by
  have hB : v ∈ ((H.boundaries j).topologicalClosure)ᗮ := by
    rw [IsClosed.submodule_topologicalClosure_eq hj]
    exact Submodule.orthogonal_le (H.boundaries_le_cycles j) hv
  have hH : v ∈ (H.harmonic j)ᗮ := Submodule.orthogonal_le (H.harmonic_le_cycles j) hv
  rw [H.adjoint_d_solutionOp hij hjk hj hk v h, H.d_solutionSigma hij hjk hj hk,
    (Submodule.starProjection_apply_eq_zero_iff _).2 hB,
    (Submodule.starProjection_apply_eq_zero_iff _).2 hH, sub_zero, sub_zero]

/-- `⟪v, x⟫ = ⟪d K v, d x⟫` for `v ⊥ 𝔷ʲ` and `x ∈ D(d)`. -/
theorem inner_eq_inner_d_solutionOp {v : W j} (hv : v ∈ (H.cycles j)ᗮ) (x : (H.d j k).domain) :
    ⟪v, (x : W j)⟫ = ⟪H.d j k (H.domainCoord j k (H.solutionOpV hij hjk hj hk v)), H.d j k x⟫ := by
  have h := H.d_solutionOp_mem_adjoint_domain hij hjk hj hk v
  have e := adjoint_isFormalAdjoint (H.dense j k) ⟨_, h⟩ x
  rw [H.adjoint_d_solutionOp_of_mem_orthogonal hij hjk hj hk hv h] at e
  exact e

/-- **`K` preserves `𝔷ᗮ`.** -/
theorem solutionOp_mem_orthogonal_cycles {v : W j} (hv : v ∈ (H.cycles j)ᗮ) :
    H.solutionOp hij hjk hj hk v ∈ (H.cycles j)ᗮ := by
  have hBc : (H.boundaries j).topologicalClosure = H.boundaries j :=
    IsClosed.submodule_topologicalClosure_eq hj
  -- `σ_v = 0`
  have hσ : H.solutionSigma hij hjk hj hk v = 0 := by
    have hB : v ∈ ((H.boundaries j).topologicalClosure)ᗮ := by
      rw [hBc]; exact Submodule.orthogonal_le (H.boundaries_le_cycles j) hv
    have hd := H.d_solutionSigma hij hjk hj hk v
    rw [(Submodule.starProjection_apply_eq_zero_iff _).2 hB] at hd
    have hz : H.solutionSigma hij hjk hj hk v ∈ H.cycles i := by
      rw [H.cycles_eq hij]; exact mem_ker_iff.2 ⟨_, rfl, hd⟩
    have := Submodule.inner_right_of_mem_orthogonal hz
      (H.solutionSigma_mem_orthogonal_cycles hij hjk hj hk v)
    exact inner_self_eq_zero.1 this
  have h₂ := H.solutionOp_mem_adjoint_domain hij hjk hj hk v
  have e := H.adjoint_solutionOp hij hjk hj hk v h₂
  rw [hσ] at e
  refine H.mem_orthogonal_cycles_of hj ?_ (H.solutionOp_mem_orthogonal_harmonic hij hjk hj hk v)
  refine (Submodule.mem_orthogonal _ _).2 fun b hb => ?_
  rw [H.boundaries_eq hij] at hb
  obtain ⟨τ, rfl⟩ := hb
  have := adjoint_isFormalAdjoint (H.dense i j) ⟨_, h₂⟩ τ
  rw [e, inner_zero_left] at this
  have h0 : ⟪H.solutionOp hij hjk hj hk v, H.d i j τ⟫ = 0 := this.symm
  rw [← inner_conj_symm]
  exact (congrArg _ h0).trans (_root_.map_zero _)

/-- **`‖φ‖² = re ⟪K (d φ), d φ⟫` for `φ ⊥ 𝔷ⁱ`** (`φ = d† K d φ`). -/
theorem norm_sq_eq_re_inner_solutionOp_d {φ : (H.d i j).domain} (hφ : (φ : W i) ∈ (H.cycles i)ᗮ) :
    ‖(φ : W i)‖ ^ 2 = RCLike.re ⟪H.solutionOp hij hjk hj hk (H.d i j φ), H.d i j φ⟫ := by
  have hg : H.d i j φ ∈ H.boundaries j := by rw [H.boundaries_eq hij]; exact ⟨_, rfl⟩
  have e := H.eq_solutionSigma_of_d_eq hij hjk hj hk hg hφ rfl
  have h₂ := H.solutionOp_mem_adjoint_domain hij hjk hj hk (H.d i j φ)
  have e2 := adjoint_isFormalAdjoint (H.dense i j) ⟨_, h₂⟩ φ
  rw [H.adjoint_solutionOp hij hjk hj hk _ h₂, ← e] at e2
  rw [← @inner_self_eq_norm_sq 𝕜, e2]

/-! ### Compactness -/

/-- **`K` is compact** under the compactness property at `j` (e.g. Rellich). See [AFW2010],
§3.1.3 and §3.2; [Arnold2018], Thm 4.10. -/
theorem isCompactOperator_solutionOp (hcp : H.HasCompactPropertyAt j) :
    IsCompactOperator (H.solutionOp hij hjk hj hk) := by
  obtain ⟨cP, hcP, hPi, hPj⟩ := H.exists_poincare_pair hij hjk hj hk
  have hcP0 : 0 ≤ cP := zero_le_one.trans hcP
  have hc : cP ≤ cP ^ 2 := by nlinarith
  obtain ⟨Kc, hKc, hsub⟩ := hcp.exists_isCompact (cP ^ 2)
  refine ⟨Kc, hKc, Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun f hf => ?_⟩
  have hf1 : ‖f‖ ≤ 1 := (mem_ball_zero_iff.1 hf).le
  have b1 := H.norm_solutionOp_le hij hjk hj hk hcP0 hPi hPj f
  have b2 := H.norm_d_solutionOp_le hij hjk hj hk hcP0 hPi hPj f
  have b3 := H.norm_solutionSigma_le hij hjk hj hk hcP0 hPi hPj f
  obtain rfl := c.next_eq' hjk
  obtain rfl := c.prev_eq' hij
  have h₂ := H.solutionOp_mem_adjoint_domain hij hjk hj hk f
  refine hsub _ (H.domainIncl_mem j _) h₂ ?_ ?_ ?_
  · nlinarith [sq_nonneg cP]
  · change ‖H.d j (c.next j) (H.domainCoord j (c.next j) (H.solutionOpV hij hjk hj hk f))‖ ≤ _
    nlinarith
  · rw [H.adjoint_solutionOp hij hjk hj hk f h₂]
    nlinarith

/-! ### The Hodge Laplacian of a finite window -/

section Window

variable [Fintype ι]

omit [∀ i, CompleteSpace (W i)] in
private theorem apply_mk_sub {E F : Type*} [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
    [Module 𝕜 F] (T : E →ₗ.[𝕜] F) {a b : E} (ha : a ∈ T.domain) (hb : b ∈ T.domain)
    (h : a - b ∈ T.domain) : T ⟨a - b, h⟩ = T ⟨a, ha⟩ - T ⟨b, hb⟩ := by
  rw [← T.map_sub]; rfl

/-- **The Hodge Laplacian is `𝐝 𝐝* + 𝐝* 𝐝`**: for `x ∈ D(Δ)`, `x ∈ D(𝐝) ∩ D(𝐝*)`, `𝐝 x ∈ D(𝐝*)`,
`𝐝* x ∈ D(𝐝)` and `Δ x = 𝐝 𝐝* x + 𝐝* 𝐝 x` (the terms `𝐝 𝐝`, `𝐝* 𝐝*` of `-L²` vanish). See
[AFW2010], §3.2. -/
theorem hodgeLaplacian_apply_eq (x : H.hodgeLaplacian.domain) :
    ∃ (h₁ : (x : PiLp 2 W) ∈ H.totalD.domain) (h₂ : (x : PiLp 2 W) ∈ H.dual.totalD.domain)
      (h₃ : (H.totalD ⟨_, h₁⟩ : PiLp 2 W) ∈ H.dual.totalD.domain)
      (h₄ : (H.dual.totalD ⟨_, h₂⟩ : PiLp 2 W) ∈ H.totalD.domain),
      H.hodgeLaplacian x = H.totalD ⟨_, h₄⟩ + H.dual.totalD ⟨_, h₃⟩ := by
  rcases x with ⟨x, hw, hLx⟩
  set X1 : H.totalD.domain := ⟨x, hw.1⟩
  set X2 : H.dual.totalD.domain := ⟨x, hw.2⟩
  have hL : (H.wave ⟨x, hw⟩ : PiLp 2 W) = H.totalD X1 - H.dual.totalD X2 := rfl
  have hd1 : (H.totalD X1 : PiLp 2 W) ∈ H.totalD.domain := H.totalD_mapsTo X1
  have hd2 : (H.dual.totalD X2 : PiLp 2 W) ∈ H.dual.totalD.domain := H.dual.totalD_mapsTo X2
  have hd1' : (H.totalD X1 : PiLp 2 W) ∈ H.dual.totalD.domain := by
    have e : (H.totalD X1 : PiLp 2 W) = H.wave ⟨x, hw⟩ + H.dual.totalD X2 := by rw [hL]; abel
    rw [e]; exact add_mem hLx.2 hd2
  have hd2' : (H.dual.totalD X2 : PiLp 2 W) ∈ H.totalD.domain := by
    have e : (H.dual.totalD X2 : PiLp 2 W) = H.totalD X1 - H.wave ⟨x, hw⟩ := by rw [hL]; abel
    rw [e]; exact sub_mem hd1 hLx.1
  refine ⟨hw.1, hw.2, hd1', hd2', ?_⟩
  have e1 : H.totalD ⟨_, hLx.1⟩ = H.totalD ⟨_, hd1⟩ - H.totalD ⟨_, hd2'⟩ := by
    rw [← apply_mk_sub _ hd1 hd2' (by rw [← hL]; exact hLx.1)]
    exact congrArg _ (Subtype.ext hL)
  have e2 : H.dual.totalD ⟨_, hLx.2⟩ = H.dual.totalD ⟨_, hd1'⟩ - H.dual.totalD ⟨_, hd2⟩ := by
    rw [← apply_mk_sub _ hd1' hd2 (by rw [← hL]; exact hLx.2)]
    exact congrArg _ (Subtype.ext hL)
  have z1 : H.totalD ⟨_, hd1⟩ = 0 := H.totalD_comp_totalD X1
  have z2 : H.dual.totalD ⟨_, hd2⟩ = 0 := H.dual.totalD_comp_totalD X2
  change -(H.totalD ⟨_, hLx.1⟩ - H.dual.totalD ⟨_, hLx.2⟩) = _
  rw [e1, e2, z1, z2]; abel

include hij hjk in
/-- **The `j`-th component of the window Hodge Laplacian** `Δ = -L²` is the Hodge Laplacian
`d d† + d† d` at `j`: for `x ∈ D(Δ)`, `x j ∈ D(d) ∩ D(d†)`, `d x j ∈ D(d†)`, `d† x j ∈ D(d)` and
`(Δ x) j = d (d† x j) + d† (d x j)`. No closed range is needed. See [AFW2010], §3.2. -/
theorem hodgeLaplacian_apply_of_rel (x : H.hodgeLaplacian.domain) :
    ∃ (h₁ : (x : PiLp 2 W) j ∈ (H.d j k).domain) (h₂ : (x : PiLp 2 W) j ∈ ((H.d i j)†).domain)
      (h₃ : H.d j k ⟨_, h₁⟩ ∈ ((H.d j k)†).domain)
      (h₄ : ((H.d i j)† ⟨_, h₂⟩ : W i) ∈ (H.d i j).domain),
      (H.hodgeLaplacian x) j = H.d i j ⟨_, h₄⟩ + (H.d j k)† ⟨_, h₃⟩ := by
  obtain ⟨hx1, hx2, hd1', hd2', hΔ⟩ := H.hodgeLaplacian_apply_eq x
  set X1 : H.totalD.domain := ⟨x, hx1⟩
  set X2 : H.dual.totalD.domain := ⟨x, hx2⟩
  have h₁ : (x : PiLp 2 W) j ∈ (H.d j k).domain := hx1 j k
  have h₂ : (x : PiLp 2 W) j ∈ ((H.d i j)†).domain := hx2 j i
  have ci : (H.dual.totalD X2 : PiLp 2 W) i = (H.d i j)† ⟨_, h₂⟩ :=
    H.dual.totalD_apply_of_rel X2 (show c.symm.Rel j i from hij)
  have ck : (H.totalD X1 : PiLp 2 W) k = H.d j k ⟨_, h₁⟩ := H.totalD_apply_of_rel X1 hjk
  have h₄ : ((H.d i j)† ⟨_, h₂⟩ : W i) ∈ (H.d i j).domain := ci ▸ hd2' i j
  have h₃ : H.d j k ⟨_, h₁⟩ ∈ ((H.d j k)†).domain := ck ▸ hd1' k j
  refine ⟨h₁, h₂, h₃, h₄, ?_⟩
  rw [hΔ, PiLp.add_apply, H.totalD_apply_of_rel _ hij,
    H.dual.totalD_apply_of_rel _ (show c.symm.Rel k j from hjk)]
  exact congrArg₂ (· + ·) (congrArg (H.d i j) (Subtype.ext ci))
    (congrArg ((H.d j k)†) (Subtype.ext ck))

include hij hjk in
/-- **`K` inverts the window Hodge Laplacian at `j`**: if `x ∈ D(Δ)` has `j`-th component `K f`,
then `(Δ x) j = f - P_ℌ f`. See [AFW2010], §3.2. -/
theorem hodgeLaplacian_apply_of_apply_eq_solutionOp {f : W j} (x : H.hodgeLaplacian.domain)
    (hx : (x : PiLp 2 W) j = H.solutionOp hij hjk hj hk f) :
    (H.hodgeLaplacian x) j = f - (H.harmonic j).starProjection f := by
  obtain ⟨h₁, h₂, h₃, h₄, e⟩ := H.hodgeLaplacian_apply_of_rel hij hjk x
  obtain ⟨h₁', h₂', h₃', h₄', e'⟩ := H.hodgeLaplacian_solutionOp hij hjk hj hk f
  rw [e, ← e']
  revert h₁ h₂ h₃ h₄
  rw [hx]
  intro _ _ _ _ _
  rfl

include hij hjk in
/-- `Pi.single j u ∈ D(Δ)` as soon as `u` is in the domain of the Hodge Laplacian at `j`. -/
theorem single_mem_hodgeLaplacian_domain [DecidableEq ι] {u : W j} (h₁ : u ∈ (H.d j k).domain)
    (h₂ : u ∈ ((H.d i j)†).domain) (h₃ : H.d j k ⟨u, h₁⟩ ∈ ((H.d j k)†).domain)
    (h₄ : ((H.d i j)† ⟨u, h₂⟩ : W i) ∈ (H.d i j).domain) :
    PiLp.single 2 j u ∈ H.hodgeLaplacian.domain := by
  obtain rfl := c.next_eq' hjk
  obtain rfl := c.prev_eq' hij
  have hx1 : PiLp.single 2 j u ∈ H.totalD.domain := H.single_mem_totalDomain j h₁
  have hx2 : PiLp.single 2 j u ∈ H.dual.totalD.domain := H.dual.single_mem_totalDomain j h₂
  -- the components of `𝐝 x` and `𝐝* x`
  have c1 : ∀ a, (H.totalD ⟨_, hx1⟩ : PiLp 2 W) a =
      H.d j a ⟨u, H.domain_next_le j a h₁⟩ := by
    intro a
    rw [totalD_apply]
    refine (Finset.sum_eq_single j (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ j) h)).trans
      ?_
    · exact LinearPMap.apply_mk_eq_zero _ _ (PiLp.single_eq_of_ne (p := 2) hb _)
    · congr 1; exact Subtype.ext (PiLp.single_eq_same (p := 2) _ _)
  have c2 : ∀ a, (H.dual.totalD ⟨_, hx2⟩ : PiLp 2 W) a =
      H.dual.d j a ⟨u, H.dual.domain_next_le j a h₂⟩ := by
    intro a
    rw [totalD_apply]
    refine (Finset.sum_eq_single j (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ j) h)).trans
      ?_
    · exact LinearPMap.apply_mk_eq_zero _ _ (PiLp.single_eq_of_ne (p := 2) hb _)
    · congr 1; exact Subtype.ext (PiLp.single_eq_same (p := 2) _ _)
  have hy1 : (H.totalD ⟨_, hx1⟩ : PiLp 2 W) ∈ H.dual.totalD.domain := by
    intro a b
    rw [c1 a]
    by_cases hba : c.Rel b a
    · by_cases ha : c.Rel j a
      · obtain rfl := c.prev_eq hba ha
        obtain rfl := c.next_eq' ha
        exact h₃
      · rw [apply_eq_zero_of_not_rel _ ha]; exact Submodule.zero_mem _
    · rw [H.dual.domain_eq_top_of_not_rel (show ¬ c.symm.Rel a b from hba)]
      exact Submodule.mem_top
  have hy2 : (H.dual.totalD ⟨_, hx2⟩ : PiLp 2 W) ∈ H.totalD.domain := by
    intro a b
    rw [c2 a]
    by_cases hab : c.Rel a b
    · by_cases ha : c.symm.Rel j a
      · obtain rfl := c.next_eq hab ha
        obtain rfl := c.prev_eq' ha
        exact h₄
      · rw [H.dual.apply_eq_zero_of_not_rel ha]; exact Submodule.zero_mem _
    · rw [H.domain_eq_top_of_not_rel hab]; exact Submodule.mem_top
  have hw : PiLp.single 2 j u ∈ H.wave.domain := ⟨hx1, hx2⟩
  refine ⟨hw, ?_⟩
  change (H.totalD ⟨_, hx1⟩ - H.dual.totalD ⟨_, hx2⟩ : PiLp 2 W) ∈ H.wave.domain
  exact sub_mem ⟨H.totalD_mapsTo _, hy1⟩ ⟨hy2, H.dual.totalD_mapsTo _⟩

include hij hjk in
/-- **`K = Δ⁻¹` on the window, componentwise**: `x = Pi.single j (K f) ∈ D(Δ)` and
`(Δ x) j = f - P_ℌ f`. See [AFW2010], §3.2; [Arnold2018], Thm 4.10. -/
theorem hodgeLaplacian_single_solutionOp [DecidableEq ι] (f : W j) :
    ∃ hx : PiLp.single 2 j (H.solutionOp hij hjk hj hk f) ∈ H.hodgeLaplacian.domain,
      (H.hodgeLaplacian ⟨_, hx⟩) j = f - (H.harmonic j).starProjection f := by
  obtain ⟨h₁, h₂, h₃, h₄, -⟩ := H.hodgeLaplacian_solutionOp hij hjk hj hk f
  have hx := H.single_mem_hodgeLaplacian_domain hij hjk h₁ h₂ h₃ h₄
  exact ⟨hx, H.hodgeLaplacian_apply_of_apply_eq_solutionOp hij hjk hj hk ⟨_, hx⟩
    (PiLp.single_eq_same (p := 2) _ _)⟩

end Window

end Feec.HilbertComplex
