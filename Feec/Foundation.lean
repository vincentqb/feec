import Mathlib

/-!
# Feec foundation: shared definitions

Sections:
* §A Operators
* §B Evolution
* §C, §D, §E Complex
* §F BGG
* §G Tensor

Conventions: real scalars only; `open scoped RealInnerProductSpace` (so `⟪x, y⟫ = ⟪x, y⟫_ℝ`);
complexes indexed by explicit segments `k, k+1, k+2` (no `k-1`).
No `axiom`, no `sorry`: missing theory (Hille–Yosida/Stone, Sobolev spaces, traces)
enters only as explicit hypotheses / structure fields.
-/

open scoped RealInnerProductSpace
open Set

noncomputable section

namespace Feec

/-! ## §A. Unbounded operators -/

section Operators
open LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Skew-adjoint (possibly unbounded) operator: `A† = -A` (equal domains). -/
def IsSkewAdjoint [CompleteSpace E] (A : E →ₗ.[ℝ] E) : Prop := A† = -A

/-- Skew-symmetry on the domain: `⟪A x, y⟫ = -⟪x, A y⟫`. (Weaker than skew-adjoint;
enough for all energy/uniqueness/constraint-propagation arguments.) -/
def IsSkewSymm (A : E →ₗ.[ℝ] E) : Prop :=
  ∀ x y : A.domain, ⟪A x, (y : E)⟫ = -⟪(x : E), A y⟫

/-- Restriction of `L` to an invariant subspace `K`, as an operator `K → K`
(domain `D(L) ∩ K`). Used by Thm 4.4. -/
def restrictTo (L : E →ₗ.[ℝ] E) (K : Submodule ℝ E)
    (hinv : ∀ x : L.domain, (x : E) ∈ K → L x ∈ K) : K →ₗ.[ℝ] K where
  domain := L.domain.comap K.subtype
  toFun :=
    { toFun := fun x => ⟨L ⟨(x : K), x.2⟩, hinv ⟨_, x.2⟩ (x : K).2⟩
      map_add' := fun x y => by ext; simp [← LinearPMap.map_add]; rfl
      map_smul' := fun c x => by ext; simp [← LinearPMap.map_smul]; rfl }

/-- (4.1a) `(range T)ᗮ = ker T†` for densely defined `T` (no closedness needed). -/
theorem orth_range_eq_ker_adjoint {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) :
    (LinearMap.range T.toFun)ᗮ = T†.ker := by
  ext y
  constructor
  · intro hy
    have key : ∀ x : T.domain, ⟪(0 : E), (x : E)⟫ = ⟪y, T x⟫ := fun x => by
      have := (Submodule.mem_orthogonal _ _).1 hy (T x) ⟨x, rfl⟩
      rw [inner_zero_left, real_inner_comm, this]
    have hmem : y ∈ T†.domain := mem_adjoint_domain_of_exists y ⟨0, key⟩
    rw [LinearPMap.mem_ker_iff]
    exact ⟨⟨y, hmem⟩, rfl, adjoint_apply_eq hT ⟨y, hmem⟩ key⟩
  · intro hy
    rw [LinearPMap.mem_ker_iff] at hy
    obtain ⟨y', rfl, hy0⟩ := hy
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    have := (adjoint_isFormalAdjoint hT) y' x
    rw [hy0] at this
    simpa [real_inner_comm] using this.symm

/-- Skew-adjoint ⇒ skew-symmetric. -/
theorem IsSkewAdjoint.isSkewSymm [CompleteSpace E] {L : E →ₗ.[ℝ] E}
    (hD : Dense (L.domain : Set E)) (hL : IsSkewAdjoint L) : IsSkewSymm L := by
  intro x y
  have hle : -L ≤ L† := hL ▸ le_rfl
  have hx : (x : E) ∈ L†.domain := hle.1 x.2
  have h1 := adjoint_isFormalAdjoint hD ⟨x, hx⟩ y
  have h2 : L† ⟨x, hx⟩ = -L x := (hle.2 (x := x) (y := ⟨x, hx⟩) rfl).symm
  rw [h2, inner_neg_left] at h1
  linarith

end Operators

/-! ## §B. Evolution problems: solutions and the well-posedness hypothesis -/

section Evolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strong solution of `U' = L U + F` on `[0,T]` with `U 0 = U₀`.
Derivatives are within `Icc 0 T` (one-sided at the endpoints). Continuity of `U` in `E`
follows from `deriv`; graph-norm continuity is NOT part of the predicate (no module needs it). -/
structure IsStrongSolution (L : E →ₗ.[ℝ] E) (T : ℝ) (U₀ : E) (F U : ℝ → E) : Prop where
  mem : ∀ t ∈ Icc 0 T, U t ∈ L.domain
  deriv : ∀ t (ht : t ∈ Icc 0 T), HasDerivWithinAt U (L ⟨U t, mem t ht⟩ + F t) (Icc 0 T) t
  init : U 0 = U₀

/-- **Explicit hypothesis standing in for Thm 4.3 (Hille–Yosida / Stone), which Mathlib lacks.**
For every initial datum in `D(L)` and every admissible forcing there is a strong solution.
`Adm` abstracts the class "`C([0,T];X) ∩ (W^{1,1}(0,T;X) ∪ L¹(0,T;D(L)))`".
Never assumed as an `axiom`; always a theorem hypothesis. Uniqueness is *proved* (energy). -/
def WellPosedExistence (L : E →ₗ.[ℝ] E) (T : ℝ) (Adm : (ℝ → E) → Prop) : Prop :=
  ∀ U₀ ∈ L.domain, ∀ F, Adm F → ∃ U, IsStrongSolution L T U₀ F U

/-- Homogeneous version (`F = 0`), the form used in Thm 4.6. -/
def WellPosedHom (L : E →ₗ.[ℝ] E) (T : ℝ) : Prop :=
  ∀ U₀ ∈ L.domain, ∃ U, IsStrongSolution L T U₀ 0 U

/-- Energy lemma: if `⟪e', e⟫ = 0` on `[0,T)` then `e(0) = 0` forces `e ≡ 0` on `[0,T]`.
The single engine behind every uniqueness statement (Thm 4.3/4.6/4.7, Cor 4.5, Ch 6). -/
theorem energy_zero {e e' : ℝ → E} {T : ℝ}
    (hcont : ContinuousOn e (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (e' t) (Ici t) t)
    (horth : ∀ t ∈ Ico 0 T, ⟪e' t, e t⟫ = 0) (h0 : e 0 = 0) :
    ∀ t ∈ Icc 0 T, e t = 0 := by
  have hc : ∀ t ∈ Icc (0:ℝ) T, ‖e t‖ ^ 2 = ‖e 0‖ ^ 2 := by
    refine constant_of_has_deriv_right_zero (f := fun t => ‖e t‖ ^ 2)
      (hcont.norm.pow 2) ?_
    intro t ht
    have := (hd t ht).norm_sq
    rw [real_inner_comm, horth t ht, mul_zero] at this; exact this
  intro t ht
  simpa [h0] using hc t ht

end Evolution

/-! ## §C. Unbounded Hilbert complexes (the thesis' / Brüning–Lesch picture) -/

/-- A length-2 Hilbert complex `W0 --d0--> W1 --d1--> W2` of closed, densely defined operators
(§4.4 setup). Closed range is **not** part of the structure (see `HilbertComplex2.ClosedRange`). -/
structure HilbertComplex2 (W0 W1 W2 : Type*)
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2] where
  d0 : W0 →ₗ.[ℝ] W1
  d1 : W1 →ₗ.[ℝ] W2
  dense0 : Dense (d0.domain : Set W0)
  dense1 : Dense (d1.domain : Set W1)
  closed0 : d0.IsClosed
  closed1 : d1.IsClosed
  /-- `d0 V0 ⊂ V1` (missing from the thesis' definition). -/
  map_mem : ∀ x : d0.domain, d0 x ∈ d1.domain
  comp_zero : ∀ x : d0.domain, d1 ⟨d0 x, map_mem x⟩ = 0

namespace HilbertComplex2
open LinearPMap

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    (H : HilbertComplex2 W0 W1 W2)

/-- Closed-range hypothesis (a closed complex in AFW's sense). -/
def ClosedRange : Prop :=
  IsClosed (LinearMap.range H.d0.toFun : Set W1) ∧ IsClosed (LinearMap.range H.d1.toFun : Set W2)

/-- Domain of the middle space of the Hodge wave operator: `V1 ∩ V1*`. -/
def midDomain : Submodule ℝ W1 := H.d1.domain ⊓ H.d0†.domain

/-- The product space `W = W0 × W1 × W2` with the ℓ² inner product. -/
abbrev Tot (W0 W1 W2 : Type*) := WithLp 2 (W0 × WithLp 2 (W1 × W2))

/-- coordinates of `Tot` -/
def tot (W0 W1 W2 : Type*)
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] : Tot W0 W1 W2 ≃ₗ[ℝ] W0 × W1 × W2 :=
  (WithLp.linearEquiv 2 ℝ _).trans ((LinearEquiv.refl ℝ W0).prodCongr (WithLp.linearEquiv 2 ℝ _))
/-- domain `V0 × (V1 ∩ V1*) × V2*` of the Hodge wave operator, as a submodule of `Tot`. -/
def domL : Submodule ℝ (Tot W0 W1 W2) :=
  (H.d0.domain.prod (H.midDomain.prod H.d1†.domain)).comap (tot W0 W1 W2).toLinearMap
/-- the coordinate projections of `domL` into the operator domains -/
def pr0 : H.domL →ₗ[ℝ] H.d0.domain :=
  LinearMap.codRestrict _ ((LinearMap.fst ℝ _ _).comp ((tot W0 W1 W2).toLinearMap.comp
    H.domL.subtype)) (fun x => x.2.1)
def prV1 : H.domL →ₗ[ℝ] H.d1.domain :=
  LinearMap.codRestrict _ ((LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    ((tot W0 W1 W2).toLinearMap.comp H.domL.subtype))) (fun x => x.2.2.1.1)
def prV1s : H.domL →ₗ[ℝ] H.d0†.domain :=
  LinearMap.codRestrict _ ((LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    ((tot W0 W1 W2).toLinearMap.comp H.domL.subtype))) (fun x => x.2.2.1.2)
def prV2s : H.domL →ₗ[ℝ] H.d1†.domain :=
  LinearMap.codRestrict _ ((LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    ((tot W0 W1 W2).toLinearMap.comp H.domL.subtype))) (fun x => x.2.2.2)

/-- Hodge wave operator (4.5): `L(σ,u,ρ) = (-d0* u, d0 σ + d1* ρ, -d1 u)` on `domL`. -/
def waveOp : Tot W0 W1 W2 →ₗ.[ℝ] Tot W0 W1 W2 where
  domain := H.domL
  toFun := (tot W0 W1 W2).symm.toLinearMap.comp
    ((-(H.d0†.toFun.comp H.prV1s)).prod
      (((H.d0.toFun.comp H.pr0) + (H.d1†.toFun.comp H.prV2s)).prod
        (-(H.d1.toFun.comp H.prV1))))

end HilbertComplex2

/-- ℕ-indexed unbounded Hilbert complex (W-level). `segment k` gives the length-2 piece. -/
structure UHilbertComplex (W : ℕ → Type*)
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    where
  d : ∀ k, W k →ₗ.[ℝ] W (k + 1)
  dense : ∀ k, Dense ((d k).domain : Set (W k))
  closed : ∀ k, (d k).IsClosed
  map_mem : ∀ k (x : (d k).domain), d k x ∈ (d (k + 1)).domain
  comp_zero : ∀ k (x : (d k).domain), d (k + 1) ⟨d k x, map_mem k x⟩ = 0

namespace UHilbertComplex

variable {W : ℕ → Type*}
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    (C : UHilbertComplex W)

def segment (k : ℕ) : HilbertComplex2 (W k) (W (k + 1)) (W (k + 2)) where
  d0 := C.d k
  d1 := C.d (k + 1)
  dense0 := C.dense k
  dense1 := C.dense (k + 1)
  closed0 := C.closed k
  closed1 := C.closed (k + 1)
  map_mem := C.map_mem k
  comp_zero := C.comp_zero k

end UHilbertComplex

/-! ## §D. Bounded "domain complex" (AFW): `V k` carries the graph inner product -/

/-- `V k` = domain of `d k` with its graph inner product, `ι k : V k → W k` the inclusion.
All Hodge/Poincaré/cohomology arguments live in `V` using Mathlib's `ᗮ`/`starProjection`. -/
structure HilbertComplex (V W : ℕ → Type*)
    [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)] [∀ k, CompleteSpace (V k)]
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    where
  ι : ∀ k, V k →L[ℝ] W k
  ι_injective : ∀ k, Function.Injective (ι k)
  d : ∀ k, V k →L[ℝ] V (k + 1)
  d_comp_d : ∀ k, (d (k + 1)).comp (d k) = 0
  inner_graph : ∀ k (u v : V k),
    ⟪u, v⟫ = ⟪ι k u, ι k v⟫ + ⟪ι (k + 1) (d k u), ι (k + 1) (d k v)⟫

namespace HilbertComplex

variable {V W : ℕ → Type*}
    [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)] [∀ k, CompleteSpace (V k)]
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    (C : HilbertComplex V W)

/-- cycles `𝔷^k = ker d^k ⊂ V^k` -/
def Z (k : ℕ) : Submodule ℝ (V k) := (C.d k).ker
/-- boundaries `𝔅^{k+1} = d^k V^k ⊂ V^{k+1}` -/
def B (k : ℕ) : Submodule ℝ (V (k + 1)) := (C.d k).range
/-- harmonic forms `ℌ^{k+1} = 𝔅^{k+1}ᗮ ∩ 𝔷^{k+1}` -/
def H (k : ℕ) : Submodule ℝ (V (k + 1)) := (C.B k)ᗮ ⊓ C.Z (k + 1)
/-- closed complex at position `k → k+1` -/
def IsClosedAt (k : ℕ) : Prop := IsClosed (C.B k : Set (V (k + 1)))

theorem d_d (k : ℕ) (u : V k) : C.d (k + 1) (C.d k u) = 0 := by
  simpa using congrArg (fun f => f u) (C.d_comp_d k)

theorem B_le_Z (k : ℕ) : C.B k ≤ C.Z (k + 1) := by
  rintro _ ⟨u, rfl⟩; exact C.d_d k u

theorem isClosed_Z (k : ℕ) : IsClosed (C.Z k : Set (V k)) := (C.d k).isClosed_ker

instance (k : ℕ) : (C.Z k).HasOrthogonalProjection := by
  have : CompleteSpace (C.Z k) := (C.isClosed_Z k).completeSpace_coe
  infer_instance

/-- On cycles the `V`- and `W`-inner products agree. -/
theorem inner_of_mem_Z {k : ℕ} {u v : V k} (hu : u ∈ C.Z k) :
    ⟪u, v⟫ = ⟪C.ι k u, C.ι k v⟫ := by
  have : C.d k u = 0 := hu
  simp [C.inner_graph, this]

/-- A subcomplex: subspaces `Vh k` with `d (Vh k) ⊆ Vh (k+1)`. -/
structure Subcomplex where
  Vh : ∀ k, Submodule ℝ (V k)
  d_mem : ∀ k, ∀ u ∈ Vh k, C.d k u ∈ Vh (k + 1)

/-- Bounded cochain projections onto a subcomplex (AFW 2010, Thm 5.9 abstracted). -/
structure CochainProjection (S : C.Subcomplex) where
  π : ∀ k, V k →L[ℝ] V k
  mem : ∀ k u, π k u ∈ S.Vh k
  proj : ∀ k, ∀ u ∈ S.Vh k, π k u = u
  comm : ∀ k u, C.d k (π k u) = π (k + 1) (C.d k u)

end HilbertComplex

/-! ## §E. Algebraic complex segment with W-inner products ("type = domain" model)

Used where only algebra + inner products are needed (Prop 4.13, Thm 4.14, Ch 5.2, Ch 6.2, Ch 7):
each type carries the **W** inner product and `d` is a linear map on the domain type.
Graph norms are explicit functions. -/

structure Complex3 (X0 X1 X2 : Type*) [AddCommGroup X0] [Module ℝ X0]
    [AddCommGroup X1] [Module ℝ X1] [AddCommGroup X2] [Module ℝ X2] where
  d0 : X0 →ₗ[ℝ] X1
  d1 : X1 →ₗ[ℝ] X2
  d1_d0 : ∀ x, d1 (d0 x) = 0

namespace Complex3

variable {X0 X1 X2 : Type*}
  [NormedAddCommGroup X0] [InnerProductSpace ℝ X0]
  [NormedAddCommGroup X1] [InnerProductSpace ℝ X1]
  [NormedAddCommGroup X2] [InnerProductSpace ℝ X2]
  (C : Complex3 X0 X1 X2)

/-- skew form `a(σ,u,ρ; τ,v,μ)` of the weak Hodge wave (4.7). -/
def a (σ : X0) (u : X1) (ρ : X2) (τ : X0) (v : X1) (μ : X2) : ℝ :=
  -⟪u, C.d0 τ⟫ + ⟪C.d0 σ, v⟫ + ⟪ρ, C.d1 v⟫ - ⟪C.d1 u, μ⟫

/-- `A = (·,·)_W + a` (the shifted form of §4.6). -/
def bigA (σ : X0) (u : X1) (ρ : X2) (τ : X0) (v : X1) (μ : X2) : ℝ :=
  ⟪σ, τ⟫ + ⟪u, v⟫ + ⟪ρ, μ⟫ + C.a σ u ρ τ v μ

/-- squared `V`-norm on `V0 × V1 × W2`. -/
def nV2 (σ : X0) (u : X1) (ρ : X2) : ℝ :=
  ‖σ‖ ^ 2 + ‖C.d0 σ‖ ^ 2 + ‖u‖ ^ 2 + ‖C.d1 u‖ ^ 2 + ‖ρ‖ ^ 2

theorem a_self (σ : X0) (u : X1) (ρ : X2) : C.a σ u ρ σ u ρ = 0 := by
  simp only [a, real_inner_comm (C.d0 σ) u, real_inner_comm (C.d1 u) ρ]; ring

/-- A subcomplex of the algebraic segment. -/
structure Sub where
  V0h : Submodule ℝ X0
  V1h : Submodule ℝ X1
  V2h : Submodule ℝ X2
  d0_mem : ∀ σ ∈ V0h, C.d0 σ ∈ V1h
  d1_mem : ∀ u ∈ V1h, C.d1 u ∈ V2h

end Complex3

/-! ## §F. BGG data (Ch 5–6): two complexes linked by `S₀, S₁` -/

/-- Top complex `V0 → V1 → W2`, bottom complex `Ṽ0 → Ṽ1 → W̃2`, connecting maps
`S0 : Ṽ0 → V1`, `S1 : Ṽ1 → W2`, anticommuting. Algebraic core only; analytic hypotheses
(closed ranges, continuity, completeness, regularity `d¹V¹ ⊆ d¹S₀Ṽ⁰`) are added per theorem. -/
structure BGGData (V0 V1 W2 Vt0 Vt1 Wt2 : Type*)
    [AddCommGroup V0] [Module ℝ V0] [AddCommGroup V1] [Module ℝ V1]
    [AddCommGroup W2] [Module ℝ W2] [AddCommGroup Vt0] [Module ℝ Vt0]
    [AddCommGroup Vt1] [Module ℝ Vt1] [AddCommGroup Wt2] [Module ℝ Wt2] where
  d0 : V0 →ₗ[ℝ] V1
  d1 : V1 →ₗ[ℝ] W2
  dt0 : Vt0 →ₗ[ℝ] Vt1
  dt1 : Vt1 →ₗ[ℝ] Wt2
  S0 : Vt0 →ₗ[ℝ] V1
  S1 : Vt1 →ₗ[ℝ] W2
  d1_d0 : ∀ σ, d1 (d0 σ) = 0
  dt1_dt0 : ∀ φ, dt1 (dt0 φ) = 0
  anticomm : ∀ φ, d1 (S0 φ) = -S1 (dt0 φ)

namespace BGGData

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [AddCommGroup V0] [Module ℝ V0] [AddCommGroup V1] [Module ℝ V1]
  [AddCommGroup W2] [Module ℝ W2] [AddCommGroup Vt0] [Module ℝ Vt0]
  [AddCommGroup Vt1] [Module ℝ Vt1] [AddCommGroup Wt2] [Module ℝ Wt2]
  (D : BGGData V0 V1 W2 Vt0 Vt1 Wt2)

/-- exactness hypotheses, stated separately so that they appear explicitly in theorems -/
def ExactTop : Prop := LinearMap.ker D.d1 = LinearMap.range D.d0
def ExactBot : Prop := LinearMap.ker D.dt1 = LinearMap.range D.dt0

/-- `Γ = {(σ, φ) | d σ = S φ}` -/
def Γ : Submodule ℝ (V0 × Vt0) :=
  LinearMap.ker (D.d0.comp (LinearMap.fst ℝ V0 Vt0) - D.S0.comp (LinearMap.snd ℝ V0 Vt0))

theorem mem_Γ {x : V0 × Vt0} : x ∈ D.Γ ↔ D.d0 x.1 = D.S0 x.2 := by
  simp [Γ, sub_eq_zero]

/-- first operator `(0 d) : Γ → Ṽ¹` of the complex (5.1) -/
def D0 : D.Γ →ₗ[ℝ] Vt1 := D.dt0.comp ((LinearMap.snd ℝ V0 Vt0).comp D.Γ.subtype)

/-- second operator `(S, d) : Ṽ¹ → W² × W̃²` of the complex (5.1) -/
def D1 : Vt1 →ₗ[ℝ] W2 × Wt2 := D.S1.prod D.dt1

theorem D1_D0 (x : D.Γ) : D.D1 (D.D0 x) = 0 := by
  obtain ⟨⟨σ, φ⟩, hx⟩ := x
  have h := D.d1_d0 σ
  rw [(D.mem_Γ).1 hx, D.anticomm] at h
  simp [D0, D1, neg_eq_zero.mp h, D.dt1_dt0]

end BGGData

/-! ## §G. Component tensors (Ch 2–3) -/

section Tensor

/-- (0,4)-tensor in components over an index type `ι`. -/
abbrev T4 (ι : Type*) := ι → ι → ι → ι → ℝ

variable {ι : Type*}

def PairSkew (C : T4 ι) : Prop :=
  ∀ a b c d, C a b c d = -C b a c d ∧ C a b c d = -C a b d c
def Bianchi1 (C : T4 ι) : Prop := ∀ a b c d, C a b c d + C a c d b + C a d b c = 0
def Interchange (C : T4 ι) : Prop := ∀ a b c d, C a b c d = C c d a b

/-- Minkowski metric, signature (−+++), diagonal entries. -/
def η : Fin 4 → ℝ := ![-1, 1, 1, 1]

/-- Levi-Civita symbol on `Fin 3` (determinant of basis rows). -/
def eps3 (i j k : Fin 3) : ℝ :=
  Matrix.det (Matrix.of ![Pi.single i (1 : ℝ), Pi.single j 1, Pi.single k 1])

/-- Levi-Civita symbol on `Fin 4`. -/
def eps4 (a b c d : Fin 4) : ℝ :=
  Matrix.det (Matrix.of ![Pi.single a (1 : ℝ), Pi.single b 1, Pi.single c 1, Pi.single d 1])

/-- first jet of a 3×3 matrix field: `dA c = ∂_c A`. -/
abbrev Jet1 := Fin 3 → Matrix (Fin 3) (Fin 3) ℝ

/-- row-wise curl, thesis convention `(curl A)_{ab} = ε_{bcd} ∂_c A_{ad}`. -/
def curl (dA : Jet1) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => ∑ c, ∑ d, eps3 b c d * dA c a d

/-- row-wise divergence `(div A)_a = ∂_b A_{ab}`. -/
def div (dA : Jet1) : Fin 3 → ℝ := fun a => ∑ b, dA b a b

/-- `(vskw A)_a = ½ ε_{abc} A_{bc}`. NB: the BGG map is `S₁ = 2·vskw` (thesis says `vskw`). -/
def vskw (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  fun a => (1 / 2 : ℝ) * ∑ b, ∑ c, eps3 a b c * A b c

/-- partial derivative of a scalar field on `ℝⁿ` (coordinates). -/
def pd {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

end Tensor

end Feec

/-! Sanity checks that the API elaborates. -/
section Checks
open Feec
example {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : E →ₗ.[ℝ] E) (T : ℝ) :
    WellPosedHom L T ↔ ∀ U₀ ∈ L.domain, ∃ U, IsStrongSolution L T U₀ 0 U := Iff.rfl
example : eps3 0 1 2 = 1 := by simp [eps3, Matrix.det_fin_three]
end Checks
