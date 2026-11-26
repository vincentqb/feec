module

public import Feec.Domain.ConstCoeffOp
public import Feec.HilbertComplex.InvariantCore
public import Feec.Evolution.Tangent

/-!
# Boundary obstructions to constraint propagation

The obstruction `K ⊓ (K ⊓ D)ᗮ` is the part of a closed constraint subspace `K` that `K ∩ D` cannot
approximate; for a short Hilbert complex, a `G ⊥ K₁ ∩ D(d₁)` with `⟪G, d₁† B₀⟫ ≠ 0` makes every
strong solution of `U' = L U` from `(0, E₀, B₀)` leave `K₁` within every `[0, T]`.

## Main results

* `dense_iff_obstruction_eq_bot`: `K ∩ D` is dense in `K` iff the obstruction vanishes.
* `ShortHilbertComplex.adjoint_mem_closure_of_propagates`: the `Ė(0)` argument.
* `ShortHilbertComplex.not_propagates_of_inner_ne_zero`: the loss of the constraint.
-/

open scoped InnerProductSpace ContDiff ENNReal ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Domain

/-! ## Adjoints reverse extensions -/

section AdjointAntitone

variable {𝕜 : Type*} [RCLike 𝕜] {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

theorem _root_.LinearPMap.adjoint_le_adjoint_of_le {T S : H₁ →ₗ.[𝕜] H₂}
    (hT : Dense (T.domain : Set H₁)) (h : T ≤ S) : S† ≤ T† := by
  refine LinearPMap.IsFormalAdjoint.le_adjoint hT fun x y => ?_
  have hS : Dense (S.domain : Set H₁) := hT.mono h.1
  have e : S ⟨(x : H₁), h.1 x.2⟩ = T x := (h.2 rfl).symm
  have h2 := LinearPMap.adjoint_isFormalAdjoint hS y ⟨(x : H₁), h.1 x.2⟩
  rw [e] at h2
  rw [← inner_conj_symm (x : H₁), h2, inner_conj_symm]

end AdjointAntitone

/-! ## Closed-graph bound behind the projection hypotheses -/

section ClosedGraph

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

theorem _root_.LinearPMap.exists_norm_apply_le_of_mapsTo {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (P : E →L[𝕜] E) (hP : ∀ x : T.domain, P x ∈ T.domain) :
    ∃ C : ℝ, ∀ x : T.domain, ‖T ⟨P x, hP x⟩‖ ≤ C * ‖((x : E), T x)‖ := by
  have : CompleteSpace T.graph :=
    (show IsClosed (T.graph : Set (E × F)) from hT).completeSpace_coe
  have hdom : ∀ p : T.graph, P (p : E × F).1 ∈ T.domain := fun p =>
    hP ⟨_, LinearPMap.mem_domain_of_mem_graph (y := (p : E × F).2) p.2⟩
  let g0 : T.graph →ₗ[𝕜] T.domain := LinearMap.codRestrict T.domain
    ((P : E →L[𝕜] E).toLinearMap ∘ₗ (LinearMap.fst 𝕜 E F) ∘ₗ T.graph.subtype) hdom
  let g : T.graph →ₗ[𝕜] F := T.toFun ∘ₗ g0
  have hgc : IsClosed (g.graph : Set (T.graph × F)) := by
    have e : (g.graph : Set (T.graph × F)) =
        (fun q : T.graph × F => (P (q.1 : E × F).1, q.2)) ⁻¹' (T.graph : Set (E × F)) := by
      ext ⟨p, y⟩
      simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, mem_preimage]
      constructor
      · rintro rfl
        exact T.mem_graph (g0 p)
      · intro h
        obtain ⟨z, hz1, hz2⟩ := T.mem_graph_iff.1 h
        have e1 : z = g0 p := Subtype.ext hz1
        change y = T (g0 p)
        rw [← e1]
        exact hz2.symm
    rw [e]
    exact hT.preimage ((P.continuous.comp
      (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd)
  let gc : T.graph →L[𝕜] F := ⟨g, g.continuous_of_isClosed_graph hgc⟩
  refine ⟨‖gc‖, fun x => ?_⟩
  have hp : ((x : E), T x) ∈ T.graph := T.mem_graph x
  have h := gc.le_opNorm ⟨_, hp⟩
  have e : gc ⟨_, hp⟩ = T ⟨P x, hP x⟩ := rfl
  rw [e] at h
  exact h

end ClosedGraph

/-! ## The obstruction subspace -/

section Abstract

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The **obstruction** of `K` for `D`: the part of `K` orthogonal to `K ∩ D`. -/
def obstruction (D K : Submodule 𝕜 H) : Submodule 𝕜 H := K ⊓ (K ⊓ D)ᗮ

variable {D K : Submodule 𝕜 H}

omit [CompleteSpace H] in
theorem mem_obstruction {G : H} : G ∈ obstruction D K ↔ G ∈ K ∧ ∀ z ∈ K ⊓ D, ⟪z, G⟫_𝕜 = 0 :=
  Iff.and Iff.rfl (Submodule.mem_orthogonal _ _)

omit [CompleteSpace H] in
theorem obstruction_eq : obstruction D K = K ⊓ (K ⊓ D).topologicalClosureᗮ := by
  rw [obstruction, Submodule.orthogonal_closure]

theorem closure_sup_obstruction (hK : IsClosed (K : Set H)) :
    (K ⊓ D).topologicalClosure ⊔ obstruction D K = K := by
  have hle : (K ⊓ D).topologicalClosure ≤ K :=
    Submodule.topologicalClosure_minimal _ inf_le_left hK
  have : CompleteSpace (K ⊓ D).topologicalClosure :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have h := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
  rw [obstruction_eq, inf_comm K ((K ⊓ D).topologicalClosureᗮ)]
  exact h

/-- `K ∩ D` is dense in a closed `K` iff the obstruction vanishes. -/
theorem dense_iff_obstruction_eq_bot (hK : IsClosed (K : Set H)) :
    (K ⊓ D).topologicalClosure = K ↔ obstruction D K = ⊥ := by
  constructor
  · intro h
    rw [obstruction_eq, h, Submodule.inf_orthogonal_eq_bot]
  · intro h
    have := closure_sup_obstruction (D := D) hK
    rwa [h, sup_bot_eq] at this

omit [CompleteSpace H] in
theorem topologicalClosure_inf_eq_of_mapsTo [K.HasOrthogonalProjection] {s : Set H}
    (hs : Dense s) (hP : Set.MapsTo K.starProjection s D) : (K ⊓ D).topologicalClosure = K := by
  have h := Kᗮ.orthogonal_le_topologicalClosure_of_dense hs (K ⊓ D) fun v hv => by
    rw [Submodule.starProjection_orthogonal_val, sub_sub_cancel]
    exact ⟨K.starProjection_apply_mem v, hP hv⟩
  rw [K.orthogonal_orthogonal] at h
  exact h.antisymm' (Submodule.topologicalClosure_minimal _ inf_le_left
    (K.orthogonal_orthogonal ▸ Kᗮ.isClosed_orthogonal))

end Abstract

/-! ## Boundary forms of constant-coefficient operators -/

namespace ConstCoeffOp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
  {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ] {Ω : Set E}
  (A : ConstCoeffOp E 𝕜 ι κ)

theorem adjoint_formalAdj_maximal (hΩ : IsOpen Ω) :
    (A.formalAdj.maximal Ω)† = A.minimal Ω := by
  rw [A.formalAdj.adjoint_maximal hΩ, formalAdj_formalAdj]

theorem mem_minimal_domain_iff (hΩ : IsOpen Ω) {u : L2F 𝕜 Ω ι} :
    u ∈ (A.minimal Ω).domain ↔ ∃ w : L2F 𝕜 Ω κ, ∀ v : (A.formalAdj.maximal Ω).domain,
      ⟪w, (v : L2F 𝕜 Ω κ)⟫_𝕜 = ⟪u, A.formalAdj.maximal Ω v⟫_𝕜 := by
  rw [← A.adjoint_formalAdj_maximal hΩ]
  constructor
  · intro hu
    exact ⟨_, LinearPMap.adjoint_isFormalAdjoint (A.formalAdj.dense_maximal_domain hΩ) ⟨u, hu⟩⟩
  · rintro ⟨w, hw⟩
    exact LinearPMap.mem_adjoint_domain_of_exists _ ⟨w, hw⟩

end ConstCoeffOp

end Feec.Domain

/-! ## The `Ė(0)` argument for short complexes -/

namespace Feec.ShortHilbertComplex

open Feec.Evolution

universe u

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
  (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂)

theorem wave_one_mem_closure_of_propagates [NormedSpace ℝ (PiLp 2 (W3 W₀ W₁ W₂))]
    [IsScalarTower ℝ 𝕜 (PiLp 2 (W3 W₀ W₁ W₂))] {K₁ : Submodule 𝕜 W₁} {T : ℝ} (hT : 0 < T)
    {U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)} (hU : IsStrongSolution S.wave (Icc 0 T) 0 U)
    (hK : ∀ t ∈ Icc 0 T, ((U t : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁) ∈ K₁) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ((S.wave ⟨U t, hU.mem_domain ht⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁) ∈
      (K₁ ⊓ S.d₁.domain).topologicalClosure := by
  set Z := (K₁ ⊓ S.d₁.domain).topologicalClosure
  let K' : Submodule 𝕜 (PiLp 2 (W3 W₀ W₁ W₂)) :=
    { carrier := {x | ((x : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁) ∈ Z}
      add_mem' := fun ha hb => Z.add_mem ha hb
      zero_mem' := Z.zero_mem
      smul_mem' := fun c _ hx => Z.smul_mem c hx }
  have hK' : IsClosed (K' : Set (PiLp 2 (W3 W₀ W₁ W₂))) :=
    (Submodule.isClosed_topologicalClosure (K₁ ⊓ S.d₁.domain)).preimage
      (PiLp.continuous_apply 2 (W3 W₀ W₁ W₂) 1)
  have hmem : ∀ s ∈ Icc 0 T, U s ∈ K' := by
    intro s hs
    refine Submodule.le_topologicalClosure _ ⟨hK s hs, ?_⟩
    exact ((S.mem_wave_domain).1 (hU.mem_domain hs)).2.1
  have h := hU.deriv_mem_of_mem hT hK' hmem ht
  rw [Pi.zero_apply, add_zero] at h
  exact h

/-- **The `Ė(0)` argument**: a strong solution of `U' = L U` from `(0, E₀, B₀)` keeping `K₁` on
`[0, T]`, `T > 0`, has `d₁† B₀ ∈ cl (K₁ ∩ D(d₁))`. -/
theorem adjoint_mem_closure_of_propagates [NormedSpace ℝ (PiLp 2 (W3 W₀ W₁ W₂))]
    [IsScalarTower ℝ 𝕜 (PiLp 2 (W3 W₀ W₁ W₂))] {K₁ : Submodule 𝕜 W₁} {T : ℝ} (hT : 0 < T)
    {U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)} (hU : IsStrongSolution S.wave (Icc 0 T) 0 U)
    (h0 : ((U 0 : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀) = 0)
    (hK : ∀ t ∈ Icc 0 T, ((U t : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁) ∈ K₁) :
    ∃ hB : ((U 0 : PiLp 2 (W3 W₀ W₁ W₂)) 2 : W₂) ∈ S.d₁†.domain,
      (S.d₁† ⟨_, hB⟩ : W₁) ∈ (K₁ ⊓ S.d₁.domain).topologicalClosure := by
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hD := (S.mem_wave_domain).1 (hU.mem_domain h0T)
  refine ⟨hD.2.2.2, ?_⟩
  have h := S.wave_one_mem_closure_of_propagates hT hU hK h0T
  rw [S.wave_apply_one] at h
  have e : S.d₀ ⟨((U 0 : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀), hD.1⟩ = 0 := by
    have : (⟨((U 0 : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀), hD.1⟩ : S.d₀.domain) = 0 := Subtype.ext h0
    rw [this, LinearPMap.map_zero]
  rw [e, zero_sub] at h
  have := (Submodule.neg_mem_iff _).1 h
  convert this using 2

/-- **Instantaneous loss of the constraint** when `G ⊥ K₁ ∩ D(d₁)` and `⟪G, d₁† B₀⟫ ≠ 0`. -/
theorem not_propagates_of_inner_ne_zero [NormedSpace ℝ (PiLp 2 (W3 W₀ W₁ W₂))]
    [IsScalarTower ℝ 𝕜 (PiLp 2 (W3 W₀ W₁ W₂))] {K₁ : Submodule 𝕜 W₁} {G : W₁}
    (hG : G ∈ (K₁ ⊓ S.d₁.domain)ᗮ) (B₀ : S.d₁†.domain) (hB : ⟪G, S.d₁† B₀⟫_𝕜 ≠ 0) {T : ℝ}
    (hT : 0 < T) {U : ℝ → PiLp 2 (W3 W₀ W₁ W₂)} (hU : IsStrongSolution S.wave (Icc 0 T) 0 U)
    (h0 : ((U 0 : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀) = 0)
    (h2 : ((U 0 : PiLp 2 (W3 W₀ W₁ W₂)) 2 : W₂) = (B₀ : W₂)) :
    ∃ t ∈ Icc 0 T, ((U t : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁) ∉ K₁ := by
  by_contra hall
  push Not at hall
  obtain ⟨hB', hmem⟩ := S.adjoint_mem_closure_of_propagates hT hU h0 hall
  have e : (⟨_, hB'⟩ : S.d₁†.domain) = B₀ := Subtype.ext h2
  rw [e] at hmem
  rw [← Submodule.orthogonal_closure] at hG
  exact hB (inner_eq_zero_symm.1 ((Submodule.mem_orthogonal _ _).1 hG _ hmem))

end Feec.ShortHilbertComplex
