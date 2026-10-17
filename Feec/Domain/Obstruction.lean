module

public import Feec.Domain.ConstCoeffOp
public import Feec.HilbertComplex.InvariantCore
public import Feec.Evolution.Tangent

/-!
# Boundary obstructions to constraint propagation

A constraint subspace `K` of `L²(Ω)` may fail to be approximable by constrained fields satisfying
a boundary condition: `K ∩ D(A_min)` need not be dense in `K`. This file isolates the mechanism
behind the bounded-domain refutations of thesis Props 4.17/4.19, in general form.

## Main definitions and results

* `Feec.Domain.obstruction D K = K ⊓ (K ⊓ D)ᗮ`: the part of a closed subspace `K` that the
  constrained domain `K ∩ D` cannot approximate; `K = cl (K ∩ D) ⊕ obstruction D K`
  (`closure_sup_obstruction`), each `G ∈ obstruction D K` is at distance `‖G‖` from `K ∩ D`
  (`norm_le_norm_sub_of_mem_obstruction`), and `K ∩ D` is dense in `K` iff the obstruction
  vanishes (`dense_iff_obstruction_eq_bot`).
* **Boundary form.** `ConstCoeffOp.mem_minimal_domain_iff`: `u ∈ D(A_min)` iff the boundary form
  `⟪A_max u, v⟫ - ⟪u, (Aᵗ)_max v⟫` vanishes for all `v ∈ D((Aᵗ)_max)` (no traces needed);
  `ConstCoeffOp.formalAdj_mem_orthogonal`: a smooth field `ψ` with no boundary condition and
  `ψ ⊥ A_min (K ∩ D(A_min))` gives `Aᵗ ψ ⊥ K ∩ D(A_min)` (the "zero mean" / "normal trace"
  obstruction: `B n = 0` on `∂Ω` in the weak sense).
* **The `Ė(0)` argument** (`ShortHilbertComplex.adjoint_mem_closure_of_propagates`): if a strong
  solution of `U' = L U` from `(0, E₀, B₀)` keeps its middle component in `K₁` on `[0, T]`,
  `T > 0`, then `d₁† B₀ ∈ cl (K₁ ∩ D(d₁))`. Hence (`not_propagates_of_inner_ne_zero`) a single
  `G ⊥ K₁ ∩ D(d₁)` with `⟪G, d₁† B₀⟫ ≠ 0` makes every strong solution leave the constraint at
  once.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17, the projection and density hypotheses)
* [Arnold2018], §6.2 (minimal and maximal domains, boundary conditions)
-/

open scoped InnerProductSpace ContDiff ENNReal ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Domain

/-! ## Adjoints reverse extensions -/

section AdjointAntitone

variable {𝕜 : Type*} [RCLike 𝕜] {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- **Adjoints reverse extensions**: `T ≤ S` (densely defined `T`) implies `S† ≤ T†`. -/
theorem _root_.LinearPMap.adjoint_le_adjoint_of_le {T S : H₁ →ₗ.[𝕜] H₂}
    (hT : Dense (T.domain : Set H₁)) (h : T ≤ S) : S† ≤ T† := by
  refine LinearPMap.IsFormalAdjoint.le_adjoint hT fun x y => ?_
  have hS : Dense (S.domain : Set H₁) := hT.mono h.1
  have e : S ⟨(x : H₁), h.1 x.2⟩ = T x := (h.2 rfl).symm
  have h2 := LinearPMap.adjoint_isFormalAdjoint hS y ⟨(x : H₁), h.1 x.2⟩
  rw [e] at h2
  rw [← inner_conj_symm (x : H₁), h2, inner_conj_symm]

end AdjointAntitone

/-! ## The obstruction subspace -/

section Abstract

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The **obstruction** of a constraint subspace `K` for a domain `D`: the part of `K`
orthogonal to the constrained domain `K ∩ D`. -/
def obstruction (D K : Submodule 𝕜 H) : Submodule 𝕜 H := K ⊓ (K ⊓ D)ᗮ

variable {D K : Submodule 𝕜 H}

omit [CompleteSpace H] in
theorem mem_obstruction {G : H} : G ∈ obstruction D K ↔ G ∈ K ∧ ∀ z ∈ K ⊓ D, ⟪z, G⟫_𝕜 = 0 :=
  Iff.and Iff.rfl (Submodule.mem_orthogonal _ _)

omit [CompleteSpace H] in
theorem obstruction_eq : obstruction D K = K ⊓ (K ⊓ D).topologicalClosureᗮ := by
  rw [obstruction, Submodule.orthogonal_closure]

/-- `K = cl (K ∩ D) ⊕ obstruction D K` for closed `K`. -/
theorem closure_sup_obstruction (hK : IsClosed (K : Set H)) :
    (K ⊓ D).topologicalClosure ⊔ obstruction D K = K := by
  have hle : (K ⊓ D).topologicalClosure ≤ K :=
    Submodule.topologicalClosure_minimal _ inf_le_left hK
  have : CompleteSpace (K ⊓ D).topologicalClosure :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have h := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
  rw [obstruction_eq, inf_comm K ((K ⊓ D).topologicalClosureᗮ)]
  exact h

omit [CompleteSpace H] in
/-- Every element of the obstruction is at distance `‖G‖` from `K ∩ D`. -/
theorem norm_le_norm_sub_of_mem_obstruction {G z : H} (hG : G ∈ obstruction D K)
    (hz : z ∈ K ⊓ D) : ‖G‖ ≤ ‖G - z‖ := by
  have h0 : ⟪z, G⟫_𝕜 = 0 := (mem_obstruction.1 hG).2 z hz
  have h : ‖G - z‖ ^ 2 = ‖G‖ ^ 2 + ‖z‖ ^ 2 := by
    rw [@norm_sub_sq 𝕜, inner_eq_zero_symm.1 h0, map_zero]
    ring
  nlinarith [norm_nonneg G, norm_nonneg (G - z), sq_nonneg ‖z‖]

/-- `K ∩ D` is dense in a closed `K` iff the obstruction vanishes. -/
theorem dense_iff_obstruction_eq_bot (hK : IsClosed (K : Set H)) :
    (K ⊓ D).topologicalClosure = K ↔ obstruction D K = ⊥ := by
  constructor
  · intro h
    rw [obstruction_eq, h, Submodule.inf_orthogonal_eq_bot]
  · intro h
    have := closure_sup_obstruction (D := D) hK
    rwa [h, sup_bot_eq] at this

end Abstract

/-! ## Boundary forms of constant-coefficient operators -/

namespace ConstCoeffOp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
  {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ] {Ω : Set E}
  (A : ConstCoeffOp E 𝕜 ι κ)

/-- `A_min = ((Aᵗ)_max)†`. -/
theorem adjoint_formalAdj_maximal (hΩ : IsOpen Ω) :
    (A.formalAdj.maximal Ω)† = A.minimal Ω := by
  rw [A.formalAdj.adjoint_maximal hΩ, formalAdj_formalAdj]

/-- **The minimal domain is the kernel of the boundary form**: `u ∈ D(A_min)` iff there is `w`
with `⟪w, v⟫ = ⟪u, (Aᵗ)_max v⟫` for every `v ∈ D((Aᵗ)_max)`; then `w = A_min u`. -/
theorem mem_minimal_domain_iff (hΩ : IsOpen Ω) {u : L2F 𝕜 Ω ι} :
    u ∈ (A.minimal Ω).domain ↔ ∃ w : L2F 𝕜 Ω κ, ∀ v : (A.formalAdj.maximal Ω).domain,
      ⟪w, (v : L2F 𝕜 Ω κ)⟫_𝕜 = ⟪u, A.formalAdj.maximal Ω v⟫_𝕜 := by
  rw [← A.adjoint_formalAdj_maximal hΩ]
  constructor
  · intro hu
    exact ⟨_, LinearPMap.adjoint_isFormalAdjoint (A.formalAdj.dense_maximal_domain hΩ) ⟨u, hu⟩⟩
  · rintro ⟨w, hw⟩
    exact LinearPMap.mem_adjoint_domain_of_exists _ ⟨w, hw⟩

/-- **Green's formula with vanishing boundary form**: for `u ∈ D(A_min)` and
`v ∈ D((Aᵗ)_max)`, `⟪A_min u, v⟫ = ⟪u, (Aᵗ)_max v⟫`. -/
theorem inner_minimal_eq_inner_maximal (hΩ : IsOpen Ω) (u : (A.minimal Ω).domain)
    (v : (A.formalAdj.maximal Ω).domain) :
    ⟪A.minimal Ω u, (v : L2F 𝕜 Ω κ)⟫_𝕜 = ⟪(u : L2F 𝕜 Ω ι), A.formalAdj.maximal Ω v⟫_𝕜 := by
  have h := LinearPMap.adjoint_isFormalAdjoint (A.formalAdj.dense_maximal_domain hΩ)
    ⟨(u : L2F 𝕜 Ω ι), by rw [A.adjoint_formalAdj_maximal hΩ]; exact u.2⟩ v
  have e : (A.formalAdj.maximal Ω)† ⟨(u : L2F 𝕜 Ω ι), by
      rw [A.adjoint_formalAdj_maximal hΩ]; exact u.2⟩ = A.minimal Ω u := by
    have key : ∀ T : L2F 𝕜 Ω ι →ₗ.[𝕜] L2F 𝕜 Ω κ, T = A.minimal Ω →
        ∀ hu : (u : L2F 𝕜 Ω ι) ∈ T.domain, T ⟨u, hu⟩ = A.minimal Ω u := by
      rintro _ rfl hu; rfl
    exact key _ (A.adjoint_formalAdj_maximal hΩ) _
  rw [e] at h
  exact h

/-- **The normal-trace obstruction.** Let `ψ` be a `C^N` field on `E` (`N ≥` the order of `A`),
with **no boundary condition**, such that `ψ, Aᵗ ψ ∈ L²(Ω)` and `ψ ⊥ A_min u` for every
`u ∈ K ∩ D(A_min)`. Then `Aᵗ ψ ⊥ K ∩ D(A_min)`. -/
theorem formalAdj_mem_orthogonal (hΩ : IsOpen Ω) {N : ℕ} (hA : A.IsOrderLE N)
    {K : Submodule 𝕜 (L2F 𝕜 Ω ι)} {ψ : κ → E → 𝕜} (hψs : ∀ j, ContDiff ℝ N (ψ j))
    (hψ : ∀ j, MemLp (ψ j) 2 (volume.restrict Ω))
    (hAψ : ∀ i, MemLp (A.formalAdj.apply ψ i) 2 (volume.restrict Ω))
    (horth : ∀ u : (A.minimal Ω).domain, (u : L2F 𝕜 Ω ι) ∈ K →
      ⟪A.minimal Ω u, toL2F hψ⟫_𝕜 = 0) :
    toL2F hAψ ∈ (K ⊓ (A.minimal Ω).domain)ᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro u ⟨huK, hu⟩
  rw [← A.minimal_green hΩ hA ⟨u, hu⟩ hψs hψ hAψ]
  exact horth ⟨u, hu⟩ huK

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

/-- **The tangent condition at every time**: if a strong solution of `U' = L U` on `[0, T]`,
`T > 0`, keeps its middle component in `K₁`, then
`d₀ U₀(t) - d₁† U₂(t) ∈ cl (K₁ ∩ D(d₁))` for every `t ∈ [0, T]`. -/
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

/-- **The `Ė(0)` argument** (thesis' proof of Prop 4.17): if a strong solution of `U' = L U`
from `(0, E₀, B₀)` keeps its middle component in `K₁` on `[0, T]`, `T > 0`, then
`d₁† B₀ ∈ cl (K₁ ∩ D(d₁))`. -/
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

/-- **Instantaneous loss of the constraint.** If `G ⊥ K₁ ∩ D(d₁)` and `⟪G, d₁† B₀⟫ ≠ 0`, then
for every `T > 0` every strong solution of `U' = L U` on `[0, T]` from `(0, E₀, B₀)` has its
middle component outside `K₁` at some `t ∈ [0, T]`. -/
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
