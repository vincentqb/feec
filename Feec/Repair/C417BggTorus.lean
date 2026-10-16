module

public import Feec.Ch6.Whole
public import Feec.Ch4.TorusSym
public import Feec.Ch4.Unconditional

/-!
# Chapter 6 on the flat torus `𝕋³`: the BGG weak-symmetry system propagates TSD

The Ch. 6 method of the thesis ([QuennevilleBelair2015, §6.1, §6.3]) is the Hodge wave equation
of the BGG complex (5.1), with the symmetry of `E` imposed weakly through `M`. On bounded domains
with the §6.3 boundary conditions it loses the TSD constraint
(`Feec.Ch6.Bounded.bggComplex_verdict`); on `ℝ³` it keeps it (`Feec.Ch6.Whole.bggWhole_verdict`).
This file proves the periodic version, on the Fourier side `ℓ²(ℤ³)` of `Feec.Ch4.Torus`, with
the fibre algebra of `Feec.Ch6.Whole` at the frequencies `ζ = 2πk`:
`L²(𝕋³) ⊇ H²(𝕋³) --grad grad--> H(curl; M) --(S₁, curl)--> L²(V) × L²(M)`
(`bggTorus`). It is also the periodic complex compressed in `Feec.Repair.C417BggCube` to the box
with mirror boundary conditions.

## Main results

* `bggTorus`, and the hypotheses of `Feec.Constraints.prop_4_17` for `S1 = L²(TSD)`,
  `S2 = {0} × L²(TSD)`: `L2TSD_le_ker_bggT`, `bggT_mem_L2TSDBT`, `adjoint_bggT_mem_L2TSD`,
  `projKc_mem_domL_bggT`.
* **`bggTorus_verdict`**: for `E₀, B₀ ∈ L²(TSD) ∩ H(curl)`, existence (Stone) and uniqueness
  of a classical solution from `(0, E₀, (0, B₀))`, with `σ ≡ 0`, `u(t) ∈ L²(TSD)`,
  `(M, B)(t) = (0, B(t))`, `B(t) ∈ L²(TSD)`, solving (4.15).

## References

* [QuennevilleBelair2015], Ch. 5 (§5.1, (5.1)), Ch. 6 (§6.1, §6.3), §3.4 (Lemma 3.5)
* [ArnoldHu2021] (BGG), [AFW2010] (Hilbert complexes), [Pazy1983], §1.10
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open LinearPMap Set

namespace Feec.Repair.C417

open Feec.Torus Feec.Constraints Feec.HilbertComplex2
open Feec.Ch6.Whole (VM hessSym bggSym skwSym bggSym_apply bggSym_hessSym adjoint_bggSym_apply
  adjoint_hessSym_of_mem_tsd tsdB mem_tsdB starProjection_tsdB inrM inrM_apply fstV sndM
  fstV_apply sndM_apply norm_bggSym_proj_le norm_adjoint_bggSym_proj_le skwSym_eq_zero_of_symm
  norm_toLp_zero)

/-- A bounded fibre map preserves `ℓ²`. -/
theorem memℓp_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] F) (u : L2 Z3 E) :
    Memℓp (fun k => B (u k)) 2 := by
  have hg : Memℓp (fun k => ‖B‖ * ‖u k‖) 2 := by
    have := (memℓp_norm_iff.2 (lp.memℓp u)).const_smul ‖B‖
    convert this using 1
  refine hg.mono' fun k => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact B.le_opNorm _

/-- Scalar fields on `𝕋³` (Fourier coefficients). -/
abbrev L2RT := L2 Z3 ℂ
/-- Pairs `(M, B)` of a vector and a matrix field on `𝕋³` (Fourier coefficients). -/
abbrev L2WT := L2 Z3 VM

/-- `grad grad` on `𝕋³`, `û ↦ -û ζ ζᵀ`. -/
def hessTT : L2RT →ₗ.[ℝ] L2M := mulOp fun k => hessSym (freq k)

/-- `(S₁, curl)` on `𝕋³`. -/
def bggT : L2M →ₗ.[ℝ] L2WT := mulOp fun k => bggSym (freq k)

/-- **The BGG complex (5.1) on `𝕋³`.** -/
def bggTorus : HilbertComplex2 L2RT L2M L2WT where
  d0 := hessTT
  d1 := bggT
  dense0 := dense_mulDomain _
  dense1 := dense_mulDomain _
  closed0 := isClosed_mulOp _
  closed1 := isClosed_mulOp _
  map_mem x := by
    change Memℓp _ 2
    convert (zero_memℓp : Memℓp (0 : Z3 → VM) 2) using 1
    funext k
    exact bggSym_hessSym _ _
  comp_zero x := by
    refine lp.ext (funext fun k => ?_)
    rw [lp.coeFn_zero, Pi.zero_apply]
    exact bggSym_hessSym _ _

/-- `{0} × L²(TSD)` on `𝕋³`. -/
abbrev L2TSDBT : Submodule ℝ L2WT := fibreSub fun k => tsdB (freq k)

theorem projTSDBT_apply (ρ : L2WT) (k : Z3) :
    L2TSDBT.starProjection ρ k = (tsdB (freq k)).starProjection (ρ k) :=
  starProjection_fibreSub_apply _ ρ k

/-- `L²(TSD) ⊆ ker (grad grad)*`. -/
theorem L2TSD_le_ker_bggT : L2TSD ≤ bggTorus.d0†.ker := by
  intro A hA
  change A ∈ hessTT†.ker
  have hdom : A ∈ hessTT†.domain := by
    rw [hessTT, adjoint_mulOp]
    change Memℓp _ 2
    convert (zero_memℓp : Memℓp (0 : Z3 → ℂ) 2) using 1
    funext k
    exact adjoint_hessSym_of_mem_tsd (hA k)
  refine LinearPMap.mem_ker_iff.2 ⟨⟨A, hdom⟩, rfl, lp.ext (funext fun k => ?_)⟩
  rw [lp.coeFn_zero, Pi.zero_apply]
  exact (adjoint_mulOp_apply (fun k => hessSym (freq k)) ⟨A, hdom⟩ k).trans
    (adjoint_hessSym_of_mem_tsd (hA k))

/-- `(S₁, curl)` maps `H(curl) ∩ L²(TSD)` into `{0} × L²(TSD)`. -/
theorem bggT_mem_L2TSDBT (u : bggTorus.d1.domain) (hu : (u : L2M) ∈ L2TSD) :
    bggTorus.d1 u ∈ L2TSDBT := fun k => by
  change bggSym (freq k) ((u : L2M) k) ∈ tsdB (freq k)
  rw [bggSym_apply, mem_tsdB, WithLp.ofLp_toLp]
  exact ⟨skwSym_eq_zero_of_symm (hu k).1, curlSym_mem_tsd (hu k)⟩

/-- `(S₁, curl)* (0, B) = curl B` maps `{0} × L²(TSD)` into `L²(TSD)`. -/
theorem adjoint_bggT_mem_L2TSD (ρ : bggTorus.d1†.domain) (hρ : (ρ : L2WT) ∈ L2TSDBT) :
    bggTorus.d1† ρ ∈ L2TSD := fun k => by
  have h := adjoint_mulOp_apply (fun k => bggSym (freq k)) ρ k
  change (bggTorus.d1† ρ : L2M) k ∈ tsd (freq k)
  obtain ⟨h1, h2⟩ := mem_tsdB.1 (hρ k)
  rw [show (bggTorus.d1† ρ : L2M) k = _ from h, adjoint_bggSym_apply, h1, _root_.map_zero,
    zero_add]
  exact curlSym_mem_tsd h2

/-- **The projection hypothesis holds for the Ch. 6 complex on `𝕋³`.** -/
theorem projKc_mem_domL_bggT : ∀ x ∈ bggTorus.domL,
    projKc L2RT L2TSD L2TSDBT x ∈ bggTorus.domL := by
  intro x hx
  rw [Constraints.mem_domL] at hx ⊢
  rw [tot_projKc]
  obtain ⟨-, hu, hρ⟩ := hx
  refine ⟨bggTorus.d0.domain.zero_mem, ⟨?_, ?_⟩, ?_⟩
  · have hu1 : (tot L2RT L2M L2WT x).2.1 ∈ bggT.domain := (Submodule.mem_inf.1 hu).1
    change Memℓp _ 2
    refine Memℓp.mono' hu1 fun k => ?_
    rw [projTSD_apply]
    exact norm_bggSym_proj_le _ _
  · exact (LinearPMap.mem_ker_iff.1 (L2TSD_le_ker_bggT (L2TSD.starProjection_apply_mem _))).elim
      fun y hy => hy.1 ▸ y.2
  · have hρ' : (tot L2RT L2M L2WT x).2.2 ∈ bggT†.domain := hρ
    change L2TSDBT.starProjection (tot L2RT L2M L2WT x).2.2 ∈ bggT†.domain
    rw [bggT, adjoint_mulOp] at hρ' ⊢
    change Memℓp _ 2
    change Memℓp _ 2 at hρ'
    set ρ := (tot L2RT L2M L2WT x).2.2
    have hs : Memℓp (fun k => (ContinuousLinearMap.adjoint skwSym ∘L fstV) (ρ k)) 2 :=
      memℓp_clm _ ρ
    refine Memℓp.mono' (hρ'.sub hs) fun k => ?_
    rw [projTSDBT_apply]
    exact norm_adjoint_bggSym_proj_le _ _

/-- The embedding `B ↦ (0, B)`. -/
def embBT : L2M →L[ℝ] L2WT :=
  LinearMap.mkContinuous
    { toFun := fun B => ⟨fun k => inrM (B k), (lp.memℓp B).mono' fun k => by
        rw [inrM_apply, norm_toLp_zero]⟩
      map_add' := fun B B' => lp.ext (funext fun k => by
        change inrM ((B + B' : L2M) k) = inrM (B k) + inrM (B' k)
        rw [lp.coeFn_add, Pi.add_apply, _root_.map_add])
      map_smul' := fun r B => lp.ext (funext fun k => by
        change inrM ((r • B : L2M) k) = r • inrM (B k)
        rw [lp.coeFn_smul, Pi.smul_apply, _root_.map_smul]) }
    1 fun B => by
      rw [one_mul]
      refine lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg _) fun s => ?_
      refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => ?_)
        (lp.sum_rpow_le_norm_rpow (by norm_num) B s)
      change ‖inrM (B k)‖ ^ _ = _
      rw [inrM_apply, norm_toLp_zero]

theorem embBT_apply (B : L2M) (k : Z3) : embBT B k = inrM (B k) := rfl

/-- `ρ ∈ {0} × L²(TSD)` iff `ρ = (0, B)` with `B ∈ L²(TSD)`. -/
theorem mem_L2TSDBT_iff {ρ : L2WT} : ρ ∈ L2TSDBT ↔ ∃ B ∈ L2TSD, ρ = embBT B := by
  constructor
  · intro hρ
    refine ⟨⟨fun k => sndM (ρ k), memℓp_clm sndM ρ⟩, fun k => ?_, lp.ext (funext fun k => ?_)⟩
    · exact (mem_tsdB.1 (hρ k)).2
    · change ρ k = inrM (sndM (ρ k))
      rw [inrM_apply, sndM_apply, ← (mem_tsdB.1 (hρ k)).1]
  · rintro ⟨B, hB, rfl⟩ k
    rw [embBT_apply, inrM_apply, mem_tsdB, WithLp.ofLp_toLp]
    exact ⟨rfl, hB k⟩

theorem ini_mem_domL_bggT {E₀ B₀ : L2M} (hE₀ : E₀ ∈ L2TSD) (hE₀c : E₀ ∈ Hcurl)
    (hB₀c : B₀ ∈ Hcurl) : ini L2RT E₀ (embBT B₀) ∈ bggTorus.domL := by
  rw [Constraints.mem_domL, tot_ini]
  refine ⟨bggTorus.d0.domain.zero_mem, ⟨?_, ?_⟩, ?_⟩
  · change Memℓp (fun k => bggSym (freq k) (E₀ k)) 2
    refine Memℓp.mono' (hE₀c : Memℓp (fun k => curlSym (freq k) (E₀ k)) 2) fun k => ?_
    rw [bggSym_apply, skwSym_eq_zero_of_symm (hE₀ k).1, norm_toLp_zero]
  · exact (LinearPMap.mem_ker_iff.1 (L2TSD_le_ker_bggT hE₀)).elim fun y hy => hy.1 ▸ y.2
  · change embBT B₀ ∈ bggT†.domain
    rw [bggT, adjoint_mulOp]
    show Memℓp (fun k => ContinuousLinearMap.adjoint (bggSym (freq k)) (embBT B₀ k)) 2
    have e : (fun k => ContinuousLinearMap.adjoint (bggSym (freq k)) (embBT B₀ k)) =
        fun k => curlSym (freq k) (B₀ k) := funext fun k => by
      rw [embBT_apply, inrM_apply, adjoint_bggSym_apply, WithLp.ofLp_toLp, _root_.map_zero,
        zero_add]
    rw [e]
    exact hB₀c

/-- **Ch. 6 on `𝕋³`: TSD propagates.** For `E₀, B₀ ∈ L²(TSD) ∩ H(curl)` the Hodge wave equation
of the BGG complex (5.1) on `𝕋³` has a classical solution from `(0, E₀, (0, B₀))` (Stone's
theorem), unique among strong solutions, with `σ(t) = 0`, `u(t) ∈ L²(TSD)` (the weakly imposed
symmetry holds strongly) and `(M, B)(t) = (0, B(t))`, `B(t) ∈ L²(TSD)` for all `t ∈ [0, T]`;
`(u, (M, B))` solves (4.15). Periodic counterpart of `Feec.Ch6.Whole.bggWhole_verdict`. -/
theorem bggTorus_verdict (T : ℝ) {E₀ B₀ : L2M} (hE₀ : E₀ ∈ L2TSD) (hB₀ : B₀ ∈ L2TSD)
    (hE₀c : E₀ ∈ Hcurl) (hB₀c : B₀ ∈ Hcurl) :
    ∃ U, IsClassicalSolution (-bggTorus.waveOp) T (ini L2RT E₀ (embBT B₀)) 0 U ∧
      (∀ U', IsStrongSolution (-bggTorus.waveOp) T (ini L2RT E₀ (embBT B₀)) 0 U' →
        EqOn U' U (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (tot L2RT L2M L2WT (U t)).1 = 0 ∧ (tot L2RT L2M L2WT (U t)).2.1 ∈ L2TSD ∧
        ∃ B ∈ L2TSD, (tot L2RT L2M L2WT (U t)).2.2 = embBT B) ∧
      IsReducedSolution bggTorus T E₀ (embBT B₀) (fun t => (tot L2RT L2M L2WT (U t)).2.1)
        (fun t => (tot L2RT L2M L2WT (U t)).2.2) := by
  have hρ₀ : embBT B₀ ∈ L2TSDBT := mem_L2TSDBT_iff.2 ⟨B₀, hB₀, rfl⟩
  obtain ⟨U, hU, hK, hR, huniq⟩ := prop_4_17_exists_unconditional L2TSD_le_ker_bggT
    projKc_mem_domL_bggT bggT_mem_L2TSDBT adjoint_bggT_mem_L2TSD T hE₀ hρ₀
    (ini_mem_domL_bggT hE₀ hE₀c hB₀c)
  refine ⟨U, hU, huniq, fun t ht => ?_, hR⟩
  have hk' := (mem_Kc (W0 := L2RT) (S1 := L2TSD) (S2 := L2TSDBT)).1 (hK t ht)
  exact ⟨hk'.1, hk'.2.1, mem_L2TSDBT_iff.1 hk'.2.2⟩

end Feec.Repair.C417
