module

public import Feec.FiniteElement.WeakSymmetryMaps
public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.HilbertComplex.BGG.ToComplex
public import Feec.HilbertComplex.BGG.Discrete
public import Feec.HilbertComplex.BGG.WeakSymmetry

/-!
# The continuous BGG data (4.16) on the cube

The complex of [QuennevilleBelair2015], §5.3, on `Q = (0, ½)³` with the thesis' boundary
conditions,

`H̊Λ⁰(Q) --d--> H̊Λ¹(Q) --d--> L²Λ²(Q)` (top row: `H̊¹ → H̊(curl) → L²(V)`),
`H̊Λ⁰(Q)³ --d--> H̊Λ¹(Q)³ --d--> L²Λ²(Q)³` (bottom row: `H̊¹(V) → H̊(curl, M) → L²(M)`),

linked by `S⁰ = I` and `S¹ = 2 vskw` (`Feec.FiniteElement.wsL2`, `Σᵢ dxᵢ ∧ ·`), as BGG data
`Feec.BGG.Hilb` (`bggHilb`, hence the segment `bggHilb.toSegment`): the domains carry the graph
inner products (`LinearPMap.GraphSpace` of the minimal realizations `d_min`), `d S⁰ = −S¹ d`
(`Feec.FiniteElement.wsL2_mem_minimal`).

**The hypotheses (H1)–(H3), (H6) of §5.1** (`Feec.BGG.Hilb.Hyps`), and the continuous constants
`Feec.BGG.Stability` of Prop 5.3, hold on the cube from the identification of `H̊Λ(Q)` with the
parity classes of the torus de Rham complex (`Feec.Models.Cube.DeRhamIdentFEM`: closed range and
`ℌᵏ(H̊Λ(Q)) = 0` for `k ≠ 3`): injectivity of `d⁰` (`d0_injective`), closed ranges, exactness at
`H̊Λ¹` (`exact1`) and the Hodge decomposition with Poincaré constant `(2π)⁻¹` (`hodge_one`), in
both rows; `‖S⁰ψ‖ ≤ ‖ψ‖`, `‖S¹v‖² ≤ 2 ‖v‖²` (`Feec.FiniteElement.norm_wsL2_sq_le`).

**The regularity hypothesis** `curl H̊(curl) = curl H̊¹(V)` is the one hypothesis that is not
proved here (`CurlPotential`): the regular decomposition `H̊(curl) = H̊¹(V) + grad H̊¹` of
[Hiptmair2002], Lemma 2.4, [HiptmairXu2007], §3 (Costabel–McIntosh regularized Poincaré
operators) is absent from Mathlib, and it does not follow from the parity model of the cube (the
potential must vanish on `∂Q` in every component, a parity class different from that of
`H̊Λ¹`). We show that it is **exactly the closedness of `curl S⁰ H̊¹(V)`**
(`curlPotential_iff_isClosed`): the inclusion `curl H̊(curl) ⊆ cl (curl S⁰ H̊¹(V))` is a theorem
(`range_d1_subset_closure`: on test fields `u = S⁰ (proxy u)`), so the hypothesis is non-vacuous
in the sense that it holds on the dense subspace of test fields, and its constant `C_R` follows
from the open mapping theorem (`CurlPotential.exists_bound`). With it, `bggHyps` and
`bggStability` hold.

## Main definitions

* `D0`, `D1` (`d_min` in degrees `0`, `1`), `V0`, `V1` (graph spaces), `Vt0`, `Vt1` (`ℝ³`-valued),
  `bggD0`, `bggDt0`, `bggS0`, `bggS1`; `bggHilb : Feec.BGG.Hilb ℝ …`.
* `CurlPotential`: the regularity hypothesis.
* `bggSegment`: the same data in the `W`-normed domain model of `Feec.BGG.Stability`.

## Main results

* `d0_injective`, `exact1`, `isClosed_range_d0`, `isClosed_range_d1`, `poincare0`, `hodge_one`;
* **`bggHyps`** (`CurlPotential → bggHilb.Hyps`), **`bggStability`**;
* `range_d1_subset_closure`, `curlPotential_iff_isClosed`, `CurlPotential.exists_bound`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.1 (hypotheses of Prop 5.1, Prop 5.3), §5.3 (the complex (4.16), Table 5.1)
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
  (regular decomposition)
* [R. Hiptmair, J. Xu, *Nodal auxiliary space preconditioning in H(curl) and H(div) spaces*][HiptmairXu2007],
  §3 (regular decomposition)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1 (Poincaré inequality, Hodge decomposition), §4.3 (the de Rham complex)
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021] (BGG construction)
-/

open scoped InnerProductSpace
open Set MeasureTheory Filter LinearPMap

@[expose] public noncomputable section

namespace Feec.Models.Cube.WeakSymmetry

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM

/-! ### The spaces -/

/-- `L²(Q; Λ⁰)`. -/
abbrev W0 := L2F ℝ (cubeDomain 3) (formIdx 3 0)
/-- `L²(Q; Λ¹)`. -/
abbrev W1 := L2F ℝ (cubeDomain 3) (formIdx 3 1)
/-- `L²(Q; Λ²)`. -/
abbrev W2 := L2F ℝ (cubeDomain 3) (formIdx 3 2)

/-- `ℝ³`-valued fields. -/
abbrev Wv (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] :=
  PiLp 2 (fun _ : Fin 3 => W)

/-- `d_min` in degree `0` (`grad` on `H̊¹(Q)`). -/
abbrev D0 : W0 →ₗ.[ℝ] W1 := (extDerivOp ℝ 3 0).minimal (cubeDomain 3)
/-- `d_min` in degree `1` (`curl` on `H̊(curl, Q)`). -/
abbrev D1 : W1 →ₗ.[ℝ] W2 := (extDerivOp ℝ 3 1).minimal (cubeDomain 3)

theorem complexMin_d01 : (complexMin 3).d 0 1 = D0 :=
  deRham_minimalComplex_d (isOpen_cubeDomain 3) 0

theorem complexMin_d12 : (complexMin 3).d 1 2 = D1 :=
  deRham_minimalComplex_d (isOpen_cubeDomain 3) 1

theorem D0_isClosed : D0.IsClosed := ConstCoeffOp.isClosed_minimal _ (isOpen_cubeDomain 3)
theorem D1_isClosed : D1.IsClosed := ConstCoeffOp.isClosed_minimal _ (isOpen_cubeDomain 3)

/-- `H̊Λ⁰(Q)` with the graph inner product. -/
abbrev V0 := D0.GraphSpace
/-- `H̊Λ¹(Q)` with the graph inner product. -/
abbrev V1 := D1.GraphSpace

instance : CompleteSpace V0 := D0_isClosed.completeSpace_graphSpace
instance : CompleteSpace V1 := D1_isClosed.completeSpace_graphSpace

/-- `H̊Λ⁰(Q)³`. -/
abbrev Vt0 := Wv V0
/-- `H̊Λ¹(Q)³`. -/
abbrev Vt1 := Wv V1

/-! ### Componentwise bounded maps -/

/-- The componentwise bounded map on `ℝ³`-valued fields. -/
def piCLM {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (f : V →L[ℝ] W) : Wv V →L[ℝ] Wv W :=
  LinearMap.mkContinuous (piMap (f : V →ₗ[ℝ] W)) ‖f‖ fun x =>
    norm_piMap_le (f : V →ₗ[ℝ] W) (norm_nonneg f) (fun v => f.le_opNorm v) x

@[simp] theorem piCLM_apply {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (f : V →L[ℝ] W) (x : Wv V) (a : Fin 3) :
    piCLM f x a = f (x a) := rfl

theorem inner_piCLM {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (f : V →L[ℝ] W) (x y : Wv V) :
    ⟪piCLM f x, piCLM f y⟫_ℝ = ∑ a, ⟪f (x a), f (y a)⟫_ℝ := by
  rw [PiLp.inner_apply]; rfl

theorem injective_piCLM {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {f : V →L[ℝ] W}
    (hf : Function.Injective f) : Function.Injective (piCLM f) := fun x y h =>
  PiLp.ext fun a => hf (by have := congrArg (fun z : Wv W => z a) h; simpa using this)

theorem denseRange_piCLM {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {f : V →L[ℝ] W} (hf : DenseRange f) :
    DenseRange (piCLM f) := by
  have : Set.range (piCLM f) =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => W)) ⁻¹' Set.univ.pi fun _ => Set.range f := by
    ext y
    simp only [Set.mem_range, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      PiLp.continuousLinearEquiv_apply]
    constructor
    · rintro ⟨x, rfl⟩ a; exact ⟨x a, rfl⟩
    · intro h
      choose x hx using h
      exact ⟨WithLp.toLp 2 x, PiLp.ext fun a => hx a⟩
  rw [DenseRange, this]
  exact (dense_pi Set.univ fun a _ => hf).preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => W)).toHomeomorph.isOpenMap

/-! ### Graph spaces -/

section GraphSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] (T : E →ₗ.[ℝ] F)

theorem graphFst_mem_domain (v : T.GraphSpace) : T.graphFst v ∈ T.domain :=
  LinearPMap.mem_domain_of_mem_graph (x := T.graphFst v) (y := T.graphSnd v) (mem_graphL2.1 v.2)

/-- The point of `D(T)` of a point of the graph space. -/
def graphDom (v : T.GraphSpace) : T.domain := ⟨T.graphFst v, graphFst_mem_domain T v⟩

@[simp] theorem coe_graphDom (v : T.GraphSpace) : (graphDom T v : E) = T.graphFst v := rfl

theorem apply_graphDom (v : T.GraphSpace) : T (graphDom T v) = T.graphSnd v :=
  ((LinearPMap.image_iff (graphFst_mem_domain T v)).2 (mem_graphL2.1 v.2)).symm

theorem graphDom_add (u v : T.GraphSpace) : graphDom T (u + v) = graphDom T u + graphDom T v :=
  Subtype.ext (map_add T.graphFst u v)

theorem graphDom_smul (c : ℝ) (v : T.GraphSpace) : graphDom T (c • v) = c • graphDom T v :=
  Subtype.ext (map_smul T.graphFst c v)

theorem inner_graphSpace (u v : T.GraphSpace) :
    ⟪u, v⟫_ℝ = ⟪T.graphFst u, T.graphFst v⟫_ℝ + ⟪T.graphSnd u, T.graphSnd v⟫_ℝ :=
  WithLp.prod_inner_apply (u : WithLp 2 (E × F)) v

theorem norm_sq_graphSpace (v : T.GraphSpace) :
    ‖v‖ ^ 2 = ‖T.graphFst v‖ ^ 2 + ‖T.graphSnd v‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (v : WithLp 2 (E × F))

theorem norm_toGraphSpace_sq (x : T.domain) :
    ‖T.toGraphSpace x‖ ^ 2 = ‖(x : E)‖ ^ 2 + ‖T x‖ ^ 2 :=
  norm_sq_graphSpace T _

theorem toGraphSpace_add (x y : T.domain) :
    T.toGraphSpace (x + y) = T.toGraphSpace x + T.toGraphSpace y :=
  Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext rfl (map_add T x y)))

theorem toGraphSpace_smul (c : ℝ) (x : T.domain) :
    T.toGraphSpace (c • x) = c • T.toGraphSpace x :=
  Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext rfl (LinearPMap.map_smul T c x)))

theorem denseRange_graphFst (hT : Dense (T.domain : Set E)) : DenseRange T.graphFst := by
  refine hT.mono fun x hx => ⟨T.toGraphSpace ⟨x, hx⟩, rfl⟩

end GraphSpace

/-! ### The complex property in degrees `0, 1` -/

theorem D0_mem_D1 (x : D0.domain) : D0 x ∈ D1.domain :=
  ConstCoeffOp.minimal_mapsTo (isOpen_cubeDomain 3) (isComplexPair_extDerivOp 0) x

theorem D1_D0 (x : D0.domain) : D1 ⟨D0 x, D0_mem_D1 x⟩ = 0 :=
  ConstCoeffOp.minimal_comp (isOpen_cubeDomain 3) (isComplexPair_extDerivOp 0) x

/-! ### The BGG data -/

/-- `d⁰ : H̊Λ⁰ → H̊Λ¹` in graph norms. -/
def bggD0 : V0 →L[ℝ] V1 :=
  LinearMap.mkContinuous
    { toFun := fun v => D1.toGraphSpace ⟨D0 (graphDom D0 v), D0_mem_D1 _⟩
      map_add' := fun u v => by
        rw [← toGraphSpace_add]
        congr 1
        refine Subtype.ext ?_
        change D0 (graphDom D0 (u + v)) = D0 (graphDom D0 u) + D0 (graphDom D0 v)
        rw [graphDom_add, LinearPMap.map_add]
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← toGraphSpace_smul]
        congr 1
        refine Subtype.ext ?_
        change D0 (graphDom D0 (c • v)) = c • D0 (graphDom D0 v)
        rw [graphDom_smul, LinearPMap.map_smul] } 1
    fun v => by
      rw [one_mul]
      have h1 := norm_toGraphSpace_sq D1 ⟨D0 (graphDom D0 v), D0_mem_D1 _⟩
      have h0 : D1 ⟨D0 (graphDom D0 v), D0_mem_D1 _⟩ = 0 := D1_D0 _
      rw [h0, norm_zero] at h1
      have h2 := norm_sq_graphSpace D0 v
      have h3 : ‖D0 (graphDom D0 v)‖ = ‖D0.graphSnd v‖ := by rw [apply_graphDom]
      change ‖D1.toGraphSpace ⟨D0 (graphDom D0 v), D0_mem_D1 _⟩‖ ≤ ‖v‖
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
      change ‖D1.toGraphSpace ⟨D0 (graphDom D0 v), D0_mem_D1 _⟩‖ ^ 2 =
        ‖D0 (graphDom D0 v)‖ ^ 2 + 0 ^ 2 at h1
      rw [h1, h3]
      nlinarith [sq_nonneg ‖D0.graphFst v‖]

theorem graphFst_bggD0 (v : V0) : D1.graphFst (bggD0 v) = D0.graphSnd v := apply_graphDom D0 v

theorem graphSnd_bggD0 (v : V0) : D1.graphSnd (bggD0 v) = 0 := D1_D0 _

/-- `d¹ : H̊Λ¹ → L²Λ²`. -/
def bggD1 : V1 →L[ℝ] W2 := D1.graphSnd

/-- `d̃⁰ : H̊Λ⁰(Q)³ → H̊Λ¹(Q)³`. -/
def bggDt0 : Vt0 →L[ℝ] Vt1 := piCLM bggD0

/-- `d̃¹ : H̊Λ¹(Q)³ → L²Λ²(Q)³`. -/
def bggDt1 : Vt1 →L[ℝ] Wv W2 := piCLM bggD1

/-- The inclusion `H̊Λ⁰(Q)³ → L²Λ⁰(Q)³`. -/
abbrev ιt0 : Vt0 →L[ℝ] Wv W0 := piCLM D0.graphFst
/-- The inclusion `H̊Λ¹(Q)³ → L²Λ¹(Q)³`. -/
abbrev ιt1 : Vt1 →L[ℝ] Wv W1 := piCLM D1.graphFst

theorem ιt0_mem (φ : Vt0) (a : Fin 3) : ιt0 φ a ∈ D0.domain := graphFst_mem_domain D0 (φ a)

/-- `S⁰ ψ ∈ H̊Λ¹(Q)` for `ψ ∈ H̊Λ⁰(Q)³`, with `d S⁰ψ = −S¹ dψ`. -/
theorem wsL2_zero_mem (φ : Vt0) :
    ∃ h : wsL2 (Ω := cubeDomain 3) 0 (ιt0 φ) ∈ D1.domain,
      D1 ⟨_, h⟩ = -wsL2 (Ω := cubeDomain 3) 1 (ιt1 (bggDt0 φ)) := by
  obtain ⟨h, e⟩ := wsL2_mem_minimal (isOpen_cubeDomain 3) 0 (v := ιt0 φ) (ιt0_mem φ)
  have e' : D1 ⟨_, h⟩ = -wsL2 (Ω := cubeDomain 3) 1
      (WithLp.toLp 2 fun a => D0 ⟨ιt0 φ a, ιt0_mem φ a⟩) := e
  refine ⟨h, e'.trans ?_⟩
  congr 2

/-- **`S⁰ = I : H̊Λ⁰(Q)³ → H̊Λ¹(Q)`** in graph norms. -/
def bggS0 : Vt0 →L[ℝ] V1 :=
  LinearMap.mkContinuous
    { toFun := fun φ => D1.toGraphSpace ⟨_, (wsL2_zero_mem φ).1⟩
      map_add' := fun φ ψ => by
        rw [← toGraphSpace_add]
        congr 1
        exact Subtype.ext (by simp)
      map_smul' := fun c φ => by
        rw [RingHom.id_apply, ← toGraphSpace_smul]
        congr 1
        exact Subtype.ext (by simp) } (Real.sqrt 2)
    fun φ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      have h1 := norm_toGraphSpace_sq D1 ⟨_, (wsL2_zero_mem φ).1⟩
      rw [(wsL2_zero_mem φ).2, norm_neg] at h1
      have h2 := norm_wsL2_sq_le (Ω := cubeDomain 3) 0 (ιt0 φ)
      have h3 := norm_wsL2_sq_le (Ω := cubeDomain 3) 1 (ιt1 (bggDt0 φ))
      have h4 : ‖φ‖ ^ 2 = ‖ιt0 φ‖ ^ 2 + ‖ιt1 (bggDt0 φ)‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [norm_sq_graphSpace D0 (φ a)]
        simp [bggDt0, graphFst_bggD0]
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num at h2 h3
      nlinarith [sq_nonneg ‖ιt0 φ‖, sq_nonneg ‖ιt1 (bggDt0 φ)‖]

theorem graphFst_bggS0 (φ : Vt0) : D1.graphFst (bggS0 φ) = wsL2 (Ω := cubeDomain 3) 0 (ιt0 φ) :=
  rfl

/-- **`S¹ = 2 vskw : H̊Λ¹(Q)³ → L²Λ²(Q)`**. -/
def bggS1 : Vt1 →L[ℝ] W2 := wsL2 (Ω := cubeDomain 3) 1 ∘L ιt1

/-- **The anticommutation** `d S⁰ = −S¹ d̃` (`curl S₀ = −S₁ grad`). -/
theorem bggAnticomm (φ : Vt0) : bggD1 (bggS0 φ) = -bggS1 (bggDt0 φ) := (wsL2_zero_mem φ).2

/-! ### The BGG data as `Feec.BGG.Hilb` -/

theorem inner_Vt {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (u v : Wv V) :
    ⟪u, v⟫_ℝ = ∑ a, ⟪u a, v a⟫_ℝ := PiLp.inner_apply u v

theorem bgg_graph0 (u v : V0) :
    ⟪u, v⟫_ℝ = ⟪D0.graphFst u, D0.graphFst v⟫_ℝ +
      ⟪D1.graphFst (bggD0 u), D1.graphFst (bggD0 v)⟫_ℝ := by
  rw [inner_graphSpace D0, graphFst_bggD0, graphFst_bggD0]

theorem bgg_grapht0 (u v : Vt0) :
    ⟪u, v⟫_ℝ = ⟪ιt0 u, ιt0 v⟫_ℝ + ⟪ιt1 (bggDt0 u), ιt1 (bggDt0 v)⟫_ℝ := by
  rw [inner_Vt u v, inner_Vt (ιt0 u) (ιt0 v), inner_Vt (ιt1 (bggDt0 u)) (ιt1 (bggDt0 v)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inner_graphSpace D0 (u a) (v a)]
  congr 1
  change _ = ⟪D1.graphFst (bggD0 (u a)), D1.graphFst (bggD0 (v a))⟫_ℝ
  rw [graphFst_bggD0, graphFst_bggD0]

theorem bgg_grapht1 (u v : Vt1) :
    ⟪u, v⟫_ℝ = ⟪ιt1 u, ιt1 v⟫_ℝ + ⟪bggDt1 u, bggDt1 v⟫_ℝ := by
  rw [inner_Vt u v, inner_Vt (ιt1 u) (ιt1 v), inner_Vt (bggDt1 u) (bggDt1 v),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact inner_graphSpace D1 (u a) (v a)

theorem bgg_dt1_dt0 (φ : Vt0) : bggDt1 (bggDt0 φ) = 0 :=
  PiLp.ext fun _ => graphSnd_bggD0 _

/-- **The BGG data (4.16) on the cube** with the thesis' boundary conditions: top row
`H̊Λ⁰ → H̊Λ¹ → L²Λ²`, bottom row `(H̊Λ⁰)³ → (H̊Λ¹)³ → (L²Λ²)³`, `S⁰ = I`, `S¹ = 2 vskw`. -/
def bggHilb : Feec.BGG.Hilb ℝ W0 W1 (Wv W0) (Wv W1) W2 (Wv W2) V0 V1 Vt0 Vt1 where
  ι0 := D0.graphFst
  ι1 := D1.graphFst
  ιt0 := ιt0
  ιt1 := ιt1
  ι0_injective := graphFst_injective D0
  ι1_injective := graphFst_injective D1
  ιt0_injective := injective_piCLM (graphFst_injective D0)
  ιt1_injective := injective_piCLM (graphFst_injective D1)
  dense0 := denseRange_graphFst D0 (ConstCoeffOp.dense_minimal_domain _ (isOpen_cubeDomain 3))
  dense1 := denseRange_graphFst D1 (ConstCoeffOp.dense_minimal_domain _ (isOpen_cubeDomain 3))
  denset0 := denseRange_piCLM
    (denseRange_graphFst D0 (ConstCoeffOp.dense_minimal_domain _ (isOpen_cubeDomain 3)))
  denset1 := denseRange_piCLM
    (denseRange_graphFst D1 (ConstCoeffOp.dense_minimal_domain _ (isOpen_cubeDomain 3)))
  d0 := bggD0
  d1 := bggD1
  dt0 := bggDt0
  dt1 := bggDt1
  S0 := bggS0
  S1 := bggS1
  graph0 := bgg_graph0
  graph1 := inner_graphSpace D1
  grapht0 := bgg_grapht0
  grapht1 := bgg_grapht1
  d1_d0 := graphSnd_bggD0
  dt1_dt0 := bgg_dt1_dt0
  anticomm := bggAnticomm

/-! ### Exactness and closed ranges from `H̊Λ(Q)` -/

theorem rel_m10 : (ComplexShape.up ℤ).Rel (-1) 0 := rfl
theorem rel_01 : (ComplexShape.up ℤ).Rel 0 1 := rfl
theorem rel_12 : (ComplexShape.up ℤ).Rel 1 2 := rfl

/-- **`ker d⁰ = 0` on `H̊Λ⁰(Q)`** (`ℌ⁰(H̊Λ(Q)) = 0`). -/
theorem D0_eq_zero {x : D0.domain} (hx : D0 x = 0) : (x : W0) = 0 := by
  have hz : (x : W0) ∈ (complexMin 3).cycles 0 := by
    rw [(complexMin 3).cycles_eq rel_01, complexMin_d01]
    exact LinearPMap.mem_ker_iff.2 ⟨x, rfl, hx⟩
  rw [← (complexMin 3).exact_iff_harmonic_eq_bot (closedRangeAt_min 0) |>.2
    (harmonic_eq_bot_min (by norm_num)), (complexMin 3).boundaries_eq rel_m10] at hz
  obtain ⟨y, hy⟩ := hz
  have : Subsingleton (L2F ℝ (cubeDomain 3) (formIdx 3 (-1 : ℤ))) :=
    LocalElement.subsingleton_L2F_negSucc _ 0
  have hy0 : y = 0 := Subtype.ext (Subsingleton.elim _ _)
  rw [← hy, hy0]
  exact LinearPMap.map_zero _

/-- **Exactness of `H̊Λ(Q)` at `H̊Λ¹`**: `d¹ u = 0` gives `u = d⁰ x`. -/
theorem exists_D0_eq {u : D1.domain} (hu : D1 u = 0) : ∃ x : D0.domain, D0 x = u := by
  have hz : (u : W1) ∈ (complexMin 3).cycles 1 := by
    rw [(complexMin 3).cycles_eq rel_12, complexMin_d12]
    exact LinearPMap.mem_ker_iff.2 ⟨u, rfl, hu⟩
  rw [← (complexMin 3).exact_iff_harmonic_eq_bot (closedRangeAt_min 1) |>.2
    (harmonic_eq_bot_min (by norm_num)), (complexMin 3).boundaries_eq rel_01,
    complexMin_d01] at hz
  obtain ⟨x, hx⟩ := hz
  exact ⟨x, hx⟩

theorem range_D0_eq : (Set.range fun x : D0.domain => D0 x) = ((complexMin 3).boundaries 1 : Set W1) := by
  rw [(complexMin 3).boundaries_eq rel_01, complexMin_d01]
  rfl

theorem range_D1_eq : (Set.range fun x : D1.domain => D1 x) = ((complexMin 3).boundaries 2 : Set W2) := by
  rw [(complexMin 3).boundaries_eq rel_12, complexMin_d12]
  rfl

theorem isClosed_range_D0 : IsClosed (Set.range fun x : D0.domain => D0 x) := by
  rw [range_D0_eq]; exact closedRangeAt_min 1

theorem isClosed_range_D1 : IsClosed (Set.range fun x : D1.domain => D1 x) := by
  rw [range_D1_eq]; exact closedRangeAt_min 2

/-! ### The hypotheses (H1)–(H3), (H6) -/

theorem graphDom_toGraphSpace {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (T : E →ₗ.[ℝ] F) (x : T.domain) :
    graphDom T (T.toGraphSpace x) = x := Subtype.ext rfl

theorem range_graphSnd_D0 : Set.range D0.graphSnd = Set.range fun x : D0.domain => D0 x := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩; exact ⟨graphDom D0 v, apply_graphDom D0 v⟩
  · rintro ⟨x, rfl⟩; exact ⟨D0.toGraphSpace x, rfl⟩

theorem range_graphSnd_D1 : Set.range D1.graphSnd = Set.range fun x : D1.domain => D1 x := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩; exact ⟨graphDom D1 v, apply_graphDom D1 v⟩
  · rintro ⟨x, rfl⟩; exact ⟨D1.toGraphSpace x, rfl⟩

theorem range_pi_eq {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (f : V →L[ℝ] W) :
    Set.range (piCLM f) =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => W)) ⁻¹' Set.univ.pi fun _ => Set.range f := by
  ext y
  simp only [Set.mem_range, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
    PiLp.continuousLinearEquiv_apply]
  constructor
  · rintro ⟨x, rfl⟩ a; exact ⟨x a, rfl⟩
  · intro h
    choose x hx using h
    exact ⟨WithLp.toLp 2 x, PiLp.ext fun a => hx a⟩

theorem isClosed_range_pi {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {f : V →L[ℝ] W} (hf : IsClosed (Set.range f)) :
    IsClosed (Set.range (piCLM f)) := by
  rw [range_pi_eq]
  exact (isClosed_set_pi fun _ _ => hf).preimage (ContinuousLinearEquiv.continuous _)

theorem bggD0_injective : Function.Injective bggD0 := by
  refine (injective_iff_map_eq_zero bggD0).2 fun v hv => graphFst_injective D0 ?_
  have h1 : D0 (graphDom D0 v) = 0 := by
    have := congrArg D1.graphFst hv
    rwa [graphFst_bggD0, _root_.map_zero, ← apply_graphDom] at this
  rw [_root_.map_zero]
  exact D0_eq_zero h1

theorem range_bggD0 : Set.range (D1.graphFst ∘L bggD0) = Set.range fun x : D0.domain => D0 x := by
  rw [← range_graphSnd_D0]
  ext y
  simp [graphFst_bggD0]

theorem isClosed_range_bggD0 : IsClosed (Set.range (D1.graphFst ∘L bggD0)) := by
  rw [range_bggD0]; exact isClosed_range_D0

theorem isClosed_range_bggD1 : IsClosed (Set.range bggD1) := by
  change IsClosed (Set.range D1.graphSnd)
  rw [range_graphSnd_D1]; exact isClosed_range_D1

/-- **Exactness of the top row at `H̊Λ¹(Q)`.** -/
theorem exact1 : LinearMap.ker (bggD1 : V1 →ₗ[ℝ] W2) = LinearMap.range (bggD0 : V0 →ₗ[ℝ] V1) := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · intro hv
    have hv' : D1 (graphDom D1 v) = 0 := by rw [apply_graphDom]; exact hv
    obtain ⟨x, hx⟩ := exists_D0_eq hv'
    refine ⟨D0.toGraphSpace x, graphFst_injective D1 ?_⟩
    rw [graphFst_bggD0]
    exact hx
  · rintro ⟨x, rfl⟩
    exact graphSnd_bggD0 x

/-- **The regularity hypothesis** of [QuennevilleBelair2015], §5.3, `curl H̊(curl, Q) ⊆
curl S⁰ H̊¹(Q; ℝ³)`: every `d u`, `u ∈ H̊Λ¹(Q)`, is `d (S⁰ φ)` for a vector field
`φ ∈ H̊Λ⁰(Q)³`, i.e. has a potential with components in `H̊¹(Q)`. The thesis derives it from the
regular decomposition `H̊(curl) = H̊¹(V) + grad H̊¹` ([Hiptmair2002], Lemma 2.4;
[HiptmairXu2007], §3), which is not in Mathlib; it is the field `reg` of `Feec.BGG.Hilb.Hyps`.
It holds on the dense subspace of test fields (`range_d1_subset_closure`), is equivalent to the
closedness of `curl S⁰ H̊¹(Q; ℝ³)` (`curlPotential_iff_isClosed`), and carries its constant
(`CurlPotential.exists_bound`). -/
def CurlPotential : Prop := Set.range bggD1 ⊆ Set.range (bggD1 ∘ bggS0)

/-- **The hypotheses (H1)–(H3), (H6) of [QuennevilleBelair2015], §5.1 on the cube**, with the
regularity hypothesis `CurlPotential` (the only one not proved from `H̊Λ(Q)`). -/
theorem bggHyps (hR : CurlPotential) : bggHilb.Hyps where
  d0_injective := bggD0_injective
  dt0_injective := injective_piCLM bggD0_injective
  d0_closed := isClosed_range_bggD0
  dt0_closed := by
    have : (bggHilb.ιt1 ∘L bggHilb.dt0) = piCLM (D1.graphFst ∘L bggD0) := by
      ext φ a; rfl
    rw [this]
    exact isClosed_range_pi isClosed_range_bggD0
  exact1 := exact1
  exactt1 := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hv
      have h : ∀ a, v a ∈ LinearMap.ker (bggD1 : V1 →ₗ[ℝ] W2) := fun a => by
        have := congrArg (fun z : Wv W2 => z a) hv
        exact this
      simp only [exact1] at h
      choose x hx using h
      exact ⟨WithLp.toLp 2 x, PiLp.ext fun a => hx a⟩
    · rintro ⟨x, rfl⟩
      exact bgg_dt1_dt0 x
  d1_closed := isClosed_range_bggD1
  dt1_closed := isClosed_range_pi isClosed_range_bggD1
  reg := hR

/-! ### The regularity hypothesis: non-vacuity and the constant -/

/-- The vector proxy of a `1`-form: `ψₐ = u_{{a}}`, a vector of `0`-forms with `S⁰ ψ = u`. -/
def proxy0 (φ : formIdx 3 1 → (Fin 3 → ℝ) → ℝ) : Fin 3 → formIdx 3 0 → (Fin 3 → ℝ) → ℝ :=
  fun a _ => φ ⟨{a}, by simp⟩

theorem wsFields_proxy0 (φ : formIdx 3 1 → (Fin 3 → ℝ) → ℝ) :
    wsFields (n := 3) 0 (proxy0 φ) = φ := by
  funext t
  obtain ⟨t, ht⟩ := t
  obtain ⟨j, rfl⟩ : ∃ j, t = {j} := Finset.card_eq_one.1 (by exact_mod_cast ht)
  simp only [wsFields]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single ⟨∅, by simp⟩]
    · rw [wsCoeff_eq]
      simp [proxy0, ExteriorFibre.sgn, Finset.filter_singleton]
    · intro r _ hr
      rw [wsCoeff_eq]
      have : ¬ ((∅ : Finset (Fin 3)) = r.1) := fun h => hr (Subtype.ext h.symm)
      simp [this]
    · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [wsCoeff_eq]
    simp [ha]
  · simp

/-- **Non-vacuity of the regularity hypothesis**: `curl H̊(curl) ⊆ cl (curl S⁰ H̊¹(V))`. On a
test `1`-form `u`, `u = S⁰ ψ` with the test vector field `ψ = (u_{{a}})ₐ`, and the test forms are
dense in `H̊Λ¹(Q)` in the graph norm (the definition of `d_min`). -/
theorem range_d1_subset_closure : Set.range bggD1 ⊆ closure (Set.range (bggD1 ∘ bggS0)) := by
  have hQ := isOpen_cubeDomain 3
  have hsub : Prod.snd '' (SetLike.coe ((extDerivOp ℝ 3 1).testGraph (cubeDomain 3)) :
      Set (W1 × W2)) ⊆ Set.range (bggD1 ∘ bggS0) := by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    have hψ : ∀ a, IsTestField (cubeDomain 3) (proxy0 φ a) := fun a r => hφ _
    set Φ : Vt0 := WithLp.toLp 2 fun a =>
      D0.toGraphSpace ⟨testField (hψ a), ConstCoeffOp.testField_mem_minimal_domain _ hQ (hψ a)⟩
    refine ⟨Φ, ?_⟩
    have hS : wsL2 (Ω := cubeDomain 3) 0 (ιt0 Φ) = testField hφ := by
      have := wsL2_testField (Ω := cubeDomain 3) (k := 0) hψ
      refine this.trans (testField_congr _ _ (wsFields_proxy0 φ))
    change D1 ⟨wsL2 (Ω := cubeDomain 3) 0 (ιt0 Φ), _⟩ = testField _
    have e := ConstCoeffOp.minimal_testField (extDerivOp ℝ 3 1) hQ hφ
    refine Eq.trans ?_ e
    congr 1
    exact Subtype.ext hS
  intro y ⟨v, hv⟩
  have hmem := ConstCoeffOp.mem_closure_minimal (extDerivOp ℝ 3 1) hQ (graphDom D1 v)
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hmem
  have := mem_closure_image continuous_snd.continuousAt hmem
  rw [apply_graphDom] at this
  rw [← hv]
  exact closure_mono hsub this

/-- **The regularity hypothesis is the closedness of `curl S⁰ H̊¹(Q; ℝ³)`.** -/
theorem curlPotential_iff_isClosed :
    CurlPotential ↔ IsClosed (Set.range (bggD1 ∘ bggS0)) := by
  constructor
  · intro h
    have : Set.range (bggD1 ∘ bggS0) = Set.range bggD1 :=
      Set.Subset.antisymm (by rintro _ ⟨φ, rfl⟩; exact ⟨_, rfl⟩) h
    rw [this]
    exact isClosed_range_bggD1
  · intro h
    exact range_d1_subset_closure.trans h.closure_eq.le

/-- **The constant of the regularity hypothesis** (open mapping theorem): a potential can be
chosen with `‖φ‖_{H̊Λ⁰(Q)³} ≤ C_R ‖d u‖`. -/
theorem CurlPotential.exists_bound (h : CurlPotential) :
    ∃ CR, 0 ≤ CR ∧ ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖ := by
  set R := Set.range bggD1
  have hRc : IsClosed R := isClosed_range_bggD1
  set Rs : Submodule ℝ W2 := LinearMap.range (bggD1 : V1 →ₗ[ℝ] W2)
  have hRs : (Rs : Set W2) = R := LinearMap.coe_range _
  have : CompleteSpace Rs := by
    have : IsClosed (Rs : Set W2) := hRs ▸ hRc
    exact this.completeSpace_coe
  set T : Vt0 →L[ℝ] Rs := (bggD1 ∘L bggS0).codRestrict Rs fun φ => ⟨bggS0 φ, rfl⟩
  have hT : Function.Surjective T := by
    rintro ⟨y, ⟨u, rfl⟩⟩
    obtain ⟨φ, hφ⟩ := h ⟨u, rfl⟩
    exact ⟨φ, Subtype.ext hφ⟩
  obtain ⟨C, hC0, hC⟩ := T.exists_preimage_norm_le hT
  refine ⟨C, hC0.le, fun u => ?_⟩
  obtain ⟨φ, hφ, hn⟩ := hC ⟨bggD1 u, ⟨u, rfl⟩⟩
  exact ⟨φ, congrArg Subtype.val hφ, hn⟩

/-! ### Poincaré inequalities and the Hodge decomposition of `H̊Λ¹(Q)` -/

theorem cycles_zero_eq_bot : (complexMin 3).cycles 0 = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  rw [(complexMin 3).cycles_eq rel_01, complexMin_d01] at hx
  obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hx
  exact D0_eq_zero hy

/-- **Poincaré on `H̊Λ⁰(Q)`**: `‖σ‖ ≤ (2π)⁻¹ ‖dσ‖`. -/
theorem poincare0 (x : D0.domain) : ‖(x : W0)‖ ≤ (2 * Real.pi)⁻¹ * ‖D0 x‖ := by
  have h := norm_le_of_mem_orthogonal_cycles_min (n := 3) rel_01
  rw [complexMin_d01] at h
  exact h x (by rw [cycles_zero_eq_bot, Submodule.bot_orthogonal_eq_top]; exact Submodule.mem_top)

/-- **Poincaré on `H̊Λ¹(Q) ∩ (𝔷¹)ᗮ`**. -/
theorem poincare1 (x : D1.domain) (hx : (x : W1) ∈ ((complexMin 3).cycles 1)ᗮ) :
    ‖(x : W1)‖ ≤ (2 * Real.pi)⁻¹ * ‖D1 x‖ := by
  have h := norm_le_of_mem_orthogonal_cycles_min (n := 3) rel_12
  rw [complexMin_d12] at h
  exact h x hx

/-- **Hodge decomposition of `H̊Λ¹(Q)`** (no harmonic part): `u = d ψ + w` with `d w = d u` and
`‖w‖ ≤ (2π)⁻¹ ‖d u‖`. -/
theorem hodge_one (u : D1.domain) :
    ∃ ψ : D0.domain, ∃ w : D1.domain, (u : W1) = D0 ψ + w ∧ D1 w = D1 u ∧
      ‖(w : W1)‖ ≤ (2 * Real.pi)⁻¹ * ‖D1 u‖ := by
  set K := (complexMin 3).cycles 1
  have hK : K = D1.ker := by
    change (complexMin 3).cycles 1 = _
    rw [(complexMin 3).cycles_eq rel_12, complexMin_d12]
  have hp : K.starProjection (u : W1) ∈ D1.ker := hK ▸ K.starProjection_apply_mem _
  obtain ⟨p, hpe, hp0⟩ := LinearPMap.mem_ker_iff.1 hp
  obtain ⟨ψ, hψ⟩ := exists_D0_eq hp0
  refine ⟨ψ, u - p, ?_, ?_, ?_⟩
  · rw [Submodule.coe_sub, hψ]; abel
  · rw [LinearPMap.map_sub, hp0, sub_zero]
  · have hw : ((u - p : D1.domain) : W1) ∈ Kᗮ := by
      rw [Submodule.coe_sub, ← hpe]
      exact K.sub_starProjection_mem_orthogonal _
    have := poincare1 (u - p) hw
    rwa [LinearPMap.map_sub, hp0, sub_zero] at this

/-! ### The `W`-normed model and the constants of Prop 5.3 -/

/-- `H̊Λ⁰(Q)` with the `L²` norm. -/
abbrev U0 := D0.domain
/-- `H̊Λ¹(Q)` with the `L²` norm. -/
abbrev U1 := D1.domain

/-- `d⁰` on the domains. -/
def segD0 : U0 →ₗ[ℝ] U1 where
  toFun x := ⟨D0 x, D0_mem_D1 x⟩
  map_add' x y := Subtype.ext (LinearPMap.map_add _ x y)
  map_smul' c x := Subtype.ext (LinearPMap.map_smul _ c x)

/-- `d¹` on the domain. -/
def segD1 : U1 →ₗ[ℝ] W2 := D1.toFun

/-- The inclusion `(H̊Λ⁰)³ → (L²Λ⁰)³`. -/
abbrev incl0 : Wv U0 →ₗ[ℝ] Wv W0 := piMap D0.domain.subtype
/-- The inclusion `(H̊Λ¹)³ → (L²Λ¹)³`. -/
abbrev incl1 : Wv U1 →ₗ[ℝ] Wv W1 := piMap D1.domain.subtype

theorem norm_incl0 (φ : Wv U0) : ‖incl0 φ‖ = ‖φ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2]
  rfl

theorem norm_incl1 (φ : Wv U1) : ‖incl1 φ‖ = ‖φ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2]
  rfl

theorem wsL2_incl0_mem (φ : Wv U0) :
    ∃ h : wsL2 (Ω := cubeDomain 3) 0 (incl0 φ) ∈ D1.domain,
      D1 ⟨_, h⟩ = -wsL2 (Ω := cubeDomain 3) 1 (incl1 (piMap segD0 φ)) := by
  obtain ⟨h, e⟩ := wsL2_mem_minimal (isOpen_cubeDomain 3) 0 (v := incl0 φ) fun a => (φ a).2
  exact ⟨h, e⟩

/-- `S⁰` on the domains. -/
def segS0 : Wv U0 →ₗ[ℝ] U1 where
  toFun φ := ⟨_, (wsL2_incl0_mem φ).1⟩
  map_add' φ ψ := Subtype.ext (by simp)
  map_smul' c φ := Subtype.ext (by simp)

theorem coe_segS0 (ψ : Wv U0) :
    ((segS0 ψ : U1) : W1) = wsL2 (Ω := cubeDomain 3) 0 (incl0 ψ) := rfl

theorem norm_segS0 (ψ : Wv U0) : ‖segS0 ψ‖ = ‖wsL2 (Ω := cubeDomain 3) 0 (incl0 ψ)‖ := by
  rw [← coe_segS0]; rfl

theorem norm_segD1_segS0 (ψ : Wv U0) :
    ‖segD1 (segS0 ψ)‖ = ‖wsL2 (Ω := cubeDomain 3) 1 (incl1 (piMap segD0 ψ))‖ := by
  change ‖D1 ⟨_, (wsL2_incl0_mem ψ).1⟩‖ = _
  rw [(wsL2_incl0_mem ψ).2, norm_neg]

theorem norm_wsL2_zero_incl0_sq_le (ψ : Wv U0) :
    ‖wsL2 (Ω := cubeDomain 3) 0 (incl0 ψ)‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
  have h := norm_wsL2_sq_le (Ω := cubeDomain 3) 0 (incl0 ψ)
  have e : ‖incl0 ψ‖ ^ 2 = ‖ψ‖ ^ 2 := congrArg (· ^ 2) (norm_incl0 ψ)
  have h1 : (((0 : ℤ) : ℝ) + 1) = 1 := by norm_num
  rw [h1, one_mul] at h
  exact h.trans_eq e

theorem norm_wsL2_one_incl1_sq_le (v : Wv U1) :
    ‖wsL2 (Ω := cubeDomain 3) 1 (incl1 v)‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  have h := norm_wsL2_sq_le (Ω := cubeDomain 3) 1 (incl1 v)
  have e : ‖incl1 v‖ ^ 2 = ‖v‖ ^ 2 := congrArg (· ^ 2) (norm_incl1 v)
  have h1 : (((1 : ℤ) : ℝ) + 1) = 2 := by norm_num
  rw [h1] at h
  exact h.trans_eq (congrArg (2 * ·) e)

/-- `S¹` on the domain. -/
def segS1 : Wv U1 →ₗ[ℝ] W2 where
  toFun v := wsL2 (Ω := cubeDomain 3) 1 (incl1 v)
  map_add' u v := by simp
  map_smul' c v := by simp

/-- **The BGG data (4.16) in the `W`-normed model** of `Feec.BGG.Stability`. -/
def bggSegment : Feec.BGG.Segment ℝ U0 U1 W2 (Wv U0) (Wv U1) (Wv W2) where
  d0 := segD0
  d1 := segD1
  dt0 := piMap segD0
  dt1 := piMap segD1
  S0 := segS0
  S1 := segS1
  d1_d0 x := D1_D0 x
  dt1_dt0 _ := PiLp.ext fun _ => D1_D0 _
  anticomm ψ := (wsL2_incl0_mem ψ).2

theorem norm_sq_piMap_le {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (f : V →ₗ[ℝ] W) {C : ℝ}
    (hC : ∀ v, ‖f v‖ ≤ C * ‖v‖) (φ : Wv V) : ‖piMap f φ‖ ^ 2 ≤ C ^ 2 * ‖φ‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [piMap_apply, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 2

theorem sqrt_le_of_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  (pow_le_pow_iff_left₀ ha hb two_ne_zero).1 h

theorem seg_poinct0 (φ : Wv U0) : ‖φ‖ ≤ (2 * Real.pi)⁻¹ * ‖piMap segD0 φ‖ := by
  have hCp : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  refine sqrt_le_of_sq (norm_nonneg _) (mul_nonneg hCp (norm_nonneg _)) ?_
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (poincare0 (φ a)) 2

theorem seg_hodget1 (v : Wv U1) : ∃ (ψ : Wv U0) (w : Wv U1), v = piMap segD0 ψ + w ∧
    ‖w‖ ≤ (2 * Real.pi)⁻¹ * ‖piMap segD1 v‖ := by
  have hCp : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  choose ψ w hvw hdw hnw using fun a => hodge_one (v a)
  refine ⟨WithLp.toLp 2 ψ, WithLp.toLp 2 w, PiLp.ext fun a => Subtype.ext (hvw a), ?_⟩
  refine sqrt_le_of_sq (norm_nonneg _) (mul_nonneg hCp (norm_nonneg _)) ?_
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hnw a) 2

theorem seg_reg {CR : ℝ}
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) (x : U1) :
    ∃ φ : Wv U0, segD1 (segS0 φ) = segD1 x ∧ ‖piMap segD0 φ‖ ≤ CR * ‖segD1 x‖ := by
  obtain ⟨φ0, e, hn⟩ := hCR (D1.toGraphSpace x)
  refine ⟨WithLp.toLp 2 fun a => graphDom D0 (φ0 a), e, ?_⟩
  refine le_trans ?_ hn
  refine sqrt_le_of_sq (norm_nonneg _) (norm_nonneg _) ?_
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum fun a _ => ?_
  have h1 := norm_sq_graphSpace D0 (φ0 a)
  change ‖D0 (graphDom D0 (φ0 a))‖ ^ 2 ≤ _
  rw [apply_graphDom, h1]
  nlinarith [sq_nonneg ‖D0.graphFst (φ0 a)‖]

theorem seg_boundS0 (ψ : Wv U0) :
    ‖segS0 ψ‖ ^ 2 + ‖segD1 (segS0 ψ)‖ ^ 2 ≤
      Real.sqrt 2 ^ 2 * (‖ψ‖ ^ 2 + ‖piMap segD0 ψ‖ ^ 2) := by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 := norm_wsL2_zero_incl0_sq_le ψ
  have h1 := norm_wsL2_one_incl1_sq_le (piMap segD0 ψ)
  have e1 := norm_segS0 ψ
  have e2 := norm_segD1_segS0 ψ
  calc ‖segS0 ψ‖ ^ 2 + ‖segD1 (segS0 ψ)‖ ^ 2
      = ‖wsL2 (Ω := cubeDomain 3) 0 (incl0 ψ)‖ ^ 2 +
          ‖wsL2 (Ω := cubeDomain 3) 1 (incl1 (piMap segD0 ψ))‖ ^ 2 :=
        congrArg₂ (fun a b : ℝ => a ^ 2 + b ^ 2) e1 e2
    _ ≤ ‖ψ‖ ^ 2 + 2 * ‖piMap segD0 ψ‖ ^ 2 := add_le_add h0 h1
    _ ≤ 2 * (‖ψ‖ ^ 2 + ‖piMap segD0 ψ‖ ^ 2) := by nlinarith [sq_nonneg ‖ψ‖]
    _ = Real.sqrt 2 ^ 2 * (‖ψ‖ ^ 2 + ‖piMap segD0 ψ‖ ^ 2) := by rw [hsq2]

theorem seg_boundS1 (v : Wv U1) :
    ‖segS1 v‖ ^ 2 ≤ Real.sqrt 2 ^ 2 * (‖v‖ ^ 2 + ‖piMap segD1 v‖ ^ 2) := by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 := norm_wsL2_one_incl1_sq_le v
  calc ‖segS1 v‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := h1
    _ ≤ 2 * (‖v‖ ^ 2 + ‖piMap segD1 v‖ ^ 2) := by nlinarith [sq_nonneg ‖piMap segD1 v‖]
    _ = Real.sqrt 2 ^ 2 * (‖v‖ ^ 2 + ‖piMap segD1 v‖ ^ 2) := by rw [hsq2]

/-- **The continuous constants of Prop 5.3 on the cube** (`Feec.BGG.Stability`), with
`C_p = (2π)⁻¹`, `C_S = √2`, and `C_R` the constant of the regularity hypothesis. -/
theorem bggStability (hR : CurlPotential) :
    ∃ CR, Feec.BGG.Stability bggSegment (2 * Real.pi)⁻¹ CR (Real.sqrt 2) := by
  obtain ⟨CR, hCR0, hCR⟩ := hR.exists_bound
  exact ⟨CR, ⟨by positivity, hCR0, Real.sqrt_nonneg _, poincare0, seg_poinct0,
    fun μ hμ => by obtain ⟨x, hx⟩ := exists_D0_eq hμ; exact ⟨x, Subtype.ext hx⟩,
    seg_hodget1, seg_reg hCR, seg_boundS0, seg_boundS1⟩⟩

/-! ### Consequences -/

/-- `(S⁰ψ)_{{j}} = ψⱼ`: the `L²` form of `S₀ = I`. -/
theorem wsL2_zero_apply (v : Wv W0) (j : Fin 3) :
    wsL2 (Ω := cubeDomain 3) 0 v ⟨{j}, by simp⟩ = v j ⟨∅, by simp⟩ := by
  rw [wsL2_apply, Fintype.sum_prod_type, Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single ⟨∅, by simp⟩]
    · rw [wsCoeff_eq]
      simp [ExteriorFibre.sgn, Finset.filter_singleton]
    · intro r _ hr
      rw [wsCoeff_eq]
      have : ¬ ((∅ : Finset (Fin 3)) = r.1) := fun h => hr (Subtype.ext h.symm)
      simp [this]
    · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [wsCoeff_eq]
    simp [ha]
  · simp

/-- `S⁰` is injective (`S₀ = I`). -/
theorem bggS0_injective : Function.Injective bggS0 := by
  refine (injective_iff_map_eq_zero bggS0).2 fun φ hφ => ?_
  have h1 : wsL2 (Ω := cubeDomain 3) 0 (ιt0 φ) = 0 := by
    have := congrArg D1.graphFst hφ
    rwa [graphFst_bggS0, _root_.map_zero] at this
  refine injective_piCLM (graphFst_injective D0) ?_
  rw [_root_.map_zero]
  refine PiLp.ext fun j => PiLp.ext fun r => ?_
  obtain ⟨r, hr⟩ := r
  have hr0 : r = ∅ := Finset.card_eq_zero.1 (by exact_mod_cast hr)
  subst hr0
  have := congrArg (fun z : W1 => z ⟨{j}, by simp⟩) h1
  simp only at this
  rw [wsL2_zero_apply] at this
  exact this

/-- **Thesis Prop 5.1 on the cube**: under the regularity hypothesis, the complex (5.1)
`Γ̄ → W̃¹ → W² × W̃²` built from (4.16) is a closed, exact short Hilbert complex. -/
theorem bggShort_closedRange_exact (hR : CurlPotential) :
    IsClosed (LinearMap.range (bggHilb.toShort (bggHyps hR) bggS0_injective).d₀.toFun :
      Set (Wv W1)) ∧
    IsClosed (LinearMap.range (bggHilb.toShort (bggHyps hR) bggS0_injective).d₁.toFun :
      Set (WithLp 2 (W2 × Wv W2))) ∧
    (bggHilb.toShort (bggHyps hR) bggS0_injective).d₁.ker =
      LinearMap.range (bggHilb.toShort (bggHyps hR) bggS0_injective).d₀.toFun ∧
    (bggHilb.toShort (bggHyps hR) bggS0_injective).d₀.ker = ⊥ :=
  bggHilb.toShort_closedRange_exact (bggHyps hR) bggS0_injective

/-- **Thesis Prop 5.2 on the cube**: under the regularity hypothesis, the saddle point problem
(5.3) for (4.16) is well posed. -/
theorem bgg_existsUnique_isSaddle (hR : CurlPotential) :
    (∀ f : Wv W1, ∃! xl : Feec.BGG.Xsp V0 Vt0 Vt1 × bggHilb.Wcheck,
      bggHilb.IsSaddle f xl.1 xl.2) ∧
    ∃ C, ∀ (f : Wv W1) (x : Feec.BGG.Xsp V0 Vt0 Vt1) (l : bggHilb.Wcheck),
      bggHilb.IsSaddle f x l → ‖x‖ + ‖l‖ ≤ C * ‖f‖ :=
  bggHilb.existsUnique_isSaddle (bggHyps hR)

end Feec.Models.Cube.WeakSymmetry
