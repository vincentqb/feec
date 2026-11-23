module

public import Solution.GradCurl
public import Solution.Absorbing

/-!
# The losses occur in the boundary layer

The domain of dependence of the challenge is `Feec.Models.BoundedDomain.depDomain`
(`depDomain_eq`: for `r > 0` the Euclidean ball `Σᵢ (zᵢ - yᵢ)² < r²` is the ball of
`EuclideanSpace ℝ (Fin 3)`), its Gauss law is `Feec`'s weak divergence against test fields
(`isDivFree_iff` of `Solution.Proxy`; `isDivFree_of_mem_ker` for `N(d₀†)`), and its pointwise
symmetry and trace-freeness are `Feec`'s `SymTF`, by definition. So:

* `interior_of` (`TSDVerdict.interior`): on every open `Ω`, the strong solutions of the system
  (4.14) are `Feec`'s strong solutions of the grad–curl complex through the state map, and
  `Feec.Models.BoundedDomain.tsd_cone` (`σ = 0` and the Gauss laws) and `tsd_depDomain`
  (symmetric and trace-free on the domain of dependence) apply;
* `absorbing_interior_of_eq` (`AbsorbingVerdict.interior`): every evolution of the absorbing
  problem is the absorbing semigroup (`absorbing_eq_semigroup`), whose orbits from TSD data keep
  the Gauss laws (`Feec.Models.Cube.Absorbing.absorbingSemigroup_divFree`) and are symmetric and
  trace-free on the domain of dependence (`absorbingSemigroup_symTF_depDomain`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.4, §4.10 (Prop 4.17)
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §7.3.2 (domain of dependence)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set MeasureTheory Filter

@[expose] public noncomputable section

namespace FEEC

open Feec Feec.Domain Feec.Models.BoundedDomain
open Feec.Models.Cube.Geometry (Q)
open Feec.Models.Cube.Absorbing (absorbingSemigroup absorbingSemigroup_divFree
  absorbingSemigroup_symTF_depDomain)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- **The domain of dependence of the challenge is `Feec`'s**, at `t ≥ 0`. -/
theorem depDomain_eq {t : ℝ} (ht : 0 ≤ t) (Ω : Set (Fin 3 → ℝ)) :
    depDomain Ω t = Feec.Models.BoundedDomain.depDomain Ω t := by
  ext y
  simp only [depDomain, Feec.Models.BoundedDomain.depDomain, mem_ofPred_eq]
  refine exists_congr fun r => and_congr_right fun hr => forall_congr' fun z => imp_congr_left ?_
  have e : dist (euc z) (euc y) ^ 2 = ∑ i, (z i - y i) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp [Real.dist_eq, sq_abs]
  rw [← e]
  exact pow_lt_pow_iff_left₀ dist_nonneg (ht.trans hr.le) two_ne_zero

variable {Ω : Set (Fin 3 → ℝ)}

/-- The fields of `N(d₀†)`, `d₀` the minimal gradient, satisfy the Gauss law. -/
theorem isDivFree_of_mem_ker (hΩ : IsOpen Ω) {X : L2F ℝ Ω Ix}
    (hX : X ∈ (gradCurl ℝ hΩ).d₀†.ker) : IsDivFree fun a b => X (a, b) :=
  (isDivFree_iff _).2 fun φ hφ => weakDiv_eq_zero_of_mem_ker hΩ hX φ hφ

/-- **The electric boundary conditions on every open `Ω`**: every strong solution of (4.14) from
data in `K` keeps `σ = 0` and the Gauss laws, and is symmetric and trace-free on the domain of
dependence. -/
theorem interior_of (hΩ : IsOpen Ω) (T : ℝ) (U : ℝ → L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2)
    (hU : IsStrongSolution (gradCurlWave Ω) (Icc 0 T) U) (h0 : U 0 ∈ tsdConstraint Ω) (t : ℝ)
    (ht : t ∈ Icc 0 T) :
    (U t).1 = 0 ∧ IsDivFree (mat1 (U t).2.1) ∧ IsDivFree (mat2 (U t).2.2) ∧
      IsSymTFOn (depDomain Ω t) (mat1 (U t).2.1) ∧
      IsSymTFOn (depDomain Ω t) (mat2 (U t).2.2) := by
  have hX := isStrongSolution_toFeec field0 fieldE fieldB (gradCurl ℝ hΩ)
    (mem_graph_grad_iff hΩ) (mem_graph_curl_iff hΩ) hU
  obtain ⟨h00, hE, hB⟩ := h0
  have hσ0 : winσ (gcState (U 0)) = 0 := by
    change -field0 (U 0).1 = 0
    rw [h00, map_zero, neg_zero]
  have hE0 : winE (gcState (U 0)) ∈ tsd Ω := by
    change fieldE (U 0).2.1 ∈ tsd Ω
    rw [← toIx_mat1, ← isTSD_iff]; exact hE
  have hB0 : winB (gcState (U 0)) ∈ tsd Ω := by
    change fieldB (U 0).2.2 ∈ tsd Ω
    rw [← toIx_mat2, ← isTSD_iff]; exact hB
  obtain ⟨hσ, hdE, hdB, -⟩ := tsd_cone hΩ hX hσ0 hE0 hB0 (x := 0) (r := 0)
    (fun z hz => absurd hz (not_lt.2 dist_nonneg)) ht
  have hdep := tsd_depDomain hΩ hX hσ0 hE0 hB0 ht
  rw [← depDomain_eq ht.1] at hdep
  refine ⟨?_, isDivFree_of_mem_ker hΩ hdE, isDivFree_of_mem_ker hΩ hdB,
    hdep.mono fun y hy => hy.1, hdep.mono fun y hy => hy.2⟩
  have h : -field0 (U t).1 = 0 := hσ
  rwa [neg_eq_zero, LinearIsometryEquiv.map_eq_zero_iff] at h

/-- **The absorbing boundary conditions: the losses occur in the boundary layer.** -/
theorem absorbing_interior_of_eq {Ω₃ : Set (Fin 3 → ℝ)} {Ω₂ : Set (Fin 2 → ℝ)}
    (h₃ : Ω₃ = Q (Fin 3)) (h₂ : Ω₂ = Q (Fin 2))
    (S : ℝ → WithLp 2 (L2F ℝ Ω₃ Ix × L2F ℝ Ω₃ Ix) →L[ℝ] WithLp 2 (L2F ℝ Ω₃ Ix × L2F ℝ Ω₃ Ix))
    (hS : IsEvolution ℝ (absorbingOn Ω₃ Ω₂) (Ici 0) S)
    (x : WithLp 2 (L2F ℝ Ω₃ Ix × L2F ℝ Ω₃ Ix)) (hx : x ∈ tsdPairOn Ω₃) (t : ℝ) (ht : 0 ≤ t) :
    IsDivFree (fun a b => (S t x).fst (a, b)) ∧ IsDivFree (fun a b => (S t x).snd (a, b)) ∧
      IsSymTFOn (depDomain Ω₃ t) (fun a b => (S t x).fst (a, b)) ∧
      IsSymTFOn (depDomain Ω₃ t) (fun a b => (S t x).snd (a, b)) := by
  subst h₃ h₂
  have hx' := (tsdPairOn_iff x).1 hx
  have hd := absorbingSemigroup_symTF_depDomain hx' ht
  rw [← depDomain_eq ht] at hd
  rw [absorbing_eq_semigroup hS ht]
  exact ⟨(isDivFree_iff _).2 fun φ hφ => (absorbingSemigroup_divFree hx' ht φ hφ).1,
    (isDivFree_iff _).2 fun φ hφ => (absorbingSemigroup_divFree hx' ht φ hφ).2,
    hd.mono fun y hy => hy.1, hd.mono fun y hy => hy.2⟩

end FEEC
