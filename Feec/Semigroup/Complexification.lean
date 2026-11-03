module

public import Feec.Semigroup.Basic
public import Feec.ForMathlib.LinearPMap.Integral
public import Feec.ForMathlib.Analysis.NormedComplexification

/-!
# The complexification of a strongly continuous semigroup

For a strongly continuous semigroup `G` on a normed space `E` over `𝕜 = ℝ` or `ℂ`, the operators
`S(t)_ℂ` form a strongly continuous semigroup `C0Semigroup.complexification G` on the
complexification `E_ℂ` (`NormedComplexification`, Taylor norm), with `‖S(t)_ℂ‖ = ‖S(t)‖`.
Its generator acts componentwise: if `(p, q)` is in its graph, so are `(re p, re q)` and
`(im p, im q)` in the graph of the generator `A` of `G`
(`C0Semigroup.mem_graph_of_mem_graph_complexification`), and `(x, y)` in the graph of `A` gives
`(x + i 0, y + i 0)` in its graph (`C0Semigroup.mk_mem_graph_complexification`). Hence an
operator `R` with `R (x - τ A x) = x` on `D(A)` has a complexification with the same property
(`C0Semigroup.map_apply_sub_smul`). This brings the complex points of the spectrum, through the
complex Hille–Yosida estimates, to real Banach spaces.

## References

* [K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*][EngelNagel2000],
  §II.1

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Complexification

@[expose] public noncomputable section

namespace Feec.C0Semigroup

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] (G : C0Semigroup 𝕜 E)

/-- **The complexification** `t ↦ S(t)_ℂ` of a strongly continuous semigroup. -/
def complexification : C0Semigroup ℂ (NormedComplexification 𝕜 E) where
  S t := map (G.S t)
  map_zero := by rw [G.map_zero]; exact (mapHom (n := .taylor) (𝕜 := 𝕜) (V := E)).map_one
  map_add s t hs ht := by
    rw [G.map_add s t hs ht]; exact (mapHom (n := .taylor) (𝕜 := 𝕜) (V := E)).map_mul _ _
  strongCont p := continuous_mk.comp_continuousOn ((G.strongCont p.re).prodMk (G.strongCont p.im))

@[simp] theorem complexification_S (t : ℝ) : G.complexification.S t = map (G.S t) := rfl

theorem norm_complexification_S (t : ℝ) : ‖G.complexification.S t‖ = ‖G.S t‖ := norm_map _

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **The generator of the complexification acts componentwise**: `(p, q)` in its graph gives
`(re p, re q)` and `(im p, im q)` in the graph of the generator. -/
theorem mem_graph_of_mem_graph_complexification {p q : NormedComplexification 𝕜 E}
    (h : (p, q) ∈ G.complexification.generator.graph) :
    (p.re, q.re) ∈ G.generator.graph ∧ (p.im, q.im) ∈ G.generator.graph := by
  obtain ⟨hp, rfl⟩ := LinearPMap.mem_graph_iff_exists.1 h
  have d := G.complexification.hasDerivWithinAt_generator ⟨p, hp⟩
  have dre : HasDerivWithinAt (fun t => G.S t p.re) (G.complexification.generator ⟨p, hp⟩).re
      (Ici 0) 0 := (reCLM (n := .taylor) (𝕜 := 𝕜) (V := E)).hasFDerivAt.comp_hasDerivWithinAt 0 d
  have dim : HasDerivWithinAt (fun t => G.S t p.im) (G.complexification.generator ⟨p, hp⟩).im
      (Ici 0) 0 := (imCLM (n := .taylor) (𝕜 := 𝕜) (V := E)).hasFDerivAt.comp_hasDerivWithinAt 0 d
  exact ⟨LinearPMap.mem_graph_iff_exists.2 ⟨⟨_, dre⟩, G.generator_apply_eq dre⟩,
    LinearPMap.mem_graph_iff_exists.2 ⟨⟨_, dim⟩, G.generator_apply_eq dim⟩⟩

/-- Conversely, `(x, y)` in the graph of the generator gives `(x + i 0, y + i 0)` in the graph of
the generator of the complexification. -/
theorem mk_mem_graph_complexification {x y : E} (h : (x, y) ∈ G.generator.graph) :
    (Complexification.mk x 0, Complexification.mk y 0) ∈
      G.complexification.generator.graph := by
  obtain ⟨hx, rfl⟩ := LinearPMap.mem_graph_iff_exists.1 h
  have e : (fun t => G.complexification.S t (Complexification.mk x 0)) =
      ofRealCLM ∘ fun t => G.S t x :=
    funext fun t => by ext <;> simp [map_mk]
  have d : HasDerivWithinAt (fun t => G.complexification.S t (Complexification.mk x 0))
      (Complexification.mk (G.generator ⟨x, hx⟩) 0) (Ici 0) 0 :=
    e ▸ (ofRealCLM (n := .taylor) (𝕜 := 𝕜) (V := E)).hasFDerivAt.comp_hasDerivWithinAt 0
      (G.hasDerivWithinAt_generator ⟨x, hx⟩)
  exact LinearPMap.mem_graph_iff_exists.2 ⟨⟨_, d⟩, G.complexification.generator_apply_eq d⟩

/-- An operator `R` with `R (x - τ y) = x` on the graph of the generator has a complexification
with the same property for the complexified semigroup. -/
theorem map_apply_sub_smul {R : E →L[𝕜] E} {τ : ℝ}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x)
    {p q : NormedComplexification 𝕜 E} (h : (p, q) ∈ G.complexification.generator.graph) :
    map R (p - (τ : ℂ) • q) = p := by
  obtain ⟨h1, h2⟩ := G.mem_graph_of_mem_graph_complexification h
  ext
  · rw [re_map, re_sub, re_ofReal_smul, hR _ _ h1]
  · rw [im_map, im_sub, im_ofReal_smul, hR _ _ h2]

end Feec.C0Semigroup
