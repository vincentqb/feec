module

public import Feec.Semigroup.Basic
public import Feec.ForMathlib.LinearPMap.Integral
public import Feec.ForMathlib.Analysis.NormedComplexification

/-!
# The complexification of a strongly continuous semigroup

The operators `S(t)_ℂ` form a strongly continuous semigroup on the complexification, with
`‖S(t)_ℂ‖ = ‖S(t)‖` and a generator that acts componentwise.
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

theorem map_apply_sub_smul {R : E →L[𝕜] E} {τ : ℝ}
    (hR : ∀ x y, (x, y) ∈ G.generator.graph → R (x - (τ : 𝕜) • y) = x)
    {p q : NormedComplexification 𝕜 E} (h : (p, q) ∈ G.complexification.generator.graph) :
    map R (p - (τ : ℂ) • q) = p := by
  obtain ⟨h1, h2⟩ := G.mem_graph_of_mem_graph_complexification h
  ext
  · rw [re_map, re_sub, re_ofReal_smul, hR _ _ h1]
  · rw [im_map, im_sub, im_ofReal_smul, hR _ _ h2]

end Feec.C0Semigroup
