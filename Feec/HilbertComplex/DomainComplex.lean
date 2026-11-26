module

public import Feec.HilbertComplex.Hodge

/-!
# The domain complex

The domain complex of a Hilbert complex: the spaces `Vⁱ = D(d i (c.next i))` with the graph inner
product and the restricted, bounded differentials, a Hilbert complex with the same cycles, harmonic
forms and closed ranges.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Set

@[expose] public noncomputable section

namespace Feec.HilbertComplex

/-- The Hilbert complex of a complex of bounded operators, with full domains. -/
def ofBounded {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {X : ι → Type*}
    [∀ i, NormedAddCommGroup (X i)] [∀ i, InnerProductSpace 𝕜 (X i)] [∀ i, CompleteSpace (X i)]
    (δ : ∀ i j, X i →L[𝕜] X j) (shape : ∀ i j, ¬ c.Rel i j → δ i j = 0)
    (comp : ∀ i j k x, δ j k (δ i j x) = 0) : HilbertComplex 𝕜 c X where
  d i j := (δ i j : X i →ₗ[𝕜] X j).toPMap ⊤
  shape i j h := by rw [shape i j h]; rfl
  dense _ _ := by simp
  closed i j := ContinuousLinearMap.isClosed_toPMap_top (δ i j)
  mapsTo _ _ _ _ := Submodule.mem_top
  d_comp_d i j k x := comp i j k x

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

theorem domain_next_le (i j : ι) : (H.d i (c.next i)).domain ≤ (H.d i j).domain := by
  by_cases hj : j = c.next i
  · subst hj; exact le_rfl
  · rw [H.d_eq_zero_of_ne_next hj]; exact le_top

/-- The domain space `Vⁱ = D(d i (c.next i))` with the graph inner product. -/
abbrev domainSpace (i : ι) : Type _ := (H.d i (c.next i)).GraphSpace

instance (i : ι) : CompleteSpace (H.domainSpace i) := (H.closed _ _).completeSpace_graphSpace

/-- The inclusion `Vⁱ → Wⁱ`. -/
def domainIncl (i : ι) : H.domainSpace i →L[𝕜] W i := (H.d i (c.next i)).graphFst

theorem domainIncl_injective (i : ι) : Function.Injective (H.domainIncl i) :=
  graphFst_injective _

theorem domainIncl_mem (i : ι) (v : H.domainSpace i) :
    H.domainIncl i v ∈ (H.d i (c.next i)).domain :=
  (H.d i (c.next i)).graphFst_mem_domain v

/-- `Vⁱ → D(d i j)`, `v ↦ ι v`. -/
def domainCoord (i j : ι) : H.domainSpace i →ₗ[𝕜] (H.d i j).domain :=
  LinearMap.codRestrict _ (H.domainIncl i).toLinearMap fun v =>
    H.domain_next_le i j (H.domainIncl_mem i v)

@[simp] theorem coe_domainCoord (i j : ι) (v : H.domainSpace i) :
    (H.domainCoord i j v : W i) = H.domainIncl i v := rfl

@[simp] theorem domainIncl_toGraphSpace (i : ι) (x : (H.d i (c.next i)).domain) :
    H.domainIncl i ((H.d i (c.next i)).toGraphSpace x) = x := rfl

theorem norm_d_domainCoord_le (i j : ι) (v : H.domainSpace i) :
    ‖H.d i j (H.domainCoord i j v)‖ ≤ ‖v‖ := by
  by_cases hj : j = c.next i
  · subst hj
    obtain ⟨x, rfl, -, -⟩ := (H.d i (c.next i)).exists_toGraphSpace_eq v
    exact WithLp.norm_snd_le (x := WithLp.toLp 2 ((x : W i), H.d i (c.next i) x))
  · rw [apply_eq_zero_of_eq_zero (H.d_eq_zero_of_ne_next hj), norm_zero]
    exact norm_nonneg _

theorem norm_domainIncl_le (i : ι) (v : H.domainSpace i) : ‖H.domainIncl i v‖ ≤ ‖v‖ :=
  norm_graphFst_le v

theorem norm_sq_domainSpace (i : ι) (v : H.domainSpace i) :
    ‖v‖ ^ 2 = ‖H.domainIncl i v‖ ^ 2 + ‖H.d i (c.next i) (H.domainCoord i _ v)‖ ^ 2 := by
  obtain ⟨x, rfl, -, -⟩ := (H.d i (c.next i)).exists_toGraphSpace_eq v
  exact WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 ((x : W i), H.d i (c.next i) x))

theorem toLp_d_mem (i j : ι) (v : H.domainSpace i) :
    WithLp.toLp 2 (H.d i j (H.domainCoord i j v), (0 : W (c.next j))) ∈
      (H.d j (c.next j)).graphL2 := by
  rw [mem_graphL2, WithLp.ofLp_toLp, LinearPMap.mem_graph_iff]
  exact ⟨⟨_, H.mapsTo i j (c.next j) _⟩, rfl, H.d_comp_d i j (c.next j) _⟩

/-- The bounded differential `Vⁱ → Vʲ`, `(x, d x) ↦ (d i j x, 0)`. -/
def domainD (i j : ι) : H.domainSpace i →L[𝕜] H.domainSpace j :=
  LinearMap.mkContinuous
    (LinearMap.codRestrict _
      ((WithLp.linearEquiv 2 𝕜 (W j × W (c.next j))).symm.toLinearMap ∘ₗ
        (((H.d i j).toFun ∘ₗ H.domainCoord i j).prod 0)) (H.toLp_d_mem i j))
    1 fun v => by
      rw [one_mul]
      refine le_of_eq_of_le ?_ (H.norm_d_domainCoord_le i j v)
      change ‖WithLp.toLp 2 (H.d i j (H.domainCoord i j v), (0 : W (c.next j)))‖ = _
      rw [WithLp.prod_norm_eq_of_L2]
      simp

@[simp] theorem domainIncl_domainD (i j : ι) (v : H.domainSpace i) :
    H.domainIncl j (H.domainD i j v) = H.d i j (H.domainCoord i j v) := rfl

theorem d_domainCoord_domainD (i j k : ι) (v : H.domainSpace i) :
    H.d j k (H.domainCoord j k (H.domainD i j v)) = 0 :=
  H.d_comp_d i j k (H.domainCoord i j v)

theorem domainD_eq_zero_of_not_rel {i j : ι} (h : ¬ c.Rel i j) : H.domainD i j = 0 :=
  ContinuousLinearMap.ext fun v => H.domainIncl_injective j (by
    rw [domainIncl_domainD, apply_eq_zero_of_not_rel _ h, _root_.zero_apply,
      _root_.map_zero])

theorem domainD_comp_domainD (i j k : ι) (v : H.domainSpace i) :
    H.domainD j k (H.domainD i j v) = 0 :=
  H.domainIncl_injective k (by
    rw [domainIncl_domainD, d_domainCoord_domainD, _root_.map_zero])

/-- **The domain complex**: the spaces `Vⁱ` with the bounded differentials `domainD`.
[QuennevilleBelair2015], §4.2; [BruningLesch1992], §2; [AFW2010], §3.1.2 -/
def domainComplex : HilbertComplex 𝕜 c H.domainSpace :=
  ofBounded H.domainD (fun _ _ h => H.domainD_eq_zero_of_not_rel h) H.domainD_comp_domainD

theorem range_domainComplex_d (i j : ι) :
    LinearMap.range (H.domainComplex.d i j).toFun =
      LinearMap.range (H.domainD i j : H.domainSpace i →ₗ[𝕜] H.domainSpace j) := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩

/-! ### Cycles and boundaries of the domain complex -/

theorem mem_domainComplex_cycles {i : ι} {v : H.domainSpace i} :
    v ∈ H.domainComplex.cycles i ↔ H.domainIncl i v ∈ H.cycles i := by
  rw [cycles, cycles, LinearPMap.mem_ker_iff, LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨y, rfl, hy⟩
    refine ⟨H.domainCoord i _ y, rfl, ?_⟩
    have := congrArg (H.domainIncl (c.next i)) hy
    rwa [_root_.map_zero] at this
  · rintro ⟨y, hy, hy0⟩
    refine ⟨⟨v, Submodule.mem_top⟩, rfl, H.domainIncl_injective _ ?_⟩
    change H.d i (c.next i) (H.domainCoord i _ v) = H.domainIncl _ 0
    rw [_root_.map_zero, ← hy0]; congr 1; exact Subtype.ext hy

theorem norm_of_mem_domainComplex_cycles {i : ι} {v : H.domainSpace i}
    (hv : v ∈ H.domainComplex.cycles i) : ‖v‖ = ‖H.domainIncl i v‖ := by
  obtain ⟨y, hy, hy0⟩ := (LinearPMap.mem_ker_iff).1 ((H.mem_domainComplex_cycles).1 hv)
  have h := H.norm_sq_domainSpace i v
  have e : H.d i (c.next i) (H.domainCoord i _ v) = 0 := by
    rw [← hy0]; congr 1; exact Subtype.ext hy
  rw [e, norm_zero, zero_pow two_ne_zero, add_zero] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem inner_of_mem_domainComplex_cycles {i : ι} {u : H.domainSpace i}
    (hu : u ∈ H.domainComplex.cycles i) (v : H.domainSpace i) :
    ⟪u, v⟫_𝕜 = ⟪H.domainIncl i u, H.domainIncl i v⟫_𝕜 := by
  obtain ⟨y, hy, hy0⟩ := (LinearPMap.mem_ker_iff).1 ((H.mem_domainComplex_cycles).1 hu)
  have e : (H.d i (c.next i)).graphSnd u = 0 := by
    obtain ⟨x, rfl, -, -⟩ := (H.d i (c.next i)).exists_toGraphSpace_eq u
    change H.d i (c.next i) x = 0
    rw [← hy0]; congr 1; exact Subtype.ext hy
  change ⟪(u : WithLp 2 (W i × W (c.next i))), (v : WithLp 2 (W i × W (c.next i)))⟫_𝕜 = _
  rw [WithLp.prod_inner_apply]
  change _ + ⟪(H.d i (c.next i)).graphSnd u, _⟫_𝕜 = _
  rw [e, inner_zero_left, add_zero]
  rfl

theorem boundaries_eq_bot_of_not_rel {j : ι} (h : ¬ c.Rel (c.prev j) j) : H.boundaries j = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨x, rfl⟩
  exact (Submodule.mem_bot 𝕜).2 (apply_eq_zero_of_not_rel _ h x)

theorem map_domainIncl_range_domainD {i j : ι} (h : c.Rel i j) :
    (LinearMap.range (H.domainD i j : H.domainSpace i →ₗ[𝕜] H.domainSpace j)).map
        (H.domainIncl j : H.domainSpace j →ₗ[𝕜] W j) = LinearMap.range (H.d i j).toFun := by
  obtain rfl := c.next_eq' h
  ext w
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨H.domainCoord _ _ v, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨(H.d i (c.next i)).toGraphSpace x, rfl⟩, rfl⟩

theorem map_domainIncl_boundaries (j : ι) :
    (H.domainComplex.boundaries j).map (H.domainIncl j : H.domainSpace j →ₗ[𝕜] W j) =
      H.boundaries j := by
  by_cases h : c.Rel (c.prev j) j
  · rw [H.domainComplex.boundaries_eq h, range_domainComplex_d, H.boundaries_eq h,
      H.map_domainIncl_range_domainD h]
  · rw [H.boundaries_eq_bot_of_not_rel h, H.domainComplex.boundaries_eq_bot_of_not_rel h,
      Submodule.map_bot]

/-- **Closed in `V` ⇔ closed in `W`**: the boundaries of the domain complex are closed iff
those of `H` are. [QuennevilleBelair2015], §4.2 -/
theorem domainComplex_closedRangeAt_iff (j : ι) :
    H.domainComplex.ClosedRangeAt j ↔ H.ClosedRangeAt j := by
  have hZ := H.domainComplex.isClosed_cycles j
  have : CompleteSpace (H.domainComplex.cycles j) := hZ.completeSpace_coe
  -- `ι` restricted to the cycles of `V` is an isometry
  let f : H.domainComplex.cycles j →L[𝕜] W j :=
    (H.domainIncl j).comp (H.domainComplex.cycles j).subtypeL
  have hf : Isometry f := AddMonoidHomClass.isometry_of_norm f fun z =>
    (H.norm_of_mem_domainComplex_cycles z.2).symm
  have hBV : (H.domainComplex.boundaries j : Set (H.domainSpace j)) =
      Subtype.val '' (Subtype.val ⁻¹' (H.domainComplex.boundaries j : Set (H.domainSpace j)) :
        Set (H.domainComplex.cycles j)) := by
    ext v; constructor
    · intro hv; exact ⟨⟨v, H.domainComplex.boundaries_le_cycles j hv⟩, hv, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  have hBW : (H.boundaries j : Set (W j)) =
      f '' (Subtype.val ⁻¹' (H.domainComplex.boundaries j : Set (H.domainSpace j))) := by
    rw [← H.map_domainIncl_boundaries j, Submodule.map_coe]
    ext w; constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, H.domainComplex.boundaries_le_cycles j hv⟩, hv, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  unfold ClosedRangeAt
  rw [hBV, hBW]
  exact hZ.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.symm.trans
    hf.isClosedEmbedding.isClosed_iff_image_isClosed

/-! ### Harmonic forms and the `V`-level Hodge decomposition -/

theorem map_domainIncl_harmonic (i : ι) :
    (H.domainComplex.harmonic i).map (H.domainIncl i : H.domainSpace i →ₗ[𝕜] W i) =
      H.harmonic i := by
  ext w
  simp only [Submodule.mem_map, ContinuousLinearMap.coe_coe, mem_harmonic_iff]
  constructor
  · rintro ⟨v, ⟨hvZ, hvB⟩, rfl⟩
    refine ⟨H.mem_domainComplex_cycles.1 hvZ, ?_⟩
    rw [← H.map_domainIncl_boundaries i, Submodule.mem_orthogonal]
    rintro _ ⟨u, hu, rfl⟩
    have := (Submodule.mem_orthogonal _ _).1 hvB u hu
    rwa [H.inner_of_mem_domainComplex_cycles (H.domainComplex.boundaries_le_cycles i hu)] at this
  · rintro ⟨hwZ, hwB⟩
    obtain ⟨y, rfl, -⟩ := (LinearPMap.mem_ker_iff).1 hwZ
    set v := (H.d i (c.next i)).toGraphSpace y
    have hvZ : v ∈ H.domainComplex.cycles i := H.mem_domainComplex_cycles.2 hwZ
    refine ⟨v, ⟨hvZ, ?_⟩, rfl⟩
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [H.inner_of_mem_domainComplex_cycles (H.domainComplex.boundaries_le_cycles i hu)]
    rw [← H.map_domainIncl_boundaries i] at hwB
    exact (Submodule.mem_orthogonal _ _).1 hwB _ (Submodule.mem_map_of_mem hu)

/-- **Hodge decomposition of `V`**: under closed range, `Vⁱ = 𝔅ⁱ ⊕ ℌⁱ ⊕ (𝔷ⁱ)^{⊥V}` in the domain
complex, pairwise orthogonal in the graph inner product. [QuennevilleBelair2015], Thm 4.1 -/
theorem hodge_domainComplex {i : ι} (hi : H.ClosedRangeAt i) :
    H.domainComplex.boundaries i ⊔ H.domainComplex.harmonic i ⊔
        (H.domainComplex.cycles i)ᗮ = ⊤ ∧
      H.domainComplex.boundaries i ⟂ H.domainComplex.harmonic i ∧
      H.domainComplex.harmonic i ⟂ (H.domainComplex.cycles i)ᗮ ∧
      H.domainComplex.boundaries i ⟂ (H.domainComplex.cycles i)ᗮ := by
  have hV := (H.domainComplex_closedRangeAt_iff i).2 hi
  have hZ := H.domainComplex.boundaries_sup_harmonic hV
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hZ]; exact Submodule.sup_orthogonal_of_hasOrthogonalProjection
  · have := H.domainComplex.isOrtho_closure_boundaries_harmonic i
    exact this.mono_left (H.domainComplex.boundaries i).le_topologicalClosure
  · exact (Submodule.isOrtho_orthogonal_right _).mono_left
      (H.domainComplex.harmonic_le_cycles i)
  · exact (Submodule.isOrtho_orthogonal_right _).mono_left
      (H.domainComplex.boundaries_le_cycles i)

end Feec.HilbertComplex
