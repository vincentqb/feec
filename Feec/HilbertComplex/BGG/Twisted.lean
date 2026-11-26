module

public import Feec.ForMathlib.LinearPMap.Bounded
public import Feec.HilbertComplex.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The twisted Hilbert complex of analytic BGG data of any length

Two Hilbert complexes linked by bounded connecting maps `S` with `S D(d̃) ⊆ D(d)` and
`d S = -S d̃` (`Feec.BGG.HilbertData`) give the twisted Hilbert complex
`(σ, φ) ↦ (dσ - Sφ, d̃φ)` on `Wⁱ ⊕ W̃ⁱ` (`HilbertData.twistComplex`, [ArnoldHu2021], §5.1).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §5.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 : Type*} [RCLike 𝕜] {E₁ E₂ F₁ F₂ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

theorem _root_.WithLp.prod_ext' {p : ENNReal} {α β : Type*} {x y : WithLp p (α × β)}
    (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  (WithLp.ext_iff p).2 (Prod.ext h1 h2)

/-- The rearrangement `((x₁, x₂), (y₁, y₂)) ↦ ((x₁, y₁), (x₂, y₂))`. -/
def prodL2Swap : WithLp 2 (E₁ × E₂) × WithLp 2 (F₁ × F₂) →ₗ[𝕜] (E₁ × F₁) × (E₂ × F₂) where
  toFun p := ((p.1.fst, p.2.fst), (p.1.snd, p.2.snd))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem continuous_prodL2Swap : Continuous (prodL2Swap (𝕜 := 𝕜) (E₁ := E₁) (E₂ := E₂)
    (F₁ := F₁) (F₂ := F₂)) := by
  have h1 : Continuous fun x : WithLp 2 (E₁ × E₂) => x.fst :=
    (WithLp.fstL 2 𝕜 E₁ E₂).continuous
  have h2 : Continuous fun x : WithLp 2 (E₁ × E₂) => x.snd :=
    (WithLp.sndL 2 𝕜 E₁ E₂).continuous
  have h3 : Continuous fun x : WithLp 2 (F₁ × F₂) => x.fst :=
    (WithLp.fstL 2 𝕜 F₁ F₂).continuous
  have h4 : Continuous fun x : WithLp 2 (F₁ × F₂) => x.snd :=
    (WithLp.sndL 2 𝕜 F₁ F₂).continuous
  exact ((h1.comp continuous_fst).prodMk (h3.comp continuous_snd)).prodMk
    ((h2.comp continuous_fst).prodMk (h4.comp continuous_snd))

/-- The graph of `T₁ ⊕ T₂`. -/
def prodL2Graph (T₁ : E₁ →ₗ.[𝕜] F₁) (T₂ : E₂ →ₗ.[𝕜] F₂) :
    Submodule 𝕜 (WithLp 2 (E₁ × E₂) × WithLp 2 (F₁ × F₂)) :=
  (T₁.graph.prod T₂.graph).comap prodL2Swap

/-- The direct sum `T₁ ⊕ T₂` on `WithLp 2` products, with domain `D(T₁) × D(T₂)`. -/
def prodL2 (T₁ : E₁ →ₗ.[𝕜] F₁) (T₂ : E₂ →ₗ.[𝕜] F₂) :
    WithLp 2 (E₁ × E₂) →ₗ.[𝕜] WithLp 2 (F₁ × F₂) :=
  (prodL2Graph T₁ T₂).toLinearPMap

theorem prodL2Graph_hg (T₁ : E₁ →ₗ.[𝕜] F₁) (T₂ : E₂ →ₗ.[𝕜] F₂) :
    ∀ (x : WithLp 2 (E₁ × E₂) × WithLp 2 (F₁ × F₂)) (_ : x ∈ prodL2Graph T₁ T₂),
      x.1 = 0 → x.2 = 0 := by
  rintro ⟨x, y⟩ ⟨h1, h2⟩ (rfl : x = 0)
  exact WithLp.prod_ext' (T₁.graph_fst_eq_zero_snd h1 rfl) (T₂.graph_fst_eq_zero_snd h2 rfl)

theorem prodL2_graph (T₁ : E₁ →ₗ.[𝕜] F₁) (T₂ : E₂ →ₗ.[𝕜] F₂) :
    (prodL2 T₁ T₂).graph = prodL2Graph T₁ T₂ :=
  Submodule.toLinearPMap_graph_eq _ (prodL2Graph_hg T₁ T₂)

theorem mem_prodL2_domain {T₁ : E₁ →ₗ.[𝕜] F₁} {T₂ : E₂ →ₗ.[𝕜] F₂} {x : WithLp 2 (E₁ × E₂)} :
    x ∈ (prodL2 T₁ T₂).domain ↔ x.fst ∈ T₁.domain ∧ x.snd ∈ T₂.domain := by
  rw [LinearPMap.mem_domain_iff, prodL2_graph]
  constructor
  · rintro ⟨y, h1, h2⟩
    exact ⟨mem_domain_of_mem_graph h1, mem_domain_of_mem_graph h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨WithLp.toLp 2 (T₁ ⟨_, h1⟩, T₂ ⟨_, h2⟩), mem_graph T₁ ⟨_, h1⟩, mem_graph T₂ ⟨_, h2⟩⟩

theorem prodL2_apply_fst {T₁ : E₁ →ₗ.[𝕜] F₁} {T₂ : E₂ →ₗ.[𝕜] F₂} (x : (prodL2 T₁ T₂).domain) :
    (prodL2 T₁ T₂ x).fst = T₁ ⟨(x : WithLp 2 (E₁ × E₂)).fst, (mem_prodL2_domain.1 x.2).1⟩ := by
  have hm : ((x : WithLp 2 (E₁ × E₂)), prodL2 T₁ T₂ x) ∈ prodL2Graph T₁ T₂ := by
    rw [← prodL2_graph]; exact mem_graph _ x
  exact (T₁.mem_graph_iff.1 hm.1 |>.choose_spec.2).symm.trans (congrArg T₁
    (Subtype.ext (T₁.mem_graph_iff.1 hm.1).choose_spec.1))

theorem prodL2_apply_snd {T₁ : E₁ →ₗ.[𝕜] F₁} {T₂ : E₂ →ₗ.[𝕜] F₂} (x : (prodL2 T₁ T₂).domain) :
    (prodL2 T₁ T₂ x).snd = T₂ ⟨(x : WithLp 2 (E₁ × E₂)).snd, (mem_prodL2_domain.1 x.2).2⟩ := by
  have hm : ((x : WithLp 2 (E₁ × E₂)), prodL2 T₁ T₂ x) ∈ prodL2Graph T₁ T₂ := by
    rw [← prodL2_graph]; exact mem_graph _ x
  exact (T₂.mem_graph_iff.1 hm.2 |>.choose_spec.2).symm.trans (congrArg T₂
    (Subtype.ext (T₂.mem_graph_iff.1 hm.2).choose_spec.1))

theorem IsClosed.prodL2 {T₁ : E₁ →ₗ.[𝕜] F₁} {T₂ : E₂ →ₗ.[𝕜] F₂} (h₁ : T₁.IsClosed)
    (h₂ : T₂.IsClosed) : (prodL2 T₁ T₂).IsClosed := by
  rw [LinearPMap.IsClosed, prodL2_graph]
  exact (h₁.prod h₂).preimage continuous_prodL2Swap

theorem dense_prodL2_domain {T₁ : E₁ →ₗ.[𝕜] F₁} {T₂ : E₂ →ₗ.[𝕜] F₂}
    (h₁ : Dense (T₁.domain : Set E₁)) (h₂ : Dense (T₂.domain : Set E₂)) :
    Dense ((prodL2 T₁ T₂).domain : Set (WithLp 2 (E₁ × E₂))) := by
  have : ((prodL2 T₁ T₂).domain : Set (WithLp 2 (E₁ × E₂))) =
      (WithLp.prodContinuousLinearEquiv 2 𝕜 E₁ E₂) ⁻¹' ((T₁.domain : Set E₁) ×ˢ T₂.domain) := by
    ext x; exact mem_prodL2_domain
  rw [this]
  exact (h₁.prod h₂).preimage (WithLp.prodContinuousLinearEquiv 2 𝕜 E₁ E₂).toHomeomorph.isOpenMap

theorem prodL2_zero : prodL2 (0 : E₁ →ₗ.[𝕜] F₁) (0 : E₂ →ₗ.[𝕜] F₂) = 0 := by
  refine LinearPMap.ext ?_ fun x hx _ => ?_
  · ext x; simp [mem_prodL2_domain, zero_domain]
  · have h1 := prodL2_apply_fst ⟨x, hx⟩
    have h2 := prodL2_apply_snd ⟨x, hx⟩
    simp only [zero_apply] at h1 h2
    rw [zero_apply]
    exact WithLp.prod_ext' h1 h2

end LinearPMap

namespace Feec.BGG

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W Wt : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (Wt i)] [∀ i, InnerProductSpace 𝕜 (Wt i)]
  [∀ i, CompleteSpace (Wt i)]

/-- Two Hilbert complexes linked by bounded maps `S` with `S D(d̃) ⊆ D(d)` and `d S = -S d̃`. -/
structure HilbertData (𝕜 : Type*) [RCLike 𝕜] {ι : Type*} (c : ComplexShape ι)
    (W Wt : ι → Type*) [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
    [∀ i, CompleteSpace (W i)] [∀ i, NormedAddCommGroup (Wt i)]
    [∀ i, InnerProductSpace 𝕜 (Wt i)] [∀ i, CompleteSpace (Wt i)] where
  /-- the top complex -/
  H : HilbertComplex 𝕜 c W
  /-- the bottom complex -/
  Ht : HilbertComplex 𝕜 c Wt
  /-- the connecting maps -/
  S : ∀ i j, Wt i →L[𝕜] W j
  shape_S : ∀ i j, ¬ c.Rel i j → S i j = 0
  S_mapsTo : ∀ i j k (φ : (Ht.d i j).domain), S i j φ ∈ (H.d j k).domain
  anticomm : ∀ i j k (φ : (Ht.d i j).domain),
    H.d j k ⟨S i j φ, S_mapsTo i j k φ⟩ = -S j k (Ht.d i j φ)

namespace HilbertData

variable (D : HilbertData 𝕜 c W Wt)

/-- The bounded part `(σ, φ) ↦ (-Sφ, 0)` of the twisted differential. -/
def twistS (i j : ι) : WithLp 2 (W i × Wt i) →L[𝕜] WithLp 2 (W j × Wt j) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 (W j) (Wt j)).symm.toContinuousLinearMap ∘L
    ((-(D.S i j)).prod 0) ∘L WithLp.sndL 2 𝕜 (W i) (Wt i)

@[simp] theorem twistS_fst (i j : ι) (x : WithLp 2 (W i × Wt i)) :
    (D.twistS i j x).fst = -D.S i j x.snd := rfl

@[simp] theorem twistS_snd (i j : ι) (x : WithLp 2 (W i × Wt i)) :
    (D.twistS i j x).snd = 0 := rfl

/-- The twisted differential `(σ, φ) ↦ (dσ - Sφ, d̃φ)`, with domain `D(d) × D(d̃)`. -/
def twistD (i j : ι) : WithLp 2 (W i × Wt i) →ₗ.[𝕜] WithLp 2 (W j × Wt j) :=
  (D.twistS i j : WithLp 2 (W i × Wt i) →ₗ[𝕜] WithLp 2 (W j × Wt j)) +ᵥ
    LinearPMap.prodL2 (D.H.d i j) (D.Ht.d i j)

theorem mem_twistD_domain {i j : ι} {x : WithLp 2 (W i × Wt i)} :
    x ∈ (D.twistD i j).domain ↔ x.fst ∈ (D.H.d i j).domain ∧ x.snd ∈ (D.Ht.d i j).domain :=
  LinearPMap.mem_prodL2_domain

theorem twistD_apply {i j : ι} (x : (D.twistD i j).domain) :
    D.twistD i j x = D.twistS i j x + LinearPMap.prodL2 (D.H.d i j) (D.Ht.d i j) ⟨x, x.2⟩ :=
  LinearPMap.vadd_apply _ _ x

theorem twistD_apply_fst {i j : ι} (x : (D.twistD i j).domain) :
    (D.twistD i j x).fst = D.H.d i j ⟨(x : WithLp 2 (W i × Wt i)).fst,
      (D.mem_twistD_domain.1 x.2).1⟩ - D.S i j (x : WithLp 2 (W i × Wt i)).snd := by
  rw [twistD_apply, WithLp.add_fst, twistS_fst, LinearPMap.prodL2_apply_fst]
  abel

theorem twistD_apply_snd {i j : ι} (x : (D.twistD i j).domain) :
    (D.twistD i j x).snd = D.Ht.d i j ⟨(x : WithLp 2 (W i × Wt i)).snd,
      (D.mem_twistD_domain.1 x.2).2⟩ := by
  rw [twistD_apply, WithLp.add_snd, twistS_snd, LinearPMap.prodL2_apply_snd, zero_add]

theorem twistD_eq_zero {i j : ι} (h : ¬ c.Rel i j) : D.twistD i j = 0 := by
  have hS : D.twistS i j = 0 := by
    ext x
    refine WithLp.prod_ext' ?_ rfl
    rw [twistS_fst, D.shape_S i j h]; simp
  rw [twistD, D.H.shape i j h, D.Ht.shape i j h, LinearPMap.prodL2_zero, hS]
  exact LinearPMap.ext rfl fun x hx _ => by
    rw [LinearPMap.vadd_apply]; simp

/-- The twisted Hilbert complex `(σ, φ) ↦ (dσ - Sφ, d̃φ)` on `Wⁱ ⊕ W̃ⁱ`. [ArnoldHu2021], §5.1 -/
def twistComplex : HilbertComplex 𝕜 c (fun i => WithLp 2 (W i × Wt i)) where
  d := D.twistD
  shape i j h := D.twistD_eq_zero h
  dense i j := LinearPMap.dense_prodL2_domain (D.H.dense i j) (D.Ht.dense i j)
  closed i j := ((D.H.closed i j).prodL2 (D.Ht.closed i j)).vadd _
  mapsTo i j k x := by
    rw [mem_twistD_domain, twistD_apply_fst, twistD_apply_snd]
    refine ⟨Submodule.sub_mem _ (D.H.mapsTo i j k _) ?_, D.Ht.mapsTo i j k _⟩
    exact D.S_mapsTo i j k ⟨_, (D.mem_twistD_domain.1 x.2).2⟩
  d_comp_d i j k x := by
    set σ : (D.H.d i j).domain :=
      ⟨(x : WithLp 2 (W i × Wt i)).fst, (D.mem_twistD_domain.1 x.2).1⟩
    set φ : (D.Ht.d i j).domain :=
      ⟨(x : WithLp 2 (W i × Wt i)).snd, (D.mem_twistD_domain.1 x.2).2⟩
    have key1 : ∀ y : (D.H.d j k).domain, (y : W j) = D.H.d i j σ - D.S i j φ →
        D.H.d j k y = D.S j k (D.Ht.d i j φ) := by
      intro y hy
      have : y = ⟨D.H.d i j σ, D.H.mapsTo i j k σ⟩ - ⟨D.S i j φ, D.S_mapsTo i j k φ⟩ :=
        Subtype.ext hy
      rw [this, LinearPMap.map_sub, D.H.d_comp_d, D.anticomm, zero_sub, neg_neg]
    have key2 : ∀ y : (D.Ht.d j k).domain, (y : Wt j) = D.Ht.d i j φ → D.Ht.d j k y = 0 := by
      intro y hy
      have : y = ⟨D.Ht.d i j φ, D.Ht.mapsTo i j k φ⟩ := Subtype.ext hy
      rw [this, D.Ht.d_comp_d]
    refine WithLp.prod_ext' ?_ ?_
    · rw [twistD_apply_fst, WithLp.zero_fst, key1 _ (by simp only [twistD_apply_fst]; rfl)]
      simp only [twistD_apply_snd]
      exact sub_self _
    · rw [twistD_apply_snd, WithLp.zero_snd, key2 _ (by simp only [twistD_apply_snd]; rfl)]


end HilbertData

namespace HilbertData

/-! ### Analytic BGG data on `ComplexShape.up α` from successive connecting maps -/

section OfSucc

variable {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

/-- `f i : Xⁱ → Yⁱ⁺¹` transported along `i + 1 = j`, and `0` otherwise. -/
def succCLM {X Y : α → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
    [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace 𝕜 (Y i)] (f : ∀ i, X i →L[𝕜] Y (i + 1))
    (i j : α) : X i →L[𝕜] Y j :=
  if h : i + 1 = j then h ▸ f i else 0

variable {X Y : α → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
  [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace 𝕜 (Y i)] (f : ∀ i, X i →L[𝕜] Y (i + 1))

@[simp] theorem succCLM_succ (i : α) : succCLM f i (i + 1) = f i := by simp [succCLM]

theorem succCLM_of_ne {i j : α} (h : i + 1 ≠ j) : succCLM f i j = 0 := by simp [succCLM, h]

variable {U Ut : α → Type*} [∀ i, NormedAddCommGroup (U i)] [∀ i, InnerProductSpace 𝕜 (U i)]
  [∀ i, CompleteSpace (U i)] [∀ i, NormedAddCommGroup (Ut i)] [∀ i, InnerProductSpace 𝕜 (Ut i)]
  [∀ i, CompleteSpace (Ut i)]

/-- Analytic BGG data on `ComplexShape.up α` from successive connecting maps `S i : W̃ⁱ → Wⁱ⁺¹`. -/
def ofSucc (H : HilbertComplex 𝕜 (ComplexShape.up α) U)
    (Ht : HilbertComplex 𝕜 (ComplexShape.up α) Ut) (S : ∀ i, Ut i →L[𝕜] U (i + 1))
    (mapsTo : ∀ i (φ : (Ht.d i (i + 1)).domain), S i φ ∈ (H.d (i + 1) (i + 1 + 1)).domain)
    (anticomm : ∀ i (φ : (Ht.d i (i + 1)).domain),
      H.d (i + 1) (i + 1 + 1) ⟨S i φ, mapsTo i φ⟩ = -S (i + 1) (Ht.d i (i + 1) φ)) :
    HilbertData 𝕜 (ComplexShape.up α) U Ut where
  H := H
  Ht := Ht
  S := succCLM S
  shape_S _ _ h := succCLM_of_ne S h
  S_mapsTo i j k φ := by
    by_cases hij : i + 1 = j
    · subst hij
      by_cases hk : i + 1 + 1 = k
      · subst hk
        rw [succCLM_succ]
        exact mapsTo i φ
      · rw [H.domain_eq_top_of_not_rel hk]
        exact Submodule.mem_top
    · rw [succCLM_of_ne S hij]
      exact Submodule.zero_mem _
  anticomm i j k φ := by
    by_cases hij : i + 1 = j
    · subst hij
      by_cases hk : i + 1 + 1 = k
      · subst hk
        conv_rhs => rw [succCLM_succ]
        rw [← anticomm i φ]
        exact congrArg _ (Subtype.ext (show succCLM S i (i + 1) (φ : Ut i) = S i φ by
          rw [succCLM_succ]))
      · rw [H.apply_eq_zero_of_not_rel hk, succCLM_of_ne S hk]
        simp
    · rw [Ht.apply_eq_zero_of_not_rel hij, map_zero, neg_zero]
      have h0 : ∀ y : (H.d j k).domain, (y : U j) = succCLM S i j φ → H.d j k y = 0 :=
        fun y hy => by
          have : y = 0 := Subtype.ext (by rw [hy, succCLM_of_ne S hij]; rfl)
          rw [this, LinearPMap.map_zero]
      exact h0 _ rfl

end OfSucc

end HilbertData

end Feec.BGG
