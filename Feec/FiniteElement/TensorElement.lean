module

public import Feec.FiniteElement.Assembly
public import Feec.FiniteElement.SmoothedProjection

/-!
# Vector-valued finite element spaces `Vₕ ⊗ ℝᵐ`

The bottom row of the BGG discretization of [QuennevilleBelair2015], §5.3 (Table 5.1:
`P₂Λ⁰ ⊗ ℝ³ → P₂⁻Λ¹ ⊗ ℝ³ → P₁Λ² ⊗ ℝ³`) consists of `m`-fold products of scalar-form finite element
spaces. This file builds them on the Hilbert-complex side and on the element side.

**Products of Hilbert complexes.** For a Hilbert complex `H` and a finite index type `α`, the
`α`-fold product `H.pi α` (`Feec.HilbertComplex.pi`) has the spaces `L²`-sums
`PiLp 2 (fun _ : α => W i)` and the componentwise differentials (domain: all components in the
domain). It is again a Hilbert complex (closed graphs, dense domains). A subcomplex `S` of `H`
gives the product subcomplex `S.pi α` (`Subcomplex.pi`), finite-dimensional when `S` is; a
commuting map or a cochain projection of `S` gives the componentwise one of `S.pi α`
(`Subcomplex.CommutingMap.pi`, `Subcomplex.CochainProjection.pi`), **with the same bounds**:
`‖π x‖ ≤ C ‖x‖` (`CochainProjection.norm_pi_le`), the graph bound
(`CochainProjection.isGraphBounded_pi`), and the estimate `‖v - Q v‖ ≤ θ ‖v‖` on `Vₕ` of the
smoothed-projection construction (`CommutingMap.norm_sub_pi_le`), so that the smoothed projection
of the product is a cochain projection with the bounds of the factors
(`CommutingMap.norm_toCochainProjection_pi_le`).

**Finite element spaces `⊗ ℝᵐ`.** For an element family `E` on a conforming mesh `M` of an open
`Ω ⊆ ℝⁿ`, `LocalElement.tensorSubcomplex E M hΩ m` (resp. `tensorSubcomplexMin`, vanishing
boundary DOFs) is the product subcomplex of the `m`-fold product of `HΛ(Ω)` (resp. `H̊Λ(Ω)`), with
spaces `(Vₕᵏ)ᵐ ⊆ L²(Ω; Λᵏ)ᵐ` (`mem_tensorSubcomplex_V`), finite-dimensional. The componentwise
canonical interpolant (`LocalElement.tensorInterp`) maps `(C⁰Λᵏ)ᵐ` to the `m`-fold product of
global spaces, is a projection, and commutes with `d` on `C¹` forms
(`tensorInterp_extDeriv`); componentwise gluing (`LocalElement.tensorGlue`) lands in the product
spaces.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, Table 5.1 (the spaces `P₂Λ⁰ ⊗ V`, `P₂⁻Λ¹ ⊗ V`, `P₁Λ² ⊗ V`)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (subcomplexes, bounded cochain projections), §5.4 (smoothed projections)
* [D. N. Arnold, R. S. Falk, R. Winther, *Mixed finite element methods for linear elasticity with weakly imposed symmetry*][AFW2007]
  (vector-valued finite element spaces)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W) (α : Type*)

/-! ### Componentwise maps on `L²`-sums -/

section PiMap

variable {𝕜' V V' : Type*} [RCLike 𝕜'] [NormedAddCommGroup V] [InnerProductSpace 𝕜' V]
  [NormedAddCommGroup V'] [InnerProductSpace 𝕜' V'] {α}

/-- The componentwise map `(x_a)_a ↦ (f x_a)_a` on `L²`-sums. -/
def piMap (f : V →ₗ[𝕜'] V') : PiLp 2 (fun _ : α => V) →ₗ[𝕜'] PiLp 2 (fun _ : α => V') :=
  (WithLp.linearEquiv 2 𝕜' (α → V')).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun a => f ∘ₗ LinearMap.proj a) ∘ₗ (WithLp.linearEquiv 2 𝕜' (α → V)).toLinearMap

@[simp] theorem piMap_apply (f : V →ₗ[𝕜'] V') (x : PiLp 2 (fun _ : α => V)) (a : α) :
    piMap f x a = f (x a) := rfl

/-- **Componentwise bounds**: `‖f v‖ ≤ C ‖v‖` gives `‖piMap f x‖ ≤ C ‖x‖`. -/
theorem norm_piMap_le [Fintype α] (f : V →ₗ[𝕜'] V') {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, ‖f v‖ ≤ C * ‖v‖)
    (x : PiLp 2 (fun _ : α => V)) : ‖piMap f x‖ ≤ C * ‖x‖ := by
  have h2 : ‖piMap f x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [piMap_apply, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 2
  exact (abs_le_of_sq_le_sq' h2 (mul_nonneg hC0 (norm_nonneg x))).2

end PiMap

/-! ### The product of a Hilbert complex -/

/-- The domain of the componentwise differential: all components in `D(d i j)`. -/
def piDomain (i j : ι) : Submodule 𝕜 (PiLp 2 (fun _ : α => W i)) :=
  (Submodule.pi Set.univ fun _ : α => (H.d i j).domain).comap
    (WithLp.linearEquiv 2 𝕜 (α → W i)).toLinearMap

variable {H α} in
theorem mem_piDomain {i j : ι} {x : PiLp 2 (fun _ : α => W i)} :
    x ∈ H.piDomain α i j ↔ ∀ a, x a ∈ (H.d i j).domain := by
  simp [piDomain, Submodule.mem_pi]

/-- The componentwise differential on the domain. -/
def piDLin (i j : ι) : H.piDomain α i j →ₗ[𝕜] PiLp 2 (fun _ : α => W j) where
  toFun x := WithLp.toLp 2 fun a => H.d i j ⟨x.1 a, mem_piDomain.1 x.2 a⟩
  map_add' x y := by
    ext a
    change H.d i j ⟨(x.1 + y.1) a, _⟩ = H.d i j ⟨x.1 a, _⟩ + H.d i j ⟨y.1 a, _⟩
    rw [← LinearPMap.map_add]
    rfl
  map_smul' r x := by
    ext a
    change H.d i j ⟨(r • x.1) a, _⟩ = r • H.d i j ⟨x.1 a, _⟩
    rw [← LinearPMap.map_smul]
    rfl

/-- The componentwise differential `(x_a)_a ↦ (d x_a)_a` of the product complex. -/
def piD (i j : ι) : PiLp 2 (fun _ : α => W i) →ₗ.[𝕜] PiLp 2 (fun _ : α => W j) :=
  ⟨H.piDomain α i j, H.piDLin α i j⟩

variable {H α}

theorem piD_domain (i j : ι) : (H.piD α i j).domain = H.piDomain α i j := rfl

@[simp] theorem piD_apply {i j : ι} (x : (H.piD α i j).domain) (a : α) :
    H.piD α i j x a = H.d i j ⟨(x : PiLp 2 (fun _ : α => W i)) a, mem_piDomain.1 x.2 a⟩ := rfl

theorem mem_graph_piD_iff {i j : ι} {p : PiLp 2 (fun _ : α => W i) × PiLp 2 (fun _ : α => W j)} :
    p ∈ (H.piD α i j).graph ↔ ∀ a, (p.1 a, p.2 a) ∈ (H.d i j).graph := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x, hx1, hx2⟩ a
    rw [LinearPMap.mem_graph_iff]
    have hxa : p.1 a ∈ (H.d i j).domain := by rw [← hx1]; exact mem_piDomain.1 x.2 a
    refine ⟨⟨p.1 a, hxa⟩, rfl, ?_⟩
    rw [← hx2, piD_apply]
    congr 2
    rw [hx1]
  · intro h
    choose y hy1 hy2 using fun a => (LinearPMap.mem_graph_iff _).1 (h a)
    have hdom : p.1 ∈ (H.piD α i j).domain := mem_piDomain.2 fun a => by
      have := (y a).2
      rwa [hy1 a] at this
    refine ⟨⟨p.1, hdom⟩, rfl, ?_⟩
    ext a
    refine Eq.trans ?_ (hy2 a)
    exact congrArg (H.d i j) (Subtype.ext (hy1 a).symm)

theorem piD_isClosed {i j : ι} : (H.piD α i j).IsClosed := by
  have : (SetLike.coe (H.piD α i j).graph :
      Set (PiLp 2 (fun _ : α => W i) × PiLp 2 (fun _ : α => W j))) =
      ⋂ a, (fun p : PiLp 2 (fun _ : α => W i) × PiLp 2 (fun _ : α => W j) => (p.1 a, p.2 a)) ⁻¹'
        (SetLike.coe (H.d i j).graph : Set (W i × W j)) := by
    ext p; simp only [SetLike.mem_coe, mem_graph_piD_iff, Set.mem_iInter, Set.mem_preimage]
  change _root_.IsClosed (SetLike.coe (H.piD α i j).graph)
  rw [this]
  refine isClosed_iInter fun a => (H.closed i j).preimage ?_
  exact ((PiLp.continuous_apply 2 _ a).comp continuous_fst).prodMk
    ((PiLp.continuous_apply 2 _ a).comp continuous_snd)

theorem piD_dense {i j : ι} : Dense ((H.piD α i j).domain : Set (PiLp 2 (fun _ : α => W i))) := by
  have : ((H.piD α i j).domain : Set (PiLp 2 (fun _ : α => W i))) =
      (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : α => W i)) ⁻¹'
        Set.univ.pi fun _ : α => ((H.d i j).domain : Set (W i)) := by
    ext x; simp [piD_domain, mem_piDomain]
  rw [this]
  exact (dense_pi Set.univ fun a _ => H.dense i j).preimage
    (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : α => W i)).toHomeomorph.isOpenMap

variable (H α) [Fintype α]

/-- **The `α`-fold product of a Hilbert complex**: spaces `PiLp 2 (fun _ : α => W i)`,
componentwise differentials. -/
def pi : HilbertComplex 𝕜 c fun i => PiLp 2 (fun _ : α => W i) where
  d := H.piD α
  shape i j h := by
    refine LinearPMap.ext ?_ fun x y hxy => ?_
    · ext x
      simp only [piD_domain, mem_piDomain, H.domain_eq_top_of_not_rel h, Submodule.mem_top,
        implies_true, LinearPMap.zero_domain]
    · ext a
      rw [piD_apply, H.apply_eq_zero_of_not_rel h]
      simp
  dense _ _ := piD_dense
  closed _ _ := piD_isClosed
  mapsTo i j k x := mem_piDomain.2 fun a => by
    rw [piD_apply]; exact H.mapsTo i j k _
  d_comp_d i j k x := by
    ext a
    rw [piD_apply]
    have : (⟨(H.piD α i j x : PiLp 2 (fun _ : α => W j)) a, _⟩ : (H.d j k).domain) =
        ⟨_, H.mapsTo i j k ⟨(x : PiLp 2 (fun _ : α => W i)) a, mem_piDomain.1 x.2 a⟩⟩ := rfl
    rw [this, H.d_comp_d]
    rfl

variable {H α}

@[simp] theorem pi_d (i j : ι) : (H.pi α).d i j = H.piD α i j := rfl

theorem mem_pi_domain {i j : ι} {x : PiLp 2 (fun _ : α => W i)} :
    x ∈ ((H.pi α).d i j).domain ↔ ∀ a, x a ∈ (H.d i j).domain := mem_piDomain

@[simp] theorem pi_d_apply {i j : ι} (x : ((H.pi α).d i j).domain) (a : α) :
    (H.pi α).d i j x a = H.d i j ⟨(x : PiLp 2 (fun _ : α => W i)) a, mem_piDomain.1 x.2 a⟩ :=
  rfl

/-- The squared graph norm of the product is the sum of the squared graph norms. -/
theorem norm_sq_add_norm_sq_pi_d {i j : ι} (x : ((H.pi α).d i j).domain) :
    ‖(x : PiLp 2 (fun _ : α => W i))‖ ^ 2 + ‖(H.pi α).d i j x‖ ^ 2 =
      ∑ a, (‖(x : PiLp 2 (fun _ : α => W i)) a‖ ^ 2 +
        ‖H.d i j ⟨(x : PiLp 2 (fun _ : α => W i)) a, mem_piDomain.1 x.2 a⟩‖ ^ 2) := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, ← Finset.sum_add_distrib]
  rfl

/-! ### Product subcomplexes -/

namespace Subcomplex

variable (S : H.Subcomplex) (α)

/-- **The product subcomplex** `(Vₕ)^α` of `H.pi α`. -/
def pi : (H.pi α).Subcomplex where
  V i := (Submodule.pi Set.univ fun _ : α => S.V i).comap
    (WithLp.linearEquiv 2 𝕜 (α → W i)).toLinearMap
  le_domain i j x hx := mem_piDomain.2 fun a => S.le_domain i j (by
    simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies] at hx
    exact hx a)
  mapsTo i j x hx := by
    simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    intro a
    exact S.mapsTo i j _ (hx a)

variable {S α}

theorem mem_pi_V {i : ι} {x : PiLp 2 (fun _ : α => W i)} :
    x ∈ (S.pi α).V i ↔ ∀ a, x a ∈ S.V i := by
  simp [pi, Submodule.mem_pi]

instance finiteDimensional_pi_V [∀ i, FiniteDimensional 𝕜 (S.V i)] (i : ι) :
    FiniteDimensional 𝕜 ((S.pi α).V i) := by
  let f : (S.pi α).V i →ₗ[𝕜] (α → S.V i) :=
    { toFun := fun x a => ⟨(x : PiLp 2 (fun _ : α => W i)) a, mem_pi_V.1 x.2 a⟩
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  refine Module.Finite.of_injective f fun x y hxy => Subtype.ext ?_
  ext a
  exact congrArg Subtype.val (congrFun hxy a)

/-! ### Commuting maps and cochain projections of products -/

namespace CommutingMap

variable (Q : S.CommutingMap) (α)

/-- The componentwise commuting map of the product subcomplex. -/
def pi : (S.pi α).CommutingMap where
  Q i := piMap (Q.Q i)
  mem i x := mem_pi_V.2 fun a => Q.mem i _
  comm i j x := by
    ext a
    rw [pi_d_apply]
    exact Q.comm i j ⟨(x : PiLp 2 (fun _ : α => W i)) a, mem_piDomain.1 x.2 a⟩

variable {Q α}

@[simp] theorem pi_Q_apply (i : ι) (x : PiLp 2 (fun _ : α => W i)) (a : α) :
    (Q.pi α).Q i x a = Q.Q i (x a) := rfl

/-- `‖v - Q v‖ ≤ θ ‖v‖` on `Vₕ` passes to the product. -/
theorem norm_sub_pi_le {θ : ℝ} (hθ : 0 ≤ θ) (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) :
    ∀ i, ∀ v ∈ (S.pi α).V i, ‖v - (Q.pi α).Q i v‖ ≤ θ * ‖v‖ := by
  intro i v hv
  have h2 : ‖v - (Q.pi α).Q i v‖ ^ 2 ≤ (θ * ‖v‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hQ i _ (mem_pi_V.1 hv a)) 2
  exact (abs_le_of_sq_le_sq' h2 (mul_nonneg hθ (norm_nonneg v))).2

/-- `‖Q x‖ ≤ C ‖x‖` passes to the product. -/
theorem norm_pi_Q_le {i : ι} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖Q.Q i x‖ ≤ C * ‖x‖)
    (x : PiLp 2 (fun _ : α => W i)) : ‖(Q.pi α).Q i x‖ ≤ C * ‖x‖ :=
  norm_piMap_le (Q.Q i) hC0 hC x

/-- **The smoothed projection of the product** (`π = J⁻¹ Q` for the componentwise `Q`) is a
cochain projection bounded by `(1 - θ)⁻¹ C`, the bound of the factors. -/
theorem norm_toCochainProjection_pi_le [∀ i, FiniteDimensional 𝕜 (S.V i)] {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) {i : ι} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖Q.Q i x‖ ≤ C * ‖x‖) (x : PiLp 2 (fun _ : α => W i)) :
    ‖((Q.pi α).toCochainProjection hθ (norm_sub_pi_le hθ0 hQ)).π i x‖ ≤ (1 - θ)⁻¹ * C * ‖x‖ :=
  (Q.pi α).norm_toCochainProjection_le hθ _ (norm_pi_Q_le hC0 hC) x

/-- The graph bound of the smoothed projection of the product, from the `W`-bounds of the
factors. -/
theorem isGraphBounded_toCochainProjection_pi [∀ i, FiniteDimensional 𝕜 (S.V i)] {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < 1) (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) {i j : ι}
    {C : ℝ} (hC0 : 0 ≤ C) (hi : ∀ x, ‖Q.Q i x‖ ≤ C * ‖x‖) (hj : ∀ x, ‖Q.Q j x‖ ≤ C * ‖x‖) :
    ((Q.pi α).toCochainProjection hθ (norm_sub_pi_le hθ0 hQ)).IsGraphBounded i j
      ((1 - θ)⁻¹ * C) :=
  (Q.pi α).isGraphBounded_toCochainProjection_of_norm_le hθ _ (norm_pi_Q_le hC0 hi)
    (norm_pi_Q_le hC0 hj)

end CommutingMap

namespace CochainProjection

variable (P : S.CochainProjection) (α)

/-- **The product of a cochain projection** is a cochain projection of the product
subcomplex. -/
def pi : (S.pi α).CochainProjection where
  π i := piMap (P.π i)
  mem i x := mem_pi_V.2 fun a => P.mem i _
  proj i x hx := by
    ext a
    exact P.proj i _ (mem_pi_V.1 hx a)
  comm i j x := by
    ext a
    rw [pi_d_apply]
    exact P.comm i j ⟨(x : PiLp 2 (fun _ : α => W i)) a, mem_piDomain.1 x.2 a⟩

variable {P α}

@[simp] theorem pi_π_apply (i : ι) (x : PiLp 2 (fun _ : α => W i)) (a : α) :
    (P.pi α).π i x a = P.π i (x a) := rfl

/-- **Same `W`-bound**: `‖π x‖ ≤ C ‖x‖` for the factors gives it for the product. -/
theorem norm_pi_le {i : ι} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖)
    (x : PiLp 2 (fun _ : α => W i)) : ‖(P.pi α).π i x‖ ≤ C * ‖x‖ :=
  norm_piMap_le (P.π i) hC0 hC x

/-- **Same graph bound** for the product. -/
theorem isGraphBounded_pi {i j : ι} {C : ℝ} (hP : P.IsGraphBounded i j C) :
    (P.pi α).IsGraphBounded i j C := by
  intro x
  have e1 := norm_sq_add_norm_sq_pi_d (H := H) (α := α) x
  have e2 : ‖(P.pi α).π i x‖ ^ 2 +
      ‖(H.pi α).d i j ⟨(P.pi α).π i x, (S.pi α).le_domain i j ((P.pi α).mem i x)⟩‖ ^ 2 =
      ∑ a, (‖P.π i ((x : PiLp 2 (fun _ : α => W i)) a)‖ ^ 2 +
        ‖H.d i j ⟨P.π i ((x : PiLp 2 (fun _ : α => W i)) a),
          S.le_domain i j (P.mem i _)⟩‖ ^ 2) :=
    norm_sq_add_norm_sq_pi_d (H := H) (α := α)
      ⟨(P.pi α).π i x, (S.pi α).le_domain i j ((P.pi α).mem i x)⟩
  rw [e2, e1, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ =>
    hP ⟨(x : PiLp 2 (fun _ : α => W i)) a, mem_piDomain.1 x.2 a⟩

end CochainProjection

end Subcomplex

end Feec.HilbertComplex

/-! ### Finite element spaces `⊗ ℝᵐ` -/

namespace Feec.FiniteElement

open Feec.Domain Feec.Mesh Feec.HilbertComplex

variable {n : ℕ} (E : LocalElement n) (M : SimplicialMesh n)

namespace LocalElement

/-- **The finite element subcomplex `Vₕ ⊗ ℝᵐ`** of the `m`-fold product of `HΛ(Ω)`: the spaces
`(Vₕᵏ)ᵐ ⊆ L²(Ω; Λᵏ)ᵐ`. -/
def tensorSubcomplex [NeZero n] (hΩ : IsOpen M.domain) (m : ℕ) :
    (((deRham ℝ n).maximalComplex hΩ).pi (Fin m)).Subcomplex :=
  (E.subcomplex M hΩ).pi (Fin m)

/-- **The finite element subcomplex `V̊ₕ ⊗ ℝᵐ`** (vanishing boundary DOFs) of the `m`-fold
product of `H̊Λ(Ω)`. -/
def tensorSubcomplexMin [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    (m : ℕ) : (((deRham ℝ n).minimalComplex hΩ).pi (Fin m)).Subcomplex :=
  (E.subcomplexMin M hΩ x₀ hstar).pi (Fin m)

theorem mem_tensorSubcomplex_V [NeZero n] (hΩ : IsOpen M.domain) {m : ℕ} {k : ℤ}
    {x : PiLp 2 (fun _ : Fin m => L2F ℝ M.domain (formIdx n k))} :
    x ∈ (E.tensorSubcomplex M hΩ m).V k ↔ ∀ a, x a ∈ E.V M k :=
  Subcomplex.mem_pi_V

theorem mem_tensorSubcomplexMin_V [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    {m : ℕ} {k : ℤ} {x : PiLp 2 (fun _ : Fin m => L2F ℝ M.domain (formIdx n k))} :
    x ∈ (E.tensorSubcomplexMin M hΩ x₀ hstar m).V k ↔ ∀ a, x a ∈ E.V₀ M k :=
  Subcomplex.mem_pi_V

instance [NeZero n] (hΩ : IsOpen M.domain) (m : ℕ) (k : ℤ) :
    FiniteDimensional ℝ ((E.tensorSubcomplex M hΩ m).V k) :=
  haveI : ∀ i, FiniteDimensional ℝ ((E.subcomplex M hΩ).V i) := fun _ => inferInstance
  Subcomplex.finiteDimensional_pi_V (S := E.subcomplex M hΩ) k

instance [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    (m : ℕ) (k : ℤ) : FiniteDimensional ℝ ((E.tensorSubcomplexMin M hΩ x₀ hstar m).V k) :=
  haveI : ∀ i, FiniteDimensional ℝ ((E.subcomplexMin M hΩ x₀ hstar).V i) :=
    fun _ => inferInstance
  Subcomplex.finiteDimensional_pi_V (S := E.subcomplexMin M hΩ x₀ hstar) k

/-- **Componentwise gluing** `(Λ_hᵏ)ᵐ → L²(Ω; Λᵏ)ᵐ`. -/
def tensorGlue (m : ℕ) (k : ℤ) :
    (Fin m → E.Piecewise M k.toNat) →ₗ[ℝ] PiLp 2 (fun _ : Fin m => L2F ℝ M.domain (formIdx n k)) :=
  (WithLp.linearEquiv 2 ℝ (Fin m → L2F ℝ M.domain (formIdx n k))).symm.toLinearMap ∘ₗ
    LinearMap.pi fun a => E.glue M k ∘ₗ LinearMap.proj a

@[simp] theorem tensorGlue_apply {m : ℕ} {k : ℤ} (u : Fin m → E.Piecewise M k.toNat) (a : Fin m) :
    E.tensorGlue M m k u a = E.glue M k (u a) := rfl

theorem tensorGlue_mem [NeZero n] (hΩ : IsOpen M.domain) {m : ℕ} {k : ℤ}
    {u : Fin m → E.Piecewise M k.toNat} (hu : ∀ a, u a ∈ E.globalSpace M k.toNat) :
    E.tensorGlue M m k u ∈ (E.tensorSubcomplex M hΩ m).V k :=
  (E.mem_tensorSubcomplex_V M hΩ).2 fun a => ⟨⟨u a, hu a⟩, rfl⟩

theorem tensorGlue_mem_min [NeZero n] (hΩ : IsOpen M.domain) (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    {m : ℕ} {k : ℤ} {u : Fin m → E.Piecewise M k.toNat}
    (hu : ∀ a, u a ∈ E.globalSpace₀ M k.toNat) :
    E.tensorGlue M m k u ∈ (E.tensorSubcomplexMin M hΩ x₀ hstar m).V k :=
  (E.mem_tensorSubcomplexMin_V M hΩ x₀ hstar).2 fun a => ⟨⟨u a, hu a⟩, rfl⟩

/-- **The componentwise canonical interpolant** `(C⁰Λᵏ)ᵐ → (Λ_hᵏ)ᵐ`. -/
def tensorInterp (m k : ℕ) : (Fin m → contForms n) →ₗ[ℝ] (Fin m → E.globalSpace M k) :=
  LinearMap.pi fun a => E.globalInterp M k ∘ₗ LinearMap.proj a

@[simp] theorem tensorInterp_apply {m k : ℕ} (w : Fin m → contForms n) (a : Fin m) :
    E.tensorInterp M m k w a = E.globalInterp M k (w a) := rfl

/-- The componentwise interpolant is a projection: componentwise continuous forms equal to the
discrete fields on every closed element are interpolated to them. -/
theorem tensorInterp_eq_of_eqOn {m k : ℕ} (u : Fin m → E.globalSpace M k)
    (w : Fin m → contForms n)
    (hw : ∀ a, ∀ T : M.simplices, ∀ x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (w a : FormField n) x = ((((u a : E.globalSpace M k) : E.Piecewise M k) T : E.space T k) :
        FormField n) x) :
    E.tensorInterp M m k w = u :=
  funext fun a => E.globalInterp_eq_of_eqOn M k (u a) (w a) (hw a)

/-- **The componentwise interpolant commutes with `d`** on `C¹` forms. -/
theorem tensorInterp_extDeriv {m k : ℕ} (w : Fin m → c1Forms n) :
    E.tensorInterp M m (k + 1) (fun a => extDerivC1 (w a)) =
      fun a => E.dGlobal M k (E.tensorInterp M m k
        (fun b => Submodule.inclusion c1Forms_le_contForms (w b)) a) :=
  funext fun a => E.globalInterp_extDeriv M k (w a)

end LocalElement

end Feec.FiniteElement
