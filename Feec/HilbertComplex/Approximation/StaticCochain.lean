module

public import Feec.HilbertComplex.Approximation.DiscreteCohomology
public import Feec.HilbertComplex.Approximation.StaticCrime

/-!
# The static theory with cochain reading maps

The static FEEC theorem with variational crimes for cochain reading maps `iₕ` with cochain
projections `πₕ`, `πₕ iₕ = 1`, uniformly bounded in the graph norm ([HolstStern2012], §3).

## Main results

* `ApproxComplexCrime.Family.IsCochain.isPoincare`: the uniform discrete Poincaré inequality.
* `ApproxComplexCrime.Family.IsCochain.staticError_le`: the error estimate.
* `ApproxComplexCrime.Family.IsCochain.staticError_le_of_approx`: the static rate.
* `ApproxComplexCrime.Family.IsCochain.tendsto_staticError`: convergence for every datum.
* `ApproxComplexCrime.Family.IsCochain.eventually_bijective_cohomologyMap`: cohomology isomorphisms.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem le_add_of_sq_eq {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (e : x ^ 2 = a ^ 2 + b ^ 2) : x ≤ a + b := by
  nlinarith [mul_nonneg ha hb]

private theorem le_add_add_of_sq_eq {x a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : x ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) : x ≤ a + b + c := by
  nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]

private theorem norm_sub_starProjection_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x : E) :
    ‖x - K.starProjection x‖ ≤ ‖x‖ := by
  rw [show x - K.starProjection x = Kᗮ.starProjection x by
    rw [Submodule.starProjection_orthogonal']; rfl]
  exact Kᗮ.norm_starProjection_apply_le x

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι}
  {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)]

section Cycles

variable (H : HilbertComplex 𝕜 c W)

theorem mem_totalD_domain_of_mem_cycles {x : PiLp 2 W} (hx : x ∈ H.total.cycles ()) :
    x ∈ H.totalD.domain := by
  obtain ⟨y, rfl, -⟩ := LinearPMap.mem_ker_iff.1 hx
  exact y.2

theorem totalD_mem_cycles (z : H.totalD.domain) : H.totalD z ∈ H.total.cycles () :=
  H.total.boundaries_le_cycles () ⟨z, rfl⟩

omit [Fintype ι] in
theorem starProjection_cycles_eq_of_mem_orthogonal (E : HilbertComplex 𝕜 c W) (i : ι)
    {u : W i} (hu : u ∈ (E.harmonic i)ᗮ) :
    (E.cycles i).starProjection u = (E.boundaries i).topologicalClosure.starProjection u := by
  set B := (E.boundaries i).topologicalClosure
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (E.closure_boundaries_le_cycles i (B.starProjection_apply_mem u)) fun w hw => ?_
  have hq : w - B.starProjection w ∈ E.harmonic i := E.mem_harmonic_iff.2
    ⟨(E.cycles i).sub_mem hw (E.closure_boundaries_le_cycles i (B.starProjection_apply_mem w)),
      by rw [← E.orthogonal_closure_boundaries]; exact B.sub_starProjection_mem_orthogonal w⟩
  have h1 : ⟪u - B.starProjection u, B.starProjection w⟫_𝕜 = 0 :=
    Submodule.inner_left_of_mem_orthogonal (B.starProjection_apply_mem w)
      (B.sub_starProjection_mem_orthogonal u)
  have h2 : ⟪u, w - B.starProjection w⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal hq hu
  have h3 : ⟪B.starProjection u, w - B.starProjection w⟫_𝕜 = 0 :=
    (E.isOrtho_closure_boundaries_harmonic i).inner_eq (B.starProjection_apply_mem u) hq
  calc ⟪u - B.starProjection u, w⟫_𝕜 =
        ⟪u - B.starProjection u, B.starProjection w⟫_𝕜 +
          (⟪u, w - B.starProjection w⟫_𝕜 - ⟪B.starProjection u, w - B.starProjection w⟫_𝕜) := by
        rw [← inner_sub_left, ← inner_add_right, add_sub_cancel]
    _ = 0 := by rw [h1, h2, h3, sub_zero, add_zero]

end Cycles

namespace ApproxComplexCrime.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplexCrime.Family.{u} H κ)

/-- The reading maps are cochain maps: `iₕ Xₕ ⊆ D(𝐝)`, `𝐝 iₕ = iₕ 𝐝ₕ`. [HolstStern2012], §3.1 -/
structure IsCochain : Prop where
  incl_mem : ∀ h v, S.incl h v ∈ H.totalD.domain
  totalD_incl : ∀ h v, H.totalD ⟨S.incl h v, incl_mem h v⟩ = S.incl h (S.D h v)

/-- Cochain projections `πₕ`, `πₕ iₕ = 1`, `πₕ 𝐝 = 𝐝ₕ πₕ`, bounded by `C_π` in the graph norm. -/
structure CochainProj (Cπ : ℝ) where
  /-- the projections -/
  π : ∀ h, PiLp 2 W →ₗ[𝕜] S.X h
  π_incl : ∀ h v, π h (S.incl h v) = v
  nonneg : 0 ≤ Cπ
  norm_π_le : ∀ h x (hx : x ∈ H.totalD.domain), ‖π h x‖ ≤ Cπ * (‖x‖ + ‖H.totalD ⟨x, hx⟩‖)
  π_totalD : ∀ h (z : H.totalD.domain), π h (H.totalD z) = S.D h (π h z)

variable {S}

namespace CochainProj

variable {Cπ : ℝ}

/-- Cochain projections bounded by `C_π` in `W` are bounded by `C_π` in the graph norm. -/
def ofNormLe (π : ∀ h, PiLp 2 W →L[𝕜] S.X h) (π_incl : ∀ h v, π h (S.incl h v) = v)
    (hCπ : 0 ≤ Cπ) (norm_π_le : ∀ h, ‖π h‖ ≤ Cπ)
    (π_totalD : ∀ h (z : H.totalD.domain), π h (H.totalD z) = S.D h (π h z)) :
    S.CochainProj Cπ where
  π h := π h
  π_incl := π_incl
  nonneg := hCπ
  norm_π_le h x _ := ((π h).le_opNorm x).trans (mul_le_mul (norm_π_le h)
    (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg _) hCπ)
  π_totalD := π_totalD

variable (P : S.CochainProj Cπ)

theorem norm_π_apply_le_of_mem_cycles (h : κ) {x : PiLp 2 W} (hx : x ∈ H.total.cycles ()) :
    ‖P.π h x‖ ≤ Cπ * ‖x‖ := by
  obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hx
  have h1 : ‖P.π h y‖ ≤ Cπ * (‖(y : PiLp 2 W)‖ + ‖H.totalD y‖) := P.norm_π_le h y y.2
  rwa [show H.totalD y = 0 from hy, norm_zero, add_zero] at h1

theorem lipschitzOnWith_π (h : κ) :
    LipschitzOnWith (Real.toNNReal Cπ) (P.π h) (H.total.cycles () : Set (PiLp 2 W)) :=
  LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
    rw [dist_eq_norm, dist_eq_norm, ← _root_.map_sub, Real.coe_toNNReal _ P.nonneg]
    exact P.norm_π_apply_le_of_mem_cycles h (Submodule.sub_mem _ hx hy)

theorem mem_range_of_mem_closure (h : κ) {b : PiLp 2 W}
    (hb : b ∈ (H.total.boundaries ()).topologicalClosure) :
    P.π h b ∈ LinearMap.range (S.D h : S.X h →ₗ[𝕜] S.X h) := by
  have hA : IsClosed ((H.total.cycles () : Set (PiLp 2 W)) ∩
      P.π h ⁻¹' (LinearMap.range (S.D h : S.X h →ₗ[𝕜] S.X h) : Set (S.X h))) :=
    (P.lipschitzOnWith_π h).continuousOn.preimage_isClosed_of_isClosed
      (H.total.isClosed_cycles ()) (Submodule.closed_of_finiteDimensional _)
  have hsub : (H.total.boundaries () : Set (PiLp 2 W)) ⊆ (H.total.cycles () : Set (PiLp 2 W)) ∩
      P.π h ⁻¹' (LinearMap.range (S.D h : S.X h →ₗ[𝕜] S.X h) : Set (S.X h)) := by
    rintro _ ⟨z, rfl⟩
    exact Set.mem_inter (H.totalD_mem_cycles z)
      (Set.mem_preimage.2 ⟨P.π h z, (P.π_totalD h z).symm⟩)
  exact (closure_minimal hsub hA (by rwa [← Submodule.topologicalClosure_coe])).2

/-- The approximation error of `iₕ πₕ` at `σ`, `𝐝 σ`, `u`, `𝐝 u`, `p`. -/
def projError (h : κ) (X : H.total.MixedSpace () ()) : ℝ :=
  ‖H.total.mixedI0 () () X - S.incl h (P.π h (H.total.mixedI0 () () X))‖ +
    ‖H.total.mixedD0 () () X - S.incl h (P.π h (H.total.mixedD0 () () X))‖ +
    ‖H.total.mixedI1 () () X - S.incl h (P.π h (H.total.mixedI1 () () X))‖ +
    ‖H.total.mixedD1 () () () X - S.incl h (P.π h (H.total.mixedD1 () () () X))‖ +
    ‖H.total.mixedI2 () () X - S.incl h (P.π h (H.total.mixedI2 () () X))‖

end CochainProj

variable (S) in
/-- The constant of the static rate with cochain reading maps. -/
def cochainRateConst (Cπ cP : ℝ) : ℝ :=
  (5 * (1 + S.boundConst ^ 2) * (1 + S.boundConst * Cπ) + S.boundConst * Cπ) +
    240 * S.boundConst * cP ^ 2 * (51 * Cπ +
      S.boundConst * (5 * (1 + S.boundConst ^ 2) * (1 + S.boundConst * Cπ) + S.boundConst * Cπ) +
      S.boundConst * (1 + S.boundConst * Cπ))

theorem cochainRateConst_nonneg {Cπ : ℝ} (hCπ : 0 ≤ Cπ) (cP : ℝ) :
    0 ≤ S.cochainRateConst Cπ cP := by
  have := S.boundConst_nonneg
  unfold cochainRateConst
  positivity

namespace IsCochain

variable (hi : S.IsCochain)
include hi

theorem cochainDefect_eq_zero (h : κ) (y : H.wave.domain) : S.cochainDefect h y = 0 :=
  S.cochainDefect_eq_zero h (hi.incl_mem h) (hi.totalD_incl h) y

theorem incl_mem_cycles (h : κ) {v : S.X h} (hv : S.D h v = 0) :
    S.incl h v ∈ H.total.cycles () :=
  show S.incl h v ∈ H.totalD.ker from
    LinearPMap.mem_ker_iff.2 ⟨⟨S.incl h v, hi.incl_mem h v⟩, rfl, by
      rw [hi.totalD_incl, hv, _root_.map_zero]⟩

theorem incl_mem_closure (h : κ) {β : S.X h}
    (hβ : β ∈ ((S.cpx h).boundaries ()).topologicalClosure) :
    S.incl h β ∈ (H.total.boundaries ()).topologicalClosure := by
  have hle : (S.cpx h).boundaries () ≤ (H.total.boundaries ()).topologicalClosure.comap
      (S.incl h : S.X h →ₗ[𝕜] PiLp 2 W) := by
    rintro _ ⟨w, rfl⟩
    exact Submodule.le_topologicalClosure _ ⟨⟨S.incl h w, hi.incl_mem h w⟩, hi.totalD_incl h w⟩
  exact Submodule.topologicalClosure_minimal _ hle
    ((H.total.boundaries ()).isClosed_topologicalClosure.preimage (S.incl h).continuous) hβ

/-- **The uniform discrete Poincaré inequality**: if `𝐝` has the Poincaré constant `c₀`, then
`‖v‖ ≤ (c₀ + 1) C_π C ‖𝐝ₕ v‖` on `(ker 𝐝ₕ)ᗮ`, `C` the bound of the reading maps. -/
theorem isPoincare {Cπ : ℝ} (P : S.CochainProj Cπ) {c₀ : ℝ}
    (hc : ∀ z : H.totalD.domain, (z : PiLp 2 W) ∈ H.totalD.kerᗮ →
      ‖(z : PiLp 2 W)‖ ≤ c₀ * ‖H.totalD z‖) :
    S.IsPoincare ((c₀ + 1) * Cπ * S.boundConst) :=
  (S.isPoincare_of_norm_proj_le (M := Cπ * (c₀ + 1)) hi.incl_mem
    (fun h v => by rw [hi.totalD_incl]; exact S.norm_incl_apply_le h _) P.π P.π_incl
    (fun h z hz => by
      have h1 : ‖P.π h z‖ ≤ Cπ * (‖(z : PiLp 2 W)‖ + ‖H.totalD z‖) := P.norm_π_le h z z.2
      nlinarith [hc z hz, P.nonneg])
    fun h z hz => by rw [← P.π_totalD, hz, _root_.map_zero]).mono (le_of_eq (by ring))

theorem norm_inner_incl_harmonic_le_of_gap {Cπ : ℝ} (P : S.CochainProj Cπ) (h : κ) {δ : ℝ}
    (hδ : ∀ q ∈ (S.cpx h).harmonic (),
      ‖S.incl h q - (H.total.harmonic ()).starProjection (S.incl h q)‖ ≤ δ * ‖q‖)
    {u : PiLp 2 W} (hu : u ∈ (H.total.harmonic ())ᗮ) {q : S.X h}
    (hq : q ∈ (S.cpx h).harmonic ()) :
    ‖⟪S.incl h q, u⟫_𝕜‖ ≤ (δ * ‖(H.total.cycles ()).starProjection u -
        S.incl h (P.π h ((H.total.cycles ()).starProjection u))‖ +
      Cπ * S.graphDefect h * ‖u‖) * ‖q‖ := by
  set K := H.total.cycles ()
  set b := K.starProjection u
  obtain ⟨hDq, hDsq⟩ := (mem_diffComplex_harmonic (S.D h) (S.D_D h)).1 hq
  have hiq : S.incl h q ∈ K := hi.incl_mem_cycles h hDq
  have e1 : ⟪S.incl h q, u⟫_𝕜 = ⟪S.incl h q, b⟫_𝕜 := by
    have := Submodule.inner_right_of_mem_orthogonal hiq (K.sub_starProjection_mem_orthogonal u)
    rwa [inner_sub_right, sub_eq_zero] at this
  have hbo : b ∈ (H.total.harmonic ())ᗮ := by
    refine (Submodule.mem_orthogonal _ _).2 fun r hr => ?_
    calc ⟪r, b⟫_𝕜 = ⟪K.starProjection r, u⟫_𝕜 :=
          (Submodule.inner_starProjection_left_eq_right _ _ _).symm
      _ = ⟪r, u⟫_𝕜 := by
          rw [Submodule.starProjection_eq_self_iff.2 (H.total.harmonic_le_cycles () hr)]
      _ = 0 := Submodule.inner_right_of_mem_orthogonal hr hu
  have hbcl : b ∈ (H.total.boundaries ()).topologicalClosure :=
    H.total.mem_closure_boundaries_of_mem_cycles (K.starProjection_apply_mem u) hbo
  obtain ⟨w, hw⟩ := P.mem_range_of_mem_closure h hbcl
  have hq0 : ⟪q, P.π h b⟫_𝕜 = 0 := by
    rw [← hw]
    change ⟪q, S.D h w⟫_𝕜 = 0
    rw [← ContinuousLinearMap.adjoint_inner_left, hDsq, inner_zero_left]
  have e2 : ⟪S.incl h q, S.incl h (P.π h b)⟫_𝕜 = -⟪(1 - S.J h) q, P.π h b⟫_𝕜 := by
    rw [← S.inner_J, _root_.sub_apply, one_apply_eq_self, inner_sub_left,
      hq0, zero_sub, neg_neg]
  have e3 : ⟪S.incl h q, u⟫_𝕜 =
      ⟪S.incl h q, b - S.incl h (P.π h b)⟫_𝕜 - ⟪(1 - S.J h) q, P.π h b⟫_𝕜 := by
    rw [e1, inner_sub_right, e2, sub_neg_eq_add, add_sub_cancel_right]
  have hβ : b - S.incl h (P.π h b) ∈ (H.total.boundaries ()).topologicalClosure :=
    Submodule.sub_mem _ hbcl (hi.incl_mem_closure h
      (Submodule.le_topologicalClosure _ ⟨⟨w, Submodule.mem_top⟩, hw⟩))
  have e4 : ⟪S.incl h q, b - S.incl h (P.π h b)⟫_𝕜 =
      ⟪S.incl h q - (H.total.harmonic ()).starProjection (S.incl h q),
        b - S.incl h (P.π h b)⟫_𝕜 := by
    rw [inner_sub_left, inner_eq_zero_symm.1
      ((H.total.isOrtho_closure_boundaries_harmonic ()).inner_eq hβ
        ((H.total.harmonic ()).starProjection_apply_mem _)), sub_zero]
  rw [e3, e4]
  have hCπ := P.nonneg
  have t1 : ‖⟪S.incl h q - (H.total.harmonic ()).starProjection (S.incl h q),
      b - S.incl h (P.π h b)⟫_𝕜‖ ≤ δ * ‖q‖ * ‖b - S.incl h (P.π h b)‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hδ q hq) (norm_nonneg _))
  have t2 : ‖⟪(1 - S.J h) q, P.π h b⟫_𝕜‖ ≤ S.graphDefect h * ‖q‖ * (Cπ * ‖u‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (S.norm_one_sub_J_apply_le_of_D_eq_zero h hDq)
      ((P.norm_π_apply_le_of_mem_cycles h (K.starProjection_apply_mem u)).trans
        (mul_le_mul_of_nonneg_left (K.norm_starProjection_apply_le u) hCπ))
      (norm_nonneg _) (mul_nonneg (S.graphDefect_nonneg h) (norm_nonneg _)))
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add t1 t2
    _ = _ := by ring

theorem norm_inner_incl_harmonic_le {Cπ : ℝ} (P : S.CochainProj Cπ) (h : κ) {u : PiLp 2 W}
    (hu : u ∈ (H.total.harmonic ())ᗮ) {q : S.X h} (hq : q ∈ (S.cpx h).harmonic ()) :
    ‖⟪S.incl h q, u⟫_𝕜‖ ≤ (S.boundConst * ‖(H.total.cycles ()).starProjection u -
        S.incl h (P.π h ((H.total.cycles ()).starProjection u))‖ +
      Cπ * S.graphDefect h * ‖u‖) * ‖q‖ :=
  hi.norm_inner_incl_harmonic_le_of_gap P h (fun q _ => (norm_sub_starProjection_le _ _).trans
    (S.norm_incl_apply_le h q)) hu hq

theorem norm_incl_sub_harmonicProj_le {Cπ : ℝ} (P : S.CochainProj Cπ) (h : κ) {q : S.X h}
    (hq : q ∈ (S.cpx h).harmonic ()) :
    ‖S.incl h q - (H.total.harmonic ()).starProjection (S.incl h q)‖ ≤
      ‖(H.total.harmonic ()).starProjection (S.incl h q) -
          S.incl h (P.π h ((H.total.harmonic ()).starProjection (S.incl h q)))‖ +
        Cπ * S.graphDefect h * ‖q‖ := by
  set r := (H.total.harmonic ()).starProjection (S.incl h q)
  set b := S.incl h q - r
  obtain ⟨hDq, hDsq⟩ := (mem_diffComplex_harmonic (S.D h) (S.D_D h)).1 hq
  have hr : r ∈ H.total.harmonic () := (H.total.harmonic ()).starProjection_apply_mem _
  have hbK : b ∈ H.total.cycles () := (H.total.cycles ()).sub_mem
    (hi.incl_mem_cycles h hDq) (H.total.harmonic_le_cycles () hr)
  have hbcl : b ∈ (H.total.boundaries ()).topologicalClosure :=
    H.total.mem_closure_boundaries_of_mem_cycles hbK
      ((H.total.harmonic ()).sub_starProjection_mem_orthogonal (S.incl h q))
  obtain ⟨w, hw⟩ := P.mem_range_of_mem_closure h hbcl
  have hq0 : ⟪q, P.π h b⟫_𝕜 = 0 := by
    rw [← hw]
    change ⟪q, S.D h w⟫_𝕜 = 0
    rw [← ContinuousLinearMap.adjoint_inner_left, hDsq, inner_zero_left]
  have hr0 : ⟪r, S.incl h (P.π h b)⟫_𝕜 = 0 :=
    inner_eq_zero_symm.1 ((H.total.isOrtho_closure_boundaries_harmonic ()).inner_eq
      (hi.incl_mem_closure h (Submodule.le_topologicalClosure _ ⟨⟨w, Submodule.mem_top⟩, hw⟩)) hr)
  have e1 : ⟪b, S.incl h (P.π h b)⟫_𝕜 = -⟪(1 - S.J h) q, P.π h b⟫_𝕜 := by
    rw [show ⟪b, S.incl h (P.π h b)⟫_𝕜 = ⟪S.incl h q - r, S.incl h (P.π h b)⟫_𝕜 from rfl,
      inner_sub_left, hr0, sub_zero, ← S.inner_J, _root_.sub_apply, one_apply_eq_self,
      inner_sub_left, hq0, zero_sub, neg_neg]
  have e2 : b - S.incl h (P.π h b) = -(r - S.incl h (P.π h r)) := by
    change S.incl h q - r - S.incl h (P.π h (S.incl h q - r)) = _
    simp only [_root_.map_sub, P.π_incl]
    abel
  have hCπ := P.nonneg
  have t1 : ‖⟪b, b - S.incl h (P.π h b)⟫_𝕜‖ ≤ ‖b‖ * ‖r - S.incl h (P.π h r)‖ :=
    (norm_inner_le_norm _ _).trans_eq (by rw [e2, norm_neg])
  have t2 : ‖⟪b, S.incl h (P.π h b)⟫_𝕜‖ ≤ S.graphDefect h * ‖q‖ * (Cπ * ‖b‖) := by
    rw [e1, norm_neg]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul (S.norm_one_sub_J_apply_le_of_D_eq_zero h hDq)
      (P.norm_π_apply_le_of_mem_cycles h hbK) (norm_nonneg _)
      (mul_nonneg (S.graphDefect_nonneg h) (norm_nonneg _)))
  have h1 : ‖b‖ * ‖b‖ ≤ ‖b‖ * (‖r - S.incl h (P.π h r)‖ + Cπ * S.graphDefect h * ‖q‖) := by
    have hre : ‖b‖ * ‖b‖ = RCLike.re ⟪b, b⟫_𝕜 := by
      rw [← pow_two, @norm_sq_eq_re_inner 𝕜]
    rw [hre, show ⟪b, b⟫_𝕜 = ⟪b, b - S.incl h (P.π h b)⟫_𝕜 + ⟪b, S.incl h (P.π h b)⟫_𝕜 by
      rw [← inner_add_right, sub_add_cancel]]
    refine (RCLike.re_le_norm _).trans ((norm_add_le _ _).trans ((add_le_add t1 t2).trans
      (le_of_eq ?_)))
    ring
  rcases (norm_nonneg b).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact add_nonneg (norm_nonneg _)
      (mul_nonneg (mul_nonneg hCπ (S.graphDefect_nonneg h)) (norm_nonneg _))
  · exact le_of_mul_le_mul_left h1 hpos

theorem norm_sub_incl_harmonic_le {Cπ : ℝ} (P : S.CochainProj Cπ) (h : κ) {p : PiLp 2 W}
    (hp : p ∈ H.total.harmonic ()) :
    ‖p - S.incl h (((S.cpx h).harmonic ()).starProjection (P.π h p))‖ ≤
      (1 + S.boundConst ^ 2) * ‖p - S.incl h (P.π h p)‖ +
        S.boundConst * Cπ * S.graphDefect h * ‖p‖ := by
  set Kh := (S.cpx h).harmonic ()
  set a := P.π h p
  set β := a - Kh.starProjection a
  obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 (H.total.harmonic_le_cycles () hp)
  have hDa : S.D h a = 0 := by
    show S.D h (P.π h p) = 0
    rw [hy]
    exact (P.π_totalD h y).symm.trans ((congrArg (P.π h) hy0).trans (_root_.map_zero _))
  have haK : a ∈ (S.cpx h).cycles () := by
    rw [diffComplex_cycles]; exact LinearMap.mem_ker.2 hDa
  have hβ : β ∈ ((S.cpx h).boundaries ()).topologicalClosure :=
    (S.cpx h).mem_closure_boundaries_of_mem_cycles
      (((S.cpx h).cycles ()).sub_mem haK
        ((S.cpx h).harmonic_le_cycles () (Kh.starProjection_apply_mem a)))
      (Kh.sub_starProjection_mem_orthogonal a)
  have h0 : ⟪S.incl h β, p⟫_𝕜 = 0 :=
    (H.total.isOrtho_closure_boundaries_harmonic ()).inner_eq (hi.incl_mem_closure h hβ) hp
  have hβa : ⟪β, a⟫_𝕜 = ⟪β, β⟫_𝕜 := by
    have : ⟪β, Kh.starProjection a⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal
      (Kh.starProjection_apply_mem a) (Kh.sub_starProjection_mem_orthogonal a)
    rw [show ⟪β, β⟫_𝕜 = ⟪β, a⟫_𝕜 - ⟪β, Kh.starProjection a⟫_𝕜 from inner_sub_right _ _ _, this,
      sub_zero]
  have e : ⟪β, β⟫_𝕜 = ⟪S.incl h β, S.incl h a - p⟫_𝕜 + ⟪(1 - S.J h) β, a⟫_𝕜 := by
    rw [← hβa, inner_sub_right, h0, sub_zero, ← S.inner_J, _root_.sub_apply,
      one_apply_eq_self, inner_sub_left β (S.J h β) a]
    exact (add_sub_cancel _ _).symm
  have hC := S.boundConst_nonneg
  have hCπ := P.nonneg
  have hDβ : S.D h β = 0 := by
    change S.D h (a - Kh.starProjection a) = 0
    rw [_root_.map_sub, hDa, ((mem_diffComplex_harmonic (S.D h) (S.D_D h)).1
      (Kh.starProjection_apply_mem a)).1, sub_zero]
  have hβle : ‖β‖ ≤ S.boundConst * ‖p - S.incl h a‖ + Cπ * S.graphDefect h * ‖p‖ := by
    have t1 : ‖⟪S.incl h β, S.incl h a - p⟫_𝕜‖ ≤ S.boundConst * ‖β‖ * ‖p - S.incl h a‖ :=
      (norm_inner_le_norm _ _).trans (by
        rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_right (S.norm_incl_apply_le h β)
          (norm_nonneg _))
    have t2 : ‖⟪(1 - S.J h) β, a⟫_𝕜‖ ≤ S.graphDefect h * ‖β‖ * (Cπ * ‖p‖) :=
      (norm_inner_le_norm _ _).trans (mul_le_mul (S.norm_one_sub_J_apply_le_of_D_eq_zero h hDβ)
        (P.norm_π_apply_le_of_mem_cycles h (H.total.harmonic_le_cycles () hp)) (norm_nonneg _)
        (mul_nonneg (S.graphDefect_nonneg h) (norm_nonneg _)))
    have h1 : ‖β‖ * ‖β‖ ≤ ‖β‖ * (S.boundConst * ‖p - S.incl h a‖ + Cπ * S.graphDefect h * ‖p‖) := by
      have hre : ‖β‖ * ‖β‖ = RCLike.re ⟪β, β⟫_𝕜 := by
        rw [← pow_two, @norm_sq_eq_re_inner 𝕜]
      rw [hre, e]
      refine (RCLike.re_le_norm _).trans ((norm_add_le _ _).trans ((add_le_add t1 t2).trans
        (le_of_eq ?_)))
      ring
    rcases (norm_nonneg β).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact add_nonneg (mul_nonneg hC (norm_nonneg _))
        (mul_nonneg (mul_nonneg hCπ (S.graphDefect_nonneg h)) (norm_nonneg _))
    · exact le_of_mul_le_mul_left h1 hpos
  have e' : p - S.incl h (Kh.starProjection a) = (p - S.incl h a) + S.incl h β := by
    simp only [β, _root_.map_sub]; abel
  rw [e']
  calc _ ≤ ‖p - S.incl h a‖ + S.boundConst * ‖β‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (S.norm_incl_apply_le h β))
    _ ≤ ‖p - S.incl h a‖ + S.boundConst *
        (S.boundConst * ‖p - S.incl h a‖ + Cπ * S.graphDefect h * ‖p‖) := by gcongr
    _ = _ := by ring

theorem norm_sub_incl_π_le {Cπ : ℝ} (P : S.CochainProj Cπ) (h : κ) (x : H.totalD.domain)
    (v : S.X h) :
    ‖(x : PiLp 2 W) - S.incl h (P.π h x)‖ ≤ (1 + S.boundConst * Cπ) *
      (‖(x : PiLp 2 W) - S.incl h v‖ + ‖H.totalD x - S.incl h (S.D h v)‖) := by
  set w : H.totalD.domain := x - ⟨S.incl h v, hi.incl_mem h v⟩
  have hw : H.totalD w = H.totalD x - S.incl h (S.D h v) := by
    rw [LinearPMap.map_sub, hi.totalD_incl]
  have hw' : (w : PiLp 2 W) = (x : PiLp 2 W) - S.incl h v := rfl
  have e : (x : PiLp 2 W) - S.incl h (P.π h x) = (w : PiLp 2 W) - S.incl h (P.π h w) := by
    rw [hw', _root_.map_sub, P.π_incl, _root_.map_sub]; abel
  have h1 : ‖P.π h w‖ ≤ Cπ * (‖(w : PiLp 2 W)‖ + ‖H.totalD w‖) := P.norm_π_le h w w.2
  have h2 := S.norm_incl_apply_le h (P.π h w)
  rw [e, ← hw', ← hw]
  have := S.boundConst_nonneg
  have := P.nonneg
  calc _ ≤ ‖(w : PiLp 2 W)‖ + ‖S.incl h (P.π h w)‖ := norm_sub_le _ _
    _ ≤ ‖(w : PiLp 2 W)‖ + S.boundConst * (Cπ * (‖(w : PiLp 2 W)‖ + ‖H.totalD w‖)) := by
        gcongr; exact h2.trans (by gcongr)
    _ ≤ _ := by nlinarith [norm_nonneg (H.totalD w), norm_nonneg (w : PiLp 2 W)]

theorem norm_sub_incl_π_le_of_mem_cycles {Cπ : ℝ} (P : S.CochainProj Cπ) (h : κ) {x : PiLp 2 W}
    (hx : x ∈ H.total.cycles ()) (v : S.X h) :
    ‖x - S.incl h (P.π h x)‖ ≤ (1 + S.boundConst * Cπ) *
      (‖x - S.incl h v‖ + ‖S.incl h (S.D h v)‖) := by
  obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hx
  have := hi.norm_sub_incl_π_le P h y v
  rwa [show H.totalD y = 0 from hy, zero_sub, norm_neg] at this

theorem norm_incl_sub_harmonicProj_le_of_harmonic {Cπ : ℝ} (P : S.CochainProj Cπ) (h : κ)
    {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ r ∈ H.total.harmonic (), ‖r - S.incl h (P.π h r)‖ ≤ μ * ‖r‖) {q : S.X h}
    (hq : q ∈ (S.cpx h).harmonic ()) :
    ‖S.incl h q - (H.total.harmonic ()).starProjection (S.incl h q)‖ ≤
      (S.boundConst * μ + Cπ * S.graphDefect h) * ‖q‖ := by
  refine (hi.norm_incl_sub_harmonicProj_le P h hq).trans ?_
  have hr := (hμ _ ((H.total.harmonic ()).starProjection_apply_mem _)).trans
    (mul_le_mul_of_nonneg_left (((H.total.harmonic ()).norm_starProjection_apply_le _).trans
      (S.norm_incl_apply_le h q)) hμ0)
  nlinarith

variable (hcr : ∀ i, H.ClosedRangeAt i)

theorem staticError_le_of_gap {Cπ : ℝ} (P : S.CochainProj Cπ) {cP : ℝ} (hP : S.IsPoincare cP)
    (hcP : 1 ≤ cP) (h : κ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ q ∈ (S.cpx h).harmonic (),
      ‖S.incl h q - (H.total.harmonic ()).starProjection (S.incl h q)‖ ≤ δ * ‖q‖)
    (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) :
    S.staticError hcr h f ≤ S.readError h (H.totalMixedSolution hcr f) x +
      240 * S.boundConst * cP ^ 2 * (5 * S.graphDefect h * ‖x‖ +
        S.boundConst * S.readError h (H.totalMixedSolution hcr f) x +
        (δ * ‖(H.total.cycles ()).starProjection (H.greenOp hcr f) -
            S.incl h (P.π h ((H.total.cycles ()).starProjection (H.greenOp hcr f)))‖ +
          Cπ * S.graphDefect h * ‖H.greenOp hcr f‖)) := by
  have hCπ := P.nonneg
  have hη0 : 0 ≤ δ * ‖(H.total.cycles ()).starProjection (H.greenOp hcr f) -
      S.incl h (P.π h ((H.total.cycles ()).starProjection (H.greenOp hcr f)))‖ +
      Cπ * S.graphDefect h * ‖H.greenOp hcr f‖ :=
    add_nonneg (mul_nonneg hδ0 (norm_nonneg _))
      (mul_nonneg (mul_nonneg hCπ (S.graphDefect_nonneg h)) (norm_nonneg _))
  have := S.staticError_le_of_split hcr hP hcP h f x le_rfl le_rfl hη0
    (fun v => by rw [hi.cochainDefect_eq_zero, inner_zero_left, norm_zero, zero_mul])
    (fun v => by rw [hi.cochainDefect_eq_zero, inner_zero_left, norm_zero, zero_mul])
    (fun q hq => hi.norm_inner_incl_harmonic_le_of_gap P h hδ
      (H.greenOp_mem_orthogonal_harmonic hcr f) hq)
  simpa only [add_zero] using this

/-- **The error estimate with cochain reading maps**: with a uniform discrete Poincaré inequality,
`e(f)` is bounded by the read error of any discrete triple, the inner-product defect and
`‖b - iₕ πₕ b‖`, `b = P_𝔷 G f`. -/
theorem staticError_le {Cπ : ℝ} (P : S.CochainProj Cπ) {cP : ℝ} (hP : S.IsPoincare cP)
    (hcP : 1 ≤ cP) (h : κ) (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) :
    S.staticError hcr h f ≤ S.readError h (H.totalMixedSolution hcr f) x +
      240 * S.boundConst * cP ^ 2 * (5 * S.graphDefect h * ‖x‖ +
        S.boundConst * S.readError h (H.totalMixedSolution hcr f) x +
        (S.boundConst * ‖(H.total.cycles ()).starProjection (H.greenOp hcr f) -
            S.incl h (P.π h ((H.total.cycles ()).starProjection (H.greenOp hcr f)))‖ +
          Cπ * S.graphDefect h * ‖H.greenOp hcr f‖)) :=
  hi.staticError_le_of_gap hcr P hP hcP h S.boundConst_nonneg
    (fun q _ => (norm_sub_starProjection_le _ _).trans (S.norm_incl_apply_le h q)) f x

theorem staticError_le_of_harmonic {Cπ : ℝ} (P : S.CochainProj Cπ) {cP : ℝ}
    (hP : S.IsPoincare cP) (hcP : 1 ≤ cP) (h : κ) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ r ∈ H.total.harmonic (), ‖r - S.incl h (P.π h r)‖ ≤ μ * ‖r‖)
    (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) :
    S.staticError hcr h f ≤ S.readError h (H.totalMixedSolution hcr f) x +
      240 * S.boundConst * cP ^ 2 * (5 * S.graphDefect h * ‖x‖ +
        S.boundConst * S.readError h (H.totalMixedSolution hcr f) x +
        ((S.boundConst * μ + Cπ * S.graphDefect h) *
            ‖(H.total.cycles ()).starProjection (H.greenOp hcr f) -
              S.incl h (P.π h ((H.total.cycles ()).starProjection (H.greenOp hcr f)))‖ +
          Cπ * S.graphDefect h * ‖H.greenOp hcr f‖)) :=
  hi.staticError_le_of_gap hcr P hP hcP h
    (add_nonneg (mul_nonneg S.boundConst_nonneg hμ0) (mul_nonneg P.nonneg (S.graphDefect_nonneg h)))
    (fun _ hq => hi.norm_incl_sub_harmonicProj_le_of_harmonic P h hμ0 hμ hq) f x

theorem staticError_le_of_gap_inf {Cπ : ℝ} (P : S.CochainProj Cπ) {cP : ℝ}
    (hP : S.IsPoincare cP) (hcP : 1 ≤ cP) (h : κ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ q ∈ (S.cpx h).harmonic (),
      ‖S.incl h q - (H.total.harmonic ()).starProjection (S.incl h q)‖ ≤ δ * ‖q‖)
    (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) (v : S.X h) :
    S.staticError hcr h f ≤ S.readError h (H.totalMixedSolution hcr f) x +
      240 * S.boundConst * cP ^ 2 * (5 * S.graphDefect h * ‖x‖ +
        S.boundConst * S.readError h (H.totalMixedSolution hcr f) x +
        (δ * ((1 + S.boundConst * Cπ) *
            (‖(H.total.cycles ()).starProjection (H.greenOp hcr f) - S.incl h v‖ +
              ‖S.incl h (S.D h v)‖)) +
          Cπ * S.graphDefect h * ‖H.greenOp hcr f‖)) := by
  refine (hi.staticError_le_of_gap hcr P hP hcP h hδ0 hδ f x).trans ?_
  have := S.boundConst_nonneg
  gcongr
  exact hi.norm_sub_incl_π_le_of_mem_cycles P h ((H.total.cycles ()).starProjection_apply_mem _) v

theorem staticError_le_inf {Cπ : ℝ} (P : S.CochainProj Cπ) {cP : ℝ} (hP : S.IsPoincare cP)
    (hcP : 1 ≤ cP) (h : κ) (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) (v : S.X h) :
    S.staticError hcr h f ≤ S.readError h (H.totalMixedSolution hcr f) x +
      240 * S.boundConst * cP ^ 2 * (5 * S.graphDefect h * ‖x‖ +
        S.boundConst * S.readError h (H.totalMixedSolution hcr f) x +
        (S.boundConst * ((1 + S.boundConst * Cπ) *
            (‖(H.total.cycles ()).starProjection (H.greenOp hcr f) - S.incl h v‖ +
              ‖S.incl h (S.D h v)‖)) +
          Cπ * S.graphDefect h * ‖H.greenOp hcr f‖)) :=
  hi.staticError_le_of_gap_inf hcr P hP hcP h S.boundConst_nonneg
    (fun q _ => (norm_sub_starProjection_le _ _).trans (S.norm_incl_apply_le h q)) f x v

theorem staticError_le_of_harmonic_inf {Cπ : ℝ} (P : S.CochainProj Cπ) {cP : ℝ}
    (hP : S.IsPoincare cP) (hcP : 1 ≤ cP) (h : κ) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ r ∈ H.total.harmonic (), ‖r - S.incl h (P.π h r)‖ ≤ μ * ‖r‖)
    (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) (v : S.X h) :
    S.staticError hcr h f ≤ S.readError h (H.totalMixedSolution hcr f) x +
      240 * S.boundConst * cP ^ 2 * (5 * S.graphDefect h * ‖x‖ +
        S.boundConst * S.readError h (H.totalMixedSolution hcr f) x +
        ((S.boundConst * μ + Cπ * S.graphDefect h) * ((1 + S.boundConst * Cπ) *
            (‖(H.total.cycles ()).starProjection (H.greenOp hcr f) - S.incl h v‖ +
              ‖S.incl h (S.D h v)‖)) +
          Cπ * S.graphDefect h * ‖H.greenOp hcr f‖)) :=
  hi.staticError_le_of_gap_inf hcr P hP hcP h
    (add_nonneg (mul_nonneg S.boundConst_nonneg hμ0) (mul_nonneg P.nonneg (S.graphDefect_nonneg h)))
    (fun _ hq => hi.norm_incl_sub_harmonicProj_le_of_harmonic P h hμ0 hμ hq) f x v

theorem staticError_le_projError {Cπ : ℝ} (P : S.CochainProj Cπ) {cP : ℝ}
    (hP : S.IsPoincare cP) (hcP : 1 ≤ cP) (h : κ) (f : PiLp 2 W) :
    S.staticError hcr h f ≤ ((1 + S.boundConst ^ 2) * P.projError h (H.totalMixedSolution hcr f) +
        S.boundConst * Cπ * S.graphDefect h * ‖H.totalMixedSolution hcr f‖) +
      240 * S.boundConst * cP ^ 2 * (51 * Cπ * S.graphDefect h * ‖H.totalMixedSolution hcr f‖ +
        S.boundConst * ((1 + S.boundConst ^ 2) * P.projError h (H.totalMixedSolution hcr f) +
          S.boundConst * Cπ * S.graphDefect h * ‖H.totalMixedSolution hcr f‖) +
        S.boundConst * ‖(H.total.cycles ()).starProjection (H.greenOp hcr f) -
          S.incl h (P.π h ((H.total.cycles ()).starProjection (H.greenOp hcr f)))‖) := by
  set X := H.totalMixedSolution hcr f
  set σ : H.totalD.domain := H.total.domainCoord () () X.fst
  set υ : H.totalD.domain := H.total.domainCoord () () X.snd.fst
  set p : PiLp 2 W := (X.snd.snd : PiLp 2 W)
  have hp : p ∈ H.total.harmonic () := X.snd.snd.2
  have hC := S.boundConst_nonneg
  have hCπ := P.nonneg
  obtain ⟨n0, n1, n2, n3, n4⟩ := norm_mixedComponents_le H.total X
  -- the approximants
  set x : (S.cpx h).MixedSpace () () :=
    MixedSpace.mk (toDom (S.D h) (S.D_D h) (P.π h σ)) (toDom (S.D h) (S.D_D h) (P.π h υ))
      ⟨((S.cpx h).harmonic ()).starProjection (P.π h p),
        ((S.cpx h).harmonic ()).starProjection_apply_mem _⟩
  have hread : S.readError h X x ≤
      (1 + S.boundConst ^ 2) * P.projError h X + S.boundConst * Cπ * S.graphDefect h * ‖X‖ := by
    have hgap := hi.norm_sub_incl_harmonic_le P h hp
    have e : S.readError h X x = ‖(σ : PiLp 2 W) - S.incl h (P.π h σ)‖ +
        ‖H.totalD σ - S.incl h (S.D h (P.π h σ))‖ + ‖(υ : PiLp 2 W) - S.incl h (P.π h υ)‖ +
        ‖H.totalD υ - S.incl h (S.D h (P.π h υ))‖ +
        ‖p - S.incl h (((S.cpx h).harmonic ()).starProjection (P.π h p))‖ := rfl
    have e' : P.projError h X = ‖(σ : PiLp 2 W) - S.incl h (P.π h σ)‖ +
        ‖H.totalD σ - S.incl h (P.π h (H.totalD σ))‖ + ‖(υ : PiLp 2 W) - S.incl h (P.π h υ)‖ +
        ‖H.totalD υ - S.incl h (P.π h (H.totalD υ))‖ + ‖p - S.incl h (P.π h p)‖ := rfl
    rw [e, ← P.π_totalD, ← P.π_totalD]
    rw [e']
    have hp4 : ‖p‖ ≤ ‖X‖ := n4
    have : 0 ≤ S.boundConst * Cπ * S.graphDefect h :=
      mul_nonneg (mul_nonneg hC hCπ) (S.graphDefect_nonneg h)
    have := mul_le_mul_of_nonneg_left hp4 this
    nlinarith [norm_nonneg ((σ : PiLp 2 W) - S.incl h (P.π h σ)),
      norm_nonneg (H.totalD σ - S.incl h (P.π h (H.totalD σ))),
      norm_nonneg ((υ : PiLp 2 W) - S.incl h (P.π h υ)),
      norm_nonneg (H.totalD υ - S.incl h (P.π h (H.totalD υ))), sq_nonneg S.boundConst]
  have hnorm : ‖x‖ ≤ 10 * Cπ * ‖X‖ := by
    have hdom : ∀ z : H.totalD.domain,
        ‖toDom (S.D h) (S.D_D h) (P.π h z)‖ ≤ 2 * Cπ * (‖(z : PiLp 2 W)‖ + ‖H.totalD z‖) := by
      intro z
      have e : ‖toDom (S.D h) (S.D_D h) (P.π h z)‖ ^ 2 =
          ‖P.π h z‖ ^ 2 + ‖S.D h (P.π h z)‖ ^ 2 :=
        (S.cpx h).norm_sq_domainSpace () _
      refine (le_add_of_sq_eq (norm_nonneg _) (norm_nonneg _) e).trans ?_
      rw [← P.π_totalD]
      have h1 : ‖P.π h z‖ ≤ Cπ * (‖(z : PiLp 2 W)‖ + ‖H.totalD z‖) := P.norm_π_le h z z.2
      have h2 := P.norm_π_apply_le_of_mem_cycles h (H.totalD_mem_cycles z)
      nlinarith [norm_nonneg (z : PiLp 2 W), norm_nonneg (H.totalD z)]
    have e := MixedSpace.norm_sq x
    refine (le_add_add_of_sq_eq (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) e).trans ?_
    have h3 : ‖((x.snd.snd : S.X h))‖ ≤ Cπ * ‖p‖ :=
      (Submodule.norm_starProjection_apply_le _ _).trans
        (P.norm_π_apply_le_of_mem_cycles h (H.total.harmonic_le_cycles () hp))
    have h1 := hdom σ
    have h2 := hdom υ
    change ‖toDom (S.D h) (S.D_D h) (P.π h σ)‖ + ‖toDom (S.D h) (S.D_D h) (P.π h υ)‖ +
      ‖((x.snd.snd : S.X h))‖ ≤ 10 * Cπ * ‖X‖
    have m0 : ‖(σ : PiLp 2 W)‖ ≤ ‖X‖ := n0
    have m1 : ‖H.totalD σ‖ ≤ ‖X‖ := n1
    have m2 : ‖(υ : PiLp 2 W)‖ ≤ ‖X‖ := n2
    have m3 : ‖H.totalD υ‖ ≤ ‖X‖ := n3
    have m4 : ‖p‖ ≤ ‖X‖ := n4
    nlinarith [mul_le_mul_of_nonneg_left m0 hCπ, mul_le_mul_of_nonneg_left m1 hCπ,
      mul_le_mul_of_nonneg_left m2 hCπ, mul_le_mul_of_nonneg_left m3 hCπ,
      mul_le_mul_of_nonneg_left m4 hCπ, mul_nonneg hCπ (norm_nonneg X)]
  have hg : ‖H.greenOp hcr f‖ ≤ ‖X‖ := n2
  have hJ0 := S.graphDefect_nonneg h
  refine (hi.staticError_le hcr P hP hcP h f x).trans ?_
  have hK : 0 ≤ 240 * S.boundConst * cP ^ 2 := by positivity
  refine add_le_add hread (mul_le_mul_of_nonneg_left ?_ hK)
  have t1 : 5 * S.graphDefect h * ‖x‖ ≤ 50 * Cπ * S.graphDefect h * ‖X‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hnorm hJ0]
  have t2 : Cπ * S.graphDefect h * ‖H.greenOp hcr f‖ ≤ Cπ * S.graphDefect h * ‖X‖ :=
    mul_le_mul_of_nonneg_left hg (mul_nonneg hCπ hJ0)
  have t3 := mul_le_mul_of_nonneg_left hread hC
  linarith

/-- **The static rate with cochain reading maps**: with a uniform discrete Poincaré inequality, if
`σ`, `u`, `p`, `P_𝔷 u` are within `ε` of `iₕ Xₕ` in the graph norm and `‖1 - Jₕ‖_{Vₕ} ‖X‖ ≤ ε`,
then `e(f) ≤ K ε`, `K = cochainRateConst`. -/
theorem staticError_le_of_approx {Cπ : ℝ} (P : S.CochainProj Cπ) {cP : ℝ}
    (hP : S.IsPoincare cP) (hcP : 1 ≤ cP) (h : κ) (f : PiLp 2 W) {ε : ℝ}
    (hσ : ∃ v, ‖H.total.mixedI0 () () (H.totalMixedSolution hcr f) - S.incl h v‖ +
      ‖H.total.mixedD0 () () (H.totalMixedSolution hcr f) - S.incl h (S.D h v)‖ ≤ ε)
    (hu : ∃ v, ‖H.total.mixedI1 () () (H.totalMixedSolution hcr f) - S.incl h v‖ +
      ‖H.total.mixedD1 () () () (H.totalMixedSolution hcr f) - S.incl h (S.D h v)‖ ≤ ε)
    (hp : ∃ v, ‖H.total.mixedI2 () () (H.totalMixedSolution hcr f) - S.incl h v‖ +
      ‖S.incl h (S.D h v)‖ ≤ ε)
    (hb : ∃ v, ‖(H.total.cycles ()).starProjection (H.greenOp hcr f) - S.incl h v‖ +
      ‖S.incl h (S.D h v)‖ ≤ ε)
    (hJ : S.graphDefect h * ‖H.totalMixedSolution hcr f‖ ≤ ε) :
    S.staticError hcr h f ≤ S.cochainRateConst Cπ cP * ε := by
  set X := H.totalMixedSolution hcr f
  set σ : H.totalD.domain := H.total.domainCoord () () X.fst
  set υ : H.totalD.domain := H.total.domainCoord () () X.snd.fst
  have hC := S.boundConst_nonneg
  have hCπ := P.nonneg
  have hε : 0 ≤ ε := (mul_nonneg (S.graphDefect_nonneg h) (norm_nonneg X)).trans hJ
  set Q := 1 + S.boundConst * Cπ
  have hQ : 0 ≤ Q := by positivity
  -- the quasi-optimality on `D(𝐝)` and on the cycles
  have hdom : ∀ (z : H.totalD.domain) (v : S.X h),
      ‖(z : PiLp 2 W) - S.incl h v‖ + ‖H.totalD z - S.incl h (S.D h v)‖ ≤ ε →
      ‖(z : PiLp 2 W) - S.incl h (P.π h z)‖ +
        ‖H.totalD z - S.incl h (P.π h (H.totalD z))‖ ≤ 2 * Q * ε := fun z v hv => by
    have h1 := hi.norm_sub_incl_π_le P h z v
    have h2 := hi.norm_sub_incl_π_le_of_mem_cycles P h (H.totalD_mem_cycles z) (S.D h v)
    rw [S.D_D, _root_.map_zero, norm_zero, add_zero] at h2
    have := norm_nonneg ((z : PiLp 2 W) - S.incl h v)
    have := norm_nonneg (H.totalD z - S.incl h (S.D h v))
    nlinarith [mul_le_mul_of_nonneg_left hv hQ]
  have hcyc : ∀ x ∈ H.total.cycles (), ∀ v : S.X h, ‖x - S.incl h v‖ + ‖S.incl h (S.D h v)‖ ≤ ε →
      ‖x - S.incl h (P.π h x)‖ ≤ Q * ε := fun x hx v hv =>
    (hi.norm_sub_incl_π_le_of_mem_cycles P h hx v).trans (mul_le_mul_of_nonneg_left hv hQ)
  obtain ⟨v₀, hv₀⟩ := hσ
  obtain ⟨v₁, hv₁⟩ := hu
  obtain ⟨v₂, hv₂⟩ := hp
  obtain ⟨v₃, hv₃⟩ := hb
  have hπ : P.projError h X ≤ 5 * Q * ε := by
    have e : P.projError h X = (‖(σ : PiLp 2 W) - S.incl h (P.π h σ)‖ +
        ‖H.totalD σ - S.incl h (P.π h (H.totalD σ))‖) + (‖(υ : PiLp 2 W) - S.incl h (P.π h υ)‖ +
        ‖H.totalD υ - S.incl h (P.π h (H.totalD υ))‖) +
        ‖H.total.mixedI2 () () X - S.incl h (P.π h (H.total.mixedI2 () () X))‖ := by
      simp only [CochainProj.projError, add_assoc]; rfl
    rw [e]
    have := hdom σ v₀ hv₀
    have := hdom υ v₁ hv₁
    have := hcyc (H.total.mixedI2 () () X) (H.total.harmonic_le_cycles () (X.snd.snd.2)) v₂ hv₂
    linarith
  have hbε := hcyc _ ((H.total.cycles ()).starProjection_apply_mem _) v₃ hv₃
  refine (hi.staticError_le_projError hcr P hP hcP h f).trans ?_
  have hR : (1 + S.boundConst ^ 2) * P.projError h X + S.boundConst * Cπ * S.graphDefect h * ‖X‖ ≤
      (5 * (1 + S.boundConst ^ 2) * Q + S.boundConst * Cπ) * ε := by
    have := mul_le_mul_of_nonneg_left hπ (by positivity : (0 : ℝ) ≤ 1 + S.boundConst ^ 2)
    have := mul_le_mul_of_nonneg_left hJ (mul_nonneg hC hCπ)
    nlinarith
  have hK : 0 ≤ 240 * S.boundConst * cP ^ 2 := by positivity
  have hJ' := mul_le_mul_of_nonneg_left hJ (by positivity : (0 : ℝ) ≤ 51 * Cπ)
  have hR' := mul_le_mul_of_nonneg_left hR hC
  have hb' := mul_le_mul_of_nonneg_left hbε hC
  have := mul_le_mul_of_nonneg_left (show 51 * Cπ * S.graphDefect h * ‖X‖ +
      S.boundConst * ((1 + S.boundConst ^ 2) * P.projError h X +
        S.boundConst * Cπ * S.graphDefect h * ‖X‖) +
      S.boundConst * ‖(H.total.cycles ()).starProjection (H.greenOp hcr f) -
        S.incl h (P.π h ((H.total.cycles ()).starProjection (H.greenOp hcr f)))‖ ≤
      (51 * Cπ + S.boundConst * (5 * (1 + S.boundConst ^ 2) * Q + S.boundConst * Cπ) +
        S.boundConst * Q) * ε by nlinarith) hK
  simp only [cochainRateConst]
  nlinarith

/-- **Convergence with cochain reading maps**: with a uniform discrete Poincaré inequality,
`‖1 - Jₕ‖_{Vₕ} → 0` and `iₕ πₕ x → x` on `D(𝐝)`, the static error tends to `0` for every datum. -/
theorem tendsto_staticError {Cπ : ℝ} (P : S.CochainProj Cπ) {cP : ℝ} (hP : S.IsPoincare cP)
    (hcP : 1 ≤ cP) {l : Filter κ} (hJ : Tendsto S.graphDefect l (𝓝 0))
    (happ : ∀ x ∈ H.totalD.domain, Tendsto (fun h => ‖x - S.incl h (P.π h x)‖) l (𝓝 0))
    (f : PiLp 2 W) : Tendsto (fun h => S.staticError hcr h f) l (𝓝 0) := by
  set X := H.totalMixedSolution hcr f
  set σ : H.totalD.domain := H.total.domainCoord () () X.fst
  set υ : H.totalD.domain := H.total.domainCoord () () X.snd.fst
  have hK : ∀ x ∈ H.total.cycles (), Tendsto (fun h => ‖x - S.incl h (P.π h x)‖) l (𝓝 0) :=
    fun x hx => happ x (H.mem_totalD_domain_of_mem_cycles hx)
  have hε : Tendsto (fun h => P.projError h X) l (𝓝 0) := by
    have := ((((happ σ σ.2).add (hK _ (H.totalD_mem_cycles σ))).add (happ υ υ.2)).add
      (hK _ (H.totalD_mem_cycles υ))).add
      (hK _ (H.total.harmonic_le_cycles () X.snd.snd.2))
    simp only [add_zero] at this
    exact this
  have hb := hK _ ((H.total.cycles ()).starProjection_apply_mem (H.greenOp hcr f))
  set C := S.boundConst
  have hR : Tendsto (fun h => (1 + C ^ 2) * P.projError h X + C * Cπ * S.graphDefect h * ‖X‖) l
      (𝓝 0) := by
    simpa using (hε.const_mul (1 + C ^ 2)).add ((hJ.const_mul (C * Cπ)).mul_const ‖X‖)
  have hT := hR.add ((((hJ.const_mul (51 * Cπ)).mul_const ‖X‖).add (hR.const_mul C)).add
    (hb.const_mul C) |>.const_mul (240 * C * cP ^ 2))
  simp only [mul_zero, add_zero, zero_mul] at hT
  refine squeeze_zero (fun h => S.staticError_nonneg hcr h f) (fun h =>
    (hi.staticError_le_projError hcr P hP hcP h f).trans_eq ?_) hT
  ring

end IsCochain

/-! ### Cohomology -/

namespace CochainProj

variable {Cπ : ℝ} (P : S.CochainProj Cπ)

theorem π_cochainMap (h : κ) (j k : Unit) (_ : ComplexShape.loop.Rel j k)
    (x : (H.total.d j k).domain) :
    ∃ hx : (P.π h : PiLp 2 W →ₗ[𝕜] S.X h) x ∈ ((S.cpx h).d j k).domain,
      (S.cpx h).d j k ⟨_, hx⟩ = (P.π h : PiLp 2 W →ₗ[𝕜] S.X h) (H.total.d j k x) :=
  ⟨Submodule.mem_top, (P.π_totalD h x).symm⟩

/-- `πₕ` on the cycles, valued in the discrete cycles. -/
def cyclesMap (h : κ) : H.total.cycles () →ₗ[𝕜] (S.cpx h).cycles () :=
  (P.π h : PiLp 2 W →ₗ[𝕜] S.X h).restrict fun _ hz =>
    HilbertComplex.apply_mem_cycles (T := fun _ => (P.π h : PiLp 2 W →ₗ[𝕜] S.X h))
      (P.π_cochainMap h) hz

/-- **The map induced on cohomology** `H(𝐝) → H(𝐝ₕ)`, `[z] ↦ [πₕ z]`. [HolstStern2012], §3.1 -/
def cohomologyMap (h : κ) : H.total.cohomology () →ₗ[𝕜] (S.cpx h).cohomology () :=
  Submodule.mapQ _ _ (P.cyclesMap h) fun _ hz => by
    exact HilbertComplex.apply_mem_boundaries (T := fun _ => (P.π h : PiLp 2 W →ₗ[𝕜] S.X h))
      (P.π_cochainMap h) hz

end CochainProj

namespace IsCochain

variable (hi : S.IsCochain)
include hi

theorem cohomologyMap_surjective {Cπ : ℝ} (P : S.CochainProj Cπ) (h : κ) :
    Function.Surjective (P.cohomologyMap h) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hx : S.D h x = 0 := LinearMap.mem_ker.1 ((diffComplex_cycles _ _ ()).le x.2)
  refine ⟨Submodule.Quotient.mk ⟨S.incl h x, hi.incl_mem_cycles h hx⟩, ?_⟩
  rw [CochainProj.cohomologyMap, Submodule.mapQ_apply]
  exact congrArg _ (Subtype.ext (P.π_incl h x))

theorem cohomologyMap_injective {Cπ : ℝ} (P : S.CochainProj Cπ) (hcr : ∀ i, H.ClosedRangeAt i)
    (h : κ) (hgap : ∀ q ∈ H.total.harmonic (), q ≠ 0 → ‖q - S.incl h (P.π h q)‖ < ‖q‖) :
    Function.Injective (P.cohomologyMap h) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [CochainProj.cohomologyMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  have hz : P.π h z ∈ (S.cpx h).boundaries () := hy
  have hz' : (z : PiLp 2 W) ∈ H.total.boundaries () ⊔ H.total.harmonic () := by
    rw [H.total.boundaries_sup_harmonic (H.closedRangeAt_total hcr ())]; exact z.2
  obtain ⟨b, ⟨w, hw⟩, q, hq, hbq⟩ := Submodule.mem_sup.1 hz'
  have hπb : P.π h b ∈ (S.cpx h).boundaries () :=
    ⟨⟨P.π h w, Submodule.mem_top⟩, (P.π_totalD h w).symm.trans (congrArg (P.π h) hw)⟩
  have hπq : P.π h q ∈ (S.cpx h).boundaries () := by
    have := ((S.cpx h).boundaries ()).sub_mem hz hπb
    rwa [← hbq, _root_.map_add, add_sub_cancel_left] at this
  obtain ⟨v, hv⟩ := hπq
  have hiq : S.incl h (P.π h q) ∈ H.total.boundaries () :=
    ⟨⟨S.incl h v, hi.incl_mem h v⟩, (hi.totalD_incl h v).trans (congrArg (S.incl h) hv)⟩
  have hq0 : q = 0 := by
    by_contra hq0
    have h0 : ⟪S.incl h (P.π h q), q⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal hiq (H.total.mem_harmonic_iff.1 hq).2
    have hle : ‖q‖ ^ 2 ≤ ‖q - S.incl h (P.π h q)‖ * ‖q‖ := by
      rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), show ⟪q, q⟫_𝕜 = ⟪q - S.incl h (P.π h q), q⟫_𝕜 by
        rw [inner_sub_left, h0, sub_zero]]
      exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    nlinarith [hgap q hq hq0, norm_pos_iff.2 hq0]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, ← hbq, hq0,
    add_zero]
  exact ⟨w, hw⟩

/-- The isomorphism `H(𝐝) ≃ H(𝐝ₕ)` under closed range and a strict gap. [HolstStern2012], Cor 3.4 -/
def cohomologyEquiv {Cπ : ℝ} (P : S.CochainProj Cπ) (hcr : ∀ i, H.ClosedRangeAt i) (h : κ)
    (hgap : ∀ q ∈ H.total.harmonic (), q ≠ 0 → ‖q - S.incl h (P.π h q)‖ < ‖q‖) :
    H.total.cohomology () ≃ₗ[𝕜] (S.cpx h).cohomology () :=
  LinearEquiv.ofBijective _
    ⟨hi.cohomologyMap_injective P hcr h hgap, hi.cohomologyMap_surjective P h⟩

end IsCochain

namespace CochainProj

variable {Cπ : ℝ} (P : S.CochainProj Cπ)

theorem eventually_norm_sub_incl_π_lt [FiniteDimensional 𝕜 (H.total.harmonic ())] {l : Filter κ}
    (happ : ∀ q ∈ H.total.harmonic (), Tendsto (fun h => ‖q - S.incl h (P.π h q)‖) l (𝓝 0)) :
    ∀ᶠ h in l, ∀ q ∈ H.total.harmonic (), q ≠ 0 → ‖q - S.incl h (P.π h q)‖ < ‖q‖ := by
  set Hm := H.total.harmonic ()
  set B := 1 + S.boundConst * Cπ
  have hC := S.boundConst_nonneg
  have hCπ := P.nonneg
  have hB : 0 ≤ B := by positivity
  have hlip : ∀ h (x y : Hm), ‖(x : PiLp 2 W) - S.incl h (P.π h x)‖ ≤
      ‖(y : PiLp 2 W) - S.incl h (P.π h y)‖ + B * dist x y := by
    intro h x y
    set z : PiLp 2 W := (x : PiLp 2 W) - y
    have e : (x : PiLp 2 W) - S.incl h (P.π h x) =
        ((y : PiLp 2 W) - S.incl h (P.π h y)) + (z - S.incl h (P.π h z)) := by
      simp only [z, _root_.map_sub]; abel
    have hz : ‖S.incl h (P.π h z)‖ ≤ S.boundConst * Cπ * ‖z‖ := by
      rw [mul_assoc]
      exact (S.norm_incl_apply_le h _).trans (mul_le_mul_of_nonneg_left
        (P.norm_π_apply_le_of_mem_cycles h (H.total.harmonic_le_cycles ()
          (Hm.sub_mem x.2 y.2))) hC)
    have hd : dist x y = ‖z‖ := by rw [dist_eq_norm]; rfl
    rw [e, hd]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sub_le _ _).trans ?_))
    linarith
  have hev := (isCompact_closedBall (0 : Hm) 1).eventually_forall_le_of_lipschitz hB hlip
    (fun x => happ x x.2) (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hev] with h hh q hq hq0
  have hq' : 0 < ‖q‖ := norm_pos_iff.2 hq0
  set c : 𝕜 := ((‖q‖⁻¹ : ℝ) : 𝕜)
  have hr : c • (⟨q, hq⟩ : Hm) ∈ Metric.closedBall (0 : Hm) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm]
    exact (inv_mul_cancel₀ hq'.ne').le
  have h1 := hh _ hr
  have e : q - S.incl h (P.π h q) = ((‖q‖ : ℝ) : 𝕜) •
      ((((c • (⟨q, hq⟩ : Hm)) : Hm) : PiLp 2 W) - S.incl h (P.π h (c • (⟨q, hq⟩ : Hm) : Hm))) := by
    rw [Submodule.coe_smul, _root_.map_smul, _root_.map_smul, ← smul_sub, smul_smul,
      ← RCLike.ofReal_mul, mul_inv_cancel₀ hq'.ne', RCLike.ofReal_one, one_smul]
  rw [e, norm_smul, RCLike.norm_ofReal, abs_norm]
  nlinarith

end CochainProj

namespace IsCochain

variable (hi : S.IsCochain)
include hi

/-- **Eventual isomorphisms on cohomology**: under closed range, with `ℌ` finite-dimensional and
`iₕ πₕ q → q` on `ℌ`, the maps `[z] ↦ [πₕ z]` are eventually bijective. [HolstStern2012], Cor 3.4 -/
theorem eventually_bijective_cohomologyMap {Cπ : ℝ} (P : S.CochainProj Cπ)
    (hcr : ∀ i, H.ClosedRangeAt i) [FiniteDimensional 𝕜 (H.total.harmonic ())] {l : Filter κ}
    (happ : ∀ q ∈ H.total.harmonic (), Tendsto (fun h => ‖q - S.incl h (P.π h q)‖) l (𝓝 0)) :
    ∀ᶠ h in l, Function.Bijective (P.cohomologyMap h) :=
  (P.eventually_norm_sub_incl_π_lt happ).mono fun h hh =>
    ⟨hi.cohomologyMap_injective P hcr h hh, hi.cohomologyMap_surjective P h⟩

end IsCochain

end ApproxComplexCrime.Family

/-! ### Instances -/

theorem ApproxComplex.Family.isCochain_toCrimeFamily {H : HilbertComplex 𝕜 c W} {κ : Type*}
    (S : ApproxComplex.Family.{u} H κ) : S.toCrimeFamily.IsCochain :=
  ⟨S.inclL_mem, fun h v => (S.inclL_D h v).symm⟩

namespace ConstrainedFEEC

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ) {C : ℝ} (hC : 0 ≤ C)
  (hb : ∀ h i x, ‖(F.π h).π i x‖ ≤ C * ‖x‖)

/-- The total cochain projection `Πₕ x = (πₕⁱ xⁱ)ᵢ`, valued in `Xₕ = ∏ Vₕⁱ`, bounded by `C`. -/
def totalπ (h : κ) : PiLp 2 W →L[𝕜] PiLp 2 (F.toFamily.V h) :=
  LinearMap.mkContinuous
    { toFun := fun x => WithLp.toLp 2 fun i => ⟨(F.π h).π i (x i), (F.π h).mem i _⟩
      map_add' := fun v w => PiLp.ext fun i => Subtype.ext (by
        change (F.π h).π i ((v + w) i) = (F.π h).π i (v i) + (F.π h).π i (w i)
        rw [PiLp.add_apply, _root_.map_add])
      map_smul' := fun a v => PiLp.ext fun i => Subtype.ext (by
        change (F.π h).π i ((a • v) i) = a • (F.π h).π i (v i)
        rw [PiLp.smul_apply, _root_.map_smul]) }
    C fun x => norm_piLp_le_of_le hC fun i => hb h i (x i)

theorem inclL_totalπ (h : κ) (x : PiLp 2 W) :
    F.toFamily.inclL h (F.totalπ hC hb h x) = F.piProj h x :=
  rfl

/-- The total cochain projections of a subcomplex family bounded in `W`. -/
def cochainProj : F.toCrime.toFamily.CochainProj C :=
  .ofNormLe (F.totalπ hC hb) (fun h v => PiLp.ext fun i => Subtype.ext
    ((F.π h).proj i _ ((show PiLp 2 (F.toFamily.V h) from v) i).2)) hC
    (fun h => LinearMap.mkContinuous_norm_le _ hC _) fun h z => by
    have inj : Function.Injective (F.toFamily.inclL h) := fun a b e => by
      rw [← F.toFamily.projL_inclL h a, e, F.toFamily.projL_inclL]
    apply inj
    change F.toFamily.inclL h (F.totalπ hC hb h (H.totalD z)) =
      F.toFamily.inclL h (F.toFamily.D h (F.totalπ hC hb h z))
    rw [inclL_totalπ, F.toFamily.inclL_D, ← F.totalD_piProj]
    rfl

include hC hb in
theorem toCrime_isPoincare (hcr : ∀ i, H.ClosedRangeAt i) :
    ∃ cP, 1 ≤ cP ∧ F.toCrime.toFamily.IsPoincare cP := by
  obtain ⟨c₀, hc₀⟩ := H.exists_poincare_totalD hcr
  have h := (F.toComplex.toFamily.isCochain_toCrimeFamily).isPoincare (F.cochainProj hC hb)
    hc₀
  exact ⟨_, le_max_right _ 1, h.mono (le_max_left _ _)⟩

end ConstrainedFEEC

end Feec.HilbertComplex
