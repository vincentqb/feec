module

public import Feec.HilbertComplex.Approximation.StaticCrime

/-!
# The static theory with cochain reading maps

The static FEEC theorem with variational crimes (`Feec.HilbertComplex.Approximation.StaticCrime`)
in the setting of [HolstStern2012], §3: the reading maps `iₕ : Xₕ → W` are **cochain maps**
(`iₕ Xₕ ⊆ D(𝐝)`, `𝐝 iₕ = iₕ 𝐝ₕ`; `ApproxComplexCrime.Family.IsCochain`), not necessarily
isometric, and there are uniformly bounded **cochain projections** `πₕ : W → Xₕ` (`πₕ iₕ = 1`,
`πₕ 𝐝 = 𝐝ₕ πₕ` on `D(𝐝)`, `‖πₕ‖ ≤ C_π`; `ApproxComplexCrime.Family.CochainProj`). The `πₕ` are
analysis data only: the discrete problem has the load `iₕ* f`, and they need not be the left
inverses of the family (for a conforming family those are the orthogonal projections). Bounds in
`W` are a strengthening of the `V`-bounds of [HolstStern2012], §3.3 (as for the smoothed
projections of [AFW2010], §5.5).

In this setting every hypothesis of the static theorem with crimes beyond the inner-product
defect and best approximation is derived: the cochain defects vanish, the uniform discrete
Poincaré inequality holds, and the harmonic defect `sup |⟪iₕ q, u⟫| / ‖q‖` over the discrete
harmonic forms is bounded by the approximation of `P_𝔷 u` and the inner-product defect. So the
error estimate needs no assumed defect, and the method converges for every datum as soon as
`‖1 - Jₕ‖ → 0` and `iₕ πₕ → 1` pointwise.

## Main results

* `ApproxComplexCrime.Family.IsCochain.cochainDefect_eq_zero`: the cochain defect vanishes.
* `ApproxComplexCrime.Family.IsCochain.isPoincare`: **the uniform discrete Poincaré inequality**
  with `c_P = c₀ C_π C` ([HolstStern2012], Thm 3.5: `c_P ‖πₕ‖ ‖iₕ‖`, there with the `V`-norm of
  `πₕ`).
* `ApproxComplexCrime.Family.IsCochain.norm_inner_incl_harmonic_le`: **the harmonic defect**: for
  `u ⊥ ℌ` and a discrete harmonic form `q`,
  `|⟪iₕ q, u⟫| ≤ (C ‖b - iₕ πₕ b‖ + C_π ‖1 - Jₕ‖ ‖u‖) ‖q‖`, `b = P_𝔷 u` (which lies in `cl 𝔅`).
* `ApproxComplexCrime.Family.IsCochain.norm_sub_incl_harmonic_le`: **the gap from `ℌ` to
  `iₕ ℌₕ`**: `‖p - iₕ P_ℌₕ πₕ p‖ ≤ (1 + C²) ‖p - iₕ πₕ p‖ + C C_π ‖1 - Jₕ‖ ‖p‖` for `p ∈ ℌ`
  (for subcomplexes, `Jₕ = 1`, cf. [AFW2010], Thm 3.5).
* `ApproxComplexCrime.Family.IsCochain.staticError_le`: **the error estimate**
  `e(f) ≤ E + 240 C c_P² (5 ‖1 - Jₕ‖ ‖x̃‖ + C E + C ‖b - iₕ πₕ b‖ + C_π ‖1 - Jₕ‖ ‖u‖)`, `E` the
  read error of any discrete triple `x̃`, `u = G f`, `b = P_𝔷 u`: best approximation, the
  inner-product defect, and the approximation of `P_𝔷 u` (cf. [HolstStern2012], Cor 3.11, whose
  harmonic term is `μ inf ‖P_𝔅 u - v‖`, here without the factor `μ`).
* `ApproxComplexCrime.Family.IsCochain.tendsto_staticError`: **convergence for every datum**
  from `‖1 - Jₕ‖ → 0` and `‖x - iₕ πₕ x‖ → 0` for every `x` (the approximants are
  `(πₕ σ, πₕ u, P_ℌₕ πₕ p)`).
* `ApproxComplexCrime.Family.IsCochain.cohomologyEquiv`: **the isomorphism on cohomology**
  `H(𝐝) ≃ H(𝐝ₕ)` induced by `πₕ` (`CochainProj.cohomologyMap`; onto always,
  `cohomologyMap_surjective`; one-to-one under closed range and the strict gap
  `‖q - iₕ πₕ q‖ < ‖q‖` on `ℌ \ 0`, `cohomologyMap_injective`; [HolstStern2012], Thm 3.3 and,
  under closed range, Cor 3.4).
* The instances: `ApproxComplex.Family.isCochain_toCrimeFamily` (cochain reading maps of graded
  discrete complexes), `ConstrainedFEEC.cochainProj` (the total cochain projection of a
  subcomplex family with projections bounded in `W`), `ConstrainedFEEC.toCrime_isPoincare`.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (Thm 3.3, Cor 3.4, Thm 3.5, Cor 3.11)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.5 (the gap between harmonic forms), §5.5 (bounded smoothed projections)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `x ≤ a + b` from `x² = a² + b²`. -/
private theorem le_add_of_sq_eq {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (e : x ^ 2 = a ^ 2 + b ^ 2) : x ≤ a + b := by
  nlinarith [mul_nonneg ha hb]

/-- `x ≤ a + b + c` from `x² = a² + b² + c²`. -/
private theorem le_add_add_of_sq_eq {x a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : x ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) : x ≤ a + b + c := by
  nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι}
  {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)]

namespace ApproxComplexCrime.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplexCrime.Family.{u} H κ)

/-- **The reading maps are cochain maps**: `iₕ Xₕ ⊆ D(𝐝)` and `𝐝 iₕ = iₕ 𝐝ₕ` (the morphisms
`iₕ` of [HolstStern2012], §3.1, on the total complexes). -/
structure IsCochain : Prop where
  incl_mem : ∀ h v, S.incl h v ∈ H.totalD.domain
  totalD_incl : ∀ h v, H.totalD ⟨S.incl h v, incl_mem h v⟩ = S.incl h (S.D h v)

/-- **Cochain projections bounded by `C_π`**: left inverses `πₕ : W → Xₕ` of the reading maps
(`πₕ iₕ = 1`) with `πₕ 𝐝 = 𝐝ₕ πₕ` on `D(𝐝)` and `‖πₕ‖ ≤ C_π` (the projection morphisms of
[HolstStern2012], §3.1, bounded in `W`). -/
structure CochainProj (Cπ : ℝ) where
  /-- the projections -/
  π : ∀ h, PiLp 2 W →L[𝕜] S.X h
  π_incl : ∀ h v, π h (S.incl h v) = v
  norm_π_le : ∀ h, ‖π h‖ ≤ Cπ
  π_totalD : ∀ h (z : H.totalD.domain), π h (H.totalD z) = S.D h (π h z)

variable {S}

namespace CochainProj

variable {Cπ : ℝ} (P : S.CochainProj Cπ)

include P in
/-- `C_π ≥ 0` (as soon as there is a level). -/
theorem nonneg (h : κ) : 0 ≤ Cπ := (norm_nonneg _).trans (P.norm_π_le h)

/-- `‖πₕ x‖ ≤ C_π ‖x‖`. -/
theorem norm_π_apply_le (h : κ) (x : PiLp 2 W) : ‖P.π h x‖ ≤ Cπ * ‖x‖ :=
  ((P.π h).le_opNorm x).trans (mul_le_mul_of_nonneg_right (P.norm_π_le h) (norm_nonneg _))

/-- `πₕ` maps `cl 𝔅` into `𝔅ₕ = range 𝐝ₕ` (closed: `Xₕ` is finite-dimensional). -/
theorem mem_range_of_mem_closure (h : κ) {b : PiLp 2 W}
    (hb : b ∈ (H.total.boundaries ()).topologicalClosure) :
    P.π h b ∈ LinearMap.range (S.D h : S.X h →ₗ[𝕜] S.X h) := by
  have hle : H.total.boundaries () ≤
      (LinearMap.range (S.D h : S.X h →ₗ[𝕜] S.X h)).comap (P.π h : PiLp 2 W →ₗ[𝕜] S.X h) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨P.π h z, (P.π_totalD h z).symm⟩
  exact Submodule.topologicalClosure_minimal _ hle
    ((Submodule.closed_of_finiteDimensional _).preimage (P.π h).continuous) hb

end CochainProj

namespace IsCochain

variable (hi : S.IsCochain)
include hi

/-- **Cochain reading maps have no cochain defect.** -/
theorem cochainDefect_eq_zero (h : κ) (y : H.wave.domain) : S.cochainDefect h y = 0 :=
  S.cochainDefect_eq_zero h (hi.incl_mem h) (hi.totalD_incl h) y

/-- `iₕ` maps the discrete cycles into the cycles. -/
theorem incl_mem_cycles (h : κ) {v : S.X h} (hv : S.D h v = 0) :
    S.incl h v ∈ H.total.cycles () :=
  show S.incl h v ∈ H.totalD.ker from
    LinearPMap.mem_ker_iff.2 ⟨⟨S.incl h v, hi.incl_mem h v⟩, rfl, by
      rw [hi.totalD_incl, hv, _root_.map_zero]⟩

/-- `iₕ` maps `cl 𝔅ₕ` into `cl 𝔅`. -/
theorem incl_mem_closure (h : κ) {β : S.X h}
    (hβ : β ∈ ((S.cpx h).boundaries ()).topologicalClosure) :
    S.incl h β ∈ (H.total.boundaries ()).topologicalClosure := by
  have hle : (S.cpx h).boundaries () ≤ (H.total.boundaries ()).topologicalClosure.comap
      (S.incl h : S.X h →ₗ[𝕜] PiLp 2 W) := by
    rintro _ ⟨w, rfl⟩
    exact Submodule.le_topologicalClosure _ ⟨⟨S.incl h w, hi.incl_mem h w⟩, hi.totalD_incl h w⟩
  exact Submodule.topologicalClosure_minimal _ hle
    ((H.total.boundaries ()).isClosed_topologicalClosure.preimage (S.incl h).continuous) hβ

/-- **The uniform discrete Poincaré inequality from bounded cochain projections**: if `𝐝` has the
Poincaré constant `c₀` on `(ker 𝐝)ᗮ`, then `‖v‖ ≤ c₀ C_π C ‖𝐝ₕ v‖` on `(ker 𝐝ₕ)ᗮ`, `C` the bound
of the reading maps. [HolstStern2012], Thm 3.5 (there `‖πₕ‖` is the `V`-norm, and `πₕ` need not
be bounded in `W`) -/
theorem isPoincare {Cπ : ℝ} (P : S.CochainProj Cπ) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc : ∀ z : H.totalD.domain, (z : PiLp 2 W) ∈ H.totalD.kerᗮ →
      ‖(z : PiLp 2 W)‖ ≤ c₀ * ‖H.totalD z‖) :
    S.IsPoincare (c₀ * Cπ * S.boundConst) :=
  S.isPoincare_of_proj hc₀ hc hi.incl_mem
    (fun h v => by rw [hi.totalD_incl]; exact S.norm_incl_apply_le h _) P.π P.π_incl P.norm_π_le
    fun h z hz => by rw [← P.π_totalD, hz, _root_.map_zero]

/-- **The harmonic defect of cochain reading maps**: for `u ⊥ ℌ`, `b = P_𝔷 u` and a discrete
harmonic form `q`, `|⟪iₕ q, u⟫| ≤ (C ‖b - iₕ πₕ b‖ + C_π ‖1 - Jₕ‖ ‖u‖) ‖q‖`. Indeed
`iₕ q ∈ 𝔷`, so `⟪iₕ q, u⟫ = ⟪iₕ q, b⟫`; `b ∈ cl 𝔅`, so `πₕ b ∈ 𝔅ₕ ⊥ q`, and
`⟪iₕ q, iₕ πₕ b⟫ = -⟪(1 - Jₕ) q, πₕ b⟫`. -/
theorem norm_inner_incl_harmonic_le {Cπ : ℝ} (P : S.CochainProj Cπ) (h : κ) {u : PiLp 2 W}
    (hu : u ∈ (H.total.harmonic ())ᗮ) {q : S.X h} (hq : q ∈ (S.cpx h).harmonic ()) :
    ‖⟪S.incl h q, u⟫_𝕜‖ ≤ (S.boundConst * ‖(H.total.cycles ()).starProjection u -
        S.incl h (P.π h ((H.total.cycles ()).starProjection u))‖ +
      Cπ * ‖1 - S.J h‖ * ‖u‖) * ‖q‖ := by
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
  obtain ⟨w, hw⟩ := P.mem_range_of_mem_closure h
    (H.total.mem_closure_boundaries_of_mem_cycles (K.starProjection_apply_mem u) hbo)
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
  rw [e3]
  have hCπ := P.nonneg h
  have t1 : ‖⟪S.incl h q, b - S.incl h (P.π h b)⟫_𝕜‖ ≤
      S.boundConst * ‖q‖ * ‖b - S.incl h (P.π h b)‖ :=
    (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (S.norm_incl_apply_le h q) (norm_nonneg _))
  have t2 : ‖⟪(1 - S.J h) q, P.π h b⟫_𝕜‖ ≤ ‖1 - S.J h‖ * ‖q‖ * (Cπ * ‖u‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul ((1 - S.J h).le_opNorm q)
      ((P.norm_π_apply_le h b).trans
        (mul_le_mul_of_nonneg_left (K.norm_starProjection_apply_le u) hCπ))
      (norm_nonneg _) (by positivity))
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add t1 t2
    _ = _ := by ring

/-- **The gap from the harmonic forms to the read discrete harmonic forms**: for `p ∈ ℌ`,
`‖p - iₕ P_ℌₕ πₕ p‖ ≤ (1 + C²) ‖p - iₕ πₕ p‖ + C C_π ‖1 - Jₕ‖ ‖p‖`. With `β = πₕ p - P_ℌₕ πₕ p`
(in `cl 𝔅ₕ`, so `iₕ β ⊥ p`): `‖β‖² = ⟪iₕ β, iₕ πₕ p - p⟫ + ⟪(1 - Jₕ) β, πₕ p⟫`. For
subcomplexes (`Jₕ = 1`) cf. [AFW2010], Thm 3.5. -/
theorem norm_sub_incl_harmonic_le {Cπ : ℝ} (P : S.CochainProj Cπ) (h : κ) {p : PiLp 2 W}
    (hp : p ∈ H.total.harmonic ()) :
    ‖p - S.incl h (((S.cpx h).harmonic ()).starProjection (P.π h p))‖ ≤
      (1 + S.boundConst ^ 2) * ‖p - S.incl h (P.π h p)‖ +
        S.boundConst * Cπ * ‖1 - S.J h‖ * ‖p‖ := by
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
  have hCπ := P.nonneg h
  have hβle : ‖β‖ ≤ S.boundConst * ‖p - S.incl h a‖ + Cπ * ‖1 - S.J h‖ * ‖p‖ := by
    have t1 : ‖⟪S.incl h β, S.incl h a - p⟫_𝕜‖ ≤ S.boundConst * ‖β‖ * ‖p - S.incl h a‖ :=
      (norm_inner_le_norm _ _).trans (by
        rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_right (S.norm_incl_apply_le h β)
          (norm_nonneg _))
    have t2 : ‖⟪(1 - S.J h) β, a⟫_𝕜‖ ≤ ‖1 - S.J h‖ * ‖β‖ * (Cπ * ‖p‖) :=
      (norm_inner_le_norm _ _).trans (mul_le_mul ((1 - S.J h).le_opNorm β)
        (P.norm_π_apply_le h p) (norm_nonneg _) (by positivity))
    have h1 : ‖β‖ * ‖β‖ ≤ ‖β‖ * (S.boundConst * ‖p - S.incl h a‖ + Cπ * ‖1 - S.J h‖ * ‖p‖) := by
      have hre : ‖β‖ * ‖β‖ = RCLike.re ⟪β, β⟫_𝕜 := by
        rw [← pow_two, @norm_sq_eq_re_inner 𝕜]
      rw [hre, e]
      refine (RCLike.re_le_norm _).trans ((norm_add_le _ _).trans ((add_le_add t1 t2).trans
        (le_of_eq ?_)))
      ring
    rcases (norm_nonneg β).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · exact le_of_mul_le_mul_left h1 hpos
  have e' : p - S.incl h (Kh.starProjection a) = (p - S.incl h a) + S.incl h β := by
    simp only [β, _root_.map_sub]; abel
  rw [e']
  calc _ ≤ ‖p - S.incl h a‖ + S.boundConst * ‖β‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (S.norm_incl_apply_le h β))
    _ ≤ ‖p - S.incl h a‖ + S.boundConst *
        (S.boundConst * ‖p - S.incl h a‖ + Cπ * ‖1 - S.J h‖ * ‖p‖) := by gcongr
    _ = _ := by ring

variable (hcr : ∀ i, H.ClosedRangeAt i)

/-- **The error estimate with cochain reading maps**: for every discrete triple `x̃`,
`e(f) ≤ E + 240 C c_P² (5 ‖1 - Jₕ‖ ‖x̃‖ + C E + C ‖b - iₕ πₕ b‖ + C_π ‖1 - Jₕ‖ ‖u‖)`, `E` the
read error of `x̃`, `u = G f` and `b = P_𝔷 u`: no cochain defect, and the harmonic defect bounded
by `norm_inner_incl_harmonic_le` (cf. [HolstStern2012], Cor 3.11). -/
theorem staticError_le {Cπ : ℝ} (P : S.CochainProj Cπ) {cP : ℝ} (hP : S.IsPoincare cP)
    (hcP : 1 ≤ cP) (h : κ) (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) :
    S.staticError hcr h f ≤ S.readError h (H.totalMixedSolution hcr f) x +
      240 * S.boundConst * cP ^ 2 * (5 * ‖1 - S.J h‖ * ‖x‖ +
        S.boundConst * S.readError h (H.totalMixedSolution hcr f) x +
        (S.boundConst * ‖(H.total.cycles ()).starProjection (H.greenOp hcr f) -
            S.incl h (P.π h ((H.total.cycles ()).starProjection (H.greenOp hcr f)))‖ +
          Cπ * ‖1 - S.J h‖ * ‖H.greenOp hcr f‖)) := by
  have hCπ := P.nonneg h
  have hη0 : 0 ≤ S.boundConst * ‖(H.total.cycles ()).starProjection (H.greenOp hcr f) -
      S.incl h (P.π h ((H.total.cycles ()).starProjection (H.greenOp hcr f)))‖ +
      Cπ * ‖1 - S.J h‖ * ‖H.greenOp hcr f‖ :=
    add_nonneg (mul_nonneg S.boundConst_nonneg (norm_nonneg _))
      (mul_nonneg (mul_nonneg hCπ (norm_nonneg _)) (norm_nonneg _))
  have := S.staticError_le_of_split hcr hP hcP h f x le_rfl le_rfl hη0
    (fun v => by rw [hi.cochainDefect_eq_zero, inner_zero_left, norm_zero, zero_mul])
    (fun v => by rw [hi.cochainDefect_eq_zero, inner_zero_left, norm_zero, zero_mul])
    (fun q hq => hi.norm_inner_incl_harmonic_le P h
      (H.greenOp_mem_orthogonal_harmonic hcr f) hq)
  simpa only [add_zero] using this

/-- **Convergence with cochain reading maps**: under the uniform discrete Poincaré inequality, if
the inner-product defect tends to `0` and `iₕ πₕ x → x` for every `x`, the static error tends to
`0` for every datum. The approximants are `(πₕ σ, πₕ u, P_ℌₕ πₕ p)`: their read error is the
approximation error `‖x - iₕ πₕ x‖` at `σ`, `𝐝 σ`, `u`, `𝐝 u` (`𝐝ₕ πₕ = πₕ 𝐝`) plus the
harmonic gap at `p` (`norm_sub_incl_harmonic_le`), and the harmonic defect is bounded by
`norm_inner_incl_harmonic_le`. Cf. [HolstStern2012], Cor 3.11 -/
theorem tendsto_staticError {Cπ : ℝ} (P : S.CochainProj Cπ) {cP : ℝ} (hP : S.IsPoincare cP)
    (hcP : 1 ≤ cP) {l : Filter κ} (hJ : Tendsto (fun h => ‖1 - S.J h‖) l (𝓝 0))
    (happ : ∀ x, Tendsto (fun h => ‖x - S.incl h (P.π h x)‖) l (𝓝 0)) (f : PiLp 2 W) :
    Tendsto (fun h => S.staticError hcr h f) l (𝓝 0) := by
  set X := H.totalMixedSolution hcr f
  set σ : H.totalD.domain := H.total.domainCoord () () X.fst
  set υ : H.totalD.domain := H.total.domainCoord () () X.snd.fst
  set p : PiLp 2 W := (X.snd.snd : PiLp 2 W)
  have hp : p ∈ H.total.harmonic () := X.snd.snd.2
  set b := (H.total.cycles ()).starProjection (H.greenOp hcr f)
  set g : PiLp 2 W := H.greenOp hcr f
  set C := S.boundConst
  -- the approximants
  let xa : ∀ h, (S.cpx h).MixedSpace () () := fun h =>
    MixedSpace.mk (toDom (S.D h) (S.D_D h) (P.π h σ)) (toDom (S.D h) (S.D_D h) (P.π h υ))
      ⟨((S.cpx h).harmonic ()).starProjection (P.π h p),
        ((S.cpx h).harmonic ()).starProjection_apply_mem _⟩
  -- the bound of the read error and of the harmonic defect
  set T : κ → ℝ := fun h => ‖(σ : PiLp 2 W) - S.incl h (P.π h σ)‖ +
    ‖H.totalD σ - S.incl h (P.π h (H.totalD σ))‖ + ‖(υ : PiLp 2 W) - S.incl h (P.π h υ)‖ +
    ‖H.totalD υ - S.incl h (P.π h (H.totalD υ))‖ +
    ((1 + C ^ 2) * ‖p - S.incl h (P.π h p)‖ + C * Cπ * ‖1 - S.J h‖ * ‖p‖) +
    (C * ‖b - S.incl h (P.π h b)‖ + Cπ * ‖1 - S.J h‖ * ‖g‖)
  have hT : Tendsto T l (𝓝 0) := by
    have := ((((happ σ).add (happ (H.totalD σ))).add (happ υ)).add (happ (H.totalD υ))).add
      ((((happ p).const_mul (1 + C ^ 2)).add (((hJ.const_mul (C * Cπ)).mul_const ‖p‖))).add
        (((happ b).const_mul C).add ((hJ.const_mul Cπ).mul_const ‖g‖)))
    simp only [mul_zero, zero_mul, add_zero] at this
    refine this.congr fun h => ?_
    simp only [T, mul_assoc, add_assoc]
  have hreadT : ∀ h, S.readError h X (xa h) ≤ T h := fun h => by
    have hgap := hi.norm_sub_incl_harmonic_le P h hp
    have e : S.readError h X (xa h) = ‖(σ : PiLp 2 W) - S.incl h (P.π h σ)‖ +
        ‖H.totalD σ - S.incl h (S.D h (P.π h σ))‖ + ‖(υ : PiLp 2 W) - S.incl h (P.π h υ)‖ +
        ‖H.totalD υ - S.incl h (S.D h (P.π h υ))‖ +
        ‖p - S.incl h (((S.cpx h).harmonic ()).starProjection (P.π h p))‖ := rfl
    rw [e, ← P.π_totalD, ← P.π_totalD]
    have h0 : 0 ≤ C * ‖b - S.incl h (P.π h b)‖ + Cπ * ‖1 - S.J h‖ * ‖g‖ :=
      add_nonneg (mul_nonneg S.boundConst_nonneg (norm_nonneg _))
        (mul_nonneg (mul_nonneg (P.nonneg h) (norm_nonneg _)) (norm_nonneg _))
    simp only [T]
    linarith
  set M := ‖(σ : PiLp 2 W)‖ + ‖H.totalD σ‖ + (‖(υ : PiLp 2 W)‖ + ‖H.totalD υ‖) + ‖p‖
  have hnorm : ∀ h, ‖xa h‖ ≤ Cπ * M := fun h => by
    have hCπ := P.nonneg h
    have hdom : ∀ z : H.totalD.domain,
        ‖toDom (S.D h) (S.D_D h) (P.π h z)‖ ≤ Cπ * (‖(z : PiLp 2 W)‖ + ‖H.totalD z‖) := by
      intro z
      have e : ‖toDom (S.D h) (S.D_D h) (P.π h z)‖ ^ 2 =
          ‖P.π h z‖ ^ 2 + ‖S.D h (P.π h z)‖ ^ 2 :=
        (S.cpx h).norm_sq_domainSpace () _
      refine (le_add_of_sq_eq (norm_nonneg _) (norm_nonneg _) e).trans ?_
      rw [← P.π_totalD, mul_add]
      exact add_le_add (P.norm_π_apply_le h _) (P.norm_π_apply_le h _)
    have e := MixedSpace.norm_sq (xa h)
    refine (le_add_add_of_sq_eq (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) e).trans ?_
    have h3 : ‖(((xa h).snd.snd : S.X h))‖ ≤ Cπ * ‖p‖ :=
      (Submodule.norm_starProjection_apply_le _ _).trans (P.norm_π_apply_le h p)
    have h1 := hdom σ
    have h2 := hdom υ
    change ‖toDom (S.D h) (S.D_D h) (P.π h σ)‖ + ‖toDom (S.D h) (S.D_D h) (P.π h υ)‖ +
      ‖(((xa h).snd.snd : S.X h))‖ ≤ Cπ * M
    simp only [M]
    nlinarith
  refine (S.staticConsistent_iff_tendsto hcr hP hcP l f).1
    (S.staticConsistent_of_split hcr hJ (B := Cπ * M) f fun ε hε => ?_)
  filter_upwards [(tendsto_order.1 hT).2 ε hε] with h hh
  have hCπ := P.nonneg h
  have hη : C * ‖b - S.incl h (P.π h b)‖ + Cπ * ‖1 - S.J h‖ * ‖g‖ ≤ T h := by
    have hC := S.boundConst_nonneg
    have : 0 ≤ C * Cπ * ‖1 - S.J h‖ * ‖p‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg hC hCπ) (norm_nonneg _)) (norm_nonneg _)
    have : 0 ≤ (1 + C ^ 2) * ‖p - S.incl h (P.π h p)‖ := by positivity
    have := norm_nonneg ((σ : PiLp 2 W) - S.incl h (P.π h σ))
    have := norm_nonneg (H.totalD σ - S.incl h (P.π h (H.totalD σ)))
    have := norm_nonneg ((υ : PiLp 2 W) - S.incl h (P.π h υ))
    have := norm_nonneg (H.totalD υ - S.incl h (P.π h (H.totalD υ)))
    simp only [T]; linarith
  refine ⟨xa h, hnorm h, (hreadT h).trans hh.le,
    fun v => by rw [hi.cochainDefect_eq_zero, inner_zero_left, norm_zero]; positivity,
    fun v => by rw [hi.cochainDefect_eq_zero, inner_zero_left, norm_zero]; positivity,
    fun q hq => (hi.norm_inner_incl_harmonic_le P h
      (H.greenOp_mem_orthogonal_harmonic hcr f) hq).trans
      (mul_le_mul_of_nonneg_right (hη.trans hh.le) (norm_nonneg _))⟩

end IsCochain

/-! ### Cohomology -/

namespace CochainProj

variable {Cπ : ℝ} (P : S.CochainProj Cπ)

/-- `πₕ` on the cycles, valued in the discrete cycles. -/
def cyclesMap (h : κ) : H.total.cycles () →ₗ[𝕜] (S.cpx h).cycles () :=
  (P.π h : PiLp 2 W →ₗ[𝕜] S.X h).restrict fun z hz => by
    obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hz
    rw [diffComplex_cycles, hy]
    exact LinearMap.mem_ker.2
      ((P.π_totalD h y).symm.trans ((congrArg (P.π h) hy0).trans (_root_.map_zero _)))

/-- **The map induced on cohomology** `H(𝐝) → H(𝐝ₕ)`, `[z] ↦ [πₕ z]`. [HolstStern2012], §3.1 -/
def cohomologyMap (h : κ) : H.total.cohomology () →ₗ[𝕜] (S.cpx h).cohomology () :=
  Submodule.mapQ _ _ (P.cyclesMap h) fun z hz => by
    obtain ⟨w, hw⟩ := hz
    exact ⟨⟨P.π h w, Submodule.mem_top⟩,
      (P.π_totalD h w).symm.trans (congrArg (P.π h) hw)⟩

end CochainProj

namespace IsCochain

variable (hi : S.IsCochain)
include hi

/-- **The induced map on cohomology is onto**: a discrete cycle `z` is `πₕ` of the cycle
`iₕ z`. [HolstStern2012], §3.1 -/
theorem cohomologyMap_surjective {Cπ : ℝ} (P : S.CochainProj Cπ) (h : κ) :
    Function.Surjective (P.cohomologyMap h) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hx : S.D h x = 0 := LinearMap.mem_ker.1 ((diffComplex_cycles _ _ ()).le x.2)
  refine ⟨Submodule.Quotient.mk ⟨S.incl h x, hi.incl_mem_cycles h hx⟩, ?_⟩
  rw [CochainProj.cohomologyMap, Submodule.mapQ_apply]
  exact congrArg _ (Subtype.ext (P.π_incl h x))

/-- **The induced map on cohomology is one-to-one** under closed range and the strict gap
`‖q - iₕ πₕ q‖ < ‖q‖` on `ℌ \ 0`: write a cycle `z = b + q`, `b ∈ 𝔅`, `q ∈ ℌ`; if
`πₕ z ∈ 𝔅ₕ` then `πₕ q ∈ 𝔅ₕ`, so `iₕ πₕ q ∈ 𝔅 ⊥ q`, and the gap forces `q = 0`.
[HolstStern2012], Thm 3.3 (reduced cohomology, no closed range) and Cor 3.4 (closed complexes) -/
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

/-- **Cochain reading maps and projections induce an isomorphism on cohomology**
`H(𝐝) ≃ H(𝐝ₕ)` under closed range and the strict gap `‖q - iₕ πₕ q‖ < ‖q‖` on `ℌ \ 0`.
[HolstStern2012], Thm 3.3, Cor 3.4 -/
def cohomologyEquiv {Cπ : ℝ} (P : S.CochainProj Cπ) (hcr : ∀ i, H.ClosedRangeAt i) (h : κ)
    (hgap : ∀ q ∈ H.total.harmonic (), q ≠ 0 → ‖q - S.incl h (P.π h q)‖ < ‖q‖) :
    H.total.cohomology () ≃ₗ[𝕜] (S.cpx h).cohomology () :=
  LinearEquiv.ofBijective _
    ⟨hi.cohomologyMap_injective P hcr h hgap, hi.cohomologyMap_surjective P h⟩

end IsCochain

end ApproxComplexCrime.Family

/-! ### Instances -/

/-- **Cochain reading maps of graded discrete complexes are cochain maps of the total
complexes.** -/
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

/-- **The total cochain projections of a subcomplex family bounded in `W`** are cochain
projections of the family with zero defects `F.toCrime`. -/
def cochainProj : F.toCrime.toFamily.CochainProj C where
  π := F.totalπ hC hb
  π_incl h v := PiLp.ext fun i => Subtype.ext
    ((F.π h).proj i _ ((show PiLp 2 (F.toFamily.V h) from v) i).2)
  norm_π_le h := LinearMap.mkContinuous_norm_le _ hC _
  π_totalD h z := by
    have inj : Function.Injective (F.toFamily.inclL h) := fun a b e => by
      rw [← F.toFamily.projL_inclL h a, e, F.toFamily.projL_inclL]
    apply inj
    change F.toFamily.inclL h (F.totalπ hC hb h (H.totalD z)) =
      F.toFamily.inclL h (F.toFamily.D h (F.totalπ hC hb h z))
    rw [inclL_totalπ, F.toFamily.inclL_D, ← F.totalD_piProj]
    rfl

include hC hb in
/-- **The conforming case satisfies the uniform discrete Poincaré inequality**: under closed range,
for projections bounded in `W` (`ConstrainedFEEC.cochainProj`,
`ApproxComplexCrime.Family.IsCochain.isPoincare`). -/
theorem toCrime_isPoincare (hcr : ∀ i, H.ClosedRangeAt i) :
    ∃ cP, 1 ≤ cP ∧ F.toCrime.toFamily.IsPoincare cP := by
  obtain ⟨c₀, hc₀⟩ := H.exists_poincare_totalD hcr
  have h := (F.toComplex.toFamily.isCochain_toCrimeFamily).isPoincare (F.cochainProj hC hb)
    (le_max_right c₀ 0)
    (fun z hz => (hc₀ z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  exact ⟨_, le_max_right _ 1, h.mono (le_max_left _ _)⟩

end ConstrainedFEEC

end Feec.HilbertComplex
