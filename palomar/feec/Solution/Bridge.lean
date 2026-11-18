module

public import Solution.Legacy
public import Feec.HilbertComplex.Approximation.StaticFEEC
public import Feec.ForMathlib.InnerProductSpace.Basic

/-!
# The bridge from the challenge to `Feec`

The vocabulary of `Challenge.lean` restates over Mathlib the objects of `Feec`: a Hilbert complex
of the challenge is a `Feec.HilbertComplex` on `ComplexShape.up ℤ` (`HilbertComplex.toFeec`, the
same fields), and so are its subcomplexes; a cochain projection of the challenge, defined on the
domain complex only, extends linearly to `W` (`CochainProjection.extend`: continuously where it is
bounded in `W`, otherwise along an algebraic complement of `D(d)`), which is a `Feec` cochain
projection
(`CochainProjection.toFeec`). A family of subcomplexes is a `Feec.HilbertComplex.SubcomplexFamily`
(`SubcomplexFamily.toFeec`), to which the graph-norm bounds and the approximation property
transfer degree by degree. The graph norm of the challenge is the norm of `Feec`'s domain spaces
(`graphNorm_domainCoord`). This module identifies the challenge's cycles, boundaries, harmonic
forms, harmonic gaps, graph-norm distances, mixed forms and mixed solutions with those of `Feec`,
and turns the verdict of `Feec.HilbertComplex.SubcomplexFamily.staticFEEC` into the conclusions of
the challenge (`SubcomplexFamily.staticVerdict_of`), with explicit constants.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.3–§3.4

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-! ### The complex, its subcomplexes and cochain projections in `Feec` -/

/-- The complex as a `Feec` Hilbert complex on `ComplexShape.up ℤ`. -/
def toFeec : Feec.HilbertComplex 𝕜 (ComplexShape.up ℤ) W where
  d := H.d
  shape := H.shape
  dense := H.dense
  closed := H.closed
  mapsTo := H.mapsTo
  d_comp_d := H.d_comp_d

theorem rel_add_one (i : ℤ) : (ComplexShape.up ℤ).Rel i (i + 1) := rfl

theorem rel_sub_one (i : ℤ) : (ComplexShape.up ℤ).Rel (i - 1) i := sub_add_cancel i 1

theorem cycles_eq (i : ℤ) : H.toFeec.cycles i = H.cycles i :=
  H.toFeec.cycles_eq (rel_add_one i)

theorem boundaries_eq (i : ℤ) : H.toFeec.boundaries i = H.boundaries i :=
  H.toFeec.boundaries_eq (rel_sub_one i)

theorem harmonic_eq (i : ℤ) : H.toFeec.harmonic i = H.harmonic i := by
  have hp : (ComplexShape.up ℤ).prev i = i - 1 := (ComplexShape.up ℤ).prev_eq' (rel_sub_one i)
  change H.toFeec.cycles i ⊓ ((H.toFeec.d _ i)†).ker = _
  rw [cycles_eq, hp]
  rfl

theorem closedRangeAt_iff (i : ℤ) :
    H.toFeec.ClosedRangeAt i ↔ IsClosed (H.boundaries i : Set (W i)) := by
  rw [Feec.HilbertComplex.ClosedRangeAt, boundaries_eq]

/-- The coordinate `Vⁱ → D(d i k)` of `Feec`'s domain space, valued in the challenge's domain. -/
def coord (i k : ℤ) : H.toFeec.domainSpace i →ₗ[𝕜] (H.d i k).domain := H.toFeec.domainCoord i k

/-- **The graph norm is the norm of the domain space** of `Feec`. -/
theorem graphNorm_domainCoord {i k : ℤ} (hik : (ComplexShape.up ℤ).Rel i k)
    (v : H.toFeec.domainSpace i) : H.graphNorm i k (H.coord i k v) = ‖v‖ := by
  obtain rfl := (ComplexShape.up ℤ).next_eq' hik
  have e := H.toFeec.norm_sq_domainSpace i v
  change √(‖H.toFeec.domainIncl i v‖ ^ 2 + ‖H.toFeec.d i _ (H.toFeec.domainCoord i _ v)‖ ^ 2) = _
  rw [← e, Real.sqrt_sq (norm_nonneg _)]

theorem mixedNorm_domainCoord {j : ℤ} (σ : H.toFeec.domainSpace (j - 1))
    (u : H.toFeec.domainSpace j) (p : W j) :
    H.mixedNorm₃ j (H.coord (j - 1) j σ) (H.coord j (j + 1) u) p =
      ‖σ‖ + ‖u‖ + ‖p‖ := by
  unfold mixedNorm₃
  rw [H.graphNorm_domainCoord (rel_sub_one j), H.graphNorm_domainCoord (rel_add_one j)]

/-- The error of the challenge at points of `Feec`'s domain spaces is their distance there. -/
theorem mixedError_domainCoord {j : ℤ} (σ σ' : H.toFeec.domainSpace (j - 1))
    (u u' : H.toFeec.domainSpace j) (p p' : W j) :
    H.mixedError j (H.coord (j - 1) j σ) (H.coord (j - 1) j σ')
      (H.coord j (j + 1) u) (H.coord j (j + 1) u') p p' =
      ‖σ - σ'‖ + ‖u - u'‖ + ‖p - p'‖ := by
  unfold mixedError
  rw [← _root_.map_sub (H.coord (j - 1) j), ← _root_.map_sub (H.coord j (j + 1)),
    mixedNorm_domainCoord]

/-- A linear projection of `Wⁱ` onto `D(dⁱ)`, along an algebraic complement. -/
def domainProj (i : ℤ) : W i →ₗ[𝕜] (H.d i (i + 1)).domain :=
  Submodule.projectionOnto _ _ (Submodule.exists_isCompl (H.d i (i + 1)).domain).choose_spec

theorem domainProj_apply {i : ℤ} (x : (H.d i (i + 1)).domain) : H.domainProj i x = x :=
  Submodule.projectionOnto_apply_left _ x

namespace Subcomplex

variable {H} (S : H.Subcomplex)

/-- The subcomplex as a `Feec` subcomplex. -/
def toFeec : H.toFeec.Subcomplex := ⟨S.V, S.le_domain, S.mapsTo⟩

instance [∀ i, FiniteDimensional 𝕜 (S.V i)] (i : ℤ) : FiniteDimensional 𝕜 (S.toFeec.V i) :=
  ‹∀ i, FiniteDimensional 𝕜 (S.V i)› i

namespace CochainProjection

variable {S} (P : S.CochainProjection)

/-- **The cochain projection extended to `W`**: where `π` is bounded in the norm of `W` on `D(d)`
and `V` is closed, its continuous extension (`D(d)` is dense); otherwise `π` after a linear
projection onto `D(d)` along an algebraic complement (not continuous). Linear; it agrees with `π`
on `D(d)` and takes values in `V`. -/
def extend (i : ℤ) : W i →ₗ[𝕜] W i := by
  classical
  exact if hb : (∃ C, ∀ x : (H.d i (i + 1)).domain, ‖(P.π i x : W i)‖ ≤ C * ‖(x : W i)‖) ∧
      IsClosed (S.V i : Set (W i)) then
    haveI := hb.2.completeSpace_coe
    (S.V i).subtype ∘ₗ ((P.π i).extendOfNorm (H.d i (i + 1)).domain.subtype :
      W i →L[𝕜] S.V i).toLinearMap
  else (S.V i).subtype ∘ₗ P.π i ∘ₗ H.domainProj i

theorem extend_mem (i : ℤ) (x : W i) : P.extend i x ∈ S.V i := by
  unfold extend
  split_ifs with hb
  · exact Submodule.coe_mem _
  · exact Submodule.coe_mem _

theorem extend_apply {i : ℤ} (x : (H.d i (i + 1)).domain) : P.extend i x = P.π i x := by
  unfold extend
  split_ifs with hb
  · have := hb.2.completeSpace_coe
    obtain ⟨C, hC⟩ := hb.1
    change (((P.π i).extendOfNorm (H.d i (i + 1)).domain.subtype :
      W i →L[𝕜] S.V i) ((H.d i (i + 1)).domain.subtype x) : W i) = _
    rw [LinearMap.extendOfNorm_eq (H.dense i (i + 1)).denseRange_val ⟨C, fun y => hC y⟩]
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, domainProj_apply]

/-- **The continuous extension is bounded in `W`**: a bound `‖π x‖ ≤ C ‖x‖` on `D(d)` with `V`
closed gives `‖π x‖ ≤ max C 0 ‖x‖` for the extension on all of `W`. -/
theorem norm_extend_le {i : ℤ} {C : ℝ}
    (hC : ∀ x : (H.d i (i + 1)).domain, ‖(P.π i x : W i)‖ ≤ C * ‖(x : W i)‖)
    (hV : IsClosed (S.V i : Set (W i))) (x : W i) : ‖P.extend i x‖ ≤ max C 0 * ‖x‖ := by
  classical
  have hb : (∃ C, ∀ x : (H.d i (i + 1)).domain, ‖(P.π i x : W i)‖ ≤ C * ‖(x : W i)‖) ∧
      IsClosed (S.V i : Set (W i)) := ⟨⟨C, hC⟩, hV⟩
  have := hV.completeSpace_coe
  set g : W i →L[𝕜] S.V i := (P.π i).extendOfNorm (H.d i (i + 1)).domain.subtype
  have e : ∀ y, P.extend i y = g y := fun y => by
    unfold extend
    split_ifs
    rfl
  rw [e]
  have hd := (H.dense i (i + 1)).denseRange_val
  refine hd.induction_on (p := fun y => ‖(g y : W i)‖ ≤ max C 0 * ‖y‖) x
    (isClosed_le (continuous_norm.comp (continuous_subtype_val.comp g.continuous))
      (continuous_const.mul continuous_norm)) fun y => ?_
  change ‖(g ((H.d i (i + 1)).domain.subtype y) : W i)‖ ≤ _
  rw [LinearMap.extendOfNorm_eq hd ⟨C, fun z => hC z⟩]
  exact (hC y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- The extended cochain projection as a `Feec` cochain projection. -/
def toFeec : S.toFeec.CochainProjection where
  π := P.extend
  mem i x := P.extend_mem i x
  proj i x hx := (P.extend_apply ⟨x, S.le_domain i (i + 1) hx⟩).trans (P.proj i _ hx)
  comm i j x := by
    by_cases hij : i + 1 = j
    · subst hij
      have e1 : (⟨P.extend i x, S.le_domain i (i + 1) (P.extend_mem i x)⟩ :
          (H.d i (i + 1)).domain) = ⟨P.π i x, S.le_domain i (i + 1) (P.π i x).2⟩ :=
        Subtype.ext (P.extend_apply x)
      exact (congrArg (H.d i (i + 1)) e1).trans ((P.comm i x).trans
        (P.extend_apply ⟨_, H.mapsTo i (i + 1) (i + 1 + 1) x⟩).symm)
    · have h0 := H.shape i j hij
      refine (apply_eq_zero_of_eq_zero h0 _).trans ?_
      show (0 : W j) = P.extend j (H.d i j x)
      rw [apply_eq_zero_of_eq_zero h0 x, _root_.map_zero]

theorem toFeec_π_apply {i : ℤ} (x : (H.d i (i + 1)).domain) : P.toFeec.π i x = P.π i x :=
  P.extend_apply x

/-- The harmonic gap is that of `Feec`. -/
theorem harmonicGap_toFeec (j : ℤ) : P.toFeec.harmonicGap j = P.harmonicGap j := by
  unfold Feec.HilbertComplex.Subcomplex.CochainProjection.harmonicGap
    Subcomplex.CochainProjection.harmonicGap Subcomplex.CochainProjection.harmonicError
  rw [H.harmonic_eq j]
  exact iSup_congr fun q => congrArg (fun x => ‖((q : H.harmonic j) : W j) - x‖)
    (P.extend_apply ⟨_, H.harmonic_le_domain j (q : H.harmonic j).2⟩)

/-- **`πₕ` is a left inverse of the inclusion on cohomology**: `π` is the identity on `V`. -/
theorem cohomologyMap_comp_incl (j : ℤ) :
    P.cohomologyMap j ∘ₗ S.cohomologyIncl j = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, cohomologyIncl, cohomologyMap,
    Submodule.mapQ_apply, LinearMap.id_apply]
  congr 1
  exact Subtype.ext (P.proj j _ z.2.1)

/-- The map induced by `π` is bijective as soon as the one induced by the inclusion is. -/
theorem bijective_cohomologyMap {j : ℤ} (h : Function.Bijective (S.cohomologyIncl j)) :
    Function.Bijective (P.cohomologyMap j) := by
  have hl : Function.LeftInverse (P.cohomologyMap j) (S.cohomologyIncl j) := fun x =>
    LinearMap.congr_fun (P.cohomologyMap_comp_incl j) x
  exact ⟨(hl.rightInverse_of_surjective h.2).injective, hl.surjective⟩

end CochainProjection

/-- The graph-norm distance of `Feec` is at most that of the challenge. -/
theorem infDist_domainSub_le [∀ i, FiniteDimensional 𝕜 (S.V i)] {i k : ℤ}
    (hik : (ComplexShape.up ℤ).Rel i k) (σ : H.toFeec.domainSpace i) :
    Metric.infDist σ (S.toFeec.domainSub i) ≤ S.graphDist i k (H.coord i k σ) := by
  refine le_ciInf fun v => ?_
  obtain rfl := (ComplexShape.up ℤ).next_eq' hik
  set w : H.toFeec.domainSpace i := (H.d i _).toGraphSpace ⟨v, S.le_domain i _ v.2⟩
  have hmem : w ∈ S.toFeec.domainSub i :=
    ⟨(S.toFeec.toHilbertComplex.d i _).toGraphSpace ⟨v, Submodule.mem_top⟩, rfl⟩
  refine (Metric.infDist_le_dist_of_mem hmem).trans (le_of_eq ?_)
  rw [dist_eq_norm, ← H.graphNorm_domainCoord hik, _root_.map_sub]
  rfl

/-- For a cycle `b`, the same at `b`. -/
theorem infDist_cycles_le [∀ i, FiniteDimensional 𝕜 (S.V i)] {j : ℤ} {b : W j}
    (hb : b ∈ H.toFeec.cycles j) (hb' : b ∈ (H.d j (j + 1)).domain) :
    Metric.infDist (Feec.HilbertComplex.cyclesToDomainSpace hb) (S.toFeec.domainSub j) ≤
      S.graphDist j (j + 1) ⟨b, hb'⟩ :=
  (S.infDist_domainSub_le (rel_add_one j) _).trans_eq (congrArg _ (Subtype.ext rfl))

end Subcomplex

variable {H} {κ : Type*}

/-- The family as a `Feec` family of subcomplexes. -/
def SubcomplexFamily.toFeec (F : H.SubcomplexFamily κ) :
    Feec.HilbertComplex.SubcomplexFamily H.toFeec κ where
  l := F.l
  V h := (F.V h).toFeec
  finiteDimensional h i := F.finiteDimensional h i
  π h := (F.π h).toFeec

theorem graphNorm_nonneg {i j : ℤ} (x : (H.d i j).domain) : 0 ≤ H.graphNorm i j x :=
  Real.sqrt_nonneg _

theorem norm_le_graphNorm {i j : ℤ} (x : (H.d i j).domain) : ‖(x : W i)‖ ≤ H.graphNorm i j x :=
  Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))

/-- **Graph-norm bounds transfer**: `‖π x‖_V ≤ C ‖x‖_V` is `Feec`'s bound, squared, at every
`k = i + 1`. -/
theorem SubcomplexFamily.isGraphBoundedBy_toFeec {F : H.SubcomplexFamily κ} {i k : ℤ}
    (hik : i + 1 = k) {C : ℝ} (hπ : F.IsGraphBoundedBy i C) (h : κ) :
    (F.toFeec.π h).IsGraphBounded i k C := by
  subst hik
  intro x
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hπ h x) 2
  unfold graphNorm at h2
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h2
  have e1 : ‖(F.toFeec.π h).π i x‖ = ‖((F.π h).π i x : W i)‖ :=
    congrArg norm ((F.π h).extend_apply x)
  have e2 : ‖H.toFeec.d i (i + 1) ⟨(F.toFeec.π h).π i x,
      (F.toFeec.V h).le_domain i (i + 1) ((F.toFeec.π h).mem i x)⟩‖ =
      ‖H.d i (i + 1) ⟨(F.π h).π i x, (F.V h).le_domain i (i + 1) ((F.π h).π i x).2⟩‖ :=
    congrArg (fun y => ‖H.d i (i + 1) y‖) (Subtype.ext ((F.π h).extend_apply x))
  exact (congrArg₂ (· + ·) (congrArg (· ^ 2) e1) (congrArg (· ^ 2) e2)).trans_le h2

theorem SubcomplexFamily.isGraphBounded_toFeec {F : H.SubcomplexFamily κ} {i : ℤ}
    (hπ : F.IsGraphBounded i) : F.toFeec.IsGraphBounded i := by
  obtain ⟨C, hC⟩ := hπ
  refine ⟨C, fun h => ?_⟩
  rw [(ComplexShape.up ℤ).next_eq' (rel_add_one i)]
  exact SubcomplexFamily.isGraphBoundedBy_toFeec rfl hC h

theorem SubcomplexFamily.IsGraphBoundedBy.mono {F : H.SubcomplexFamily κ} {i : ℤ} {C C' : ℝ}
    (hπ : F.IsGraphBoundedBy i C) (hC : C ≤ C') : F.IsGraphBoundedBy i C' := fun h x =>
  (hπ h x).trans (mul_le_mul_of_nonneg_right hC (graphNorm_nonneg x))

theorem SubcomplexFamily.IsGraphBounded.exists_one_le {F : H.SubcomplexFamily κ} {i : ℤ}
    (hπ : F.IsGraphBounded i) : ∃ C, 1 ≤ C ∧ F.IsGraphBoundedBy i C := by
  obtain ⟨C, hC⟩ := hπ
  exact ⟨max C 1, le_max_right _ _, hC.mono (le_max_left _ _)⟩

/-- **The Poincaré inequality transfers**: `‖v‖_V ≤ c ‖d v‖` gives `Feec`'s `‖v‖ ≤ c ‖d v‖` at
every `k = i + 1`. -/
theorem PoincareBy.toFeec {i k : ℤ} (hik : i + 1 = k) {c : ℝ} (hP : H.PoincareBy i c) :
    ∀ z : (H.toFeec.d i k).domain, (z : W i) ∈ (H.toFeec.cycles i)ᗮ →
      ‖(z : W i)‖ ≤ c * ‖H.toFeec.d i k z‖ := by
  subst hik
  intro z hz
  rw [H.cycles_eq] at hz
  exact (norm_le_graphNorm z).trans (hP z hz)

theorem PoincareBy.mono {i : ℤ} {c c' : ℝ} (hP : H.PoincareBy i c) (hc : c ≤ c') :
    H.PoincareBy i c' := fun v hv =>
  (hP v hv).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

variable (H) in
/-- `Feec`'s Poincaré inequality `‖v‖ ≤ c ‖d v‖` gives `‖v‖_V ≤ √(1 + c²) ‖d v‖`. -/
theorem poincareBy_of_feec {i : ℤ} {c : ℝ}
    (hP : ∀ z : (H.toFeec.d i (i + 1)).domain, (z : W i) ∈ (H.toFeec.cycles i)ᗮ →
      ‖(z : W i)‖ ≤ c * ‖H.toFeec.d i (i + 1) z‖) : H.PoincareBy i √(1 + c ^ 2) := by
  intro z hz
  rw [← H.cycles_eq] at hz
  have h1 := hP z hz
  have h0 := norm_nonneg (z : W i)
  have h2 : ‖(z : W i)‖ ^ 2 ≤ c ^ 2 * ‖H.d i (i + 1) z‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ h0 h1 2
  rw [show √(1 + c ^ 2) * ‖H.d i (i + 1) z‖ = √((1 + c ^ 2) * ‖H.d i (i + 1) z‖ ^ 2) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]]
  exact Real.sqrt_le_sqrt (by linarith)

variable (H) in
/-- Closed range at `i + 1` gives a Poincaré inequality `‖v‖_V ≤ c ‖d v‖` in degree `i`. -/
theorem exists_poincareBy {i : ℤ} (hi : IsClosed (H.boundaries (i + 1) : Set (W (i + 1)))) :
    ∃ c, H.PoincareBy i c := by
  obtain ⟨c, -, hc⟩ := H.toFeec.exists_poincare_of_closedRangeAt (rel_add_one i)
    ((H.closedRangeAt_iff (i + 1)).2 hi)
  exact ⟨_, H.poincareBy_of_feec hc⟩

variable (H) in
/-- **Closed range is the Poincaré inequality**: `R(dⁱ) = 𝔅ⁱ⁺¹` is closed iff
`‖v‖_V ≤ c ‖d v‖` on `D(dⁱ) ∩ (𝔷ⁱ)ᗮ` for some `c` (`Feec`'s
`Feec.HilbertComplex.closedRangeAt_iff_poincare_of_rel`). -/
theorem closedRange_iff_poincareBy (i : ℤ) :
    IsClosed (H.boundaries (i + 1) : Set (W (i + 1))) ↔ ∃ c, H.PoincareBy i c :=
  ⟨H.exists_poincareBy, fun ⟨_, hc⟩ => (H.closedRangeAt_iff (i + 1)).1
    ((H.toFeec.closedRangeAt_iff_poincare_of_rel (rel_add_one i)).2 ⟨_, hc.toFeec rfl⟩)⟩

variable (H) in
theorem closedRange_iff_poincareBy_of_eq {i k : ℤ} (hik : i + 1 = k) :
    IsClosed (H.boundaries k : Set (W k)) ↔ ∃ c, H.PoincareBy i c := by
  subst hik; exact H.closedRange_iff_poincareBy i

/-- **The approximation property transfers**: the graph-norm distance of `Feec` is at most that
of the challenge. -/
theorem SubcomplexFamily.approximates_toFeec {F : H.SubcomplexFamily κ} {i : ℤ}
    (ha : F.Approximates i) : F.toFeec.Approximates i := fun σ =>
  squeeze_zero (fun _ => Metric.infDist_nonneg)
    (fun h => (F.V h).infDist_domainSub_le (rel_add_one i) σ)
    (ha (H.coord i (i + 1) σ))

end HilbertComplex

/-! ### Mixed solutions -/

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-- Two solutions with the same data differ by a solution with zero data. -/
theorem IsMixedSolution.sub {j : ℤ} {A : Submodule 𝕜 (W (j - 1))} {B Q : Submodule 𝕜 (W j)}
    {f : W j} {σ σ' : (H.d (j - 1) j).domain} {u u' : (H.d j (j + 1)).domain} {p p' : W j}
    (hs : H.IsMixedSolution j A B Q f σ u p) (hs' : H.IsMixedSolution j A B Q f σ' u' p') :
    H.IsMixedSolution j A B Q 0 (σ - σ') (u - u') (p - p') where
  mem := ⟨A.sub_mem hs.mem.1 hs'.mem.1, B.sub_mem hs.mem.2.1 hs'.mem.2.1,
    Q.sub_mem hs.mem.2.2 hs'.mem.2.2⟩
  fst τ hτ := by
    have h1 := hs.fst τ hτ
    have h2 := hs'.fst τ hτ
    rw [Submodule.coe_sub, Submodule.coe_sub, inner_sub_right, inner_sub_right]
    linear_combination h1 - h2
  snd v hv := by
    have h1 := hs.snd v hv
    have h2 := hs'.snd v hv
    rw [LinearPMap.map_sub, LinearPMap.map_sub, inner_sub_right, inner_sub_right, inner_sub_right,
      inner_zero_right]
    linear_combination h1 - h2
  harm q hq := by
    rw [Submodule.coe_sub, inner_sub_right, hs.harm q hq, hs'.harm q hq, sub_zero]

/-- **Uniqueness for the mixed problem**: a solution with zero data vanishes when the harmonic
space `Q` is made of cycles of `B` and contains every cycle of `B` orthogonal to `d A`. -/
theorem IsMixedSolution.eq_zero {j : ℤ} {A : Submodule 𝕜 (W (j - 1))} {B Q : Submodule 𝕜 (W j)}
    (hQ : ∀ q ∈ Q, ∃ hq : q ∈ (H.d j (j + 1)).domain, q ∈ B ∧ H.d j (j + 1) ⟨q, hq⟩ = 0)
    (hQ' : ∀ u : (H.d j (j + 1)).domain, (u : W j) ∈ B → H.d j (j + 1) u = 0 →
      (∀ τ : (H.d (j - 1) j).domain, (τ : W (j - 1)) ∈ A → ⟪H.d (j - 1) j τ, (u : W j)⟫_𝕜 = 0) →
        (u : W j) ∈ Q)
    {σ : (H.d (j - 1) j).domain} {u : (H.d j (j + 1)).domain} {p : W j}
    (hs : H.IsMixedSolution j A B Q 0 σ u p) : σ = 0 ∧ u = 0 ∧ p = 0 := by
  obtain ⟨hσ, hu, hp⟩ := hs.mem
  have e1 := hs.fst σ hσ
  have e2 := hs.snd u hu
  have e3 := hs.harm p hp
  rw [inner_zero_right] at e2
  have e3' : ⟪(u : W j), p⟫_𝕜 = 0 := by rw [← inner_conj_symm, e3, _root_.map_zero]
  have e4 : ⟪(u : W j), H.d (j - 1) j σ⟫_𝕜 = ⟪(σ : W (j - 1)), σ⟫_𝕜 := by
    rw [← inner_conj_symm, ← sub_eq_zero.1 e1, inner_conj_symm]
  rw [e3', e4, add_zero] at e2
  obtain ⟨hσ0, hdu⟩ := inner_self_add_inner_self_eq_zero e2
  have hσ0' : σ = 0 := Subtype.ext hσ0
  subst hσ0'
  obtain ⟨hpd, hpB, hdp⟩ := hQ p hp
  have e5 := hs.snd ⟨p, hpd⟩ hpB
  simp only [LinearPMap.map_zero, inner_zero_right, zero_add, hdp, inner_zero_left,
    inner_self_eq_zero] at e5
  subst e5
  have huQ : (u : W j) ∈ Q := hQ' u hu hdu fun τ hτ => by
    have := hs.fst τ hτ
    rwa [ZeroMemClass.coe_zero, inner_zero_right, zero_sub, neg_eq_zero] at this
  have e6 := hs.harm _ huQ
  rw [inner_self_eq_zero] at e6
  exact ⟨rfl, Subtype.ext e6, rfl⟩

/-- **Uniqueness for the mixed problem** with the same data. -/
theorem IsMixedSolution.unique {j : ℤ} {A : Submodule 𝕜 (W (j - 1))} {B Q : Submodule 𝕜 (W j)}
    (hQ : ∀ q ∈ Q, ∃ hq : q ∈ (H.d j (j + 1)).domain, q ∈ B ∧ H.d j (j + 1) ⟨q, hq⟩ = 0)
    (hQ' : ∀ u : (H.d j (j + 1)).domain, (u : W j) ∈ B → H.d j (j + 1) u = 0 →
      (∀ τ : (H.d (j - 1) j).domain, (τ : W (j - 1)) ∈ A → ⟪H.d (j - 1) j τ, (u : W j)⟫_𝕜 = 0) →
        (u : W j) ∈ Q)
    {f : W j} {σ σ' : (H.d (j - 1) j).domain} {u u' : (H.d j (j + 1)).domain} {p p' : W j}
    (hs : H.IsMixedSolution j A B Q f σ u p) (hs' : H.IsMixedSolution j A B Q f σ' u' p') :
    σ = σ' ∧ u = u' ∧ p = p' := by
  obtain ⟨h1, h2, h3⟩ := (hs.sub H hs').eq_zero H hQ hQ'
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2, sub_eq_zero.1 h3⟩

/-- The harmonic forms are cycles. -/
theorem harmonic_cond {j : ℤ} : ∀ q ∈ H.harmonic j, ∃ hq : q ∈ (H.d j (j + 1)).domain,
    q ∈ (⊤ : Submodule 𝕜 (W j)) ∧ H.d j (j + 1) ⟨q, hq⟩ = 0 := by
  rintro q ⟨hq, -⟩
  obtain ⟨y, hy, rfl⟩ := hq
  exact ⟨y.2, trivial, hy⟩

/-- A cycle orthogonal to the boundaries is harmonic. -/
theorem harmonic_cond' {j : ℤ} : ∀ u : (H.d j (j + 1)).domain, (u : W j) ∈ (⊤ : Submodule 𝕜 (W j)) →
    H.d j (j + 1) u = 0 → (∀ τ : (H.d (j - 1) j).domain, (τ : W (j - 1)) ∈ (⊤ : Submodule 𝕜 _) →
      ⟪H.d (j - 1) j τ, (u : W j)⟫_𝕜 = 0) → (u : W j) ∈ H.harmonic j := by
  intro u _ hdu hτ
  refine ⟨⟨u, hdu, rfl⟩, ?_⟩
  have hmem : (u : W j) ∈ (H.d (j - 1) j)†.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨0, fun τ => by
      rw [inner_zero_left, ← inner_conj_symm, hτ τ trivial, _root_.map_zero]⟩
  refine ⟨⟨_, hmem⟩, ?_, rfl⟩
  exact LinearPMap.adjoint_apply_eq (H.dense _ _) _ fun τ => by
    rw [inner_zero_left, ← inner_conj_symm, hτ τ trivial, _root_.map_zero]

end HilbertComplex

/-! ### Mixed solutions of `Feec` -/

namespace HilbertComplex

variable (H : HilbertComplex 𝕜 W)

/-- A point of `D(d i j)` at a related pair, as a point of the domain space of `Feec`. -/
def toDomainSpace {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (x : (H.d i j).domain) :
    H.toFeec.domainSpace i :=
  (H.toFeec.d i ((ComplexShape.up ℤ).next i)).toGraphSpace
    ⟨x, by rw [(ComplexShape.up ℤ).next_eq' hij]; exact x.2⟩

/-- The mixed solutions of `Feec` are mixed solutions. -/
theorem isMixedSolution_of_feec {j : ℤ} {f : W j} {σ : H.toFeec.domainSpace (j - 1)}
    {u : H.toFeec.domainSpace j} {p : H.toFeec.harmonic j}
    (hs : H.toFeec.IsMixedSolution (j - 1) j (j + 1) f σ u p) :
    H.IsMixedSolution j ⊤ ⊤ (H.harmonic j) f (H.coord (j - 1) j σ)
      (H.coord j (j + 1) u) p where
  mem := ⟨trivial, trivial, H.harmonic_eq j ▸ p.2⟩
  fst τ _ := hs.fst (H.toDomainSpace (rel_sub_one j) τ)
  snd v _ := hs.snd (H.toDomainSpace (rel_add_one j) v)
  harm q hq := hs.harm q ((H.harmonic_eq j).symm ▸ hq)

namespace Subcomplex

variable {H} (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)]

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
theorem boundaries_eq (i : ℤ) : S.toFeec.boundariesW i = S.boundaries i := by
  have hp : (ComplexShape.up ℤ).prev i = i - 1 := (ComplexShape.up ℤ).prev_eq' (rel_sub_one i)
  change LinearMap.range ((S.V i).subtype ∘ₗ S.toFeec.dLin _ i) = _
  rw [hp]
  rfl

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
theorem harmonic_eq (i : ℤ) : S.toFeec.harmonicW i = S.harmonic i := by
  change S.V i ⊓ H.toFeec.cycles i ⊓ (S.toFeec.boundariesW i)ᗮ = _
  rw [H.cycles_eq, boundaries_eq]
  rfl

/-- A point of `Vⁱ` at a related pair, as a point of the discrete domain space of `Feec`. -/
def toDomainSpace (i : ℤ) (x : S.V i) : S.toFeec.toHilbertComplex.domainSpace i :=
  (S.toFeec.toHilbertComplex.d i ((ComplexShape.up ℤ).next i)).toGraphSpace ⟨x, Submodule.mem_top⟩

/-- The discrete mixed solutions of `Feec`, read in `W`, are discrete mixed solutions. -/
theorem isMixedSolution_of_feec {j : ℤ} {f : W j}
    {σ : S.toFeec.toHilbertComplex.domainSpace (j - 1)}
    {u : S.toFeec.toHilbertComplex.domainSpace j} {p : S.toFeec.toHilbertComplex.harmonic j}
    (hs : S.toFeec.toHilbertComplex.IsMixedSolution (j - 1) j (j + 1)
      ((S.V j).orthogonalProjectionOnto f) σ u p) :
    H.IsMixedSolution j (S.V (j - 1)) (S.V j) (S.harmonic j) f
      (H.coord (j - 1) j (S.toFeec.embD (j - 1) σ))
      (H.coord j (j + 1) (S.toFeec.embD j u)) ((p : S.toFeec.V j) : W j) where
  mem := ⟨(S.toFeec.toHilbertComplex.domainIncl (j - 1) σ).2,
    (S.toFeec.toHilbertComplex.domainIncl j u).2,
    by rw [← S.harmonic_eq j]; exact S.toFeec.mem_harmonic_iff.1 p.2⟩
  fst τ hτ := hs.fst (S.toDomainSpace (j - 1) ⟨τ, hτ⟩)
  snd v hv := by
    exact (hs.snd (S.toDomainSpace j ⟨v, hv⟩)).trans
      (Feec.HilbertComplex.Subcomplex.CochainProjection.inner_orthogonalProjectionOnto_eq
        S.toFeec f ⟨v, hv⟩)
  harm q hq := by
    have hqV : q ∈ S.V j := hq.1.1
    exact hs.harm ⟨q, hqV⟩ (S.toFeec.mem_harmonic_iff.2 (S.harmonic_eq j ▸ hq))

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- The discrete harmonic forms are cycles of `V`. -/
theorem harmonic_cond {j : ℤ} : ∀ q ∈ S.harmonic j, ∃ hq : q ∈ (H.d j (j + 1)).domain,
    q ∈ S.V j ∧ H.d j (j + 1) ⟨q, hq⟩ = 0 := by
  rintro q ⟨⟨hqV, hq⟩, -⟩
  obtain ⟨y, hy, rfl⟩ := hq
  exact ⟨y.2, hqV, hy⟩

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- A cycle of `V` orthogonal to the discrete boundaries is discrete harmonic. -/
theorem harmonic_cond' {j : ℤ} : ∀ u : (H.d j (j + 1)).domain, (u : W j) ∈ S.V j →
    H.d j (j + 1) u = 0 → (∀ τ : (H.d (j - 1) j).domain, (τ : W (j - 1)) ∈ S.V (j - 1) →
      ⟪H.d (j - 1) j τ, (u : W j)⟫_𝕜 = 0) → (u : W j) ∈ S.harmonic j := by
  intro u hu hdu hτ
  refine ⟨⟨hu, u, hdu, rfl⟩, fun b hb => ?_⟩
  obtain ⟨y, rfl⟩ := hb
  exact hτ ⟨y, S.le_domain _ _ y.2⟩ y.2

end Subcomplex

end HilbertComplex

/-! ### The static verdict -/

namespace HilbertComplex

variable {H : HilbertComplex 𝕜 W}

/-- **The inclusion induces an isomorphism on cohomology** as soon as the map `[z] ↦ [π z]`
induced by a cochain projection is one-to-one (`Feec`'s `cohomologyMap`). -/
theorem Subcomplex.cohomologyIncl_bijective (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)]
    (P : S.CochainProjection) {j : ℤ} (hP : Function.Injective (P.toFeec.cohomologyMap j)) :
    Function.Bijective (S.cohomologyIncl j) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun q hq => ?_, fun q => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [cohomologyIncl, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨y, hy⟩ := hq
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨P.toFeec.π (j - 1) y, P.toFeec.mem _ _⟩, (P.toFeec.comm (j - 1) j y).trans ?_⟩
    change P.toFeec.π j (H.d (j - 1) j y) = (z : W j)
    rw [show H.d (j - 1) j y = (z : W j) from hy, P.toFeec.proj _ _ z.2.1]
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hz : (z : W j) ∈ H.toFeec.cycles j := (H.cycles_eq j).symm ▸ z.2
    have hπz : P.toFeec.π j z ∈ S.V j ⊓ H.toFeec.cycles j := P.toFeec.mem_cyclesW hz
    have hdiff : (z : W j) - P.toFeec.π j z ∈ H.toFeec.cycles j := sub_mem hz hπz.2
    have h0 : P.toFeec.cohomologyMap j (Submodule.Quotient.mk ⟨_, hdiff⟩) =
        P.toFeec.cohomologyMap j 0 := by
      rw [_root_.map_zero, Feec.HilbertComplex.Subcomplex.CochainProjection.cohomologyMap,
        Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      have : P.toFeec.cyclesMap j ⟨_, hdiff⟩ = 0 := Subtype.ext (Subtype.ext (by
        rw [Feec.HilbertComplex.Subcomplex.CochainProjection.coe_cyclesMap_apply]
        change P.toFeec.π j ((z : W j) - P.toFeec.π j z) = 0
        rw [_root_.map_sub, P.toFeec.proj _ _ (P.toFeec.mem _ _), sub_self]))
      rw [this]
      exact zero_mem _
    have hb := Submodule.Quotient.mk_eq_zero _ |>.1 (hP h0)
    rw [Submodule.mem_comap, Submodule.coe_subtype, HilbertComplex.boundaries_eq H j] at hb
    refine ⟨Submodule.Quotient.mk ⟨P.toFeec.π j z, hπz.1, by
      have h2 := hπz.2; rwa [H.cycles_eq j] at h2⟩, ?_⟩
    rw [cohomologyIncl, Submodule.mapQ_apply, Submodule.Quotient.eq]
    have := neg_mem hb
    rwa [neg_sub] at this

variable {κ : Type*}

namespace Subcomplex

variable (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)]

/-- A point of `Feec`'s discrete mixed space, read in the challenge: its norm there. -/
theorem mixedNorm_eq {j : ℤ} (x : S.toFeec.toHilbertComplex.MixedSpace (j - 1) j) :
    H.mixedNorm₃ j (H.coord (j - 1) j (S.toFeec.embD (j - 1) (WithLp.fst x)))
      (H.coord j (j + 1) (S.toFeec.embD j (WithLp.snd x).fst))
      (((WithLp.snd x).snd : S.toFeec.V j) : W j) =
      ‖WithLp.fst x‖ + ‖(WithLp.snd x).fst‖ + ‖(((WithLp.snd x).snd : S.toFeec.V j) : W j)‖ := by
  rw [H.mixedNorm_domainCoord, LinearIsometry.norm_map, LinearIsometry.norm_map]

/-- The norm of the challenge is between the `ℓ²` norm of `Feec` and twice it. -/
theorem norm_le_mixedNorm {j : ℤ} (x : S.toFeec.toHilbertComplex.MixedSpace (j - 1) j) :
    ‖x‖ ≤ H.mixedNorm₃ j (H.coord (j - 1) j (S.toFeec.embD (j - 1) (WithLp.fst x)))
      (H.coord j (j + 1) (S.toFeec.embD j (WithLp.snd x).fst))
      (((WithLp.snd x).snd : S.toFeec.V j) : W j) ∧
    H.mixedNorm₃ j (H.coord (j - 1) j (S.toFeec.embD (j - 1) (WithLp.fst x)))
      (H.coord j (j + 1) (S.toFeec.embD j (WithLp.snd x).fst))
      (((WithLp.snd x).snd : S.toFeec.V j) : W j) ≤ 2 * ‖x‖ := by
  rw [S.mixedNorm_eq]
  have e := Feec.HilbertComplex.MixedSpace.norm_sq x
  have hc' : ‖((WithLp.snd x).snd : S.toFeec.V j)‖ =
      ‖(((WithLp.snd x).snd : S.toFeec.V j) : W j)‖ := rfl
  rw [hc'] at e
  have ha := norm_nonneg (WithLp.fst x)
  have hb := norm_nonneg (WithLp.snd x).fst
  have hc := norm_nonneg (((WithLp.snd x).snd : S.toFeec.V j) : W j)
  have hx := norm_nonneg x
  constructor
  · nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
  · nlinarith [sq_nonneg (‖WithLp.fst x‖ - ‖(WithLp.snd x).fst‖),
      sq_nonneg (‖(WithLp.snd x).fst‖ - ‖(((WithLp.snd x).snd : S.toFeec.V j) : W j)‖),
      sq_nonneg (‖WithLp.fst x‖ - ‖(((WithLp.snd x).snd : S.toFeec.V j) : W j)‖)]

/-- A discrete triple of `Feec`'s mixed space of norm at most `B` has norm at most `2 B` in the
challenge. -/
theorem mixedNorm_le_of_norm_le {j : ℤ} (x : S.toFeec.toHilbertComplex.MixedSpace (j - 1) j)
    {B : ℝ} (hx : ‖x‖ ≤ B) :
    H.mixedNorm₃ j (H.coord (j - 1) j (S.toFeec.embD (j - 1) (WithLp.fst x)))
      (H.coord j (j + 1) (S.toFeec.embD j (WithLp.snd x).fst))
      (((WithLp.snd x).snd : S.toFeec.V j) : W j) ≤ 2 * B := by
  have := (S.norm_le_mixedNorm x).2
  linarith

/-- The mixed form of the challenge at points of `Feec`'s discrete mixed space is `Feec`'s. -/
theorem mixedForm_eq {j : ℤ} (x y : S.toFeec.toHilbertComplex.MixedSpace (j - 1) j) :
    H.mixedForm j (H.coord (j - 1) j (S.toFeec.embD (j - 1) (WithLp.fst x)))
      (H.coord j (j + 1) (S.toFeec.embD j (WithLp.snd x).fst))
      (((WithLp.snd x).snd : S.toFeec.V j) : W j)
      (H.coord (j - 1) j (S.toFeec.embD (j - 1) (WithLp.fst y)))
      (H.coord j (j + 1) (S.toFeec.embD j (WithLp.snd y).fst))
      (((WithLp.snd y).snd : S.toFeec.V j) : W j) =
      S.toFeec.toHilbertComplex.mixedForm (j - 1) j (j + 1) x y := by
  rw [Feec.HilbertComplex.Subcomplex.CochainProjection.mixedForm_toHilbertComplex_apply]
  rfl

/-- **The discrete inf-sup condition of the challenge** from `Feec`'s inf-sup condition (with
constant `γ = 1 / (16 (C √(1 + c_P²))²)`) of the discrete mixed form, with constant `γ / 16`. -/
theorem infSup_of_feec (P : S.CochainProjection) {j : ℤ} {cP C : ℝ} (hC : 1 ≤ C)
    (hPi : ∀ z : (H.toFeec.d (j - 1) j).domain, (z : W (j - 1)) ∈ (H.toFeec.cycles (j - 1))ᗮ →
      ‖(z : W (j - 1))‖ ≤ cP * ‖H.toFeec.d (j - 1) j z‖)
    (hPj : ∀ z : (H.toFeec.d j (j + 1)).domain, (z : W j) ∈ (H.toFeec.cycles j)ᗮ →
      ‖(z : W j)‖ ≤ cP * ‖H.toFeec.d j (j + 1) z‖)
    (hπi : P.toFeec.IsGraphBounded (j - 1) j C) (hπj : P.toFeec.IsGraphBounded j (j + 1) C)
    (σ : (H.d (j - 1) j).domain) (u : (H.d j (j + 1)).domain) (p : W j)
    (hσ : (σ : W (j - 1)) ∈ S.V (j - 1)) (hu : (u : W j) ∈ S.V j) (hp : p ∈ S.harmonic j) :
    ∃ (τ : (H.d (j - 1) j).domain) (v : (H.d j (j + 1)).domain) (q : W j),
      (τ : W (j - 1)) ∈ S.V (j - 1) ∧ (v : W j) ∈ S.V j ∧ q ∈ S.harmonic j ∧
      H.mixedNorm₃ j τ v q ≤ H.mixedNorm₃ j σ u p ∧
      1 / (16 * (C * √(1 + cP ^ 2)) ^ 2) / 16 * H.mixedNorm₃ j σ u p ^ 2 ≤
        ‖H.mixedForm j σ u p τ v q‖ := by
  have hIS := P.toFeec.infSup_mixedForm_of_graph (rel_sub_one j) (rel_add_one j) hC hPi hPj hπi hπj
  set γ := 1 / (16 * (C * √(1 + cP ^ 2)) ^ 2)
  obtain ⟨X, rfl, rfl, rfl⟩ : ∃ X : S.toFeec.toHilbertComplex.MixedSpace (j - 1) j,
      H.coord (j - 1) j (S.toFeec.embD (j - 1) (WithLp.fst X)) = σ ∧
      H.coord j (j + 1) (S.toFeec.embD j (WithLp.snd X).fst) = u ∧
      (((WithLp.snd X).snd : S.toFeec.V j) : W j) = p :=
    ⟨Feec.HilbertComplex.MixedSpace.mk (S.toDomainSpace (j - 1) ⟨σ, hσ⟩)
      (S.toDomainSpace j ⟨u, hu⟩)
      ⟨⟨p, hp.1.1⟩, S.toFeec.mem_harmonic_iff.2 ((S.harmonic_eq j).symm ▸ hp)⟩,
      Subtype.ext rfl, Subtype.ext rfl, rfl⟩
  obtain ⟨hnX, hXn⟩ := S.norm_le_mixedNorm X
  have hγ := hIS.pos
  obtain ⟨Y, hY1, hY2⟩ := hIS.exists_norm_le_mul_le X (t := ‖X‖ / 2) (by positivity)
  obtain ⟨-, hYn⟩ := S.norm_le_mixedNorm Y
  have hm0 := (norm_nonneg X).trans hnX
  refine ⟨H.coord (j - 1) j (S.toFeec.embD (j - 1) (WithLp.fst Y)),
    H.coord j (j + 1) (S.toFeec.embD j (WithLp.snd Y).fst),
    (((WithLp.snd Y).snd : S.toFeec.V j) : W j),
    (S.toFeec.toHilbertComplex.domainIncl (j - 1) (WithLp.fst Y)).2,
    (S.toFeec.toHilbertComplex.domainIncl j (WithLp.snd Y).fst).2,
    by rw [← S.harmonic_eq j]; exact S.toFeec.mem_harmonic_iff.1 (WithLp.snd Y).snd.2,
    hYn.trans (le_trans (by linarith) hnX), ?_⟩
  rw [S.mixedForm_eq]
  refine le_trans ?_ hY2
  have h4 := pow_le_pow_left₀ hm0 hXn 2
  nlinarith

end Subcomplex

theorem starProjection_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {K K' : Submodule 𝕜 E} (h : K = K') [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection]
    (x : E) : K.starProjection x = K'.starProjection x := by
  subst h; rfl

/-- The constant of the static verdict for cochain projections bounded by `c` in the graph norm
and the Poincaré constant `c_P`: `256 (1 + K²) (1 + c)²`, `K = c √(1 + c_P²)`. -/
def staticConst (c cP : ℝ) : ℝ := 256 * (1 + (c * √(1 + cP ^ 2)) ^ 2) * (1 + c) ^ 2

theorem Subcomplex.graphDist_nonneg (S : H.Subcomplex) {i j : ℤ} (x : (H.d i j).domain) :
    0 ≤ S.graphDist i j x :=
  Real.iInf_nonneg fun _ => graphNorm_nonneg _

/-- **The static verdict** from `Feec`'s static FEEC theorem for families of subcomplexes, with
the constant `staticConst c c_P` for cochain projections bounded by `c ≥ 1` in the graph norm and
the Poincaré constant `c_P`. -/
theorem SubcomplexFamily.staticVerdict_of (F : H.SubcomplexFamily κ) (j : ℤ) {c cP : ℝ}
    (hc : 1 ≤ c) (hπ : F.IsGraphBoundedBy (j - 1) c) (hπ' : F.IsGraphBoundedBy j c)
    (hP : H.PoincareBy (j - 1) cP) (hP' : H.PoincareBy j cP) :
    F.StaticVerdict₀ j (staticConst c cP) := by
  set G := F.toFeec
  have hPi := hP.toFeec (sub_add_cancel j 1)
  have hPj := hP'.toFeec (rel_add_one j)
  have hcj : H.toFeec.ClosedRangeAt j :=
    (H.toFeec.closedRangeAt_iff_poincare_of_rel (rel_sub_one j)).2 ⟨cP, hPi⟩
  have hck : H.toFeec.ClosedRangeAt (j + 1) :=
    (H.toFeec.closedRangeAt_iff_poincare_of_rel (rel_add_one j)).2 ⟨cP, hPj⟩
  have hCi := SubcomplexFamily.isGraphBoundedBy_toFeec (sub_add_cancel j 1) hπ
  have hCj := SubcomplexFamily.isGraphBoundedBy_toFeec (rel_add_one j) hπ'
  have hbi' := SubcomplexFamily.isGraphBounded_toFeec ⟨c, hπ⟩
  have hbj := SubcomplexFamily.isGraphBounded_toFeec ⟨c, hπ'⟩
  have hbi : G.IsGraphBounded ((ComplexShape.up ℤ).prev j) := by
    rw [(ComplexShape.up ℤ).prev_eq' (rel_sub_one j)]
    exact hbi'
  have V := G.staticFEEC j hbi hbj hcj fun k hk => by
    obtain rfl : j + 1 = k := hk; exact hck
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  set K := c * √(1 + cP ^ 2) with hKdef
  have hK : 1 ≤ K := Feec.HilbertComplex.Subcomplex.CochainProjection.one_le_mul_sqrt hc
  rw [show staticConst c cP = 256 * (1 + K ^ 2) * (1 + c) ^ 2 from rfl]
  have hΦK : 256 * (1 + K ^ 2) ≤ 256 * (1 + K ^ 2) * (1 + c) ^ 2 :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))
  have hK2 := sq_nonneg K
  have hsol := fun f => H.isMixedSolution_of_feec (H.toFeec.isMixedSolution_mixedSolution
    (rel_sub_one j) (rel_add_one j) hcj hck f)
  have hdsol := fun h f => (F.V h).isMixedSolution_of_feec
    (Feec.HilbertComplex.Subcomplex.CochainProjection.isMixedSolution_discreteMixedSolution
      (F.V h).toFeec (rel_sub_one j) (rel_add_one j) f)
  have uq := fun {f σ σ' u u' p p'} => @IsMixedSolution.unique _ _ _ _ _ _ H j ⊤ ⊤ (H.harmonic j)
    H.harmonic_cond H.harmonic_cond' f σ σ' u u' p p'
  have uqh := fun h {f σ σ' u u' p p'} => @IsMixedSolution.unique _ _ _ _ _ _ H j
    ((F.V h).V (j - 1)) ((F.V h).V j) ((F.V h).harmonic j) (F.V h).harmonic_cond
    (F.V h).harmonic_cond' f σ σ' u u' p p'
  have hgap : ∀ h, (G.π h).harmonicGap j = (F.π h).harmonicGap j := fun h =>
    (F.π h).harmonicGap_toFeec j
  have hFD : FiniteDimensional 𝕜 (H.harmonic j) → FiniteDimensional 𝕜 (H.toFeec.harmonic j) :=
    fun _ => by rw [H.harmonic_eq]; infer_instance
  refine
    { harmonicDist := fun h q hq => ?_
      discreteHarmonicDist := fun h q hq => ?_
      cohomologyMap_comp_incl := fun h => (F.π h).cohomologyMap_comp_incl j
      cohomology_of_lt := fun h hlt => ?_
      harmonicGap := fun ha _ => ?_
      cohomology := fun ha _ => ?_
      poincare := ?_
      existsUnique := fun f => ⟨(_, _, _), hsol f, fun x hx => ?_⟩
      existsUnique_discrete := fun h f => ⟨(_, _, _), hdsol h f, fun x hx => ?_⟩
      infSup := ?_
      stable := ?_
      quasiOptimal := ?_
      converges := fun ha ha' {f σ u p} hs {σh uh ph} hsh => ?_ }
  · -- the gap from `ℌ` to `ℌₕ`
    have hq' : q ∈ H.toFeec.harmonic j := (H.harmonic_eq j).symm ▸ hq
    have hm : ((G.V h).harmonicW j).starProjection q ∈ (F.V h).harmonic j := by
      rw [← (F.V h).harmonic_eq j]; exact Submodule.starProjection_apply_mem _ q
    refine (Metric.infDist_le_dist_of_mem hm).trans ?_
    rw [dist_eq_norm]
    exact (V.harmonicDist h hq').trans_eq (congrArg (fun x => ‖q - x‖)
      ((F.π h).extend_apply ⟨q, H.harmonic_le_domain j hq⟩))
  · -- the gap from `ℌₕ` to `ℌ`
    have hq' : q ∈ (G.V h).harmonicW j := ((F.V h).harmonic_eq j).symm ▸ hq
    have e := (G.π h).norm_sub_starProjection_harmonic_le hcj hq'
    rw [starProjection_congr (H.harmonic_eq j) q] at e
    exact e.trans_eq (congrArg (fun x => ‖(H.harmonic j).starProjection q - x‖)
      ((F.π h).extend_apply
        ⟨_, H.harmonic_le_domain j (Submodule.starProjection_apply_mem _ q)⟩))
  · -- Thm 3.4 under the strict gap
    have hlt' : ∀ q ∈ H.toFeec.harmonic j, q ≠ 0 → ‖q - (G.π h).π j q‖ < ‖q‖ := fun q hq hq0 => by
      rw [H.harmonic_eq] at hq
      exact (congrArg (fun x => ‖q - x‖)
        ((F.π h).extend_apply ⟨q, H.harmonic_le_domain j hq⟩)).trans_lt (hlt q hq hq0)
    have hi := (F.V h).cohomologyIncl_bijective (F.π h) ((G.π h).cohomologyMap_injective hcj hlt')
    exact ⟨(F.π h).bijective_cohomologyMap hi, hi⟩
  · have := hFD ‹_›
    have h0 := V.harmonicGap (SubcomplexFamily.approximates_toFeec ha)
    simp only [hgap] at h0
    exact h0
  · have := hFD ‹_›
    filter_upwards [V.cohomology (SubcomplexFamily.approximates_toFeec ha)] with h hh
    have hi := (F.V h).cohomologyIncl_bijective (F.π h) hh.1
    exact ⟨(F.π h).bijective_cohomologyMap hi, hi⟩
  · intro h v hv hz
    have h1 : ‖v‖ ≤ K * ‖H.d j (j + 1) ⟨v, (F.V h).le_domain j (j + 1) hv⟩‖ :=
      (G.π h).norm_le_of_forall_inner_eq_zero_of_graph (rel_add_one j) hPj hc0 (hCj h) hv
        fun y hy => hz y ⟨hy.1, by rw [← H.cycles_eq]; exact hy.2⟩
    have hb := norm_nonneg (H.d j (j + 1) ⟨v, (F.V h).le_domain j (j + 1) hv⟩)
    have h2 := pow_le_pow_left₀ (norm_nonneg v) h1 2
    have hΦ : 1 + K ^ 2 ≤ (256 * (1 + K ^ 2) * (1 + c) ^ 2) ^ 2 :=
      (by linarith : 1 + K ^ 2 ≤ 256 * (1 + K ^ 2) * (1 + c) ^ 2).trans
        (le_self_pow₀ (by linarith) two_ne_zero)
    unfold graphNorm
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow] at h2 ⊢
    have := mul_le_mul_of_nonneg_right hΦ (sq_nonneg
      ‖H.d j (j + 1) ⟨v, (F.V h).le_domain j (j + 1) hv⟩‖)
    linarith
  · obtain ⟨h1, h2, h3⟩ := uq hx (hsol f)
    exact Prod.ext h1 (Prod.ext h2 h3)
  · obtain ⟨h1, h2, h3⟩ := uqh h hx (hdsol h f)
    exact Prod.ext h1 (Prod.ext h2 h3)
  · -- the uniform discrete inf-sup condition, from `Feec`'s for the discrete mixed form
    intro h σ u p hσ hu hp
    obtain ⟨τ, v, q, h1, h2, h3, h4, h5⟩ :=
      (F.V h).infSup_of_feec (F.π h) hc hPi hPj (hCi h) (hCj h) σ u p hσ hu hp
    refine ⟨τ, v, q, h1, h2, h3, h4, ?_⟩
    have hK0 : 0 < K := by linarith
    have e : H.mixedNorm₃ j σ u p ^ 2 =
        256 * K ^ 2 * (1 / (16 * K ^ 2) / 16 * H.mixedNorm₃ j σ u p ^ 2) := by
      field_simp; ring
    rw [e]
    refine (mul_le_mul_of_nonneg_left h5 (by positivity)).trans
      (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    linarith
  · -- stability, from `Feec`'s stability for the data `P_{Vₕ} f`
    intro h f σh uh ph hsh
    obtain ⟨h1, h2, h3⟩ := uqh h hsh (hdsol h f)
    rw [h1, h2, h3]
    have p1 := (G.π h).poincare_toHilbertComplex_of_graph (rel_sub_one j) hPi hc0 (hCi h)
    have p2 := (G.π h).poincare_toHilbertComplex_of_graph (rel_add_one j) hPj hc0 (hCj h)
    have hx := (F.V h).toFeec.toHilbertComplex.norm_le_of_mixed (rel_sub_one j) (rel_add_one j)
      hK p1 p2
      ((F.V h).toFeec.toHilbertComplex.mixedForm_mixedSolution (rel_sub_one j) (rel_add_one j)
        ((F.V h).toFeec.closedRangeAt _) ((F.V h).toFeec.closedRangeAt _)
        (((F.V h).toFeec.V j).orthogonalProjectionOnto f))
    have hPf : ‖((F.V h).toFeec.V j).orthogonalProjectionOnto f‖ ≤ ‖f‖ :=
      ((F.V h).toFeec.V j).norm_orthogonalProjectionOnto_apply_le f
    refine ((F.V h).mixedNorm_le_of_norm_le _
      (hx.trans (mul_le_mul_of_nonneg_left hPf (by positivity)))).trans ?_
    have := mul_le_mul_of_nonneg_right (show 32 * K ^ 2 ≤ 256 * (1 + K ^ 2) * (1 + c) ^ 2 by
      linarith) (norm_nonneg f)
    linarith
  · intro f σ u p hs h σh uh ph hsh
    obtain ⟨rfl, rfl, rfl⟩ := uq hs (hsol f)
    obtain ⟨h1, h2, h3⟩ := uqh h hsh (hdsol h f)
    rw [h1, h2, h3, mixedError_domainCoord]
    set X := H.toFeec.mixedSolution (rel_sub_one j) (rel_add_one j) hcj hck f
    have e : (G.V h).mixedError (rel_sub_one j) (rel_add_one j) f X.fst X.snd.fst X.snd.snd ≤ _ :=
      (G.π h).norm_sub_le_infDist_harmonicGap (rel_sub_one j) (rel_add_one j) hc hPi hPj
      (hCi h) (hCj h)
      (H.toFeec.isMixedSolution_mixedSolution (rel_sub_one j) (rel_add_one j) hcj hck f)
    have a1 := (F.V h).infDist_domainSub_le (rel_sub_one j) X.fst
    have a2 := (F.V h).infDist_domainSub_le (rel_add_one j) X.snd.fst
    have a3 := ((G.π h).infDist_harmonicW_le (rel_add_one j) hc0 (hCj h)
      X.snd.snd.2).trans (mul_le_mul_of_nonneg_left
        ((F.V h).infDist_cycles_le (H.toFeec.harmonic_le_cycles j X.snd.snd.2)
          (H.harmonic_le_domain j hs.mem.2.2)) (by linarith))
    have hBc := congrArg Submodule.topologicalClosure (H.boundaries_eq j)
    have hbz : (H.boundaries j).topologicalClosure.starProjection
        (H.toFeec.domainIncl j X.snd.fst) ∈ H.toFeec.cycles j := by
      rw [← starProjection_congr hBc]
      exact H.toFeec.closure_boundaries_le_cycles j (Submodule.starProjection_apply_mem _ _)
    have eb : H.toFeec.boundaryPart j (H.toFeec.domainIncl j X.snd.fst) =
        Feec.HilbertComplex.cyclesToDomainSpace hbz :=
      H.toFeec.domainIncl_injective j (by
        rw [Feec.HilbertComplex.domainIncl_cyclesToDomainSpace]
        exact starProjection_congr hBc _)
    have a4 := (F.V h).infDist_cycles_le hbz (H.topologicalClosure_boundaries_le_domain j
      (Submodule.starProjection_apply_mem _ _))
    rw [eb] at e
    have hμ := (G.π h).harmonicGap_nonneg j
    rw [hgap h] at e hμ
    have g1 := Metric.infDist_nonneg (x := X.fst) (s := ((F.V h).toFeec.domainSub (j - 1) : Set _))
    have g2 := Metric.infDist_nonneg (x := X.snd.fst) (s := ((F.V h).toFeec.domainSub j : Set _))
    have g4 := Metric.infDist_nonneg (x := Feec.HilbertComplex.cyclesToDomainSpace hbz)
      (s := ((F.V h).toFeec.domainSub j : Set _))
    have key : ∀ {a b c d A B P D μ C' : ℝ}, a ≤ A → b ≤ B → c ≤ (1 + C') * P → d ≤ D →
        0 ≤ μ → 0 ≤ C' → 0 ≤ a → 0 ≤ b → 0 ≤ d →
        a + b + c + μ * d ≤ (1 + C') * (A + B + P + μ * D) := by
      intro a b c d A B P D μ C' h1 h2 h3 h4 h5 h6 h7 h8 h9
      nlinarith [mul_le_mul_of_nonneg_left h4 h5, mul_nonneg h6 (h7.trans h1),
        mul_nonneg h6 (h8.trans h2), mul_nonneg h6 (mul_nonneg h5 (h9.trans h4))]
    have hK' : (1 + 144 * (c * √(1 + cP ^ 2)) ^ 2) * (1 + c) * (1 + c) ≤
        256 * (1 + K ^ 2) * (1 + c) ^ 2 := by
      show (1 + 144 * K ^ 2) * (1 + c) * (1 + c) ≤ _
      rw [mul_assoc, ← _root_.sq]
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    refine e.trans (le_trans ?_ (mul_le_mul_of_nonneg_right hK' (add_nonneg (add_nonneg
      (add_nonneg ((F.V h).graphDist_nonneg _) ((F.V h).graphDist_nonneg _))
      ((F.V h).graphDist_nonneg _)) (mul_nonneg hμ ((F.V h).graphDist_nonneg _)))))
    rw [mul_assoc ((1 + 144 * (c * √(1 + cP ^ 2)) ^ 2) * (1 + c)) (1 + c)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact key a1 a2 a3 a4 hμ hc0 g1 g2 g4
  · obtain ⟨rfl, rfl, rfl⟩ := uq hs (hsol f)
    refine (V.converges (rel_sub_one j) (rel_add_one j)
      (SubcomplexFamily.approximates_toFeec ha) (SubcomplexFamily.approximates_toFeec ha')
      (H.toFeec.isMixedSolution_mixedSolution (rel_sub_one j) (rel_add_one j) hcj hck f)).congr
      fun h => ?_
    obtain ⟨h1, h2, h3⟩ := uqh h (hsh h) (hdsol h f)
    rw [h1, h2, h3, mixedError_domainCoord]
    rfl

end HilbertComplex

end FEEC
