module

public import Feec.HilbertComplex.Reducing

/-!
# The abstract Hodge wave equation: well-posedness and the weak formulation

For a closed densely defined `T` on a Hilbert space with `T T = 0` (the total differential of a
finite Hilbert complex, of any length and shape), the Hodge wave equation is
`U' = (T − T†) U + F`. Its generator `T − T†` is skew-adjoint
(`LinearPMap.isSkewAdjoint_sub_adjoint`), so the problem is well posed, and it has a **weak
formulation** with test space `D(T)` only:

`⟪U', ψ⟫ = ⟪T U, ψ⟫ − ⟪U, T ψ⟫ + ⟪F, ψ⟫` for all `ψ ∈ D(T)`, with `U(t) ∈ D(T)`.

For a short complex `W₀ → W₁ → W₂` the test space `D(𝐝) = V₀ × V₁ × W₂` is that of Thesis
(4.7)/(4.8).

## Main definitions

* `Feec.HodgeWave.IsWeakSolution T I F U`, `Feec.HodgeWave.IsClassicalWeakSolution T I F U`
  (additionally `t ↦ T U(t)` and `U'` continuous: `U ∈ C⁰(I; D(T)) ∩ C¹(I; W)`).
* `Feec.HilbertComplex.HodgeWave.IsWeakSolution H := Feec.HodgeWave.IsWeakSolution H.totalD`.

## Main results

* `HodgeWave.existsUnique`: for `U₀ ∈ D(T − T†)` and admissible forcing, a classical solution
  exists, it is unique among strong solutions, and it is the unique weak solution; for `F = 0`
  it conserves energy. Thesis: Thm 4.6 (no closed range; any length).
* `HodgeWave.isWeakSolution_of_isStrongSolution`, `HodgeWave.IsWeakSolution.unique`,
  `HodgeWave.weak_iff_strong`, `HodgeWave.IsWeakSolution.isClassicalSolution`,
  `HodgeWave.classicalWeak_iff_classical`. Thesis: Thm 4.7.
* `HilbertComplex.HodgeWave.existsUnique`, `HilbertComplex.HodgeWave.weak_iff_strong`, ...:
  the same for the wave operator of every finite Hilbert complex, in particular every window
  `H.window a n` of a complex on `ℤ`.

## References

* [QuennevilleBelair2015], §4.4 ((4.4)–(4.8), Thm 4.6, Thm 4.7)
* [Pazy1983], §1.10 (Stone's theorem); [CazenaveHaraux1998], Prop 4.1.6
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

namespace Feec.HodgeWave

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] {T : E →ₗ.[𝕜] E} {I : Set ℝ} {F U V : ℝ → E}

/-- `U` is a **weak solution** of the Hodge wave equation `U' = (T − T†) U + F` on `I`:
`U t ∈ D(T)` and `⟪U' t, ψ⟫ = ⟪T U t, ψ⟫ − ⟪U t, T ψ⟫ + ⟪F t, ψ⟫` for every test `ψ ∈ D(T)`
(derivatives within `I`). Thesis: (4.7), (4.8) -/
structure IsWeakSolution (T : E →ₗ.[𝕜] E) (I : Set ℝ) (F U : ℝ → E) : Prop where
  mem : ∀ t ∈ I, U t ∈ T.domain
  deriv : ∀ t (ht : t ∈ I), ∃ U' : E, HasDerivWithinAt U U' I t ∧ ∀ ψ : T.domain,
    ⟪U', (ψ : E)⟫_𝕜 = ⟪T ⟨U t, mem t ht⟩, (ψ : E)⟫_𝕜 - ⟪U t, T ψ⟫_𝕜 + ⟪F t, (ψ : E)⟫_𝕜

/-- A weak solution in the class `C⁰(I; D(T)) ∩ C¹(I; E)`: additionally `t ↦ T U t` and `U'` are
continuous on `I`. Thesis: §4.4 -/
structure IsClassicalWeakSolution (T : E →ₗ.[𝕜] E) (I : Set ℝ) (F U : ℝ → E) : Prop
    extends IsWeakSolution T I F U where
  contD : ∃ G : ℝ → E, ContinuousOn G I ∧ ∀ t (ht : t ∈ I), T ⟨U t, mem t ht⟩ = G t
  c1 : ∃ D : ℝ → E, ContinuousOn D I ∧ ∀ t ∈ I, HasDerivWithinAt U (D t) I t

/-- Zero forcing is admissible. -/
theorem _root_.Feec.Evolution.ForcingClass.admissible_zero (A : E →ₗ.[𝕜] E) (a b : ℝ) :
    Evolution.ForcingClass.admissible A a b 0 :=
  Evolution.ForcingClass.contDomain.admissible ⟨fun _ _ => A.domain.zero_mem, continuousOn_const,
    0, continuousOn_const, fun _ _ => by convert A.map_zero⟩

theorem IsWeakSolution.continuousOn (h : IsWeakSolution T I F U) : ContinuousOn U I :=
  fun t ht => (h.deriv t ht).choose_spec.1.continuousWithinAt

/-- **Strong solutions are weak solutions.** Thesis: Thm 4.7 -/
theorem isWeakSolution_of_isStrongSolution [CompleteSpace E] (hT : Dense (T.domain : Set E))
    (hU : Evolution.IsStrongSolution (T - T†) I F U) : IsWeakSolution T I F U where
  mem t ht := (Submodule.mem_inf.1 (hU.mem_domain ht)).1
  deriv t ht := by
    refine ⟨_, hU.hasDerivWithinAt ht, fun ψ => ?_⟩
    have hm := Submodule.mem_inf.1 (hU.mem_domain ht)
    have hadj := adjoint_isFormalAdjoint hT ⟨U t, hm.2⟩ ψ
    change ⟪T ⟨U t, hm.1⟩ - T† ⟨U t, hm.2⟩ + F t, (ψ : E)⟫_𝕜 = _
    rw [inner_add_left, inner_sub_left, hadj]

/-- **Uniqueness of weak solutions** (energy argument with the test function `ψ = U − V`; no
hypothesis on `T`). Thesis: §4.4 (after (4.8)) -/
theorem IsWeakSolution.unique {a b : ℝ} (hU : IsWeakSolution T (Icc a b) F U)
    (hV : IsWeakSolution T (Icc a b) F V) (h0 : U a = V a) : EqOn U V (Icc a b) := by
  classical
  set e' : ℝ → E := fun t => if h : t ∈ Icc a b then
    (hU.deriv t h).choose - (hV.deriv t h).choose else 0
  have key := Evolution.Energy.norm_le_of_re_inner_deriv_nonpos (𝕜 := 𝕜) (e := U - V) (e' := e')
    (hU.continuousOn.sub hV.continuousOn) (fun t ht => ?_) (fun t ht => ?_)
  · intro t ht
    have := key t ht
    rw [Pi.sub_apply, Pi.sub_apply, h0, sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero]
      at this
    exact this
  · have ht' := Ico_subset_Icc_self ht
    simp only [e', ht', ↓reduceDIte]
    exact ((hU.deriv t ht').choose_spec.1.sub (hV.deriv t ht').choose_spec.1).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  · have ht' := Ico_subset_Icc_self ht
    simp only [e', ht', ↓reduceDIte]
    have hm : U t - V t ∈ T.domain := T.domain.sub_mem (hU.mem t ht') (hV.mem t ht')
    have k1 := (hU.deriv t ht').choose_spec.2 ⟨_, hm⟩
    have k2 := (hV.deriv t ht').choose_spec.2 ⟨_, hm⟩
    have hTe : T ⟨U t, hU.mem t ht'⟩ - T ⟨V t, hV.mem t ht'⟩ = T ⟨_, hm⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    have e1 : ⟪(hU.deriv t ht').choose - (hV.deriv t ht').choose, U t - V t⟫_𝕜 =
        ⟪T ⟨_, hm⟩, U t - V t⟫_𝕜 - ⟪U t - V t, T ⟨_, hm⟩⟫_𝕜 := by
      rw [inner_sub_left, k1, k2, ← hTe, inner_sub_left, inner_sub_left (U t)]
      ring
    rw [Pi.sub_apply, e1, _root_.map_sub, ← inner_conj_symm (U t - V t), RCLike.conj_re, sub_self]

variable [CompleteSpace E]

/-- **Energy conservation** for the homogeneous Hodge wave equation. Thesis: Thm 4.6 -/
theorem norm_eq {a b : ℝ} (hskew : (T - T†).IsSkewAdjoint)
    (hU : Evolution.IsStrongSolution (T - T†) (Icc a b) 0 U) : ∀ t ∈ Icc a b, ‖U t‖ = ‖U a‖ :=
  hU.norm_eq hskew.isSkewSymmetric

variable [IsScalarTower ℝ 𝕜 E]

section Nilpotent

variable (hT : Dense (T.domain : Set E)) (hc : T.IsClosed)
  (hmaps : ∀ x : T.domain, (T x : E) ∈ T.domain) (hcomp : ∀ x : T.domain, T ⟨T x, hmaps x⟩ = 0)
include hT hc hcomp

/-- **Well-posedness of the Hodge wave equation** `U' = (T − T†) U + F`: for `U₀ ∈ D(T − T†)`
and admissible forcing `F ∈ C([a,b]) ∩ (W^{1,1} ∪ L¹(D))`, there is a classical solution with
`U a = U₀`; it is unique among strong solutions and among weak solutions.
Thesis: Thm 4.6 (closed range not needed) -/
theorem existsUnique {U₀ : E} (hU₀ : U₀ ∈ (T - T†).domain) {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible (T - T†) a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (T - T†) (Icc a b) F U ∧
      (∀ V, V a = U₀ → Evolution.IsStrongSolution (T - T†) (Icc a b) F V → EqOn V U (Icc a b)) ∧
      ∀ V, V a = U₀ → IsWeakSolution T (Icc a b) F V → EqOn V U (Icc a b) := by
  obtain ⟨U, hU0, hU, huniq⟩ :=
    (isSkewAdjoint_sub_adjoint hT hc hmaps hcomp).existsUnique_classicalSolution hU₀ hF
  refine ⟨U, hU0, hU, huniq, fun V hV0 hV => hV.unique
    (isWeakSolution_of_isStrongSolution hT hU.toIsStrongSolution) (by rw [hV0, hU0])⟩

/-- **The homogeneous Hodge wave equation** (Thesis Thm 4.6): for `U₀ ∈ D(T − T†)`,
`U' = (T − T†) U`, `U a = U₀` has a classical solution on `[a, b]`, unique among strong and weak
solutions, and it conserves energy, `‖U t‖ = ‖U₀‖`. Thesis: Thm 4.6 -/
theorem existsUnique_hom {U₀ : E} (hU₀ : U₀ ∈ (T - T†).domain) (a b : ℝ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (T - T†) (Icc a b) 0 U ∧
      (∀ V, V a = U₀ → Evolution.IsStrongSolution (T - T†) (Icc a b) 0 V → EqOn V U (Icc a b)) ∧
      (∀ V, V a = U₀ → IsWeakSolution T (Icc a b) 0 V → EqOn V U (Icc a b)) ∧
      ∀ t ∈ Icc a b, ‖U t‖ = ‖U₀‖ := by
  obtain ⟨U, hU0, hU, h1, h2⟩ := existsUnique hT hc hmaps hcomp hU₀
    (Evolution.ForcingClass.admissible_zero _ a b)
  exact ⟨U, hU0, hU, h1, h2, fun t ht => (norm_eq (isSkewAdjoint_sub_adjoint hT hc hmaps hcomp)
    hU.toIsStrongSolution t ht).trans (by rw [hU0])⟩

/-- **Weak solutions are classical**: a weak solution with `U a ∈ D(T − T†)` and admissible
forcing is the classical solution. Thesis: Thm 4.7 -/
theorem IsWeakSolution.isClassicalSolution {U₀ : E} (hU₀ : U₀ ∈ (T - T†).domain) {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible (T - T†) a b F) (hU : IsWeakSolution T (Icc a b) F U)
    (hU0 : U a = U₀) : Evolution.IsClassicalSolution (T - T†) (Icc a b) F U := by
  obtain ⟨V, hV0, hV, -, hweak⟩ := existsUnique hT hc hmaps hcomp hU₀ hF
  have h := hweak U hU0 hU
  obtain ⟨G, hGc, hG⟩ := hV.deriv_cont
  exact ⟨hV.toIsStrongSolution.congr (fun t ht => (h ht).symm) fun _ _ => rfl, G, hGc,
    fun t ht => (h ht) ▸ hG t ht⟩

/-- **Weak and strong solutions coincide** for data in `D(T − T†)` and admissible forcing.
Thesis: Thm 4.7 -/
theorem weak_iff_strong {U₀ : E} (hU₀ : U₀ ∈ (T - T†).domain) {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible (T - T†) a b F) (hU0 : U a = U₀) :
    IsWeakSolution T (Icc a b) F U ↔ Evolution.IsStrongSolution (T - T†) (Icc a b) F U :=
  ⟨fun h => (h.isClassicalSolution hT hc hmaps hcomp hU₀ hF hU0).toIsStrongSolution,
    isWeakSolution_of_isStrongSolution hT⟩

omit hc [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- `R(T†) ⊥ R(T)`: `⟪T x, T† y⟫ = 0`. -/
theorem inner_apply_adjoint_apply (x : T.domain) (y : T†.domain) : ⟪T x, T† y⟫_𝕜 = 0 := by
  rw [← inner_conj_symm, adjoint_isFormalAdjoint hT y ⟨_, hmaps x⟩, hcomp, inner_zero_right,
    _root_.map_zero]

omit hc [IsScalarTower ℝ 𝕜 E] in
/-- **Classical solutions are classical weak solutions**: `T U` is the projection of
`(T − T†) U` onto `cl R(T)`, so it is continuous. Thesis: Thm 4.7 -/
theorem isClassicalWeakSolution_of_isClassicalSolution (hF : ContinuousOn F I)
    (hU : Evolution.IsClassicalSolution (T - T†) I F U) : IsClassicalWeakSolution T I F U := by
  obtain ⟨G, hGc, hG⟩ := hU.deriv_cont
  set K := (LinearMap.range T.toFun).topologicalClosure
  have : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hw := isWeakSolution_of_isStrongSolution hT hU.toIsStrongSolution
  refine ⟨hw, ⟨fun t => K.starProjection (G t), K.starProjection.continuous.comp_continuousOn hGc,
    fun t ht => ?_⟩, hU.continuousOn_deriv hF⟩
  have hm := Submodule.mem_inf.1 (hU.mem_domain ht)
  obtain ⟨hGt, e⟩ := Evolution.mem_graph_iff_exists.1 (hG t ht)
  beta_reduce
  rw [← e]
  change T ⟨U t, hm.1⟩ = K.starProjection (T ⟨U t, hm.1⟩ - T† ⟨U t, hm.2⟩)
  have h1 : T ⟨U t, hm.1⟩ ∈ K := Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ _)
  have h2 : K.starProjection (T† ⟨U t, hm.2⟩) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_closure,
      Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    exact inner_apply_adjoint_apply hT hmaps hcomp x _
  rw [_root_.map_sub, (K.starProjection_eq_self_iff).2 h1, h2, sub_zero]

/-- **Classical weak and classical solutions coincide** (Thesis Thm 4.7 with the thesis'
regularity classes `C⁰(D(T)) ∩ C¹(E)` and `C⁰(D(T − T†)) ∩ C¹(E)`). Thesis: Thm 4.7 -/
theorem classicalWeak_iff_classical {U₀ : E} (hU₀ : U₀ ∈ (T - T†).domain) {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible (T - T†) a b F) (hU0 : U a = U₀) :
    IsClassicalWeakSolution T (Icc a b) F U ↔
      Evolution.IsClassicalSolution (T - T†) (Icc a b) F U :=
  ⟨fun h => h.toIsWeakSolution.isClassicalSolution hT hc hmaps hcomp hU₀ hF hU0,
    isClassicalWeakSolution_of_isClassicalSolution hT hmaps hcomp hF.1⟩

end Nilpotent

end Feec.HodgeWave

/-! ### The Hodge wave equation of a finite Hilbert complex -/

namespace Feec.HilbertComplex.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  (H : HilbertComplex 𝕜 c W) {F U : ℝ → PiLp 2 W}

/-- A weak solution of the Hodge wave equation `U' = L U + F` of a finite Hilbert complex:
`U t ∈ D(𝐝)` and `⟪U', ψ⟫ = ⟪𝐝 U, ψ⟫ − ⟪U, 𝐝 ψ⟫ + ⟪F, ψ⟫` for all `ψ ∈ D(𝐝)`. For a short
complex, `D(𝐝) = V₀ × V₁ × W₂`. Thesis: (4.7), (4.8) -/
abbrev IsWeakSolution (I : Set ℝ) (F U : ℝ → PiLp 2 W) : Prop :=
  Feec.HodgeWave.IsWeakSolution H.totalD I F U

/-- A weak solution in `C⁰(I; D(𝐝)) ∩ C¹(I; W)`. -/
abbrev IsClassicalWeakSolution (I : Set ℝ) (F U : ℝ → PiLp 2 W) : Prop :=
  Feec.HodgeWave.IsClassicalWeakSolution H.totalD I F U

/-- **Thm 4.6 for every finite Hilbert complex**: for `U₀ ∈ D(L)` and admissible forcing,
`U' = L U + F`, `U a = U₀` has a classical solution on `[a, b]`, unique among strong and among
weak solutions. Applies to every window `H.window a n` of a complex on `ℤ`. Thesis: Thm 4.6 -/
theorem existsUnique {U₀ : PiLp 2 W} (hU₀ : U₀ ∈ H.wave.domain) {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible H.wave a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution H.wave (Icc a b) F U ∧
      (∀ V, V a = U₀ → Evolution.IsStrongSolution H.wave (Icc a b) F V → EqOn V U (Icc a b)) ∧
      ∀ V, V a = U₀ → IsWeakSolution H (Icc a b) F V → EqOn V U (Icc a b) := by
  rw [wave_eq] at hU₀ hF ⊢
  exact Feec.HodgeWave.existsUnique H.dense_totalDomain H.isClosed_totalD H.totalD_mapsTo
    H.totalD_comp_totalD hU₀ hF

omit [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- Energy conservation for the homogeneous Hodge wave equation of a finite complex. -/
theorem norm_eq {a b : ℝ} (hU : Evolution.IsStrongSolution H.wave (Icc a b) 0 U) :
    ∀ t ∈ Icc a b, ‖U t‖ = ‖U a‖ :=
  hU.norm_eq H.isSkewAdjoint_wave.isSkewSymmetric

/-- **The homogeneous Hodge wave equation of a finite Hilbert complex**: a classical solution,
unique among strong and weak solutions, conserving energy. Thesis: Thm 4.6 -/
theorem existsUnique_hom {U₀ : PiLp 2 W} (hU₀ : U₀ ∈ H.wave.domain) (a b : ℝ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution H.wave (Icc a b) 0 U ∧
      (∀ V, V a = U₀ → Evolution.IsStrongSolution H.wave (Icc a b) 0 V → EqOn V U (Icc a b)) ∧
      (∀ V, V a = U₀ → IsWeakSolution H (Icc a b) 0 V → EqOn V U (Icc a b)) ∧
      ∀ t ∈ Icc a b, ‖U t‖ = ‖U₀‖ := by
  rw [wave_eq] at hU₀ ⊢
  exact Feec.HodgeWave.existsUnique_hom H.dense_totalDomain H.isClosed_totalD H.totalD_mapsTo
    H.totalD_comp_totalD hU₀ a b

/-- **Thm 4.7 for every finite Hilbert complex**: strong and weak solutions coincide for data in
`D(L)` and admissible forcing. Thesis: Thm 4.7 -/
theorem weak_iff_strong {U₀ : PiLp 2 W} (hU₀ : U₀ ∈ H.wave.domain) {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible H.wave a b F) (hU0 : U a = U₀) :
    IsWeakSolution H (Icc a b) F U ↔ Evolution.IsStrongSolution H.wave (Icc a b) F U := by
  rw [wave_eq] at hU₀ hF ⊢
  exact Feec.HodgeWave.weak_iff_strong H.dense_totalDomain H.isClosed_totalD H.totalD_mapsTo
    H.totalD_comp_totalD hU₀ hF hU0

/-- Thm 4.7 with the thesis' regularity classes. Thesis: Thm 4.7 -/
theorem classicalWeak_iff_classical {U₀ : PiLp 2 W} (hU₀ : U₀ ∈ H.wave.domain) {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible H.wave a b F) (hU0 : U a = U₀) :
    IsClassicalWeakSolution H (Icc a b) F U ↔
      Evolution.IsClassicalSolution H.wave (Icc a b) F U := by
  rw [wave_eq] at hU₀ hF ⊢
  exact Feec.HodgeWave.classicalWeak_iff_classical H.dense_totalDomain H.isClosed_totalD
    H.totalD_mapsTo H.totalD_comp_totalD hU₀ hF hU0

omit [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- Strong solutions of the Hodge wave equation are weak solutions. -/
theorem isWeakSolution_of_isStrongSolution {I : Set ℝ}
    (hU : Evolution.IsStrongSolution H.wave I F U) : IsWeakSolution H I F U := by
  rw [wave_eq] at hU
  exact Feec.HodgeWave.isWeakSolution_of_isStrongSolution H.dense_totalDomain hU

end Feec.HilbertComplex.HodgeWave
