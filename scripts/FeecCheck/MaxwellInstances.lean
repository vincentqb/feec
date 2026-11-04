module

public import Feec.Instances.Maxwell
public import Feec.HilbertComplex.Approximation.ApproxComplexCrime

/-!
# Regression tests: the concrete Maxwell verdicts

Every Maxwell discretization is `feec F a`, the conforming window of a conforming family `F` with
the Gauss laws, and its conclusions are fields of the FEEC theorem `ConformingFamily.feec`
(`Feec.Instances.Maxwell.maxwellFEEC`, statement `Feec.Instances.Maxwell.Verdict`: the constrained
verdict with the Gauss-law fields) and, for rates, of `ConformingFamily.feec_rated` with the
Jackson estimates of the models. The examples below pin the concrete instances: each fails to
elaborate if the generic statement stops applying to a concrete discretization.

**Snapshots.** The per-instance statements deleted when the instances became corollaries of the
FEEC theorem are stated below verbatim, with the rate classes they mention (`regRate` and its
specializations `cubePMCRate`, …, `starPolyPECRate`) defined here as before, and derived from the
new API:

* the generic Maxwell headline statements `wellPosed`, `gauss_propagates`,
  `gauss_propagates_strong`, `converges`, `rate` (`wellPosed_old`, …): fields of `maxwellFEEC`;
* `zero_mem_regRate`, `rate_regRate`, the twelve `O(h)` and `O(h^{s+1})` rates `cubePMC_rate`, …,
  `starPolyPEC_rate` and the cube non-vacuity `zero_mem_cubePMCRate`, `zero_mem_cubePECRate`
  (`*_old`): the field `rate_wave` of `ConformingFamily.feec_rated` with the Jackson estimates of
  the models (the old rate classes are contained in the Jackson classes, with equal data for
  Whitney forms);
* the rates through the discrete complex `cubePMC_ofComplex_rate`, `cubePEC_ofComplex_rate` of
  `Feec.Instances.MaxwellComplex` (`*_old`): `ConstrainedFEEC.RateClass.norm_sub_ofComplex_le`;
* the `n = 3`, `a = 0` restatements of `Feec.Physics.Maxwell.CubeFEM` (`pmc_tendstoUniformlyOn`,
  `pmc_norm_sub_le_meshSize`, `pec_tendstoUniformlyOn`, `pec_norm_sub_le_meshSize`; `*_old`): the
  window theorems of the cube model they restated.

This file is part of the `FeecCheck` library, not of `Feec`.
-/

public section

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

noncomputable section

namespace FeecCheck.MaxwellInstances

open Feec Feec.HilbertComplex Feec.Instances.Maxwell
open Feec.FiniteElement (PolySeq PolyOrder)

/-! ### The concrete instances -/

section Torus

open Feec.Models.Torus.DeRham

variable (d : Type*) [Fintype d] [LinearOrder d] (a : ℕ)

example : Verdict (torusFamily d) a := maxwellFEEC _ a

example : (torus d a).toApprox.Verdict (torus d a).toCore := (torusFamily d).feec.wave a 3 _ _

example : ∀ t, ∀ x ∈ (torus d a).K, ((complex d).window a 3).waveGroup.S t x ∈ (torus d a).K :=
  (maxwellFEEC (torusFamily d) a).gauss_propagates

end Torus

section Cube

open Feec.Models.Cube

variable (n : ℕ) [NeZero n] (a : ℤ) (S : PolySeq)

example : Verdict (FEM.whitneyFamily n) a := maxwellFEEC _ a
example : Verdict (FEM.polyFamilyMin n S) a := maxwellFEEC _ a

example : (cubePMC n a).toApprox.Verdict (cubePMC n a).toCore :=
  (FEM.whitneyFamily n).feec.wave a 3 _ _
example : (cubePEC n a).toApprox.Verdict (cubePEC n a).toCore :=
  (FEM.whitneyFamilyMin n).feec.wave a 3 _ _
example : (cubePolyPMC n S a).toApprox.Verdict (cubePolyPMC n S a).toCore :=
  (FEM.polyFamily n S).feec.wave a 3 _ _
example : (cubePolyPEC n S a).toApprox.Verdict (cubePolyPEC n S a).toCore :=
  (FEM.polyFamilyMin n S).feec.wave a 3 _ _

example {x} (hx : x ∈ ((FEM.complex n).window a 3).wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution ((FEM.complex n).window a 3).wave (Icc 0 T) 0
      (fun t => ((FEM.complex n).window a 3).waveGroup.S t x) :=
  ((maxwellFEEC (FEM.whitneyFamily n) a).wellPosed hx T).1

example : ∀ t, ∀ x ∈ (cubePEC n a).K,
    ((FEM.complexMin n).window a 3).waveGroup.S t x ∈ (cubePEC n a).K :=
  (maxwellFEEC (FEM.whitneyFamilyMin n) a).gauss_propagates

example (T : ℝ) (x : ((FEM.complex n).window a 3).wave.domain) :
    TendstoUniformlyOn
      (fun N t => ((FEM.complex n).window a 3).totalD.graphFst
        ((cubePMC n a).discrete N (waveLift _ x) t))
      (fun t => ((FEM.complex n).window a 3).waveGroup.S t x) atTop (Icc 0 T) :=
  (maxwellFEEC (FEM.whitneyFamily n) a).converges x T

end Cube

section Parallelepiped

variable {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)
  (a : ℤ)

open Feec.Models.Parallelepiped in
example : Verdict (whitneyFamily A hA b) a := maxwellFEEC _ a

example : (paraPMC A hA b a).toApprox.Verdict (paraPMC A hA b a).toCore :=
  (Feec.Models.Parallelepiped.whitneyFamily A hA b).feec.wave a 3 _ _
example : (paraPEC A hA b a).toApprox.Verdict (paraPEC A hA b a).toCore :=
  (Feec.Models.Parallelepiped.whitneyFamilyMin A hA b).feec.wave a 3 _ _

end Parallelepiped

section StarShaped

open Feec.Models.StarShaped

variable {n : ℕ} [NeZero n] {D : StarDomain n} (M : MeshFamily D) (a : ℤ)

example : Verdict M.whitneyFamilyMin a := maxwellFEEC _ a

example : (starPMC M a).toApprox.Verdict (starPMC M a).toCore := M.whitneyFamily.feec.wave a 3 _ _
example : (starPEC M a).toApprox.Verdict (starPEC M a).toCore :=
  M.whitneyFamilyMin.feec.wave a 3 _ _

end StarShaped

/-! ### Snapshots: the generic Maxwell headline statements -/

section Generic

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α]
  [CharZero α] {V : α → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]

/-- `Maxwell.wellPosed`, verbatim: the field `wellPosed` of the constrained verdict, here with no
discretization (`constrainedFEEC_wellPosed`). -/
theorem wellPosed_old (H : HilbertComplex 𝕜 (ComplexShape.up α) V) (a : α)
    {x : PiLp 2 fun i : Fin 3 => V (a + i)} (hx : x ∈ (H.window a 3).wave.domain)
    (T : ℝ) :
    Evolution.IsClassicalSolution (H.window a 3).wave (Icc 0 T) 0
        (fun t => (H.window a 3).waveGroup.S t x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution (H.window a 3).wave (Icc 0 T) 0 U →
        EqOn U (fun t => (H.window a 3).waveGroup.S t x) (Icc 0 T)) ∧
      (∀ U, U 0 = x → HilbertComplex.HodgeWave.IsWeakSolution (H.window a 3) (Icc 0 T) 0 U →
        EqOn U (fun t => (H.window a 3).waveGroup.S t x) (Icc 0 T)) ∧
      ∀ t, ‖(H.window a 3).waveGroup.S t x‖ = ‖x‖ :=
  constrainedFEEC_wellPosed hx T

variable {H : HilbertComplex 𝕜 (ComplexShape.up α) V} {κ : Type*} (F : ConformingFamily H κ)
  (a : α)

/-- `Maxwell.gauss_propagates`, verbatim. -/
theorem gauss_propagates_old : ∀ t, ∀ x ∈ (feec F a).K,
    (H.window a 3).waveGroup.S t x ∈ (feec F a).K :=
  (maxwellFEEC F a).gauss_propagates

/-- `Maxwell.gauss_propagates_strong`, verbatim. -/
theorem gauss_propagates_strong_old {T : ℝ} {U : ℝ → PiLp 2 fun i : Fin 3 => V (a + i)}
    (h0 : U 0 ∈ (feec F a).K)
    (hU : Evolution.IsStrongSolution (H.window a 3).wave (Icc 0 T) 0 U) :
    ∀ t ∈ Icc 0 T, U t ∈ (feec F a).K :=
  (maxwellFEEC F a).gauss_propagates_strong h0 hU

/-- `Maxwell.converges`, verbatim. -/
theorem converges_old (T : ℝ) :
    (∀ x : (H.window a 3).wave.domain, TendstoUniformlyOn
      (fun h t => (H.window a 3).totalD.graphFst ((feec F a).discrete h (waveLift _ x) t))
      (fun t => (H.window a 3).waveGroup.S t x) F.l (Icc 0 T)) ∧
    ∀ x : PiLp 2 fun i : Fin 3 => V (a + i),
      (∀ ξh ξh' : κ → ℝ → (H.window a 3).totalD.GraphSpace,
        (∀ h, HodgeWave.IsSemidiscreteSolution ((feec F a).Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
        Tendsto (fun h => (H.window a 3).totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => (H.window a 3).totalD.graphFst (ξh h t))
          (fun t => (H.window a 3).waveGroup.S t x) F.l (Icc 0 T)) ∧
      ∃ ξh ξh' : κ → ℝ → (H.window a 3).totalD.GraphSpace,
        (∀ h, HodgeWave.IsSemidiscreteSolution ((feec F a).Kh h) (Icc 0 T) (ξh h) (ξh' h)) ∧
        Tendsto (fun h => (H.window a 3).totalD.graphFst (ξh h 0)) F.l (𝓝 x) :=
  have V := maxwellFEEC F a
  ⟨fun x => V.converges x T, fun x => ⟨fun ξh ξh' hξh h0 => V.converges_of_tendsto x ξh ξh' hξh h0,
    V.exists_tendsto x T⟩⟩

/-- `Maxwell.rate`, verbatim: the improved conforming rate `ConstrainedFEEC.rate_le`. -/
theorem rate_old {T : ℝ} (R : (feec F a).RateClass T) {x : PiLp 2 fun i : Fin 3 => V (a + i)}
    (hxR : x ∈ R.Data) (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(H.window a 3).waveGroup.S t x - (H.window a 3).totalD.graphFst
        ((feec F a).discrete h (waveLift _ ⟨x, R.mem_domain x hxR⟩) t)‖ ≤
      (1 + ellipticConst (H.window a 3)) * (1 + 2 * t) *
        (R.C * R.meshSize h ^ R.α * R.classNorm x) :=
  (feec F a).rate_le R hxR h ht

/-- The deleted `Maxwell.regRate` (`ConstrainedFEEC.RateClass.ofDegreewise` on the window), as it
was defined. -/
abbrev regRate (T : ℝ) (Reg : ∀ k, V k → Prop) (B : α → ℝ) (r : κ → ℝ) (Λ : ℝ)
    (happ : ∀ h k (x : V k), Reg k x → ∃ v, ∃ hv : v ∈ (F.V h).V k,
      ‖x - v‖ ≤ B k * Λ * r h ∧ ∀ j (hxj : x ∈ (H.d k j).domain),
        ‖H.d k j ⟨x - v, Submodule.sub_mem _ hxj ((F.V h).le_domain k j hv)⟩‖ ≤ B k * Λ * r h)
    (hB : ∀ k, 0 ≤ B k) (hΛ : 0 ≤ Λ) (hr : ∀ h, 0 ≤ r h) : (feec F a).RateClass T :=
  ConstrainedFEEC.RateClass.ofDegreewise (feec F a) T (fun i => Reg (a + i)) (fun i => B (a + i))
    r Λ (fun h i x hx => by
      obtain ⟨v, hv, h1, h2⟩ := happ h _ x hx
      exact ⟨v, hv, h1, fun j hxj => h2 _ hxj⟩) (fun _ => hB _) hΛ hr

variable {F a}

/-- `Maxwell.zero_mem_regRate`, verbatim. -/
theorem zero_mem_regRate_old {T : ℝ} {Reg : ∀ k, V k → Prop} {B : α → ℝ} {r : κ → ℝ} {Λ : ℝ}
    {happ hB hΛ hr} (h0 : ∀ k, Reg k 0) :
    (0 : PiLp 2 fun i : Fin 3 => V (a + i)) ∈ (regRate F a T Reg B r Λ happ hB hΛ hr).Data :=
  ConstrainedFEEC.RateClass.zero_mem_ofDegreewise fun _ => h0 _

/-- `Maxwell.rate_regRate`, verbatim. -/
theorem rate_regRate_old {T : ℝ} {Reg : ∀ k, V k → Prop} {B : α → ℝ} {r : κ → ℝ} {Λ : ℝ}
    {happ hB hΛ hr} {x : PiLp 2 fun i : Fin 3 => V (a + i)}
    (hx : x ∈ (regRate F a T Reg B r Λ happ hB hΛ hr).Data) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖(H.window a 3).waveGroup.S t x - (H.window a 3).totalD.graphFst
        ((feec F a).discrete h (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst (H.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, B (a + i)) * r h * Λ) := by
  refine ((feec F a).rate_le _ hx h ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofDegreewise, Real.rpow_one, Fintype.card_fin]
  ring

end Generic

/-! ### Snapshots: the per-instance rates, from `ConformingFamily.feec_rated` -/

section Rates

/-- A rate class of degreewise regular data is contained in that of a weaker regularity (the
deleted rate classes in the classes of the Jackson estimates). -/
theorem mem_ofDegreewise_of_imp {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]
    {c : ComplexShape ι} {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] [∀ i, NormedSpace ℝ (W i)]
    [∀ i, IsScalarTower ℝ 𝕜 (W i)] {H : HilbertComplex 𝕜 c W} {κ : Type*}
    {G : ConstrainedFEEC H κ} {T : ℝ} {Reg Reg' : ∀ i, W i → Prop} {B B' : ι → ℝ}
    {r r' : κ → ℝ} {Λ : ℝ} {happ hB hΛ hr happ' hB' hr'} (hR : ∀ i x, Reg i x → Reg' i x)
    {x : PiLp 2 W} (hx : x ∈ (ConstrainedFEEC.RateClass.ofDegreewise G T Reg B r Λ happ hB hΛ
      hr).Data) :
    x ∈ (ConstrainedFEEC.RateClass.ofDegreewise G T Reg' B' r' Λ happ' hB' hΛ hr').Data :=
  ⟨hx.1, fun t ht => ⟨⟨fun i => hR _ _ ((hx.2 t ht).1.1 i), fun i => hR _ _ ((hx.2 t ht).1.2 i)⟩,
    (hx.2 t ht).2⟩⟩

section Cube

open Models.Cube Feec.Domain Feec.ExteriorFibre

variable (n : ℕ) [NeZero n]

/-- The deleted `cubePMCRate`, as it was defined. -/
abbrev cubePMCRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (cubePMC n a).RateClass T :=
  regRate (FEM.whitneyFamily n) a T (fun k x => FEM.IsC2Form k Λ x) (FEM.interpBound n)
    FEM.meshSize Λ (fun N _ _ hx => hx.exists_mem_whitney_le hΛ N) (FEM.interpBound_nonneg n) hΛ
    fun N => (FEM.meshSize_pos N).le

/-- The deleted `cubePECRate`, as it was defined. -/
abbrev cubePECRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (cubePEC n a).RateClass T :=
  regRate (FEM.whitneyFamilyMin n) a T (fun k x => FEM.IsC2FormMin k Λ x) (FEM.interpBound n)
    FEM.meshSize Λ (fun N _ _ hx => hx.exists_mem_whitneyMin_le hΛ N) (FEM.interpBound_nonneg n) hΛ
    fun N => (FEM.meshSize_pos N).le

/-- The deleted `cubePolyPMCRate`, as it was defined. -/
abbrev cubePolyPMCRate (S : PolySeq) {s : ℕ} (hS : PolyOrder n S s) (a : ℤ) (T Λ : ℝ)
    (hΛ : 0 ≤ Λ) : (cubePolyPMC n S a).RateClass T :=
  regRate (FEM.polyFamily n S) a T (fun k x => FEM.IsCsForm s k Λ x) (FEM.polyInterpBound n S)
    (fun N => FEM.meshSize N ^ (s + 1)) Λ
    (fun N k _ hx => hx.exists_mem_poly_le (hS.polyOrderAt k) hΛ N)
    (FEM.polyInterpBound_nonneg S) hΛ fun N => pow_nonneg (FEM.meshSize_pos N).le _

/-- The deleted `cubePolyPECRate`, as it was defined. -/
abbrev cubePolyPECRate (S : PolySeq) {s : ℕ} (hS : PolyOrder n S s) (a : ℤ) (T Λ : ℝ)
    (hΛ : 0 ≤ Λ) : (cubePolyPEC n S a).RateClass T :=
  regRate (FEM.polyFamilyMin n S) a T (fun k x => FEM.IsCsFormMin s k Λ x)
    (FEM.polyInterpBound n S) (fun N => FEM.meshSize N ^ (s + 1)) Λ
    (fun N k _ hx => hx.exists_mem_polyMin_le (hS.polyOrderAt k) hΛ N)
    (FEM.polyInterpBound_nonneg S) hΛ fun N => pow_nonneg (FEM.meshSize_pos N).le _

variable {n} {a : ℤ}

/-- `cubePMC_rate`, verbatim. -/
theorem cubePMC_rate_old {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePMCRate n a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complex n).window a 3).waveGroup.S t x -
        ((FEM.complex n).window a 3).totalD.graphFst
          ((cubePMC n a).discrete N (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((FEM.complex n).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, FEM.interpBound n (a + i)) * FEM.meshSize N * Λ) := by
  refine (((FEM.whitneyFamily n).feec_rated (FEM.whitneyJackson n)).rate_wave a 3 _ _ () hΛ hx N
    ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofJackson, ConstrainedFEEC.RateClass.ofDegreewise,
    SubcomplexFamily.Jackson.window, FEM.whitneyJackson, Real.rpow_one, Fintype.card_fin]
  ring

/-- `cubePEC_rate`, verbatim. -/
theorem cubePEC_rate_old {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePECRate n a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complexMin n).window a 3).waveGroup.S t x -
        ((FEM.complexMin n).window a 3).totalD.graphFst
          ((cubePEC n a).discrete N (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((FEM.complexMin n).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, FEM.interpBound n (a + i)) * FEM.meshSize N * Λ) := by
  refine (((FEM.whitneyFamilyMin n).feec_rated (FEM.whitneyJacksonMin n)).rate_wave a 3 _ _ () hΛ
    hx N ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofJackson, ConstrainedFEEC.RateClass.ofDegreewise,
    SubcomplexFamily.Jackson.window, FEM.whitneyJacksonMin, Real.rpow_one, Fintype.card_fin]
  ring

/-- `cubePolyPMC_rate`, verbatim. -/
theorem cubePolyPMC_rate_old {S : PolySeq} {s : ℕ} {hS : PolyOrder n S s} {T Λ : ℝ}
    {hΛ : 0 ≤ Λ} {x} (hx : x ∈ (cubePolyPMCRate n S hS a T Λ hΛ).Data) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖((FEM.complex n).window a 3).waveGroup.S t x -
        ((FEM.complex n).window a 3).totalD.graphFst
          ((cubePolyPMC n S a).discrete N (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((FEM.complex n).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, FEM.polyInterpBound n S (a + i)) * FEM.meshSize N ^ (s + 1) * Λ) := by
  refine (((FEM.polyFamily n S).feec_rated (FEM.polyJackson n S)).rate_wave a 3 _ _ s hΛ
    (mem_ofDegreewise_of_imp (fun i _ hy => ⟨hS.polyOrderAt _, hy⟩) hx) N ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofJackson, ConstrainedFEEC.RateClass.ofDegreewise,
    SubcomplexFamily.Jackson.window, FEM.polyJackson, Real.rpow_one, Real.rpow_natCast,
    Fintype.card_fin]
  ring

/-- `cubePolyPEC_rate`, verbatim. -/
theorem cubePolyPEC_rate_old {S : PolySeq} {s : ℕ} {hS : PolyOrder n S s} {T Λ : ℝ}
    {hΛ : 0 ≤ Λ} {x} (hx : x ∈ (cubePolyPECRate n S hS a T Λ hΛ).Data) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖((FEM.complexMin n).window a 3).waveGroup.S t x -
        ((FEM.complexMin n).window a 3).totalD.graphFst
          ((cubePolyPEC n S a).discrete N (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((FEM.complexMin n).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, FEM.polyInterpBound n S (a + i)) * FEM.meshSize N ^ (s + 1) * Λ) := by
  refine (((FEM.polyFamilyMin n S).feec_rated (FEM.polyJacksonMin n S)).rate_wave a 3 _ _ s hΛ
    (mem_ofDegreewise_of_imp (fun i _ hy => ⟨hS.polyOrderAt _, hy⟩) hx) N ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofJackson, ConstrainedFEEC.RateClass.ofDegreewise,
    SubcomplexFamily.Jackson.window, FEM.polyJacksonMin, Real.rpow_one, Real.rpow_natCast,
    Fintype.card_fin]
  ring

/-- `zero_mem_cubePMCRate`, verbatim: `zero_mem_cubePMC_ofJackson` (equal data). -/
theorem zero_mem_cubePMCRate_old {T Λ : ℝ} (hΛ : 0 ≤ Λ) :
    (0 : PiLp 2 _) ∈ (cubePMCRate n a T Λ hΛ).Data :=
  zero_mem_cubePMC_ofJackson hΛ

/-- `zero_mem_cubePECRate`, verbatim: `zero_mem_cubePEC_ofJackson` (equal data). -/
theorem zero_mem_cubePECRate_old {T Λ : ℝ} (hΛ : 0 ≤ Λ) :
    (0 : PiLp 2 _) ∈ (cubePECRate n a T Λ hΛ).Data :=
  zero_mem_cubePEC_ofJackson hΛ

/-- `cubePMC_ofComplex_rate` (`Feec.Instances.MaxwellComplex`), verbatim. -/
theorem cubePMC_ofComplex_rate_old {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePMCRate n a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complex n).window a 3).waveGroup.S t x -
        (ApproxFEEC.ofComplex (cubePMC n a).toComplex).sol N
          (((ApproxFEEC.ofComplexCore (cubePMC n a).toComplex).cmp T).p x N 0) t‖ ≤
      ((cubePMCRate n a T Λ hΛ).toCrimeRate.C +
        (cubePMC n a).toComplex.toCrime.toFamily.boundConst *
          (cubePMCRate n a T Λ hΛ).toCrimeRate.C' * t) * (FEM.meshSize N * Λ) :=
  ((cubePMCRate n a T Λ hΛ).norm_sub_ofComplex_le hx N ht).trans_eq <| by
    change _ * (FEM.meshSize N ^ (1 : ℝ) * Λ) = _
    rw [Real.rpow_one]

/-- `cubePEC_ofComplex_rate` (`Feec.Instances.MaxwellComplex`), verbatim. -/
theorem cubePEC_ofComplex_rate_old {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePECRate n a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complexMin n).window a 3).waveGroup.S t x -
        (ApproxFEEC.ofComplex (cubePEC n a).toComplex).sol N
          (((ApproxFEEC.ofComplexCore (cubePEC n a).toComplex).cmp T).p x N 0) t‖ ≤
      ((cubePECRate n a T Λ hΛ).toCrimeRate.C +
        (cubePEC n a).toComplex.toCrime.toFamily.boundConst *
          (cubePECRate n a T Λ hΛ).toCrimeRate.C' * t) * (FEM.meshSize N * Λ) :=
  ((cubePECRate n a T Λ hΛ).norm_sub_ofComplex_le hx N ht).trans_eq <| by
    change _ * (FEM.meshSize N ^ (1 : ℝ) * Λ) = _
    rw [Real.rpow_one]

end Cube

section Parallelepiped

open Models.Cube Feec.Domain Feec.ExteriorFibre
open Models.Parallelepiped (complex complexMin domain IsC2Form IsC2FormMin IsCsForm IsCsFormMin
  rateBound rateBound_nonneg polyRateBound polyRateBound_nonneg whitneyFamily whitneyFamilyMin
  polyFamily polyFamilyMin whitneyJackson whitneyJacksonMin polyJackson polyJacksonMin)

variable {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-- The deleted `paraPMCRate`, as it was defined. -/
abbrev paraPMCRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (paraPMC A hA b a).RateClass T :=
  regRate (whitneyFamily A hA b) a T (fun k x => IsC2Form A hA b k Λ x) (rateBound A)
    FEM.meshSize Λ (fun N _ _ hx => hx.exists_mem_whitney_le A hA b hΛ N) (rateBound_nonneg A) hΛ
    fun N => (FEM.meshSize_pos N).le

/-- The deleted `paraPECRate`, as it was defined. -/
abbrev paraPECRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (paraPEC A hA b a).RateClass T :=
  regRate (whitneyFamilyMin A hA b) a T (fun k x => IsC2FormMin A hA b k Λ x) (rateBound A)
    FEM.meshSize Λ (fun N _ _ hx => hx.exists_mem_whitneyMin_le A hA b hΛ N) (rateBound_nonneg A)
    hΛ fun N => (FEM.meshSize_pos N).le

/-- The deleted `paraPolyPMCRate`, as it was defined. -/
abbrev paraPolyPMCRate (S : PolySeq) {s : ℕ} (hS : PolyOrder n S s) (a : ℤ) (T Λ : ℝ)
    (hΛ : 0 ≤ Λ) : (paraPolyPMC A hA b S a).RateClass T :=
  regRate (polyFamily A hA b S) a T (fun k x => IsCsForm A hA b s k Λ x) (polyRateBound A S s)
    (fun N => FEM.meshSize N ^ (s + 1)) Λ
    (fun N k _ hx => by
      obtain ⟨v, hv, h1, h2⟩ := hx.exists_mem_poly_le A hA b (hS.polyOrderAt k) hΛ N
      exact ⟨v, hv, (mul_assoc _ Λ _).symm ▸ h1, fun j hxj => (mul_assoc _ Λ _).symm ▸ h2 j hxj⟩)
    (polyRateBound_nonneg A S s) hΛ fun N => pow_nonneg (FEM.meshSize_pos N).le _

/-- The deleted `paraPolyPECRate`, as it was defined. -/
abbrev paraPolyPECRate (S : PolySeq) {s : ℕ} (hS : PolyOrder n S s) (a : ℤ) (T Λ : ℝ)
    (hΛ : 0 ≤ Λ) : (paraPolyPEC A hA b S a).RateClass T :=
  regRate (polyFamilyMin A hA b S) a T (fun k x => IsCsFormMin A hA b s k Λ x)
    (polyRateBound A S s) (fun N => FEM.meshSize N ^ (s + 1)) Λ
    (fun N k _ hx => by
      obtain ⟨v, hv, h1, h2⟩ := hx.exists_mem_polyMin_le A hA b (hS.polyOrderAt k) hΛ N
      exact ⟨v, hv, (mul_assoc _ Λ _).symm ▸ h1, fun j hxj => (mul_assoc _ Λ _).symm ▸ h2 j hxj⟩)
    (polyRateBound_nonneg A S s) hΛ fun N => pow_nonneg (FEM.meshSize_pos N).le _

variable {A hA b} {a : ℤ}

/-- `paraPMC_rate`, verbatim. -/
theorem paraPMC_rate_old {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (paraPMCRate A hA b a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((complex A b).window a 3).waveGroup.S t x -
        ((complex A b).window a 3).totalD.graphFst
          ((paraPMC A hA b a).discrete N (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((complex A b).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, rateBound A (a + i)) * FEM.meshSize N * Λ) := by
  refine (((whitneyFamily A hA b).feec_rated (whitneyJackson A hA b)).rate_wave a 3 _ _ () hΛ hx N
    ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofJackson, ConstrainedFEEC.RateClass.ofDegreewise,
    SubcomplexFamily.Jackson.window, whitneyJackson, Real.rpow_one, Fintype.card_fin]
  ring

/-- `paraPEC_rate`, verbatim. -/
theorem paraPEC_rate_old {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (paraPECRate A hA b a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((complexMin A b).window a 3).waveGroup.S t x -
        ((complexMin A b).window a 3).totalD.graphFst
          ((paraPEC A hA b a).discrete N (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((complexMin A b).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, rateBound A (a + i)) * FEM.meshSize N * Λ) := by
  refine (((whitneyFamilyMin A hA b).feec_rated (whitneyJacksonMin A hA b)).rate_wave a 3 _ _ ()
    hΛ hx N ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofJackson, ConstrainedFEEC.RateClass.ofDegreewise,
    SubcomplexFamily.Jackson.window, whitneyJacksonMin, Real.rpow_one, Fintype.card_fin]
  ring

/-- `paraPolyPMC_rate`, verbatim. -/
theorem paraPolyPMC_rate_old {S : PolySeq} {s : ℕ} {hS : PolyOrder n S s} {T Λ : ℝ}
    {hΛ : 0 ≤ Λ} {x} (hx : x ∈ (paraPolyPMCRate A hA b S hS a T Λ hΛ).Data) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖((complex A b).window a 3).waveGroup.S t x -
        ((complex A b).window a 3).totalD.graphFst
          ((paraPolyPMC A hA b S a).discrete N (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((complex A b).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, polyRateBound A S s (a + i)) * FEM.meshSize N ^ (s + 1) * Λ) := by
  refine (((polyFamily A hA b S).feec_rated (polyJackson A hA b S)).rate_wave a 3 _ _ s hΛ
    (mem_ofDegreewise_of_imp (fun i _ hy => ⟨hS.polyOrderAt _, hy⟩) hx) N ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofJackson, ConstrainedFEEC.RateClass.ofDegreewise,
    SubcomplexFamily.Jackson.window, polyJackson, Real.rpow_one, Real.rpow_natCast,
    Fintype.card_fin]
  ring

/-- `paraPolyPEC_rate`, verbatim. -/
theorem paraPolyPEC_rate_old {S : PolySeq} {s : ℕ} {hS : PolyOrder n S s} {T Λ : ℝ}
    {hΛ : 0 ≤ Λ} {x} (hx : x ∈ (paraPolyPECRate A hA b S hS a T Λ hΛ).Data) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖((complexMin A b).window a 3).waveGroup.S t x -
        ((complexMin A b).window a 3).totalD.graphFst
          ((paraPolyPEC A hA b S a).discrete N (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((complexMin A b).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, polyRateBound A S s (a + i)) * FEM.meshSize N ^ (s + 1) * Λ) := by
  refine (((polyFamilyMin A hA b S).feec_rated (polyJacksonMin A hA b S)).rate_wave a 3 _ _ s hΛ
    (mem_ofDegreewise_of_imp (fun i _ hy => ⟨hS.polyOrderAt _, hy⟩) hx) N ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofJackson, ConstrainedFEEC.RateClass.ofDegreewise,
    SubcomplexFamily.Jackson.window, polyJacksonMin, Real.rpow_one, Real.rpow_natCast,
    Fintype.card_fin]
  ring

end Parallelepiped

section StarShaped

open Models.Cube Models.StarShaped Feec.Domain Feec.ExteriorFibre

variable {n : ℕ} [NeZero n] {D : StarDomain n} (M : MeshFamily D)

/-- The deleted `starPMCRate`, as it was defined. -/
abbrev starPMCRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (starPMC M a).RateClass T :=
  regRate M.whitneyFamily a T (fun k x => D.IsC2Form k Λ x) M.interpBound
    (fun N => (M.mesh N).meshSize) Λ (fun N _ _ hx => M.exists_mem_whitney_le_of_isC2Form hx hΛ N)
    M.interpBound_nonneg hΛ fun N => (M.meshSize_pos N).le

/-- The deleted `starPECRate`, as it was defined. -/
abbrev starPECRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (starPEC M a).RateClass T :=
  regRate M.whitneyFamilyMin a T (fun k x => D.IsC2FormMin k Λ x) M.interpBound
    (fun N => (M.mesh N).meshSize) Λ
    (fun N _ _ hx => M.exists_mem_whitneyMin_le_of_isC2FormMin hx hΛ N) M.interpBound_nonneg hΛ
    fun N => (M.meshSize_pos N).le

/-- The deleted `starPolyPMCRate`, as it was defined. -/
abbrev starPolyPMCRate (S : PolySeq) {s : ℕ} (hS : PolyOrder n S s) (a : ℤ) (T Λ : ℝ)
    (hΛ : 0 ≤ Λ) : (starPolyPMC M S a).RateClass T :=
  regRate (M.polyFamily S) a T (fun k x => D.IsCsForm s k Λ x) (M.polyInterpBound S)
    (fun N => (M.mesh N).meshSize ^ (s + 1)) Λ
    (fun N k _ hx => M.exists_mem_poly_le_of_isCsForm S (hS.polyOrderAt k) hx hΛ N)
    (M.polyInterpBound_nonneg S) hΛ fun N => pow_nonneg (M.meshSize_pos N).le _

/-- The deleted `starPolyPECRate`, as it was defined. -/
abbrev starPolyPECRate (S : PolySeq) {s : ℕ} (hS : PolyOrder n S s) (a : ℤ) (T Λ : ℝ)
    (hΛ : 0 ≤ Λ) : (starPolyPEC M S a).RateClass T :=
  regRate (M.polyFamilyMin S) a T (fun k x => D.IsCsFormMin s k Λ x) (M.polyInterpBound S)
    (fun N => (M.mesh N).meshSize ^ (s + 1)) Λ
    (fun N k _ hx => M.exists_mem_polyMin_le_of_isCsFormMin S (hS.polyOrderAt k) hx hΛ N)
    (M.polyInterpBound_nonneg S) hΛ fun N => pow_nonneg (M.meshSize_pos N).le _

variable {M} {a : ℤ}

/-- `starPMC_rate`, verbatim. -/
theorem starPMC_rate_old {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (starPMCRate M a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(D.complex.window a 3).waveGroup.S t x -
        (D.complex.window a 3).totalD.graphFst
          ((starPMC M a).discrete N (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst (D.complex.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, M.interpBound (a + i)) * (M.mesh N).meshSize * Λ) := by
  refine ((M.whitneyFamily.feec_rated M.whitneyJackson).rate_wave a 3 _ _ () hΛ hx N
    ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofJackson, ConstrainedFEEC.RateClass.ofDegreewise,
    SubcomplexFamily.Jackson.window, MeshFamily.whitneyJackson, Real.rpow_one, Fintype.card_fin]
  ring

/-- `starPEC_rate`, verbatim. -/
theorem starPEC_rate_old {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (starPECRate M a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(D.complexMin.window a 3).waveGroup.S t x -
        (D.complexMin.window a 3).totalD.graphFst
          ((starPEC M a).discrete N (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst (D.complexMin.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, M.interpBound (a + i)) * (M.mesh N).meshSize * Λ) := by
  refine ((M.whitneyFamilyMin.feec_rated M.whitneyJacksonMin).rate_wave a 3 _ _ () hΛ hx N
    ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofJackson, ConstrainedFEEC.RateClass.ofDegreewise,
    SubcomplexFamily.Jackson.window, MeshFamily.whitneyJacksonMin, Real.rpow_one,
    Fintype.card_fin]
  ring

/-- `starPolyPMC_rate`, verbatim. -/
theorem starPolyPMC_rate_old {S : PolySeq} {s : ℕ} {hS : PolyOrder n S s} {T Λ : ℝ}
    {hΛ : 0 ≤ Λ} {x} (hx : x ∈ (starPolyPMCRate M S hS a T Λ hΛ).Data) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖(D.complex.window a 3).waveGroup.S t x -
        (D.complex.window a 3).totalD.graphFst
          ((starPolyPMC M S a).discrete N (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst (D.complex.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, M.polyInterpBound S (a + i)) * (M.mesh N).meshSize ^ (s + 1) * Λ) := by
  refine (((M.polyFamily S).feec_rated (M.polyJackson S)).rate_wave a 3 _ _ s hΛ
    (mem_ofDegreewise_of_imp (fun i _ hy => ⟨hS.polyOrderAt _, hy⟩) hx) N ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofJackson, ConstrainedFEEC.RateClass.ofDegreewise,
    SubcomplexFamily.Jackson.window, MeshFamily.polyJackson, Real.rpow_one, Real.rpow_natCast,
    Fintype.card_fin]
  ring

/-- `starPolyPEC_rate`, verbatim. -/
theorem starPolyPEC_rate_old {S : PolySeq} {s : ℕ} {hS : PolyOrder n S s} {T Λ : ℝ}
    {hΛ : 0 ≤ Λ} {x} (hx : x ∈ (starPolyPECRate M S hS a T Λ hΛ).Data) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖(D.complexMin.window a 3).waveGroup.S t x -
        (D.complexMin.window a 3).totalD.graphFst
          ((starPolyPEC M S a).discrete N (waveLift _ ⟨x, LinearPMap.domainSq_le_domain hx.1⟩) t)‖ ≤
      (1 + ellipticConst (D.complexMin.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, M.polyInterpBound S (a + i)) * (M.mesh N).meshSize ^ (s + 1) * Λ) := by
  refine (((M.polyFamilyMin S).feec_rated (M.polyJacksonMin S)).rate_wave a 3 _ _ s hΛ
    (mem_ofDegreewise_of_imp (fun i _ hy => ⟨hS.polyOrderAt _, hy⟩) hx) N ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofJackson, ConstrainedFEEC.RateClass.ofDegreewise,
    SubcomplexFamily.Jackson.window, MeshFamily.polyJacksonMin, Real.rpow_one, Real.rpow_natCast,
    Fintype.card_fin]
  ring

end StarShaped

end Rates

/-! ### Snapshots: `Feec.Physics.Maxwell.CubeFEM` -/

section CubeFEM

open Feec.Domain Feec.HilbertComplex Feec.Models.Cube.FEM

/-- `Feec.Maxwell.CubeFEM.pmc_tendstoUniformlyOn`, verbatim:
`Feec.Models.Cube.FEM.maxwell_exists_tendstoUniformlyOn_whitney`. -/
theorem pmc_tendstoUniformlyOn_old (t₀ t₁ : ℝ) (x : ((complex 3).window 0 3).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((complex 3).window 0 3).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((whitney 3 N).window 0 3).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney 3 N).window 0 3).graphSub)
        (((complex 3).window 0 3).totalD.toGraphSpace
          ⟨x, (((complex 3).window 0 3).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => ((complex 3).window 0 3).totalD.graphFst (ξh N t))
        (fun t => ((complex 3).window 0 3).waveGroup.S (t - t₀) x) Filter.atTop
        (Set.Icc t₀ t₁) :=
  maxwell_exists_tendstoUniformlyOn_whitney t₀ t₁ x

/-- `Feec.Maxwell.CubeFEM.pmc_norm_sub_le_meshSize`, verbatim:
`Feec.Models.Cube.FEM.norm_sub_le_meshSize_window_smooth`. -/
theorem pmc_norm_sub_le_meshSize_old {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complex 3).window 0 3).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complex 3).window 0 3).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((whitney 3 N).window 0 3).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney 3 N).window 0 3).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ s ∈ Set.Icc t₀ t₁, ∀ i : Fin 3,
      IsC2Form (0 + i) L (((complex 3).window 0 3).totalD.graphFst (ξ s) i) ∧
        IsC2Form (0 + i) L (((complex 3).window 0 3).totalD.graphFst (ξ' s) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complex 3).window 0 3).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complex 3).window 0 3).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          ((((3 : ℕ) : ℝ) + (3 : ℕ) * (3 : ℕ)) * (∑ i : Fin 3, interpBound 3 (0 + i)) * L *
            meshSize N) :=
  norm_sub_le_meshSize_window_smooth 0 3 hξ hξh h0 hL0 hreg N ht

/-- `Feec.Maxwell.CubeFEM.pec_tendstoUniformlyOn`, verbatim:
`Feec.Models.Cube.FEM.exists_tendstoUniformlyOn_windowMin_whitney`. -/
theorem pec_tendstoUniformlyOn_old (t₀ t₁ : ℝ) (x : ((complexMin 3).window 0 3).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((complexMin 3).window 0 3).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((whitneyMin 3 N).window 0 3).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitneyMin 3 N).window 0 3).graphSub)
        (((complexMin 3).window 0 3).totalD.toGraphSpace
          ⟨x, (((complexMin 3).window 0 3).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => ((complexMin 3).window 0 3).totalD.graphFst (ξh N t))
        (fun t => ((complexMin 3).window 0 3).waveGroup.S (t - t₀) x) Filter.atTop
        (Set.Icc t₀ t₁) :=
  exists_tendstoUniformlyOn_windowMin_whitney 0 3 t₀ t₁ x

/-- `Feec.Maxwell.CubeFEM.pec_norm_sub_le_meshSize`, verbatim:
`Feec.Models.Cube.FEM.norm_sub_le_meshSize_windowMin_smooth`. -/
theorem pec_norm_sub_le_meshSize_old {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complexMin 3).window 0 3).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complexMin 3).window 0 3).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((whitneyMin 3 N).window 0 3).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ =
      HodgeWave.ellipticProjection (((whitneyMin 3 N).window 0 3).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ s ∈ Set.Icc t₀ t₁, ∀ i : Fin 3,
      IsC2FormMin (0 + i) L (((complexMin 3).window 0 3).totalD.graphFst (ξ s) i) ∧
        IsC2FormMin (0 + i) L (((complexMin 3).window 0 3).totalD.graphFst (ξ' s) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complexMin 3).window 0 3).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complexMin 3).window 0 3).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 *
          ((((3 : ℕ) : ℝ) + (3 : ℕ) * (3 : ℕ)) * (∑ i : Fin 3, interpBound 3 (0 + i)) * L *
            meshSize N) :=
  norm_sub_le_meshSize_windowMin_smooth 0 3 hξ hξh h0 hL0 hreg N ht

end CubeFEM

end FeecCheck.MaxwellInstances

end
