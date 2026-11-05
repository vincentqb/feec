module

public import Solution.Electric
public import Feec.Models.Cube.AbsorbingTSD

/-!
# The bridge for the absorbing boundary conditions

The pairs `(E, B)` of real matrix fields on `Q = (0, ½)³` of `Challenge.lean` are the states of
`Feec.Models.Cube.Absorbing` (`eAbs`); along this identification:

* the energy space `IsEnergy` (the `ε`-closure of the triples of `C¹` fields) is
  `Feec.Models.Cube.Absorbing.energySpace` (`isEnergy_iff`): the span of the triples is the set of
  the triples (`tripleSub`), and the squared distance to a triple is the sum of the squared `L²`
  distances (`norm_sub_triple_sq`);
* `IsAbsorbing` is the graph of the impedance generator `Feec.Models.Cube.Absorbing.absorbing`
  (`isAbsorbing_iff`): its weak equation against all of the energy space follows from the one
  against the `C¹` triples by density;
* the orbits of the absorbing semigroup are mild solutions (`isMildSolution_orbit`), and the only
  ones (`isMildSolution_eq_orbit`).

## References

* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003], §1.4, §4.6

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set LinearPMap
open scoped InnerProductSpace

@[expose] public noncomputable section

namespace FEEC.ConstraintPropagation

open Feec Feec.Domain Feec.Models.BoundedDomain
open Feec.Models.Cube.Geometry (Q measurableSet_Q)
open Feec.Models.Cube.Absorbing (isBounded_Q)
open Feec.Models.Cube.Absorbing (MQ Amb Bdry C1Field energySpace absorbing absorbingSemigroup
  cL2 cField tanTrace tanFun impedanceTriple fieldMap curlMap traceMap)

/-- The pairs `(E, B)` of the challenge as states of `Feec.Models.Cube.Absorbing`. -/
def eAbs : (MQ × MQ) ≃L[ℝ] Feec.Models.Cube.Absorbing.State where
  toFun U := WithLp.toLp 2 U
  invFun x := x.ofLp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := WithLp.prod_continuous_toLp 2 MQ MQ
  continuous_invFun := WithLp.prod_continuous_ofLp 2 MQ MQ

@[simp] theorem eAbs_fst (U : MQ × MQ) : (eAbs U).fst = U.1 := rfl
@[simp] theorem eAbs_snd (U : MQ × MQ) : (eAbs U).snd = U.2 := rfl

/-! ### Linearity of the triples -/

theorem cL2_congr {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) {f g : (Fin n → ℝ) → ℝ} (h : f = g) (hf : Continuous f)
    (hg : Continuous g) : cL2 hΩ hb hf = cL2 hΩ hb hg := by
  subst h; rfl

theorem cL2_add {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) {f g : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    (hg : Continuous g) : cL2 hΩ hb (hf.add hg) = cL2 hΩ hb hf + cL2 hΩ hb hg :=
  MemLp.toLp_add _ _

theorem cL2_smul {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (c : ℝ) {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    cL2 hΩ hb (hf.const_smul c) = c • cL2 hΩ hb hf :=
  MemLp.toLp_const_smul _ _

theorem cL2_zero {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) :
    cL2 hΩ hb (continuous_const : Continuous fun _ : Fin n → ℝ => (0 : ℝ)) = 0 :=
  MemLp.toLp_zero _

/-- The sum of two `C¹` fields. -/
def C1add (Φ Ψ : C1Field) : C1Field := ⟨Φ.1 + Ψ.1, fun ij => (Φ.2 ij).add (Ψ.2 ij)⟩

/-- A multiple of a `C¹` field. -/
def C1smul (c : ℝ) (Φ : C1Field) : C1Field := ⟨c • Φ.1, fun ij => (Φ.2 ij).const_smul c⟩

/-- The zero `C¹` field. -/
def C1zero : C1Field := ⟨0, fun _ => contDiff_const⟩

theorem curlM_add (Φ Ψ : C1Field) : curlM (C1add Φ Ψ).1 = curlM Φ.1 + curlM Ψ.1 := by
  funext ij x
  have hd : ∀ (Θ : C1Field) (p : Ix), DifferentiableAt ℝ (Θ.1 p) x :=
    fun Θ p => ((Θ.2 p).differentiable one_ne_zero) x
  simp only [curlM, C1add, partialDeriv, Pi.add_apply]
  rw [fderiv_add (hd Φ _) (hd Ψ _), fderiv_add (hd Φ _) (hd Ψ _)]
  simp only [_root_.add_apply]
  ring

theorem curlM_smul (c : ℝ) (Φ : C1Field) : curlM (C1smul c Φ).1 = c • curlM Φ.1 := by
  funext ij x
  have hd : ∀ p : Ix, DifferentiableAt ℝ (Φ.1 p) x := fun p => ((Φ.2 p).differentiable one_ne_zero) x
  simp only [curlM, C1smul, partialDeriv, Pi.smul_apply]
  rw [fderiv_const_smul (hd _), fderiv_const_smul (hd _)]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

theorem curlM_zero : curlM C1zero.1 = 0 := by
  funext ij x
  simp [curlM, C1zero, partialDeriv]

theorem triple_add (Φ Ψ : C1Field) : (C1add Φ Ψ).triple = Φ.triple + Ψ.triple := by
  refine withLp_prod_ext ?_ (withLp_prod_ext ?_ ?_)
  · refine PiLp.ext fun ij => ?_
    exact cL2_add measurableSet_Q isBounded_Q (Φ.continuous ij) (Ψ.continuous ij)
  · refine PiLp.ext fun ij => ?_
    change cL2 measurableSet_Q isBounded_Q
        (Feec.Models.Cube.Absorbing.continuous_curlM (C1add Φ Ψ).2 ij) =
      cL2 measurableSet_Q isBounded_Q (Feec.Models.Cube.Absorbing.continuous_curlM Φ.2 ij) +
        cL2 measurableSet_Q isBounded_Q (Feec.Models.Cube.Absorbing.continuous_curlM Ψ.2 ij)
    rw [cL2_congr measurableSet_Q isBounded_Q (congrFun (curlM_add Φ Ψ) ij) _
      ((Feec.Models.Cube.Absorbing.continuous_curlM Φ.2 ij).add
        (Feec.Models.Cube.Absorbing.continuous_curlM Ψ.2 ij))]
    exact cL2_add measurableSet_Q isBounded_Q _ _
  · refine PiLp.ext fun q => ?_
    exact cL2_add measurableSet_Q isBounded_Q (Feec.Models.Cube.Absorbing.continuous_tanFun Φ.continuous q)
      (Feec.Models.Cube.Absorbing.continuous_tanFun Ψ.continuous q)

theorem triple_smul (c : ℝ) (Φ : C1Field) : (C1smul c Φ).triple = c • Φ.triple := by
  refine withLp_prod_ext ?_ (withLp_prod_ext ?_ ?_)
  · refine PiLp.ext fun ij => ?_
    exact cL2_smul measurableSet_Q isBounded_Q c (Φ.continuous ij)
  · refine PiLp.ext fun ij => ?_
    change cL2 measurableSet_Q isBounded_Q
        (Feec.Models.Cube.Absorbing.continuous_curlM (C1smul c Φ).2 ij) =
      c • cL2 measurableSet_Q isBounded_Q (Feec.Models.Cube.Absorbing.continuous_curlM Φ.2 ij)
    rw [cL2_congr measurableSet_Q isBounded_Q (congrFun (curlM_smul c Φ) ij) _
      ((Feec.Models.Cube.Absorbing.continuous_curlM Φ.2 ij).const_smul c)]
    exact cL2_smul measurableSet_Q isBounded_Q c _
  · refine PiLp.ext fun q => ?_
    exact cL2_smul measurableSet_Q isBounded_Q c (Feec.Models.Cube.Absorbing.continuous_tanFun Φ.continuous q)

theorem triple_zero : C1zero.triple = 0 := by
  refine withLp_prod_ext ?_ (withLp_prod_ext ?_ ?_)
  · refine PiLp.ext fun ij => ?_
    exact cL2_zero measurableSet_Q isBounded_Q
  · refine PiLp.ext fun ij => ?_
    change cL2 measurableSet_Q isBounded_Q
        (Feec.Models.Cube.Absorbing.continuous_curlM C1zero.2 ij) = 0
    rw [cL2_congr measurableSet_Q isBounded_Q (congrFun curlM_zero ij) _ continuous_const]
    exact cL2_zero measurableSet_Q isBounded_Q
  · refine PiLp.ext fun q => ?_
    exact cL2_zero measurableSet_Q isBounded_Q

/-- The triples of the `C¹` fields form a subspace. -/
def tripleSub : Submodule ℝ Amb where
  carrier := range C1Field.triple
  add_mem' := by
    rintro _ _ ⟨Φ, rfl⟩ ⟨Ψ, rfl⟩
    exact ⟨C1add Φ Ψ, triple_add Φ Ψ⟩
  zero_mem' := ⟨C1zero, triple_zero⟩
  smul_mem' := by
    rintro c _ ⟨Φ, rfl⟩
    exact ⟨C1smul c Φ, triple_smul c Φ⟩

theorem mem_energySpace_iff (z : Amb) :
    z ∈ energySpace ↔ z ∈ closure (range C1Field.triple) := by
  have hle : Submodule.span ℝ (range C1Field.triple) ≤ tripleSub :=
    Submodule.span_le.2 fun _ hx => hx
  have h : (Submodule.span ℝ (range C1Field.triple) : Set Amb) = range C1Field.triple :=
    Set.Subset.antisymm (fun _ hx => hle hx) Submodule.subset_span
  change z ∈ closure (Submodule.span ℝ (range C1Field.triple) : Set Amb) ↔ _
  rw [h]

/-! ### Norms -/

theorem norm_sub_cL2_sq {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (u : Feec.Domain.L2 ℝ Ω) {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    ‖u - cL2 hΩ hb hf‖ ^ 2 = ∫ x in Ω, ((u : (Fin n → ℝ) → ℝ) x - f x) ^ 2 := by
  unfold cL2
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub u ((Feec.Domain.memLp_of_continuous hΩ hb hf).toLp f),
    (Feec.Domain.memLp_of_continuous hΩ hb hf).coeFn_toLp] with x hx hx'
  rw [hx, Pi.sub_apply, hx', real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem norm_sub_triple_sq (E C : MQ) (β : Bdry) (Φ : C1Field) :
    ‖(WithLp.toLp 2 (E, WithLp.toLp 2 (C, β)) : Amb) - Φ.triple‖ ^ 2 =
      (∑ p, ∫ x in Q (Fin 3), ((E p : (Fin 3 → ℝ) → ℝ) x - Φ.1 p x) ^ 2) +
        (∑ p, ∫ x in Q (Fin 3), ((C p : (Fin 3 → ℝ) → ℝ) x - curlM Φ.1 p x) ^ 2) +
        (∑ q, ∫ y in Q (Fin 2), ((β q : (Fin 2 → ℝ) → ℝ) y - tanFun Φ.1 q y) ^ 2) := by
  set z : Amb := WithLp.toLp 2 (E, WithLp.toLp 2 (C, β))
  have hE : ‖(z - Φ.triple).fst‖ ^ 2 =
      ∑ p, ∫ x in Q (Fin 3), ((E p : (Fin 3 → ℝ) → ℝ) x - Φ.1 p x) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl fun p _ =>
      norm_sub_cL2_sq measurableSet_Q isBounded_Q (E p) (Φ.continuous p)
  have hC : ‖(z - Φ.triple).snd.fst‖ ^ 2 =
      ∑ p, ∫ x in Q (Fin 3), ((C p : (Fin 3 → ℝ) → ℝ) x - curlM Φ.1 p x) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl fun p _ =>
      norm_sub_cL2_sq measurableSet_Q isBounded_Q (C p)
        (Feec.Models.Cube.Absorbing.continuous_curlM Φ.2 p)
  have hβ : ‖(z - Φ.triple).snd.snd‖ ^ 2 =
      ∑ q, ∫ y in Q (Fin 2), ((β q : (Fin 2 → ℝ) → ℝ) y - tanFun Φ.1 q y) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl fun q _ =>
      norm_sub_cL2_sq measurableSet_Q isBounded_Q (β q)
        (Feec.Models.Cube.Absorbing.continuous_tanFun Φ.continuous q)
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2 (z - Φ.triple).snd, ← add_assoc,
    hE, hC, hβ]

/-- **`IsEnergy` is the energy space of `Feec`.** -/
theorem isEnergy_iff (E C : MQ) (β : Bdry) :
    IsEnergy E C β ↔ (WithLp.toLp 2 (E, WithLp.toLp 2 (C, β)) : Amb) ∈ energySpace := by
  rw [mem_energySpace_iff, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨Φ, hΦ, hlt⟩ := h (ε ^ 2) (by positivity)
    refine ⟨_, ⟨⟨Φ, hΦ⟩, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
    rw [norm_sub_triple_sq]
    exact hlt
  · intro h ε hε
    obtain ⟨_, ⟨Φ, rfl⟩, hlt⟩ := h (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    refine ⟨Φ.1, Φ.2, ?_⟩
    rw [dist_eq_norm] at hlt
    have h2 := pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
    rw [Real.sq_sqrt hε.le, norm_sub_triple_sq] at h2
    exact h2

/-! ### The absorbing generator -/

/-- The weak-equation functional `z ↦ ⟪w, z_E⟫ + ⟪P, z_C⟫ + ⟪β, z_β⟫` on the ambient space. -/
def weakFun (w P : MQ) (β : Bdry) : Amb →L[ℝ] ℝ :=
  (innerSL ℝ w).comp (WithLp.fstL 2 ℝ MQ _) +
    (innerSL ℝ P).comp ((WithLp.fstL 2 ℝ MQ Bdry).comp (WithLp.sndL 2 ℝ MQ _)) +
    (innerSL ℝ β).comp ((WithLp.sndL 2 ℝ MQ Bdry).comp (WithLp.sndL 2 ℝ MQ _))

theorem weakFun_apply (w P : MQ) (β : Bdry) (z : Amb) :
    weakFun w P β z = ⟪w, z.fst⟫_ℝ + ⟪P, z.snd.fst⟫_ℝ + ⟪β, z.snd.snd⟫_ℝ := rfl

theorem inner_cField_eq (w : MQ) (Ψ : C1Field) :
    ⟪w, Ψ.l2⟫_ℝ = ∑ p, ∫ x in cube 0 (1 / 2), (w p : (Fin 3 → ℝ) → ℝ) x * Ψ.1 p x := by
  refine (L2F.inner_def _ _).trans (Finset.sum_congr rfl fun p _ => ?_)
  exact Feec.Models.Cube.Absorbing.inner_cL2_right measurableSet_Q isBounded_Q (w p) (Ψ.continuous p)

theorem inner_curlL2_eq' (w : MQ) (Ψ : C1Field) :
    ⟪w, Ψ.curlL2⟫_ℝ = ∑ p, ∫ x in cube 0 (1 / 2), (w p : (Fin 3 → ℝ) → ℝ) x * curlF Ψ.1 p x := by
  refine (L2F.inner_def _ _).trans (Finset.sum_congr rfl fun p _ => ?_)
  exact Feec.Models.Cube.Absorbing.inner_cL2_right measurableSet_Q isBounded_Q (w p)
    (Feec.Models.Cube.Absorbing.continuous_curlM Ψ.2 p)

theorem inner_tan_eq (β : Bdry) (Ψ : C1Field) :
    ⟪β, Ψ.tan⟫_ℝ = ∑ q, ∫ y in cube 0 (1 / 2),
      (β q : (Fin 2 → ℝ) → ℝ) y * Ψ.1 (q.2.1, q.1.1.succAbove q.2.2) (faceMap q.1 y) := by
  refine (L2F.inner_def _ _).trans (Finset.sum_congr rfl fun q _ => ?_)
  exact Feec.Models.Cube.Absorbing.inner_cL2_right measurableSet_Q isBounded_Q (β q)
    (Feec.Models.Cube.Absorbing.continuous_tanFun Ψ.continuous q)

/-- **`IsAbsorbing` is the graph of the absorbing generator of `Feec`.** -/
theorem isAbsorbing_iff (U V : MQ × MQ) :
    IsAbsorbing U V ↔ (eAbs U, eAbs V) ∈ absorbing.graph := by
  unfold absorbing
  rw [impedanceTriple.mem_graph_op_iff]
  have hsmooth : ∀ (β : Bdry) (Ψ : C1Field),
      weakFun V.1 U.2 β Ψ.triple = 0 ↔
        ∑ p, ∫ x in cube 0 (1 / 2), (V.1 p : (Fin 3 → ℝ) → ℝ) x * Ψ.1 p x =
          -(∑ p, ∫ x in cube 0 (1 / 2), (U.2 p : (Fin 3 → ℝ) → ℝ) x * curlF Ψ.1 p x) -
            ∑ q, ∫ y in cube 0 (1 / 2),
              (β q : (Fin 2 → ℝ) → ℝ) y * Ψ.1 (q.2.1, q.1.1.succAbove q.2.2) (faceMap q.1 y) := by
    intro β Ψ
    rw [weakFun_apply]
    change ⟪V.1, Ψ.l2⟫_ℝ + ⟪U.2, Ψ.curlL2⟫_ℝ + ⟪β, Ψ.tan⟫_ℝ = 0 ↔ _
    rw [inner_cField_eq, inner_curlL2_eq', inner_tan_eq]
    constructor <;> intro h <;> linarith
  constructor
  · rintro ⟨β, hE, hw⟩
    have hz := (isEnergy_iff U.1 V.2 β).1 hE
    refine ⟨⟨_, hz⟩, rfl, rfl, fun v' => ?_⟩
    have hle : energySpace ≤ LinearMap.ker (weakFun V.1 U.2 β).toLinearMap := by
      refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) ?_
      · rintro _ ⟨Ψ, rfl⟩
        exact (hsmooth β Ψ).2 (hw Ψ.1 Ψ.2)
      · exact (weakFun V.1 U.2 β).isClosed_ker
    have h0 : weakFun V.1 U.2 β v' = 0 := hle v'.2
    rw [weakFun_apply] at h0
    change ⟪V.1, (v' : Amb).fst⟫_ℝ = -⟪U.2, (v' : Amb).snd.fst⟫_ℝ - ⟪β, (v' : Amb).snd.snd⟫_ℝ
    linarith
  · rintro ⟨v, h1, h2, h3⟩
    refine ⟨traceMap v, ?_, fun Ψ hΨ => ?_⟩
    · have hv : (v : Amb) = WithLp.toLp 2 (U.1, WithLp.toLp 2 (V.2, traceMap v)) :=
        withLp_prod_ext h1 (withLp_prod_ext h2 rfl)
      exact (isEnergy_iff _ _ _).2 (hv ▸ v.2)
    · have e := h3 ⟨_, Feec.Models.Cube.Absorbing.triple_mem_energySpace ⟨Ψ, hΨ⟩⟩
      refine (hsmooth (traceMap v) ⟨Ψ, hΨ⟩).1 ?_
      change ⟪V.1, C1Field.l2 ⟨Ψ, hΨ⟩⟫_ℝ = -⟪U.2, C1Field.curlL2 ⟨Ψ, hΨ⟩⟫_ℝ -
        ⟪traceMap v, C1Field.tan ⟨Ψ, hΨ⟩⟫_ℝ at e
      change ⟪V.1, C1Field.l2 ⟨Ψ, hΨ⟩⟫_ℝ + ⟪U.2, C1Field.curlL2 ⟨Ψ, hΨ⟩⟫_ℝ +
        ⟪traceMap v, C1Field.tan ⟨Ψ, hΨ⟩⟫_ℝ = 0
      linarith

/-! ### Mild solutions -/

theorem intervalIntegral_mapR {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (g : ℝ → E) (a t : ℝ) :
    ∫ τ in a..t, L (g τ) = L (∫ τ in a..t, g τ) := by
  simp only [intervalIntegral, L.integral_comp_comm, _root_.map_sub]

/-- **The orbits of the absorbing semigroup are mild solutions.** -/
theorem isMildSolution_orbit (x : Feec.Models.Cube.Absorbing.State) :
    IsMildSolution IsAbsorbing (Ici 0)
      fun t => (eAbs.symm (absorbingSemigroup.S t x) : Mat ℝ 0 (1 / 2) × Mat ℝ 0 (1 / 2)) := by
  refine ⟨eAbs.symm.continuous.comp_continuousOn (absorbingSemigroup.strongCont x),
    fun t ht => ?_⟩
  obtain ⟨hd, e⟩ := Feec.Models.Cube.Absorbing.integral_mem_domain x ht
  change IsAbsorbing (∫ τ in (0 : ℝ)..t, (eAbs.symm (absorbingSemigroup.S τ x) : MQ × MQ))
    ((eAbs.symm (absorbingSemigroup.S t x) : MQ × MQ) - eAbs.symm (absorbingSemigroup.S 0 x))
  refine (isAbsorbing_iff _ _).2 ?_
  have key : ((eAbs (∫ τ in (0 : ℝ)..t, eAbs.symm (absorbingSemigroup.S τ x)),
      eAbs (eAbs.symm (absorbingSemigroup.S t x) - eAbs.symm (absorbingSemigroup.S 0 x))) :
        Feec.Models.Cube.Absorbing.State × Feec.Models.Cube.Absorbing.State) =
      ((∫ τ in (0 : ℝ)..t, absorbingSemigroup.S τ x), absorbing ⟨_, hd⟩) := by
    rw [intervalIntegral_mapR, ContinuousLinearEquiv.apply_symm_apply,
      ← _root_.map_sub, ContinuousLinearEquiv.apply_symm_apply, absorbingSemigroup.map_zero,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, e]
  have hmem := absorbing.mem_graph ⟨_, hd⟩
  rw [← key] at hmem
  exact hmem

/-- **The mild solutions are the orbits of the absorbing semigroup.** The primitive `∫₀^· U` of
a mild solution and that of the orbit of `U 0` are strong solutions of `W' = A W + U 0` on
`[0, t]` vanishing at `0`, hence equal (`A` is dissipative); `U t - U 0` is `A` of either. -/
theorem isMildSolution_eq_orbit {U : ℝ → MQ × MQ} (hU : IsMildSolution IsAbsorbing (Ici 0) U)
    {t : ℝ} (ht : 0 ≤ t) : eAbs (U t) = absorbingSemigroup.S t (eAbs (U 0)) := by
  set x := eAbs (U 0)
  have hsol : ∀ w : ℝ → Feec.Models.Cube.Absorbing.State, ContinuousOn w (Ici 0) →
      (∀ τ ∈ Ici (0 : ℝ), ((∫ s in (0 : ℝ)..τ, w s), w τ - x) ∈ absorbing.graph) →
      Evolution.IsStrongSolution absorbing (Icc 0 t) (fun _ => x)
        (fun τ => ∫ s in (0 : ℝ)..τ, w s) := fun w hw hg =>
    Evolution.IsStrongSolution.of_deriv fun τ hτ => ⟨w τ - x, hg τ hτ.1, by
      simpa using hasDerivWithinAt_integral_of_continuousOn (hw.mono Icc_subset_Ici_self) hτ⟩
  have hgU : ∀ τ ∈ Ici (0 : ℝ),
      ((∫ s in (0 : ℝ)..τ, eAbs (U s)), eAbs (U τ) - x) ∈ absorbing.graph := fun τ hτ => by
    have := (isAbsorbing_iff _ _).1 (hU.2 τ hτ)
    convert this using 2
    · exact intervalIntegral_mapR eAbs U 0 τ
    · exact (_root_.map_sub eAbs _ _).symm
  have hgS : ∀ τ ∈ Ici (0 : ℝ), ((∫ s in (0 : ℝ)..τ, absorbingSemigroup.S s x),
      absorbingSemigroup.S τ x - x) ∈ absorbing.graph := fun τ hτ => by
    obtain ⟨hd, e⟩ := Feec.Models.Cube.Absorbing.integral_mem_domain x hτ
    rw [← e]
    exact absorbing.mem_graph ⟨_, hd⟩
  have e := (hsol _ (eAbs.continuous.comp_continuousOn hU.1) hgU).unique
    Feec.Models.Cube.Absorbing.isMDissipative_absorbing.dissipative (hsol _ (absorbingSemigroup.strongCont x) hgS)
    (by simp) ⟨ht, le_rfl⟩
  exact sub_left_inj.1 (absorbing.mem_graph_snd_inj (hgU t ht) (hgS t ht) e)

end FEEC.ConstraintPropagation
