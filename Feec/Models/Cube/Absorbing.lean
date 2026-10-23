module

public import Feec.Models.Cube.AbsorbingTrace
public import Feec.Semigroup.Impedance

/-!
# Absorbing boundary conditions for the row-wise Einstein–Bianchi system on the cube

The linearized Einstein–Bianchi system in the row-wise form of [QuennevilleBelair2015], §3.4,
`Ė = -curl B`, `Ḃ = curl E` for matrix fields `E, B : Q → ℝ^{3×3}` on `Q = (0, ½)³` (the curl acts
on the rows), with the **absorbing (Silver–Müller) boundary condition**

  `n × Eᵢ + (Bᵢ)_τ = 0` on `∂Q`, for every row `i`,

which sets the incoming characteristic fields `Eᵢ · τ + Bᵢ · (n × τ)` (every tangent `τ`) to zero
(at `{x₀ = ½}`: `E_{i1} + B_{i2} = 0`, `E_{i2} - B_{i1} = 0`). Equivalently `n × Bᵢ = (Eᵢ)_τ`, i.e.
`tanTrace E + fluxTrace B = 0` in `L²(∂Q)`.

## The realization

The **energy space** `energySpace` (row-wise `H_imp(curl)`) is the closure of the triples
`(E, curl E, E_τ)` of `C¹` fields in `L²(Q) ⊕ L²(Q) ⊕ L²(∂Q; τ)`. Its elements satisfy Green's
formula
`⟪C, Ψ⟫ - ⟪E, curl Ψ⟫ = ⟪β, fluxTrace Ψ⟫` against every `C¹` field `Ψ` on `ℝ³`
(`energySpace_le_greenTriples`): `C` is the weak curl of `E` and `β` its tangential trace, in
`L²(∂Q)`. With the
field, curl and trace maps it is an impedance triple (`impedanceTriple`): the field map is
injective because flux traces of `C¹` fields are dense in `L²(∂Q; τ)`
(`AbsorbingTrace`), and its range contains the test fields. The generator `absorbing` is the
impedance operator of `Feec.ImpedanceTriple`; it is **m-dissipative** (`isMDissipative_absorbing`)
and its contraction semigroup `absorbingSemigroup` **radiates**:
`‖S(t) u₀‖² = ‖u₀‖² - 2 ∫₀ᵗ ‖E(s)_τ‖²_{L²(∂Q)} ds` (`norm_sq_absorbingSemigroup`).

The smooth states with the boundary condition are in the domain: a `C¹` state `(E, B)` with
`tanTrace E + fluxTrace B = 0` is in `D(A)`, with `A (E, B) = (-curl B, curl E)` and boundary trace
`E_τ` (`mem_domain_of_smooth`; the converse for smooth states of the domain, and the core property
of the smooth states, are not proved). An explicit smooth state, an outgoing wave
`E₀₁ = -B₀₂ = 2 x₀ ψ(x₁, x₂)`, has nonzero trace on `{x₀ = ½}`, so the energy strictly
decreases from it (`Feec.Models.Cube.Absorbing.exists_inner_absorbing_neg`, in
`Feec.Models.Cube.AbsorbingTSD`).

`greenTriples` (triples satisfying Green's formula) contains the energy space; whether the two
coincide (density of smooth fields in `H_imp(curl)`, a "weak = strong" statement) is not used and
not proved.

## References

* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003], §1.4, §4.6
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.4 (the system), §4.10 (bounded domains)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Set MeasureTheory Filter Topology Feec.Domain Feec.Models.BoundedDomain

@[expose] public noncomputable section

namespace Feec.Models.Cube.Absorbing

open Geometry

/-- `L²(Q; ℝ^{3×3})`. -/
abbrev MQ := L2F ℝ (Q (Fin 3)) Ix

/-- The state space `L²(Q; ℝ^{3×3}) ⊕₂ L²(Q; ℝ^{3×3})` of pairs `(E, B)`. -/
abbrev State := WithLp 2 (MQ × MQ)

/-- The ambient space of the energy space: triples `(E, C, β)`. -/
abbrev Amb := WithLp 2 (MQ × WithLp 2 (MQ × Bdry))

/-- `C¹` matrix fields on `ℝ³`. -/
abbrev C1Field : Type := {Ψ : Ix → R3 → ℝ // ∀ ij, ContDiff ℝ 1 (Ψ ij)}

theorem C1Field.continuous (Ψ : C1Field) (ij : Ix) : Continuous (Ψ.1 ij) := (Ψ.2 ij).continuous

/-- The `L²(Q)` class of a `C¹` field. -/
def C1Field.l2 (Ψ : C1Field) : MQ := cField Ψ.continuous

/-- The `L²(Q)` class of its curl. -/
def C1Field.curlL2 (Ψ : C1Field) : MQ := cField (continuous_curlM Ψ.2)

/-- Its flux trace. -/
def C1Field.flux (Ψ : C1Field) : Bdry := fluxTrace Ψ.continuous

/-- Its tangential trace. -/
def C1Field.tan (Ψ : C1Field) : Bdry := tanTrace Ψ.continuous

/-- **Green's functional** of a `C¹` field:
`(E, C, β) ↦ ⟪C, Ψ⟫ - ⟪E, curl Ψ⟫ - ⟪β, fluxTrace Ψ⟫`. -/
def greenFun (Ψ : C1Field) : Amb →L[ℝ] ℝ :=
  (innerSL ℝ Ψ.l2).comp ((WithLp.fstL 2 ℝ MQ Bdry).comp (WithLp.sndL 2 ℝ MQ _)) -
    (innerSL ℝ Ψ.curlL2).comp (WithLp.fstL 2 ℝ MQ _) -
    (innerSL ℝ Ψ.flux).comp ((WithLp.sndL 2 ℝ MQ Bdry).comp (WithLp.sndL 2 ℝ MQ _))

theorem greenFun_apply (Ψ : C1Field) (z : Amb) :
    greenFun Ψ z = ⟪z.snd.fst, Ψ.l2⟫_ℝ - ⟪z.fst, Ψ.curlL2⟫_ℝ - ⟪z.snd.snd, Ψ.flux⟫_ℝ := by
  simp [greenFun, real_inner_comm]

/-- **Green triples**: triples `(E, C, β)` with `⟪C, Ψ⟫ - ⟪E, curl Ψ⟫ = ⟪β, fluxTrace Ψ⟫` for every
`C¹` field `Ψ` (`C` is the weak curl of `E` and `β` its tangential trace, in `L²(∂Q)`). -/
def greenTriples : Submodule ℝ Amb := ⨅ Ψ : C1Field, LinearMap.ker (greenFun Ψ).toLinearMap

theorem mem_greenTriples {z : Amb} :
    z ∈ greenTriples ↔ ∀ Ψ : C1Field,
      ⟪z.snd.fst, Ψ.l2⟫_ℝ - ⟪z.fst, Ψ.curlL2⟫_ℝ = ⟪z.snd.snd, Ψ.flux⟫_ℝ := by
  simp only [greenTriples, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    greenFun_apply, sub_eq_zero]

theorem isClosed_greenTriples : IsClosed (greenTriples : Set Amb) := by
  have : (greenTriples : Set Amb) = ⋂ Ψ : C1Field, (greenFun Ψ) ⁻¹' {0} := by
    ext z; simp [greenTriples]
  rw [this]
  exact isClosed_iInter fun Ψ => isClosed_singleton.preimage (greenFun Ψ).continuous

/-- The triple `(Ψ, curl Ψ, tanTrace Ψ)` of a `C¹` field. -/
def C1Field.triple (Φ : C1Field) : Amb := WithLp.toLp 2 (Φ.l2, WithLp.toLp 2 (Φ.curlL2, Φ.tan))

/-- The triple of a `C¹` field is a Green triple (Green's formula). -/
theorem triple_mem_greenTriples (Φ : C1Field) : Φ.triple ∈ greenTriples := by
  rw [mem_greenTriples]
  intro Ψ
  exact inner_curl_sub_inner_curl Φ.2 Ψ.2

/-- **The energy space** (row-wise `H_imp(curl)`): the closure of the triples of `C¹` fields,
`(E, curl E, E_τ)`, in `L²(Q) ⊕ L²(Q) ⊕ L²(∂Q; τ)`. Smooth fields are dense in it by definition;
its elements are Green triples (`energySpace_le_greenTriples`). -/
def energySpace : Submodule ℝ Amb :=
  (Submodule.span ℝ (Set.range C1Field.triple)).topologicalClosure

theorem energySpace_le_greenTriples : energySpace ≤ greenTriples :=
  Submodule.topologicalClosure_minimal _
    (Submodule.span_le.2 (Set.range_subset_iff.2 triple_mem_greenTriples)) isClosed_greenTriples

theorem isClosed_energySpace : IsClosed (energySpace : Set Amb) :=
  Submodule.isClosed_topologicalClosure _

instance : CompleteSpace energySpace := isClosed_energySpace.completeSpace_coe

/-- The triple of a `C¹` field lies in the energy space. -/
theorem triple_mem_energySpace (Φ : C1Field) :
    (WithLp.toLp 2 (Φ.l2, WithLp.toLp 2 (Φ.curlL2, Φ.tan)) : Amb) ∈ energySpace :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨Φ, rfl⟩)

/-! ### The impedance triple -/

/-- The energy space as a type. -/
abbrev EnergySpace := ↥energySpace

/-- The field map `(E, C, β) ↦ E`. -/
def fieldMap : EnergySpace →L[ℝ] MQ := (WithLp.fstL 2 ℝ MQ _).comp energySpace.subtypeL

/-- The curl map `(E, C, β) ↦ C`. -/
def curlMap : EnergySpace →L[ℝ] MQ :=
  ((WithLp.fstL 2 ℝ MQ Bdry).comp (WithLp.sndL 2 ℝ MQ _)).comp energySpace.subtypeL

/-- The trace map `(E, C, β) ↦ β`. -/
def traceMap : EnergySpace →L[ℝ] Bdry :=
  ((WithLp.sndL 2 ℝ MQ Bdry).comp (WithLp.sndL 2 ℝ MQ _)).comp energySpace.subtypeL

@[simp] theorem fieldMap_apply (v : EnergySpace) : fieldMap v = (v : Amb).fst := rfl
@[simp] theorem curlMap_apply (v : EnergySpace) : curlMap v = (v : Amb).snd.fst := rfl
@[simp] theorem traceMap_apply (v : EnergySpace) : traceMap v = (v : Amb).snd.snd := rfl

/-- **Green's formula on the energy space**: `⟪curl v, Ψ⟫ - ⟪v, curl Ψ⟫ = ⟪γ v, fluxTrace Ψ⟫`. -/
theorem green_energySpace (v : EnergySpace) (Ψ : C1Field) :
    ⟪curlMap v, Ψ.l2⟫_ℝ - ⟪fieldMap v, Ψ.curlL2⟫_ℝ = ⟪traceMap v, Ψ.flux⟫_ℝ :=
  mem_greenTriples.1 (energySpace_le_greenTriples v.2) Ψ

/-- A test field on `Q` as a `C¹` field. -/
def C1Field.ofTest {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (Q (Fin 3)) Φ) : C1Field :=
  ⟨Φ, fun ij => (hΦ ij).contDiff.of_le (by simp)⟩

theorem C1Field.ofTest_l2 {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (Q (Fin 3)) Φ) :
    (C1Field.ofTest hΦ).l2 = testField hΦ := rfl

theorem C1Field.ofTest_flux {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (Q (Fin 3)) Φ) :
    (C1Field.ofTest hΦ).flux = 0 :=
  fluxTrace_eq_zero _ fun ij _ hx => (hΦ ij).eq_zero_of_notMem hx

theorem C1Field.ofTest_tan {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (Q (Fin 3)) Φ) :
    (C1Field.ofTest hΦ).tan = 0 :=
  tanTrace_eq_zero _ fun ij _ hx => (hΦ ij).eq_zero_of_notMem hx

/-- The curl component is the weak curl: `⟪curl v, Φ⟫ = ⟪v, curl Φ⟫` for test fields `Φ`. -/
theorem inner_curlMap_testField (v : EnergySpace) {Φ : Ix → R3 → ℝ}
    (hΦ : IsTestField (Q (Fin 3)) Φ) :
    ⟪curlMap v, testField hΦ⟫_ℝ = ⟪fieldMap v, (C1Field.ofTest hΦ).curlL2⟫_ℝ := by
  have h := green_energySpace v (C1Field.ofTest hΦ)
  rw [C1Field.ofTest_flux, inner_zero_right, sub_eq_zero] at h
  exact h

theorem fieldMap_injective : Function.Injective fieldMap := by
  intro v w hvw
  set z := v - w
  have hz : fieldMap z = 0 := by rw [map_sub, hvw, sub_self]
  have hc : curlMap z = 0 := by
    refine L2F.eq_zero_of_forall_inner_testField isOpen_Q _ fun Φ hΦ => ?_
    rw [inner_curlMap_testField z hΦ, hz, inner_zero_left]
  have hβ : traceMap z = 0 := eq_zero_of_forall_inner_fluxTrace fun Ψ hΨ => by
    have h := green_energySpace z ⟨Ψ, hΨ⟩
    rw [hz, hc, inner_zero_left, inner_zero_left, sub_zero] at h
    exact h.symm
  have h0 : (z : Amb) = 0 := by
    have e1 : (z : Amb).fst = 0 := hz
    have e2 : (z : Amb).snd.fst = 0 := hc
    have e3 : (z : Amb).snd.snd = 0 := hβ
    exact withLp_prod_ext e1 (withLp_prod_ext e2 e3)
  exact sub_eq_zero.1 (Subtype.ext h0)

theorem denseRange_fieldMap : DenseRange fieldMap := by
  refine (dense_testFieldSub isOpen_Q Ix).mono ?_
  rintro _ ⟨Φ, hΦ, rfl⟩
  exact ⟨⟨_, triple_mem_energySpace (C1Field.ofTest hΦ)⟩, rfl⟩

/-- **The impedance triple of the row-wise curl on the cube**: field, curl and tangential trace
on the energy space. -/
def impedanceTriple : ImpedanceTriple ℝ EnergySpace MQ MQ Bdry where
  ι := fieldMap
  c := curlMap
  γ := traceMap
  inner_eq v w := by
    rw [Submodule.coe_inner, WithLp.prod_inner_apply, WithLp.prod_inner_apply, add_assoc]
    rfl
  injective := fieldMap_injective
  denseRange := denseRange_fieldMap

/-! ### The absorbing generator and its semigroup -/

/-- **The row-wise Einstein–Bianchi generator with absorbing boundary conditions**:
`A (E, B) = (-curl B, curl E)` with `n × E + B_τ = 0` on `∂Q`, realized as the impedance operator
of `impedanceTriple`. -/
def absorbing : State →ₗ.[ℝ] State := impedanceTriple.op

/-- **The absorbing generator is m-dissipative.** -/
theorem isMDissipative_absorbing : absorbing.IsMDissipative := impedanceTriple.isMDissipative_op

/-- The contraction semigroup of the absorbing problem. -/
def absorbingSemigroup : C0Semigroup ℝ State := isMDissipative_absorbing.semigroup

/-- **The boundary flux**: `⟪A u, u⟫ = -‖E_τ‖²_{L²(∂Q)}`. -/
theorem inner_absorbing (u : absorbing.domain) :
    ⟪absorbing u, (u : State)⟫_ℝ = -‖impedanceTriple.trace u‖ ^ 2 :=
  impedanceTriple.re_inner_op u

/-- **The absorbing semigroup radiates**: for `u₀ ∈ D(A)`, the energy at time `t` is the initial
energy minus twice the outgoing flux `∫₀ᵗ ‖E(s)_τ‖²_{L²(∂Q)} ds`. -/
theorem norm_sq_absorbingSemigroup (u₀ : absorbing.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖absorbingSemigroup.S t u₀‖ ^ 2 = ‖(u₀ : State)‖ ^ 2 -
      2 * ∫ s in (0 : ℝ)..t, ‖impedanceTriple.traceExt (absorbingSemigroup.S s u₀)‖ ^ 2 :=
  impedanceTriple.norm_sq_semigroup u₀ ht

/-- **Smooth states with the absorbing condition are in the domain**: for `C¹` fields `E`, `B`
with `tanTrace E + fluxTrace B = 0` (i.e. `n × E + B_τ = 0` on `∂Q`), `(E, B) ∈ D(A)`,
`A (E, B) = (-curl B, curl E)` and the boundary trace is `E_τ`. -/
theorem mem_domain_of_smooth (E B : C1Field) (hbc : E.tan + B.flux = 0) :
    ∃ h : (WithLp.toLp 2 (E.l2, B.l2) : State) ∈ absorbing.domain,
      absorbing ⟨_, h⟩ = WithLp.toLp 2 (-B.curlL2, E.curlL2) ∧
        impedanceTriple.trace ⟨_, h⟩ = E.tan := by
  set v : EnergySpace := ⟨_, triple_mem_energySpace E⟩
  have hmem : ((WithLp.toLp 2 (E.l2, B.l2) : State), (WithLp.toLp 2 (-B.curlL2, E.curlL2) : State))
      ∈ absorbing.graph := by
    rw [absorbing, ImpedanceTriple.mem_graph_op_iff]
    refine ⟨v, rfl, rfl, fun v' => ?_⟩
    have hg := green_energySpace v' B
    have hb : E.tan = -B.flux := eq_neg_of_add_eq_zero_left hbc
    change ⟪-B.curlL2, fieldMap v'⟫_ℝ = -⟪B.l2, curlMap v'⟫_ℝ - ⟪E.tan, traceMap v'⟫_ℝ
    rw [hb, inner_neg_left, inner_neg_left]
    rw [real_inner_comm B.l2, real_inner_comm B.curlL2, real_inner_comm B.flux] at hg
    linarith
  obtain ⟨hdom, hval⟩ := LinearPMap.mem_graph_iff_exists.1 hmem
  refine ⟨hdom, hval, ?_⟩
  have hw : impedanceTriple.witness ⟨_, hdom⟩ = v := impedanceTriple.injective (by
    rw [impedanceTriple.ι_witness]; rfl)
  simp only [ImpedanceTriple.trace, hw]
  rfl

end Feec.Models.Cube.Absorbing
