module

public import Feec.Ch4.BoundedSalvageDim

/-!
# Thesis Prop 4.19 on bounded domains: the strong-symmetry complex (4.16)

Prop 4.19 ([QuennevilleBelair2015, §4.11]) propagates the TSD constraint (symmetric, trace-free,
divergence-free) for the Hodge wave equation (4.18) of the complex (4.16)
`H̊²(R) --grad grad--> H̊(curl, S) --curl--> L²(T)`, with adjoints (4.17)
`L²(R) <--div div-- H(div div, S) <--sym curl-- H(sym curl, T)`, on a bounded domain, under the
"conjectures" `P_{L²(TSD)} (H̊(curl, S) ∩ H(div div, S)) ⊂ H̊(curl, S) ∩ H(div div, S)`,
`P_{L²(TSD)} H(sym curl, T) ⊂ H(sym curl, T)` and two density hypotheses. `Feec.Ch4.TorusSym`
proves the periodic analogue; `Feec.Ch4.BoundedDomain` settles Prop 4.17 on bounded domains. This
file builds the complex (4.16) on every bounded open `Ω ⊆ ℝ³` and settles Prop 4.19 there, in the
style and with the machinery of `Feec.Ch4.BoundedDomain` (test fields, graph closures, weak
derivatives). The obstruction is the same: `H̊(curl, S) ⊆ H̊(curl, M)`, so TSD fields in
`H̊(curl, S)` have zero mean, while `L²(TSD)` contains the constants.

## Model

As in `Feec.Ch4.BoundedDomain`: `L²(Ω; ℝ³ˣ³) = L2M Ω` (nine copies of `L²(Ω)`). `L²(S)` and
`L²(T)` are the closed subspaces `symL2`, `trL2` (`L2S Ω`, `L2T Ω`); `L²(TSD)` inside them is
`TSDS`, `TSDT` (the `TSD` fields of `Feec.BoundedDomain`, no boundary condition).
* `curl : H̊(curl, S) → L²(T)` (`curlS`): the closure of the row-wise curl on symmetric test
  fields `C_c^∞(Ω; S)` (closed, densely defined; `curl S ⊆ T` by `sum_curlM_diag_of_symm`).
* `grad grad : H̊²(Ω) → L²(S)` (`hessS`): the closure of the Hessian on `C_c^∞(Ω)`
  (`closure_hessGraph_identity`: two integrations by parts against `C²` fields).
* `symComplexB : HilbertComplex2 (L2 Ω) (L2S Ω) (L2T Ω)`, the complex (4.16):
  `curl grad grad = 0` (`hessS_mem_curlSGraph`).
* Adjoints: `(grad grad)* ⊇ div div` weakly (`adjoint_hessS_of_weak`), with
  `ker (grad grad)* = H(div div, S, 0)` (`mem_ker_adjoint_hessS_iff`) and
  `C_c^∞(Ω; S) ⊆ H(div div, S)` (`testFieldS_mem_adjoint_hessS`); `curl* ⊇ sym curl` on `C¹`
  trace-free fields with no boundary condition (`smoothField_mem_adjoint_curlS`).

## Main results

* **Projection hypotheses false.** `symComplexB_not_projection_hyp`: for `E = g · diag(1, -1, 0)`
  (`g` a bump), `P_{L²(TSD)} E ∉ H̊(curl, S)`, so `P_K D(L) ⊄ D(L)` for `K = {0} × L²(TSD) × S2`,
  any `S2`. `not_projection_hyp_adjoint_curlS`, `symComplexB_not_projection_hyp2`: the second
  conjecture `P_{L²(TSD)} D(curl*) ⊆ D(curl*)` is false too (closed graph theorem, with the fields
  `E_t`, `B_t` of `Feec.Ch4.BoundedDomainExt`), so `hPD` fails also through the `B`-component.
* **Density hypothesis false**: `not_dense_TSDS_inter_domain` (`H̊(curl, S) ∩ L²(TSD)` misses the
  constant `diag(1, -1, 0)`), from the zero-mean theorem `integral_eq_zero_of_mem_TSDS`.
* **Conclusion false**: `symComplexB_betaT_not_propagate` (from `(0, E₀, β)`,
  `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`, for every `E₀`, every strong solution leaves
  `{0} × L²(TSD) × S2`), `symComplexB_not_propagate` (the TSD datum `(0, 0, β) ∈ D(L) ∩ K`), and
  `symComplexB_not_propagate_unconditional` (a strong solution exists, by Stone's theorem). The
  mechanism is `Feec.BoundedDomain.not_propagate_of_adjoint` applied through the inclusion
  `ι : L²(S) → L²(M)`, which maps `H̊(curl, S)` into `H̊(curl, M)`
  (`symL2_subtypeL_mem_HcurlZero`).
* **Diagnosis**: `symComplexB_diagnosis`. The remaining hypotheses of
  `Feec.Constraints.prop_4_17` hold on `Ω` (the thesis' third itemized check, Lemma 3.5):
  `TSDS_le_ker` (`L²(TSD) ⊆ ker div div`), `curlS_mem_TSDT`, `adjoint_curlS_mem_TSDS`.
* **What survives** (salvage, reusing `TSD₀` and the obstruction space of
  `Feec.Ch4.BoundedSalvage`):
  * `symComplexB_prop_4_16`: `σ ≡ 0` and `div div E ≡ 0` propagate unconditionally, with
    existence and uniqueness; `symComplexB_prop_4_18`: the reduction (4.18) ⇔ reduced system.
  * `mem_TSD0_of_mem_domain`: `H̊(curl, S) ∩ L²(TSD) ⊆ TSD₀` (orthogonal to `∇φ` for every `C¹`
    field `φ`; weakly `E n = 0`). `not_finiteDimensional_obstrS`: the part of `L²(TSD) ∩ L²(S)`
    orthogonal to `TSD₀`, hence to the closure of `H̊(curl, S) ∩ L²(TSD)`, is
    infinite-dimensional (harmonic Hessians), so no finite-dimensional correction rescues the
    density conjecture.
  * `symComplexB_mem_TSD0_of_propagate`: **necessary condition** for propagation: if a strong
    solution from `(0, E₀, B₀)` stays in `K` on some `[0, T]`, `T > 0`, then `E₀ ∈ TSD₀` and
    `sym curl B₀ ∈ TSD₀`.
  * `symComplexB_prop_4_19_max`: **corrected Prop 4.19**, unconditional, in maximal form. For the
    Hodge wave group, `K* = {x | ∀ t, e^{-tL} x ∈ K} = {0} × S1* × S2*` (from
    `Feec.Ch4.BoundedSalvageMax`) satisfies every hypothesis of `prop_4_17`, is the largest such
    constraint space, and its data propagate; `S1* ⊆ TSD₀`; `diag(1, -1, 0) ∉ S1*`, `β ∉ S2*`;
    the stationary data (`sym curl B = 0`: harmonic Hessians `symComplexB_hessT_mem_S2max`,
    `diag(1, -1, 0)`) lie in `S2*`, which is infinite-dimensional.

## Correction

[QuennevilleBelair2015, §4.11, Prop 4.19], on every nonempty bounded open `Ω ⊆ ℝ³` (ball, cube,
contractible or not):
* both projection conjectures are false, so Prop 4.19 as stated is vacuously true;
* the conjectured density of `H̊(curl, S) ∩ L²(TSD)` in `L²(TSD)` is false, by an
  infinite-dimensional margin;
* its conclusion is false: TSD data in `D(L)` whose (existing, unique) solution leaves `K`;
* the third itemized check of the proof (`div div`, `sym curl`, `curl` preserve TSD) is correct.
The data space `H² × H(curl, S) ∩ H̊(div div, S) × H̊(sym curl, T)` in the statement misplaces the
boundary conditions (as noted in `Feec.Ch4.TorusSym`); this file uses the space of the proof,
`D(L) = H̊²(R) × (H̊(curl, S) ∩ H(div div, S)) × H(sym curl, T)`.

Thesis gap: the zero-mean obstruction (and its generalization `TSD₀`) is a boundary effect,
absent on `𝕋³`, where Prop 4.19 holds (`Feec.TorusSym.prop_4_19_torus_exists`).

Proved in `Feec.Ch4.BoundedSymExt`: `D(curl*) = H(sym curl, T)` and
`D((grad grad)*) = H(div div, S)` exactly (`Feec.BoundedSym.mem_adjoint_curlS_iff`,
`Feec.BoundedSym.mem_adjoint_hessS_iff`); for the dual-boundary-condition placement printed in
Prop 4.19 (`symComplexD`, with `D(L)` the printed data space), the projection hypothesis and the
density fail (`symComplexD_not_projection_hyp`, `symComplexD_not_dense`), while whether the
conclusion of Prop 4.19 holds there is not decided. Under tensorial mirror conditions on a box,
in a parity model, Prop 4.19 holds for the operators of (4.16) with mirror conditions
(`Feec.Box.mirror_prop_4_19_exists` in `Feec.Ch4.BoxMirror`).

Not formalized: the density of `H(sym curl, T) ∩ L²(TSD)` in `L²(TSD)`; the closed-range
property of (4.16) on `Ω`; a non-stationary element of `K*` or a nonzero element of `S1*` (open;
the box results of `Feec.Ch4.BoxThesis` cover the boundary conditions of Prop 4.17 only).

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.10 (Props 4.16–4.18), §4.11 ((4.16)–(4.18),
  Prop 4.19)
* [ArnoldHu2021], [Eastwood2000] (the `grad grad`–`curl`–`div` complex of symmetric and
  trace-free matrix fields)
* [ACBY1997] (the Einstein–Bianchi system)
* [Brezis2011] (Sobolev spaces, the fundamental lemma, the closed graph theorem)
* [AFW2010], [BruningLesch1992] (Hilbert complexes)
* [Pazy1983], §1.10 (Stone's theorem, behind `Feec.HilbertComplex2.waveGroup`)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal ContDiff Matrix LinearPMap
open MeasureTheory Set Filter Topology

namespace Feec.BoundedSym

open Feec.BoundedDomain Feec.HilbertComplex2 Feec.Constraints

variable {Ω : Set R3}

/-! ## The spaces `L²(S)` and `L²(T)` -/

variable (Ω) in
/-- `L²(Ω; S)`: symmetric matrix fields, a closed subspace of `L²(Ω; ℝ³ˣ³)`. -/
def symL2 : Submodule ℝ (L2M Ω) where
  carrier := {B | ∀ i j, B (i, j) = B (j, i)}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb i j => by
    simp only [mem_ofPred_eq, PiLp.add_apply] at ha hb ⊢
    rw [ha i j, hb i j]
  smul_mem' := fun r B hB i j => by
    simp only [mem_ofPred_eq, PiLp.smul_apply] at hB ⊢
    rw [hB i j]

variable (Ω) in
/-- `L²(Ω; T)`: trace-free matrix fields, a closed subspace of `L²(Ω; ℝ³ˣ³)`. -/
def trL2 : Submodule ℝ (L2M Ω) where
  carrier := {B | ∑ i, B (i, i) = 0}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [mem_ofPred_eq, PiLp.add_apply, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha, hb, add_zero]
  smul_mem' := fun r B hB => by
    simp only [mem_ofPred_eq, PiLp.smul_apply, ← Finset.smul_sum] at hB ⊢
    rw [hB, smul_zero]

theorem mem_symL2 {B : L2M Ω} : B ∈ symL2 Ω ↔ ∀ i j, B (i, j) = B (j, i) := Iff.rfl

theorem mem_trL2 {B : L2M Ω} : B ∈ trL2 Ω ↔ ∑ i, B (i, i) = 0 := Iff.rfl

/-- `L²(S)` is closed. -/
theorem isClosed_symL2 : IsClosed (symL2 Ω : Set (L2M Ω)) := by
  have e : (symL2 Ω : Set (L2M Ω)) =
      ⋂ i : Fin 3, ⋂ j : Fin 3, {B : L2M Ω | B (i, j) = B (j, i)} := by
    ext B
    simp [mem_symL2]
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (continuous_component (i, j)) (continuous_component (j, i))

/-- `L²(T)` is closed. -/
theorem isClosed_trL2 : IsClosed (trL2 Ω : Set (L2M Ω)) :=
  isClosed_eq (continuous_finsetSum Finset.univ fun i _ => continuous_component (i, i))
    continuous_const

instance : CompleteSpace (symL2 Ω) := isClosed_symL2.completeSpace_coe

instance : CompleteSpace (trL2 Ω) := isClosed_trL2.completeSpace_coe

variable (Ω) in
/-- `W1 = L²(Ω; S)`. -/
abbrev L2S := ↥(symL2 Ω)

variable (Ω) in
/-- `W2 = L²(Ω; T)`. -/
abbrev L2T := ↥(trL2 Ω)

variable (Ω) in
/-- `L²(TSD)` inside `L²(S)`. -/
def TSDS : Submodule ℝ (L2S Ω) := (TSD Ω).comap (symL2 Ω).subtype

variable (Ω) in
/-- `L²(TSD)` inside `L²(T)`. -/
def TSDT : Submodule ℝ (L2T Ω) := (TSD Ω).comap (trL2 Ω).subtype

theorem mem_TSDS {B : L2S Ω} : B ∈ TSDS Ω ↔ (B : L2M Ω) ∈ TSD Ω := Iff.rfl

theorem mem_TSDT {B : L2T Ω} : B ∈ TSDT Ω ↔ (B : L2M Ω) ∈ TSD Ω := Iff.rfl

theorem isClosed_TSDS : IsClosed (TSDS Ω : Set (L2S Ω)) :=
  isClosed_TSD.preimage continuous_subtype_val

theorem isClosed_TSDT : IsClosed (TSDT Ω : Set (L2T Ω)) :=
  isClosed_TSD.preimage continuous_subtype_val

instance : (TSDS Ω).HasOrthogonalProjection := by
  have : CompleteSpace (TSDS Ω) := isClosed_TSDS.completeSpace_coe
  infer_instance

instance : (TSDT Ω).HasOrthogonalProjection := by
  have : CompleteSpace (TSDT Ω) := isClosed_TSDT.completeSpace_coe
  infer_instance

/-- Symmetric continuous fields give elements of `L²(S)`. -/
theorem smoothField_mem_symL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, Continuous (Ψ ij)) (hs : ∀ i j, Ψ (i, j) = Ψ (j, i)) :
    smoothField hΩ hb Ψ hΨ ∈ symL2 Ω := fun i j => by
  refine Lp.ext ?_
  filter_upwards [coeFn_smoothField hΩ hb Ψ hΨ (i, j), coeFn_smoothField hΩ hb Ψ hΨ (j, i)]
    with x h1 h2
  rw [h1, h2, hs]

/-- Pointwise trace-free continuous fields give elements of `L²(T)`. -/
theorem smoothField_mem_trL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, Continuous (Ψ ij)) (htr : ∀ x, ∑ i, Ψ (i, i) x = 0) :
    smoothField hΩ hb Ψ hΨ ∈ trL2 Ω := by
  rw [mem_trL2]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => (smoothField hΩ hb Ψ hΨ).ofLp (i, i)),
    coeFn_smoothField hΩ hb Ψ hΨ (0, 0), coeFn_smoothField hΩ hb Ψ hΨ (1, 1),
    coeFn_smoothField hΩ hb Ψ hΨ (2, 2), Lp.coeFn_zero ℝ 2 (volume.restrict Ω)]
    with x h0 h1 h2 h3 h4
  rw [h0, h4, Fin.sum_univ_three, h1, h2, h3]
  simpa [Fin.sum_univ_three] using htr x

/-- Symmetric fields pair with `Ψ` as with `Ψᵀ`. -/
theorem sum_integral_mul_transpose {v : L2M Ω} (hv : v ∈ symL2 Ω) (Ψ : Ix → R3 → ℝ) :
    ∑ ij : Ix, ∫ x, v ij x * Ψ (ij.2, ij.1) x ∂volume.restrict Ω =
      ∑ ij : Ix, ∫ x, v ij x * Ψ ij x ∂volume.restrict Ω := by
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun jk => ?_
  obtain ⟨j, k⟩ := jk
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [hv j k]

/-- The symmetric part `(Ψ + Ψᵀ) / 2` of a matrix field. -/
def symF (Ψ : Ix → R3 → ℝ) : Ix → R3 → ℝ := fun ij x => (Ψ ij x + Ψ (ij.2, ij.1) x) / 2

theorem symF_swap (Ψ : Ix → R3 → ℝ) (i j : Fin 3) : symF Ψ (i, j) = symF Ψ (j, i) := by
  funext x
  simp only [symF]
  ring

theorem continuous_symF {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Continuous (Ψ ij)) (ij : Ix) :
    Continuous (symF Ψ ij) :=
  ((hΨ ij).add (hΨ _)).div_const 2

/-- Symmetric fields pair with `Ψ` as with its symmetric part. -/
theorem sum_integral_mul_symF (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {v : L2M Ω}
    (hv : v ∈ symL2 Ω) {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Continuous (Ψ ij)) :
    ∑ ij : Ix, ∫ x, v ij x * symF Ψ ij x ∂volume.restrict Ω =
      ∑ ij : Ix, ∫ x, v ij x * Ψ ij x ∂volume.restrict Ω := by
  have hm : ∀ ij, MemLp (Ψ ij) 2 (volume.restrict Ω) := fun ij => memLp_of_continuous hΩ hb (hΨ ij)
  have e : ∀ ij : Ix, ∫ x, v ij x * symF Ψ ij x ∂volume.restrict Ω =
      (∫ x, v ij x * Ψ ij x ∂volume.restrict Ω +
        ∫ x, v ij x * Ψ (ij.2, ij.1) x ∂volume.restrict Ω) / 2 := by
    intro ij
    rw [← integral_add (integrable_mul _ (hm _)) (integrable_mul _ (hm _)), ← integral_div]
    congr 1
    ext x
    simp only [symF]
    ring
  simp only [e, ← Finset.sum_div, Finset.sum_add_distrib, sum_integral_mul_transpose hv]
  ring

/-! ## `curl : H̊(curl, S) → L²(T)` -/

variable (Ω) in
/-- The graph of curl on symmetric test fields `C_c^∞(Ω; S)`. -/
def curlGraphS : Set (L2M Ω × L2M Ω) :=
  {p | ∃ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) ∧ (∀ i j, Φ (i, j) = Φ (j, i)) ∧
    ∀ ij, (p.1 ij : R3 → ℝ) =ᵐ[volume.restrict Ω] Φ ij ∧
      (p.2 ij : R3 → ℝ) =ᵐ[volume.restrict Ω] curlM Φ ij}

theorem curlGraphS_subset : curlGraphS Ω ⊆ curlGraph Ω := fun _ ⟨Φ, hΦ, _, h⟩ => ⟨Φ, hΦ, h⟩

/-- The curl of a symmetric field is trace-free (part of Lemma 3.5). -/
theorem sum_curlM_diag_of_symm {Φ : Ix → R3 → ℝ} (hs : ∀ i j, Φ (i, j) = Φ (j, i)) (x : R3) :
    ∑ i, curlM Φ (i, i) x = 0 := by
  simp only [Fin.sum_univ_three, curlM]
  simp only [Fin.isValue, Fin.reduceAdd]
  rw [hs 0 2, hs 0 1, hs 1 2]
  ring

variable (Ω) in
/-- The span of `curlGraphS`. -/
def curlGraphSSub : Submodule ℝ (L2M Ω × L2M Ω) := Submodule.span ℝ (curlGraphS Ω)

/-- The closure of the symmetric curl graph lies in the closure of the full curl graph. -/
theorem closure_curlGraphSSub_subset :
    ((curlGraphSSub Ω).topologicalClosure : Set (L2M Ω × L2M Ω)) ⊆ closure (curlGraph Ω) := by
  rw [Submodule.topologicalClosure_coe]
  exact closure_mono (Submodule.span_le (p := curlGraphSub Ω).2 curlGraphS_subset)

theorem curlGraphS_subset_prod (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    curlGraphS Ω ⊆ ((symL2 Ω).prod (trL2 Ω) : Set (L2M Ω × L2M Ω)) := by
  rintro ⟨u, c⟩ ⟨Φ, hΦ, hs, hp⟩
  refine ⟨fun i j => Lp.ext ?_, ?_⟩
  · filter_upwards [(hp (i, j)).1, (hp (j, i)).1] with x h1 h2
    rw [h1, h2, hs]
  · have hc : ∀ ij, Continuous (curlM Φ ij) := continuous_curlM fun ij => (hΦ ij).contDiff_one
    have e : c = smoothField hΩ hb (curlM Φ) hc := (WithLp.ext_iff 2).2 (funext fun ij =>
      Lp.ext ((hp ij).2.trans (coeFn_smoothField hΩ hb _ hc ij).symm))
    simp only [SetLike.mem_coe]
    rw [e]
    exact smoothField_mem_trL2 hΩ hb hc (sum_curlM_diag_of_symm hs)

theorem closure_curlGraphSSub_le_prod (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (curlGraphSSub Ω).topologicalClosure ≤ (symL2 Ω).prod (trL2 Ω) :=
  Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 (curlGraphS_subset_prod hΩ hb))
    (isClosed_symL2.prod isClosed_trL2)

/-- The embedding `L²(S) × L²(T) → L²(M) × L²(M)`. -/
def embST : L2S Ω × L2T Ω →L[ℝ] L2M Ω × L2M Ω := (symL2 Ω).subtypeL.prodMap (trL2 Ω).subtypeL

@[simp] theorem embST_apply (p : L2S Ω × L2T Ω) : embST p = ((p.1 : L2M Ω), (p.2 : L2M Ω)) :=
  rfl

variable (Ω) in
/-- The graph of `curl` on `H̊(curl, S)`: the closure of `{(Φ, curl Φ) : Φ ∈ C_c^∞(Ω; S)}`. -/
def curlSGraph : Submodule ℝ (L2S Ω × L2T Ω) :=
  (curlGraphSSub Ω).topologicalClosure.comap (embST (Ω := Ω)).toLinearMap

theorem mem_curlSGraph {p : L2S Ω × L2T Ω} :
    p ∈ curlSGraph Ω ↔ ((p.1 : L2M Ω), (p.2 : L2M Ω)) ∈ (curlGraphSSub Ω).topologicalClosure :=
  Iff.rfl

theorem curlSGraph_closable (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∀ x ∈ curlSGraph Ω, x.1 = 0 → x.2 = 0 := by
  rintro ⟨u, w⟩ hx (h0 : u = 0)
  subst h0
  have h := curlGraph_closable hΩ hb (((0 : L2S Ω) : L2M Ω), (w : L2M Ω))
    (closure_curlGraphSSub_subset hx) rfl
  exact Subtype.ext h

/-- `curl : H̊(curl, Ω; S) → L²(Ω; T)`. -/
def curlS : L2S Ω →ₗ.[ℝ] L2T Ω := (curlSGraph Ω).toLinearPMap

theorem curlS_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (curlS (Ω := Ω)).graph = curlSGraph Ω :=
  Submodule.toLinearPMap_graph_eq _ (curlSGraph_closable hΩ hb)

theorem isClosed_curlS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (curlS (Ω := Ω)).IsClosed := by
  rw [LinearPMap.IsClosed, curlS_graph hΩ hb]
  exact (Submodule.isClosed_topologicalClosure _).preimage embST.continuous

/-- `(u, curl u)` lies in the closure of the symmetric curl graph. -/
theorem mem_closure_curlS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (curlS (Ω := Ω)).domain) :
    ((u : L2M Ω), (curlS u : L2M Ω)) ∈ (curlGraphSSub Ω).topologicalClosure :=
  Submodule.mem_graph_toLinearPMap (curlSGraph_closable hΩ hb) u

/-- `H̊(curl, S) ⊆ H̊(curl, M)`, with the same curl. -/
theorem mem_closure_curlGraph_curlS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (curlS (Ω := Ω)).domain) :
    ((u : L2M Ω), (curlS u : L2M Ω)) ∈ closure (curlGraph Ω) :=
  closure_curlGraphSSub_subset (mem_closure_curlS hΩ hb u)

theorem mem_HcurlZero_of_mem_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (curlS (Ω := Ω)).domain) : ((u : L2S Ω) : L2M Ω) ∈ HcurlZero Ω :=
  ⟨_, mem_closure_curlGraph_curlS hΩ hb u⟩

/-- A symmetric test field, as an element of `L²(S)`. -/
def testFieldS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Φ : Ix → R3 → ℝ}
    (hΦ : ∀ ij, IsTest Ω (Φ ij)) (hs : ∀ i j, Φ (i, j) = Φ (j, i)) : L2S Ω :=
  ⟨smoothField hΩ hb Φ (fun ij => (hΦ ij).continuous),
    smoothField_mem_symL2 hΩ hb _ hs⟩

/-- Its curl, as an element of `L²(T)`. -/
def curlTestFieldS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Φ : Ix → R3 → ℝ}
    (hΦ : ∀ ij, IsTest Ω (Φ ij)) (hs : ∀ i j, Φ (i, j) = Φ (j, i)) : L2T Ω :=
  ⟨smoothField hΩ hb (curlM Φ) (continuous_curlM fun ij => (hΦ ij).contDiff_one),
    smoothField_mem_trL2 hΩ hb _ (sum_curlM_diag_of_symm hs)⟩

theorem testFieldS_mem_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Φ : Ix → R3 → ℝ}
    (hΦ : ∀ ij, IsTest Ω (Φ ij)) (hs : ∀ i j, Φ (i, j) = Φ (j, i)) :
    (testFieldS hΩ hb hΦ hs, curlTestFieldS hΩ hb hΦ hs) ∈ (curlS (Ω := Ω)).graph := by
  rw [curlS_graph hΩ hb, mem_curlSGraph]
  refine subset_closure (Submodule.subset_span ⟨Φ, hΦ, hs, fun ij => ⟨?_, ?_⟩⟩)
  · exact coeFn_smoothField hΩ hb Φ (fun ij => (hΦ ij).continuous) ij
  · exact coeFn_smoothField hΩ hb (curlM Φ)
      (continuous_curlM fun ij => (hΦ ij).contDiff_one) ij

/-- `C_c^∞(Ω; S) ⊆ H̊(curl, S)`. -/
theorem testFieldS_mem_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Φ : Ix → R3 → ℝ}
    (hΦ : ∀ ij, IsTest Ω (Φ ij)) (hs : ∀ i j, Φ (i, j) = Φ (j, i)) :
    testFieldS hΩ hb hΦ hs ∈ (curlS (Ω := Ω)).domain := by
  obtain ⟨y, hy, -⟩ := (LinearPMap.mem_graph_iff _).1 (testFieldS_mem_graph hΩ hb hΦ hs)
  have e : (y : L2S Ω) = testFieldS hΩ hb hΦ hs := hy
  exact e ▸ y.2

/-- The symmetric part of a test field is a test field. -/
theorem isTest_symF {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, IsTest Ω (Ψ ij)) (ij : Ix) :
    IsTest Ω (symF Ψ ij) := by
  have h := ((hΨ ij).add (hΨ (ij.2, ij.1))).const_mul (1 / 2)
  convert h using 1
  funext x
  simp only [symF, Pi.add_apply]
  ring

/-- `H̊(curl, S)` is dense in `L²(S)`. -/
theorem dense_domain_curlS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    Dense ((curlS (Ω := Ω)).domain : Set (L2S Ω)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro v hv
  refine Subtype.ext (eq_zero_of_forall_integral hΩ hb fun Ψ hΨ => ?_)
  have h0 := (Submodule.mem_orthogonal' _ _).1 hv _
    (testFieldS_mem_domain hΩ hb (isTest_symF hΨ) (symF_swap Ψ))
  rw [Submodule.coe_inner, testFieldS, inner_smoothField] at h0
  rw [← sum_integral_mul_symF hΩ hb v.2 fun ij => (hΨ ij).continuous]
  exact h0

/-! ## `grad grad : H̊²(Ω) → H̊(curl, S)` -/

/-- The double divergence `div div Ψ = Σ_{ij} ∂_i ∂_j Ψ_{ij}` of a matrix field. -/
def divdivF (Ψ : Ix → R3 → ℝ) (x : R3) : ℝ :=
  ∑ ij : Ix, BoundedDomain.pd ij.1 (BoundedDomain.pd ij.2 (Ψ ij)) x

theorem continuous_divdivF {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 2 (Ψ ij)) :
    Continuous (divdivF Ψ) :=
  continuous_finsetSum _ fun ij _ => continuous_pd (contDiff_pd (hΨ ij) ij.2) ij.1

theorem isTest_hessField {φ : R3 → ℝ} (hφ : IsTest Ω φ) (ij : Ix) : IsTest Ω (hessField φ ij) :=
  (hφ.pdiff _).pdiff _

/-- The Hessian is symmetric (Schwarz). -/
theorem hessField_swap {φ : R3 → ℝ} (hφ : ContDiff ℝ 2 φ) (i j : Fin 3) :
    hessField φ (i, j) = hessField φ (j, i) :=
  funext fun x => pd_pd_comm hφ j i x

/-- `curl grad grad = 0`. -/
theorem curlM_hessField {φ : R3 → ℝ} (hφ : IsTest Ω φ) (ik : Ix) (x : R3) :
    curlM (hessField φ) ik x = 0 :=
  curlM_gradM (φ := fun i => BoundedDomain.pd i φ)
    (fun i => (hφ.pdiff i).contDiff.of_le (by simp)) ik x

/-- Integration by parts twice: `∫ ∂_j ∂_i φ ψ = ∫ φ ∂_i ∂_j ψ` for `φ ∈ C_c^∞(Ω)`, `ψ ∈ C²`. -/
theorem integral_hessField_mul {φ ψ : R3 → ℝ} (hφ : IsTest Ω φ) (hψ : ContDiff ℝ 2 ψ)
    (i j : Fin 3) :
    ∫ x, hessField φ (i, j) x * ψ x ∂volume.restrict Ω =
      ∫ x, φ x * BoundedDomain.pd i (BoundedDomain.pd j ψ) x ∂volume.restrict Ω := by
  simp only [hessField]
  rw [integral_pd_mul (hφ.pdiff i) (hψ.of_le (by norm_num)) j,
    integral_pd_mul hφ (contDiff_pd hψ j) i, neg_neg]

variable (Ω) in
/-- The graph of `grad grad` on `C_c^∞(Ω)`, in `L²(Ω) × L²(Ω; ℝ³ˣ³)`. -/
def hessGraph : Set (L2 Ω × L2M Ω) :=
  {p | ∃ φ : R3 → ℝ, IsTest Ω φ ∧ (p.1 : R3 → ℝ) =ᵐ[volume.restrict Ω] φ ∧
    ∀ ij, (p.2 ij : R3 → ℝ) =ᵐ[volume.restrict Ω] hessField φ ij}

variable (Ω) in
/-- The span of `hessGraph`. -/
def hessGraphSub : Submodule ℝ (L2 Ω × L2M Ω) := Submodule.span ℝ (hessGraph Ω)

/-- The defining identity of the closure of the `grad grad` graph, tested against a `C²` field
`Ψ` with no boundary condition: `∫ H : Ψ = ∫ f div div Ψ`. -/
theorem closure_hessGraph_identity (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {f : L2 Ω}
    {H : L2M Ω} (h : (f, H) ∈ (hessGraphSub Ω).topologicalClosure) {Ψ : Ix → R3 → ℝ}
    (hΨ : ∀ ij, ContDiff ℝ 2 (Ψ ij)) :
    ∑ ij, ∫ x, H ij x * Ψ ij x ∂volume.restrict Ω =
      ∫ x, f x * divdivF Ψ x ∂volume.restrict Ω := by
  have hc : ∀ ij, Continuous (Ψ ij) := fun ij => (hΨ ij).continuous
  have hm := memLp_of_continuous hΩ hb (continuous_divdivF hΨ)
  let F : L2 Ω × L2M Ω →L[ℝ] ℝ :=
    (innerSL ℝ (smoothField hΩ hb Ψ hc)).comp (ContinuousLinearMap.snd ℝ _ _) -
      (innerSL ℝ (hm.toLp _)).comp (ContinuousLinearMap.fst ℝ _ _)
  have hF : ∀ p : L2 Ω × L2M Ω, F p = ∑ ij, ∫ x, p.2 ij x * Ψ ij x ∂volume.restrict Ω -
      ∫ x, p.1 x * divdivF Ψ x ∂volume.restrict Ω := by
    intro p
    change ⟪smoothField hΩ hb Ψ hc, p.2⟫ - ⟪hm.toLp _, p.1⟫ = _
    rw [real_inner_comm, inner_smoothField, real_inner_comm, ← integral_mul_eq_inner]
  have hsub : hessGraphSub Ω ≤ LinearMap.ker (F : L2 Ω × L2M Ω →ₗ[ℝ] ℝ) := by
    refine Submodule.span_le.2 ?_
    rintro ⟨u, c⟩ ⟨φ, hφ, hp1, hp2⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hF, sub_eq_zero]
    have e1 : ∀ ij : Ix, ∫ x, c ij x * Ψ ij x ∂volume.restrict Ω =
        ∫ x, φ x * BoundedDomain.pd ij.1 (BoundedDomain.pd ij.2 (Ψ ij)) x ∂volume.restrict Ω :=
        fun ij => by
      rw [← integral_hessField_mul hφ (hΨ ij)]
      exact integral_congr_ae ((hp2 ij).mono fun x hx => by simp only; rw [hx])
    have e2 : ∫ x, u x * divdivF Ψ x ∂volume.restrict Ω =
        ∫ x, φ x * divdivF Ψ x ∂volume.restrict Ω :=
      integral_congr_ae (hp1.mono fun x hx => by simp only; rw [hx])
    rw [e2, Finset.sum_congr rfl fun ij _ => e1 ij, ← integral_finsetSum _ fun ij _ =>
      integrable_mul_of_compact hφ.continuous hφ.hasCompactSupport
        (continuous_pd (contDiff_pd (hΨ ij) ij.2) ij.1)]
    simp only [divdivF, Finset.mul_sum]
  have := Submodule.topologicalClosure_minimal _ hsub F.isClosed_ker h
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hF, sub_eq_zero] at this
  exact this

/-- The embedding `L²(Ω) × L²(S) → L²(Ω) × L²(M)`. -/
def embRS : L2 Ω × L2S Ω →L[ℝ] L2 Ω × L2M Ω :=
  (ContinuousLinearMap.id ℝ (L2 Ω)).prodMap (symL2 Ω).subtypeL

@[simp] theorem embRS_apply (p : L2 Ω × L2S Ω) : embRS p = (p.1, (p.2 : L2M Ω)) := rfl

variable (Ω) in
/-- The graph of `grad grad` on `H̊²(Ω)`: the closure of `{(φ, grad grad φ) : φ ∈ C_c^∞(Ω)}`. -/
def hessSGraph : Submodule ℝ (L2 Ω × L2S Ω) :=
  (hessGraphSub Ω).topologicalClosure.comap (embRS (Ω := Ω)).toLinearMap

theorem mem_hessSGraph {p : L2 Ω × L2S Ω} :
    p ∈ hessSGraph Ω ↔ (p.1, (p.2 : L2M Ω)) ∈ (hessGraphSub Ω).topologicalClosure := Iff.rfl

theorem hessSGraph_closable (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∀ x ∈ hessSGraph Ω, x.1 = 0 → x.2 = 0 := by
  rintro ⟨u, w⟩ hx (h0 : u = 0)
  subst h0
  have hx' : ((0 : L2 Ω), (w : L2M Ω)) ∈ (hessGraphSub Ω).topologicalClosure := hx
  refine Subtype.ext (eq_zero_of_forall_integral hΩ hb fun Ψ hΨ => ?_)
  show ∑ ij, ∫ x, (w : L2M Ω) ij x * Ψ ij x ∂volume.restrict Ω = 0
  rw [closure_hessGraph_identity hΩ hb hx' fun ij => (hΨ ij).contDiff.of_le (by simp),
    integral_mul_eq_inner _ (memLp_of_continuous hΩ hb (continuous_divdivF fun ij =>
      (hΨ ij).contDiff.of_le (by simp))), inner_zero_left]

/-- `grad grad : H̊²(Ω) → L²(Ω; S)`, the closure of the Hessian on `C_c^∞(Ω)`. -/
def hessS : L2 Ω →ₗ.[ℝ] L2S Ω := (hessSGraph Ω).toLinearPMap

theorem hessS_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (hessS (Ω := Ω)).graph = hessSGraph Ω :=
  Submodule.toLinearPMap_graph_eq _ (hessSGraph_closable hΩ hb)

theorem isClosed_hessS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (hessS (Ω := Ω)).IsClosed := by
  rw [LinearPMap.IsClosed, hessS_graph hΩ hb]
  exact (Submodule.isClosed_topologicalClosure _).preimage embRS.continuous

theorem mem_closure_hessS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (hessS (Ω := Ω)).domain) :
    ((u : L2 Ω), (hessS u : L2M Ω)) ∈ (hessGraphSub Ω).topologicalClosure :=
  Submodule.mem_graph_toLinearPMap (hessSGraph_closable hΩ hb) u

/-- A test function, as an element of `L²(Ω)`. -/
def testFieldR {φ : R3 → ℝ} (hφ : IsTest Ω φ) : L2 Ω := hφ.memLp.toLp φ

/-- Its Hessian, as an element of `L²(S)`. -/
def hessTestField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : R3 → ℝ} (hφ : IsTest Ω φ) :
    L2S Ω :=
  ⟨smoothField hΩ hb (hessField φ) (fun ij => (isTest_hessField hφ ij).continuous),
    smoothField_mem_symL2 hΩ hb _ (hessField_swap (hφ.contDiff.of_le (by simp)))⟩

theorem testFieldR_mem_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : R3 → ℝ}
    (hφ : IsTest Ω φ) : (testFieldR hφ, hessTestField hΩ hb hφ) ∈ (hessS (Ω := Ω)).graph := by
  rw [hessS_graph hΩ hb, mem_hessSGraph]
  exact subset_closure (Submodule.subset_span ⟨φ, hφ, hφ.memLp.coeFn_toLp,
    coeFn_smoothField hΩ hb (hessField φ) (fun ij => (isTest_hessField hφ ij).continuous)⟩)

/-- `C_c^∞(Ω) ⊆ H̊²(Ω)`. -/
theorem testFieldR_mem_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : R3 → ℝ}
    (hφ : IsTest Ω φ) : testFieldR hφ ∈ (hessS (Ω := Ω)).domain := by
  obtain ⟨y, hy, -⟩ := (LinearPMap.mem_graph_iff _).1 (testFieldR_mem_graph hΩ hb hφ)
  have e : (y : L2 Ω) = testFieldR hφ := hy
  exact e ▸ y.2

theorem hessS_testFieldR (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : R3 → ℝ}
    (hφ : IsTest Ω φ) :
    hessS ⟨testFieldR hφ, testFieldR_mem_domain hΩ hb hφ⟩ = hessTestField hΩ hb hφ :=
  apply_eq_of_mem_graph (testFieldR_mem_graph hΩ hb hφ) _

/-- `H̊²(Ω)` is dense in `L²(Ω)`. -/
theorem dense_domain_hessS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    Dense ((hessS (Ω := Ω)).domain : Set (L2 Ω)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro v hv
  refine L2_ext_of_integral hΩ hb fun g hg => ?_
  have h0 := (Submodule.mem_orthogonal' _ _).1 hv _ (testFieldR_mem_domain hΩ hb hg)
  rw [integral_mul_eq_inner _ hg.memLp, integral_mul_eq_inner _ hg.memLp, inner_zero_left]
  exact h0

/-- `grad grad H̊² ⊆ H̊(curl, S)` with `curl grad grad = 0`. -/
theorem hessS_mem_curlSGraph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (hessS (Ω := Ω)).domain) : (hessS u, (0 : L2T Ω)) ∈ curlSGraph Ω := by
  rw [mem_curlSGraph]
  let f : L2 Ω × L2M Ω →L[ℝ] L2M Ω × L2M Ω := (ContinuousLinearMap.snd ℝ (L2 Ω) (L2M Ω)).prod 0
  have hle : hessGraphSub Ω ≤ (curlGraphSSub Ω).comap (f : L2 Ω × L2M Ω →ₗ[ℝ] _) := by
    refine Submodule.span_le.2 ?_
    rintro ⟨v, H⟩ ⟨φ, hφ, -, hp2⟩
    refine Submodule.subset_span ⟨hessField φ, isTest_hessField hφ,
      hessField_swap (hφ.contDiff.of_le (by simp)), fun ij => ⟨hp2 ij, ?_⟩⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx
    simp only [f]
    rw [curlM_hessField hφ]
    simpa using hx
  have h := mem_closure_hessS hΩ hb u
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at h
  have := map_mem_closure f.continuous h (t := (curlGraphSSub Ω : Set (L2M Ω × L2M Ω)))
    fun p hp => hle hp
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  simpa [f] using this

theorem hessS_mem_domain_curlS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (hessS (Ω := Ω)).domain) : hessS u ∈ (curlS (Ω := Ω)).domain := by
  have h : (hessS u, (0 : L2T Ω)) ∈ (curlS (Ω := Ω)).graph := by
    rw [curlS_graph hΩ hb]; exact hessS_mem_curlSGraph hΩ hb u
  obtain ⟨y, hy, -⟩ := (LinearPMap.mem_graph_iff _).1 h
  have e : (y : L2S Ω) = hessS u := hy
  exact e ▸ y.2

/-! ## The complex (4.16) on `Ω` -/

/-- **The thesis' complex (4.16) on a bounded open `Ω ⊆ ℝ³`**:
`H̊²(Ω) --grad grad--> H̊(curl, Ω; S) --curl--> L²(Ω; T)`, `W0 = L²(Ω)`, `W1 = L²(Ω; S)`,
`W2 = L²(Ω; T)`. -/
def symComplexB (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    HilbertComplex2 (L2 Ω) (L2S Ω) (L2T Ω) where
  d0 := hessS
  d1 := curlS
  dense0 := dense_domain_hessS hΩ hb
  dense1 := dense_domain_curlS hΩ hb
  closed0 := isClosed_hessS hΩ hb
  closed1 := isClosed_curlS hΩ hb
  map_mem := hessS_mem_domain_curlS hΩ hb
  comp_zero := fun u => apply_eq_of_mem_graph
    (by rw [curlS_graph hΩ hb]; exact hessS_mem_curlSGraph hΩ hb u) _

@[simp] theorem symComplexB_d0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (symComplexB hΩ hb).d0 = hessS := rfl

@[simp] theorem symComplexB_d1 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (symComplexB hΩ hb).d1 = curlS := rfl

/-! ## The adjoint complex (4.17) -/


/-- `⟪(f : L2), φ⟫ = ∫ f φ` for a test function `φ`. -/
theorem inner_testFieldR (f : L2 Ω) {φ : R3 → ℝ} (hφ : IsTest Ω φ) :
    ⟪f, testFieldR hφ⟫ = ∫ x, f x * φ x ∂volume.restrict Ω :=
  (integral_mul_eq_inner f hφ.memLp).symm

/-- `⟪B, grad grad φ⟫ = Σ_{ij} ∫ B_{ij} ∂_j ∂_i φ`. -/
theorem inner_hessTestField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (B : L2S Ω)
    {φ : R3 → ℝ} (hφ : IsTest Ω φ) :
    ⟪B, hessTestField hΩ hb hφ⟫ =
      ∑ ij, ∫ x, (B : L2M Ω) ij x * hessField φ ij x ∂volume.restrict Ω := by
  rw [Submodule.coe_inner, hessTestField, inner_smoothField]

/-- **`(grad grad)* ⊇ div div`, weakly**: if `B ∈ L²(S)` has a weak double divergence `D`
(`Σ_{ij} ∫ B_{ij} ∂_i ∂_j φ = ∫ D φ` for all `φ ∈ C_c^∞(Ω)`), then `B ∈ D((grad grad)*)` and
`(grad grad)* B = D`. -/
theorem adjoint_hessS_of_weak (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2S Ω}
    {D : L2 Ω} (hD : ∀ φ : R3 → ℝ, IsTest Ω φ →
      ∑ ij, ∫ x, (B : L2M Ω) ij x * hessField φ ij x ∂volume.restrict Ω =
        ∫ x, D x * φ x ∂volume.restrict Ω) :
    ∃ h : B ∈ (hessS (Ω := Ω))†.domain, (hessS (Ω := Ω))† ⟨B, h⟩ = D := by
  have key : ∀ u : (hessS (Ω := Ω)).domain, ⟪D, (u : L2 Ω)⟫ = ⟪B, hessS u⟫ := by
    intro u
    let G : L2 Ω × L2M Ω →L[ℝ] ℝ := (innerSL ℝ (B : L2M Ω)).comp (ContinuousLinearMap.snd ℝ _ _) -
      (innerSL ℝ D).comp (ContinuousLinearMap.fst ℝ _ _)
    have hG : ∀ p : L2 Ω × L2M Ω, G p = ⟪(B : L2M Ω), p.2⟫ - ⟪D, p.1⟫ := fun p => rfl
    have hsub : hessGraphSub Ω ≤ LinearMap.ker (G : L2 Ω × L2M Ω →ₗ[ℝ] ℝ) := by
      refine Submodule.span_le.2 ?_
      rintro ⟨v, H⟩ ⟨φ, hφ, hp1, hp2⟩
      have ev : v = testFieldR hφ := Lp.ext (hp1.trans hφ.memLp.coeFn_toLp.symm)
      have eH : H = smoothField hΩ hb (hessField φ)
          (fun ij => (isTest_hessField hφ ij).continuous) :=
        (WithLp.ext_iff 2).2 (funext fun ij =>
          Lp.ext ((hp2 ij).trans (coeFn_smoothField hΩ hb _ _ ij).symm))
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hG, ev, eH,
        sub_eq_zero]
      rw [inner_smoothField, inner_testFieldR, hD φ hφ]
    have h := Submodule.topologicalClosure_minimal _ hsub G.isClosed_ker (mem_closure_hessS hΩ hb u)
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hG, sub_eq_zero] at h
    rw [Submodule.coe_inner]
    exact h.symm
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq (dense_domain_hessS hΩ hb) ⟨_, hmem⟩ key⟩

/-- `ker (grad grad)* = H(div div, S, 0)`: weakly `div div`-free symmetric fields (no boundary
condition). -/
theorem mem_ker_adjoint_hessS_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2S Ω} :
    B ∈ (hessS (Ω := Ω))†.ker ↔ ∀ φ : R3 → ℝ, IsTest Ω φ →
      ∑ ij, ∫ x, (B : L2M Ω) ij x * hessField φ ij x ∂volume.restrict Ω = 0 := by
  constructor
  · intro hB φ hφ
    obtain ⟨y, rfl, hy0⟩ := LinearPMap.mem_ker_iff.1 hB
    have e := LinearPMap.adjoint_isFormalAdjoint (dense_domain_hessS hΩ hb) y
      ⟨_, testFieldR_mem_domain hΩ hb hφ⟩
    simp only at e
    rw [hessS_testFieldR hΩ hb hφ, inner_hessTestField, hy0, inner_zero_left] at e
    exact e.symm
  · intro hB
    obtain ⟨h, h'⟩ := adjoint_hessS_of_weak hΩ hb (D := 0) fun φ hφ => by
      rw [hB φ hφ, integral_mul_eq_inner _ hφ.memLp, inner_zero_left]
    exact LinearPMap.mem_ker_iff.2 ⟨⟨B, h⟩, rfl, h'⟩

/-- `L²(TSD) ⊆ ker (grad grad)* = H(div div, S, 0)`: the hypothesis `hS1` of
`Feec.Constraints.prop_4_17` holds for (4.16) on `Ω`. -/
theorem TSDS_le_ker (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    TSDS Ω ≤ (symComplexB hΩ hb).d0†.ker := fun _ hB =>
  (mem_ker_adjoint_hessS_iff hΩ hb).2 fun φ hφ =>
    hB.2.2 (fun i => BoundedDomain.pd i φ) fun i => hφ.pdiff i

/-- Symmetric test fields lie in `D((grad grad)*) = H(div div, S)`, with
`(grad grad)* Φ = div div Φ`. -/
theorem testFieldS_mem_adjoint_hessS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij)) (hs : ∀ i j, Φ (i, j) = Φ (j, i)) :
    testFieldS hΩ hb hΦ hs ∈ (hessS (Ω := Ω))†.domain := by
  have hΦ2 : ∀ ij, ContDiff ℝ 2 (Φ ij) := fun ij => (hΦ ij).contDiff.of_le (by simp)
  have hm := memLp_of_continuous hΩ hb (continuous_divdivF hΦ2)
  refine (adjoint_hessS_of_weak hΩ hb (D := hm.toLp _) fun φ hφ => ?_).1
  have e1 : ∀ ij : Ix, ∫ x, ((testFieldS hΩ hb hΦ hs : L2S Ω) : L2M Ω) ij x * hessField φ ij x
      ∂volume.restrict Ω =
        ∫ x, φ x * BoundedDomain.pd ij.1 (BoundedDomain.pd ij.2 (Φ ij)) x ∂volume.restrict Ω := by
    intro ij
    rw [← integral_hessField_mul hφ (hΦ2 ij)]
    refine integral_congr_ae ((coeFn_smoothField hΩ hb Φ (fun ij => (hΦ ij).continuous) ij).mono
      fun x hx => ?_)
    simp only [testFieldS] at hx ⊢
    rw [hx, mul_comm]
  rw [Finset.sum_congr rfl fun ij _ => e1 ij, ← integral_finsetSum _ fun ij _ =>
    integrable_mul_of_compact hφ.continuous hφ.hasCompactSupport
      (continuous_pd (contDiff_pd (hΦ2 ij) ij.2) ij.1)]
  refine integral_congr_ae (hm.coeFn_toLp.mono fun x hx => ?_)
  simp only at hx ⊢
  rw [hx, divdivF, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **`curl* ⊇ sym curl`**: every `C¹`, pointwise trace-free field `Ψ` with no boundary
condition lies in `D(curl*) ⊆ L²(T)` (the adjoint of `curl` on `H̊(curl, S)`), and
`curl* Ψ = sym curl Ψ`. -/
theorem smoothField_mem_adjoint_curlS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) (htr : ∀ x, ∑ i, Ψ (i, i) x = 0) :
    ∃ h : (⟨smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous),
        smoothField_mem_trL2 hΩ hb _ htr⟩ : L2T Ω) ∈ (curlS (Ω := Ω))†.domain,
      ((curlS (Ω := Ω))† ⟨_, h⟩ : L2M Ω) =
        smoothField hΩ hb (symF (curlM Ψ)) (continuous_symF (continuous_curlM hΨ)) := by
  set S : L2S Ω := ⟨smoothField hΩ hb (symF (curlM Ψ)) (continuous_symF (continuous_curlM hΨ)),
    smoothField_mem_symL2 hΩ hb _ (symF_swap _)⟩
  have key : ∀ u : (curlS (Ω := Ω)).domain, ⟪S, (u : L2S Ω)⟫ =
      ⟪(⟨smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous),
        smoothField_mem_trL2 hΩ hb _ htr⟩ : L2T Ω), curlS u⟫ := by
    intro u
    rw [Submodule.coe_inner, Submodule.coe_inner, real_inner_comm ((u : L2S Ω) : L2M Ω),
      real_inner_comm ((curlS u : L2T Ω) : L2M Ω)]
    simp only [S]
    rw [inner_smoothField, inner_smoothField, sum_integral_mul_symF hΩ hb (u : L2S Ω).2
      (continuous_curlM hΨ)]
    exact (closure_curlGraph_identity hΩ hb (mem_closure_curlGraph_curlS hΩ hb u) hΨ).symm
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, congrArg Subtype.val
    (LinearPMap.adjoint_apply_eq (dense_domain_curlS hΩ hb) ⟨_, hmem⟩ key)⟩

/-! ## The zero-mean obstruction on `H̊(curl, S) ∩ L²(TSD)` -/

/-- **Every `E ∈ H̊(curl, S) ∩ L²(TSD)` has zero mean**, `∫_Ω E = 0`, on every bounded open `Ω`
(as for `H̊(curl, M)`: `H̊(curl, S) ⊆ H̊(curl, M)`). -/
theorem integral_eq_zero_of_mem_TSDS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (E : (curlS (Ω := Ω)).domain) (hE : (E : L2S Ω) ∈ TSDS Ω) (a b : Fin 3) :
    ∫ x, ((E : L2S Ω) : L2M Ω) (a, b) x ∂volume.restrict Ω = 0 :=
  integral_eq_zero_of_mem_TSD_of_mem_HcurlZero hΩ hb hE (mem_HcurlZero_of_mem_domain hΩ hb E) a b

/-- `diag(1, -1, 0)`, as an element of `L²(TSD) ⊆ L²(S)`. -/
def constS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : L2S Ω :=
  ⟨constField hΩ hb diagA, fun i j => by
    have h := (constField_mem_TSD hΩ hb diagA_transpose diagA_trace).1 i j
    exact h⟩

theorem constS_mem_TSDS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    constS hΩ hb ∈ TSDS Ω :=
  constField_mem_TSD hΩ hb diagA_transpose diagA_trace

/-- The pairing with `diag(1, -1, 0)` vanishes on `H̊(curl, S) ∩ L²(TSD)`. -/
theorem inner_constS_eq_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (E : (curlS (Ω := Ω)).domain) (hE : (E : L2S Ω) ∈ TSDS Ω) :
    ⟪(E : L2S Ω), constS hΩ hb⟫ = 0 := by
  rw [Submodule.coe_inner, constS, inner_constField]
  exact Finset.sum_eq_zero fun ij _ => by rw [integral_eq_zero_of_mem_TSDS hΩ hb E hE, mul_zero]

theorem volume_real_pos (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    0 < volume.real Ω := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (hΩ.measure_pos volume hne).ne' hb.measure_lt_top.ne

/-- **The density hypothesis of Prop 4.19 for `E` fails**: `H̊(curl, S) ∩ L²(TSD)` is not dense
in `L²(TSD)`; `diag(1, -1, 0)` is not in its closure.

Thesis gap: [QuennevilleBelair2015, §4.11, Prop 4.19] conjectures this density. -/
theorem not_dense_TSDS_inter_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    constS hΩ hb ∈ TSDS Ω ∧ constS hΩ hb ∉
      closure ((TSDS Ω : Set (L2S Ω)) ∩ (curlS (Ω := Ω)).domain) := by
  refine ⟨constS_mem_TSDS hΩ hb, fun hK => ?_⟩
  have hsub : (TSDS Ω : Set (L2S Ω)) ∩ (curlS (Ω := Ω)).domain ⊆
      (fun F => ⟪F, constS hΩ hb⟫) ⁻¹' {0} := by
    rintro F ⟨hF, hF'⟩
    exact inner_constS_eq_zero hΩ hb ⟨F, hF'⟩ hF
  have h0 := closure_minimal hsub (isClosed_singleton.preimage (continuous_id.inner
    continuous_const)) hK
  simp only [mem_preimage, mem_singleton_iff] at h0
  rw [Submodule.coe_inner, constS, inner_constField] at h0
  simp only [integral_constField] at h0
  have hpos := volume_real_pos hΩ hb hne
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, diagA] at h0
  linarith

/-! ## Prop 4.19 on `Ω`: the projection hypothesis and the conclusion fail -/

/-- `g · diag(1, -1, 0)` for a bump `g`: a symmetric test field. -/
theorem isTest_diagA_mul {g : R3 → ℝ} (hg : IsTest Ω g) (ij : Ix) :
    IsTest Ω (fun x => diagA ij.1 ij.2 * g x) :=
  ⟨contDiff_const.mul hg.contDiff, hg.hasCompactSupport.mul_left,
    tsupport_mul_subset_right.trans hg.tsupport_subset⟩

theorem diagA_swap (i j : Fin 3) : diagA i j = diagA j i := by
  rw [← Matrix.transpose_apply diagA j i, diagA_transpose]

/-- **The projection hypothesis of Prop 4.19 fails on every nonempty bounded open `Ω ⊆ ℝ³`**,
for the thesis' complex (4.16): `E = g · diag(1, -1, 0) ∈ C_c^∞(Ω; S)` lies in
`H̊(curl, S) ∩ H(div div, S)`, but `P_{L²(TSD)} E ∉ H̊(curl, S)` (it has nonzero mean). So
`P_K D(L) ⊄ D(L)` for `K = {0} × L²(TSD) × S2`, any `S2`.

Correction: refutes the first conjecture of [QuennevilleBelair2015, §4.11, Prop 4.19],
`P_{L²(TSD)} (H̊(curl, S) ∩ H(div div, S)) ⊂ H̊(curl, S) ∩ H(div div, S)`. -/
theorem symComplexB_not_projection_hyp (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S2 : Submodule ℝ (L2T Ω)) [S2.HasOrthogonalProjection] :
    ¬ ∀ x ∈ (symComplexB hΩ hb).domL,
      projKc (L2 Ω) (TSDS Ω) S2 x ∈ (symComplexB hΩ hb).domL := by
  intro hPD
  obtain ⟨g, hg, hgpos⟩ := exists_isTest_integral_pos hΩ hne
  have hΦ := isTest_diagA_mul hg
  have hs : ∀ i j, (fun x => diagA (i, j).1 (i, j).2 * g x) =
      (fun x => diagA (j, i).1 (j, i).2 * g x) := fun i j => by
    simp only [diagA_swap i j]
  set E := testFieldS hΩ hb hΦ hs
  have hx : ini (L2 Ω) E (0 : L2T Ω) ∈ (symComplexB hΩ hb).domL := by
    rw [Feec.Constraints.mem_domL, tot_ini]
    exact ⟨Submodule.zero_mem _, Submodule.mem_inf.2 ⟨testFieldS_mem_domain hΩ hb hΦ hs,
      testFieldS_mem_adjoint_hessS hΩ hb hΦ hs⟩, Submodule.zero_mem _⟩
  have h := (Feec.Constraints.mem_domL _).1 (hPD _ hx)
  rw [tot_projKc, tot_ini] at h
  have hP : (TSDS Ω).starProjection E ∈ (curlS (Ω := Ω)).domain := (Submodule.mem_inf.1 h.2.1).1
  have h0 := inner_constS_eq_zero hΩ hb ⟨_, hP⟩ (Submodule.starProjection_apply_mem _ _)
  simp only at h0
  rw [Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.2 (constS_mem_TSDS hΩ hb), Submodule.coe_inner,
    constS, inner_constField] at h0
  have hI : ∀ ij : Ix, ∫ x, ((E : L2S Ω) : L2M Ω) ij x ∂volume.restrict Ω =
      diagA ij.1 ij.2 * ∫ x, g x ∂volume.restrict Ω := fun ij => by
    rw [← integral_const_mul]
    exact integral_congr_ae (coeFn_smoothField hΩ hb _ (fun ij => (hΦ ij).continuous) ij)
  simp only [hI, Fintype.sum_prod_type, Fin.sum_univ_three] at h0
  simp [diagA] at h0
  linarith

/-- `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)` is trace-free. -/
theorem betaField_trace (x : R3) : ∑ i, betaField (i, i) x = 0 := by
  simp [betaField, Fin.sum_univ_three]

theorem contDiff_one_betaField (ij : Ix) : ContDiff ℝ 1 (betaField ij) :=
  (contDiff_betaField ij).of_le (by simp)

/-- `β`, as an element of `L²(T)`. -/
def betaT (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : L2T Ω :=
  ⟨smoothField hΩ hb betaField (fun ij => (contDiff_one_betaField ij).continuous),
    smoothField_mem_trL2 hΩ hb _ betaField_trace⟩

theorem betaT_mem_TSDT (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : betaT hΩ hb ∈ TSDT Ω :=
  betaField_mem_TSD hΩ hb

/-- `β ∈ H(sym curl, T) = D(curl*)`, with `sym curl β = -diag(1, -1, 0)`. -/
theorem betaT_mem_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∃ h : betaT hΩ hb ∈ (curlS (Ω := Ω))†.domain,
      ((curlS (Ω := Ω))† ⟨_, h⟩ : L2M Ω) = smoothField hΩ hb (symF (curlM betaField))
        (continuous_symF (continuous_curlM contDiff_one_betaField)) :=
  smoothField_mem_adjoint_curlS hΩ hb contDiff_one_betaField betaField_trace

theorem inner_constS_adjoint_betaT (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (h : betaT hΩ hb ∈ (curlS (Ω := Ω))†.domain) :
    ⟪constS hΩ hb, (curlS (Ω := Ω))† ⟨_, h⟩⟫ = -(2 * volume.real Ω) := by
  obtain ⟨h', e⟩ := betaT_mem_adjoint hΩ hb
  rw [Submodule.coe_inner, real_inner_comm, e, constS, inner_constField]
  have hI : ∀ ij : Ix, ∫ x, smoothField hΩ hb (symF (curlM betaField))
      (continuous_symF (continuous_curlM contDiff_one_betaField)) ij x ∂volume.restrict Ω =
      volume.real Ω * -diagA ij.1 ij.2 := fun ij => by
    rw [integral_congr_ae (coeFn_smoothField hΩ hb _ _ ij)]
    simp only [symF, curlM_betaField, diagA_swap ij.2 ij.1, integral_const,
      measureReal_restrict_apply_univ, smul_eq_mul]
    ring
  simp only [hI]
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, diagA]
  ring

/-- The inclusion `L²(S) → L²(Ω; ℝ³ˣ³)`; it maps `H̊(curl, S)` into `H̊(curl, M)`. -/
theorem symL2_subtypeL_mem_HcurlZero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∀ u ∈ (symComplexB hΩ hb).d1.domain, (symL2 Ω).subtypeL u ∈ HcurlZero Ω :=
  fun u hu => mem_HcurlZero_of_mem_domain hΩ hb ⟨u, hu⟩

/-- `⟪sym curl β, diag(1, -1, 0)⟫ = -2 |Ω|`. -/
theorem inner_adjoint_betaT_constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (h : betaT hΩ hb ∈ (symComplexB hΩ hb).d1†.domain) :
    ⟪(symL2 Ω).subtypeL ((symComplexB hΩ hb).d1† ⟨_, h⟩), constField hΩ hb diagA⟫ =
      -(2 * volume.real Ω) := by
  rw [real_inner_comm]
  exact inner_constS_adjoint_betaT hΩ hb h

/-- **From `(0, E₀, β)`, for any `E₀` and any `S2`, every strong solution of (4.18) leaves
`{0} × L²(TSD) × S2`** on every `[0, T]`, `T > 0`: `sym curl β = -diag(1, -1, 0)` pairs nonzero
with `diag(1, -1, 0) ∈ TSD₀ᗮ` (`Feec.BoundedDomain.not_propagate_of_adjoint`, with
`ι : L²(S) → L²(M)` the inclusion). -/
theorem symComplexB_betaT_not_propagate (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S2 : Submodule ℝ (L2T Ω)) (E₀ : L2S Ω) :
    ∀ T > 0, ∀ U : ℝ → Tot (L2 Ω) (L2S Ω) (L2T Ω),
      IsStrongSolution (-(symComplexB hΩ hb).waveOp) T (ini (L2 Ω) E₀ (betaT hΩ hb)) 0 U →
        ∃ t ∈ Icc 0 T, U t ∉ Kc (L2 Ω) (TSDS Ω) S2 := by
  obtain ⟨h, -⟩ := betaT_mem_adjoint hΩ hb
  refine not_propagate_of_adjoint hΩ hb (symComplexB hΩ hb) (symL2 Ω).subtypeL
    (symL2_subtypeL_mem_HcurlZero hΩ hb) (S1 := TSDS Ω) (S2 := S2) (fun u hu => hu)
    (E₀ := E₀) (B₀ := betaT hΩ hb) h (constField_mem_orth hΩ hb diagA) ?_
  rw [inner_adjoint_betaT_constField hΩ hb h]
  have := volume_real_pos hΩ hb hne
  linarith

/-- **The conclusion of Prop 4.19 fails on every nonempty bounded open `Ω ⊆ ℝ³`** for the
thesis' complex (4.16), for every strong solution: the TSD datum `(σ₀, E₀, B₀) = (0, 0, β)`,
`β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ) ∈ H(sym curl, T) ∩ L²(TSD)`, lies in `D(L) ∩ K`,
`K = {0} × L²(TSD) × L²(TSD)`, and every strong solution of (4.18) on `[0, T]`, `T > 0`, leaves
`K` (`symComplexB_betaT_not_propagate`). Proof: every `E ∈ H̊(curl, S) ∩ L²(TSD)` lies in
`TSD₀ ⊥ diag(1, -1, 0)`, while `⟪sym curl β, diag(1, -1, 0)⟫ = -2|Ω| ≠ 0`.

Correction: refutes the conclusion of [QuennevilleBelair2015, §4.11, Prop 4.19] on bounded
domains. -/
theorem symComplexB_not_propagate (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ∃ B₀ : L2T Ω, B₀ ∈ TSDT Ω ∧ ini (L2 Ω) 0 B₀ ∈ (symComplexB hΩ hb).domL ∧
      ini (L2 Ω) 0 B₀ ∈ Kc (L2 Ω) (TSDS Ω) (TSDT Ω) ∧
      ∀ T > 0, ∀ U : ℝ → Tot (L2 Ω) (L2S Ω) (L2T Ω),
        IsStrongSolution (-(symComplexB hΩ hb).waveOp) T (ini (L2 Ω) 0 B₀) 0 U →
          ∃ t ∈ Icc 0 T, U t ∉ Kc (L2 Ω) (TSDS Ω) (TSDT Ω) := by
  obtain ⟨h, -⟩ := betaT_mem_adjoint hΩ hb
  refine ⟨betaT hΩ hb, betaT_mem_TSDT hΩ hb, ?_, ?_,
    symComplexB_betaT_not_propagate hΩ hb hne _ 0⟩
  · rw [Feec.Constraints.mem_domL, tot_ini]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, h⟩
  · rw [mem_Kc, tot_ini]
    exact ⟨rfl, Submodule.zero_mem _, betaT_mem_TSDT hΩ hb⟩

/-- **The conclusion of Prop 4.19 fails on bounded domains, unconditionally**: for the TSD datum
`(0, 0, β) ∈ D(L) ∩ K`, on every `[0, T]` with `T > 0`, the Hodge wave equation (4.18) has a
strong solution (Stone's theorem, `Feec.HilbertComplex2.waveGroup`) and every strong solution
leaves `K = {0} × L²(TSD) × L²(TSD)`.

Correction: [QuennevilleBelair2015, §4.11, Prop 4.19]. -/
theorem symComplexB_not_propagate_unconditional (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ∃ B₀ : L2T Ω, B₀ ∈ TSDT Ω ∧ ini (L2 Ω) 0 B₀ ∈ (symComplexB hΩ hb).domL ∧
      ini (L2 Ω) 0 B₀ ∈ Kc (L2 Ω) (TSDS Ω) (TSDT Ω) ∧
      ∀ T > 0, (∃ U : ℝ → Tot (L2 Ω) (L2S Ω) (L2T Ω),
          IsStrongSolution (-(symComplexB hΩ hb).waveOp) T (ini (L2 Ω) 0 B₀) 0 U) ∧
        ∀ U : ℝ → Tot (L2 Ω) (L2S Ω) (L2T Ω),
          IsStrongSolution (-(symComplexB hΩ hb).waveOp) T (ini (L2 Ω) 0 B₀) 0 U →
            ∃ t ∈ Icc 0 T, U t ∉ Kc (L2 Ω) (TSDS Ω) (TSDT Ω) := by
  obtain ⟨B₀, hB, hD, hK, hall⟩ := symComplexB_not_propagate hΩ hb hne
  exact ⟨B₀, hB, hD, hK, fun T hT =>
    ⟨⟨_, isStrongSolution_orbit (symComplexB hΩ hb).waveGroup T ⟨_, hD⟩⟩, hall T hT⟩⟩

/-! ## The second projection hypothesis of Prop 4.19 fails -/

/-- `smoothField` depends only on the field. -/
theorem smoothField_congr (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {Ψ Ψ' : Ix → R3 → ℝ}
    (h : Ψ = Ψ') (hΨ : ∀ ij, Continuous (Ψ ij)) (hΨ' : ∀ ij, Continuous (Ψ' ij)) :
    smoothField hΩ hb Ψ hΨ = smoothField hΩ hb Ψ' hΨ' := by
  subst h
  rfl

/-- `curl B_t` is symmetric, so `sym curl B_t = curl B_t`. -/
theorem symF_curlM_symFld (t : ℝ) : symF (curlM (symFld t)) = curlM (symFld t) := by
  funext ij x
  obtain ⟨i, k⟩ := ij
  simp only [symF, curlM_symFld]
  fin_cases i <;> fin_cases k <;> simp

/-- `E_t` is trace-free. -/
theorem gradFld_trace (t : ℝ) (x : R3) : ∑ i, gradFld t (i, i) x = 0 := by
  simp [gradFld, Fin.sum_univ_three]

/-- `B_t` is trace-free. -/
theorem symFld_trace (t : ℝ) (x : R3) : ∑ i, symFld t (i, i) x = 0 := by
  simp [symFld, Fin.sum_univ_three]

/-- **The second projection hypothesis of Prop 4.19 is false on every nonempty bounded open
`Ω ⊆ ℝ³`**: `P_{L²(TSD)}` does not map `H(sym curl, T) ⊇ D(curl*)` into `D(curl*)`, for
`curl*` the adjoint of `curl` on `H̊(curl, S)`. As for Prop 4.17
(`Feec.BoundedDomain.not_projection_hyp_adjoint`): otherwise `ρ ↦ curl* (P ρ)` is bounded on
the graph of `curl*` (closed graph theorem), but `E_t ∈ L²(T)` is curl-free, `P E_t = B_t` and
`‖sym curl B_t‖ = ‖curl B_t‖ = (t/√2) ‖E_t‖`.

Correction: refutes the second conjecture of [QuennevilleBelair2015, §4.11, Prop 4.19],
`P_{L²(TSD)} H(sym curl, T) ⊂ H(sym curl, T)`. -/
theorem not_projection_hyp_adjoint_curlS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ¬ ∀ B ∈ (curlS (Ω := Ω))†.domain, (TSDT Ω).starProjection B ∈ (curlS (Ω := Ω))†.domain := by
  intro hyp
  set A := (curlS (Ω := Ω))† with hA
  have hAc : A.IsClosed := LinearPMap.adjoint_isClosed (dense_domain_curlS hΩ hb)
  have : CompleteSpace A.graph :=
    (show IsClosed (A.graph : Set (L2T Ω × L2S Ω)) from hAc).completeSpace_coe
  have hdom : ∀ p : A.graph, (TSDT Ω).starProjection (p : L2T Ω × L2S Ω).1 ∈ A.domain :=
    fun p => hyp _ (LinearPMap.mem_domain_of_mem_graph (y := (p : L2T Ω × L2S Ω).2) p.2)
  let g0 : A.graph →ₗ[ℝ] A.domain := LinearMap.codRestrict A.domain
    (((TSDT Ω).starProjection : L2T Ω →L[ℝ] L2T Ω).toLinearMap ∘ₗ
      (LinearMap.fst ℝ (L2T Ω) (L2S Ω)) ∘ₗ A.graph.subtype) hdom
  let g : A.graph →ₗ[ℝ] L2S Ω := A.toFun ∘ₗ g0
  have hgc : IsClosed (g.graph : Set (A.graph × L2S Ω)) := by
    have e : (g.graph : Set (A.graph × L2S Ω)) =
        (fun q : A.graph × L2S Ω => ((TSDT Ω).starProjection (q.1 : L2T Ω × L2S Ω).1, q.2)) ⁻¹'
          (A.graph : Set (L2T Ω × L2S Ω)) := by
      ext ⟨p, F⟩
      simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, mem_preimage]
      constructor
      · rintro rfl
        exact A.mem_graph (g0 p)
      · intro h
        exact (apply_eq_of_mem_graph h (hdom p)).symm
    rw [e]
    exact hAc.preimage (((TSDT Ω).starProjection.continuous.comp
      (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd)
  let gc : A.graph →L[ℝ] L2S Ω := ⟨g, g.continuous_of_isClosed_graph hgc⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 * ‖gc‖ + 1 := ⟨_, rfl⟩
  have hgE : ∀ ij, ContDiff ℝ 1 (gradFld t ij) := fun ij => (contDiff_gradFld t ij).of_le (by simp)
  have hsB : ∀ ij, ContDiff ℝ 1 (symFld t ij) := fun ij => (contDiff_symFld t ij).of_le (by simp)
  obtain ⟨hE, hE'⟩ := smoothField_mem_adjoint_curlS hΩ hb hgE (gradFld_trace t)
  obtain ⟨hB, hB'⟩ := smoothField_mem_adjoint_curlS hΩ hb hsB (symFld_trace t)
  let E : L2T Ω := ⟨smoothField hΩ hb (gradFld t) (fun ij => (hgE ij).continuous),
    smoothField_mem_trL2 hΩ hb _ (gradFld_trace t)⟩
  let B : L2T Ω := ⟨smoothField hΩ hb (symFld t) (fun ij => (hsB ij).continuous),
    smoothField_mem_trL2 hΩ hb _ (symFld_trace t)⟩
  have hAE : A ⟨E, hE⟩ = 0 := by
    refine Subtype.ext ?_
    rw [hE']
    exact smoothField_eq_zero hΩ hb _ _ fun ij x => by
      simp [symF, curlM_gradFld]
  have hPE : (TSDT Ω).starProjection E = B := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := TSDT Ω)
      (show B ∈ TSDT Ω from symFld_mem_TSD hΩ hb t) fun w hw => ?_
    rw [Submodule.coe_inner, Submodule.coe_sub]
    have h := (TSD Ω).sub_starProjection_mem_orthogonal (E : L2M Ω)
    have e : (TSD Ω).starProjection (E : L2M Ω) = (B : L2M Ω) := starProjection_gradFld hΩ hb t
    rw [e] at h
    exact (Submodule.mem_orthogonal' _ _).1 h _ hw
  have hpmem : ((E, 0) : L2T Ω × L2S Ω) ∈ A.graph := by
    have := A.mem_graph ⟨E, hE⟩
    rwa [hAE] at this
  let p : A.graph := ⟨(E, 0), hpmem⟩
  have hgp : (gc p : L2M Ω) = smoothField hΩ hb (curlM (symFld t))
      (continuous_curlM fun ij => (contDiff_symFld t ij).of_le (by simp)) := by
    have : g0 p = ⟨_, hB⟩ := Subtype.ext hPE
    change ((A (g0 p) : L2S Ω) : L2M Ω) = _
    rw [this, hB']
    exact smoothField_congr hΩ hb (symF_curlM_symFld t) _ _
  have hnp : ‖p‖ = ‖(E : L2M Ω)‖ := by
    change ‖((E, 0) : L2T Ω × L2S Ω)‖ = ‖(E : L2M Ω)‖
    simp [Prod.norm_def]
  have hbound := gc.le_opNorm p
  rw [hnp] at hbound
  have hn : ‖gc p‖ = ‖(gc p : L2M Ω)‖ := rfl
  rw [hn, hgp] at hbound
  have h1 := norm_sq_curlSymFld hΩ hb t
  have h2 := norm_sq_gradFld hΩ hb hne t
  have hsq : t ^ 2 / 2 * ‖(E : L2M Ω)‖ ^ 2 ≤ (‖gc‖ * ‖(E : L2M Ω)‖) ^ 2 := by
    rw [← h1]
    exact pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hc := norm_nonneg gc
  have : t ^ 2 / 2 ≤ ‖gc‖ ^ 2 := by
    rw [mul_pow] at hsq
    exact le_of_mul_le_mul_right hsq h2
  rw [ht] at this
  have e : (2 * ‖gc‖ + 1) ^ 2 / 2 = ‖gc‖ ^ 2 + (‖gc‖ ^ 2 + 2 * ‖gc‖ + 1 / 2) := by ring
  linarith [sq_nonneg ‖gc‖]

/-- **The projection hypothesis `hPD` fails through its `B`-component as well**: for
`K = {0} × S1 × L²(TSD)` with any closed `S1 ⊆ L²(S)`, `P_K D(L) ⊄ D(L)` for (4.16) on `Ω`.

Correction: [QuennevilleBelair2015, §4.11, Prop 4.19]. -/
theorem symComplexB_not_projection_hyp2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S1 : Submodule ℝ (L2S Ω)) [S1.HasOrthogonalProjection] :
    ¬ ∀ x ∈ (symComplexB hΩ hb).domL,
      projKc (L2 Ω) S1 (TSDT Ω) x ∈ (symComplexB hΩ hb).domL := by
  intro hPD
  refine not_projection_hyp_adjoint_curlS hΩ hb hne fun B hB => ?_
  have hx : ini (L2 Ω) 0 B ∈ (symComplexB hΩ hb).domL := by
    rw [Feec.Constraints.mem_domL, tot_ini]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, hB⟩
  have h := (Feec.Constraints.mem_domL _).1 (hPD _ hx)
  rw [tot_projKc, tot_ini] at h
  exact h.2.2

/-! ## What survives: the obstruction space `TSD₀` and a necessary condition -/

/-- `H̊(curl, S) ∩ L²(TSD) ⊆ TSD₀`. -/
theorem mem_TSD0_of_mem_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (E : (curlS (Ω := Ω)).domain) (hE : (E : L2S Ω) ∈ TSDS Ω) :
    ((E : L2S Ω) : L2M Ω) ∈ TSD0 Ω hΩ hb :=
  mem_TSD0_of_mem_HcurlZero hΩ hb hE (mem_HcurlZero_of_mem_domain hΩ hb E)

/-- **A necessary condition for TSD propagation on `Ω`** (salvage of Prop 4.19). If some strong
solution of (4.18) from `(0, E₀, B₀)` stays in `K = {0} × L²(TSD) × S2` on `[0, T]`, `T > 0`,
then `E₀ ∈ TSD₀` and `B₀ ∈ H(sym curl, T) = D(curl*)` with `sym curl B₀ = curl* B₀ ∈ TSD₀`: the
initial electric field and velocity `Ė(0) = -sym curl B₀` are orthogonal to every gradient `∇φ`,
`φ ∈ C¹(ℝ³; ℝ³)` (weakly, `E₀ n = 0` and `(sym curl B₀) n = 0` on `∂Ω`). Proof:
`E(t) ∈ H̊(curl, S) ∩ L²(TSD) ⊆ TSD₀` (`mem_TSD0_of_mem_domain`) and `TSD₀` is closed, so it
contains `E(0)` and `Ė(0)` (`Feec.BoundedDomain.adjoint_mem_TSD0_of_propagate`, with
`ι : L²(S) → L²(M)` the inclusion).

For `B₀ = β`, `sym curl β = -diag(1, -1, 0)` violates this
(`symComplexB_betaT_not_propagate`).

Correction: [QuennevilleBelair2015, §4.11, Prop 4.19]; not in the thesis. -/
theorem symComplexB_mem_TSD0_of_propagate (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {S2 : Submodule ℝ (L2T Ω)} {E₀ : L2S Ω} {B₀ : L2T Ω} {T : ℝ} (hT : 0 < T)
    {U : ℝ → Tot (L2 Ω) (L2S Ω) (L2T Ω)}
    (hU : IsStrongSolution (-(symComplexB hΩ hb).waveOp) T (ini (L2 Ω) E₀ B₀) 0 U)
    (hK : ∀ t ∈ Icc 0 T, U t ∈ Kc (L2 Ω) (TSDS Ω) S2) :
    (E₀ : L2M Ω) ∈ TSD0 Ω hΩ hb ∧ ∃ h : B₀ ∈ (curlS (Ω := Ω))†.domain,
      (((curlS (Ω := Ω))† ⟨B₀, h⟩ : L2S Ω) : L2M Ω) ∈ TSD0 Ω hΩ hb := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hD := (Feec.Constraints.mem_domL (symComplexB hΩ hb)).1 (hU.mem 0 h0)
  have hK0 := (mem_Kc).1 (hK 0 h0)
  rw [hU.init, tot_ini] at hD hK0
  refine ⟨mem_TSD0_of_mem_domain hΩ hb ⟨E₀, (Submodule.mem_inf.1 hD.2.1).1⟩ hK0.2.1, ?_⟩
  exact adjoint_mem_TSD0_of_propagate hΩ hb (symComplexB hΩ hb) (symL2 Ω).subtypeL
    (symL2_subtypeL_mem_HcurlZero hΩ hb) (S1 := TSDS Ω) (S2 := S2) (fun u hu => hu) hT hU hK

/-! ## What survives: Props 4.16 and 4.18 for (4.16) on `Ω` -/

/-- **Prop 4.16 for the complex (4.16) on `Ω`** (unconditional): for data
`(0, E₀, B₀) ∈ D(L)` with `div div E₀ = 0` weakly (e.g. TSD data, `TSDS_le_ker`), the Hodge wave
equation (4.18) has a unique strong solution on `[0, T]`, and for all `t`: `σ(t) = 0` and
`div div E(t) = 0` weakly (`Σ_{ij} ∫ E_{ij} ∂_i ∂_j φ = 0` for all `φ ∈ C_c^∞(Ω)`). This is the
part of the constraint `K` of Prop 4.19 that does propagate on bounded domains.

See [QuennevilleBelair2015, §4.10, Prop 4.16] and [QuennevilleBelair2015, §4.11]. -/
theorem symComplexB_prop_4_16 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (T : ℝ)
    {E₀ : L2S Ω} {B₀ : L2T Ω} (hD : ini (L2 Ω) E₀ B₀ ∈ (symComplexB hΩ hb).domL)
    (hE₀ : E₀ ∈ (symComplexB hΩ hb).d0†.ker) :
    ∃ U, IsStrongSolution (-(symComplexB hΩ hb).waveOp) T (ini (L2 Ω) E₀ B₀) 0 U ∧
      (∀ t ∈ Icc 0 T, (tot (L2 Ω) (L2S Ω) (L2T Ω) (U t)).1 = 0 ∧
        ∀ φ : R3 → ℝ, IsTest Ω φ → ∑ ij, ∫ x, (((tot (L2 Ω) (L2S Ω) (L2T Ω) (U t)).2.1 : L2S Ω) :
          L2M Ω) ij x * hessField φ ij x ∂volume.restrict Ω = 0) ∧
      ∀ U', IsStrongSolution (-(symComplexB hΩ hb).waveOp) T (ini (L2 Ω) E₀ B₀) 0 U' →
        EqOn U U' (Icc 0 T) := by
  have hK : ini (L2 Ω) E₀ B₀ ∈ K (symComplexB hΩ hb) ⊤ := by
    rw [mem_K, tot_ini]
    exact ⟨rfl, hE₀, Submodule.mem_top⟩
  obtain ⟨U, hU, hUK, huniq⟩ := prop_4_16_exists_unconditional (symComplexB hΩ hb) ⊤ le_top T hD hK
  refine ⟨U, hU, fun t ht => ?_, huniq⟩
  obtain ⟨h1, h2, -⟩ := (mem_K _).1 (hUK t ht)
  exact ⟨h1, (mem_ker_adjoint_hessS_iff hΩ hb).1 h2⟩

/-- **Prop 4.18 for the complex (4.16) on `Ω`** (unconditional): for `E₀ ∈ H̊(curl, S)` with
`div div E₀ = 0` and `B₀ ∈ D(curl*)`, the reduced system `Ė = -sym curl B`, `Ḃ = curl E` has a
unique strong solution, `div div E = 0` for all time, and `(0, E, B)` solves (4.18).

See [QuennevilleBelair2015, §4.10, Prop 4.18]. -/
theorem symComplexB_prop_4_18 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (T : ℝ)
    {E₀ : L2S Ω} {B₀ : L2T Ω} (hE₀ : E₀ ∈ (curlS (Ω := Ω)).domain)
    (hE₀k : E₀ ∈ (symComplexB hΩ hb).d0†.ker) (hB₀ : B₀ ∈ (curlS (Ω := Ω))†.domain) :
    ∃ E B, IsReducedSolution (symComplexB hΩ hb) T E₀ B₀ E B ∧
      (∀ t ∈ Icc 0 T, E t ∈ (symComplexB hΩ hb).d0†.ker) ∧
      IsStrongSolution (-(symComplexB hΩ hb).waveOp) T (ini (L2 Ω) E₀ B₀) 0
        (fun t => (tot (L2 Ω) (L2S Ω) (L2T Ω)).symm (0, E t, B t)) ∧
      ∀ E' B', IsReducedSolution (symComplexB hΩ hb) T E₀ B₀ E' B' →
        EqOn E E' (Icc 0 T) ∧ EqOn B B' (Icc 0 T) :=
  prop_4_18_unconditional (symComplexB hΩ hb) T hE₀ hE₀k hB₀

/-! ## The remaining hypotheses of `prop_4_17` hold on `Ω` (Lemma 3.5) -/

/-- **`curl (H̊(curl, S) ∩ L²(TSD)) ⊆ L²(TSD)`** (the thesis' third itemized check, via
Lemma 3.5): `curl E` is symmetric (`curl_symm_of_mem_TSD`), trace-free (it lies in `L²(T)`), and
weakly divergence-free (`div curl = 0`: test against `∇φ`, whose curl vanishes). This is the
hypothesis `hd1` of `Feec.Constraints.prop_4_17`.

See [QuennevilleBelair2015, §4.11, proof of Prop 4.19]. -/
theorem curlS_mem_TSDT (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : (curlS (Ω := Ω)).domain) (hu : (u : L2S Ω) ∈ TSDS Ω) : curlS u ∈ TSDT Ω := by
  have hC := mem_closure_curlGraph_curlS hΩ hb u
  refine ⟨fun i j => curl_symm_of_mem_TSD hΩ hb hC hu i j, (curlS u).2, fun φ hφ => ?_⟩
  have e := closure_curlGraph_identity hΩ hb hC (Ψ := gradM φ)
    fun ij => (hφ ij.1).pdiff ij.2 |>.contDiff_one
  have h0 : ∀ ij x, curlM (gradM φ) ij x = 0 := fun ij x =>
    curlM_gradM (fun i => (hφ i).contDiff.of_le (by simp)) ij x
  simp only [h0, mul_zero, integral_zero, Finset.sum_const_zero] at e
  exact e

/-- The adjoint identity against symmetric test fields: `⟪curl* ρ, Φ⟫ = ⟪ρ, curl Φ⟫`. -/
theorem adjoint_curlS_inner (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (ρ : (curlS (Ω := Ω))†.domain) {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, IsTest Ω (Φ ij))
    (hs : ∀ i j, Φ (i, j) = Φ (j, i)) :
    ∑ ij, ∫ x, (((curlS (Ω := Ω))† ρ : L2S Ω) : L2M Ω) ij x * Φ ij x ∂volume.restrict Ω =
      ∑ ij, ∫ x, ((ρ : L2T Ω) : L2M Ω) ij x * curlM Φ ij x ∂volume.restrict Ω := by
  have e := LinearPMap.adjoint_isFormalAdjoint (dense_domain_curlS hΩ hb) ρ
    ⟨_, testFieldS_mem_domain hΩ hb hΦ hs⟩
  simp only at e
  rw [apply_eq_of_mem_graph (testFieldS_mem_graph hΩ hb hΦ hs), Submodule.coe_inner,
    Submodule.coe_inner, testFieldS, curlTestFieldS, inner_smoothField, inner_smoothField] at e
  exact e

/-- `∂_k ((f + g)/2) = (∂_k f + ∂_k g)/2`. -/
theorem pd_avg {f g : R3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (k : Fin 3)
    (x : R3) : BoundedDomain.pd k (fun y => (f y + g y) / 2) x =
      (BoundedDomain.pd k f x + BoundedDomain.pd k g x) / 2 := by
  have : (fun y => (f y + g y) / 2) = fun y => (1 / 2 : ℝ) * (f + g) y := by
    funext y
    simp only [Pi.add_apply]
    ring
  rw [this, pd_const_mul (hf.add hg), pd_add hf hg]
  ring

/-- The scalar field `g I`. -/
def diagOf (g : R3 → ℝ) : Ix → R3 → ℝ := fun ij => if ij.1 = ij.2 then g else 0

/-- `curl (g I) = skewOf (-∇g)` is skew. -/
theorem curlM_diagOf {g : R3 → ℝ} (ij : Ix) (x : R3) :
    curlM (diagOf g) ij x = skewOf (fun i y => -BoundedDomain.pd i g y) ij x := by
  obtain ⟨a, b⟩ := ij
  simp only [curlM, diagOf, skewOf, pd_ite_zero]
  fin_cases a <;> fin_cases b <;> simp

/-- `curl sym ∇ψ = ½ (∇ curl ψ)ᵀ` (rows `½ ∂_a curl ψ`). -/
theorem curlM_symF_gradM {ψ : Fin 3 → R3 → ℝ} (hψ : ∀ i, IsTest Ω (ψ i)) (ab : Ix) (x : R3) :
    curlM (symF (gradM ψ)) ab x = (BoundedDomain.pd ab.1 (fun y =>
      BoundedDomain.pd (ab.2 + 1) (ψ (ab.2 + 2)) y -
        BoundedDomain.pd (ab.2 + 2) (ψ (ab.2 + 1)) y) x) / 2 := by
  obtain ⟨a, b⟩ := ab
  have hd : ∀ c i, Differentiable ℝ (BoundedDomain.pd c (ψ i)) := fun c i =>
    ((hψ i).pdiff c).differentiable
  have h2 : ∀ i, ContDiff ℝ 2 (ψ i) := fun i => (hψ i).contDiff.of_le (by simp)
  have hS : ∀ c, symF (gradM ψ) (a, c) = fun y =>
      (BoundedDomain.pd c (ψ a) y + BoundedDomain.pd a (ψ c) y) / 2 := fun c => rfl
  simp only [curlM]
  rw [hS, hS, pd_avg (hd _ _) (hd _ _), pd_avg (hd _ _) (hd _ _)]
  have hs : (fun y => BoundedDomain.pd (b + 1) (ψ (b + 2)) y -
      BoundedDomain.pd (b + 2) (ψ (b + 1)) y) =
      BoundedDomain.pd (b + 1) (ψ (b + 2)) - BoundedDomain.pd (b + 2) (ψ (b + 1)) := rfl
  rw [hs, pd_sub (hd _ _) (hd _ _), pd_pd_comm (h2 a) (b + 1) (b + 2),
    pd_pd_comm (h2 (b + 2)) (b + 1) a, pd_pd_comm (h2 (b + 1)) (b + 2) a]
  ring

/-- **`curl* (H(sym curl, T) ∩ L²(TSD)) ⊆ L²(TSD)`** (the thesis' third itemized check, via
Lemma 3.5), for `curl*` the adjoint of `curl` on `H̊(curl, S)`: `curl* ρ` is symmetric (it lies in
`L²(S)`), trace-free (`⟪curl* ρ, g I⟫ = ⟪ρ, curl (g I)⟫ = 0`, `curl (g I)` skew, `ρ` symmetric),
and weakly divergence-free (`⟪curl* ρ, ∇ψ⟫ = ⟪ρ, curl sym ∇ψ⟫ = ½ ⟪ρ, (∇ curl ψ)ᵀ⟫ = 0`). This is
the hypothesis `hd1s` of `Feec.Constraints.prop_4_17`.

See [QuennevilleBelair2015, §4.11, proof of Prop 4.19]. -/
theorem adjoint_curlS_mem_TSDS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (ρ : (curlS (Ω := Ω))†.domain) (hρ : (ρ : L2T Ω) ∈ TSDT Ω) :
    (curlS (Ω := Ω))† ρ ∈ TSDS Ω := by
  set D : L2M Ω := (((curlS (Ω := Ω))† ρ : L2S Ω) : L2M Ω)
  have hDs : D ∈ symL2 Ω := ((curlS (Ω := Ω))† ρ).2
  have hρs : ∀ j k, ((ρ : L2T Ω) : L2M Ω) (j, k) = ((ρ : L2T Ω) : L2M Ω) (k, j) := hρ.1
  refine ⟨hDs, ?_, fun ψ hψ => ?_⟩
  · -- trace
    refine L2_ext_of_integral hΩ hb fun g hg => ?_
    have hΦ : ∀ ij, IsTest Ω (diagOf g ij) := fun ij => by
      unfold diagOf; split_ifs; exacts [hg, IsTest.zero]
    have hsΦ : ∀ i j, diagOf g (i, j) = diagOf g (j, i) := fun i j => by
      simp only [diagOf, eq_comm]
    have e := adjoint_curlS_inner hΩ hb ρ hΦ hsΦ
    simp only [curlM_diagOf] at e
    rw [sum_integral_mul_skewOf_eq_zero hρs] at e
    have e2 : ∑ ij : Ix, ∫ x, D ij x * diagOf g ij x ∂volume.restrict Ω =
        ∑ i, ∫ x, D (i, i) x * g x ∂volume.restrict Ω := by
      simp only [diagOf]
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    rw [e2] at e
    rw [integral_mul_eq_inner _ hg.memLp, integral_mul_eq_inner _ hg.memLp, inner_zero_left,
      sum_inner]
    rw [← e]
    exact Finset.sum_congr rfl fun i _ => (integral_mul_eq_inner _ hg.memLp).symm
  · -- divergence
    have hΦ : ∀ ij, IsTest Ω (symF (gradM ψ) ij) := isTest_symF (isTest_gradM hψ)
    have e := adjoint_curlS_inner hΩ hb ρ hΦ (symF_swap _)
    rw [sum_integral_mul_symF hΩ hb hDs fun ij => (isTest_gradM hψ ij).continuous] at e
    have hw : ∀ b, IsTest Ω (fun y => BoundedDomain.pd (b + 1) (ψ (b + 2)) y -
        BoundedDomain.pd (b + 2) (ψ (b + 1)) y) := fun b => by
      have h := ((hψ (b + 2)).pdiff (b + 1)).add (((hψ (b + 1)).pdiff (b + 2)).const_mul (-1))
      convert h using 1
      funext y
      simp only [Pi.add_apply]
      ring
    have hdiv : ∑ ij : Ix, ∫ x, ((ρ : L2T Ω) : L2M Ω) ij x * BoundedDomain.pd ij.2
        (fun y => BoundedDomain.pd (ij.1 + 1) (ψ (ij.1 + 2)) y -
          BoundedDomain.pd (ij.1 + 2) (ψ (ij.1 + 1)) y) x ∂volume.restrict Ω = 0 :=
      hρ.2.2 (fun b y => BoundedDomain.pd (b + 1) (ψ (b + 2)) y -
        BoundedDomain.pd (b + 2) (ψ (b + 1)) y) hw
    simp only [curlM_symF_gradM hψ, mul_div_assoc', integral_div, ← Finset.sum_div] at e
    show ∑ ij : Ix, ∫ x, D ij x * gradM ψ ij x ∂volume.restrict Ω = 0
    rw [e, div_eq_zero_iff]
    left
    rw [← hdiv]
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun jk => ?_
    obtain ⟨j, k⟩ := jk
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [hρs j k]

/-- **Diagnosis of Prop 4.19 on bounded domains.** For the thesis' complex (4.16) on every
nonempty bounded open `Ω ⊆ ℝ³`, with `S1 = S2 = L²(TSD)`: the hypotheses `hS1`, `hd1`, `hd1s` of
`Feec.Constraints.prop_4_17` hold (Lemma 3.5), while the projection hypothesis `hPD` fails, through
the `E`-component and independently through the `B`-component; and TSD propagation itself fails
(`symComplexB_not_propagate_unconditional`).

Correction: [QuennevilleBelair2015, §4.11, Prop 4.19]. -/
theorem symComplexB_diagnosis (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    TSDS Ω ≤ (symComplexB hΩ hb).d0†.ker ∧
      (∀ u : (symComplexB hΩ hb).d1.domain, (u : L2S Ω) ∈ TSDS Ω →
        (symComplexB hΩ hb).d1 u ∈ TSDT Ω) ∧
      (∀ ρ : (symComplexB hΩ hb).d1†.domain, (ρ : L2T Ω) ∈ TSDT Ω →
        (symComplexB hΩ hb).d1† ρ ∈ TSDS Ω) ∧
      (¬ ∀ x ∈ (symComplexB hΩ hb).domL,
        projKc (L2 Ω) (TSDS Ω) (TSDT Ω) x ∈ (symComplexB hΩ hb).domL) ∧
      ¬ ∀ B ∈ (symComplexB hΩ hb).d1†.domain,
        (TSDT Ω).starProjection B ∈ (symComplexB hΩ hb).d1†.domain :=
  ⟨TSDS_le_ker hΩ hb, curlS_mem_TSDT hΩ hb, adjoint_curlS_mem_TSDS hΩ hb,
    symComplexB_not_projection_hyp hΩ hb hne _, not_projection_hyp_adjoint_curlS hΩ hb hne⟩

/-! ## Corrected Prop 4.19: the maximal propagating constraint space -/

section Max

variable (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)

/-- The Hessian `∇²h` of a smooth harmonic function, as an element of `L²(T)`
(`tr ∇²h = Δh = 0`). -/
def hessT {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) (hΔ : ∀ x, lap h x = 0) : L2T Ω :=
  ⟨hessL2 hΩ hb hh, smoothField_mem_trL2 hΩ hb _ hΔ⟩

/-- The Hessian `∇²h` of a smooth function, as an element of `L²(S)` (Schwarz). -/
def hessSym {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) : L2S Ω :=
  ⟨hessL2 hΩ hb hh, smoothField_mem_symL2 hΩ hb _ fun i j =>
    funext fun x => (pd_pd_comm (hh.of_le (by simp)) i j x).symm⟩

/-- `diag(1, -1, 0)`, as an element of `L²(TSD) ⊆ L²(T)`. -/
def constT : L2T Ω :=
  ⟨smoothField hΩ hb (fun ij _ => diagA ij.1 ij.2) (fun _ => continuous_const),
    smoothField_mem_trL2 hΩ hb _ fun _ => by simpa [Matrix.trace] using diagA_trace⟩

theorem constT_coe : (constT hΩ hb : L2M Ω) = constField hΩ hb diagA := rfl

theorem constT_mem_TSDT : constT hΩ hb ∈ TSDT Ω :=
  constField_mem_TSD hΩ hb diagA_transpose diagA_trace

/-- `sym curl` of a `C¹` trace-free field with `curl Ψ = 0` vanishes: such `Ψ ∈ D(curl*)` with
`curl* Ψ = 0`. -/
theorem adjoint_curlS_eq_zero {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij))
    (htr : ∀ x, ∑ i, Ψ (i, i) x = 0) (hc : ∀ ij x, curlM Ψ ij x = 0) :
    ∃ h : (⟨smoothField hΩ hb Ψ (fun ij => (hΨ ij).continuous),
        smoothField_mem_trL2 hΩ hb _ htr⟩ : L2T Ω) ∈ (symComplexB hΩ hb).d1†.domain,
      (symComplexB hΩ hb).d1† ⟨_, h⟩ = 0 := by
  obtain ⟨h, e⟩ := smoothField_mem_adjoint_curlS hΩ hb hΨ htr
  refine ⟨h, Subtype.ext ?_⟩
  change ((curlS (Ω := Ω))† ⟨_, h⟩ : L2M Ω) = 0
  rw [e]
  refine smoothField_eq_zero hΩ hb _ _ fun ij x => ?_
  simp [symF, hc]

variable (G : UnitaryGroupGenerator (-(symComplexB hΩ hb).waveOp))

/-- **The electric slot of `K*` lies in `TSD₀`** for (4.16): every `E ∈ S1*` satisfies
`E ⊥ ∇φ` for all `C¹` fields `φ` (weakly `E n = 0`), in particular `∫_Ω E = 0`
(`Feec.BoundedDomain.S1max_le_TSD0` with `ι : L²(S) → L²(M)` the inclusion). -/
theorem symComplexB_S1max_le_TSD0 (S2 : Submodule ℝ (L2T Ω)) [S2.HasOrthogonalProjection] :
    ∀ u ∈ S1max G (TSDS Ω) S2, (u : L2M Ω) ∈ TSD0 Ω hΩ hb :=
  S1max_le_TSD0 G hΩ hb (symL2 Ω).subtypeL (symL2_subtypeL_mem_HcurlZero hΩ hb) fun _ hu => hu

/-- **`S1* ⊊ L²(TSD)`** for (4.16): `diag(1, -1, 0) ∈ L²(TSD) ∩ L²(S)` is not in `S1*`. -/
theorem symComplexB_constS_not_mem_S1max (hne : Ω.Nonempty) (S2 : Submodule ℝ (L2T Ω))
    [S2.HasOrthogonalProjection] : constS hΩ hb ∉ S1max G (TSDS Ω) S2 := fun hm =>
  constField_diagA_not_mem_TSD0 hΩ hb hne (symComplexB_S1max_le_TSD0 hΩ hb G S2 _ hm)

/-- **`S2* ⊊ L²(TSD)`** for (4.16): `β ∈ L²(TSD) ∩ H(sym curl, T)` is not in `S2*`, for any
`S2`: otherwise `sym curl β = -diag(1, -1, 0) ∈ S1* ⊆ TSD₀`, which has nonzero mean. -/
theorem symComplexB_betaT_not_mem_S2max (hne : Ω.Nonempty) (S2 : Submodule ℝ (L2T Ω))
    [S2.HasOrthogonalProjection] : betaT hΩ hb ∉ S2max G (TSDS Ω) S2 := by
  intro hm
  obtain ⟨h, -⟩ := betaT_mem_adjoint hΩ hb
  have hT := symComplexB_S1max_le_TSD0 hΩ hb G S2 _ (adj1_mem_S1max G ⟨_, h⟩ hm)
  have hc := inner_adjoint_betaT_constField hΩ hb h
  have h0 := (Submodule.mem_orthogonal' _ _).1 (constField_mem_orth hΩ hb diagA) _ hT
  rw [real_inner_comm] at h0
  rw [show ((symL2 Ω).subtypeL ((symComplexB hΩ hb).d1† ⟨_, h⟩) : L2M Ω) =
    (((symComplexB hΩ hb).d1† ⟨_, h⟩ : L2S Ω) : L2M Ω) from rfl, h0] at hc
  have := volume_real_pos hΩ hb hne
  linarith

/-- **Hessians of smooth harmonic functions are stationary magnetic data for (4.16)**:
`∇²h ∈ L²(TSD) ∩ H(sym curl, T)` with `sym curl ∇²h = 0` (`curl ∇²h = 0`), so `(0, 0, ∇²h)` is a
stationary point of (4.18) in `K`, and `∇²h ∈ S2*`. -/
theorem symComplexB_hessT_mem_S2max {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) (hΔ : ∀ x, lap h x = 0) :
    hessT hΩ hb hh hΔ ∈ S2max G (TSDS Ω) (TSDT Ω) := by
  obtain ⟨hadj, e⟩ := adjoint_curlS_eq_zero hΩ hb
    (fun ij => contDiff_one_of_top (contDiff_hessField hh ij)) hΔ fun ij x => by
      rw [hessField_eq_gradM]
      exact curlM_gradM (fun i => (contDiff_pd_top hh i).of_le (by simp)) ij x
  exact mem_S2max_of_adj1_eq_zero G ⟨_, hadj⟩ (hessL2_mem_TSD hΩ hb hh hΔ) e

/-- **`diag(1, -1, 0)` is a nonzero stationary magnetic datum for (4.16)**: `constT ∈ S2*`. -/
theorem symComplexB_constT_mem_S2max : constT hΩ hb ∈ S2max G (TSDS Ω) (TSDT Ω) := by
  obtain ⟨hadj, e⟩ := adjoint_curlS_eq_zero hΩ hb (Ψ := fun ij _ => diagA ij.1 ij.2)
    (fun _ => contDiff_const) (fun _ => by simpa [Matrix.trace] using diagA_trace)
    fun ij x => by simp [curlM, BoundedDomain.pd]
  exact mem_S2max_of_adj1_eq_zero G ⟨_, hadj⟩ (constT_mem_TSDT hΩ hb) e

theorem constT_ne_zero (hne : Ω.Nonempty) : constT hΩ hb ≠ 0 := fun h0 =>
  constField_diagA_not_mem_TSD0 hΩ hb hne (by
    rw [← constT_coe, h0]; exact Submodule.zero_mem _)

/-- **The stationary part of `S2*` is infinite-dimensional** for (4.16) on a nonempty bounded
open `Ω`: it contains the independent harmonic Hessians `∇²(e^{-n x₁} cos(n x₂))`
(`Feec.BoundedDomain.linearIndependent_hessL2_expCos`). -/
theorem symComplexB_not_finiteDimensional_S2max (hne : Ω.Nonempty) :
    ¬ FiniteDimensional ℝ (S2max G (TSDS Ω) (TSDT Ω)) := by
  intro hfin
  let v : ℕ → S2max G (TSDS Ω) (TSDT Ω) := fun n =>
    ⟨_, symComplexB_hessT_mem_S2max hΩ hb G (contDiff_expCos ((n : ℝ) + 1)) (lap_expCos _)⟩
  have hli : LinearIndependent ℝ v :=
    LinearIndependent.of_comp ((trL2 Ω).subtype ∘ₗ (S2max G (TSDS Ω) (TSDT Ω)).subtype)
      (linearIndependent_hessL2_expCos hΩ hb hne)
  exact Module.Finite.not_linearIndependent_of_infinite v hli

end Max

/-- **The obstruction in `L²(S)` is infinite-dimensional**: on a nonempty bounded open `Ω`,
`L²(TSD) ∩ L²(S)` orthogonal to `TSD₀` (pulled back to `L²(S)`) contains the independent
harmonic Hessians; and since `H̊(curl, S) ∩ L²(TSD) ⊆ TSD₀`, the orthogonal complement of the
closure of `H̊(curl, S) ∩ L²(TSD)` in `L²(TSD) ∩ L²(S)` is infinite-dimensional: no
finite-dimensional correction makes the density conjecture of Prop 4.19 true.

Correction: [QuennevilleBelair2015, §4.11, Prop 4.19] conjectures density. -/
theorem not_finiteDimensional_obstrS (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ¬ FiniteDimensional ℝ (TSDS Ω ⊓ ((TSD0 Ω hΩ hb).comap (symL2 Ω).subtype)ᗮ :
        Submodule ℝ (L2S Ω)) ∧
      ¬ FiniteDimensional ℝ (TSDS Ω ⊓ (Submodule.span ℝ
        (closure ((TSDS Ω : Set (L2S Ω)) ∩ (curlS (Ω := Ω)).domain)))ᗮ : Submodule ℝ (L2S Ω)) := by
  have hmem : ∀ n : ℕ, hessSym hΩ hb (contDiff_expCos ((n : ℝ) + 1)) ∈
      TSDS Ω ⊓ ((TSD0 Ω hΩ hb).comap (symL2 Ω).subtype)ᗮ := fun n => by
    have ho := hessL2_mem_obstr hΩ hb (contDiff_expCos ((n : ℝ) + 1)) (lap_expCos _)
    refine ⟨ho.1, (Submodule.mem_orthogonal' _ _).2 fun u hu => ?_⟩
    rw [Submodule.coe_inner]
    exact (Submodule.mem_orthogonal' _ _).1 ho.2 _ hu
  have hle : (TSDS Ω ⊓ ((TSD0 Ω hΩ hb).comap (symL2 Ω).subtype)ᗮ : Submodule ℝ (L2S Ω)) ≤
      TSDS Ω ⊓ (Submodule.span ℝ
        (closure ((TSDS Ω : Set (L2S Ω)) ∩ (curlS (Ω := Ω)).domain)))ᗮ := by
    refine inf_le_inf_left _ (Submodule.orthogonal_le (Submodule.span_le.2 ?_))
    refine closure_minimal (fun E hE => mem_TSD0_of_mem_domain hΩ hb ⟨E, hE.2⟩ hE.1) ?_
    exact (isClosed_TSD0 hΩ hb).preimage continuous_subtype_val
  have h1 : ¬ FiniteDimensional ℝ (TSDS Ω ⊓ ((TSD0 Ω hΩ hb).comap (symL2 Ω).subtype)ᗮ :
      Submodule ℝ (L2S Ω)) := by
    intro hfin
    let v : ℕ → (TSDS Ω ⊓ ((TSD0 Ω hΩ hb).comap (symL2 Ω).subtype)ᗮ : Submodule ℝ (L2S Ω)) :=
      fun n => ⟨_, hmem n⟩
    have hli : LinearIndependent ℝ v :=
      LinearIndependent.of_comp ((symL2 Ω).subtype ∘ₗ Submodule.subtype _)
        (linearIndependent_hessL2_expCos hΩ hb hne)
    exact Module.Finite.not_linearIndependent_of_infinite v hli
  exact ⟨h1, fun hfin => h1 (Submodule.finiteDimensional_of_le hle)⟩

/-- **Corrected Prop 4.19 on bounded domains** (complex (4.16)
`H̊²(R) → H̊(curl, S) → L²(T)`, `K = {0} × L²(TSD) × L²(TSD)`, `K* = {x | ∀ t, e^{-tL} x ∈ K}`
for the Hodge wave group of Stone's theorem, `Feec.HilbertComplex2.waveGroup`), on every
nonempty bounded open `Ω ⊆ ℝ³`, with no hypothesis:
1. `K* = {0} × S1* × S2*` with `S1* ⊆ TSD₀` (weakly `E n = 0`) and `S2* ⊆ L²(TSD)`;
2. `(S1*, S2*)` satisfies all hypotheses of `Feec.Constraints.prop_4_17` (projection hypothesis,
   `curl (V1 ∩ S1*) ⊆ S2*`, `sym curl (V2* ∩ S2*) ⊆ S1*`), and it is the largest such pair inside
   `L²(TSD) × L²(TSD)`;
3. strictness: `diag(1, -1, 0) ∈ L²(TSD) ∩ L²(S) \ S1*` and `β ∈ L²(TSD) ∩ L²(T) \ S2*`; while
   `diag(1, -1, 0) ∈ S2*` is a nonzero **stationary** datum, and the stationary part of `S2*` is
   infinite-dimensional (`symComplexB_not_finiteDimensional_S2max`);
4. every datum `(0, E₀, B₀) ∈ D(L)` with `E₀ ∈ S1*`, `B₀ ∈ S2*` has, on every `[0, T]`, a unique
   strong solution of (4.18); it stays in `K* ⊆ K` and solves the reduced system.

Scope: as for `Feec.BoundedDomain.thesisComplex_prop_4_17_max`, `K*` is invariant by definition,
so items 2 and 4 run the thesis' argument on the largest subspace where it can work; the content
is in items 1 and 3 and in maximality. The only elements of `K*` exhibited are stationary
(`sym curl B = 0`); no nonzero element of `S1*` and no non-stationary element of `K*` is known.

Correction: [QuennevilleBelair2015, §4.11, Prop 4.19]: its projection hypotheses fail on every
nonempty bounded open `Ω` and its conclusion fails for `(0, 0, β)`; this statement replaces
`L²(TSD) × L²(TSD)` by the maximal admissible `S1* × S2*`. -/
theorem symComplexB_prop_4_19_max (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    let G := (symComplexB hΩ hb).waveGroup
    Kmax G (Kc (L2 Ω) (TSDS Ω) (TSDT Ω)) =
        Kc (L2 Ω) (S1max G (TSDS Ω) (TSDT Ω)) (S2max G (TSDS Ω) (TSDT Ω)) ∧
      (∀ u ∈ S1max G (TSDS Ω) (TSDT Ω), (u : L2M Ω) ∈ TSD0 Ω hΩ hb) ∧
      S2max G (TSDS Ω) (TSDT Ω) ≤ TSDT Ω ∧
      (∀ x ∈ (symComplexB hΩ hb).domL, projKc (L2 Ω) (S1max G (TSDS Ω) (TSDT Ω))
        (S2max G (TSDS Ω) (TSDT Ω)) x ∈ (symComplexB hΩ hb).domL) ∧
      (∀ u : (symComplexB hΩ hb).d1.domain, (u : L2S Ω) ∈ S1max G (TSDS Ω) (TSDT Ω) →
        (symComplexB hΩ hb).d1 u ∈ S2max G (TSDS Ω) (TSDT Ω)) ∧
      (∀ ρ : (symComplexB hΩ hb).d1†.domain, (ρ : L2T Ω) ∈ S2max G (TSDS Ω) (TSDT Ω) →
        (symComplexB hΩ hb).d1† ρ ∈ S1max G (TSDS Ω) (TSDT Ω)) ∧
      (∀ (S1' : Submodule ℝ (L2S Ω)) (S2' : Submodule ℝ (L2T Ω)) [S1'.HasOrthogonalProjection]
        [S2'.HasOrthogonalProjection], S1' ≤ TSDS Ω → S2' ≤ TSDT Ω →
        (∀ x ∈ (symComplexB hΩ hb).domL, projKc (L2 Ω) S1' S2' x ∈ (symComplexB hΩ hb).domL) →
        (∀ u : (symComplexB hΩ hb).d1.domain, (u : L2S Ω) ∈ S1' →
          (symComplexB hΩ hb).d1 u ∈ S2') →
        (∀ ρ : (symComplexB hΩ hb).d1†.domain, (ρ : L2T Ω) ∈ S2' →
          (symComplexB hΩ hb).d1† ρ ∈ S1') →
        S1' ≤ S1max G (TSDS Ω) (TSDT Ω) ∧ S2' ≤ S2max G (TSDS Ω) (TSDT Ω)) ∧
      constS hΩ hb ∈ TSDS Ω ∧ constS hΩ hb ∉ S1max G (TSDS Ω) (TSDT Ω) ∧
      betaT hΩ hb ∈ TSDT Ω ∧ betaT hΩ hb ∉ S2max G (TSDS Ω) (TSDT Ω) ∧
      constT hΩ hb ∈ S2max G (TSDS Ω) (TSDT Ω) ∧ constT hΩ hb ≠ 0 ∧
      ¬ FiniteDimensional ℝ (S2max G (TSDS Ω) (TSDT Ω)) ∧
      ∀ (T : ℝ) (E₀ : L2S Ω) (B₀ : L2T Ω), ini (L2 Ω) E₀ B₀ ∈ (symComplexB hΩ hb).domL →
        E₀ ∈ S1max G (TSDS Ω) (TSDT Ω) → B₀ ∈ S2max G (TSDS Ω) (TSDT Ω) →
        ∃ U, IsStrongSolution (-(symComplexB hΩ hb).waveOp) T (ini (L2 Ω) E₀ B₀) 0 U ∧
          (∀ U', IsStrongSolution (-(symComplexB hΩ hb).waveOp) T (ini (L2 Ω) E₀ B₀) 0 U' →
            EqOn U' U (Icc 0 T)) ∧
          (∀ t ∈ Icc 0 T, U t ∈ Kc (L2 Ω) (TSDS Ω) (TSDT Ω)) ∧
          IsReducedSolution (symComplexB hΩ hb) T E₀ B₀
            (fun t => (tot (L2 Ω) (L2S Ω) (L2T Ω) (U t)).2.1)
            (fun t => (tot (L2 Ω) (L2S Ω) (L2T Ω) (U t)).2.2) := by
  intro G
  refine ⟨Kmax_eq_Kc G, symComplexB_S1max_le_TSD0 hΩ hb G _, S2max_le G,
    projKcMax_mem_domL G,
    fun u hu => d1_mem_S2max G (TSDS_le_ker hΩ hb) u hu,
    fun ρ hρ => adj1_mem_S1max G ρ hρ,
    fun S1' S2' _ _ h1 h2 hPD hd1 hd1s =>
      le_max_of_prop_4_17_hyps G (TSDS_le_ker hΩ hb) h1 h2 hPD hd1 hd1s,
    constS_mem_TSDS hΩ hb, symComplexB_constS_not_mem_S1max hΩ hb G hne _,
    betaT_mem_TSDT hΩ hb, symComplexB_betaT_not_mem_S2max hΩ hb G hne _,
    symComplexB_constT_mem_S2max hΩ hb G, constT_ne_zero hΩ hb hne,
    symComplexB_not_finiteDimensional_S2max hΩ hb G hne,
    fun T E₀ B₀ hD hE₀ hB₀ => ?_⟩
  obtain ⟨U, hU, huniq, hK, hred⟩ := prop_4_17_max_unconditional (symComplexB hΩ hb)
    (TSDS_le_ker hΩ hb) T hD hE₀ hB₀
  exact ⟨U, hU, huniq, fun t ht => Kc_mono (S1max_le G) (S2max_le G) (hK t ht), hred⟩

end Feec.BoundedSym
