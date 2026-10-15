module

public import Feec.Ch4.BoundedDomainExt

/-!
# Salvaging Prop 4.17 on bounded domains: the obstruction space and the necessary condition

On a bounded open `Ω ⊆ ℝ³`, `Feec.Ch4.BoundedDomain` shows that the projection hypothesis of
thesis Prop 4.17 ([QuennevilleBelair2015, §4.10]) is false and that TSD propagation fails for the
datum `(0, 0, β)`. The engine is that every field of `Z := L²(TSD) ∩ H̊(curl, M)` has zero mean.
This file identifies the obstruction precisely, and turns it into a necessary condition for
propagation that applies to every datum and to every complex with the electric boundary condition.

## The mathematics

1. *Generalized zero mean* (`sum_integral_mul_pd_eq_zero`): for `B ∈ Z` and every `C¹` vector
   field `φ` on `ℝ³` (no boundary condition), `Σ_{jk} ∫_Ω B_{jk} ∂_k φ_j = 0`; weakly,
   `B n = 0` on `∂Ω`. Proof: `C = curl B` is symmetric (`curl_symm_of_mem_TSD`); testing the graph
   closure against the skew field `skewOf φ` gives `0 = ⟪C, skewOf φ⟫ = ⟪B, curl skewOf φ⟫`, and
   `curl (skewOf φ)_{jk} = δ_{jk} div φ - ∂_j φ_k` (`curlM_skewOf`); the `δ` term dies by
   `tr B = 0`, and symmetry of `B` gives the claim. The linear fields `φ = x_a e_b` recover
   `integral_eq_zero_of_mem_TSD_of_mem_HcurlZero`.
2. *The space `L²(TSD₀)`* (`TSD0`): TSD fields orthogonal to every `∇φ`, `φ ∈ C¹(ℝ³; ℝ³)`
   (for Lipschitz `Ω`, where `C¹(ℝ³)|_Ω` is dense in `H¹(Ω)`, this is `L²(TSD) ∩ H̊(div, M)`,
   i.e. `B n = 0` on `∂Ω`; the identification is not used). It is closed (`isClosed_TSD0`) and
   contains `Z` (`mem_TSD0_of_mem_HcurlZero`), hence its closure
   (`closure_TSD_inter_HcurlZero_subset`); that closure even has infinite codimension in
   `L²(TSD)` (`not_finiteDimensional_orth_closure_TSD_inter_HcurlZero`,
   `not_TSD_le_span_closure_sup_finiteDimensional` in `Feec.Ch4.BoundedSalvageDim`).
3. *The obstruction* `obstr = L²(TSD) ⊓ TSD₀ᗮ`, the orthogonal complement of `TSD₀` in `L²(TSD)`
   (`TSD0_sup_obstr`). Every gradient field `∇φ`, `φ ∈ C¹`, is orthogonal to `TSD₀`
   (`gradField_mem_orth`); in particular the constants (`constField_mem_orth`) and every Hessian
   `∇²h` of a smooth harmonic `h` lie in `obstr` (`hessL2_mem_obstr`). Each `G ∈ obstr` is at
   distance `‖G‖` from `Z` (`norm_le_norm_sub_of_mem_obstr`), so `Z` misses all of `obstr`.
4. *Necessary condition for propagation* (`adjoint_mem_TSD0_of_propagate`, the thesis' `Ė(0)`
   argument): for any Hilbert complex `H : W0 → W1 → W2` and continuous linear
   `ι : W1 → L²(Ω; ℝ³ˣ³)` with `ι D(d1) ⊆ H̊(curl, M)`, `ι S1 ⊆ L²(TSD)`: if a strong solution of
   (4.14) from `(0, E₀, B₀)` stays in `K = {0} × S1 × S2` on `[0, T]`, `T > 0`, then
   `ι (d1* B₀) ∈ TSD₀`. (`E(t) ∈ Z` for `t ∈ [0, T]`, `TSD₀` is closed, and `Ė(0) = -d1* B₀`.)
   The refutation `not_propagate_of_adjoint` follows: if `⟪ι (d1* B₀), G⟫ ≠ 0` for some
   `G ⊥ TSD₀`, every strong solution leaves `K`. With `ι = id` this is instantiated for the
   thesis' complex (`thesisComplex_adjoint_mem_TSD0`, `thesisComplex_curl_mem_TSD0`). It applies
   to the strong-symmetry complex (4.16) of Prop 4.19 (via `ι : L²(S) → L²(M)`, using
   `H̊(curl, S) ⊆ H̊(curl, M)`) once that complex is built on `Ω`; it is **not** instantiated
   here.
5. *Any evolution in `H̊(curl, M)`* (`deriv_mem_TSD0_of_path`, `path_not_TSD_of_deriv_not_mem`):
   the same argument for a bare path `u(t) ∈ L²(TSD) ∩ H̊(curl, M)`. This is the form that would
   apply to the weak-symmetry (BGG) method of Ch. 6, whose `u` lies in `H̊(curl, M)`, once its
   bounded-domain system is built: for the datum with magnetic part `β` one expects
   `u̇(0) = -curl β`, and `curl β ∉ L²(TSD₀)` is proved (`curl_betaField_not_mem_TSD0`). The
   identity `u̇(0) = -curl β` is not proved, because `Feec.Ch6` only has abstract operators.

## Status of the analysis this file follows

Verified here: items 1-5 (for item 5, the abstract path lemma and `curl β ∉ L²(TSD₀)`); in
`Feec.Ch4.BoundedSalvageDim`, that `obstr` is infinite-dimensional (`not_finiteDimensional_obstr`,
via the harmonic functions `e^{-n x₁} cos(n x₂)`), so `closure Z` has infinite codimension in
`L²(TSD)`; in `Feec.Ch4.BoundedSalvageMax`, the corrected (maximal) Prop 4.17, whose exhibited
elements are all stationary. Not formalized:
* *Instance for Ch. 6*: the criterion of item 4 is instantiated for the thesis' complex of
  Prop 4.17 here and for the complex (4.16) of Prop 4.19 in `Feec.Ch4.BoundedSym`
  (`Feec.BoundedSym.symComplexB_mem_TSD0_of_propagate`), but not for the Ch. 6 BGG system.
* *Density* (`closure Z = TSD₀`, so `obstr` is exactly the orthogonal complement of `closure Z` in
  `L²(TSD)`): on domains star-shaped with respect to a ball it follows from zero extension,
  dilation `B(x/λ)` and mollification; for Lipschitz `Ω` it needs a Bogovskii-type right inverse
  of `div` on symmetric trace-free fields. Only `closure Z ⊆ TSD₀` is proved.
* *Exact description of `obstr`*: with trace-free Korn (closed range of `dev sym ∇`), `obstr`
  should consist of the `dev sym ∇v` with `Δv + ⅓ ∇ div v = 0`. Only the inclusion of the
  harmonic Hessians (and of the constants) is proved.
* *Interior propagation* (thesis Prop 3.6 localized): for TSD data the solution should stay TSD
  on `{(t, x) : t < dist(x, ∂Ω)}`, by a local energy estimate for the closed symmetric hyperbolic
  system satisfied by `(tr E, tr B, vskw E, vskw B)` (Lemma 3.5); constraint violations are
  created at the wall. This needs local energy estimates, which are not in the repository.
* *Other boundary conditions*: the magnetic condition (`E ∈ H(curl) ∩ H̊(div)`, `B ∈ H̊(curl)`)
  is the same problem under `(E, B) ↦ (B, -E)`; tensorial mirror conditions on a box, obtained as
  reflection-invariant subspaces of the torus, should satisfy Props 4.17/4.19. Formally the
  latter is the torus result `Feec.Torus.prop_4_17_torus` restricted to an invariant subspace;
  identifying that subspace with a box model needs an `L²(box)` model that is not built.

Correction: the closure of `L²(TSD) ∩ H̊(curl, M)` in `L²(TSD)`, claimed to be `L²(TSD)` in the
proof of [QuennevilleBelair2015, §4.10, Prop 4.17], lies in the closed subspace `L²(TSD₀)`; the
missing directions include every Hessian of a harmonic function, not only the constants.

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.10 (Prop 4.17, (4.14)), §4.11 (Prop 4.19), Ch. 6
* [Brezis2011] (Sobolev spaces)
* [AFW2010] (Hilbert complexes)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal ContDiff Matrix
open MeasureTheory Set Filter Topology

namespace Feec.BoundedDomain

variable {Ω : Set R3}

/-! ## Generalized zero mean -/

/-- **Generalized zero mean** (weakly `B n = 0` on `∂Ω`). Every `B ∈ L²(TSD) ∩ H̊(curl, M)` is
orthogonal to `∇φ` for every `C¹` vector field `φ` on `ℝ³`, with no boundary condition on `φ`:
`Σ_{jk} ∫_Ω B_{jk} ∂_k φ_j = 0`.

Proof: `C = curl B` is symmetric (`curl_symm_of_mem_TSD`), so testing the graph closure of curl
against the skew field `Ψ = skewOf φ` gives `0 = ⟪C, Ψ⟫ = ⟪B, curl Ψ⟫`; and
`(curl Ψ)_{jk} = δ_{jk} div φ - ∂_j φ_k` (`curlM_skewOf`), the `δ` term vanishing by `tr B = 0`.
This replaces the linear fields of `integral_eq_zero_of_mem_TSD_of_mem_HcurlZero` by arbitrary
`φ`. Cf. [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem sum_integral_mul_pd_eq_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {B : L2M Ω} (hB : B ∈ TSD Ω) (hB' : B ∈ HcurlZero Ω)
    {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, ContDiff ℝ 1 (φ i)) :
    ∑ jk : Ix, ∫ x, B jk x * pd jk.2 (φ jk.1) x ∂volume.restrict Ω = 0 := by
  obtain ⟨C, hC⟩ := hB'
  have hCs := curl_symm_of_mem_TSD hΩ hb hC hB
  have e := closure_curlGraph_identity hΩ hb hC (Ψ := skewOf φ) (contDiff_skewOf hφ)
  rw [sum_integral_mul_skewOf_eq_zero hCs] at e
  simp only [curlM_skewOf (fun i => (hφ i).differentiable one_ne_zero), mul_sub] at e
  set d : R3 → ℝ := fun x => ∑ m, pd m (φ m) x
  have hdm : MemLp d 2 (volume.restrict Ω) :=
    memLp_of_continuous hΩ hb (continuous_finsetSum _ fun m _ => continuous_pd (hφ m) m)
  have hpm : ∀ j k, MemLp (pd j (φ k)) 2 (volume.restrict Ω) := fun j k =>
    memLp_of_continuous hΩ hb (continuous_pd (hφ k) j)
  rw [Finset.sum_congr rfl fun jk _ => integral_sub
    (integrable_mul _ (by split_ifs; exacts [hdm, MemLp.zero])) (integrable_mul _ (hpm _ _))]
    at e
  rw [Finset.sum_sub_distrib] at e
  have h1 : ∑ jk : Ix, ∫ x, B jk x * (if jk.1 = jk.2 then d x else 0) ∂volume.restrict Ω = 0 := by
    simp only [mul_ite, mul_zero, integral_ite_zero, Fintype.sum_prod_type, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    simp only [fun f : L2 Ω => integral_mul_eq_inner f hdm, ← sum_inner, hB.2.1, inner_zero_left]
  rw [h1, zero_sub] at e
  rw [eq_comm, neg_eq_zero] at e
  rw [← e]
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun jk => ?_
  obtain ⟨j, k⟩ := jk
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [hB.1 j k]

/-! ## Gradient fields and the space `L²(TSD₀)` -/

/-- The `L²` class of the gradient field `(∇φ)_{ij} = ∂_j φ_i` of a `C¹` vector field. -/
def gradField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : Fin 3 → R3 → ℝ}
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) : L2M Ω :=
  smoothField hΩ hb (gradM φ) fun ij => continuous_pd (hφ ij.1) ij.2

/-- `⟪B, ∇φ⟫ = Σ_{jk} ∫_Ω B_{jk} ∂_k φ_j`. -/
theorem inner_gradField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : Fin 3 → R3 → ℝ}
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) (B : L2M Ω) :
    ⟪B, gradField hΩ hb hφ⟫ = ∑ jk : Ix, ∫ x, B jk x * pd jk.2 (φ jk.1) x ∂volume.restrict Ω :=
  inner_smoothField hΩ hb _ _ B

variable (Ω) in
/-- `L²(TSD₀)`: TSD fields orthogonal to the gradient `∇φ` of every `C¹` vector field `φ` on
`ℝ³` (no boundary condition on `φ`); weakly, `B n = 0` on `∂Ω`. For Lipschitz `Ω` this is
`L²(TSD) ∩ H̊(div, M)`; for a general bounded open `Ω` the two may differ, and the identification
is not used. -/
def TSD0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : Submodule ℝ (L2M Ω) where
  carrier := {B | B ∈ TSD Ω ∧ ∀ (φ : Fin 3 → R3 → ℝ) (hφ : ∀ i, ContDiff ℝ 1 (φ i)),
    ⟪B, gradField hΩ hb hφ⟫ = 0}
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => inner_zero_left _⟩
  add_mem' := by
    rintro B B' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨Submodule.add_mem _ h1 h1', fun φ hφ => by rw [inner_add_left, h2, h2', add_zero]⟩
  smul_mem' := by
    rintro c B ⟨h1, h2⟩
    exact ⟨Submodule.smul_mem _ c h1, fun φ hφ => by rw [real_inner_smul_left, h2, mul_zero]⟩

/-- Membership in `L²(TSD₀)`, in integral form. -/
theorem mem_TSD0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2M Ω} :
    B ∈ TSD0 Ω hΩ hb ↔ B ∈ TSD Ω ∧ ∀ φ : Fin 3 → R3 → ℝ, (∀ i, ContDiff ℝ 1 (φ i)) →
      ∑ jk : Ix, ∫ x, B jk x * pd jk.2 (φ jk.1) x ∂volume.restrict Ω = 0 := by
  refine and_congr Iff.rfl (forall_congr' fun φ => ?_)
  exact ⟨fun h hφ => (inner_gradField hΩ hb hφ B).symm.trans (h hφ),
    fun h hφ => (inner_gradField hΩ hb hφ B).trans (h hφ)⟩

/-- `L²(TSD₀) ⊆ L²(TSD)`. -/
theorem TSD0_le_TSD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : TSD0 Ω hΩ hb ≤ TSD Ω :=
  fun _ h => h.1

/-- `L²(TSD₀)` is closed. -/
theorem isClosed_TSD0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    IsClosed (TSD0 Ω hΩ hb : Set (L2M Ω)) := by
  have e : (TSD0 Ω hΩ hb : Set (L2M Ω)) = (TSD Ω : Set (L2M Ω)) ∩
      ⋂ φ : Fin 3 → R3 → ℝ, ⋂ hφ : (∀ i, ContDiff ℝ 1 (φ i)),
        {B | ⟪B, gradField hΩ hb hφ⟫ = 0} := by
    ext B
    simp only [SetLike.mem_coe, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    rfl
  rw [e]
  exact isClosed_TSD.inter (isClosed_iInter fun φ => isClosed_iInter fun hφ =>
    isClosed_eq (continuous_id.inner continuous_const) continuous_const)

instance (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (TSD0 Ω hΩ hb).HasOrthogonalProjection := by
  have : CompleteSpace (TSD0 Ω hΩ hb) := (isClosed_TSD0 hΩ hb).completeSpace_coe
  infer_instance

/-- **`L²(TSD) ∩ H̊(curl, M) ⊆ L²(TSD₀)`** (`sum_integral_mul_pd_eq_zero`). -/
theorem mem_TSD0_of_mem_HcurlZero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2M Ω}
    (hB : B ∈ TSD Ω) (hB' : B ∈ HcurlZero Ω) : B ∈ TSD0 Ω hΩ hb :=
  (mem_TSD0 hΩ hb).2 ⟨hB, fun _ hφ => sum_integral_mul_pd_eq_zero hΩ hb hB hB' hφ⟩

/-- **The closure of `L²(TSD) ∩ H̊(curl, M)` lies in `L²(TSD₀)`.**

Correction: the proof of [QuennevilleBelair2015, §4.10, Prop 4.17] claims this closure is
`L²(TSD)`; it is contained in the proper closed subspace `L²(TSD₀)`. -/
theorem closure_TSD_inter_HcurlZero_subset (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    closure ((TSD Ω : Set (L2M Ω)) ∩ HcurlZero Ω) ⊆ TSD0 Ω hΩ hb :=
  closure_minimal (fun _ h => mem_TSD0_of_mem_HcurlZero hΩ hb h.1 h.2) (isClosed_TSD0 hΩ hb)

/-! ## The obstruction space -/

/-- **Gradient fields are orthogonal to `L²(TSD₀)`**: `∇φ ∈ TSD₀ᗮ` for every `C¹` field `φ`. -/
theorem gradField_mem_orth (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : Fin 3 → R3 → ℝ}
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) : gradField hΩ hb hφ ∈ (TSD0 Ω hΩ hb)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro B hB
  rw [real_inner_comm]
  exact hB.2 φ hφ

/-- Fields in `L²(TSD₀)` have zero mean (the linear fields `φ = x_b e_a`). -/
theorem integral_eq_zero_of_mem_TSD0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2M Ω}
    (hB : B ∈ TSD0 Ω hΩ hb) (a b : Fin 3) : ∫ x, B (a, b) x ∂volume.restrict Ω = 0 := by
  set φ : Fin 3 → R3 → ℝ := fun i => if i = a then (fun y : R3 => y b) else 0 with hφd
  have hφ : ∀ i, ContDiff ℝ 1 (φ i) := fun i => by
    simp only [hφd]
    split_ifs
    exacts [contDiff_apply ℝ (fun _ : Fin 3 => ℝ) b, contDiff_const]
  have hpd : ∀ k i x, pd k (φ i) x = if i = a ∧ k = b then 1 else 0 := by
    intro k i x
    by_cases hi : i = a
    · simp [hφd, hi, pd_coord]
    · simp only [hφd, hi, ite_false, false_and]
      simp [pd]
  have e := ((mem_TSD0 hΩ hb).1 hB).2 φ hφ
  simp only [hpd, mul_ite, mul_one, mul_zero] at e
  rw [Finset.sum_eq_single (a, b) (fun jk _ hjk => by
    have : ¬(jk.1 = a ∧ jk.2 = b) := fun h => hjk (Prod.ext h.1 h.2)
    simp [this]) (by simp)] at e
  simpa using e

/-- **Constant fields are orthogonal to `L²(TSD₀)`.** -/
theorem constField_mem_orth (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) : constField hΩ hb A ∈ (TSD0 Ω hΩ hb)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro B hB
  rw [real_inner_comm, inner_constField]
  exact Finset.sum_eq_zero fun ij _ => by rw [integral_eq_zero_of_mem_TSD0 hΩ hb hB, mul_zero]

variable (Ω) in
/-- **The obstruction space** `obstr = L²(TSD) ⊓ L²(TSD₀)ᗮ`, the orthogonal complement of
`L²(TSD₀)` inside `L²(TSD)`. It is orthogonal to `L²(TSD) ∩ H̊(curl, M)`
(`inner_eq_zero_of_mem_obstr`), hence contained in the orthogonal complement of its closure in
`L²(TSD)`; equality is the density statement `closure (L²(TSD) ∩ H̊(curl, M)) = L²(TSD₀)`, not
formalized. -/
def obstr (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : Submodule ℝ (L2M Ω) :=
  TSD Ω ⊓ (TSD0 Ω hΩ hb)ᗮ

/-- `L²(TSD) = L²(TSD₀) ⊕ obstr` (orthogonal sum). -/
theorem TSD0_sup_obstr (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    TSD0 Ω hΩ hb ⊔ obstr Ω hΩ hb = TSD Ω := by
  refine le_antisymm (sup_le (TSD0_le_TSD hΩ hb) inf_le_left) fun B hB => ?_
  have h1 := (TSD0 Ω hΩ hb).starProjection_apply_mem B
  have h2 := (TSD0 Ω hΩ hb).sub_starProjection_mem_orthogonal B
  have e : B = (TSD0 Ω hΩ hb).starProjection B + (B - (TSD0 Ω hΩ hb).starProjection B) := by
    abel
  rw [e]
  exact Submodule.add_mem_sup h1 ⟨Submodule.sub_mem _ hB (TSD0_le_TSD hΩ hb h1), h2⟩

/-- **Each `G ∈ obstr` is at distance `‖G‖` from `L²(TSD) ∩ H̊(curl, M)`**: `‖G‖ ≤ ‖G - Z‖` for
every `Z ∈ L²(TSD) ∩ H̊(curl, M)` (and for every `Z ∈ L²(TSD₀)`). So no nonzero element of
`obstr` is a limit of TSD fields in `H̊(curl, M)`. -/
theorem norm_le_norm_sub_of_mem_obstr (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {G Z : L2M Ω} (hG : G ∈ obstr Ω hΩ hb) (hZ : Z ∈ TSD0 Ω hΩ hb) : ‖G‖ ≤ ‖G - Z‖ := by
  have h0 : ⟪G, Z⟫ = 0 := (Submodule.mem_orthogonal' _ _).1 hG.2 Z hZ
  have e : ‖G - Z‖ ^ 2 = ‖G‖ ^ 2 + ‖Z‖ ^ 2 := by
    rw [@norm_sub_sq_real, h0]; ring
  nlinarith [norm_nonneg G, norm_nonneg (G - Z), sq_nonneg ‖Z‖]

/-- `obstr` is orthogonal to `L²(TSD) ∩ H̊(curl, M)`. -/
theorem inner_eq_zero_of_mem_obstr (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {G Z : L2M Ω} (hG : G ∈ obstr Ω hΩ hb) (hZ : Z ∈ TSD Ω) (hZ' : Z ∈ HcurlZero Ω) :
    ⟪G, Z⟫ = 0 :=
  (Submodule.mem_orthogonal' _ _).1 hG.2 Z (mem_TSD0_of_mem_HcurlZero hΩ hb hZ hZ')

/-- Constant symmetric trace-free fields lie in `obstr`. -/
theorem constField_mem_obstr (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = A) (htrA : A.trace = 0) :
    constField hΩ hb A ∈ obstr Ω hΩ hb :=
  ⟨constField_mem_TSD hΩ hb hA htrA, constField_mem_orth hΩ hb A⟩

/-- The Hessian `(∇²h)_{ij} = ∂_j ∂_i h`. -/
def hessField (h : R3 → ℝ) : Ix → R3 → ℝ := fun ij => pd ij.2 (pd ij.1 h)

/-- The Hessian is the gradient of `∇h`. -/
theorem hessField_eq_gradM (h : R3 → ℝ) : hessField h = gradM fun i => pd i h := rfl

theorem contDiff_pd_top {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (k : Fin 3) :
    ContDiff ℝ ∞ (pd k f) := by
  unfold pd
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_hessField {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) (ij : Ix) :
    ContDiff ℝ ∞ (hessField h ij) :=
  contDiff_pd_top (contDiff_pd_top hh _) _

theorem contDiff_one_of_top {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 f :=
  hf.of_le (by simp)

/-- The `L²` class of the Hessian of a smooth function. -/
def hessL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) :
    L2M Ω :=
  smoothField hΩ hb (hessField h) fun ij => (contDiff_hessField hh ij).continuous

theorem hessL2_eq_gradField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {h : R3 → ℝ}
    (hh : ContDiff ℝ ∞ h) :
    hessL2 hΩ hb hh = gradField hΩ hb (φ := fun i => pd i h)
      (fun i => contDiff_one_of_top (contDiff_pd_top hh i)) := rfl

/-- The Laplacian `Δh = Σ_i ∂_i ∂_i h`. -/
def lap (h : R3 → ℝ) (x : R3) : ℝ := ∑ i, pd i (pd i h) x

theorem pd_sum {ι : Type*} (s : Finset ι) {f : ι → R3 → ℝ} (hf : ∀ i ∈ s, Differentiable ℝ (f i))
    (k : Fin 3) (x : R3) : pd k (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, pd k (f i) x := by
  unfold pd
  rw [fderiv_fun_sum fun i hi => (hf i hi).differentiableAt]
  simp

/-- **Hessians of smooth harmonic functions lie in `L²(TSD)`**: `∇²h` is symmetric (Schwarz),
trace-free (`Δh = 0`) and divergence-free (`div ∇²h = ∇Δh = 0`). -/
theorem hessL2_mem_TSD (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {h : R3 → ℝ}
    (hh : ContDiff ℝ ∞ h) (hΔ : ∀ x, lap h x = 0) : hessL2 hΩ hb hh ∈ TSD Ω := by
  have h2 : ContDiff ℝ 2 h := hh.of_le (by simp)
  refine smoothField_mem_TSD hΩ hb (fun ij => contDiff_one_of_top (contDiff_hessField hh ij))
    (fun i j x => ?_) (fun x => hΔ x) (fun i x => ?_)
  · exact (pd_pd_comm h2 i j x).symm
  · simp only [hessField]
    have e : ∀ j, pd j (pd j (pd i h)) = pd i (pd j (pd j h)) := fun j => by
      have e1 : pd j (pd i h) = pd i (pd j h) := funext fun z => pd_pd_comm h2 j i z
      have h3 : ContDiff ℝ 2 (pd j h) := (contDiff_pd_top hh j).of_le (by simp)
      rw [e1]
      exact funext fun y => pd_pd_comm h3 j i y
    simp only [fun j => congrFun (e j) x]
    have hl : (fun y => ∑ j, pd j (pd j h) y) = lap h := rfl
    rw [← pd_sum _ (fun j _ => ((contDiff_pd_top (contDiff_pd_top hh j) j).differentiable
      (by simp))), hl]
    have : lap h = fun _ => 0 := funext hΔ
    rw [this]
    simp [pd]

/-- **Hessians of smooth harmonic functions lie in the obstruction space**: they are TSD and,
being gradients, orthogonal to `L²(TSD₀)`. They span an infinite-dimensional subspace
(`not_finiteDimensional_obstr` in `Feec.Ch4.BoundedSalvageDim`, via `e^{-n x₁} cos(n x₂)`). -/
theorem hessL2_mem_obstr (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {h : R3 → ℝ}
    (hh : ContDiff ℝ ∞ h) (hΔ : ∀ x, lap h x = 0) : hessL2 hΩ hb hh ∈ obstr Ω hΩ hb :=
  ⟨hessL2_mem_TSD hΩ hb hh hΔ, by rw [hessL2_eq_gradField]; exact gradField_mem_orth hΩ hb _⟩

/-- `diag(1, -1, 0) ∉ L²(TSD₀)` on a nonempty `Ω`. -/
theorem constField_diagA_not_mem_TSD0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : constField hΩ hb diagA ∉ TSD0 Ω hΩ hb := by
  intro h
  have h0 := integral_eq_zero_of_mem_TSD0 hΩ hb h 0 0
  rw [integral_constField] at h0
  have hpos : 0 < volume.real Ω := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hΩ.measure_pos volume hne).ne' hb.measure_lt_top.ne
  simp [diagA] at h0
  exact hpos.ne' h0

/-! ## A necessary condition for propagation, for every datum and every complex -/

section Propagation

open Feec.HilbertComplex2 Feec.Constraints LinearPMap

/-- The right derivative at `0` of a path that stays in a closed subspace on `[0, T]`, `T > 0`,
lies in the subspace (limit of difference quotients). -/
theorem mem_of_hasDerivWithinAt_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {C : Submodule ℝ F} (hC : IsClosed (C : Set F)) {f : ℝ → F} {f' : F} {T : ℝ} (hT : 0 < T)
    (hf : HasDerivWithinAt f f' (Icc 0 T) 0) (hmem : ∀ t ∈ Icc 0 T, f t ∈ C) : f' ∈ C := by
  have ht := hasDerivWithinAt_iff_tendsto_slope.1 hf
  have hsub : Ioo 0 T ⊆ Icc 0 T \ {0} := fun t ht =>
    ⟨Ioo_subset_Icc_self ht, ne_of_gt ht.1⟩
  have hne : (𝓝[Icc 0 T \ {0}] (0 : ℝ)).NeBot :=
    neBot_of_le (f := 𝓝[Ioo 0 T] (0 : ℝ)) (hf := left_nhdsWithin_Ioo_neBot hT)
      (nhdsWithin_mono _ hsub)
  refine hC.mem_of_tendsto ht (eventually_nhdsWithin_of_forall fun t ht' => ?_)
  rw [slope_def_module]
  exact C.smul_mem _ (C.sub_mem (hmem t ht'.1) (hmem 0 ⟨le_rfl, hT.le⟩))

/-- **The `Ė(0)` argument for any evolution in `H̊(curl, M)`** (no complex, no equation): if a
path `u` of matrix fields stays in `L²(TSD) ∩ H̊(curl, M)` on `[0, T]`, `T > 0`, and has right
derivative `u'` at `0`, then `u' ∈ L²(TSD₀)`.

This is the form that would apply to the weak-symmetry (BGG) method of Ch. 6 ((6.2)/(6.5)),
whose electric unknown `u` also lies in `H̊(curl, M)`, once that system is built on `Ω`: for the
datum with magnetic part `β`, the `u`-equation should give `u̇(0) = -curl β = diag(1, -1, 0)`,
which is not in `L²(TSD₀)` (`curl_betaField_not_mem_TSD0`), so `u(t)` would leave `L²(TSD)`
immediately. Only the last step is proved: the Ch. 6 data in `Feec.Ch6` are abstract bounded
operators, so the bounded-domain BGG system and its `u̇(0)` are not formalized. -/
theorem deriv_mem_TSD0_of_path (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {u : ℝ → L2M Ω}
    {u' : L2M Ω} {T : ℝ} (hT : 0 < T) (hu : HasDerivWithinAt u u' (Icc 0 T) 0)
    (hK : ∀ t ∈ Icc 0 T, u t ∈ TSD Ω ∧ u t ∈ HcurlZero Ω) : u' ∈ TSD0 Ω hΩ hb :=
  mem_of_hasDerivWithinAt_Icc (isClosed_TSD0 hΩ hb) hT hu fun t ht =>
    mem_TSD0_of_mem_HcurlZero hΩ hb (hK t ht).1 (hK t ht).2

/-- Contrapositive of `deriv_mem_TSD0_of_path`: a path in `H̊(curl, M)` whose initial velocity is
not in `L²(TSD₀)` leaves `L²(TSD)` on every `[0, T]`, `T > 0`. -/
theorem path_not_TSD_of_deriv_not_mem (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {u : ℝ → L2M Ω} {u' : L2M Ω} {T : ℝ} (hT : 0 < T) (hu : HasDerivWithinAt u u' (Icc 0 T) 0)
    (hcurl : ∀ t ∈ Icc 0 T, u t ∈ HcurlZero Ω) (hu' : u' ∉ TSD0 Ω hΩ hb) :
    ∃ t ∈ Icc 0 T, u t ∉ TSD Ω := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  exact hu' (deriv_mem_TSD0_of_path hΩ hb hT hu fun t ht => ⟨h t ht, hcurl t ht⟩)

variable {W0 W1 W2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]

/-- **Necessary condition for constraint propagation** (the `Ė(0)` argument; any datum, any
complex with the electric boundary condition). Let `H : W0 → W1 → W2` be a Hilbert complex and
`ι : W1 → L²(Ω; ℝ³ˣ³)` continuous linear with `ι D(d1) ⊆ H̊(curl, M)` and `ι S1 ⊆ L²(TSD)`. If a
strong solution of (4.14) from `(0, E₀, B₀)` stays in `K = {0} × S1 × S2` on `[0, T]`, `T > 0`,
then `ι (d1* B₀) ∈ L²(TSD₀)`.

Proof: `ι E(t) ∈ L²(TSD) ∩ H̊(curl, M) ⊆ L²(TSD₀)` for `t ∈ [0, T]`
(`mem_TSD0_of_mem_HcurlZero`); `L²(TSD₀)` is closed, so it contains `ι Ė(0) = -ι (d1* B₀)`.

Instantiated for `ι = id` and the thesis' complex `H̊¹(V) → H̊(curl, M) → L²(M)` of Prop 4.17
(`thesisComplex_adjoint_mem_TSD0`). It applies, once those complexes are built on `Ω`, to the
strong-symmetry complex (4.16) of Prop 4.19 via the inclusion `L²(S) → L²(M)`
(`H̊(curl, S) ⊆ H̊(curl, M)`); neither that instance nor the Ch. 6 weak-symmetry system is
formalized here.

Correction: the conclusion of [QuennevilleBelair2015, §4.10, Prop 4.17] (and of Prop 4.19, §4.11)
requires `d1* B₀ ∈ L²(TSD₀)` on bounded domains; TSD data `B₀` without this property leave `K`. -/
theorem adjoint_mem_TSD0_of_propagate (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (H : HilbertComplex2 W0 W1 W2) (ι : W1 →L[ℝ] L2M Ω)
    (hι : ∀ u ∈ H.d1.domain, ι u ∈ HcurlZero Ω) {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2}
    (hS1 : ∀ u ∈ S1, ι u ∈ TSD Ω) {E₀ : W1} {B₀ : W2} {T : ℝ} (hT : 0 < T)
    {U : ℝ → Tot W0 W1 W2} (hU : IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0 U)
    (hK : ∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2) :
    ∃ h : B₀ ∈ H.d1†.domain, ι (H.d1† ⟨B₀, h⟩) ∈ TSD0 Ω hΩ hb := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hD0 := (Feec.Constraints.mem_domL H).1 (hU.mem 0 h0)
  have hB₀ : B₀ ∈ H.d1†.domain := by simpa [hU.init, tot_ini] using hD0.2.2
  refine ⟨hB₀, ?_⟩
  let Φ : Tot W0 W1 W2 →L[ℝ] L2M Ω := ι.comp
    ((ContinuousLinearMap.fst ℝ W1 W2).comp ((ContinuousLinearMap.snd ℝ W0 _).comp
      (totL (W0 := W0) (W1 := W1) (W2 := W2)).toContinuousLinearMap))
  have hΦ : ∀ y, Φ y = ι (tot W0 W1 W2 y).2.1 := fun y => rfl
  have hmem : ∀ t ∈ Icc 0 T, (Φ ∘ U) t ∈ TSD0 Ω hΩ hb := by
    intro t ht
    have hD := (Feec.Constraints.mem_domL H).1 (hU.mem t ht)
    have hE : (tot W0 W1 W2 (U t)).2.1 ∈ H.d1.domain := (Submodule.mem_inf.1 hD.2.1).1
    simp only [Function.comp_apply, hΦ]
    exact mem_TSD0_of_mem_HcurlZero hΩ hb (hS1 _ ((mem_Kc).1 (hK t ht)).2.1) (hι _ hE)
  have hd := Φ.hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) (hU.deriv 0 h0)
  have hm := mem_of_hasDerivWithinAt_Icc (isClosed_TSD0 hΩ hb) hT hd hmem
  have hp0 : H.pr0 ⟨U 0, hU.mem 0 h0⟩ = 0 := Subtype.ext (by simp [hU.init])
  have hp2 : H.prV2s ⟨U 0, hU.mem 0 h0⟩ = ⟨B₀, hB₀⟩ := Subtype.ext (by simp [hU.init])
  rw [Pi.zero_apply, add_zero, LinearPMap.neg_apply, _root_.map_neg, hΦ, tot_waveOp] at hm
  simp only at hm
  rw [hp0, hp2, LinearPMap.map_zero, zero_add] at hm
  simpa using hm

/-- **Refutation criterion** (instantiated here for Prop 4.17; it applies to Prop 4.19 once
complex (4.16) is built with `ι D(d1) ⊆ H̊(curl, M)`): in
the setting of `adjoint_mem_TSD0_of_propagate`, if `⟪ι (d1* B₀), G⟫ ≠ 0` for some `G ⊥ L²(TSD₀)`
(e.g. a constant field or a gradient `∇φ`, `φ ∈ C¹`), then every strong solution of (4.14) from
`(0, E₀, B₀)` leaves `K = {0} × S1 × S2` on every `[0, T]`, `T > 0`.

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17 and §4.11, Prop 4.19]. -/
theorem not_propagate_of_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (H : HilbertComplex2 W0 W1 W2) (ι : W1 →L[ℝ] L2M Ω)
    (hι : ∀ u ∈ H.d1.domain, ι u ∈ HcurlZero Ω) {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2}
    (hS1 : ∀ u ∈ S1, ι u ∈ TSD Ω) {E₀ : W1} {B₀ : W2} (hB₀ : B₀ ∈ H.d1†.domain)
    {G : L2M Ω} (hG : G ∈ (TSD0 Ω hΩ hb)ᗮ) (hc : ⟪ι (H.d1† ⟨B₀, hB₀⟩), G⟫ ≠ 0) :
    ∀ T > 0, ∀ U : ℝ → Tot W0 W1 W2, IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0 U →
      ∃ t ∈ Icc 0 T, U t ∉ Kc W0 S1 S2 := by
  intro T hT U hU
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  obtain ⟨h, hm⟩ := adjoint_mem_TSD0_of_propagate hΩ hb H ι hι hS1 hT hU hall
  exact hc (by rw [real_inner_comm]; exact (Submodule.mem_orthogonal' _ _).1 hG _ hm)

/-- **The necessary condition for the thesis' complex** `H̊¹(V) → H̊(curl, M) → L²(M)`: if some
strong solution of (4.14) from `(0, E₀, B₀)` stays in `K = {0} × L²(TSD) × S2` on `[0, T]`,
`T > 0`, then `B₀ ∈ H(curl, M)` and `curl B₀ = d1* B₀ ∈ L²(TSD₀)` (zero mean, weakly
`(curl B₀) n = 0` on `∂Ω`).

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem thesisComplex_adjoint_mem_TSD0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {S2 : Submodule ℝ (L2M Ω)} {E₀ B₀ : L2M Ω} {T : ℝ} (hT : 0 < T)
    {U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω)}
    (hU : IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) E₀ B₀) 0 U)
    (hK : ∀ t ∈ Icc 0 T, U t ∈ Kc (L2V Ω) (TSD Ω) S2) :
    ∃ h : B₀ ∈ (thesisComplex hΩ hb).d1†.domain,
      (thesisComplex hΩ hb).d1† ⟨B₀, h⟩ ∈ TSD0 Ω hΩ hb := by
  simpa using adjoint_mem_TSD0_of_propagate hΩ hb (thesisComplex hΩ hb)
    (ContinuousLinearMap.id ℝ _) (fun u hu => mem_domain_curlClosure.1 hu)
    (S1 := TSD Ω) (fun u hu => hu) hT hU hK

/-- **Smooth magnetic data must have `curl B₀ ∈ L²(TSD₀)`**: for a `C¹` field `Ψ` on `ℝ³` and
any `E₀`, if a strong solution of (4.14) for the thesis' complex from `(0, E₀, Ψ)` stays in
`{0} × L²(TSD) × S2` on `[0, T]`, `T > 0`, then `curl Ψ ∈ L²(TSD₀)`: in particular
`∫_Ω curl Ψ = 0`. For `Ψ = β` (`curl β = -diag(1, -1, 0)`) this fails
(`thesisComplex_betaField_not_propagate`). -/
theorem thesisComplex_curl_mem_TSD0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {S2 : Submodule ℝ (L2M Ω)} {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) {E₀ : L2M Ω}
    {T : ℝ} (hT : 0 < T) {U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω)}
    (hU : IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T
      (ini (L2V Ω) E₀ (smoothField hΩ hb Ψ fun ij => (hΨ ij).continuous)) 0 U)
    (hK : ∀ t ∈ Icc 0 T, U t ∈ Kc (L2V Ω) (TSD Ω) S2) :
    smoothField hΩ hb (curlM Ψ) (continuous_curlM hΨ) ∈ TSD0 Ω hΩ hb := by
  obtain ⟨h, hm⟩ := thesisComplex_adjoint_mem_TSD0 hΩ hb hT hU hK
  obtain ⟨h', e⟩ := smoothField_mem_adjoint hΩ hb (thesisComplex hΩ hb)
    (mem_closure_curlClosure hΩ hb) hΨ
  rwa [show (⟨_, h⟩ : (thesisComplex hΩ hb).d1†.domain) = ⟨_, h'⟩ from rfl, e] at hm

/-- `curl β = -diag(1, -1, 0)` as `L²` fields. -/
theorem smoothField_curlM_betaField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    smoothField hΩ hb (curlM betaField) (continuous_curlM fun ij =>
      contDiff_one_of_top (contDiff_betaField ij)) = -constField hΩ hb diagA := by
  refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
  filter_upwards [coeFn_smoothField hΩ hb (curlM betaField) (continuous_curlM fun ij =>
    contDiff_one_of_top (contDiff_betaField ij)) ij,
    Lp.coeFn_neg (constField hΩ hb diagA ij), coeFn_constField hΩ hb diagA ij]
    with x h1 h2 h3
  simp only [PiLp.neg_apply] at h2 ⊢
  rw [h1, h2, Pi.neg_apply, h3, curlM_betaField]

/-- `curl β ∉ L²(TSD₀)`: it is the constant `-diag(1, -1, 0)`, which has nonzero mean. -/
theorem curl_betaField_not_mem_TSD0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    smoothField hΩ hb (curlM betaField) (continuous_curlM fun ij =>
      contDiff_one_of_top (contDiff_betaField ij)) ∉ TSD0 Ω hΩ hb := by
  rw [smoothField_curlM_betaField]
  intro hm
  exact constField_diagA_not_mem_TSD0 hΩ hb hne (by simpa using (TSD0 Ω hΩ hb).neg_mem hm)

/-- `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)` violates the necessary condition: from `(0, E₀, β)`, for **any**
`E₀` and any `S2`, every strong solution of (4.14) for the thesis' complex leaves
`{0} × L²(TSD) × S2` on every `[0, T]`, `T > 0`. -/
theorem thesisComplex_betaField_not_propagate (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S2 : Submodule ℝ (L2M Ω)) (E₀ : L2M Ω) {T : ℝ} (hT : 0 < T)
    (U : ℝ → Tot (L2V Ω) (L2M Ω) (L2M Ω))
    (hU : IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) E₀
      (smoothField hΩ hb betaField fun ij => (contDiff_one_of_top (contDiff_betaField ij)).continuous))
      0 U) :
    ∃ t ∈ Icc 0 T, U t ∉ Kc (L2V Ω) (TSD Ω) S2 := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  exact curl_betaField_not_mem_TSD0 hΩ hb hne (thesisComplex_curl_mem_TSD0 hΩ hb
    (fun ij => contDiff_one_of_top (contDiff_betaField ij)) hT hU hall)

end Propagation

end Feec.BoundedDomain
