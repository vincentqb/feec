module

public import Feec.Ch4.BoundedSalvage
public import Feec.Ch4.StoneApplications

/-!
# The maximal propagating constraint space: a corrected Prop 4.17

Thesis Props 4.17/4.19 ([QuennevilleBelair2015, §4.10–4.11]) assume that `P_K D(L) ⊆ D(L)` for
`K = {0} × L²(TSD) × L²(TSD)`. On bounded domains this is false and propagation fails
(`Feec.Ch4.BoundedDomain`, `Feec.Ch4.BoundedSalvage`). This file replaces `K` by the largest
subspace on which the thesis' argument works, and proves Prop 4.17 there, unconditionally.

## The construction (abstract)

For an orthogonal group `S` (generator `-L`) and a closed subspace `K`, let
`K* = {x | S t x ∈ K for all t ∈ ℝ}` (`Kmax`). Then:
* `K*` is closed, `S`-invariant, hence reducing: `P_{K*} D(L) ⊆ D(L)`, `L P_{K*} = P_{K*} L`
  (`Feec.Constraints.reducing_of_invariant`), and `D(L) ∩ K*` is dense in `K*`
  (`mem_closure_domain_inter_Kmax`);
* for `K = {0} × S1 × S2` and the Hodge wave (4.14), `K*` is again a product
  `{0} × S1* × S2*` (`Kmax_eq_Kc`), because the time reversal `R(σ, E, B) = (-σ, E, -B)` satisfies
  `R S t = S (-t) R` (`revT_S`) and so preserves `K*`;
* `(S1*, S2*)` satisfies every hypothesis of `Feec.Constraints.prop_4_17`, including the
  projection hypothesis (`projKcMax_mem_domL`, `d1_mem_S2max`, `adj1_mem_S1max`), so Prop 4.17
  holds for `{0} × S1* × S2*` (`prop_4_17_max`, with existence `prop_4_17_max_unconditional`);
* it is the **largest** such space: every closed `S1' ≤ S1`, `S2' ≤ S2` satisfying the hypotheses
  of `prop_4_17` lies in `(S1*, S2*)` (`le_max_of_prop_4_17_hyps`);
* a datum `x ∈ D(L) ∩ K` lies in `K*` iff the solutions from `x` and from `R x` both stay in `K`
  for all `t ≥ 0` (`mem_Kmax_iff_propagate`); stationary data (`L x = 0`) always do
  (`mem_Kmax_of_apply_eq_zero`, `mem_S2max_of_adj1_eq_zero`).

Correction: the research notes behind this file claim that `x ∈ D(L) ∩ K` propagates for all
`t ≥ 0` iff `x ∈ K*`. Forward propagation of `x` alone is weaker. Example (not formalized): the
complex `0 → H¹(ℝ) --d/dx--> L²(ℝ)`, `S1 = S2 = L²(0, ∞)`; (4.14) is `Ė = B'`, `Ḃ = E'`, so
`E - B` moves right and `E + B` moves left. The datum `(0, f, -f)` with `supp f ⊆ (1, 2)` stays in
`K` for `t ≥ 0` but not for `t < 0`, and `R` of it, `(0, f, f)`, leaves `K` for `t > 0`.
On the box with the thesis' boundary conditions (parity model) the gap closes: forward
invariance alone already forces `x ∈ K*` (`Feec.Box.forward_iff_mem_Kmax`,
`Feec.Box.thesisBox_forward_iff` in `Feec.Ch4.BoxForward`), and so it does on every open cube
for `Feec.BoundedDomain.thesisComplex` (`Feec.BoxIdent.openCube_forward_iff`). Abstractly,
forward invariance of a closed `K` implies `x ∈ K*` whenever the group has pure point spectrum
(`Feec.Constraints.mem_Kmax_of_forward` in `Feec.Ch4.BoundedKstar`); the example above has
continuous spectrum.

## Bounded domains

For the thesis' complex `H̊¹(V) → H̊(curl, M) → L²(M)` on a nonempty bounded open `Ω` (and any
complex with `ι D(d1) ⊆ H̊(curl, M)`):
* `S1* ⊆ L²(TSD₀)` (`S1max_le_TSD0`) and `d1*` maps `S2* ∩ D(d1*)` into `L²(TSD₀)`
  (`adj1_mem_TSD0_of_mem_S2max`), using `Feec.BoundedDomain.mem_TSD0_of_mem_HcurlZero`;
* `S2*` contains every curl-free field of `L²(TSD)` as a stationary datum
  (`thesisComplex_mem_S2max_of_weakCurl_eq_zero`), e.g. the Hessians of smooth harmonic functions
  and the constants (`thesisComplex_hessL2_mem_S2max`, `thesisComplex_constField_mem_S2max`); this
  stationary part is infinite-dimensional
  (`Feec.BoundedDomain.thesisComplex_not_finiteDimensional_S2max` in `Feec.Ch4.BoundedSalvageDim`);
* `diag(1, -1, 0) ∈ L²(TSD)` is not in `S1*` (`thesisComplex_constField_diagA_not_mem_S1max`) and
  `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ) ∈ L²(TSD)` is not in `S2*` (`thesisComplex_betaField_not_mem_S2max`),
  so `K* ⊊ K` in both slots.

What this does and does not show: `K*` is invariant by definition, and the hypotheses of
`prop_4_17` for it follow from invariance, so the corrected Prop 4.17 is the thesis' argument run
on the largest subspace where it can work. Its content is the identification above and
maximality. Every element of `K*` exhibited here is **stationary** (`d1* B = 0`), where
propagation is trivial; no nonzero element of `S1*` and no non-stationary element of `K*` is
known. It is open whether `K*` contains any non-stationary datum on a general bounded domain;
`Feec.BoundedDomain.thesisComplex_Kmax_spectral` (in `Feec.Ch4.BoundedKstar`) reduces this, under
the hypothesis `EigenDense` (pure point spectrum, not proved for any bounded domain), to the
existence of a nonzero `u ∈ L²(TSD) ∩ H̊(curl)` with `curl* curl u = ω² u`, `ω > 0`.
On every open cube with the thesis' boundary conditions `K*` consists exactly of the stationary
data in `K` (`Feec.BoxIdent.openCube_mem_Kmax_iff'`, from the parity model
`Feec.Box.thesisBox_mem_Kmax_iff` in `Feec.Ch4.BoxThesis`).

The resulting statement (`thesisComplex_prop_4_17_max`): for every datum `(0, E₀, B₀) ∈ D(L)`
with `E₀ ∈ S1*`, `B₀ ∈ S2*`, (4.14) has a unique strong solution on `[0, T]`; it stays in
`{0} × S1* × S2* ⊆ {0} × L²(TSD) × L²(TSD)`, and `(E, B)` solves (4.15).

Identifying `S1*`, `S2*` concretely: on a cube the research notes argue that `S1* = 0` and
`S2* = L²(TSD) ∩ ker curl` (only static data propagate). This is proved in the parity model of
the box (`Feec.Box.thesisBox_mem_Kmax_iff'`: `x ∈ K*` iff `x = (0, 0, B₀)` with `B₀` TSD and
curl-free), by Fourier series on the torus rather than by spectral theory of the bounded-domain
Maxwell operator; `Feec.Ch4.BoxIdent` identifies those parity subspaces with the spaces `H̊¹`,
`H̊(curl)`, `H(curl)` of `Feec.Ch4.BoundedDomain` and transfers the result to every open cube
(`Feec.BoxIdent.openCube_mem_Kmax_iff'`). Not formalized: any concrete description of `S1*`,
`S2*` on other domains.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.4, Cor 4.5), §4.10 (Props 4.16–4.18), §4.11 (Prop 4.19)
* [Pazy1983], §1.10 (Stone's theorem, reducing subspaces)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace LinearPMap ContDiff
open Set Filter Topology

namespace Feec.Constraints

/-! ## The largest invariant subspace of a closed subspace -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : E →ₗ.[ℝ] E} (G : UnitaryGroupGenerator L)

/-- `K* = {x | S t x ∈ K for all t ∈ ℝ}`: the largest `S`-invariant subset of `K`. -/
def Kmax (K : Submodule ℝ E) : Submodule ℝ E where
  carrier := {x | ∀ t, G.S t x ∈ K}
  zero_mem' := fun t => by simp
  add_mem' := fun hx hy t => by simpa using K.add_mem (hx t) (hy t)
  smul_mem' := fun c x hx t => by simpa using K.smul_mem c (hx t)

variable {G} {K : Submodule ℝ E}

theorem mem_Kmax {x : E} : x ∈ Kmax G K ↔ ∀ t, G.S t x ∈ K := Iff.rfl

theorem Kmax_le : Kmax G K ≤ K := fun x hx => by simpa [G.map_zero] using hx 0

/-- `K*` is invariant under the whole group. -/
theorem S_mem_Kmax {x : E} (hx : x ∈ Kmax G K) (s : ℝ) : G.S s x ∈ Kmax G K := fun t => by
  have : G.S t (G.S s x) = G.S (t + s) x := by rw [G.map_add]; rfl
  rw [this]
  exact hx _

/-- `K*` contains every `S`-invariant subset of `K`. -/
theorem le_Kmax {M : Submodule ℝ E} (hM : M ≤ K) (hinv : ∀ t, ∀ x ∈ M, G.S t x ∈ M) :
    M ≤ Kmax G K := fun x hx t => hM (hinv t x hx)

theorem isClosed_of_hasOrthogonalProjection (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    IsClosed (K : Set E) := by
  rw [← Submodule.orthogonal_orthogonal K]; exact Submodule.isClosed_orthogonal _

/-- `K*` is closed if `K` is. -/
theorem isClosed_Kmax (hK : IsClosed (K : Set E)) : IsClosed (Kmax G K : Set E) := by
  have e : (Kmax G K : Set E) = ⋂ t, (G.S t) ⁻¹' K := by ext; simp [mem_Kmax]
  rw [e]
  exact isClosed_iInter fun t => hK.preimage (G.S t).continuous

instance [CompleteSpace E] [K.HasOrthogonalProjection] : (Kmax G K).HasOrthogonalProjection := by
  have : CompleteSpace (Kmax G K) :=
    (isClosed_Kmax (isClosed_of_hasOrthogonalProjection K)).completeSpace_coe
  infer_instance

/-- A closed invariant subspace `M` with `P_M D(L) ⊆ D(L)`: `D(L) ∩ M` is dense in `M`. -/
theorem mem_closure_domain_inter_of_proj (hD : Dense (L.domain : Set E)) (M : Submodule ℝ E)
    [M.HasOrthogonalProjection] (hP : ∀ x ∈ L.domain, M.starProjection x ∈ L.domain) :
    ∀ k ∈ M, k ∈ closure ((L.domain : Set E) ∩ M) := by
  intro k hk
  have := map_mem_closure M.starProjection.continuous (hD k)
    (t := (L.domain : Set E) ∩ M) fun x hx => ⟨hP x hx, M.starProjection_apply_mem x⟩
  rwa [M.starProjection_eq_self_iff.2 hk] at this

/-- `K*` is reducing: `P_{K*} D(L) ⊆ D(L)`. -/
theorem starProjection_Kmax_mem_domain [CompleteSpace E] [K.HasOrthogonalProjection] (x : E) (hx : x ∈ L.domain) :
    (Kmax G K).starProjection x ∈ L.domain :=
  (reducing_of_invariant G (Kmax G K) (fun t _ h => S_mem_Kmax h t) ⟨x, hx⟩).1

/-- `D(L) ∩ K*` is dense in `K*`. -/
theorem mem_closure_domain_inter_Kmax [CompleteSpace E] [K.HasOrthogonalProjection]
    (hD : Dense (L.domain : Set E)) :
    ∀ k ∈ Kmax G K, k ∈ closure ((L.domain : Set E) ∩ Kmax G K) :=
  mem_closure_domain_inter_of_proj hD _ fun x hx => starProjection_Kmax_mem_domain x hx

/-- The generator maps `D(L) ∩ K*` into `K*`. -/
theorem apply_mem_Kmax [CompleteSpace E] [K.HasOrthogonalProjection] (x : L.domain) (hx : (x : E) ∈ Kmax G K) :
    L x ∈ Kmax G K := by
  obtain ⟨h, e⟩ := reducing_of_invariant G (Kmax G K) (fun t _ h => S_mem_Kmax h t) x
  have hx' : (⟨_, h⟩ : L.domain) = x := Subtype.ext ((Kmax G K).starProjection_eq_self_iff.2 hx)
  rw [hx'] at e
  rw [e]
  exact (Kmax G K).starProjection_apply_mem _

/-- Stationary points in `K` lie in `K*`: if `x ∈ D(L) ∩ K` and `L x = 0`, then `S t x = x`. -/
theorem mem_Kmax_of_apply_eq_zero (x : L.domain) (hx : (x : E) ∈ K) (h0 : L x = 0) :
    (x : E) ∈ Kmax G K := by
  intro t
  have hd : ∀ s, HasDerivAt (fun s => G.S s x) 0 s := fun s => by
    simpa [h0] using G.hasDerivAt_apply x s
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simp only [G.map_zero, one_apply_eq_self] at hc
  rw [hc]
  exact hx

end Abstract

/-! ## The Hodge wave (4.14): `K*` is a product -/

section Wave

open HilbertComplex2

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    {H : HilbertComplex2 W0 W1 W2} (G : UnitaryGroupGenerator (-H.waveOp))

/-- The domain of the Hodge wave operator is dense. -/
theorem dense_domain_neg_waveOp (H : HilbertComplex2 W0 W1 W2) :
    Dense ((-H.waveOp).domain : Set (Tot W0 W1 W2)) :=
  H.neg_waveOp_isSkewAdjoint.dense_domain

/-- **Time reversal on all of `W`**: `R S t = S (-t) R`
(`Feec.C0Group.IsIsometric.antiIntertwines_S`). -/
theorem revT_S (t : ℝ) (x : Tot W0 W1 W2) :
    revT W0 W1 W2 (G.S t x) = G.S (-t) (revT W0 W1 W2 x) :=
  G.isIsometric_toC0Group.antiIntertwines_S _ (intertwines_revT H G) t x

variable {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2}

/-- `R` preserves `K*`. -/
theorem revT_mem_Kmax {x : Tot W0 W1 W2} (hx : x ∈ Kmax G (Kc W0 S1 S2)) :
    revT W0 W1 W2 x ∈ Kmax G (Kc W0 S1 S2) := fun t => by
  have e := revT_S G (-t) x
  rw [neg_neg] at e
  rw [← e]
  exact revT_mem_Kc (hx _)

variable (W0) in
/-- The embedding `E ↦ (0, E, 0)`. -/
def iniE : W1 →L[ℝ] Tot W0 W1 W2 :=
  (totL (W0 := W0) (W1 := W1) (W2 := W2)).symm.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.inr ℝ W0 (W1 × W2)) ∘L ContinuousLinearMap.inl ℝ W1 W2)

variable (W0) in
/-- The embedding `B ↦ (0, 0, B)`. -/
def iniB : W2 →L[ℝ] Tot W0 W1 W2 :=
  (totL (W0 := W0) (W1 := W1) (W2 := W2)).symm.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.inr ℝ W0 (W1 × W2)) ∘L ContinuousLinearMap.inr ℝ W1 W2)

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2] in
theorem iniE_apply (u : W1) : iniE W0 (W2 := W2) u = ini W0 u 0 := rfl

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2] in
theorem iniB_apply (ρ : W2) : iniB W0 (W1 := W1) ρ = ini W0 0 ρ := rfl

variable (S1 S2) in
/-- The electric slot of `K*`: `S1* = {E | (0, E, 0) ∈ K*}`. -/
def S1max : Submodule ℝ W1 := (Kmax G (Kc W0 S1 S2)).comap (iniE W0 (W2 := W2)).toLinearMap

variable (S1 S2) in
/-- The magnetic slot of `K*`: `S2* = {B | (0, 0, B) ∈ K*}`. -/
def S2max : Submodule ℝ W2 := (Kmax G (Kc W0 S1 S2)).comap (iniB W0 (W1 := W1)).toLinearMap

theorem mem_S1max {u : W1} : u ∈ S1max G S1 S2 ↔ ini W0 u 0 ∈ Kmax G (Kc W0 S1 S2) := Iff.rfl

theorem mem_S2max {ρ : W2} : ρ ∈ S2max G S1 S2 ↔ ini W0 0 ρ ∈ Kmax G (Kc W0 S1 S2) := Iff.rfl


variable [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]

theorem isClosed_S1max : IsClosed (S1max G S1 S2 : Set W1) := by
  rw [S1max, Submodule.comap_coe]
  exact (isClosed_of_hasOrthogonalProjection (Kmax G (Kc W0 S1 S2))).preimage
    (iniE W0 (W1 := W1) (W2 := W2)).continuous

theorem isClosed_S2max : IsClosed (S2max G S1 S2 : Set W2) := by
  rw [S2max, Submodule.comap_coe]
  exact (isClosed_of_hasOrthogonalProjection (Kmax G (Kc W0 S1 S2))).preimage
    (iniB W0 (W1 := W1) (W2 := W2)).continuous

instance : (S1max G S1 S2).HasOrthogonalProjection := by
  have : CompleteSpace (S1max G S1 S2) := (isClosed_S1max G).completeSpace_coe
  infer_instance

instance : (S2max G S1 S2).HasOrthogonalProjection := by
  have : CompleteSpace (S2max G S1 S2) := (isClosed_S2max G).completeSpace_coe
  infer_instance

omit [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection] in
/-- **`K*` is a product**: `K* = {0} × S1* × S2*`. -/
theorem Kmax_eq_Kc : Kmax G (Kc W0 S1 S2) = Kc W0 (S1max G S1 S2) (S2max G S1 S2) := by
  ext x
  constructor
  · intro hx
    have hK := (mem_Kc).1 (Kmax_le hx)
    have hR := revT_mem_Kmax G hx
    rw [mem_Kc]
    refine ⟨hK.1, ?_, ?_⟩
    · rw [mem_S1max]
      have e : ini W0 (tot W0 W1 W2 x).2.1 (0 : W2) = (1 / 2 : ℝ) • (x + revT W0 W1 W2 x) := by
        apply (tot W0 W1 W2).injective
        rw [tot_ini, _root_.map_smul, _root_.map_add, tot_revT]
        refine Prod.ext (by simp [hK.1]) (Prod.ext ?_ (by simp))
        simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
        rw [← two_smul ℝ, smul_smul]
        norm_num
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ hx hR)
    · rw [mem_S2max]
      have e : ini W0 (0 : W1) (tot W0 W1 W2 x).2.2 = (1 / 2 : ℝ) • (x - revT W0 W1 W2 x) := by
        apply (tot W0 W1 W2).injective
        rw [tot_ini, _root_.map_smul, _root_.map_sub, tot_revT]
        refine Prod.ext (by simp [hK.1]) (Prod.ext (by simp) ?_)
        simp only [Prod.smul_snd, Prod.snd_sub]
        rw [sub_neg_eq_add, ← two_smul ℝ, smul_smul]
        norm_num
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hx hR)
  · intro hx
    rw [mem_Kc] at hx
    have e : x = ini W0 (tot W0 W1 W2 x).2.1 0 + ini W0 0 (tot W0 W1 W2 x).2.2 := by
      apply (tot W0 W1 W2).injective
      rw [_root_.map_add, tot_ini, tot_ini]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hx.1]
    rw [e]
    exact Submodule.add_mem _ hx.2.1 hx.2.2

omit [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection] in
theorem S1max_le : S1max G S1 S2 ≤ S1 := fun u hu => by
  simpa [tot_ini] using ((mem_Kc).1 (Kmax_le ((mem_S1max G).1 hu))).2.1

omit [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection] in
theorem S2max_le : S2max G S1 S2 ≤ S2 := fun ρ hρ => by
  simpa [tot_ini] using ((mem_Kc).1 (Kmax_le ((mem_S2max G).1 hρ))).2.2

/-- **The projection hypothesis holds for `K*`**: `P_{K*} D(L) ⊆ D(L)`. -/
theorem projKcMax_mem_domL :
    ∀ x ∈ H.domL, projKc W0 (S1max G S1 S2) (S2max G S1 S2) x ∈ H.domL := by
  intro x hx
  rw [← starProjection_Kc]
  refine (reducing_of_invariant G (Kc W0 (S1max G S1 S2) (S2max G S1 S2))
    (fun t y hy => ?_) ⟨x, hx⟩).1
  rw [← Kmax_eq_Kc] at hy ⊢
  exact S_mem_Kmax hy t

/-- `D(L) ∩ K*` is dense in `K*`. -/
theorem mem_closure_domL_inter_KcMax :
    ∀ k ∈ Kc W0 (S1max G S1 S2) (S2max G S1 S2),
      k ∈ closure ((H.domL : Set (Tot W0 W1 W2)) ∩ Kc W0 (S1max G S1 S2) (S2max G S1 S2)) :=
  mem_closure_domain_inter_of_proj (L := -H.waveOp) (dense_domain_neg_waveOp H) _
    fun x hx => by rw [starProjection_Kc]; exact projKcMax_mem_domL G x hx

/-- `(0, E, 0) ∈ D(L)` for `E ∈ V1 ∩ ker d0*`. -/
theorem ini_mem_domL_E {u : W1} (hu : u ∈ H.d1.domain) (hk : u ∈ H.d0†.ker) :
    ini W0 u (0 : W2) ∈ H.domL := by
  rw [mem_domL, tot_ini]
  exact ⟨Submodule.zero_mem _, Submodule.mem_inf.2 ⟨hu, Feec.Constraints.ker_le_domain _ hk⟩,
    Submodule.zero_mem _⟩

/-- `(0, 0, B) ∈ D(L)` for `B ∈ V2*`. -/
theorem ini_mem_domL_B {ρ : W2} (hρ : ρ ∈ H.d1†.domain) : ini W0 (0 : W1) ρ ∈ H.domL := by
  rw [mem_domL, tot_ini]
  exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, hρ⟩

/-- **`d1 (V1 ∩ S1*) ⊆ S2*`** (the `hd1` hypothesis of `prop_4_17` for `K*`). -/
theorem d1_mem_S2max (hS1 : S1 ≤ H.d0†.ker) (u : H.d1.domain) (hu : (u : W1) ∈ S1max G S1 S2) :
    H.d1 u ∈ S2max G S1 S2 := by
  have hx := ini_mem_domL_E (W0 := W0) (W2 := W2) u.2 (hS1 (S1max_le G hu))
  have hm := apply_mem_Kmax (G := G) (K := Kc W0 S1 S2) ⟨ini W0 (u : W1) 0, hx⟩ hu
  rw [Kmax_eq_Kc, mem_Kc, LinearPMap.neg_apply, _root_.map_neg, tot_waveOp] at hm
  have hp : H.prV1 ⟨ini W0 (u : W1) 0, hx⟩ = u := Subtype.ext (by simp)
  simpa [hp] using hm.2.2

/-- **`d1* (V2* ∩ S2*) ⊆ S1*`** (the `hd1s` hypothesis of `prop_4_17` for `K*`). -/
theorem adj1_mem_S1max (ρ : H.d1†.domain) (hρ : (ρ : W2) ∈ S2max G S1 S2) :
    H.d1† ρ ∈ S1max G S1 S2 := by
  have hx := ini_mem_domL_B (W0 := W0) (W1 := W1) (H := H) ρ.2
  have hm := apply_mem_Kmax (G := G) (K := Kc W0 S1 S2) ⟨ini W0 0 (ρ : W2), hx⟩ hρ
  rw [Kmax_eq_Kc, mem_Kc, LinearPMap.neg_apply, _root_.map_neg, tot_waveOp] at hm
  have hp0 : H.pr0 ⟨ini W0 0 (ρ : W2), hx⟩ = 0 := Subtype.ext (by simp)
  have hp2 : H.prV2s ⟨ini W0 0 (ρ : W2), hx⟩ = ρ := Subtype.ext (by simp)
  have := hm.2.1
  simp only [hp0, hp2, LinearPMap.map_zero, zero_add, Prod.snd_neg, Prod.fst_neg] at this
  simpa using (S1max G S1 S2).neg_mem this

/-- **Corrected Prop 4.17 (maximal form)**: for `S1 ≤ ker d0*` and any closed `S2`, Prop 4.17
holds for `K* = {0} × S1* × S2*` with all of its hypotheses proved: data `(0, E₀, B₀) ∈ D(L)`
with `E₀ ∈ S1*`, `B₀ ∈ S2*` give strong solutions that stay in `K* ⊆ K` and solve (4.15).

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17 and §4.11, Prop 4.19] assume
`P_K D(L) ⊆ D(L)` for `K = {0} × L²(TSD) × L²(TSD)`, which fails on bounded domains; replacing `K`
by `K*` (no hypothesis) gives a true statement, and `K*` is the largest admissible choice
(`le_max_of_prop_4_17_hyps`). -/
theorem prop_4_17_max (hS1 : S1 ≤ H.d0†.ker) {T : ℝ} {E₀ : W1} {B₀ : W2}
    {U : ℝ → Tot W0 W1 W2} (hE₀ : E₀ ∈ S1max G S1 S2) (hB₀ : B₀ ∈ S2max G S1 S2)
    (hU : IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0 U) :
    (∀ t ∈ Icc 0 T, U t ∈ Kc W0 (S1max G S1 S2) (S2max G S1 S2)) ∧
      IsReducedSolution H T E₀ B₀ (fun t => (tot W0 W1 W2 (U t)).2.1)
        (fun t => (tot W0 W1 W2 (U t)).2.2) :=
  prop_4_17 ((S1max_le G).trans hS1) (projKcMax_mem_domL G) (d1_mem_S2max G hS1)
    (adj1_mem_S1max G) hE₀ hB₀ hU

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2]
  [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection] in
theorem Kc_mono {S1' : Submodule ℝ W1} {S2' : Submodule ℝ W2} (h1 : S1' ≤ S1) (h2 : S2' ≤ S2) :
    Kc W0 S1' S2' ≤ Kc W0 S1 S2 := fun x hx => by
  rw [mem_Kc] at hx ⊢
  exact ⟨hx.1, h1 hx.2.1, h2 hx.2.2⟩

/-- **Maximality of `K*`**: if closed `S1' ≤ S1`, `S2' ≤ S2` satisfy the hypotheses of
`prop_4_17` (projection hypothesis, `d1 (V1 ∩ S1') ⊆ S2'`, `d1* (V2* ∩ S2') ⊆ S1'`), then
`S1' ≤ S1*` and `S2' ≤ S2*`. -/
theorem le_max_of_prop_4_17_hyps (hS1 : S1 ≤ H.d0†.ker) {S1' : Submodule ℝ W1}
    {S2' : Submodule ℝ W2} [S1'.HasOrthogonalProjection] [S2'.HasOrthogonalProjection]
    (h1 : S1' ≤ S1) (h2 : S2' ≤ S2) (hPD : ∀ x ∈ H.domL, projKc W0 S1' S2' x ∈ H.domL)
    (hd1 : ∀ u : H.d1.domain, (u : W1) ∈ S1' → H.d1 u ∈ S2')
    (hd1s : ∀ ρ : H.d1†.domain, (ρ : W2) ∈ S2' → H.d1† ρ ∈ S1') :
    S1' ≤ S1max G S1 S2 ∧ S2' ≤ S2max G S1 S2 := by
  have hfwd : ∀ x ∈ H.domL, x ∈ Kc W0 S1' S2' → ∀ t, 0 ≤ t → G.S t x ∈ Kc W0 S1' S2' :=
    fun x hx hxK t ht => Kc_propagate (h1.trans hS1) hPD hd1 hd1s
      (isStrongSolution_orbit G t ⟨x, hx⟩) hxK t ⟨ht, le_rfl⟩
  have hD : ∀ x ∈ H.domL, x ∈ Kc W0 S1' S2' → x ∈ Kmax G (Kc W0 S1 S2) := by
    intro x hx hxK t
    refine Kc_mono h1 h2 ?_
    rcases le_total 0 t with ht | ht
    · exact hfwd x hx hxK t ht
    · have e := revT_S G (-t) (revT W0 W1 W2 x)
      rw [neg_neg, revT_revT] at e
      rw [← e]
      exact revT_mem_Kc (hfwd _ (revT_mem_domL H hx) (revT_mem_Kc hxK) (-t) (by linarith))
  have hK : Kc W0 S1' S2' ≤ Kmax G (Kc W0 S1 S2) := by
    intro k hk
    have hcl := mem_closure_domain_inter_of_proj (L := -H.waveOp) (dense_domain_neg_waveOp H)
      (Kc W0 S1' S2') (fun x hx => by rw [starProjection_Kc]; exact hPD x hx) k hk
    refine closure_minimal ?_ (isClosed_of_hasOrthogonalProjection _) hcl
    rintro y ⟨hy1, hy2⟩
    exact hD y hy1 hy2
  refine ⟨fun u hu => (mem_S1max G).2 (hK ?_), fun ρ hρ => (mem_S2max G).2 (hK ?_)⟩
  · rw [mem_Kc, tot_ini]; exact ⟨rfl, hu, Submodule.zero_mem _⟩
  · rw [mem_Kc, tot_ini]; exact ⟨rfl, Submodule.zero_mem _, hρ⟩

omit [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection] in
/-- **Which data propagate**: `x ∈ D(L) ∩ K` lies in `K*` iff every strong solution from `x` and
every strong solution from `R x` (`R(σ, E, B) = (-σ, E, -B)`) stay in `K` on every `[0, T]`.
(Forward propagation from `x` alone is weaker in general; see the module docstring.) -/
theorem mem_Kmax_iff_propagate {x : Tot W0 W1 W2} (hx : x ∈ H.domL) :
    x ∈ Kmax G (Kc W0 S1 S2) ↔
      (∀ (T : ℝ) (U : ℝ → Tot W0 W1 W2), IsStrongSolution (-H.waveOp) T x 0 U →
        ∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2) ∧
      (∀ (T : ℝ) (U : ℝ → Tot W0 W1 W2), IsStrongSolution (-H.waveOp) T (revT W0 W1 W2 x) 0 U →
        ∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2) := by
  constructor
  · intro hK
    have key : ∀ y ∈ H.domL, y ∈ Kmax G (Kc W0 S1 S2) → ∀ (T : ℝ) (U : ℝ → Tot W0 W1 W2),
        IsStrongSolution (-H.waveOp) T y 0 U → ∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2 := by
      intro y hy hyK T U hU t ht
      rw [strongSolution_unique _ G.isSkewSymm hU (isStrongSolution_orbit G T ⟨y, hy⟩) ht]
      exact hyK t
    exact ⟨key x hx hK, key _ (revT_mem_domL H hx) (revT_mem_Kmax G hK)⟩
  · rintro ⟨hf, hr⟩ t
    rcases le_total 0 t with ht | ht
    · exact hf t _ (isStrongSolution_orbit G t ⟨x, hx⟩) t ⟨ht, le_rfl⟩
    · have e := revT_S G (-t) (revT W0 W1 W2 x)
      rw [neg_neg, revT_revT] at e
      rw [← e]
      exact revT_mem_Kc (hr (-t) _ (isStrongSolution_orbit G (-t) ⟨_, revT_mem_domL H hx⟩) (-t)
        ⟨by linarith, le_rfl⟩)

omit [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection] in
/-- **Stationary magnetic data propagate**: if `B ∈ V2* ∩ S2` with `d1* B = 0`, then `(0, 0, B)`
is a stationary point of (4.14) and `B ∈ S2*`. -/
theorem mem_S2max_of_adj1_eq_zero (ρ : H.d1†.domain) (hρ : (ρ : W2) ∈ S2) (h0 : H.d1† ρ = 0) :
    (ρ : W2) ∈ S2max G S1 S2 := by
  have hx := ini_mem_domL_B (W0 := W0) (W1 := W1) (H := H) ρ.2
  refine mem_Kmax_of_apply_eq_zero (G := G) (K := Kc W0 S1 S2) ⟨ini W0 0 (ρ : W2), hx⟩ ?_ ?_
  · rw [mem_Kc, tot_ini]; exact ⟨rfl, Submodule.zero_mem _, hρ⟩
  · rw [LinearPMap.neg_apply, neg_eq_zero]
    apply (tot W0 W1 W2).injective
    rw [tot_waveOp, _root_.map_zero]
    have hp0 : H.pr0 ⟨ini W0 0 (ρ : W2), hx⟩ = 0 := Subtype.ext (by simp)
    have hp1 : H.prV1 ⟨ini W0 0 (ρ : W2), hx⟩ = 0 := Subtype.ext (by simp)
    have hp1s : H.prV1s ⟨ini W0 0 (ρ : W2), hx⟩ = 0 := Subtype.ext (by simp)
    have hp2 : H.prV2s ⟨ini W0 0 (ρ : W2), hx⟩ = ρ := Subtype.ext (by simp)
    simp [hp0, hp1, hp1s, hp2, h0]

end Wave

/-! ## Unconditional forms (Stone's theorem) -/

section Unconditional

open HilbertComplex2

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    (H : HilbertComplex2 W0 W1 W2) {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2}
    [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]

/-- **Corrected Prop 4.17, unconditional**: with `S1*`, `S2*` built from the Hodge wave group
(`HilbertComplex2.waveGroup`, Stone's theorem), every datum `(0, E₀, B₀) ∈ D(L)` with
`E₀ ∈ S1*`, `B₀ ∈ S2*` has, on every `[0, T]`, a unique strong solution of (4.14); it stays in
`{0} × S1* × S2* ⊆ {0} × S1 × S2` and solves the reduced system (4.15).

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem prop_4_17_max_unconditional (hS1 : S1 ≤ H.d0†.ker) (T : ℝ) {E₀ : W1} {B₀ : W2}
    (hD : ini W0 E₀ B₀ ∈ H.domL) (hE₀ : E₀ ∈ S1max H.waveGroup S1 S2)
    (hB₀ : B₀ ∈ S2max H.waveGroup S1 S2) :
    ∃ U : ℝ → Tot W0 W1 W2, IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0 U ∧
      (∀ U', IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0 U' → EqOn U' U (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, U t ∈ Kc W0 (S1max H.waveGroup S1 S2) (S2max H.waveGroup S1 S2)) ∧
      IsReducedSolution H T E₀ B₀ (fun t => (tot W0 W1 W2 (U t)).2.1)
        (fun t => (tot W0 W1 W2 (U t)).2.2) := by
  obtain ⟨U, hU⟩ := H.neg_waveOp_isSkewAdjoint.wellPosedHom T _ hD
  have skew := H.neg_waveOp_isSkewAdjoint.isSkewSymm H.neg_waveOp_isSkewAdjoint.dense_domain
  obtain ⟨h1, h2⟩ := prop_4_17_max H.waveGroup hS1 hE₀ hB₀ hU
  exact ⟨U, hU, fun U' hU' => strongSolution_unique _ skew hU' hU, h1, h2⟩

end Unconditional

end Feec.Constraints

/-! ## Bounded domains -/

namespace Feec.BoundedDomain

open Feec.HilbertComplex2 Feec.Constraints

variable {Ω : Set R3}

section Generic

variable {W0 W1 W2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
  {H : HilbertComplex2 W0 W1 W2} (G : UnitaryGroupGenerator (-H.waveOp))
  {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2} [S1.HasOrthogonalProjection]
  [S2.HasOrthogonalProjection]

/-- **The electric slot of `K*` lies in `L²(TSD₀)`** on a bounded domain, for any complex with
`ι D(d1) ⊆ H̊(curl, M)` and `ι S1 ⊆ L²(TSD)`: `D(L) ∩ K*` is dense in `K*`, its electric fields lie
in `L²(TSD) ∩ H̊(curl, M) ⊆ L²(TSD₀)` (`mem_TSD0_of_mem_HcurlZero`), and `L²(TSD₀)` is closed. -/
theorem S1max_le_TSD0 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (ι : W1 →L[ℝ] L2M Ω)
    (hι : ∀ u ∈ H.d1.domain, ι u ∈ HcurlZero Ω) (hS1 : ∀ u ∈ S1, ι u ∈ TSD Ω) :
    ∀ u ∈ S1max G S1 S2, ι u ∈ TSD0 Ω hΩ hb := by
  intro u hu
  have hk : ini W0 u (0 : W2) ∈ Kc W0 (S1max G S1 S2) (S2max G S1 S2) := by
    rw [mem_Kc, tot_ini]; exact ⟨rfl, hu, Submodule.zero_mem _⟩
  have hcl := mem_closure_domL_inter_KcMax G _ hk
  let Φ : Tot W0 W1 W2 →L[ℝ] L2M Ω := ι.comp
    ((ContinuousLinearMap.fst ℝ W1 W2).comp ((ContinuousLinearMap.snd ℝ W0 _).comp
      (Feec.Constraints.totL (W0 := W0) (W1 := W1) (W2 := W2)).toContinuousLinearMap))
  have hΦ : ∀ y, Φ y = ι (tot W0 W1 W2 y).2.1 := fun y => rfl
  have := map_mem_closure Φ.continuous hcl (t := (TSD0 Ω hΩ hb : Set (L2M Ω))) fun y hy => by
    obtain ⟨hyD, hyK⟩ := hy
    have hD := (Feec.Constraints.mem_domL H).1 hyD
    have hE : (tot W0 W1 W2 y).2.1 ∈ H.d1.domain := (Submodule.mem_inf.1 hD.2.1).1
    rw [SetLike.mem_coe, hΦ]
    exact mem_TSD0_of_mem_HcurlZero hΩ hb (hS1 _ (S1max_le G ((mem_Kc).1 hyK).2.1)) (hι _ hE)
  rw [(isClosed_TSD0 hΩ hb).closure_eq, hΦ, tot_ini] at this
  exact this

/-- **`d1*` maps the magnetic slot of `K*` into `L²(TSD₀)`.** -/
theorem adj1_mem_TSD0_of_mem_S2max (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (ι : W1 →L[ℝ] L2M Ω) (hι : ∀ u ∈ H.d1.domain, ι u ∈ HcurlZero Ω)
    (hS1 : ∀ u ∈ S1, ι u ∈ TSD Ω) (ρ : H.d1†.domain) (hρ : (ρ : W2) ∈ S2max G S1 S2) :
    ι (H.d1† ρ) ∈ TSD0 Ω hΩ hb :=
  S1max_le_TSD0 G hΩ hb ι hι hS1 _ (adj1_mem_S1max G ρ hρ)

end Generic

section Thesis

variable (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
  (G : UnitaryGroupGenerator (-(thesisComplex hΩ hb).waveOp))

/-- For the thesis' complex, `S1* ⊆ L²(TSD₀)`. -/
theorem thesisComplex_S1max_le_TSD0 (S2 : Submodule ℝ (L2M Ω)) [S2.HasOrthogonalProjection] :
    S1max G (TSD Ω) S2 ≤ TSD0 Ω hΩ hb :=
  fun u hu => S1max_le_TSD0 G hΩ hb (ContinuousLinearMap.id ℝ _)
    (fun _ hv => mem_domain_curlClosure.1 hv) (fun _ hv => hv) u hu

/-- **Hessians of smooth harmonic functions are stationary magnetic data**: `∇²h ∈ S2*` for the
thesis' complex (`curl ∇²h = 0`, so `(0, 0, ∇²h)` is a stationary point of (4.14) in `K`). -/
theorem thesisComplex_hessL2_mem_S2max {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h)
    (hΔ : ∀ x, lap h x = 0) : hessL2 hΩ hb hh ∈ S2max G (TSD Ω) (TSD Ω) := by
  obtain ⟨hadj, e⟩ := smoothField_mem_adjoint hΩ hb (thesisComplex hΩ hb)
    (mem_closure_curlClosure hΩ hb) (fun ij => contDiff_one_of_top (contDiff_hessField hh ij))
  refine mem_S2max_of_adj1_eq_zero G ⟨_, hadj⟩ (hessL2_mem_TSD hΩ hb hh hΔ) ?_
  rw [e]
  refine smoothField_eq_zero hΩ hb _ _ fun ij x => ?_
  rw [hessField_eq_gradM]
  exact curlM_gradM (fun i => (contDiff_pd_top hh i).of_le (by simp)) ij x

/-- **Constant symmetric trace-free fields are stationary magnetic data**: `A ∈ S2*`. -/
theorem thesisComplex_constField_mem_S2max {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.transpose = A)
    (htrA : A.trace = 0) : constField hΩ hb A ∈ S2max G (TSD Ω) (TSD Ω) := by
  obtain ⟨hadj, e⟩ := smoothField_mem_adjoint hΩ hb (thesisComplex hΩ hb)
    (mem_closure_curlClosure hΩ hb) (Ψ := fun ij _ => A ij.1 ij.2) (fun ij => contDiff_const)
  refine mem_S2max_of_adj1_eq_zero G ⟨_, hadj⟩ (constField_mem_TSD hΩ hb hA htrA) ?_
  rw [e]
  refine smoothField_eq_zero hΩ hb _ _ fun ij x => ?_
  simp [curlM, pd]

/-- **`K* ⊊ K`**: `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ) ∈ L²(TSD)` is not in `S2*`, for any `S2`. -/
theorem thesisComplex_betaField_not_mem_S2max (hne : Ω.Nonempty) (S2 : Submodule ℝ (L2M Ω))
    [S2.HasOrthogonalProjection] :
    smoothField hΩ hb betaField (fun ij => (contDiff_one_of_top (contDiff_betaField ij)).continuous)
      ∉ S2max G (TSD Ω) S2 := by
  intro hm
  obtain ⟨hadj, e⟩ := smoothField_mem_adjoint hΩ hb (thesisComplex hΩ hb)
    (mem_closure_curlClosure hΩ hb) (fun ij => contDiff_one_of_top (contDiff_betaField ij))
  have := thesisComplex_S1max_le_TSD0 hΩ hb G S2 (adj1_mem_S1max G ⟨_, hadj⟩ hm)
  rw [e] at this
  exact curl_betaField_not_mem_TSD0 hΩ hb hne this

/-- **`S1* ⊊ L²(TSD)`**: `diag(1, -1, 0) ∈ L²(TSD)` is not in `S1*`, for any `S2`, because
`S1* ⊆ L²(TSD₀)` and constants with nonzero mean are not in `L²(TSD₀)`. -/
theorem thesisComplex_constField_diagA_not_mem_S1max (hne : Ω.Nonempty)
    (S2 : Submodule ℝ (L2M Ω)) [S2.HasOrthogonalProjection] :
    constField hΩ hb diagA ∉ S1max G (TSD Ω) S2 := fun hm =>
  constField_diagA_not_mem_TSD0 hΩ hb hne (thesisComplex_S1max_le_TSD0 hΩ hb G S2 hm)

/-- **Every curl-free magnetic field of `S2` is a stationary datum**: if `B ∈ S2` has weak curl
`0` (`Σ_{ij} ∫_Ω B_{ij} (curl Φ)_{ij} = 0` for all test fields `Φ`), then `B ∈ D(d1*)`,
`d1* B = 0`, and `B ∈ S2*`. With `S2 = L²(TSD)` this is the static part `L²(TSD) ∩ ker curl` of
`K*` (on simply connected `Ω`: the Hessians `∇²h`, `h` harmonic, `∇²h ∈ L²`). -/
theorem thesisComplex_mem_S2max_of_weakCurl_eq_zero (S2 : Submodule ℝ (L2M Ω))
    [S2.HasOrthogonalProjection] {B : L2M Ω} (hB : B ∈ S2)
    (hc : ∀ Φ : Ix → R3 → ℝ, (∀ ij, IsTest Ω (Φ ij)) →
      ∑ ij, ∫ x, B ij x * curlM Φ ij x ∂MeasureTheory.volume.restrict Ω = 0) :
    B ∈ S2max G (TSD Ω) S2 := by
  obtain ⟨h, e⟩ := thesisComplex_adjoint_d1_apply hΩ hb (C := 0) fun Φ hΦ => by
    rw [hc Φ hΦ]
    refine (Finset.sum_eq_zero fun ij _ => ?_).symm
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    have hz : ((0 : L2M Ω) ij : R3 → ℝ) =ᵐ[MeasureTheory.volume.restrict Ω] 0 := by
      rw [PiLp.zero_apply]; exact MeasureTheory.Lp.coeFn_zero _ _ _
    filter_upwards [hz] with x hx
    rw [hx, Pi.zero_apply, zero_mul]
  exact mem_S2max_of_adj1_eq_zero G ⟨B, h⟩ hB e

/-- **Corrected Prop 4.17 on bounded domains** (thesis' complex `H̊¹(V) → H̊(curl, M) → L²(M)`,
`K = {0} × L²(TSD) × L²(TSD)`, `K* = {0} × S1* × S2*` for the Hodge wave group):
1. `K* = {0} × S1* × S2*` with `S1* ⊆ L²(TSD₀)` and `S2* ⊆ L²(TSD)`;
2. `(S1*, S2*)` satisfies all hypotheses of `Feec.Constraints.prop_4_17` (projection hypothesis,
   `d1 (V1 ∩ S1*) ⊆ S2*`, `d1* (V2* ∩ S2*) ⊆ S1*`), and it is the largest such pair: every closed
   `S1' ≤ L²(TSD)`, `S2' ≤ L²(TSD)` satisfying them lies in `(S1*, S2*)`;
3. strictness: `diag(1, -1, 0) ∈ L²(TSD) \ S1*` and `β ∈ L²(TSD) \ S2*`, so `K* ⊊ K` in both
   slots; and `diag(1, -1, 0) ∈ S2*`, a nonzero **stationary** datum;
4. every datum `(0, E₀, B₀) ∈ D(L)` with `E₀ ∈ S1*`, `B₀ ∈ S2*` has, on every `[0, T]`, a unique
   strong solution of (4.14); it stays in `K* ⊆ K` and solves (4.15).

Scope: `K*` is invariant by definition, so items 2 and 4 are the thesis' argument run on the
largest subspace where it can work; the content is in items 1 and 3 and in maximality. The only
elements of `K*` exhibited are stationary (`d1* B = 0`: harmonic Hessians, constants,
`thesisComplex_mem_S2max_of_weakCurl_eq_zero`), where propagation is trivial. No nonzero element
of `S1*` and no non-stationary element of `K*` is known. It is open whether `K*` contains any
non-stationary datum; on every open cube it does not (`Feec.BoxIdent.openCube_mem_Kmax_iff'`).

Correction: [QuennevilleBelair2015, §4.10, Prop 4.17]: its projection hypothesis fails on every
nonempty bounded open `Ω`, and its conclusion fails for `(0, 0, β)`; this statement replaces
`L²(TSD) × L²(TSD)` by the maximal admissible `S1* × S2*` and needs no hypothesis. -/
theorem thesisComplex_prop_4_17_max (hne : Ω.Nonempty) :
    let G := (thesisComplex hΩ hb).waveGroup
    Kmax G (Kc (L2V Ω) (TSD Ω) (TSD Ω)) =
        Kc (L2V Ω) (S1max G (TSD Ω) (TSD Ω)) (S2max G (TSD Ω) (TSD Ω)) ∧
      S1max G (TSD Ω) (TSD Ω) ≤ TSD0 Ω hΩ hb ∧ S2max G (TSD Ω) (TSD Ω) ≤ TSD Ω ∧
      (∀ x ∈ (thesisComplex hΩ hb).domL, projKc (L2V Ω) (S1max G (TSD Ω) (TSD Ω))
        (S2max G (TSD Ω) (TSD Ω)) x ∈ (thesisComplex hΩ hb).domL) ∧
      (∀ u : (thesisComplex hΩ hb).d1.domain, (u : L2M Ω) ∈ S1max G (TSD Ω) (TSD Ω) →
        (thesisComplex hΩ hb).d1 u ∈ S2max G (TSD Ω) (TSD Ω)) ∧
      (∀ ρ : (thesisComplex hΩ hb).d1†.domain, (ρ : L2M Ω) ∈ S2max G (TSD Ω) (TSD Ω) →
        (thesisComplex hΩ hb).d1† ρ ∈ S1max G (TSD Ω) (TSD Ω)) ∧
      (∀ (S1' S2' : Submodule ℝ (L2M Ω)) [S1'.HasOrthogonalProjection]
        [S2'.HasOrthogonalProjection], S1' ≤ TSD Ω → S2' ≤ TSD Ω →
        (∀ x ∈ (thesisComplex hΩ hb).domL, projKc (L2V Ω) S1' S2' x ∈ (thesisComplex hΩ hb).domL) →
        (∀ u : (thesisComplex hΩ hb).d1.domain, (u : L2M Ω) ∈ S1' →
          (thesisComplex hΩ hb).d1 u ∈ S2') →
        (∀ ρ : (thesisComplex hΩ hb).d1†.domain, (ρ : L2M Ω) ∈ S2' →
          (thesisComplex hΩ hb).d1† ρ ∈ S1') →
        S1' ≤ S1max G (TSD Ω) (TSD Ω) ∧ S2' ≤ S2max G (TSD Ω) (TSD Ω)) ∧
      constField hΩ hb diagA ∈ TSD Ω ∧ constField hΩ hb diagA ∉ S1max G (TSD Ω) (TSD Ω) ∧
      constField hΩ hb diagA ∈ S2max G (TSD Ω) (TSD Ω) ∧ constField hΩ hb diagA ≠ 0 ∧
      smoothField hΩ hb betaField (fun ij => (contDiff_one_of_top (contDiff_betaField ij)).continuous)
        ∈ TSD Ω ∧
      smoothField hΩ hb betaField (fun ij => (contDiff_one_of_top (contDiff_betaField ij)).continuous)
        ∉ S2max G (TSD Ω) (TSD Ω) ∧
      ∀ (T : ℝ) (E₀ B₀ : L2M Ω), ini (L2V Ω) E₀ B₀ ∈ (thesisComplex hΩ hb).domL →
        E₀ ∈ S1max G (TSD Ω) (TSD Ω) → B₀ ∈ S2max G (TSD Ω) (TSD Ω) →
        ∃ U, IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) E₀ B₀) 0 U ∧
          (∀ U', IsStrongSolution (-(thesisComplex hΩ hb).waveOp) T (ini (L2V Ω) E₀ B₀) 0 U' →
            EqOn U' U (Icc 0 T)) ∧
          (∀ t ∈ Icc 0 T, U t ∈ Kc (L2V Ω) (TSD Ω) (TSD Ω)) ∧
          IsReducedSolution (thesisComplex hΩ hb) T E₀ B₀
            (fun t => (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.1)
            (fun t => (tot (L2V Ω) (L2M Ω) (L2M Ω) (U t)).2.2) := by
  intro G
  refine ⟨Kmax_eq_Kc G, thesisComplex_S1max_le_TSD0 hΩ hb G _, S2max_le G,
    projKcMax_mem_domL G,
    fun u hu => d1_mem_S2max G (thesisComplex_TSD_le_ker hΩ hb) u hu,
    fun ρ hρ => adj1_mem_S1max G ρ hρ,
    fun S1' S2' _ _ h1 h2 hPD hd1 hd1s =>
      le_max_of_prop_4_17_hyps G (thesisComplex_TSD_le_ker hΩ hb) h1 h2 hPD hd1 hd1s,
    constField_mem_TSD hΩ hb diagA_transpose diagA_trace,
    thesisComplex_constField_diagA_not_mem_S1max hΩ hb G hne _,
    thesisComplex_constField_mem_S2max hΩ hb G diagA_transpose diagA_trace,
    fun h0 => constField_diagA_not_mem_TSD0 hΩ hb hne (h0 ▸ Submodule.zero_mem _),
    betaField_mem_TSD hΩ hb, thesisComplex_betaField_not_mem_S2max hΩ hb G hne _,
    fun T E₀ B₀ hD hE₀ hB₀ => ?_⟩
  obtain ⟨U, hU, huniq, hK, hred⟩ := prop_4_17_max_unconditional (thesisComplex hΩ hb)
    (thesisComplex_TSD_le_ker hΩ hb) T hD hE₀ hB₀
  exact ⟨U, hU, huniq, fun t ht => Kc_mono (S1max_le G) (S2max_le G) (hK t ht), hred⟩

end Thesis

end Feec.BoundedDomain
