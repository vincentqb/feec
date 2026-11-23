module

public import Solution.Bounded
public import Solution.Engine
public import Feec.Counterexamples.BoxStationary

/-!
# On boxes the grad–curl system keeps a TSD constraint only along stationary solutions

The challenge's Hodge wave operator `IsHodgeWave d⁰ d¹` is carried by unitary maps
`e₀, e₁, e₂` intertwining `d⁰, d¹` with the differentials of a `Feec` short complex `S` to the
wave operator of `S`, `(σ, u, ρ) ↦ (-e₀σ, e₁u, e₂ρ)` (`isHodgeWave_iff`; the sign of `σ` is the
sign convention of the challenge), and so are its domain (`exists_isHodgeWave_iff`) and the strong
solutions (`isStrongSolution_toFeec`, `isStrongSolution_ofFeec`). On an open `Ω ⊆ ℝ³` the vector
`0`-, `1`- and `2`-forms are the vector fields and matrix fields of `Feec.Models.BoundedDomain`
(`field0`, `fieldE`, `fieldB`), and the componentwise minimal exterior derivatives are the minimal
row-wise `grad` and `curl` (`mem_graph_grad_iff`, `mem_graph_curl_iff`: row by row, the matrices
of the fields and their transposes intertwine the operators on smooth fields, and
`Feec.Domain.ConstCoeffOp.minimal_ofMatrixCLM_of_comm` carries the minimal graphs both ways).
So the challenge's grad–curl system on a box is `Feec.Models.BoundedDomain.gradCurl`, and
the box clause of `FEEC.tsd_boundary_conditions` is
`Feec.Counterexamples.BoxStationary.forward_iff_stationary_box`: the
strong solutions are the orbits of the wave group (`eq_waveGroup_of_isStrongSolution`), and the
stationary vectors are the zeros of `L`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 ((4.14), Prop 4.17)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set MeasureTheory Filter Topology

@[expose] public noncomputable section

universe u

namespace FEEC

open Feec Feec.Domain Feec.Models.BoundedDomain
open Feec.HilbertComplex (totalSub)
open Feec.ShortHilbertComplex (W3 family3 mk3 mem_totalSub_family3)
open Feec.Koszul.Proxy3 (vec1)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- A point of a graph is a point of the operator. -/
theorem apply_of_mem_graph {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {T : E →ₗ.[ℝ] F} {x : E} {y : F} (h : (x, y) ∈ T.graph) :
    ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = y :=
  ⟨LinearPMap.mem_domain_of_mem_graph h, ((LinearPMap.image_iff _).2 h).symm⟩

theorem pmap_congr {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (T : E →ₗ.[ℝ] F) {x y : E} (h : x = y) (hx : x ∈ T.domain) (hy : y ∈ T.domain) :
    T ⟨x, hx⟩ = T ⟨y, hy⟩ := by
  subst h; rfl

/-! ### The Hodge wave operator under unitary maps -/

section Transfer

variable {W0 W1 W2 : Type*} [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [NormedAddCommGroup W2]
  [InnerProductSpace ℝ W2] {X0 X1 X2 : Type u} [NormedAddCommGroup X0] [InnerProductSpace ℝ X0]
  [NormedAddCommGroup X1] [InnerProductSpace ℝ X1] [NormedAddCommGroup X2]
  [InnerProductSpace ℝ X2]
  (e0 : W0 ≃ₗᵢ[ℝ] X0) (e1 : W1 ≃ₗᵢ[ℝ] X1) (e2 : W2 ≃ₗᵢ[ℝ] X2)

/-- **The state map** `(σ, u, ρ) ↦ (-e₀σ, e₁u, e₂ρ)`. -/
def stateL : W0 × W1 × W2 →L[ℝ] PiLp 2 (W3 X0 X1 X2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (W3 X0 X1 X2)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun
      | 0 => -((e0 : W0 →L[ℝ] X0) ∘L ContinuousLinearMap.fst ℝ W0 (W1 × W2))
      | 1 => (e1 : W1 →L[ℝ] X1) ∘L ContinuousLinearMap.fst ℝ W1 W2 ∘L
          ContinuousLinearMap.snd ℝ W0 (W1 × W2)
      | 2 => (e2 : W2 →L[ℝ] X2) ∘L ContinuousLinearMap.snd ℝ W1 W2 ∘L
          ContinuousLinearMap.snd ℝ W0 (W1 × W2)

theorem stateL_apply (U : W0 × W1 × W2) :
    stateL e0 e1 e2 U = mk3 (-e0 U.1) (e1 U.2.1) (e2 U.2.2) := by
  refine PiLp.ext fun i => ?_
  fin_cases i <;> rfl

/-- The inverse of the state map. -/
def stateInvL : PiLp 2 (W3 X0 X1 X2) →L[ℝ] W0 × W1 × W2 :=
  ((-(e0.symm : X0 →L[ℝ] W0)).comp (PiLp.proj 2 (𝕜 := ℝ) (W3 X0 X1 X2) 0)).prod
    (((e1.symm : X1 →L[ℝ] W1).comp (PiLp.proj 2 (𝕜 := ℝ) (W3 X0 X1 X2) 1)).prod
      ((e2.symm : X2 →L[ℝ] W2).comp (PiLp.proj 2 (𝕜 := ℝ) (W3 X0 X1 X2) 2)))

theorem stateInvL_apply (x : PiLp 2 (W3 X0 X1 X2)) :
    stateInvL e0 e1 e2 x = (-e0.symm (x 0), e1.symm (x 1), e2.symm (x 2)) := rfl

theorem stateL_stateInvL (x : PiLp 2 (W3 X0 X1 X2)) :
    stateL e0 e1 e2 (stateInvL e0 e1 e2 x) = x := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · show -e0 (-e0.symm (x 0 : X0)) = (x 0 : X0)
    rw [map_neg, neg_neg]
    exact e0.apply_symm_apply _
  · exact e1.apply_symm_apply (x 1 : X1)
  · exact e2.apply_symm_apply (x 2 : X2)

theorem stateInvL_stateL (U : W0 × W1 × W2) : stateInvL e0 e1 e2 (stateL e0 e1 e2 U) = U := by
  obtain ⟨U1, U2, U3⟩ := U
  show (-e0.symm (-e0 U1), e1.symm (e1 U2), e2.symm (e2 U3)) = (U1, U2, U3)
  simp

variable [CompleteSpace X0] [CompleteSpace X1] [CompleteSpace X2]
  (S : ShortHilbertComplex ℝ X0 X1 X2) {d0 : W0 →ₗ.[ℝ] W1} {d1 : W1 →ₗ.[ℝ] W2}
  (h0 : ∀ x y, (x, y) ∈ d0.graph ↔ (e0 x, e1 y) ∈ S.d₀.graph)
  (h1 : ∀ x y, (x, y) ∈ d1.graph ↔ (e1 x, e2 y) ∈ S.d₁.graph)

include h0 in
theorem d0_of (σ : d0.domain) : ∃ h : e0 σ ∈ S.d₀.domain, S.d₀ ⟨_, h⟩ = e1 (d0 σ) :=
  apply_of_mem_graph ((h0 _ _).1 (d0.mem_graph σ))

include h0 in
theorem d0_of' (x : W0) (hx : e0 x ∈ S.d₀.domain) :
    ∃ h : x ∈ d0.domain, e1 (d0 ⟨x, h⟩) = S.d₀ ⟨_, hx⟩ := by
  obtain ⟨h, e⟩ := apply_of_mem_graph ((h0 x (e1.symm (S.d₀ ⟨_, hx⟩))).2 (by
    simpa using S.d₀.mem_graph ⟨_, hx⟩))
  exact ⟨h, by rw [e, LinearIsometryEquiv.apply_symm_apply]⟩

include h1 in
theorem d1_of (u : d1.domain) : ∃ h : e1 u ∈ S.d₁.domain, S.d₁ ⟨_, h⟩ = e2 (d1 u) :=
  apply_of_mem_graph ((h1 _ _).1 (d1.mem_graph u))

include h1 in
theorem d1_of' (x : W1) (hx : e1 x ∈ S.d₁.domain) :
    ∃ h : x ∈ d1.domain, e2 (d1 ⟨x, h⟩) = S.d₁ ⟨_, hx⟩ := by
  obtain ⟨h, e⟩ := apply_of_mem_graph ((h1 x (e2.symm (S.d₁ ⟨_, hx⟩))).2 (by
    simpa using S.d₁.mem_graph ⟨_, hx⟩))
  exact ⟨h, by rw [e, LinearIsometryEquiv.apply_symm_apply]⟩

include h0 h1 in
/-- **The challenge's Hodge wave operator is `Feec`'s, through the state map.** -/
theorem isHodgeWave_iff (U V : W0 × W1 × W2) :
    IsHodgeWave d0 d1 U V ↔ ∃ h : stateL e0 e1 e2 U ∈ S.wave.domain,
      S.wave ⟨_, h⟩ = stateL e0 e1 e2 V := by
  obtain ⟨U1, U2, U3⟩ := U
  obtain ⟨V1, V2, V3⟩ := V
  simp only [stateL_apply]
  constructor
  · rintro ⟨σ, u, rfl, rfl, H1, H2, H3⟩
    dsimp only at H1 H2 H3
    obtain ⟨hσ, eσ⟩ := d0_of e0 e1 S h0 σ
    obtain ⟨hu, eu⟩ := d1_of e1 e2 S h1 u
    have K0 : ∀ z : S.d₀.domain, ⟪e0 V1, (z : X0)⟫ = ⟪e1 u, S.d₀ z⟫ := fun z => by
      obtain ⟨hz, ez⟩ := d0_of' e0 e1 S h0 (e0.symm z) (by simp)
      have ez' : S.d₀ z = e1 (d0 ⟨_, hz⟩) := by
        rw [ez]; exact pmap_congr _ (by simp) _ _
      calc ⟪e0 V1, (z : X0)⟫ = ⟪e0 V1, e0 (e0.symm z)⟫ := by
            rw [LinearIsometryEquiv.apply_symm_apply]
        _ = ⟪V1, ((⟨_, hz⟩ : d0.domain) : W0)⟫ := LinearIsometryEquiv.inner_map_map e0 _ _
        _ = ⟪(u : W1), d0 ⟨_, hz⟩⟫ := H1 _
        _ = ⟪e1 u, S.d₀ z⟫ := by rw [ez', LinearIsometryEquiv.inner_map_map]
    have K1 : ∀ z : S.d₁.domain, ⟪-(e1 V2 + e1 (d0 σ)), (z : X1)⟫ = ⟪e2 U3, S.d₁ z⟫ :=
      fun z => by
        obtain ⟨hz, ez⟩ := d1_of' e1 e2 S h1 (e1.symm z) (by simp)
        have ez' : S.d₁ z = e2 (d1 ⟨_, hz⟩) := by
          rw [ez]; exact pmap_congr _ (by simp) _ _
        have H := H2 ⟨_, hz⟩
        calc ⟪-(e1 V2 + e1 (d0 σ)), (z : X1)⟫
            = ⟪-(e1 V2 + e1 (d0 σ)), e1 (e1.symm z)⟫ := by
              rw [LinearIsometryEquiv.apply_symm_apply]
          _ = -⟪V2, ((⟨_, hz⟩ : d1.domain) : W1)⟫ - ⟪d0 σ, ((⟨_, hz⟩ : d1.domain) : W1)⟫ := by
              rw [inner_neg_left, inner_add_left, LinearIsometryEquiv.inner_map_map,
                LinearIsometryEquiv.inner_map_map]; ring
          _ = ⟪U3, d1 ⟨_, hz⟩⟫ := by rw [H]; ring
          _ = ⟪e2 U3, S.d₁ z⟫ := by rw [ez', LinearIsometryEquiv.inner_map_map]
    have hadj0 : (e1 u : X1) ∈ S.d₀†.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, K0⟩
    have eadj0 : S.d₀† ⟨_, hadj0⟩ = e0 V1 := LinearPMap.adjoint_apply_eq S.dense₀ _ K0
    have hadj1 : (e2 U3 : X2) ∈ S.d₁†.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, K1⟩
    have eadj1 : S.d₁† ⟨_, hadj1⟩ = -(e1 V2 + e1 (d0 σ)) :=
      LinearPMap.adjoint_apply_eq S.dense₁ _ K1
    have hdom : mk3 (-e0 σ) (e1 u) (e2 U3) ∈ S.wave.domain :=
      S.mem_wave_domain.2 ⟨S.d₀.domain.neg_mem hσ, hu, hadj0, hadj1⟩
    refine ⟨hdom, PiLp.ext fun i => ?_⟩
    fin_cases i
    · change ((S.wave ⟨_, hdom⟩ : PiLp 2 (W3 X0 X1 X2)) 0 : X0) = -e0 V1
      rw [S.wave_apply_zero]
      show -(S.d₀† ⟨e1 u, hadj0⟩) = -e0 V1
      rw [eadj0]
    · change ((S.wave ⟨_, hdom⟩ : PiLp 2 (W3 X0 X1 X2)) 1 : X1) = e1 V2
      rw [S.wave_apply_one]
      show S.d₀ ⟨-e0 σ, S.d₀.domain.neg_mem hσ⟩ - S.d₁† ⟨e2 U3, hadj1⟩ = e1 V2
      have hn : S.d₀ ⟨-e0 σ, S.d₀.domain.neg_mem hσ⟩ = -e1 (d0 σ) := by
        rw [← eσ, ← LinearPMap.map_neg]; rfl
      rw [hn, eadj1]
      abel
    · change ((S.wave ⟨_, hdom⟩ : PiLp 2 (W3 X0 X1 X2)) 2 : X2) = e2 V3
      rw [S.wave_apply_two]
      show S.d₁ ⟨e1 u, hu⟩ = e2 V3
      rw [eu, H3]
  · rintro ⟨hdom, hL⟩
    obtain ⟨hd0, hd1, hadj0, hadj1⟩ := S.mem_wave_domain.1 hdom
    have hσ : (e0 U1 : X0) ∈ S.d₀.domain := by
      simpa using S.d₀.domain.neg_mem hd0
    obtain ⟨hσ', eσ⟩ := d0_of' e0 e1 S h0 U1 hσ
    obtain ⟨hu', eu⟩ := d1_of' e1 e2 S h1 U2 hd1
    have L0 : S.d₀† ⟨e1 U2, hadj0⟩ = e0 V1 := by
      have := congrArg (fun x : PiLp 2 (W3 X0 X1 X2) => (x 0 : X0)) hL
      rw [S.wave_apply_zero] at this
      exact neg_inj.1 this
    have L1 : S.d₀ ⟨-e0 U1, hd0⟩ - S.d₁† ⟨e2 U3, hadj1⟩ = e1 V2 := by
      have := congrArg (fun x : PiLp 2 (W3 X0 X1 X2) => (x 1 : X1)) hL
      rw [S.wave_apply_one] at this
      exact this
    have L2 : S.d₁ ⟨e1 U2, hd1⟩ = e2 V3 := by
      have := congrArg (fun x : PiLp 2 (W3 X0 X1 X2) => (x 2 : X2)) hL
      rw [S.wave_apply_two] at this
      exact this
    have hneg : S.d₀ ⟨-e0 U1, hd0⟩ = -S.d₀ ⟨e0 U1, hσ⟩ := by
      rw [← LinearPMap.map_neg]; rfl
    refine ⟨⟨U1, hσ'⟩, ⟨U2, hu'⟩, rfl, rfl, fun τ => ?_, fun v => ?_, ?_⟩
    · obtain ⟨hτ, eτ⟩ := d0_of e0 e1 S h0 τ
      calc ⟪V1, (τ : W0)⟫ = ⟪e0 V1, e0 τ⟫ := (LinearIsometryEquiv.inner_map_map e0 _ _).symm
        _ = ⟪S.d₀† ⟨e1 U2, hadj0⟩, ((⟨_, hτ⟩ : S.d₀.domain) : X0)⟫ := by rw [L0]
        _ = ⟪e1 U2, S.d₀ ⟨_, hτ⟩⟫ := LinearPMap.adjoint_isFormalAdjoint S.dense₀ _ _
        _ = ⟪U2, d0 τ⟫ := by rw [eτ, LinearIsometryEquiv.inner_map_map]
    · obtain ⟨hv, ev⟩ := d1_of e1 e2 S h1 v
      have A := LinearPMap.adjoint_isFormalAdjoint S.dense₁ ⟨e2 U3, hadj1⟩ ⟨_, hv⟩
      calc ⟪V2, (v : W1)⟫ = ⟪e1 V2, e1 v⟫ := (LinearIsometryEquiv.inner_map_map e1 _ _).symm
        _ = -⟪e1 (d0 ⟨U1, hσ'⟩), e1 v⟫ - ⟪S.d₁† ⟨e2 U3, hadj1⟩, ((⟨_, hv⟩ : S.d₁.domain) : X1)⟫ := by
          rw [← L1, hneg, ← eσ, inner_sub_left, inner_neg_left]
        _ = -⟪d0 ⟨U1, hσ'⟩, v⟫ - ⟪U3, d1 v⟫ := by
          rw [A, ev, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
    · apply e2.injective
      rw [← L2, ← eu]

include h0 h1 in
/-- **The domain of the challenge's Hodge wave operator is `Feec`'s**, through the state map. -/
theorem exists_isHodgeWave_iff (U : W0 × W1 × W2) :
    (∃ V, IsHodgeWave d0 d1 U V) ↔ stateL e0 e1 e2 U ∈ S.wave.domain :=
  ⟨fun ⟨V, hV⟩ => ((isHodgeWave_iff e0 e1 e2 S h0 h1 U V).1 hV).1, fun h =>
    ⟨_, (isHodgeWave_iff e0 e1 e2 S h0 h1 U _).2 ⟨h, (stateL_stateInvL e0 e1 e2 _).symm⟩⟩⟩

include h0 h1 in
/-- **Strong solutions of the challenge are `Feec`'s**, through the state map. -/
theorem isStrongSolution_toFeec {I : Set ℝ} {U : ℝ → W0 × W1 × W2}
    (hU : IsStrongSolution {p | IsHodgeWave d0 d1 p.1 p.2} I U) :
    Evolution.IsStrongSolution S.wave I 0 fun t => stateL e0 e1 e2 (U t) where
  continuousOn := (stateL e0 e1 e2).continuous.comp_continuousOn hU.1
  deriv t ht := by
    obtain ⟨V, hV, hd⟩ := hU.2 t ht
    obtain ⟨h, e⟩ := (isHodgeWave_iff e0 e1 e2 S h0 h1 _ _).1 hV
    refine ⟨stateL e0 e1 e2 V, ?_, ?_⟩
    · rw [← e]; exact LinearPMap.mem_graph _ ⟨_, h⟩
    · rw [Pi.zero_apply, add_zero]
      exact (stateL e0 e1 e2).hasFDerivAt.comp_hasDerivWithinAt t hd

include h0 h1 in
/-- **`Feec`'s strong solutions are strong solutions of the challenge.** -/
theorem isStrongSolution_ofFeec {I : Set ℝ} {X : ℝ → PiLp 2 (W3 X0 X1 X2)}
    (hX : Evolution.IsStrongSolution S.wave I 0 X) :
    IsStrongSolution {p | IsHodgeWave d0 d1 p.1 p.2} I fun t => stateInvL e0 e1 e2 (X t) := by
  refine ⟨(stateInvL e0 e1 e2).continuous.comp_continuousOn hX.continuousOn, fun t ht => ?_⟩
  obtain ⟨v, hv, hd⟩ := hX.deriv t ht
  rw [Pi.zero_apply, add_zero] at hd
  obtain ⟨h, e⟩ := apply_of_mem_graph hv
  refine ⟨stateInvL e0 e1 e2 v, (isHodgeWave_iff e0 e1 e2 S h0 h1 _ _).2 ?_, ?_⟩
  · rw [stateL_stateInvL, stateL_stateInvL]; exact ⟨h, e⟩
  · exact (stateInvL e0 e1 e2).hasFDerivAt.comp_hasDerivWithinAt t hd

end Transfer

/-! ### The vector fields of vector `0`-forms -/

section Fields

variable {Ω : Set (Fin 3 → ℝ)}

/-- `∅`, the index of the coefficient of a `0`-form. -/
def ix0 : FormIdx 3 0 := ⟨∅, by simp⟩

instance : Unique (FormIdx 3 0) where
  default := ix0
  uniq s := Subtype.ext (Finset.card_eq_zero.1 (by exact_mod_cast s.2))

/-- **The vector field** `L²(Ω; Λ⁰ ⊗ ℝ³) ≃ L²(Ω; ℝ³)` of a vector `0`-form. -/
def field0 : L2Vec Ω 0 ≃ₗᵢ[ℝ] L2F ℝ Ω (Fin 3) where
  toFun σ := WithLp.toLp 2 fun a => σ a ix0
  invFun v := WithLp.toLp 2 fun a => WithLp.toLp 2 fun _ => v a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv σ := PiLp.ext fun a => PiLp.ext fun s => by rw [Subsingleton.elim s ix0]
  right_inv v := PiLp.ext fun a => rfl
  norm_map' σ := by
    show ‖(WithLp.toLp 2 fun a => σ a ix0 : L2F ℝ Ω (Fin 3))‖ = ‖σ‖
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_unique]
    rfl

theorem field0_apply (σ : L2Vec Ω 0) (a : Fin 3) : field0 σ a = σ a ix0 := rfl

/-- The entry `a` of a vector field: `(M₀ φ)_i = [i = a] φ`. -/
def mat0 (a : Fin 3) : Matrix (Fin 3) (FormIdx 3 0) ℝ := fun i _ => if i = a then 1 else 0

/-- The entry `a` of a vector, from `Fin 1`. -/
def rowVec (a : Fin 3) : Matrix (Fin 3) (Fin 1) ℝ := fun i _ => if i = a then 1 else 0

theorem ofMatrixCLM_mat0_apply (a : Fin 3) (v : L2Form Ω 0) (i : Fin 3) :
    L2F.ofMatrixCLM (mat0 a) v i = if i = a then v ix0 else 0 := by
  rw [L2F.ofMatrixCLM_apply, Fintype.sum_unique]
  by_cases h : i = a
  · simp [mat0, h]; rfl
  · simp [mat0, h]

theorem field0_eq_sum (σ : L2Vec Ω 0) : field0 σ = ∑ a, L2F.ofMatrixCLM (mat0 a) (σ a) := by
  refine PiLp.ext fun i => ?_
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [ofMatrixCLM_mat0_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

theorem ofMatrix_rowVec_apply (a : Fin 3) (g : Fin 1 → R3 → ℝ) :
    (ConstCoeffOp.ofMatrix (rowVec a) : ConstCoeffOp R3 ℝ _ _).apply g =
      fun i => if i = a then g 0 else 0 := by
  funext i x
  rw [ConstCoeffOp.ofMatrix_apply]
  by_cases h : i = a <;> simp [rowVec, h]

theorem gradOp_rowVec (a : Fin 3) (g : Fin 1 → R3 → ℝ) :
    (gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).apply
        ((ConstCoeffOp.ofMatrix (rowVec a) : ConstCoeffOp R3 ℝ _ _).apply g) =
      (ConstCoeffOp.ofMatrix (rowMat a) : ConstCoeffOp R3 ℝ _ _).apply
        ((gradOp 3 1 : ConstCoeffOp R3 ℝ (Fin 1) (Fin 1 × Fin 3)).apply g) := by
  rw [ofMatrix_rowVec_apply, ofMatrix_rowMat_apply]
  funext p x
  rw [gradOp_apply]
  by_cases h : p.1 = a
  · simp only [h, ite_true]
    rw [gradOp_apply]
  · simp [h]

theorem ofMatrix_mat0_apply (a : Fin 3) (f : FormIdx 3 0 → R3 → ℝ) :
    (ConstCoeffOp.ofMatrix (mat0 a) : ConstCoeffOp R3 ℝ _ _).apply f =
      (ConstCoeffOp.ofMatrix (rowVec a) : ConstCoeffOp R3 ℝ _ _).apply
        ((ConstCoeffOp.ofMatrix (proxyMat 0) : ConstCoeffOp R3 ℝ _ _).apply f) := by
  rw [ofMatrix_rowVec_apply, ofMatrix_proxyMat_zero]
  funext i x
  rw [ConstCoeffOp.ofMatrix_apply, Fintype.sum_unique]
  by_cases h : i = a
  · simp [mat0, h, formExt]; rfl
  · simp [mat0, h]

/-- **The entries of the vector field intertwine `d` and `grad`.** -/
theorem gradOp_mat0 (a : Fin 3) (f : FormIdx 3 0 → R3 → ℝ) :
    (gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).apply
        ((ConstCoeffOp.ofMatrix (mat0 a) : ConstCoeffOp R3 ℝ _ _).apply f) =
      (ConstCoeffOp.ofMatrix (matE a) : ConstCoeffOp R3 ℝ _ _).apply
        ((extDerivOp ℝ 3 0).apply f) := by
  rw [ofMatrix_mat0_apply, gradOp_rowVec, gradOp_proxyMat, ofMatrix_matE_apply]

/-! The transposes extract a row. -/

theorem ofMatrix_mat0_transpose_apply (a : Fin 3) (f : Fin 3 → R3 → ℝ) :
    (ConstCoeffOp.ofMatrix (mat0 a).transpose : ConstCoeffOp R3 ℝ _ _).apply f = fun _ => f a := by
  funext s x
  rw [ConstCoeffOp.ofMatrix_apply, Finset.sum_eq_single a]
  · simp [mat0]
  · intro b _ hb; simp [mat0, hb]
  · simp

theorem ofMatrix_matE_transpose_apply (a : Fin 3) (f : Ix → R3 → ℝ) :
    (ConstCoeffOp.ofMatrix (matE a).transpose : ConstCoeffOp R3 ℝ _ _).apply f =
      fun s => f (a, ix1.symm s) := by
  funext s x
  rw [ConstCoeffOp.ofMatrix_apply, Finset.sum_eq_single (a, ix1.symm s)]
  · simp [matE]
  · rintro ⟨i, b⟩ _ hb
    have : ¬(i = a ∧ s = ix1 b) := fun ⟨h1, h2⟩ => hb (by rw [h1, h2, Equiv.symm_apply_apply])
    simp [matE, this]
  · simp

theorem ofMatrix_matB_transpose_apply (a : Fin 3) (f : Ix → R3 → ℝ) :
    (ConstCoeffOp.ofMatrix (matB a).transpose : ConstCoeffOp R3 ℝ _ _).apply f =
      fun t => sgn3 (ix2.symm t) • f (a, ix2.symm t) := by
  funext t x
  rw [ConstCoeffOp.ofMatrix_apply, Finset.sum_eq_single (a, ix2.symm t)]
  · simp [matB]
  · rintro ⟨i, k⟩ _ hk
    have : ¬(i = a ∧ t = ix2 k) := fun ⟨h1, h2⟩ => hk (by rw [h1, h2, Equiv.symm_apply_apply])
    simp [matB, this]
  · simp

theorem ofMatrix_matE_apply' (a : Fin 3) (f : FormIdx 3 1 → R3 → ℝ) :
    (ConstCoeffOp.ofMatrix (matE a) : ConstCoeffOp R3 ℝ _ _).apply f =
      fun p => if p.1 = a then f (ix1 p.2) else 0 := by
  rw [ofMatrix_matE_apply, ofMatrix_rowMat_apply, ofMatrix_proxyMat_one]
  funext p x
  by_cases h : p.1 = a
  · simp [h, vec1, ix1, f1, formExt]
  · simp [h]

theorem ofMatrix_matB_apply' (a : Fin 3) (f : FormIdx 3 2 → R3 → ℝ) :
    (ConstCoeffOp.ofMatrix (matB a) : ConstCoeffOp R3 ℝ _ _).apply f =
      fun p => if p.1 = a then sgn3 p.2 • f (ix2 p.2) else 0 := by
  funext p x
  rw [ConstCoeffOp.ofMatrix_apply]
  by_cases h : p.1 = a
  · rw [Finset.sum_eq_single (ix2 p.2)]
    · simp [matB, h]
    · intro t _ ht; simp [matB, ht]
    · simp
  · simp [matB, h]

theorem ofMatrix_mat0_mat0T (a : Fin 3) (f : Fin 3 → R3 → ℝ) :
    (ConstCoeffOp.ofMatrix (mat0 a) : ConstCoeffOp R3 ℝ _ _).apply
      ((ConstCoeffOp.ofMatrix (mat0 a).transpose : ConstCoeffOp R3 ℝ _ _).apply f) a = f a := by
  rw [ofMatrix_mat0_transpose_apply]
  funext x
  rw [ConstCoeffOp.ofMatrix_apply, Fintype.sum_unique]
  simp [mat0]

theorem ofMatrix_matE_matET (a : Fin 3) (f : Ix → R3 → ℝ) (j : Fin 3) :
    (ConstCoeffOp.ofMatrix (matE a) : ConstCoeffOp R3 ℝ _ _).apply
      ((ConstCoeffOp.ofMatrix (matE a).transpose : ConstCoeffOp R3 ℝ _ _).apply f) (a, j) =
        f (a, j) := by
  rw [ofMatrix_matE_apply', ofMatrix_matE_transpose_apply]
  simp

/-- **The transposed rows intertwine `grad` with `d`** (the row `a` of `grad f` only depends on
`f a`). -/
theorem extDerivOp_mat0_transpose (a : Fin 3) (f : Fin 3 → R3 → ℝ) :
    (extDerivOp ℝ 3 0).apply
        ((ConstCoeffOp.ofMatrix (mat0 a).transpose : ConstCoeffOp R3 ℝ _ _).apply f) =
      (ConstCoeffOp.ofMatrix (matE a).transpose : ConstCoeffOp R3 ℝ _ _).apply
        ((gradOp 3 3 : ConstCoeffOp R3 ℝ (Fin 3) Ix).apply f) := by
  have h1 := congrArg (fun F => (ConstCoeffOp.ofMatrix (matE a).transpose :
    ConstCoeffOp R3 ℝ _ _).apply F)
      (gradOp_mat0 a ((ConstCoeffOp.ofMatrix (mat0 a).transpose : ConstCoeffOp R3 ℝ _ _).apply f))
  rw [ofMatrix_matE_transpose_apply, ofMatrix_matE_transpose_apply, ofMatrix_matE_apply'] at h1
  rw [ofMatrix_matE_transpose_apply]
  funext s
  have h2 := congrFun h1 s
  simp only [ite_true, Equiv.apply_symm_apply] at h2
  rw [← h2]
  funext x
  rw [gradOp_apply, gradOp_apply, ofMatrix_mat0_mat0T]

/-- **The transposed rows intertwine `curl` with `d`** (the row `a` of `curl f` only depends on
the row `a` of `f`). -/
theorem extDerivOp_matE_transpose (a : Fin 3) (f : Ix → R3 → ℝ) :
    (extDerivOp ℝ 3 1).apply
        ((ConstCoeffOp.ofMatrix (matE a).transpose : ConstCoeffOp R3 ℝ _ _).apply f) =
      (ConstCoeffOp.ofMatrix (matB a).transpose : ConstCoeffOp R3 ℝ _ _).apply
        ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply f) := by
  have h1 := congrArg (fun F => (ConstCoeffOp.ofMatrix (matB a).transpose :
    ConstCoeffOp R3 ℝ _ _).apply F)
      (curlOp_matE a ((ConstCoeffOp.ofMatrix (matE a).transpose : ConstCoeffOp R3 ℝ _ _).apply f))
  rw [ofMatrix_matB_transpose_apply, ofMatrix_matB_transpose_apply, ofMatrix_matB_apply'] at h1
  rw [ofMatrix_matB_transpose_apply]
  funext t
  have h2 := congrFun h1 t
  simp only [ite_true, Equiv.apply_symm_apply, smul_smul, sgn3_mul_self, one_smul] at h2
  rw [← h2]
  congr 1
  funext x
  rw [curlOp_apply, curlOp_apply, ofMatrix_matE_matET, ofMatrix_matE_matET]

/-! The transposes on `L²` fields. -/

theorem ofMatrixCLM_mat0_transpose (σ : L2Vec Ω 0) (a : Fin 3) :
    L2F.ofMatrixCLM (mat0 a).transpose (field0 σ) = σ a := by
  refine PiLp.ext fun s => ?_
  rw [L2F.ofMatrixCLM_apply, Finset.sum_eq_single a]
  · simp [mat0, Subsingleton.elim s ix0]; rfl
  · intro b _ hb; simp [mat0, hb]
  · simp

theorem ofMatrixCLM_matE_transpose (u : L2Vec Ω 1) (a : Fin 3) :
    L2F.ofMatrixCLM (matE a).transpose (fieldE u) = u a := by
  refine PiLp.ext fun s => ?_
  rw [L2F.ofMatrixCLM_apply, Finset.sum_eq_single (a, ix1.symm s)]
  · simp only [Matrix.transpose_apply, matE, Equiv.apply_symm_apply, and_self, ite_true,
      one_smul]
    show u a (ix1 (ix1.symm s)) = u a s
    rw [Equiv.apply_symm_apply]
  · rintro ⟨i, b⟩ _ hb
    have : ¬(i = a ∧ s = ix1 b) := fun ⟨h1, h2⟩ => hb (by rw [h1, h2, Equiv.symm_apply_apply])
    simp [matE, this]
  · simp

theorem ofMatrixCLM_matB_transpose (ρ : L2Vec Ω 2) (a : Fin 3) :
    L2F.ofMatrixCLM (matB a).transpose (fieldB ρ) = ρ a := by
  refine PiLp.ext fun t => ?_
  rw [L2F.ofMatrixCLM_apply, Finset.sum_eq_single (a, ix2.symm t)]
  · simp only [Matrix.transpose_apply, matB, Equiv.apply_symm_apply, and_self, ite_true]
    show sgn3 (ix2.symm t) • (sgn3 (ix2.symm t) • ρ a (ix2 (ix2.symm t))) = ρ a t
    rw [smul_smul, sgn3_mul_self, one_smul, Equiv.apply_symm_apply]
  · rintro ⟨i, k⟩ _ hk
    have : ¬(i = a ∧ t = ix2 k) := fun ⟨h1, h2⟩ => hk (by rw [h1, h2, Equiv.symm_apply_apply])
    simp [matB, this]
  · simp

theorem pair_sum {X Y : Type*} [AddCommMonoid X] [AddCommMonoid Y] (x : Fin 3 → X)
    (y : Fin 3 → Y) : (∑ a, x a, ∑ a, y a) = ∑ a, (x a, y a) := by
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

/-- **The componentwise `d̊` on vector `0`-forms is the minimal gradient.** -/
theorem mem_graph_grad_iff (hΩ : IsOpen Ω) (x : L2Vec Ω 0) (y : L2Vec Ω 1) :
    (x, y) ∈ (vecOpC (n := 3) (dMin Ω 0)).graph ↔ (field0 x, fieldE y) ∈ (gradCurl ℝ hΩ).d₀.graph := by
  rw [gradCurl_d₀, mem_graph_vecOp_iff, dMin_eq]
  constructor
  · intro h
    rw [field0_eq_sum, fieldE_eq_sum, pair_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨ha, e⟩ := apply_of_mem_graph (h a)
    obtain ⟨hm, e'⟩ := ConstCoeffOp.minimal_ofMatrixCLM_of_comm hΩ (A := gradOp 3 3)
      (fun f _ => gradOp_mat0 a f) ⟨_, ha⟩
    rw [← e, ← e']
    exact LinearPMap.mem_graph _ ⟨_, hm⟩
  · intro h a
    obtain ⟨hd, e⟩ := apply_of_mem_graph h
    obtain ⟨hm, e'⟩ := ConstCoeffOp.minimal_ofMatrixCLM_of_comm hΩ (A := extDerivOp ℝ 3 0)
      (B := gradOp 3 3) (M := (mat0 a).transpose) (M' := (matE a).transpose)
      (fun f _ => extDerivOp_mat0_transpose a f) ⟨_, hd⟩
    have := LinearPMap.mem_graph _ ⟨_, hm⟩
    rw [e', e, ofMatrixCLM_matE_transpose] at this
    simpa only [ofMatrixCLM_mat0_transpose] using this

/-- **The componentwise `d̊` on vector `1`-forms is the minimal row-wise curl.** -/
theorem mem_graph_curl_iff (hΩ : IsOpen Ω) (x : L2Vec Ω 1) (y : L2Vec Ω 2) :
    (x, y) ∈ (vecOpC (n := 3) (dMin Ω 1)).graph ↔ (fieldE x, fieldB y) ∈ (gradCurl ℝ hΩ).d₁.graph := by
  rw [gradCurl_d₁]
  constructor
  · intro h
    obtain ⟨hx, e⟩ := apply_of_mem_graph h
    have := fieldE_mem_curl_minimal hΩ ⟨x, hx⟩
    rwa [e] at this
  · intro h
    rw [mem_graph_vecOp_iff, dMin_eq]
    intro a
    obtain ⟨hd, e⟩ := apply_of_mem_graph h
    obtain ⟨hm, e'⟩ := ConstCoeffOp.minimal_ofMatrixCLM_of_comm hΩ (A := extDerivOp ℝ 3 1)
      (B := curlOp 3) (M := (matE a).transpose) (M' := (matB a).transpose)
      (fun f _ => extDerivOp_matE_transpose a f) ⟨_, hd⟩
    have := LinearPMap.mem_graph _ ⟨_, hm⟩
    rw [e', e, ofMatrixCLM_matB_transpose] at this
    simpa only [ofMatrixCLM_matE_transpose] using this

end Fields

/-! ### The grad–curl system on an open set -/

section GradCurl

variable {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω)

/-- The challenge's grad–curl wave operator on `Ω`. -/
abbrev gcWave :=
  IsHodgeWave (vecOpC (n := 3) (dMin Ω 0)) (vecOpC (n := 3) (dMin Ω 1))

/-- The state map of the grad–curl system. -/
abbrev gcState : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2 →L[ℝ]
    PiLp 2 (W3 (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)) :=
  stateL field0 fieldE fieldB

include hΩ in
theorem gcWave_iff (U V : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :
    gcWave U V ↔ ∃ h : gcState U ∈ (gradCurl ℝ hΩ).wave.domain,
      (gradCurl ℝ hΩ).wave ⟨_, h⟩ = gcState V :=
  isHodgeWave_iff field0 fieldE fieldB _ (mem_graph_grad_iff hΩ) (mem_graph_curl_iff hΩ) U V

theorem gc_orbit {U : ℝ → L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2}
    (hU : IsStrongSolution {p | gcWave (Ω := Ω) p.1 p.2} (Ici 0) U) {t : ℝ} (ht : 0 ≤ t) :
    gcState (U t) = (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t (gcState (U 0)) := by
  obtain ⟨V, hV, -⟩ := hU.2 0 le_rfl
  obtain ⟨hd, -⟩ := (gcWave_iff hΩ _ _).1 hV
  exact (gradCurl ℝ hΩ).toHilbertComplex.eq_waveGroup_of_isStrongSolution hd rfl
    (isStrongSolution_toFeec field0 fieldE fieldB _ (mem_graph_grad_iff hΩ)
      (mem_graph_curl_iff hΩ) (hU.mono_Icc t)) ⟨ht, le_rfl⟩

include hΩ in
theorem gc_exists {U₀ V : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2} (hV : gcWave U₀ V) :
    ∃ U, U 0 = U₀ ∧ IsStrongSolution {p | gcWave (Ω := Ω) p.1 p.2} (Ici 0) U := by
  obtain ⟨hd, -⟩ := (gcWave_iff hΩ _ _).1 hV
  refine ⟨fun t => stateInvL field0 fieldE fieldB
      ((gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t (gcState U₀)), ?_,
    isStrongSolution_Ici fun T => isStrongSolution_ofFeec field0 fieldE fieldB _
      (mem_graph_grad_iff hΩ) (mem_graph_curl_iff hΩ)
      ((gradCurl ℝ hΩ).toHilbertComplex.isStrongSolution_waveGroup hd T)⟩
  simp only
  rw [show (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S 0 (gcState U₀) = gcState U₀ by simp]
  exact stateInvL_stateL _ _ _ U₀

include hΩ in
theorem gc_stationary (U₀ : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :
    gcState U₀ ∈ (gradCurl ℝ hΩ).stationary ↔ gcWave U₀ 0 := by
  rw [gcWave_iff hΩ, map_zero]
  constructor
  · intro h; exact (gradCurl ℝ hΩ).wave_eq_zero_of_mem_stationary h
  · rintro ⟨h, e⟩; exact (gradCurl ℝ hΩ).mem_stationary_of_wave_eq_zero ⟨_, h⟩ e

omit hΩ in
theorem gc_mem_iff (S₁ : Submodule ℝ (L2Vec Ω 1)) (S₂ : Submodule ℝ (L2Vec Ω 2))
    (W : L2Vec Ω 0 × L2Vec Ω 1 × L2Vec Ω 2) :
    gcState W ∈ totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3)))
      (S₁.map (fieldE (Ω := Ω)).toLinearEquiv.toLinearMap)
      (S₂.map (fieldB (Ω := Ω)).toLinearEquiv.toLinearMap)) ↔
      W.1 = 0 ∧ W.2.1 ∈ S₁ ∧ W.2.2 ∈ S₂ := by
  rw [mem_totalSub_family3]
  show -field0 W.1 ∈ (⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3))) ∧
    fieldE W.2.1 ∈ S₁.map (fieldE (Ω := Ω)).toLinearEquiv.toLinearMap ∧
    fieldB W.2.2 ∈ S₂.map (fieldB (Ω := Ω)).toLinearEquiv.toLinearMap ↔ _
  rw [Submodule.mem_bot, neg_eq_zero, LinearIsometryEquiv.map_eq_zero_iff]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · exact ⟨fun ⟨u, hu, e⟩ => fieldE.injective e ▸ hu, fun h => ⟨_, h, rfl⟩⟩
  · exact ⟨fun ⟨u, hu, e⟩ => fieldB.injective e ▸ hu, fun h => ⟨_, h, rfl⟩⟩

end GradCurl

/-! ### The theorem -/

theorem box_stationary_of {a ℓ : Fin 3 → ℝ} (hℓ : ∀ i, 0 < ℓ i) :
    let L := IsHodgeWave (vecOp fun _ => dMin (box a ℓ) 0) (vecOp fun _ => dMin (box a ℓ) 1)
    (∀ U₀ V, L U₀ V → ∃ U, U 0 = U₀ ∧ IsStrongSolution {p | L p.1 p.2} (Ici 0) U) ∧
    ∀ (S₁ : Submodule ℝ (L2Vec (box a ℓ) 1)) (S₂ : Submodule ℝ (L2Vec (box a ℓ) 2)),
      (∀ u ∈ S₁, IsTSD (mat1 u)) → (∀ ρ ∈ S₂, IsTSD (mat2 ρ)) → ∀ U,
        IsStrongSolution {p | L p.1 p.2} (Ici 0) U →
        ((∀ t ≥ 0, (U t).1 = 0 ∧ (U t).2.1 ∈ S₁ ∧ (U t).2.2 ∈ S₂) ↔
          ((U 0).1 = 0 ∧ (U 0).2.1 ∈ S₁ ∧ (U 0).2.2 ∈ S₂) ∧ L (U 0) 0) := by
  intro L
  have hΩ : IsOpen (box a ℓ) := Feec.Models.Box.isOpen_openBox a ℓ
  refine ⟨fun U₀ V hV => gc_exists hΩ hV, fun S₁ S₂ hS₁ hS₂ U hU => ?_⟩
  show _ ↔ _ ∧ gcWave (U 0) 0
  have h1' : S₁.map (fieldE (Ω := box a ℓ)).toLinearEquiv.toLinearMap ≤ tsd (box a ℓ) := by
    rintro _ ⟨u, hu, rfl⟩
    exact (isTSD_iff _).1 (hS₁ u hu)
  have h2' : S₂.map (fieldB (Ω := box a ℓ)).toLinearEquiv.toLinearMap ≤ tsd (box a ℓ) := by
    rintro _ ⟨ρ, hρ, rfl⟩
    exact (isTSD_iff _).1 (hS₂ ρ hρ)
  have key := Feec.Counterexamples.BoxStationary.forward_iff_stationary_box hℓ h1' h2'
    (gcState (U 0))
  rw [← gc_stationary hΩ, ← gc_mem_iff S₁ S₂]
  refine Iff.trans ?_ key
  refine forall₂_congr fun t ht => ?_
  exact (gc_mem_iff S₁ S₂ (U t)).symm.trans
    (iff_of_eq (congrArg (fun x => x ∈ _) (gc_orbit hΩ hU ht)))

end FEEC
