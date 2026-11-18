module

public import Solution.Complex
public import Feec.Models.Cube.InhomogeneousLeapfrog

/-!
# The fully discrete Hodge wave equation on a window of a subcomplex

A Hilbert complex of the challenge is a `Feec` complex on `ComplexShape.up ℤ`
(`HilbertComplex.toFeec`, the converse of `HilbertComplex.ofFeec`), two complexes with the same
differentials `d k (k + 1)` are equal (`HilbertComplex.ext_of_d`), and the total differential of a
window is that of the `Feec` window (`totalD_eq`). The forms of the window whose components lie in
a subcomplex `Vₕ` are the image of the discrete state space `DState` of the `Feec` window of `Vₕ`
(`mem_iff_exists_dEmb`), on which the challenge's `𝐝` is `discreteD` (`dApply_dEmb`), its wave
form that of `discreteWave` (`waveForm_dEmb`), and a strong solution of the Hodge wave equation
solves the weak form of the scheme (`inner_of_mem_graph_wave`, the adjoint `𝐝*` being a formal
adjoint of `𝐝`). So the Crank–Nicolson and leapfrog steps of the challenge with homogeneous
boundary conditions (trial and test space `Vₕ`, no boundary data) are `Feec`'s Dirichlet steps with
`V̊ₕ = Vₕ`, and `wave_error` is the abstract error estimate of
`Feec.Models.Cube.Inhomogeneous.norm_cn_error_le` and
`Feec.Models.Cube.Inhomogeneous.norm_leapfrog_error_le_of_sub_mem` for the comparison fields
`P U(tₙ)` of a linear map `P` into `Vₕ`: `‖u_K − U(K Δt)‖ ≤ ‖u₀ − U(0)‖ + 3 ε + T (L₃ Δt² / 2 + 2 ε)`
and, under the CFL condition, `(1 − c) ‖u_K − U(K Δt)‖ ≤ ‖u₀ − U(0)‖ + ‖u₁ − U(Δt)‖ + 3 ε +
T (L₃ Δt² / 3 + 4 ε)`, where `ε` bounds `P U - U`, `𝐝 (P U - U)` and the time increments of
`P U - U` per unit time.

## References

* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter LinearPMap Feec.Models.Cube.Inhomogeneous

@[expose] public noncomputable section

namespace FEEC

namespace HilbertComplex

variable {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)]
  [∀ i, CompleteSpace (W i)]

/-- A Hilbert complex of the challenge as a `Feec` complex on `ComplexShape.up ℤ`. -/
def toFeec (H : HilbertComplex ℝ W) : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) W where
  d := H.d
  shape := H.shape
  dense := H.dense
  closed := H.closed
  mapsTo := H.mapsTo
  d_comp_d := H.d_comp_d

/-- **Two Hilbert complexes with the same differentials `d k (k + 1)` are equal** (the others
vanish). -/
theorem ext_of_d {H H' : HilbertComplex ℝ W} (h : ∀ k, H.d k (k + 1) = H'.d k (k + 1)) :
    H = H' := by
  have hd : H.d = H'.d := by
    funext i j
    by_cases hij : i + 1 = j
    · subst hij; exact h i
    · rw [H.shape i j hij, H'.shape i j hij]
  cases H
  cases H'
  cases hd
  rfl

variable (H : HilbertComplex ℝ W) (a : ℤ) (m : ℕ)

theorem totalD_eq : H.totalD a m = (H.toFeec.window a m).totalD := by
  refine LinearPMap.ext rfl fun x hx hy => ?_
  ext j
  rw [Feec.HilbertComplex.totalD_apply]
  rfl

theorem dense_totalD_domain : Dense ((H.totalD a m).domain : Set (Total W a m)) := by
  rw [totalD_eq]
  exact (H.toFeec.window a m).dense_totalDomain

/-- `d i j = 0` unless `j = i + 1`. -/
theorem apply_eq_zero {i j : ℤ} (h : ¬ i + 1 = j) (x : (H.d i j).domain) : H.d i j x = 0 := by
  have hz : ∀ (T : W i →ₗ.[ℝ] W j), T = 0 → ∀ y : T.domain, T y = 0 := by
    rintro T rfl y; rfl
  exact hz _ (H.shape i j h) x

/-- **A componentwise bound of the total differential**: if `‖d (a + i) (a + i + 1) xᵢ‖ ≤ βᵢ`,
then `‖𝐝 x‖ ≤ m Σᵢ βᵢ`. -/
theorem norm_totalD_le {x : Total W a m} (hx : x ∈ (H.totalD a m).domain) {β : Fin m → ℝ}
    (hβ0 : ∀ i, 0 ≤ β i)
    (hβ : ∀ i j : Fin m, (i : ℕ) + 1 = j → ‖H.d (a + (i : ℕ)) (a + (j : ℕ)) ⟨x i, hx i j⟩‖ ≤ β i) :
    ‖H.totalD a m ⟨x, hx⟩‖ ≤ m * ∑ i, β i := by
  refine (PiLp.norm_le_sum_norm _).trans ?_
  have hj : ∀ j : Fin m, ‖(H.totalD a m ⟨x, hx⟩) j‖ ≤ ∑ i, β i := fun j => by
    change ‖∑ i : Fin m, H.d (a + (i : ℕ)) (a + (j : ℕ)) ⟨x i, hx i j⟩‖ ≤ _
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    by_cases hij : (i : ℕ) + 1 = j
    · exact hβ i j hij
    · rw [H.apply_eq_zero (fun h => hij (by omega)), norm_zero]
      exact hβ0 i
  calc ∑ j, ‖(H.totalD a m ⟨x, hx⟩) j‖ ≤ ∑ _j : Fin m, ∑ i, β i :=
        Finset.sum_le_sum fun j _ => hj j
    _ = m * ∑ i, β i := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A subcomplex of the challenge as a `Feec` subcomplex (reducible, so that instances on `Vⁱ`
apply to its spaces). -/
abbrev Subcomplex.toFeec {H : HilbertComplex ℝ W} (S : H.Subcomplex) : H.toFeec.Subcomplex :=
  ⟨S.V, S.le_domain, S.mapsTo⟩

variable {H a m} (S : H.Subcomplex)

/-- The discrete states of the window of `S`. -/
abbrev WState := DState (S.toFeec.window a m)

/-- **The forms of the window with components in `S` are the discrete states.** -/
theorem mem_iff_exists_dEmb {x : Total W a m} :
    (∀ i : Fin m, x i ∈ S.V (a + (i : ℕ))) ↔ ∃ v : WState (a := a) (m := m) S, x = dEmb _ v := by
  constructor
  · intro hx
    exact ⟨WithLp.toLp 2 fun i => ⟨x i, hx i⟩, rfl⟩
  · rintro ⟨v, rfl⟩ i
    exact (v i).2

theorem dEmb_mem_domain (v : WState (a := a) (m := m) S) :
    (dEmb _ v : Total W a m) ∈ (H.totalD a m).domain :=
  dEmb_mem_totalDomain (S.toFeec.window a m) v

theorem totalD_apply_eq {x : Total W a m} (h1 : x ∈ (H.totalD a m).domain)
    (h2 : x ∈ (H.toFeec.window a m).totalD.domain) :
    H.totalD a m ⟨x, h1⟩ = (H.toFeec.window a m).totalD ⟨x, h2⟩ := by
  ext j
  rw [Feec.HilbertComplex.totalD_apply]
  rfl

theorem totalD_dEmb' (v : WState (a := a) (m := m) S) :
    H.totalD a m ⟨dEmb _ v, dEmb_mem_domain S v⟩ = dEmb _ (discreteD _ v) := by
  rw [← totalD_dEmb (S.toFeec.window a m) v]
  exact totalD_apply_eq _ _

/-- **The challenge's `𝐝` on the discrete states is `discreteD`.** -/
theorem dApply_dEmb (v : WState (a := a) (m := m) S) :
    H.dApply a m (dEmb _ v) = dEmb _ (discreteD _ v) := by
  rw [dApply, dite_eq_left (dEmb_mem_domain S v), totalD_dEmb']

theorem dApply_eq {x : Total W a m} (hx : x ∈ (H.totalD a m).domain) :
    H.dApply a m x = H.totalD a m ⟨x, hx⟩ := by
  rw [dApply, dite_eq_left hx]

/-- **A strong solution of the Hodge wave equation solves the weak form of the scheme**: if
`(U, U') ∈ graph (𝐝 - 𝐝*)`, then `⟪U', v⟫ = ⟪𝐝 U, v⟫ - ⟪U, 𝐝 v⟫` on the discrete states. -/
theorem inner_of_mem_graph_wave {U U' : Total W a m} (hU : (U, U') ∈ (H.wave a m).graph) :
    ∃ hD : U ∈ (H.totalD a m).domain, ∀ v : WState (a := a) (m := m) S,
      ⟪U', dEmb _ v⟫ = ⟪H.totalD a m ⟨U, hD⟩, dEmb _ v⟫ - ⟪U, dEmb _ (discreteD _ v)⟫ := by
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hU
  have hy1' : (y : Total W a m) = U := hy1
  have hD : U ∈ (H.totalD a m).domain := hy1' ▸ y.2.1
  have hD' : U ∈ (H.totalD a m)†.domain := hy1' ▸ y.2.2
  refine ⟨hD, fun v => ?_⟩
  have e : U' = H.totalD a m ⟨U, hD⟩ - (H.totalD a m)† ⟨U, hD'⟩ := by
    have hy2' : H.wave a m y = U' := hy2
    rw [← hy2']
    calc H.wave a m y = H.totalD a m ⟨(y : Total W a m), y.2.1⟩ -
          (H.totalD a m)† ⟨(y : Total W a m), y.2.2⟩ := rfl
      _ = _ := by congr 2 <;> exact Subtype.ext hy1'
  have h2 := LinearPMap.adjoint_isFormalAdjoint (H.dense_totalD_domain a m) ⟨U, hD'⟩
    ⟨dEmb _ v, dEmb_mem_domain S v⟩
  rw [totalD_dEmb'] at h2
  rw [e, inner_sub_left, h2]

open Classical in
/-- The discrete state of a form of the window with components in `S` (`0` otherwise). -/
def lift (x : Total W a m) : WState (a := a) (m := m) S :=
  WithLp.toLp 2 fun i => if h : x i ∈ S.V (a + (i : ℕ)) then ⟨x i, h⟩ else 0

theorem dEmb_lift {x : Total W a m} (hx : ∀ i : Fin m, x i ∈ S.V (a + (i : ℕ))) :
    dEmb _ (lift S x) = x :=
  PiLp.ext fun i => by
    rw [dEmb_apply, lift, PiLp.toLp_apply, dite_eq_left (hx i)]

variable [∀ i, FiniteDimensional ℝ (S.V i)]

/-- **The challenge's wave form on the discrete states is that of `discreteWave`.** -/
theorem waveForm_dEmb (v w : WState (a := a) (m := m) S) :
    H.waveForm a m (dEmb _ v) (dEmb _ w) = ⟪discreteWave _ v, w⟫ := by
  rw [waveForm, dApply_dEmb, dApply_dEmb, inner_discreteWave, inner_dEmb, inner_dEmb]

/-- **The Crank–Nicolson step with homogeneous boundary conditions** of the challenge on the forms
of the window with components in `S` is `Feec`'s Dirichlet step with `V̊ₕ = Vₕ`. -/
theorem isDirichletCNStep_of {Δt : ℝ} {u u' : Total W a m}
    (h : H.IsCNStep a m {x | ∀ i : Fin m, x i ∈ S.V (a + (i : ℕ))}
      {x | ∀ i : Fin m, x i ∈ S.V (a + (i : ℕ))} Δt 0 u u')
    (hu : ∀ i : Fin m, u i ∈ S.V (a + (i : ℕ))) :
    Feec.TimeStepping.IsDirichletCNStep ⊤ (discreteWave (S.toFeec.window a m)) (Δt / 2) 0 0
      (lift S u) (lift S u') := by
  refine ⟨Submodule.mem_top, fun v _ => ?_⟩
  have hv := h.2.2 (dEmb _ v) fun i => (v i).2
  rw [← dEmb_lift S hu, ← dEmb_lift S h.1, ← _root_.map_sub, ← _root_.map_add, inner_dEmb, waveForm_dEmb] at hv
  rw [hv, inner_zero_left, add_zero]

/-- **The leapfrog step with homogeneous boundary conditions** of the challenge is `Feec`'s
Dirichlet leapfrog step with `V̊ₕ = Vₕ`. -/
theorem isDirichletLeapfrogStep_of {Δt : ℝ} {u u' u'' : Total W a m}
    (h : H.IsLeapfrogStep a m {x | ∀ i : Fin m, x i ∈ S.V (a + (i : ℕ))}
      {x | ∀ i : Fin m, x i ∈ S.V (a + (i : ℕ))} Δt 0 u u' u'')
    (hu : ∀ i : Fin m, u i ∈ S.V (a + (i : ℕ))) (hu' : ∀ i : Fin m, u' i ∈ S.V (a + (i : ℕ))) :
    Feec.TimeStepping.IsDirichletLeapfrogStep ⊤ (discreteWave (S.toFeec.window a m)) Δt 0
      (lift S u) (lift S u') (lift S u'') := by
  refine ⟨Submodule.mem_top, fun v _ => ?_⟩
  have hv := h.2.2 (dEmb _ v) fun i => (v i).2
  rwa [← dEmb_lift S hu, ← dEmb_lift S hu', ← dEmb_lift S h.1, ← _root_.map_sub, inner_dEmb,
    waveForm_dEmb] at hv

/-- **Crank–Nicolson and leapfrog with homogeneous boundary conditions on a window of a
subcomplex**, from comparison fields `P U(t)` (`P` linear into `Vₕ`) with `‖P U - U‖`,
`‖𝐝 (P U - U)‖` at most `ε` and the increments of `P U - U` at most `ε |t' - t|` on `[0, T]`,
for a strong solution `U` of the Hodge wave equation, `C³` in time with `‖U'''‖ ≤ L₃` on
`[0, T]`: Crank–Nicolson iterates from any `u₀ ∈ Xₕ` have
`‖u_K - U(K Δt)‖ ≤ ‖u₀ - U(0)‖ + 3 ε + T (L₃ Δt² / 2 + 2 ε)`, and under the CFL condition
`2 Δt ‖𝐝 x‖ ≤ c ‖x‖` on `Xₕ`, `0 ≤ c < 1`, leapfrog iterates from any `u₀, u₁ ∈ Xₕ` have
`(1 - c) ‖u_K - U(K Δt)‖ ≤ ‖u₀ - U(0)‖ + ‖u₁ - U(Δt)‖ + 3 ε + T (L₃ Δt² / 3 + 4 ε)`. -/
theorem wave_error (P : Total W a m →ₗ[ℝ] Total W a m)
    (hP : ∀ x (i : Fin m), P x i ∈ S.V (a + (i : ℕ))) {T L₃ ε Δt : ℝ} (hΔt : 0 < Δt)
    {U U₁ U₂ U₃ : ℝ → Total W a m}
    (hU : ∀ t, HasDerivAt U (U₁ t) t ∧ HasDerivAt U₁ (U₂ t) t ∧ HasDerivAt U₂ (U₃ t) t)
    (hU' : ∀ t ∈ Icc 0 T, ‖U₃ t‖ ≤ L₃ ∧ (U t, U₁ t) ∈ (H.wave a m).graph)
    (h1 : ∀ t ∈ Icc 0 T, ‖P (U t) - U t‖ ≤ ε)
    (h2 : ∀ t ∈ Icc 0 T, ‖H.dApply a m (P (U t)) - H.dApply a m (U t)‖ ≤ ε)
    (h3 : ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, ‖(P (U t') - U t') - (P (U t) - U t)‖ ≤ ε * |t' - t|)
    {K : ℕ} (hK : K * Δt ≤ T) (u : ℕ → Total W a m) :
    ((∀ k < K, H.IsCNStep a m {x | ∀ i : Fin m, x i ∈ S.V (a + (i : ℕ))}
        {x | ∀ i : Fin m, x i ∈ S.V (a + (i : ℕ))} Δt 0 (u k) (u (k + 1))) →
      (∀ i : Fin m, u 0 i ∈ S.V (a + (i : ℕ))) →
      ‖u K - U (K * Δt)‖ ≤ ‖u 0 - U 0‖ + 3 * ε + T * (L₃ * Δt ^ 2 / 2 + 2 * ε)) ∧
    ∀ c : ℝ, 0 ≤ c → c < 1 →
      (∀ x, (∀ i : Fin m, x i ∈ S.V (a + (i : ℕ))) → 2 * Δt * ‖H.dApply a m x‖ ≤ c * ‖x‖) →
      (∀ k, k + 2 ≤ K → H.IsLeapfrogStep a m {x | ∀ i : Fin m, x i ∈ S.V (a + (i : ℕ))}
        {x | ∀ i : Fin m, x i ∈ S.V (a + (i : ℕ))} Δt 0 (u k) (u (k + 1)) (u (k + 2))) →
      (∀ i : Fin m, u 0 i ∈ S.V (a + (i : ℕ))) → (∀ i : Fin m, u 1 i ∈ S.V (a + (i : ℕ))) →
      (1 - c) * ‖u K - U (K * Δt)‖ ≤
        ‖u 0 - U 0‖ + ‖u 1 - U Δt‖ + 3 * ε + T * (L₃ * Δt ^ 2 / 3 + 4 * ε) := by
  set S' := S.toFeec.window a m
  have hT0 : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg K) hΔt.le).trans hK
  -- the setting of the abstract estimates
  have hemb : ∀ x y : WState (a := a) (m := m) S, ⟪dEmb S' x, dEmb S' y⟫ = ⟪x, y⟫ :=
    inner_dEmb S'
  have hA : ∀ x y, ⟪discreteWave S' x, y⟫ = ⟪discreteD S' x, y⟫ - ⟪x, discreteD S' y⟫ :=
    inner_discreteWave S'
  have hD₀ : ∀ v ∈ (⊤ : Submodule ℝ (WState (a := a) (m := m) S)),
      discreteD S' v ∈ (⊤ : Submodule ℝ (WState (a := a) (m := m) S)) :=
    fun _ _ => Submodule.mem_top
  have hDD : ∀ v ∈ (⊤ : Submodule ℝ (WState (a := a) (m := m) S)),
      discreteD S' (discreteD S' v) = 0 := fun v _ => discreteD_discreteD S' v
  set DU : ℝ → Total W a m := fun t => H.dApply a m (U t)
  have hweak : ∀ t ∈ Icc 0 T, ∀ v ∈ (⊤ : Submodule ℝ (WState (a := a) (m := m) S)),
      ⟪U₁ t, dEmb S' v⟫ = ⟪DU t, dEmb S' v⟫ - ⟪U t, dEmb S' (discreteD S' v)⟫ := fun t ht v _ => by
    obtain ⟨hD, h⟩ := inner_of_mem_graph_wave S (hU' t ht).2
    rw [h v, show DU t = H.totalD a m ⟨U t, hD⟩ from dApply_eq hD]
  set w : ℕ → WState (a := a) (m := m) S := fun k => lift S (P (U (k * Δt)))
  have hw : ∀ k, dEmb S' (w k) = P (U (k * Δt)) := fun k => dEmb_lift S (hP _)
  have hmem : ∀ k : ℕ, (k : ℝ) * Δt ≤ T → (k : ℝ) * Δt ∈ Icc 0 T := fun k hk =>
    ⟨mul_nonneg (Nat.cast_nonneg k) hΔt.le, hk⟩
  have hA1 : ∀ k : ℕ, (k : ℝ) * Δt ≤ T → ‖dEmb S' (w k) - U (k * Δt)‖ ≤ ε := fun k hk => by
    rw [hw]; exact h1 _ (hmem k hk)
  have hA2 : ∀ k : ℕ, (k : ℝ) * Δt ≤ T → ‖dEmb S' (discreteD S' (w k)) - DU (k * Δt)‖ ≤ ε :=
    fun k hk => by rw [← dApply_dEmb, hw]; exact h2 _ (hmem k hk)
  have hA3 : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * Δt ≤ T →
      ‖(dEmb S' (w (k + 1)) - U ((k + 1 : ℕ) * Δt)) - (dEmb S' (w k) - U (k * Δt))‖ ≤
        ε * Δt := fun k hk => by
    have hk' : (k : ℝ) * Δt ≤ T :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hΔt.le).trans hk
    rw [hw, hw]
    refine (h3 _ (hmem k hk') _ (hmem (k + 1) hk)).trans_eq ?_
    rw [show ((k + 1 : ℕ) : ℝ) * Δt - k * Δt = Δt by push_cast; ring, abs_of_pos hΔt]
  have hε : 0 ≤ ε := (norm_nonneg _).trans (h1 0 ⟨le_rfl, hT0⟩)
  have hU0 : ‖dEmb S' (w 0) - U 0‖ ≤ ε := by simpa using hA1 0 (by simpa using hT0)
  have hU1 : ∀ i, ∀ x, (∀ j : Fin m, x j ∈ S.V (a + (j : ℕ))) → ‖dEmb S' (lift S x) - U i‖ =
      ‖x - U i‖ := fun i x hx => by rw [dEmb_lift S hx]
  refine ⟨fun hstep hu0 => ?_, fun c hc0 hc1 hcfl hstep hu0 hu1 => ?_⟩
  · -- Crank–Nicolson
    have hu : ∀ k ≤ K, ∀ i : Fin m, u k i ∈ S.V (a + (i : ℕ)) := by
      intro k hk
      rcases k with _ | k
      · exact hu0
      · exact (hstep k hk).1
    have key := norm_cn_error_le (V₀ := ⊤) (g := fun _ => 0) (u := fun k => lift S (u k)) hemb
      hD₀ hDD hA hΔt (fun t _ => ((hU t).1).hasDerivWithinAt)
      (fun t _ => ((hU t).2.1).hasDerivWithinAt) (fun t _ => ((hU t).2.2).hasDerivWithinAt)
      (fun t ht => (hU' t ht).1) hweak hA1 hA2 hA3 hK
      (fun k hk => isDirichletCNStep_of S (hstep k hk) (hu k hk.le))
      (fun _ _ => Submodule.mem_top) Submodule.mem_top
    obtain ⟨-, -, -, -, hfin⟩ := key
    rw [dEmb_lift S (hu K le_rfl)] at hfin
    have h0 : ‖lift S (u 0) - w 0‖ ≤ ‖u 0 - U 0‖ + ε := by
      rw [← norm_emb hemb, _root_.map_sub, dEmb_lift S hu0]
      calc ‖u 0 - dEmb S' (w 0)‖ ≤ ‖u 0 - U 0‖ + ‖U 0 - dEmb S' (w 0)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by rw [norm_sub_rev (U 0)]; linarith
    linarith
  · -- leapfrog
    have hu : ∀ k ≤ K, ∀ i : Fin m, u k i ∈ S.V (a + (i : ℕ)) := by
      intro k hk
      rcases k with _ | _ | k
      · exact hu0
      · exact hu1
      · exact (hstep k hk).1
    have hD : ∀ v : WState (a := a) (m := m) S, ‖discreteD S' v‖ ≤ c / (2 * Δt) * ‖v‖ := by
      intro v
      have := hcfl (dEmb S' v) fun i => (v i).2
      rw [dApply_dEmb, norm_emb hemb, norm_emb hemb] at this
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have hcA : Δt * ‖LinearMap.toContinuousLinearMap (discreteWave S')‖ ≤ c := by
      have := opNorm_discreteWave_le S' (by positivity) hD
      calc Δt * ‖LinearMap.toContinuousLinearMap (discreteWave S')‖ ≤
          Δt * (2 * (c / (2 * Δt))) := mul_le_mul_of_nonneg_left this hΔt.le
        _ = c := by field_simp
    have key := norm_leapfrog_error_le_of_sub_mem (V₀ := ⊤) (g := fun _ => 0)
      (u := fun k => lift S (u k)) hemb hD₀ hDD hA hΔt hcA hc1 (fun t => (hU t).1)
      (fun t => (hU t).2.1) (fun t => (hU t).2.2) (fun t ht => (hU' t ht).1) hweak hA1 hA2 hA3 hK
      (fun k hk => isDirichletLeapfrogStep_of S (hstep k hk) (hu k (by omega))
        (hu (k + 1) (by omega)))
      (fun _ _ => Submodule.mem_top) Submodule.mem_top Submodule.mem_top
    rwa [dEmb_lift S (hu K le_rfl), dEmb_lift S hu0, dEmb_lift S hu1] at key

end HilbertComplex

end FEEC
