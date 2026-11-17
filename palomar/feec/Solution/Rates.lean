module

public import Solution.Dynamic

/-!
# The rates of a Jackson estimate

The rated conclusions of the challenge (`SubcomplexFamily.Rated`) from the verdicts: the static
rate from quasi-optimality (`StaticVerdict.quasiOptimal`), the Jackson estimate and the bound
`μₕ ≤ 1 + c` of the harmonic gap (`SubcomplexFamily.harmonicGap_le`); the fully discrete wave rate
from the semidiscrete error bound (`WaveVerdict.error`), the Jackson estimate of the window
(`SubcomplexFamily.graphDist_le_of_jackson`) and the temporal error of the rational scheme
(`EvolutionVerdict.rational_temporal`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §3.4, Thm 3.9
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015], Thm 4.14

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

namespace HilbertComplex

variable {H : HilbertComplex 𝕜 W} {κ : Type*}

/-- **The static verdict** with some constant, from bounded projections and closed ranges. -/
theorem SubcomplexFamily.exists_staticVerdict (F : H.SubcomplexFamily κ) (j : ℤ)
    (hπ : F.IsGraphBounded (j - 1)) (hπ' : F.IsGraphBounded j)
    (hj : IsClosed (H.boundaries j : Set (W j)))
    (hj' : IsClosed (H.boundaries (j + 1) : Set (W (j + 1)))) : ∃ C, F.StaticVerdict₀ j C := by
  obtain ⟨c₁, hc₁, h₁⟩ := hπ.exists_one_le
  obtain ⟨c₂, -, h₂⟩ := hπ'.exists_one_le
  obtain ⟨p₁, hp₁⟩ := H.exists_poincareBy (i := j - 1) (by rwa [sub_add_cancel])
  obtain ⟨p₂, hp₂⟩ := H.exists_poincareBy hj'
  exact ⟨_, F.staticVerdict_of j (hc₁.trans (le_max_left _ c₂)) (h₁.mono (le_max_left _ _))
    (h₂.mono (le_max_right _ _)) (hp₁.mono (le_max_left _ p₂)) (hp₂.mono (le_max_right _ _))⟩

/-- A harmonic form is a cycle: `d q = 0`. -/
theorem d_eq_zero_of_mem_harmonic {j : ℤ} {q : W j} (hq : q ∈ H.harmonic j) :
    H.d j (j + 1) ⟨q, H.harmonic_le_domain j hq⟩ = 0 := by
  obtain ⟨y, hyq, hy⟩ := LinearPMap.mem_ker_iff.1 hq.1
  have : (⟨q, H.harmonic_le_domain j hq⟩ : (H.d j (j + 1)).domain) = y := Subtype.ext hyq
  rw [this, hy]

/-- **The harmonic gap is bounded** by `1 + c` for cochain projections bounded by `c` in the graph
norm: `‖q - π q‖ ≤ ‖q‖ + ‖π q‖_V ≤ (1 + c) ‖q‖` on the harmonic forms (`d q = 0`). -/
theorem SubcomplexFamily.harmonicGap_le (F : H.SubcomplexFamily κ) {j : ℤ} {c : ℝ}
    (hπ : F.IsGraphBoundedBy j c) (h : κ) : (F.π h).harmonicGap j ≤ 1 + max c 0 := by
  have hne : Nonempty {q : H.harmonic j // ‖(q : W j)‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  refine ciSup_le fun q => ?_
  obtain ⟨⟨q, hq⟩, hq1⟩ := q
  dsimp only
  set x : (H.d j (j + 1)).domain := ⟨q, H.harmonic_le_domain j hq⟩
  have h1 := hπ h x
  have hx : H.graphNorm j (j + 1) x = ‖q‖ := by
    unfold graphNorm
    rw [show H.d j (j + 1) x = 0 from d_eq_zero_of_mem_harmonic hq, norm_zero,
      zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg _)]
  rw [hx] at h1
  have h2 := norm_le_graphNorm (H := H) (⟨(F.π h).π j x, (F.V h).le_domain j (j + 1)
    ((F.π h).π j x).2⟩ : (H.d j (j + 1)).domain)
  have h3 : c * ‖q‖ ≤ max c 0 * 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left c 0) (norm_nonneg q)).trans
      (mul_le_mul_of_nonneg_left hq1 (le_max_right c 0))
  calc ‖q - ((F.π h).π j x : W j)‖ ≤ ‖q‖ + ‖((F.π h).π j x : W j)‖ := norm_sub_le _ _
    _ ≤ 1 + max c 0 := by linarith

/-- The graph-norm distance is at most `‖x - v‖ + ‖d (x - v)‖` for every `v ∈ Vⁱ`. -/
theorem Subcomplex.graphDist_le (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)] {i j : ℤ}
    (x : (H.d i j).domain) (v : S.V i) :
    S.graphDist i j x ≤ ‖(x : W i) - v‖ + ‖H.d i j (x - ⟨v, S.le_domain i j v.2⟩)‖ := by
  refine (ciInf_le ⟨0, fun _ ⟨_, hy⟩ => hy ▸ graphNorm_nonneg _⟩ v).trans ?_
  unfold graphNorm
  have ha := norm_nonneg ((x : W i) - v)
  have hb := norm_nonneg (H.d i j (x - ⟨v, S.le_domain i j v.2⟩))
  rw [Real.sqrt_le_left (by positivity)]
  change ‖(x : W i) - v‖ ^ 2 + _ ≤ _
  nlinarith [mul_nonneg ha hb]

/-- **The graph-norm distance of an `s`-regular form** is at most `2 |B| L hᵒʳᵈ⁽ˢ⁾`. -/
theorem SubcomplexFamily.Jackson.graphDist_le {F : H.SubcomplexFamily κ} {ρ : Type*}
    (J : F.Jackson ρ) (s : ρ) (h : κ) {i j : ℤ} {L : ℝ} (hL : 0 ≤ L) (x : (H.d i j).domain)
    (hx : J.Reg s i L x) :
    (F.V h).graphDist i j x ≤ 2 * |J.B s i| * (L * J.meshSize h ^ J.ord s) := by
  obtain ⟨v, hv, h1, h2⟩ := J.jackson s h i (x : W i) hL hx
  have hm : 0 ≤ L * J.meshSize h ^ J.ord s :=
    mul_nonneg hL (Real.rpow_nonneg (J.meshSize_nonneg h) _)
  have hB := mul_le_mul_of_nonneg_right (le_abs_self (J.B s i)) hm
  refine ((F.V h).graphDist_le x ⟨v, hv⟩).trans ?_
  have e : (x - ⟨v, (F.V h).le_domain i j hv⟩ : (H.d i j).domain) =
      ⟨(x : W i) - v, Submodule.sub_mem _ x.2 ((F.V h).le_domain i j hv)⟩ := rfl
  have h2' := h2 j x.2
  rw [← e] at h2'
  change ‖(x : W i) - v‖ + ‖H.d i j (x - ⟨v, (F.V h).le_domain i j hv⟩)‖ ≤ _
  linarith

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

namespace SubcomplexFamily

variable (F : H.SubcomplexFamily κ) (a : ℤ) (m : ℕ)

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- **The Jackson estimate on the window**: a point of `D(𝐝)` whose components are `s`-regular
with bound `L` is within `(1 + m) (∑ᵢ |Bₛ,ₐ₊ᵢ|) L hᵒʳᵈ⁽ˢ⁾` of `Xₕ` in the graph norm of `𝐝`. -/
theorem graphDist_le_of_jackson {ρ : Type*} (J : F.Jackson ρ) (s : ρ) (h : κ) {L : ℝ}
    (hL : 0 ≤ L) (y : (H.totalD a m).domain)
    (hy : ∀ i : Fin m, J.Reg s (a + (i : ℕ)) L ((y : Total W a m) i)) :
    F.graphDist a m h y ≤
      (1 + m) * (∑ i : Fin m, |J.B s (a + (i : ℕ))|) * (L * J.meshSize h ^ J.ord s) := by
  classical
  set ε := L * J.meshSize h ^ J.ord s
  have hε : 0 ≤ ε := mul_nonneg hL (Real.rpow_nonneg (J.meshSize_nonneg h) _)
  choose v hv h1 h2 using fun i : Fin m => J.jackson s h (a + (i : ℕ)) _ hL (hy i)
  set w : Total W a m := WithLp.toLp 2 fun i => v i
  have hw : w ∈ F.Xh a m h := fun i => hv i
  set B := ∑ i : Fin m, |J.B s (a + (i : ℕ))|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have e1 : ‖(y : Total W a m) - w‖ ≤ B * ε := by
    refine (PiLp.norm_le_sum_norm _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    exact (h1 i).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hε)
  have e2 : ‖H.totalD a m y - H.totalD a m ⟨w, F.Xh_le a m h hw⟩‖ ≤ m * B * ε := by
    rw [← LinearPMap.map_sub]
    refine (PiLp.norm_le_sum_norm _).trans ?_
    have hj : ∀ j : Fin m, ‖(H.totalD a m (y - ⟨w, F.Xh_le a m h hw⟩)) j‖ ≤ B * ε := by
      intro j
      change ‖∑ i : Fin m, H.d (a + (i : ℕ)) (a + (j : ℕ)) ⟨_, _⟩‖ ≤ _
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      refine le_of_eq_of_le ?_ ((h2 i (a + (j : ℕ)) (y.2 i j)).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) hε))
      rfl
    calc ∑ j : Fin m, ‖(H.totalD a m (y - ⟨w, F.Xh_le a m h hw⟩)) j‖
        ≤ ∑ _j : Fin m, B * ε := Finset.sum_le_sum fun j _ => hj j
      _ = m * B * ε := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_assoc]
  refine (ciInf_le ⟨0, fun _ ⟨_, hz⟩ => hz ▸ by positivity⟩ ⟨w, hw⟩).trans ?_
  change ‖(y : Total W a m) - w‖ + ‖H.totalD a m y - H.totalD a m ⟨w, F.Xh_le a m h hw⟩‖ ≤ _
  nlinarith

omit [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- **The rates of a Jackson estimate** (`Rated`). -/
theorem rated {ρ : Type*} (J : F.Jackson ρ) : F.Rated₀ J where
  static j hπ hπ' hj hj' s := by
    obtain ⟨C, V⟩ := F.exists_staticVerdict j hπ hπ' hj hj'
    obtain ⟨c, hc⟩ := hπ'
    refine ⟨max C 0 * (2 * |J.B s (j - 1)| + 2 * |J.B s j| + 2 * |J.B s j| +
      (1 + max c 0) * (2 * |J.B s j|)), fun {f σ u p} hs {L} hL hσ hu hp hb h σh uh ph hsh => ?_⟩
    have e := V.quasiOptimal hs h hsh
    have hε : 0 ≤ L * J.meshSize h ^ J.ord s :=
      mul_nonneg hL (Real.rpow_nonneg (J.meshSize_nonneg h) _)
    have a1 := J.graphDist_le s h hL σ hσ
    have a2 := J.graphDist_le s h hL u hu
    have a3 := J.graphDist_le s h hL ⟨p, H.harmonic_le_domain j hs.mem.2.2⟩ hp
    have a4 := J.graphDist_le s h hL ⟨_, H.topologicalClosure_boundaries_le_domain j
      (Submodule.starProjection_apply_mem (H.boundaries j).topologicalClosure (u : W j))⟩ hb
    have hμ := F.harmonicGap_le hc h
    have g4 := (F.V h).graphDist_nonneg (⟨_, H.topologicalClosure_boundaries_le_domain j
      (Submodule.starProjection_apply_mem (H.boundaries j).topologicalClosure (u : W j))⟩ :
        (H.d j (j + 1)).domain)
    have hX : 0 ≤ (F.V h).graphDist (j - 1) j σ + (F.V h).graphDist j (j + 1) u +
        (F.V h).graphDist j (j + 1) ⟨p, H.harmonic_le_domain j hs.mem.2.2⟩ +
        (F.π h).harmonicGap j * (F.V h).graphDist j (j + 1) ⟨_,
          H.topologicalClosure_boundaries_le_domain j
            (Submodule.starProjection_apply_mem (H.boundaries j).topologicalClosure
              (u : W j))⟩ := by
      have := (F.V h).graphDist_nonneg σ
      have := (F.V h).graphDist_nonneg u
      have := (F.V h).graphDist_nonneg (⟨p, H.harmonic_le_domain j hs.mem.2.2⟩ :
        (H.d j (j + 1)).domain)
      have hμ0 : 0 ≤ (F.π h).harmonicGap j := Real.iSup_nonneg fun _ => norm_nonneg _
      positivity
    have hμd := mul_le_mul hμ a4 g4 (by positivity)
    have key : (F.V h).graphDist (j - 1) j σ + (F.V h).graphDist j (j + 1) u +
        (F.V h).graphDist j (j + 1) ⟨p, H.harmonic_le_domain j hs.mem.2.2⟩ +
        (F.π h).harmonicGap j * (F.V h).graphDist j (j + 1) ⟨_,
          H.topologicalClosure_boundaries_le_domain j
            (Submodule.starProjection_apply_mem (H.boundaries j).topologicalClosure
              (u : W j))⟩ ≤
        (2 * |J.B s (j - 1)| + 2 * |J.B s j| + 2 * |J.B s j| +
          (1 + max c 0) * (2 * |J.B s j|)) * (L * J.meshSize h ^ J.ord s) := by
      linarith
    calc H.mixedError j σ σh u uh p ph ≤ _ := e
      _ ≤ max C 0 * _ := mul_le_mul_of_nonneg_right (le_max_left C 0) hX
      _ ≤ max C 0 * ((2 * |J.B s (j - 1)| + 2 * |J.B s j| + 2 * |J.B s j| +
          (1 + max c 0) * (2 * |J.B s j|)) * (L * J.meshSize h ^ J.ord s)) :=
        mul_le_mul_of_nonneg_left key (le_max_right C 0)
      _ = _ := by ring
  wave a m ha r hr p hp s := by
    have : ∀ i, IsScalarTower ℝ 𝕜 (W i) := fun _ => isScalarTower_of_normedSpace
    obtain ⟨S, hS⟩ := F.waveVerdict a m (F.approximates_window a m ha.1 ha.2)
    obtain ⟨K, hK⟩ := hS.evolution.rational_temporal r hr hp
    refine ⟨S, hS, 2 * (1 + 4 * √3) * ((1 + m) * ∑ i : Fin m, |J.B s (a + (i : ℕ))|), K,
      fun x hx hx2 L hL h τ hτ n v hreg => ?_⟩
    set M := (1 + m) * (∑ i : Fin m, |J.B s (a + (i : ℕ))|) * (L * J.meshSize h ^ J.ord s)
    have hnτ : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg n) hτ
    have e1 := hS.error x hx hx2 h v (t := n * τ) (M := M) hnτ fun t ht y hy => by
      refine F.graphDist_le_of_jackson a m J s h hL y fun i => ?_
      rcases hy with hy | hy
      · rw [hy]; exact (hreg t ht i).1
      · rw [hy]; exact (hreg t ht i).2
    have e2 := hK h hτ n v
    have e3 : ‖S (n * τ) x - ((r.apply ((τ : 𝕜) • F.Lh a m h) ^ n) v : Total W a m)‖ ≤
        ‖S (n * τ) x - (semiflow (F.Lh a m h) (n * τ) v : Total W a m)‖ +
          ‖semiflow (F.Lh a m h) (n * τ) v - (r.apply ((τ : 𝕜) • F.Lh a m h) ^ n) v‖ := by
      rw [← Submodule.norm_coe, Submodule.coe_sub]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    have e4 : 2 * (1 + 4 * √3) * (1 + n * τ) * M = 2 * (1 + 4 * √3) *
        ((1 + m) * ∑ i : Fin m, |J.B s (a + (i : ℕ))|) * (1 + n * τ) * L *
          J.meshSize h ^ J.ord s := by
      ring
    linarith

end SubcomplexFamily

end HilbertComplex

end FEEC
