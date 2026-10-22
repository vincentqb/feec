module

public import Feec.HilbertComplex.Approximation.MixedError
public import Feec.HilbertComplex.HodgeSolution

/-!
# Quasi-optimal error estimates for the mixed Hodge Laplacian

Let `Vₕ` be a finite-dimensional subcomplex of a Hilbert complex `H` with a cochain projection `π`
bounded by `C ≥ 1` in the graph norm, and let `c_P` be a Poincaré constant of `H` at the arrows
`i → j → k`. The discrete mixed problem (the mixed problem of the discrete complex
`S.toHilbertComplex`, with data the `W`-projection of `f`) is uniformly stable, and its solution
`(σₕ, uₕ, pₕ)` is quasi-optimal ([AFW2010], Thm 3.9):

`‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖ ≤ C' (inf ‖σ - τ‖_V + inf ‖u - v‖_V + inf ‖p - q‖ + μ inf ‖P_𝔅 u - v‖_V)`

with `μ = sup_{q ∈ ℌ, ‖q‖ ≤ 1} ‖q - π q‖` (`harmonicGap`) and the explicit constant
`C' = (1 + 144 (C √(1 + c_P²))²) (1 + C)`. The infima are over `Vₕⁱ`, `Vₕʲ` (graph norm), `ℌₕʲ`
(`W` norm) and `Vₕʲ` (graph norm). The `ℌₕʲ` term is at least as sharp as the graph-norm distance
of `p` to `Vₕʲ` used in [AFW2010], Thm 3.9: `dist(p, ℌₕ) ≤ (1 + C) dist_V(p, Vₕ)`
(`infDist_harmonicW_le`), which gives the estimate in the exact form of AFW
(`norm_sub_le_infDist_domainSub`).

The discrete harmonic forms are in general not harmonic (`ℌₕ ⊄ ℌ`): the discrete problem is not
a Galerkin restriction of the continuous one. As in [AFW2010], §3.4 this *variational crime* is
handled by comparing the two problems on the discrete test space: the continuous solution
satisfies the discrete equations up to the consistency term `⟪q', u⟫`, `q' ∈ ℌₕ`, which is bounded
by `‖(I - π) P_𝔅 u‖ ‖q' - P_ℌ q'‖ ≤ μ ‖(I - π) P_𝔅 u‖ ‖q'‖` (`norm_inner_le_of_orthogonal_harmonic`
and the second half of the gap estimate, `norm_sub_starProjection_harmonic_le`).

## Main definitions

* `Subcomplex.embD`: the isometric embedding `Vₕⁱ → Vⁱ` of the discrete domain spaces.
* `CochainProjection.IsGraphBounded`: the graph-norm bound `‖π x‖_V ≤ C ‖x‖_V`.
* `CochainProjection.harmonicGap`: `μ = sup_{q ∈ ℌ, ‖q‖ ≤ 1} ‖q - π q‖`.
* `CochainProjection.discreteMixedSolution`: `(σₕ, uₕ, pₕ)`, the solution of the mixed problem
  of the discrete complex with data `P_{Vₕ} f`.

## Main results

* `CochainProjection.norm_sub_starProjection_harmonic_le`: `‖q - P_ℌ q‖ ≤ ‖(I - π) P_ℌ q‖` for
  `q ∈ ℌₕ` ([AFW2010], Thm 3.5, second inequality); with the first inequality
  (`norm_sub_starProjection_harmonicW_le`) the gap between `ℌ` and `ℌₕ` is at most `μ` in both
  directions (`norm_sub_starProjection_harmonic_le_mul`).
* `CochainProjection.norm_inner_le_of_orthogonal_harmonic`: the consistency estimate.
* `CochainProjection.infSup_mixedForm_of_graph`: uniform discrete inf-sup with a graph-bounded
  cochain projection.
* `CochainProjection.mixedForm_error_eq`, `CochainProjection.norm_mixedForm_error_le`: Galerkin
  orthogonality up to the consistency term, and the residual bound.
* **`CochainProjection.norm_sub_le_quasiOptimal`** (`∀`-form),
  **`CochainProjection.norm_sub_le_infDist`** (`infDist` form) and
  `CochainProjection.norm_sub_le_infDist_harmonicGap` (`μ = harmonicGap`): the quasi-optimal
  estimate; `CochainProjection.norm_sub_le_infDist_domainSub`: the same in the form of
  [AFW2010], Thm 3.9, via `CochainProjection.infDist_harmonicW_le`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.4, Thm 3.5 (gap between `ℌ` and `ℌₕ`), Thm 3.9 (quasi-optimality)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Thm 5.5 (quasi-optimality of
  the mixed method)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
  (stable mixed discretizations from bounded cochain projections)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Feec.Variational

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Cycles as points of the domain space -/

/-- The domain-space element of a cycle. -/
def cyclesToDomainSpace {j : ι} {z : W j} (hz : z ∈ H.cycles j) : H.domainSpace j :=
  (H.d j (c.next j)).toGraphSpace ⟨z, H.cycles_le_domain j hz⟩

@[simp] theorem domainIncl_cyclesToDomainSpace {j : ι} {z : W j} (hz : z ∈ H.cycles j) :
    H.domainIncl j (cyclesToDomainSpace hz) = z := rfl

theorem d_domainCoord_cyclesToDomainSpace {j : ι} (k : ι) {z : W j} (hz : z ∈ H.cycles j) :
    H.d j k (H.domainCoord j k (cyclesToDomainSpace hz)) = 0 :=
  H.d_eq_zero_of_mem_cycles hz _

namespace Subcomplex

variable (S : H.Subcomplex)

/-! ### The embedding of the discrete domain spaces -/

section Discrete

variable [∀ i, FiniteDimensional 𝕜 (S.V i)]

/-- The point of `Vₕⁱ ⊆ D(d)` underlying a point of the discrete domain space. -/
abbrev toW (i : ι) (a : S.toHilbertComplex.domainSpace i) : W i :=
  (S.toHilbertComplex.domainIncl i a : W i)

theorem norm_sq_discrete_domainSpace (i : ι) (a : S.toHilbertComplex.domainSpace i) :
    ‖a‖ ^ 2 = ‖S.toW i a‖ ^ 2 +
      ‖H.d i (c.next i) (S.toDomain i (c.next i) (S.toHilbertComplex.domainIncl i a))‖ ^ 2 :=
  S.toHilbertComplex.norm_sq_domainSpace i a

/-- **The embedding `Vₕⁱ → Vⁱ`** of the discrete domain space into the domain space, an
isometry for the graph norms. -/
def embD (i : ι) : S.toHilbertComplex.domainSpace i →ₗᵢ[𝕜] H.domainSpace i where
  toFun a := (H.d i (c.next i)).toGraphSpace (S.toDomain i (c.next i)
    (S.toHilbertComplex.domainIncl i a))
  map_add' a b := H.domainIncl_injective i (by
    simp only [domainIncl_toGraphSpace, coe_toDomain, _root_.map_add, Submodule.coe_add])
  map_smul' a b := H.domainIncl_injective i (by
    simp only [domainIncl_toGraphSpace, coe_toDomain, _root_.map_smul, Submodule.coe_smul,
      RingHom.id_apply])
  norm_map' a := by
    have h1 := H.norm_sq_domainSpace i ((H.d i (c.next i)).toGraphSpace (S.toDomain i (c.next i)
      (S.toHilbertComplex.domainIncl i a)))
    have h2 := S.norm_sq_discrete_domainSpace i a
    have h : ‖(H.d i (c.next i)).toGraphSpace (S.toDomain i (c.next i)
        (S.toHilbertComplex.domainIncl i a))‖ ^ 2 = ‖a‖ ^ 2 := by
      rw [h1, h2]; rfl
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

@[simp] theorem domainIncl_embD (i : ι) (a : S.toHilbertComplex.domainSpace i) :
    H.domainIncl i (S.embD i a) = S.toW i a := rfl

/-- The image of `embD`: the discrete domain space `Vₕⁱ` inside `Vⁱ`. -/
def domainSub (i : ι) : Submodule 𝕜 (H.domainSpace i) := LinearMap.range (S.embD i).toLinearMap

theorem mem_domainSub {i : ι} (a : S.toHilbertComplex.domainSpace i) :
    S.embD i a ∈ S.domainSub i := ⟨a, rfl⟩

end Discrete

namespace CochainProjection

variable {S} (P : S.CochainProjection)

/-! ### Graph-bounded cochain projections -/

/-- `π` is bounded by `C` in the graph norm of `d i j`:
`‖π x‖² + ‖d π x‖² ≤ C² (‖x‖² + ‖d x‖²)` (the hypothesis of
`norm_le_of_forall_inner_eq_zero_of_graph`). -/
def IsGraphBounded (i j : ι) (C : ℝ) : Prop :=
  ∀ x : (H.d i j).domain, ‖P.π i x‖ ^ 2 +
    ‖H.d i j ⟨P.π i x, S.le_domain i j (P.mem i x)⟩‖ ^ 2 ≤ C ^ 2 * (‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2)

/-- `‖π (ι x)‖ ≤ C ‖x‖_V`. -/
theorem norm_π_domainIncl_le {i j : ι} (hij : c.Rel i j) {C : ℝ} (hC : 0 ≤ C)
    (hπ : P.IsGraphBounded i j C) (x : H.domainSpace i) :
    ‖P.π i (H.domainIncl i x)‖ ≤ C * ‖x‖ := by
  have h : ‖P.π i (H.domainIncl i x)‖ ^ 2 +
      ‖H.d i j ⟨P.π i (H.domainIncl i x), S.le_domain i j (P.mem i _)⟩‖ ^ 2 ≤
        C ^ 2 * (‖H.domainIncl i x‖ ^ 2 + ‖H.d i j (H.domainCoord i j x)‖ ^ 2) :=
    hπ (H.domainCoord i j x)
  rw [← H.norm_sq_domainSpace_of_rel hij] at h
  have h' : ‖P.π i (H.domainIncl i x)‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [mul_pow]; nlinarith [sq_nonneg ‖H.d i j ⟨P.π i (H.domainIncl i x),
      S.le_domain i j (P.mem i _)⟩‖]
  exact (abs_le_of_sq_le_sq' h' (mul_nonneg hC (norm_nonneg x))).2

/-- `π` maps boundaries to discrete boundaries. -/
theorem mem_boundariesW {j : ι} {b : W j} (hb : b ∈ H.boundaries j) :
    P.π j b ∈ S.boundariesW j := by
  obtain ⟨ρ, rfl⟩ := hb
  exact ⟨⟨P.π (c.prev j) ρ, P.mem _ _⟩, P.comm _ j ρ⟩

/-! ### The gap between `ℌ` and `ℌₕ` -/

/-- **The harmonic gap, discrete to continuous**: for `q ∈ ℌₕ`,
`‖q - P_ℌ q‖ ≤ ‖P_ℌ q - π P_ℌ q‖`. See [AFW2010], Thm 3.5. -/
theorem norm_sub_starProjection_harmonic_le {j : ι} (hj : H.ClosedRangeAt j) {q : W j}
    (hq : q ∈ S.harmonicW j) :
    ‖q - (H.harmonic j).starProjection q‖ ≤
      ‖(H.harmonic j).starProjection q - P.π j ((H.harmonic j).starProjection q)‖ := by
  set r := (H.harmonic j).starProjection q
  have hrH : r ∈ H.harmonic j := Submodule.starProjection_apply_mem _ _
  have hqz : q ∈ H.cycles j := S.cyclesW_le_cycles j (S.harmonicW_le_cyclesW j hq)
  have hqrB : q - r ∈ H.boundaries j :=
    H.mem_boundaries_of_mem_cycles hj (sub_mem hqz (H.harmonic_le_cycles j hrH))
      (Submodule.sub_starProjection_mem_orthogonal q)
  have hBh : q - P.π j r ∈ S.boundariesW j := by
    have := P.mem_boundariesW hqrB
    rwa [_root_.map_sub, P.proj j q (S.harmonicW_le_V j hq)] at this
  have hperp : ⟪q - r, q - P.π j r⟫ = 0 := by
    have h1 : ⟪q - P.π j r, q⟫ = 0 := (S.mem_harmonicW_iff.1 hq).2.2 _ hBh
    have h2 : ⟪q - P.π j r, r⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (S.boundariesW_le j hBh)
        (H.mem_harmonic_iff.1 hrH).2
    rw [← inner_conj_symm, inner_sub_right, h1, h2, sub_zero, _root_.map_zero]
  have hsq : ‖q - r‖ ^ 2 ≤ ‖q - r‖ * ‖r - P.π j r‖ := by
    have e : (‖q - r‖ : 𝕜) ^ 2 = ⟪q - r, P.π j r - r⟫ := by
      rw [← inner_self_eq_norm_sq_to_K, show q - r = (q - P.π j r) + (P.π j r - r) by abel,
        inner_add_right]
      rw [show (q - P.π j r) + (P.π j r - r) = q - r by abel, hperp, zero_add]
    have := norm_inner_le_norm (𝕜 := 𝕜) (q - r) (P.π j r - r)
    rw [← e, norm_pow, RCLike.norm_ofReal, abs_norm, ← norm_neg (P.π j r - r), neg_sub] at this
    exact this
  rcases (norm_nonneg (q - r)).eq_or_lt with h | h
  · rw [← h]; exact norm_nonneg _
  · exact le_of_mul_le_mul_left (by nlinarith) h

/-- With a gap bound `‖q - π q‖ ≤ μ ‖q‖` on `ℌ`: `‖q - P_ℌ q‖ ≤ μ ‖q‖` for `q ∈ ℌₕ`. -/
theorem norm_sub_starProjection_harmonic_le_mul {j : ι} (hj : H.ClosedRangeAt j) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ : ∀ q ∈ H.harmonic j, ‖q - P.π j q‖ ≤ μ * ‖q‖) {q : W j}
    (hq : q ∈ S.harmonicW j) : ‖q - (H.harmonic j).starProjection q‖ ≤ μ * ‖q‖ :=
  (P.norm_sub_starProjection_harmonic_le hj hq).trans ((hμ _ (Submodule.starProjection_apply_mem
    _ _)).trans (mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le _ _) hμ0))

/-- **The harmonic gap** `μ = sup_{q ∈ ℌʲ, ‖q‖ ≤ 1} ‖q - π q‖` ([AFW2010], (3.20)); it is the
smallest `μ` with `‖q - π q‖ ≤ μ ‖q‖` on `ℌʲ` when that set of `μ` is nonempty
(`norm_sub_le_harmonicGap_mul`, `harmonicGap_le`). -/
def harmonicGap (j : ι) : ℝ :=
  ⨆ q : {q : H.harmonic j // ‖(q : W j)‖ ≤ 1}, ‖((q : H.harmonic j) : W j) - P.π j q‖

theorem harmonicGap_nonneg (j : ι) : 0 ≤ P.harmonicGap j :=
  Real.iSup_nonneg fun _ => norm_nonneg _

private theorem bddAbove_harmonicGap {j : ι} {μ : ℝ}
    (hμ : ∀ q ∈ H.harmonic j, ‖q - P.π j q‖ ≤ μ * ‖q‖) :
    BddAbove (Set.range fun q : {q : H.harmonic j // ‖(q : W j)‖ ≤ 1} =>
      ‖((q : H.harmonic j) : W j) - P.π j q‖) := by
  refine ⟨max μ 0, ?_⟩
  rintro _ ⟨q, rfl⟩
  refine (hμ _ (q : H.harmonic j).2).trans ?_
  rcases le_total 0 μ with h | h
  · exact (mul_le_of_le_one_right h q.2).trans (le_max_left _ _)
  · exact (mul_nonpos_of_nonpos_of_nonneg h (norm_nonneg _)).trans (le_max_right _ _)

/-- `‖q - π q‖ ≤ μₕ ‖q‖` on `ℌ`, provided some bound of this form holds. -/
theorem norm_sub_le_harmonicGap_mul {j : ι} {μ : ℝ}
    (hμ : ∀ q ∈ H.harmonic j, ‖q - P.π j q‖ ≤ μ * ‖q‖) {q : W j} (hq : q ∈ H.harmonic j) :
    ‖q - P.π j q‖ ≤ P.harmonicGap j * ‖q‖ := by
  rcases (norm_nonneg q).eq_or_lt with h | h
  · have hq0 : q = 0 := norm_eq_zero.1 h.symm
    simp [hq0]
  · set a : 𝕜 := ((‖q‖⁻¹ : ℝ) : 𝕜)
    have hna : ‖a • q‖ = 1 := by
      rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ h.ne']
    have hle := le_ciSup (P.bddAbove_harmonicGap hμ)
      (⟨⟨a • q, Submodule.smul_mem _ _ hq⟩, hna.le⟩ : {q : H.harmonic j // ‖(q : W j)‖ ≤ 1})
    simp only at hle
    rw [_root_.map_smul, ← smul_sub, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm] at hle
    rw [← div_le_iff₀ h, div_eq_inv_mul]
    exact hle

theorem harmonicGap_le {j : ι} {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ q ∈ H.harmonic j, ‖q - P.π j q‖ ≤ μ * ‖q‖) : P.harmonicGap j ≤ μ := by
  unfold harmonicGap
  exact Real.iSup_le (fun (q : {q : H.harmonic j // ‖(q : W j)‖ ≤ 1}) =>
    (hμ _ q.1.2).trans (mul_le_of_le_one_right hμ0 q.2)) hμ0

/-- A graph-bounded projection has finite harmonic gap: `‖q - π q‖ ≤ (1 + C) ‖q‖` on `ℌʲ`. -/
theorem norm_sub_π_harmonic_le {j k : ι} (hjk : c.Rel j k) {C : ℝ} (hC : 0 ≤ C)
    (hπ : P.IsGraphBounded j k C) {q : W j} (hq : q ∈ H.harmonic j) :
    ‖q - P.π j q‖ ≤ (1 + C) * ‖q‖ := by
  have hz := H.harmonic_le_cycles j hq
  have h := P.norm_π_domainIncl_le hjk hC hπ (cyclesToDomainSpace hz)
  have hn : ‖cyclesToDomainSpace hz‖ = ‖q‖ := by
    have := H.norm_sq_domainSpace_of_rel hjk (cyclesToDomainSpace hz)
    rw [domainIncl_cyclesToDomainSpace, d_domainCoord_cyclesToDomainSpace, norm_zero,
      zero_pow two_ne_zero, add_zero] at this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  rw [domainIncl_cyclesToDomainSpace, hn] at h
  calc ‖q - P.π j q‖ ≤ ‖q‖ + ‖P.π j q‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

/-! ### The consistency term -/

/-- **The consistency estimate** of the variational crime `ℌₕ ⊄ ℌ`: for `u ⊥ ℌ` and `q ∈ ℌₕ`,
`|⟪q, u⟫| ≤ ‖q - P_ℌ q‖ ‖(I - π) P_𝔅 u‖` (here `P_𝔅` is the projection onto the closure of the
boundaries, i.e. onto `𝔅` under closed range). See the proof of [AFW2010], Thm 3.9. -/
theorem norm_inner_le_of_orthogonal_harmonic {j : ι} (hj : H.ClosedRangeAt j) {q u : W j}
    (hq : q ∈ S.harmonicW j) (hu : u ∈ (H.harmonic j)ᗮ) :
    ‖⟪q, u⟫‖ ≤ ‖q - (H.harmonic j).starProjection q‖ *
      ‖(H.boundaries j).topologicalClosure.starProjection u -
        P.π j ((H.boundaries j).topologicalClosure.starProjection u)‖ := by
  set Bc := (H.boundaries j).topologicalClosure
  have hBc : Bc = H.boundaries j := IsClosed.submodule_topologicalClosure_eq hj
  set b := Bc.starProjection u
  set r := (H.harmonic j).starProjection q
  have hb : b ∈ H.boundaries j := hBc ▸ Submodule.starProjection_apply_mem Bc u
  have hqz : q ∈ H.cycles j := S.cyclesW_le_cycles j (S.harmonicW_le_cyclesW j hq)
  rw [← H.boundaries_sup_harmonic hj] at hqz
  obtain ⟨b', hb', h', hh', hq'⟩ := Submodule.mem_sup.1 hqz
  have e1 : ⟪q, u - b⟫ = 0 := by
    rw [← hq', inner_add_left,
      Submodule.inner_right_of_mem_orthogonal ((H.boundaries j).le_topologicalClosure hb')
        (Submodule.sub_starProjection_mem_orthogonal u),
      inner_sub_right, Submodule.inner_right_of_mem_orthogonal hh' hu,
      Submodule.inner_left_of_mem_orthogonal hb (H.mem_harmonic_iff.1 hh').2]
    simp
  have hπb := P.mem_boundariesW hb
  have e2 : ⟪q, P.π j b⟫ = 0 := by
    rw [← inner_conj_symm, (S.mem_harmonicW_iff.1 hq).2.2 _ hπb, _root_.map_zero]
  have hbB : b - P.π j b ∈ H.boundaries j := sub_mem hb (S.boundariesW_le j hπb)
  have e3 : ⟪r, b - P.π j b⟫ = 0 := Submodule.inner_left_of_mem_orthogonal hbB
    (H.mem_harmonic_iff.1 (Submodule.starProjection_apply_mem _ q)).2
  have e : ⟪q, u⟫ = ⟪q - r, b - P.π j b⟫ := by
    rw [inner_sub_left, e3, sub_zero, inner_sub_right, e2, sub_zero]
    rw [inner_sub_right, sub_eq_zero] at e1
    exact e1
  rw [e]
  exact norm_inner_le_norm _ _

variable [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- `‖(I - π) b‖ ≤ (1 + C) ‖b - v‖_V` for a cycle `b` and any `v ∈ Vₕʲ`. -/
theorem norm_sub_π_le_of_mem_cycles {j k : ι} (hjk : c.Rel j k) {C : ℝ} (hC : 0 ≤ C)
    (hπ : P.IsGraphBounded j k C) {b : W j} (hb : b ∈ H.cycles j)
    (w : S.toHilbertComplex.domainSpace j) :
    ‖b - P.π j b‖ ≤ (1 + C) * ‖cyclesToDomainSpace hb - S.embD j w‖ := by
  set x := cyclesToDomainSpace hb - S.embD j w
  have hx : H.domainIncl j x = b - S.toW j w := by
    simp [x, _root_.map_sub]
  have hπw : P.π j (S.toW j w) = S.toW j w :=
    P.proj j _ (S.toHilbertComplex.domainIncl j w).2
  have e : b - P.π j b = H.domainIncl j x - P.π j (H.domainIncl j x) := by
    rw [hx, _root_.map_sub, hπw]; abel
  rw [e]
  calc _ ≤ ‖H.domainIncl j x‖ + ‖P.π j (H.domainIncl j x)‖ := norm_sub_le _ _
    _ ≤ ‖x‖ + C * ‖x‖ := add_le_add (H.norm_domainIncl_le j x)
        (P.norm_π_domainIncl_le hjk hC hπ x)
    _ = _ := by ring

/-! ### Uniform discrete stability with a graph-bounded projection -/

variable [∀ i, FiniteDimensional 𝕜 (S.V i)]

/-- **The discrete Poincaré inequality** with a cochain projection bounded by `C` in the graph
norm: the discrete complex has Poincaré constant `C √(1 + c_P²)`. See [AFW2010], Thm 3.6. -/
theorem poincare_toHilbertComplex_of_graph {i j : ι} (hij : c.Rel i j) {cP C : ℝ}
    (hP : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hC : 0 ≤ C) (hπ : P.IsGraphBounded i j C) :
    ∀ z : (S.toHilbertComplex.d i j).domain,
      (z : S.V i) ∈ (S.toHilbertComplex.cycles i)ᗮ →
        ‖(z : S.V i)‖ ≤ C * √(1 + cP ^ 2) * ‖S.toHilbertComplex.d i j z‖ := by
  intro z hz
  have hxo : ∀ y ∈ S.cyclesW i, ⟪y, ((z : S.V i) : W i)⟫ = 0 := by
    intro y hy
    have hy' : (⟨y, (S.mem_cyclesW_iff.1 hy).1⟩ : S.V i) ∈ S.toHilbertComplex.cycles i :=
      S.mem_cycles_iff.2 (S.mem_cyclesW_iff.1 hy).2
    have := Submodule.inner_right_of_mem_orthogonal hy' hz
    rwa [Submodule.coe_inner] at this
  exact P.norm_le_of_forall_inner_eq_zero_of_graph hij hP hC hπ (z : S.V i).2 hxo

theorem one_le_mul_sqrt {cP C : ℝ} (hC : 1 ≤ C) : 1 ≤ C * √(1 + cP ^ 2) :=
  one_le_mul_of_one_le_of_one_le hC (Real.one_le_sqrt.2 (by nlinarith [sq_nonneg cP]))

/-- **Uniform inf-sup condition for the discrete mixed Hodge Laplacian** with a cochain
projection bounded in the graph norm: constant `1 / (16 (C √(1 + c_P²))²)`. See [AFW2010],
Thm 3.8. -/
theorem infSup_mixedForm_of_graph {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) {cP C : ℝ}
    (hC : 1 ≤ C)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : P.IsGraphBounded i j C) (hπj : P.IsGraphBounded j k C) :
    InfSup (S.toHilbertComplex.mixedForm i j k) (1 / (16 * (C * √(1 + cP ^ 2)) ^ 2)) :=
  S.toHilbertComplex.infSup_mixedForm hij hjk (one_le_mul_sqrt hC)
    (P.poincare_toHilbertComplex_of_graph hij hPi (zero_le_one.trans hC) hπi)
    (P.poincare_toHilbertComplex_of_graph hjk hPj (zero_le_one.trans hC) hπj)

/-! ### Quasi-optimality -/

/-- The discrete mixed form in terms of the `W` inner products of the embedded components. -/
theorem mixedForm_toHilbertComplex_apply {i j k : ι} (x y : S.toHilbertComplex.MixedSpace i j) :
    S.toHilbertComplex.mixedForm i j k x y =
      ⟪H.domainIncl i (S.embD i y.fst), H.domainIncl i (S.embD i x.fst)⟫ -
        ⟪H.d i j (H.domainCoord i j (S.embD i y.fst)), H.domainIncl j (S.embD j x.snd.fst)⟫ +
        ⟪H.domainIncl j (S.embD j y.snd.fst), H.d i j (H.domainCoord i j (S.embD i x.fst))⟫ +
        ⟪H.d j k (H.domainCoord j k (S.embD j y.snd.fst)),
          H.d j k (H.domainCoord j k (S.embD j x.snd.fst))⟫ +
        ⟪H.domainIncl j (S.embD j y.snd.fst), ((x.snd.snd : S.V j) : W j)⟫ -
        ⟪((y.snd.snd : S.V j) : W j), H.domainIncl j (S.embD j x.snd.fst)⟫ := by
  rw [mixedForm_apply]; rfl

/-- `P_𝔅 u` (the projection onto the closure of the boundaries) as a point of `Vʲ`. -/
def _root_.Feec.HilbertComplex.boundaryPart (H : HilbertComplex 𝕜 c W) (j : ι) (u : W j) :
    H.domainSpace j :=
  cyclesToDomainSpace (H.closure_boundaries_le_cycles j
    (Submodule.starProjection_apply_mem (H.boundaries j).topologicalClosure u))

private theorem norm_inner_le_of_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {x y : E} {X Y : ℝ} (hx : ‖x‖ ≤ X) (hy : ‖y‖ ≤ Y) : ‖⟪x, y⟫‖ ≤ X * Y :=
  (norm_inner_le_norm x y).trans (mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx))

private theorem norm_seven_le (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : 𝕜) :
    ‖x₁ - x₂ + x₃ + x₄ + x₅ - x₆ + x₇‖ ≤
      ‖x₁‖ + ‖x₂‖ + ‖x₃‖ + ‖x₄‖ + ‖x₅‖ + ‖x₆‖ + ‖x₇‖ := by
  have := norm_add_le (x₁ - x₂ + x₃ + x₄ + x₅ - x₆) x₇
  have := norm_sub_le (x₁ - x₂ + x₃ + x₄ + x₅) x₆
  have := norm_add_le (x₁ - x₂ + x₃ + x₄) x₅
  have := norm_add_le (x₁ - x₂ + x₃) x₄
  have := norm_add_le (x₁ - x₂) x₃
  have := norm_sub_le x₁ x₂
  linarith

/-- **Galerkin orthogonality up to the variational crime**: the discrete mixed form of the
error `xₕ - z` (`z = (τ, v, q)` discrete) tested with `(τ', v', q')` is the continuous form of
`(σ, u, p) - z` plus the consistency term `⟪q', u⟫`. -/
theorem mixedForm_error_eq {i j k : ι} {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j}
    {p : H.harmonic j} (hs : H.IsMixedSolution i j k f σ u p)
    {fh : S.V j} (hfh : ∀ v : S.V j, ⟪(v : W j), (fh : W j)⟫ = ⟪(v : W j), f⟫)
    {σh : S.toHilbertComplex.domainSpace i} {uh : S.toHilbertComplex.domainSpace j}
    {ph : S.toHilbertComplex.harmonic j}
    (hsh : S.toHilbertComplex.IsMixedSolution i j k fh σh uh ph)
    (τ τ' : S.toHilbertComplex.domainSpace i) (v v' : S.toHilbertComplex.domainSpace j)
    (q q' : S.toHilbertComplex.harmonic j) :
    S.toHilbertComplex.mixedForm i j k (MixedSpace.mk σh uh ph - MixedSpace.mk τ v q)
        (MixedSpace.mk τ' v' q') =
      ⟪H.domainIncl i (S.embD i τ'), H.domainIncl i σ - H.domainIncl i (S.embD i τ)⟫ -
        ⟪H.d i j (H.domainCoord i j (S.embD i τ')),
          H.domainIncl j u - H.domainIncl j (S.embD j v)⟫ +
        ⟪H.domainIncl j (S.embD j v'), H.d i j (H.domainCoord i j σ) -
          H.d i j (H.domainCoord i j (S.embD i τ))⟫ +
        ⟪H.d j k (H.domainCoord j k (S.embD j v')), H.d j k (H.domainCoord j k u) -
          H.d j k (H.domainCoord j k (S.embD j v))⟫ +
        ⟪H.domainIncl j (S.embD j v'), (p : W j) - ((q : S.V j) : W j)⟫ -
        ⟪((q' : S.V j) : W j), H.domainIncl j u - H.domainIncl j (S.embD j v)⟫ +
        ⟪((q' : S.V j) : W j), H.domainIncl j u⟫ := by
  have eq1 := hs.fst (S.embD i τ')
  have eq2 := hs.snd (S.embD j v')
  have hxh : S.toHilbertComplex.mixedForm i j k (MixedSpace.mk σh uh ph) =
      S.toHilbertComplex.mixedRHS i j fh :=
    mixedForm_eq_mixedRHS_iff.2 hsh
  have hrhs : S.toHilbertComplex.mixedForm i j k (MixedSpace.mk σh uh ph)
      (MixedSpace.mk τ' v' q') = ⟪H.domainIncl j (S.embD j v'), f⟫ := by
    rw [hxh, mixedRHS_apply]; exact hfh _
  rw [(S.toHilbertComplex.mixedForm i j k).map_sub, _root_.sub_apply, hrhs,
    mixedForm_toHilbertComplex_apply]
  simp only [MixedSpace.mk_fst, MixedSpace.mk_snd_fst, MixedSpace.mk_snd_snd, inner_sub_right]
  linear_combination -eq1 - eq2

/-- The bound on the discrete residual of the error. -/
theorem norm_mixedForm_error_le {i j k : ι} (hij : c.Rel i j) {cP μ : ℝ} (hμ0 : 0 ≤ μ)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hμ : ∀ q ∈ H.harmonic j, ‖q - P.π j q‖ ≤ μ * ‖q‖)
    {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j}
    (hs : H.IsMixedSolution i j k f σ u p)
    {fh : S.V j} (hfh : ∀ v : S.V j, ⟪(v : W j), (fh : W j)⟫ = ⟪(v : W j), f⟫)
    {σh : S.toHilbertComplex.domainSpace i} {uh : S.toHilbertComplex.domainSpace j}
    {ph : S.toHilbertComplex.harmonic j}
    (hsh : S.toHilbertComplex.IsMixedSolution i j k fh σh uh ph)
    (τ : S.toHilbertComplex.domainSpace i) (v : S.toHilbertComplex.domainSpace j)
    (q : S.toHilbertComplex.harmonic j) (y : S.toHilbertComplex.MixedSpace i j) :
    ‖S.toHilbertComplex.mixedForm i j k (MixedSpace.mk σh uh ph - MixedSpace.mk τ v q) y‖ ≤
      (3 * (‖σ - S.embD i τ‖ + ‖u - S.embD j v‖ + ‖(p : W j) - ((q : S.V j) : W j)‖) +
        μ * ‖(H.boundaries j).topologicalClosure.starProjection (H.domainIncl j u) -
          P.π j ((H.boundaries j).topologicalClosure.starProjection (H.domainIncl j u))‖) * ‖y‖ := by
  have hj : H.ClosedRangeAt j := (H.closedRangeAt_iff_poincare_of_rel hij).2 ⟨cP, hPi⟩
  rw [← MixedSpace.eta y, mixedForm_error_eq hs hfh hsh]
  rw [MixedSpace.eta y]
  -- the norms of the test components
  have hy1 : ‖y.fst‖ ≤ ‖y‖ := WithLp.norm_fst_le (x := y)
  have hy2 : ‖y.snd.fst‖ ≤ ‖y‖ :=
    (WithLp.norm_fst_le (x := y.snd)).trans (WithLp.norm_snd_le (x := y))
  have hy3 : ‖((y.snd.snd : S.V j) : W j)‖ ≤ ‖y‖ :=
    (WithLp.norm_snd_le (x := y.snd)).trans (WithLp.norm_snd_le (x := y))
  have t1 : ‖H.domainIncl i (S.embD i y.fst)‖ ≤ ‖y‖ :=
    (H.norm_domainIncl_le i _).trans ((S.embD i).norm_map y.fst ▸ hy1)
  have t2 : ‖H.d i j (H.domainCoord i j (S.embD i y.fst))‖ ≤ ‖y‖ :=
    (H.norm_d_domainCoord_le i j _).trans ((S.embD i).norm_map y.fst ▸ hy1)
  have t3 : ‖H.domainIncl j (S.embD j y.snd.fst)‖ ≤ ‖y‖ :=
    (H.norm_domainIncl_le j _).trans ((S.embD j).norm_map y.snd.fst ▸ hy2)
  have t4 : ‖H.d j k (H.domainCoord j k (S.embD j y.snd.fst))‖ ≤ ‖y‖ :=
    (H.norm_d_domainCoord_le j k _).trans ((S.embD j).norm_map y.snd.fst ▸ hy2)
  -- the norms of the error components
  have s1 : ‖H.domainIncl i σ - H.domainIncl i (S.embD i τ)‖ ≤ ‖σ - S.embD i τ‖ := by
    rw [← _root_.map_sub]; exact H.norm_domainIncl_le i _
  have s2 : ‖H.domainIncl j u - H.domainIncl j (S.embD j v)‖ ≤ ‖u - S.embD j v‖ := by
    rw [← _root_.map_sub]; exact H.norm_domainIncl_le j _
  have s3 : ‖H.d i j (H.domainCoord i j σ) - H.d i j (H.domainCoord i j (S.embD i τ))‖ ≤
      ‖σ - S.embD i τ‖ := by
    rw [← LinearPMap.map_sub, ← _root_.map_sub]; exact H.norm_d_domainCoord_le i j _
  have s4 : ‖H.d j k (H.domainCoord j k u) - H.d j k (H.domainCoord j k (S.embD j v))‖ ≤
      ‖u - S.embD j v‖ := by
    rw [← LinearPMap.map_sub, ← _root_.map_sub]; exact H.norm_d_domainCoord_le j k _
  -- the consistency term
  have hq'h : ((y.snd.snd : S.V j) : W j) ∈ S.harmonicW j := S.mem_harmonic_iff.1 y.snd.snd.2
  have huo : H.domainIncl j u ∈ (H.harmonic j)ᗮ :=
    (Submodule.mem_orthogonal _ _).2 fun r hr => hs.harm r hr
  have hθ0 := norm_nonneg ((H.boundaries j).topologicalClosure.starProjection (H.domainIncl j u) -
    P.π j ((H.boundaries j).topologicalClosure.starProjection (H.domainIncl j u)))
  have hcons := (P.norm_inner_le_of_orthogonal_harmonic hj hq'h huo).trans
    (mul_le_mul_of_nonneg_right
      ((P.norm_sub_starProjection_harmonic_le_mul hj hμ0 hμ hq'h).trans
        (mul_le_mul_of_nonneg_left hy3 hμ0)) hθ0)
  refine (norm_seven_le _ _ _ _ _ _ _).trans ?_
  have := norm_inner_le_of_le (𝕜 := 𝕜) t1 s1
  have := norm_inner_le_of_le (𝕜 := 𝕜) t2 s2
  have := norm_inner_le_of_le (𝕜 := 𝕜) t3 s3
  have := norm_inner_le_of_le (𝕜 := 𝕜) t4 s4
  have := norm_inner_le_of_le (𝕜 := 𝕜) t3 (le_refl ‖(p : W j) - ((q : S.V j) : W j)‖)
  have := norm_inner_le_of_le (𝕜 := 𝕜) hy3 s2
  have hy0 := norm_nonneg y
  have := norm_nonneg (σ - S.embD i τ)
  have := norm_nonneg (u - S.embD j v)
  have := norm_nonneg ((p : W j) - ((q : S.V j) : W j))
  nlinarith

private theorem quasiOptimal_arith {E₁ E₂ E₃ a b g e θ ω μ C K : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : 0 ≤ g) (hω : 0 ≤ ω)
    (c₁ : E₁ ≤ a + e) (c₂ : E₂ ≤ b + e) (c₃ : E₃ ≤ g + e)
    (he : e ≤ 16 * K * (3 * (a + b + g) + μ * θ)) (hθ : θ ≤ (1 + C) * ω) :
    E₁ + E₂ + E₃ ≤ (1 + 144 * K) * (1 + C) * (a + b + g + μ * ω) := by
  have h2 : μ * θ ≤ μ * ((1 + C) * ω) := mul_le_mul_of_nonneg_left hθ hμ
  have h3 : 16 * K * (μ * θ) ≤ 16 * K * (μ * ((1 + C) * ω)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hs : 0 ≤ a + b + g := by positivity
  nlinarith [mul_nonneg hK (mul_nonneg hμ hω), mul_nonneg hC hs, mul_nonneg (mul_nonneg hK hC) hs,
    mul_nonneg hC (mul_nonneg hμ hω), mul_nonneg (mul_nonneg hK hC) (mul_nonneg hμ hω),
    mul_nonneg hμ hω, mul_nonneg hK hs]

/-- **Quasi-optimality of the mixed finite element method** (`∀` form): with a cochain projection
bounded by `C ≥ 1` in the graph norm and a Poincaré constant `c_P`, the discrete solution
`(σₕ, uₕ, pₕ)` of the mixed problem of the subcomplex (data `fₕ`, the `W`-projection of `f`)
satisfies, for every `τ ∈ Vₕⁱ`, `v, w ∈ Vₕʲ`, `q ∈ ℌₕʲ`,

`‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖ ≤ C' (‖σ - τ‖_V + ‖u - v‖_V + ‖p - q‖ + μ ‖P_𝔅 u - w‖_V)`

with `C' = (1 + 144 (C √(1 + c_P²))²) (1 + C)` and `μ` any bound `‖q - π q‖ ≤ μ ‖q‖` on `ℌʲ`
(e.g. `harmonicGap`). See [AFW2010], Thm 3.9; [Arnold2018], Thm 5.5. -/
theorem norm_sub_le_quasiOptimal {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k)
    {cP C μ : ℝ} (hC : 1 ≤ C) (hμ0 : 0 ≤ μ)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : P.IsGraphBounded i j C) (hπj : P.IsGraphBounded j k C)
    (hμ : ∀ q ∈ H.harmonic j, ‖q - P.π j q‖ ≤ μ * ‖q‖)
    {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j}
    (hs : H.IsMixedSolution i j k f σ u p)
    {fh : S.V j} (hfh : ∀ v : S.V j, ⟪(v : W j), (fh : W j)⟫ = ⟪(v : W j), f⟫)
    {σh : S.toHilbertComplex.domainSpace i} {uh : S.toHilbertComplex.domainSpace j}
    {ph : S.toHilbertComplex.harmonic j}
    (hsh : S.toHilbertComplex.IsMixedSolution i j k fh σh uh ph)
    (τ : S.toHilbertComplex.domainSpace i) (v : S.toHilbertComplex.domainSpace j)
    (q : S.toHilbertComplex.harmonic j) (w : S.toHilbertComplex.domainSpace j) :
    ‖σ - S.embD i σh‖ + ‖u - S.embD j uh‖ + ‖(p : W j) - ((ph : S.V j) : W j)‖ ≤
      (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) *
        (‖σ - S.embD i τ‖ + ‖u - S.embD j v‖ + ‖(p : W j) - ((q : S.V j) : W j)‖ +
          μ * ‖H.boundaryPart j (H.domainIncl j u) - S.embD j w‖) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hγ := P.infSup_mixedForm_of_graph hij hjk hC hPi hPj hπi hπj
  have hBn := ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (P.norm_mixedForm_error_le hij hμ0 hPi hμ hs hfh hsh τ v q)
  have he := (hγ.norm_le (MixedSpace.mk σh uh ph - MixedSpace.mk τ v q)).trans
    (mul_le_mul_of_nonneg_left hBn (inv_nonneg.2 hγ.pos.le))
  rw [one_div, inv_inv] at he
  generalize hθ : ‖(H.boundaries j).topologicalClosure.starProjection (H.domainIncl j u) -
    P.π j ((H.boundaries j).topologicalClosure.starProjection (H.domainIncl j u))‖ = θ at he
  have hθ' : θ ≤ (1 + C) * ‖H.boundaryPart j (H.domainIncl j u) - S.embD j w‖ :=
    hθ ▸ P.norm_sub_π_le_of_mem_cycles hjk hC0 hπj _ w
  generalize hE : MixedSpace.mk σh uh ph - MixedSpace.mk τ v q = e at he
  -- the component errors
  have he1 : ‖σh - τ‖ ≤ ‖e‖ := hE ▸ WithLp.norm_fst_le (x := MixedSpace.mk σh uh ph - MixedSpace.mk τ v q)
  have he2 : ‖uh - v‖ ≤ ‖e‖ := hE ▸ (WithLp.norm_fst_le (x := (MixedSpace.mk σh uh ph - MixedSpace.mk τ v q).snd)).trans
    (WithLp.norm_snd_le (x := MixedSpace.mk σh uh ph - MixedSpace.mk τ v q))
  have he3 : ‖ph - q‖ ≤ ‖e‖ := hE ▸ (WithLp.norm_snd_le (x := (MixedSpace.mk σh uh ph - MixedSpace.mk τ v q).snd)).trans
    (WithLp.norm_snd_le (x := MixedSpace.mk σh uh ph - MixedSpace.mk τ v q))
  have c1 : ‖σ - S.embD i σh‖ ≤ ‖σ - S.embD i τ‖ + ‖e‖ := by
    have : σ - S.embD i σh = (σ - S.embD i τ) - S.embD i (σh - τ) := by
      rw [LinearIsometry.map_sub]; abel
    rw [this]
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [LinearIsometry.norm_map]; exact he1
  have c2 : ‖u - S.embD j uh‖ ≤ ‖u - S.embD j v‖ + ‖e‖ := by
    have : u - S.embD j uh = (u - S.embD j v) - S.embD j (uh - v) := by
      rw [LinearIsometry.map_sub]; abel
    rw [this]
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [LinearIsometry.norm_map]; exact he2
  have c3 : ‖(p : W j) - ((ph : S.V j) : W j)‖ ≤ ‖(p : W j) - ((q : S.V j) : W j)‖ + ‖e‖ := by
    have : (p : W j) - ((ph : S.V j) : W j) = ((p : W j) - ((q : S.V j) : W j)) -
        (((ph - q : S.toHilbertComplex.harmonic j) : S.V j) : W j) := by
      simp only [Submodule.coe_sub]; abel
    rw [this]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl he3)
  exact quasiOptimal_arith (sq_nonneg _) hC0 hμ0 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) c1 c2 c3 he hθ'

/-! ### The discrete solution and the `infDist` form -/

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
private theorem le_add_mul_infDist {X : Type*} [PseudoMetricSpace X] {s : Set X}
    (hs : s.Nonempty) {x : X} {A B K : ℝ} (hK : 0 ≤ K) (h : ∀ y ∈ s, A ≤ B + K * dist x y) :
    A ≤ B + K * Metric.infDist x s := by
  by_contra hlt
  push Not at hlt
  rcases hK.eq_or_lt with hK0 | hK0
  · obtain ⟨y, hy⟩ := hs
    have := h y hy
    rw [← hK0, zero_mul, add_zero] at this hlt
    linarith
  · have hr : Metric.infDist x s < (A - B) / K := by
      rw [lt_div_iff₀ hK0]; linarith
    obtain ⟨y, hy, hd⟩ := (Metric.infDist_lt_iff hs).1 hr
    have := h y hy
    rw [lt_div_iff₀ hK0] at hd
    linarith

variable (S) in
/-- **The discrete mixed solution** `(σₕ, uₕ, pₕ)`: the solution of the mixed problem of the
discrete complex with data `P_{Vₕ} f` (the discrete complex has closed range everywhere). -/
def discreteMixedSolution {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) (f : W j) :
    S.toHilbertComplex.MixedSpace i j :=
  S.toHilbertComplex.mixedSolution hij hjk (S.closedRangeAt j) (S.closedRangeAt k)
    ((S.V j).orthogonalProjectionOnto f)

variable (S) in
theorem inner_orthogonalProjectionOnto_eq {j : ι} (f : W j)
    (v : S.V j) : ⟪(v : W j), (((S.V j).orthogonalProjectionOnto f : S.V j) : W j)⟫ = ⟪(v : W j), f⟫ := by
  have h := Submodule.starProjection_inner_eq_zero f (v : W j) v.2
  rw [inner_sub_left, sub_eq_zero] at h
  rw [← inner_conj_symm, ← Submodule.starProjection_apply, ← h, inner_conj_symm]

variable (S) in
theorem isMixedSolution_discreteMixedSolution {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k)
    (f : W j) :
    S.toHilbertComplex.IsMixedSolution i j k ((S.V j).orthogonalProjectionOnto f)
      (discreteMixedSolution S hij hjk f).fst (discreteMixedSolution S hij hjk f).snd.fst
      (discreteMixedSolution S hij hjk f).snd.snd :=
  S.toHilbertComplex.isMixedSolution_mixedSolution hij hjk _ _ _

/-- **Quasi-optimality of the mixed finite element method** ([AFW2010], Thm 3.9;
[Arnold2018], Thm 5.5): with a cochain projection bounded by `C ≥ 1` in the graph norm, a
Poincaré constant `c_P` and a harmonic gap bound `μ`, the discrete solution `(σₕ, uₕ, pₕ)`
(`discreteMixedSolution`) of the mixed Hodge Laplacian satisfies

`‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖ ≤ C' (E_V(σ) + E_V(u) + E(p) + μ E_V(P_𝔅 u))`

with `C' = (1 + 144 (C √(1 + c_P²))²) (1 + C)`, `E_V` the distance in the graph norm to `Vₕ`
and `E(p)` the `W`-distance to `ℌₕ`. -/
theorem norm_sub_le_infDist {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k)
    {cP C μ : ℝ} (hC : 1 ≤ C) (hμ0 : 0 ≤ μ)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : P.IsGraphBounded i j C) (hπj : P.IsGraphBounded j k C)
    (hμ : ∀ q ∈ H.harmonic j, ‖q - P.π j q‖ ≤ μ * ‖q‖)
    {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j}
    (hs : H.IsMixedSolution i j k f σ u p) :
    ‖σ - S.embD i (discreteMixedSolution S hij hjk f).fst‖ +
        ‖u - S.embD j (discreteMixedSolution S hij hjk f).snd.fst‖ +
        ‖(p : W j) - (((discreteMixedSolution S hij hjk f).snd.snd : S.V j) : W j)‖ ≤
      (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) *
        (Metric.infDist σ (S.domainSub i) + Metric.infDist u (S.domainSub j) +
          Metric.infDist (p : W j) (S.harmonicW j) +
          μ * Metric.infDist (H.boundaryPart j (H.domainIncl j u)) (S.domainSub j)) := by
  set K := (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C)
  have hK : 0 ≤ K := by have := zero_le_one.trans hC; positivity
  set A := ‖σ - S.embD i (discreteMixedSolution S hij hjk f).fst‖ +
        ‖u - S.embD j (discreteMixedSolution S hij hjk f).snd.fst‖ +
        ‖(p : W j) - (((discreteMixedSolution S hij hjk f).snd.snd : S.V j) : W j)‖
  have hall := fun τ v q w => P.norm_sub_le_quasiOptimal hij hjk hC hμ0 hPi hPj hπi hπj hμ hs
    (inner_orthogonalProjectionOnto_eq S f) (isMixedSolution_discreteMixedSolution S hij hjk f)
    τ v q w
  have hne : ∀ l, (S.domainSub l : Set (H.domainSpace l)).Nonempty := fun l => ⟨0, zero_mem _⟩
  -- the four infima, one at a time
  have h1 : ∀ (v : S.toHilbertComplex.domainSpace j) (q : S.toHilbertComplex.harmonic j)
      (w : S.toHilbertComplex.domainSpace j), A ≤ K * (‖u - S.embD j v‖ + ‖(p : W j) - ((q : S.V j) : W j)‖ +
      μ * ‖H.boundaryPart j (H.domainIncl j u) - S.embD j w‖) +
      K * Metric.infDist σ (S.domainSub i) := by
    intro v q w
    refine le_add_mul_infDist (hne i) hK fun y hy => ?_
    obtain ⟨τ, rfl⟩ := hy
    have := hall τ v q w
    simp only [LinearIsometry.coe_toLinearMap]
    rw [dist_eq_norm]; change A ≤ _ at this; linarith
  have h2 : ∀ (q : S.toHilbertComplex.harmonic j) (w : S.toHilbertComplex.domainSpace j), A ≤ K * (‖(p : W j) - ((q : S.V j) : W j)‖ +
      μ * ‖H.boundaryPart j (H.domainIncl j u) - S.embD j w‖) +
      K * Metric.infDist σ (S.domainSub i) + K * Metric.infDist u (S.domainSub j) := by
    intro q w
    refine le_add_mul_infDist (hne j) hK fun y hy => ?_
    obtain ⟨v, rfl⟩ := hy
    have := h1 v q w
    simp only [LinearIsometry.coe_toLinearMap]
    rw [dist_eq_norm]; linarith
  have h3 : ∀ w : S.toHilbertComplex.domainSpace j, A ≤ K * (μ * ‖H.boundaryPart j (H.domainIncl j u) - S.embD j w‖) +
      K * Metric.infDist σ (S.domainSub i) + K * Metric.infDist u (S.domainSub j) +
      K * Metric.infDist (p : W j) (S.harmonicW j) := by
    intro w
    refine le_add_mul_infDist ⟨0, zero_mem _⟩ hK fun y hy => ?_
    have := h2 ⟨⟨y, S.harmonicW_le_V j hy⟩, S.mem_harmonic_iff.2 hy⟩ w
    rw [dist_eq_norm]; linarith
  have h4 : A ≤ K * Metric.infDist σ (S.domainSub i) + K * Metric.infDist u (S.domainSub j) +
      K * Metric.infDist (p : W j) (S.harmonicW j) +
      (K * μ) * Metric.infDist (H.boundaryPart j (H.domainIncl j u)) (S.domainSub j) := by
    refine le_add_mul_infDist (hne j) (mul_nonneg hK hμ0) fun y hy => ?_
    obtain ⟨w, rfl⟩ := hy
    have := h3 w
    simp only [LinearIsometry.coe_toLinearMap]
    rw [dist_eq_norm]; linarith
  linarith

/-- **The harmonic term in the graph norm**: for `q ∈ ℌʲ`,
`dist(q, ℌₕʲ) ≤ (1 + C) dist_V(q, Vₕʲ)` (`‖q - P_{ℌₕ} q‖ ≤ ‖(I - π) q‖`, [AFW2010], Thm 3.5). -/
theorem infDist_harmonicW_le {j k : ι} (hjk : c.Rel j k) {C : ℝ} (hC : 0 ≤ C)
    (hπ : P.IsGraphBounded j k C) {q : W j} (hq : q ∈ H.harmonic j) :
    Metric.infDist q (S.harmonicW j) ≤
      (1 + C) * Metric.infDist (cyclesToDomainSpace (H.harmonic_le_cycles j hq)) (S.domainSub j) := by
  have h := le_add_mul_infDist (A := Metric.infDist q (S.harmonicW j)) (B := 0)
    (x := cyclesToDomainSpace (H.harmonic_le_cycles j hq)) ⟨0, zero_mem (S.domainSub j)⟩
    (by linarith : (0 : ℝ) ≤ 1 + C) fun y hy => by
      obtain ⟨w, rfl⟩ := hy
      simp only [LinearIsometry.coe_toLinearMap]
      rw [zero_add, dist_eq_norm, ← Submodule.dist_starProjection_eq_infDist, dist_eq_norm]
      exact (P.norm_sub_starProjection_harmonicW_le hq).trans
        (P.norm_sub_π_le_of_mem_cycles hjk hC hπ _ w)
  rwa [zero_add] at h

/-- **Quasi-optimality in the form of [AFW2010], Thm 3.9**: the harmonic term measured by the
graph-norm distance of `p` to `Vₕʲ`,

`‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖ ≤ C' (E_V(σ) + E_V(u) + (1 + C) E_V(p) + μ E_V(P_𝔅 u))`.

This follows from `norm_sub_le_infDist` and `infDist_harmonicW_le`; the `infDist`-to-`ℌₕ` form
of `norm_sub_le_infDist` is the sharper one. -/
theorem norm_sub_le_infDist_domainSub {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k)
    {cP C μ : ℝ} (hC : 1 ≤ C) (hμ0 : 0 ≤ μ)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : P.IsGraphBounded i j C) (hπj : P.IsGraphBounded j k C)
    (hμ : ∀ q ∈ H.harmonic j, ‖q - P.π j q‖ ≤ μ * ‖q‖)
    {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j}
    (hs : H.IsMixedSolution i j k f σ u p) :
    ‖σ - S.embD i (discreteMixedSolution S hij hjk f).fst‖ +
        ‖u - S.embD j (discreteMixedSolution S hij hjk f).snd.fst‖ +
        ‖(p : W j) - (((discreteMixedSolution S hij hjk f).snd.snd : S.V j) : W j)‖ ≤
      (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) *
        (Metric.infDist σ (S.domainSub i) + Metric.infDist u (S.domainSub j) +
          (1 + C) * Metric.infDist (cyclesToDomainSpace (H.harmonic_le_cycles j p.2))
            (S.domainSub j) +
          μ * Metric.infDist (H.boundaryPart j (H.domainIncl j u)) (S.domainSub j)) := by
  have hK : 0 ≤ (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) := by
    have := zero_le_one.trans hC; positivity
  refine (P.norm_sub_le_infDist hij hjk hC hμ0 hPi hPj hπi hπj hμ hs).trans
    (mul_le_mul_of_nonneg_left ?_ hK)
  have := P.infDist_harmonicW_le hjk (zero_le_one.trans hC) hπj p.2
  linarith

/-- **Quasi-optimality with the harmonic gap** `μ = harmonicGap`: the same estimate with `μ` the
sup of `‖q - π q‖` over the unit ball of `ℌʲ` ([AFW2010], Thm 3.9). -/
theorem norm_sub_le_infDist_harmonicGap {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k)
    {cP C : ℝ} (hC : 1 ≤ C)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : P.IsGraphBounded i j C) (hπj : P.IsGraphBounded j k C)
    {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j}
    (hs : H.IsMixedSolution i j k f σ u p) :
    ‖σ - S.embD i (discreteMixedSolution S hij hjk f).fst‖ +
        ‖u - S.embD j (discreteMixedSolution S hij hjk f).snd.fst‖ +
        ‖(p : W j) - (((discreteMixedSolution S hij hjk f).snd.snd : S.V j) : W j)‖ ≤
      (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) *
        (Metric.infDist σ (S.domainSub i) + Metric.infDist u (S.domainSub j) +
          Metric.infDist (p : W j) (S.harmonicW j) +
          P.harmonicGap j * Metric.infDist (H.boundaryPart j (H.domainIncl j u)) (S.domainSub j)) :=
  P.norm_sub_le_infDist hij hjk hC (P.harmonicGap_nonneg j) hPi hPj hπi hπj
    (fun _ hq => P.norm_sub_le_harmonicGap_mul
      (fun _ hq' => P.norm_sub_π_harmonic_le hjk (zero_le_one.trans hC) hπj hq') hq) hs

end CochainProjection

end Subcomplex

end Feec.HilbertComplex
