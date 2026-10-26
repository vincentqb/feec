module

public import Feec.Models.Cube.Sobolev
public import Feec.Models.Cube.ParitySmoothingEstimates
public import Feec.HilbertComplex.Approximation.DiscreteCohomology

/-!
# Finite element rates in Sobolev norms on the cube

Rates of the finite element methods of every admissible sequence `S` (`Feec.FiniteElement.PolySeq`)
on the Freudenthal meshes of `Q = (0, ½)ⁿ` (mesh size `h_N = meshSize N`) for data in the Sobolev
spaces of `Feec.Models.Cube.Sobolev`, `0 ≤ s ≤ 1`. The forms of the finite element method live on
`cubeDomain n`; `toQ k` identifies them with the forms on `Geometry.Q (Fin n)` of the Sobolev
spaces.

**Method.** Truncate the Fourier series (of an extension, or of the parity extension) at
`M = N + 1 ≈ 1/(2h_N)`: `‖u - u_M‖ ≤ (2π(N + 2))^{-s} ‖u‖_s ≤ h_N^s ‖u‖_s`, and
`‖∇ u_M‖ ≲ M^{1-s} ‖u‖_s`; the `H¹` estimates of the smoothed interpolants
(`exists_mem_poly_near_grad`, `exists_mem_polyPartial_near_grad`) give
`dist(u_M, Vₕ) ≲ h_N ‖∇ u_M‖ ≲ h_N^s ‖u‖_s` (`meshSize_mul_rpow_le`). Through a uniformly bounded
cochain projection `π` this passes to the graph norm (`infDist_domainSub_le_proj`), to the mixed
Hodge Laplacian by quasi-optimality ([AFW2010], Thm 3.9) and to the semi-discrete Hodge wave
equation ([QuennevilleBelair2015], Thm 4.14).

## Main results

* **Best approximation**, `dist(y, Vₕᵏ) ≤ C h_N^s ‖y‖_s`, `C` independent of `N` and `s`:
  **`infDist_poly_le_sobolevQ`** (`HΛ(Q)`, `y ∈ Hˢ(Q)`), **`infDist_polyPartial_le_sobolevPar`**
  (`HΛ_J(Q)`, `y ∈ Hˢ_J(Q)`, every class `J`); `h^{min(s,1)}` for every `s ≥ 0`:
  `infDist_polyPartial_le_sobolevPar_min`.
* **Graph norm**: the Jackson estimate `sobolevJackson` of the complexes of `S` for `Hˢ(Q)`
  components (`SobComp`, from `SobGraph`), through the projections
  (`ConformingFamily.Jackson.ofInfDist`); `ParitySmoothingEstimates.infDist_domainSub_le_sobGraphPar`
  (`σ, dσ ∈ Hˢ`, `SobGraphPar`; degrees in `ℤ`, `SobAt`, `SobAtPar`).
* **Mixed Hodge–Laplace problem**: **`mixed_rate_sobolevQ`** (`HΛ(Q)`) and
  **`mixed_rate_sobolevPar`** (`HΛ_J(Q)`, in particular `H̊Λ(Q)` for `J = univ`):
  `‖σ - σₕ‖ + ‖u - uₕ‖ + ‖q - qₕ‖ ≤ K L h_N^s` when `σ, dσ, u, du, P_𝔅 u, d P_𝔅 u, q` have
  Sobolev norms `≤ L`, for every admissible sequence `S` (de Rham Hodge–Laplace rates for any
  element family, including those of the rows of Tables 5.1/6.1; the BGG elasticity/TSD rates of
  those tables are not restated here).
* **Semi-discrete Hodge wave equation** on every window, for solutions with uniform-in-time
  `Hˢ` bounds `L` on `[t₀, t₁]` (`L^∞([t₀, t₁]; Hˢ)`, e.g. `C⁰([t₀, t₁]; Hˢ)` solutions) on the
  values and time derivatives (and their differentials):
  **`PolySmoothingEstimates.norm_sub_le_window_sobolevQ`** (`HΛ(Q)`),
  **`ParitySmoothingEstimates.norm_sub_le_window_sobolevPar`** (`HΛ_J(Q)`),
  `‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² (m + m²) (1 + 2C) K L h_N^s`
  (smoothing estimates exist for every `S` and `J`: `polySmoothingEstimates_exists`,
  `paritySmoothing_exists`).

## Proved exponents and the optimal ones

`r` is the polynomial degree; the optimal `L²` best-approximation rate for `Hˢ` data is
`h^{min(s, r_eff)}`, `r_eff = s_S + 1` where `S` reproduces `P_{s_S}` in the degrees used
(`FEM.PolyOrder`, `FEM.PolyOrderAt`; `r_eff = r + 1` for `P_rΛᵏ`, `r` for `P_r⁻Λᵏ`).

| Setting | proved | optimal | what is missing |
|---|---|---|---|
| `HΛ(Q)`, `y ∈ Hˢ(Q)` | `h^{min(s,1)}` | `h^{min(s, r_eff)}` | for `s > 1`: an `L²` Bramble–Hilbert estimate `‖y - π y‖ ≲ hᵐ ‖Dᵐ y‖` for the no-boundary-condition smoother; only its `H¹` form (`norm_sub_proj_le_grad`) is available |
| `HΛ_J(Q)`, `H̊Λ(Q)`, `y ∈ Hˢ_J(Q)` | `h^{min(s,1)}` | `h^{min(s, r_eff)}` | for `s > 1`: the `L²` form of the high-order parity estimate; `norm_sub_proj_le_smooth` is in `sup_{cl Q} ‖D^{s+1} w‖`, which through the truncation would give only `h^{min(s, r_eff) - n/2}` (not formalized) |
| graph norm, `σ, dσ ∈ Hˢ` | `h^{min(s,1)}` | `h^{min(s, r_eff)}` | as above |
| mixed Hodge Laplacian | `h^s`, `s ≤ 1` | `h^{min(s, r_eff)}` | as above (the improved `L²` estimates of [AFW2010] are not combined with Sobolev data) |
| semi-discrete Hodge wave | `h^s`, `s ≤ 1` | `h^{min(s, r_eff)}` | as above |

For `s ≤ 1` the proved exponent is optimal. The `O(h^{s+1})` rates for `C^{s+2}` data are in
`Feec.Models.Cube.PolyRate` and `Feec.Models.Cube.ParitySmoothingEstimates`; the BGG rates of
Tables 5.1/6.1 (`Feec.Models.Cube.WeakSymmetryWave`, unconditional since `CurlPotential` is
proved, `Feec.Models.Cube.RegularDecomposition`) are not restated here for Sobolev data.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.9 (quasi-optimality of the mixed method), §5.5 (smoothed projections)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (approximation
  estimates)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.1 (Sobolev spaces)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Set MeasureTheory Filter Finset

@[expose] public noncomputable section

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement
open Feec.Models.Cube.Sobolev
open Feec.Models.Cube.DeRhamIdent (dPart Jinvf JfJ trunc)
open Feec.Models.Cube.Geometry (Q)

variable {n : ℕ}

/-! ### Transport between `cubeDomain n` and `Q (Fin n)` -/

/-- The identification `L²(Ω; ℝ^ι) = L²(Ω'; ℝ^ι)` along `Ω = Ω'`. -/
def castL2F {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (ι : Type) [Fintype ι] :
    L2F ℝ Ω ι ≃ₗᵢ[ℝ] L2F ℝ Ω' ι := by
  subst h; exact LinearIsometryEquiv.refl ℝ _

/-- `L²(cubeDomain n; Λᵏ) = L²(Q; Λᵏ)`: the forms of the finite element method as forms on the
cube `Q` of the Sobolev spaces. -/
abbrev toQ (k : ℤ) : L2F ℝ (cubeDomain n) (formIdx n k) ≃ₗᵢ[ℝ] L2F ℝ (Q (Fin n)) (formIdx n k) :=
  castL2F (cubeDomain_eq_Q n) _

theorem maximalComplex_d_zero {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) :
    ((deRham ℝ n).maximalComplex hΩ).d 0 1 = (extDerivOp ℝ n 0).maximal Ω :=
  deRham_maximalComplex_d hΩ 0

/-- **Transport of `H¹` coefficients, no boundary condition**. -/
theorem coeffForm_mem_of_eq {Ω : Set (Fin n → ℝ)} (h : Ω = Q (Fin n)) (hΩ : IsOpen Ω)
    {ι : Type} [Fintype ι] (z : L2F ℝ (Q (Fin n)) ι) (t : ι)
    (hz : zeroF (z t) ∈ ((extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n))).domain) :
    ∃ hz' : coeffForm ((castL2F h ι).symm z t) ∈ (((deRham ℝ n).maximalComplex hΩ).d 0 1).domain,
      ‖((deRham ℝ n).maximalComplex hΩ).d 0 1 ⟨_, hz'⟩‖ =
        ‖(extDerivOp ℝ n ((0 : ℕ) : ℤ)).maximal (Q (Fin n)) ⟨_, hz⟩‖ := by
  subst h
  have e := maximalComplex_d_zero (n := n) hΩ
  have hz' : coeffForm (z t) ∈ (((deRham ℝ n).maximalComplex hΩ).d 0 1).domain := by
    rw [e]; exact hz
  refine ⟨hz', ?_⟩
  change ‖((deRham ℝ n).maximalComplex hΩ).d 0 1 ⟨coeffForm (z t), hz'⟩‖ = _
  exact congrArg norm (LinearPMap.apply_eq_of_eq e ⟨_, hz'⟩ ⟨_, hz⟩ rfl)

/-- **Transport of `H¹` coefficients with vanishing traces on the faces normal to `J'`**. -/
theorem zeroForm_mem_dPart_of_eq {Ω : Set (Fin n → ℝ)} (h : Ω = Q (Fin n)) {ι : Type}
    [Fintype ι] (z : L2F ℝ (Q (Fin n)) ι) (t : ι) (J' : Finset (Fin n))
    (hz : zeroF (z t) ∈ (dPart (Q (Fin n)) J' ((0 : ℕ) : ℤ)).domain) :
    ∃ hz' : ParitySmoother.zeroForm ((castL2F h ι).symm z t) ∈
        (dPart Ω J' ((0 : ℕ) : ℤ)).domain,
      ‖dPart Ω J' ((0 : ℕ) : ℤ) ⟨_, hz'⟩‖ = ‖dPart (Q (Fin n)) J' ((0 : ℕ) : ℤ) ⟨_, hz⟩‖ := by
  subst h
  exact ⟨hz, rfl⟩

/-! ### Elementary bounds in the mesh size -/

theorem meshSize_le_half (N : ℕ) : meshSize N ≤ 1 / 2 := by
  unfold meshSize
  rw [div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ N := N.cast_nonneg
  nlinarith

theorem two_pi_mul_succ_eq (N : ℕ) : 2 * Real.pi * ((N + 1 : ℕ) : ℝ) = Real.pi / meshSize N := by
  unfold meshSize; push_cast; field_simp

/-- `(2π(N + 2))^{-s} ≤ h_N^s`. -/
theorem rpow_neg_le_meshSize_rpow {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    (2 * Real.pi * (((N + 1 : ℕ) : ℝ) + 1)) ^ (-s) ≤ meshSize N ^ s := by
  have hh := meshSize_pos N
  have hle : (meshSize N)⁻¹ ≤ 2 * Real.pi * (((N + 1 : ℕ) : ℝ) + 1) := by
    have e : (meshSize N)⁻¹ = 2 * ((N : ℝ) + 1) := by unfold meshSize; field_simp
    rw [e]
    push_cast
    have := Real.two_le_pi
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    nlinarith
  refine (rpow_le_rpow_of_nonpos (inv_pos.2 hh) hle (neg_nonpos.2 hs)).trans (le_of_eq ?_)
  rw [Real.inv_rpow hh.le, Real.rpow_neg hh.le, inv_inv]

/-- `h_N (1 + n (2π(N+1))²)^{(1-s)/2} ≤ (1 + n) π² h_N^s` for `0 ≤ s ≤ 1`. -/
theorem meshSize_mul_rpow_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (N : ℕ) :
    meshSize N * (1 + n * (2 * Real.pi * ((N + 1 : ℕ) : ℝ)) ^ 2) ^ ((1 - s) / 2) ≤
      ((1 + n) * Real.pi ^ 2) * meshSize N ^ s := by
  set h := meshSize N
  have hh : 0 < h := meshSize_pos N
  have hh2 : h ≤ 1 / 2 := meshSize_le_half N
  set A : ℝ := (1 + n) * Real.pi ^ 2
  have hA1 : 1 ≤ A := by
    have h4 : 4 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    calc (1 : ℝ) ≤ 1 * Real.pi ^ 2 := by linarith
      _ ≤ A := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have he0 : 0 ≤ (1 - s) / 2 := by linarith
  rw [two_pi_mul_succ_eq]
  have hb : 1 + n * (Real.pi / h) ^ 2 ≤ A / h ^ 2 := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
    have : h ^ 2 ≤ Real.pi ^ 2 := by
      have := Real.two_le_pi
      exact pow_le_pow_left₀ hh.le (by linarith) 2
    have : 0 ≤ (n : ℝ) := n.cast_nonneg
    rw [add_mul, one_mul, div_mul_cancel₀ _ (by positivity)]
    nlinarith
  have h1 := Real.rpow_le_rpow (by positivity) hb he0
  have h2 : (A / h ^ 2) ^ ((1 - s) / 2) = A ^ ((1 - s) / 2) / h ^ (1 - s) := by
    rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast h 2,
      ← Real.rpow_mul hh.le]
    norm_num
    ring_nf
  have h3 : A ^ ((1 - s) / 2) ≤ A := by
    calc A ^ ((1 - s) / 2) ≤ A ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
      _ = A := Real.rpow_one A
  have h4 : h / h ^ (1 - s) = h ^ s := by
    have := Real.rpow_sub hh 1 (1 - s)
    rw [Real.rpow_one] at this
    rw [← this]; ring_nf
  calc h * (1 + n * (Real.pi / h) ^ 2) ^ ((1 - s) / 2) ≤ h * (A ^ ((1 - s) / 2) / h ^ (1 - s)) :=
        mul_le_mul_of_nonneg_left (h1.trans (le_of_eq h2)) hh.le
    _ = A ^ ((1 - s) / 2) * (h / h ^ (1 - s)) := by ring
    _ ≤ A * h ^ s := by rw [h4]; exact mul_le_mul_of_nonneg_right h3 (by positivity)

theorem sum_le_sqrt_card_mul {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∑ i, a i ≤ √(Fintype.card ι) * √(∑ i, a i ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.le_sqrt_of_sq_le ?_
  have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := a)
  simpa using this

/-! ### Best approximation in `HΛ(Q)` for `Hˢ(Q)` data, `0 ≤ s ≤ 1` -/

variable (n) in
/-- The constant of the best-approximation estimate for `Hˢ(Q; Λᵏ)` data in the spaces of `S`. -/
def sobConst (S : PolySeq) (k : ℕ) : ℝ :=
  1 + h1Const n S k 1 * √(Fintype.card (formIdx n (k : ℤ))) * ((1 + n) * Real.pi ^ 2)

theorem sobConst_nonneg (S : PolySeq) (k : ℕ) : 0 ≤ sobConst n S k := by
  have := h1Const_nonneg (n := n) S k zero_le_one
  unfold sobConst; positivity

theorem sqrt_rpow_mul {a : ℝ} (ha : 0 ≤ a) (b e : ℝ) :
    √(a ^ e * b) = a ^ (e / 2) * √b := by
  rw [Real.sqrt_mul (Real.rpow_nonneg ha e), Real.sqrt_eq_rpow, ← Real.rpow_mul ha]
  ring_nf

variable [NeZero n]

/-- **Best approximation of `Hˢ(Q)` forms by the spaces of `S`, `0 ≤ s ≤ 1`** ([AFW2010],
§5.4; [Brezis2011], §9.1): for `y ∈ Hˢ(Q; Λᵏ)`,
`dist(y, Vₕᵏ) ≤ C h_N^s ‖y‖_{Hˢ(Q)}`, `C = sobConst n S k` independent of `N` and `s`.
The proof truncates the Fourier series of an extension at `M = N + 1 ≈ 1/(2h_N)`
(`norm_sub_Jinvf_trunc_le`, `grad_truncQ_le`) and applies the `H¹` estimate of the smoothed
interpolant (`exists_mem_poly_near_grad`) to the truncation. -/
theorem infDist_poly_le_sobolevQ (S : PolySeq) (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (N : ℕ) (y : L2F ℝ (cubeDomain n) (formIdx n k)) (hy : toQ k y ∈ sobolevQ n k s) :
    Metric.infDist y ((poly n S N).V k) ≤
      sobConst n S k * meshSize N ^ s * qNorm k s (toQ k y) := by
  have hh := meshSize_pos N
  refine le_mul_qNorm hy (mul_nonneg (sobConst_nonneg S k) (Real.rpow_nonneg hh.le s))
    fun x hx hxu => ?_
  set M := N + 1
  set z := Jinvf k (trunc M k x)
  obtain ⟨hg, hgs⟩ := grad_truncQ_le hs1 hx M
  set z' := (toQ k).symm z
  have hcoef := fun t => coeffForm_mem_of_eq (cubeDomain_eq_Q n) (isOpen_cubeDomain n) z t (hg t)
  choose hc hcn using hcoef
  obtain ⟨v, hv, hzv⟩ := exists_mem_poly_near_grad S one_pos le_rfl N k z' hc
  set σ := √(sobSum s x)
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  -- the truncation error
  have h1 : ‖y - z'‖ ≤ meshSize N ^ s * σ := by
    have e : ‖y - z'‖ = ‖Jinvf k x - z‖ := by
      rw [← (toQ k).norm_map, map_sub, LinearIsometryEquiv.apply_symm_apply, hxu]
    rw [e]
    refine (norm_sub_Jinvf_trunc_le hs0 hx M).trans ?_
    exact mul_le_mul_of_nonneg_right (rpow_neg_le_meshSize_rpow hs0 N) hσ
  -- the gradient of the truncation
  have h2 : ∑ t, ‖(complex n).d 0 1 ⟨coeffForm (z' t), hc t⟩‖ ≤
      √(Fintype.card (formIdx n (k : ℤ))) *
        ((1 + n * (2 * Real.pi * ((N + 1 : ℕ) : ℝ)) ^ 2) ^ ((1 - s) / 2) * σ) := by
    refine (le_of_eq (Finset.sum_congr rfl fun t _ => hcn t)).trans ?_
    refine (sum_le_sqrt_card_mul _).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    rw [← sqrt_rpow_mul (by positivity) (sobSum s x)]
    exact Real.sqrt_le_sqrt hgs
  have h3 : ‖z' - v‖ ≤ h1Const n S k 1 * √(Fintype.card (formIdx n (k : ℤ))) *
      ((1 + n) * Real.pi ^ 2) * meshSize N ^ s * σ := by
    refine hzv.trans ?_
    have hK := h1Const_nonneg (n := n) S k zero_le_one
    have h4 := meshSize_mul_rpow_le (n := n) hs0 hs1 N
    calc h1Const n S k 1 * meshSize N * ∑ t, ‖(complex n).d 0 1 ⟨coeffForm (z' t), hc t⟩‖ ≤
        h1Const n S k 1 * meshSize N * (√(Fintype.card (formIdx n (k : ℤ))) *
          ((1 + n * (2 * Real.pi * ((N + 1 : ℕ) : ℝ)) ^ 2) ^ ((1 - s) / 2) * σ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = h1Const n S k 1 * √(Fintype.card (formIdx n (k : ℤ))) * σ *
          (meshSize N * (1 + n * (2 * Real.pi * ((N + 1 : ℕ) : ℝ)) ^ 2) ^ ((1 - s) / 2)) := by
          ring
      _ ≤ h1Const n S k 1 * √(Fintype.card (formIdx n (k : ℤ))) * σ *
          (((1 + n) * Real.pi ^ 2) * meshSize N ^ s) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring
  calc Metric.infDist y ((poly n S N).V k) ≤ dist y v := Metric.infDist_le_dist_of_mem hv
    _ = ‖y - v‖ := dist_eq_norm y v
    _ ≤ ‖y - z'‖ + ‖z' - v‖ := norm_sub_le_norm_sub_add_norm_sub y z' v
    _ ≤ meshSize N ^ s * σ + h1Const n S k 1 * √(Fintype.card (formIdx n (k : ℤ))) *
          ((1 + n) * Real.pi ^ 2) * meshSize N ^ s * σ := add_le_add h1 h3
    _ = sobConst n S k * meshSize N ^ s * σ := by unfold sobConst; ring

/-! ### Best approximation in `HΛ_J(Q)` for the parity classes `Hˢ_J(Q)`, `0 ≤ s ≤ 1` -/

variable (n) in
/-- The constant of the best-approximation estimate for `Hˢ_J(Q; Λᵏ)` data in `V_{h,Γ_J}`. -/
def sobConstPar (S : PolySeq) (k : ℕ) : ℝ :=
  1 + h1ConstPar n S k * √(Fintype.card (formIdx n (k : ℤ))) * ((1 + n) * Real.pi ^ 2)

omit [NeZero n] in
theorem sobConstPar_nonneg (S : PolySeq) (k : ℕ) : 0 ≤ sobConstPar n S k := by
  have := h1ConstPar_nonneg (n := n) S k
  unfold sobConstPar; positivity

/-- **Best approximation of the parity classes by `V_{h,Γ_J}`, `0 ≤ s ≤ 1`**: for
`y ∈ Hˢ_J(Q; Λᵏ)` (the parity extension of the class `J` lies in `Hˢ(𝕋ⁿ)`),
`dist(y, V_{h,Γ_J}ᵏ) ≤ C h_N^s ‖y‖_{s,J}`, `C = sobConstPar n S k`. The truncation
`u_M` stays in the class (`truncPar`), its coefficients lie in `H¹` with the traces of the class
(`mem_sobolevPar_one_iff`), and the parity smoother's `H¹` estimate
(`exists_mem_polyPartial_near_grad`) applies. -/
theorem infDist_polyPartial_le_sobolevPar (S : PolySeq) (J : Finset (Fin n)) (k : ℕ) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (N : ℕ) (y : L2F ℝ (cubeDomain n) (formIdx n k))
    (hy : toQ k y ∈ sobolevPar J k s) :
    Metric.infDist y ((polyPartial n S N J).V k) ≤
      sobConstPar n S k * meshSize N ^ s * parNorm J k s (toQ k y) := by
  have hh := meshSize_pos N
  set u := toQ k y
  set M := N + 1
  set z := truncPar J k M u
  have hz1 : z ∈ sobolevPar J k 1 := truncPar_mem J k 1 M u
  have hg := (mem_sobolevPar_one_iff J k).1 hz1
  set z' := (toQ k).symm z
  have hcoef := fun t : formIdx n (k : ℤ) =>
    zeroForm_mem_dPart_of_eq (cubeDomain_eq_Q n) z t (symmDiff J t.1) (hg t)
  choose hc hcn using hcoef
  obtain ⟨v, hv, hzv⟩ := exists_mem_polyPartial_near_grad S J N k z' hc
  set σ := parNorm J k s u
  have hσ : 0 ≤ σ := parNorm_nonneg J k s u
  have h1 : ‖y - z'‖ ≤ meshSize N ^ s * σ := by
    have e : ‖y - z'‖ = ‖u - z‖ := by
      rw [← (toQ k).norm_map, map_sub, LinearIsometryEquiv.apply_symm_apply]
    rw [e]
    refine (norm_sub_truncPar_le J k hs0 hy M).trans ?_
    exact mul_le_mul_of_nonneg_right (rpow_neg_le_meshSize_rpow hs0 N) hσ
  have h2 : ∑ t : formIdx n (k : ℤ), ‖dPart (cubeDomain n) (symmDiff J t.1) ((0 : ℕ) : ℤ)
      ⟨ParitySmoother.zeroForm (z' t), hc t⟩‖ ≤ √(Fintype.card (formIdx n (k : ℤ))) *
        ((1 + n * (2 * Real.pi * ((N + 1 : ℕ) : ℝ)) ^ 2) ^ ((1 - s) / 2) * σ) := by
    refine (le_of_eq (Finset.sum_congr rfl fun t _ => hcn t)).trans ?_
    refine (sum_le_sqrt_card_mul _).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    rw [← Real.sqrt_sq hσ, ← sqrt_rpow_mul (by positivity) (σ ^ 2)]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ t : formIdx n (k : ℤ), ‖dPart (Q (Fin n)) (symmDiff J t.1) ((0 : ℕ) : ℤ)
          ⟨zeroF (z t), hg t⟩‖ ^ 2 ≤
        ‖z‖ ^ 2 + ∑ t : formIdx n (k : ℤ), ‖dPart (Q (Fin n)) (symmDiff J t.1) ((0 : ℕ) : ℤ)
          ⟨zeroF (z t), hg t⟩‖ ^ 2 := le_add_of_nonneg_left (sq_nonneg _)
      _ = parNorm J k 1 z ^ 2 := (parNorm_one_sq J k hz1).symm
      _ ≤ _ := parNorm_truncPar_sq_le J k hs1 hy M
  have h3 : ‖z' - v‖ ≤ h1ConstPar n S k * √(Fintype.card (formIdx n (k : ℤ))) *
      ((1 + n) * Real.pi ^ 2) * meshSize N ^ s * σ := by
    refine hzv.trans ?_
    have hK := h1ConstPar_nonneg (n := n) S k
    have h4 := meshSize_mul_rpow_le (n := n) hs0 hs1 N
    calc h1ConstPar n S k * meshSize N * ∑ t : formIdx n (k : ℤ),
          ‖dPart (cubeDomain n) (symmDiff J t.1) ((0 : ℕ) : ℤ)
            ⟨ParitySmoother.zeroForm (z' t), hc t⟩‖ ≤
        h1ConstPar n S k * meshSize N * (√(Fintype.card (formIdx n (k : ℤ))) *
          ((1 + n * (2 * Real.pi * ((N + 1 : ℕ) : ℝ)) ^ 2) ^ ((1 - s) / 2) * σ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = h1ConstPar n S k * √(Fintype.card (formIdx n (k : ℤ))) * σ *
          (meshSize N * (1 + n * (2 * Real.pi * ((N + 1 : ℕ) : ℝ)) ^ 2) ^ ((1 - s) / 2)) := by
          ring
      _ ≤ h1ConstPar n S k * √(Fintype.card (formIdx n (k : ℤ))) * σ *
          (((1 + n) * Real.pi ^ 2) * meshSize N ^ s) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring
  calc Metric.infDist y ((polyPartial n S N J).V k) ≤ dist y v := Metric.infDist_le_dist_of_mem hv
    _ = ‖y - v‖ := dist_eq_norm y v
    _ ≤ ‖y - z'‖ + ‖z' - v‖ := norm_sub_le_norm_sub_add_norm_sub y z' v
    _ ≤ meshSize N ^ s * σ + h1ConstPar n S k * √(Fintype.card (formIdx n (k : ℤ))) *
          ((1 + n) * Real.pi ^ 2) * meshSize N ^ s * σ := add_le_add h1 h3
    _ = sobConstPar n S k * meshSize N ^ s * σ := by unfold sobConstPar; ring

/-- **The rate `h^{min(s,1)}` for every `s ≥ 0`** in the parity classes. -/
theorem infDist_polyPartial_le_sobolevPar_min (S : PolySeq) (J : Finset (Fin n)) (k : ℕ)
    {s : ℝ} (hs0 : 0 ≤ s) (N : ℕ) (y : L2F ℝ (cubeDomain n) (formIdx n k))
    (hy : toQ k y ∈ sobolevPar J k s) :
    Metric.infDist y ((polyPartial n S N J).V k) ≤
      sobConstPar n S k * meshSize N ^ min s 1 * parNorm J k s (toQ k y) := by
  have hm : min s 1 ≤ s := min_le_left _ _
  refine (infDist_polyPartial_le_sobolevPar S J k (le_min hs0 zero_le_one) (min_le_right _ _) N y
    (sobolevPar_anti J k hm hy)).trans ?_
  exact mul_le_mul_of_nonneg_left (parNorm_mono J k hm hy)
    (mul_nonneg (sobConstPar_nonneg S k) (Real.rpow_nonneg (meshSize_pos N).le _))

/-! ### Cochain projections and graph-norm distances -/

section Projection

variable {𝕜 : Type*} [RCLike 𝕜] {V : ℤ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up ℤ) V} {S' : H.Subcomplex}

/-- **A bounded cochain projection is quasi-optimal**: `‖y - π y‖ ≤ (1 + 2C) dist(y, Vₕ)`, the
case `2C` of `Subcomplex.CochainProjection.norm_sub_π_le_infDist`. -/
theorem norm_sub_π_le_infDist (P : S'.CochainProjection) {C : ℝ} (hC : 0 ≤ 2 * C) {i : ℤ}
    (hπ : ∀ x, ‖P.π i x‖ ≤ 2 * C * ‖x‖) (y : V i) :
    ‖y - P.π i y‖ ≤ (1 + 2 * C) * Metric.infDist y (S'.V i) :=
  P.norm_sub_π_le_infDist hC hπ y

/-- **Graph-norm distance through a cochain projection**: for `σ ∈ D(dʲ)`,
`dist_V(σ, Vₕʲ) ≤ (1 + 2C) (dist(σ, Vₕʲ) + dist(dσ, Vₕʲ⁺¹))` (`π` commutes with `d`). -/
theorem infDist_domainSub_le_proj [∀ i, FiniteDimensional 𝕜 (S'.V i)] (P : S'.CochainProjection)
    {C : ℝ} (hC : 0 ≤ 2 * C) (hπ : ∀ i x, ‖P.π i x‖ ≤ 2 * C * ‖x‖) (j : ℤ)
    (σ : H.domainSpace j) :
    Metric.infDist σ (S'.domainSub j) ≤ (1 + 2 * C) *
      (Metric.infDist (H.domainIncl j σ) (S'.V j) +
        Metric.infDist (H.d j (j + 1) (H.domainCoord j (j + 1) σ)) (S'.V (j + 1))) := by
  have hrel : (ComplexShape.up ℤ).Rel j (j + 1) := rfl
  refine (Subcomplex.infDist_domainSub_le S' hrel σ (P.mem j (H.domainIncl j σ))).trans ?_
  have hcomm := P.comm j (j + 1) (H.domainCoord j (j + 1) σ)
  have e : H.d j (j + 1) ⟨P.π j (H.domainIncl j σ),
      S'.le_domain j (j + 1) (P.mem j (H.domainIncl j σ))⟩ =
        P.π (j + 1) (H.d j (j + 1) (H.domainCoord j (j + 1) σ)) := hcomm
  rw [e, mul_add]
  exact add_le_add (norm_sub_π_le_infDist P hC (hπ j) _) (norm_sub_π_le_infDist P hC (hπ _) _)

/-- **Componentwise approximation through a cochain projection**, in the form used for the
graph spaces of windows (`Subcomplex.exists_mem_graphSub_le`). -/
theorem exists_mem_le_proj (P : S'.CochainProjection) {C : ℝ} (hC : 0 ≤ 2 * C)
    (hπ : ∀ i x, ‖P.π i x‖ ≤ 2 * C * ‖x‖) {j : ℤ} (x : V j) {ε : ℝ}
    (h0 : (1 + 2 * C) * Metric.infDist x (S'.V j) ≤ ε)
    (h1 : ∀ hx : x ∈ (H.d j (j + 1)).domain,
      (1 + 2 * C) * Metric.infDist (H.d j (j + 1) ⟨x, hx⟩) (S'.V (j + 1)) ≤ ε) (hε : 0 ≤ ε) :
    ∃ v, ∃ hv : v ∈ S'.V j, ‖x - v‖ ≤ ε ∧
      ∀ j' (hxj : x ∈ (H.d j j').domain),
        ‖H.d j j' ⟨x - v, Submodule.sub_mem _ hxj (S'.le_domain j j' hv)⟩‖ ≤ ε := by
  refine ⟨P.π j x, P.mem j x, (norm_sub_π_le_infDist P hC (hπ j) x).trans h0, fun j' hxj => ?_⟩
  by_cases hjj : (ComplexShape.up ℤ).Rel j j'
  · obtain rfl : j + 1 = j' := hjj
    have e : H.d j (j + 1) ⟨x - P.π j x, Submodule.sub_mem _ hxj (S'.le_domain j (j + 1)
        (P.mem j x))⟩ = H.d j (j + 1) ⟨x, hxj⟩ - P.π (j + 1) (H.d j (j + 1) ⟨x, hxj⟩) := by
      rw [← P.comm j (j + 1) ⟨x, hxj⟩, ← LinearPMap.map_sub]
      rfl
    rw [e]
    exact (norm_sub_π_le_infDist P hC (hπ _) _).trans (h1 hxj)
  · rw [LinearPMap.apply_eq_zero_of_eq_zero (H.shape j j' hjj), norm_zero]
    exact hε

/-- **The mixed error from four graph-norm distances** ([AFW2010], Thm 3.9): with a cochain
projection bounded by `C ≥ 1` in the graph norm and a Poincaré constant `c_P`, if `σ`, `u`,
`P_𝔅 u` and the harmonic part `p` are within `T` of the discrete spaces in the graph norm, the
error of the discrete mixed solution is `≤ (1 + 144 (C √(1 + c_P²))²) (1 + C) (4 + 2C) T`. -/
theorem norm_sub_discreteMixedSolution_le [∀ i, FiniteDimensional 𝕜 (S'.V i)]
    (P : S'.CochainProjection) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP C : ℝ} (hC : 1 ≤ C)
    (hPi : ∀ z : (H.d i j).domain, (z : V i) ∈ (H.cycles i)ᗮ → ‖(z : V i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : V j) ∈ (H.cycles j)ᗮ → ‖(z : V j)‖ ≤ cP * ‖H.d j k z‖)
    (hπi : P.IsGraphBounded i j C) (hπj : P.IsGraphBounded j k C)
    {f : V j} {σ : H.domainSpace i} {u : H.domainSpace j} {p : H.harmonic j}
    (hs : H.IsMixedSolution i j k f σ u p) {T : ℝ}
    (hσ : Metric.infDist σ (S'.domainSub i) ≤ T) (hu : Metric.infDist u (S'.domainSub j) ≤ T)
    (hp : Metric.infDist (cyclesToDomainSpace (H.harmonic_le_cycles j p.2)) (S'.domainSub j) ≤ T)
    (hB : Metric.infDist (H.boundaryPart j (H.domainIncl j u)) (S'.domainSub j) ≤ T) :
    ‖σ - S'.embD i (Subcomplex.CochainProjection.discreteMixedSolution S' hij hjk f).fst‖ +
        ‖u - S'.embD j (Subcomplex.CochainProjection.discreteMixedSolution S' hij hjk f).snd.fst‖ +
        ‖(p : V j) - (((Subcomplex.CochainProjection.discreteMixedSolution S' hij hjk f).snd.snd :
          S'.V j) : V j)‖ ≤
      (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) * (4 + 2 * C) * T := by
  have hC0 : 0 ≤ 1 + C := by linarith
  refine (P.norm_sub_le_infDist_domainSub hij hjk hC hC0 hPi hPj hπi hπj
    (fun _ hq => P.norm_sub_π_harmonic_le hjk (by linarith) hπj hq) hs).trans ?_
  rw [show (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) * (4 + 2 * C) * T =
    (1 + 144 * (C * √(1 + cP ^ 2)) ^ 2) * (1 + C) * ((4 + 2 * C) * T) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hC0)
  have h1 := mul_le_mul_of_nonneg_left hp hC0
  have h2 := mul_le_mul_of_nonneg_left hB hC0
  linarith

end Projection

/-! ### Sobolev data in every degree -/

variable (n) in
/-- **`Hˢ(Q)` data with bound `L` in degree `j ∈ ℤ`**: for `j = k ≥ 0`, `y ∈ Hˢ(Q; Λᵏ)` with
`‖y‖_{Hˢ(Q)} ≤ L`; no condition in negative degrees (the spaces are `0`). -/
def SobAt (s L : ℝ) : (j : ℤ) → L2F ℝ (cubeDomain n) (formIdx n j) → Prop
  | Int.ofNat k, y => toQ k y ∈ sobolevQ n k s ∧ qNorm k s (toQ k y) ≤ L
  | Int.negSucc _, _ => True

variable (n) in
/-- The constant `sobConst` in degree `j ∈ ℤ` (`0` in negative degrees). -/
def sobConstZ (S : PolySeq) : ℤ → ℝ
  | Int.ofNat k => sobConst n S k
  | Int.negSucc _ => 0

omit [NeZero n] in
theorem sobConstZ_nonneg (S : PolySeq) (j : ℤ) : 0 ≤ sobConstZ n S j := by
  rcases j with k | k
  · exact sobConst_nonneg S k
  · exact le_rfl

omit [NeZero n] in
theorem sobAt_zero {s L : ℝ} (hL : 0 ≤ L) (j : ℤ) : SobAt n s L j 0 := by
  rcases j with k | k
  · refine ⟨by rw [map_zero]; exact Submodule.zero_mem _, ?_⟩
    rw [map_zero]
    refine (qNorm_le (memSob_zero_seq s) (map_zero _)).trans ?_
    simp [sobSum, cf_zero, hL]
  · trivial

/-- **Best approximation in every degree** for `Hˢ(Q)` data (`0 ≤ s ≤ 1`). -/
theorem infDist_poly_le_sobAt (S : PolySeq) {s L : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (N : ℕ)
    {j : ℤ} {y : L2F ℝ (cubeDomain n) (formIdx n j)} (hy : SobAt n s L j y) :
    Metric.infDist y ((poly n S N).V j) ≤ sobConstZ n S j * meshSize N ^ s * L := by
  rcases j with k | k
  · obtain ⟨h1, h2⟩ := hy
    refine (infDist_poly_le_sobolevQ S k hs0 hs1 N y h1).trans ?_
    exact mul_le_mul_of_nonneg_left h2
      (mul_nonneg (sobConst_nonneg S k) (Real.rpow_nonneg (meshSize_pos N).le s))
  · have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    rw [Subsingleton.elim y 0, Metric.infDist_zero_of_mem (Submodule.zero_mem _)]
    simp [sobConstZ]

variable (n) in
/-- **`Hˢ(Q)` data in the graph norm**: `σ ∈ D(dʲ)` with `σ, dσ` in `Hˢ(Q)`, norms `≤ L`. -/
def SobGraph (s L : ℝ) {j : ℤ} (σ : (complex n).domainSpace j) : Prop :=
  SobAt n s L j ((complex n).domainIncl j σ) ∧
    SobAt n s L (j + 1) ((complex n).d j (j + 1) ((complex n).domainCoord j (j + 1) σ))

/-! ### The mixed Hodge Laplacian with `Hˢ(Q)` solutions -/

variable (n) in
/-- **A component with `Hˢ(Q)` data in the graph norm**: `x ∈ Hˢ(Q)` and, if `x ∈ D(d)`,
`dx ∈ Hˢ(Q)`, norms `≤ L`. -/
def SobComp (s L : ℝ) {j : ℤ} (x : L2F ℝ (cubeDomain n) (formIdx n j)) : Prop :=
  SobAt n s L j x ∧ ∀ hx : x ∈ ((complex n).d j (j + 1)).domain,
    SobAt n s L (j + 1) ((complex n).d j (j + 1) ⟨x, hx⟩)

omit [NeZero n] in
/-- `σ ∈ D(d)` with `σ, dσ ∈ Hˢ(Q)` is an `Hˢ(Q)` component. -/
theorem SobGraph.sobComp {s L : ℝ} {j : ℤ} {σ : (complex n).domainSpace j}
    (hσ : SobGraph n s L σ) : SobComp n s L ((complex n).domainIncl j σ) :=
  ⟨hσ.1, fun _ => hσ.2⟩

omit [NeZero n] in
/-- A cycle with `Hˢ(Q)` data is an `Hˢ(Q)` component (`d q = 0`). -/
theorem SobAt.sobComp_of_mem_cycles {s L : ℝ} (hL : 0 ≤ L) {j : ℤ}
    {q : L2F ℝ (cubeDomain n) (formIdx n j)} (h : SobAt n s L j q) (hq : q ∈ (complex n).cycles j) :
    SobComp n s L q :=
  ⟨h, fun hx => by rw [(complex n).d_eq_zero_of_mem_cycles hq hx]; exact sobAt_zero hL _⟩

variable (n) in
/-- **The Jackson estimate of the complexes of `S` for `Hˢ(Q)` data, `0 ≤ s ≤ 1`**: `Hˢ(Q)`
components (`SobComp`) at the order `h_N^s`, from the best approximation `infDist_poly_le_sobAt`
through the projections (`ConformingFamily.Jackson.ofInfDist`). -/
def sobolevJackson (S : PolySeq) : (polyFamily n S).Jackson (Set.Icc (0 : ℝ) 1) :=
  .ofInfDist _ meshSize (fun N => (meshSize_pos N).le) tendsto_meshSize
    (fun s _ L x => SobComp n s L x) (fun s => s) (fun _ j => sobConstZ n S j + sobConstZ n S (j + 1))
    (fun _ _ => add_nonneg (sobConstZ_nonneg S _) (sobConstZ_nonneg S _))
    fun s N i L x hL hx => by
      have h0 := sobConstZ_nonneg (n := n) S i
      have h1 := sobConstZ_nonneg (n := n) S (i + 1)
      have hh := mul_nonneg hL (Real.rpow_nonneg (meshSize_pos N).le (s : ℝ))
      refine ⟨(infDist_poly_le_sobAt S s.2.1 s.2.2 N hx.1).trans (by nlinarith),
        fun j hij hxj => ?_⟩
      obtain rfl : i + 1 = j := hij
      exact (infDist_poly_le_sobAt S s.2.1 s.2.2 N (hx.2 hxj)).trans (by nlinarith)

/-- **Convergence of order `h^s` of the mixed method for `Hˢ(Q)` solutions, `0 ≤ s ≤ 1`**
([AFW2010], Thm 3.9, with the best-approximation estimate `infDist_poly_le_sobolevQ`): for every
admissible sequence `S`, if `σ, dσ, u, du, P_𝔅 u, d P_𝔅 u` and the harmonic part `q` lie in `Hˢ(Q)`
with norms `≤ L`, the error of the discrete mixed solution is `≤ K L h_N^s`, `K` independent of
`N` and of the solution. -/
theorem mixed_rate_sobolevQ (S : PolySeq) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j},
    (complex n).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    SobGraph n s L σ → SobGraph n s L u →
    SobGraph n s L ((complex n).boundaryPart j ((complex n).domainIncl j u)) →
    SobAt n s L j (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (poly n S N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).fst‖ +
        ‖u - (poly n S N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (poly n S N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n S N) hij hjk f).snd.snd :
            (poly n S N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N ^ s := by
  obtain ⟨K, hK⟩ := ((polyFamily n S).staticFEEC closedRangeAt j).rate (sobolevJackson n S)
    ⟨s, hs0, hs1⟩ hij hjk
  refine ⟨K, fun {f σ u q} hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL hσ.sobComp hu.sobComp hb.sobComp
    (hq.sobComp_of_mem_cycles hL ((complex n).harmonic_le_cycles j q.2)) N
  simp only [polyFamily_V] at h
  exact h

/-! ### The semi-discrete Hodge wave equation with uniformly `Hˢ(Q)`-bounded solutions -/

/-- **Graph-norm approximation in the total space of a window** for `Hˢ(Q)` components. -/
theorem PolySmoothingEstimates.exists_mem_window_le_sob {S : PolySeq}
    {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimates n S p C) {s L : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hL0 : 0 ≤ L) {a : ℤ} {m : ℕ}
    (ζ : ((complex n).window a m).totalD.GraphSpace)
    (hζ : ∀ i : Fin m, SobComp n s L (((complex n).window a m).totalD.graphFst ζ i)) (N : ℕ) :
    ∃ w ∈ ((poly n S N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * ((1 + 2 * C) * (∑ i : Fin m, (sobConstZ n S (a + i) +
        sobConstZ n S (a + i + 1))) * meshSize N ^ s * L) := by
  obtain ⟨x, rfl, -, -⟩ := ((complex n).window a m).totalD.exists_toGraphSpace_eq ζ
  simp only [LinearPMap.graphFst_toGraphSpace] at hζ
  have hC := hE.two_mul_nonneg
  have hh := Real.rpow_nonneg (meshSize_pos N).le s
  set K := ∑ i : Fin m, (sobConstZ n S (a + i) + sobConstZ n S (a + i + 1))
  have hKi : ∀ i : Fin m, sobConstZ n S (a + i) + sobConstZ n S (a + i + 1) ≤ K := fun i =>
    Finset.single_le_sum (f := fun i : Fin m => sobConstZ n S (a + i) + sobConstZ n S (a + i + 1))
      (fun i _ => add_nonneg (sobConstZ_nonneg S _) (sobConstZ_nonneg S _)) (Finset.mem_univ i)
  have hε : 0 ≤ (1 + 2 * C) * K * meshSize N ^ s * L := by
    have : 0 ≤ K := Finset.sum_nonneg fun i _ =>
      add_nonneg (sobConstZ_nonneg S _) (sobConstZ_nonneg S _)
    have : 0 ≤ 1 + 2 * C := by linarith
    positivity
  obtain ⟨w, hw, hlt⟩ := Subcomplex.exists_mem_graphSub_le ((poly n S N).window a m) x
    (ε := (1 + 2 * C) * K * meshSize N ^ s * L) fun i => by
      set xi := (x : PiLp 2 fun i : Fin m => L2F ℝ (cubeDomain n) (formIdx n (a + i))) i
      have h0 := infDist_poly_le_sobAt S hs0 hs1 N (hζ i).1
      have hA : (1 + 2 * C) * Metric.infDist xi ((poly n S N).V (a + i)) ≤
          (1 + 2 * C) * K * meshSize N ^ s * L := by
        have hs := sobConstZ_nonneg (n := n) S (a + i + 1)
        calc (1 + 2 * C) * Metric.infDist xi ((poly n S N).V (a + i)) ≤
            (1 + 2 * C) * (sobConstZ n S (a + i) * meshSize N ^ s * L) :=
              mul_le_mul_of_nonneg_left h0 (by linarith)
          _ ≤ (1 + 2 * C) * K * meshSize N ^ s * L := by
              rw [mul_assoc (1 + 2 * C) K, mul_assoc (1 + 2 * C) (K * _)]
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              rw [mul_assoc, mul_assoc]
              exact mul_le_mul_of_nonneg_right (by linarith [hKi i]) (mul_nonneg hh hL0)
      have hB : ∀ hx : xi ∈ ((complex n).d (a + i) (a + i + 1)).domain,
          (1 + 2 * C) * Metric.infDist ((complex n).d (a + i) (a + i + 1) ⟨xi, hx⟩)
            ((poly n S N).V (a + i + 1)) ≤ (1 + 2 * C) * K * meshSize N ^ s * L := by
        intro hx
        have h1 := infDist_poly_le_sobAt S hs0 hs1 N ((hζ i).2 hx)
        have hs := sobConstZ_nonneg (n := n) S (a + i)
        calc (1 + 2 * C) * Metric.infDist ((complex n).d (a + i) (a + i + 1) ⟨xi, hx⟩)
              ((poly n S N).V (a + i + 1)) ≤
            (1 + 2 * C) * (sobConstZ n S (a + i + 1) * meshSize N ^ s * L) :=
              mul_le_mul_of_nonneg_left h1 (by linarith)
          _ ≤ (1 + 2 * C) * K * meshSize N ^ s * L := by
              rw [mul_assoc (1 + 2 * C) K, mul_assoc (1 + 2 * C) (K * _)]
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              rw [mul_assoc, mul_assoc]
              exact mul_le_mul_of_nonneg_right (by linarith [hKi i]) (mul_nonneg hh hL0)
      obtain ⟨v, hv, h1, h2⟩ := exists_mem_le_proj (hE.proj N) hC (hE.norm_proj_le N)
        (j := a + i) xi hA hB hε
      exact ⟨v, hv, h1, fun j hx => h2 (a + j) hx⟩
  refine ⟨w, hw, hlt.trans (le_of_eq ?_)⟩
  rw [Fintype.card_fin]

/-- **Convergence of order `h^s` of the semi-discrete Hodge wave equation for solutions bounded
in `Hˢ(Q)` uniformly on `[t₀, t₁]` (e.g. `C⁰([t₀, t₁]; Hˢ(Q))`), `0 ≤ s ≤ 1`**
([QuennevilleBelair2015], Thm 4.14), on every window of `HΛ(Q)`: if the values and time derivatives of the weak solution have `Hˢ(Q)` components
(and differentials) with bound `L` on `[t₀, t₁]`, then
`‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² (m + m²) (1 + 2C) K L h_N^s`. -/
theorem PolySmoothingEstimates.norm_sub_le_window_sobolevQ {S : PolySeq}
    {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimates n S p C) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (a : ℤ) (m : ℕ) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((poly n S N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((poly n S N).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      SobComp n s L (((complex n).window a m).totalD.graphFst (ξ τ) i) ∧
        SobComp n s L (((complex n).window a m).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complex n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complex n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 * (((m : ℝ) + m * m) * ((1 + 2 * C) * (∑ i : Fin m,
          (sobConstZ n S (a + i) + sobConstZ n S (a + i + 1))) * meshSize N ^ s * L)) :=
  ((poly n S N).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (fun τ hτ =>
    ⟨hE.exists_mem_window_le_sob hs0 hs1 hL0 (ξ τ) (fun i => (hreg τ hτ i).1) N,
      hE.exists_mem_window_le_sob hs0 hs1 hL0 (ξ' τ) (fun i => (hreg τ hτ i).2) N⟩) ht

/-! ### The parity classes: `HΛ_J(Q)` with `Hˢ_J(Q)` data -/

section Parity

variable (J : Finset (Fin n))

variable (n) in
/-- **`Hˢ_J(Q)` data with bound `L` in degree `j ∈ ℤ`** (no condition in negative degrees). -/
def SobAtPar (s L : ℝ) : (j : ℤ) → L2F ℝ (cubeDomain n) (formIdx n j) → Prop
  | Int.ofNat k, y => toQ k y ∈ sobolevPar J k s ∧ parNorm J k s (toQ k y) ≤ L
  | Int.negSucc _, _ => True

variable (n) in
/-- The constant `sobConstPar` in degree `j ∈ ℤ` (`0` in negative degrees). -/
def sobConstParZ (S : PolySeq) : ℤ → ℝ
  | Int.ofNat k => sobConstPar n S k
  | Int.negSucc _ => 0

omit [NeZero n] in
theorem sobConstParZ_nonneg (S : PolySeq) (j : ℤ) : 0 ≤ sobConstParZ n S j := by
  rcases j with k | k
  · exact sobConstPar_nonneg S k
  · exact le_rfl

omit [NeZero n] in
theorem sobAtPar_zero {s L : ℝ} (hL : 0 ≤ L) (j : ℤ) : SobAtPar n J s L j 0 := by
  rcases j with k | k
  · refine ⟨by rw [map_zero]; exact Submodule.zero_mem _, ?_⟩
    rw [map_zero, parNorm, map_zero]
    simpa [sobSum, cf_zero] using hL
  · trivial

/-- **Best approximation in every degree** for `Hˢ_J(Q)` data (`0 ≤ s ≤ 1`). -/
theorem infDist_polyPartial_le_sobAtPar (S : PolySeq) {s L : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (N : ℕ) {j : ℤ} {y : L2F ℝ (cubeDomain n) (formIdx n j)} (hy : SobAtPar n J s L j y) :
    Metric.infDist y ((polyPartial n S N J).V j) ≤ sobConstParZ n S j * meshSize N ^ s * L := by
  rcases j with k | k
  · obtain ⟨h1, h2⟩ := hy
    refine (infDist_polyPartial_le_sobolevPar S J k hs0 hs1 N y h1).trans ?_
    exact mul_le_mul_of_nonneg_left h2
      (mul_nonneg (sobConstPar_nonneg S k) (Real.rpow_nonneg (meshSize_pos N).le s))
  · have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    rw [Subsingleton.elim y 0, Metric.infDist_zero_of_mem (Submodule.zero_mem _)]
    simp [sobConstParZ]

variable (n) in
/-- **`Hˢ_J(Q)` data in the graph norm of `HΛ_J(Q)`**. -/
def SobGraphPar (s L : ℝ) {j : ℤ} (σ : (complexPart n J).domainSpace j) : Prop :=
  SobAtPar n J s L j ((complexPart n J).domainIncl j σ) ∧
    SobAtPar n J s L (j + 1)
      ((complexPart n J).d j (j + 1) ((complexPart n J).domainCoord j (j + 1) σ))

variable {J} in
/-- **Graph-norm best approximation in `HΛ_J(Q)`** through the parity-smoothed projections. -/
theorem ParitySmoothingEstimates.infDist_domainSub_le_sobGraphPar {S : PolySeq}
    {ρ : ℕ → ParitySmoother.ReflKernel n} {C : ℝ} (hE : ParitySmoothingEstimates n J S ρ C)
    {s L : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (N : ℕ) {j : ℤ}
    {σ : (complexPart n J).domainSpace j} (hσ : SobGraphPar n J s L σ) :
    Metric.infDist σ ((polyPartial n S N J).domainSub j) ≤
      (1 + 2 * C) * (sobConstParZ n S j + sobConstParZ n S (j + 1)) * meshSize N ^ s * L := by
  refine (infDist_domainSub_le_proj (hE.proj N) hE.two_mul_nonneg (hE.norm_proj_le N) j σ).trans ?_
  have h1 := infDist_polyPartial_le_sobAtPar J S hs0 hs1 N hσ.1
  have h2 := infDist_polyPartial_le_sobAtPar J S hs0 hs1 N hσ.2
  have := hE.two_mul_nonneg
  calc (1 + 2 * C) * (Metric.infDist ((complexPart n J).domainIncl j σ)
        ((polyPartial n S N J).V j) +
        Metric.infDist ((complexPart n J).d j (j + 1) ((complexPart n J).domainCoord j (j + 1) σ))
          ((polyPartial n S N J).V (j + 1))) ≤
      (1 + 2 * C) * (sobConstParZ n S j * meshSize N ^ s * L +
        sobConstParZ n S (j + 1) * meshSize N ^ s * L) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by linarith)
    _ = _ := by ring

set_option maxHeartbeats 400000 in
/-- **Convergence of order `h^s` of the mixed method in `HΛ_J(Q)` for `Hˢ_J(Q)` solutions,
`0 ≤ s ≤ 1`**, for every class `J` (`J = univ`: `H̊Λ(Q)`; `J = ∅`: `HΛ(Q)` with parity data) and
every admissible sequence ([AFW2010], Thm 3.9, with the parity smoother and the Poincaré
inequality of `HΛ_J(Q)`). -/
theorem mixed_rate_sobolevPar (S : PolySeq) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complexPart n J).domainSpace i}
    {u : (complexPart n J).domainSpace j} {q : (complexPart n J).harmonic j},
    (complexPart n J).IsMixedSolution i j k f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    SobGraphPar n J s L σ → SobGraphPar n J s L u →
    SobGraphPar n J s L ((complexPart n J).boundaryPart j ((complexPart n J).domainIncl j u)) →
    SobAtPar n J s L j (q : L2F ℝ (cubeDomain n) (formIdx n j)) → ∀ N : ℕ,
    ‖σ - (polyPartial n S N J).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (polyPartial n S N J) hij hjk f).fst‖ +
        ‖u - (polyPartial n S N J).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (polyPartial n S N J) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (polyPartial n S N J) hij hjk
            f).snd.snd : (polyPartial n S N J).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      K * L * meshSize N ^ s := by
  obtain ⟨ρ, C, hE⟩ := paritySmoothing_exists J S
  obtain rfl : j + 1 = k := hjk
  have hC := hE.two_mul_nonneg
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = sobConstParZ n S i + sobConstParZ n S (i + 1) + sobConstParZ n S j +
      sobConstParZ n S (j + 1) := ⟨_, rfl⟩
  have hi := sobConstParZ_nonneg (n := n) S i; have hi1 := sobConstParZ_nonneg (n := n) S (i + 1)
  have hj := sobConstParZ_nonneg (n := n) S j; have hj1 := sobConstParZ_nonneg (n := n) S (j + 1)
  refine ⟨(1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) *
    (4 + 2 * (2 * C)) * ((1 + 2 * C) * A), fun {f σ u q} hs {L} hL0 hσ hu hBu hq N => ?_⟩
  have hδ : 0 ≤ meshSize N ^ s * L := mul_nonneg (Real.rpow_nonneg (meshSize_pos N).le _) hL0
  have hle : ∀ a b : ℝ, a + b ≤ A →
      (1 + 2 * C) * (a + b) * meshSize N ^ s * L ≤ (1 + 2 * C) * A * (meshSize N ^ s * L) :=
    fun a b hab => by
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab
        (by linarith : (0 : ℝ) ≤ 1 + 2 * C)) hδ]
  have hg : SobGraphPar n J s L (HilbertComplex.cyclesToDomainSpace
      ((complexPart n J).harmonic_le_cycles j q.2)) :=
    ⟨by rw [HilbertComplex.domainIncl_cyclesToDomainSpace]; exact hq,
      by rw [HilbertComplex.d_domainCoord_cyclesToDomainSpace]; exact sobAtPar_zero J hL0 _⟩
  have h1 := (hE.infDist_domainSub_le_sobGraphPar hs0 hs1 N hσ).trans (hle _ _ (by linarith))
  have h2 := (hE.infDist_domainSub_le_sobGraphPar hs0 hs1 N hu).trans (hle _ _ (by linarith))
  have h3 := (hE.infDist_domainSub_le_sobGraphPar hs0 hs1 N hg).trans (hle _ _ (by linarith))
  have h4 := (hE.infDist_domainSub_le_sobGraphPar hs0 hs1 N hBu).trans (hle _ _ (by linarith))
  refine (norm_sub_discreteMixedSolution_le (hE.proj N) hij rfl (by linarith [hE.half_le])
    (norm_le_of_mem_orthogonal_cycles_part J hij) (norm_le_of_mem_orthogonal_cycles_part J rfl)
    ((hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j))
    ((hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N j) (hE.norm_proj_le N (j + 1))) hs h1 h2 h3 h4).trans
    (le_of_eq (by ring))

omit [NeZero n] in
instance (S : PolySeq) (N : ℕ) (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional ℝ (((polyPartial n S N J).window a m).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((polyPartial n S N J).V (a + i)))

omit [NeZero n] in
instance (S : PolySeq) (N : ℕ) (a : ℤ) (m : ℕ) :
    FiniteDimensional ℝ ((polyPartial n S N J).window a m).graphSub :=
  inferInstance

variable (n) in
/-- **A component with `Hˢ_J(Q)` data in the graph norm of `HΛ_J(Q)`**. -/
def SobCompPar (s L : ℝ) {j : ℤ} (x : L2F ℝ (cubeDomain n) (formIdx n j)) : Prop :=
  SobAtPar n J s L j x ∧ ∀ hx : x ∈ ((complexPart n J).d j (j + 1)).domain,
    SobAtPar n J s L (j + 1) ((complexPart n J).d j (j + 1) ⟨x, hx⟩)

variable {J} in
/-- **Graph-norm approximation in the total space of a window of `HΛ_J(Q)`**. -/
theorem ParitySmoothingEstimates.exists_mem_window_le_sobPar {S : PolySeq}
    {ρ : ℕ → ParitySmoother.ReflKernel n} {C : ℝ} (hE : ParitySmoothingEstimates n J S ρ C)
    {s L : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hL0 : 0 ≤ L) {a : ℤ} {m : ℕ}
    (ζ : ((complexPart n J).window a m).totalD.GraphSpace)
    (hζ : ∀ i : Fin m, SobCompPar n J s L (((complexPart n J).window a m).totalD.graphFst ζ i))
    (N : ℕ) :
    ∃ w ∈ ((polyPartial n S N J).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * ((1 + 2 * C) * (∑ i : Fin m, (sobConstParZ n S (a + i) +
        sobConstParZ n S (a + i + 1))) * meshSize N ^ s * L) := by
  obtain ⟨x, rfl, -, -⟩ := ((complexPart n J).window a m).totalD.exists_toGraphSpace_eq ζ
  simp only [LinearPMap.graphFst_toGraphSpace] at hζ
  have hC := hE.two_mul_nonneg
  have hh := Real.rpow_nonneg (meshSize_pos N).le s
  set K := ∑ i : Fin m, (sobConstParZ n S (a + i) + sobConstParZ n S (a + i + 1))
  have hKi : ∀ i : Fin m, sobConstParZ n S (a + i) + sobConstParZ n S (a + i + 1) ≤ K :=
    fun i => Finset.single_le_sum
      (f := fun i : Fin m => sobConstParZ n S (a + i) + sobConstParZ n S (a + i + 1))
      (fun i _ => add_nonneg (sobConstParZ_nonneg S _) (sobConstParZ_nonneg S _))
      (Finset.mem_univ i)
  have hε : 0 ≤ (1 + 2 * C) * K * meshSize N ^ s * L := by
    have : 0 ≤ K := Finset.sum_nonneg fun i _ =>
      add_nonneg (sobConstParZ_nonneg S _) (sobConstParZ_nonneg S _)
    have : 0 ≤ 1 + 2 * C := by linarith
    positivity
  obtain ⟨w, hw, hlt⟩ := Subcomplex.exists_mem_graphSub_le ((polyPartial n S N J).window a m) x
    (ε := (1 + 2 * C) * K * meshSize N ^ s * L) fun i => by
      set xi := (x : PiLp 2 fun i : Fin m => L2F ℝ (cubeDomain n) (formIdx n (a + i))) i
      have h0 := infDist_polyPartial_le_sobAtPar J S hs0 hs1 N (hζ i).1
      have hA : (1 + 2 * C) * Metric.infDist xi ((polyPartial n S N J).V (a + i)) ≤
          (1 + 2 * C) * K * meshSize N ^ s * L := by
        have hs := sobConstParZ_nonneg (n := n) S (a + i + 1)
        calc (1 + 2 * C) * Metric.infDist xi ((polyPartial n S N J).V (a + i)) ≤
            (1 + 2 * C) * (sobConstParZ n S (a + i) * meshSize N ^ s * L) :=
              mul_le_mul_of_nonneg_left h0 (by linarith)
          _ ≤ (1 + 2 * C) * K * meshSize N ^ s * L := by
              rw [mul_assoc (1 + 2 * C) K, mul_assoc (1 + 2 * C) (K * _)]
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              rw [mul_assoc, mul_assoc]
              exact mul_le_mul_of_nonneg_right (by linarith [hKi i]) (mul_nonneg hh hL0)
      have hB : ∀ hx : xi ∈ ((complexPart n J).d (a + i) (a + i + 1)).domain,
          (1 + 2 * C) * Metric.infDist ((complexPart n J).d (a + i) (a + i + 1) ⟨xi, hx⟩)
            ((polyPartial n S N J).V (a + i + 1)) ≤ (1 + 2 * C) * K * meshSize N ^ s * L := by
        intro hx
        have h1 := infDist_polyPartial_le_sobAtPar J S hs0 hs1 N ((hζ i).2 hx)
        have hs := sobConstParZ_nonneg (n := n) S (a + i)
        calc (1 + 2 * C) * Metric.infDist ((complexPart n J).d (a + i) (a + i + 1) ⟨xi, hx⟩)
              ((polyPartial n S N J).V (a + i + 1)) ≤
            (1 + 2 * C) * (sobConstParZ n S (a + i + 1) * meshSize N ^ s * L) :=
              mul_le_mul_of_nonneg_left h1 (by linarith)
          _ ≤ (1 + 2 * C) * K * meshSize N ^ s * L := by
              rw [mul_assoc (1 + 2 * C) K, mul_assoc (1 + 2 * C) (K * _)]
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              rw [mul_assoc, mul_assoc]
              exact mul_le_mul_of_nonneg_right (by linarith [hKi i]) (mul_nonneg hh hL0)
      obtain ⟨v, hv, h1, h2⟩ := exists_mem_le_proj (hE.proj N) hC (hE.norm_proj_le N)
        (j := a + i) xi hA hB hε
      exact ⟨v, hv, h1, fun j hx => h2 (a + j) hx⟩
  refine ⟨w, hw, hlt.trans (le_of_eq ?_)⟩
  rw [Fintype.card_fin]

variable {J} in
/-- **Convergence of order `h^s` of the semi-discrete Hodge wave equation in `HΛ_J(Q)` for
solutions bounded in `Hˢ_J(Q)` uniformly on `[t₀, t₁]`, `0 ≤ s ≤ 1`**, on every window, for
every class `J`. -/
theorem ParitySmoothingEstimates.norm_sub_le_window_sobolevPar {S : PolySeq}
    {ρ : ℕ → ParitySmoother.ReflKernel n} {C : ℝ} (hE : ParitySmoothingEstimates n J S ρ C)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (a : ℤ) (m : ℕ) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complexPart n J).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complexPart n J).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((polyPartial n S N J).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ =
      HodgeWave.ellipticProjection (((polyPartial n S N J).window a m).graphSub) (ξ t₀))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hreg : ∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
      SobCompPar n J s L (((complexPart n J).window a m).totalD.graphFst (ξ τ) i) ∧
        SobCompPar n J s L (((complexPart n J).window a m).totalD.graphFst (ξ' τ) i))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complexPart n J).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complexPart n J).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 * (((m : ℝ) + m * m) * ((1 + 2 * C) * (∑ i : Fin m,
          (sobConstParZ n S (a + i) + sobConstParZ n S (a + i + 1))) * meshSize N ^ s * L)) :=
  ((polyPartial n S N J).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (fun τ hτ =>
    ⟨hE.exists_mem_window_le_sobPar hs0 hs1 hL0 (ξ τ) (fun i => (hreg τ hτ i).1) N,
      hE.exists_mem_window_le_sobPar hs0 hs1 hL0 (ξ' τ) (fun i => (hreg τ hτ i).2) N⟩) ht

end Parity

end Feec.Models.Cube.FEM
