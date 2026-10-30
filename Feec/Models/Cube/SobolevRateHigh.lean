module

public import Feec.Models.Cube.SobolevRate
public import Feec.Models.Cube.PolyRate
public import Feec.Models.Cube.SobolevWeak
public import Feec.FiniteElement.BrambleHilbertL2

/-!
# Optimal finite element rates for Sobolev data on the cube

Rates `h^{min(s, r_eff)}` of the finite element methods of every admissible sequence `S` on the
Freudenthal meshes of `Q = (0, ½)ⁿ` for data in the Sobolev spaces of
`Feec.Models.Cube.Sobolev`, every real `s ≥ 0`, where `r_eff = p + 1` and `S` reproduces `P_p`
in the degrees used (`polySpace n p k ≤ S.space n k`, e.g. `FEM.PolyOrder n S p`,
`FEM.PolyOrderAt n S p j`; `r_eff = r + 1` for `P_rΛᵏ`, `r` for `P_r⁻Λᵏ`), in **every dimension**
`n` and every order (no condition `2 r_eff > n`; for `r_eff = 1` also
`Feec.Models.Cube.SobolevRate`).

**Method.** Truncate the Fourier series of an extension (or of the parity extension) at
`M = N + 1 ≈ 1/(2h_N)`: `‖u - u_M‖ ≤ h_N^q ‖u‖_s`, `q = min(s, r_eff)`. By the Bernstein inequality
(`sum_norm_iteratedFDeriv_truncQ_sq_le`), `‖D^{r_eff} u_M‖_{L²(Q)} ≲ M^{r_eff - q} ‖u‖_s`, and the
`L²` interpolation error with lower-order terms (`norm_formL2_sub_glue_globalInterp_le_sum`:
`‖w - Π_h w‖ ≤ C h_N^{r_eff} Σ_{i ≤ ⌊n/2⌋ + 1} h_Nⁱ ‖D^{r_eff + i} w‖_{L²(Q)}`), in which every term
is `≲ h_N^q ‖u‖_s` for the band-limited `u_M` (`meshSize_pow_mul_sqrt_integral_truncField_le`,
`meshSize_pow_mul_rpow_le`), gives `dist(u_M, Vₕ) ≲ h_N^q ‖u‖_s`
(`norm_formL2_truncField_sub_glue_le`). The local estimate
(`sum_integral_sq_sub_globalInterp_le_sum`) is the `C⁰` estimate
`|w - Π_T w| ≤ C h_N^{r_eff} sup_T ‖D^{r_eff} w‖` of the canonical interpolant
(`Poly.abs_sub_globalInterp_le`, the DOF bounds of `Feec.Models.Cube.PolySmoothingEstimates`,
uniform over the Kuhn simplices) with the Sobolev embedding of `D^{r_eff} w` on each simplex at the
order `⌊n/2⌋ + 1 > n/2` (`norm_iteratedFDeriv_le_mesh`, from `Feec.FiniteElement.enorm_le_L2`;
`|T| = h_Nⁿ/n!`, `volume_closedInterior_mesh`); the simplices overlap boundedly
(`sum_integral_closedInterior_le`). The point values of the degrees of freedom are harmless because
the data are smoothed first: the classical route for rough data replaces the canonical
interpolant by a quasi-interpolant ([Clement1975]; [ScottZhang1990]) or by the smoothed
projections ([AFW2010], §5); here the Fourier truncation plays the role of the smoothing, and only
its derivatives of order `≤ r_eff + ⌊n/2⌋ + 1` enter. For `2 r_eff > n` the sharper local estimate
with the single term `h_N^{r_eff} ‖D^{r_eff} w‖` (`sum_integral_sq_sub_globalInterp_le`, the
Sobolev embedding of `w` itself, [Ciarlet2002], Thm 3.1.4) is also proved, with its own
constant `sobConstHighEmb` (`norm_formL2_truncField_sub_glue_le_emb`); any such bound on the
truncations gives a rate (`infDist_poly_le_sobolevQ_of_near`). The parity version
interpolates with vanishing boundary DOFs on the faces normal to `J` (`truncField_face`,
`exists_mem_polyPartial_of_le`). Graph norms, the mixed Hodge Laplacian and the semi-discrete
Hodge wave equation follow through the uniformly bounded cochain projections (which exist for
every `S` and `J`: `polySmoothingEstimates_exists`, `paritySmoothing_exists`) as in
`Feec.Models.Cube.SobolevRate`.

## Main results

* **Interpolation error with lower-order terms**, every dimension:
  `norm_formL2_sub_glue_globalInterp_le_sum`; for `2(p + 1) > n` the single-term
  `norm_formL2_sub_glue_globalInterp_le`.
* **Best approximation**, from any interpolation bound on the truncations:
  `infDist_poly_le_sobolevQ_of_near`, `infDist_polyPartial_le_sobolevPar_of_near`.
* **Best approximation at the optimal rate**: **`infDist_poly_le_sobolevQ_high`**
  (`dist(y, Vₕᵏ) ≤ C h_N^{min(s, p+1)} ‖y‖_{Hˢ(Q)}`), **`infDist_polyPartial_le_sobolevPar_high`**
  (`HΛ_J(Q)`, every class `J`, `‖y‖_{s,J}`); in every degree `infDist_poly_le_sobAt_high`,
  `infDist_polyPartial_le_sobAtPar_high`.
* **Graph norm**: the Jackson estimate `sobolevHighJackson` (orders `h_N^{min(s, p+1)}`),
  `ParitySmoothingEstimates.infDist_domainSub_le_sobGraphPar_high`.
* **Mixed Hodge–Laplace problem** ([AFW2010], Thm 3.9): **`mixed_rate_sobolevQ_high`**,
  **`mixed_rate_sobolevPar_high`** (error `≤ K L h_N^{min(s, p+1)}` for `S` reproducing `P_p` in
  the degrees `i, i + 1, i + 2`), the `_of_polyOrderAt` variant, and the bottom row
  `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` of Tables 5.1/6.1 on `1`-forms at the rate `h^{min(s,2)}`
  (`mixed_rate_lagrangeP2_sobolevQ`, every `n`).
* **Semi-discrete Hodge wave equation** ([QuennevilleBelair2015], Thm 4.14) on every window:
  `PolySmoothingEstimates.norm_sub_le_window_sobolevQ_high`; with no smoothing hypothesis,
  `exists_norm_sub_le_window_sobolevQ_high` (the smoothing estimates from
  `polySmoothingEstimates_exists`).

## Proved exponents (superseding the table of `Feec.Models.Cube.SobolevRate`)

| Setting | proved | condition |
|---|---|---|
| `HΛ(Q)`, `y ∈ Hˢ(Q)` | `h^{min(s, r_eff)}` | none |
| `HΛ_J(Q)`, `H̊Λ(Q)`, `y ∈ Hˢ_J(Q)` | `h^{min(s, r_eff)}` | none |
| graph norm, `σ, dσ ∈ Hˢ` | `h^{min(s, r_eff)}` | degrees `j, j + 1` |
| mixed Hodge Laplacian | `h^{min(s, r_eff)}` | degrees `i, i+1, i+2` |
| semi-discrete Hodge wave | `h^{min(s, r_eff)}` | degrees of the window |

*Remark* (not a theorem here): the exponents are the optimal orders of the `L²` best
approximation by piecewise polynomials of degree `p`; no lower bound is formalized.

What remains: Sobolev rates off the cube (parallelepipeds, star-shaped domains: there the data
have no Fourier truncation, and a quasi-interpolant would be needed), the improved `L²` estimates
of [AFW2010], §3.5 for the mixed method, and the BGG rates of Tables 5.1/6.1 for Sobolev data.

No hypothesis is assumed beyond the data (the smoothing estimates `hE` exist for every sequence
and class).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.9 (quasi-optimality of the mixed method), §5 (approximation, smoothed projections)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (approximation
  estimates)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], Thm 3.1.4
  (interpolation error)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.1 (Sobolev spaces)
* [L. C. Evans, *Partial Differential Equations*][Evans2010], §5.6 (Sobolev inequalities)
* [Ph. Clément, *Approximation by finite element functions using local regularization*][Clement1975]
  (quasi-interpolation of rough data)
* [L. R. Scott, S. Zhang, *Finite element interpolation of nonsmooth functions satisfying boundary conditions*][ScottZhang1990]
  (quasi-interpolation of rough data)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace Topology ContDiff ENNReal
open Set MeasureTheory Filter Finset

@[expose] public noncomputable section

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.HilbertComplex Feec.FiniteElement Feec.ExteriorFibre
open Feec.Models.Cube.Sobolev
open Feec.Models.Cube.DeRhamIdent (dPart Jinvf JfJ trunc)
open Feec.Models.Cube.Geometry (Q)

variable {n : ℕ}

/-! ### The local interpolation error from `L²` derivatives -/

namespace Poly

variable (S : PolySeq)

/-- **`C⁰` quasi-optimality of the canonical interpolant** on a mesh simplex: if a polynomial form
`P ∈ P(T)ᵏ` is `e`-close to `w` on `T`, then `|w - Π_T w| ≤ (1 + B dim D) e` on `T` (the DOF
bound `DofBound` and the DOF stability `abs_dof_le`; the argument of `abs_sub_globalInterp_le`
for an arbitrary approximant). -/
theorem abs_sub_globalInterp_le_of_near {N k : ℕ} {B D : ℝ} (hB : DofBound S n k B)
    (hB0 : 0 ≤ B) (hD : CoeffBound S n k D) (T : (mesh n N).simplices) {w : FormField n}
    (hw : Continuous w) {P : FormField n} (hPS : P ∈ S.space n k) {e : ℝ} (he : 0 ≤ e)
    (hwP : ∀ x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ‖w x - P x‖ ≤ e)
    {x : Fin n → ℝ} (hx : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior)
    (t : Finset (Fin n)) :
    |w x t - ((((polyElement n S).globalInterp (mesh n N) k ⟨w, hw⟩ :
      (polyElement n S).Piecewise (mesh n N) k) T : (polyElement n S).space T k) :
        FormField n) x t| ≤
      (1 + B * Module.finrank ℝ (S.space n k) * D) * e := by
  set Iw : (polyElement n S).space T k := (((polyElement n S).globalInterp (mesh n N) k
    ⟨w, hw⟩ : (polyElement n S).Piecewise (mesh n N) k) T)
  have hIw : (Iw : FormField n) ∈ S.space n k := Iw.2
  set z : FormField n := (Iw : FormField n) - P
  have hz : z ∈ S.space n k := Submodule.sub_mem _ hIw hPS
  have hwPc : Continuous (w - P) := hw.sub (PolyKind.contDiff_of_mem_space hPS).continuous
  have hdof : ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ hN N ^ k * (D * e) := by
    intro g hgT i
    have e1 : S.dof g k i ⟨(Iw : FormField n), S.space_le_contForms n k hIw⟩ =
        S.dof g k i ⟨w, hw⟩ :=
      (polyElement n S).localDof_globalInterp (mesh n N) k ⟨w, hw⟩ T g hgT i
    have e2 : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ = S.dof g k i ⟨w - P, hwPc⟩ := by
      have : (⟨z, S.space_le_contForms n k hz⟩ : contForms n) =
          ⟨(Iw : FormField n), S.space_le_contForms n k hIw⟩ -
            ⟨P, S.space_le_contForms n k hPS⟩ := rfl
      have : (⟨w - P, hwPc⟩ : contForms n) = ⟨w, hw⟩ -
          ⟨P, S.space_le_contForms n k hPS⟩ := rfl
      rw [‹(⟨z, _⟩ : contForms n) = _›, this, map_sub, map_sub, e1]
    rw [e2]
    refine (abs_dof_le S hD T.2 hgT i _ he fun y hy t => ?_).trans (le_of_eq (by ring))
    have := norm_le_pi_norm ((w - P) y) t
    rw [Real.norm_eq_abs] at this
    exact this.trans (hwP y hy)
  have hzb := abs_le_of_abs_dof_le S hB hB0 T.2 hz hdof hx t
  have h1 : |w x t - P x t| ≤ e := by
    have := norm_le_pi_norm (w x - P x) t
    rw [Real.norm_eq_abs, Pi.sub_apply] at this
    exact this.trans (hwP x hx)
  calc |w x t - (Iw : FormField n) x t| = |(w x t - P x t) - z x t| := by
        simp only [z, Pi.sub_apply]; ring_nf
    _ ≤ |w x t - P x t| + |z x t| := abs_sub _ _
    _ ≤ e + B * Module.finrank ℝ (S.space n k) * (D * e) := add_le_add h1 hzb
    _ = (1 + B * Module.finrank ℝ (S.space n k) * D) * e := by ring

end Poly

/-! #### Sobolev embedding on the mesh simplices -/

variable (n) in
/-- The Riesz constant `n |B₁| h^{2(p+1) - n} / (2(p+1) - n)` of the Sobolev embedding at scale
`h` (`Feec.FiniteElement.rieszConst`, as a real number). -/
def rieszR (p : ℕ) (h : ℝ) : ℝ :=
  n * volume.real (Metric.ball (0 : Fin n → ℝ) 1) *
    (h ^ ((n : ℝ) + ((2 * (p + 1) : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ)) /
      ((n : ℝ) + ((2 * (p + 1) : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ)))

variable (n) in
/-- `n |B₁| / (2(p+1) - n)`. -/
def rieszC (p : ℕ) : ℝ :=
  n * volume.real (Metric.ball (0 : Fin n → ℝ) 1) /
    ((n : ℝ) + ((2 * (p + 1) : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ))

theorem denom_pos {p : ℕ} (hns : n < 2 * (p + 1)) :
    0 < (n : ℝ) + ((2 * (p + 1) : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ) := by
  have : (n : ℝ) < ((2 * (p + 1) : ℕ) : ℝ) := by exact_mod_cast hns
  push_cast at this ⊢
  linarith

theorem rieszR_nonneg {p : ℕ} (hns : n < 2 * (p + 1)) {h : ℝ} (hh : 0 ≤ h) : 0 ≤ rieszR n p h := by
  have := denom_pos hns
  unfold rieszR
  have : 0 ≤ h ^ ((n : ℝ) + ((2 * (p + 1) : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ)) :=
    Real.rpow_nonneg hh _
  positivity

theorem rieszC_nonneg {p : ℕ} (hns : n < 2 * (p + 1)) : 0 ≤ rieszC n p := by
  have := denom_pos hns
  unfold rieszC; positivity

theorem pow_mul_rieszR {p : ℕ} {h : ℝ} (hh : 0 < h) :
    h ^ n * rieszR n p h = rieszC n p * h ^ (2 * (p + 1)) := by
  unfold rieszR rieszC
  have e : h ^ n * h ^ ((n : ℝ) + ((2 * (p + 1) : ℕ) : ℝ) - ((2 * n : ℕ) : ℝ)) =
      h ^ (2 * (p + 1)) := by
    rw [← Real.rpow_natCast h n, ← Real.rpow_add hh, ← Real.rpow_natCast h (2 * (p + 1))]
    congr 1
    push_cast; ring
  rw [div_eq_mul_inv, div_eq_mul_inv, ← e]
  ring

variable (n) in
/-- `n! / (n p!)`, the constant `dⁿ / (n p! |T|)` of the Riesz bound on a Freudenthal simplex
(`|T| = h_Nⁿ / n!`, `d = h_N`). -/
def embA (p : ℕ) : ℝ := n.factorial / (n * p.factorial)

theorem embA_nonneg (p : ℕ) : 0 ≤ embA n p := by unfold embA; positivity

/-- `|T| = h_Nⁿ / n!` for the simplices of the Freudenthal meshes. -/
theorem volume_closedInterior_mesh {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) :
    volume T.closedInterior = ENNReal.ofReal (hN N ^ n / n.factorial) := by
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  have hfin := ((cubeSimplex N m σ).isCompact_closedInterior.measure_lt_top (μ := volume)).ne
  rw [← ENNReal.ofReal_toReal hfin]
  congr 1
  have h1 := integral_closedInterior_mapEquiv_boxMap (kuhnSimplex σ)
    (hN N • latticePoint (finLattice m)) (hN_pos N) (fun _ => (1 : ℝ))
  rw [← cubeSimplex_eq, setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at h1
  rw [← Measure.real, h1, Measure.real, volume_closedInterior_kuhnSimplex]
  simp [div_eq_mul_inv]

/-- The constant `dⁿ / (n p! |T|)` of the averaged Taylor polynomial on a Freudenthal simplex is
`embA n p` (`|T| = h_Nⁿ / n!`, `d = h_N`). -/
theorem avgTaylorConst_mesh [NeZero n] {N : ℕ} (p : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) :
    avgTaylorConst n p (hN N) T.closedInterior = ENNReal.ofReal (embA n p) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hh := hN_pos N
  rw [avgTaylorConst, volume_closedInterior_mesh hT, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  unfold embA
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  have : (p.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The square root of the Riesz constant as a real number, for `2(p + 1) > n`. -/
theorem rieszConst_rpow_half {p : ℕ} (hns : n < 2 * (p + 1)) {h : ℝ} (hh : 0 ≤ h) :
    rieszConst n (2 * (p + 1)) (2 * n) h ^ (1 / 2 : ℝ) = ENNReal.ofReal (√(rieszR n p h)) := by
  rw [show rieszConst n (2 * (p + 1)) (2 * n) h = ENNReal.ofReal (rieszR n p h) from rfl,
    ENNReal.ofReal_rpow_of_nonneg (rieszR_nonneg hns hh) (by norm_num), Real.sqrt_eq_rpow]

/-- **Sobolev embedding on a Freudenthal simplex** (`2(p + 1) > n`): the degree-`k` part `P` of
the averaged Taylor polynomial of order `p + 1` (`avgTaylorPoly`, a form of `P_pΛᵏ`) satisfies
`sup_T ‖w - P‖ ≤ (n!/(n p!)) (R(h_N))^{1/2} (∫_T ‖D^{p+1} w‖²)^{1/2}`
(`Feec.FiniteElement.enorm_sub_avgTaylorPoly_le_L2`, `|T| = h_Nⁿ/n!`, `d = h_N`). -/
theorem norm_sub_degPart_avgTaylorPoly_le [NeZero n] {N k p : ℕ} (hns : n < 2 * (p + 1))
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices) {w : FormField n}
    (hw : ContDiff ℝ (p + 1) w) (hdeg : ∀ x, IsDeg k (w x)) {x : Fin n → ℝ}
    (hx : x ∈ T.closedInterior) :
    ‖w x - degPartField k (avgTaylorPoly T.closedInterior w (p + 1)) x‖ ≤
      embA n p * √(rieszR n p (hN N)) *
        √(∫ y in T.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hh := hN_pos N
  have hTc : IsCompact T.closedInterior := T.isCompact_closedInterior
  have hTm : MeasurableSet T.closedInterior := hTc.isClosed.measurableSet
  have hd : ∀ x ∈ T.closedInterior, ∀ y ∈ T.closedInterior, ‖x - y‖ ≤ hN N := by
    obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
    exact fun x hx y hy => norm_sub_le_of_mem_cubeSimplex hx hy
  have h := enorm_sub_avgTaylorPoly_le_L2 hn hTc (convex_closedInterior T)
    (volume_closedInterior_ne_zero T) isOpen_univ (subset_univ _) hns hw.contDiffOn hd hx
  -- the three factors as real numbers
  have hDc : ContinuousOn (iteratedFDeriv ℝ (p + 1) w) T.closedInterior :=
    (hw.continuous_iteratedFDeriv le_rfl).continuousOn
  have hI : (∫⁻ z in T.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w z‖ₑ ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (√(∫ y in T.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2)) := by
    rw [integral_norm_sq_eq_toReal_lintegral hTm hDc, Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal (setLIntegral_enorm_sq_lt_top hTc hDc).ne]
  rw [avgTaylorConst_mesh p hT, rieszConst_rpow_half hns hh.le, hI,
    ← ENNReal.ofReal_mul (embA_nonneg p), ← ENNReal.ofReal_mul
    (mul_nonneg (embA_nonneg p) (Real.sqrt_nonneg _))] at h
  have e : w x - degPartField k (avgTaylorPoly T.closedInterior w (p + 1)) x =
      degPart k (w x - avgTaylorPoly T.closedInterior w (p + 1) x) := by
    have h2 := congrFun (degPartField_sub k w (avgTaylorPoly T.closedInterior w (p + 1))) x
    rw [degPartField_of_isDeg hdeg] at h2
    exact h2.symm
  rw [e]
  refine (norm_degPart_le k _).trans ?_
  rw [← ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (embA_nonneg p)
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))).1 h

/-! #### The local and global `L²` interpolation errors -/

variable (n) in
/-- The `C⁰`-stability constant `1 + B_k dim(P(T)ᵏ) D_k` of the canonical interpolant of `S`. -/
def interpCi (S : PolySeq) (k : ℕ) : ℝ :=
  1 + dofConst n S k * Module.finrank ℝ (S.space n k) * coeffConst n S k

variable (n) in
/-- The constant of the local `L²` interpolation error from `L²` derivatives. -/
def localL2Const (S : PolySeq) (k p : ℕ) : ℝ :=
  2 ^ n * (interpCi n S k * embA n p) ^ 2 * rieszC n p

theorem localL2Const_nonneg (S : PolySeq) (k : ℕ) {p : ℕ} (hns : n < 2 * (p + 1)) :
    0 ≤ localL2Const n S k p := by
  have := rieszC_nonneg hns
  unfold localL2Const; positivity

/-- **The local `L²` interpolation error from `L²` derivatives** on a Freudenthal simplex
([Arnold2018], Ch. 7; [Ciarlet2002], Thm 3.1.4, Sobolev form): for `P_pΛᵏ ⊆ P(T)ᵏ`,
`2(p + 1) > n` and a smooth degree-`k` form `w`,
`‖w - Π_T w‖²_{L²(T)} ≤ C h_N^{2(p+1)} ∫_T ‖D^{p+1} w‖²`, `C = localL2Const n S k p`
independent of `N` and `T` (Sobolev embedding on `T` and `C⁰` stability of `Π_T`). -/
theorem sum_integral_sq_sub_globalInterp_le [NeZero n] (S : PolySeq) {N k p : ℕ}
    (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1)) (T : (mesh n N).simplices)
    {w : FormField n} (hw : ContDiff ℝ ∞ w) (hdeg : ∀ x, IsDeg k (w x)) :
    ∑ t : formIdx n k, ∫ x in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (w x t.1 - ((((polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩ :
        (polyElement n S).Piecewise (mesh n N) k) T : (polyElement n S).space T k) :
          FormField n) x t.1) ^ 2 ≤
      localL2Const n S k p * hN N ^ (2 * (p + 1)) *
        ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
          ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2 := by
  set T' : Affine.Simplex ℝ (Fin n → ℝ) n := T.1
  have hT : T' ∈ (mesh n N).simplices := T.2
  have hh := hN_pos N
  have hw1 : ContDiff ℝ (p + 1) w := hw.of_le (by exact_mod_cast le_top)
  set I := ∫ y in T'.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2
  have hI : 0 ≤ I := setIntegral_nonneg T'.isCompact_closedInterior.isClosed.measurableSet
    fun _ _ => sq_nonneg _
  set e := embA n p * √(rieszR n p (hN N)) * √I
  have he : 0 ≤ e := mul_nonneg (mul_nonneg (embA_nonneg p) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
  set P := degPartField k (avgTaylorPoly T'.closedInterior w (p + 1))
  have hP : P ∈ S.space n k := hs (degPartField_mem_polySpace (avgTaylorPoly_mem_polyFunctions
    T'.isCompact_closedInterior isOpen_univ (subset_univ _)
      (hw.of_le (by exact_mod_cast le_top)).contDiffOn) k)
  have hwP : ∀ x ∈ T'.closedInterior, ‖w x - P x‖ ≤ e := fun x hx =>
    norm_sub_degPart_avgTaylorPoly_le hns hT hw1 hdeg hx
  set Iw : (polyElement n S).space T k := (((polyElement n S).globalInterp (mesh n N) k
    ⟨w, hw.continuous⟩ : (polyElement n S).Piecewise (mesh n N) k) T)
  have hIwc : Continuous (Iw : FormField n) :=
    (PolyKind.contDiff_of_mem_space Iw.2).continuous
  have hpt : ∀ x ∈ T'.closedInterior, ∀ t : Finset (Fin n),
      |w x t - (Iw : FormField n) x t| ≤ interpCi n S k * e := fun x hx t =>
    Poly.abs_sub_globalInterp_le_of_near S (dofBound_dofConst S k) (dofConst_nonneg S k)
      (coeffBound_coeffConst S k) T hw.continuous hP he hwP hx t
  obtain ⟨m, σ, hmσ⟩ := mem_mesh_simplices.1 hT
  have hone : ∀ t : formIdx n k, ∫ x in T'.closedInterior, (w x t.1 - (Iw : FormField n) x t.1) ^ 2
      ≤ hN N ^ n * (interpCi n S k * e) ^ 2 := by
    intro t
    have hc : Continuous fun x => (w x t.1 - (Iw : FormField n) x t.1) ^ 2 :=
      (((continuous_apply t.1).comp hw.continuous).sub ((continuous_apply t.1).comp hIwc)).pow 2
    have := integral_cubeSimplex_le m σ hc (fun x hx => by
      rw [hmσ] at hx
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hpt x hx t.1) 2) (fun x => sq_nonneg _)
    rwa [hmσ] at this
  have hsq : (interpCi n S k * e) ^ 2 =
      (interpCi n S k * embA n p) ^ 2 * rieszR n p (hN N) * I := by
    simp only [e]
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (rieszR_nonneg hns hh.le), Real.sq_sqrt hI]
    ring
  calc ∑ t : formIdx n k, ∫ x in T'.closedInterior, (w x t.1 - (Iw : FormField n) x t.1) ^ 2
      ≤ ∑ _t : formIdx n k, hN N ^ n * (interpCi n S k * e) ^ 2 :=
        Finset.sum_le_sum fun t _ => hone t
    _ = Fintype.card (formIdx n k) * (hN N ^ n * (interpCi n S k * e) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * (hN N ^ n * (interpCi n S k * e) ^ 2) :=
        mul_le_mul_of_nonneg_right (card_formIdx_le _) (by positivity)
    _ = 2 ^ n * (interpCi n S k * embA n p) ^ 2 * (hN N ^ n * rieszR n p (hN N)) * I := by
        rw [hsq]; ring
    _ = _ := by rw [pow_mul_rieszR hh, localL2Const]; ring

/-- **Bounded overlap of the closed simplices**: `Σ_T ∫_T F ≤ 6ⁿ n! ∫_Q F` for `F ≥ 0`
continuous. -/
theorem sum_integral_closedInterior_le (N : ℕ) {F : (Fin n → ℝ) → ℝ} (hF : Continuous F)
    (hF0 : ∀ x, 0 ≤ F x) :
    ∑ T ∈ (mesh n N).simplices, ∫ x in T.closedInterior, F x ≤
      (6 ^ n * n.factorial : ℕ) * ∫ x in cubeDomain n, F x := by
  set C := closure (cubeDomain n)
  have hCc : IsCompact C := (isBounded_cubeDomain (n := n)).isCompact_closure
  have hCm : MeasurableSet C := isClosed_closure.measurableSet
  set f := C.indicator F
  have hfi : Integrable f :=
    (integrable_indicator_iff hCm).2 (hF.continuousOn.integrableOn_compact hCc)
  have hf0 : ∀ x, 0 ≤ f x := fun x => Set.indicator_nonneg (fun x _ => hF0 x) x
  have h1 : ∀ T ∈ (mesh n N).simplices, ∫ x in T.closedInterior, F x ≤
      ∫ x in Metric.cthickening (2 * hN N) T.closedInterior, f x := by
    intro T hT
    have hTC : T.closedInterior ⊆ C := by
      have := (mesh n N).closedInterior_subset_closure hT
      rwa [mesh_domain n N] at this
    have e : ∫ x in T.closedInterior, F x = ∫ x in T.closedInterior, f x :=
      setIntegral_congr_fun T.isCompact_closedInterior.isClosed.measurableSet fun x hx =>
        (Set.indicator_of_mem (hTC hx) F).symm
    rw [e]
    exact setIntegral_mono_set hfi.integrableOn (Eventually.of_forall hf0)
      (Eventually.of_forall (Metric.self_subset_cthickening _))
  refine (Finset.sum_le_sum h1).trans ((sum_integral_cthickening_le N hfi hf0).trans
    (le_of_eq ?_))
  congr 1
  rw [integral_indicator hCm]
  have hnull : volume (frontier (cubeDomain n)) = 0 :=
    Convex.addHaar_frontier volume (convex_cubeDomain n)
  rw [Measure.restrict_congr_set (closure_ae_eq_of_null_frontier hnull)]

variable (n) in
/-- The constant of the global `L²` interpolation error from `L²` derivatives. -/
def globalL2Const (S : PolySeq) (k p : ℕ) : ℝ :=
  √(localL2Const n S k p * (6 ^ n * n.factorial : ℕ))

theorem globalL2Const_nonneg (S : PolySeq) (k p : ℕ) : 0 ≤ globalL2Const n S k p :=
  Real.sqrt_nonneg _

/-- **The global `L²` interpolation error from `L²` derivatives** on the Freudenthal meshes:
`‖w - Π_h w‖_{L²(Q)} ≤ C h_N^{p+1} ‖D^{p+1} w‖_{L²(Q)}` for `P_pΛᵏ ⊆ P(T)ᵏ`, `2(p + 1) > n`,
`C = globalL2Const n S k p`. -/
theorem norm_formL2_sub_glue_globalInterp_le [NeZero n] (S : PolySeq) {N k p : ℕ}
    (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1)) {w : FormField n}
    (hw : ContDiff ℝ ∞ w) (hdeg : ∀ x, IsDeg k (w x)) :
    ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
        ⟨w, hw.continuous⟩ - (polyElement n S).glue (mesh n N) k
          ((polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩ :
            (polyElement n S).Piecewise (mesh n N) k)‖ ≤
      globalL2Const n S k p * hN N ^ (p + 1) *
        √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2) := by
  set u := ((polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩ :
    (polyElement n S).Piecewise (mesh n N) k)
  have hK := localL2Const_nonneg (n := n) S k hns
  have hh := (hN_pos N).le
  have hDc : Continuous fun y => ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2 :=
    ((hw.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm).pow 2
  have hsq := norm_sq_formL2_sub_glue_le (polyElement n S) (mesh n N)
    (isOpen_mesh_domain n N).measurableSet k ⟨w, hw.continuous⟩ u
  have h2 : ∑ T ∈ (mesh n N).simplices, ∑ s : formIdx n k, ∫ x in T.closedInterior,
      (w x s.1 - (polyElement n S).extendPW (mesh n N) u T x s.1) ^ 2 ≤
      localL2Const n S k p * hN N ^ (2 * (p + 1)) *
        ∑ T ∈ (mesh n N).simplices,
          ∫ y in T.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun T hT => ?_
    have e : ∀ x, (polyElement n S).extendPW (mesh n N) u T x =
        ((u (⟨T, hT⟩ : (mesh n N).simplices) : (polyElement n S).space
          (⟨T, hT⟩ : (mesh n N).simplices) k) : FormField n) x := fun x => by
      rw [(polyElement n S).extendPW_of_mem (mesh n N) u hT]
    simp_rw [e]
    exact sum_integral_sq_sub_globalInterp_le S hs hns (⟨T, hT⟩ : (mesh n N).simplices) hw hdeg
  have h3 := sum_integral_closedInterior_le N hDc (fun _ => sq_nonneg _)
  have hJ : 0 ≤ ∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2 :=
    setIntegral_nonneg (isOpen_cubeDomain n).measurableSet fun _ _ => sq_nonneg _
  have h4 : ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
        ⟨w, hw.continuous⟩ - (polyElement n S).glue (mesh n N) k u‖ ^ 2 ≤
      (globalL2Const n S k p * hN N ^ (p + 1) *
        √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2)) ^ 2 := by
    refine hsq.trans (h2.trans ?_)
    rw [mul_pow, mul_pow, globalL2Const, Real.sq_sqrt (by positivity), Real.sq_sqrt hJ, ← pow_mul,
      mul_comm (p + 1) 2]
    calc localL2Const n S k p * hN N ^ (2 * (p + 1)) * ∑ T ∈ (mesh n N).simplices,
          ∫ y in T.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2
        ≤ localL2Const n S k p * hN N ^ (2 * (p + 1)) * (((6 ^ n * n.factorial : ℕ) : ℝ) *
          ∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have := globalL2Const_nonneg (n := n) S k p
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h4

/-! #### With lower-order terms, in every dimension -/

/-- **Sobolev embedding of `D^r w` on a Freudenthal simplex**, with the lower-order terms
(`Feec.FiniteElement.enorm_le_L2` for `f = D^r w`, `|T| = h_Nⁿ/n!`, `d = h_N`): for `2(ν + 1) > n`
and every `r`, `sup_T ‖D^r w‖ ≤ Σ_{i ≤ ν} h_Nⁱ/i! (n!/h_Nⁿ ∫_T ‖D^{i+r} w‖²)^{1/2} +
(n!/(n ν!)) R(h_N)^{1/2} (∫_T ‖D^{ν+1+r} w‖²)^{1/2}`. -/
theorem norm_iteratedFDeriv_le_mesh [NeZero n] {N r ν : ℕ} (hnν : n < 2 * (ν + 1))
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices) {w : FormField n}
    (hw : ContDiff ℝ ∞ w) {y : Fin n → ℝ} (hy : y ∈ T.closedInterior) :
    ‖iteratedFDeriv ℝ r w y‖ ≤ ∑ i ∈ range (ν + 1), hN N ^ i / i.factorial *
        √(n.factorial / hN N ^ n * ∫ z in T.closedInterior, ‖iteratedFDeriv ℝ (i + r) w z‖ ^ 2) +
      embA n ν * √(rieszR n ν (hN N)) *
        √(∫ z in T.closedInterior, ‖iteratedFDeriv ℝ (ν + 1 + r) w z‖ ^ 2) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hh := hN_pos N
  have hTc : IsCompact T.closedInterior := T.isCompact_closedInterior
  have hTm : MeasurableSet T.closedInterior := hTc.isClosed.measurableSet
  have hd : ∀ x ∈ T.closedInterior, ∀ y ∈ T.closedInterior, ‖x - y‖ ≤ hN N := by
    obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
    exact fun x hx y hy => norm_sub_le_of_mem_cubeSimplex hx hy
  set g := iteratedFDeriv ℝ r w
  have hg : ContDiff ℝ ∞ g := hw.iteratedFDeriv_right (by exact_mod_cast le_top)
  have h := enorm_le_L2 hn hTc (convex_closedInterior T) (volume_closedInterior_ne_zero T)
    isOpen_univ (subset_univ _) hnν (hg.of_le (by exact_mod_cast le_top)).contDiffOn hd hy
  -- the integrals as real numbers
  have hI : ∀ i, (∫⁻ z in T.closedInterior, ‖iteratedFDeriv ℝ i g z‖ₑ ^ 2) =
      ENNReal.ofReal (∫ z in T.closedInterior, ‖iteratedFDeriv ℝ (i + r) w z‖ ^ 2) := by
    intro i
    have e : ∀ z, ‖iteratedFDeriv ℝ i g z‖ₑ = ‖iteratedFDeriv ℝ (i + r) w z‖ₑ := fun z => by
      rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_iteratedFDeriv]
    have hDc : ContinuousOn (iteratedFDeriv ℝ (i + r) w) T.closedInterior :=
      (hw.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
    simp_rw [e]
    rw [integral_norm_sq_eq_toReal_lintegral hTm hDc,
      ENNReal.ofReal_toReal (setLIntegral_enorm_sq_lt_top hTc hDc).ne]
  have hJ : ∀ i, 0 ≤ ∫ z in T.closedInterior, ‖iteratedFDeriv ℝ (i + r) w z‖ ^ 2 := fun i =>
    setIntegral_nonneg hTm fun _ _ => sq_nonneg _
  have hvol : volume T.closedInterior = ENNReal.ofReal (hN N ^ n / n.factorial) :=
    volume_closedInterior_mesh hT
  have havg : ∀ i, (⨍⁻ z in T.closedInterior, ‖iteratedFDeriv ℝ i g z‖ₑ ^ 2 ∂volume) ^
      (1 / 2 : ℝ) = ENNReal.ofReal
        (√(n.factorial / hN N ^ n *
          ∫ z in T.closedInterior, ‖iteratedFDeriv ℝ (i + r) w z‖ ^ 2)) := by
    intro i
    rw [setLAverage_eq, hI, hvol, ← ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (div_nonneg (hJ i) (by positivity)) (by norm_num),
      Real.sqrt_eq_rpow]
    congr 2
    field_simp
  have hlast : (∫⁻ z in T.closedInterior, ‖iteratedFDeriv ℝ (ν + 1) g z‖ₑ ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (√(∫ z in T.closedInterior, ‖iteratedFDeriv ℝ (ν + 1 + r) w z‖ ^ 2)) := by
    rw [hI, ENNReal.ofReal_rpow_of_nonneg (hJ _) (by norm_num), Real.sqrt_eq_rpow]
  simp_rw [havg] at h
  rw [avgTaylorConst_mesh ν hT, rieszConst_rpow_half hnν hh.le, hlast, ← ofReal_norm] at h
  have hE := embA_nonneg (n := n) ν
  have hE' : 0 ≤ embA n ν * √(rieszR n ν (hN N)) := mul_nonneg hE (Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_mul hE, ← ENNReal.ofReal_mul hE'] at h
  simp_rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hh.le _) (Nat.cast_nonneg _))] at h
  have hS : ∀ i ∈ range (ν + 1), 0 ≤ hN N ^ i / i.factorial *
      √(n.factorial / hN N ^ n * ∫ z in T.closedInterior, ‖iteratedFDeriv ℝ (i + r) w z‖ ^ 2) :=
    fun i _ => mul_nonneg (div_nonneg (pow_nonneg hh.le _) (Nat.cast_nonneg _))
      (Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_sum_of_nonneg hS, ← ENNReal.ofReal_add (Finset.sum_nonneg hS)
    (mul_nonneg hE' (Real.sqrt_nonneg _))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (Finset.sum_nonneg hS)
    (mul_nonneg hE' (Real.sqrt_nonneg _)))).1 h

variable (n) in
/-- The constant `2ⁿ C_I² (2 (ν + 1) n! + 2 A_ν² C_ν)`, `ν = ⌊n/2⌋`, of the local `L²`
interpolation error with lower-order terms (`sum_integral_sq_sub_globalInterp_le_sum`). -/
def localL2SumConst (S : PolySeq) (k : ℕ) : ℝ :=
  2 ^ n * interpCi n S k ^ 2 *
    (((2 * (n / 2 + 1) * n.factorial : ℕ) : ℝ) + 2 * embA n (n / 2) ^ 2 * rieszC n (n / 2))

theorem localL2SumConst_nonneg (S : PolySeq) (k : ℕ) : 0 ≤ localL2SumConst n S k := by
  have := rieszC_nonneg (n := n) (p := n / 2) (by omega)
  unfold localL2SumConst; positivity

/-- **The local `L²` interpolation error with lower-order terms**, in every dimension: for
`P_pΛᵏ ⊆ P(T)ᵏ` and a smooth degree-`k` form `w`,
`‖w - Π_T w‖²_{L²(T)} ≤ C h_N^{2(p+1)} Σ_{i ≤ ⌊n/2⌋ + 1} h_N^{2i} ∫_T ‖D^{i+p+1} w‖²`,
`C = localL2SumConst n S k` independent of `N`, `T` and `p`: the `C⁰` estimate
`|w - Π_T w| ≤ C_I h_N^{p+1} sup_T ‖D^{p+1} w‖` (`Poly.abs_sub_globalInterp_le`) and the Sobolev
embedding of `D^{p+1} w` (`norm_iteratedFDeriv_le_mesh`, order `⌊n/2⌋ + 1`). Unlike
`sum_integral_sq_sub_globalInterp_le` there is no condition `2(p + 1) > n`. -/
theorem sum_integral_sq_sub_globalInterp_le_sum [NeZero n] (S : PolySeq) {N k p : ℕ}
    (hs : polySpace n p k ≤ S.space n k) (T : (mesh n N).simplices)
    {w : FormField n} (hw : ContDiff ℝ ∞ w) (hdeg : ∀ x, IsDeg k (w x)) :
    ∑ t : formIdx n k, ∫ x in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (w x t.1 - ((((polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩ :
        (polyElement n S).Piecewise (mesh n N) k) T : (polyElement n S).space T k) :
          FormField n) x t.1) ^ 2 ≤
      localL2SumConst n S k * hN N ^ (2 * (p + 1)) * ∑ i ∈ range (n / 2 + 2), hN N ^ (2 * i) *
        ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
          ‖iteratedFDeriv ℝ (i + (p + 1)) w y‖ ^ 2 := by
  set ν := n / 2
  have hnν : n < 2 * (ν + 1) := by omega
  set T' : Affine.Simplex ℝ (Fin n → ℝ) n := T.1
  have hT : T' ∈ (mesh n N).simplices := T.2
  have hh := hN_pos N
  set h := hN N
  set I : ℕ → ℝ := fun i => ∫ y in T'.closedInterior, ‖iteratedFDeriv ℝ (i + (p + 1)) w y‖ ^ 2
  have hI : ∀ i, 0 ≤ I i := fun i => setIntegral_nonneg
    T'.isCompact_closedInterior.isClosed.measurableSet fun _ _ => sq_nonneg _
  set b : ℕ → ℝ := fun i => h ^ i / i.factorial * √(n.factorial / h ^ n * I i)
  set c : ℝ := embA n ν * √(rieszR n ν h) * √(I (ν + 1))
  set M : ℝ := ∑ i ∈ range (ν + 1), b i + c
  have hb : ∀ i, 0 ≤ b i := fun i => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hc : 0 ≤ c :=
    mul_nonneg (mul_nonneg (embA_nonneg ν) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hM : ∀ y ∈ T'.closedInterior, ‖iteratedFDeriv ℝ (p + 1) w y‖ ≤ M := fun y hy =>
    norm_iteratedFDeriv_le_mesh (r := p + 1) hnν hT hw hy
  have hw1 : ContDiff ℝ (p + 1) w := hw.of_le (by exact_mod_cast le_top)
  set Iw : (polyElement n S).space T k := (((polyElement n S).globalInterp (mesh n N) k
    ⟨w, hw.continuous⟩ : (polyElement n S).Piecewise (mesh n N) k) T)
  have hIwc : Continuous (Iw : FormField n) :=
    (PolyKind.contDiff_of_mem_space Iw.2).continuous
  set e := interpCi n S k * (h ^ (p + 1) * M)
  have hpt : ∀ x ∈ T'.closedInterior, ∀ t : Finset (Fin n),
      |w x t - (Iw : FormField n) x t| ≤ e := fun x hx t =>
    Poly.abs_sub_globalInterp_le S hs (dofBound_dofConst S k) (dofConst_nonneg S k)
      (coeffBound_coeffConst S k) T hw1 hdeg hM hx t
  obtain ⟨m, σ, hmσ⟩ := mem_mesh_simplices.1 hT
  have hone : ∀ t : formIdx n k, ∫ x in T'.closedInterior,
      (w x t.1 - (Iw : FormField n) x t.1) ^ 2 ≤ h ^ n * e ^ 2 := by
    intro t
    have hc : Continuous fun x => (w x t.1 - (Iw : FormField n) x t.1) ^ 2 :=
      (((continuous_apply t.1).comp hw.continuous).sub ((continuous_apply t.1).comp hIwc)).pow 2
    have := integral_cubeSimplex_le m σ hc (fun x hx => by
      rw [hmσ] at hx
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hpt x hx t.1) 2) (fun x => sq_nonneg _)
    rwa [hmσ] at this
  -- `hⁿ M² ≤ K Σ_{i ≤ ν + 1} h^{2i} I_i`
  have hb2 : ∀ i, h ^ n * b i ^ 2 ≤ n.factorial * (h ^ (2 * i) * I i) := by
    intro i
    have hf : (1 : ℝ) ≤ (i.factorial : ℝ) ^ 2 := by
      have := i.factorial_pos
      exact_mod_cast Nat.one_le_pow _ _ this
    have e : h ^ n * b i ^ 2 = n.factorial * (h ^ (2 * i) * I i) / (i.factorial : ℝ) ^ 2 := by
      simp only [b]
      rw [mul_pow, div_pow, Real.sq_sqrt (by have := hI i; positivity)]
      field_simp
      ring
    rw [e]
    exact div_le_self (by have := hI i; positivity) hf
  have hc2 : h ^ n * c ^ 2 = embA n ν ^ 2 * rieszC n ν * (h ^ (2 * (ν + 1)) * I (ν + 1)) := by
    simp only [c]
    rw [mul_pow, mul_pow, Real.sq_sqrt (rieszR_nonneg hnν hh.le), Real.sq_sqrt (hI _)]
    have := pow_mul_rieszR (n := n) (p := ν) hh
    calc h ^ n * (embA n ν ^ 2 * rieszR n ν h * I (ν + 1)) =
        (h ^ n * rieszR n ν h) * embA n ν ^ 2 * I (ν + 1) := by ring
      _ = _ := by rw [this]; ring
  set S0 := ∑ i ∈ range (ν + 1), h ^ (2 * i) * I i
  have hS0 : 0 ≤ S0 := Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hI i)
  have hL0 : 0 ≤ h ^ (2 * (ν + 1)) * I (ν + 1) := mul_nonneg (by positivity) (hI _)
  have hK0 : 0 ≤ embA n ν ^ 2 * rieszC n ν := mul_nonneg (sq_nonneg _) (rieszC_nonneg hnν)
  have hMb : h ^ n * M ^ 2 ≤ (((2 * (ν + 1) * n.factorial : ℕ) : ℝ) +
      2 * embA n ν ^ 2 * rieszC n ν) * ∑ i ∈ range (ν + 2), h ^ (2 * i) * I i := by
    have h1 : M ^ 2 ≤ 2 * (∑ i ∈ range (ν + 1), b i) ^ 2 + 2 * c ^ 2 := by
      nlinarith [sq_nonneg (∑ i ∈ range (ν + 1), b i - c)]
    have h2 : (∑ i ∈ range (ν + 1), b i) ^ 2 ≤ (ν + 1) * ∑ i ∈ range (ν + 1), b i ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := range (ν + 1)) (f := b)
      simpa using this
    have h3 : h ^ n * ∑ i ∈ range (ν + 1), b i ^ 2 ≤ n.factorial * S0 := by
      rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hb2 i
    have hhn : 0 ≤ h ^ n := by positivity
    rw [Finset.sum_range_succ]
    push_cast
    calc h ^ n * M ^ 2 ≤ h ^ n * (2 * ((ν + 1) * ∑ i ∈ range (ν + 1), b i ^ 2) + 2 * c ^ 2) := by
          gcongr; linarith
      _ = 2 * (ν + 1) * (h ^ n * ∑ i ∈ range (ν + 1), b i ^ 2) + 2 * (h ^ n * c ^ 2) := by ring
      _ ≤ 2 * (ν + 1) * (n.factorial * S0) +
          2 * (embA n ν ^ 2 * rieszC n ν * (h ^ (2 * (ν + 1)) * I (ν + 1))) := by
          rw [hc2]; gcongr
      _ ≤ _ := by
          have : (0 : ℝ) ≤ n.factorial := by positivity
          have : (0 : ℝ) ≤ ν := by positivity
          nlinarith [mul_nonneg hK0 hS0, mul_nonneg this hL0, mul_nonneg (mul_nonneg this this) hL0]
  have hci := sq_nonneg (interpCi n S k)
  calc ∑ t : formIdx n k, ∫ x in T'.closedInterior, (w x t.1 - (Iw : FormField n) x t.1) ^ 2
      ≤ ∑ _t : formIdx n k, h ^ n * e ^ 2 := Finset.sum_le_sum fun t _ => hone t
    _ = Fintype.card (formIdx n k) * (h ^ n * e ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * (h ^ n * e ^ 2) :=
        mul_le_mul_of_nonneg_right (card_formIdx_le _) (by positivity)
    _ = 2 ^ n * interpCi n S k ^ 2 * h ^ (2 * (p + 1)) * (h ^ n * M ^ 2) := by
        simp only [e]; ring
    _ ≤ 2 ^ n * interpCi n S k ^ 2 * h ^ (2 * (p + 1)) * ((((2 * (ν + 1) * n.factorial : ℕ) : ℝ) +
      2 * embA n ν ^ 2 * rieszC n ν) * ∑ i ∈ range (ν + 2), h ^ (2 * i) * I i) := by gcongr
    _ = _ := by unfold localL2SumConst; ring

variable (n) in
/-- The constant `(6ⁿ n! localL2SumConst)^{1/2}` of the global `L²` interpolation error with
lower-order terms. -/
def globalL2SumConst (S : PolySeq) (k : ℕ) : ℝ :=
  √(localL2SumConst n S k * (6 ^ n * n.factorial : ℕ))

theorem globalL2SumConst_nonneg (S : PolySeq) (k : ℕ) : 0 ≤ globalL2SumConst n S k :=
  Real.sqrt_nonneg _

/-- **The global `L²` interpolation error with lower-order terms** on the Freudenthal meshes, in
every dimension: `‖w - Π_h w‖_{L²(Q)} ≤ C h_N^{p+1} Σ_{i ≤ ⌊n/2⌋ + 1} h_Nⁱ ‖D^{i+p+1} w‖_{L²(Q)}`
for `P_pΛᵏ ⊆ P(T)ᵏ`, `C = globalL2SumConst n S k` (`sum_integral_sq_sub_globalInterp_le_sum`,
bounded overlap). -/
theorem norm_formL2_sub_glue_globalInterp_le_sum [NeZero n] (S : PolySeq) {N k p : ℕ}
    (hs : polySpace n p k ≤ S.space n k) {w : FormField n} (hw : ContDiff ℝ ∞ w)
    (hdeg : ∀ x, IsDeg k (w x)) :
    ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
        ⟨w, hw.continuous⟩ - (polyElement n S).glue (mesh n N) k
          ((polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩ :
            (polyElement n S).Piecewise (mesh n N) k)‖ ≤
      globalL2SumConst n S k * hN N ^ (p + 1) * ∑ i ∈ range (n / 2 + 2), hN N ^ i *
        √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (i + (p + 1)) w y‖ ^ 2) := by
  set u := ((polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩ :
    (polyElement n S).Piecewise (mesh n N) k)
  have hK := localL2SumConst_nonneg (n := n) S k
  have hh := (hN_pos N).le
  set J : ℕ → ℝ := fun i => ∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (i + (p + 1)) w y‖ ^ 2
  have hJ : ∀ i, 0 ≤ J i := fun i =>
    setIntegral_nonneg (isOpen_cubeDomain n).measurableSet fun _ _ => sq_nonneg _
  have hsq := norm_sq_formL2_sub_glue_le (polyElement n S) (mesh n N)
    (isOpen_mesh_domain n N).measurableSet k ⟨w, hw.continuous⟩ u
  have h2 : ∑ T ∈ (mesh n N).simplices, ∑ s : formIdx n k, ∫ x in T.closedInterior,
      (w x s.1 - (polyElement n S).extendPW (mesh n N) u T x s.1) ^ 2 ≤
      ∑ T ∈ (mesh n N).simplices, localL2SumConst n S k * hN N ^ (2 * (p + 1)) *
        ∑ i ∈ range (n / 2 + 2), hN N ^ (2 * i) *
          ∫ y in T.closedInterior, ‖iteratedFDeriv ℝ (i + (p + 1)) w y‖ ^ 2 := by
    refine Finset.sum_le_sum fun T hT => ?_
    have e : ∀ x, (polyElement n S).extendPW (mesh n N) u T x =
        ((u (⟨T, hT⟩ : (mesh n N).simplices) : (polyElement n S).space
          (⟨T, hT⟩ : (mesh n N).simplices) k) : FormField n) x := fun x => by
      rw [(polyElement n S).extendPW_of_mem (mesh n N) u hT]
    simp_rw [e]
    exact sum_integral_sq_sub_globalInterp_le_sum S hs (⟨T, hT⟩ : (mesh n N).simplices) hw hdeg
  have h3 : ∀ i, ∑ T ∈ (mesh n N).simplices,
      ∫ y in T.closedInterior, ‖iteratedFDeriv ℝ (i + (p + 1)) w y‖ ^ 2 ≤
        ((6 ^ n * n.factorial : ℕ) : ℝ) * J i := fun i =>
    sum_integral_closedInterior_le N
      (((hw.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm).pow 2)
      (fun _ => sq_nonneg _)
  set x : ℕ → ℝ := fun i => hN N ^ i * √(J i)
  have hx : ∀ i, 0 ≤ x i := fun i => mul_nonneg (pow_nonneg hh _) (Real.sqrt_nonneg _)
  have hxs : ∑ i ∈ range (n / 2 + 2), x i ^ 2 ≤ (∑ i ∈ range (n / 2 + 2), x i) ^ 2 := by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => hx j) hi) (hx i)
  have h4 : ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
        ⟨w, hw.continuous⟩ - (polyElement n S).glue (mesh n N) k u‖ ^ 2 ≤
      (globalL2SumConst n S k * hN N ^ (p + 1) * ∑ i ∈ range (n / 2 + 2), x i) ^ 2 := by
    refine hsq.trans (h2.trans ?_)
    rw [← Finset.mul_sum, mul_pow, mul_pow, globalL2SumConst, Real.sq_sqrt (by positivity),
      ← pow_mul, mul_comm (p + 1) 2, Finset.sum_comm]
    calc localL2SumConst n S k * hN N ^ (2 * (p + 1)) * ∑ i ∈ range (n / 2 + 2),
          ∑ T ∈ (mesh n N).simplices, hN N ^ (2 * i) *
            ∫ y in T.closedInterior, ‖iteratedFDeriv ℝ (i + (p + 1)) w y‖ ^ 2
        ≤ localL2SumConst n S k * hN N ^ (2 * (p + 1)) * ∑ i ∈ range (n / 2 + 2),
            ((6 ^ n * n.factorial : ℕ) : ℝ) * x i ^ 2 := by
          gcongr with i
          rw [← Finset.mul_sum, mul_pow, Real.sq_sqrt (hJ i), ← pow_mul, mul_comm i 2]
          calc hN N ^ (2 * i) * _ ≤ hN N ^ (2 * i) * (((6 ^ n * n.factorial : ℕ) : ℝ) * J i) :=
                mul_le_mul_of_nonneg_left (h3 i) (by positivity)
            _ = _ := by ring
      _ ≤ _ := by
          rw [← Finset.mul_sum]
          have : (0 : ℝ) ≤ ((6 ^ n * n.factorial : ℕ) : ℝ) := by positivity
          calc localL2SumConst n S k * hN N ^ (2 * (p + 1)) *
                (((6 ^ n * n.factorial : ℕ) : ℝ) * ∑ i ∈ range (n / 2 + 2), x i ^ 2)
              ≤ localL2SumConst n S k * hN N ^ (2 * (p + 1)) *
                (((6 ^ n * n.factorial : ℕ) : ℝ) * (∑ i ∈ range (n / 2 + 2), x i) ^ 2) := by
                gcongr
            _ = _ := by ring
  have := globalL2SumConst_nonneg (n := n) S k
  exact (sq_le_sq₀ (norm_nonneg _) (by
    have := Finset.sum_nonneg fun i (_ : i ∈ range (n / 2 + 2)) => hx i
    positivity)).1 h4

/-! #### In the finite element spaces of the cube -/

/-- **The canonical interpolant in `Vₕᵏ ⊆ HΛᵏ(Q)`**: a bound `e` of the `L²` interpolation error
`‖w - Π_h w‖` on the mesh domain bounds the distance of `w` to `(poly n S N).V k`. -/
theorem exists_mem_poly_of_le [NeZero n] (S : PolySeq) (N k : ℕ) {w : FormField n}
    (hw : Continuous w) {e : ℝ}
    (he : ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
        ⟨w, hw⟩ - (polyElement n S).glue (mesh n N) k
          ((polyElement n S).globalInterp (mesh n N) k ⟨w, hw⟩ :
            (polyElement n S).Piecewise (mesh n N) k)‖ ≤ e) :
    ∃ v ∈ (poly n S N).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw⟩ - v‖ ≤ e := by
  refine (deRham ℝ n).maximalSubcomplexOfEq_induction (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (S.subcomplex (mesh n N) (isOpen_mesh_domain n N))
    (fun Θ hΘ S' => ∀ hb : Bornology.IsBounded Θ,
      ∃ v ∈ S'.V k, ‖formL2 hΘ.measurableSet hb k ⟨w, hw⟩ - asForm n v‖ ≤ e) ?_
    (isBounded_cubeDomain n)
  intro hb
  set u := (polyElement n S).globalInterp (mesh n N) k ⟨w, hw⟩
  exact ⟨(polyElement n S).glue (mesh n N) k (u : (polyElement n S).Piecewise (mesh n N) k),
    ⟨u, rfl⟩, he⟩

/-- **The canonical interpolant in `V_{h,Γ_J}ᵏ ⊆ HΛ_Jᵏ(Q)`**: as `exists_mem_poly_of_le`, for a
form whose tangential components vanish on the faces normal to `J`, with the interpolant in
`(polyPartial n S N J).V k` (vanishing boundary DOFs on those faces). -/
theorem exists_mem_polyPartial_of_le [NeZero n] (S : PolySeq) (J : Finset (Fin n)) (N k : ℕ)
    {w : FormField n} (hw : Continuous w)
    (hJ : ∀ x : Fin n → ℝ, ∀ j ∈ J, (x j = 0 ∨ x j = 1 / 2) → ∀ t : Finset (Fin n), j ∉ t →
      w x t = 0)
    {e : ℝ} (he : ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
        ⟨w, hw⟩ - (polyElement n S).glue (mesh n N) k
          ((polyElement n S).globalInterp (mesh n N) k ⟨w, hw⟩ :
            (polyElement n S).Piecewise (mesh n N) k)‖ ≤ e) :
    ∃ v ∈ (polyPartial n S N J).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw⟩ - v‖ ≤ e := by
  have hV : ∃ v ∈ (polyElement n S).VPartial (mesh n N) (partialFaces n J) k,
      ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
          ⟨w, hw⟩ - v‖ ≤ e := by
    set u := (polyElement n S).globalInterp (mesh n N) k ⟨w, hw⟩
    exact ⟨(polyElement n S).glue (mesh n N) k (u : (polyElement n S).Piecewise (mesh n N) k),
      ⟨⟨_, globalInterp_mem_globalSpacePartial_of_face (polyElement n S) (mesh n N) J k _ hJ⟩,
        rfl⟩, he⟩
  have key : ∀ (Ω' : Set (Fin n → ℝ)) (h : (mesh n N).domain = Ω') (hΩ' : IsOpen Ω')
      (hΩQ' : Ω' ⊆ Geometry.Q (Fin n)) (hb : Bornology.IsBounded Ω'),
      ∃ v ∈ (partialSubcomplexOfEq h (isOpen_of_eq_Q (mesh_domain_eq_Q N))
          (mesh_domain_eq_Q N).le hΩ' hΩQ' J
          (subcomplexPart (polyElement n S) (mesh n N) (mesh_domain_eq_Q N) J)).V k,
        ‖formL2 hΩ'.measurableSet hb k ⟨w, hw⟩ - v‖ ≤ e := by
    rintro Ω' rfl hΩ' hΩQ' hb
    exact hV
  exact key _ (mesh_domain n N) (isOpen_cubeDomain n) (cubeDomain_subset_Q n)
    (isBounded_cubeDomain n)

/-- **`L²` interpolation from `L²` derivatives in `Vₕᵏ ⊆ HΛᵏ(Q)`**: for a smooth degree-`k` form
`w`, some `v ∈ (poly n S N).V k` has
`‖w - v‖ ≤ C h_N^{p+1} ‖D^{p+1} w‖_{L²(Q)}` (`P_pΛᵏ ⊆ P(T)ᵏ`, `2(p + 1) > n`). -/
theorem exists_mem_poly_le_L2 [NeZero n] (S : PolySeq) (N k p : ℕ)
    (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1)) {w : FormField n}
    (hw : ContDiff ℝ ∞ w) (hdeg : ∀ x, IsDeg k (w x)) :
    ∃ v ∈ (poly n S N).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ - v‖ ≤ globalL2Const n S k p * meshSize N ^ (p + 1) *
        √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2) :=
  exists_mem_poly_of_le S N k hw.continuous
    (hN_eq_meshSize N ▸ norm_formL2_sub_glue_globalInterp_le S hs hns hw hdeg)

/-- **`L²` interpolation from `L²` derivatives in `V_{h,Γ_J}ᵏ ⊆ HΛ_Jᵏ(Q)`**: as
`exists_mem_poly_le_L2`, for a form whose tangential components vanish on the faces normal to
`J` (`exists_mem_polyPartial_of_le`). -/
theorem exists_mem_polyPartial_le_L2 [NeZero n] (S : PolySeq) (J : Finset (Fin n)) (N k p : ℕ)
    (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1)) {w : FormField n}
    (hw : ContDiff ℝ ∞ w) (hdeg : ∀ x, IsDeg k (w x))
    (hJ : ∀ x : Fin n → ℝ, ∀ j ∈ J, (x j = 0 ∨ x j = 1 / 2) → ∀ t : Finset (Fin n), j ∉ t →
      w x t = 0) :
    ∃ v ∈ (polyPartial n S N J).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ - v‖ ≤ globalL2Const n S k p * meshSize N ^ (p + 1) *
        √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ (p + 1) w y‖ ^ 2) :=
  exists_mem_polyPartial_of_le S J N k hw.continuous hJ
    (hN_eq_meshSize N ▸ norm_formL2_sub_glue_globalInterp_le S hs hns hw hdeg)

/-! ### The truncations as smooth forms on the cube -/

theorem castL2F_apply_ae {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') {ι : Type} [Fintype ι]
    (u : L2F ℝ Ω ι) (t : ι) :
    ((castL2F h ι u t : L2 ℝ Ω') : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Ω']
      ((u t : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) := by
  subst h; rfl

theorem integral_cubeDomain_eq (f : (Fin n → ℝ) → ℝ) :
    ∫ y in cubeDomain n, f y = ∫ y in Q (Fin n), f y := by
  rw [cubeDomain_eq_Q]

/-- **The truncation as a smooth form**: `(x_M)|_Q` is the form `truncField k x M` of the finite
element method, transported to `Q` (`toQ`). -/
theorem toQ_formL2_truncField (k : ℕ) (x : Seq n k) (M : ℕ) :
    toQ k (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
      ⟨truncField k x M, (contDiff_truncField x M).continuous⟩) = Jinvf k (trunc M k x) := by
  rw [Jinvf_trunc_eq_toL2F]
  refine PiLp.ext fun t => Lp.ext ?_
  have h2 := ae_restrict_of_ae_restrict_of_subset (cubeDomain_eq_Q n).symm.le
    (coeFn_formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
      ⟨truncField k x M, (contDiff_truncField x M).continuous⟩ t)
  filter_upwards [castL2F_apply_ae (cubeDomain_eq_Q n) _ t, h2,
    (DeRhamIdent.memLp_trigLift k (trunc M k x) (DeRhamIdent.bandS M) t).coeFn_toLp] with y h1 h2 h3
  rw [h1, h2]
  rw [truncField_val]
  exact h3.symm

theorem isDeg_truncField (k : ℕ) (x : Seq n k) (M : ℕ) (y : Fin n → ℝ) :
    IsDeg k (truncField k x M y) := fun _ hs => truncField_of_ne x M y hs

/-- **The parity truncation has vanishing tangential components on the faces normal to `J`**. -/
theorem truncField_face (J : Finset (Fin n)) (k : ℕ)
    (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) (M : ℕ) :
    ∀ y : Fin n → ℝ, ∀ j ∈ J, (y j = 0 ∨ y j = 1 / 2) → ∀ t : Finset (Fin n), j ∉ t →
      truncField k (JfJ J k u) M y t = 0 := by
  intro y j hj hy t ht
  by_cases hk : #t = k
  · have hk' : (#t : ℤ) = k := by exact_mod_cast hk
    rw [show t = (⟨t, hk'⟩ : formIdx n (k : ℤ)).1 from rfl, truncField_val]
    exact DeRhamIdent.trigLift_eq_zero_of_faceJ
      (DeRhamIdent.realParJ_trunc (DeRhamIdent.JfJ_realParJ J k u) M)
      (fun j m hm => DeRhamIdent.flipAt_mem_bandS j hm) hj ht hy
  · exact truncField_of_ne _ M y hk

/-! ### Best approximation of `Hˢ` data at the optimal rate -/

/-- `h_N^r (1 + n (2π(N+1))²)^{(r-q)/2} ≤ ((1 + n) π²)^r h_N^q` for `0 ≤ q ≤ r`. -/
theorem meshSize_pow_mul_rpow_le {q : ℝ} {r : ℕ} (hq0 : 0 ≤ q) (hqr : q ≤ r) (N : ℕ) :
    meshSize N ^ r * (1 + n * (2 * Real.pi * ((N + 1 : ℕ) : ℝ)) ^ 2) ^ (((r : ℝ) - q) / 2) ≤
      ((1 + n) * Real.pi ^ 2) ^ r * meshSize N ^ q := by
  set h := meshSize N
  have hh : 0 < h := meshSize_pos N
  set A : ℝ := (1 + n) * Real.pi ^ 2
  have hA1 : 1 ≤ A := by
    have h4 : 4 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    calc (1 : ℝ) ≤ 1 * Real.pi ^ 2 := by linarith
      _ ≤ A := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have he0 : 0 ≤ ((r : ℝ) - q) / 2 := by linarith
  rw [two_pi_mul_succ_eq]
  have hb : 1 + n * (Real.pi / h) ^ 2 ≤ A / h ^ 2 := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
    have : h ^ 2 ≤ Real.pi ^ 2 := by
      have := Real.two_le_pi
      have := meshSize_le_half N
      exact pow_le_pow_left₀ hh.le (by linarith) 2
    have : 0 ≤ (n : ℝ) := n.cast_nonneg
    rw [add_mul, one_mul, div_mul_cancel₀ _ (by positivity)]
    nlinarith
  have h1 := Real.rpow_le_rpow (by positivity) hb he0
  have h2 : (A / h ^ 2) ^ (((r : ℝ) - q) / 2) = A ^ (((r : ℝ) - q) / 2) / h ^ ((r : ℝ) - q) := by
    rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast h 2,
      ← Real.rpow_mul hh.le]
    norm_num
    ring_nf
  have h3 : A ^ (((r : ℝ) - q) / 2) ≤ A ^ r := by
    rw [← Real.rpow_natCast A r]
    exact Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
  have h4 : h ^ r / h ^ ((r : ℝ) - q) = h ^ q := by
    rw [← Real.rpow_natCast h r, ← Real.rpow_sub hh]
    ring_nf
  calc h ^ r * (1 + n * (Real.pi / h) ^ 2) ^ (((r : ℝ) - q) / 2) ≤
        h ^ r * (A ^ (((r : ℝ) - q) / 2) / h ^ ((r : ℝ) - q)) :=
        mul_le_mul_of_nonneg_left (h1.trans (le_of_eq h2)) (by positivity)
    _ = A ^ (((r : ℝ) - q) / 2) * (h ^ r / h ^ ((r : ℝ) - q)) := by ring
    _ ≤ A ^ r * h ^ q := by
        rw [h4]; exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hh.le _)

/-- **The Bernstein step of the optimal rate**: for an extension `x ∈ Hˢ(𝕋ⁿ)`, `0 ≤ q ≤ r` and
`q ≤ s`, the truncation `u_M` (`M = N + 1`) satisfies
`h_N^r ‖D^r u_M‖_{L²(Q)} ≤ (2ⁿ n^r)^{1/2} ((1 + n) π²)^r h_N^q ‖x‖_{Hˢ(𝕋ⁿ)}`
(`sum_norm_iteratedFDeriv_truncQ_sq_le`, `meshSize_pow_mul_rpow_le`). -/
theorem meshSize_pow_mul_sqrt_integral_truncField_le {k r : ℕ} {q s : ℝ} (hq0 : 0 ≤ q)
    (hqr : q ≤ r) (hqs : q ≤ s) {x : Seq n k} (hx : MemSob s x) (N : ℕ) :
    meshSize N ^ r * √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ r (truncField k x (N + 1)) y‖ ^ 2) ≤
      √(2 ^ n * (n : ℝ) ^ r) * ((1 + n) * Real.pi ^ 2) ^ r * meshSize N ^ q * √(sobSum s x) := by
  have hq : MemSob q x := hx.mono hqs
  have hB := sum_norm_iteratedFDeriv_truncQ_sq_le (p := r) hqr hq (N + 1)
  rw [← integral_cubeDomain_eq] at hB
  have hh := (meshSize_pos N).le
  set A : ℝ := (1 + n * (2 * Real.pi * ((N + 1 : ℕ) : ℝ)) ^ 2)
  have hA : 0 ≤ A := by positivity
  have hsq : √(∫ y in cubeDomain n, ‖iteratedFDeriv ℝ r (truncField k x (N + 1)) y‖ ^ 2) ≤
      √(2 ^ n * (n : ℝ) ^ r) * A ^ (((r : ℝ) - q) / 2) * √(sobSum s x) := by
    refine (Real.sqrt_le_sqrt hB).trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (sobSum_mono hqs hx)) (by positivity)))
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (Real.rpow_nonneg hA _),
      Real.sqrt_eq_rpow (A ^ _), ← Real.rpow_mul hA]
    ring_nf
  have hm := meshSize_pow_mul_rpow_le (n := n) hq0 hqr N
  calc meshSize N ^ r * √(∫ y in cubeDomain n,
        ‖iteratedFDeriv ℝ r (truncField k x (N + 1)) y‖ ^ 2)
      ≤ meshSize N ^ r * (√(2 ^ n * (n : ℝ) ^ r) * A ^ (((r : ℝ) - q) / 2) * √(sobSum s x)) := by
        gcongr
    _ = √(2 ^ n * (n : ℝ) ^ r) * √(sobSum s x) * (meshSize N ^ r * A ^ (((r : ℝ) - q) / 2)) := by
        ring
    _ ≤ √(2 ^ n * (n : ℝ) ^ r) * √(sobSum s x) * (((1 + n) * Real.pi ^ 2) ^ r * meshSize N ^ q) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

variable (n) in
/-- The constant of the optimal-rate best-approximation estimate in degree `k` for an order-`p`
sequence (`r_eff = p + 1`):
`1 + C_glob Σ_{i ≤ ⌊n/2⌋ + 1} (2ⁿ n^{i+p+1})^{1/2} ((1 + n) π²)^{i+p+1}`,
`C_glob = globalL2SumConst n S k`. -/
def sobConstHigh (S : PolySeq) (k p : ℕ) : ℝ :=
  1 + globalL2SumConst n S k * ∑ i ∈ range (n / 2 + 2),
    √(2 ^ n * (n : ℝ) ^ (i + (p + 1))) * ((1 + n) * Real.pi ^ 2) ^ (i + (p + 1))

theorem sobConstHigh_nonneg (S : PolySeq) (k p : ℕ) : 0 ≤ sobConstHigh n S k p := by
  have := globalL2SumConst_nonneg (n := n) S k
  unfold sobConstHigh; positivity

/-- **The interpolation step of the optimal rate**: for an extension `x ∈ Hˢ(𝕋ⁿ)`,
`0 ≤ q ≤ p + 1` and `q ≤ s`, the canonical interpolant of the truncation `u_M` (`M = N + 1`)
satisfies `‖u_M - Π_h u_M‖ ≤ (sobConstHigh - 1) h_N^q ‖x‖_{Hˢ(𝕋ⁿ)}`, in every dimension
(`norm_formL2_sub_glue_globalInterp_le_sum`, and the Bernstein step
`meshSize_pow_mul_sqrt_integral_truncField_le` in each order `i + p + 1 ≥ q`). -/
theorem norm_formL2_truncField_sub_glue_le [NeZero n] (S : PolySeq) {k p : ℕ}
    (hs : polySpace n p k ≤ S.space n k) {q s : ℝ} (hq0 : 0 ≤ q) (hqp : q ≤ p + 1)
    (hqs : q ≤ s) {x : Seq n k} (hx : MemSob s x) (N : ℕ) :
    ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
        ⟨truncField k x (N + 1), (contDiff_truncField x (N + 1)).continuous⟩ -
      (polyElement n S).glue (mesh n N) k
        ((polyElement n S).globalInterp (mesh n N) k
          ⟨truncField k x (N + 1), (contDiff_truncField x (N + 1)).continuous⟩ :
            (polyElement n S).Piecewise (mesh n N) k)‖ ≤
      (sobConstHigh n S k p - 1) * meshSize N ^ q * √(sobSum s x) := by
  have hG := globalL2SumConst_nonneg (n := n) S k
  have hb := norm_formL2_sub_glue_globalInterp_le_sum S (N := N) hs
    (contDiff_truncField x (N + 1)) (isDeg_truncField k x (N + 1))
  rw [hN_eq_meshSize] at hb
  refine hb.trans ?_
  rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, sobConstHigh, add_sub_cancel_left,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_assoc (meshSize N ^ (p + 1)), ← pow_add, add_comm (p + 1) i, mul_assoc, mul_assoc,
    mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hG
  have := meshSize_pow_mul_sqrt_integral_truncField_le hq0 (r := i + (p + 1))
    (by push_cast; linarith) hqs hx N
  linarith

variable (n) in
/-- The constant of the optimal-rate estimate through the embedding of `w` itself
(`2(p + 1) > n`, `norm_formL2_truncField_sub_glue_le_emb`):
`1 + C_glob (2ⁿ n^{p+1})^{1/2} ((1 + n) π²)^{p+1}`, `C_glob = globalL2Const n S k p`. -/
def sobConstHighEmb (S : PolySeq) (k p : ℕ) : ℝ :=
  1 + globalL2Const n S k p * √(2 ^ n * (n : ℝ) ^ (p + 1)) * ((1 + n) * Real.pi ^ 2) ^ (p + 1)

theorem sobConstHighEmb_nonneg (S : PolySeq) (k p : ℕ) : 0 ≤ sobConstHighEmb n S k p := by
  have := globalL2Const_nonneg (n := n) S k p
  unfold sobConstHighEmb; positivity

/-- **The interpolation step of the optimal rate for `2(p + 1) > n`**: as
`norm_formL2_truncField_sub_glue_le`, with the single-term estimate
`norm_formL2_sub_glue_globalInterp_le` (embedding of `w` itself) and the Bernstein step in the
order `p + 1` only, and the constant `sobConstHighEmb`. -/
theorem norm_formL2_truncField_sub_glue_le_emb [NeZero n] (S : PolySeq) {k p : ℕ}
    (hs : polySpace n p k ≤ S.space n k) (hns : n < 2 * (p + 1)) {q s : ℝ} (hq0 : 0 ≤ q)
    (hqp : q ≤ p + 1) (hqs : q ≤ s) {x : Seq n k} (hx : MemSob s x) (N : ℕ) :
    ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
        ⟨truncField k x (N + 1), (contDiff_truncField x (N + 1)).continuous⟩ -
      (polyElement n S).glue (mesh n N) k
        ((polyElement n S).globalInterp (mesh n N) k
          ⟨truncField k x (N + 1), (contDiff_truncField x (N + 1)).continuous⟩ :
            (polyElement n S).Piecewise (mesh n N) k)‖ ≤
      (sobConstHighEmb n S k p - 1) * meshSize N ^ q * √(sobSum s x) := by
  have hb := norm_formL2_sub_glue_globalInterp_le S (N := N) hs hns
    (contDiff_truncField x (N + 1)) (isDeg_truncField k x (N + 1))
  rw [hN_eq_meshSize] at hb
  have hB := meshSize_pow_mul_sqrt_integral_truncField_le hq0 (r := p + 1)
    (by exact_mod_cast hqp) hqs hx N
  have hG := globalL2Const_nonneg (n := n) S k p
  refine hb.trans ?_
  rw [sobConstHighEmb, add_sub_cancel_left]
  have := mul_le_mul_of_nonneg_left hB hG
  linarith

/-- **Best approximation of `Hˢ(Q)` forms from an interpolation bound on the truncations**
(`infDist_poly_le_sobolevQ_of_near`): if, for `0 ≤ q ≤ s`, the canonical interpolant of the
truncation `u_M` (`M = N + 1`) of every `x ∈ Hˢ(𝕋ⁿ)` has
`‖u_M - Π_h u_M‖ ≤ (C - 1) h_N^q ‖x‖_{Hˢ(𝕋ⁿ)}`, then
`dist(y, Vₕᵏ) ≤ C h_N^q ‖y‖_{Hˢ(Q)}`. The truncation error of an extension is
`≤ h_N^q ‖x‖_{Hˢ(𝕋ⁿ)}` (`norm_sub_Jinvf_trunc_le`, `M ≈ 1/(2h_N)`). -/
theorem infDist_poly_le_sobolevQ_of_near [NeZero n] (S : PolySeq) {k N : ℕ} {C q s : ℝ}
    (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hqs : q ≤ s)
    (hnear : ∀ x : Seq n k, MemSob s x →
      ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
          ⟨truncField k x (N + 1), (contDiff_truncField x (N + 1)).continuous⟩ -
        (polyElement n S).glue (mesh n N) k
          ((polyElement n S).globalInterp (mesh n N) k
            ⟨truncField k x (N + 1), (contDiff_truncField x (N + 1)).continuous⟩ :
              (polyElement n S).Piecewise (mesh n N) k)‖ ≤
        (C - 1) * meshSize N ^ q * √(sobSum s x))
    (y : L2F ℝ (cubeDomain n) (formIdx n k)) (hy : toQ k y ∈ sobolevQ n k s) :
    Metric.infDist y ((poly n S N).V k) ≤ C * meshSize N ^ q * qNorm k s (toQ k y) := by
  have hh := meshSize_pos N
  refine le_mul_qNorm hy (mul_nonneg hC (Real.rpow_nonneg hh.le q)) fun x hx hxu => ?_
  set M := N + 1
  set w := truncField k x M
  have hw := contDiff_truncField x M
  set z' := formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw.continuous⟩
  have hz : toQ k z' = Jinvf k (trunc M k x) := toQ_formL2_truncField k x M
  obtain ⟨v, hv, hzv⟩ := exists_mem_poly_of_le S N k hw.continuous (hnear x hx)
  set σ := √(sobSum s x)
  have h1 : ‖y - z'‖ ≤ meshSize N ^ q * σ := by
    have e : ‖y - z'‖ = ‖Jinvf k x - Jinvf k (trunc M k x)‖ := by
      rw [← (toQ k).norm_map, map_sub, hz, hxu]
    rw [e]
    refine (norm_sub_Jinvf_trunc_le hq0 (hx.mono hqs) M).trans ?_
    exact mul_le_mul (rpow_neg_le_meshSize_rpow hq0 N)
      (Real.sqrt_le_sqrt (sobSum_mono hqs hx)) (Real.sqrt_nonneg _) (Real.rpow_nonneg hh.le _)
  calc Metric.infDist y ((poly n S N).V k) ≤ dist y v := Metric.infDist_le_dist_of_mem hv
    _ = ‖y - v‖ := dist_eq_norm y v
    _ ≤ ‖y - z'‖ + ‖z' - v‖ := norm_sub_le_norm_sub_add_norm_sub y z' v
    _ ≤ meshSize N ^ q * σ + (C - 1) * meshSize N ^ q * σ := add_le_add h1 hzv
    _ = C * meshSize N ^ q * σ := by ring

/-- **Best approximation of `Hˢ(Q)` forms at the optimal rate**
(`infDist_poly_le_sobolevQ_high`; [AFW2010], §5; [Arnold2018], Ch. 7): for a sequence `S`
reproducing `P_pΛᵏ` in degree `k` (`r_eff = p + 1`, e.g. `FEM.PolyOrder n S p`), in every
dimension, and every real `s ≥ 0`,
`dist(y, Vₕᵏ) ≤ C h_N^{min(s, r_eff)} ‖y‖_{Hˢ(Q)}`, `C = sobConstHigh n S k p` independent of
`N` and `s`: `infDist_poly_le_sobolevQ_of_near` with the interpolation step
`norm_formL2_truncField_sub_glue_le` (the `L²` estimate of the canonical interpolant with
lower-order terms, and the Bernstein inequality in every order `r_eff + i`). -/
theorem infDist_poly_le_sobolevQ_high [NeZero n] (S : PolySeq) (k p : ℕ)
    (hs : polySpace n p k ≤ S.space n k) {s : ℝ} (hs0 : 0 ≤ s)
    (N : ℕ) (y : L2F ℝ (cubeDomain n) (formIdx n k)) (hy : toQ k y ∈ sobolevQ n k s) :
    Metric.infDist y ((poly n S N).V k) ≤
      sobConstHigh n S k p * meshSize N ^ min s (p + 1) * qNorm k s (toQ k y) :=
  have hq0 : 0 ≤ min s (p + 1) := le_min hs0 (by positivity)
  infDist_poly_le_sobolevQ_of_near S (sobConstHigh_nonneg S k p) hq0 (min_le_left _ _)
    (fun _ hx => norm_formL2_truncField_sub_glue_le S hs hq0 (min_le_right _ _)
      (min_le_left _ _) hx N) y hy

/-- **Best approximation of the parity classes from an interpolation bound on the truncations**
(`infDist_polyPartial_le_sobolevPar_of_near`): for `y ∈ Hˢ_J(Q; Λᵏ)`, every class `J`, the
hypothesis of `infDist_poly_le_sobolevQ_of_near` gives
`dist(y, V_{h,Γ_J}ᵏ) ≤ 2^{n/2} C h_N^q ‖y‖_{s,J}`. The parity truncation `truncPar` stays in the
class, its tangential components vanish on the faces normal to `J` (`truncField_face`), and the
canonical interpolant has vanishing boundary DOFs there (`exists_mem_polyPartial_of_le`). -/
theorem infDist_polyPartial_le_sobolevPar_of_near [NeZero n] (S : PolySeq) (J : Finset (Fin n))
    {k N : ℕ} {C q s : ℝ} (hq0 : 0 ≤ q) (hqs : q ≤ s)
    (hnear : ∀ x : Seq n k, MemSob s x →
      ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
          ⟨truncField k x (N + 1), (contDiff_truncField x (N + 1)).continuous⟩ -
        (polyElement n S).glue (mesh n N) k
          ((polyElement n S).globalInterp (mesh n N) k
            ⟨truncField k x (N + 1), (contDiff_truncField x (N + 1)).continuous⟩ :
              (polyElement n S).Piecewise (mesh n N) k)‖ ≤
        (C - 1) * meshSize N ^ q * √(sobSum s x))
    (y : L2F ℝ (cubeDomain n) (formIdx n k)) (hy : toQ k y ∈ sobolevPar J k s) :
    Metric.infDist y ((polyPartial n S N J).V k) ≤
      √(2 ^ n) * C * meshSize N ^ q * parNorm J k s (toQ k y) := by
  have hh := meshSize_pos N
  set u := toQ k y
  set x := JfJ J k u
  have hx : MemSob s x := (mem_sobolevPar J k).1 hy
  have hxu : Jinvf k x = u := DeRhamIdent.Jinvf_JfJ J k u
  set M := N + 1
  set w := truncField k x M
  have hw := contDiff_truncField x M
  set z' := formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw.continuous⟩
  have hz : toQ k z' = Jinvf k (trunc M k x) := toQ_formL2_truncField k x M
  obtain ⟨v, hv, hzv⟩ := exists_mem_polyPartial_of_le S J N k hw.continuous
    (truncField_face J k u M) (hnear x hx)
  set σ := √(sobSum s x)
  have hσ : σ = √(2 ^ n) * parNorm J k s u := by
    show √(sobSum s (JfJ J k u)) = _
    rw [show sobSum s (JfJ J k u) = 2 ^ n * parNorm J k s u ^ 2 by rw [parNorm_sq]; field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (parNorm_nonneg J k s u)]
  have h1 : ‖y - z'‖ ≤ meshSize N ^ q * σ := by
    have e : ‖y - z'‖ = ‖Jinvf k x - Jinvf k (trunc M k x)‖ := by
      rw [← (toQ k).norm_map, map_sub, hz, hxu]
    rw [e]
    refine (norm_sub_Jinvf_trunc_le hq0 (hx.mono hqs) M).trans ?_
    exact mul_le_mul (rpow_neg_le_meshSize_rpow hq0 N)
      (Real.sqrt_le_sqrt (sobSum_mono hqs hx)) (Real.sqrt_nonneg _) (Real.rpow_nonneg hh.le _)
  calc Metric.infDist y ((polyPartial n S N J).V k) ≤ dist y v := Metric.infDist_le_dist_of_mem hv
    _ = ‖y - v‖ := dist_eq_norm y v
    _ ≤ ‖y - z'‖ + ‖z' - v‖ := norm_sub_le_norm_sub_add_norm_sub y z' v
    _ ≤ meshSize N ^ q * σ + (C - 1) * meshSize N ^ q * σ := add_le_add h1 hzv
    _ = _ := by rw [hσ]; ring

/-- **Best approximation of the parity classes at the optimal rate**
(`infDist_polyPartial_le_sobolevPar_high`): for `y ∈ Hˢ_J(Q; Λᵏ)`, every class `J`,
`dist(y, V_{h,Γ_J}ᵏ) ≤ C' h_N^{min(s, r_eff)} ‖y‖_{s,J}`, `C' = 2^{n/2} sobConstHigh n S k p`
(`infDist_polyPartial_le_sobolevPar_of_near`, `norm_formL2_truncField_sub_glue_le`). -/
theorem infDist_polyPartial_le_sobolevPar_high [NeZero n] (S : PolySeq) (J : Finset (Fin n))
    (k p : ℕ) (hs : polySpace n p k ≤ S.space n k) {s : ℝ}
    (hs0 : 0 ≤ s) (N : ℕ) (y : L2F ℝ (cubeDomain n) (formIdx n k))
    (hy : toQ k y ∈ sobolevPar J k s) :
    Metric.infDist y ((polyPartial n S N J).V k) ≤
      √(2 ^ n) * sobConstHigh n S k p * meshSize N ^ min s (p + 1) *
        parNorm J k s (toQ k y) :=
  have hq0 : 0 ≤ min s (p + 1) := le_min hs0 (by positivity)
  infDist_polyPartial_le_sobolevPar_of_near S J hq0 (min_le_left _ _)
    (fun _ hx => norm_formL2_truncField_sub_glue_le S hs hq0 (min_le_right _ _)
      (min_le_left _ _) hx N) y hy

/-! ### Sobolev data in every degree, graph norms -/

variable (n) in
/-- The constant `sobConstHigh` in degree `j ∈ ℤ` (`0` in negative degrees). -/
def sobConstHighZ (S : PolySeq) (p : ℕ) : ℤ → ℝ
  | Int.ofNat k => sobConstHigh n S k p
  | Int.negSucc _ => 0

theorem sobConstHighZ_nonneg (S : PolySeq) (p : ℕ) (j : ℤ) : 0 ≤ sobConstHighZ n S p j := by
  rcases j with k | k
  · exact sobConstHigh_nonneg S k p
  · exact le_rfl

/-- **Best approximation in every degree** for `Hˢ(Q)` data at the optimal rate, for a sequence
reproducing `P_p` in the degree `j`. -/
theorem infDist_poly_le_sobAt_high [NeZero n] (S : PolySeq) {p : ℕ}
    {s L : ℝ} (hs0 : 0 ≤ s) (N : ℕ) {j : ℤ}
    (hS : ∀ k : ℕ, (k : ℤ) = j → polySpace n p k ≤ S.space n k)
    {y : L2F ℝ (cubeDomain n) (formIdx n j)} (hy : SobAt n s L j y) :
    Metric.infDist y ((poly n S N).V j) ≤
      sobConstHighZ n S p j * meshSize N ^ min s (p + 1) * L := by
  rcases j with k | k
  · obtain ⟨h1, h2⟩ := hy
    refine (infDist_poly_le_sobolevQ_high S k p (hS k rfl) hs0 N y h1).trans ?_
    exact mul_le_mul_of_nonneg_left h2
      (mul_nonneg (sobConstHigh_nonneg S k p) (Real.rpow_nonneg (meshSize_pos N).le _))
  · have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    rw [Subsingleton.elim y 0, Metric.infDist_zero_of_mem (Submodule.zero_mem _)]
    simp [sobConstHighZ]

/-! ### The mixed Hodge Laplacian with `Hˢ(Q)` solutions, optimal rate -/

variable (n) in
/-- **The Jackson estimate of the complexes of `S` for `Hˢ(Q)` data at the optimal rate**, for a
sequence reproducing `P_p` in the degrees of the form and of its differential, in every dimension:
`Hˢ(Q)` components (`SobComp`), `s ≥ 0`, at the order `h_N^{min(s, p + 1)}`, from the best
approximation `infDist_poly_le_sobAt_high` through the projections
(`ConformingFamily.Jackson.ofInfDist`). -/
def sobolevHighJackson [NeZero n] (S : PolySeq) (p : ℕ) :
    (polyFamily n S).Jackson (Set.Ici (0 : ℝ)) :=
  .ofInfDist _ meshSize (fun N => (meshSize_pos N).le) tendsto_meshSize
    (fun s l L x => (∀ d : ℕ, (d : ℤ) = l ∨ (d : ℤ) = l + 1 → polySpace n p d ≤ S.space n d) ∧
      SobComp n s L x) (fun s => min (s : ℝ) (p + 1))
    (fun _ j => sobConstHighZ n S p j + sobConstHighZ n S p (j + 1))
    (fun _ _ => add_nonneg (sobConstHighZ_nonneg S p _) (sobConstHighZ_nonneg S p _))
    fun s N i L x hL hx => by
      have h0 := sobConstHighZ_nonneg (n := n) S p i
      have h1 := sobConstHighZ_nonneg (n := n) S p (i + 1)
      have hh := mul_nonneg hL (Real.rpow_nonneg (meshSize_pos N).le (min (s : ℝ) (p + 1)))
      refine ⟨(infDist_poly_le_sobAt_high S s.2 N (fun d hd => hx.1 d (.inl hd))
        hx.2.1).trans (by nlinarith), fun j hij hxj => ?_⟩
      obtain rfl : i + 1 = j := hij
      exact (infDist_poly_le_sobAt_high S s.2 N (fun d hd => hx.1 d (.inr hd))
        (hx.2.2 hxj)).trans (by nlinarith)

/-- **Convergence of the mixed method at the optimal rate `h^{min(s, r_eff)}` for `Hˢ(Q)`
solutions** (`mixed_rate_sobolevQ_high`; [AFW2010], Thm 3.9, with
`infDist_poly_le_sobolevQ_high`; [Arnold2018], Ch. 7): for every admissible sequence `S` that
reproduces `P_p` in the degrees `i, i + 1 = j, j + 1` (`r_eff = p + 1`, every dimension) and every
real `s ≥ 0`, if `σ, dσ, u, du, P_𝔅 u, d P_𝔅 u` and the harmonic part `q` lie in `Hˢ(Q)` with
norms `≤ L`, the error is `≤ K L h_N^{min(s, r_eff)}`, `K` independent of `N`, `s` and the
solution. -/
theorem mixed_rate_sobolevQ_high [NeZero n] (S : PolySeq) {p : ℕ}
    {s : ℝ} (hs0 : 0 ≤ s) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k)
    (hS : ∀ d : ℕ, i ≤ d → (d : ℤ) ≤ i + 2 → polySpace n p d ≤ S.space n d) :
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
      K * L * meshSize N ^ min s (p + 1) := by
  obtain ⟨K, hK⟩ := ((polyFamily n S).staticFEEC closedRangeAt j).rate
    (sobolevHighJackson n S p) ⟨s, hs0⟩ hij hjk
  have hij' : i + 1 = j := hij
  have hi (d : ℕ) (hd : (d : ℤ) = i ∨ (d : ℤ) = i + 1) := hS d (by omega) (by omega)
  have hj (d : ℕ) (hd : (d : ℤ) = j ∨ (d : ℤ) = j + 1) := hS d (by omega) (by omega)
  refine ⟨K, fun {f σ u q} hs _ hL hσ hu hb hq N => ?_⟩
  have h := hK hs hL ⟨hi, hσ.sobComp⟩ ⟨hj, hu.sobComp⟩ ⟨hj, hb.sobComp⟩
    ⟨hj, hq.sobComp_of_mem_cycles hL ((complex n).harmonic_le_cycles j q.2)⟩ N
  simp only [polyFamily_V] at h
  exact h

/-! ### The semi-discrete Hodge wave equation, optimal rate -/

/-- **Graph-norm approximation in the total space of a window at the optimal rate**, for
`Hˢ(Q)` components and a sequence reproducing `P_p` in the degrees of the window. -/
theorem PolySmoothingEstimates.exists_mem_window_le_sob_high [NeZero n] {S : PolySeq}
    {p' : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimates n S p' C)
    {p : ℕ} {s L : ℝ} (hs0 : 0 ≤ s) (hL0 : 0 ≤ L) {a : ℤ} {m : ℕ}
    (hS : ∀ k : ℕ, a ≤ k → (k : ℤ) ≤ a + m → polySpace n p k ≤ S.space n k)
    (ζ : ((complex n).window a m).totalD.GraphSpace)
    (hζ : ∀ i : Fin m, SobComp n s L (((complex n).window a m).totalD.graphFst ζ i)) (N : ℕ) :
    ∃ w ∈ ((poly n S N).window a m).graphSub, ‖ζ - w‖ ≤
      ((m : ℝ) + m * m) * ((1 + 2 * C) * (∑ i : Fin m, (sobConstHighZ n S p (a + i) +
        sobConstHighZ n S p (a + i + 1))) * meshSize N ^ min s (p + 1) * L) := by
  obtain ⟨x, rfl, -, -⟩ := ((complex n).window a m).totalD.exists_toGraphSpace_eq ζ
  simp only [LinearPMap.graphFst_toGraphSpace] at hζ
  have hC := hE.two_mul_nonneg
  set e := meshSize N ^ min s (p + 1)
  have hh : 0 ≤ e := Real.rpow_nonneg (meshSize_pos N).le _
  set K := ∑ i : Fin m, (sobConstHighZ n S p (a + i) + sobConstHighZ n S p (a + i + 1))
  have hKi : ∀ i : Fin m, sobConstHighZ n S p (a + i) + sobConstHighZ n S p (a + i + 1) ≤ K :=
    fun i => Finset.single_le_sum
      (f := fun i : Fin m => sobConstHighZ n S p (a + i) + sobConstHighZ n S p (a + i + 1))
      (fun i _ => add_nonneg (sobConstHighZ_nonneg S p _) (sobConstHighZ_nonneg S p _))
      (Finset.mem_univ i)
  have hε : 0 ≤ (1 + 2 * C) * K * e * L := by
    have : 0 ≤ K := Finset.sum_nonneg fun i _ =>
      add_nonneg (sobConstHighZ_nonneg S p _) (sobConstHighZ_nonneg S p _)
    have : 0 ≤ 1 + 2 * C := by linarith
    positivity
  obtain ⟨w, hw, hlt⟩ := Subcomplex.exists_mem_graphSub_le ((poly n S N).window a m) x
    (ε := (1 + 2 * C) * K * e * L) fun i => by
      set xi := (x : PiLp 2 fun i : Fin m => L2F ℝ (cubeDomain n) (formIdx n (a + i))) i
      have hO : ∀ k : ℕ, (k : ℤ) = a + i → polySpace n p k ≤ S.space n k :=
        fun k hk => hS k (by omega) (by have := i.2; omega)
      have hO1 : ∀ k : ℕ, (k : ℤ) = a + i + 1 → polySpace n p k ≤ S.space n k :=
        fun k hk => hS k (by omega) (by have := i.2; omega)
      have h0 := infDist_poly_le_sobAt_high S hs0 N hO (hζ i).1
      have hA : (1 + 2 * C) * Metric.infDist xi ((poly n S N).V (a + i)) ≤
          (1 + 2 * C) * K * e * L := by
        have hs := sobConstHighZ_nonneg (n := n) S p (a + i + 1)
        calc (1 + 2 * C) * Metric.infDist xi ((poly n S N).V (a + i)) ≤
            (1 + 2 * C) * (sobConstHighZ n S p (a + i) * e * L) :=
              mul_le_mul_of_nonneg_left h0 (by linarith)
          _ ≤ (1 + 2 * C) * K * e * L := by
              rw [mul_assoc (1 + 2 * C) K, mul_assoc (1 + 2 * C) (K * _)]
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              rw [mul_assoc, mul_assoc]
              exact mul_le_mul_of_nonneg_right (by linarith [hKi i]) (mul_nonneg hh hL0)
      have hB : ∀ hx : xi ∈ ((complex n).d (a + i) (a + i + 1)).domain,
          (1 + 2 * C) * Metric.infDist ((complex n).d (a + i) (a + i + 1) ⟨xi, hx⟩)
            ((poly n S N).V (a + i + 1)) ≤ (1 + 2 * C) * K * e * L := by
        intro hx
        have h1 := infDist_poly_le_sobAt_high S hs0 N hO1 ((hζ i).2 hx)
        have hs := sobConstHighZ_nonneg (n := n) S p (a + i)
        calc (1 + 2 * C) * Metric.infDist ((complex n).d (a + i) (a + i + 1) ⟨xi, hx⟩)
              ((poly n S N).V (a + i + 1)) ≤
            (1 + 2 * C) * (sobConstHighZ n S p (a + i + 1) * e * L) :=
              mul_le_mul_of_nonneg_left h1 (by linarith)
          _ ≤ (1 + 2 * C) * K * e * L := by
              rw [mul_assoc (1 + 2 * C) K, mul_assoc (1 + 2 * C) (K * _)]
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              rw [mul_assoc, mul_assoc]
              exact mul_le_mul_of_nonneg_right (by linarith [hKi i]) (mul_nonneg hh hL0)
      obtain ⟨v, hv, h1, h2⟩ := exists_mem_le_proj (hE.proj N) hC (hE.norm_proj_le N)
        (j := a + i) xi hA hB hε
      exact ⟨v, hv, h1, fun j hx => h2 (a + j) hx⟩
  refine ⟨w, hw, hlt.trans (le_of_eq ?_)⟩
  rw [Fintype.card_fin]

/-- **Convergence of the semi-discrete Hodge wave equation at the optimal rate
`h^{min(s, r_eff)}`** (`norm_sub_le_window_sobolevQ_high`; [QuennevilleBelair2015], Thm 4.14,
with `infDist_poly_le_sobolevQ_high`), on every window of `HΛ(Q)`, for solutions bounded in
`Hˢ(Q)` uniformly on `[t₀, t₁]` and a sequence reproducing `P_p` in the degrees of the window. -/
theorem PolySmoothingEstimates.norm_sub_le_window_sobolevQ_high [NeZero n] {S : PolySeq}
    {p' : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : PolySmoothingEstimates n S p' C)
    {p : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (a : ℤ) (m : ℕ)
    (hS : ∀ k : ℕ, a ≤ k → (k : ℤ) ≤ a + m → polySpace n p k ≤ S.space n k) {t₀ t₁ : ℝ}
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
          (sobConstHighZ n S p (a + i) + sobConstHighZ n S p (a + i + 1))) *
            meshSize N ^ min s (p + 1) * L)) :=
  ((poly n S N).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (fun τ hτ =>
    ⟨hE.exists_mem_window_le_sob_high hs0 hL0 hS (ξ τ) (fun i => (hreg τ hτ i).1) N,
      hE.exists_mem_window_le_sob_high hs0 hL0 hS (ξ' τ) (fun i => (hreg τ hτ i).2) N⟩) ht

/-! ### The parity classes: `HΛ_J(Q)` with `Hˢ_J(Q)` data, optimal rate -/

section Parity

variable (J : Finset (Fin n))

variable (n) in
/-- The constant `2^{n/2} sobConstHigh` in degree `j ∈ ℤ` (`0` in negative degrees). -/
def sobConstHighParZ (S : PolySeq) (p : ℕ) : ℤ → ℝ
  | Int.ofNat k => √(2 ^ n) * sobConstHigh n S k p
  | Int.negSucc _ => 0

theorem sobConstHighParZ_nonneg (S : PolySeq) (p : ℕ) (j : ℤ) :
    0 ≤ sobConstHighParZ n S p j := by
  rcases j with k | k
  · exact mul_nonneg (Real.sqrt_nonneg _) (sobConstHigh_nonneg S k p)
  · exact le_rfl

/-- **Best approximation in every degree** for `Hˢ_J(Q)` data at the optimal rate. -/
theorem infDist_polyPartial_le_sobAtPar_high [NeZero n] (S : PolySeq) {p : ℕ}
    {s L : ℝ} (hs0 : 0 ≤ s) (N : ℕ) {j : ℤ}
    (hS : ∀ k : ℕ, (k : ℤ) = j → polySpace n p k ≤ S.space n k)
    {y : L2F ℝ (cubeDomain n) (formIdx n j)} (hy : SobAtPar n J s L j y) :
    Metric.infDist y ((polyPartial n S N J).V j) ≤
      sobConstHighParZ n S p j * meshSize N ^ min s (p + 1) * L := by
  rcases j with k | k
  · obtain ⟨h1, h2⟩ := hy
    refine (infDist_polyPartial_le_sobolevPar_high S J k p (hS k rfl) hs0 N y h1).trans ?_
    exact mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (sobConstHigh_nonneg S k p)) (Real.rpow_nonneg (meshSize_pos N).le _))
  · have := LocalElement.subsingleton_L2F_negSucc (cubeDomain n) (n := n) k
    rw [Subsingleton.elim y 0, Metric.infDist_zero_of_mem (Submodule.zero_mem _)]
    simp [sobConstHighParZ]

variable {J} in
/-- **Graph-norm best approximation in `HΛ_J(Q)` at the optimal rate**
(`infDist_domainSub_le_sobGraphPar_high`) through the parity-smoothed projections. -/
theorem ParitySmoothingEstimates.infDist_domainSub_le_sobGraphPar_high [NeZero n] {S : PolySeq}
    {ρ : ℕ → ParitySmoother.ReflKernel n} {C : ℝ} (hE : ParitySmoothingEstimates n J S ρ C)
    {p : ℕ} {s L : ℝ} (hs0 : 0 ≤ s) (N : ℕ) {j : ℤ}
    (hS0 : ∀ k : ℕ, (k : ℤ) = j → polySpace n p k ≤ S.space n k)
    (hS1 : ∀ k : ℕ, (k : ℤ) = j + 1 → polySpace n p k ≤ S.space n k)
    {σ : (complexPart n J).domainSpace j} (hσ : SobGraphPar n J s L σ) :
    Metric.infDist σ ((polyPartial n S N J).domainSub j) ≤
      (1 + 2 * C) * (sobConstHighParZ n S p j + sobConstHighParZ n S p (j + 1)) *
        meshSize N ^ min s (p + 1) * L := by
  refine (infDist_domainSub_le_proj (hE.proj N) hE.two_mul_nonneg (hE.norm_proj_le N) j σ).trans ?_
  have h1 := infDist_polyPartial_le_sobAtPar_high J S hs0 N hS0 hσ.1
  have h2 := infDist_polyPartial_le_sobAtPar_high J S hs0 N hS1 hσ.2
  have := hE.two_mul_nonneg
  calc (1 + 2 * C) * (Metric.infDist ((complexPart n J).domainIncl j σ)
        ((polyPartial n S N J).V j) +
        Metric.infDist ((complexPart n J).d j (j + 1) ((complexPart n J).domainCoord j (j + 1) σ))
          ((polyPartial n S N J).V (j + 1))) ≤
      (1 + 2 * C) * (sobConstHighParZ n S p j * meshSize N ^ min s (p + 1) * L +
        sobConstHighParZ n S p (j + 1) * meshSize N ^ min s (p + 1) * L) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by linarith)
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- **Convergence of the mixed method in `HΛ_J(Q)` at the optimal rate for `Hˢ_J(Q)` solutions**
(`mixed_rate_sobolevPar_high`), for every class `J` and every admissible sequence reproducing
`P_p` in the degrees `i, i + 1, i + 2` (every dimension, every real `s ≥ 0`): error
`≤ K L h_N^{min(s, p+1)}` ([AFW2010], Thm 3.9, with the parity smoother and the Poincaré
inequality of `HΛ_J(Q)`). -/
theorem mixed_rate_sobolevPar_high [NeZero n] (S : PolySeq) {p : ℕ}
    {s : ℝ} (hs0 : 0 ≤ s) {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k)
    (hS : ∀ d : ℕ, i ≤ d → (d : ℤ) ≤ i + 2 → polySpace n p d ≤ S.space n d) :
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
      K * L * meshSize N ^ min s (p + 1) := by
  obtain ⟨ρ, C, hE⟩ := paritySmoothing_exists J S
  obtain rfl : j + 1 = k := hjk
  have hij' : i + 1 = j := hij
  have hC := hE.two_mul_nonneg
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = sobConstHighParZ n S p i + sobConstHighParZ n S p (i + 1) +
      sobConstHighParZ n S p j + sobConstHighParZ n S p (j + 1) := ⟨_, rfl⟩
  have hi := sobConstHighParZ_nonneg (n := n) S p i
  have hi1 := sobConstHighParZ_nonneg (n := n) S p (i + 1)
  have hj := sobConstHighParZ_nonneg (n := n) S p j
  have hj1 := sobConstHighParZ_nonneg (n := n) S p (j + 1)
  have hSσ0 : ∀ d : ℕ, (d : ℤ) = i → polySpace n p d ≤ S.space n d :=
    fun d hd => hS d (by omega) (by omega)
  have hSσ1 : ∀ d : ℕ, (d : ℤ) = i + 1 → polySpace n p d ≤ S.space n d :=
    fun d hd => hS d (by omega) (by omega)
  have hSu0 : ∀ d : ℕ, (d : ℤ) = j → polySpace n p d ≤ S.space n d :=
    fun d hd => hS d (by omega) (by omega)
  have hSu1 : ∀ d : ℕ, (d : ℤ) = j + 1 → polySpace n p d ≤ S.space n d :=
    fun d hd => hS d (by omega) (by omega)
  refine ⟨(1 + 144 * (2 * C * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 2 * C) *
    (4 + 2 * (2 * C)) * ((1 + 2 * C) * A), fun {f σ u q} hs {L} hL0 hσ hu hBu hq N => ?_⟩
  have hδ : 0 ≤ meshSize N ^ min s (p + 1) * L :=
    mul_nonneg (Real.rpow_nonneg (meshSize_pos N).le _) hL0
  have hle : ∀ a b : ℝ, a + b ≤ A →
      (1 + 2 * C) * (a + b) * meshSize N ^ min s (p + 1) * L ≤
        (1 + 2 * C) * A * (meshSize N ^ min s (p + 1) * L) :=
    fun a b hab => by
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab
        (by linarith : (0 : ℝ) ≤ 1 + 2 * C)) hδ]
  have hg : SobGraphPar n J s L (HilbertComplex.cyclesToDomainSpace
      ((complexPart n J).harmonic_le_cycles j q.2)) :=
    ⟨by rw [HilbertComplex.domainIncl_cyclesToDomainSpace]; exact hq,
      by rw [HilbertComplex.d_domainCoord_cyclesToDomainSpace]; exact sobAtPar_zero J hL0 _⟩
  have h1 := (hE.infDist_domainSub_le_sobGraphPar_high hs0 N hSσ0 hSσ1 hσ).trans
    (hle _ _ (by linarith))
  have h2 := (hE.infDist_domainSub_le_sobGraphPar_high hs0 N hSu0 hSu1 hu).trans
    (hle _ _ (by linarith))
  have h3 := (hE.infDist_domainSub_le_sobGraphPar_high hs0 N hSu0 hSu1 hg).trans
    (hle _ _ (by linarith))
  have h4 := (hE.infDist_domainSub_le_sobGraphPar_high hs0 N hSu0 hSu1 hBu).trans
    (hle _ _ (by linarith))
  refine (norm_sub_discreteMixedSolution_le (hE.proj N) hij rfl (by linarith [hE.half_le])
    (norm_le_of_mem_orthogonal_cycles_part J hij) (norm_le_of_mem_orthogonal_cycles_part J rfl)
    ((hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j))
    ((hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N j) (hE.norm_proj_le N (j + 1)))
      hs h1 h2 h3 h4).trans
    (le_of_eq (by ring))

end Parity

/-! ### Degreewise orders, the bottom row of Tables 5.1/6.1 -/

/-- The degrees `i, i + 1, i + 2` of a mixed problem from the degreewise orders at `i` and
`j = i + 1 ≥ 0`. -/
theorem degrees_of_polyOrderAt {S : PolySeq} {p : ℕ} {i j : ℤ} (hij : i + 1 = j) (hj : 0 ≤ j)
    (hSi : PolyOrderAt n S p i) (hSj : PolyOrderAt n S p j) :
    ∀ d : ℕ, i ≤ d → (d : ℤ) ≤ i + 2 → polySpace n p d ≤ S.space n d := by
  intro d h1 h2
  rcases (show (d : ℤ) = i ∨ (d : ℤ) = j ∨ (d : ℤ) = j + 1 by omega) with h | h | h
  · exact (hSi d h).1
  · exact (hSj d h).1
  · obtain ⟨j', hj'⟩ : ∃ j' : ℕ, (j' : ℤ) = j := ⟨j.toNat, by omega⟩
    obtain rfl : d = j' + 1 := by omega
    exact (hSj j' hj').2

/-- **`mixed_rate_sobolevQ_high` for the degreewise orders** (`_of_polyOrderAt`): a sequence
reproducing `P_p` in the degrees `i, j, j + 1` (`PolyOrderAt` at `i` and `j = i + 1 ≥ 0`). -/
theorem mixed_rate_sobolevQ_high_of_polyOrderAt [NeZero n] (S : PolySeq) {p : ℕ}
    {s : ℝ} (hs0 : 0 ≤ s) {i j k : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) (hj : 0 ≤ j)
    (hSi : PolyOrderAt n S p i) (hSj : PolyOrderAt n S p j) :
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
      K * L * meshSize N ^ min s (p + 1) :=
  mixed_rate_sobolevQ_high S hs0 hij hjk (degrees_of_polyOrderAt hij hj hSi hSj)

/-- **The bottom row `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³` on `1`-forms at the rate `h^{min(s,2)}` for
`Hˢ(Q)` solutions** (`mixed_rate_lagrangeP2_sobolevQ`, every dimension): the Hodge Laplacian in
degree `1` uses only `P₂Λ⁰, P₂⁻Λ¹, P₁Λ²`, which contain `P₁` (`r_eff = 2`), although
`P₀Λ³` limits the global order to `h`; [AFW2010], Thm 3.9. -/
theorem mixed_rate_lagrangeP2_sobolevQ [NeZero n] {s : ℝ} (hs0 : 0 ≤ s) :
    ∃ K : ℝ, ∀ {f : L2F ℝ (cubeDomain n) (formIdx n 1)} {σ : (complex n).domainSpace 0}
    {u : (complex n).domainSpace 1} {q : (complex n).harmonic 1},
    (complex n).IsMixedSolution 0 1 2 f σ u q → ∀ {L : ℝ}, 0 ≤ L →
    SobGraph n s L σ → SobGraph n s L u →
    SobGraph n s L ((complex n).boundaryPart 1 ((complex n).domainIncl 1 u)) →
    SobAt n s L 1 (q : L2F ℝ (cubeDomain n) (formIdx n 1)) → ∀ N : ℕ,
    ‖σ - (poly n PolySeq.lagrangeP2 N).embD 0
          (Subcomplex.CochainProjection.discreteMixedSolution
            (poly n PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl f).fst‖ +
        ‖u - (poly n PolySeq.lagrangeP2 N).embD 1
          (Subcomplex.CochainProjection.discreteMixedSolution
            (poly n PolySeq.lagrangeP2 N) (i := 0) (j := 1) (k := 2) rfl rfl f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n 1)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (poly n PolySeq.lagrangeP2 N)
            (i := 0) (j := 1) (k := 2) rfl rfl f).snd.snd :
            (poly n PolySeq.lagrangeP2 N).V 1) : L2F ℝ (cubeDomain n) (formIdx n 1))‖ ≤
      K * L * meshSize N ^ min s 2 := by
  have h := mixed_rate_sobolevQ_high_of_polyOrderAt (n := n) PolySeq.lagrangeP2 (p := 1) hs0
    (i := 0) (j := 1) (k := 2) rfl rfl (by norm_num)
    lagrangeP2_polyOrderAt_zero lagrangeP2_polyOrderAt_one
  rw [show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num] at h
  exact h

/-! ### Windows with no smoothing hypothesis -/

/-- **Convergence of the semi-discrete Hodge wave equation at the optimal rate, unconditionally**
(`exists_norm_sub_le_window_sobolevQ_high`):
`PolySmoothingEstimates.norm_sub_le_window_sobolevQ_high`
with the smoothing estimates supplied by `polySmoothingEstimates_exists`; the constant `K` depends
only on `S`, `p` and the window. -/
theorem exists_norm_sub_le_window_sobolevQ_high [NeZero n] (S : PolySeq) {p : ℕ}
    {s : ℝ} (hs0 : 0 ≤ s) (a : ℤ) (m : ℕ)
    (hS : ∀ k : ℕ, a ≤ k → (k : ℤ) ≤ a + m → polySpace n p k ≤ S.space n k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t₀ t₁ : ℝ} {ξ ξ' : ℝ → ((complex n).window a m).totalD.GraphSpace},
      HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ' →
      ∀ {ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace},
      (∀ N, HodgeWave.IsSemidiscreteSolution (((poly n S N).window a m).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) →
      (∀ N, ξh N t₀ =
        HodgeWave.ellipticProjection (((poly n S N).window a m).graphSub) (ξ t₀)) →
      ∀ {L : ℝ}, 0 ≤ L →
      (∀ τ ∈ Set.Icc t₀ t₁, ∀ i : Fin m,
        SobComp n s L (((complex n).window a m).totalD.graphFst (ξ τ) i) ∧
          SobComp n s L (((complex n).window a m).totalD.graphFst (ξ' τ) i)) →
      ∀ (N : ℕ) {t : ℝ}, t ∈ Set.Icc t₀ t₁ →
      ‖((complex n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
        (1 + ‖HodgeWave.shiftedForm ((complex n).window a m).totalD‖ / ((1 / 2) / √3)) *
          (1 + (t - t₀)) ^ 2 * (K * meshSize N ^ min s (p + 1) * L) := by
  obtain ⟨p', C, hE⟩ := polySmoothingEstimates_exists (n := n) S
  have hC := hE.two_mul_nonneg
  have hK : 0 ≤ ∑ i : Fin m, (sobConstHighZ n S p (a + i) + sobConstHighZ n S p (a + i + 1)) :=
    Finset.sum_nonneg fun i _ =>
      add_nonneg (sobConstHighZ_nonneg S p _) (sobConstHighZ_nonneg S p _)
  refine ⟨((m : ℝ) + m * m) * ((1 + 2 * C) * ∑ i : Fin m,
    (sobConstHighZ n S p (a + i) + sobConstHighZ n S p (a + i + 1))),
    mul_nonneg (by positivity) (mul_nonneg (by linarith) hK),
    fun {t₀ t₁ ξ ξ'} hξ {ξh ξh'} hξh h0 {L} hL0 hreg N {t} ht => ?_⟩
  refine (hE.norm_sub_le_window_sobolevQ_high hs0 a m hS hξ hξh h0 hL0 hreg N ht).trans
    (le_of_eq ?_)
  ring

end Feec.Models.Cube.FEM
