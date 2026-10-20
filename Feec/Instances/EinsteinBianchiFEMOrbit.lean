module

public import Feec.HilbertComplex.Approximation.ApproxFEEC

/-!
# Orbit cores of approximating FEEC discretizations with orthogonal reading maps

For an approximating FEEC discretization (`Feec.HilbertComplex.ApproxFEEC`) whose
reading maps `ιₕ` are isometric with `πₕ = ιₕ*` (`IsOrthogonal`), `ιₕ πₕ` is the orthogonal
projection onto the range of `ιₕ`, so `ιₕ πₕ y` is the best approximation of `y`
(`norm_sub_incl_proj_le`). Consequently, if for a datum `x` some discrete initial values `vₕ` give
solutions `ιₕ e^{tLₕ} vₕ` within `ε` of `e^{tL} x` on `[0, T]` (a model convergence theorem, e.g.
from an elliptic projection), then so does `vₕ = πₕ x`, within `3ε`
(`norm_sub_sol_proj_le`).

This gives an **orbit core** (`orbitCore`): the comparison trajectory of `x` is the discrete orbit
`e^{tLₕ} πₕ x` itself (consistency defect `0`, `orbitComparison_defect`), and the approximation
hypothesis of the core is the model convergence theorem. Likewise a model rate
`‖e^{tL} x - ιₕ e^{tLₕ} vₕ‖ ≤ c hᵅ ‖x‖_c` on `[0, T]` gives a rate class with constants
`C = 3c`, `C' = 0` (`orbitRate`).

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (best approximation in the image of the reading map)
-/

open scoped InnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi.FEM

open Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*}

namespace ApproxFEEC

variable (F : ApproxFEEC H κ)

/-- **Orthogonal reading maps**: `ιₕ` is isometric and `πₕ = ιₕ*`. -/
structure IsOrthogonal : Prop where
  inner_incl : ∀ h (a b : F.X h), ⟪F.incl h a, F.incl h b⟫_𝕜 = ⟪a, b⟫_𝕜
  inner_incl_left : ∀ h (a : F.X h) (y : PiLp 2 W), ⟪F.incl h a, y⟫_𝕜 = ⟪a, F.proj h y⟫_𝕜

variable {F}

theorem IsOrthogonal.norm_incl (hF : IsOrthogonal F) (h : κ) (a : F.X h) :
    ‖F.incl h a‖ = ‖a‖ := by
  have e := congrArg RCLike.re (hF.inner_incl h a a)
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at e
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e

/-- Orthogonal reading maps have norm at most `1`. -/
theorem IsOrthogonal.norm_incl_le_one (hF : IsOrthogonal F) (h : κ) : ‖F.incl h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by rw [hF.norm_incl, one_mul]

/-- `y - ιₕ πₕ y ⊥ ιₕ Xₕ`. -/
theorem IsOrthogonal.inner_sub_incl_proj (hF : IsOrthogonal F) (h : κ) (y : PiLp 2 W)
    (a : F.X h) : ⟪y - F.incl h (F.proj h y), F.incl h a⟫_𝕜 = 0 := by
  rw [inner_sub_left, hF.inner_incl, ← inner_conj_symm, hF.inner_incl_left, inner_conj_symm,
    sub_self]

/-- **Best approximation**: `‖y - ιₕ πₕ y‖ ≤ ‖y - ιₕ w‖` for every discrete `w`. -/
theorem IsOrthogonal.norm_sub_incl_proj_le (hF : IsOrthogonal F) (h : κ) (y : PiLp 2 W)
    (w : F.X h) : ‖y - F.incl h (F.proj h y)‖ ≤ ‖y - F.incl h w‖ := by
  have e : y - F.incl h w = (y - F.incl h (F.proj h y)) + F.incl h (F.proj h y - w) := by
    rw [map_sub]; abel
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    (hF.inner_sub_incl_proj h y (F.proj h y - w))
  rw [← e] at hp
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  nlinarith [mul_self_nonneg ‖F.incl h (F.proj h y - w)‖]

/-! ### The orbit comparison -/

variable (F) in
/-- The discrete orbit is differentiable, `(d/dt) e^{tLₕ} v = Lₕ e^{tLₕ} v`. -/
theorem hasDerivAt_group (h : κ) (v : F.X h) (t : ℝ) :
    HasDerivAt (fun s => (F.group h).S s v) (F.L h ((F.group h).S t v)) t :=
  C0Group.hasDerivAt_exp_ofReal_smul_apply (F.L h) v t

variable (F) in
/-- **The orbit comparison**: the discrete orbit `e^{tLₕ} πₕ x` itself, with derivative
`Lₕ e^{tLₕ} πₕ x`. -/
def orbitComparison (T : ℝ) : F.Comparison T where
  Data := univ
  p x h t := (F.group h).S t (F.proj h x)
  p' x h t := F.L h ((F.group h).S t (F.proj h x))
  continuousOn _ _ h := ((F.group h).strongCont _).continuousOn
  continuousOn' _ _ h := ((F.L h).continuous.comp ((F.group h).strongCont _)).continuousOn
  hasDerivWithinAt x _ h t _ := (hasDerivAt_group F h (F.proj h x) t).hasDerivWithinAt

variable (F) in
/-- The orbit comparison has consistency defect `0`. -/
theorem orbitComparison_defect (T : ℝ) (x : PiLp 2 W) (h : κ) (t : ℝ) :
    (orbitComparison F T).defect x h t = 0 :=
  sub_self (F.L h ((F.group h).S t (F.proj h x)))

variable (F) in
theorem incl_orbitComparison_p (T : ℝ) (x : PiLp 2 W) (h : κ) (t : ℝ) :
    F.incl h ((orbitComparison F T).p x h t) = F.sol h (F.proj h x) t := rfl

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **Initial values by orthogonal projection**: the discrete solution from `πₕ x` is within
`‖e^{tL} x - ιₕ e^{tLₕ} v‖ + 2 ‖x - ιₕ v‖` of `e^{tL} x`, for every discrete `v`. -/
theorem IsOrthogonal.norm_sub_sol_proj_le (hF : IsOrthogonal F) (h : κ) (x : PiLp 2 W)
    (v : F.X h) (t : ℝ) :
    ‖H.waveGroup.S t x - F.sol h (F.proj h x) t‖ ≤
      ‖H.waveGroup.S t x - F.sol h v t‖ + 2 * ‖x - F.incl h v‖ := by
  have h1 : ‖F.sol h v t - F.sol h (F.proj h x) t‖ = ‖F.proj h x - v‖ := by
    rw [ApproxFEEC.sol, ApproxFEEC.sol, ← map_sub, ← map_sub, hF.norm_incl,
      ApproxFEEC.norm_group_apply, norm_sub_rev]
  have h2 : ‖F.proj h x - v‖ ≤ 2 * ‖x - F.incl h v‖ := by
    rw [← hF.norm_incl h, map_sub]
    have e : F.incl h (F.proj h x) - F.incl h v =
        -(x - F.incl h (F.proj h x)) + (x - F.incl h v) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    linarith [hF.norm_sub_incl_proj_le h x v]
  have e : H.waveGroup.S t x - F.sol h (F.proj h x) t =
      (H.waveGroup.S t x - F.sol h v t) + (F.sol h v t - F.sol h (F.proj h x) t) := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [h1]
  linarith

/-- **The orbit core** of a model convergence theorem: if for every datum `x` of `Data`, every
`T > 0` and `ε > 0`, for `h` eventually some discrete initial value gives a solution within `ε`
of `e^{tL} x` on `[0, T]`, then `Data` with the orbit comparison is a core (zero defect). -/
def orbitCore (hF : IsOrthogonal F) (Data : Submodule 𝕜 (PiLp 2 W))
    (hconv : ∀ x ∈ Data, ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε → ∀ᶠ h in F.l, ∃ v : F.X h,
      ∀ t ∈ Icc 0 T, ‖H.waveGroup.S t x - F.sol h v t‖ ≤ ε) : F.Core where
  Data := Data
  cmp T := (orbitComparison F T).restrict Data (subset_univ _)
  data_eq _ := rfl
  tendsto_approx T x hx := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hconv x hx (max T 1) (lt_max_of_lt_right one_pos) (ε / 4) (by positivity)]
      with h ⟨v, hv⟩ t ht
    have ht' : t ∈ Icc 0 (max T 1) := ⟨ht.1, ht.2.trans (le_max_left _ _)⟩
    have h0 : (0 : ℝ) ∈ Icc 0 (max T 1) := ⟨le_rfl, le_max_of_le_right zero_le_one⟩
    have hv0 := hv 0 h0
    rw [C0Group.S_zero_apply, ApproxFEEC.sol_zero] at hv0
    rw [dist_eq_norm]
    change ‖H.waveGroup.S t x - F.sol h (F.proj h x) t‖ < ε
    have := hF.norm_sub_sol_proj_le h x v t
    linarith [hv t ht']
  tendsto_defect T x _ := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    refine Eventually.of_forall fun h t _ => ?_
    change dist 0 ‖(orbitComparison F T).defect x h t‖ < ε
    rw [orbitComparison_defect, norm_zero, dist_self]
    exact hε

theorem orbitCore_data (hF : IsOrthogonal F) (Data : Submodule 𝕜 (PiLp 2 W)) hconv :
    (orbitCore hF Data hconv).Data = Data := rfl

theorem orbitCore_p (hF : IsOrthogonal F) (Data : Submodule 𝕜 (PiLp 2 W)) hconv (T : ℝ)
    (x : PiLp 2 W) (h : κ) (t : ℝ) :
    ((orbitCore hF Data hconv).cmp T).p x h t = (F.group h).S t (F.proj h x) := rfl

/-- **The orbit rate class** of a model rate: if for every datum `x` of `S` and every `h` some
discrete initial value gives `‖e^{tL} x - ιₕ e^{tLₕ} v‖ ≤ c hᵅ ‖x‖_c` on `[0, T]`, the orbit
comparison is a rate class on `S` with `C = 3c` and `C' = 0`. -/
def orbitRate (hF : IsOrthogonal F) {T : ℝ} (S : Set (PiLp 2 W)) (classNorm : PiLp 2 W → ℝ)
    (meshSize : κ → ℝ) (α cst : ℝ)
    (hrate : ∀ x ∈ S, ∀ h, ∃ v : F.X h, ∀ t ∈ Icc 0 T,
      ‖H.waveGroup.S t x - F.sol h v t‖ ≤ cst * meshSize h ^ α * classNorm x) :
    F.RateClass T where
  toComparison := (orbitComparison F T).restrict S (subset_univ _)
  classNorm := classNorm
  meshSize := meshSize
  α := α
  C := 3 * cst
  C' := 0
  approx x hx h t ht := by
    obtain ⟨v, hv⟩ := hrate x hx h
    have hv0 := hv 0 ⟨le_rfl, ht.1.trans ht.2⟩
    rw [C0Group.S_zero_apply, ApproxFEEC.sol_zero] at hv0
    change ‖H.waveGroup.S t x - F.sol h (F.proj h x) t‖ ≤ _
    have := hF.norm_sub_sol_proj_le h x v t
    linarith [hv t ht]
  consistency x _ h t _ := by
    change ‖(orbitComparison F T).defect x h t‖ ≤ _
    rw [orbitComparison_defect, norm_zero, zero_mul, zero_mul]

theorem orbitRate_C (hF : IsOrthogonal F) {T : ℝ} (S : Set (PiLp 2 W)) classNorm meshSize α cst
    hrate : (orbitRate (T := T) hF S classNorm meshSize α cst hrate).C = 3 * cst := rfl

theorem orbitRate_C' (hF : IsOrthogonal F) {T : ℝ} (S : Set (PiLp 2 W)) classNorm meshSize α cst
    hrate : (orbitRate (T := T) hF S classNorm meshSize α cst hrate).C' = 0 := rfl

theorem orbitRate_p (hF : IsOrthogonal F) {T : ℝ} (S : Set (PiLp 2 W)) classNorm meshSize α cst
    hrate (x : PiLp 2 W) (h : κ) (t : ℝ) :
    (orbitRate (T := T) hF S classNorm meshSize α cst hrate).p x h t =
      (F.group h).S t (F.proj h x) := rfl

end ApproxFEEC

/-! ### Complexification of orthogonal reading maps -/

section Complexify

open scoped RealInnerProductSpace

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace ℝ (W' i)]
  [∀ i, CompleteSpace (W' i)] {H' : HilbertComplex ℝ c W'} {κ' : Type*}

/-- An isometric `J` with `J² = -1` is skew: `⟪J x, y⟫ = -⟪x, J y⟫`. -/
theorem inner_J_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (J : E →L[ℝ] E)
    (hJJ : ∀ x, J (J x) = -x) (hJ : ∀ x, ‖J x‖ = ‖x‖) (x y : E) : ⟪J x, y⟫ = -⟪x, J y⟫ := by
  have h := (⟨J.toLinearMap, hJ⟩ : E →ₗᵢ[ℝ] E).inner_map_map (J x) y
  change ⟪J (J x), J y⟫ = ⟪J x, y⟫ at h
  rw [hJJ, inner_neg_left] at h
  rw [← h]

theorem inner_J_J {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (J : E →L[ℝ] E)
    (hJ : ∀ x, ‖J x‖ = ‖x‖) (x y : E) : ⟪J x, J y⟫ = ⟪x, y⟫ :=
  (⟨J.toLinearMap, hJ⟩ : E →ₗᵢ[ℝ] E).inner_map_map x y

/-- **The complexification of orthogonal reading maps is orthogonal**: `ι'(a, b) = ιa + J ιb` is
isometric with adjoint `π' y = (πy, -π(Jy))`. -/
theorem ApproxFEEC.IsOrthogonal.complexify {F : ApproxFEEC H' κ'} (hF : ApproxFEEC.IsOrthogonal F)
    (J : PiLp 2 W' →L[ℝ] PiLp 2 W') (hJJ : ∀ x, J (J x) = -x) (hJ : ∀ x, ‖J x‖ = ‖x‖)
    (hπJ : ∀ h b, F.proj h (J (F.incl h b)) = 0)
    (hJι : ∀ h a b, ⟪F.incl h a, J (F.incl h b)⟫ = 0) :
    ApproxFEEC.IsOrthogonal (F.complexify J hJJ hJ hπJ hJι) where
  inner_incl h x y := by
    obtain ⟨⟨a, b⟩⟩ := x
    obtain ⟨⟨a', b'⟩⟩ := y
    rw [ApproxFEEC.complexify_incl, ApproxFEEC.complexify_incl]
    change ⟪F.incl h a + J (F.incl h b), F.incl h a' + J (F.incl h b')⟫ = ⟪a, a'⟫ + ⟪b, b'⟫
    rw [inner_add_left, inner_add_right, inner_add_right, hF.inner_incl, hJι,
      real_inner_comm (F.incl h a') (J (F.incl h b)), hJι, inner_J_J J hJ, hF.inner_incl]
    ring
  inner_incl_left h x y := by
    obtain ⟨⟨a, b⟩⟩ := x
    rw [ApproxFEEC.complexify_incl]
    change ⟪F.incl h a + J (F.incl h b), y⟫ = ⟪a, F.proj h y⟫ + ⟪b, -F.proj h (J y)⟫
    rw [inner_add_left, hF.inner_incl_left, inner_J_left J hJJ hJ, hF.inner_incl_left,
      inner_neg_right]

end Complexify

end Feec.Instances.EinsteinBianchi.FEM
