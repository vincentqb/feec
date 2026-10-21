module

public import Feec.HilbertComplex.Approximation.QuasiOptimal

/-!
# Smoothed projections: bounded cochain projections from commuting smoothed interpolants

Let `Vₕ` be a finite-dimensional subcomplex of a Hilbert complex `H`. The canonical interpolant
`Π_h` of a finite element space commutes with `d` but is only defined on smooth fields; composing
it with a **smoother** `R` that commutes with `d` (mollification after a dilation, or a Fourier
multiplier on a torus) gives a map `Q = Π_h R : W → Vₕ` that is defined and bounded on all of `W`
and commutes with `d`, but is not a projection. If `Q` is close to the identity on `Vₕ`,
`‖v - Q v‖ ≤ θ ‖v‖` for `v ∈ Vₕ` with `θ < 1` (in [AFW2010], §5.4 and
[ChristiansenWinther2008], `θ = ½` for a smoothing parameter `ε = c h` with `c` small), then
`J = Q|_{Vₕ}` is invertible with `‖J⁻¹‖ ≤ (1 - θ)⁻¹` and

`π = J⁻¹ Q`

is a **cochain projection** onto `Vₕ` (`CommutingMap.toCochainProjection`), bounded in `W` by
`(1 - θ)⁻¹ ‖Q‖` (`CommutingMap.norm_toCochainProjection_le`) and in the graph norm by
`(1 - θ)⁻¹` times the graph bound of `Q` (`CommutingMap.isGraphBounded_toCochainProjection`):
only the `W`-estimate on `Vₕ` is needed, because `d π x = J⁻¹ Q d x`. With `θ = ½` and
`Q = Π_h R`, `‖R‖ ≤ C_R`, `‖Π_h‖ ≤ C_Π`, the bound is `‖π‖ ≤ 2 C_Π C_R`
(`SmoothedInterpolant.norm_toCochainProjection_le_half`), and the discrete Poincaré inequality
follows (`SmoothedInterpolant.norm_le_of_forall_inner_eq_zero_half`).

For a family of subcomplexes with uniformly `W`-bounded cochain projections that approximate
every point, the **harmonic gap tends to zero** whenever the harmonic space is
finite-dimensional (`CochainProjection.tendsto_harmonicGap`): `‖q - π q‖ ≤ (1 + C) dist(q, Vₕ)`
(`CochainProjection.norm_sub_π_le_infDist`), and a basis of `ℌ` makes the convergence uniform on
the unit ball.

## Main definitions

* `Subcomplex.CommutingMap`: a linear map `Q : W → Vₕ` commuting with `d`.
* `Subcomplex.CommutingMap.restrictV`: `J = Q|_{Vₕ}`; `CommutingMap.restrictVEquiv`: `J` as a
  linear equivalence when `‖v - Q v‖ ≤ θ ‖v‖` on `Vₕ`, `θ < 1`.
* `Subcomplex.CommutingMap.toCochainProjection`: `π = J⁻¹ Q`.
* `Subcomplex.SmoothedInterpolant`: a smoother `R : W → X` into a complex `X` of smooth fields
  and an interpolant `Π : X → Vₕ`, both commuting with the differentials;
  `SmoothedInterpolant.toCommutingMap`: `Q = Π R`.

## Main results

* `CommutingMap.norm_le_of_restrictV`: `‖v‖ ≤ (1 - θ)⁻¹ ‖J v‖`.
* **`CommutingMap.toCochainProjection`**, `CommutingMap.toCochainProjection_π`,
  **`CommutingMap.norm_toCochainProjection_le`**,
  **`CommutingMap.isGraphBounded_toCochainProjection`**,
  `CommutingMap.isGraphBounded_toCochainProjection_of_norm_le` (graph bound from `W`-bounds,
  since `d Q = Q d`).
* **`SmoothedInterpolant.norm_toCochainProjection_le_half`**: `‖π‖ ≤ 2 C_Π C_R`;
  `SmoothedInterpolant.norm_le_of_forall_inner_eq_zero_half`: the discrete Poincaré inequality
  `‖x‖ ≤ 2 C_Π C_R c_P ‖d x‖` on `Vₕ ⊥ 𝔷ₕ`.
* `CochainProjection.norm_sub_π_le_infDist`, **`CochainProjection.tendsto_harmonicGap`**.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.4 (smoothed projections; `J = Π_h R_ε|_{Vₕ}` and `π_h = J⁻¹ Π_h R_ε`), Thm 3.5 (harmonic
  gap)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
  (the construction `π_h = J⁻¹ Π_h R_ε`)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (canonical interpolants commuting with `d`)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (bounded commuting
  projections)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Filter Topology

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace Subcomplex

variable (S : H.Subcomplex)

/-- A **commuting map into the subcomplex**: linear maps `Qⁱ : Wⁱ → Wⁱ` with values in `Vₕⁱ` and
`d Qⁱ = Qʲ d` on `D(d i j)`; for instance `Q = Π_h R` with `R` a smoother and `Π_h` the
canonical interpolant ([AFW2010], §5.4). Unlike a cochain projection, `Q` need not fix `Vₕ`. -/
structure CommutingMap where
  /-- the maps -/
  Q : ∀ i, W i →ₗ[𝕜] W i
  mem : ∀ i x, Q i x ∈ S.V i
  comm : ∀ i j (x : (H.d i j).domain),
    H.d i j ⟨Q i x, S.le_domain i j (mem i x)⟩ = Q j (H.d i j x)

namespace CommutingMap

variable {S} (Q : S.CommutingMap)

/-- `J = Q|_{Vₕ} : Vₕ → Vₕ`. -/
def restrictV (i : ι) : S.V i →ₗ[𝕜] S.V i :=
  (Q.Q i).restrict fun x _ => Q.mem i x

@[simp] theorem coe_restrictV_apply (i : ι) (v : S.V i) :
    (Q.restrictV i v : W i) = Q.Q i v := rfl

/-- If `‖v - Q v‖ ≤ θ ‖v‖` on `Vₕ` with `θ < 1`, then `(1 - θ) ‖v‖ ≤ ‖J v‖`. -/
theorem norm_le_of_restrictV {i : ι} {θ : ℝ}
    (hQ : ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) (v : S.V i) :
    (1 - θ) * ‖(v : W i)‖ ≤ ‖(Q.restrictV i v : W i)‖ := by
  have h1 : ‖(v : W i)‖ ≤ ‖(v : W i) - Q.Q i v‖ + ‖Q.Q i v‖ := norm_le_norm_sub_add _ _
  have h2 := hQ v v.2
  rw [coe_restrictV_apply]
  nlinarith

theorem injective_restrictV {i : ι} {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) : Function.Injective (Q.restrictV i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h := Q.norm_le_of_restrictV hQ v
  rw [hv, ZeroMemClass.coe_zero, norm_zero] at h
  have h0 : ‖(v : W i)‖ = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right h (by linarith)) (norm_nonneg _)
  exact Subtype.ext (by simpa using h0)

variable [∀ i, FiniteDimensional 𝕜 (S.V i)]

theorem bijective_restrictV {i : ι} {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) : Function.Bijective (Q.restrictV i) :=
  ⟨Q.injective_restrictV hθ hQ, LinearMap.injective_iff_surjective.1 (Q.injective_restrictV hθ hQ)⟩

/-- `J = Q|_{Vₕ}` as a linear equivalence of `Vₕ` (`‖v - Q v‖ ≤ θ ‖v‖` on `Vₕ`, `θ < 1`). -/
def restrictVEquiv {θ : ℝ} (hθ : θ < 1) (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖)
    (i : ι) : S.V i ≃ₗ[𝕜] S.V i :=
  LinearEquiv.ofBijective (Q.restrictV i) (Q.bijective_restrictV hθ (hQ i))

theorem restrictVEquiv_apply {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) (i : ι) (v : S.V i) :
    Q.restrictVEquiv hθ hQ i v = Q.restrictV i v := rfl

/-- `Q (J⁻¹ w) = w` for `w ∈ Vₕ`. -/
theorem Q_restrictVEquiv_symm {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) (i : ι) (w : S.V i) :
    Q.Q i ((Q.restrictVEquiv hθ hQ i).symm w) = w := by
  have h := (Q.restrictVEquiv hθ hQ i).apply_symm_apply w
  rw [restrictVEquiv_apply] at h
  exact congrArg Subtype.val h

/-- `‖J⁻¹ w‖ ≤ (1 - θ)⁻¹ ‖w‖`. -/
theorem norm_restrictVEquiv_symm_le {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) (i : ι) (w : S.V i) :
    ‖(((Q.restrictVEquiv hθ hQ i).symm w : S.V i) : W i)‖ ≤ (1 - θ)⁻¹ * ‖(w : W i)‖ := by
  have h := Q.norm_le_of_restrictV (hQ i) ((Q.restrictVEquiv hθ hQ i).symm w)
  rw [← restrictVEquiv_apply Q hθ hQ, LinearEquiv.apply_symm_apply] at h
  rw [le_inv_mul_iff₀ (by linarith)]
  exact h

/-- **The smoothed projection** `π = J⁻¹ Q`: a cochain projection onto `Vₕ` as soon as
`‖v - Q v‖ ≤ θ ‖v‖` on `Vₕ` for some `θ < 1`. See [AFW2010], §5.4;
[ChristiansenWinther2008]. -/
def toCochainProjection {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) : S.CochainProjection where
  π i := (S.V i).subtype ∘ₗ ((Q.restrictVEquiv hθ hQ i).symm : S.V i →ₗ[𝕜] S.V i) ∘ₗ
    (Q.Q i).codRestrict (S.V i) (Q.mem i)
  mem i x := ((Q.restrictVEquiv hθ hQ i).symm _).2
  proj i x hx := by
    have h : (Q.Q i).codRestrict (S.V i) (Q.mem i) x = Q.restrictVEquiv hθ hQ i ⟨x, hx⟩ := rfl
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe, h, LinearEquiv.symm_apply_apply]
  comm i j x := by
    set e := Q.restrictVEquiv hθ hQ
    set v := (e i).symm ((Q.Q i).codRestrict (S.V i) (Q.mem i) x)
    have hv : Q.Q i v = Q.Q i x := Q.Q_restrictVEquiv_symm hθ hQ i _
    -- `J (d v) = Q (d v) = d (Q v) = d (Q x) = Q (d x)`
    set dv : S.V j := S.dLin i j v
    have hJ : e j dv = (Q.Q j).codRestrict (S.V j) (Q.mem j) (H.d i j x) := by
      refine Subtype.ext ?_
      change Q.Q j (H.d i j (S.toDomain i j v)) = Q.Q j (H.d i j x)
      rw [← Q.comm i j (S.toDomain i j v), ← Q.comm i j x]
      congr 2
    change H.d i j (S.toDomain i j v) = (((e j).symm _ : S.V j) : W j)
    rw [← hJ, LinearEquiv.symm_apply_apply]
    rfl

@[simp] theorem toCochainProjection_π {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) (i : ι) (x : W i) :
    (Q.toCochainProjection hθ hQ).π i x =
      ((Q.restrictVEquiv hθ hQ i).symm ⟨Q.Q i x, Q.mem i x⟩ : W i) := rfl

/-- `‖π x‖ ≤ (1 - θ)⁻¹ ‖Q x‖`. -/
theorem norm_toCochainProjection_le_norm_Q {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) (i : ι) (x : W i) :
    ‖(Q.toCochainProjection hθ hQ).π i x‖ ≤ (1 - θ)⁻¹ * ‖Q.Q i x‖ :=
  Q.norm_restrictVEquiv_symm_le hθ hQ i ⟨Q.Q i x, Q.mem i x⟩

/-- **`W`-bound of the smoothed projection**: `‖Q‖ ≤ C` gives `‖π‖ ≤ (1 - θ)⁻¹ C`. -/
theorem norm_toCochainProjection_le {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) {i : ι} {C : ℝ}
    (hC : ∀ x, ‖Q.Q i x‖ ≤ C * ‖x‖) (x : W i) :
    ‖(Q.toCochainProjection hθ hQ).π i x‖ ≤ (1 - θ)⁻¹ * C * ‖x‖ := by
  rw [mul_assoc]
  exact (Q.norm_toCochainProjection_le_norm_Q hθ hQ i x).trans
    (mul_le_mul_of_nonneg_left (hC x) (inv_nonneg.2 (by linarith)))

/-- `d π x = J⁻¹ Q d x`, so `‖d π x‖ ≤ (1 - θ)⁻¹ ‖Q d x‖`. -/
theorem norm_d_toCochainProjection_le {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) {i j : ι} (x : (H.d i j).domain) :
    ‖H.d i j ⟨(Q.toCochainProjection hθ hQ).π i x,
        S.le_domain i j ((Q.toCochainProjection hθ hQ).mem i x)⟩‖ ≤
      (1 - θ)⁻¹ * ‖Q.Q j (H.d i j x)‖ := by
  rw [(Q.toCochainProjection hθ hQ).comm]
  exact Q.norm_toCochainProjection_le_norm_Q hθ hQ j _

/-- **Graph-norm bound of the smoothed projection**: if
`‖Q x‖² + ‖d Q x‖² ≤ C² (‖x‖² + ‖d x‖²)`, then `π` is graph-bounded by `(1 - θ)⁻¹ C`. Only the
`W`-estimate of `Q` on `Vₕ` (at both indices) is used. -/
theorem isGraphBounded_toCochainProjection {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) {i j : ι} {C : ℝ}
    (hC : ∀ x : (H.d i j).domain, ‖Q.Q i x‖ ^ 2 +
      ‖H.d i j ⟨Q.Q i x, S.le_domain i j (Q.mem i x)⟩‖ ^ 2 ≤
        C ^ 2 * (‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2)) :
    (Q.toCochainProjection hθ hQ).IsGraphBounded i j ((1 - θ)⁻¹ * C) := by
  intro x
  have ha := Q.norm_toCochainProjection_le_norm_Q hθ hQ i x
  have hb := Q.norm_d_toCochainProjection_le hθ hQ x
  rw [← Q.comm i j x] at hb
  have hk : 0 ≤ (1 - θ)⁻¹ := inv_nonneg.2 (by linarith)
  have ha2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have := hC x
  calc _ ≤ ((1 - θ)⁻¹ * ‖Q.Q i x‖) ^ 2 +
        ((1 - θ)⁻¹ * ‖H.d i j ⟨Q.Q i x, S.le_domain i j (Q.mem i x)⟩‖) ^ 2 := add_le_add ha2 hb2
    _ = (1 - θ)⁻¹ ^ 2 * (‖Q.Q i x‖ ^ 2 +
        ‖H.d i j ⟨Q.Q i x, S.le_domain i j (Q.mem i x)⟩‖ ^ 2) := by ring
    _ ≤ (1 - θ)⁻¹ ^ 2 * (C ^ 2 * (‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

omit [∀ i, FiniteDimensional 𝕜 (S.V i)] in
/-- A commuting map bounded by `C` in `W` at both ends of `i → j` is bounded by `C` in the graph
norm: `d Q x = Q d x`. -/
theorem graph_le_of_norm_le {i j : ι} {C : ℝ} (hi : ∀ x, ‖Q.Q i x‖ ≤ C * ‖x‖)
    (hj : ∀ x, ‖Q.Q j x‖ ≤ C * ‖x‖) (x : (H.d i j).domain) :
    ‖Q.Q i x‖ ^ 2 + ‖H.d i j ⟨Q.Q i x, S.le_domain i j (Q.mem i x)⟩‖ ^ 2 ≤
      C ^ 2 * (‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2) := by
  rw [Q.comm]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hi x) 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (hj (H.d i j x)) 2
  nlinarith

/-- **Graph bound of the smoothed projection from `W`-bounds**: `‖Q‖ ≤ C` at `i` and `j` gives
`π` graph-bounded by `(1 - θ)⁻¹ C` at `i → j`. -/
theorem isGraphBounded_toCochainProjection_of_norm_le {θ : ℝ} (hθ : θ < 1)
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) {i j : ι} {C : ℝ}
    (hi : ∀ x, ‖Q.Q i x‖ ≤ C * ‖x‖) (hj : ∀ x, ‖Q.Q j x‖ ≤ C * ‖x‖) :
    (Q.toCochainProjection hθ hQ).IsGraphBounded i j ((1 - θ)⁻¹ * C) :=
  Q.isGraphBounded_toCochainProjection hθ hQ (Q.graph_le_of_norm_le hi hj)

end CommutingMap

/-! ### Smoother followed by an interpolant -/

/-- A **smoothed interpolant** for the subcomplex `Vₕ`: a complex of (smooth) fields `X` with
differentials `d_X`, a **smoother** `R : W → X` with `R d = d_X R` on `D(d)`, and an
**interpolant** `Π : X → Vₕ` with `d Π = Π d_X` (the canonical interpolant of a finite element
space, defined on smooth fields only). Then `Q = Π R` is a commuting map
(`SmoothedInterpolant.toCommutingMap`). See [AFW2010], §5.4; [ChristiansenWinther2008]. -/
structure SmoothedInterpolant (X : ι → Type*) [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)]
    where
  /-- the differentials of the smooth complex -/
  dX : ∀ i j, X i →ₗ[𝕜] X j
  /-- the smoother -/
  R : ∀ i, W i →ₗ[𝕜] X i
  /-- the interpolant -/
  interp : ∀ i, X i →ₗ[𝕜] W i
  mem_interp : ∀ i y, interp i y ∈ S.V i
  R_comm : ∀ i j (x : (H.d i j).domain), R j (H.d i j x) = dX i j (R i x)
  interp_comm : ∀ i j y,
    H.d i j ⟨interp i y, S.le_domain i j (mem_interp i y)⟩ = interp j (dX i j y)

namespace SmoothedInterpolant

variable {S} {X : ι → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)]
  (P : S.SmoothedInterpolant X)

/-- `Q = Π R`, a commuting map into `Vₕ`. -/
def toCommutingMap : S.CommutingMap where
  Q i := P.interp i ∘ₗ P.R i
  mem i x := P.mem_interp i _
  comm i j x := by
    change H.d i j ⟨P.interp i (P.R i x), _⟩ = P.interp j (P.R j (H.d i j x))
    rw [P.interp_comm, P.R_comm]

@[simp] theorem toCommutingMap_Q (i : ι) (x : W i) :
    P.toCommutingMap.Q i x = P.interp i (P.R i x) := rfl

end SmoothedInterpolant

namespace SmoothedInterpolant

variable {S} {X : ι → Type*} [∀ i, SeminormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
  (P : S.SmoothedInterpolant X)

/-- `‖Π R x‖ ≤ C_Π C_R ‖x‖` for any seminorms on the smooth fields with `‖R x‖ ≤ C_R ‖x‖` and
`‖Π y‖ ≤ C_Π ‖y‖`. -/
theorem norm_toCommutingMap_le {i : ι} {CR CI : ℝ}
    (hCI : 0 ≤ CI) (hR : ∀ x, ‖P.R i x‖ ≤ CR * ‖x‖) (hI : ∀ y, ‖P.interp i y‖ ≤ CI * ‖y‖)
    (x : W i) : ‖P.toCommutingMap.Q i x‖ ≤ CI * CR * ‖x‖ := by
  rw [toCommutingMap_Q, mul_assoc]
  exact (hI _).trans (mul_le_mul_of_nonneg_left (hR x) hCI)

variable [∀ i, FiniteDimensional 𝕜 (S.V i)]

/-- **The smoothed projection `π_h = J⁻¹ Π_h R` is bounded by `2 C_Π C_R`** when
`‖v - Π_h R v‖ ≤ ½ ‖v‖` on `Vₕ` ([AFW2010], §5.4; [ChristiansenWinther2008]). -/
theorem norm_toCochainProjection_le_half
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - P.interp i (P.R i v)‖ ≤ 1 / 2 * ‖v‖) {i : ι} {CR CI : ℝ}
    (hCI : 0 ≤ CI) (hR : ∀ x, ‖P.R i x‖ ≤ CR * ‖x‖) (hI : ∀ y, ‖P.interp i y‖ ≤ CI * ‖y‖)
    (x : W i) :
    ‖(P.toCommutingMap.toCochainProjection (by norm_num) hQ).π i x‖ ≤ 2 * CI * CR * ‖x‖ := by
  have h := P.toCommutingMap.norm_toCochainProjection_le (θ := 1 / 2) (by norm_num) hQ
    (P.norm_toCommutingMap_le hCI hR hI) x
  have e : (1 - 1 / 2 : ℝ)⁻¹ * (CI * CR) = 2 * CI * CR := by ring
  rwa [e] at h

/-- **Discrete Poincaré inequality from a smoothed projection**: with `‖v - Π_h R v‖ ≤ ½ ‖v‖` on
`Vₕ`, `‖R‖ ≤ C_R`, `‖Π_h‖ ≤ C_Π` and the Poincaré inequality `‖z‖ ≤ c_P ‖d z‖` on `(𝔷ⁱ)ᗮ`,
`‖x‖ ≤ 2 C_Π C_R c_P ‖d x‖` for `x ∈ Vₕⁱ ⊥ 𝔷ₕⁱ` ([AFW2010], Thm 3.6 and §5.4). -/
theorem norm_le_of_forall_inner_eq_zero_half
    (hQ : ∀ i, ∀ v ∈ S.V i, ‖v - P.interp i (P.R i v)‖ ≤ 1 / 2 * ‖v‖) {i j : ι}
    (hij : c.Rel i j) {cP CR CI : ℝ} (hCI : 0 ≤ CI) (hCR : 0 ≤ CR)
    (hR : ∀ x, ‖P.R i x‖ ≤ CR * ‖x‖) (hI : ∀ y, ‖P.interp i y‖ ≤ CI * ‖y‖)
    (hP : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    {x : W i} (hx : x ∈ S.V i) (hxo : ∀ y ∈ S.cyclesW i, ⟪y, x⟫ = 0) :
    ‖x‖ ≤ 2 * CI * CR * cP * ‖H.d i j ⟨x, S.le_domain i j hx⟩‖ :=
  (P.toCommutingMap.toCochainProjection (by norm_num) hQ).norm_le_of_forall_inner_eq_zero hij hP
    (by positivity) (P.norm_toCochainProjection_le_half hQ hCI hR hI) hx hxo

end SmoothedInterpolant

/-! ### The harmonic gap of uniformly bounded cochain projections -/

namespace CochainProjection

variable {S}

/-- `‖x - π x‖ ≤ (1 + C) dist(x, Vₕ)` for a cochain projection bounded by `C` (in `W`). -/
theorem norm_sub_π_le_infDist (P : S.CochainProjection) {i : ι} {C : ℝ} (hC : 0 ≤ C)
    (hπ : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) (x : W i) :
    ‖x - P.π i x‖ ≤ (1 + C) * Metric.infDist x (S.V i : Set (W i)) := by
  have key : ∀ v ∈ S.V i, ‖x - P.π i x‖ ≤ (1 + C) * dist x v := by
    intro v hv
    have e : x - P.π i x = (x - v) - P.π i (x - v) := by
      rw [_root_.map_sub, P.proj i v hv]; abel
    rw [e, dist_eq_norm]
    calc ‖(x - v) - P.π i (x - v)‖ ≤ ‖x - v‖ + ‖P.π i (x - v)‖ := norm_sub_le _ _
      _ ≤ ‖x - v‖ + C * ‖x - v‖ := by gcongr; exact hπ _
      _ = (1 + C) * ‖x - v‖ := by ring
  have hne : (S.V i : Set (W i)).Nonempty := ⟨0, (S.V i).zero_mem⟩
  have h1 : 0 < 1 + C := by linarith
  have h2 : ‖x - P.π i x‖ / (1 + C) ≤ Metric.infDist x (S.V i : Set (W i)) := by
    refine (Metric.le_infDist hne).2 fun v hv => ?_
    rw [div_le_iff₀' h1]
    exact key v hv
  rwa [div_le_iff₀' h1] at h2

/-- **The harmonic gap tends to zero** (cf. [AFW2010], Thm 3.5 and §3.4): for a family of
subcomplexes `Vₕ` with cochain projections uniformly bounded in `W` by `C`, approximating every
harmonic form (`dist(q, Vₕ) → 0`), and a finite-dimensional harmonic space `ℌʲ`,
`μₕ = sup_{q ∈ ℌ, ‖q‖ ≤ 1} ‖q - πₕ q‖ → 0`. -/
theorem tendsto_harmonicGap {κ : Type*} {l : Filter κ} {S : κ → H.Subcomplex}
    (P : ∀ h, (S h).CochainProjection) {j : ι} [FiniteDimensional 𝕜 (H.harmonic j)] {C : ℝ}
    (hC : 0 ≤ C) (hπ : ∀ h x, ‖(P h).π j x‖ ≤ C * ‖x‖)
    (happrox : ∀ q ∈ H.harmonic j,
      Tendsto (fun h => Metric.infDist q ((S h).V j : Set (W j))) l (𝓝 0)) :
    Tendsto (fun h => (P h).harmonicGap j) l (𝓝 0) := by
  classical
  -- a basis of `ℌʲ` and the (continuous) coordinate functionals
  set b := Module.finBasis 𝕜 (H.harmonic j)
  set m := Module.finrank 𝕜 (H.harmonic j)
  set coord : Fin m → H.harmonic j →L[𝕜] 𝕜 := fun k =>
    LinearMap.toContinuousLinearMap (b.coord k)
  set A : ℝ := ∑ k, ‖coord k‖ * ‖((b k : H.harmonic j) : W j)‖
  -- the gap is bounded by `(1 + C) Σ_k ‖c_k‖ dist(b_k, Vₕ)`
  set g : κ → ℝ := fun h => (1 + C) * ∑ k, ‖coord k‖ *
    Metric.infDist ((b k : H.harmonic j) : W j) ((S h).V j : Set (W j))
  have hg : Tendsto g l (𝓝 0) := by
    have : Tendsto g l (𝓝 ((1 + C) * ∑ k : Fin m, ‖coord k‖ * 0)) :=
      (tendsto_finsetSum _ fun k _ =>
        (happrox _ (b k).2).const_mul ‖coord k‖).const_mul (1 + C)
    simpa using this
  have hle : ∀ h, (P h).harmonicGap j ≤ g h := by
    intro h
    have hg0 : 0 ≤ g h := by
      refine mul_nonneg (by linarith) (Finset.sum_nonneg fun k _ => ?_)
      exact mul_nonneg (norm_nonneg _) Metric.infDist_nonneg
    refine (P h).harmonicGap_le hg0 fun q hq => ?_
    set q' : H.harmonic j := ⟨q, hq⟩
    have hrepr : q = ∑ k, (b.repr q' k) • ((b k : H.harmonic j) : W j) := by
      have := congrArg Subtype.val (b.sum_repr q')
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have hcoord : ∀ k, ‖b.repr q' k‖ ≤ ‖coord k‖ * ‖q‖ := fun k =>
      (coord k).le_opNorm q'
    calc ‖q - (P h).π j q‖
        = ‖∑ k, (b.repr q' k) • (((b k : H.harmonic j) : W j) -
            (P h).π j ((b k : H.harmonic j) : W j))‖ := by
          conv_lhs => rw [hrepr]
          rw [map_sum]
          simp only [_root_.map_smul, smul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ k, ‖b.repr q' k‖ * ‖((b k : H.harmonic j) : W j) -
            (P h).π j ((b k : H.harmonic j) : W j)‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_smul]
      _ ≤ ∑ k, (‖coord k‖ * ‖q‖) * ((1 + C) *
            Metric.infDist ((b k : H.harmonic j) : W j) ((S h).V j : Set (W j))) := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul (hcoord k) ((P h).norm_sub_π_le_infDist hC (hπ h) _)
            (norm_nonneg _) (by positivity)
      _ = g h * ‖q‖ := by
          simp only [g, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  exact squeeze_zero (fun h => (P h).harmonicGap_nonneg j) hle hg

end CochainProjection

end Subcomplex

end Feec.HilbertComplex
