module

public import Feec.Physics.EinsteinBianchi.BoundedConvergence
public import Feec.Physics.EinsteinBianchi.WaveFEMTangentialCube
public import Feec.Models.Cube.WeakSymmetrySobolevRate

/-!
# Regularity of the forms-model Hodge wave equation on the cube and an `O(h)` rate from `D(L³)`

[QuennevilleBelair2015], §6.3: which powers of the domain of the forms-model Hodge wave operator
`L` (`formsShort.wave`) give the regularity that the rate `cubeWave_rate_sobolev` of the scheme
(6.5) needs, and an `O(h)` rate for data in `D(L³)`.

**(a) Powers of the domain.** `MemDomainPow A k`: `x, A x, …, A^{k-1} x ∈ D(A)`. For a
skew-adjoint `A` the group `e^{tA}` preserves `D(Aᵏ)`, commutes with `Aʲ` and conserves `‖Aʲ x‖`
(`memDomainPow_group`, `norm_iterate_extOp_group`); kernel vectors are stationary and in every
`D(Aᵏ)` (`group_S_eq_self`, `memDomainPow_of_mem_ker`).

**(b) Degree-0 and degree-1 rows.** For `U ∈ D(L)`, `σ ∈ H¹_univ` with
`‖σ‖_{1,univ} ≤ ‖U‖ + ‖L U‖` (Gaffney, `sobRel_σOf`), unconditionally. The rows of `dφ` are in
`H¹_univ` (`sobRel_D0_φOf`) under further hypotheses: `L U ∈ D(L)`, an `L²`-bounded multiplier of
`L U` and `M ∈ D(d¹*)`, with a constant involving those bounds. The rows `uₐ` are in `H¹_univ`
iff `div uₐ ∈ L²` (`D(d⁰*)`), which `D(Lᵏ)` does not give for any `k` (`uₐ = ∇ψₐ` with `ψ`
divergence-free in `H¹₀ \ H²`; argued, not formalized). An `L²`-bounded multiplier implies it
(`rowu_mem_adjoint_of_mult`); the converse is not proved (it would need a right inverse of
`(τ, ψ) ↦ dτ − S⁰ψ` bounded in `L²`), so the multiplier hypothesis of `cubeWave_rate_tr` is kept.
The Hessian rows `d uₐ`, `d φ'ₐ` follow from `L U ∈ D(L)` and `M ∈ D(d¹*)`
(`rowD1Ladj_mem_adjoint`).

**(c) Top rows.** The rows of `ρ` are always in `D(d¹*)`, and `D(d²)` propagates along the orbit
from `ρ(0)` (`compρL_waveOrbit_mem`). It is not implied by `D(L^∞)`: the stationary state with
`ρ = (sawW2, 0, 0)` lies in `ker L` while `sawW2 ∉ H̊Λ²(Q)` and `∉ H^{1/2}_univ`
(`exists_memDomainPow_compρL_not_mem`; the obstruction is the tangential trace, the field is
smooth inside `Q`). The obstruction lives in `N(L)`: on `N(L)ᗮ = cl R(L)` the magnetic rows are in
`N(d²)` (`compρL_mem_ker_of_mem_orthogonal`), hence in `H¹_univ` with norm
`≤ (1 + √2) ‖U‖ + 2 ‖L U‖` for `U ∈ D(L) ∩ N(L)ᗮ` (`sobRel_compρL_of_mem_orthogonal`); for general
`U₀` only the stationary part `P_{N(L)} U₀` needs a hypothesis (`compρL_mem_of_projKer`). The skew
field `M` is assumed in `H¹_univ = D(d²) ∩ D(d¹*)`: `S¹` couples components of incompatible
parities, and the corresponding coupled regularity is absent from Mathlib.

**The rate.** `waveFEM_rate_of_mem_domain`: for `U₀ ∈ D(L³)`, the classical solution
`orbitExact` along `e^{tL} U₀` and the solution of (6.5) from the elliptic projection satisfy
`(‖σ − σₕ‖² + ‖u − uₕ‖² + ‖M − Mₕ‖² + ‖ρ − ρₕ‖²)^{1/2}(t) ≤
K (Σ_{j≤3} ‖Lʲ U₀‖ + (1 + T) Λ)(1 + t) h_N` under hypotheses with bound `Λ`: on the datum, the
multiplier of `U₀`, `M(U₀) ∈ H¹_univ` and the magnetic rows of `P_{N(L)} U₀` in `H¹_univ`; along
the orbit, the multipliers of `L U(t)`, `L² U(t)` and `S¹u(t), S¹u'(t) ∈ H¹_univ`. This is not the
purely datum-level statement `U₀ ∈ D(Lᵏ)`, `P_{N(L)} U₀ ∈ H¹`: the orbit hypotheses on the
multiplier and on `S¹u` remain (see the docstring of `waveFEM_rate_of_mem_domain`). It replaces the
`C²` orbit hypothesis of `waveFEM_rate_tr_cube`. `k = 3` is what the argument uses
(`du' = (L² U)_ρ ∈ D(d¹*)` needs `L² U ∈ D(L)`); minimality is not shown.
`waveFEM_rate_of_mem_domain_of_orbit` is the version with all hypotheses along the orbit.

**Non-vacuity.** The standing wave `U(t) = cos(ωt) (0, u, 0) + ω⁻¹ sin(ωt) (0, 0, (0, du))`,
`u = ((sin 2πy₁ sin 2πy₂) dx₀, 0, 0)`, `ω² = 8π²`, is the orbit of `(0, u, 0) ∈ D(L³)`
(`waveOrbit_modeU`, by uniqueness of strong solutions), is not stationary, and satisfies the
hypotheses with `Λ = 0` (`waveFEM_rate_of_mem_domain_nonvacuous`: zero multipliers, `M ≡ 0`,
`P_{N(L)} U₀ = 0` since `U₀ ∈ R(L)`). It exercises the hypotheses on `M`, `S¹u` and the
multipliers only trivially.

## Main results

* `memDomainPow_group`, `norm_iterate_extOp_group`, `group_S_eq_self`.
* `isSobolevStateTr_of_mem`: the rate class of `cubeWave_rate_sobolev` at `s = 1` from `D(L³)`
  and the hypotheses on multipliers, `M` and `ρ(0)`.
* `compρL_mem_ker_of_mem_orthogonal`, `sobRel_compρL_of_mem_orthogonal`: the magnetic rows on
  `N(L)ᗮ`; `projKer`, `projKer_waveOrbit`, `compρL_mem_of_projKer`: the stationary part.
* `exists_mem_domain_of_hasDerivWithinAt`: domains of closed operators along trajectories.
* **`waveFEM_rate_of_mem_domain`**: the `O(h)` rate of (6.5) for data in `D(L³)`;
  `waveFEM_rate_of_mem_domain_cube`, with the smoothing estimates discharged;
  `waveFEM_rate_of_mem_domain_of_orbit`, with the hypotheses along the orbit.
* **`waveFEM_rate_of_mem_domain_nonvacuous`**: the hypotheses hold for a non-stationary solution.
* **`exists_memDomainPow_compρL_not_mem`**: a state in every `D(Lᵏ)` whose `ρ` row is not in
  `D(d²)` nor in `H^{1/2}_univ`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 5.5, §6.1 ((6.1), (6.2)), §6.3 ((6.4), (6.5), Table 6.1)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.9, §4.3 (Gaffney's inequality), §5.4

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi.WaveFEM

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry Feec.Models.BoundedDomain Feec.EinsteinBianchi.MatrixModel
  Feec.EinsteinBianchi.BoundedFailure Feec.EinsteinBianchi.BoundedConvergence

/-! ### Adjoint domains from bounded functionals -/

section Adjoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **A bounded functional gives a point of the adjoint domain, with the bound**: if
`|⟪y, T x⟫| ≤ c ‖x‖` on `D(T)` (dense), then `y ∈ D(T*)` and `‖T* y‖ ≤ c`. -/
theorem exists_mem_adjoint_of_abs_le (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) {y : F}
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ x : T.domain, |⟪y, T x⟫| ≤ c * ‖(x : E)‖) :
    ∃ hy : y ∈ T†.domain, ‖T† ⟨y, hy⟩‖ ≤ c := by
  have hy : y ∈ T†.domain := by
    rw [LinearPMap.mem_adjoint_domain_iff]
    refine AddMonoidHomClass.continuous_of_bound _ c fun x => ?_
    simpa [Real.norm_eq_abs] using h x
  refine ⟨hy, ?_⟩
  set v := T† ⟨y, hy⟩
  have hv : ∀ x : T.domain, |⟪v, (x : E)⟫| ≤ c * ‖(x : E)‖ := fun x => by
    rw [LinearPMap.adjoint_isFormalAdjoint hT ⟨y, hy⟩ x]; exact h x
  have hcl : IsClosed {x : E | |⟪v, x⟫| ≤ c * ‖x‖} :=
    isClosed_le (continuous_const.inner continuous_id).abs (continuous_const.mul continuous_norm)
  have hall : ∀ x : E, |⟪v, x⟫| ≤ c * ‖x‖ := by
    have hsub : (T.domain : Set E) ⊆ {x : E | |⟪v, x⟫| ≤ c * ‖x‖} := fun x hx => hv ⟨x, hx⟩
    have := closure_minimal hsub hcl
    rw [hT.closure_eq] at this
    exact fun x => this (Set.mem_univ x)
  have h1 := hall v
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _), sq] at h1
  by_cases hv0 : ‖v‖ = 0
  · rw [hv0]; exact hc
  · exact le_of_mul_le_mul_right (by linarith) (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0))

variable [CompleteSpace F]

/-- **The weak characterization of the domain of a closed operator** (von Neumann, `T†† = T`): if
`|⟪x, T* y⟫| ≤ c ‖y‖` on `D(T*)`, then `x ∈ D(T)` and `‖T x‖ ≤ c`. -/
theorem exists_mem_domain_of_abs_le (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) {x : E} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y : T†.domain, |⟪x, T† y⟫| ≤ c * ‖(y : F)‖) :
    ∃ hx : x ∈ T.domain, ‖T ⟨x, hx⟩‖ ≤ c := by
  obtain ⟨hx, hb⟩ := exists_mem_adjoint_of_abs_le T† (LinearPMap.dense_adjoint_domain T hT hTc) hc h
  have e := LinearPMap.adjoint_adjoint T hT hTc
  exact ⟨mem_domain_of_eq_op e.symm hx, by rw [norm_apply_of_eq_op e.symm hx]; exact hb⟩

/-- **A trajectory whose right derivative stays in the domain of a closed operator, with a
bound, stays in the domain**: if `f(0) ∈ D(A)` and `f'(r) ∈ D(A)` on `[0, T)`, with
`‖A f(0)‖, ‖A f'(r)‖ ≤ Λ`, then `f(t) ∈ D(A)` with `‖A f(t)‖ ≤ (1 + t) Λ` (pair with `D(A*)`
and apply the mean value inequality; `exists_mem_domain_of_abs_le`). -/
theorem exists_mem_domain_of_hasDerivWithinAt (A : E →ₗ.[ℝ] F) (hA : Dense (A.domain : Set E))
    (hAc : A.IsClosed) {f f' : ℝ → E} {T Λ : ℝ} (hΛ : 0 ≤ Λ) (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    (h0 : ∃ h : f 0 ∈ A.domain, ‖A ⟨_, h⟩‖ ≤ Λ)
    (h' : ∀ t ∈ Ico 0 T, ∃ h : f' t ∈ A.domain, ‖A ⟨_, h⟩‖ ≤ Λ) :
    ∀ t ∈ Icc 0 T, ∃ h : f t ∈ A.domain, ‖A ⟨_, h⟩‖ ≤ (1 + t) * Λ := by
  intro t ht
  refine exists_mem_domain_of_abs_le A hA hAc (by nlinarith [ht.1]) fun y => ?_
  have hadj : ∀ (z : E) (hz : z ∈ A.domain), ⟪z, A† y⟫ = ⟪(y : F), A ⟨z, hz⟩⟫ := fun z hz => by
    rw [real_inner_comm]; exact LinearPMap.adjoint_isFormalAdjoint hA y ⟨z, hz⟩
  have hgc : ContinuousOn (fun r => ⟪f r, A† y⟫) (Icc 0 T) := hc.inner continuousOn_const
  have hgd : ∀ r ∈ Ico 0 T, HasDerivWithinAt (fun r => ⟪f r, A† y⟫) ⟪f' r, A† y⟫ (Ici r) r :=
    fun r hr => by simpa using (hd r hr).inner ℝ (hasDerivWithinAt_const r (Ici r) (A† y))
  have hgb : ∀ r ∈ Ico 0 T, ‖⟪f' r, A† y⟫‖ ≤ Λ * ‖(y : F)‖ := fun r hr => by
    obtain ⟨h, hb⟩ := h' r hr
    rw [hadj _ h, Real.norm_eq_abs, mul_comm]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hgb t ht
  have h00 : |⟪f 0, A† y⟫| ≤ Λ * ‖(y : F)‖ := by
    obtain ⟨h, hb⟩ := h0
    rw [hadj _ h, mul_comm]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  rw [Real.norm_eq_abs, sub_zero] at hmv
  have := abs_sub_abs_le_abs_sub ⟪f t, A† y⟫ ⟪f 0, A† y⟫
  nlinarith [norm_nonneg (y : F)]

end Adjoint

/-! ### Skew-adjoint groups and the domains of the powers of the generator -/

section Powers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : E →ₗ.[ℝ] E}

open Classical in
/-- `A` extended by `0` off its domain. -/
def extOp (A : E →ₗ.[ℝ] E) (x : E) : E := if h : x ∈ A.domain then A ⟨x, h⟩ else 0

theorem extOp_eq {x : E} (h : x ∈ A.domain) : extOp A x = A ⟨x, h⟩ := by
  simp [extOp, h]

/-- **`x ∈ D(Aᵏ)`**: `x, A x, …, A^{k-1} x ∈ D(A)`. -/
def MemDomainPow (A : E →ₗ.[ℝ] E) : ℕ → E → Prop
  | 0, _ => True
  | k + 1, x => x ∈ A.domain ∧ MemDomainPow A k (extOp A x)

theorem MemDomainPow.mono : ∀ {k l : ℕ} {x : E}, l ≤ k → MemDomainPow A k x →
    MemDomainPow A l x
  | _, 0, _, _, _ => trivial
  | 0, l + 1, _, h, _ => absurd h (by omega)
  | k + 1, l + 1, _, h, hx => ⟨hx.1, MemDomainPow.mono (by omega) hx.2⟩

/-- `Aʲ x ∈ D(A)` for `j < k` when `x ∈ D(Aᵏ)`. -/
theorem MemDomainPow.iterate_mem : ∀ {k : ℕ} {x : E}, MemDomainPow A k x → ∀ j < k,
    (extOp A)^[j] x ∈ A.domain
  | 0, _, _, j, hj => absurd hj (by omega)
  | k + 1, _, hx, 0, _ => hx.1
  | k + 1, _, hx, j + 1, hj => MemDomainPow.iterate_mem hx.2 j (by omega)

theorem MemDomainPow.iterate : ∀ {k : ℕ} {x : E}, MemDomainPow A k x → ∀ j ≤ k,
    MemDomainPow A (k - j) ((extOp A)^[j] x)
  | _, _, hx, 0, _ => hx
  | 0, _, _, j + 1, hj => absurd hj (by omega)
  | k + 1, _, hx, j + 1, hj => by
    have := MemDomainPow.iterate hx.2 j (by omega)
    rwa [show k + 1 - (j + 1) = k - j by omega]

theorem extOp_add_smul (a b : ℝ) {x y : E} (hx : x ∈ A.domain) (hy : y ∈ A.domain) :
    extOp A (a • x + b • y) = a • extOp A x + b • extOp A y := by
  have h : a • x + b • y ∈ A.domain :=
    A.domain.add_mem (A.domain.smul_mem a hx) (A.domain.smul_mem b hy)
  rw [extOp_eq h, extOp_eq hx, extOp_eq hy]
  have e : (⟨a • x + b • y, h⟩ : A.domain) = a • ⟨x, hx⟩ + b • ⟨y, hy⟩ := rfl
  rw [e, LinearPMap.map_add, LinearPMap.map_smul, LinearPMap.map_smul]

/-- A kernel vector of `A` lies in every `D(Aᵏ)`. -/
theorem memDomainPow_of_mem_ker {x : E} (hx : x ∈ A.domain) (h0 : A ⟨x, hx⟩ = 0) :
    ∀ k, MemDomainPow A k x
  | 0 => trivial
  | k + 1 => by
    refine ⟨hx, ?_⟩
    rw [extOp_eq hx, h0]
    exact memDomainPow_of_mem_ker A.domain.zero_mem (LinearPMap.map_zero A) k

variable [CompleteSpace E] (hA : A.IsSkewAdjoint)
include hA

/-- **(a) `D(Aᵏ)` is invariant under the group, and `Aʲ e^{tA} = e^{tA} Aʲ`** for `j ≤ k`. -/
theorem memDomainPow_group : ∀ (k : ℕ) {x : E}, MemDomainPow A k x → ∀ t : ℝ,
    MemDomainPow A k (hA.group.S t x) ∧
      ∀ j ≤ k, (extOp A)^[j] (hA.group.S t x) = hA.group.S t ((extOp A)^[j] x)
  | 0, _, _, _ => ⟨trivial, fun j hj => by rw [Nat.le_zero.1 hj]; rfl⟩
  | k + 1, x, hx, t => by
    have hgen := hA.generator_group
    have hS : hA.group.S t x ∈ A.domain := mem_domain_of_generator hgen hx.1 t
    have hw : extOp A (hA.group.S t x) = hA.group.S t (extOp A x) := by
      rw [extOp_eq hS, extOp_eq hx.1]
      exact generator_apply_S_of_eq hgen hx.1 t hS
    obtain ⟨ih1, ih2⟩ := memDomainPow_group k hx.2 t
    refine ⟨⟨hS, hw ▸ ih1⟩, fun j hj => ?_⟩
    rcases j with _ | j
    · rfl
    · change (extOp A)^[j] (extOp A (hA.group.S t x)) = hA.group.S t ((extOp A)^[j] (extOp A x))
      rw [hw]
      exact ih2 j (by omega)

/-- **(a) The norms of the powers are conserved**: `‖Aʲ e^{tA} x‖ = ‖Aʲ x‖`, `j ≤ k`. -/
theorem norm_iterate_extOp_group {k : ℕ} {x : E} (hx : MemDomainPow A k x) (t : ℝ) {j : ℕ}
    (hj : j ≤ k) : ‖(extOp A)^[j] (hA.group.S t x)‖ = ‖(extOp A)^[j] x‖ := by
  rw [(memDomainPow_group hA k hx t).2 j hj, hA.isIsometric_group]

/-- **The kernel of `A` is fixed by the group.** -/
theorem group_S_eq_self {z : E} (hz : z ∈ A.domain) (h0 : A ⟨z, hz⟩ = 0) (t : ℝ) :
    hA.group.S t z = z := by
  have hgen := hA.generator_group
  have hz' : z ∈ hA.group.generator.domain := by rw [hgen]; exact hz
  have hg : hA.group.generator ⟨z, hz'⟩ = 0 := by
    rw [LinearPMap.apply_eq_of_eq hgen ⟨z, hz'⟩ ⟨z, hz⟩ rfl, h0]
  have hd : ∀ s, HasDerivAt (fun s => hA.group.S s z) 0 s := fun s => by
    have := hA.group.hasDerivAt_apply ⟨z, hz'⟩ s
    rwa [hg, map_zero] at this
  have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  rw [this]
  simp

/-- **Orthogonality to the kernel**: `⟪e^{tA} x − x, z⟫ = 0` for `z ∈ N(A)`. -/
theorem inner_group_sub_self_ker (x : E) {z : E} (hz : z ∈ A.domain) (h0 : A ⟨z, hz⟩ = 0)
    (t : ℝ) : ⟪hA.group.S t x - x, z⟫ = 0 := by
  rw [inner_sub_left, hA.isIsometric_group.inner_S_left, group_S_eq_self hA hz h0, sub_self]

/-- **`R(A)ᗮ ⊆ N(A)`**: a vector orthogonal to the range is in `D(A*) = D(A)` with
`A x = −A* x = 0`. -/
theorem mem_ker_of_forall_inner_eq_zero (hD : Dense (A.domain : Set E)) {z : E}
    (h : ∀ y : A.domain, ⟪z, A y⟫ = 0) : z ∈ A.ker := by
  obtain ⟨hz, hb⟩ := exists_mem_adjoint_of_abs_le A hD le_rfl (y := z) fun y => by
    rw [h y, abs_zero, zero_mul]
  have e : A† = -A := hA
  have hz' : z ∈ (-A).domain := mem_domain_of_eq_op e.symm hz
  have hn := norm_apply_of_eq_op e.symm hz
  rw [LinearPMap.neg_apply, norm_neg] at hn
  exact LinearPMap.mem_ker_iff.2 ⟨⟨z, hz'⟩, rfl, norm_le_zero_iff.1 (hn.trans_le hb)⟩

/-- **`R(A) ⊆ N(A)ᗮ`** (skew-symmetry). -/
theorem mem_orthogonal_ker (y : A.domain) : A y ∈ (A.ker)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨u', rfl, hu0⟩ := LinearPMap.mem_ker_iff.1 hu
  have hs := hA.isSkewSymmetric u' y
  rw [hu0, inner_zero_left] at hs
  linarith

/-- **`N(A)ᗮ = cl R(A)`, in the form used here**: a closed subspace containing `R(A)` contains
`N(A)ᗮ`. -/
theorem orthogonal_ker_le (hD : Dense (A.domain : Set E)) {K : Submodule ℝ E}
    (hK : IsClosed (K : Set E)) (hR : ∀ y : A.domain, A y ∈ K) : (A.ker)ᗮ ≤ K := by
  have : CompleteSpace K := hK.completeSpace_coe
  have hsub : Kᗮ ≤ A.ker := fun w hw =>
    mem_ker_of_forall_inner_eq_zero hA hD fun y => Submodule.inner_left_of_mem_orthogonal (hR y) hw
  intro z hz
  have := Submodule.orthogonal_le hsub hz
  rwa [Submodule.orthogonal_orthogonal] at this

/-- `orthogonal_ker_le` for the preimage of the kernel of a closed operator. -/
theorem mem_ker_of_mem_orthogonal_ker {G H : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (hD : Dense (A.domain : Set E)) (f : E →L[ℝ] G) (S : G →ₗ.[ℝ] H) (hS : S.IsClosed)
    (hR : ∀ y : A.domain, f (A y) ∈ S.ker) {z : E} (hz : z ∈ (A.ker)ᗮ) : f z ∈ S.ker :=
  orthogonal_ker_le hA hD (K := (S.ker).comap (f : E →ₗ[ℝ] G)) ((LinearPMap.isClosed_ker hS).preimage f.continuous)
    hR hz

/-- **The orthogonal projection onto `N(A)`** (closed, `A` being closed). -/
def projKerOf : E →L[ℝ] E :=
  haveI : CompleteSpace A.ker := (LinearPMap.isClosed_ker hA.isClosed).completeSpace_coe
  A.ker.starProjection

theorem projKerOf_mem_ker (x : E) : projKerOf hA x ∈ A.ker := by
  have : CompleteSpace A.ker := (LinearPMap.isClosed_ker hA.isClosed).completeSpace_coe
  exact Submodule.starProjection_apply_mem _ x

theorem sub_projKerOf_mem_orthogonal (x : E) : x - projKerOf hA x ∈ (A.ker)ᗮ := by
  have : CompleteSpace A.ker := (LinearPMap.isClosed_ker hA.isClosed).completeSpace_coe
  exact Submodule.sub_starProjection_mem_orthogonal x

theorem projKerOf_eq_zero {x : E} (hx : x ∈ (A.ker)ᗮ) : projKerOf hA x = 0 := by
  have : CompleteSpace A.ker := (LinearPMap.isClosed_ker hA.isClosed).completeSpace_coe
  exact (Submodule.starProjection_apply_eq_zero_iff _).2 hx

theorem projKerOf_smul_eq_zero (c : ℝ) (y : A.domain) : projKerOf hA (c • A y) = 0 :=
  projKerOf_eq_zero hA (Submodule.smul_mem _ c (mem_orthogonal_ker hA y))

/-- **The stationary part is conserved by the group**: `P_{N(A)} e^{tA} x = P_{N(A)} x`. -/
theorem projKerOf_group (x : E) (t : ℝ) : projKerOf hA (hA.group.S t x) = projKerOf hA x := by
  have h : hA.group.S t x - x ∈ (A.ker)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    obtain ⟨u', rfl, hu0⟩ := LinearPMap.mem_ker_iff.1 hu
    exact inner_group_sub_self_ker hA x u'.2 hu0 t
  have h0 := projKerOf_eq_zero hA h
  rw [map_sub, sub_eq_zero] at h0
  exact h0

end Powers

/-! ### The rows of a point of `D(L)` -/

section Rows

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

theorem dense_D0_domain : Dense (D0.domain : Set W0) := by
  have h := (complexMin 3).dense 0 1
  rwa [complexMin_d01] at h

/-- The field with the single row `w` in position `a`. -/
abbrev single3 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a : Fin 3) (w : V) :
    Wv V := WithLp.toLp 2 (Pi.single a w)

theorem single3_apply_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a : Fin 3)
    (w : V) : single3 a w a = w := by
  change (Pi.single a w : Fin 3 → V) a = w
  exact Pi.single_eq_same _ _

theorem single3_apply_of_ne {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a b : Fin 3} (w : V) (h : b ≠ a) : single3 a w b = 0 := by
  change (Pi.single a w : Fin 3 → V) b = 0
  exact Pi.single_eq_of_ne h _

theorem norm_single3 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a : Fin 3)
    (w : V) : ‖single3 a w‖ = ‖w‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
    Finset.sum_eq_single a (fun b _ hb => by rw [single3_apply_of_ne w hb, norm_zero]; ring)
      (by simp), single3_apply_self]

theorem inner_single3_right {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : Wv V) (a : Fin 3) (w : V) : ⟪u, single3 a w⟫ = ⟪u a, w⟫ := by
  rw [inner_Vt, Finset.sum_eq_single a (fun b _ hb => by
    rw [single3_apply_of_ne w hb, inner_zero_right]) (by simp), single3_apply_self]

theorem norm_segS0_le (ψ : Wv U0) : ‖bggSegment.S0 ψ‖ ≤ ‖ψ‖ := by
  have h := norm_wsL2_zero_incl0_sq_le ψ
  rw [← norm_segS0] at h
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h

theorem norm_segS1_le (v : Wv U1) : ‖bggSegment.S1 v‖ ≤ √2 * ‖v‖ := by
  have h := norm_wsL2_one_incl1_sq_le v
  have h' : ‖bggSegment.S1 v‖ ^ 2 ≤ (√2 * ‖v‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; exact h
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h'

set_option maxHeartbeats 2000000

variable {z : WS} (hz : z ∈ formsShort.wave.domain)
include hz

/-- **`d₁* x₂` against `Ṽ¹`**: `⟪d₁* (M, ρ), v⟫ = ⟪M, S¹v⟫ + ⟪ρ, dv⟫`. -/
theorem inner_D1L_adjoint (v : Wv U1) :
    ⟪bggHilb.D1L† ⟨comp2 z, dom2 hz⟩, incl1 v⟫ =
      ⟪compML z, bggSegment.S1 v⟫ + ⟪compρL z, bggSegment.dt1 v⟫ := by
  have hv : ιt1 (toGraphVec1 v) ∈ bggHilb.D1L.domain := by
    rw [bggHilb.D1L_domain]; exact ⟨toGraphVec1 v, rfl⟩
  have hadj := LinearPMap.adjoint_isFormalAdjoint formsShort.dense₁ ⟨comp2 z, dom2 hz⟩
    ⟨ιt1 (toGraphVec1 v), hv⟩
  change ⟪bggHilb.D1L† ⟨comp2 z, dom2 hz⟩, ιt1 (toGraphVec1 v)⟫ =
    ⟪comp2 z, bggHilb.D1L ⟨ιt1 (toGraphVec1 v), hv⟩⟫ at hadj
  rw [D1L_apply_ιt1, ιt1_toGraphVec1] at hadj
  have hTL : WithLp.ofLp (bggHilb.TL (toGraphVec1 v)) = (segS1 v, piMap segD1 v) := rfl
  rw [WithLp.prod_inner_apply, hTL] at hadj
  rw [hadj, compML_apply, compρL_apply]
  rfl

/-- **(c) The magnetic rows of a point of `D(L)` are in `D(d¹*)`**: `ρₐ ∈ D((d¹)*)` with
`‖(d¹)* ρₐ‖ ≤ ‖d₁* x₂‖ + √2 ‖M‖`. -/
theorem rowρ_mem_adjoint (a : Fin 3) :
    ∃ h : compρL z a ∈ (D1†).domain, ‖D1† ⟨_, h⟩‖ ≤
      ‖bggHilb.D1L† ⟨comp2 z, dom2 hz⟩‖ + √2 * ‖compML z‖ := by
  refine exists_mem_adjoint_of_abs_le D1 dense_D1_domain (by positivity) fun w => ?_
  have e := inner_D1L_adjoint hz (single3 a w)
  have e2 : ⟪compρL z, bggSegment.dt1 (single3 a w)⟫ = ⟪compρL z a, D1 w⟫ := by
    have : bggSegment.dt1 (single3 a w) = single3 a (D1 w) := by
      refine PiLp.ext fun b => ?_
      change D1 (single3 a w b) = single3 a (D1 w) b
      by_cases hb : b = a
      · subst hb; rw [single3_apply_self, single3_apply_self]
      · rw [single3_apply_of_ne _ hb, single3_apply_of_ne _ hb, LinearPMap.map_zero]
    rw [this, inner_single3_right]
  rw [e2] at e
  have hw : ‖single3 a w‖ = ‖(w : W1)‖ := norm_single3 a w
  have h1 := abs_real_inner_le_norm (bggHilb.D1L† ⟨comp2 z, dom2 hz⟩) (incl1 (single3 a w))
  have h2 := abs_real_inner_le_norm (compML z) (bggSegment.S1 (single3 a w))
  rw [norm_incl1, hw] at h1
  have h3 := norm_segS1_le (single3 a w)
  rw [hw] at h3
  have h4 : ⟪compρL z a, D1 w⟫ = ⟪bggHilb.D1L† ⟨comp2 z, dom2 hz⟩, incl1 (single3 a w)⟫ -
      ⟪compML z, bggSegment.S1 (single3 a w)⟫ := by rw [e]; ring
  rw [h4]
  have h5 : ‖compML z‖ * ‖bggSegment.S1 (single3 a w)‖ ≤ ‖compML z‖ * (√2 * ‖(w : W1)‖) :=
    mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  calc |_ - _| ≤ |⟪bggHilb.D1L† ⟨comp2 z, dom2 hz⟩, incl1 (single3 a w)⟫| +
        |⟪compML z, bggSegment.S1 (single3 a w)⟫| := abs_sub _ _
    _ ≤ _ := by nlinarith [norm_nonneg (compML z), norm_nonneg (w : W1)]

/-- **(b) An `L²`-bounded multiplier puts the rows of the electric field in `D(d⁰*)`** (one
direction; the converse is not proved here): `|ℓ μ| ≤ Λ ‖μ‖` for the multiplier `ℓ = multOf σ' u` of the point gives
`uₐ ∈ D((d⁰)*)` (`div uₐ ∈ L²`) with `‖(d⁰)* uₐ‖ ≤ Λ`. -/
theorem rowu_mem_adjoint_of_mult {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hℓ : ∀ μ : U1, |multOf (aOf z) (bOf z) μ| ≤ Λ * ‖μ‖) (a : Fin 3) :
    ∃ h : comp1 z a ∈ (D0†).domain, ‖D0† ⟨_, h⟩‖ ≤ Λ := by
  refine exists_mem_adjoint_of_abs_le D0 dense_D0_domain hΛ fun τ => ?_
  have hrep := isMultRep_multOf (inner_sub_inner_eq_zero hz) 0 (single3 a τ)
  have e1 : bggSegment.d0 0 - bggSegment.S0 (single3 a τ) = -bggSegment.S0 (single3 a τ) := by
    rw [map_zero, zero_sub]
  rw [e1, map_neg] at hrep
  have e2 : ⟪bOf z, incl1 (bggSegment.dt0 (single3 a τ))⟫ = ⟪comp1 z a, D0 τ⟫ := by
    have : incl1 (bggSegment.dt0 (single3 a τ)) = single3 a (D0 τ) := by
      refine PiLp.ext fun b => ?_
      change D0 (single3 a τ b) = single3 a (D0 τ) b
      by_cases hb : b = a
      · subst hb; rw [single3_apply_self, single3_apply_self]
      · rw [single3_apply_of_ne _ hb, single3_apply_of_ne _ hb, LinearPMap.map_zero]
    rw [this, inner_single3_right]; rfl
  have e3 : ⟪comp1 z a, D0 τ⟫ = multOf (aOf z) (bOf z) (bggSegment.S0 (single3 a τ)) := by
    rw [← e2]
    have : ⟪aOf z, ((0 : U0) : W0)⟫ = 0 := by simp
    linarith
  rw [e3]
  refine (hℓ _).trans (mul_le_mul_of_nonneg_left ?_ hΛ)
  have h := norm_segS0_le (single3 a τ)
  rw [norm_single3] at h
  exact h

/-- **The coupling `d₁* x₂` is in `D(d⁰*)` row by row when `M ∈ D(d¹*)`**:
`⟪(d₁* x₂)ₐ, dτ⟫ = ⟪M, S¹ d(τ eₐ)⟫ = −⟪M, d S⁰(τ eₐ)⟫ = −⟪(d¹)* M, S⁰(τ eₐ)⟫`
(the anticommutation `d S⁰ = −S¹ d` and `d d = 0`), so `‖(d⁰)* (d₁* x₂)ₐ‖ ≤ ‖(d¹)* M‖`. -/
theorem rowD1Ladj_mem_adjoint (hM : compML z ∈ (D1†).domain) (a : Fin 3) :
    ∃ h : (bggHilb.D1L† ⟨comp2 z, dom2 hz⟩) a ∈ (D0†).domain, ‖D0† ⟨_, h⟩‖ ≤ ‖D1† ⟨_, hM⟩‖ := by
  refine exists_mem_adjoint_of_abs_le D0 dense_D0_domain (norm_nonneg _) fun τ => ?_
  have e := inner_D1L_adjoint hz (bggSegment.dt0 (single3 a τ))
  have e1 : incl1 (bggSegment.dt0 (single3 a τ)) = single3 a (D0 τ) := by
    refine PiLp.ext fun b => ?_
    change D0 (single3 a τ b) = single3 a (D0 τ) b
    by_cases hb : b = a
    · subst hb; rw [single3_apply_self, single3_apply_self]
    · rw [single3_apply_of_ne _ hb, single3_apply_of_ne _ hb, LinearPMap.map_zero]
  rw [e1, inner_single3_right, bggSegment.dt1_dt0, inner_zero_right, add_zero] at e
  have e2 : bggSegment.S1 (bggSegment.dt0 (single3 a τ)) =
      -bggSegment.d1 (bggSegment.S0 (single3 a τ)) := by
    rw [bggSegment.anticomm, neg_neg]
  rw [e2, inner_neg_right] at e
  have hadj := LinearPMap.adjoint_isFormalAdjoint dense_D1_domain ⟨_, hM⟩
    (bggSegment.S0 (single3 a τ))
  change ⟪D1† ⟨_, hM⟩, ((bggSegment.S0 (single3 a τ) : U1) : W1)⟫ =
    ⟪compML z, bggSegment.d1 (bggSegment.S0 (single3 a τ))⟫ at hadj
  change ⟪(bggHilb.D1L† ⟨comp2 z, dom2 hz⟩) a, D0 τ⟫ = _ at e
  rw [e, ← hadj, abs_neg]
  refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have h := norm_segS0_le (single3 a τ)
  rw [norm_single3] at h
  exact h

end Rows

/-! ### The minimal `d²`, and the kernel of `L` -/

section Kernel

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

set_option maxHeartbeats 2000000

/-- The inner product of the total space (`InnerProductSpace.toInner`; not found by instance
search through the `PiLp` instances with the shortcut instances removed). -/
local instance instInnerWS : Inner ℝ WS := InnerProductSpace.toInner

theorem apply_eq_zero_of_coe_eq_zero {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {f : E →ₗ.[ℝ] F} (x : f.domain) (hx : (x : E) = 0) : f x = 0 := by
  have : x = 0 := Subtype.ext hx
  rw [this, LinearPMap.map_zero]

theorem complexMin_d23 : (complexMin 3).d 2 3 = D2min :=
  deRham_minimalComplex_d (isOpen_cubeDomain 3) 2

/-- `d¹ w ∈ D(d²)` with `d² d¹ w = 0`. -/
theorem D1_mem_D2min (w : U1) : D1 w ∈ D2min.domain := by
  have h := (complexMin 3).mapsTo 1 2 3 ⟨w, by rw [complexMin_d12]; exact w.2⟩
  rw [LinearPMap.apply_eq_of_eq complexMin_d12 _ w rfl] at h
  exact mem_domain_of_eq_op complexMin_d23.symm h

theorem D2min_D1 (w : U1) : D2min ⟨D1 w, D1_mem_D2min w⟩ = 0 := by
  have h := (complexMin 3).d_comp_d 1 2 3 ⟨w, by rw [complexMin_d12]; exact w.2⟩
  have e1 : (complexMin 3).d 1 2 ⟨w, by rw [complexMin_d12]; exact w.2⟩ = D1 w :=
    LinearPMap.apply_eq_of_eq complexMin_d12 _ w rfl
  rw [← LinearPMap.apply_eq_of_eq complexMin_d23
    ⟨_, (complexMin 3).mapsTo 1 2 3 ⟨w, by rw [complexMin_d12]; exact w.2⟩⟩ _ e1]
  exact h

/-- **The orthogonal of `N((d¹)*)` lies in `N(d²)`** (`HilbertComplex.orthogonal_ker_adjoint_le_ker`
for `H̊Λ(Q)`): no closed range is needed. -/
theorem mem_D2min_of_mem_orthogonal {y : W2} (hy : y ∈ ((D1†).ker)ᗮ) :
    ∃ h : y ∈ D2min.domain, D2min ⟨y, h⟩ = 0 := by
  have h := (complexMin 3).orthogonal_ker_adjoint_le_ker 1 2 3 (by rw [complexMin_d12]; exact hy)
  obtain ⟨y', hy', h0⟩ := LinearPMap.mem_ker_iff.1 h
  have hd : y ∈ D2min.domain := by
    rw [hy']; exact mem_domain_of_eq_op complexMin_d23.symm y'.2
  refine ⟨hd, ?_⟩
  rw [← LinearPMap.apply_eq_of_eq complexMin_d23 y' ⟨y, hd⟩ hy'.symm]
  exact h0

/-- The pairing of the magnetic slot with `D(d₁)`: every `y ∈ D(d₁)` is `ιt1 v'`, and
`⟪w, d₁ y⟫ = ⟪w_M, S¹ v'⟫ + ⟪w_ρ, d v'⟫`. -/
theorem inner_comp2_D1L (w : WithLp 2 (W2 × Wv W2)) (y : bggHilb.D1L.domain) :
    ∃ v' : Wv U1, (y : Wv W1) = incl1 v' ∧
      ⟪w, bggHilb.D1L y⟫ = ⟪(WithLp.ofLp w).1, bggSegment.S1 v'⟫ +
        ⟪(WithLp.ofLp w).2, bggSegment.dt1 v'⟫ := by
  obtain ⟨v, hv⟩ := mem_range_of_mem_D1L y.2
  refine ⟨rp1 v, by rw [incl1_rp1]; exact hv.symm, ?_⟩
  have hv' : ιt1 (toGraphVec1 (rp1 v)) ∈ bggHilb.D1L.domain := by
    rw [bggHilb.D1L_domain]; exact ⟨toGraphVec1 (rp1 v), rfl⟩
  have e : bggHilb.D1L y = bggHilb.D1L ⟨ιt1 (toGraphVec1 (rp1 v)), hv'⟩ :=
    LinearPMap.apply_congr' _ y.2 hv' (by rw [ιt1_toGraphVec1, incl1_rp1]; exact hv.symm)
  rw [e, D1L_apply_ιt1]
  have hTL : WithLp.ofLp (bggHilb.TL (toGraphVec1 (rp1 v))) =
      (segS1 (rp1 v), piMap segD1 (rp1 v)) := rfl
  rw [WithLp.prod_inner_apply, hTL]
  rfl

/-- **The kernel elements `(0, 0, (0, q eₐ))`**, `q ∈ N((d¹)*)`. -/
def kerRho (a : Fin 3) (q : W2) : WS :=
  ShortHilbertComplex.mk3 (0 : bggHilb.Γbar) (0 : Wv W1)
    (WithLp.toLp 2 ((0 : W2), single3 a q) : WithLp 2 (W2 × Wv W2))

theorem kerRho_comp2_mem {a : Fin 3} {q : W2} (hq : q ∈ (D1†).domain) (hq0 : D1† ⟨q, hq⟩ = 0) :
    ∃ h : comp2 (kerRho a q) ∈ (bggHilb.D1L†).domain, bggHilb.D1L† ⟨_, h⟩ = 0 := by
  obtain ⟨h, hb⟩ := exists_mem_adjoint_of_abs_le bggHilb.D1L formsShort.dense₁ le_rfl
    (y := comp2 (kerRho a q)) fun y => by
      obtain ⟨v', -, e⟩ := inner_comp2_D1L (comp2 (kerRho a q)) y
      rw [e]
      change |⟪(0 : W2), bggSegment.S1 v'⟫ + ⟪single3 a q, bggSegment.dt1 v'⟫| ≤ 0 * _
      rw [inner_zero_left, zero_add, real_inner_comm, inner_single3_right]
      change |⟪D1 (v' a), q⟫| ≤ _
      have hadj := LinearPMap.adjoint_isFormalAdjoint dense_D1_domain ⟨q, hq⟩ (v' a)
      rw [real_inner_comm, ← hadj, hq0, inner_zero_left, abs_zero, zero_mul]
  exact ⟨h, norm_le_zero_iff.1 hb⟩

/-- **`(0, 0, (0, q eₐ)) ∈ N(L)`** for `q ∈ N((d¹)*)`: a stationary state of the Hodge wave
equation (`d₁* (0, q eₐ) = 0`, `⟪q, d w⟫ = 0`). -/
theorem kerRho_mem_ker {a : Fin 3} {q : W2} (hq : q ∈ (D1†).domain) (hq0 : D1† ⟨q, hq⟩ = 0) :
    kerRho a q ∈ formsShort.wave.domain ∧ waveOf (kerRho a q) = 0 := by
  obtain ⟨h2, h20⟩ := kerRho_comp2_mem hq hq0
  have hdom : kerRho a q ∈ formsShort.wave.domain :=
    formsShort.mem_wave_domain.2 ⟨Submodule.zero_mem _, Submodule.zero_mem _,
      Submodule.zero_mem _, h2⟩
  refine ⟨hdom, ?_⟩
  have c0 : comp0 (waveOf (kerRho a q)) = 0 := by
    rw [comp0_waveOf hdom, apply_eq_zero_of_coe_eq_zero _ rfl, neg_zero]
  have c1 : comp1 (waveOf (kerRho a q)) = 0 := by
    rw [comp1_waveOf hdom, apply_eq_zero_of_coe_eq_zero (f := bggHilb.D0Γ) _ rfl, zero_sub,
      neg_eq_zero]
    exact h20
  have c2 : comp2 (waveOf (kerRho a q)) = 0 := by
    rw [comp2_waveOf hdom, apply_eq_zero_of_coe_eq_zero _ rfl]
  rw [← ShortHilbertComplex.mk3_eta (waveOf (kerRho a q))]
  change ShortHilbertComplex.mk3 (comp0 (waveOf (kerRho a q))) (comp1 (waveOf (kerRho a q)))
    (comp2 (waveOf (kerRho a q))) = 0
  rw [c0, c1, c2]
  refine PiLp.ext fun i => ?_
  fin_cases i <;> rfl

end Kernel

/-! ### The Sobolev regularity of a point of `D(L)` -/

section State

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

set_option maxHeartbeats 2000000

theorem sqrt_sq_add_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a ^ 2 + b ^ 2) ≤ a + b :=
  Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩

theorem sqrt_sq_add_sq_add_sq_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    √(a ^ 2 + b ^ 2 + c ^ 2) ≤ a + b + c :=
  Real.sqrt_le_iff.2 ⟨by positivity, by
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]⟩

theorem norm_comp0_le (z : WS) : ‖((comp0 z : bggHilb.Γbar) : W0)‖ ≤ ‖z‖ :=
  PiLp.norm_apply_le z 0

theorem norm_comp1_le (z : WS) : ‖comp1 z‖ ≤ ‖z‖ := PiLp.norm_apply_le z 1

theorem norm_comp2_le (z : WS) : ‖comp2 z‖ ≤ ‖z‖ := PiLp.norm_apply_le z 2

theorem norm_compML_le (z : WS) : ‖compML z‖ ≤ ‖z‖ :=
  (WithLp.norm_fst_le (x := comp2 z)).trans (norm_comp2_le z)

theorem norm_compρL_le (z : WS) : ‖compρL z‖ ≤ ‖z‖ :=
  (WithLp.norm_snd_le (x := comp2 z)).trans (norm_comp2_le z)

theorem norm_row_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (u : Wv V)
    (a : Fin 3) : ‖u a‖ ≤ ‖u‖ := PiLp.norm_apply_le u a

variable {z : WS} (hz : z ∈ formsShort.wave.domain)
include hz

omit hz in
theorem norm_projK_comp1_le : ‖projK (comp1 (waveOf z))‖ ≤ ‖waveOf z‖ :=
  (Submodule.norm_starProjection_apply_le _ _).trans (norm_comp1_le _)

/-- `‖d₁* x₂‖ ≤ 2 ‖L x‖` (`(L x)₁ = d₀ x₀ − d₁* x₂` and `d₀ x₀ = P (L x)₁`). -/
theorem norm_D1Ladj_le : ‖bggHilb.D1L† ⟨comp2 z, dom2 hz⟩‖ ≤ 2 * ‖waveOf z‖ := by
  have e := comp1_waveOf hz
  have e2 : bggHilb.D1L† ⟨comp2 z, dom2 hz⟩ =
      bggHilb.D0Γ ⟨comp0 z, dom0 hz⟩ - comp1 (waveOf z) := by rw [e]; abel
  rw [e2, ← projK_comp1_waveOf hz]
  refine (norm_sub_le _ _).trans ?_
  linarith [norm_projK_comp1_le (z := z), norm_comp1_le (waveOf z)]

/-- **(b) `σ ∈ H¹_univ`** with `‖σ‖_{1,univ} ≤ ‖x‖ + ‖L x‖` (`σ ∈ H̊Λ⁰(Q)`, `dσ = S⁰φ`,
`‖φ‖ ≤ (2π)⁻¹ ‖dφ‖` and `dφ = −P (L x)₁`). -/
theorem sobRel_σOf : SobRel 1 (‖z‖ + ‖waveOf z‖) 0 ((D0.graphDom (σOf z) : U0) : W0) := by
  have h := sobRel_zero_of_mem (x := ((D0.graphDom (σOf z) : U0) : W0)) (D0.graphDom (σOf z)).2
  refine h.mono ?_
  have h1 : ‖((D0.graphDom (σOf z) : U0) : W0)‖ ≤ ‖z‖ := by
    rw [coe_graphDom_σOf hz, norm_neg]; exact norm_comp0_le z
  have h2 : ‖D0 ⟨_, (D0.graphDom (σOf z)).2⟩‖ ≤ ‖waveOf z‖ := by
    have e := congrArg (fun y : U1 => (y : W1)) (d0_graphDom_σOf_eq z)
    change D0 (D0.graphDom (σOf z)) = _ at e
    change ‖D0 (D0.graphDom (σOf z))‖ ≤ _
    rw [e]
    have hS := norm_segS0_le (rp (φOf z))
    have hP := seg_poinct0 (rp (φOf z))
    have hd : ‖piMap segD0 (rp (φOf z))‖ = ‖projK (comp1 (waveOf z))‖ := by
      rw [← norm_neg (projK _), ← incl1_dt0_φOf hz, norm_incl1]; rfl
    have hpi : (2 * Real.pi)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]; nlinarith [Real.two_le_pi]
    calc ‖((bggSegment.S0 (rp (φOf z)) : U1) : W1)‖ ≤ ‖rp (φOf z)‖ := hS
      _ ≤ (2 * Real.pi)⁻¹ * ‖piMap segD0 (rp (φOf z))‖ := hP
      _ ≤ 1 * ‖projK (comp1 (waveOf z))‖ := by
          rw [hd]; exact mul_le_mul_of_nonneg_right hpi (norm_nonneg _)
      _ ≤ ‖waveOf z‖ := by rw [one_mul]; exact norm_projK_comp1_le
  exact (sqrt_sq_add_sq_le (norm_nonneg _) (norm_nonneg _)).trans (add_le_add h1 h2)

/-- The rows of `dφ` (the Hessian of `σ`): `d φₐ = −((L x)₁ₐ + (d₁* x₂)ₐ)`. -/
theorem D0_rp_φOf (a : Fin 3) :
    D0 (rp (φOf z) a) = -((comp1 (waveOf z)) a + (bggHilb.D1L† ⟨comp2 z, dom2 hz⟩) a) := by
  have e1 := incl1_dt0_φOf hz
  rw [projK_comp1_waveOf hz] at e1
  have e2 : bggHilb.D0Γ ⟨comp0 z, dom0 hz⟩ =
      comp1 (waveOf z) + bggHilb.D1L† ⟨comp2 z, dom2 hz⟩ := by rw [comp1_waveOf hz]; abel
  rw [e2] at e1
  have := congrArg (fun y : Wv W1 => y a) e1
  exact this

/-- **(b) The rows of `dφ` are in `H¹_univ`** when the multiplier of `L x` is `L²`-bounded and
`M ∈ D(d¹*)`: `dφₐ ∈ D(d¹) ∩ D(d⁰*)` (`d dφₐ = 0`; `rowu_mem_adjoint_of_mult`,
`rowD1Ladj_mem_adjoint`) and Gaffney. -/
theorem sobRel_D0_φOf (hLz : waveOf z ∈ formsShort.wave.domain) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hℓ' : ∀ μ : U1, |multOf (aOf (waveOf z)) (bOf (waveOf z)) μ| ≤ Λ * ‖μ‖)
    (hM : compML z ∈ (D1†).domain) (hMb : ‖D1† ⟨_, hM⟩‖ ≤ Λ) (a : Fin 3) :
    SobRel 1 (‖waveOf z‖ + 2 * Λ) 1 (D0 (rp (φOf z) a)) := by
  obtain ⟨h1, hb1⟩ := rowu_mem_adjoint_of_mult hLz hΛ hℓ' a
  obtain ⟨h2, hb2⟩ := rowD1Ladj_mem_adjoint hz hM a
  have hmem : D0 (rp (φOf z) a) ∈ (D0†).domain := by
    rw [D0_rp_φOf hz a]
    exact Submodule.neg_mem _ (Submodule.add_mem _ h1 h2)
  have hval : D0† ⟨_, hmem⟩ = -(D0† ⟨_, h1⟩ + D0† ⟨_, h2⟩) := by
    have e : (⟨D0 (rp (φOf z) a), hmem⟩ : (D0†).domain) = -((⟨_, h1⟩ : (D0†).domain) + ⟨_, h2⟩) :=
      Subtype.ext (D0_rp_φOf hz a)
    rw [e, LinearPMap.map_neg, LinearPMap.map_add]
  have h := sobRel_one_of_mem (x := D0 (rp (φOf z) a)) (D0_mem_D1 _) hmem
  refine h.mono ?_
  rw [D1_D0, norm_zero, hval, norm_neg]
  have hn : ‖D0 (rp (φOf z) a)‖ ≤ ‖waveOf z‖ := by
    calc ‖D0 (rp (φOf z) a)‖ = ‖(incl1 (bggSegment.dt0 (rp (φOf z)))) a‖ := rfl
      _ ≤ ‖incl1 (bggSegment.dt0 (rp (φOf z)))‖ := norm_row_le _ a
      _ = ‖projK (comp1 (waveOf z))‖ := by rw [incl1_dt0_φOf hz, norm_neg]
      _ ≤ ‖waveOf z‖ := norm_projK_comp1_le
  have hs := sqrt_sq_add_sq_add_sq_le (norm_nonneg (D0 (rp (φOf z) a))) (le_refl (0 : ℝ))
    (norm_nonneg (D0† ⟨_, h1⟩ + D0† ⟨_, h2⟩))
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num] at hs
  refine (by simpa using hs : _ ≤ _).trans ?_
  have := norm_add_le (D0† ⟨_, h1⟩) (D0† ⟨_, h2⟩)
  linarith

/-- **(b) The rows of the electric field are in `H¹_univ`** when the multiplier is `L²`-bounded:
`uₐ ∈ H̊(curl) ∩ H(div)` and Gaffney. -/
theorem sobRel_uOf {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hℓ : ∀ μ : U1, |multOf (aOf z) (bOf z) μ| ≤ Λ * ‖μ‖) (a : Fin 3) :
    SobRel 1 (‖z‖ + ‖waveOf z‖ + Λ) 1 ((uOf z a : U1) : W1) := by
  have hrow : ((uOf z a : U1) : W1) = comp1 z a := by
    have := congrArg (fun y : Wv W1 => y a) (incl1_uOf (dom1 hz))
    exact this
  obtain ⟨h1, hb1⟩ := rowu_mem_adjoint_of_mult hz hΛ hℓ a
  have h1' : ((uOf z a : U1) : W1) ∈ (D0†).domain := by rw [hrow]; exact h1
  have h := sobRel_one_of_mem (x := ((uOf z a : U1) : W1)) (uOf z a).2 h1'
  refine h.mono ?_
  have hu : ‖((uOf z a : U1) : W1)‖ ≤ ‖z‖ := by
    rw [hrow]; exact (norm_row_le _ a).trans (norm_comp1_le z)
  have hdu : ‖D1 ⟨_, (uOf z a).2⟩‖ ≤ ‖waveOf z‖ :=
    calc ‖D1 ⟨_, (uOf z a).2⟩‖ = ‖(bggSegment.dt1 (uOf z)) a‖ := rfl
      _ ≤ ‖bggSegment.dt1 (uOf z)‖ := norm_row_le _ a
      _ = ‖compρL (waveOf z)‖ := by rw [dt1_uOf hz]
      _ ≤ ‖waveOf z‖ := norm_compρL_le _
  have hdiv : ‖D0† ⟨_, h1'⟩‖ ≤ Λ := by
    have e : D0† ⟨_, h1'⟩ = D0† ⟨_, h1⟩ := LinearPMap.apply_congr' _ _ _ hrow
    rw [e]; exact hb1
  exact (sqrt_sq_add_sq_add_sq_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)).trans
    (add_le_add (add_le_add hu hdu) hdiv)

/-- **(c) The rows of `du` are in `H¹_univ`**: `duₐ = ρ'ₐ ∈ N(d²) ∩ D(d¹*)` for `L x ∈ D(L)`. -/
theorem sobRel_D1_uOf (hLz : waveOf z ∈ formsShort.wave.domain) (a : Fin 3) :
    SobRel 1 (‖waveOf z‖ + 2 * ‖waveOf (waveOf z)‖ + √2 * ‖waveOf z‖) 2 (D1 (uOf z a)) := by
  have hrow : D1 (uOf z a) = compρL (waveOf z) a := by
    have := congrArg (fun y : Wv W2 => y a) (dt1_uOf hz)
    exact this
  obtain ⟨h1, hb1⟩ := rowρ_mem_adjoint hLz a
  have h1' : D1 (uOf z a) ∈ (D1†).domain := by rw [hrow]; exact h1
  have h := sobRel_two_of_mem (x := D1 (uOf z a)) (D1_mem_D2min _) h1'
  refine h.mono ?_
  rw [D2min_D1, norm_zero]
  have hn : ‖D1 (uOf z a)‖ ≤ ‖waveOf z‖ := by
    rw [hrow]; exact (norm_row_le _ a).trans (norm_compρL_le _)
  have hd : ‖D1† ⟨_, h1'⟩‖ ≤ 2 * ‖waveOf (waveOf z)‖ + √2 * ‖waveOf z‖ := by
    have e : D1† ⟨_, h1'⟩ = D1† ⟨_, h1⟩ := LinearPMap.apply_congr' _ _ _ hrow
    rw [e]
    refine hb1.trans (add_le_add (norm_D1Ladj_le hLz) ?_)
    exact mul_le_mul_of_nonneg_left (norm_compML_le _) (Real.sqrt_nonneg _)
  have hs := sqrt_sq_add_sq_add_sq_le (norm_nonneg (D1 (uOf z a))) (le_refl (0 : ℝ))
    (norm_nonneg (D1† ⟨_, h1'⟩))
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num] at hs
  refine (by simpa using hs : _ ≤ _).trans ?_
  linarith

/-- **(c) The magnetic rows are in `H¹_univ` once they are in `D(d²)`** (`ρₐ ∈ D(d¹*)` for every
point of `D(L)`). -/
theorem sobRel_compρL (a : Fin 3) {Λ : ℝ} (hρ : compρL z a ∈ D2min.domain)
    (hρb : ‖D2min ⟨_, hρ⟩‖ ≤ Λ) :
    SobRel 1 (‖z‖ + Λ + (2 * ‖waveOf z‖ + √2 * ‖z‖)) 2 (compρL z a) := by
  obtain ⟨h1, hb1⟩ := rowρ_mem_adjoint hz a
  have h := sobRel_two_of_mem (x := compρL z a) hρ h1
  refine h.mono ?_
  have hd : ‖D1† ⟨_, h1⟩‖ ≤ 2 * ‖waveOf z‖ + √2 * ‖z‖ :=
    hb1.trans (add_le_add (norm_D1Ladj_le hz)
      (mul_le_mul_of_nonneg_left (norm_compML_le _) (Real.sqrt_nonneg _)))
  exact (sqrt_sq_add_sq_add_sq_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)).trans
    (add_le_add (add_le_add ((norm_row_le _ a).trans (norm_compρL_le z)) hρb) hd)

omit hz in
/-- **The skew field is in `H¹_univ` once it is in `D(d²) ∩ D(d¹*)`** (Gaffney). -/
theorem sobRel_compML {Λ : ℝ} (hM2 : compML z ∈ D2min.domain) (hM2b : ‖D2min ⟨_, hM2⟩‖ ≤ Λ)
    (hM1 : compML z ∈ (D1†).domain) (hM1b : ‖D1† ⟨_, hM1⟩‖ ≤ Λ) :
    SobRel 1 (‖z‖ + 2 * Λ) 2 (compML z) := by
  have h := sobRel_two_of_mem (x := compML z) hM2 hM1
  refine h.mono ?_
  refine (sqrt_sq_add_sq_add_sq_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)).trans ?_
  linarith [norm_compML_le z]

omit hz in
theorem sqrt_two_le_two : √2 ≤ 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- **The relative-class `H¹` regularity of the state of a point of `D(L)`** (the fields of
`exactOfStrong`): `σ`, `dφₐ`, `uₐ`, `duₐ`, `M`, `ρₐ`, `S¹u` are in `H¹_univ` with norms
`≤ 4 (‖x‖ + ‖Lx‖ + ‖L²x‖ + Λ)`, provided `L x ∈ D(L)`, the multipliers of `x` and `L x` are
`L²`-bounded by `Λ`, the skew fields `M` of `x` and `L x` are in `D(d²) ∩ D(d¹*)` and the
magnetic rows of `x` are in `D(d²)`, with bounds `Λ`. -/
theorem isSobolevStateTr_of_mem (hLz : waveOf z ∈ formsShort.wave.domain) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hℓ : ∀ μ : U1, |multOf (aOf z) (bOf z) μ| ≤ Λ * ‖μ‖)
    (hℓ' : ∀ μ : U1, |multOf (aOf (waveOf z)) (bOf (waveOf z)) μ| ≤ Λ * ‖μ‖)
    (hM2 : compML z ∈ D2min.domain) (hM2b : ‖D2min ⟨_, hM2⟩‖ ≤ Λ)
    (hM1 : compML z ∈ (D1†).domain) (hM1b : ‖D1† ⟨_, hM1⟩‖ ≤ Λ)
    (hM2' : compML (waveOf z) ∈ D2min.domain) (hM2b' : ‖D2min ⟨_, hM2'⟩‖ ≤ Λ)
    (hM1' : compML (waveOf z) ∈ (D1†).domain) (hM1b' : ‖D1† ⟨_, hM1'⟩‖ ≤ Λ)
    (hρ : ∀ a, ∃ h : compρL z a ∈ D2min.domain, ‖D2min ⟨_, h⟩‖ ≤ Λ) :
    IsSobolevStateTr 1 (4 * (‖z‖ + ‖waveOf z‖ + ‖waveOf (waveOf z)‖ + Λ))
      (D0.graphDom (σOf z)) (rp (φOf z)) (uOf z) (compML z) (compρL z) := by
  have h0 := norm_nonneg z
  have h1 := norm_nonneg (waveOf z)
  have h2 := norm_nonneg (waveOf (waveOf z))
  have hs := sqrt_two_le_two
  have hs0 := Real.sqrt_nonneg 2
  refine ⟨(sobRel_σOf hz).mono (by linarith), fun a => (sobRel_D0_φOf hz hLz hΛ hℓ' hM1 hM1b a).mono
    (by linarith), fun a => (sobRel_uOf hz hΛ hℓ a).mono (by linarith),
    fun a => (sobRel_D1_uOf hz hLz a).mono (by nlinarith),
    (sobRel_compML hM2 hM2b hM1 hM1b).mono (by linarith), fun a => ?_, ?_⟩
  · obtain ⟨hρa, hρab⟩ := hρ a
    exact (sobRel_compρL hz a hρa hρab).mono (by nlinarith)
  · rw [segS1_uOf hz]
    exact (sobRel_compML hM2' hM2b' hM1' hM1b').mono (by linarith)

end State

/-! ### Derivatives in a closed subspace -/

section ClosedSub

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **A trajectory whose right derivative lies in a closed subspace `K` moves inside `K`**:
`f(t) − f(0) ∈ K` (project onto `Kᗮ`: the projection has zero right derivative). -/
theorem sub_mem_of_hasDerivWithinAt (K : Submodule ℝ E) (hK : IsClosed (K : Set E)) {f f' : ℝ → E}
    {T : ℝ} (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (f' t) (Ici t) t) (hK' : ∀ t ∈ Ico 0 T, f' t ∈ K) :
    ∀ t ∈ Icc 0 T, f t - f 0 ∈ K := by
  have : CompleteSpace K := hK.completeSpace_coe
  set P := Kᗮ.starProjection
  have hP : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun s => P (f s)) 0 (Ici t) t := fun t ht => by
    have h := P.hasFDerivAt.comp_hasDerivWithinAt t (hd t ht)
    have h0 : P (f' t) = 0 := (Submodule.starProjection_apply_eq_zero_iff _).2
      (Submodule.le_orthogonal_orthogonal K (hK' t ht))
    simpa [Function.comp_def, h0] using h
  have hconst := constant_of_has_deriv_right_zero (P.continuous.comp_continuousOn hc) hP
  intro t ht
  have h1 : P (f t - f 0) = 0 := by rw [map_sub, sub_eq_zero]; exact hconst t ht
  have h2 := (Submodule.starProjection_apply_eq_zero_iff _).1 h1
  rwa [Submodule.orthogonal_orthogonal] at h2

end ClosedSub

/-! ### Orbits of `D(L³)` -/

section Orbit

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

set_option maxHeartbeats 2000000

/-- The orbit `t ↦ e^{tL} U₀` of the forms-model Hodge wave group. -/
def waveOrbit (U₀ : WS) (t : ℝ) : WS := formsShort.isSkewAdjoint_wave.group.S t U₀

theorem extOp_wave : extOp formsShort.wave = waveOf := rfl

theorem waveOrbit_zero (U₀ : WS) : waveOrbit U₀ 0 = U₀ := by
  simp [waveOrbit, (formsShort.isSkewAdjoint_wave.group).map_zero]

variable {U₀ : WS} (hU₀ : MemDomainPow formsShort.wave 3 U₀)
include hU₀

theorem waveOrbit_iterate (t : ℝ) {j : ℕ} (hj : j ≤ 3) :
    waveOf^[j] (waveOrbit U₀ t) =
      formsShort.isSkewAdjoint_wave.group.S t (waveOf^[j] U₀) :=
  (memDomainPow_group formsShort.isSkewAdjoint_wave 3 hU₀ t).2 j hj

theorem waveOrbit_memDomainPow (t : ℝ) : MemDomainPow formsShort.wave 3 (waveOrbit U₀ t) :=
  (memDomainPow_group formsShort.isSkewAdjoint_wave 3 hU₀ t).1

theorem norm_waveOrbit_iterate (t : ℝ) {j : ℕ} (hj : j ≤ 3) :
    ‖waveOf^[j] (waveOrbit U₀ t)‖ = ‖waveOf^[j] U₀‖ :=
  norm_iterate_extOp_group formsShort.isSkewAdjoint_wave hU₀ t hj

theorem waveOrbit_mem (t : ℝ) {j : ℕ} (hj : j < 3) :
    waveOf^[j] (waveOrbit U₀ t) ∈ formsShort.wave.domain :=
  (waveOrbit_memDomainPow hU₀ t).iterate_mem j hj

theorem isStrongSolution_waveOrbit (T : ℝ) :
    Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 (waveOrbit U₀) :=
  isStrongSolution_of_generator formsShort.isSkewAdjoint_wave.generator_group hU₀.1 _

theorem isStrongSolution_waveOf_waveOrbit (T : ℝ) :
    Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 fun t => waveOf (waveOrbit U₀ t) := by
  refine (isStrongSolution_of_generator formsShort.isSkewAdjoint_wave.generator_group hU₀.2.1
    (Icc 0 T)).congr (fun t _ => ?_) fun _ _ => rfl
  exact (waveOrbit_iterate hU₀ t (j := 1) (by norm_num)).symm

theorem continuousOn_waveOf_waveOf_waveOrbit (T : ℝ) :
    ContinuousOn (fun t => waveOf (waveOf (waveOrbit U₀ t))) (Icc 0 T) := by
  refine ((formsShort.isSkewAdjoint_wave.group).strongCont (waveOf (waveOf U₀))).continuousOn.congr
    fun t _ => ?_
  exact waveOrbit_iterate hU₀ t (j := 2) (by norm_num)

/-- **The classical solution of (6.2) of an orbit of `D(L³)`** (`exactOfStrong`). -/
abbrev orbitExact (T : ℝ) : Feec.BGG.ExactWave bggSegment T (srcFun 0) :=
  exactOfStrong (isStrongSolution_waveOrbit hU₀ T) (isStrongSolution_waveOf_waveOrbit hU₀ T)
    (continuousOn_waveOf_waveOf_waveOrbit hU₀ T)

theorem orbitExact_ℓ (T t : ℝ) (μ : U1) :
    (orbitExact hU₀ T).ℓ t μ = multOf (aOf (waveOrbit U₀ t)) (bOf (waveOrbit U₀ t)) μ := rfl

theorem orbitExact_ℓ' (T t : ℝ) (μ : U1) :
    (orbitExact hU₀ T).ℓ' t μ =
      multOf (aOf (waveOf (waveOrbit U₀ t))) (bOf (waveOf (waveOrbit U₀ t))) μ := rfl

theorem orbitExact_M (T t : ℝ) : (orbitExact hU₀ T).M t = compML (waveOrbit U₀ t) := rfl

theorem orbitExact_M' (T t : ℝ) : (orbitExact hU₀ T).M' t = compML (waveOf (waveOrbit U₀ t)) :=
  rfl

/-- **(c) The magnetic rows stay in `D(d²)` along the orbit, with `d²ρₐ(t) = d²ρₐ(0)`**:
`ρ' = du ∈ N(d²)` (`sub_mem_of_hasDerivWithinAt`). -/
theorem compρL_waveOrbit_mem {T : ℝ} {a : Fin 3} {Λ : ℝ}
    (hρ0 : ∃ h : compρL U₀ a ∈ D2min.domain, ‖D2min ⟨_, h⟩‖ ≤ Λ) :
    ∀ t ∈ Icc 0 T, ∃ h : compρL (waveOrbit U₀ t) a ∈ D2min.domain, ‖D2min ⟨_, h⟩‖ ≤ Λ := by
  obtain ⟨h0, hb0⟩ := hρ0
  have hK : IsClosed ((D2min.ker : Submodule ℝ W2) : Set W2) :=
    LinearPMap.isClosed_ker (ConstCoeffOp.isClosed_minimal _ (isOpen_cubeDomain 3))
  set s := orbitExact hU₀ T
  have hc : ContinuousOn (fun r => (s.ρ r) a) (Icc 0 T) :=
    (PiLp.continuous_apply 2 _ a).comp_continuousOn s.cρ
  have hd : ∀ r ∈ Ico 0 T, HasDerivWithinAt (fun r => (s.ρ r) a) ((s.ρ' r) a) (Ici r) r :=
    fun r hr => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => W2) a).hasFDerivAt.comp_hasDerivWithinAt r
      (s.dρ r hr)
  have hK' : ∀ r ∈ Ico 0 T, (s.ρ' r) a ∈ D2min.ker := fun r hr => by
    have hm := waveOrbit_mem hU₀ r (j := 0) (by norm_num)
    have e : (s.ρ' r) a = D1 (uOf (waveOrbit U₀ r) a) := by
      have := congrArg (fun y : Wv W2 => y a) (dt1_uOf hm)
      exact this.symm
    rw [e]
    exact LinearPMap.mem_ker_iff.2 ⟨⟨_, D1_mem_D2min _⟩, rfl, D2min_D1 _⟩
  intro t ht
  have hmem := sub_mem_of_hasDerivWithinAt _ hK hc hd hK' t ht
  obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hmem
  have e0 : (s.ρ 0) a = compρL U₀ a := by
    change compρL (waveOrbit U₀ 0) a = _; rw [waveOrbit_zero]
  have et : (s.ρ t) a = compρL U₀ a + (y : W2) := by rw [← hy, ← e0]; abel
  have hdom : compρL (waveOrbit U₀ t) a ∈ D2min.domain := by
    change (s.ρ t) a ∈ _; rw [et]; exact Submodule.add_mem _ h0 y.2
  refine ⟨hdom, ?_⟩
  have e : D2min ⟨_, hdom⟩ = D2min ⟨_, h0⟩ + D2min y := by
    rw [← LinearPMap.map_add]; exact LinearPMap.apply_congr' _ _ _ et
  rw [e, hy0, add_zero]
  exact hb0

end Orbit

/-! ### The kernel of `L` and its orthogonal: the magnetic rows -/

section KernelPart

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

set_option maxHeartbeats 2000000

/-- The magnetic row map `z ↦ ρₐ(z)`. -/
def rowρ (a : Fin 3) : WS →L[ℝ] W2 := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => W2) a).comp compρL

theorem rowρ_apply (a : Fin 3) (z : WS) : rowρ a z = compρL z a := rfl

/-- **The range of `L` has magnetic rows in `N(d²)`**: `(L y)_ρ = d u_y` row by row, and
`d² d¹ = 0`. -/
theorem rowρ_wave_mem_ker (a : Fin 3) (y : formsShort.wave.domain) :
    rowρ a (formsShort.wave y) ∈ D2min.ker := by
  rw [← waveOf_eq y.2, rowρ_apply]
  have e : compρL (waveOf (y : WS)) a = D1 (uOf (y : WS) a) :=
    (congrArg (fun w : Wv W2 => w a) (dt1_uOf y.2)).symm
  rw [e]
  exact LinearPMap.mem_ker_iff.2 ⟨⟨_, D1_mem_D2min _⟩, rfl, D2min_D1 _⟩

/-- **(c) On `N(L)ᗮ` the magnetic rows are in `N(d²)`**: `N(L)ᗮ = cl R(L)` and `R(L)` lies in the
closed subspace of states whose `a`-th magnetic row is in `N(d²)` (`rowρ_wave_mem_ker`); no
closed range is needed. -/
theorem compρL_mem_ker_of_mem_orthogonal {z : WS} (hz : z ∈ (formsShort.wave.ker)ᗮ)
    (a : Fin 3) : ∃ h : compρL z a ∈ D2min.domain, D2min ⟨_, h⟩ = 0 := by
  have hmem := mem_ker_of_mem_orthogonal_ker formsShort.isSkewAdjoint_wave
    formsShort.toHilbertComplex.dense_wave_domain (rowρ a) D2min
    (ConstCoeffOp.isClosed_minimal _ (isOpen_cubeDomain 3)) (rowρ_wave_mem_ker a) hz
  obtain ⟨y, hy, h0⟩ := LinearPMap.mem_ker_iff.1 hmem
  rw [rowρ_apply] at hy
  have hd : compρL z a ∈ D2min.domain := by rw [hy]; exact y.2
  refine ⟨hd, ?_⟩
  rw [← h0]
  exact LinearPMap.apply_congr' _ _ _ hy

/-- **(c) `H¹` on `N(L)ᗮ`**: for `z ∈ D(L) ∩ N(L)ᗮ` every magnetic row is in `H¹_univ`, with
`‖ρₐ‖_{1,univ} ≤ (1 + √2) ‖z‖ + 2 ‖L z‖` (`ρₐ ∈ N(d²) ∩ D(d¹*)`, Gaffney). The obstruction of
`exists_memDomainPow_compρL_not_mem` lives in `N(L)`. -/
theorem sobRel_compρL_of_mem_orthogonal {z : WS} (hz : z ∈ formsShort.wave.domain)
    (hzo : z ∈ (formsShort.wave.ker)ᗮ) (a : Fin 3) :
    SobRel 1 ((1 + √2) * ‖z‖ + 2 * ‖waveOf z‖) 2 (compρL z a) := by
  obtain ⟨h, h0⟩ := compρL_mem_ker_of_mem_orthogonal hzo a
  refine (sobRel_compρL hz a h (Λ := 0) (by rw [h0, norm_zero])).mono (le_of_eq ?_)
  ring

/-- **The stationary part `P_{N(L)} U`** of a state. -/
def projKer (U : WS) : WS := projKerOf formsShort.isSkewAdjoint_wave U

theorem projKer_mem_ker (U : WS) : projKer U ∈ formsShort.wave.ker :=
  projKerOf_mem_ker formsShort.isSkewAdjoint_wave U

theorem sub_projKer_mem_orthogonal (U : WS) : U - projKer U ∈ (formsShort.wave.ker)ᗮ :=
  sub_projKerOf_mem_orthogonal formsShort.isSkewAdjoint_wave U

/-- **The stationary part is conserved**: `P_{N(L)} e^{tL} U = P_{N(L)} U`. -/
theorem projKer_waveOrbit (U : WS) (t : ℝ) : projKer (waveOrbit U t) = projKer U :=
  projKerOf_group formsShort.isSkewAdjoint_wave U t

/-- **(c) The magnetic rows of the datum from its stationary part**: if the rows of
`P_{N(L)} U₀` are in `H¹_univ` with norm `≤ Λ`, the rows of `U₀` are in `D(d²)` with
`‖d² ρₐ(U₀)‖ ≤ Λ` (the rows of `U₀ − P U₀ ∈ N(L)ᗮ` are in `N(d²)`). -/
theorem compρL_mem_of_projKer {U₀ : WS} {Λ : ℝ}
    (h : ∀ a, SobRel 1 Λ 2 (compρL (projKer U₀) a)) (a : Fin 3) :
    ∃ h : compρL U₀ a ∈ D2min.domain, ‖D2min ⟨_, h⟩‖ ≤ Λ := by
  obtain ⟨h1, -, b1, -⟩ := mem_D2min_D1adj_of_sobRel_one (h a)
  obtain ⟨h2, h20⟩ := compρL_mem_ker_of_mem_orthogonal (sub_projKer_mem_orthogonal U₀) a
  have e : compρL U₀ a = compρL (projKer U₀) a + compρL (U₀ - projKer U₀) a := by
    rw [map_sub, PiLp.sub_apply]; abel
  have hd : compρL U₀ a ∈ D2min.domain := by rw [e]; exact Submodule.add_mem _ h1 h2
  refine ⟨hd, ?_⟩
  have e2 : D2min ⟨_, hd⟩ = D2min ⟨_, h1⟩ + D2min ⟨_, h2⟩ := by
    rw [← LinearPMap.map_add]; exact LinearPMap.apply_congr' _ _ _ e
  rw [e2, h20, add_zero]
  exact b1

end KernelPart

/-! ### The `O(h)` rate of (6.5) from `D(L³)` -/

section Rate

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- The graph norm of `D(L³)`: `Σ_{j ≤ 3} ‖Lʲ U₀‖`. -/
def domNorm3 (U₀ : WS) : ℝ :=
  ‖U₀‖ + ‖waveOf U₀‖ + ‖waveOf (waveOf U₀)‖ + ‖waveOf (waveOf (waveOf U₀))‖

theorem domNorm3_nonneg (U₀ : WS) : 0 ≤ domNorm3 U₀ := by unfold domNorm3; positivity

set_option maxHeartbeats 8000000 in
/-- **The `O(h)` rate of (6.5) along an orbit of `D(L³)`, with hypotheses along the orbit**
([QuennevilleBelair2015], §6.3, (6.5), Table 6.1, from the elliptic projection (6.4)): there is
`K`, independent of `N`, `T` and the data, such that for every `U₀ ∈ D(L³)` and `Λ ≥ 0` with,
along the orbit `U(t) = e^{tL} U₀`,
* (multiplier) the multipliers of `U(t)`, `L U(t)`, `L² U(t)` are `L²`-bounded by `Λ`
  (`|ℓ μ| ≤ Λ ‖μ‖`, the hypothesis of `cubeWave_rate_tr`; it implies `div uₐ ∈ L²` row by row,
  `rowu_mem_adjoint_of_mult`; the converse is not proved here),
* (skew field) the fields `M` of `U(t)`, `L U(t)`, `L² U(t)` are in `D(d²) ∩ D(d¹*)` with
  `‖d M‖, ‖d* M‖ ≤ Λ` (`M ∈ H¹_univ` by Gaffney),
* (magnetic datum) the rows of `ρ(0)` are in `D(d²)` with `‖d ρₐ(0)‖ ≤ Λ`,
the classical solution `orbitExact` of (6.2) satisfies, for the solution of (6.5) from its elliptic
projection, `(‖σ − σₕ‖² + ‖u − uₕ‖² + ‖M − Mₕ‖² + ‖ρ − ρₕ‖²)^{1/2}(t) ≤
K (Σ_{j ≤ 3} ‖Lʲ U₀‖ + Λ) (1 + t) h_N`. Every other field of the rate class
(`σ, dφ, u, du, ρ, S¹u` and their time derivatives in `H¹_univ`) is derived:
`isSobolevStateTr_of_mem`, `compρL_waveOrbit_mem`, through `cubeWave_rate_sobolev` at `s = 1`.
`k = 3` is what the argument needs: `du' = (L² U)ρ` in `D(d¹*)` uses `L² U(t) ∈ D(L)`.
`waveFEM_rate_of_mem_domain` moves the `j = 0` hypotheses and the magnetic datum to `U₀`. -/
theorem waveFEM_rate_of_mem_domain_of_orbit :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T) {U₀ : WS}
      (hU₀ : MemDomainPow formsShort.wave 3 U₀) {Λ : ℝ}, 0 ≤ Λ →
      (∀ t ∈ Icc 0 T, ∀ j ≤ 2, ∀ μ : U1,
        |multOf (aOf (waveOf^[j] (waveOrbit U₀ t))) (bOf (waveOf^[j] (waveOrbit U₀ t))) μ| ≤
          Λ * ‖μ‖) →
      (∀ t ∈ Icc 0 T, ∀ j ≤ 2, ∃ h2 : compML (waveOf^[j] (waveOrbit U₀ t)) ∈ D2min.domain,
        ∃ h1 : compML (waveOf^[j] (waveOrbit U₀ t)) ∈ (D1†).domain,
          ‖D2min ⟨_, h2⟩‖ ≤ Λ ∧ ‖D1† ⟨_, h1⟩‖ ≤ Λ) →
      (∀ a, ∃ h : compρL U₀ a ∈ D2min.domain, ‖D2min ⟨_, h⟩‖ ≤ Λ) →
      ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH
              ((orbitExact hU₀ T).σ 0) ((orbitExact hU₀ T).φ 0) ((orbitExact hU₀ T).u 0)
              ((orbitExact hU₀ T).M 0) ((orbitExact hU₀ T).ρ 0) ((orbitExact hU₀ T).ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖(orbitExact hU₀ T).σ t - sh.σ t‖ ^ 2 +
          ‖(orbitExact hU₀ T).u t - sh.u t‖ ^ 2 + ‖(orbitExact hU₀ T).M t - sh.M t‖ ^ 2 +
          ‖(orbitExact hU₀ T).ρ t - sh.ρ t‖ ^ 2) ≤
            K * (domNorm3 U₀ + Λ) * (1 + t) * meshSize N := by
  have hrate := cubeWave_rate_sobolev hT hB
  obtain ⟨K0, hK0⟩ := hrate
  have hK00 := hK0.1
  refine ⟨4 * K0, by positivity, fun N T hT0 U₀ hU₀ Λ hΛ hmult hM hρ0 => ?_⟩
  have ex_L : ∃ x : ℝ, x = 4 * (domNorm3 U₀ + Λ) := ⟨_, rfl⟩
  obtain ⟨L', hL'⟩ := ex_L
  have hL'0 : 0 ≤ L' := by rw [hL']; have := domNorm3_nonneg U₀; positivity
  have hΛL : Λ ≤ L' := by rw [hL']; have := domNorm3_nonneg U₀; linarith
  have hn : ∀ t, ∀ j ≤ 3, ‖waveOf^[j] (waveOrbit U₀ t)‖ = ‖waveOf^[j] U₀‖ :=
    fun t j hj => norm_waveOrbit_iterate hU₀ t hj
  have hsob : ∀ t ∈ Icc 0 T,
      IsSobolevStateTr 1 L' ((orbitExact hU₀ T).σ t) ((orbitExact hU₀ T).φ t)
          ((orbitExact hU₀ T).u t) ((orbitExact hU₀ T).M t) ((orbitExact hU₀ T).ρ t) ∧
        IsSobolevStateTr 1 L' ((orbitExact hU₀ T).σ' t) ((orbitExact hU₀ T).φ' t)
          ((orbitExact hU₀ T).u' t) ((orbitExact hU₀ T).M' t) ((orbitExact hU₀ T).ρ' t) := by
    intro t ht
    have hz := waveOrbit_mem hU₀ t (j := 0) (by norm_num)
    have hLz := waveOrbit_mem hU₀ t (j := 1) (by norm_num)
    have hL2z := waveOrbit_mem hU₀ t (j := 2) (by norm_num)
    obtain ⟨hM02, hM01, hM02b, hM01b⟩ := hM t ht 0 (by norm_num)
    obtain ⟨hM12, hM11, hM12b, hM11b⟩ := hM t ht 1 (by norm_num)
    obtain ⟨hM22, hM21, hM22b, hM21b⟩ := hM t ht 2 (by norm_num)
    have n0 := hn t 0 (by norm_num)
    have n1 := hn t 1 (by norm_num)
    have n2 := hn t 2 (by norm_num)
    have n3 := hn t 3 (by norm_num)
    change ‖waveOrbit U₀ t‖ = ‖U₀‖ at n0
    change ‖waveOf (waveOrbit U₀ t)‖ = ‖waveOf U₀‖ at n1
    change ‖waveOf (waveOf (waveOrbit U₀ t))‖ = ‖waveOf (waveOf U₀)‖ at n2
    change ‖waveOf (waveOf (waveOf (waveOrbit U₀ t)))‖ = ‖waveOf (waveOf (waveOf U₀))‖ at n3
    have hd3 := domNorm3_nonneg U₀
    refine ⟨?_, ?_⟩
    · have h := isSobolevStateTr_of_mem hz hLz hΛ (hmult t ht 0 (by norm_num))
        (hmult t ht 1 (by norm_num)) hM02 hM02b hM01 hM01b hM12 hM12b hM11 hM11b
        (fun a => compρL_waveOrbit_mem hU₀ (hρ0 a) t ht)
      refine h.mono ?_
      change 4 * (‖waveOrbit U₀ t‖ + ‖waveOf (waveOrbit U₀ t)‖ +
        ‖waveOf (waveOf (waveOrbit U₀ t))‖ + Λ) ≤ L'
      rw [n0, n1, n2, hL']
      unfold domNorm3
      linarith [norm_nonneg (waveOf (waveOf (waveOf U₀)))]
    · have hρ' : ∀ a, ∃ h : compρL (waveOf (waveOrbit U₀ t)) a ∈ D2min.domain,
          ‖D2min ⟨_, h⟩‖ ≤ Λ := fun a => by
        have e : compρL (waveOf (waveOrbit U₀ t)) a = D1 (uOf (waveOrbit U₀ t) a) := by
          have := congrArg (fun y : Wv W2 => y a) (dt1_uOf hz)
          exact this.symm
        have hd : compρL (waveOf (waveOrbit U₀ t)) a ∈ D2min.domain := by
          rw [e]; exact D1_mem_D2min _
        refine ⟨hd, ?_⟩
        have : D2min ⟨_, hd⟩ = D2min ⟨_, D1_mem_D2min (uOf (waveOrbit U₀ t) a)⟩ :=
          LinearPMap.apply_congr' _ _ _ e
        rw [this, D2min_D1, norm_zero]; exact hΛ
      have h := isSobolevStateTr_of_mem hLz hL2z hΛ (hmult t ht 1 (by norm_num))
        (hmult t ht 2 (by norm_num)) hM12 hM12b hM11 hM11b hM22 hM22b hM21 hM21b hρ'
      refine h.mono ?_
      change 4 * (‖waveOf (waveOrbit U₀ t)‖ + ‖waveOf (waveOf (waveOrbit U₀ t))‖ +
        ‖waveOf (waveOf (waveOf (waveOrbit U₀ t)))‖ + Λ) ≤ L'
      rw [n1, n2, n3, hL']
      unfold domNorm3
      linarith [norm_nonneg U₀]
  have hMd : ∀ t ∈ Icc 0 T, ∀ v : U1, |⟪(orbitExact hU₀ T).M t, bggSegment.d1 v⟫| ≤ L' * ‖v‖ ∧
      |⟪(orbitExact hU₀ T).M' t, bggSegment.d1 v⟫| ≤ L' * ‖v‖ := by
    intro t ht v
    obtain ⟨-, hM01, -, hM01b⟩ := hM t ht 0 (by norm_num)
    obtain ⟨-, hM11, -, hM11b⟩ := hM t ht 1 (by norm_num)
    have k0 := LinearPMap.adjoint_isFormalAdjoint dense_D1_domain ⟨_, hM01⟩ v
    have k1 := LinearPMap.adjoint_isFormalAdjoint dense_D1_domain ⟨_, hM11⟩ v
    refine ⟨?_, ?_⟩
    · change |⟪compML (waveOf^[0] (waveOrbit U₀ t)), D1 v⟫| ≤ _
      rw [← k0]
      refine (abs_real_inner_le_norm _ _).trans (mul_le_mul (hM01b.trans hΛL) le_rfl
        (norm_nonneg _) hL'0)
    · change |⟪compML (waveOf^[1] (waveOrbit U₀ t)), D1 v⟫| ≤ _
      rw [← k1]
      refine (abs_real_inner_le_norm _ _).trans (mul_le_mul (hM11b.trans hΛL) le_rfl
        (norm_nonneg _) hL'0)
  have hmL : ∀ t ∈ Icc 0 T, ∀ μ : U1, |(orbitExact hU₀ T).ℓ t μ| ≤ L' * ‖μ‖ ∧
      |(orbitExact hU₀ T).ℓ' t μ| ≤ L' * ‖μ‖ := fun t ht μ =>
    ⟨(hmult t ht 0 (by norm_num) μ).trans (mul_le_mul_of_nonneg_right hΛL (norm_nonneg _)),
      (hmult t ht 1 (by norm_num) μ).trans (mul_le_mul_of_nonneg_right hΛL (norm_nonneg _))⟩
  have hres := hK0.2 N hT0 continuousOn_const (orbitExact hU₀ T) zero_le_one hL'0 hsob hMd hmL
  obtain ⟨sh, h0, hb⟩ := hres
  refine ⟨sh, h0, fun t ht => (hb t ht).trans (le_of_eq ?_)⟩
  rw [min_self, Real.rpow_one, hL']
  ring

set_option maxHeartbeats 8000000 in
/-- **The `O(h)` rate of the scheme (6.5) for data in `D(L³)`** ([QuennevilleBelair2015], §6.3,
(6.5), Table 6.1, thesis' boundary conditions, from the elliptic projection (6.4); unconditional in
the regularity hypothesis `curlPotential`). There is `K`, independent of `N`, `T` and the data,
such that for every `U₀ ∈ D(L³)` and `Λ ≥ 0` with
* (multiplier) `|ℓ_{U₀} μ| ≤ Λ ‖μ‖` for the multiplier of the datum, and the same for the
  multipliers of `L U(t)`, `L² U(t)` along the orbit `U(t) = e^{tL} U₀`, `t ∈ [0, T]`;
* (skew field) `M(U₀) ∈ H¹_univ` with `‖M(U₀)‖_{1,univ} ≤ Λ`, and the same for the skew fields
  `M(L U(t)) = S¹u(t)` and `M(L² U(t)) = S¹u'(t)` along the orbit;
* (stationary part) the magnetic rows of `P_{N(L)} U₀` are in `H¹_univ` with norm `≤ Λ`,
the classical solution `orbitExact` of (6.2) and the solution of (6.5) from its elliptic projection
satisfy `(‖σ − σₕ‖² + ‖u − uₕ‖² + ‖M − Mₕ‖² + ‖ρ − ρₕ‖²)^{1/2}(t) ≤
K (Σ_{j ≤ 3} ‖Lʲ U₀‖ + (1 + T) Λ) (1 + t) h_N`.

The datum-level hypotheses replace orbit-level ones: the multiplier and the skew field of `U(t)`
are controlled by those of `U₀` and of `L U(t)` (mean value inequality,
`exists_mem_domain_of_hasDerivWithinAt`; hence the factor `1 + T`), and the magnetic rows of `U₀`
by its stationary part, since the rows of `U₀ − P_{N(L)} U₀ ∈ N(L)ᗮ` are in `N(d²)`
(`compρL_mem_of_projKer`). The stationary hypothesis cannot be dropped: `N(L) ⊆ D(L^∞)` contains
states whose magnetic row is not in `H^{1/2}` (`exists_memDomainPow_compρL_not_mem`).

**What remains along the orbit**, explicitly: the `L²` bound of the multipliers of `L U(t)` and
`L² U(t)` and the `H¹_univ` bound of `S¹u(t)` and `S¹u'(t)`. They are not implied by
`U₀ ∈ D(Lᵏ)` for any `k` by the arguments available here: the multiplier bound would need a right
inverse of `(τ, ψ) ↦ dτ − S⁰ψ` bounded in `L²` (`IsMultRep` gives only the graph norm), and the
`H¹` regularity of `S¹u` couples components of incompatible parities (corner regularity of the
coupled system, absent from Mathlib). `k = 3` is what the argument uses (`du' = (L² U)_ρ ∈ D(d¹*)`
needs `L² U(t) ∈ D(L)`); minimality of `k` is not shown. -/
theorem waveFEM_rate_of_mem_domain :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T) {U₀ : WS}
      (hU₀ : MemDomainPow formsShort.wave 3 U₀) {Λ : ℝ}, 0 ≤ Λ →
      (∀ μ : U1, |multOf (aOf U₀) (bOf U₀) μ| ≤ Λ * ‖μ‖) →
      (∀ t ∈ Icc 0 T, ∀ j, 1 ≤ j → j ≤ 2 → ∀ μ : U1,
        |multOf (aOf (waveOf^[j] (waveOrbit U₀ t))) (bOf (waveOf^[j] (waveOrbit U₀ t))) μ| ≤
          Λ * ‖μ‖) →
      SobRel 1 Λ 2 (compML U₀) →
      (∀ t ∈ Icc 0 T, ∀ j, 1 ≤ j → j ≤ 2 →
        SobRel 1 Λ 2 (compML (waveOf^[j] (waveOrbit U₀ t)))) →
      (∀ a, SobRel 1 Λ 2 (compρL (projKer U₀) a)) →
      ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH
              ((orbitExact hU₀ T).σ 0) ((orbitExact hU₀ T).φ 0) ((orbitExact hU₀ T).u 0)
              ((orbitExact hU₀ T).M 0) ((orbitExact hU₀ T).ρ 0) ((orbitExact hU₀ T).ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖(orbitExact hU₀ T).σ t - sh.σ t‖ ^ 2 +
          ‖(orbitExact hU₀ T).u t - sh.u t‖ ^ 2 + ‖(orbitExact hU₀ T).M t - sh.M t‖ ^ 2 +
          ‖(orbitExact hU₀ T).ρ t - sh.ρ t‖ ^ 2) ≤
            K * (domNorm3 U₀ + (1 + T) * Λ) * (1 + t) * meshSize N := by
  have hrate := waveFEM_rate_of_mem_domain_of_orbit hT hB
  obtain ⟨K, hK⟩ := hrate
  have hK0 := hK.1
  refine ⟨K, hK0, fun N T hT0 U₀ hU₀ Λ hΛ hm0 hm hM0 hM hρ => ?_⟩
  have hT1 : 0 ≤ (1 + T) * Λ := mul_nonneg (by linarith) hΛ
  have hΛT : ∀ t ∈ Icc (0 : ℝ) T, (1 + t) * Λ ≤ (1 + T) * Λ := fun t ht =>
    mul_le_mul_of_nonneg_right (by linarith [ht.2]) hΛ
  have hΛ1 : Λ ≤ (1 + T) * Λ := by nlinarith
  -- the multiplier of `U(t)`
  have hmult0 : ∀ t ∈ Icc 0 T, ∀ μ : U1,
      |multOf (aOf (waveOrbit U₀ t)) (bOf (waveOrbit U₀ t)) μ| ≤ (1 + t) * Λ * ‖μ‖ := by
    intro t ht μ
    have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment ((orbitExact hU₀ T).cℓ μ)
      (fun r hr => (orbitExact hU₀ T).dℓ r hr μ) (C := Λ * ‖μ‖) (fun r hr => by
        rw [Real.norm_eq_abs, orbitExact_ℓ']
        exact hm r (Ico_subset_Icc_self hr) 1 le_rfl (by norm_num) μ) t ht
    rw [Real.norm_eq_abs, sub_zero, orbitExact_ℓ, orbitExact_ℓ, waveOrbit_zero] at hmv
    have h0 := hm0 μ
    have := abs_sub_abs_le_abs_sub (multOf (aOf (waveOrbit U₀ t)) (bOf (waveOrbit U₀ t)) μ)
      (multOf (aOf U₀) (bOf U₀) μ)
    nlinarith [norm_nonneg μ]
  -- the skew field of `U(t)`
  have eM0 : (orbitExact hU₀ T).M 0 = compML U₀ := by
    rw [orbitExact_M, waveOrbit_zero]
  have hM0' := mem_D2min_D1adj_of_sobRel_one hM0
  obtain ⟨a1, a2, a3, a4⟩ := hM0'
  have hd' : ∀ r ∈ Ico 0 T,
      (∃ h : (orbitExact hU₀ T).M' r ∈ D2min.domain, ‖D2min ⟨_, h⟩‖ ≤ Λ) ∧
        ∃ h : (orbitExact hU₀ T).M' r ∈ (D1†).domain, ‖D1† ⟨_, h⟩‖ ≤ Λ := fun r hr => by
    have hs := hM r (Ico_subset_Icc_self hr) 1 le_rfl (by norm_num)
    rw [Function.iterate_one, ← orbitExact_M' hU₀ T r] at hs
    have hs' := mem_D2min_D1adj_of_sobRel_one hs
    obtain ⟨b1, b2, b3, b4⟩ := hs'
    exact ⟨⟨b1, b3⟩, ⟨b2, b4⟩⟩
  have hMt2 := exists_mem_domain_of_hasDerivWithinAt D2min
    (ConstCoeffOp.dense_minimal_domain (extDerivOp ℝ 3 2) (isOpen_cubeDomain 3))
    (ConstCoeffOp.isClosed_minimal (extDerivOp ℝ 3 2) (isOpen_cubeDomain 3)) hΛ (orbitExact hU₀ T).cM
    (orbitExact hU₀ T).dM (by rw [eM0]; exact ⟨a1, a3⟩) (fun r hr => (hd' r hr).1)
  have hMt1 := exists_mem_domain_of_hasDerivWithinAt (D1†)
    dense_D1_adjoint_domain (LinearPMap.adjoint_isClosed dense_D1_domain) hΛ (orbitExact hU₀ T).cM
    (orbitExact hU₀ T).dM (by rw [eM0]; exact ⟨a2, a4⟩) (fun r hr => (hd' r hr).2)
  have hmult' : ∀ t ∈ Icc 0 T, ∀ j ≤ 2, ∀ μ : U1,
      |multOf (aOf (waveOf^[j] (waveOrbit U₀ t))) (bOf (waveOf^[j] (waveOrbit U₀ t))) μ| ≤
        (1 + T) * Λ * ‖μ‖ := by
    intro t ht j hj μ
    rcases j with _ | j
    · rw [Function.iterate_zero_apply]
      exact (hmult0 t ht μ).trans (mul_le_mul_of_nonneg_right (hΛT t ht) (norm_nonneg _))
    · exact (hm t ht (j + 1) (by omega) hj μ).trans
        (mul_le_mul_of_nonneg_right hΛ1 (norm_nonneg _))
  have hM' : ∀ t ∈ Icc 0 T, ∀ j ≤ 2,
      ∃ h2 : compML (waveOf^[j] (waveOrbit U₀ t)) ∈ D2min.domain,
        ∃ h1 : compML (waveOf^[j] (waveOrbit U₀ t)) ∈ (D1†).domain,
          ‖D2min ⟨_, h2⟩‖ ≤ (1 + T) * Λ ∧ ‖D1† ⟨_, h1⟩‖ ≤ (1 + T) * Λ := by
    intro t ht j hj
    rcases j with _ | j
    · have k2 := hMt2 t ht
      have k1 := hMt1 t ht
      rw [orbitExact_M] at k2 k1
      rw [Function.iterate_zero_apply]
      obtain ⟨c1, c3⟩ := k2
      obtain ⟨c2, c4⟩ := k1
      exact ⟨c1, c2, c3.trans (hΛT t ht), c4.trans (hΛT t ht)⟩
    · have hs := mem_D2min_D1adj_of_sobRel_one (hM t ht (j + 1) (by omega) hj)
      obtain ⟨c1, c2, c3, c4⟩ := hs
      exact ⟨c1, c2, c3.trans hΛ1, c4.trans hΛ1⟩
  have hρ' : ∀ a, ∃ h : compρL U₀ a ∈ D2min.domain, ‖D2min ⟨_, h⟩‖ ≤ (1 + T) * Λ := fun a => by
    have hs := compρL_mem_of_projKer hρ a
    obtain ⟨c1, c2⟩ := hs
    exact ⟨c1, c2.trans hΛ1⟩
  exact hK.2 N hT0 hU₀ hT1 hmult' hM' hρ'

end Rate

/-! ### An explicit mode: `δ d w = 8π² w` for `w = (sin 2πy₁ sin 2πy₂) dx₀` -/

section ModeCalculus

open Real
open Feec.ExteriorFibre (sgn)

theorem fderiv_coordDir_eq {g : (Fin 3 → ℝ) → ℝ} (hg : Differentiable ℝ g) (y : Fin 3 → ℝ)
    (i : Fin 3) {c : ℝ} (h : HasDerivAt (fun t : ℝ => g (y + t • coordDir i)) c 0) :
    fderiv ℝ g y (coordDir i) = c := by
  have h1 : HasDerivAt (fun t : ℝ => g (y + t • coordDir i)) (fderiv ℝ g y (coordDir i)) 0 := by
    have hl : HasDerivAt (fun t : ℝ => y + t • (coordDir i : Fin 3 → ℝ)) (coordDir i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordDir i : Fin 3 → ℝ)).const_add y
    have h2 : HasFDerivAt g (fderiv ℝ g y) (y + (0 : ℝ) • (coordDir i : Fin 3 → ℝ)) := by
      simpa using (hg y).hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) hl
  exact h1.unique h

theorem line_apply (y : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) :
    (y + t • coordDir i) j = y j + if j = i then t else 0 := by
  simp [coordDir, Pi.single_apply]

/-- `sin(2π y₁) sin(2π y₂)`. -/
def gW (y : Fin 3 → ℝ) : ℝ := Real.sin (2 * π * y 1) * Real.sin (2 * π * y 2)
/-- `∂₁ gW`. -/
def gW1 (y : Fin 3 → ℝ) : ℝ := 2 * π * (Real.cos (2 * π * y 1) * Real.sin (2 * π * y 2))
/-- `∂₂ gW`. -/
def gW2 (y : Fin 3 → ℝ) : ℝ := 2 * π * (Real.sin (2 * π * y 1) * Real.cos (2 * π * y 2))

theorem hasDerivAt_sin_line (a : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (2 * π * (a + t))) (2 * π * Real.cos (2 * π * a)) 0 := by
  have h := (((hasDerivAt_id' (0 : ℝ)).const_add a).const_mul (2 * π)).sin
  convert h using 1
  simp only [add_zero, mul_one]; ring

theorem hasDerivAt_cos_line (a : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (2 * π * (a + t))) (-(2 * π * Real.sin (2 * π * a))) 0 := by
  have h := (((hasDerivAt_id' (0 : ℝ)).const_add a).const_mul (2 * π)).cos
  convert h using 1
  simp only [add_zero, mul_one]; ring

theorem differentiable_gW : Differentiable ℝ gW := by
  unfold gW; fun_prop
theorem differentiable_gW1 : Differentiable ℝ gW1 := by
  unfold gW1; fun_prop
theorem differentiable_gW2 : Differentiable ℝ gW2 := by
  unfold gW2; fun_prop

theorem fderiv_gW_zero (y : Fin 3 → ℝ) : fderiv ℝ gW y (coordDir 0) = 0 := by
  refine fderiv_coordDir_eq differentiable_gW y 0 ?_
  simp only [gW, line_apply]
  simpa using hasDerivAt_const (0 : ℝ) (Real.sin (2 * π * y 1) * Real.sin (2 * π * y 2))

theorem fderiv_gW_one (y : Fin 3 → ℝ) : fderiv ℝ gW y (coordDir 1) = gW1 y := by
  refine fderiv_coordDir_eq differentiable_gW y 1 ?_
  simp only [gW, gW1, line_apply]
  have h := (hasDerivAt_sin_line (y 1)).mul_const (Real.sin (2 * π * y 2))
  convert h using 1
  · funext t; simp
  · ring

theorem fderiv_gW_two (y : Fin 3 → ℝ) : fderiv ℝ gW y (coordDir 2) = gW2 y := by
  refine fderiv_coordDir_eq differentiable_gW y 2 ?_
  simp only [gW, gW2, line_apply]
  have h := (hasDerivAt_sin_line (y 2)).const_mul (Real.sin (2 * π * y 1))
  convert h using 1
  · funext t; simp
  · ring

theorem fderiv_gW1_zero (y : Fin 3 → ℝ) : fderiv ℝ gW1 y (coordDir 0) = 0 := by
  refine fderiv_coordDir_eq differentiable_gW1 y 0 ?_
  simp only [gW1, line_apply]
  simpa using hasDerivAt_const (0 : ℝ)
    (2 * π * (Real.cos (2 * π * y 1) * Real.sin (2 * π * y 2)))

theorem fderiv_gW2_zero (y : Fin 3 → ℝ) : fderiv ℝ gW2 y (coordDir 0) = 0 := by
  refine fderiv_coordDir_eq differentiable_gW2 y 0 ?_
  simp only [gW2, line_apply]
  simpa using hasDerivAt_const (0 : ℝ)
    (2 * π * (Real.sin (2 * π * y 1) * Real.cos (2 * π * y 2)))

theorem fderiv_gW1_one (y : Fin 3 → ℝ) :
    fderiv ℝ gW1 y (coordDir 1) = -(4 * π ^ 2) * gW y := by
  refine fderiv_coordDir_eq differentiable_gW1 y 1 ?_
  simp only [gW1, gW, line_apply]
  have h := ((hasDerivAt_cos_line (y 1)).mul_const (Real.sin (2 * π * y 2))).const_mul (2 * π)
  convert h using 1
  · funext t; simp
  · ring

theorem fderiv_gW2_two (y : Fin 3 → ℝ) :
    fderiv ℝ gW2 y (coordDir 2) = -(4 * π ^ 2) * gW y := by
  refine fderiv_coordDir_eq differentiable_gW2 y 2 ?_
  simp only [gW2, gW, line_apply]
  have h := ((hasDerivAt_cos_line (y 2)).const_mul (Real.sin (2 * π * y 1))).const_mul (2 * π)
  convert h using 1
  · funext t; simp
  · ring

/-- The witness is `gW dx₀`. -/
theorem normalWitness_eq (y : Fin 3 → ℝ) (s : Finset (Fin 3)) :
    normalWitness (n := 3) y s = if s = {0} then gW y else 0 := by
  simp only [normalWitness, gW]
  split_ifs
  · rw [show (Finset.univ.erase (0 : Fin 3)) = {1, 2} by decide, Finset.prod_pair (by decide)]
  · rfl

theorem sgn_vals : (sgn (0 : Fin 3) ({0, 1} : Finset (Fin 3)) : ℝ) = 1 ∧
    (sgn (1 : Fin 3) ({0, 1} : Finset (Fin 3)) : ℝ) = -1 ∧
    (sgn (0 : Fin 3) ({0, 2} : Finset (Fin 3)) : ℝ) = 1 ∧
    (sgn (2 : Fin 3) ({0, 2} : Finset (Fin 3)) : ℝ) = -1 ∧
    (sgn (1 : Fin 3) ({0} : Finset (Fin 3)) : ℝ) = -1 ∧
    (sgn (2 : Fin 3) ({0} : Finset (Fin 3)) : ℝ) = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [sgn]
  · rw [show ({l ∈ ({0, 1} : Finset (Fin 3)) | l < 0}).card = 0 by decide]; norm_num
  · rw [show ({l ∈ ({0, 1} : Finset (Fin 3)) | l < 1}).card = 1 by decide]; norm_num
  · rw [show ({l ∈ ({0, 2} : Finset (Fin 3)) | l < 0}).card = 0 by decide]; norm_num
  · rw [show ({l ∈ ({0, 2} : Finset (Fin 3)) | l < 2}).card = 1 by decide]; norm_num
  · rw [show ({l ∈ ({0} : Finset (Fin 3)) | l < 1}).card = 1 by decide]; norm_num
  · rw [show ({l ∈ ({0} : Finset (Fin 3)) | l < 2}).card = 1 by decide]; norm_num

theorem extDeriv_nW_01 (y : Fin 3 → ℝ) :
    FiniteElement.extDeriv (normalWitness (n := 3)) y {0, 1} = -gW1 y := by
  rw [FiniteElement.extDeriv_apply, Finset.sum_pair (by decide)]
  have e0 : (fun z => normalWitness (n := 3) z (({0, 1} : Finset (Fin 3)).erase 0)) =
      fun _ => 0 := by
    funext z; rw [normalWitness_eq]; simp [show (({0, 1} : Finset (Fin 3)).erase 0) = {1} by decide]
  have e1 : (fun z => normalWitness (n := 3) z (({0, 1} : Finset (Fin 3)).erase 1)) = gW := by
    funext z; rw [normalWitness_eq]; simp [show (({0, 1} : Finset (Fin 3)).erase 1) = {0} by decide]
  rw [e0, e1]
  simp only [partialDeriv, fderiv_const_apply, zero_apply, mul_zero, zero_add]
  rw [show (Pi.single (1 : Fin 3) (1 : ℝ) : Fin 3 → ℝ) = coordDir 1 from rfl, fderiv_gW_one,
    sgn_vals.2.1]
  ring

theorem extDeriv_nW_02 (y : Fin 3 → ℝ) :
    FiniteElement.extDeriv (normalWitness (n := 3)) y {0, 2} = -gW2 y := by
  rw [FiniteElement.extDeriv_apply, Finset.sum_pair (by decide)]
  have e0 : (fun z => normalWitness (n := 3) z (({0, 2} : Finset (Fin 3)).erase 0)) =
      fun _ => 0 := by
    funext z; rw [normalWitness_eq]; simp [show (({0, 2} : Finset (Fin 3)).erase 0) = {2} by decide]
  have e1 : (fun z => normalWitness (n := 3) z (({0, 2} : Finset (Fin 3)).erase 2)) = gW := by
    funext z; rw [normalWitness_eq]; simp [show (({0, 2} : Finset (Fin 3)).erase 2) = {0} by decide]
  rw [e0, e1]
  simp only [partialDeriv, fderiv_const_apply, zero_apply, mul_zero, zero_add]
  rw [show (Pi.single (2 : Fin 3) (1 : ℝ) : Fin 3 → ℝ) = coordDir 2 from rfl, fderiv_gW_two,
    sgn_vals.2.2.2.1]
  ring

theorem extDeriv_nW_12 (y : Fin 3 → ℝ) :
    FiniteElement.extDeriv (normalWitness (n := 3)) y {1, 2} = 0 := by
  rw [FiniteElement.extDeriv_apply, Finset.sum_pair (by decide)]
  have e0 : (fun z => normalWitness (n := 3) z (({1, 2} : Finset (Fin 3)).erase 1)) =
      fun _ => 0 := by
    funext z; rw [normalWitness_eq]; simp [show (({1, 2} : Finset (Fin 3)).erase 1) = {2} by decide]
  have e1 : (fun z => normalWitness (n := 3) z (({1, 2} : Finset (Fin 3)).erase 2)) =
      fun _ => 0 := by
    funext z; rw [normalWitness_eq]; simp [show (({1, 2} : Finset (Fin 3)).erase 2) = {1} by decide]
  rw [e0, e1]
  simp only [partialDeriv, fderiv_const_apply, zero_apply, mul_zero, zero_add]

theorem formExt_tangentialDψ_01 :
    formExt tangentialDψ ({0, 1} : Finset (Fin 3)) = fun y => -gW1 y := by
  rw [formExt_of_card _ (by decide)]; funext y; exact extDeriv_nW_01 y

theorem formExt_tangentialDψ_02 :
    formExt tangentialDψ ({0, 2} : Finset (Fin 3)) = fun y => -gW2 y := by
  rw [formExt_of_card _ (by decide)]; funext y; exact extDeriv_nW_02 y

theorem formExt_tangentialDψ_12 :
    formExt tangentialDψ ({1, 2} : Finset (Fin 3)) = fun _ => 0 := by
  rw [formExt_of_card _ (by decide)]; funext y; exact extDeriv_nW_12 y

/-- **`δ d w = 8π² w`** for `w = (sin 2πy₁ sin 2πy₂) dx₀`, pointwise. -/
theorem formalAdj_tangentialDψ (r : formIdx 3 1) (y : Fin 3 → ℝ) :
    (extDerivOp ℝ 3 1).formalAdj.apply tangentialDψ r y =
      8 * π ^ 2 * normalWitness (n := 3) y r.1 := by
  rw [formalAdj_extDerivOp_apply, extDAdj, normalWitness_eq]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (by exact_mod_cast r.2 : r.1.card = 1)
  rw [ha]
  have hn1 : fderiv ℝ (fun y => -gW1 y) y = -fderiv ℝ gW1 y := fderiv_neg
  have hn2 : fderiv ℝ (fun y => -gW2 y) y = -fderiv ℝ gW2 y := fderiv_neg
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · rw [show ({0} : Finset (Fin 3))ᶜ = {1, 2} by decide, Finset.sum_pair (by decide),
      show insert (1 : Fin 3) ({0} : Finset (Fin 3)) = {0, 1} by decide,
      show insert (2 : Fin 3) ({0} : Finset (Fin 3)) = {0, 2} by decide,
      formExt_tangentialDψ_01, formExt_tangentialDψ_02, hn1, hn2]
    simp only [neg_apply, fderiv_gW1_one, fderiv_gW2_two, sgn_vals.2.2.2.2.1,
      sgn_vals.2.2.2.2.2, ite_true]
    ring
  · rw [show ({1} : Finset (Fin 3))ᶜ = {0, 2} by decide, Finset.sum_pair (by decide),
      show insert (0 : Fin 3) ({1} : Finset (Fin 3)) = {0, 1} by decide,
      show insert (2 : Fin 3) ({1} : Finset (Fin 3)) = {1, 2} by decide,
      formExt_tangentialDψ_01, formExt_tangentialDψ_12, hn1]
    simp only [neg_apply, fderiv_gW1_zero, fderiv_const_apply, zero_apply]
    simp
  · rw [show ({2} : Finset (Fin 3))ᶜ = {0, 1} by decide, Finset.sum_pair (by decide),
      show insert (0 : Fin 3) ({2} : Finset (Fin 3)) = {0, 2} by decide,
      show insert (1 : Fin 3) ({2} : Finset (Fin 3)) = {1, 2} by decide,
      formExt_tangentialDψ_02, formExt_tangentialDψ_12, hn2]
    simp only [neg_apply, fderiv_gW2_zero, fderiv_const_apply, zero_apply]
    simp


/-- **`D1* D1 w = 8π² w`** in `L²`: the source of `waveTangential` is `8π²` times the witness. -/
theorem toL2F_formalAdj_tangentialDψ :
    toL2F memLp_formalAdj_tangentialDψ = (8 * π ^ 2) • tangentialX := by
  refine PiLp.ext fun r => ?_
  refine Lp.ext ?_
  filter_upwards [(memLp_formalAdj_tangentialDψ r).coeFn_toLp,
    Lp.coeFn_smul (8 * π ^ 2) (tangentialX r),
    coeFn_formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) 1
      ⟨normalWitness, contDiff_normalWitness.continuous⟩ r] with y h1 h2 h3
  change ((memLp_formalAdj_tangentialDψ r).toLp _ : L2 ℝ (cubeDomain 3)) y =
    (((8 * π ^ 2) • tangentialX) r : L2 ℝ (cubeDomain 3)) y
  rw [h1, PiLp.smul_apply, h2, Pi.smul_apply, smul_eq_mul]
  have h3' : (tangentialX r : L2 ℝ (cubeDomain 3)) y = normalWitness y r.1 := h3
  rw [h3', formalAdj_tangentialDψ]

theorem waveTangentialSrc_eq : waveTangentialSrc = (8 * π ^ 2) • incl1 tangentialU := by
  refine PiLp.ext fun a => ?_
  by_cases ha : a = 0
  · subst ha
    rw [waveTangentialSrc_apply_zero, toL2F_formalAdj_tangentialDψ, PiLp.smul_apply]
    change _ = (8 * π ^ 2) • ((tangentialU 0 : U1) : W1)
    rw [tangentialU_apply_zero]; rfl
  · rw [waveTangentialSrc_apply_of_ne ha, PiLp.smul_apply]
    change _ = (8 * π ^ 2) • ((tangentialU a : U1) : W1)
    rw [tangentialU_apply_of_ne ha]; simp

end ModeCalculus

/-! ### The mode `(0, cos(ωt) u, sin(ωt) ω⁻¹ (0, du))`, `ω² = 8π²` -/

section Mode

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

set_option maxHeartbeats 4000000

open Real

/-- The datum `(0, u, 0)`, `u = ((sin 2πy₁ sin 2πy₂) dx₀, 0, 0)` (`tangentialU`). -/
def modeU : WS :=
  ShortHilbertComplex.mk3 (0 : bggHilb.Γbar) (incl1 tangentialU) (0 : WithLp 2 (W2 × Wv W2))

/-- `L (0, u, 0) = (0, 0, (0, du))` (`S¹u = 0`). -/
def modeY : WS :=
  ShortHilbertComplex.mk3 (0 : bggHilb.Γbar) (0 : Wv W1)
    (WithLp.toLp 2 ((0 : W2), bggSegment.dt1 tangentialU) : WithLp 2 (W2 × Wv W2))

theorem comp1_modeU_mem_D1L : comp1 modeU ∈ bggHilb.D1L.domain := by
  rw [bggHilb.D1L_domain]; exact ⟨toGraphVec1 tangentialU, ιt1_toGraphVec1 _⟩

theorem comp1_modeU_mem_adjoint :
    ∃ h : comp1 modeU ∈ (bggHilb.D0Γ†).domain, bggHilb.D0Γ† ⟨_, h⟩ = 0 := by
  obtain ⟨h, hb⟩ := exists_mem_adjoint_of_abs_le bggHilb.D0Γ formsShort.dense₀ le_rfl
    (y := comp1 modeU) fun y => by
      obtain ⟨g, hg⟩ := bggHilb.mem_D0Γ_graph bggS0_injective y
      have e : bggHilb.D0Γ y = ιt1 (bggDt0 (g : V0 × Vt0).2) := (congrArg Prod.snd hg).symm
      rw [e, ιt1_bggDt0]
      change |⟪incl1 tangentialU, incl1 (bggSegment.dt0 (rp (g : V0 × Vt0).2))⟫| ≤ _
      rw [← inner_wv_U1, inner_tangentialU_dt0, abs_zero, zero_mul]
  exact ⟨h, norm_le_zero_iff.1 hb⟩

theorem modeU_mem : modeU ∈ formsShort.wave.domain :=
  formsShort.mem_wave_domain.2 ⟨Submodule.zero_mem _, comp1_modeU_mem_D1L,
    comp1_modeU_mem_adjoint.1, Submodule.zero_mem _⟩

theorem ext_WS {x y : WS} (h0 : comp0 x = comp0 y) (h1 : comp1 x = comp1 y)
    (h2 : comp2 x = comp2 y) : x = y := by
  rw [← ShortHilbertComplex.mk3_eta x, ← ShortHilbertComplex.mk3_eta y]
  change ShortHilbertComplex.mk3 (comp0 x) (comp1 x) (comp2 x) =
    ShortHilbertComplex.mk3 (comp0 y) (comp1 y) (comp2 y)
  rw [h0, h1, h2]

theorem waveOf_modeU : waveOf modeU = modeY := by
  obtain ⟨hadj, hadj0⟩ := comp1_modeU_mem_adjoint
  refine ext_WS ?_ ?_ ?_
  · rw [comp0_waveOf modeU_mem]
    rw [LinearPMap.apply_congr' _ _ hadj rfl, hadj0, neg_zero]
    rfl
  · rw [comp1_waveOf modeU_mem, apply_eq_zero_of_coe_eq_zero (f := bggHilb.D0Γ) _ rfl,
      apply_eq_zero_of_coe_eq_zero (f := bggHilb.D1L†) _ rfl, sub_zero]
    rfl
  · rw [comp2_waveOf modeU_mem]
    have hv : ιt1 (toGraphVec1 tangentialU) ∈ bggHilb.D1L.domain := by
      rw [bggHilb.D1L_domain]; exact ⟨_, rfl⟩
    rw [LinearPMap.apply_congr' bggHilb.D1L (dom1 modeU_mem) hv
      (ιt1_toGraphVec1 tangentialU).symm, D1L_apply_ιt1]
    change (WithLp.toLp 2 (segS1 tangentialU, piMap segD1 tangentialU) : WithLp 2 (W2 × Wv W2)) =
      WithLp.toLp 2 ((0 : W2), bggSegment.dt1 tangentialU)
    have : segS1 tangentialU = 0 := segS1_tangentialU
    rw [this]
    rfl

theorem comp2_modeY_mem_adjoint :
    ∃ h : comp2 modeY ∈ (bggHilb.D1L†).domain,
      bggHilb.D1L† ⟨_, h⟩ = (8 * π ^ 2) • incl1 tangentialU := by
  have key : ∀ y : bggHilb.D1L.domain, ⟪comp2 modeY, bggHilb.D1L y⟫ =
      ⟪(8 * π ^ 2) • incl1 tangentialU, (y : Wv W1)⟫ := fun y => by
    obtain ⟨v', hv', e⟩ := inner_comp2_D1L (comp2 modeY) y
    rw [e]
    change ⟪(0 : W2), bggSegment.S1 v'⟫ + ⟪bggSegment.dt1 tangentialU, bggSegment.dt1 v'⟫ = _
    rw [inner_zero_left, zero_add, inner_dt1_tangentialU, waveTangentialSrc_eq, hv']
  obtain ⟨h, -⟩ := exists_mem_adjoint_of_abs_le bggHilb.D1L formsShort.dense₁
    (norm_nonneg ((8 * π ^ 2) • incl1 tangentialU)) (y := comp2 modeY) fun y => by
      rw [key]; exact abs_real_inner_le_norm _ _
  exact ⟨h, LinearPMap.adjoint_apply_eq formsShort.dense₁ ⟨_, h⟩ fun x => (key x).symm⟩

theorem modeY_mem : modeY ∈ formsShort.wave.domain :=
  formsShort.mem_wave_domain.2 ⟨Submodule.zero_mem _, Submodule.zero_mem _, Submodule.zero_mem _,
    comp2_modeY_mem_adjoint.1⟩

theorem waveOf_modeY : waveOf modeY = (-(8 * π ^ 2)) • modeU := by
  obtain ⟨hadj, hadj0⟩ := comp2_modeY_mem_adjoint
  refine ext_WS ?_ ?_ ?_
  · rw [comp0_waveOf modeY_mem, apply_eq_zero_of_coe_eq_zero (f := bggHilb.D0Γ†) _ rfl, neg_zero]
    change (0 : bggHilb.Γbar) = (-(8 * π ^ 2)) • (0 : bggHilb.Γbar)
    rw [smul_zero]
  · rw [comp1_waveOf modeY_mem, apply_eq_zero_of_coe_eq_zero (f := bggHilb.D0Γ) _ rfl, zero_sub,
      LinearPMap.apply_congr' _ _ hadj rfl, hadj0]
    change _ = (-(8 * π ^ 2)) • incl1 tangentialU
    rw [neg_smul]
  · rw [comp2_waveOf modeY_mem, apply_eq_zero_of_coe_eq_zero (f := bggHilb.D1L) _ rfl]
    change (0 : WithLp 2 (W2 × Wv W2)) = (-(8 * π ^ 2)) • (0 : WithLp 2 (W2 × Wv W2))
    rw [smul_zero]

/-- The combinations `α (0, u, 0) + β (0, 0, (0, du))`, invariant under `L`. -/
def modeComb (α β : ℝ) : WS := α • modeU + β • modeY

theorem modeComb_mem (α β : ℝ) : modeComb α β ∈ formsShort.wave.domain :=
  Submodule.add_mem _ (Submodule.smul_mem _ α modeU_mem) (Submodule.smul_mem _ β modeY_mem)

theorem waveOf_modeComb (α β : ℝ) :
    waveOf (modeComb α β) = modeComb (-(8 * π ^ 2) * β) α := by
  rw [modeComb, ← extOp_wave, extOp_add_smul α β modeU_mem modeY_mem, extOp_wave, waveOf_modeU,
    waveOf_modeY, smul_smul, modeComb, add_comm, mul_comm]

theorem iterate_waveOf_modeComb (j : ℕ) (α β : ℝ) :
    ∃ α' β', waveOf^[j] (modeComb α β) = modeComb α' β' := by
  induction j generalizing α β with
  | zero => exact ⟨α, β, rfl⟩
  | succ j ih =>
    obtain ⟨α', β', h⟩ := ih (-(8 * π ^ 2) * β) α
    refine ⟨α', β', ?_⟩
    change waveOf^[j] (waveOf (modeComb α β)) = _
    rw [waveOf_modeComb, h]

theorem compML_modeComb (α β : ℝ) : compML (modeComb α β) = 0 := by
  rw [modeComb, map_add, map_smul, map_smul]
  change α • (0 : W2) + β • (0 : W2) = 0
  simp

theorem comp0_modeComb (α β : ℝ) : comp0 (modeComb α β) = 0 := by
  change comp0L (modeComb α β) = 0
  rw [modeComb, map_add, map_smul, map_smul]
  change α • (0 : bggHilb.Γbar) + β • (0 : bggHilb.Γbar) = 0
  simp

theorem comp1_modeComb (α β : ℝ) : comp1 (modeComb α β) = α • incl1 tangentialU := by
  change comp1L (modeComb α β) = _
  rw [modeComb, map_add, map_smul, map_smul]
  change α • incl1 tangentialU + β • (0 : Wv W1) = _
  simp

/-- **The multiplier of every combination vanishes** (`div u = 0` row by row: `⟪u, dψ⟫ = 0`). -/
theorem multOf_modeComb (α β : ℝ) (μ : U1) :
    multOf (aOf (modeComb α β)) (bOf (modeComb α β)) μ = 0 := by
  have ha : aOf (modeComb α β) = 0 := by
    rw [aOf, waveOf_modeComb, comp0_modeComb]; simp
  rw [multOf_apply, ha, inner_zero_left, zero_sub, neg_eq_zero, bOf, comp1_modeComb,
    inner_smul_left, ← inner_wv_U1, inner_tangentialU_dt0, mul_zero]

/-- The frequency `ω = 2√2 π` of the mode (`ω² = 8π²`). -/
def modeFreq : ℝ := 2 * √2 * π

theorem modeFreq_pos : 0 < modeFreq := by unfold modeFreq; positivity

theorem modeFreq_sq : modeFreq ^ 2 = 8 * π ^ 2 := by
  unfold modeFreq
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

/-- **The explicit solution** `U(t) = cos(ωt) (0, u, 0) + sin(ωt) ω⁻¹ (0, 0, (0, du))`. -/
def modeG (t : ℝ) : WS := modeComb (Real.cos (modeFreq * t)) (Real.sin (modeFreq * t) / modeFreq)

theorem isStrongSolution_modeG (I : Set ℝ) :
    Evolution.IsStrongSolution formsShort.wave I (fun _ => 0) modeG := by
  refine Evolution.IsStrongSolution.of_deriv fun t _ => ⟨formsShort.wave ⟨_, modeComb_mem _ _⟩,
    formsShort.wave.mem_graph ⟨_, modeComb_mem _ _⟩, ?_⟩
  rw [← waveOf_eq (modeComb_mem _ _), waveOf_modeComb]
  simp only [add_zero]
  have hω := modeFreq_pos
  have hc : HasDerivAt (fun r => Real.cos (modeFreq * r)) (-(modeFreq * Real.sin (modeFreq * t)))
      t := by
    have := ((hasDerivAt_id' t).const_mul modeFreq).cos
    convert this using 1; ring
  have hs : HasDerivAt (fun r => Real.sin (modeFreq * r) / modeFreq) (Real.cos (modeFreq * t))
      t := by
    have := (((hasDerivAt_id' t).const_mul modeFreq).sin).div_const modeFreq
    convert this using 1; field_simp
  have h := (hc.smul_const modeU).add (hs.smul_const modeY)
  refine h.hasDerivWithinAt.congr_deriv ?_
  rw [modeComb, mul_div_assoc', ← modeFreq_sq]
  congr 1
  congr 1
  field_simp

theorem modeG_zero : modeG 0 = modeU := by simp [modeG, modeComb]

theorem memDomainPow_modeU : MemDomainPow formsShort.wave 3 modeU := by
  refine ⟨modeU_mem, ?_⟩
  change MemDomainPow formsShort.wave 2 (waveOf modeU)
  rw [waveOf_modeU]
  refine ⟨modeY_mem, ?_⟩
  change MemDomainPow formsShort.wave 1 (waveOf modeY)
  rw [waveOf_modeY]
  exact ⟨Submodule.smul_mem _ _ modeU_mem, trivial⟩

theorem waveOrbit_modeU {T : ℝ} : ∀ t ∈ Icc 0 T, waveOrbit modeU t = modeG t :=
  (isStrongSolution_waveOrbit memDomainPow_modeU T).unique
    formsShort.isSkewAdjoint_wave.isDissipative (isStrongSolution_modeG _)
    (by rw [waveOrbit_zero, modeG_zero])

theorem dt1_tangentialU_ne_zero : bggSegment.dt1 tangentialU ≠ 0 := by
  intro h
  have e := inner_dt1_tangentialU tangentialU
  rw [h, inner_zero_left, waveTangentialSrc_eq, inner_smul_left, real_inner_self_eq_norm_sq,
    norm_incl1] at e
  have hn : ‖tangentialU‖ ≠ 0 := norm_ne_zero_iff.2 tangentialU_ne_zero
  have hpi := Real.pi_pos
  have : (8 * π ^ 2 : ℝ) * ‖tangentialU‖ ^ 2 = 0 := by simpa using e.symm
  rcases mul_eq_zero.1 this with h1 | h1
  · nlinarith
  · exact hn (pow_eq_zero_iff (by norm_num) |>.1 h1)

/-- **The mode is not stationary**: `U(t) ≠ U(0)` as soon as `sin(ωt) ≠ 0`. -/
theorem modeG_ne_modeU {t : ℝ} (ht : Real.sin (modeFreq * t) ≠ 0) : modeG t ≠ modeU := by
  intro h
  have h2 := congrArg comp2 h
  change comp2L (modeG t) = comp2L modeU at h2
  rw [modeG, modeComb, map_add, map_smul, map_smul] at h2
  change Real.cos (modeFreq * t) • (0 : WithLp 2 (W2 × Wv W2)) +
    (Real.sin (modeFreq * t) / modeFreq) •
      (WithLp.toLp 2 ((0 : W2), bggSegment.dt1 tangentialU) : WithLp 2 (W2 × Wv W2)) = 0 at h2
  rw [smul_zero, zero_add, smul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact ht (by have := modeFreq_pos; field_simp at h2; simpa using h2)
  · have := congrArg (fun w : WithLp 2 (W2 × Wv W2) => (WithLp.ofLp w).2) h2
    exact dt1_tangentialU_ne_zero this

end Mode

/-! ### Non-vacuity, and the kernel obstruction for the top rows -/

section NonVacuity

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

set_option maxHeartbeats 4000000

open Real

theorem multOf_waveOrbit_modeU {T t : ℝ} (ht : t ∈ Icc 0 T) (j : ℕ) (μ : U1) :
    multOf (aOf (waveOf^[j] (waveOrbit modeU t))) (bOf (waveOf^[j] (waveOrbit modeU t))) μ = 0 := by
  rw [waveOrbit_modeU t ht, modeG]
  obtain ⟨α, β, h⟩ := iterate_waveOf_modeComb j (Real.cos (modeFreq * t))
    (Real.sin (modeFreq * t) / modeFreq)
  rw [h, multOf_modeComb]

theorem compML_waveOrbit_modeU {T t : ℝ} (ht : t ∈ Icc 0 T) (j : ℕ) :
    compML (waveOf^[j] (waveOrbit modeU t)) = 0 := by
  rw [waveOrbit_modeU t ht, modeG]
  obtain ⟨α, β, h⟩ := iterate_waveOf_modeComb j (Real.cos (modeFreq * t))
    (Real.sin (modeFreq * t) / modeFreq)
  rw [h, compML_modeComb]

theorem compρL_modeU (a : Fin 3) : compρL modeU a = 0 := rfl

/-- `ω t₀ ∈ (0, π/2]` for `t₀ = min T (π / (2ω))`. -/
theorem sin_modeFreq_min_ne_zero {T : ℝ} (hT0 : 0 < T) :
    Real.sin (modeFreq * min T (π / (2 * modeFreq))) ≠ 0 := by
  have hω := modeFreq_pos
  have hpi := Real.pi_pos
  refine (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
  calc modeFreq * min T (π / (2 * modeFreq)) ≤ modeFreq * (π / (2 * modeFreq)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hω.le
    _ = π / 2 := by field_simp
    _ < π := by linarith

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- **Non-vacuity of `waveFEM_rate_of_mem_domain`**: the hypotheses hold, with `Λ = 0`, for the
non-stationary standing wave `U(t) = cos(ωt) (0, u, 0) + ω⁻¹ sin(ωt) (0, 0, (0, du))`,
`u = ((sin 2πy₁ sin 2πy₂) dx₀, 0, 0)` (`tangentialU`, `ω² = 8π²`), whose orbit is
`waveOrbit_modeU`: the multipliers vanish (`div u = 0`), `M ≡ 0`, `ρ(0) = 0`; so the scheme (6.5)
converges at `O(h)` to it, with a constant `K (Σ_{j ≤ 3} ‖Lʲ U₀‖)`. -/
theorem waveFEM_rate_of_mem_domain_nonvacuous :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T),
      (∃ t ∈ Icc 0 T, waveOrbit modeU t ≠ modeU) ∧
      ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH
              ((orbitExact memDomainPow_modeU T).σ 0) ((orbitExact memDomainPow_modeU T).φ 0)
              ((orbitExact memDomainPow_modeU T).u 0) ((orbitExact memDomainPow_modeU T).M 0)
              ((orbitExact memDomainPow_modeU T).ρ 0) ((orbitExact memDomainPow_modeU T).ℓ 0))
              0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖(orbitExact memDomainPow_modeU T).σ t - sh.σ t‖ ^ 2 +
          ‖(orbitExact memDomainPow_modeU T).u t - sh.u t‖ ^ 2 +
          ‖(orbitExact memDomainPow_modeU T).M t - sh.M t‖ ^ 2 +
          ‖(orbitExact memDomainPow_modeU T).ρ t - sh.ρ t‖ ^ 2) ≤
            K * domNorm3 modeU * (1 + t) * meshSize N := by
  have hrate := waveFEM_rate_of_mem_domain hT hB
  obtain ⟨K, hK⟩ := hrate
  have hK0 := hK.1
  refine ⟨K, hK0, fun N T hT0 => ⟨?_, ?_⟩⟩
  · have hω := modeFreq_pos
    refine ⟨min T (π / (2 * modeFreq)), ⟨by positivity, min_le_left _ _⟩, ?_⟩
    rw [waveOrbit_modeU _ ⟨by positivity, min_le_left _ _⟩]
    exact modeG_ne_modeU (sin_modeFreq_min_ne_zero hT0)
  · have hpt : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
    have hm0 : ∀ μ : U1, |multOf (aOf modeU) (bOf modeU) μ| ≤ 0 * ‖μ‖ := fun μ => by
      have h := multOf_waveOrbit_modeU hpt 0 μ
      rw [Function.iterate_zero_apply, waveOrbit_zero] at h
      rw [h, abs_zero, zero_mul]
    have hm : ∀ t ∈ Icc 0 T, ∀ j, 1 ≤ j → j ≤ 2 → ∀ μ : U1,
        |multOf (aOf (waveOf^[j] (waveOrbit modeU t))) (bOf (waveOf^[j] (waveOrbit modeU t))) μ|
          ≤ 0 * ‖μ‖ := fun t ht j _ _ μ => by
      rw [multOf_waveOrbit_modeU ht, abs_zero, zero_mul]
    have hM0 : SobRel 1 0 2 (compML modeU) := by
      have h := compML_waveOrbit_modeU hpt 0
      rw [Function.iterate_zero_apply, waveOrbit_zero] at h
      rw [h]; exact sobRel_zero le_rfl 2
    have hM : ∀ t ∈ Icc 0 T, ∀ j, 1 ≤ j → j ≤ 2 →
        SobRel 1 0 2 (compML (waveOf^[j] (waveOrbit modeU t))) := fun t ht j _ _ => by
      rw [compML_waveOrbit_modeU ht j]; exact sobRel_zero le_rfl 2
    have hP : projKer modeU = 0 := by
      have e : modeU = (-(8 * π ^ 2))⁻¹ • formsShort.wave ⟨modeY, modeY_mem⟩ := by
        rw [← waveOf_eq modeY_mem, waveOf_modeY, smul_smul,
          inv_mul_cancel₀ (neg_ne_zero.2 (by positivity)), one_smul]
      rw [e]
      exact projKerOf_smul_eq_zero formsShort.isSkewAdjoint_wave _ _
    have hρ : ∀ a, SobRel 1 0 2 (compρL (projKer modeU) a) := fun a => by
      rw [hP, map_zero, PiLp.zero_apply]; exact sobRel_zero le_rfl 2
    have hres := hK.2 N hT0 memDomainPow_modeU le_rfl hm0 hm hM0 hM hρ
    obtain ⟨sh, hsh⟩ := hres
    have h1 := hsh.1
    have h2 := hsh.2
    exact ⟨sh, h1, fun t ht => by simpa only [mul_zero, add_zero] using h2 t ht⟩

/-- **(c) `D(L^∞)` does not control the top rows**: the stationary state `(0, 0, (0, (q, 0, 0)))`,
`q` the sawtooth 2-form `sawW2` (`d¹* q = 0`), lies in the kernel of `L`, hence in every `D(Lᵏ)`,
while its row `ρ₀ = q` is neither in `H̊Λ²(Q) = D(d²)` (nonzero tangential trace on `{y₀ = 0}`)
nor in `H^{1/2}` of the relative class: the hypothesis on `ρ(0)` in
`waveFEM_rate_of_mem_domain` is not implied by any power of the domain. -/
theorem exists_memDomainPow_compρL_not_mem :
    ∃ U₀ : WS, (∀ k, MemDomainPow formsShort.wave k U₀) ∧ (∀ t, waveOrbit U₀ t = U₀) ∧
      compρL U₀ 0 ∉ D2min.domain ∧ ∀ L, ¬ SobRel (1 / 2) L 2 (compρL U₀ 0) := by
  obtain ⟨hq, hq0⟩ := exists_mem_adjoint_of_abs_le D1 dense_D1_domain le_rfl (y := sawW2)
    fun w => by rw [inner_sawW2_D1, abs_zero, zero_mul]
  have hq0' : D1† ⟨sawW2, hq⟩ = 0 := norm_le_zero_iff.1 hq0
  obtain ⟨hz, h0⟩ := kerRho_mem_ker (a := 0) hq hq0'
  have h0' : formsShort.wave ⟨_, hz⟩ = 0 := by rw [← waveOf_eq hz, h0]
  have hρ : compρL (kerRho 0 sawW2) 0 = sawW2 := single3_apply_self 0 sawW2
  refine ⟨kerRho 0 sawW2, memDomainPow_of_mem_ker hz h0',
    fun t => group_S_eq_self formsShort.isSkewAdjoint_wave hz h0' t, ?_, fun L => ?_⟩
  · rw [hρ]; exact sawW2_not_mem_D2min
  · rw [hρ]; exact not_sobRel_sawW2_half L

set_option maxHeartbeats 8000000 in
/-- **`waveFEM_rate_of_mem_domain` with the smoothing estimates discharged** (the common smoother of
both rows of Table 6.1, `tableRows_uniform_cochainProjection`). -/
theorem waveFEM_rate_of_mem_domain_cube :
    ∃ (p : ℕ → SmoothingParam (Fin 3 → ℝ)) (C : ℝ)
      (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
      (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C),
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T) {U₀ : WS}
      (hU₀ : MemDomainPow formsShort.wave 3 U₀) {Λ : ℝ}, 0 ≤ Λ →
      (∀ μ : U1, |multOf (aOf U₀) (bOf U₀) μ| ≤ Λ * ‖μ‖) →
      (∀ t ∈ Icc 0 T, ∀ j, 1 ≤ j → j ≤ 2 → ∀ μ : U1,
        |multOf (aOf (waveOf^[j] (waveOrbit U₀ t))) (bOf (waveOf^[j] (waveOrbit U₀ t))) μ| ≤
          Λ * ‖μ‖) →
      SobRel 1 Λ 2 (compML U₀) →
      (∀ t ∈ Icc 0 T, ∀ j, 1 ≤ j → j ≤ 2 →
        SobRel 1 Λ 2 (compML (waveOf^[j] (waveOrbit U₀ t)))) →
      (∀ a, SobRel 1 Λ 2 (compρL (projKer U₀) a)) →
      ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH
              ((orbitExact hU₀ T).σ 0) ((orbitExact hU₀ T).φ 0) ((orbitExact hU₀ T).u 0)
              ((orbitExact hU₀ T).M 0) ((orbitExact hU₀ T).ρ 0) ((orbitExact hU₀ T).ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖(orbitExact hU₀ T).σ t - sh.σ t‖ ^ 2 +
          ‖(orbitExact hU₀ T).u t - sh.u t‖ ^ 2 + ‖(orbitExact hU₀ T).M t - sh.M t‖ ^ 2 +
          ‖(orbitExact hU₀ T).ρ t - sh.ρ t‖ ^ 2) ≤
            K * (domNorm3 U₀ + (1 + T) * Λ) * (1 + t) * meshSize N := by
  have hrows := tableRows_uniform_cochainProjection
  obtain ⟨p, C, hT, hB, -⟩ := hrows
  exact ⟨p, C, hT, hB, waveFEM_rate_of_mem_domain hT hB⟩

end NonVacuity

end Feec.EinsteinBianchi.WaveFEM
