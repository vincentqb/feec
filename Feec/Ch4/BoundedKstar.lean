module

public import Feec.Ch4.BoundedSalvageMax
public import Feec.Ch4.BoundedSym
public import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-!
# When does `K*` contain moving data? A spectral mechanism

`Feec.Ch4.BoundedSalvageMax` introduces, for an orthogonal group `S` (generator `L`) and a closed
constraint space `K`, the largest invariant subspace `K* = {x | S t x ∈ K for all t}` (`Kmax`).
For the thesis' complexes on bounded domains every element of `K*` exhibited there is stationary,
and on the box with the thesis' boundary conditions (parity model) `K*` consists exactly of
stationary data, and forward invariance (`t ≥ 0`) already forces this (`Feec.Ch4.BoxForward`,
via Cesàro means of the mode-wise trigonometric flow). This file isolates the abstract mechanism
behind the box proof and reduces the question for general domains to an eigenvalue problem.

## Abstract part (any orthogonal group on a real Hilbert space)

* `Per G τ = {x | S τ x = x}`, `Stat G = {x | S t x = x ∀ t}`; `PurePoint G`: the periodic vectors
  span a dense subspace; `FreqSub G ω` (`ω > 0`): `S t v = cos(ωt) v + sin(ωt) S(π/(2ω)) v`, which
  is exactly the eigenspace `L² v = -ω² v` (`isEigenSq_of_mem_Freq`, `mem_Freq_of_isEigenSq`);
  `EigenDense G`: `Stat` and the `FreqSub ω` span a dense subspace (`L` has a complete set of
  eigenvectors; `eigenDense_of_isEigenSq`, and `purePoint_of_eigenDense`).
* **`starProjection_Per_mem_Kmax`** (no hypothesis): if `S t x ∈ K` for `t ≥ 0`, then the
  projection of `x` onto the `τ`-periodic vectors lies in `K*`, for every `τ > 0`. Proof: von
  Neumann's mean ergodic theorem for `S τ` (Mathlib) and periodicity.
* **`mem_Kmax_of_forward`**: under `PurePoint`, forward invariance implies `x ∈ K*`. This is the
  general form of the box statement `Feec.Box.forward_iff_mem_Kmax`; without a spectral
  hypothesis it is false (the transport example, not formalized, in the docstring of
  `Feec.Ch4.BoundedSalvageMax`).
* **`Kmax_le_Stat`**: under `PurePoint`, `K*` is stationary iff its periodic elements are.
* **`exists_isEigenSq_mem_Kmax`**: under `EigenDense`, a non-stationary `K*` contains a nonzero
  eigenvector of `L²` with eigenvalue `-ω²`, `ω > 0` (`K*` is reducing, so its projection
  commutes with the spectral projections onto `FreqSub ω`).
* **`mem_Kmax_iff_of_isEigenSq`**: such an eigenvector lies in `K*` iff `v ∈ K` and `L v ∈ K`
  (its orbit is `cos(ωt) v + (sin(ωt)/ω) L v`, `S_eq_of_isEigenSq`).

## The Hodge wave (4.14), any Hilbert complex, `K = {0} × S1 × S2`

* **`Kmax_le_Stat_iff`**, **`Kmax_le_Stat_iff_harmonic`** (no hypothesis): `K*` is stationary iff
  every `E ∈ S1*` is harmonic (`E ∈ V1 ∩ V1*`, `d1 E = 0`, `d0* E = 0`). Only the electric slot
  matters: for `(0, E, B) ∈ D(L) ∩ K*`, `d1* B ∈ S1*`, and a harmonic `d1* B` is `0`.
* **`eigen_mem_S1max`** (no hypothesis) and **`not_Kmax_le_Stat_iff`** (`⇒` under
  `EigenDense`): `K*` contains a non-stationary datum iff there are `ω > 0` and `u ≠ 0` with
  `u ∈ S1 ∩ V1 ∩ V1*`, `d0* u = 0`, `d1 u ∈ S2 ∩ V2*`, `d1* d1 u = ω² u`; then
  `S t (0, u, 0) = (0, cos(ωt) u, (sin(ωt)/ω) d1 u)`.
* `Kmax_spectral`: the three statements together for `S1 ≤ ker d0*`.

## Bounded domains

`Feec.BoundedDomain.thesisComplex_Kmax_spectral` (complex of Prop 4.17,
`H̊¹(V) → H̊(curl, M) → L²(M)`) and `Feec.BoundedSym.symComplexB_Kmax_spectral` (complex (4.16))
apply this with `K = {0} × L²(TSD) × L²(TSD)`. The one hypothesis, `EigenDense G`, is explicit
and documented: it stands for the pure point spectrum of the Hodge wave operator, which follows
from the compactness property of the complex (Rellich, and a Weber–Weck selection theorem for
`H̊(curl) ∩ H(div)`); Mathlib has neither, and the selection theorem is known under boundary
regularity, so `EigenDense` is **not** proved for any domain here. Under it: forward invariance
⇔ `K*`, and `K*` contains a moving datum iff `curl* curl u = ω² u` (`ω > 0`) has a nonzero solution
`u ∈ L²(TSD) ∩ H̊(curl, M)` with `curl u ∈ L²(TSD)`; every such `u` lies in `S1* ⊆ L²(TSD₀)`.

What is not decided: whether such TSD eigenfields exist on a given bounded domain. On the box,
in the parity model, `K*` has no non-stationary element (`Feec.Box.thesisBox_mem_Kmax_iff`).
Not formalized (heuristic, for smooth `u` and `Ω`): a symmetric trace-free `u` with zero
tangential trace row-wise vanishes on `∂Ω`, and for `u ∈ L²(TSD)`, `curl curl u = -Δu`; so `u`
would be a divergence-free, symmetric, trace-free Dirichlet eigenfield of the vector Laplacian,
an overdetermined problem whose solvability on a given `Ω` is not settled here.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17), §4.11 (Prop 4.19)
* [Pazy1983], §1.10 (groups, reducing subspaces)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace LinearPMap
open Set Filter Topology

namespace Feec.Constraints

section Periodic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : E →ₗ.[ℝ] E} (G : UnitaryGroupGenerator L)

/-- The `τ`-periodic vectors: `Per τ = {x | S τ x = x}`. -/
def Per (τ : ℝ) : Submodule ℝ E := (G.S τ).eqLocus (1 : E →L[ℝ] E)

/-- The stationary vectors: `Stat = {x | S t x = x for all t}`. -/
def Stat : Submodule ℝ E := ⨅ t, Per G t

variable {G}

theorem mem_Per {τ : ℝ} {x : E} : x ∈ Per G τ ↔ G.S τ x = x := by
  simp [Per]

theorem mem_Stat {x : E} : x ∈ Stat G ↔ ∀ t, G.S t x = x := by
  simp [Stat, mem_Per]

theorem Stat_le_Per (τ : ℝ) : Stat G ≤ Per G τ := fun _ hx => mem_Per.2 (mem_Stat.1 hx τ)

theorem isClosed_Per (τ : ℝ) : IsClosed (Per G τ : Set E) :=
  ContinuousLinearMap.isClosed_eqLocus (G.S τ) 1

theorem isClosed_Stat : IsClosed (Stat G : Set E) := by
  have e : (Stat G : Set E) = ⋂ t, (Per G t : Set E) := by ext; simp [Stat]
  rw [e]; exact isClosed_iInter fun t => isClosed_Per t

theorem iterate_S (τ : ℝ) (n : ℕ) (x : E) : (G.S τ)^[n] x = G.S (n * τ) x := by
  induction n with
  | zero => simp [G.map_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, ← mul_apply_eq_comp, ← G.map_add]
    congr 2; push_cast; ring

theorem S_nat_mul_of_mem_Per {τ : ℝ} {x : E} (hx : x ∈ Per G τ) (n : ℕ) :
    G.S (n * τ) x = x := by
  rw [← iterate_S]
  exact Function.iterate_fixed (mem_Per.1 hx) n

theorem norm_S_le_one (t : ℝ) : ‖G.S t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [G.norm_map, one_mul]

variable [CompleteSpace E]

instance (τ : ℝ) : (Per G τ).HasOrthogonalProjection := by
  have : CompleteSpace (Per G τ) := (isClosed_Per τ).completeSpace_coe
  infer_instance

instance : (Stat G).HasOrthogonalProjection := by
  have : CompleteSpace (Stat G) := isClosed_Stat.completeSpace_coe
  infer_instance

/-- **Mean ergodic theorem for the time-`τ` map**:
`N⁻¹ Σ_{n < N} S(n τ) x → P_{Per τ} x`. -/
theorem tendsto_birkhoffAverage_S (τ : ℝ) (x : E) :
    Tendsto (fun N => birkhoffAverage ℝ (G.S τ) _root_.id N x) atTop
      (𝓝 ((Per G τ).starProjection x)) :=
  (G.S τ).tendsto_birkhoffAverage_orthogonalProjection (norm_S_le_one τ) x

/-- **The periodic part of a forward-invariant datum lies in `K*`.** If `K` is closed and
`S t x ∈ K` for all `t ≥ 0`, then for every `τ > 0` the projection of `x` onto the `τ`-periodic
vectors lies in `K* = Kmax G K`. No spectral hypothesis. -/
theorem starProjection_Per_mem_Kmax {K : Submodule ℝ E} (hK : IsClosed (K : Set E)) {τ : ℝ}
    (hτ : 0 < τ) {x : E} (hx : ∀ t, 0 ≤ t → G.S t x ∈ K) :
    (Per G τ).starProjection x ∈ Kmax G K := by
  set p := (Per G τ).starProjection x
  have hfwd : ∀ s, 0 ≤ s → G.S s p ∈ K := by
    intro s hs
    have ht := ((G.S s).continuous.tendsto _).comp (tendsto_birkhoffAverage_S (G := G) τ x)
    refine hK.mem_of_tendsto ht (Eventually.of_forall fun N => ?_)
    simp only [Function.comp_apply, birkhoffAverage, birkhoffSum, map_smul, map_sum, id]
    refine K.smul_mem _ (K.sum_mem fun n _ => ?_)
    rw [iterate_S, ← mul_apply_eq_comp, ← G.map_add]
    exact hx _ (by have := hτ.le; positivity)
  intro t
  obtain ⟨n, hn⟩ := exists_nat_ge (-t / τ)
  have hp : p ∈ Per G τ := (Per G τ).starProjection_apply_mem x
  rw [← S_nat_mul_of_mem_Per hp n, ← mul_apply_eq_comp, ← G.map_add]
  refine hfwd _ ?_
  have := (div_le_iff₀ hτ).1 hn
  linarith

variable (G) in
/-- Pure point spectrum, in group form: the periodic vectors span a dense subspace. -/
def PurePoint : Prop := Dense ((⨆ τ : Ioi (0 : ℝ), Per G τ : Submodule ℝ E) : Set E)

theorem eq_zero_of_starProjection_Per (hPP : PurePoint G) {z : E}
    (h : ∀ τ, 0 < τ → (Per G τ).starProjection z = 0) : z = 0 := by
  let Z : Submodule ℝ E := LinearMap.ker (innerSL ℝ z).toLinearMap
  have hle : (⨆ τ : Ioi (0 : ℝ), Per G τ : Submodule ℝ E) ≤ Z := by
    refine iSup_le fun τ y hy => ?_
    have hz : z ∈ (Per G τ)ᗮ := by
      simpa [h τ τ.2] using (Per G τ).sub_starProjection_mem_orthogonal z
    simp only [Z, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hy hz
  have hZ : IsClosed (Z : Set E) := (innerSL ℝ z).isClosed_ker
  have : z ∈ Z := by
    have := closure_mono hle (hPP z)
    rwa [hZ.closure_eq] at this
  simpa [Z] using this

omit [CompleteSpace E] in
theorem starProjection_eq_zero_of_mem {N P : Submodule ℝ E} [P.HasOrthogonalProjection] {z : E}
    (hz : z ∈ Nᗮ) (hP : P.starProjection z ∈ N) : P.starProjection z = 0 := by
  have h1 : ⟪P.starProjection z, z - P.starProjection z⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (P.starProjection_apply_mem z)
      (P.sub_starProjection_mem_orthogonal z)
  have h2 : ⟪P.starProjection z, z⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hP hz
  rw [inner_sub_right, h2, zero_sub, neg_eq_zero] at h1
  exact inner_self_eq_zero.1 h1

/-- **Forward invariance implies `K*` under pure point spectrum.** -/
theorem mem_Kmax_of_forward (hPP : PurePoint G) {K : Submodule ℝ E} (hK : IsClosed (K : Set E))
    {x : E} (hx : ∀ t, 0 ≤ t → G.S t x ∈ K) : x ∈ Kmax G K := by
  have hN : IsClosed (Kmax G K : Set E) := isClosed_Kmax hK
  have : CompleteSpace (Kmax G K) := hN.completeSpace_coe
  set N := Kmax G K
  set z := x - N.starProjection x
  have hz : z ∈ Nᗮ := N.sub_starProjection_mem_orthogonal x
  have h0 : z = 0 := by
    refine eq_zero_of_starProjection_Per hPP fun τ hτ => starProjection_eq_zero_of_mem hz ?_
    rw [map_sub]
    refine N.sub_mem (starProjection_Per_mem_Kmax hK hτ hx) (Kmax_le (G := G) (K := N) ?_)
    exact starProjection_Per_mem_Kmax hN hτ fun t _ => S_mem_Kmax (N.starProjection_apply_mem x) t
  have := N.starProjection_apply_mem x
  rwa [← sub_eq_zero.1 h0] at this

/-- **`K*` is stationary iff its periodic elements are**, under pure point spectrum. -/
theorem Kmax_le_Stat (hPP : PurePoint G) {K : Submodule ℝ E} (hK : IsClosed (K : Set E))
    (hkey : ∀ τ, 0 < τ → ∀ x ∈ Kmax G K, x ∈ Per G τ → x ∈ Stat G) : Kmax G K ≤ Stat G := by
  intro x hx
  set z := x - (Stat G).starProjection x
  have hz : z ∈ (Stat G)ᗮ := (Stat G).sub_starProjection_mem_orthogonal x
  have h0 : z = 0 := by
    refine eq_zero_of_starProjection_Per hPP fun τ hτ => starProjection_eq_zero_of_mem hz ?_
    rw [map_sub, (Per G τ).starProjection_eq_self_iff.2
      (Stat_le_Per τ ((Stat G).starProjection_apply_mem x))]
    refine (Stat G).sub_mem (hkey τ hτ _ (Kmax_le (G := G) (K := Kmax G K) ?_)
      ((Per G τ).starProjection_apply_mem x))
      ((Stat G).starProjection_apply_mem x)
    exact starProjection_Per_mem_Kmax (isClosed_Kmax hK) hτ fun t _ => S_mem_Kmax hx t
  have := (Stat G).starProjection_apply_mem x
  rwa [← sub_eq_zero.1 h0] at this

end Periodic

/-! ## Stationary points and eigenvectors of `L²` -/

section Eigen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : E →ₗ.[ℝ] E} {G : UnitaryGroupGenerator L}

/-- A zero of the generator is a stationary point. -/
theorem mem_Stat_of_apply_eq_zero (x : L.domain) (h0 : L x = 0) : (x : E) ∈ Stat G := by
  refine mem_Stat.2 fun t => ?_
  have hd : ∀ s, HasDerivAt (fun s => G.S s x) 0 s := fun s => by
    simpa [h0] using G.hasDerivAt_apply x s
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa [G.map_zero] using hc

/-- A stationary point lies in `D(L)` and is a zero of the generator. -/
theorem apply_eq_zero_of_mem_Stat {x : E} (hx : x ∈ Stat G) :
    ∃ h : x ∈ L.domain, L ⟨x, h⟩ = 0 := by
  have hf : (fun t => G.S t x) = fun _ => x := funext fun t => mem_Stat.1 hx t
  have hdom : x ∈ L.domain :=
    (G.mem_domain_iff x).2 (by rw [hf]; exact differentiableAt_const _)
  refine ⟨hdom, ?_⟩
  have h1 := G.hasDerivAt_zero ⟨x, hdom⟩
  change HasDerivAt (fun t => G.S t x) _ 0 at h1
  rw [hf] at h1
  exact h1.unique (hasDerivAt_const _ _)

/-- If every element of `D(L) ∩ K*` is stationary, so is every element of `K*`. -/
theorem Kmax_le_Stat_of_domain [CompleteSpace E] {K : Submodule ℝ E} [K.HasOrthogonalProjection]
    (h : ∀ x : L.domain, (x : E) ∈ Kmax G K → (x : E) ∈ Stat G) : Kmax G K ≤ Stat G := by
  intro k hk
  have hcl := mem_closure_domain_inter_Kmax (G := G) G.dense_domain k hk
  refine closure_minimal ?_ isClosed_Stat hcl
  rintro y ⟨hy1, hy2⟩
  exact h ⟨y, hy1⟩ hy2

variable (L) in
/-- `v` is an eigenvector of `L²` with eigenvalue `-ω²`: `v ∈ D(L)`, `L v ∈ D(L)`,
`L (L v) = -ω² v`. For skew-adjoint `L` these are the real parts of the eigenvectors of `L` with
eigenvalues `± i ω`. -/
def IsEigenSq (ω : ℝ) (v : E) : Prop :=
  ∃ (h : v ∈ L.domain) (h' : L ⟨v, h⟩ ∈ L.domain), L ⟨L ⟨v, h⟩, h'⟩ = -(ω ^ 2) • v

theorem IsEigenSq.abs {ω : ℝ} {v : E} (hv : IsEigenSq L ω v) : IsEigenSq L |ω| v := by
  obtain ⟨h, h', e⟩ := hv
  exact ⟨h, h', by rw [e, sq_abs]⟩

/-- An eigenvector of `L²` with eigenvalue `0` is stationary (skew-symmetry: `‖L v‖² = 0`). -/
theorem mem_Stat_of_isEigenSq_zero {v : E} (hv : IsEigenSq L 0 v) : v ∈ Stat G := by
  obtain ⟨h, h', e⟩ := hv
  have hs := G.isSkewSymm ⟨L ⟨v, h⟩, h'⟩ ⟨v, h⟩
  simp only [e, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_smul,
    inner_zero_left] at hs
  have hi : ⟪L ⟨v, h⟩, L ⟨v, h⟩⟫ = 0 := by linarith
  have h0 : L ⟨v, h⟩ = 0 := inner_self_eq_zero.1 hi
  exact mem_Stat_of_apply_eq_zero ⟨v, h⟩ h0

/-- **The orbit of an eigenvector**: if `L (L v) = -ω² v` with `ω > 0`, then
`S t v = cos(ω t) v + (sin(ω t) / ω) L v` for all `t` (uniqueness of strong solutions). -/
theorem S_eq_of_isEigenSq [CompleteSpace E] {ω : ℝ} (hω : 0 < ω) {v : E} (h : v ∈ L.domain)
    (h' : L ⟨v, h⟩ ∈ L.domain) (e : L ⟨L ⟨v, h⟩, h'⟩ = -(ω ^ 2) • v) (t : ℝ) :
    G.S t v = Real.cos (ω * t) • v + (Real.sin (ω * t) / ω) • L ⟨v, h⟩ := by
  set w := L ⟨v, h⟩
  let y : ℝ → E := fun s => Real.cos (ω * s) • v + (Real.sin (ω * s) / ω) • w
  have hm : ∀ s, y s ∈ L.domain := fun s =>
    L.domain.add_mem (L.domain.smul_mem _ h) (L.domain.smul_mem _ h')
  have hLy : ∀ s, L ⟨y s, hm s⟩ = Real.cos (ω * s) • w - (ω * Real.sin (ω * s)) • v := by
    intro s
    have : (⟨y s, hm s⟩ : L.domain) =
        Real.cos (ω * s) • (⟨v, h⟩ : L.domain) + (Real.sin (ω * s) / ω) • ⟨w, h'⟩ := rfl
    rw [this, L.map_add, L.map_smul, L.map_smul, e, smul_smul, sub_eq_add_neg, ← neg_smul]
    congr 2
    field_simp
  have hfwd : ∀ T, 0 ≤ T → G.S T v = y T := by
    intro T hT
    have hy : IsStrongSolution L T v 0 y := by
      refine ⟨fun s _ => hm s, fun s _ => ?_, by simp [y]⟩
      rw [Pi.zero_apply, add_zero, hLy]
      have h1 : HasDerivAt (fun s => ω * s) ω s := by
        simpa using (hasDerivAt_id s).const_mul ω
      have hd : HasDerivAt y ((-Real.sin (ω * s) * ω) • v + (Real.cos (ω * s) * ω / ω) • w) s :=
        (h1.cos.smul_const v).add ((h1.sin.div_const ω).smul_const w)
      refine hd.hasDerivWithinAt.congr_deriv ?_
      rw [mul_div_cancel_right₀ _ hω.ne']
      module
    exact strongSolution_unique L G.isSkewSymm (isStrongSolution_orbit G T ⟨v, h⟩) hy
      ⟨hT, le_rfl⟩
  have hper : ∀ s (n : ℕ), y (s + n * (2 * Real.pi / ω)) = y s := by
    intro s n
    have : ω * (s + n * (2 * Real.pi / ω)) = ω * s + n * (2 * Real.pi) := by
      field_simp
    simp only [y, this, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
  have hτ : 0 < 2 * Real.pi / ω := by positivity
  have hvP : ∀ n : ℕ, G.S (n * (2 * Real.pi / ω)) v = v := by
    intro n
    rw [hfwd _ (by positivity), ← zero_add ((n : ℝ) * _), hper]
    simp [y]
  obtain ⟨n, hn⟩ := exists_nat_ge (-t / (2 * Real.pi / ω))
  have hn' : 0 ≤ t + n * (2 * Real.pi / ω) := by
    have := (div_le_iff₀ hτ).1 hn
    linarith
  show G.S t v = y t
  rw [← hper t n, ← hfwd _ hn', G.map_add, mul_apply_eq_comp, hvP]

/-- Eigenvectors of `L²` with eigenvalue `-ω²`, `ω > 0`, are `2π/ω`-periodic. -/
theorem mem_Per_of_isEigenSq [CompleteSpace E] {ω : ℝ} (hω : 0 < ω) {v : E}
    (hv : IsEigenSq L ω v) : v ∈ Per G (2 * Real.pi / ω) := by
  obtain ⟨h, h', e⟩ := hv
  rw [mem_Per, S_eq_of_isEigenSq hω h h' e]
  have : ω * (2 * Real.pi / ω) = 2 * Real.pi := by field_simp
  simp [this]

/-- **Which eigenvectors propagate**: an eigenvector `v` of `L²` with eigenvalue `-ω²`, `ω > 0`,
lies in `K*` iff `v ∈ K` and `L v ∈ K`. -/
theorem mem_Kmax_iff_of_isEigenSq [CompleteSpace E] {K : Submodule ℝ E}
    [K.HasOrthogonalProjection] {ω : ℝ} (hω : 0 < ω) {v : E} (h : v ∈ L.domain)
    (h' : L ⟨v, h⟩ ∈ L.domain) (e : L ⟨L ⟨v, h⟩, h'⟩ = -(ω ^ 2) • v) :
    v ∈ Kmax G K ↔ v ∈ K ∧ L ⟨v, h⟩ ∈ K := by
  constructor
  · intro hv
    exact ⟨Kmax_le hv, Kmax_le (apply_mem_Kmax ⟨v, h⟩ hv)⟩
  · rintro ⟨h1, h2⟩ t
    rw [S_eq_of_isEigenSq hω h h' e]
    exact K.add_mem (K.smul_mem _ h1) (K.smul_mem _ h2)

/-- A nonzero eigenvector of `L²` with eigenvalue `-ω² ≠ 0` is not stationary. -/
theorem not_mem_Stat_of_isEigenSq {ω : ℝ} (hω : ω ≠ 0) {v : E} (hv : IsEigenSq L ω v)
    (hv0 : v ≠ 0) : v ∉ Stat G := by
  intro hs
  obtain ⟨h, h', e⟩ := hv
  obtain ⟨h'', e0⟩ := apply_eq_zero_of_mem_Stat (G := G) hs
  have hw : L ⟨v, h⟩ = 0 := e0
  have : (⟨L ⟨v, h⟩, h'⟩ : L.domain) = 0 := Subtype.ext hw
  rw [this, LinearPMap.map_zero] at e
  exact hv0 (smul_eq_zero.1 e.symm |>.resolve_left (by simpa using hω))

/-- **An eigenbasis gives pure point spectrum**: if eigenvectors of `L²` span a dense subspace,
then the periodic vectors do (`PurePoint`). -/
theorem purePoint_of_isEigenSq [CompleteSpace E] {ι : Type*} (e : ι → E) (ω : ι → ℝ)
    (he : ∀ i, IsEigenSq L (ω i) (e i)) (hd : Dense (Submodule.span ℝ (Set.range e) : Set E)) :
    PurePoint G := by
  refine hd.mono (Submodule.span_le.2 ?_)
  rintro _ ⟨i, rfl⟩
  by_cases h0 : ω i = 0
  · have := mem_Stat_of_isEigenSq_zero (G := G) (h0 ▸ he i)
    exact (le_iSup (fun τ : Ioi (0 : ℝ) => Per G τ) ⟨1, one_pos⟩) (Stat_le_Per 1 this)
  · have hp := abs_pos.2 h0
    have := mem_Per_of_isEigenSq (G := G) hp (he i).abs
    exact (le_iSup (fun τ : Ioi (0 : ℝ) => Per G τ)
      ⟨2 * Real.pi / |ω i|, Set.mem_Ioi.2 (by positivity)⟩) this

end Eigen

/-! ## Frequency subspaces and spectral extraction from `K*` -/

section Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {L : E →ₗ.[ℝ] E} {G : UnitaryGroupGenerator L}

omit [CompleteSpace E] in
theorem inner_S_S (t : ℝ) (a b : E) : ⟪G.S t a, G.S t b⟫ = ⟪a, b⟫ := by
  rw [G.inner_S_left, ← mul_apply_eq_comp, ← G.map_add, neg_add_cancel, G.map_zero,
    one_apply_eq_self]

variable (G) in
/-- The frequency-`ω` subspace: `v` with `S t v = cos(ω t) v + sin(ω t) S(π/(2ω)) v` for all `t`.
For `ω > 0` it is the eigenspace `ker(L² + ω²)` (`isEigenSq_of_mem_Freq`,
`mem_Freq_of_isEigenSq`). -/
def FreqSub (ω : ℝ) : Submodule ℝ E where
  carrier := {v | ∀ t, G.S t v =
    Real.cos (ω * t) • v + Real.sin (ω * t) • G.S (Real.pi / (2 * ω)) v}
  zero_mem' := fun t => by simp
  add_mem' := fun {a b} ha hb t => by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, ha t, hb t, map_add]
    module
  smul_mem' := fun c x hx t => by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_smul, hx t, map_smul]
    module

omit [CompleteSpace E] in
theorem mem_Freq {ω : ℝ} {v : E} : v ∈ FreqSub G ω ↔ ∀ t, G.S t v =
    Real.cos (ω * t) • v + Real.sin (ω * t) • G.S (Real.pi / (2 * ω)) v := Iff.rfl

omit [CompleteSpace E] in
theorem isClosed_Freq (ω : ℝ) : IsClosed (FreqSub G ω : Set E) := by
  have e : (FreqSub G ω : Set E) = ⋂ t, {v | G.S t v =
      Real.cos (ω * t) • v + Real.sin (ω * t) • G.S (Real.pi / (2 * ω)) v} := by
    ext; simp [mem_Freq]
  rw [e]
  exact isClosed_iInter fun t => isClosed_eq (G.S t).continuous
    ((continuous_const_smul _).add ((continuous_const_smul _).comp (G.S _).continuous))

instance (ω : ℝ) : (FreqSub G ω).HasOrthogonalProjection := by
  have : CompleteSpace (FreqSub G ω) := (isClosed_Freq ω).completeSpace_coe
  infer_instance

omit [CompleteSpace E] in
theorem S_mem_Freq {ω : ℝ} {v : E} (hv : v ∈ FreqSub G ω) (s : ℝ) : G.S s v ∈ FreqSub G ω := by
  intro t
  have hc : ∀ a b : ℝ, G.S a (G.S b v) = G.S b (G.S a v) := fun a b => by
    rw [← mul_apply_eq_comp, G.comm, mul_apply_eq_comp]
  rw [hc t s, hv t, map_add, map_smul, map_smul, hc s]

omit [CompleteSpace E] in
/-- Stationary vectors are orthogonal to the frequency-`ω` subspace, `ω > 0`. -/
theorem inner_eq_zero_of_mem_Stat_Freq {ω : ℝ} (hω : 0 < ω) {s v : E} (hs : s ∈ Stat G)
    (hv : v ∈ FreqSub G ω) : ⟪s, v⟫ = 0 := by
  have h := inner_S_S (G := G) (Real.pi / ω) s v
  rw [mem_Stat.1 hs, hv, show ω * (Real.pi / ω) = Real.pi by field_simp, Real.cos_pi,
    Real.sin_pi, zero_smul, add_zero, neg_one_smul, inner_neg_right] at h
  linarith

omit [CompleteSpace E] in
/-- On the frequency-`ω` subspace, `L v = ω S(π/(2ω)) v`. -/
theorem apply_of_mem_Freq {ω : ℝ} {v : E} (hv : v ∈ FreqSub G ω) :
    ∃ h : v ∈ L.domain, L ⟨v, h⟩ = ω • G.S (Real.pi / (2 * ω)) v := by
  set w := G.S (Real.pi / (2 * ω)) v
  have h1 : HasDerivAt (fun s : ℝ => ω * s) ω 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul ω
  have hd : HasDerivAt (fun t => G.S t v) ((-Real.sin (ω * 0) * ω) • v + (Real.cos (ω * 0) * ω) • w)
      0 := by
    have := (h1.cos.smul_const v).add (h1.sin.smul_const w)
    exact this.congr_of_eventuallyEq (Eventually.of_forall fun t => hv t)
  simp only [mul_zero, Real.sin_zero, neg_zero, zero_mul, zero_smul, Real.cos_zero, one_mul,
    zero_add] at hd
  have hdom : v ∈ L.domain := (G.mem_domain_iff v).2 hd.differentiableAt
  exact ⟨hdom, (G.hasDerivAt_zero ⟨v, hdom⟩).unique hd⟩

omit [CompleteSpace E] in
/-- **Elements of `FreqSub ω`, `ω > 0`, are eigenvectors of `L²`** with eigenvalue `-ω²`. -/
theorem isEigenSq_of_mem_Freq {ω : ℝ} (hω : 0 < ω) {v : E} (hv : v ∈ FreqSub G ω) :
    IsEigenSq L ω v := by
  obtain ⟨h, e⟩ := apply_of_mem_Freq hv
  set w := G.S (Real.pi / (2 * ω)) v
  obtain ⟨hw, ew⟩ := apply_of_mem_Freq (S_mem_Freq hv (Real.pi / (2 * ω)))
  have hww : G.S (Real.pi / (2 * ω)) w = -v := by
    rw [← mul_apply_eq_comp, ← G.map_add, hv, show ω * (Real.pi / (2 * ω) + Real.pi / (2 * ω)) =
      Real.pi by field_simp; ring, Real.cos_pi, Real.sin_pi, zero_smul, add_zero, neg_one_smul]
  have h' : L ⟨v, h⟩ ∈ L.domain := e ▸ L.domain.smul_mem ω hw
  refine ⟨h, h', ?_⟩
  have : (⟨L ⟨v, h⟩, h'⟩ : L.domain) = ω • ⟨w, hw⟩ := Subtype.ext e
  rw [this, L.map_smul, ew, hww]
  module

/-- Eigenvectors of `L²` with eigenvalue `-ω²`, `ω > 0`, lie in `FreqSub ω`. -/
theorem mem_Freq_of_isEigenSq {ω : ℝ} (hω : 0 < ω) {v : E} (hv : IsEigenSq L ω v) :
    v ∈ FreqSub G ω := by
  obtain ⟨h, h', e⟩ := hv
  intro t
  have hq : G.S (Real.pi / (2 * ω)) v = (1 / ω) • L ⟨v, h⟩ := by
    rw [S_eq_of_isEigenSq hω h h' e, show ω * (Real.pi / (2 * ω)) = Real.pi / 2 by field_simp,
      Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, zero_add, one_div]
  rw [S_eq_of_isEigenSq hω h h' e, hq, smul_smul, div_eq_mul_one_div]

omit [CompleteSpace E] in
theorem Freq_le_Per {ω : ℝ} (hω : 0 < ω) : FreqSub G ω ≤ Per G (2 * Real.pi / ω) := fun v hv => by
  rw [mem_Per, hv, show ω * (2 * Real.pi / ω) = 2 * Real.pi by field_simp]
  simp

omit [CompleteSpace E] in
/-- A closed `S`-invariant subspace is reducing: its projection commutes with every `S t`. -/
theorem S_starProjection_of_invariant {M : Submodule ℝ E} [M.HasOrthogonalProjection]
    (hM : ∀ t, ∀ x ∈ M, G.S t x ∈ M) (t : ℝ) (x : E) :
    G.S t (M.starProjection x) = M.starProjection (G.S t x) := by
  refine (M.eq_starProjection_of_mem_orthogonal' (hM t _ (M.starProjection_apply_mem x))
    (z := G.S t (x - M.starProjection x)) ?_ (by rw [map_sub]; abel)).symm
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [real_inner_comm, G.inner_S_left]
  exact Submodule.inner_left_of_mem_orthogonal (hM _ u hu) (M.sub_starProjection_mem_orthogonal x)

omit [CompleteSpace E] in
/-- If `P_N V ⊆ V` for closed `V`, `N`, then `P_V N ⊆ N`. -/
theorem starProjection_mem_of_invariant {V N : Submodule ℝ E} [V.HasOrthogonalProjection]
    [N.HasOrthogonalProjection] (hV : ∀ v ∈ V, N.starProjection v ∈ V) {x : E} (hx : x ∈ N) :
    V.starProjection x ∈ N := by
  set y := V.starProjection x
  have hz : N.starProjection (x - y) ∈ Vᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [← Submodule.inner_starProjection_left_eq_right]
    exact Submodule.inner_right_of_mem_orthogonal (hV v hv) (V.sub_starProjection_mem_orthogonal x)
  have e : V.starProjection x = N.starProjection y :=
    V.eq_starProjection_of_mem_orthogonal' (hV _ (V.starProjection_apply_mem x)) hz
      (by rw [map_sub, (N.starProjection_eq_self_iff).2 hx]; abel)
  rw [show y = N.starProjection y from e]
  exact N.starProjection_apply_mem y

theorem starProjection_Freq_mem_Kmax {K : Submodule ℝ E} (hK : IsClosed (K : Set E)) (ω : ℝ)
    {x : E} (hx : x ∈ Kmax G K) : (FreqSub G ω).starProjection x ∈ Kmax G K := by
  have : CompleteSpace (Kmax G K) := (isClosed_Kmax hK).completeSpace_coe
  have hcomm := S_starProjection_of_invariant (G := G) (M := Kmax G K)
    (fun t _ h => S_mem_Kmax h t)
  refine starProjection_mem_of_invariant (fun v hv t => ?_) hx
  rw [hcomm, hv t, map_add, map_smul, map_smul, ← hcomm]

variable (G) in
/-- **Eigenvector completeness** (pure point spectrum, eigenvector form): the stationary vectors
and the frequency subspaces `FreqSub ω`, `ω > 0`, span a dense subspace. For a skew-adjoint `L`
this is the real form of "`L` has an orthonormal eigenbasis in the complexification"; it is the
standard consequence of a compact resolvent on `(ker L)ᗮ` (not proved here). -/
def EigenDense : Prop :=
  Dense ((Stat G ⊔ ⨆ ω : Ioi (0 : ℝ), FreqSub G ω : Submodule ℝ E) : Set E)

/-- A family of eigenvectors of `L²` with dense span gives `EigenDense`. -/
theorem eigenDense_of_isEigenSq {ι : Type*} (e : ι → E) (ω : ι → ℝ)
    (he : ∀ i, IsEigenSq L (ω i) (e i)) (hd : Dense (Submodule.span ℝ (Set.range e) : Set E)) :
    EigenDense G := by
  refine hd.mono (Submodule.span_le.2 ?_)
  rintro _ ⟨i, rfl⟩
  by_cases h0 : ω i = 0
  · exact Submodule.mem_sup_left (mem_Stat_of_isEigenSq_zero (h0 ▸ he i))
  · have hp := abs_pos.2 h0
    refine Submodule.mem_sup_right ?_
    exact (le_iSup (fun τ : Ioi (0 : ℝ) => FreqSub G τ) ⟨|ω i|, hp⟩)
      (mem_Freq_of_isEigenSq hp (he i).abs)

omit [CompleteSpace E] in
/-- `EigenDense` implies `PurePoint`. -/
theorem purePoint_of_eigenDense (hD : EigenDense G) : PurePoint G := by
  unfold EigenDense at hD
  unfold PurePoint
  refine hD.mono (show (Stat G ⊔ ⨆ ω : Ioi (0 : ℝ), FreqSub G ω : Submodule ℝ E) ≤
    ⨆ τ : Ioi (0 : ℝ), Per G τ from sup_le ?_ (iSup_le fun ω => ?_))
  · exact (Stat_le_Per 1).trans (le_iSup (fun τ : Ioi (0 : ℝ) => Per G τ) ⟨1, one_pos⟩)
  · exact (Freq_le_Per ω.2).trans (le_iSup (fun τ : Ioi (0 : ℝ) => Per G τ)
      ⟨2 * Real.pi / ω, Set.mem_Ioi.2 (div_pos (by positivity) ω.2)⟩)

/-- **Spectral extraction**: under `EigenDense`, if `K*` contains a non-stationary vector, then
it contains a nonzero eigenvector of `L²` with eigenvalue `-ω²`, `ω > 0` (the `FreqSub ω`-component
of that vector, which stays in `K*` because `K*` is reducing). -/
theorem exists_isEigenSq_mem_Kmax (hD : EigenDense G) {K : Submodule ℝ E}
    (hK : IsClosed (K : Set E)) (h : ¬ Kmax G K ≤ Stat G) :
    ∃ ω : ℝ, 0 < ω ∧ ∃ v ∈ Kmax G K, IsEigenSq L ω v ∧ v ≠ 0 := by
  unfold EigenDense at hD
  by_contra hne
  push Not at hne
  refine h fun x hx => ?_
  have hF : ∀ ω : ℝ, 0 < ω → x ∈ (FreqSub G ω)ᗮ := fun ω hω => by
    have hp := starProjection_Freq_mem_Kmax hK ω hx
    have := hne ω hω _ hp (isEigenSq_of_mem_Freq hω ((FreqSub G ω).starProjection_apply_mem x))
    exact (Submodule.starProjection_apply_eq_zero_iff _).1 this
  set z := x - (Stat G).starProjection x
  let Z : Submodule ℝ E := LinearMap.ker (innerSL ℝ z).toLinearMap
  have hZ : ∀ y, y ∈ Z ↔ ⟪z, y⟫ = 0 := fun y => by simp [Z]
  have hle : (Stat G ⊔ ⨆ ω : Ioi (0 : ℝ), FreqSub G ω : Submodule ℝ E) ≤ Z := by
    refine sup_le (fun y hy => (hZ y).2 ?_) (iSup_le fun ω y hy => (hZ y).2 ?_)
    · exact Submodule.inner_left_of_mem_orthogonal hy ((Stat G).sub_starProjection_mem_orthogonal x)
    · rw [inner_sub_left, Submodule.inner_left_of_mem_orthogonal hy (hF ω ω.2),
        inner_eq_zero_of_mem_Stat_Freq ω.2 ((Stat G).starProjection_apply_mem x) hy, sub_zero]
  have hzZ : z ∈ Z := by
    have := closure_mono hle (hD z)
    rwa [(innerSL ℝ z).isClosed_ker.closure_eq] at this
  have hz0 : z = 0 := inner_self_eq_zero.1 ((hZ z).1 hzZ)
  have := (Stat G).starProjection_apply_mem x
  rwa [← sub_eq_zero.1 hz0] at this

end Spectral

/-! ## The Hodge wave (4.14): reduction to the electric slot -/

section Hodge

open HilbertComplex2

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    {H : HilbertComplex2 W0 W1 W2} {G : UnitaryGroupGenerator (-H.waveOp)}
    {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2}

omit [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2] in
theorem tot_eq_zero_iff {x : Tot W0 W1 W2} :
    x = 0 ↔ (tot W0 W1 W2 x).1 = 0 ∧ (tot W0 W1 W2 x).2.1 = 0 ∧ (tot W0 W1 W2 x).2.2 = 0 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1, h2⟩
    apply (tot W0 W1 W2).injective
    rw [_root_.map_zero]
    exact Prod.ext h0 (Prod.ext h1 h2)

/-- **Stationary electric data are harmonic**: `(0, E, 0)` is a stationary point of (4.14) iff
`E ∈ V1 ∩ V1*` with `d1 E = 0` and `d0* E = 0`. -/
theorem ini_mem_Stat_iff {u : W1} : ini W0 u (0 : W2) ∈ Stat G ↔
    ∃ (h1 : u ∈ H.d1.domain) (h2 : u ∈ H.d0†.domain), H.d1 ⟨u, h1⟩ = 0 ∧ H.d0† ⟨u, h2⟩ = 0 := by
  constructor
  · intro hs
    obtain ⟨hD, h0⟩ := apply_eq_zero_of_mem_Stat hs
    have hD' := (mem_domL H).1 hD
    rw [tot_ini] at hD'
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hD'.2.1
    refine ⟨h1, h2, ?_⟩
    rw [LinearPMap.neg_apply, neg_eq_zero, tot_eq_zero_iff, tot_waveOp] at h0
    have hp1 : H.prV1 ⟨ini W0 u 0, hD⟩ = ⟨u, h1⟩ := Subtype.ext (by simp)
    have hp1s : H.prV1s ⟨ini W0 u 0, hD⟩ = ⟨u, h2⟩ := Subtype.ext (by simp)
    simp only [hp1, hp1s, neg_eq_zero] at h0
    exact ⟨h0.2.2, h0.1⟩
  · rintro ⟨h1, h2, e1, e2⟩
    have hD : ini W0 u (0 : W2) ∈ H.domL := by
      rw [mem_domL, tot_ini]
      exact ⟨Submodule.zero_mem _, Submodule.mem_inf.2 ⟨h1, h2⟩, Submodule.zero_mem _⟩
    refine mem_Stat_of_apply_eq_zero (L := -H.waveOp) ⟨ini W0 u 0, hD⟩ ?_
    rw [LinearPMap.neg_apply, neg_eq_zero, tot_eq_zero_iff, tot_waveOp]
    have hp0 : H.pr0 ⟨ini W0 u 0, hD⟩ = 0 := Subtype.ext (by simp)
    have hp1 : H.prV1 ⟨ini W0 u 0, hD⟩ = ⟨u, h1⟩ := Subtype.ext (by simp)
    have hp1s : H.prV1s ⟨ini W0 u 0, hD⟩ = ⟨u, h2⟩ := Subtype.ext (by simp)
    have hp2 : H.prV2s ⟨ini W0 u 0, hD⟩ = 0 := Subtype.ext (by simp)
    simp [hp0, hp1, hp1s, hp2, e1, e2]

variable [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]

/-- **`K*` is stationary iff its electric slot is**: for the Hodge wave (4.14) of any Hilbert
complex and any closed `S1`, `S2`, every element of `K* = Kmax G ({0} × S1 × S2)` is a stationary
point iff every `E ∈ S1*` gives a stationary point `(0, E, 0)`. No spectral hypothesis.

Mechanism: for `x = (0, E, B) ∈ D(L) ∩ K*`, `L x = -(-d0* E, d1* B, -d1 E) ∈ K*`, so
`d1* B ∈ S1*`. If `S1*` is stationary, `d1 E = 0`, `d0* E = 0`, and `u = d1* B` satisfies
`d1 u = 0`, so `‖u‖² = ⟪B, d1 u⟫ = 0`. Hence `L x = 0`; density of `D(L) ∩ K*` in `K*` gives the
rest. -/
theorem Kmax_le_Stat_iff : Kmax G (Kc W0 S1 S2) ≤ Stat G ↔
    ∀ u ∈ S1max G S1 S2, ini W0 u (0 : W2) ∈ Stat G := by
  constructor
  · intro h u hu
    exact h ((mem_S1max G).1 hu)
  · intro h
    refine Kmax_le_Stat_of_domain fun y hy => ?_
    have hc : (y : Tot W0 W1 W2) ∈ Kc W0 (S1max G S1 S2) (S2max G S1 S2) := Kmax_eq_Kc G ▸ hy
    rw [mem_Kc] at hc
    obtain ⟨h1, h2, e1, e2⟩ := ini_mem_Stat_iff.1 (h _ hc.2.1)
    have hLy := apply_mem_Kmax (G := G) (K := Kc W0 S1 S2) y hy
    rw [Kmax_eq_Kc G, mem_Kc, LinearPMap.neg_apply, _root_.map_neg, tot_waveOp] at hLy
    have hp0 : H.pr0 ⟨y.1, y.2⟩ = 0 := Subtype.ext (by simp [hc.1])
    have hp1 : H.prV1 ⟨y.1, y.2⟩ = ⟨_, h1⟩ := Subtype.ext (by simp)
    have hp1s : H.prV1s ⟨y.1, y.2⟩ = ⟨_, h2⟩ := Subtype.ext (by simp)
    simp only [hp0, LinearPMap.map_zero, zero_add, Prod.fst_neg, Prod.snd_neg] at hLy
    set u := H.d1† (H.prV2s ⟨y.1, y.2⟩)
    have hu : u ∈ S1max G S1 S2 := by simpa using (S1max G S1 S2).neg_mem hLy.2.1
    obtain ⟨hu1, -, eu1, -⟩ := ini_mem_Stat_iff.1 (h u hu)
    have hadj := LinearPMap.adjoint_isFormalAdjoint H.dense1 (H.prV2s ⟨y.1, y.2⟩) ⟨u, hu1⟩
    rw [eu1, inner_zero_right] at hadj
    have hu0 : u = 0 := inner_self_eq_zero.1 hadj
    refine mem_Stat_of_apply_eq_zero y ?_
    rw [LinearPMap.neg_apply, neg_eq_zero, tot_eq_zero_iff, tot_waveOp]
    simp only [hp0, hp1, hp1s, e1, e2, LinearPMap.map_zero, zero_add, neg_zero]
    exact ⟨trivial, hu0, trivial⟩

/-- **Harmonic form**: `K*` is stationary iff every `E ∈ S1*` lies in `V1 ∩ V1*` with
`d1 E = 0` and `d0* E = 0`. -/
theorem Kmax_le_Stat_iff_harmonic : Kmax G (Kc W0 S1 S2) ≤ Stat G ↔
    ∀ u ∈ S1max G S1 S2, ∃ (h1 : u ∈ H.d1.domain) (h2 : u ∈ H.d0†.domain),
      H.d1 ⟨u, h1⟩ = 0 ∧ H.d0† ⟨u, h2⟩ = 0 := by
  rw [Kmax_le_Stat_iff]
  exact forall₂_congr fun u _ => ini_mem_Stat_iff

/-- If the electric slot `S1*` is `0`, every element of `K*` is stationary. -/
theorem Kmax_le_Stat_of_S1max_eq_bot (h : S1max G S1 S2 = ⊥) : Kmax G (Kc W0 S1 S2) ≤ Stat G :=
  Kmax_le_Stat_iff.2 fun u hu => by
    rw [h, Submodule.mem_bot] at hu
    subst hu
    have : ini W0 (0 : W1) (0 : W2) = 0 := (tot W0 W1 W2).injective (by simp)
    rw [this]; exact (Stat G).zero_mem

/-- **Electric eigenfields give moving elements of `K*`**: let `ω > 0` and `u ∈ S1` with
`u ∈ V1 ∩ V1*`, `d0* u = 0`, `d1 u ∈ V2* ∩ S2` and `d1* d1 u = ω² u`. Then
`(0, u, 0)` is an eigenvector of `L²` with eigenvalue `-ω²`, `u ∈ S1*`, the orbit is
`S t (0, u, 0) = (0, cos(ωt) u, (sin(ωt)/ω) d1 u)` (`S_eq_of_isEigenSq`), and if `u ≠ 0` it is
not stationary. -/
theorem eigen_mem_S1max {ω : ℝ} (hω : 0 < ω) {u : W1} (hu : u ∈ S1) (h1 : u ∈ H.d1.domain)
    (h2 : u ∈ H.d0†.domain) (e2 : H.d0† ⟨u, h2⟩ = 0) (h3 : H.d1 ⟨u, h1⟩ ∈ H.d1†.domain)
    (h3S : H.d1 ⟨u, h1⟩ ∈ S2) (e3 : H.d1† ⟨_, h3⟩ = ω ^ 2 • u) :
    IsEigenSq (-H.waveOp) ω (ini W0 u (0 : W2)) ∧ u ∈ S1max G S1 S2 ∧
      (u ≠ 0 → ini W0 u (0 : W2) ∉ Stat G) := by
  have hD : ini W0 u (0 : W2) ∈ H.domL := by
    rw [mem_domL, tot_ini]
    exact ⟨Submodule.zero_mem _, Submodule.mem_inf.2 ⟨h1, h2⟩, Submodule.zero_mem _⟩
  have hp0 : H.pr0 ⟨ini W0 u 0, hD⟩ = 0 := Subtype.ext (by simp)
  have hp1 : H.prV1 ⟨ini W0 u 0, hD⟩ = ⟨u, h1⟩ := Subtype.ext (by simp)
  have hp1s : H.prV1s ⟨ini W0 u 0, hD⟩ = ⟨u, h2⟩ := Subtype.ext (by simp)
  have hp2 : H.prV2s ⟨ini W0 u 0, hD⟩ = 0 := Subtype.ext (by simp)
  have hL : (-H.waveOp) ⟨ini W0 u 0, hD⟩ = ini W0 (0 : W1) (H.d1 ⟨u, h1⟩) := by
    apply (tot W0 W1 W2).injective
    rw [LinearPMap.neg_apply, _root_.map_neg, tot_waveOp, tot_ini]
    simp [hp0, hp1, hp1s, hp2, e2]
  have hD2 : ini W0 (0 : W1) (H.d1 ⟨u, h1⟩) ∈ H.domL := ini_mem_domL_B h3
  have hD2' : (-H.waveOp) ⟨ini W0 u 0, hD⟩ ∈ (-H.waveOp).domain := hL ▸ hD2
  have hLL : (-H.waveOp) ⟨(-H.waveOp) ⟨ini W0 u 0, hD⟩, hD2'⟩ = -(ω ^ 2) • ini W0 u (0 : W2) := by
    have hq : (⟨(-H.waveOp) ⟨ini W0 u 0, hD⟩, hD2'⟩ : (-H.waveOp).domain) =
        ⟨ini W0 (0 : W1) (H.d1 ⟨u, h1⟩), hD2⟩ := Subtype.ext hL
    rw [hq]
    have hq0 : H.pr0 ⟨ini W0 (0 : W1) (H.d1 ⟨u, h1⟩), hD2⟩ = 0 := Subtype.ext (by simp)
    have hq1 : H.prV1 ⟨ini W0 (0 : W1) (H.d1 ⟨u, h1⟩), hD2⟩ = 0 := Subtype.ext (by simp)
    have hq1s : H.prV1s ⟨ini W0 (0 : W1) (H.d1 ⟨u, h1⟩), hD2⟩ = 0 := Subtype.ext (by simp)
    have hq2 : H.prV2s ⟨ini W0 (0 : W1) (H.d1 ⟨u, h1⟩), hD2⟩ = ⟨_, h3⟩ := Subtype.ext (by simp)
    apply (tot W0 W1 W2).injective
    rw [LinearPMap.neg_apply, _root_.map_neg, tot_waveOp, _root_.map_smul, tot_ini]
    simp [hq0, hq1, hq1s, hq2, e3]
  have hE : IsEigenSq (-H.waveOp) ω (ini W0 u (0 : W2)) := ⟨hD, hD2', hLL⟩
  refine ⟨hE, ?_, fun hu0 => not_mem_Stat_of_isEigenSq hω.ne' hE fun h0 => hu0 ?_⟩
  · rw [mem_S1max, mem_Kmax_iff_of_isEigenSq (G := G) hω hD hD2' hLL, hL, mem_Kc, mem_Kc,
      tot_ini, tot_ini]
    exact ⟨⟨rfl, hu, Submodule.zero_mem _⟩, ⟨rfl, Submodule.zero_mem _, h3S⟩⟩
  · simpa using congrArg (fun x => (tot W0 W1 W2 x).2.1) h0

/-- **Eigenvectors of `L²` in `K*` come from electric eigenfields**: if `v ∈ K*` is a nonzero
eigenvector of `L²` with eigenvalue `-ω²`, `ω > 0`, then there is `u ≠ 0` with the hypotheses of
`eigen_mem_S1max` (`u` is the electric part of `v` if nonzero, and `-d1* B` otherwise). -/
theorem exists_eigenfield_of_isEigenSq_mem_Kmax {ω : ℝ} (hω : 0 < ω) {v : Tot W0 W1 W2}
    (hvK : v ∈ Kmax G (Kc W0 S1 S2)) (hv : IsEigenSq (-H.waveOp) ω v) (hv0 : v ≠ 0) :
    ∃ u : W1, u ≠ 0 ∧ u ∈ S1 ∧ ∃ (h1 : u ∈ H.d1.domain) (h2 : u ∈ H.d0†.domain),
      H.d0† ⟨u, h2⟩ = 0 ∧ ∃ h3 : H.d1 ⟨u, h1⟩ ∈ H.d1†.domain,
        H.d1 ⟨u, h1⟩ ∈ S2 ∧ H.d1† ⟨_, h3⟩ = ω ^ 2 • u := by
  obtain ⟨h, h', e⟩ := hv
  have hK := (mem_Kc).1 (Kmax_le hvK)
  have hLK := (mem_Kc).1 (Kmax_le (apply_mem_Kmax (G := G) ⟨v, h⟩ hvK))
  have hD := (mem_domL H).1 h
  obtain ⟨hE1, hE2⟩ := Submodule.mem_inf.1 hD.2.1
  have hB := hD.2.2
  have hp0 : H.pr0 ⟨v, h⟩ = 0 := Subtype.ext (by simp [hK.1])
  have hp1 : H.prV1 ⟨v, h⟩ = ⟨_, hE1⟩ := Subtype.ext rfl
  have hp1s : H.prV1s ⟨v, h⟩ = ⟨_, hE2⟩ := Subtype.ext rfl
  have hp2 : H.prV2s ⟨v, h⟩ = ⟨_, hB⟩ := Subtype.ext rfl
  have hTL : tot W0 W1 W2 ((-H.waveOp) ⟨v, h⟩) =
      (H.d0† ⟨_, hE2⟩, -(H.d1† ⟨_, hB⟩), H.d1 ⟨_, hE1⟩) := by
    rw [LinearPMap.neg_apply, _root_.map_neg, tot_waveOp]
    simp [hp0, hp1, hp1s, hp2]
  rw [hTL] at hLK
  obtain ⟨e2, huS, hd1S⟩ := hLK
  have hD' := (mem_domL H).1 h'
  rw [hTL] at hD'
  obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.1 hD'.2.1
  have h3 := hD'.2.2
  have hq0 : H.pr0 ⟨_, h'⟩ = 0 := Subtype.ext (by rw [coe_pr0, hTL]; simpa using e2)
  have hq1 : H.prV1 ⟨_, h'⟩ = ⟨_, hu1⟩ := Subtype.ext (by rw [coe_prV1, hTL])
  have hq1s : H.prV1s ⟨_, h'⟩ = ⟨_, hu2⟩ := Subtype.ext (by rw [coe_prV1s, hTL])
  have hq2 : H.prV2s ⟨_, h'⟩ = ⟨_, h3⟩ := Subtype.ext (by rw [coe_prV2s, hTL])
  have e' := congrArg (tot W0 W1 W2) e
  rw [LinearPMap.neg_apply, _root_.map_neg, tot_waveOp, _root_.map_smul] at e'
  simp only [hq0, hq1, hq1s, hq2, LinearPMap.map_zero, zero_add] at e'
  have eσ : H.d0† ⟨_, hu2⟩ = 0 := by
    have := congrArg Prod.fst e'
    simpa [hK.1] using this
  have eE : H.d1† ⟨_, h3⟩ = ω ^ 2 • (tot W0 W1 W2 v).2.1 := by
    have := congrArg (fun p => p.2.1) e'
    simpa using this
  have eB : H.d1 ⟨_, hu1⟩ = -(ω ^ 2) • (tot W0 W1 W2 v).2.2 := by
    have := congrArg (fun p => p.2.2) e'
    simpa using this
  by_cases hE0 : (tot W0 W1 W2 v).2.1 = 0
  · refine ⟨_, ?_, huS, hu1, hu2, eσ, ?_⟩
    · intro hu0
      have : (⟨_, hu1⟩ : H.d1.domain) = 0 := Subtype.ext hu0
      rw [this, LinearPMap.map_zero] at eB
      have hB0 : (tot W0 W1 W2 v).2.2 = 0 := by
        have := eB.symm
        rw [smul_eq_zero] at this
        exact this.resolve_left (by simpa using hω.ne')
      exact hv0 (tot_eq_zero_iff.2 ⟨hK.1, hE0, hB0⟩)
    · have h3' : H.d1 ⟨_, hu1⟩ ∈ H.d1†.domain := eB ▸ H.d1†.domain.smul_mem _ hB
      refine ⟨h3', eB ▸ S2.smul_mem _ hK.2.2, ?_⟩
      have : (⟨H.d1 ⟨_, hu1⟩, h3'⟩ : H.d1†.domain) = (-(ω ^ 2)) • ⟨_, hB⟩ := Subtype.ext eB
      rw [this, LinearPMap.map_smul, neg_smul, smul_neg]
  · exact ⟨_, hE0, hK.2.1, hE1, hE2, e2, h3, hd1S, eE⟩

/-- **When does `K*` contain a moving datum?** For the Hodge wave (4.14) of any Hilbert complex,
closed `S1`, `S2`, and an orthogonal group whose generator has a complete set of eigenvectors
(`EigenDense`): `K* = Kmax G ({0} × S1 × S2)` contains a non-stationary element iff there are
`ω > 0` and `u ≠ 0` with `u ∈ S1 ∩ V1 ∩ V1*`, `d0* u = 0`, `d1 u ∈ S2 ∩ V2*` and
`d1* d1 u = ω² u` (an electric eigenfield whose curl stays in `S2`). The direction `⇐` needs no
hypothesis. -/
theorem not_Kmax_le_Stat_iff (hD : EigenDense G) :
    ¬ Kmax G (Kc W0 S1 S2) ≤ Stat G ↔ ∃ ω : ℝ, 0 < ω ∧ ∃ u : W1, u ≠ 0 ∧ u ∈ S1 ∧
      ∃ (h1 : u ∈ H.d1.domain) (h2 : u ∈ H.d0†.domain), H.d0† ⟨u, h2⟩ = 0 ∧
        ∃ h3 : H.d1 ⟨u, h1⟩ ∈ H.d1†.domain, H.d1 ⟨u, h1⟩ ∈ S2 ∧ H.d1† ⟨_, h3⟩ = ω ^ 2 • u := by
  constructor
  · intro h
    obtain ⟨ω, hω, v, hvK, hv, hv0⟩ :=
      exists_isEigenSq_mem_Kmax hD (isClosed_of_hasOrthogonalProjection _) h
    exact ⟨ω, hω, exists_eigenfield_of_isEigenSq_mem_Kmax hω hvK hv hv0⟩
  · rintro ⟨ω, hω, u, hu0, hu, h1, h2, e2, h3, h3S, e3⟩ hle
    obtain ⟨-, hm, hns⟩ := eigen_mem_S1max (G := G) hω hu h1 h2 e2 h3 h3S e3
    exact hns hu0 (hle ((mem_S1max G).1 hm))

omit [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection] in
theorem exists_adj0_eq_zero_of_mem_ker {u : W1} (hu : u ∈ H.d0†.ker) :
    ∃ h2 : u ∈ H.d0†.domain, H.d0† ⟨u, h2⟩ = 0 := by
  obtain ⟨y, hyu, hy0⟩ := LinearPMap.mem_ker_iff.1 hu
  subst hyu
  exact ⟨y.2, hy0⟩

/-- **Summary for a complex with `S1 ≤ ker d0*`** (as for (4.14) with `L²(TSD)`), under
`EigenDense`:
1. forward invariance of `K = {0} × S1 × S2` (`t ≥ 0`) is equivalent to `x ∈ K*`;
2. `K*` is stationary iff every `E ∈ S1*` satisfies `E ∈ V1`, `d1 E = 0`
   (this item needs no hypothesis);
3. `K*` contains a non-stationary datum iff there are `ω > 0` and `u ≠ 0` in `S1 ∩ V1` with
   `d1 u ∈ S2 ∩ V2*` and `d1* d1 u = ω² u`. -/
theorem Kmax_spectral (hS1 : S1 ≤ H.d0†.ker) (hD : EigenDense G) :
    (∀ x, (∀ t, 0 ≤ t → G.S t x ∈ Kc W0 S1 S2) ↔ x ∈ Kmax G (Kc W0 S1 S2)) ∧
    (Kmax G (Kc W0 S1 S2) ≤ Stat G ↔
      ∀ u ∈ S1max G S1 S2, ∃ h1 : u ∈ H.d1.domain, H.d1 ⟨u, h1⟩ = 0) ∧
    (¬ Kmax G (Kc W0 S1 S2) ≤ Stat G ↔ ∃ ω : ℝ, 0 < ω ∧ ∃ u : W1, u ≠ 0 ∧ u ∈ S1 ∧
      ∃ (h1 : u ∈ H.d1.domain) (h3 : H.d1 ⟨u, h1⟩ ∈ H.d1†.domain),
        H.d1 ⟨u, h1⟩ ∈ S2 ∧ H.d1† ⟨_, h3⟩ = ω ^ 2 • u) := by
  refine ⟨fun x => ⟨fun h => mem_Kmax_of_forward (purePoint_of_eigenDense hD)
    (isClosed_of_hasOrthogonalProjection _) h, fun h t _ => h t⟩, ?_, ?_⟩
  · rw [Kmax_le_Stat_iff_harmonic]
    refine forall₂_congr fun u hu => ⟨fun ⟨h1, _, e1, _⟩ => ⟨h1, e1⟩, fun ⟨h1, e1⟩ => ?_⟩
    obtain ⟨h2, e2⟩ := exists_adj0_eq_zero_of_mem_ker (hS1 (S1max_le G hu))
    exact ⟨h1, h2, e1, e2⟩
  · rw [not_Kmax_le_Stat_iff hD]
    constructor
    · rintro ⟨ω, hω, u, hu0, hu, h1, -, -, h3, h3S, e3⟩
      exact ⟨ω, hω, u, hu0, hu, h1, h3, h3S, e3⟩
    · rintro ⟨ω, hω, u, hu0, hu, h1, h3, h3S, e3⟩
      obtain ⟨h2, e2⟩ := exists_adj0_eq_zero_of_mem_ker (hS1 hu)
      exact ⟨ω, hω, u, hu0, hu, h1, h2, e2, h3, h3S, e3⟩

end Hodge

end Feec.Constraints

/-! ## Bounded domains: the thesis' complex and (4.16) -/

namespace Feec.BoundedDomain

open Feec.HilbertComplex2 Feec.Constraints

variable {Ω : Set R3} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)

/-- **`K*` on a bounded domain, thesis' complex `H̊¹(V) → H̊(curl, M) → L²(M)`**, for any
orthogonal group `G` generated by its Hodge wave operator and with
`K = {0} × L²(TSD) × L²(TSD)`.

Hypothesis `hD : EigenDense G` (eigenvectors of `L²` together with the stationary data span a
dense subspace). It stands for the spectral consequence of the compactness of the complex
(Rellich for `H̊¹`, a Weber–Weck selection theorem for `H̊(curl, M) ∩ H(div, M)`), which gives
`L` pure point spectrum; Mathlib has neither. Such selection theorems are known under boundary
regularity (e.g. Lipschitz `Ω`); `hD` is not proved here for any `Ω`.

Under `hD`:
1. a datum whose forward orbit (`t ≥ 0`) stays in `K` lies in `K*`;
2. `K*` is stationary iff every `E ∈ S1*` lies in `H̊(curl, M)` with `curl E = 0` (no hypothesis);
3. `K*` contains a non-stationary datum iff there are `ω > 0` and a nonzero
   `u ∈ L²(TSD) ∩ H̊(curl, M)` with `curl u ∈ L²(TSD) ∩ D(curl*)` and `curl* curl u = ω² u`;
4. every such `u` lies in `S1* ⊆ L²(TSD₀)`, and `(0, u, 0)` moves:
   `S t (0, u, 0) = (0, cos(ωt) u, (sin(ωt)/ω) curl u)` (`Feec.Constraints.S_eq_of_isEigenSq`).

Whether such eigenfields exist is not decided here. On the box, in the parity model of
`Feec.Ch4.Box` (a different complex, `Feec.Box.thesisBoxComplex`), `K*` has no non-stationary
element (`Feec.Box.thesisBox_mem_Kmax_iff`). -/
theorem thesisComplex_Kmax_spectral
    (G : UnitaryGroupGenerator (-(thesisComplex hΩ hb).waveOp)) (hD : EigenDense G) :
    let K := Kc (L2V Ω) (TSD Ω) (TSD Ω)
    (∀ x, (∀ t, 0 ≤ t → G.S t x ∈ K) ↔ x ∈ Kmax G K) ∧
    (Kmax G K ≤ Stat G ↔ ∀ u ∈ S1max G (TSD Ω) (TSD Ω),
      ∃ h1 : u ∈ (thesisComplex hΩ hb).d1.domain, (thesisComplex hΩ hb).d1 ⟨u, h1⟩ = 0) ∧
    (¬ Kmax G K ≤ Stat G ↔ ∃ ω : ℝ, 0 < ω ∧ ∃ u : L2M Ω, u ≠ 0 ∧ u ∈ TSD Ω ∧
      ∃ (h1 : u ∈ (thesisComplex hΩ hb).d1.domain)
        (h3 : (thesisComplex hΩ hb).d1 ⟨u, h1⟩ ∈ (thesisComplex hΩ hb).d1†.domain),
        (thesisComplex hΩ hb).d1 ⟨u, h1⟩ ∈ TSD Ω ∧
          (thesisComplex hΩ hb).d1† ⟨_, h3⟩ = ω ^ 2 • u) ∧
    (∀ (ω : ℝ), 0 < ω → ∀ u : L2M Ω, u ∈ TSD Ω →
      ∀ (h1 : u ∈ (thesisComplex hΩ hb).d1.domain)
        (h3 : (thesisComplex hΩ hb).d1 ⟨u, h1⟩ ∈ (thesisComplex hΩ hb).d1†.domain),
        (thesisComplex hΩ hb).d1 ⟨u, h1⟩ ∈ TSD Ω →
          (thesisComplex hΩ hb).d1† ⟨_, h3⟩ = ω ^ 2 • u →
            u ∈ S1max G (TSD Ω) (TSD Ω) ∧ u ∈ TSD0 Ω hΩ hb ∧
              (u ≠ 0 → ini (L2V Ω) u (0 : L2M Ω) ∉ Stat G)) := by
  intro K
  obtain ⟨h1, h2, h3⟩ := Kmax_spectral (G := G) (S2 := TSD Ω) (thesisComplex_TSD_le_ker hΩ hb) hD
  refine ⟨h1, h2, h3, fun ω hω u hu hu1 hu3 hS e => ?_⟩
  obtain ⟨hu2, e2⟩ := exists_adj0_eq_zero_of_mem_ker (thesisComplex_TSD_le_ker hΩ hb hu)
  obtain ⟨-, hm, hns⟩ := eigen_mem_S1max (G := G) hω hu hu1 hu2 e2 hu3 hS e
  exact ⟨hm, thesisComplex_S1max_le_TSD0 hΩ hb G _ hm, hns⟩

end Feec.BoundedDomain

namespace Feec.BoundedSym

open Feec.BoundedDomain Feec.HilbertComplex2 Feec.Constraints

variable {Ω : Set R3} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)

/-- **`K*` on a bounded domain for the strong-symmetry complex (4.16)** (`symComplexB`,
`K = {0} × L²(TSD) ∩ L²(S) × L²(TSD) ∩ L²(T)`), under the same documented hypothesis
`EigenDense G` as `Feec.BoundedDomain.thesisComplex_Kmax_spectral`: forward invariance is
equivalent to `x ∈ K*`; `K*` is stationary iff `S1* ⊆ ker d1`; `K*` contains a non-stationary
datum iff `d1* d1 u = ω² u` has a nonzero solution `u ∈ L²(TSD) ∩ D(d1)` with
`d1 u ∈ L²(TSD) ∩ D(d1*)`, `ω > 0`; and every such `u` lies in `S1*`, has `u ∈ L²(TSD₀)`, and
moves. -/
theorem symComplexB_Kmax_spectral
    (G : UnitaryGroupGenerator (-(symComplexB hΩ hb).waveOp)) (hD : EigenDense G) :
    let K := Kc (L2 Ω) (TSDS Ω) (TSDT Ω)
    (∀ x, (∀ t, 0 ≤ t → G.S t x ∈ K) ↔ x ∈ Kmax G K) ∧
    (Kmax G K ≤ Stat G ↔ ∀ u ∈ S1max G (TSDS Ω) (TSDT Ω),
      ∃ h1 : u ∈ (symComplexB hΩ hb).d1.domain, (symComplexB hΩ hb).d1 ⟨u, h1⟩ = 0) ∧
    (¬ Kmax G K ≤ Stat G ↔ ∃ ω : ℝ, 0 < ω ∧ ∃ u : L2S Ω, u ≠ 0 ∧ u ∈ TSDS Ω ∧
      ∃ (h1 : u ∈ (symComplexB hΩ hb).d1.domain)
        (h3 : (symComplexB hΩ hb).d1 ⟨u, h1⟩ ∈ (symComplexB hΩ hb).d1†.domain),
        (symComplexB hΩ hb).d1 ⟨u, h1⟩ ∈ TSDT Ω ∧
          (symComplexB hΩ hb).d1† ⟨_, h3⟩ = ω ^ 2 • u) ∧
    (∀ (ω : ℝ), 0 < ω → ∀ u : L2S Ω, u ∈ TSDS Ω →
      ∀ (h1 : u ∈ (symComplexB hΩ hb).d1.domain)
        (h3 : (symComplexB hΩ hb).d1 ⟨u, h1⟩ ∈ (symComplexB hΩ hb).d1†.domain),
        (symComplexB hΩ hb).d1 ⟨u, h1⟩ ∈ TSDT Ω →
          (symComplexB hΩ hb).d1† ⟨_, h3⟩ = ω ^ 2 • u →
            u ∈ S1max G (TSDS Ω) (TSDT Ω) ∧ (u : L2M Ω) ∈ TSD0 Ω hΩ hb ∧
              (u ≠ 0 → ini (L2 Ω) u (0 : L2T Ω) ∉ Stat G)) := by
  intro K
  obtain ⟨h1, h2, h3⟩ := Kmax_spectral (G := G) (S2 := TSDT Ω) (TSDS_le_ker hΩ hb) hD
  refine ⟨h1, h2, h3, fun ω hω u hu hu1 hu3 hS e => ?_⟩
  obtain ⟨hu2, e2⟩ := exists_adj0_eq_zero_of_mem_ker (TSDS_le_ker hΩ hb hu)
  obtain ⟨-, hm, hns⟩ := eigen_mem_S1max (G := G) hω hu hu1 hu2 e2 hu3 hS e
  exact ⟨hm, symComplexB_S1max_le_TSD0 hΩ hb G _ u hm, hns⟩

end Feec.BoundedSym
