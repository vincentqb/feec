module

public import Feec.HilbertComplex.InvariantCore
public import Feec.Semigroup.Spectral

/-!
# Which data of `K*` move: stationary data and electric eigenfields

For a short Hilbert complex `W₀ --d₀--> W₁ --d₁--> W₂`, its Hodge wave group `e^{tL}` and a
product constraint `K = {0} × S₁ × S₂`, the invariant core `K* = {0} × S₁* × S₂*`
(`Feec.ShortHilbertComplex.coreSub`, `Feec.HilbertComplex.InvariantCore`) is the largest closed
subspace of `K` reducing `L`. This file decides when `K*` consists of stationary data only.

* **Stationary electric data are harmonic** (`inj₁_mem_stationary_iff`): `(0, E, 0)` is
  stationary iff `E ∈ D(d₁) ∩ D(d₀†)` with `d₁ E = 0` and `d₀† E = 0`.
* **`K*` is stationary iff its electric slot is** (`coreSub_le_stationary_iff`,
  `coreSub_le_stationary_iff_harmonic`), with no spectral hypothesis: for `x = (0, E, B)` in
  `D(L) ∩ K*`, `d₁† B ∈ S₁*` (`adjoint_mem_invariantCore₁`), so if `S₁*` is stationary then
  `u = d₁† B` has `d₁ u = 0` and `‖u‖² = ⟪B, d₁ u⟫ = 0`; hence `L x = 0`, and `D(L) ∩ K*` is
  dense in `K*`.
* **Electric eigenfields move** (`eigenfield_mem_invariantCore₁`): for `ω > 0` and
  `u ∈ S₁ ∩ D(d₁) ∩ N(d₀†)` with `d₁ u ∈ S₂ ∩ D(d₁†)` and `d₁† d₁ u = ω² u`, the datum `(0, u, 0)`
  is an eigenvector of `L²` with eigenvalue `-ω²` lying in `K*`, and it is not stationary unless
  `u = 0`. Conversely every nonzero eigenvector of `L²` in `K*` with eigenvalue `-ω²`, `ω > 0`,
  yields such a `u` (`exists_eigenfield_of_isEigenSq_mem_coreSub`).
* Under a complete set of eigenvectors of `L²` (`Feec.C0Group.EigenDense`), `K*` contains a
  moving datum iff an electric eigenfield exists (`not_coreSub_le_stationary_iff`), and forward
  invariance of `K` is equivalent to membership in `K*` (`coreSub_spectral`).

## Main definitions

* `stationary`, `EigenDense`: the stationary data and the eigenvector hypothesis for the wave
  group of a short complex; `IsEigenfield`: `d₁† d₁ u = ω² u`.

## Main results

* `inj₁_mem_stationary_iff`, `coreSub_le_stationary_iff`, `coreSub_le_stationary_iff_harmonic`,
  `coreSub_le_stationary_of_invariantCore₁_eq_bot`.
* `eigenfield_mem_invariantCore₁`, `exists_eigenfield_of_isEigenSq_mem_coreSub`.
* **`not_coreSub_le_stationary_iff`**, **`coreSub_spectral`**.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Props 4.16–4.18), §4.11 (Prop 4.19)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.10 (groups of isometries)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

/-- A vector of the kernel of a partially defined map lies in its domain and is killed by it. -/
theorem LinearPMap.exists_apply_eq_zero_of_mem_ker {R E F : Type*} [Ring R] [AddCommGroup E]
    [Module R E] [AddCommGroup F] [Module R F] {f : E →ₗ.[R] F} {x : E} (hx : x ∈ f.ker) :
    ∃ h : x ∈ f.domain, f ⟨x, h⟩ = 0 := by
  obtain ⟨y, hyx, hy0⟩ := LinearPMap.mem_ker_iff.1 hx
  subst hyx
  exact ⟨y.2, hy0⟩

namespace Feec.ShortHilbertComplex

universe u

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
  {S : ShortHilbertComplex 𝕜 W₀ W₁ W₂}
  [∀ i, NormedSpace ℝ (W3 W₀ W₁ W₂ i)] [∀ i, IsScalarTower ℝ 𝕜 (W3 W₀ W₁ W₂ i)]
  {S₁ : Submodule 𝕜 W₁} {S₂ : Submodule 𝕜 W₂}

/-! ### The wave group and the wave operator -/

variable (S) in
/-- The stationary data of the Hodge wave group `e^{tL}` of `S`. -/
abbrev stationary : Submodule 𝕜 (PiLp 2 (W3 W₀ W₁ W₂)) := S.toHilbertComplex.waveGroup.stationary

variable (S) in
/-- `v` is an **electric eigenfield** with frequency `ω`: `v ∈ D(d₁)`, `d₁ v ∈ D(d₁†)` and
`d₁† d₁ v = ω² v`. -/
def IsEigenfield (ω : ℝ) (v : W₁) : Prop :=
  ∃ (h1 : v ∈ S.d₁.domain) (h3 : S.d₁ ⟨v, h1⟩ ∈ (S.d₁†).domain),
    S.d₁† ⟨_, h3⟩ = ((ω ^ 2 : ℝ) : 𝕜) • v

variable (S) in
/-- The eigenvectors of `L²` span a dense subspace (`Feec.C0Group.EigenDense` for the Hodge wave
group of `S`). -/
abbrev EigenDense : Prop := S.toHilbertComplex.waveGroup.EigenDense

/-- A stationary vector lies in `D(L)` and is killed by `L`. -/
theorem wave_eq_zero_of_mem_stationary {x : PiLp 2 (W3 W₀ W₁ W₂)}
    (hx : x ∈ S.stationary) :
    ∃ h : x ∈ S.wave.domain, S.wave ⟨x, h⟩ = 0 := by
  have := C0Group.mem_domain_generator_of_mem_stationary hx
  rwa [HilbertComplex.generator_waveGroup] at this

/-- A zero of `L` is stationary. -/
theorem mem_stationary_of_wave_eq_zero (x : S.wave.domain) (h0 : S.wave x = 0) :
    (x : PiLp 2 (W3 W₀ W₁ W₂)) ∈ S.stationary := by
  have key : ∀ (A : PiLp 2 (W3 W₀ W₁ W₂) →ₗ.[𝕜] PiLp 2 (W3 W₀ W₁ W₂)) (_ : A = S.wave),
      ∃ hx' : (x : PiLp 2 (W3 W₀ W₁ W₂)) ∈ A.domain, A ⟨_, hx'⟩ = 0 := by
    rintro _ rfl; exact ⟨x.2, h0⟩
  obtain ⟨hx', e⟩ := key _ S.toHilbertComplex.generator_waveGroup
  exact C0Group.mem_stationary.2 fun t => C0Group.S_apply_eq_of_generator_eq_zero ⟨_, hx'⟩ e t

omit [CompleteSpace W₀] [CompleteSpace W₁] [CompleteSpace W₂] in
private theorem apply_eq_zero_of_coe {E F : Type*} [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
    [Module 𝕜 F] {T : E →ₗ.[𝕜] F} (x : T.domain) (h : (x : E) = 0) : T x = 0 := by
  have : x = 0 := Subtype.ext h
  rw [this, LinearPMap.map_zero]

omit [∀ i, NormedSpace ℝ (W3 W₀ W₁ W₂ i)] [∀ i, IsScalarTower ℝ 𝕜 (W3 W₀ W₁ W₂ i)] in
/-- `L (0, E, 0) = (-d₀† E, 0, d₁ E)`. -/
private theorem wave_inj₁_eq (u : S.d₁.domain) (hu : (u : W₁) ∈ (S.d₀†).domain) :
    S.wave ⟨_, inj₁_mem_wave_domain (S := S) u.2 hu⟩ =
      WithLp.toLp 2 (fun i => match i with
        | 0 => -(S.d₀† ⟨u, hu⟩)
        | 1 => (0 : W₁)
        | 2 => S.d₁ u) := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · exact wave_inj₁_zero u hu
  · exact wave_inj₁_one u hu
  · exact wave_inj₁_two u hu

/-! ### Stationary data -/

/-- **Stationary electric data are harmonic**: `(0, E, 0)` is stationary iff
`E ∈ D(d₁) ∩ D(d₀†)`, `d₁ E = 0` and `d₀† E = 0`. -/
theorem inj₁_mem_stationary_iff {v : W₁} :
    inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ v ∈ S.stationary ↔
      ∃ (h1 : v ∈ S.d₁.domain) (h2 : v ∈ (S.d₀†).domain),
        S.d₁ ⟨v, h1⟩ = 0 ∧ S.d₀† ⟨v, h2⟩ = 0 := by
  constructor
  · intro hs
    obtain ⟨hD, h0⟩ := wave_eq_zero_of_mem_stationary hs
    obtain ⟨-, h1, h2, -⟩ := S.mem_wave_domain.1 hD
    have h1' : v ∈ S.d₁.domain := h1
    have h2' : v ∈ (S.d₀†).domain := h2
    refine ⟨h1', h2', ?_, ?_⟩
    · have e := wave_inj₁_two (S := S) ⟨v, h1'⟩ h2'
      have e0 := congrArg (fun z : PiLp 2 (W3 W₀ W₁ W₂) => (z 2 : W₂)) h0
      exact e.symm.trans e0
    · have e := wave_inj₁_zero (S := S) ⟨v, h1'⟩ h2'
      have e0 := congrArg (fun z : PiLp 2 (W3 W₀ W₁ W₂) => (z 0 : W₀)) h0
      exact neg_eq_zero.1 (e.symm.trans e0)
  · rintro ⟨h1, h2, e1, e2⟩
    refine mem_stationary_of_wave_eq_zero ⟨_, inj₁_mem_wave_domain (S := S) h1 h2⟩ ?_
    rw [wave_inj₁_eq (S := S) ⟨v, h1⟩ h2]
    refine PiLp.ext fun i => ?_
    fin_cases i
    · exact (congrArg Neg.neg e2).trans neg_zero
    · rfl
    · exact e1

variable [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection]

/-- `L` maps `D(L) ∩ K*` into `K*`. -/
theorem wave_mem_coreSub (x : S.wave.domain) (hx : (x : PiLp 2 (W3 W₀ W₁ W₂)) ∈ S.coreSub S₁ S₂) :
    S.wave x ∈ S.coreSub S₁ S₂ := by
  have key : ∀ (A : PiLp 2 (W3 W₀ W₁ W₂) →ₗ.[𝕜] PiLp 2 (W3 W₀ W₁ W₂))
      (_ : S.toHilbertComplex.waveGroup.generator = A) (hA : (x : PiLp 2 (W3 W₀ W₁ W₂)) ∈ A.domain),
      A ⟨_, hA⟩ ∈ S.coreSub S₁ S₂ := by
    rintro _ rfl hA
    exact S.toHilbertComplex.isIsometric_waveGroup.apply_mem_invariantCore ⟨_, hA⟩ hx
  exact key _ S.toHilbertComplex.generator_waveGroup x.2

/-- **`K*` is stationary iff its electric slot is**: every element of
`K* = {0} × S₁* × S₂*` is a stationary point of `U' = L U` iff every `E ∈ S₁*` gives a
stationary point `(0, E, 0)`. No spectral hypothesis.

For `x = (0, E, B) ∈ D(L) ∩ K*`, `d₁† B ∈ S₁*`; if `S₁*` is stationary, `d₁ E = 0`, `d₀† E = 0`
and `u = d₁† B` has `d₁ u = 0`, so `‖u‖² = ⟪B, d₁ u⟫ = 0` and `L x = 0`; `D(L) ∩ K*` is dense in
`K*`. -/
theorem coreSub_le_stationary_iff :
    S.coreSub S₁ S₂ ≤ S.stationary ↔
      ∀ v ∈ S.invariantCore₁ S₁ S₂,
        inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ v ∈ S.stationary := by
  refine ⟨fun h v hv => h (mem_invariantCore₁.1 hv), fun h => ?_⟩
  refine S.toHilbertComplex.isIsometric_waveGroup.invariantCore_le_stationary_of_domain
    fun x hx => ?_
  have hxD : (x : PiLp 2 (W3 W₀ W₁ W₂)) ∈ S.wave.domain := by
    have key : ∀ (A : PiLp 2 (W3 W₀ W₁ W₂) →ₗ.[𝕜] PiLp 2 (W3 W₀ W₁ W₂))
        (_ : S.toHilbertComplex.waveGroup.generator = A),
        (x : PiLp 2 (W3 W₀ W₁ W₂)) ∈ A.domain := by
      rintro _ rfl; exact x.2
    exact key _ S.toHilbertComplex.generator_waveGroup
  set y : S.wave.domain := ⟨x, hxD⟩
  have hy : (y : PiLp 2 (W3 W₀ W₁ W₂)) ∈ S.coreSub S₁ S₂ := hx
  obtain ⟨hy0, hy1, hy2⟩ := mem_coreSub_iff.1 hy
  obtain ⟨-, h1, h2, h3⟩ := S.mem_wave_domain.1 hxD
  obtain ⟨hy11, hy12, e1, e2⟩ := inj₁_mem_stationary_iff.1 (h _ hy1)
  -- `u = d₁† B ∈ S₁*` is curl-free, hence zero
  have hu := adjoint_mem_invariantCore₁ (S := S) ⟨_, h3⟩ hy2
  obtain ⟨hu1, hu2, eu1, eu2⟩ := inj₁_mem_stationary_iff.1 (h _ hu)
  have hadj := LinearPMap.adjoint_isFormalAdjoint S.dense₁ ⟨_, h3⟩ ⟨_, hu1⟩
  rw [eu1, inner_zero_right] at hadj
  have hu0 : S.d₁† ⟨_, h3⟩ = 0 := inner_self_eq_zero.1 hadj
  refine mem_stationary_of_wave_eq_zero y (PiLp.ext fun i => ?_)
  fin_cases i
  · show ((S.wave y : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀) = 0
    rw [S.wave_apply_zero]
    exact (congrArg Neg.neg e2).trans neg_zero
  · show ((S.wave y : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁) = 0
    rw [S.wave_apply_one, apply_eq_zero_of_coe _ hy0]
    exact (sub_eq_zero.2 hu0.symm)
  · show ((S.wave y : PiLp 2 (W3 W₀ W₁ W₂)) 2 : W₂) = 0
    rw [S.wave_apply_two]
    exact e1

/-- **Harmonic form**: `K*` is stationary iff every `E ∈ S₁*` lies in `D(d₁) ∩ D(d₀†)` with
`d₁ E = 0` and `d₀† E = 0`. -/
theorem coreSub_le_stationary_iff_harmonic :
    S.coreSub S₁ S₂ ≤ S.stationary ↔
      ∀ v ∈ S.invariantCore₁ S₁ S₂, ∃ (h1 : v ∈ S.d₁.domain) (h2 : v ∈ (S.d₀†).domain),
        S.d₁ ⟨v, h1⟩ = 0 ∧ S.d₀† ⟨v, h2⟩ = 0 := by
  rw [coreSub_le_stationary_iff]
  exact forall₂_congr fun _ _ => inj₁_mem_stationary_iff

/-- If the electric slot `S₁*` is `0`, every element of `K*` is stationary. -/
theorem coreSub_le_stationary_of_invariantCore₁_eq_bot (h : S.invariantCore₁ S₁ S₂ = ⊥) :
    S.coreSub S₁ S₂ ≤ S.stationary :=
  coreSub_le_stationary_iff.2 fun v hv => by
    rw [h, Submodule.mem_bot] at hv
    rw [hv, _root_.map_zero]
    exact Submodule.zero_mem _

/-! ### Electric eigenfields -/

omit [S₁.HasOrthogonalProjection] [S₂.HasOrthogonalProjection] in
/-- An eigenvector of `L²` lies in `K*` iff it and its image under `L` lie in `K`. -/
theorem mem_coreSub_iff_of_isEigenSq [(HilbertComplex.totalSub
      (family3 (⊥ : Submodule 𝕜 W₀) S₁ S₂)).HasOrthogonalProjection]
    {ω : ℝ} (hω : 0 < ω) {v : PiLp 2 (W3 W₀ W₁ W₂)}
    (h : v ∈ S.wave.domain) (h' : S.wave ⟨v, h⟩ ∈ S.wave.domain)
    (e : S.wave ⟨S.wave ⟨v, h⟩, h'⟩ = -(ω ^ 2) • v) :
    v ∈ S.coreSub S₁ S₂ ↔ v ∈ HilbertComplex.totalSub (family3 (⊥ : Submodule 𝕜 W₀) S₁ S₂) ∧
      S.wave ⟨v, h⟩ ∈ HilbertComplex.totalSub (family3 (⊥ : Submodule 𝕜 W₀) S₁ S₂) := by
  have key : ∀ (A : PiLp 2 (W3 W₀ W₁ W₂) →ₗ.[𝕜] PiLp 2 (W3 W₀ W₁ W₂))
      (_ : S.toHilbertComplex.waveGroup.generator = A) (h : v ∈ A.domain)
      (h' : A ⟨v, h⟩ ∈ A.domain) (_ : A ⟨A ⟨v, h⟩, h'⟩ = -(ω ^ 2) • v),
      v ∈ S.coreSub S₁ S₂ ↔
        v ∈ HilbertComplex.totalSub (family3 (⊥ : Submodule 𝕜 W₀) S₁ S₂) ∧
          A ⟨v, h⟩ ∈ HilbertComplex.totalSub (family3 (⊥ : Submodule 𝕜 W₀) S₁ S₂) := by
    rintro _ rfl h h' e
    exact S.toHilbertComplex.isIsometric_waveGroup.mem_invariantCore_iff_of_isEigenSq hω h h' e
  exact key _ S.toHilbertComplex.generator_waveGroup h h' e

/-- **Electric eigenfields give moving elements of `K*`**: let `ω > 0` and `u ∈ S₁` with
`u ∈ D(d₁) ∩ D(d₀†)`, `d₀† u = 0`, `d₁ u ∈ D(d₁†) ∩ S₂` and `d₁† d₁ u = ω² u`. Then `(0, u, 0)` is
an eigenvector of `L²` with eigenvalue `-ω²`, `u ∈ S₁*`, its orbit is
`(0, cos(ωt) u, (sin(ωt)/ω) d₁ u)` (`Feec.C0Group.IsIsometric.S_eq_of_isEigenSq`), and it is not
stationary unless `u = 0`. -/
theorem eigenfield_mem_invariantCore₁ {ω : ℝ} (hω : 0 < ω) {v : W₁} (hv : v ∈ S₁)
    (h1 : v ∈ S.d₁.domain) (h2 : v ∈ (S.d₀†).domain) (e2 : S.d₀† ⟨v, h2⟩ = 0)
    (h3 : S.d₁ ⟨v, h1⟩ ∈ (S.d₁†).domain) (h3S : S.d₁ ⟨v, h1⟩ ∈ S₂)
    (e3 : S.d₁† ⟨_, h3⟩ = ((ω ^ 2 : ℝ) : 𝕜) • v) :
    S.wave.IsEigenSq ω (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ v) ∧ v ∈ S.invariantCore₁ S₁ S₂ ∧
      (v ≠ 0 → inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ v ∉ S.stationary) := by
  have hD := inj₁_mem_wave_domain (S := S) h1 h2
  have hL : S.wave ⟨_, hD⟩ = inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ (S.d₁ ⟨v, h1⟩) := by
    rw [wave_inj₁_eq (S := S) ⟨v, h1⟩ h2]
    refine PiLp.ext fun i => ?_
    fin_cases i
    · exact (congrArg Neg.neg e2).trans neg_zero
    · rfl
    · rfl
  have hD2 : S.wave ⟨_, hD⟩ ∈ S.wave.domain := hL ▸ inj₂_mem_wave_domain (S := S) h3
  have hLL : S.wave ⟨S.wave ⟨_, hD⟩, hD2⟩ = -(ω ^ 2) • inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ v := by
    have hq : (⟨S.wave ⟨_, hD⟩, hD2⟩ : S.wave.domain) =
        ⟨_, inj₂_mem_wave_domain (S := S) (⟨_, h3⟩ : S.d₁†.domain).2⟩ := Subtype.ext hL
    rw [hq, wave_inj₂, e3, RCLike.real_smul_eq_coe_smul (K := 𝕜), ← _root_.map_smul]
    congr 1
    rw [RCLike.ofReal_neg, neg_smul]
  have hE : S.wave.IsEigenSq ω (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ v) := ⟨hD, hD2, hLL⟩
  refine ⟨hE, ?_, fun hv0 hs => ?_⟩
  · rw [mem_invariantCore₁, mem_coreSub_iff_of_isEigenSq hω hD hD2 hLL, hL]
    exact ⟨single_one_mem_totalSub_family3 _ _ _ hv, single_two_mem_totalSub_family3 _ _ _ h3S⟩
  · have hE' : S.toHilbertComplex.waveGroup.generator.IsEigenSq ω
        (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ v) := by
      rw [HilbertComplex.generator_waveGroup]; exact hE
    refine C0Group.not_mem_stationary_of_isEigenSq hω.ne' hE' (fun h0 => hv0 ?_) hs
    have := congrArg (fun z : PiLp 2 (W3 W₀ W₁ W₂) => (z 1 : W₁)) h0
    simp only [inj₁_apply_one] at this
    exact this

/-- **Eigenvectors of `L²` in `K*` come from electric eigenfields**: if `x ∈ K*` is a nonzero
eigenvector of `L²` with eigenvalue `-ω²`, `ω > 0`, there is `u ≠ 0` with the hypotheses of
`eigenfield_mem_invariantCore₁` (the electric part of `x` if nonzero, `-d₁† B` otherwise). -/
theorem exists_eigenfield_of_isEigenSq_mem_coreSub {ω : ℝ} (hω : 0 < ω)
    {x : PiLp 2 (W3 W₀ W₁ W₂)} (hxK : x ∈ S.coreSub S₁ S₂) (hx : S.wave.IsEigenSq ω x)
    (hx0 : x ≠ 0) :
    ∃ v : W₁, v ≠ 0 ∧ v ∈ S₁ ∧ ∃ (h1 : v ∈ S.d₁.domain) (h2 : v ∈ (S.d₀†).domain),
      S.d₀† ⟨v, h2⟩ = 0 ∧ ∃ h3 : S.d₁ ⟨v, h1⟩ ∈ (S.d₁†).domain,
        S.d₁ ⟨v, h1⟩ ∈ S₂ ∧ S.d₁† ⟨_, h3⟩ = ((ω ^ 2 : ℝ) : 𝕜) • v := by
  obtain ⟨h, h', e⟩ := hx
  set r : 𝕜 := ((ω ^ 2 : ℝ) : 𝕜) with hr
  have r0 : r ≠ 0 := by rw [hr]; exact_mod_cast (pow_pos hω 2).ne'
  obtain ⟨hK0, hK1, hK2⟩ := mem_totalSub_family3.1 (coreSub_le hxK)
  have hx0' : (x 0 : W₀) = 0 := (Submodule.mem_bot 𝕜).1 hK0
  set a : W₁ := x 1
  set b : W₂ := x 2
  have hxab : x = inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ a + inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ b := by
    refine PiLp.ext fun i => ?_
    fin_cases i
    · show (x 0 : W₀) = (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ a 0 : W₀) + (inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ b 0 : W₀)
      rw [hx0', inj₁_apply_zero, inj₂_apply_zero, add_zero]
    · show a = (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ a 1 : W₁) + (inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ b 1 : W₁)
      rw [inj₁_apply_one, inj₂_apply_one, add_zero]
    · show b = (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ a 2 : W₂) + (inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ b 2 : W₂)
      rw [inj₁_apply_two, inj₂_apply_two, zero_add]
  have e' : S.wave ⟨S.wave ⟨x, h⟩, h'⟩ =
      inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ ((-r) • a) + inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ ((-r) • b) := by
    rw [e, RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.ofReal_neg, ← hr]
    conv_lhs => rw [hxab]
    rw [smul_add, ← _root_.map_smul, ← _root_.map_smul]
  obtain ⟨hL0, hL1, hL2⟩ := mem_totalSub_family3.1 (coreSub_le (wave_mem_coreSub ⟨x, h⟩ hxK))
  obtain ⟨-, hE1, hE2, hB⟩ := S.mem_wave_domain.1 h
  -- the components of `L x` and of `L (L x)`
  have c0 : ((S.wave ⟨x, h⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀) = -(S.d₀† ⟨_, hE2⟩) :=
    S.wave_apply_zero _
  have c1 : ((S.wave ⟨x, h⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁) = -(S.d₁† ⟨_, hB⟩) := by
    rw [S.wave_apply_one, apply_eq_zero_of_coe _ hx0', zero_sub]
  have c2 : ((S.wave ⟨x, h⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 2 : W₂) = S.d₁ ⟨_, hE1⟩ :=
    S.wave_apply_two _
  have e2 : S.d₀† ⟨_, hE2⟩ = 0 := by
    have := (Submodule.mem_bot 𝕜 (M := W₀)).1 hL0
    rw [c0] at this
    exact neg_eq_zero.1 this
  obtain ⟨hl0, hu1, hu2, h3⟩ := S.mem_wave_domain.1 h'
  have eσ : S.d₀† ⟨_, hu2⟩ = 0 := by
    have h0 : ((S.wave ⟨S.wave ⟨x, h⟩, h'⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀) = 0 := by
      rw [e']
      show (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ ((-r) • a) 0 : W₀) +
        (inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ ((-r) • b) 0 : W₀) = 0
      rw [inj₁_apply_zero, inj₂_apply_zero, add_zero]
    rw [S.wave_apply_zero] at h0
    exact neg_eq_zero.1 h0
  have hl00 : ((S.wave ⟨x, h⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀) = 0 :=
    c0.trans ((congrArg Neg.neg e2).trans neg_zero)
  have eE : S.d₁† ⟨_, h3⟩ = r • a := by
    have h1 : ((S.wave ⟨S.wave ⟨x, h⟩, h'⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁) = (-r) • a := by
      rw [e']
      show (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ ((-r) • a) 1 : W₁) +
        (inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ ((-r) • b) 1 : W₁) = ((-r) • a : W₁)
      rw [inj₁_apply_one, inj₂_apply_one]
      exact add_zero _
    rw [S.wave_apply_one, apply_eq_zero_of_coe (T := S.d₀) _ hl00, zero_sub, neg_smul] at h1
    exact neg_inj.1 h1
  have eB : S.d₁ ⟨_, hu1⟩ = (-r) • b := by
    have h2 : ((S.wave ⟨S.wave ⟨x, h⟩, h'⟩ : PiLp 2 (W3 W₀ W₁ W₂)) 2 : W₂) = (-r) • b := by
      rw [e']
      show (inj₁ (𝕜 := 𝕜) W₀ W₁ W₂ ((-r) • a) 2 : W₂) +
        (inj₂ (𝕜 := 𝕜) W₀ W₁ W₂ ((-r) • b) 2 : W₂) = ((-r) • b : W₂)
      rw [inj₁_apply_two, inj₂_apply_two]
      exact zero_add _
    rw [S.wave_apply_two] at h2
    exact h2
  by_cases hE0 : a = 0
  · -- the electric part vanishes: use `u = -d₁† B`
    refine ⟨_, ?_, hL1, hu1, hu2, eσ, ?_⟩
    · intro hu0
      rw [apply_eq_zero_of_coe _ hu0] at eB
      have hB0 : b = 0 := (smul_eq_zero.1 eB.symm).resolve_left (neg_ne_zero.2 r0)
      refine hx0 ?_
      rw [hxab, hE0, hB0, _root_.map_zero, _root_.map_zero, add_zero]
    · have h3' : S.d₁ ⟨_, hu1⟩ ∈ (S.d₁†).domain := by
        rw [eB]; exact (S.d₁†).domain.smul_mem _ hB
      refine ⟨h3', by rw [eB]; exact S₂.smul_mem _ hK2, ?_⟩
      have hq : (⟨S.d₁ ⟨_, hu1⟩, h3'⟩ : S.d₁†.domain) = (-r) • ⟨b, hB⟩ := Subtype.ext eB
      rw [hq, LinearPMap.map_smul, c1, smul_neg, neg_smul]
  · have h3'' : S.d₁ ⟨_, hE1⟩ ∈ (S.d₁†).domain := c2 ▸ h3
    refine ⟨_, hE0, hK1, hE1, hE2, e2, h3'', c2 ▸ hL2, ?_⟩
    have hq : (⟨S.d₁ ⟨_, hE1⟩, h3''⟩ : S.d₁†.domain) = ⟨_, h3⟩ := Subtype.ext c2.symm
    rw [hq]
    exact eE

/-- **When does `K*` contain a moving datum?** Under a complete set of eigenvectors of `L²`
(`Feec.C0Group.EigenDense`), `K*` contains a non-stationary element iff there are `ω > 0` and
`u ≠ 0` with `u ∈ S₁ ∩ D(d₁) ∩ D(d₀†)`, `d₀† u = 0`, `d₁ u ∈ S₂ ∩ D(d₁†)` and `d₁† d₁ u = ω² u`
(an electric eigenfield whose `d₁` stays in `S₂`). The direction `⇐` needs no hypothesis. -/
theorem not_coreSub_le_stationary_iff (hD : S.EigenDense) :
    ¬ S.coreSub S₁ S₂ ≤ S.stationary ↔
      ∃ ω : ℝ, 0 < ω ∧ ∃ v : W₁, v ≠ 0 ∧ v ∈ S₁ ∧
        ∃ (h1 : v ∈ S.d₁.domain) (h2 : v ∈ (S.d₀†).domain), S.d₀† ⟨v, h2⟩ = 0 ∧
          ∃ h3 : S.d₁ ⟨v, h1⟩ ∈ (S.d₁†).domain,
            S.d₁ ⟨v, h1⟩ ∈ S₂ ∧ S.d₁† ⟨_, h3⟩ = ((ω ^ 2 : ℝ) : 𝕜) • v := by
  constructor
  · intro h
    obtain ⟨ω, hω, x, hxK, hx, hx0⟩ :=
      S.toHilbertComplex.isIsometric_waveGroup.exists_isEigenSq_mem_invariantCore hD
        HilbertComplex.isClosed_totalSub h
    rw [HilbertComplex.generator_waveGroup] at hx
    exact ⟨ω, hω, exists_eigenfield_of_isEigenSq_mem_coreSub hω hxK hx hx0⟩
  · rintro ⟨ω, hω, v, hv0, hv, h1, h2, e2, h3, h3S, e3⟩ hle
    obtain ⟨-, hm, hns⟩ := eigenfield_mem_invariantCore₁ (S := S) hω hv h1 h2 e2 h3 h3S e3
    exact hns hv0 (hle (mem_invariantCore₁.1 hm))

/-- **Summary for `S₁ ⊆ N(d₀†)`** (as for the TSD constraint), under a complete set of
eigenvectors of `L²`:
1. forward invariance of `K = {0} × S₁ × S₂` (`t ≥ 0`) is equivalent to `x ∈ K*`;
2. `K*` is stationary iff every `E ∈ S₁*` satisfies `E ∈ D(d₁)`, `d₁ E = 0` (this item needs no
   hypothesis);
3. `K*` contains a non-stationary datum iff there are `ω > 0` and `u ≠ 0` in `S₁ ∩ D(d₁)` with
   `d₁ u ∈ S₂ ∩ D(d₁†)` and `d₁† d₁ u = ω² u`. -/
theorem coreSub_spectral (hS₁ : S₁ ≤ (S.d₀†).ker)
    (hD : S.EigenDense) :
    (∀ x, (∀ t, 0 ≤ t → S.toHilbertComplex.waveGroup.S t x ∈
        HilbertComplex.totalSub (family3 (⊥ : Submodule 𝕜 W₀) S₁ S₂)) ↔
          x ∈ S.coreSub S₁ S₂) ∧
    (S.coreSub S₁ S₂ ≤ S.stationary ↔
      ∀ v ∈ S.invariantCore₁ S₁ S₂, ∃ h1 : v ∈ S.d₁.domain, S.d₁ ⟨v, h1⟩ = 0) ∧
    (¬ S.coreSub S₁ S₂ ≤ S.stationary ↔
      ∃ ω : ℝ, 0 < ω ∧ ∃ v : W₁, v ≠ 0 ∧ v ∈ S₁ ∧
        ∃ (h1 : v ∈ S.d₁.domain) (h3 : S.d₁ ⟨v, h1⟩ ∈ (S.d₁†).domain),
          S.d₁ ⟨v, h1⟩ ∈ S₂ ∧ S.d₁† ⟨_, h3⟩ = ((ω ^ 2 : ℝ) : 𝕜) • v) := by
  have hG := S.toHilbertComplex.isIsometric_waveGroup
  refine ⟨fun x => ⟨fun h => hG.mem_invariantCore_of_forward_invariant
    (hG.isPurePoint_of_eigenDense hD) HilbertComplex.isClosed_totalSub h,
      fun h t _ => coreSub_le (C0Group.S_mem_invariantCore h t)⟩, ?_, ?_⟩
  · rw [coreSub_le_stationary_iff_harmonic]
    refine forall₂_congr fun v hv => ⟨fun ⟨h1, _, e1, _⟩ => ⟨h1, e1⟩, fun ⟨h1, e1⟩ => ?_⟩
    obtain ⟨h2, e2⟩ := LinearPMap.exists_apply_eq_zero_of_mem_ker (hS₁ (invariantCore₁_le hv))
    exact ⟨h1, h2, e1, e2⟩
  · rw [not_coreSub_le_stationary_iff hD]
    constructor
    · rintro ⟨ω, hω, v, hv0, hv, h1, -, -, h3, h3S, e3⟩
      exact ⟨ω, hω, v, hv0, hv, h1, h3, h3S, e3⟩
    · rintro ⟨ω, hω, v, hv0, hv, h1, h3, h3S, e3⟩
      obtain ⟨h2, e2⟩ := LinearPMap.exists_apply_eq_zero_of_mem_ker (hS₁ hv)
      exact ⟨ω, hω, v, hv0, hv, h1, h2, e2, h3, h3S, e3⟩

end Feec.ShortHilbertComplex
