module

public import Feec.HilbertComplex.Approximation.ApproxComplexCrime
public import Feec.HilbertComplex.Total

/-!
# The static FEEC theorem with variational crimes

The mixed Hodge Laplacian of the total complex (`Feec.HilbertComplex.Total`), discretized on an
approximating family of discrete differential spaces (`ApproxComplexCrime.Family`: `Xₕ` with its
own inner product, a differential `𝐝ₕ` independent of `𝐝`, reading maps `iₕ` that need not be
cochain maps nor isometric), with the load `iₕ* f`. This is the elliptic theory of
[HolstStern2012], §3 (Thms 3.9, 3.10, there for cochain reading maps) for the families of
`Feec.HilbertComplex.Approximation.ApproxComplexCrime`, where the failure of `iₕ` to commute with
the differentials enters as a cochain defect.

## Setting

* `diffComplex D hDD`: a differential `D` (`D D = 0`) on a Hilbert space `X` as a Hilbert complex
  on the one-point shape `ComplexShape.loop`; its mixed problem is the mixed Hodge Laplacian of
  `(X, D)`: find `(σ, u, p)` with `σ = D* u`, `D σ + D* D u + p = f`, `p ∈ ker D ∩ ker D*`,
  `u ⊥ ker D ∩ ker D*`. Its cycles are `ker D` (`diffComplex_cycles`), its harmonic forms
  `ker D ∩ ker D*` (`mem_diffComplex_harmonic`).
* `ApproxComplexCrime.Family.cpx h`: the discrete differential space `(Xₕ, 𝐝ₕ)` as such a
  complex; `mixedSol h f`: **the discrete mixed solution** `(σₕ, uₕ, pₕ)` with the load `iₕ* f`
  (well posed for every `h`: `Xₕ` is finite-dimensional, `wellPosed_mixedSol`).
* `IsPoincare cP`: the **uniform discrete Poincaré inequality** `‖v‖ ≤ c_P ‖𝐝ₕ v‖` on
  `(ker 𝐝ₕ)ᗮ`, for every `h`.
* `readError h X x`: `‖σ - iₕ σ̃‖ + ‖𝐝 σ - iₕ 𝐝ₕ σ̃‖ + ‖u - iₕ ũ‖ + ‖𝐝 u - iₕ 𝐝ₕ ũ‖ + ‖p - iₕ p̃‖`
  for a continuous triple `X = (σ, u, p)` and a discrete one `x = (σ̃, ũ, p̃)`; `staticError h f`
  is the read error of the discrete mixed solution against the mixed solution with data `f`.
  The read differential `iₕ 𝐝ₕ` is compared with `𝐝`: `iₕ Xₕ` need not lie in `D(𝐝)`.
* `staticResidual h f x`: the residual `B x̃ - F` of a discrete triple in the discrete mixed form,
  an antilinear functional on the discrete mixed space (dual graph norm).

## Main results

* `ApproxComplexCrime.Family.norm_mixedSol_le`: **uniform stability**,
  `‖(σₕ, uₕ, pₕ)‖ ≤ 16 c_P² C ‖f‖` (graph norms; [AFW2010], Thm 3.8 for `(Xₕ, 𝐝ₕ)`).
* `ApproxComplexCrime.Family.staticError_le`: **the Strang lemma**, for every discrete triple
  `x̃`, `e(f) ≤ readError(x̃) + 80 C c_P² ‖B x̃ - F‖`.
* `ApproxComplexCrime.Family.inner_staticResidual_eq`, `norm_staticResidual_le`: **the residual
  splits** into the inner-product defect `‖1 - Jₕ‖`, the read error of `x̃`, the cochain defects
  `κₕ(u)`, `κₕ(𝐝 u)` (`ApproxComplexCrime.Family.cochainDefect`) in the dual discrete graph norm,
  and the **harmonic defect** `sup |⟪iₕ q, u⟫| / ‖q‖` over the discrete harmonic forms `q`;
  `staticError_le_of_split`: the error estimate
  `e(f) ≤ E + 240 C c_P² (5 ‖1 - Jₕ‖ ‖x̃‖ + C E + δ₁ + δ₂ + η)`, `E` the read error of `x̃`, `δ₁`,
  `δ₂` bounds of the cochain defects and `η` of the harmonic defect (the crime analogue of
  [HolstStern2012], Thm 3.10, where the reading maps are cochain maps and `δ₁ = δ₂ = 0`).
* `ApproxComplexCrime.Family.staticConsistent_iff_tendsto`: consistent approximation at `f`
  (approximants with read error and residual tending to `0`) is equivalent to `e(f) → 0`;
  `staticConsistent_of_split` derives it from vanishing defects; `tendsto_staticError_of_dense`:
  on a dense set of data it gives `e(f) → 0` for every `f`.
* `ApproxComplexCrime.Family.isPoincare_of_proj`: **the discrete Poincaré inequality from the
  projections** (for cochain maps, [HolstStern2012], §3): if `πₕ` maps `ker 𝐝` into `ker 𝐝ₕ`,
  `iₕ Xₕ ⊆ D(𝐝)` with `‖𝐝 iₕ v‖ ≤ C' ‖𝐝ₕ v‖` (`C' = C` for cochain maps), then
  `c_P = c₀ C C'`, `c₀` a Poincaré constant of `𝐝`.
* `ApproxComplexCrime.Family.StaticVerdict`, **`ApproxComplexCrime.Family.staticFEEC`**: the
  conclusions together.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (Thm 3.9, Thm 3.10)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.2, §3.4 (Thm 3.8)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The Hilbert complex of a differential -/

section DiffComplex

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  (D : X →L[𝕜] X) (hDD : ∀ v, D (D v) = 0)

/-- **The Hilbert complex of a differential** `D` (`D D = 0`): `X →D X` on the one-point shape
`ComplexShape.loop`, with full domains (`ofBounded`). -/
def diffComplex : HilbertComplex 𝕜 ComplexShape.loop (fun _ : Unit => X) :=
  ofBounded (fun _ _ => D) (fun _ _ h => absurd trivial h) fun _ _ _ x => hDD x

theorem diffComplex_d_apply (i j : Unit) (x : ((diffComplex D hDD).d i j).domain) :
    (diffComplex D hDD).d i j x = D x :=
  rfl

theorem diffComplex_domain (i j : Unit) : ((diffComplex D hDD).d i j).domain = ⊤ :=
  rfl

/-- The adjoint of the differential of `diffComplex D` is `D*`. -/
theorem adjoint_diffComplex_d_apply (i j : Unit) (y : (((diffComplex D hDD).d i j)†).domain) :
    ((diffComplex D hDD).d i j)† y = D.adjoint y :=
  LinearPMap.apply_eq_of_eq (ContinuousLinearMap.adjoint_toPMap_top D) y ⟨y, Submodule.mem_top⟩
    rfl

theorem mem_adjoint_diffComplex_d_domain (i j : Unit) (y : X) :
    y ∈ (((diffComplex D hDD).d i j)†).domain := by
  change y ∈ (((D : X →ₗ[𝕜] X).toPMap ⊤)†).domain
  rw [ContinuousLinearMap.adjoint_toPMap_top]; trivial

/-- The cycles of `diffComplex D` are `ker D`. -/
theorem diffComplex_cycles (i : Unit) :
    (diffComplex D hDD).cycles i = LinearMap.ker (D : X →ₗ[𝕜] X) := by
  ext v
  change v ∈ ((diffComplex D hDD).d i (ComplexShape.loop.next i)).ker ↔ _
  rw [LinearPMap.mem_ker_iff, LinearMap.mem_ker]
  exact ⟨fun ⟨y, hy, h0⟩ => hy ▸ h0, fun h0 => ⟨⟨v, Submodule.mem_top⟩, rfl, h0⟩⟩

/-- The harmonic forms of `diffComplex D` are `ker D ∩ ker D*`. -/
theorem mem_diffComplex_harmonic {i : Unit} {q : X} :
    q ∈ (diffComplex D hDD).harmonic i ↔ D q = 0 ∧ D.adjoint q = 0 := by
  rw [harmonic_eq_cycles_inf_dual, Submodule.mem_inf, cycles_dual, diffComplex_cycles,
    LinearMap.mem_ker, LinearPMap.mem_ker_iff]
  refine and_congr_right fun _ => ⟨fun ⟨y, hy, h0⟩ => ?_, fun h0 =>
    ⟨⟨q, mem_adjoint_diffComplex_d_domain D hDD _ _ q⟩, rfl, ?_⟩⟩
  · rw [hy, ← adjoint_diffComplex_d_apply D hDD (ComplexShape.loop.prev i) i y, h0]
  · rw [adjoint_diffComplex_d_apply]; exact h0

theorem closedRangeAt_diffComplex [FiniteDimensional 𝕜 X] (i : Unit) :
    (diffComplex D hDD).ClosedRangeAt i :=
  Submodule.closed_of_finiteDimensional _

/-- `v ∈ X` as an element of the domain space of `diffComplex D`. -/
def toDom (v : X) : (diffComplex D hDD).domainSpace () :=
  (diffComplex D hDD).toDomainSpace (loop_rel () ()) ⟨v, Submodule.mem_top⟩

@[simp] theorem domainIncl_toDom (v : X) : (diffComplex D hDD).domainIncl () (toDom D hDD v) = v :=
  rfl

theorem d_domainCoord_diffComplex (w : (diffComplex D hDD).domainSpace ()) :
    (diffComplex D hDD).d () () ((diffComplex D hDD).domainCoord () () w) =
      D ((diffComplex D hDD).domainIncl () w) :=
  rfl

end DiffComplex

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι}
  {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)]

/-! ### The mixed solution of the total complex in `D(L)` -/

section Total

variable (H : HilbertComplex 𝕜 c W) (hcr : ∀ i, H.ClosedRangeAt i)

theorem greenOp_mem_wave_domain (f : PiLp 2 W) : H.greenOp hcr f ∈ H.wave.domain := by
  obtain ⟨h, -⟩ := (H.isMixedSolution_totalMixedSolution hcr f).mem_adjoint_domain (loop_rel () ())
  refine ⟨H.total.domainIncl_mem () _, ?_⟩
  change _ ∈ (H.totalD†).domain at h
  rwa [adjoint_totalD] at h

/-- The potential `u = G f` of the mixed solution with data `f`, a state of `D(L)`. -/
def greenWave (f : PiLp 2 W) : H.wave.domain := ⟨H.greenOp hcr f, H.greenOp_mem_wave_domain hcr f⟩

theorem coe_greenWave (f : PiLp 2 W) : (H.greenWave hcr f : PiLp 2 W) = H.greenOp hcr f := rfl

/-- `𝐝* u = σ` for the mixed solution `(σ, u, p)` with data `f`. -/
theorem dual_totalD_greenWave (f : PiLp 2 W) :
    H.dual.totalD ⟨H.greenWave hcr f, (H.greenWave hcr f).2.2⟩ =
      H.total.mixedI0 () () (H.totalMixedSolution hcr f) := by
  obtain ⟨h, e⟩ := (H.isMixedSolution_totalMixedSolution hcr f).mem_adjoint_domain (loop_rel () ())
  rw [mixedI0_apply, ← e]
  exact (LinearPMap.apply_eq_of_eq H.adjoint_totalD ⟨_, h⟩ _ rfl).symm

theorem totalD_greenOp_mem_wave_domain (f : PiLp 2 W) :
    H.totalD ⟨H.greenOp hcr f, (H.greenWave hcr f).2.1⟩ ∈ H.wave.domain := by
  obtain ⟨h, -⟩ :=
    (H.isMixedSolution_totalMixedSolution hcr f).mem_adjoint_domain_d (loop_rel () ())
  refine ⟨H.totalD_mapsTo _, ?_⟩
  change _ ∈ (H.totalD†).domain at h
  rw [adjoint_totalD] at h
  exact h

/-- `𝐝 u` for the potential `u = G f`, a state of `D(L)`. -/
def dGreenWave (f : PiLp 2 W) : H.wave.domain :=
  ⟨H.totalD ⟨H.greenOp hcr f, (H.greenWave hcr f).2.1⟩, H.totalD_greenOp_mem_wave_domain hcr f⟩

/-- `u` is the `u` component of the mixed solution. -/
theorem coe_greenWave_eq_mixedI1 (f : PiLp 2 W) :
    (H.greenWave hcr f : PiLp 2 W) = H.total.mixedI1 () () (H.totalMixedSolution hcr f) :=
  rfl

/-- `𝐝 u` is the `𝐝 u` component of the mixed solution. -/
theorem coe_dGreenWave (f : PiLp 2 W) :
    (H.dGreenWave hcr f : PiLp 2 W) = H.total.mixedD1 () () () (H.totalMixedSolution hcr f) :=
  rfl

/-- `𝐝* 𝐝 u = f - p - 𝐝 σ` for the mixed solution `(σ, u, p)` with data `f`. -/
theorem dual_totalD_dGreenWave (f : PiLp 2 W) :
    H.dual.totalD ⟨H.dGreenWave hcr f, (H.dGreenWave hcr f).2.2⟩ =
      f - H.total.mixedI2 () () (H.totalMixedSolution hcr f) -
        H.total.mixedD0 () () (H.totalMixedSolution hcr f) := by
  obtain ⟨h, e⟩ :=
    (H.isMixedSolution_totalMixedSolution hcr f).mem_adjoint_domain_d (loop_rel () ())
  rw [mixedI2_apply, mixedD0_apply, ← e]
  exact (LinearPMap.apply_eq_of_eq H.adjoint_totalD ⟨_, h⟩ _ rfl).symm

/-- `u ⊥ ℌ`. -/
theorem inner_harmonic_greenOp (f : PiLp 2 W) {q : PiLp 2 W} (hq : q ∈ H.total.harmonic ()) :
    ⟪q, H.greenOp hcr f⟫_𝕜 = 0 :=
  (H.isMixedSolution_totalMixedSolution hcr f).harm q hq

end Total

/-! ### Arithmetic of the residual bound -/

theorem sum_le_three_mul_of_sq {a₀ a₁ a₂ a₃ a₄ n : ℝ} (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂)
    (h₃ : 0 ≤ a₃) (h₄ : 0 ≤ a₄) (hn : 0 ≤ n)
    (e : n ^ 2 = a₀ ^ 2 + a₁ ^ 2 + (a₂ ^ 2 + a₃ ^ 2) + a₄ ^ 2) :
    a₀ + a₁ + a₂ + a₃ + a₄ ≤ 3 * n := by
  nlinarith [sq_nonneg (a₀ - a₁), sq_nonneg (a₀ - a₂), sq_nonneg (a₀ - a₃), sq_nonneg (a₀ - a₄),
    sq_nonneg (a₁ - a₂), sq_nonneg (a₁ - a₃), sq_nonneg (a₁ - a₄), sq_nonneg (a₂ - a₃),
    sq_nonneg (a₂ - a₄), sq_nonneg (a₃ - a₄), sq_nonneg (a₀ + a₁ + a₂ + a₃ + a₄ - 3 * n)]

theorem norm_sum₁₅_le {E : Type*} [SeminormedAddCommGroup E]
    (t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃ t₁₄ t₁₅ : E) :
    ‖t₁ + t₂ - t₃ - t₄ - t₅ + t₆ + t₇ + t₈ + t₉ + t₁₀ + t₁₁ + t₁₂ - t₁₃ - t₁₄ - t₁₅‖ ≤
      ‖t₁‖ + ‖t₂‖ + ‖t₃‖ + ‖t₄‖ + ‖t₅‖ + ‖t₆‖ + ‖t₇‖ + ‖t₈‖ + ‖t₉‖ + ‖t₁₀‖ + ‖t₁₁‖ + ‖t₁₂‖ +
        ‖t₁₃‖ + ‖t₁₄‖ + ‖t₁₅‖ := by
  repeat (first
    | exact norm_add_le _ _
    | refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    | refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl))

/-- The arithmetic of the residual bound: fifteen terms, each bounded by a component of the test
triple times a defect, sum to at most `3 (5 j ‖x‖ + C E + δ₁ + δ₂ + η) ‖y‖`. -/
theorem residual_arith {t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃ t₁₄ t₁₅ a₀ a₁ a₂ a₃ a₄ n₀ n₁ n₂
      n₃ n₄ e₀ e₁ e₂ e₃ e₄ j C δ₁ δ₂ η nx ny : ℝ}
    (hj : 0 ≤ j) (hC : 0 ≤ C) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hη : 0 ≤ η) (hnx : 0 ≤ nx)
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄)
    (he₀ : 0 ≤ e₀) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (he₃ : 0 ≤ e₃) (he₄ : 0 ≤ e₄)
    (hn₀ : n₀ ≤ nx) (hn₁ : n₁ ≤ nx) (hn₂ : n₂ ≤ nx) (hn₃ : n₃ ≤ nx) (hn₄ : n₄ ≤ nx)
    (hy : a₀ + a₁ + a₂ + a₃ + a₄ ≤ 3 * ny)
    (b₁ : t₁ ≤ a₀ * (j * n₀)) (b₂ : t₂ ≤ a₀ * (C * e₀)) (b₃ : t₃ ≤ a₁ * (j * n₂))
    (b₄ : t₄ ≤ a₁ * (C * e₂)) (b₅ : t₅ ≤ δ₁ * (a₀ + a₁)) (b₆ : t₆ ≤ a₂ * (j * n₁))
    (b₇ : t₇ ≤ a₂ * (C * e₁)) (b₈ : t₈ ≤ a₃ * (j * n₃)) (b₉ : t₉ ≤ a₃ * (C * e₃))
    (b₁₀ : t₁₀ ≤ δ₂ * (a₂ + a₃)) (b₁₁ : t₁₁ ≤ a₂ * (j * n₄)) (b₁₂ : t₁₂ ≤ a₂ * (C * e₄))
    (b₁₃ : t₁₃ ≤ a₄ * (j * n₂)) (b₁₄ : t₁₄ ≤ a₄ * (C * e₂)) (b₁₅ : t₁₅ ≤ a₄ * η) :
    t₁ + t₂ + t₃ + t₄ + t₅ + t₆ + t₇ + t₈ + t₉ + t₁₀ + t₁₁ + t₁₂ + t₁₃ + t₁₄ + t₁₅ ≤
      3 * (5 * j * nx + C * (e₀ + e₁ + e₂ + e₃ + e₄) + δ₁ + δ₂ + η) * ny := by
  set M := 5 * j * nx + C * (e₀ + e₁ + e₂ + e₃ + e₄) + δ₁ + δ₂ + η
  have hjn : ∀ {n : ℝ}, n ≤ nx → j * n ≤ j * nx := fun hn => mul_le_mul_of_nonneg_left hn hj
  have hjnx : 0 ≤ j * nx := mul_nonneg hj hnx
  have hC0 : C * e₀ ≤ C * (e₀ + e₁ + e₂ + e₃ + e₄) := mul_le_mul_of_nonneg_left (by linarith) hC
  have hC1 : C * e₁ ≤ C * (e₀ + e₁ + e₂ + e₃ + e₄) := mul_le_mul_of_nonneg_left (by linarith) hC
  have hC2 : C * e₂ ≤ C * (e₀ + e₁ + e₂ + e₃ + e₄) := mul_le_mul_of_nonneg_left (by linarith) hC
  have hC3 : C * e₃ ≤ C * (e₀ + e₁ + e₂ + e₃ + e₄) := mul_le_mul_of_nonneg_left (by linarith) hC
  have hC14 : C * e₁ + C * e₄ ≤ C * (e₀ + e₁ + e₂ + e₃ + e₄) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hC
  have hCs : 0 ≤ C * (e₀ + e₁ + e₂ + e₃ + e₄) := mul_nonneg hC (by linarith)
  have c₀ : j * n₀ + C * e₀ + δ₁ ≤ M := by have := hjn hn₀; linarith
  have c₁ : j * n₂ + C * e₂ + δ₁ ≤ M := by have := hjn hn₂; linarith
  have c₂ : j * n₁ + C * e₁ + δ₂ + j * n₄ + C * e₄ ≤ M := by
    have := hjn hn₁; have := hjn hn₄; linarith
  have c₃ : j * n₃ + C * e₃ + δ₂ ≤ M := by have := hjn hn₃; linarith
  have c₄ : j * n₂ + C * e₂ + η ≤ M := by have := hjn hn₂; linarith
  have hM : 0 ≤ M := by linarith
  calc _ ≤ a₀ * (j * n₀ + C * e₀ + δ₁) + a₁ * (j * n₂ + C * e₂ + δ₁) +
        a₂ * (j * n₁ + C * e₁ + δ₂ + j * n₄ + C * e₄) + a₃ * (j * n₃ + C * e₃ + δ₂) +
        a₄ * (j * n₂ + C * e₂ + η) := by linarith
    _ ≤ a₀ * M + a₁ * M + a₂ * M + a₃ * M + a₄ * M := by gcongr
    _ = M * (a₀ + a₁ + a₂ + a₃ + a₄) := by ring
    _ ≤ M * (3 * ny) := mul_le_mul_of_nonneg_left hy hM
    _ = _ := by ring

/-! ### The discrete mixed problem -/

namespace ApproxComplexCrime.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplexCrime.Family.{u} H κ)

/-- The discrete differential space `(Xₕ, 𝐝ₕ)` as a Hilbert complex on `ComplexShape.loop`. -/
abbrev cpx (h : κ) : HilbertComplex 𝕜 ComplexShape.loop (fun _ : Unit => S.X h) :=
  diffComplex (S.D h) (S.D_D h)

theorem cpx_mixedD0 (h : κ) (y : (S.cpx h).MixedSpace () ()) :
    (S.cpx h).mixedD0 () () y = S.D h ((S.cpx h).mixedI0 () () y) :=
  rfl

theorem cpx_mixedD1 (h : κ) (y : (S.cpx h).MixedSpace () ()) :
    (S.cpx h).mixedD1 () () () y = S.D h ((S.cpx h).mixedI1 () () y) :=
  rfl

/-- **The uniform discrete Poincaré inequality** `‖v‖ ≤ c_P ‖𝐝ₕ v‖` on `(ker 𝐝ₕ)ᗮ`, for every
`h`. -/
def IsPoincare (cP : ℝ) : Prop :=
  ∀ h (v : S.X h), v ∈ (LinearMap.ker (S.D h : S.X h →ₗ[𝕜] S.X h))ᗮ → ‖v‖ ≤ cP * ‖S.D h v‖

/-- **The discrete mixed solution** `(σₕ, uₕ, pₕ)` with the load `iₕ* f`: the solution of the mixed
Hodge Laplacian of `(Xₕ, 𝐝ₕ)` with data `iₕ* f`. -/
def mixedSol (h : κ) : PiLp 2 W →L[𝕜] (S.cpx h).MixedSpace () () :=
  (S.cpx h).mixedSolution (loop_rel () ()) (loop_rel () ()) (closedRangeAt_diffComplex _ _ ())
    (closedRangeAt_diffComplex _ _ ()) ∘L (S.incl h).adjoint

theorem mixedForm_mixedSol (h : κ) (f : PiLp 2 W) :
    (S.cpx h).mixedForm () () () (S.mixedSol h f) =
      (S.cpx h).mixedRHS () () ((S.incl h).adjoint f) :=
  (S.cpx h).mixedForm_mixedSolution (loop_rel () ()) (loop_rel () ())
    (closedRangeAt_diffComplex _ _ ()) (closedRangeAt_diffComplex _ _ ()) _

theorem isMixedSolution_mixedSol (h : κ) (f : PiLp 2 W) :
    (S.cpx h).IsMixedSolution () () () ((S.incl h).adjoint f) (S.mixedSol h f).fst
      (S.mixedSol h f).snd.fst (S.mixedSol h f).snd.snd :=
  (S.cpx h).isMixedSolution_mixedSolution (loop_rel () ()) (loop_rel () ())
    (closedRangeAt_diffComplex _ _ ()) (closedRangeAt_diffComplex _ _ ()) _

/-- **The discrete mixed problem is well posed** for every `h` (`Xₕ` is finite-dimensional). -/
theorem wellPosed_mixedSol (h : κ) (f : PiLp 2 W) :
    ∃! x : (S.cpx h).MixedSpace () (), (S.cpx h).IsMixedSolution () () ()
      ((S.incl h).adjoint f) x.fst x.snd.fst x.snd.snd :=
  ⟨S.mixedSol h f, S.isMixedSolution_mixedSol h f, fun _ hx =>
    ((S.cpx h).mixedSolution_eq (loop_rel () ()) (loop_rel () ())
      (closedRangeAt_diffComplex _ _ ()) (closedRangeAt_diffComplex _ _ ()) hx).symm⟩

variable {S} in
theorem IsPoincare.cycles {cP : ℝ} (hP : S.IsPoincare cP) (h : κ)
    (z : ((S.cpx h).d () ()).domain) (hz : (z : S.X h) ∈ ((S.cpx h).cycles ())ᗮ) :
    ‖(z : S.X h)‖ ≤ cP * ‖(S.cpx h).d () () z‖ := by
  rw [diffComplex_cycles] at hz
  exact hP h z hz

variable {S} in
theorem IsPoincare.mono {cP cP' : ℝ} (hP : S.IsPoincare cP) (hc : cP ≤ cP') : S.IsPoincare cP' :=
  fun h v hv => (hP h v hv).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

variable {S} in
/-- **The uniform discrete inf-sup condition** of the discrete mixed form, with the constant
`1 / (16 c_P²)` ([AFW2010], Thm 3.8). -/
theorem IsPoincare.infSup {cP : ℝ} (hP : S.IsPoincare cP) (hcP : 1 ≤ cP) (h : κ) :
    Variational.InfSup ((S.cpx h).mixedForm () () ()) (1 / (16 * cP ^ 2)) :=
  (S.cpx h).infSup_mixedForm (loop_rel () ()) (loop_rel () ()) hcP (hP.cycles h) (hP.cycles h)

/-- **Uniform stability of the discrete mixed problem**: `‖(σₕ, uₕ, pₕ)‖ ≤ 16 c_P² C ‖f‖` (graph
norms), `C` the bound of the reading maps. -/
theorem norm_mixedSol_le {cP : ℝ} (hP : S.IsPoincare cP) (hcP : 1 ≤ cP) (h : κ) (f : PiLp 2 W) :
    ‖S.mixedSol h f‖ ≤ 16 * cP ^ 2 * S.boundConst * ‖f‖ := by
  have h1 := (S.cpx h).norm_le_of_mixed (loop_rel () ()) (loop_rel () ()) hcP (hP.cycles h)
    (hP.cycles h) (S.mixedForm_mixedSol h f)
  have h2 := S.norm_adjoint_incl_apply_le h f
  have : 0 ≤ 16 * cP ^ 2 := by positivity
  calc _ ≤ 16 * cP ^ 2 * ‖(S.incl h).adjoint f‖ := h1
    _ ≤ 16 * cP ^ 2 * (S.boundConst * ‖f‖) := mul_le_mul_of_nonneg_left h2 this
    _ = _ := by ring

/-! #### The read error and the Strang lemma -/

/-- **The read error** of a discrete triple `x = (σ̃, ũ, p̃)` against a continuous one
`X = (σ, u, p)`: `‖σ - iₕ σ̃‖ + ‖𝐝 σ - iₕ 𝐝ₕ σ̃‖ + ‖u - iₕ ũ‖ + ‖𝐝 u - iₕ 𝐝ₕ ũ‖ + ‖p - iₕ p̃‖`. -/
def readError (h : κ) (X : H.total.MixedSpace () ()) (x : (S.cpx h).MixedSpace () ()) : ℝ :=
  ‖H.total.mixedI0 () () X - S.incl h ((S.cpx h).mixedI0 () () x)‖ +
    ‖H.total.mixedD0 () () X - S.incl h ((S.cpx h).mixedD0 () () x)‖ +
    ‖H.total.mixedI1 () () X - S.incl h ((S.cpx h).mixedI1 () () x)‖ +
    ‖H.total.mixedD1 () () () X - S.incl h ((S.cpx h).mixedD1 () () () x)‖ +
    ‖H.total.mixedI2 () () X - S.incl h ((S.cpx h).mixedI2 () () x)‖

theorem readError_nonneg (h : κ) (X : H.total.MixedSpace () ()) (x : (S.cpx h).MixedSpace () ()) :
    0 ≤ S.readError h X x := by
  unfold readError; positivity

/-- **The static error** of the mixed method with variational crimes: the read error of the
discrete mixed solution `(σₕ, uₕ, pₕ)` (load `iₕ* f`) against the mixed solution `(σ, u, p)` of
the total complex with data `f`. -/
def staticError (hcr : ∀ i, H.ClosedRangeAt i) (h : κ) (f : PiLp 2 W) : ℝ :=
  S.readError h (H.totalMixedSolution hcr f) (S.mixedSol h f)

/-- The components of a mixed triple are bounded by its norm. -/
theorem norm_mixedComponents_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [CompleteSpace V] (E : HilbertComplex 𝕜 ComplexShape.loop (fun _ : Unit => V))
    (x : E.MixedSpace () ()) :
    ‖E.mixedI0 () () x‖ ≤ ‖x‖ ∧ ‖E.mixedD0 () () x‖ ≤ ‖x‖ ∧ ‖E.mixedI1 () () x‖ ≤ ‖x‖ ∧
      ‖E.mixedD1 () () () x‖ ≤ ‖x‖ ∧ ‖E.mixedI2 () () x‖ ≤ ‖x‖ := by
  have hσ : ‖x.fst‖ ≤ ‖x‖ := WithLp.norm_fst_le (x := x)
  have hu : ‖x.snd.fst‖ ≤ ‖x‖ :=
    (WithLp.norm_fst_le (x := x.snd)).trans (WithLp.norm_snd_le (x := x))
  have hp : ‖x.snd.snd‖ ≤ ‖x‖ :=
    (WithLp.norm_snd_le (x := x.snd)).trans (WithLp.norm_snd_le (x := x))
  exact ⟨(E.norm_domainIncl_le () _).trans hσ, (E.norm_d_domainCoord_le () () _).trans hσ,
    (E.norm_domainIncl_le () _).trans hu, (E.norm_d_domainCoord_le () () _).trans hu, hp⟩

/-- The read error is Lipschitz in the discrete triple:
`readError(y) ≤ readError(x) + 5 C ‖x - y‖`. -/
theorem readError_le (h : κ) (X : H.total.MixedSpace () ()) (x y : (S.cpx h).MixedSpace () ()) :
    S.readError h X y ≤ S.readError h X x + 5 * S.boundConst * ‖x - y‖ := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := norm_mixedComponents_le (S.cpx h) (x - y)
  have key : ∀ (a : PiLp 2 W) (b b' : S.X h), ‖b - b'‖ ≤ ‖x - y‖ →
      ‖a - S.incl h b'‖ ≤ ‖a - S.incl h b‖ + S.boundConst * ‖x - y‖ := fun a b b' hb => by
    have e : a - S.incl h b' = (a - S.incl h b) + S.incl h (b - b') := by
      rw [_root_.map_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((S.norm_incl_apply_le h _).trans
      (mul_le_mul_of_nonneg_left hb S.boundConst_nonneg)))
  simp only [_root_.map_sub] at h0 h1 h2 h3 h4
  unfold readError
  linarith [key (H.total.mixedI0 () () X) _ _ h0, key (H.total.mixedD0 () () X) _ _ h1,
    key (H.total.mixedI1 () () X) _ _ h2, key (H.total.mixedD1 () () () X) _ _ h3,
    key (H.total.mixedI2 () () X) _ _ h4]

/-- The **residual** `B x - F` of a discrete triple `x` in the discrete mixed form with the load
`iₕ* f`: an antilinear functional on the discrete mixed space, measured in the dual graph norm. -/
def staticResidual (h : κ) (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) :
    (S.cpx h).MixedSpace () () →L⋆[𝕜] 𝕜 :=
  (S.cpx h).mixedForm () () () x - (S.cpx h).mixedRHS () () ((S.incl h).adjoint f)

theorem staticResidual_mixedSol (h : κ) (f : PiLp 2 W) :
    S.staticResidual h f (S.mixedSol h f) = 0 := by
  rw [staticResidual, mixedForm_mixedSol, sub_self]

/-- **Stability against the residual**: `‖x - (σₕ, uₕ, pₕ)‖ ≤ 16 c_P² ‖B x - F‖`. -/
theorem norm_sub_mixedSol_le {cP : ℝ} (hP : S.IsPoincare cP) (hcP : 1 ≤ cP) (h : κ)
    (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) :
    ‖x - S.mixedSol h f‖ ≤ 16 * cP ^ 2 * ‖S.staticResidual h f x‖ := by
  have hB : (S.cpx h).mixedForm () () () (x - S.mixedSol h f) = S.staticResidual h f x := by
    rw [_root_.map_sub, mixedForm_mixedSol]; rfl
  have := (hP.infSup hcP h).norm_le_of_apply_eq hB
  have hcP0 : 0 < cP := one_pos.trans_le hcP
  rwa [one_div, inv_inv] at this

/-- **The Strang lemma for the mixed method with variational crimes**: for every discrete triple
`x̃`, `e(f) ≤ readError(x̃) + 80 C c_P² ‖B x̃ - F‖` (best approximation plus consistency).
Cf. [HolstStern2012], Thm 3.9 -/
theorem staticError_le (hcr : ∀ i, H.ClosedRangeAt i) {cP : ℝ} (hP : S.IsPoincare cP)
    (hcP : 1 ≤ cP) (h : κ) (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) :
    S.staticError hcr h f ≤
      S.readError h (H.totalMixedSolution hcr f) x + 80 * S.boundConst * cP ^ 2 *
        ‖S.staticResidual h f x‖ := by
  have h1 := S.readError_le h (H.totalMixedSolution hcr f) x (S.mixedSol h f)
  have h2 := S.norm_sub_mixedSol_le hP hcP h f x
  have := S.boundConst_nonneg
  unfold staticError
  nlinarith

/-! #### The splitting of the residual -/

/-- The cochain defect paired on the right: `⟪v, κₕ(y)⟫ = ⟪iₕ 𝐝ₕ v, y⟫ - ⟪iₕ v, 𝐝* y⟫`. -/
theorem inner_cochainDefect_right (h : κ) (y : H.wave.domain) (v : S.X h) :
    ⟪v, S.cochainDefect h y⟫_𝕜 =
      ⟪S.incl h (S.D h v), (y : PiLp 2 W)⟫_𝕜 - ⟪S.incl h v, H.dual.totalD ⟨y, y.2.2⟩⟫_𝕜 := by
  rw [cochainDefect, inner_sub_right, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]

theorem inner_one_sub_J_right (h : κ) (a b : S.X h) :
    ⟪a, (1 - S.J h) b⟫_𝕜 = ⟪a, b⟫_𝕜 - ⟪S.incl h a, S.incl h b⟫_𝕜 := by
  rw [_root_.sub_apply, one_apply_eq_self, inner_sub_right, J, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

variable (hcr : ∀ i, H.ClosedRangeAt i)

/-- **The residual splits** into the inner-product defect, the read error, the cochain defects
of `u` and `𝐝 u` and the harmonic defect: for the mixed solution `(σ, u, p)` with data `f`, a
discrete triple `x = (σ̃, ũ, p̃)` and a test triple `y = (τ, v, q)`,
`(B x - F) y = ⟪τ, (1 - Jₕ) σ̃⟫ + ⟪iₕ τ, iₕ σ̃ - σ⟫ - ⟪𝐝ₕ τ, (1 - Jₕ) ũ⟫ - ⟪iₕ 𝐝ₕ τ, iₕ ũ - u⟫
- ⟪τ, κₕ(u)⟫ + ⟪v, (1 - Jₕ) 𝐝ₕ σ̃⟫ + ⟪iₕ v, iₕ 𝐝ₕ σ̃ - 𝐝 σ⟫ + ⟪𝐝ₕ v, (1 - Jₕ) 𝐝ₕ ũ⟫
+ ⟪iₕ 𝐝ₕ v, iₕ 𝐝ₕ ũ - 𝐝 u⟫ + ⟪v, κₕ(𝐝 u)⟫ + ⟪v, (1 - Jₕ) p̃⟫ + ⟪iₕ v, iₕ p̃ - p⟫
- ⟪q, (1 - Jₕ) ũ⟫ - ⟪iₕ q, iₕ ũ - u⟫ - ⟪iₕ q, u⟫`. -/
theorem inner_staticResidual_eq (h : κ) (f : PiLp 2 W) (x y : (S.cpx h).MixedSpace () ()) :
    S.staticResidual h f x y =
      ⟪(S.cpx h).mixedI0 () () y, (1 - S.J h) ((S.cpx h).mixedI0 () () x)⟫_𝕜 +
        ⟪S.incl h ((S.cpx h).mixedI0 () () y), S.incl h ((S.cpx h).mixedI0 () () x) -
          H.total.mixedI0 () () (H.totalMixedSolution hcr f)⟫_𝕜 -
        ⟪(S.cpx h).mixedD0 () () y, (1 - S.J h) ((S.cpx h).mixedI1 () () x)⟫_𝕜 -
        ⟪S.incl h ((S.cpx h).mixedD0 () () y), S.incl h ((S.cpx h).mixedI1 () () x) -
          H.total.mixedI1 () () (H.totalMixedSolution hcr f)⟫_𝕜 -
        ⟪(S.cpx h).mixedI0 () () y, S.cochainDefect h (H.greenWave hcr f)⟫_𝕜 +
        ⟪(S.cpx h).mixedI1 () () y, (1 - S.J h) ((S.cpx h).mixedD0 () () x)⟫_𝕜 +
        ⟪S.incl h ((S.cpx h).mixedI1 () () y), S.incl h ((S.cpx h).mixedD0 () () x) -
          H.total.mixedD0 () () (H.totalMixedSolution hcr f)⟫_𝕜 +
        ⟪(S.cpx h).mixedD1 () () () y, (1 - S.J h) ((S.cpx h).mixedD1 () () () x)⟫_𝕜 +
        ⟪S.incl h ((S.cpx h).mixedD1 () () () y), S.incl h ((S.cpx h).mixedD1 () () () x) -
          H.total.mixedD1 () () () (H.totalMixedSolution hcr f)⟫_𝕜 +
        ⟪(S.cpx h).mixedI1 () () y, S.cochainDefect h (H.dGreenWave hcr f)⟫_𝕜 +
        ⟪(S.cpx h).mixedI1 () () y, (1 - S.J h) ((S.cpx h).mixedI2 () () x)⟫_𝕜 +
        ⟪S.incl h ((S.cpx h).mixedI1 () () y), S.incl h ((S.cpx h).mixedI2 () () x) -
          H.total.mixedI2 () () (H.totalMixedSolution hcr f)⟫_𝕜 -
        ⟪(S.cpx h).mixedI2 () () y, (1 - S.J h) ((S.cpx h).mixedI1 () () x)⟫_𝕜 -
        ⟪S.incl h ((S.cpx h).mixedI2 () () y), S.incl h ((S.cpx h).mixedI1 () () x) -
          H.total.mixedI1 () () (H.totalMixedSolution hcr f)⟫_𝕜 -
        ⟪S.incl h ((S.cpx h).mixedI2 () () y), (H.greenWave hcr f : PiLp 2 W)⟫_𝕜 := by
  rw [staticResidual, _root_.sub_apply, mixedForm_apply, mixedRHS_apply,
    ContinuousLinearMap.adjoint_inner_right]
  simp only [S.inner_cochainDefect_right]
  simp only [H.dual_totalD_greenWave, H.dual_totalD_dGreenWave]
  simp only [H.coe_greenWave_eq_mixedI1, H.coe_dGreenWave, ← cpx_mixedD0, ← cpx_mixedD1,
    inner_one_sub_J_right, inner_sub_right]
  ring

theorem norm_inner_one_sub_J_le (h : κ) (a b : S.X h) :
    ‖⟪a, (1 - S.J h) b⟫_𝕜‖ ≤ ‖a‖ * (‖1 - S.J h‖ * ‖b‖) :=
  (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ((1 - S.J h).le_opNorm b)
    (norm_nonneg _))

theorem norm_inner_incl_sub_le (h : κ) (a b : S.X h) (z : PiLp 2 W) :
    ‖⟪S.incl h a, S.incl h b - z⟫_𝕜‖ ≤ ‖a‖ * (S.boundConst * ‖z - S.incl h b‖) := by
  calc _ ≤ ‖S.incl h a‖ * ‖S.incl h b - z‖ := norm_inner_le_norm _ _
    _ ≤ (S.boundConst * ‖a‖) * ‖z - S.incl h b‖ := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_right (S.norm_incl_apply_le h a) (norm_nonneg _)
    _ = _ := by ring

/-- The norm of a test triple `y = (τ, v, q)` controls `‖τ‖ + ‖𝐝ₕ τ‖ + ‖v‖ + ‖𝐝ₕ v‖ + ‖q‖`. -/
theorem sum_norm_mixedComponents_le (h : κ) (y : (S.cpx h).MixedSpace () ()) :
    ‖(S.cpx h).mixedI0 () () y‖ + ‖(S.cpx h).mixedD0 () () y‖ + ‖(S.cpx h).mixedI1 () () y‖ +
      ‖(S.cpx h).mixedD1 () () () y‖ + ‖(S.cpx h).mixedI2 () () y‖ ≤ 3 * ‖y‖ := by
  have e : ‖y‖ ^ 2 = ‖y.fst‖ ^ 2 + ‖y.snd.fst‖ ^ 2 + ‖(S.cpx h).mixedI2 () () y‖ ^ 2 :=
    MixedSpace.norm_sq y
  have e0 : ‖y.fst‖ ^ 2 = ‖(S.cpx h).mixedI0 () () y‖ ^ 2 + ‖(S.cpx h).mixedD0 () () y‖ ^ 2 :=
    (S.cpx h).norm_sq_domainSpace () y.fst
  have e1 : ‖y.snd.fst‖ ^ 2 =
      ‖(S.cpx h).mixedI1 () () y‖ ^ 2 + ‖(S.cpx h).mixedD1 () () () y‖ ^ 2 :=
    (S.cpx h).norm_sq_domainSpace () y.snd.fst
  rw [e0, e1] at e
  exact sum_le_three_mul_of_sq (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) e

/-- **The residual bound**: if the cochain defects `κₕ(u)`, `κₕ(𝐝 u)` are at most `δ₁`, `δ₂` in the
dual discrete graph norm and the harmonic defect is at most `η`, `|⟪iₕ q, u⟫| ≤ η ‖q‖` on the
discrete harmonic forms, then `‖B x - F‖ ≤ 3 (5 ‖1 - Jₕ‖ ‖x‖ + C E + δ₁ + δ₂ + η)`, `E` the read
error of `x`. -/
theorem norm_staticResidual_le (h : κ) (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ())
    {δ₁ δ₂ η : ℝ} (hδ₁0 : 0 ≤ δ₁) (hδ₂0 : 0 ≤ δ₂) (hη0 : 0 ≤ η)
    (hδ₁ : ∀ v, ‖⟪S.cochainDefect h (H.greenWave hcr f), v⟫_𝕜‖ ≤ δ₁ * (‖v‖ + ‖S.D h v‖))
    (hδ₂ : ∀ v, ‖⟪S.cochainDefect h (H.dGreenWave hcr f), v⟫_𝕜‖ ≤ δ₂ * (‖v‖ + ‖S.D h v‖))
    (hη : ∀ q ∈ (S.cpx h).harmonic (),
      ‖⟪S.incl h q, (H.greenWave hcr f : PiLp 2 W)⟫_𝕜‖ ≤ η * ‖q‖) :
    ‖S.staticResidual h f x‖ ≤ 3 * (5 * ‖1 - S.J h‖ * ‖x‖ +
      S.boundConst * S.readError h (H.totalMixedSolution hcr f) x + δ₁ + δ₂ + η) := by
  have hE := S.readError_nonneg h (H.totalMixedSolution hcr f) x
  have hC := S.boundConst_nonneg
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rw [S.inner_staticResidual_eq hcr h f x y]
  refine (norm_sum₁₅_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
  obtain ⟨n0, n1, n2, n3, n4⟩ := norm_mixedComponents_le (S.cpx h) x
  have b5 : ‖⟪(S.cpx h).mixedI0 () () y, S.cochainDefect h (H.greenWave hcr f)⟫_𝕜‖ ≤
      δ₁ * (‖(S.cpx h).mixedI0 () () y‖ + ‖(S.cpx h).mixedD0 () () y‖) := by
    rw [norm_inner_symm]; exact hδ₁ _
  have b10 : ‖⟪(S.cpx h).mixedI1 () () y, S.cochainDefect h (H.dGreenWave hcr f)⟫_𝕜‖ ≤
      δ₂ * (‖(S.cpx h).mixedI1 () () y‖ + ‖(S.cpx h).mixedD1 () () () y‖) := by
    rw [norm_inner_symm]; exact hδ₂ _
  have b15 : ‖⟪S.incl h ((S.cpx h).mixedI2 () () y), (H.greenWave hcr f : PiLp 2 W)⟫_𝕜‖ ≤
      ‖(S.cpx h).mixedI2 () () y‖ * η :=
    (hη _ y.snd.snd.2).trans_eq (mul_comm _ _)
  unfold readError
  exact residual_arith (norm_nonneg _) hC hδ₁0 hδ₂0 hη0 (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) n0 n1 n2 n3 n4
    (S.sum_norm_mixedComponents_le h y)
    (S.norm_inner_one_sub_J_le h _ _) (S.norm_inner_incl_sub_le h _ _ _)
    (S.norm_inner_one_sub_J_le h _ _) (S.norm_inner_incl_sub_le h _ _ _) b5
    (S.norm_inner_one_sub_J_le h _ _) (S.norm_inner_incl_sub_le h _ _ _)
    (S.norm_inner_one_sub_J_le h _ _) (S.norm_inner_incl_sub_le h _ _ _) b10
    (S.norm_inner_one_sub_J_le h _ _) (S.norm_inner_incl_sub_le h _ _ _)
    (S.norm_inner_one_sub_J_le h _ _) (S.norm_inner_incl_sub_le h _ _ _) b15

/-- **The error estimate of the mixed method with variational crimes**: for every discrete triple
`x̃` with cochain defects at most `δ₁`, `δ₂` and harmonic defect at most `η`,
`e(f) ≤ E + 240 C c_P² (5 ‖1 - Jₕ‖ ‖x̃‖ + C E + δ₁ + δ₂ + η)`, `E` the read error of `x̃`: best
approximation, inner-product defect and the defects of the reading map. Cf. [HolstStern2012],
Thm 3.10 (cochain reading maps, where `δ₁ = δ₂ = 0`) -/
theorem staticError_le_of_split {cP : ℝ} (hP : S.IsPoincare cP) (hcP : 1 ≤ cP) (h : κ)
    (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) {δ₁ δ₂ η : ℝ}
    (hδ₁0 : 0 ≤ δ₁) (hδ₂0 : 0 ≤ δ₂) (hη0 : 0 ≤ η)
    (hδ₁ : ∀ v, ‖⟪S.cochainDefect h (H.greenWave hcr f), v⟫_𝕜‖ ≤ δ₁ * (‖v‖ + ‖S.D h v‖))
    (hδ₂ : ∀ v, ‖⟪S.cochainDefect h (H.dGreenWave hcr f), v⟫_𝕜‖ ≤ δ₂ * (‖v‖ + ‖S.D h v‖))
    (hη : ∀ q ∈ (S.cpx h).harmonic (),
      ‖⟪S.incl h q, (H.greenWave hcr f : PiLp 2 W)⟫_𝕜‖ ≤ η * ‖q‖) :
    S.staticError hcr h f ≤ S.readError h (H.totalMixedSolution hcr f) x +
      240 * S.boundConst * cP ^ 2 * (5 * ‖1 - S.J h‖ * ‖x‖ +
        S.boundConst * S.readError h (H.totalMixedSolution hcr f) x + δ₁ + δ₂ + η) := by
  have h1 := S.staticError_le hcr hP hcP h f x
  have h2 := S.norm_staticResidual_le hcr h f x hδ₁0 hδ₂0 hη0 hδ₁ hδ₂ hη
  have : 0 ≤ 80 * S.boundConst * cP ^ 2 := by have := S.boundConst_nonneg; positivity
  calc _ ≤ _ := h1
    _ ≤ S.readError h (H.totalMixedSolution hcr f) x + 80 * S.boundConst * cP ^ 2 * (3 *
        (5 * ‖1 - S.J h‖ * ‖x‖ + S.boundConst * S.readError h (H.totalMixedSolution hcr f) x +
          δ₁ + δ₂ + η)) := add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 this)
    _ = _ := by ring

/-! #### Consistency and convergence -/

/-- **Consistent approximation** of the mixed solution with data `f` along `l`: discrete triples
whose read error and residual (dual graph norm) tend to `0`. -/
def StaticConsistent (l : Filter κ) (f : PiLp 2 W) : Prop :=
  ∀ ε > 0, ∀ᶠ h in l, ∃ x : (S.cpx h).MixedSpace () (),
    S.readError h (H.totalMixedSolution hcr f) x ≤ ε ∧ ‖S.staticResidual h f x‖ ≤ ε

theorem staticError_nonneg (h : κ) (f : PiLp 2 W) : 0 ≤ S.staticError hcr h f :=
  S.readError_nonneg h _ _

/-- **Consistent approximation is convergence**: under the uniform discrete Poincaré inequality,
`f` is consistently approximated iff `e(f) → 0`. Forward: the Strang lemma. Backward: the
discrete mixed solution has residual `0`. -/
theorem staticConsistent_iff_tendsto {cP : ℝ} (hP : S.IsPoincare cP) (hcP : 1 ≤ cP)
    (l : Filter κ) (f : PiLp 2 W) :
    S.StaticConsistent hcr l f ↔ Tendsto (fun h => S.staticError hcr h f) l (𝓝 0) := by
  constructor
  · intro hc
    rw [Metric.tendsto_nhds]
    intro ε hε
    set K := 1 + 80 * S.boundConst * cP ^ 2
    have hK : 0 < K := by have := S.boundConst_nonneg; positivity
    filter_upwards [hc (ε / (2 * K)) (by positivity)] with h ⟨x, hx1, hx2⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (S.staticError_nonneg hcr h f)]
    have h1 := S.staticError_le hcr hP hcP h f x
    have h2 : 80 * S.boundConst * cP ^ 2 * ‖S.staticResidual h f x‖ ≤
        80 * S.boundConst * cP ^ 2 * (ε / (2 * K)) :=
      mul_le_mul_of_nonneg_left hx2 (by have := S.boundConst_nonneg; positivity)
    have e : ε / (2 * K) + 80 * S.boundConst * cP ^ 2 * (ε / (2 * K)) = ε / 2 := by
      field_simp; ring
    linarith
  · intro ht ε hε
    filter_upwards [(Metric.tendsto_nhds.1 ht) ε hε] with h hh
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (S.staticError_nonneg hcr h f)] at hh
    exact ⟨S.mixedSol h f, hh.le, by rw [S.staticResidual_mixedSol, norm_zero]; exact hε.le⟩

/-- **Consistent approximation from vanishing defects**: if the inner-product defect tends to `0`
and `f` has bounded discrete approximants whose read error, cochain defects and harmonic defect
tend to `0`, then `f` is consistently approximated (`norm_staticResidual_le`). -/
theorem staticConsistent_of_split {l : Filter κ} (hJ : Tendsto (fun h => ‖1 - S.J h‖) l (𝓝 0))
    {B : ℝ} (f : PiLp 2 W)
    (happ : ∀ ε > 0, ∀ᶠ h in l, ∃ x : (S.cpx h).MixedSpace () (), ‖x‖ ≤ B ∧
      S.readError h (H.totalMixedSolution hcr f) x ≤ ε ∧
      (∀ v, ‖⟪S.cochainDefect h (H.greenWave hcr f), v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) ∧
      (∀ v, ‖⟪S.cochainDefect h (H.dGreenWave hcr f), v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) ∧
      ∀ q ∈ (S.cpx h).harmonic (),
        ‖⟪S.incl h q, (H.greenWave hcr f : PiLp 2 W)⟫_𝕜‖ ≤ ε * ‖q‖) :
    S.StaticConsistent hcr l f := by
  intro ε hε
  set C := S.boundConst
  have hC := S.boundConst_nonneg
  set B' := max B 0
  have hB' : 0 ≤ B' := le_max_right _ _
  set ε' := ε / (12 * (C + 4))
  have hε' : 0 < ε' := by positivity
  have hJev := (tendsto_order.1 hJ).2 (ε / (30 * (B' + 1))) (by positivity)
  filter_upwards [happ ε' hε', hJev] with h ⟨x, hxB, hE, hδ₁, hδ₂, hη⟩ hj
  refine ⟨x, hE.trans (div_le_self hε.le (by nlinarith)), ?_⟩
  refine (S.norm_staticResidual_le hcr h f x hε'.le hε'.le hε'.le hδ₁ hδ₂ hη).trans ?_
  have hxB' : ‖x‖ ≤ B' := hxB.trans (le_max_left _ _)
  have hj0 := norm_nonneg (1 - S.J h)
  have h1 : 5 * ‖1 - S.J h‖ * ‖x‖ ≤ ε / 6 := by
    have : ‖1 - S.J h‖ * ‖x‖ ≤ ε / (30 * (B' + 1)) * B' :=
      mul_le_mul hj.le hxB' (norm_nonneg _) (by positivity)
    have e : ε / (30 * (B' + 1)) * B' ≤ ε / 30 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have h2 : C * S.readError h (H.totalMixedSolution hcr f) x ≤ C * ε' :=
    mul_le_mul_of_nonneg_left hE hC
  have e1 : 3 * (C * ε' + ε' + ε' + ε') ≤ 3 * ((C + 4) * ε') := by nlinarith
  have e2 : 3 * ((C + 4) * ε') = ε / 4 := by
    have hC4 : C + 4 ≠ 0 := by positivity
    simp only [ε']; field_simp; ring
  nlinarith

/-- The read error is subadditive in the pair of triples. -/
theorem readError_add_le (h : κ) (X X' : H.total.MixedSpace () ())
    (x x' : (S.cpx h).MixedSpace () ()) :
    S.readError h (X + X') (x + x') ≤ S.readError h X x + S.readError h X' x' := by
  have key : ∀ (a a' : PiLp 2 W) (b b' : S.X h),
      ‖(a + a') - (S.incl h b + S.incl h b')‖ ≤ ‖a - S.incl h b‖ + ‖a' - S.incl h b'‖ :=
    fun a a' b b' => by rw [add_sub_add_comm]; exact norm_add_le _ _
  unfold readError
  simp only [_root_.map_add]
  linarith [key (H.total.mixedI0 () () X) (H.total.mixedI0 () () X') ((S.cpx h).mixedI0 () () x)
      ((S.cpx h).mixedI0 () () x'),
    key (H.total.mixedD0 () () X) (H.total.mixedD0 () () X') ((S.cpx h).mixedD0 () () x)
      ((S.cpx h).mixedD0 () () x'),
    key (H.total.mixedI1 () () X) (H.total.mixedI1 () () X') ((S.cpx h).mixedI1 () () x)
      ((S.cpx h).mixedI1 () () x'),
    key (H.total.mixedD1 () () () X) (H.total.mixedD1 () () () X') ((S.cpx h).mixedD1 () () () x)
      ((S.cpx h).mixedD1 () () () x'),
    key (H.total.mixedI2 () () X) (H.total.mixedI2 () () X') ((S.cpx h).mixedI2 () () x)
      ((S.cpx h).mixedI2 () () x')]

/-- The read error is at most `5 ‖X‖ + 5 C ‖x‖`. -/
theorem readError_le_norm (h : κ) (X : H.total.MixedSpace () ()) (x : (S.cpx h).MixedSpace () ()) :
    S.readError h X x ≤ 5 * ‖X‖ + 5 * S.boundConst * ‖x‖ := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := norm_mixedComponents_le H.total X
  obtain ⟨b0, b1, b2, b3, b4⟩ := norm_mixedComponents_le (S.cpx h) x
  have hC := S.boundConst_nonneg
  have key : ∀ (a : PiLp 2 W) (b : S.X h), ‖a‖ ≤ ‖X‖ → ‖b‖ ≤ ‖x‖ →
      ‖a - S.incl h b‖ ≤ ‖X‖ + S.boundConst * ‖x‖ := fun a b ha hb =>
    (norm_sub_le _ _).trans (add_le_add ha ((S.norm_incl_apply_le h b).trans
      (mul_le_mul_of_nonneg_left hb hC)))
  unfold readError
  linarith [key _ _ a0 b0, key _ _ a1 b1, key _ _ a2 b2, key _ _ a3 b3, key _ _ a4 b4]

/-- The constant `5 ‖f ↦ (σ, u, p)‖ + 80 c_P² C²` of `staticError_le_add`. -/
def staticLipConst (cP : ℝ) : ℝ :=
  5 * ‖H.totalMixedSolution hcr‖ + 80 * cP ^ 2 * S.boundConst ^ 2

/-- **The static error is Lipschitz in the data**, uniformly in `h`:
`e(f) ≤ e(g) + K ‖f - g‖`. -/
theorem staticError_le_add {cP : ℝ} (hP : S.IsPoincare cP) (hcP : 1 ≤ cP) (h : κ)
    (f g : PiLp 2 W) :
    S.staticError hcr h f ≤ S.staticError hcr h g + S.staticLipConst hcr cP * ‖f - g‖ := by
  have ef : f = g + (f - g) := by abel
  have h1 : S.staticError hcr h f ≤ S.staticError hcr h g +
      S.readError h (H.totalMixedSolution hcr (f - g)) (S.mixedSol h (f - g)) := by
    unfold staticError
    conv_lhs => rw [ef, _root_.map_add, _root_.map_add]
    exact S.readError_add_le h _ _ _ _
  have h2 := S.readError_le_norm h (H.totalMixedSolution hcr (f - g)) (S.mixedSol h (f - g))
  have h3 := (H.totalMixedSolution hcr).le_opNorm (f - g)
  have h4 := S.norm_mixedSol_le hP hcP h (f - g)
  have hC := S.boundConst_nonneg
  have h5 : 5 * S.boundConst * ‖S.mixedSol h (f - g)‖ ≤
      5 * S.boundConst * (16 * cP ^ 2 * S.boundConst * ‖f - g‖) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  unfold staticLipConst
  nlinarith

/-- **Convergence from a dense set of data**: under the uniform discrete Poincaré inequality, if
`e(g) → 0` on a dense set of data `g`, then `e(f) → 0` for every `f` (`staticError_le_add`). -/
theorem tendsto_staticError_of_dense {cP : ℝ} (hP : S.IsPoincare cP) (hcP : 1 ≤ cP)
    {l : Filter κ} {D : Set (PiLp 2 W)} (hD : Dense D)
    (hconv : ∀ g ∈ D, Tendsto (fun h => S.staticError hcr h g) l (𝓝 0)) (f : PiLp 2 W) :
    Tendsto (fun h => S.staticError hcr h f) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set K := S.staticLipConst hcr cP
  have hK : 0 ≤ K := by unfold K staticLipConst; positivity
  obtain ⟨g, hg, hfg⟩ := hD.exists_dist_lt f (show 0 < ε / (2 * (K + 1)) by positivity)
  rw [dist_eq_norm] at hfg
  filter_upwards [(Metric.tendsto_nhds.1 (hconv g hg)) (ε / 2) (half_pos hε)] with h hh
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (S.staticError_nonneg hcr h g)] at hh
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (S.staticError_nonneg hcr h f)]
  have h1 := S.staticError_le_add hcr hP hcP h f g
  have h2 : K * ‖f - g‖ ≤ K * (ε / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hfg.le hK
  have h3 : K * (ε / (2 * (K + 1))) < ε / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-! #### The discrete Poincaré inequality from the projections -/

/-- **The uniform discrete Poincaré inequality from the projections** (for cochain maps,
[HolstStern2012], §3): if `𝐝` has the Poincaré constant `c₀` on `(ker 𝐝)ᗮ`, `πₕ` maps `ker 𝐝`
into `ker 𝐝ₕ`, and `iₕ Xₕ ⊆ D(𝐝)` with `‖𝐝 iₕ v‖ ≤ C' ‖𝐝ₕ v‖` (`C' = C` when `iₕ` is a cochain
map), then `‖v‖ ≤ c₀ C C' ‖𝐝ₕ v‖` on `(ker 𝐝ₕ)ᗮ`: split `iₕ v` into its `ker 𝐝` part and the
rest, and project back. -/
theorem isPoincare_of_proj {c₀ C' : ℝ} (hc₀ : 0 ≤ c₀)
    (hc : ∀ z : H.totalD.domain, (z : PiLp 2 W) ∈ H.totalD.kerᗮ →
      ‖(z : PiLp 2 W)‖ ≤ c₀ * ‖H.totalD z‖)
    (hmem : ∀ h v, S.incl h v ∈ H.totalD.domain)
    (hd : ∀ h v, ‖H.totalD ⟨S.incl h v, hmem h v⟩‖ ≤ C' * ‖S.D h v‖)
    (hπ : ∀ h (z : H.totalD.domain), H.totalD z = 0 → S.D h (S.proj h z) = 0) :
    S.IsPoincare (c₀ * S.boundConst * C') := by
  intro h v hv
  by_cases hv0 : v = 0
  · rw [hv0, norm_zero, _root_.map_zero, norm_zero, mul_zero]
  set K := H.total.cycles ()
  set z : H.totalD.domain := ⟨S.incl h v, hmem h v⟩
  have hz0 : K.starProjection (z : PiLp 2 W) ∈ H.totalD.ker := K.starProjection_apply_mem _
  obtain ⟨y₀, hy₀, hy₀0⟩ := LinearPMap.mem_ker_iff.1 hz0
  have hperp : ((z - y₀ : H.totalD.domain) : PiLp 2 W) ∈ H.totalD.kerᗮ := by
    rw [Submodule.coe_sub, ← hy₀]; exact K.sub_starProjection_mem_orthogonal _
  have hd' : H.totalD (z - y₀) = H.totalD z := by rw [LinearPMap.map_sub, hy₀0, sub_zero]
  have h1 := hc _ hperp
  rw [hd'] at h1
  have hker : S.proj h y₀ ∈ LinearMap.ker (S.D h : S.X h →ₗ[𝕜] S.X h) := hπ h y₀ hy₀0
  set b := S.proj h ((z - y₀ : H.totalD.domain) : PiLp 2 W)
  have hv' : v = S.proj h y₀ + b := by
    rw [← _root_.map_add, Submodule.coe_sub, add_sub_cancel]; exact (S.proj_incl h v).symm
  have e : ⟪v, S.proj h y₀ + b⟫_𝕜 = ⟪v, S.proj h y₀⟫_𝕜 + ⟪v, b⟫_𝕜 := inner_add_right _ _ _
  rw [← hv', Submodule.inner_left_of_mem_orthogonal hker hv, zero_add] at e
  have hsq : ‖v‖ ^ 2 ≤ ‖v‖ * ‖b‖ := by
    rw [@norm_sq_eq_re_inner 𝕜, e]; exact re_inner_le_norm _ _
  have hb : ‖b‖ ≤ S.boundConst * (c₀ * (C' * ‖S.D h v‖)) := by
    have hC := S.boundConst_nonneg
    refine ((S.proj h).le_opNorm _).trans (mul_le_mul (S.norm_proj_le h) (h1.trans ?_)
      (norm_nonneg _) hC)
    exact mul_le_mul_of_nonneg_left (hd h v) hc₀
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have : ‖v‖ ≤ ‖b‖ := le_of_mul_le_mul_left (by nlinarith) hpos
  calc ‖v‖ ≤ _ := this.trans hb
    _ = _ := by ring

/-! #### The static verdict -/

variable (cP : ℝ) (l : Filter κ)

/-- **The conclusions of the static FEEC theorem with variational crimes**
(`ApproxComplexCrime.Family.staticFEEC`) for the mixed Hodge Laplacian of the total complex,
under closed range of `H` and the uniform discrete Poincaré inequality with constant `c_P`:
well-posedness, uniform stability, the Strang lemma, the splitting of the residual into the
crimes, the resulting error estimate, consistency as convergence, and convergence for every
datum from consistency on a dense set. [HolstStern2012], §3 -/
structure StaticVerdict : Prop where
  /-- the discrete mixed problem with the load `iₕ* f` is well posed -/
  wellPosed (h : κ) (f : PiLp 2 W) : ∃! x : (S.cpx h).MixedSpace () (),
    (S.cpx h).IsMixedSolution () () () ((S.incl h).adjoint f) x.fst x.snd.fst x.snd.snd
  /-- uniformly stable in the graph norms -/
  stable (h : κ) (f : PiLp 2 W) : ‖S.mixedSol h f‖ ≤ 16 * cP ^ 2 * S.boundConst * ‖f‖
  /-- the Strang lemma: best approximation plus consistency -/
  strang (h : κ) (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) :
    S.staticError hcr h f ≤
      S.readError h (H.totalMixedSolution hcr f) x + 80 * S.boundConst * cP ^ 2 *
        ‖S.staticResidual h f x‖
  /-- the residual splits into the inner-product defect, the read error, the cochain defects and
  the harmonic defect -/
  residual_le (h : κ) (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) {δ₁ δ₂ η : ℝ}
    (hδ₁0 : 0 ≤ δ₁) (hδ₂0 : 0 ≤ δ₂) (hη0 : 0 ≤ η)
    (hδ₁ : ∀ v, ‖⟪S.cochainDefect h (H.greenWave hcr f), v⟫_𝕜‖ ≤ δ₁ * (‖v‖ + ‖S.D h v‖))
    (hδ₂ : ∀ v, ‖⟪S.cochainDefect h (H.dGreenWave hcr f), v⟫_𝕜‖ ≤ δ₂ * (‖v‖ + ‖S.D h v‖))
    (hη : ∀ q ∈ (S.cpx h).harmonic (),
      ‖⟪S.incl h q, (H.greenWave hcr f : PiLp 2 W)⟫_𝕜‖ ≤ η * ‖q‖) :
    ‖S.staticResidual h f x‖ ≤ 3 * (5 * ‖1 - S.J h‖ * ‖x‖ +
      S.boundConst * S.readError h (H.totalMixedSolution hcr f) x + δ₁ + δ₂ + η)
  /-- the error estimate in terms of the crimes -/
  error_le (h : κ) (f : PiLp 2 W) (x : (S.cpx h).MixedSpace () ()) {δ₁ δ₂ η : ℝ}
    (hδ₁0 : 0 ≤ δ₁) (hδ₂0 : 0 ≤ δ₂) (hη0 : 0 ≤ η)
    (hδ₁ : ∀ v, ‖⟪S.cochainDefect h (H.greenWave hcr f), v⟫_𝕜‖ ≤ δ₁ * (‖v‖ + ‖S.D h v‖))
    (hδ₂ : ∀ v, ‖⟪S.cochainDefect h (H.dGreenWave hcr f), v⟫_𝕜‖ ≤ δ₂ * (‖v‖ + ‖S.D h v‖))
    (hη : ∀ q ∈ (S.cpx h).harmonic (),
      ‖⟪S.incl h q, (H.greenWave hcr f : PiLp 2 W)⟫_𝕜‖ ≤ η * ‖q‖) :
    S.staticError hcr h f ≤ S.readError h (H.totalMixedSolution hcr f) x +
      240 * S.boundConst * cP ^ 2 * (5 * ‖1 - S.J h‖ * ‖x‖ +
        S.boundConst * S.readError h (H.totalMixedSolution hcr f) x + δ₁ + δ₂ + η)
  /-- consistent approximation at `f` is convergence at `f` -/
  consistent_iff (f : PiLp 2 W) :
    S.StaticConsistent hcr l f ↔ Tendsto (fun h => S.staticError hcr h f) l (𝓝 0)
  /-- convergence for every datum from consistency on a dense set of data -/
  converges {D : Set (PiLp 2 W)} (hD : Dense D) (hc : ∀ g ∈ D, S.StaticConsistent hcr l g)
    (f : PiLp 2 W) : Tendsto (fun h => S.staticError hcr h f) l (𝓝 0)

variable {cP}

/-- **The static FEEC theorem with variational crimes**: for an approximating family of
discrete differential spaces of a Hilbert complex with closed range, under the uniform discrete
Poincaré inequality, the mixed Hodge Laplacian of the total complex with the load `iₕ* f` is
uniformly well posed, its error is best approximation plus the residual, the residual splits into
the inner-product defect, the cochain defects and the harmonic defect, and the method converges
for every datum once it is consistent on a dense set. The crime analogue of [HolstStern2012],
Thms 3.9, 3.10 (there for cochain reading maps); [AFW2010], Thm 3.8 -/
theorem staticFEEC (hcP : 1 ≤ cP) (hP : S.IsPoincare cP) : S.StaticVerdict hcr cP l :=
  ⟨S.wellPosed_mixedSol, S.norm_mixedSol_le hP hcP, S.staticError_le hcr hP hcP,
    fun h f x _ _ _ hδ₁0 hδ₂0 hη0 hδ₁ hδ₂ hη =>
      S.norm_staticResidual_le hcr h f x hδ₁0 hδ₂0 hη0 hδ₁ hδ₂ hη,
    fun h f x _ _ _ hδ₁0 hδ₂0 hη0 hδ₁ hδ₂ hη =>
      S.staticError_le_of_split hcr hP hcP h f x hδ₁0 hδ₂0 hη0 hδ₁ hδ₂ hη,
    S.staticConsistent_iff_tendsto hcr hP hcP l,
    fun hD hc f => S.tendsto_staticError_of_dense hcr hP hcP hD
      (fun g hg => (S.staticConsistent_iff_tendsto hcr hP hcP l g).1 (hc g hg)) f⟩

end ApproxComplexCrime.Family

end Feec.HilbertComplex
