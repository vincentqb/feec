module

public import Feec.HilbertComplex.Approximation.DissipFEEC

/-!
# Ritz projections: one object for cores and rate classes

The comparison trajectories of the dissipative FEEC theorem (`Feec.HilbertComplex.dissipFEEC`)
are, in every instance, a **Ritz projection** of the exact orbit: `pₕ(t) = Rₕ ℓ(S(t) x)` for
bounded `Rₕ : G → Xₕ` on an auxiliary normed space `G` into which the exact states are lifted by
`ℓ` (the identity, the graph of `𝐝`, the resolvent shift `1 - A`, …), with a **defect identity**

`Rₕ ℓ(A y) - Lₕ Rₕ ℓ(y) = Δₕ ℓ(A y) + Δₕ' ℓ(y)`

for bounded `Δₕ`, `Δₕ'`. This file states that object once and derives the core and the rate class
from it.

* A **lift** (`DissipFEEC.Lift`) is the exact side: a subspace of data `D ⊆ D(A)` kept by `S(t)`,
  a lift `ℓ : E → G` along whose orbits `t ↦ ℓ(S(t) x)` is `C¹` with derivative `ℓ(S(t) A x)`,
  and a bounded reading `ρ : G → E` with `ρ ℓ = 1` on `D`. `Lift.ofDomain` is the identity lift
  of `D(A)`.
* A **Ritz projection** (`DissipFEEC.Ritz`, fields `R`, `Δ`, `Δ'`, `defect_eq`, `bound`) is the
  discrete side, uniformly bounded. Its comparison is `Ritz.cmp`, its consistency defect is
  `Δₕ ℓ(S(t) A x) + Δₕ' ℓ(S(t) x)` (`Ritz.cmp_defect`).
* **Cores** (`Ritz.toCore`): `ιₕ Rₕ → ρ` and `Δₕ, Δₕ' → 0` strongly give the core `D`
  (uniformity on `[0, T]` from the compactness of the lifted orbits); for the identity lift this
  is the Trotter–Kato bridge `DissipFEEC.Core.ofOperator` (`Ritz.ofOperator`).
* **Rate classes** (`Ritz.toRateClass`): a **regularity scale** (`DissipFEEC.RegScale`: regular
  states `𝒮` with a norm `‖·‖_𝒮`, data whose orbits stay in `𝒮` with
  `‖S(t) x‖_𝒮 ≤ M ‖x‖_c` on `[0, T]`) and **static** estimates on `𝒮`,
  `‖y - ιₕ Rₕ ℓ y‖ ≤ C_s hᵅ ‖y‖_𝒮` and `‖Δₕ ℓ(A y)‖ + ‖Δₕ' ℓ y‖ ≤ C_d hᵅ ‖y‖_𝒮`, give a rate class
  with `C = C_s M`, `C' = C_d M`: the dynamic rate is the static one along the orbit. Two scales:
  `RegScale.trajectory` (regularity assumed along the orbit) and `RegScale.domainPow` (the graph
  norm of `Aᵏ` on `D(Aᵏ)`, kept with `M = 1` because `S(t)` commutes with `A` and is a
  contraction: no hypothesis along the orbit).

## Main results

* `DissipFEEC.Ritz.toCore`, `DissipFEEC.Ritz.toRateClass`;
* `DissipFEEC.RegScale.domainPow`: `D(Aᵏ)` with its graph norm is a regularity scale with `M = 1`.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.4 (Trotter–Kato approximation theorems)
* [M. F. Wheeler, *A priori L₂ error estimates for Galerkin approximations to parabolic partial differential equations*][Wheeler1973]
  (the Ritz projection as comparison function)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex.DissipFEEC

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  {A : E →ₗ.[𝕜] E} {κ : Type*} (F : DissipFEEC.{u} A κ)
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G] [IsScalarTower ℝ 𝕜 G]

/-! ### The exact flow on the domain -/

/-- `S(t)` commutes with `A` on `D(A)` (`t ≥ 0`), in terms of the extension `genExt A`. -/
theorem S_genExt {x : E} (hx : x ∈ A.domain) {t : ℝ} (ht : 0 ≤ t) :
    F.S t (genExt A x) = genExt A (F.S t x) := by
  have hm : F.S t x ∈ A.domain := F.isMDissipative.semigroup_mem_domain ⟨x, hx⟩ ht
  rw [genExt_of_mem hx, genExt_of_mem hm]
  exact (F.isMDissipative.apply_semigroup ⟨x, hx⟩ ht).symm

/-- `S(t)` is a contraction (`t ≥ 0`). -/
theorem norm_S_apply_le {t : ℝ} (ht : 0 ≤ t) (x : E) : ‖F.S t x‖ ≤ ‖x‖ :=
  ((F.S t).le_opNorm x).trans (by
    simpa [S_def] using mul_le_mul_of_nonneg_right
      (F.isMDissipative.isContraction_semigroup t ht) (norm_nonneg x))

/-! ### Lifts and Ritz projections -/

/-- A **lift** of the exact states into a normed space `G`: data `D ⊆ D(A)` kept by `S(t)`, a lift
`ℓ : E → G` (meaningful on `D`), along whose orbits `t ↦ ℓ(S(t) x)` is continuous on `[0, ∞)` with
right derivative `ℓ(S(t) A x)`, and a bounded reading `ρ : G → E` with `ρ ℓ = 1` on `D`. -/
structure Lift (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G] where
  /-- the data -/
  Data : Submodule 𝕜 E
  le_domain : Data ≤ A.domain
  S_mem : ∀ x ∈ Data, ∀ t, 0 ≤ t → F.S t x ∈ Data
  /-- the lift of the exact states -/
  lift : E → G
  /-- the reading of lifted states -/
  read : G →L[𝕜] E
  read_lift : ∀ y ∈ Data, read (lift y) = y
  continuousOn : ∀ x ∈ Data, ContinuousOn (fun t => lift (F.S t x)) (Ici 0)
  continuousOn' : ∀ x ∈ Data, ContinuousOn (fun t => lift (F.S t (genExt A x))) (Ici 0)
  hasDerivWithinAt : ∀ x ∈ Data, ∀ t, 0 ≤ t →
    HasDerivWithinAt (fun s => lift (F.S s x)) (lift (F.S t (genExt A x))) (Ici t) t

/-- The **identity lift** of `D(A)`: `G = E`, `ℓ = ρ = 1`. -/
def Lift.ofDomain : F.Lift E where
  Data := A.domain
  le_domain := le_rfl
  S_mem x hx _ ht := F.isMDissipative.semigroup_mem_domain ⟨x, hx⟩ ht
  lift y := y
  read := ContinuousLinearMap.id 𝕜 E
  read_lift _ _ := rfl
  continuousOn x _ := F.isMDissipative.semigroup.strongCont x
  continuousOn' x _ := F.isMDissipative.semigroup.strongCont (genExt A x)
  hasDerivWithinAt x hx _ ht := by
    have hd := F.isMDissipative.hasDerivWithinAt_semigroup ⟨x, hx⟩ ht
    rwa [← genExt_of_mem hx] at hd

variable {F} in
/-- A **Ritz projection** for the lift `Λ`: uniformly bounded `Rₕ : G → Xₕ` with a defect identity
`Rₕ ℓ(A y) - Lₕ Rₕ ℓ(y) = Δₕ ℓ(A y) + Δₕ' ℓ(y)` on the data, `Δₕ`, `Δₕ'` uniformly bounded.
[Wheeler1973]; [Pazy1983], §3.4 -/
structure Ritz (Λ : F.Lift G) where
  /-- the projection -/
  R : ∀ h, G →L[𝕜] F.X h
  /-- the defect on `ℓ(A y)` -/
  Δ : ∀ h, G →L[𝕜] F.X h
  /-- the defect on `ℓ(y)` -/
  Δ' : ∀ h, G →L[𝕜] F.X h
  defect_eq : ∀ h, ∀ y ∈ Λ.Data,
    R h (Λ.lift (genExt A y)) - F.L h (R h (Λ.lift y)) = Δ h (Λ.lift (genExt A y)) + Δ' h (Λ.lift y)
  bound : ∃ C, ∀ h, ‖R h‖ ≤ C ∧ ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C

namespace Ritz

variable {F} {Λ : F.Lift G} (𝓡 : F.Ritz Λ)

omit [IsScalarTower ℝ 𝕜 G] in
theorem bound_R : ∃ C, ∀ h, ‖𝓡.R h‖ ≤ C :=
  let ⟨C, hC⟩ := 𝓡.bound
  ⟨C, fun h => (hC h).1⟩

omit [IsScalarTower ℝ 𝕜 G] in
theorem bound_Δ : ∃ C, ∀ h, ‖𝓡.Δ h‖ ≤ C ∧ ‖𝓡.Δ' h‖ ≤ C :=
  let ⟨C, hC⟩ := 𝓡.bound
  ⟨C, fun h => (hC h).2⟩

/-- The comparison trajectories `pₕ(t) = Rₕ ℓ(S(t) x)` of a Ritz projection, with derivatives
`Rₕ ℓ(S(t) A x)`, on the data of the lift. -/
def cmp (T : ℝ) : F.Comparison T where
  Data := Λ.Data
  p x h t := 𝓡.R h (Λ.lift (F.S t x))
  p' x h t := 𝓡.R h (Λ.lift (F.S t (genExt A x)))
  continuousOn x hx h :=
    (𝓡.R h).continuous.comp_continuousOn ((Λ.continuousOn x hx).mono Icc_subset_Ici_self)
  continuousOn' x hx h :=
    (𝓡.R h).continuous.comp_continuousOn ((Λ.continuousOn' x hx).mono Icc_subset_Ici_self)
  hasDerivWithinAt x hx h t ht :=
    ((𝓡.R h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (Λ.hasDerivWithinAt x hx t ht.1)

/-- **The consistency defect of a Ritz projection** is `Δₕ ℓ(S(t) A x) + Δₕ' ℓ(S(t) x)`. -/
theorem cmp_defect (T : ℝ) {x : E} (hx : x ∈ Λ.Data) (h : κ) {t : ℝ} (ht : 0 ≤ t) :
    (𝓡.cmp T).defect x h t =
      𝓡.Δ h (Λ.lift (F.S t (genExt A x))) + 𝓡.Δ' h (Λ.lift (F.S t x)) := by
  change 𝓡.R h (Λ.lift (F.S t (genExt A x))) - F.L h (𝓡.R h (Λ.lift (F.S t x))) = _
  rw [F.S_genExt (Λ.le_domain hx) ht]
  exact 𝓡.defect_eq h _ (Λ.S_mem x hx t ht)

/-- **The core of a Ritz projection**: `ιₕ Rₕ g → ρ g` and `Δₕ g, Δₕ' g → 0` for every `g ∈ G`
give the core `D` of the lift; uniformity on `[0, T]` comes from the compactness of the lifted
orbits. [Pazy1983], §3.4 -/
def toCore (happrox : ∀ g, Tendsto (fun h => F.incl h (𝓡.R h g)) F.l (𝓝 (Λ.read g)))
    (hΔ0 : ∀ g, Tendsto (fun h => ‖𝓡.Δ h g‖) F.l (𝓝 0))
    (hΔ'0 : ∀ g, Tendsto (fun h => ‖𝓡.Δ' h g‖) F.l (𝓝 0)) : F.Core where
  Data := Λ.Data
  cmp := 𝓡.cmp
  data_eq _ := rfl
  tendsto_approx T x hx :=
    (tendstoUniformlyOn_apply_of_tendsto (P₀ := Λ.read) (F.bound_incl_comp 𝓡.bound_R) happrox
      (isCompact_Icc.image_of_continuousOn ((Λ.continuousOn x hx).mono Icc_subset_Ici_self))
      ).congr_right fun t ht => Λ.read_lift _ (Λ.S_mem x hx t ht.1)
  tendsto_defect T x hx := tendstoUniformlyOn_norm_of_le 𝓡.bound_Δ hΔ0 hΔ'0
    (isCompact_Icc.image_of_continuousOn ((Λ.continuousOn' x hx).mono Icc_subset_Ici_self))
    (isCompact_Icc.image_of_continuousOn ((Λ.continuousOn x hx).mono Icc_subset_Ici_self))
    fun h t ht => by rw [𝓡.cmp_defect T hx h ht.1]; exact norm_add_le _ _

@[simp] theorem toCore_data {happrox hΔ0 hΔ'0} : (𝓡.toCore happrox hΔ0 hΔ'0).Data = Λ.Data :=
  rfl

end Ritz

/-- The Ritz projection of the identity lift given by bounded `Rₕ : E → Xₕ` with a defect identity
`Rₕ (A y) - Lₕ Rₕ y = Δₕ (A y) + Δₕ' y` on `D(A)`: its comparison is `Comparison.ofOperator` and
its core is the Trotter–Kato bridge `Core.ofOperator`. -/
def Ritz.ofOperator (R Δ Δ' : ∀ h, E →L[𝕜] F.X h) (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : A.domain), R h (A y) - F.L h (R h y) = Δ h (A y) + Δ' h y) :
    F.Ritz (Lift.ofDomain F) where
  R := R
  Δ := Δ
  Δ' := Δ'
  defect_eq h y hy := by
    change R h (genExt A y) - F.L h (R h y) = Δ h (genExt A y) + Δ' h y
    rw [genExt_of_mem hy]
    exact hdef h ⟨y, hy⟩
  bound :=
    let ⟨C₁, h₁⟩ := hR
    let ⟨C₂, h₂⟩ := hΔ
    ⟨max C₁ C₂, fun h => ⟨(h₁ h).trans (le_max_left _ _), (h₂ h).1.trans (le_max_right _ _),
      (h₂ h).2.trans (le_max_right _ _)⟩⟩

/-! ### Regularity scales and rate classes -/

/-- A **regularity scale** on `[0, T]`: regular states `𝒮` with a norm `‖·‖_𝒮`, and data whose
orbits stay in `𝒮` with `‖S(t) x‖_𝒮 ≤ M ‖x‖_c` for `t ∈ [0, T]`. -/
structure RegScale (T : ℝ) where
  /-- the regular states -/
  Reg : Set E
  /-- their norm -/
  regNorm : E → ℝ
  /-- the data -/
  Data : Set E
  /-- the norm of the data -/
  classNorm : E → ℝ
  /-- the growth constant of the regular norm along the orbits -/
  M : ℝ
  mem : ∀ x ∈ Data, ∀ t ∈ Icc 0 T, F.S t x ∈ Reg
  regNorm_le : ∀ x ∈ Data, ∀ t ∈ Icc 0 T, regNorm (F.S t x) ≤ M * classNorm x

/-- The **trajectory scale**: data in `D` whose orbit on `[0, T]` stays in `𝒮` with
`‖S(t) x‖_𝒮 ≤ c(x)`, `M = 1` (the regularity is assumed along the orbit). -/
def RegScale.trajectory (T : ℝ) (D Reg : Set E) (regNorm classNorm : E → ℝ) : F.RegScale T where
  Reg := Reg
  regNorm := regNorm
  Data := {x ∈ D | ∀ t ∈ Icc 0 T, F.S t x ∈ Reg ∧ regNorm (F.S t x) ≤ classNorm x}
  classNorm := classNorm
  M := 1
  mem _ hx t ht := (hx.2 t ht).1
  regNorm_le _ hx t ht := (one_mul (classNorm _)).symm ▸ (hx.2 t ht).2

/-- The domain of `Aᵏ`: `A^[j] y ∈ D(A)` for `j < k` (with `A` extended by `0`, `genExt`). -/
def iterDomain (A : E →ₗ.[𝕜] E) (k : ℕ) : Set E := {y | ∀ j < k, (genExt A)^[j] y ∈ A.domain}

/-- The graph norm of `Aᵏ`: `Σ_{j ≤ k} ‖Aʲ y‖`. -/
def iterDomainNorm (A : E →ₗ.[𝕜] E) (k : ℕ) (y : E) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ‖(genExt A)^[j] y‖

/-- `S(t)` keeps `D(Aᵏ)` and commutes with `Aʲ` on it, `j ≤ k` (`t ≥ 0`). -/
theorem iterate_genExt_S {k : ℕ} {x : E} (hx : x ∈ iterDomain A k) {t : ℝ} (ht : 0 ≤ t) :
    ∀ j ≤ k, (genExt A)^[j] (F.S t x) = F.S t ((genExt A)^[j] x) := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega),
      F.S_genExt (hx j (by omega)) ht]

theorem S_mem_iterDomain {k : ℕ} {x : E} (hx : x ∈ iterDomain A k) {t : ℝ} (ht : 0 ≤ t) :
    F.S t x ∈ iterDomain A k := fun j hj => by
  rw [F.iterate_genExt_S hx ht j hj.le]
  exact F.isMDissipative.semigroup_mem_domain ⟨_, hx j hj⟩ ht

theorem iterDomainNorm_S_le {k : ℕ} {x : E} (hx : x ∈ iterDomain A k) {t : ℝ} (ht : 0 ≤ t) :
    iterDomainNorm A k (F.S t x) ≤ iterDomainNorm A k x :=
  Finset.sum_le_sum fun j hj => by
    rw [F.iterate_genExt_S hx ht j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
    exact F.norm_S_apply_le ht _

/-- **The domain scale**: `D(Aᵏ)` with the graph norm of `Aᵏ`, data `D ∩ D(Aᵏ)`, `M = 1`. No
regularity is assumed along the orbit: `S(t)` keeps `D(Aᵏ)`, commutes with `A` and is a
contraction. -/
def RegScale.domainPow (T : ℝ) (D : Set E) (k : ℕ) : F.RegScale T where
  Reg := iterDomain A k
  regNorm := iterDomainNorm A k
  Data := D ∩ iterDomain A k
  classNorm := iterDomainNorm A k
  M := 1
  mem _ hx _ ht := F.S_mem_iterDomain hx.2 ht.1
  regNorm_le _ hx _ ht := (one_mul (iterDomainNorm A k _)).symm ▸ F.iterDomainNorm_S_le hx.2 ht.1

variable {F} {Λ : F.Lift G}

/-- **The rate class of a Ritz projection**: static estimates on the regular states of a scale,
`‖y - ιₕ Rₕ ℓ y‖ ≤ C_s hᵅ ‖y‖_𝒮` and `‖Δₕ ℓ(A y)‖ + ‖Δₕ' ℓ y‖ ≤ C_d hᵅ ‖y‖_𝒮`, give a rate class
on the data of the scale, with `C = C_s M` and `C' = C_d M`. -/
def Ritz.toRateClass (𝓡 : F.Ritz Λ) {T : ℝ} (𝒮 : F.RegScale T) (hD : 𝒮.Data ⊆ Λ.Data)
    (meshSize : κ → ℝ) (hmesh : ∀ h, 0 ≤ meshSize h) (α Cs Cd : ℝ) (hCs : 0 ≤ Cs)
    (hCd : 0 ≤ Cd)
    (happrox : ∀ y ∈ 𝒮.Reg, ∀ h,
      ‖y - F.incl h (𝓡.R h (Λ.lift y))‖ ≤ Cs * meshSize h ^ α * 𝒮.regNorm y)
    (hdefect : ∀ y ∈ 𝒮.Reg, ∀ h, ‖𝓡.Δ h (Λ.lift (genExt A y))‖ + ‖𝓡.Δ' h (Λ.lift y)‖ ≤
      Cd * meshSize h ^ α * 𝒮.regNorm y) : F.RateClass T where
  toComparison := (𝓡.cmp T).restrict 𝒮.Data hD
  classNorm := 𝒮.classNorm
  meshSize := meshSize
  α := α
  C := Cs * 𝒮.M
  C' := Cd * 𝒮.M
  approx x hx h t ht := by
    have hr := 𝒮.regNorm_le x hx t ht
    have hc : 0 ≤ Cs * meshSize h ^ α := mul_nonneg hCs (Real.rpow_nonneg (hmesh h) _)
    calc _ ≤ Cs * meshSize h ^ α * 𝒮.regNorm (F.S t x) := happrox _ (𝒮.mem x hx t ht) h
      _ ≤ Cs * meshSize h ^ α * (𝒮.M * 𝒮.classNorm x) := mul_le_mul_of_nonneg_left hr hc
      _ = _ := by ring
  consistency x hx h t ht := by
    have hr := 𝒮.regNorm_le x hx t ht
    have hc : 0 ≤ Cd * meshSize h ^ α := mul_nonneg hCd (Real.rpow_nonneg (hmesh h) _)
    have e : ((𝓡.cmp T).restrict 𝒮.Data hD).defect x h t = (𝓡.cmp T).defect x h t := rfl
    rw [e, 𝓡.cmp_defect T (hD hx) h ht.1, F.S_genExt (Λ.le_domain (hD hx)) ht.1]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ Cd * meshSize h ^ α * 𝒮.regNorm (F.S t x) := hdefect _ (𝒮.mem x hx t ht) h
      _ ≤ Cd * meshSize h ^ α * (𝒮.M * 𝒮.classNorm x) := mul_le_mul_of_nonneg_left hr hc
      _ = _ := by ring

end Feec.HilbertComplex.DissipFEEC
