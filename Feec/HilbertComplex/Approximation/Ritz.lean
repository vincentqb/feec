module

public import Feec.HilbertComplex.Approximation.DissipFEEC
public import Feec.HilbertComplex.HodgeLaplacian

/-!
# Ritz projections: one object for cores and rate classes

A Ritz projection `pₕ(t) = Rₕ ℓ(S(t) x)` of the exact orbit, for a lift `ℓ` of the exact states and
bounded `Rₕ` with a defect identity, gives a core and rate classes of the dissipative FEEC theorem.

## Main definitions

* `DissipFEEC.Lift`: lifts of the exact states.
* `DissipFEEC.Ritz`: Ritz projections, with their core `Ritz.toCore`.
* `DissipFEEC.Ritz.orbitRateClass`, `DissipFEEC.Ritz.toRateClass`: their rate classes.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983]
* [M. F. Wheeler, *A priori L₂ error estimates for Galerkin approximations to parabolic partial differential equations*][Wheeler1973]

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

theorem S_genExt {x : E} (hx : x ∈ A.domain) {t : ℝ} (ht : 0 ≤ t) :
    F.S t (genExt A x) = genExt A (F.S t x) := by
  have hm : F.S t x ∈ A.domain := F.isMDissipative.semigroup_mem_domain ⟨x, hx⟩ ht
  rw [genExt_of_mem hx, genExt_of_mem hm]
  exact (F.isMDissipative.apply_semigroup ⟨x, hx⟩ ht).symm

theorem norm_S_apply_le {t : ℝ} (ht : 0 ≤ t) (x : E) : ‖F.S t x‖ ≤ ‖x‖ :=
  ((F.S t).le_opNorm x).trans (by
    simpa [S_def] using mul_le_mul_of_nonneg_right
      (F.isMDissipative.isContraction_semigroup t ht) (norm_nonneg x))

/-! ### Lifts and Ritz projections -/

/-- A lift of the exact states: data `D ⊆ D(A)`, a lift `ℓ : E → G`, a reading `ρ`, `ρ ℓ = 1`. -/
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

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem mem_sqDomain_iff {x : E} : x ∈ A.sqDomain ↔ x ∈ A.domain ∧ genExt A x ∈ A.domain :=
  ⟨fun ⟨hx, h⟩ => ⟨hx, (genExt_of_mem hx).symm ▸ h⟩,
    fun ⟨hx, h⟩ => ⟨hx, (genExt_of_mem hx) ▸ h⟩⟩

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem _root_.LinearPMap.IsMDissipative.dense_sqDomain (hA : A.IsMDissipative) :
    Dense (A.sqDomain : Set E) := by
  have hR := hA.isResolvent_one
  set R := Operator.resolvent A 1
  have h1 : ∀ y ∈ A.domain, R y ∈ A.sqDomain := fun y hy => by
    refine ⟨hR.mem_domain y, ?_⟩
    have e : A ⟨R y, hR.mem_domain y⟩ = R y - y := by
      have h := hR.sub_apply y
      rw [one_smul] at h
      exact (sub_sub_cancel _ _).symm.trans (congrArg (R y - ·) h)
    rw [e]
    exact sub_mem (hR.mem_domain y) hy
  have h2 : (A.domain : Set E) ⊆ closure (A.sqDomain : Set E) := fun x hx => by
    have e : x = R ((1 : 𝕜) • x - A ⟨x, hx⟩) := (hR.apply_sub ⟨x, hx⟩).symm
    have hm : (1 : 𝕜) • x - A ⟨x, hx⟩ ∈ closure (A.domain : Set E) := by
      rw [hA.dense_domain.closure_eq]; trivial
    rw [e]
    exact closure_mono (by rintro _ ⟨y, hy, rfl⟩; exact h1 y hy)
      (image_closure_subset_closure_image R.continuous ⟨_, hm, rfl⟩)
  rw [dense_iff_closure_eq, ← Set.univ_subset_iff, ← hA.dense_domain.closure_eq]
  exact closure_minimal h2 isClosed_closure

/-- The graph lift `ℓ y = (y, A y)` of `D(A²)`, with a reading `ρ`, `ρ (y, A y) = y`. -/
def Lift.graph (read : E × E →L[𝕜] E) (hread : ∀ y ∈ A.sqDomain, read (y, genExt A y) = y) :
    F.Lift (E × E) where
  Data := A.sqDomain
  le_domain _ hx := hx.1
  S_mem x hx t ht := by
    obtain ⟨hx, hx'⟩ := mem_sqDomain_iff.1 hx
    refine mem_sqDomain_iff.2 ⟨F.isMDissipative.semigroup_mem_domain ⟨x, hx⟩ ht, ?_⟩
    rw [← F.S_genExt hx ht]
    exact F.isMDissipative.semigroup_mem_domain ⟨_, hx'⟩ ht
  lift y := (y, genExt A y)
  read := read
  read_lift := hread
  continuousOn x hx := by
    have hx := (mem_sqDomain_iff.1 hx).1
    exact (F.isMDissipative.semigroup.strongCont x).prodMk
      ((F.isMDissipative.semigroup.strongCont (genExt A x)).congr fun t ht =>
        (F.S_genExt hx ht).symm)
  continuousOn' x hx := by
    have hx := (mem_sqDomain_iff.1 hx).2
    exact (F.isMDissipative.semigroup.strongCont (genExt A x)).prodMk
      ((F.isMDissipative.semigroup.strongCont (genExt A (genExt A x))).congr fun t ht =>
        (F.S_genExt hx ht).symm)
  hasDerivWithinAt x hx t ht := by
    obtain ⟨hx, hx'⟩ := mem_sqDomain_iff.1 hx
    have h2 := ((Lift.ofDomain F).hasDerivWithinAt _ hx' t ht).congr
      (fun s hs => (F.S_genExt hx (ht.trans hs)).symm) (F.S_genExt hx ht).symm
    rw [F.S_genExt hx' ht] at h2
    exact ((Lift.ofDomain F).hasDerivWithinAt x hx t ht).prodMk h2

@[simp] theorem Lift.graph_data {read : E × E →L[𝕜] E} {hread} :
    (Lift.graph F read hread).Data = A.sqDomain := rfl

@[simp] theorem Lift.graph_lift {read : E × E →L[𝕜] E} {hread} (y : E) :
    (Lift.graph F read hread).lift y = (y, genExt A y) := rfl

variable {F} in
/-- The comparison trajectories `pₕ(t) = Rₕ ℓ(S(t) x)` of bounded `Rₕ : G → Xₕ`. -/
def Lift.cmp (Λ : F.Lift G) (R : ∀ h, G →L[𝕜] F.X h) (T : ℝ) : F.Comparison T where
  Data := Λ.Data
  p x h t := R h (Λ.lift (F.S t x))
  p' x h t := R h (Λ.lift (F.S t (genExt A x)))
  continuousOn x hx h :=
    (R h).continuous.comp_continuousOn ((Λ.continuousOn x hx).mono Icc_subset_Ici_self)
  continuousOn' x hx h :=
    (R h).continuous.comp_continuousOn ((Λ.continuousOn' x hx).mono Icc_subset_Ici_self)
  hasDerivWithinAt x hx h t ht :=
    ((R h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (Λ.hasDerivWithinAt x hx t ht.1)

variable {F} in
/-- A Ritz projection: `Rₕ ℓ(A y) - Lₕ Rₕ ℓ y = Δₕ ℓ(A y) + Δₕ' ℓ y`, all bounded. [Wheeler1973] -/
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

/-- The comparison trajectories `pₕ(t) = Rₕ ℓ(S(t) x)` of a Ritz projection. -/
def cmp (T : ℝ) : F.Comparison T := Λ.cmp 𝓡.R T

theorem cmp_defect (T : ℝ) {x : E} (hx : x ∈ Λ.Data) (h : κ) {t : ℝ} (ht : 0 ≤ t) :
    (𝓡.cmp T).defect x h t =
      𝓡.Δ h (Λ.lift (F.S t (genExt A x))) + 𝓡.Δ' h (Λ.lift (F.S t x)) := by
  change 𝓡.R h (Λ.lift (F.S t (genExt A x))) - F.L h (𝓡.R h (Λ.lift (F.S t x))) = _
  rw [F.S_genExt (Λ.le_domain hx) ht]
  exact 𝓡.defect_eq h _ (Λ.S_mem x hx t ht)

/-- The core of a Ritz projection with `ιₕ Rₕ → ρ` and `Δₕ, Δₕ' → 0` strongly. [Pazy1983], §3.4 -/
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

/-- The Ritz projection of the identity lift given by a defect identity on `D(A)`. -/
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

/-- A regularity scale on `[0, T]`: normed regular states and data whose orbits stay in them. -/
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

/-- The trajectory scale: data whose orbits on `[0, T]` stay in the regular states, `M = 1`. -/
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

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem mem_graph_of_mem_iterDomain {k : ℕ} {y : E} (hy : y ∈ iterDomain A k) :
    ∀ j < k, ((genExt A)^[j] y, (genExt A)^[j + 1] y) ∈ A.graph := fun j hj => by
  rw [Function.iterate_succ_apply', genExt_of_mem (hy j hj)]
  exact A.mem_graph ⟨_, hy j hj⟩

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

/-- **The domain scale**: `D(Aᵏ)` with the graph norm of `Aᵏ`, data `D ∩ D(Aᵏ)`, `M = 1`. -/
def RegScale.domainPow (T : ℝ) (D : Set E) (k : ℕ) : F.RegScale T where
  Reg := iterDomain A k
  regNorm := iterDomainNorm A k
  Data := D ∩ iterDomain A k
  classNorm := iterDomainNorm A k
  M := 1
  mem _ hx _ ht := F.S_mem_iterDomain hx.2 ht.1
  regNorm_le _ hx _ ht := (one_mul (iterDomainNorm A k _)).symm ▸ F.iterDomainNorm_S_le hx.2 ht.1

variable {F} {Λ : F.Lift G}

/-- The rate class of a Ritz projection from estimates along the orbits of its data. -/
def Ritz.orbitRateClass (𝓡 : F.Ritz Λ) {T : ℝ} (D : Set E) (hD : D ⊆ Λ.Data)
    (classNorm : E → ℝ) (meshSize : κ → ℝ) (α C C' : ℝ)
    (happrox : ∀ x ∈ D, ∀ h, ∀ t ∈ Icc 0 T,
      ‖F.S t x - F.incl h (𝓡.R h (Λ.lift (F.S t x)))‖ ≤ C * meshSize h ^ α * classNorm x)
    (hdefect : ∀ x ∈ D, ∀ h, ∀ t ∈ Icc 0 T,
      ‖𝓡.Δ h (Λ.lift (F.S t (genExt A x)))‖ + ‖𝓡.Δ' h (Λ.lift (F.S t x))‖ ≤
        C' * meshSize h ^ α * classNorm x) : F.RateClass T where
  toComparison := (𝓡.cmp T).restrict D hD
  classNorm := classNorm
  meshSize := meshSize
  α := α
  C := C
  C' := C'
  approx := happrox
  consistency x hx h t ht := by
    have e : ((𝓡.cmp T).restrict D hD).defect x h t = (𝓡.cmp T).defect x h t := rfl
    rw [e, 𝓡.cmp_defect T (hD hx) h ht.1]
    exact (norm_add_le _ _).trans (hdefect x hx h t ht)

/-- The rate class of a Ritz projection from static estimates on a regularity scale. -/
def Ritz.toRateClass (𝓡 : F.Ritz Λ) {T : ℝ} (𝒮 : F.RegScale T) (hD : 𝒮.Data ⊆ Λ.Data)
    (meshSize : κ → ℝ) (hmesh : ∀ h, 0 ≤ meshSize h) (α Cs Cd : ℝ) (hCs : 0 ≤ Cs)
    (hCd : 0 ≤ Cd)
    (happrox : ∀ y ∈ 𝒮.Reg, ∀ h,
      ‖y - F.incl h (𝓡.R h (Λ.lift y))‖ ≤ Cs * meshSize h ^ α * 𝒮.regNorm y)
    (hdefect : ∀ y ∈ 𝒮.Reg, ∀ h, ‖𝓡.Δ h (Λ.lift (genExt A y))‖ + ‖𝓡.Δ' h (Λ.lift y)‖ ≤
      Cd * meshSize h ^ α * 𝒮.regNorm y) : F.RateClass T :=
  𝓡.orbitRateClass 𝒮.Data hD 𝒮.classNorm meshSize α (Cs * 𝒮.M) (Cd * 𝒮.M)
    (fun x hx h t ht => by
      have hc : 0 ≤ Cs * meshSize h ^ α := mul_nonneg hCs (Real.rpow_nonneg (hmesh h) _)
      calc _ ≤ Cs * meshSize h ^ α * 𝒮.regNorm (F.S t x) := happrox _ (𝒮.mem x hx t ht) h
        _ ≤ Cs * meshSize h ^ α * (𝒮.M * 𝒮.classNorm x) :=
          mul_le_mul_of_nonneg_left (𝒮.regNorm_le x hx t ht) hc
        _ = _ := by ring)
    (fun x hx h t ht => by
      have hc : 0 ≤ Cd * meshSize h ^ α := mul_nonneg hCd (Real.rpow_nonneg (hmesh h) _)
      rw [F.S_genExt (Λ.le_domain (hD hx)) ht.1]
      calc _ ≤ Cd * meshSize h ^ α * 𝒮.regNorm (F.S t x) := hdefect _ (𝒮.mem x hx t ht) h
        _ ≤ Cd * meshSize h ^ α * (𝒮.M * 𝒮.classNorm x) :=
          mul_le_mul_of_nonneg_left (𝒮.regNorm_le x hx t ht) hc
        _ = _ := by ring)

end Feec.HilbertComplex.DissipFEEC
