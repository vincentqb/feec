module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Prod

/-!
# BGG data: two complexes linked by connecting maps

Two complexes `(V, d)` and `(Ṽ, d̃)` of modules on any complex shape, linked by connecting maps
`S` with `d S = -S d̃` ([ArnoldHu2021], (19)–(22)): one segment gives the complex (5.1) of
[QuennevilleBelair2015], §5.1, and data of any length the twisted complex.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.1
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], (19)–(22), §5.1

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

universe u v

namespace Feec.BGG

/-! ## One segment: the input of the complex (5.1) -/

/-- One segment of BGG data: `V⁰ → V¹ → V²`, `Ṽ⁰ → Ṽ¹ → Ṽ²` and `S₀`, `S₁` with `d¹S₀ = -S₁d̃⁰`. -/
structure Segment (R : Type*) [Ring R] (V0 V1 V2 Vt0 Vt1 Vt2 : Type*)
    [AddCommGroup V0] [Module R V0] [AddCommGroup V1] [Module R V1]
    [AddCommGroup V2] [Module R V2] [AddCommGroup Vt0] [Module R Vt0]
    [AddCommGroup Vt1] [Module R Vt1] [AddCommGroup Vt2] [Module R Vt2] where
  d0 : V0 →ₗ[R] V1
  d1 : V1 →ₗ[R] V2
  dt0 : Vt0 →ₗ[R] Vt1
  dt1 : Vt1 →ₗ[R] Vt2
  S0 : Vt0 →ₗ[R] V1
  S1 : Vt1 →ₗ[R] V2
  d1_d0 : ∀ σ, d1 (d0 σ) = 0
  dt1_dt0 : ∀ φ, dt1 (dt0 φ) = 0
  anticomm : ∀ φ, d1 (S0 φ) = -S1 (dt0 φ)

namespace Segment

variable {R : Type*} [Ring R] {V0 V1 V2 Vt0 Vt1 Vt2 : Type*}
  [AddCommGroup V0] [Module R V0] [AddCommGroup V1] [Module R V1]
  [AddCommGroup V2] [Module R V2] [AddCommGroup Vt0] [Module R Vt0]
  [AddCommGroup Vt1] [Module R Vt1] [AddCommGroup Vt2] [Module R Vt2]
  (D : Segment R V0 V1 V2 Vt0 Vt1 Vt2)

/-- Exactness of the top complex at `V¹`. -/
def ExactTop : Prop := LinearMap.ker D.d1 = LinearMap.range D.d0

/-- Exactness of the bottom complex at `Ṽ¹`. -/
def ExactBot : Prop := LinearMap.ker D.dt1 = LinearMap.range D.dt0

/-- `Γ = {(σ, φ) | d⁰σ = S₀φ}`. -/
def Γ : Submodule R (V0 × Vt0) :=
  LinearMap.ker (D.d0.comp (LinearMap.fst R V0 Vt0) - D.S0.comp (LinearMap.snd R V0 Vt0))

theorem mem_Γ {x : V0 × Vt0} : x ∈ D.Γ ↔ D.d0 x.1 = D.S0 x.2 := by
  simp [Γ, sub_eq_zero]

/-- The first operator `(0 d̃) : Γ → Ṽ¹` of the complex (5.1). -/
def D0 : D.Γ →ₗ[R] Vt1 := D.dt0.comp ((LinearMap.snd R V0 Vt0).comp D.Γ.subtype)

/-- The second operator `(S₁, d̃¹) : Ṽ¹ → V² × Ṽ²` of the complex (5.1). -/
def D1 : Vt1 →ₗ[R] V2 × Vt2 := D.S1.prod D.dt1

@[simp] lemma D1_apply (u : Vt1) : D.D1 u = (D.S1 u, D.dt1 u) := rfl

lemma S1_dt0_of_mem {x : V0 × Vt0} (hx : x ∈ D.Γ) : D.S1 (D.dt0 x.2) = 0 := by
  have h := D.d1_d0 x.1
  rw [D.mem_Γ.1 hx, D.anticomm] at h
  simpa using h

lemma S1_dt0_eq_zero {ψ : Vt0} (hψ : D.S0 ψ = 0) : D.S1 (D.dt0 ψ) = 0 := by
  have := D.anticomm ψ; rw [hψ, map_zero] at this; exact neg_eq_zero.mp this.symm

/-- (5.1) is a complex: `(S₁, d̃¹) ∘ (0 d̃) = 0`. [QuennevilleBelair2015], Prop 5.1 -/
theorem D1_D0 (x : D.Γ) : D.D1 (D.D0 x) = 0 := by
  obtain ⟨⟨σ, φ⟩, hx⟩ := x
  have h := D.d1_d0 σ
  rw [(D.mem_Γ).1 hx, D.anticomm] at h
  simp [D0, D1, neg_eq_zero.mp h, D.dt1_dt0]

/-- `R(0 d̃) = R(d̃⁰) ∩ N(S₁)` when the top complex is exact at `V¹`. -/
theorem range_D0 (hT : D.ExactTop) :
    LinearMap.range D.D0 = LinearMap.range D.dt0 ⊓ LinearMap.ker D.S1 := by
  ext y
  simp only [LinearMap.mem_range, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨_, rfl⟩, D.S1_dt0_of_mem x.2⟩
  · rintro ⟨⟨φ, rfl⟩, hS⟩
    have : D.S0 φ ∈ LinearMap.ker D.d1 := by simp [D.anticomm, hS]
    rw [hT] at this
    obtain ⟨σ, hσ⟩ := this
    exact ⟨⟨(σ, φ), D.mem_Γ.2 hσ⟩, rfl⟩

/-- (5.1) is exact at `Ṽ¹` when the top complex is exact at `V¹` and the bottom one at `Ṽ¹`.
Cf. [QuennevilleBelair2015], Prop 5.1 -/
theorem ker_D1_eq_range_D0 (hT : D.ExactTop) (hB : D.ExactBot) :
    LinearMap.ker D.D1 = LinearMap.range D.D0 := by
  rw [range_D0 D hT, ← hB]
  ext u
  simp [and_comm]

theorem D0_injective (hd0 : Function.Injective D.d0) (hdt0 : Function.Injective D.dt0) :
    Function.Injective D.D0 := by
  rintro ⟨⟨σ, φ⟩, hx⟩ ⟨⟨τ, ψ⟩, hy⟩ e
  have hφ : φ = ψ := hdt0 e
  subst hφ
  have h1 := D.mem_Γ.1 hx
  have h2 := D.mem_Γ.1 hy
  have : σ = τ := hd0 (h1.trans h2.symm)
  subst this
  rfl

/-- If `d¹V¹ ⊆ d¹S₀Ṽ⁰`, then `R(S₁, d̃¹) = {(ρ, μ) | ∃ w, d̃¹w = μ, ρ - S₁w ∈ R(d¹)}`. -/
theorem range_D1 (hreg : LinearMap.range D.d1 ≤ LinearMap.range (D.d1 ∘ₗ D.S0)) :
    (LinearMap.range D.D1 : Set (V2 × Vt2)) =
      {p | ∃ w, D.dt1 w = p.2 ∧ p.1 - D.S1 w ∈ LinearMap.range D.d1} := by
  ext ⟨ρ, μ⟩
  simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_ofPred_eq, D1_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨u, rfl, rfl⟩
    exact ⟨u, rfl, 0, by simp⟩
  · rintro ⟨w, hw, hρ⟩
    obtain ⟨φ, hφ⟩ := hreg hρ
    simp only [LinearMap.comp_apply, D.anticomm] at hφ
    refine ⟨w - D.dt0 φ, ?_, ?_⟩
    · rw [map_sub, sub_eq_add_neg, hφ]; abel
    · simp [D.dt1_dt0, hw]

end Segment

/-! ## BGG data of any length -/

/-- BGG data on a complex shape: complexes `V`, `Ṽ` and maps `S i j : Ṽⁱ → Vʲ`, `d S = -S d̃`. -/
structure Data (R : Type*) [Ring R] {ι : Type*} (c : ComplexShape ι) (V Vt : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, AddCommGroup (Vt i)]
    [∀ i, Module R (Vt i)] where
  d : ∀ i j, V i →ₗ[R] V j
  dt : ∀ i j, Vt i →ₗ[R] Vt j
  S : ∀ i j, Vt i →ₗ[R] V j
  shape_d : ∀ i j, ¬ c.Rel i j → d i j = 0
  shape_dt : ∀ i j, ¬ c.Rel i j → dt i j = 0
  shape_S : ∀ i j, ¬ c.Rel i j → S i j = 0
  d_comp_d : ∀ i j k x, d j k (d i j x) = 0
  dt_comp_dt : ∀ i j k x, dt j k (dt i j x) = 0
  anticomm : ∀ i j k φ, d j k (S i j φ) = -S j k (dt i j φ)

namespace Data

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι} {V Vt : ι → Type v}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, AddCommGroup (Vt i)]
  [∀ i, Module R (Vt i)] (D : Data R c V Vt)

/-- The segment of `D` at `i → j → k`. -/
def segment (i j k : ι) : Segment R (V i) (V j) (V k) (Vt i) (Vt j) (Vt k) where
  d0 := D.d i j
  d1 := D.d j k
  dt0 := D.dt i j
  dt1 := D.dt j k
  S0 := D.S i j
  S1 := D.S j k
  d1_d0 := D.d_comp_d i j k
  dt1_dt0 := D.dt_comp_dt i j k
  anticomm := D.anticomm i j k

/-- The twisted differential `(σ, φ) ↦ (dσ - Sφ, d̃φ)` on `Vⁱ × Ṽⁱ`. -/
def twist (i j : ι) : V i × Vt i →ₗ[R] V j × Vt j :=
  (D.d i j ∘ₗ LinearMap.fst R (V i) (Vt i) - D.S i j ∘ₗ LinearMap.snd R (V i) (Vt i)).prod
    (D.dt i j ∘ₗ LinearMap.snd R (V i) (Vt i))

@[simp] theorem twist_apply (i j : ι) (x : V i × Vt i) :
    D.twist i j x = (D.d i j x.1 - D.S i j x.2, D.dt i j x.2) := rfl

theorem twist_eq_zero {i j : ι} (h : ¬ c.Rel i j) : D.twist i j = 0 := by
  ext x <;> simp [D.shape_d i j h, D.shape_S i j h, D.shape_dt i j h]

/-- The twisted differential squares to zero. [ArnoldHu2021], §5.1 -/
theorem twist_twist (i j k : ι) (x : V i × Vt i) : D.twist j k (D.twist i j x) = 0 := by
  simp [D.d_comp_d, D.dt_comp_dt, D.anticomm]

section Complex

/-- The twisted complex `(V × Ṽ, (σ, φ) ↦ (dσ - Sφ, d̃φ))` of `R`-modules. [ArnoldHu2021], (59) -/
def twistComplex : HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (V i × Vt i)
  d i j := ModuleCat.ofHom (D.twist i j)
  shape i j h := by rw [D.twist_eq_zero h]; rfl
  d_comp_d' i j k _ _ := ModuleCat.hom_ext (LinearMap.ext fun x => D.twist_twist i j k x)

end Complex

/-! ### Data on `ComplexShape.up α` from successive maps -/

section OfSucc

variable {α : Type*} [Add α] [One α] [DecidableEq α] {R : Type*} [Ring R]

/-- `f i : Xⁱ → Yⁱ⁺¹` transported along `i + 1 = j`, and `0` otherwise. -/
def succMap {X Y : α → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module R (Y i)] (f : ∀ i, X i →ₗ[R] Y (i + 1)) (i j : α) :
    X i →ₗ[R] Y j :=
  if h : i + 1 = j then h ▸ f i else 0

variable {X Y : α → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)]
  [∀ i, AddCommGroup (Y i)] [∀ i, Module R (Y i)] (f : ∀ i, X i →ₗ[R] Y (i + 1))

@[simp] theorem succMap_succ (i : α) : succMap f i (i + 1) = f i := by simp [succMap]

theorem succMap_of_ne {i j : α} (h : i + 1 ≠ j) : succMap f i j = 0 := by simp [succMap, h]

variable {V Vt : α → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  [∀ i, AddCommGroup (Vt i)] [∀ i, Module R (Vt i)]

/-- BGG data on `ComplexShape.up α` from successive maps `d i`, `d̃ i`, `S i`. -/
def ofSucc [IsRightCancelAdd α] (d : ∀ i, V i →ₗ[R] V (i + 1)) (dt : ∀ i, Vt i →ₗ[R] Vt (i + 1))
    (S : ∀ i, Vt i →ₗ[R] V (i + 1)) (d_comp_d : ∀ i x, d (i + 1) (d i x) = 0)
    (dt_comp_dt : ∀ i x, dt (i + 1) (dt i x) = 0)
    (anticomm : ∀ i φ, d (i + 1) (S i φ) = -S (i + 1) (dt i φ)) :
    Data R (ComplexShape.up α) V Vt where
  d := succMap d
  dt := succMap dt
  S := succMap S
  shape_d _ _ h := succMap_of_ne d h
  shape_dt _ _ h := succMap_of_ne dt h
  shape_S _ _ h := succMap_of_ne S h
  d_comp_d i j k x := by
    by_cases h : i + 1 = j
    · subst h
      by_cases h' : i + 1 + 1 = k
      · subst h'; simp [d_comp_d]
      · simp [succMap_of_ne d h']
    · simp [succMap_of_ne d h]
  dt_comp_dt i j k x := by
    by_cases h : i + 1 = j
    · subst h
      by_cases h' : i + 1 + 1 = k
      · subst h'; simp [dt_comp_dt]
      · simp [succMap_of_ne dt h']
    · simp [succMap_of_ne dt h]
  anticomm i j k φ := by
    by_cases h : i + 1 = j
    · subst h
      by_cases h' : i + 1 + 1 = k
      · subst h'; simp [anticomm]
      · simp [succMap_of_ne d h', succMap_of_ne S h']
    · simp [succMap_of_ne S h, succMap_of_ne dt h]

end OfSucc

end Data

end Feec.BGG
