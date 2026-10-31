module

public import Feec.ForMathlib.InnerProductSpace.MoorePenrose
public import Feec.HilbertComplex.BGG.Analytic
public import Feec.HilbertComplex.BGG.SumComplex

/-!
# The orthogonal model of the BGG complex and the cochain map (30) with Moore–Penrose inverses

For bounded BGG data on Hilbert spaces (`Feec.BGG.BoundedData`) on `ℤ`, [ArnoldHu2021], §3,
realize the BGG complex on the **output spaces** ((15), `BoundedData.Υ`)

  `Υⁱ = R(Sⁱ⁻¹)ᗮ ⊆ Vⁱ` (`i ≤ J`), `Υⁱ = N(Sⁱ) ⊆ Ṽⁱ` (`i > J`)

(here as `R(Sⁱ⁻¹)ᗮ × 0` and `0 × N(Sⁱ)` inside `Vⁱ × Ṽⁱ`), with the **output differentials**
((16), `BoundedData.orthDMap`)

  `𝒟ⁱ = P_{R(Sⁱ)ᗮ} dⁱ` (`i < J`), `𝒟ᴶ = d̃ᴶ (Sᴶ)⁻¹ dᴶ`, `𝒟ⁱ = d̃ⁱ` (`i > J`).

When `Sᴶ` is bijective this is a complex (`BoundedData.orthComplex`; `𝒟 𝒟 = 0` uses only that
the bounded `d`, `d̃`, `(Sᴶ)⁻¹` carry `R(S)` into `R(S)`, hence its closure `R(S)ᗮᗮ`). The map
`[(σ, φ)] ↦ P_{R(Sⁱ⁻¹)ᗮ} σ` up to `J`, `[(0, φ)] ↦ φ` after `J`, from the subquotient model
`Γ / Δ` (`Data.bgg`), is a cochain map (`BoundedData.toOrth`), an **isomorphism of complexes
when the ranges `R(Sⁱ⁻¹)`, `i ≤ J`, are closed** (`BoundedData.isIso_toOrth`; the quotient
`Vⁱ / R(Sⁱ⁻¹)` is then `R(Sⁱ⁻¹)ᗮ`).

With the **Moore–Penrose inverses** `tⁱ⁺¹ = (Sⁱ)†` of the connecting maps (`BoundedData.mpInv`,
[ArnoldHu2021], (29)), right inverses from `J` on (`BoundedData.injSurjWith_mpInv`), the
projection `1 - tⁱ⁺¹ Sⁱ` of `Data.kerProj` is the orthogonal projection `P_{N(Sⁱ)}`
(`BoundedData.kerProj_mpInv`), and the cochain map (30) of `Data.bggSumMap` composed with
`toOrth` is the map of [ArnoldHu2021], Theorem 7, in its stated orthogonal form
(`BoundedData.orthSumMap`, `orthSumMap_of_le`, `orthSumMap_of_gt`):

  `𝒦ⁱ(ω, μ) = P_{R(Sⁱ⁻¹)ᗮ}(ω + Kμ)` (`i ≤ J`),
  `𝒦ⁱ(ω, μ) = P_{N(Sⁱ)}[d̃ⁱ⁻¹ tⁱ ω + (I + d̃ⁱ⁻¹ tⁱ K)μ]` (`i > J`),

for null-homotopic connecting maps `S = dK - Kd̃` ((28)). Under (23) (`Sⁱ` one-to-one for
`i ≤ J`, onto for `i ≥ J`) and closed ranges up to `J`, **`𝒦` is a quasi-isomorphism from the
sum complex to the output complex** (`BoundedData.quasiIso_orthSumMap`, Theorem 7, an instance of
`Data.quasiIso_of_Γι_comp` through `Data.quasiIso_bggSumMap`), and it carries cohomology
representatives `H × H̃` of the rows to cohomology representatives of the output complex
(`BoundedData.orth_represents`, Corollary 1, (31)). In [ArnoldHu2021] the connecting maps are
`id ⊗ s` with `s` between finite-dimensional spaces, so all their ranges are closed.

## Main definitions

* `BoundedData.SL`, `BoundedData.mpInv`: the connecting maps as bounded operators and their
  Moore–Penrose inverses.
* `BoundedData.Υ`, `BoundedData.orthDMap`, `BoundedData.orthComplex`: the output complex
  (15)–(16).
* `BoundedData.toOrth`: the cochain map from `Γ / Δ` to the output complex.
* `BoundedData.orthSumMap`: the cochain map (30).
* `BoundedData.altShift`: `Data.altShift` as bounded data.

## Main results

* `BoundedData.injSurjWith_mpInv`, `BoundedData.kerProj_mpInv`.
* `BoundedData.isIso_toOrth`.
* `BoundedData.orthSumMap_of_le`, `BoundedData.orthSumMap_of_gt` ((30)),
  **`BoundedData.quasiIso_orthSumMap`** (Theorem 7), `BoundedData.orth_represents` (Corollary 1).
* `BoundedData.altShift_quasiIso_orthSumMap`: non-vacuity, with nonzero `d`, `d̃` and `S`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3 ((15)–(16) the output
  complex, (23), (28), (29) the Moore–Penrose inverse, (30), Theorem 7, Corollary 1, (31))

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Feec.BGG.BoundedData

variable {𝕜 : Type*} [RCLike 𝕜] {V Vt : ℤ → Type u}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
  [∀ i, NormedAddCommGroup (Vt i)] [∀ i, InnerProductSpace 𝕜 (Vt i)]
  [∀ i, CompleteSpace (Vt i)] (D : BoundedData 𝕜 (ComplexShape.up ℤ) V Vt)

/-! ### The Moore–Penrose inverses of the connecting maps -/

/-- The connecting map `S : Ṽⁱ → Vʲ` as a bounded operator. -/
def SL (i j : ℤ) : Vt i →L[𝕜] V j := ⟨D.S i j, D.continuous_S i j⟩

/-- The differential `d : Vⁱ → Vʲ` as a bounded operator. -/
def dL (i j : ℤ) : V i →L[𝕜] V j := ⟨D.d i j, D.continuous_d i j⟩

/-- The differential `d̃ : Ṽⁱ → Ṽʲ` as a bounded operator. -/
def dtL (i j : ℤ) : Vt i →L[𝕜] Vt j := ⟨D.dt i j, D.continuous_dt i j⟩

/-- **The Moore–Penrose inverses of the connecting maps**, `tʲ = (S : Ṽⁱ → Vʲ)†`
([ArnoldHu2021], (29)). -/
def mpInv (i j : ℤ) : V j →ₗ[𝕜] Vt i := (D.SL i j).moorePenrose

variable {D} {J : ℤ}

omit [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)] in
theorem hasOrthogonalProjection_range {i j : ℤ} (hS : Function.Surjective (D.S i j)) :
    (D.SL i j).range.HasOrthogonalProjection := by
  rw [show (D.SL i j).range = ⊤ from LinearMap.range_eq_top.2 hS]
  infer_instance

/-- `S t = 1` where `S` is onto. -/
theorem S_mpInv {i j : ℤ} (hS : Function.Surjective (D.S i j)) (v : V j) :
    D.S i j (D.mpInv i j v) = v :=
  have := hasOrthogonalProjection_range hS
  (D.SL i j).apply_moorePenrose_of_surjective hS v

/-- `t S = 1` where `S` is bijective. -/
theorem mpInv_S {i j : ℤ} (hS : Function.Bijective (D.S i j)) (φ : Vt i) :
    D.mpInv i j (D.S i j φ) = φ :=
  have := hasOrthogonalProjection_range hS.2
  (D.SL i j).moorePenrose_apply_of_injective hS.1 φ

/-- **The Moore–Penrose inverses are right inverses from `J` on** under the condition (23)
of [ArnoldHu2021] (`Sⁱ` one-to-one for `i ≤ J`, onto for `i ≥ J`). -/
theorem injSurjWith_mpInv (h : D.InjSurj J) (hJ : Function.Injective (D.S J (J + 1))) :
    D.InjSurjWith J D.mpInv where
  injective i hi := by
    rcases hi.lt_or_eq with hi | rfl
    · exact h.1 i hi
    · exact hJ
  S_t i j hij hi v := by
    subst hij
    exact S_mpInv (h.2 i hi) v

/-- **With the Moore–Penrose inverse, `1 - tⁱ⁺¹ Sⁱ` is the orthogonal projection `P_{N(Sⁱ)}`**
where `Sⁱ` is onto. [ArnoldHu2021], (29) -/
theorem kerProj_mpInv {i : ℤ} (hS : Function.Surjective (D.S i (i + 1))) (φ : Vt i) :
    D.kerProj D.mpInv i φ = (D.SL i (i + 1)).ker.starProjection φ :=
  have := hasOrthogonalProjection_range hS
  (D.SL i (i + 1)).sub_moorePenrose_apply φ

/-! ### The output complex (15)–(16) -/

variable (D J)

/-- **The output spaces** ([ArnoldHu2021], (15)) inside `Vⁱ × Ṽⁱ`: `R(Sⁱ⁻¹)ᗮ × 0` up to `J`,
`0 × N(Sⁱ)` after `J`. -/
def Υ (i : ℤ) : Submodule 𝕜 (V i × Vt i) :=
  if i ≤ J then (D.SL (i - 1) i).rangeᗮ.prod ⊥ else (⊥ : Submodule 𝕜 (V i)).prod (D.SL i (i + 1)).ker

/-- **The output differentials** ([ArnoldHu2021], (16)) on `Vⁱ × Ṽⁱ`: `σ ↦ P_{R(Sⁱ)ᗮ} dσ`
before `J`, `σ ↦ d̃ (Sᴶ)⁻¹ dσ` at `J` (`(Sᴶ)† = (Sᴶ)⁻¹` when `Sᴶ` is bijective), `φ ↦ d̃φ`
after `J`. -/
def orthDMap (i : ℤ) : V i × Vt i →ₗ[𝕜] V (i + 1) × Vt (i + 1) :=
  if i < J then
    (((D.SL (i + 1 - 1) (i + 1)).rangeᗮ.starProjection : V (i + 1) →ₗ[𝕜] V (i + 1)) ∘ₗ
      D.d i (i + 1) ∘ₗ LinearMap.fst 𝕜 _ _).prod 0
  else if i = J then
    (0 : V i × Vt i →ₗ[𝕜] V (i + 1)).prod
      (D.dt i (i + 1) ∘ₗ D.mpInv i (i + 1) ∘ₗ D.d i (i + 1) ∘ₗ LinearMap.fst 𝕜 _ _)
  else (0 : V i × Vt i →ₗ[𝕜] V (i + 1)).prod (D.dt i (i + 1) ∘ₗ LinearMap.snd 𝕜 _ _)

variable {D J}

omit [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)] in
theorem mem_Υ_of_le {i : ℤ} (hi : i ≤ J) {x : V i × Vt i} :
    x ∈ D.Υ J i ↔ x.1 ∈ (D.SL (i - 1) i).rangeᗮ ∧ x.2 = 0 := by
  simp [Υ, hi]

omit [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)] in
theorem mem_Υ_of_gt {i : ℤ} (hi : J < i) {x : V i × Vt i} :
    x ∈ D.Υ J i ↔ x.1 = 0 ∧ D.S i (i + 1) x.2 = 0 := by
  simp [Υ, not_le.2 hi]
  exact fun _ => Iff.rfl

theorem orthDMap_of_lt {i : ℤ} (hi : i < J) (x : V i × Vt i) :
    D.orthDMap J i x = ((D.SL (i + 1 - 1) (i + 1)).rangeᗮ.starProjection (D.d i (i + 1) x.1), 0) := by
  simp [orthDMap, hi]

theorem orthDMap_of_eq (x : V J × Vt J) :
    D.orthDMap J J x = (0, D.dt J (J + 1) (D.mpInv J (J + 1) (D.d J (J + 1) x.1))) := by
  simp [orthDMap]

theorem orthDMap_of_gt {i : ℤ} (hi : J < i) (x : V i × Vt i) :
    D.orthDMap J i x = (0, D.dt i (i + 1) x.2) := by
  simp [orthDMap, not_lt.2 hi.le, hi.ne']

omit [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)] in
/-- `R(S : Ṽᵃ → Vᵏ) ⊆ R(Sᵏ⁻¹)` for `a + 1 = k`. -/
theorem S_mem_range {a k : ℤ} (h : a + 1 = k) (ψ : Vt a) : D.S a k ψ ∈ (D.SL (k - 1) k).range := by
  subst h
  rw [add_sub_cancel_right]
  exact ⟨ψ, rfl⟩

omit [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)] in
/-- `S d̃ φ = -d S φ`. -/
theorem S_dt (i j k : ℤ) (φ : Vt i) : D.S j k (D.dt i j φ) = -D.d j k (D.S i j φ) := by
  rw [D.anticomm, neg_neg]

omit [∀ i, CompleteSpace (Vt i)] in
/-- **`P_{R(Sⁱ)ᗮ} d P_{R(Sⁱ⁻¹)ᗮ} = P_{R(Sⁱ)ᗮ} d`**: `d` carries `R(Sⁱ⁻¹)` into `R(Sⁱ)`. -/
theorem starProjection_d_starProjection (i : ℤ) (x : V i) :
    (D.SL (i + 1 - 1) (i + 1)).rangeᗮ.starProjection
        (D.d i (i + 1) ((D.SL (i - 1) i).rangeᗮ.starProjection x)) =
      (D.SL (i + 1 - 1) (i + 1)).rangeᗮ.starProjection (D.d i (i + 1) x) :=
  (D.dL i (i + 1)).starProjection_orthogonal_apply_starProjection_orthogonal (by
    rintro _ ⟨ψ, rfl⟩
    change D.d i (i + 1) (D.S (i - 1) i ψ) ∈ _
    rw [D.anticomm, ← map_neg]
    exact S_mem_range rfl _) x

/-- **`d̃ (Sᴶ)⁻¹ d P_{R(Sᴶ⁻¹)ᗮ} = d̃ (Sᴶ)⁻¹ d`**: `d̃ (Sᴶ)⁻¹ d` vanishes on `R(Sᴶ⁻¹)`. -/
theorem dt_mpInv_d_starProjection (hJ : Function.Bijective (D.S J (J + 1))) (x : V J) :
    D.dt J (J + 1) (D.mpInv J (J + 1) (D.d J (J + 1) ((D.SL (J - 1) J).rangeᗮ.starProjection x))) =
      D.dt J (J + 1) (D.mpInv J (J + 1) (D.d J (J + 1) x)) := by
  have := hasOrthogonalProjection_range hJ.2
  let g : V J →L[𝕜] Vt (J + 1) := D.dtL J (J + 1) ∘L (D.SL J (J + 1)).moorePenrose ∘L D.dL J (J + 1)
  have hg : g ((D.SL (J - 1) J).rangeᗮ.starProjection x) = g x := by
    rw [← sub_eq_zero, ← map_sub, ← neg_sub, map_neg, neg_eq_zero]
    refine g.apply_eq_zero_of_mem_orthogonal_orthogonal (A := (D.SL (J - 1) J).range) ?_
      ((D.SL (J - 1) J).rangeᗮ.sub_starProjection_mem_orthogonal x)
    rintro _ ⟨ψ, rfl⟩
    change D.dt J (J + 1) (D.mpInv J (J + 1) (D.d J (J + 1) (D.S (J - 1) J ψ))) = 0
    rw [D.anticomm, map_neg, mpInv_S hJ, map_neg, D.dt_comp_dt, neg_zero]
  exact hg

/-- `𝒟` maps `Υⁱ` to `Υⁱ⁺¹`. -/
theorem orthDMap_mem (hJ : Function.Bijective (D.S J (J + 1))) {i : ℤ} {x : V i × Vt i}
    (hx : x ∈ D.Υ J i) : D.orthDMap J i x ∈ D.Υ J (i + 1) := by
  rcases lt_trichotomy i J with hi | rfl | hi
  · rw [orthDMap_of_lt hi, mem_Υ_of_le (by omega)]
    exact ⟨Submodule.starProjection_apply_mem _ _, rfl⟩
  · rw [orthDMap_of_eq, mem_Υ_of_gt (by omega)]
    refine ⟨rfl, ?_⟩
    change D.S (i + 1) (i + 1 + 1) (D.dt i (i + 1) _) = 0
    rw [S_dt, S_mpInv hJ.2, D.d_comp_d, neg_zero]
  · rw [orthDMap_of_gt hi, mem_Υ_of_gt (by omega)]
    refine ⟨rfl, ?_⟩
    change D.S (i + 1) (i + 1 + 1) (D.dt i (i + 1) x.2) = 0
    rw [S_dt, ((mem_Υ_of_gt hi).1 hx).2, map_zero, neg_zero]

/-- **`𝒟 𝒟 = 0` on the output spaces.** -/
theorem orthDMap_orthDMap (hJ : Function.Bijective (D.S J (J + 1))) {i : ℤ} {x : V i × Vt i}
    (hx : x ∈ D.Υ J i) : D.orthDMap J (i + 1) (D.orthDMap J i x) = 0 := by
  rcases lt_trichotomy (i + 1) J with hi | hi | hi
  · rw [orthDMap_of_lt (i := i) (by omega), orthDMap_of_lt hi, starProjection_d_starProjection,
      D.d_comp_d, map_zero]
    rfl
  · obtain rfl := hi
    rw [orthDMap_of_lt (i := i) (by omega), orthDMap_of_eq, dt_mpInv_d_starProjection hJ, D.d_comp_d,
      map_zero, map_zero]
    rfl
  · rw [orthDMap_of_gt hi]
    rcases (by omega : i = J ∨ J < i) with rfl | hi'
    · rw [orthDMap_of_eq, D.dt_comp_dt]
      rfl
    · rw [orthDMap_of_gt hi', D.dt_comp_dt]
      rfl

variable (D J) in
/-- **The output complex** of [ArnoldHu2021], (14)–(16): the spaces `Υⁱ` with the
differentials `𝒟ⁱ`, for `Sᴶ` bijective. -/
def orthComplex (hJ : Function.Bijective (D.S J (J + 1))) : CochainComplex (ModuleCat.{u} 𝕜) ℤ :=
  CochainComplex.of (fun i => ModuleCat.of 𝕜 (D.Υ J i))
    (fun i => ModuleCat.ofHom ((D.orthDMap J i ∘ₗ (D.Υ J i).subtype).codRestrict _
      fun x => orthDMap_mem hJ x.2))
    fun _ => ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (orthDMap_orthDMap hJ x.2))

theorem coe_orthComplex_d (hJ : Function.Bijective (D.S J (J + 1))) (i : ℤ) (x : D.Υ J i) :
    Subtype.val (((D.orthComplex J hJ).d i (i + 1)).hom x) = D.orthDMap J i x := by
  simp only [orthComplex, CochainComplex.of_d]
  rfl

/-! ### From the subquotient model to the output complex -/

variable (D J) in
/-- The map `(σ, φ) ↦ (P_{R(Sⁱ⁻¹)ᗮ} σ, 0)` up to `J`, the identity after `J`. -/
def toOrthMap (i : ℤ) : V i × Vt i →ₗ[𝕜] V i × Vt i :=
  if i ≤ J then
    (((D.SL (i - 1) i).rangeᗮ.starProjection : V i →ₗ[𝕜] V i) ∘ₗ LinearMap.fst 𝕜 _ _).prod 0
  else LinearMap.id

omit [∀ i, CompleteSpace (Vt i)] in
theorem toOrthMap_of_le {i : ℤ} (hi : i ≤ J) (x : V i × Vt i) :
    D.toOrthMap J i x = ((D.SL (i - 1) i).rangeᗮ.starProjection x.1, 0) := by
  simp [toOrthMap, hi]

omit [∀ i, CompleteSpace (Vt i)] in
theorem toOrthMap_of_gt {i : ℤ} (hi : J < i) (x : V i × Vt i) : D.toOrthMap J i x = x := by
  simp [toOrthMap, not_le.2 hi]

omit [∀ i, CompleteSpace (Vt i)] in
theorem toOrthMap_mem {i : ℤ} {x : V i × Vt i} (hx : x ∈ D.Γ (J < ·) i) :
    D.toOrthMap J i x ∈ D.Υ J i := by
  rcases le_or_gt i J with hi | hi
  · rw [toOrthMap_of_le hi, mem_Υ_of_le hi]
    exact ⟨Submodule.starProjection_apply_mem _ _, rfl⟩
  · rw [toOrthMap_of_gt hi, mem_Υ_of_gt hi]
    exact (D.mem_bgg_Γ_of_gt hi).1 hx

omit [∀ i, CompleteSpace (Vt i)] in
theorem toOrthMap_eq_zero {i : ℤ} {x : V i × Vt i} (hx : x ∈ D.Δ (· < J) i) :
    D.toOrthMap J i x = 0 := by
  rcases le_or_gt i J with hi | hi
  · obtain ⟨φ, ψ, -, rfl⟩ := (D.mem_bgg_Δ_of_le hi).1 hx
    rw [toOrthMap_of_le hi, (Submodule.starProjection_apply_eq_zero_iff _).2
      (Submodule.le_orthogonal_orthogonal (D.SL (i - 1) i).range ⟨-ψ, by simp [SL]⟩)]
    rfl
  · rw [D.bgg_Δ_of_gt hi, Submodule.mem_bot] at hx
    rw [hx, map_zero]

/-- `Ψ T = 𝒟 Ψ` on `Γ`. -/
theorem toOrthMap_twist (hJ : Function.Bijective (D.S J (J + 1))) {i : ℤ} {x : V i × Vt i}
    (hx : x ∈ D.Γ (J < ·) i) :
    D.toOrthMap J (i + 1) (D.twist i (i + 1) x) = D.orthDMap J i (D.toOrthMap J i x) := by
  obtain ⟨σ, φ⟩ := x
  rcases lt_trichotomy i J with hi | rfl | hi
  · rw [toOrthMap_of_le (by omega), toOrthMap_of_le hi.le, orthDMap_of_lt hi,
      starProjection_d_starProjection, Data.twist_apply, map_sub,
      (Submodule.starProjection_apply_eq_zero_iff _).2
        (Submodule.le_orthogonal_orthogonal _ (S_mem_range rfl φ)), sub_zero]
  · have hσ := (D.mem_bgg_Γ_self).1 hx
    rw [toOrthMap_of_gt (by omega), toOrthMap_of_le le_rfl, orthDMap_of_eq,
      dt_mpInv_d_starProjection hJ, Data.twist_apply]
    simp only at hσ ⊢
    rw [hσ, sub_self, mpInv_S hJ]
  · obtain ⟨h1, h2⟩ := (D.mem_bgg_Γ_of_gt hi).1 hx
    simp only at h1 h2
    rw [toOrthMap_of_gt (by omega), toOrthMap_of_gt hi, orthDMap_of_gt hi, Data.twist_apply, h1, h2,
      map_zero, sub_zero]

variable (D J) in
/-- **The cochain map from the subquotient model `Γ / Δ` to the output complex**:
`[(σ, φ)] ↦ P_{R(Sⁱ⁻¹)ᗮ} σ` up to `J`, `[(0, φ)] ↦ φ` after `J`. -/
def toOrth (hJ : Function.Bijective (D.S J (J + 1))) : D.bgg J ⟶ D.orthComplex J hJ where
  f i := ModuleCat.ofHom (X := (D.bgg J).X i) (Y := (D.orthComplex J hJ).X i)
    ((((D.Δ (· < J) i).comap (D.Γ (J < ·) i).subtype).liftQ ((D.toOrthMap J i ∘ₗ (D.Γ (J < ·) i).subtype).codRestrict (D.Υ J i)
      fun x => toOrthMap_mem x.2) fun x hx => Subtype.ext (toOrthMap_eq_zero hx)))
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => Subtype.ext ?_))
    exact (coe_orthComplex_d hJ i _).trans (toOrthMap_twist hJ x.2).symm

theorem coe_toOrth_mk (hJ : Function.Bijective (D.S J (J + 1))) (i : ℤ) (x : D.Γ (J < ·) i) :
    Subtype.val (((D.toOrth J hJ).f i).hom (Submodule.Quotient.mk x)) = D.toOrthMap J i x := rfl

/-- **`toOrth` is bijective where the ranges `R(Sⁱ⁻¹)`, `i ≤ J`, are closed**: up to `J` it is
`Vⁱ / R(Sⁱ⁻¹) ≅ R(Sⁱ⁻¹)ᗮ` (`Data.bggXEquivOfLt`, `Data.bggXEquivOfBijective`), after `J`
`Γⁱ = Υⁱ`. -/
theorem bijective_toOrth (hJ : Function.Bijective (D.S J (J + 1)))
    (hR : ∀ i ≤ J, IsClosed ((D.SL (i - 1) i).range : Set (V i))) (i : ℤ) :
    Function.Bijective ((D.toOrth J hJ).f i).hom := by
  rcases le_or_gt i J with hi | hi
  · have := (hR i hi).completeSpace_coe
    let R : Submodule 𝕜 (V i) := LinearMap.range (D.S (i - 1) i)
    let g : V i ⧸ R →ₗ[𝕜] D.Υ J i := R.liftQ
      ((((D.SL (i - 1) i).rangeᗮ.starProjection : V i →ₗ[𝕜] V i).prod 0).codRestrict _
        fun σ => (mem_Υ_of_le hi).2 ⟨Submodule.starProjection_apply_mem _ _, rfl⟩)
      fun σ hσ => Subtype.ext (Prod.ext ((Submodule.starProjection_apply_eq_zero_iff _).2
        (Submodule.le_orthogonal_orthogonal _ hσ)) rfl)
    have hg : Function.Bijective g := by
      refine ⟨LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ fun σ h0 => ?_),
        fun y => ?_⟩
      · have h0 := congrArg (fun y : D.Υ J i => (y : V i × Vt i).1) (LinearMap.mem_ker.1 h0)
        have := (Submodule.starProjection_apply_eq_zero_iff _).1 h0
        rwa [Submodule.orthogonal_orthogonal] at this
      · obtain ⟨⟨σ, φ⟩, hy⟩ := y
        obtain ⟨hσ, rfl⟩ := (mem_Υ_of_le hi).1 hy
        exact ⟨Submodule.Quotient.mk σ, Subtype.ext (Prod.ext
          (Submodule.starProjection_eq_self_iff.2 hσ) rfl)⟩
    rcases hi.lt_or_eq with hi' | rfl
    · have e : ∀ q, ((D.toOrth J hJ).f i).hom q = g (D.bggXEquivOfLt hi' q) := fun q => by
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
        exact Subtype.ext ((toOrthMap_of_le hi (Subtype.val x)).trans rfl)
      rw [show ⇑((D.toOrth J hJ).f i).hom = g ∘ D.bggXEquivOfLt hi' from funext e]
      exact hg.comp (D.bggXEquivOfLt hi').bijective
    · have e : ∀ q, ((D.toOrth i hJ).f i).hom q = g (D.bggXEquivOfBijective hJ q) := fun q => by
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
        exact Subtype.ext ((toOrthMap_of_le le_rfl (Subtype.val x)).trans rfl)
      rw [show ⇑((D.toOrth i hJ).f i).hom = g ∘ D.bggXEquivOfBijective hJ from funext e]
      exact hg.comp (D.bggXEquivOfBijective hJ).bijective
  · let e := D.derivedXEquiv (J < ·) (· < J) (D.bgg_Δ_of_gt hi)
    have he : ∀ q, Subtype.val (((D.toOrth J hJ).f i).hom q) = (e q : V i × Vt i) := fun q => by
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
      exact (toOrthMap_of_gt hi (Subtype.val x)).trans
        (congrArg Subtype.val (Submodule.quotEquivOfEqBot_apply_mk _ _ x)).symm
    refine ⟨fun q₁ q₂ hq => e.injective (Subtype.ext ?_), fun y => ?_⟩
    · rw [← he, ← he, hq]
    · refine ⟨e.symm ⟨Subtype.val y, (D.mem_bgg_Γ_of_gt hi).2
        ((mem_Υ_of_gt hi).1 (Subtype.property y))⟩, Subtype.ext ?_⟩
      exact (he _).trans (congrArg Subtype.val (e.apply_symm_apply _))

/-- **The subquotient model and the output complex are isomorphic** where the ranges
`R(Sⁱ⁻¹)`, `i ≤ J`, are closed. -/
theorem isIso_toOrth (hJ : Function.Bijective (D.S J (J + 1)))
    (hR : ∀ i ≤ J, IsClosed ((D.SL (i - 1) i).range : Set (V i))) : IsIso (D.toOrth J hJ) := by
  have : ∀ i, IsIso ((D.toOrth J hJ).f i) := fun i =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_toOrth hJ hR i)
  exact HomologicalComplex.Hom.isIso_of_components _

/-! ### The cochain map (30) -/

variable {K : ∀ i, Vt i →ₗ[𝕜] V i} (hK : D.IsNullHomotopy K) (h : D.InjSurj J)
  (hJ : Function.Injective (D.S J (J + 1)))

omit [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)] in
/-- Under (23), `Sᴶ` is bijective. -/
theorem bijective_S (h : D.InjSurj J) (hJ : Function.Injective (D.S J (J + 1))) :
    Function.Bijective (D.S J (J + 1)) :=
  ⟨hJ, h.2 J le_rfl⟩

variable (D J) in
/-- **The cochain map (30) of Theorem 7** in the orthogonal form of [ArnoldHu2021], from the
sum complex to the output complex: `Data.bggSumMap` with the Moore–Penrose inverses, followed by
`toOrth`. -/
def orthSumMap (h : D.InjSurj J) (hJ : Function.Injective (D.S J (J + 1))) {K : ∀ i, Vt i →ₗ[𝕜] V i}
    (hK : D.IsNullHomotopy K) : D.sumComplex ⟶ D.orthComplex J (bijective_S h hJ) :=
  D.bggSumMap D.mpInv hK (injSurjWith_mpInv h hJ) ≫ D.toOrth J _

theorem coe_orthSumMap_apply (i : ℤ) (x : V i × Vt i) :
    Subtype.val (((D.orthSumMap J h hJ hK).f i).hom x) =
      D.toOrthMap J i (D.bggProjMap J D.mpInv i (x.1 + K i x.2, x.2)) := by
  rfl

/-- **(30) up to `J`**: `𝒦ⁱ(ω, μ) = P_{R(Sⁱ⁻¹)ᗮ}(ω + Kμ)`. [ArnoldHu2021], (30) -/
theorem orthSumMap_of_le {i : ℤ} (hi : i ≤ J) (x : V i × Vt i) :
    Subtype.val (((D.orthSumMap J h hJ hK).f i).hom x) =
      ((D.SL (i - 1) i).rangeᗮ.starProjection (x.1 + K i x.2), 0) := by
  rw [coe_orthSumMap_apply, toOrthMap_of_le hi]
  rcases hi.lt_or_eq with hi' | rfl
  · rw [Data.bggProjMap_of_lt hi']
  · rw [Data.bggProjMap_of_eq rfl]

/-- **(30) after `J`**: `𝒦ⁱ(ω, μ) = P_{N(Sⁱ)}[d̃ tⁱ ω + (I + d̃ tⁱ K)μ]` with the Moore–Penrose
inverse `tⁱ = (Sⁱ⁻¹)†`. [ArnoldHu2021], (30) -/
theorem orthSumMap_of_gt {i : ℤ} (hi : J < i) (x : V i × Vt i) :
    Subtype.val (((D.orthSumMap J h hJ hK).f i).hom x) =
      (0, (D.SL i (i + 1)).ker.starProjection (D.dt (i - 1) i (D.mpInv (i - 1) i x.1) +
        (x.2 + D.dt (i - 1) i (D.mpInv (i - 1) i (K i x.2))))) := by
  rw [coe_orthSumMap_apply, toOrthMap_of_gt hi, Data.bggProjMap_of_gt hi,
    kerProj_mpInv (h.2 i hi.le)]
  congr 2
  rw [map_add, map_add]
  abel

/-- **The cochain map (30) induces an isomorphism on cohomology** ([ArnoldHu2021], Theorem 7),
under (23) with the ranges `R(Sⁱ⁻¹)`, `i ≤ J`, closed: an instance of `Data.quasiIso_of_Γι_comp`
(`Data.quasiIso_bggSumMap`) composed with the isomorphism `toOrth`. -/
theorem quasiIso_orthSumMap (hR : ∀ i ≤ J, IsClosed ((D.SL (i - 1) i).range : Set (V i))) :
    QuasiIso (D.orthSumMap J h hJ hK) := by
  have := Data.quasiIso_bggSumMap (injSurjWith_mpInv h hJ) hK
  have := isIso_toOrth (bijective_S h hJ) hR
  unfold orthSumMap
  infer_instance

/-- **Cohomology representatives of the output complex** ([ArnoldHu2021], Corollary 1, (31)): if
`H`, `H̃` represent the cohomology of the rows at `i`, then `𝒦(H × H̃)` represents the cohomology of
the output complex, `N(𝒟ⁱ) = R(𝒟ⁱ⁻¹) ⊕ 𝒦(H × H̃)`. -/
theorem orth_represents (hR : ∀ i ≤ J, IsClosed ((D.SL (i - 1) i).range : Set (V i))) {i : ℤ}
    {H : Submodule 𝕜 (V i)} {Ht : Submodule 𝕜 (Vt i)} (hH : D.rowTop.Represents i H)
    (hHt : D.rowBot.Represents i Ht) :
    (D.orthComplex J (bijective_S h hJ)).Represents i
      ((H.prod Ht).map ((D.orthSumMap J h hJ hK).f i).hom) :=
  have := quasiIso_orthSumMap hK h hJ hR
  (Data.represents_sumComplex hH hHt).map _

/-! ### Non-vacuity -/

variable (𝕜) in
/-- `Data.altShift` on `𝕜` (`dⁱ = id` for even `i`, `d̃ⁱ = -dⁱ⁺¹`, `Sⁱ = id`), as bounded
data. -/
def altShift : BoundedData 𝕜 (ComplexShape.up ℤ) (fun _ => 𝕜) (fun _ => 𝕜) where
  toData := Data.altShift 𝕜
  continuous_d _ _ := LinearMap.continuous_of_finiteDimensional _
  continuous_dt _ _ := LinearMap.continuous_of_finiteDimensional _
  continuous_S _ _ := LinearMap.continuous_of_finiteDimensional _

variable (𝕜) in
/-- **Non-vacuity of the orthogonal Theorem 7**: the cochain map (30) of `altShift` (nonzero `d`,
`d̃` and `S`) is a quasi-isomorphism at every `J`. -/
theorem altShift_quasiIso_orthSumMap (J : ℤ) :
    QuasiIso ((altShift 𝕜).orthSumMap J (Data.altShift_injSurjWith 𝕜 J).injSurj
      ((Data.altShift_injSurjWith 𝕜 J).injective J le_rfl) (Data.altShift_isNullHomotopy 𝕜)) :=
  quasiIso_orthSumMap _ _ _ fun _ _ => Submodule.closed_of_finiteDimensional _

end Feec.BGG.BoundedData
