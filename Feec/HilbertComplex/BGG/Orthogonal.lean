module

public import Feec.ForMathlib.InnerProductSpace.MoorePenrose
public import Feec.ForMathlib.InnerProductSpace.OrthogonalClosure
public import Feec.HilbertComplex.BGG.Analytic
public import Feec.HilbertComplex.BGG.SumComplex

/-!
# The orthogonal model of the BGG complex and the cochain map (30) with Moore–Penrose inverses

For bounded BGG data on `ℤ`, the output complex of [ArnoldHu2021], (24)–(26), on the spaces
`R(Sⁱ⁻¹)ᗮ` and `N(Sⁱ)`, is isomorphic to the subquotient model when the ranges `R(Sⁱ⁻¹)`, `i ≤ J`,
are closed, and with the Moore–Penrose inverses of the connecting maps the cochain map (30) is a
quasi-isomorphism onto it ([ArnoldHu2021], Theorem 7).

## Main results

* `BoundedData.isIso_toOrth`: the two models are isomorphic.
* `BoundedData.quasiIso_orthSumMap`: (30) is a quasi-isomorphism.
* `BoundedData.orth_represents`: cohomology representatives of the output complex.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3

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

/-- The Moore–Penrose inverses `tʲ = (S : Ṽⁱ → Vʲ)†` of the connecting maps. [ArnoldHu2021], (29) -/
def mpInv (i j : ℤ) : V j →ₗ[𝕜] Vt i := (D.SL i j).moorePenrose

variable {D} {J : ℤ}

omit [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)] in
theorem hasOrthogonalProjection_range_of_surjective {i j : ℤ} (hS : Function.Surjective (D.S i j)) :
    (D.SL i j).range.HasOrthogonalProjection := by
  rw [show (D.SL i j).range = ⊤ from LinearMap.range_eq_top.2 hS]
  infer_instance

theorem S_mpInv {i j : ℤ} (hS : Function.Surjective (D.S i j)) (v : V j) :
    D.S i j (D.mpInv i j v) = v :=
  have := hasOrthogonalProjection_range_of_surjective hS
  (D.SL i j).apply_moorePenrose_of_surjective hS v

theorem mpInv_S {i j : ℤ} (hS : Function.Bijective (D.S i j)) (φ : Vt i) :
    D.mpInv i j (D.S i j φ) = φ :=
  have := hasOrthogonalProjection_range_of_surjective hS.2
  (D.SL i j).moorePenrose_apply_of_injective hS.1 φ

theorem injSurjWith_mpInv (hinj : ∀ i ≤ J, Function.Injective (D.S i (i + 1)))
    (hsurj : ∀ i, J ≤ i → Function.Surjective (D.S i (i + 1))) : D.InjSurjWith J D.mpInv where
  injective := hinj
  S_t i j hij hi v := by
    subst hij
    exact S_mpInv (hsurj i hi) v

theorem kerProj_mpInv {i : ℤ} (hS : Function.Surjective (D.S i (i + 1))) (φ : Vt i) :
    D.kerProj D.mpInv i φ = (D.SL i (i + 1)).ker.starProjection φ :=
  have := hasOrthogonalProjection_range_of_surjective hS
  (D.SL i (i + 1)).sub_moorePenrose_apply φ

/-! ### The output complex (24)–(26) -/

variable (D J)

/-- The output spaces `R(Sⁱ⁻¹)ᗮ × 0` up to `J` and `0 × N(Sⁱ)` after `J`. [ArnoldHu2021], (25) -/
def Υ (i : ℤ) : Submodule 𝕜 (V i × Vt i) :=
  if i ≤ J then (D.SL (i - 1) i).rangeᗮ.prod ⊥ else (⊥ : Submodule 𝕜 (V i)).prod (D.SL i (i + 1)).ker

/-- The output differentials `P_{R(Sⁱ)ᗮ} d`, `d̃ (Sᴶ)† d` and `d̃`. [ArnoldHu2021], (26) -/
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
theorem S_mem_range {a k : ℤ} (h : a + 1 = k) (ψ : Vt a) : D.S a k ψ ∈ (D.SL (k - 1) k).range := by
  subst h
  rw [add_sub_cancel_right]
  exact ⟨ψ, rfl⟩

omit [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)] in
theorem S_dt (i j k : ℤ) (φ : Vt i) : D.S j k (D.dt i j φ) = -D.d j k (D.S i j φ) := by
  rw [D.anticomm, neg_neg]

omit [∀ i, CompleteSpace (Vt i)] in
theorem starProjection_d_starProjection (i : ℤ) (x : V i) :
    (D.SL (i + 1 - 1) (i + 1)).rangeᗮ.starProjection
        (D.d i (i + 1) ((D.SL (i - 1) i).rangeᗮ.starProjection x)) =
      (D.SL (i + 1 - 1) (i + 1)).rangeᗮ.starProjection (D.d i (i + 1) x) :=
  (D.dL i (i + 1)).starProjection_orthogonal_apply_starProjection_orthogonal (by
    rintro _ ⟨ψ, rfl⟩
    change D.d i (i + 1) (D.S (i - 1) i ψ) ∈ _
    rw [D.anticomm, ← map_neg]
    exact S_mem_range rfl _) x

theorem dt_mpInv_d_starProjection (hJ : Function.Bijective (D.S J (J + 1))) (x : V J) :
    D.dt J (J + 1) (D.mpInv J (J + 1) (D.d J (J + 1) ((D.SL (J - 1) J).rangeᗮ.starProjection x))) =
      D.dt J (J + 1) (D.mpInv J (J + 1) (D.d J (J + 1) x)) := by
  have := hasOrthogonalProjection_range_of_surjective hJ.2
  let g : V J →L[𝕜] Vt (J + 1) := D.dtL J (J + 1) ∘L (D.SL J (J + 1)).moorePenrose ∘L D.dL J (J + 1)
  have hg : g ((D.SL (J - 1) J).rangeᗮ.starProjection x) = g x := by
    rw [← sub_eq_zero, ← map_sub, ← neg_sub, map_neg, neg_eq_zero]
    refine g.apply_eq_zero_of_mem_orthogonal_orthogonal (A := (D.SL (J - 1) J).range) ?_
      ((D.SL (J - 1) J).rangeᗮ.sub_starProjection_mem_orthogonal x)
    rintro _ ⟨ψ, rfl⟩
    change D.dt J (J + 1) (D.mpInv J (J + 1) (D.d J (J + 1) (D.S (J - 1) J ψ))) = 0
    rw [D.anticomm, map_neg, mpInv_S hJ, map_neg, D.dt_comp_dt, neg_zero]
  exact hg

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
/-- The output complex of [ArnoldHu2021], (24)–(26), for `Sᴶ` bijective. -/
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
/-- The cochain map from the subquotient model `Γ / Δ` to the output complex. -/
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

/-- The subquotient model and the output complex are isomorphic where the ranges `R(Sⁱ⁻¹)`,
`i ≤ J`, are closed. -/
theorem isIso_toOrth (hJ : Function.Bijective (D.S J (J + 1)))
    (hR : ∀ i ≤ J, IsClosed ((D.SL (i - 1) i).range : Set (V i))) : IsIso (D.toOrth J hJ) := by
  have : ∀ i, IsIso ((D.toOrth J hJ).f i) := fun i =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_toOrth hJ hR i)
  exact HomologicalComplex.Hom.isIso_of_components _

/-! ### The cochain map (30) -/

variable {K : ∀ i, Vt i →ₗ[𝕜] V i} (hK : D.IsNullHomotopy K)
  (hinj : ∀ i ≤ J, Function.Injective (D.S i (i + 1)))
  (hsurj : ∀ i, J ≤ i → Function.Surjective (D.S i (i + 1)))

omit [∀ i, CompleteSpace (V i)] [∀ i, CompleteSpace (Vt i)] in
theorem bijective_S (hinj : ∀ i ≤ J, Function.Injective (D.S i (i + 1)))
    (hsurj : ∀ i, J ≤ i → Function.Surjective (D.S i (i + 1))) :
    Function.Bijective (D.S J (J + 1)) :=
  ⟨hinj J le_rfl, hsurj J le_rfl⟩

variable (D J) in
/-- The cochain map (30) of [ArnoldHu2021], Theorem 7, with the Moore–Penrose inverses. -/
def orthSumMap (hinj : ∀ i ≤ J, Function.Injective (D.S i (i + 1)))
    (hsurj : ∀ i, J ≤ i → Function.Surjective (D.S i (i + 1))) {K : ∀ i, Vt i →ₗ[𝕜] V i}
    (hK : D.IsNullHomotopy K) : D.sumComplex ⟶ D.orthComplex J (bijective_S hinj hsurj) :=
  D.bggSumMap D.mpInv hK (injSurjWith_mpInv hinj hsurj) ≫ D.toOrth J _

theorem coe_orthSumMap_apply (i : ℤ) (x : V i × Vt i) :
    Subtype.val (((D.orthSumMap J hinj hsurj hK).f i).hom x) =
      D.toOrthMap J i (D.bggProjMap J D.mpInv i (x.1 + K i x.2, x.2)) := by
  rfl

/-- (30) up to `J`: `𝒦ⁱ(ω, μ) = P_{R(Sⁱ⁻¹)ᗮ}(ω + Kμ)`. [ArnoldHu2021], (30) -/
theorem orthSumMap_of_le {i : ℤ} (hi : i ≤ J) (x : V i × Vt i) :
    Subtype.val (((D.orthSumMap J hinj hsurj hK).f i).hom x) =
      ((D.SL (i - 1) i).rangeᗮ.starProjection (x.1 + K i x.2), 0) := by
  rw [coe_orthSumMap_apply, toOrthMap_of_le hi]
  rcases hi.lt_or_eq with hi' | rfl
  · rw [Data.bggProjMap_of_lt hi']
  · rw [Data.bggProjMap_of_eq rfl]

/-- (30) after `J`: `𝒦ⁱ(ω, μ) = P_{N(Sⁱ)}[d̃ tⁱ ω + (I + d̃ tⁱ K)μ]`. [ArnoldHu2021], (30) -/
theorem orthSumMap_of_gt {i : ℤ} (hi : J < i) (x : V i × Vt i) :
    Subtype.val (((D.orthSumMap J hinj hsurj hK).f i).hom x) =
      (0, (D.SL i (i + 1)).ker.starProjection (D.dt (i - 1) i (D.mpInv (i - 1) i x.1) +
        (x.2 + D.dt (i - 1) i (D.mpInv (i - 1) i (K i x.2))))) := by
  rw [coe_orthSumMap_apply, toOrthMap_of_gt hi, Data.bggProjMap_of_gt hi,
    kerProj_mpInv (hsurj i hi.le)]
  congr 2
  rw [map_add, map_add]
  abel

/-- If the ranges `R(Sⁱ⁻¹)`, `i ≤ J`, are closed, the cochain map (30) induces an isomorphism on
cohomology. [ArnoldHu2021], Theorem 7 -/
theorem quasiIso_orthSumMap (hR : ∀ i ≤ J, IsClosed ((D.SL (i - 1) i).range : Set (V i))) :
    QuasiIso (D.orthSumMap J hinj hsurj hK) := by
  have := Data.quasiIso_bggSumMap (injSurjWith_mpInv hinj hsurj) hK
  have := isIso_toOrth (bijective_S hinj hsurj) hR
  unfold orthSumMap
  infer_instance

/-- The cochain map (30) carries cohomology representatives `H × H̃` of the rows to cohomology
representatives of the output complex. [ArnoldHu2021], Corollary 1, (31) -/
theorem orth_represents (hR : ∀ i ≤ J, IsClosed ((D.SL (i - 1) i).range : Set (V i))) {i : ℤ}
    {H : Submodule 𝕜 (V i)} {Ht : Submodule 𝕜 (Vt i)} (hH : D.rowTop.Represents i H)
    (hHt : D.rowBot.Represents i Ht) :
    (D.orthComplex J (bijective_S hinj hsurj)).Represents i
      ((H.prod Ht).map ((D.orthSumMap J hinj hsurj hK).f i).hom) :=
  have := quasiIso_orthSumMap hK hinj hsurj hR
  (Data.represents_sumComplex hH hHt).map _

/-! ### Non-vacuity -/

section NonVacuity

variable (𝕜)

/-- The orthogonal projection `x ↦ x₀ e₀` of `𝕜²` onto its first axis. -/
def axisProj : EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2) :=
  (EuclideanSpace.projₗ 0).smulRight (EuclideanSpace.single 0 1)

variable {𝕜}

theorem axisProj_apply (x : EuclideanSpace 𝕜 (Fin 2)) :
    axisProj 𝕜 x = x 0 • EuclideanSpace.single 0 1 := rfl

theorem axisProj_axisProj (x : EuclideanSpace 𝕜 (Fin 2)) : axisProj 𝕜 (axisProj 𝕜 x) = axisProj 𝕜 x := by
  simp [axisProj_apply]

/-- `c • axisProj` between subspaces `A`, `B` of `𝕜²`, `B` containing the first axis. -/
def axisMap {A B : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin 2))} (hB : LinearMap.range (axisProj 𝕜) ≤ B)
    (c : 𝕜) : A →ₗ[𝕜] B :=
  c • (axisProj 𝕜 ∘ₗ A.subtype).codRestrict B fun x => hB ⟨x, rfl⟩

theorem coe_axisMap_apply {A B : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin 2))}
    (hB : LinearMap.range (axisProj 𝕜) ≤ B) (c : 𝕜) (x : A) :
    (axisMap hB c x : EuclideanSpace 𝕜 (Fin 2)) = c • axisProj 𝕜 x := rfl

theorem axisMap_axisMap {A B C : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin 2))}
    (hB : LinearMap.range (axisProj 𝕜) ≤ B) (hC : LinearMap.range (axisProj 𝕜) ≤ C) (b c : 𝕜)
    (x : A) : axisMap (A := B) hC c (axisMap hB b x) = axisMap hC (c * b) x := by
  ext1
  simp only [coe_axisMap_apply, map_smul, axisProj_axisProj, smul_smul]

theorem axisMap_zero {A B : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin 2))}
    (hB : LinearMap.range (axisProj 𝕜) ≤ B) : axisMap (A := A) hB 0 = 0 := by
  simp [axisMap]

theorem axisMap_neg {A B : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin 2))}
    (hB : LinearMap.range (axisProj 𝕜) ≤ B) (c : 𝕜) (x : A) :
    axisMap hB (-c) x = -axisMap hB c x := by
  simp [axisMap]

theorem axisMap_sub {A B : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin 2))}
    (hB : LinearMap.range (axisProj 𝕜) ≤ B) (b c : 𝕜) (x : A) :
    axisMap hB (b - c) x = axisMap hB b x - axisMap hB c x := by
  simp [axisMap, sub_smul]

theorem apply_one_mul_apply_one (f g : 𝕜 →ₗ[𝕜] 𝕜) : f 1 * g 1 = f (g 1) := by
  rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

variable {ι : Type*} {c : ComplexShape ι} (D₀ : Data 𝕜 c (fun _ => 𝕜) (fun _ => 𝕜))
  {W Wt : ι → Submodule 𝕜 (EuclideanSpace 𝕜 (Fin 2))}

/-- Scalar BGG data `D₀` along the first axis of subspaces of `𝕜²`. -/
def axisData (hW : ∀ i, LinearMap.range (axisProj 𝕜) ≤ W i)
    (hWt : ∀ i, LinearMap.range (axisProj 𝕜) ≤ Wt i) :
    BoundedData 𝕜 c (fun i => W i) (fun i => Wt i) where
  d i j := axisMap (hW j) (D₀.d i j 1)
  dt i j := axisMap (hWt j) (D₀.dt i j 1)
  S i j := axisMap (hW j) (D₀.S i j 1)
  shape_d i j h := by rw [D₀.shape_d i j h, LinearMap.zero_apply, axisMap_zero]
  shape_dt i j h := by rw [D₀.shape_dt i j h, LinearMap.zero_apply, axisMap_zero]
  shape_S i j h := by rw [D₀.shape_S i j h, LinearMap.zero_apply, axisMap_zero]
  d_comp_d i j k x := by
    rw [axisMap_axisMap, apply_one_mul_apply_one, D₀.d_comp_d, axisMap_zero, LinearMap.zero_apply]
  dt_comp_dt i j k x := by
    rw [axisMap_axisMap, apply_one_mul_apply_one, D₀.dt_comp_dt, axisMap_zero,
      LinearMap.zero_apply]
  anticomm i j k φ := by
    rw [axisMap_axisMap, axisMap_axisMap, apply_one_mul_apply_one, apply_one_mul_apply_one,
      D₀.anticomm, axisMap_neg]
  continuous_d _ _ := LinearMap.continuous_of_finiteDimensional _
  continuous_dt _ _ := LinearMap.continuous_of_finiteDimensional _
  continuous_S _ _ := LinearMap.continuous_of_finiteDimensional _

variable {D₀}

theorem axisData_isNullHomotopy (hW : ∀ i, LinearMap.range (axisProj 𝕜) ≤ W i)
    (hWt : ∀ i, LinearMap.range (axisProj 𝕜) ≤ Wt i) {K₀ : ι → 𝕜 →ₗ[𝕜] 𝕜}
    (hK₀ : D₀.IsNullHomotopy K₀) :
    (axisData D₀ hW hWt).IsNullHomotopy fun i => axisMap (hW i) (K₀ i 1) := fun i j hij μ => by
  change axisMap (hW j) _ μ =
    axisMap (hW j) _ (axisMap (hW i) _ μ) - axisMap (hW j) _ (axisMap (hWt j) _ μ)
  rw [axisMap_axisMap, axisMap_axisMap, apply_one_mul_apply_one, apply_one_mul_apply_one,
    ← axisMap_sub, ← hK₀ i j hij]

theorem injective_axisMap {A B : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin 2))}
    (hB : LinearMap.range (axisProj 𝕜) ≤ B) (hA : A ≤ LinearMap.range (axisProj 𝕜)) :
    Function.Injective (axisMap (A := A) hB 1) := fun x y h => by
  obtain ⟨x', hx'⟩ := hA x.2
  obtain ⟨y', hy'⟩ := hA y.2
  have h := congrArg Subtype.val h
  simp only [coe_axisMap_apply, one_smul, ← hx', ← hy', axisProj_axisProj] at h
  exact Subtype.ext (hx'.symm.trans (h.trans hy'))

theorem surjective_axisMap {A B : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin 2))}
    (hB : LinearMap.range (axisProj 𝕜) ≤ B) (hA : LinearMap.range (axisProj 𝕜) ≤ A)
    (hB' : B ≤ LinearMap.range (axisProj 𝕜)) :
    Function.Surjective (axisMap (A := A) hB 1) := fun y => by
  obtain ⟨y', hy'⟩ := hB' y.2
  refine ⟨⟨axisProj 𝕜 y', hA ⟨y', rfl⟩⟩, Subtype.ext ?_⟩
  rw [coe_axisMap_apply, one_smul, axisProj_axisProj, hy']

theorem injective_axisData_S (hW : ∀ i, LinearMap.range (axisProj 𝕜) ≤ W i)
    (hWt : ∀ i, LinearMap.range (axisProj 𝕜) ≤ Wt i) {i j : ι} (h : D₀.S i j 1 = 1)
    (hA : Wt i ≤ LinearMap.range (axisProj 𝕜)) : Function.Injective ((axisData D₀ hW hWt).S i j) := by
  change Function.Injective (axisMap (hW j) (D₀.S i j 1))
  rw [h]
  exact injective_axisMap _ hA

theorem surjective_axisData_S (hW : ∀ i, LinearMap.range (axisProj 𝕜) ≤ W i)
    (hWt : ∀ i, LinearMap.range (axisProj 𝕜) ≤ Wt i) {i j : ι} (h : D₀.S i j 1 = 1)
    (hB : W j ≤ LinearMap.range (axisProj 𝕜)) :
    Function.Surjective ((axisData D₀ hW hWt).S i j) := by
  change Function.Surjective (axisMap (hW j) (D₀.S i j 1))
  rw [h]
  exact surjective_axisMap _ (hWt i) hB

variable (𝕜)

/-- `Data.altShift` along the first axis, with the second axis added to `V⁰` and to `Ṽ¹`. -/
def planeAltShift :
    BoundedData 𝕜 (ComplexShape.up ℤ)
      (fun i => ↥(if i = 0 then ⊤ else LinearMap.range (axisProj 𝕜)))
      (fun i => ↥(if i = 1 then ⊤ else LinearMap.range (axisProj 𝕜))) :=
  axisData (Data.altShift 𝕜) (fun i => by split_ifs <;> simp) (fun i => by split_ifs <;> simp)

/-- For `planeAltShift` at `J = 0`, (30) is a quasi-isomorphism and the output spaces `Υ⁰`, `Υ¹`
are nonzero. -/
theorem planeAltShift_quasiIso_orthSumMap :
    ∃ (hinj : ∀ i ≤ 0, Function.Injective ((planeAltShift 𝕜).S i (i + 1)))
      (hsurj : ∀ i, 0 ≤ i → Function.Surjective ((planeAltShift 𝕜).S i (i + 1))),
      QuasiIso ((planeAltShift 𝕜).orthSumMap 0 hinj hsurj
        (axisData_isNullHomotopy _ _ (Data.altShift_isNullHomotopy 𝕜))) ∧
      (planeAltShift 𝕜).Υ 0 0 ≠ ⊥ ∧ (planeAltShift 𝕜).Υ 0 1 ≠ ⊥ := by
  have hS : ∀ i, (Data.altShift 𝕜).S i (i + 1) 1 = 1 := fun i => by simp [Data.altShift]
  have e₁ : EuclideanSpace.single (1 : Fin 2) (1 : 𝕜) ≠ 0 := by simp
  refine ⟨fun i hi => injective_axisData_S _ _ (hS i) (by simp [show i ≠ 1 by omega]),
    fun i hi => surjective_axisData_S _ _ (hS i) (by simp [show i + 1 ≠ 0 by omega]),
    quasiIso_orthSumMap _ _ _ fun _ _ => Submodule.closed_of_finiteDimensional _,
    (Submodule.ne_bot_iff _).2 ⟨(⟨EuclideanSpace.single 1 1, by simp⟩, 0), ?_, ?_⟩,
    (Submodule.ne_bot_iff _).2 ⟨(0, ⟨EuclideanSpace.single 1 1, by simp⟩), ?_, ?_⟩⟩
  · rw [mem_Υ_of_le le_rfl]
    refine ⟨(Submodule.mem_orthogonal _ _).2 ?_, rfl⟩
    rintro _ ⟨φ, rfl⟩
    simp [Submodule.coe_inner, planeAltShift, axisData, SL, coe_axisMap_apply, axisProj_apply,
      EuclideanSpace.inner_single_right]
  · exact fun h => e₁ (congrArg (fun x => (x.1 : EuclideanSpace 𝕜 (Fin 2))) h)
  · rw [mem_Υ_of_gt zero_lt_one]
    refine ⟨rfl, Subtype.ext ?_⟩
    simp [planeAltShift, axisData, coe_axisMap_apply, axisProj_apply]
  · exact fun h => e₁ (congrArg (fun x => (x.2 : EuclideanSpace 𝕜 (Fin 2))) h)

end NonVacuity

end Feec.BGG.BoundedData
