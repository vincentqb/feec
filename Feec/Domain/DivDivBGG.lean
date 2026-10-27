module

public import Feec.Domain.DivDivComplex
public import Feec.Domain.ElasticityBGG

/-!
# The div-div complex as a BGG complex

The de Rham complex of `ℝ³` with values in `𝕜³` (`deRhamVec 3`) stacked over the scalar de Rham
complex (`deRhamVec 1`), linked by `S⁰ ψ = ψ I`, `S¹ = -mskw` and `S² = I`, is BGG data of
constant-coefficient operators (`divDivBGG`): `S⁰` and `S¹` are one-to-one and `S²` is bijective,
so the injectivity/surjectivity condition holds at `J = 2` (**`injSurj_divDivBGG`**). Its BGG
complex `bgg 2` eliminates `V³` against `S²` and `Ṽ⁰, Ṽ¹` against `S⁰, S¹`, and **is the div-div
complex** `𝕜³ --dev grad--> T --sym curl--> Sym --div div--> 𝕜` of `Feec.Domain.DivDivComplex` on
smooth fields (**`divDivBGGIso`**): in degree `1` the quotient `V¹ / R(S⁰) = 𝕜^{3×3} / 𝕜 I ≅ T`,
`[σ] ↦ dev σ`, in degree `2` the quotient `V² / R(S¹) = 𝕜^{3×3} / skew ≅ Sym`, `[σ] ↦ sym σ`
(the pairs `(σ, div σ)` modulo `(-S¹ψ, curl ψ)`), with differentials `u ↦ dev grad u`,
`σ ↦ sym curl σ` and `σ ↦ div div σ`. Hence the smooth div-div complex has the cohomology of the
twisted de Rham complex (`divDivSmoothComplexHomologyIso`).

## Main definitions

* `Feec.Domain.divDivBGG`: the BGG diagram of the div-div complex.
* `Feec.Domain.divDivSmoothComplex`: the smooth div-div complex (`divDivOp`, `divDivMat`).

## Main results

* **`injSurj_divDivBGG`**, `divDivBGGHomologyIso`.
* **`divDivBGGIso`**, `divDivSmoothComplexHomologyIso`.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §4.3 (the div-div complex,
  `J = 2`)
* [D. Pauly, W. Zulehner, *The divDiv-complex and applications to biharmonic equations*][PaulyZulehner2020]
  (the div-div complex)
* [A. Čap, J. Slovák, V. Souček, *Bernstein–Gelfand–Gelfand sequences*][CapSlovakSoucek2001]
  (BGG sequences)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped ContDiff
open CategoryTheory

@[expose] public noncomputable section

namespace Feec.Domain

variable {𝕜 : Type*} [RCLike 𝕜]

section DivDiv

open ConstCoeffOp Matrix

/-- `S⁰ ψ = ψ I : 𝕜 → 𝕜^{3×3}`. -/
def ddS0 : Matrix (Fin 3 × Fin 3) (Fin 1) 𝕜 := fun ij _ => if ij.1 = ij.2 then 1 else 0

/-- `S¹ = -mskw : 𝕜^{1×3} → 𝕜^{3×3}`. -/
def ddS1 : Matrix (Fin 3 × Fin 3) (Fin 1 × Fin 3) 𝕜 := fun ij a => elS0 ij a.2

/-- `S² = I : 𝕜^{1×3} → 𝕜³`. -/
def ddS2 : Matrix (Fin 3) (Fin 1 × Fin 3) 𝕜 := fun i a => if a.2 = i then 1 else 0

variable (𝕜) in
/-- The connecting operators of the div-div diagram: `ψ ↦ ψ I`, `-mskw`, `I`. -/
def divDivS : ∀ k : ℤ, ConstCoeffOp (Fin 3 → ℝ) 𝕜 (vecIdx 1 k) (vecIdx 3 (k + 1))
  | .ofNat 0 => ofMatrix ddS0
  | .ofNat 1 => ofMatrix ddS1
  | .ofNat 2 => ofMatrix ddS2
  | .ofNat (_ + 3) => zeroOp _ _
  | .negSucc _ => zeroOp _ _

theorem ofMatrix_ddS0_apply (f : Fin 1 → (Fin 3 → ℝ) → 𝕜) (ij : Fin 3 × Fin 3) :
    (ofMatrix ddS0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f ij =
      if ij.1 = ij.2 then f 0 else 0 := by
  funext x
  simp only [ofMatrix_apply, ddS0, Fin.sum_univ_one]
  split_ifs <;> simp

theorem ofMatrix_ddS1_apply (f : Fin 1 × Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (ofMatrix ddS1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f =
      (ofMatrix elS0).apply fun l => f (0, l) := by
  funext ij x
  simp only [ofMatrix_apply, ddS1, Fintype.sum_prod_type, Fin.sum_univ_one]

theorem ofMatrix_ddS2_apply (f : Fin 1 × Fin 3 → (Fin 3 → ℝ) → 𝕜) (i : Fin 3) :
    (ofMatrix ddS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f i = f (0, i) := by
  funext x
  simp only [ofMatrix_apply, ddS2, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp

/-- `curl S⁰ = -S¹ grad`. -/
theorem curlOp_ddS0 (f : Fin 1 → (Fin 3 → ℝ) → 𝕜) :
    (curlOp 3).apply ((ofMatrix ddS0).apply f) =
      -(ofMatrix ddS1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply ((gradOp 3 1).apply f) := by
  funext ⟨i, k⟩ x
  rw [curlOp_apply, Pi.neg_apply, Pi.neg_apply, ofMatrix_ddS1_apply, ofMatrix_elS0_apply,
    ofMatrix_ddS0_apply, ofMatrix_ddS0_apply]
  fin_cases i <;> fin_cases k <;> simp [gradOp_apply]

/-- `div S¹ = -S² curl`. -/
theorem divOp_ddS1 (f : Fin 1 × Fin 3 → (Fin 3 → ℝ) → 𝕜) :
    (divOp 3 3).apply ((ofMatrix ddS1).apply f) =
      -(ofMatrix ddS2 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply ((curlOp 1).apply f) := by
  funext i x
  rw [divOp_apply, Pi.neg_apply, Pi.neg_apply, ofMatrix_ddS2_apply, ofMatrix_ddS1_apply]
  simp only [ofMatrix_elS0_apply, Fin.sum_univ_three, curlOp_apply]
  fin_cases i <;> simp [fderiv_neg] <;> ring

theorem divDivS_anticomm (k : ℤ) (f : vecIdx 1 k → (Fin 3 → ℝ) → 𝕜)
    (_ : ∀ i, ContDiff ℝ ∞ (f i)) :
    (vecOp 𝕜 3 (k + 1)).apply ((divDivS 𝕜 k).apply f) =
      -(divDivS 𝕜 (k + 1)).apply ((vecOp 𝕜 1 k).apply f) := by
  by_cases h0 : k = 0
  · subst h0; exact curlOp_ddS0 f
  by_cases h1 : k = 1
  · subst h1; exact divOp_ddS1 f
  rcases lt_or_gt_of_ne h0 with hk | hk
  · have := isEmpty_vecIdx 1 (k := k) (Or.inl hk)
    rw [ConstCoeffOp.apply_eq_zero_of_isEmpty _ f (Or.inl this),
      ConstCoeffOp.apply_eq_zero_of_isEmpty _ f (Or.inl this), apply_zero, apply_zero, neg_zero]
  · have := isEmpty_vecIdx 3 (k := k + 1 + 1) (Or.inr (by omega))
    exact funext fun j => isEmptyElim j

variable (𝕜) in
/-- **The BGG diagram of the div-div complex**: the de Rham complex with values in `𝕜³` over the
scalar de Rham complex, linked by `ψ ↦ ψ I`, `-mskw`, `I`. [ArnoldHu2021], §4.3 -/
abbrev divDivBGG : ConstCoeffBGG (Fin 3 → ℝ) 𝕜 where
  top := deRhamVec 𝕜 3
  bot := deRhamVec 𝕜 1
  S := divDivS 𝕜
  anticomm := divDivS_anticomm

/-- A left inverse of `S⁰`: `M ↦ M₀₀`. -/
def ddN0 : Matrix (Fin 1) (Fin 3 × Fin 3) 𝕜 := fun _ ij => if ij = (0, 0) then 1 else 0

/-- A left inverse of `S¹`: `v_l = M_{l+2,l+1}`. -/
def ddN1 : Matrix (Fin 1 × Fin 3) (Fin 3 × Fin 3) 𝕜 := fun a ij => elN0 a.2 ij

/-- The inverse of `S²`. -/
def ddN2 : Matrix (Fin 1 × Fin 3) (Fin 3) 𝕜 := fun a i => if a.2 = i then 1 else 0

theorem ddN0_mul_ddS0 : ddN0 * ddS0 = (1 : Matrix (Fin 1) (Fin 1) 𝕜) := by
  ext a b
  fin_cases a; fin_cases b
  simp [Matrix.mul_apply, ddS0, ddN0, Fintype.sum_prod_type]

theorem ddN1_mul_ddS1 : ddN1 * ddS1 = (1 : Matrix (Fin 1 × Fin 3) (Fin 1 × Fin 3) 𝕜) := by
  ext ⟨a, l⟩ ⟨b, l'⟩
  fin_cases a; fin_cases b
  fin_cases l <;> fin_cases l' <;>
    simp [Matrix.mul_apply, ddS1, ddN1, elS0, elN0, Fintype.sum_prod_type, Fin.sum_univ_three]

theorem ddS2_mul_ddN2 : ddS2 * ddN2 = (1 : Matrix (Fin 3) (Fin 3) 𝕜) := by
  ext i i'
  fin_cases i <;> fin_cases i' <;>
    simp [Matrix.mul_apply, ddS2, ddN2, Fintype.sum_prod_type]

theorem ddN2_mul_ddS2 : ddN2 * ddS2 = (1 : Matrix (Fin 1 × Fin 3) (Fin 1 × Fin 3) 𝕜) := by
  ext ⟨a, l⟩ ⟨b, l'⟩
  fin_cases a; fin_cases b
  fin_cases l <;> fin_cases l' <;> simp [Matrix.mul_apply, ddS2, ddN2]

/-- **The div-div diagram satisfies the injectivity/surjectivity condition at `J = 2`**:
`ψ ↦ ψ I` and `-mskw` are one-to-one, `I` is onto. [ArnoldHu2021], (23), §4.3 -/
theorem injSurj_divDivBGG : (divDivBGG 𝕜).smoothData.InjSurj 2 := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [ConstCoeffBGG.smoothData_S]
    by_cases h0 : i = 0
    · subst h0
      have h := smoothMap_ofMatrix_injective (E := Fin 3 → ℝ) (ddN0_mul_ddS0 (𝕜 := 𝕜))
      exact h
    by_cases h1 : i = 1
    · subst h1
      have h := smoothMap_ofMatrix_injective (E := Fin 3 → ℝ) (ddN1_mul_ddS1 (𝕜 := 𝕜))
      exact h
    have := isEmpty_vecIdx 1 (k := i) (Or.inl (by omega))
    have hs := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 1 i)
    exact fun a b _ => hs.elim a b
  · rw [ConstCoeffBGG.smoothData_S]
    by_cases h2 : i = 2
    · subst h2
      have h := smoothMap_ofMatrix_surjective (E := Fin 3 → ℝ) (ddS2_mul_ddN2 (𝕜 := 𝕜))
      exact h
    have := isEmpty_vecIdx 3 (k := i + 1) (Or.inr (by omega))
    have hs := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 3 (i + 1))
    exact fun y => ⟨0, hs.elim _ _⟩

/-- **The div-div BGG complex has the cohomology of the twisted de Rham complex.**
[ArnoldHu2021], §5.2 -/
def divDivBGGHomologyIso (i : ℤ) :
    ((divDivBGG 𝕜).smoothData.bgg 2).homology i ≅
      (divDivBGG 𝕜).smoothData.twistComplex.homology i :=
  BGG.Data.bggHomologyIso injSurj_divDivBGG i

/-! ### The BGG complex is the smooth div-div complex -/

variable (𝕜) in
/-- The smooth div-div complex `𝕜³ --dev grad--> T --sym curl--> Sym --div div--> 𝕜` of
`Feec.Domain.DivDivComplex`. -/
abbrev divDivSmoothComplex : CochainComplex (ModuleCat 𝕜) ℤ :=
  (divDivConstCoeffComplex 𝕜).smoothComplex (divDivMat 𝕜) divDivOp_matMapsTo

theorem bijective_divDivBGG_S_two :
    Function.Bijective ((divDivBGG 𝕜).smoothData.S 2 (2 + 1)) := by
  rw [ConstCoeffBGG.smoothData_S]
  have h1 := smoothMap_ofMatrix_injective (E := Fin 3 → ℝ) (ddN2_mul_ddS2 (𝕜 := 𝕜))
  have h2 := smoothMap_ofMatrix_surjective (E := Fin 3 → ℝ) (ddS2_mul_ddN2 (𝕜 := 𝕜))
  exact ⟨h1, h2⟩

theorem range_divDivBGG_S_neg_one :
    LinearMap.range ((divDivBGG 𝕜).smoothData.S (0 - 1) 0) = ⊥ := by
  have := isEmpty_vecIdx 1 (k := 0 - 1) (Or.inl (by norm_num))
  have hs := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 1 (0 - 1))
  refine eq_bot_iff.2 ?_
  rintro _ ⟨ψ, rfl⟩
  rw [hs.elim ψ 0, map_zero]
  exact zero_mem _

theorem divDivBGG_Δ_eq_bot {k : ℤ} (hk : k < 0 ∨ 2 < k) :
    (divDivBGG 𝕜).smoothData.Δ (· < 2) k = ⊥ := by
  rcases hk with hk | hk
  · have := isEmpty_vecIdx 1 (k := k) (Or.inl hk)
    have := isEmpty_vecIdx 3 (k := k) (Or.inl hk)
    have h1 := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 1 k)
    have h3 := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 3 k)
    exact eq_bot_iff.2 fun x _ => (Submodule.mem_bot 𝕜).2 (Prod.ext (h3.elim _ _) (h1.elim _ _))
  · exact (divDivBGG 𝕜).smoothData.bgg_Δ_of_gt hk

/-- `σ ↦ dev σ` on smooth matrix fields. -/
def devSmoothMap : smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) →ₗ[𝕜]
    smoothFieldsIn (Fin 3 → ℝ) (deviatoricMat 3 : _ → _ → 𝕜) where
  toFun σ := ⟨matMulField (deviatoricMat 3) σ, contDiff_matMulField _ σ.2,
    isProjMat_deviatoricMat.matMulField_matMulField _⟩
  map_add' _ _ := Subtype.ext (funext fun _ => funext fun _ => by
    simp [matMulField, mul_add, Finset.sum_add_distrib])
  map_smul' _ _ := Subtype.ext (funext fun _ => funext fun _ => by
    simp [matMulField, Finset.mul_sum, mul_left_comm])

theorem devSmoothMap_surjective : Function.Surjective (devSmoothMap (𝕜 := 𝕜)) := fun s =>
  ⟨⟨s, s.2.1⟩, Subtype.ext s.2.2⟩

/-- `dev (ψ I) = 0`. -/
theorem matMulField_deviatoricMat_ddS0 (f : Fin 1 → (Fin 3 → ℝ) → 𝕜) :
    matMulField (deviatoricMat 3) ((ofMatrix ddS0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f) =
      0 := by
  funext ⟨i, j⟩ x
  rw [matMulField_deviatoricMat]
  simp only [ofMatrix_ddS0_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The kernel of `dev` is the range of `S⁰ : ψ ↦ ψ I`. -/
theorem ker_devSmoothMap :
    LinearMap.ker (devSmoothMap (𝕜 := 𝕜)) =
      LinearMap.range ((divDivBGG 𝕜).smoothData.S (1 - 1) 1) := by
  ext σ
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro h
    have h' : matMulField (deviatoricMat 3) (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) = 0 :=
      congrArg Subtype.val h
    refine ⟨⟨fun _ => (3 : 𝕜)⁻¹ • ((σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) (0, 0) +
      (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) (1, 1) + (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) (2, 2)),
      fun _ => by
        have := (((σ.2 (0, 0)).add (σ.2 (1, 1))).add (σ.2 (2, 2))).const_smul (3 : 𝕜)⁻¹
        exact this⟩, ?_⟩
    refine Subtype.ext (funext fun ⟨i, j⟩ => funext fun x => ?_)
    have := congrFun (congrFun h' (i, j)) x
    rw [matMulField_deviatoricMat] at this
    change (ofMatrix ddS0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply _ (i, j) x = _
    rw [ofMatrix_ddS0_apply]
    simp only [Fin.sum_univ_three, Pi.zero_apply] at this
    split_ifs at this ⊢ with hij
    · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      linear_combination -this
    · simp only [sub_zero] at this
      exact this.symm
  · rintro ⟨ψ, rfl⟩
    exact Subtype.ext (matMulField_deviatoricMat_ddS0
      (Subtype.val (p := fun f => f ∈ smoothFields (Fin 3 → ℝ) 𝕜 (Fin 1)) ψ))

/-- `𝕜^{3×3} / 𝕜 I ≃ T`, `[σ] ↦ dev σ`. -/
def devQuotEquiv : (smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) ⧸
      LinearMap.range ((divDivBGG 𝕜).smoothData.S (1 - 1) 1)) ≃ₗ[𝕜]
    smoothFieldsIn (Fin 3 → ℝ) (deviatoricMat 3 : _ → _ → 𝕜) :=
  (Submodule.quotEquivOfEq _ _ ker_devSmoothMap.symm).trans
    (LinearMap.quotKerEquivOfSurjective _ devSmoothMap_surjective)

/-- The kernel of `sym` is the range of `S¹ = -mskw`. -/
theorem ker_symSmoothMap_divDiv :
    LinearMap.ker (symSmoothMap (𝕜 := 𝕜)) =
      LinearMap.range ((divDivBGG 𝕜).smoothData.S (2 - 1) 2) := by
  ext σ
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro h
    have h' : matMulField (symMat 3) (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) = 0 :=
      congrArg Subtype.val h
    refine ⟨⟨fun a => (ofMatrix elN0 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) a.2,
      fun a => (ofMatrix elN0).contDiff_apply σ.2 a.2⟩, Subtype.ext ?_⟩
    change (ofMatrix ddS1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply _ = _
    rw [ofMatrix_ddS1_apply]
    exact elS0_elN0_of_skew h'
  · rintro ⟨ψ, rfl⟩
    refine Subtype.ext ?_
    change matMulField (symMat 3) ((ofMatrix ddS1 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (Subtype.val (p := fun f => f ∈ smoothFields (Fin 3 → ℝ) 𝕜 (Fin 1 × Fin 3)) ψ)) = 0
    rw [ofMatrix_ddS1_apply]
    exact matMulField_symMat_elS0 _

/-- `𝕜^{3×3} / skew ≃ Sym`, `[σ] ↦ sym σ`. -/
def symQuotEquivDivDiv : (smoothFields (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) ⧸
      LinearMap.range ((divDivBGG 𝕜).smoothData.S (2 - 1) 2)) ≃ₗ[𝕜]
    smoothFieldsIn (Fin 3 → ℝ) (symMat 3 : _ → _ → 𝕜) :=
  (Submodule.quotEquivOfEq _ _ ker_symSmoothMap_divDiv.symm).trans
    (LinearMap.quotKerEquivOfSurjective _ symSmoothMap_surjective)

/-- The kernel of `S³ = 0` is all of `Ṽ³`, the scalars. -/
def kerDD3Equiv : LinearMap.ker ((divDivBGG 𝕜).smoothData.S 3 (3 + 1)) ≃ₗ[𝕜]
    smoothFieldsIn (Fin 3 → ℝ) (idMat Unit : _ → _ → 𝕜) :=
  (LinearEquiv.ofTop _ (LinearMap.ker_eq_top.2 (LinearMap.ext fun _ =>
    Subtype.ext (funext fun j => isEmptyElim (α := Empty) j)))).trans scalarFieldsEquiv

theorem subsingleton_divDivSmoothComplex_X {k : ℤ} (hk : k < 0 ∨ 3 < k) :
    Subsingleton (smoothFieldsIn (Fin 3 → ℝ) (divDivMat 𝕜 k)) := by
  have : IsEmpty (divDivIdx k) := isEmpty_divDivIdx (by omega) (by omega) (by omega) (by omega)
  exact ⟨fun a b => Subtype.ext (funext fun i => isEmptyElim i)⟩

theorem subsingleton_divDivBGG_Γ {k : ℤ} (hk : k < 0 ∨ 3 < k) :
    Subsingleton ((divDivBGG 𝕜).smoothData.Γ (2 < ·) k) := by
  have := isEmpty_vecIdx 1 hk
  have := isEmpty_vecIdx 3 hk
  have h1 := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 1 k)
  have h3 := subsingleton_smoothFields (E := Fin 3 → ℝ) (𝕜 := 𝕜) (ι := vecIdx 3 k)
  exact ⟨fun a b => Subtype.ext (Prod.ext (h3.elim _ _) (h1.elim _ _))⟩

/-- The components of the identification of the BGG complex with the div-div complex. -/
def divDivBGGEquiv : ∀ k : ℤ, ((divDivBGG 𝕜).smoothData.bgg 2).X k ≃ₗ[𝕜]
    (divDivSmoothComplex 𝕜).X k
  | .ofNat 0 => ((divDivBGG 𝕜).smoothData.bggXEquivOfLt (J := 2) (i := 0) two_pos).trans
      ((Submodule.quotEquivOfEqBot _ range_divDivBGG_S_neg_one).trans smoothFieldsEquivIdMat)
  | .ofNat 1 => ((divDivBGG 𝕜).smoothData.bggXEquivOfLt (J := 2) (i := 1) one_lt_two).trans
      devQuotEquiv
  | .ofNat 2 => ((divDivBGG 𝕜).smoothData.bggXEquivOfBijective
      bijective_divDivBGG_S_two).trans symQuotEquivDivDiv
  | .ofNat 3 => ((divDivBGG 𝕜).smoothData.derivedXEquiv (2 < ·) (· < 2)
      (divDivBGG_Δ_eq_bot (Or.inr (by norm_num)))).trans
      (((divDivBGG 𝕜).smoothData.bggΓEquivKer (J := 2) (i := 3) (by norm_num)).trans
        kerDD3Equiv)
  | .ofNat (n + 4) =>
      have := subsingleton_divDivBGG_Γ (𝕜 := 𝕜) (k := .ofNat (n + 4))
        (Or.inr (by rw [Int.ofNat_eq_natCast]; omega))
      have : Subsingleton ((divDivSmoothComplex 𝕜).X (.ofNat (n + 4))) :=
        subsingleton_divDivSmoothComplex_X (𝕜 := 𝕜) (k := .ofNat (n + 4))
          (Or.inr (by rw [Int.ofNat_eq_natCast]; omega))
      ((divDivBGG 𝕜).smoothData.derivedXEquiv (2 < ·) (· < 2)
        (divDivBGG_Δ_eq_bot (k := .ofNat (n + 4))
          (Or.inr (by rw [Int.ofNat_eq_natCast]; omega)))).trans (LinearEquiv.ofSubsingleton _ _)
  | .negSucc n =>
      have := subsingleton_divDivBGG_Γ (𝕜 := 𝕜) (k := .negSucc n)
        (Or.inl (Int.negSucc_lt_zero n))
      have : Subsingleton ((divDivSmoothComplex 𝕜).X (.negSucc n)) :=
        subsingleton_divDivSmoothComplex_X (𝕜 := 𝕜) (k := .negSucc n)
          (Or.inl (Int.negSucc_lt_zero n))
      ((divDivBGG 𝕜).smoothData.derivedXEquiv (2 < ·) (· < 2)
        (divDivBGG_Δ_eq_bot (k := .negSucc n) (Or.inl (Int.negSucc_lt_zero n)))).trans
        (LinearEquiv.ofSubsingleton _ _)

/-- `sym curl (dev σ) = sym curl σ`: `curl (g I)` is skew. -/
theorem symCurl_dev {σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜} (hσ : ∀ i, ContDiff ℝ ∞ (σ i)) :
    matMulField (symMat 3) ((curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (matMulField (deviatoricMat 3) σ)) = matMulField (symMat 3) ((curlOp 3).apply σ) := by
  set D : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜 :=
    fun ij => if ij.1 = ij.2 then fun x => ∑ k, σ (k, k) x else 0 with hDdef
  have hD : ∀ ij, ContDiff ℝ ∞ (D ij) := fun ij => by
    simp only [hDdef]
    split_ifs
    · exact ContDiff.sum fun k _ => hσ (k, k)
    · exact contDiff_const
  rw [matMulField_deviatoricMat_three, ← hDdef,
    (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply_add (f := σ) (g := (-(3 : 𝕜)⁻¹) • D) hσ
      fun ij => (hD ij).const_smul (-(3 : 𝕜)⁻¹),
    (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply_smul _ (f := D) hD]
  have h0 := matMulField_symMat_curlOp_smul_id (𝕜 := 𝕜) fun x => ∑ k, σ (k, k) x
  funext ij x
  have h0' := congrFun (congrFun h0 ij) x
  simp only [matMulField, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_add,
    Finset.sum_add_distrib] at h0' ⊢
  rw [show (∑ j, symMat 3 ij j * (-(3 : 𝕜)⁻¹ *
      (curlOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply D j x)) =
      -(3 : 𝕜)⁻¹ * ∑ j, symMat 3 ij j * (curlOp 3).apply D j x by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, h0', mul_zero, add_zero]

/-- `div div (sym σ) = div div σ`. -/
theorem divdivOp_symMat {σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜} (hσ : ∀ i, ContDiff ℝ ∞ (σ i)) :
    (divdivOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply (matMulField (symMat 3) σ) =
      (divdivOp 3).apply σ := by
  have hσT : ∀ i : Fin 3 × Fin 3, ContDiff ℝ ∞ ((fun ij : Fin 3 × Fin 3 => σ (ij.2, ij.1)) i) :=
    fun i => hσ _
  rw [matMulField_symMat_eq,
    (divdivOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) Unit).apply_smul _
      (f := σ + fun ij : Fin 3 × Fin 3 => σ (ij.2, ij.1)) (fun i => (hσ i).add (hσT i)),
    (divdivOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 (Fin 3 × Fin 3) Unit).apply_add hσ hσT,
    divdivOp_apply_transpose hσ]
  funext u x
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem divDivBGGEquiv_comm_zero :
    (divDivBGGEquiv 0).toModuleIso.hom ≫ (divDivSmoothComplex 𝕜).d 0 (0 + 1) =
      ((divDivBGG 𝕜).smoothData.bgg 2).d 0 (0 + 1) ≫ (divDivBGGEquiv (0 + 1)).toModuleIso.hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun q => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨⟨u, ψ⟩, hx⟩ := (x : (divDivBGG 𝕜).smoothData.Γ (2 < ·) 0)
  apply Subtype.ext
  change (devGradOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply (u : Fin 3 → (Fin 3 → ℝ) → 𝕜) =
    matMulField (deviatoricMat 3) ((gradOp 3 3).apply (u : Fin 3 → (Fin 3 → ℝ) → 𝕜) -
      (ofMatrix ddS0).apply (ψ : Fin 1 → (Fin 3 → ℝ) → 𝕜))
  rw [devGradOp_apply]
  have h0 := matMulField_deviatoricMat_ddS0 (𝕜 := 𝕜) ψ
  funext ij x
  have := congrFun (congrFun h0 ij) x
  simp only [matMulField, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply] at this ⊢
  rw [this, sub_zero]

theorem divDivBGGEquiv_comm_one :
    (divDivBGGEquiv 1).toModuleIso.hom ≫ (divDivSmoothComplex 𝕜).d 1 (1 + 1) =
      ((divDivBGG 𝕜).smoothData.bgg 2).d 1 (1 + 1) ≫ (divDivBGGEquiv (1 + 1)).toModuleIso.hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun q => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨⟨σ, φ⟩, hx⟩ := (x : (divDivBGG 𝕜).smoothData.Γ (2 < ·) 1)
  apply Subtype.ext
  change (symCurlOp : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (matMulField (deviatoricMat 3) (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜)) =
    matMulField (symMat 3) ((curlOp 3).apply (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) -
      (ofMatrix ddS1).apply (φ : Fin 1 × Fin 3 → (Fin 3 → ℝ) → 𝕜))
  rw [symCurlOp, postComp_apply_eq_matMulField, symCurl_dev σ.2]
  have h0 := matMulField_symMat_elS0 (𝕜 := 𝕜) fun l => (φ : Fin 1 × Fin 3 → (Fin 3 → ℝ) → 𝕜) (0, l)
  rw [← ofMatrix_ddS1_apply] at h0
  funext ij x
  have := congrFun (congrFun h0 ij) x
  simp only [matMulField, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply] at this ⊢
  rw [this, sub_zero]

theorem divDivBGGEquiv_comm_two :
    (divDivBGGEquiv 2).toModuleIso.hom ≫ (divDivSmoothComplex 𝕜).d 2 (2 + 1) =
      ((divDivBGG 𝕜).smoothData.bgg 2).d 2 (2 + 1) ≫ (divDivBGGEquiv (2 + 1)).toModuleIso.hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun q => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨⟨σ, φ⟩, hx⟩ := (x : (divDivBGG 𝕜).smoothData.Γ (2 < ·) 2)
  apply Subtype.ext
  change (divdivOp 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (matMulField (symMat 3) (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜)) =
    fun _ => (divOp 3 1).apply (φ : Fin 1 × Fin 3 → (Fin 3 → ℝ) → 𝕜) 0
  have h := congrArg Subtype.val ((divDivBGG 𝕜).smoothData.mem_bgg_Γ_self.1 hx)
  change (divOp 3 3 : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply
      (σ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → 𝕜) =
    (ofMatrix ddS2).apply (φ : Fin 1 × Fin 3 → (Fin 3 → ℝ) → 𝕜) at h
  rw [divdivOp_symMat σ.2]
  funext u x
  rw [divdivOp_apply_eq_sum_divOp σ.2, divOp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h, ofMatrix_ddS2_apply]

theorem subsingleton_divDivBGG_bgg_X {k : ℤ} (hk : k < 0 ∨ 3 < k) :
    Subsingleton (((divDivBGG 𝕜).smoothData.bgg 2).X k) :=
  have : Subsingleton ((divDivSmoothComplex 𝕜).X k) := subsingleton_divDivSmoothComplex_X hk
  (divDivBGGEquiv k).injective.subsingleton

theorem divDivBGGEquiv_comm (i : ℤ) :
    (divDivBGGEquiv i).toModuleIso.hom ≫ (divDivSmoothComplex 𝕜).d i (i + 1) =
      ((divDivBGG 𝕜).smoothData.bgg 2).d i (i + 1) ≫ (divDivBGGEquiv (i + 1)).toModuleIso.hom := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i < 0 ∨ 2 < i) with rfl | rfl | rfl | hi | hi
  · exact divDivBGGEquiv_comm_zero
  · exact divDivBGGEquiv_comm_one
  · exact divDivBGGEquiv_comm_two
  · have := subsingleton_divDivBGG_bgg_X (𝕜 := 𝕜) (Or.inl hi)
    exact ModuleCat.hom_ext (LinearMap.ext fun q => by
      rw [Subsingleton.elim q 0, map_zero, map_zero])
  · have : Subsingleton ((divDivSmoothComplex 𝕜).X (i + 1)) :=
      subsingleton_divDivSmoothComplex_X (Or.inr (by omega))
    exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

/-- **The BGG complex of the div-div diagram is the div-div complex**: `bgg 2` of `divDivBGG`
is isomorphic to the smooth div-div complex `dev grad → sym curl → div div` on trace-free and
symmetric fields of `Feec.Domain.DivDivComplex` (`divDivOp`, `divDivMat`).
[ArnoldHu2021], §4.3 -/
def divDivBGGIso : (divDivBGG 𝕜).smoothData.bgg 2 ≅ divDivSmoothComplex 𝕜 :=
  HomologicalComplex.Hom.isoOfComponents (fun k => (divDivBGGEquiv k).toModuleIso)
    fun i j hij => by
      obtain rfl : i + 1 = j := hij
      exact divDivBGGEquiv_comm i

/-- **The cohomology of the smooth div-div complex is that of the twisted de Rham complex**
of the div-div diagram. [ArnoldHu2021], §5.2 -/
def divDivSmoothComplexHomologyIso (i : ℤ) :
    (divDivSmoothComplex 𝕜).homology i ≅
      (divDivBGG 𝕜).smoothData.twistComplex.homology i :=
  ((HomologicalComplex.homologyFunctor _ _ i).mapIso divDivBGGIso).symm ≪≫
    divDivBGGHomologyIso i

end DivDiv

end Feec.Domain
