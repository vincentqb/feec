module

public import Feec.Foundation.Tensor
public import Feec.Geometry.Connection
public import Feec.Counterexamples.Curvature
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Ch 2.3–2.4: curvature tensors in components (shim)

Strangler shim over `Feec.Geometry.AlgebraicCurvature` and `Feec.Geometry.Connection`, where
these results hold over any commutative ring (with `2`, resp. `3`, invertible where a factor
is cancelled), any index type, and, for `einstein_zero_iff`, over any field in every dimension
`n ≠ 2`. Every declaration below keeps its old statement and is proved by the new result.

## References

* [QuennevilleBelair2015], Ch. 2, §2.3 (Riemann curvature tensor, Prop 2.1, eqs. (2.2)–(2.4))
  and §2.4 (Einstein's equations)
* [Wald1984], §3.2, §3.3, §4.3
-/

@[expose] public section

open Finset

noncomputable section

namespace Feec.Curvature

section AlgebraicCurvature

variable {ι : Type*}

/-- Total antisymmetrisation, unnormalised (`Feec.CurvatureTensor.alt4`). -/
abbrev alt4 (C : T4 ι) (a b c d : ι) : ℝ := CurvatureTensor.alt4 C a b c d

/-- Shim of `Feec.CurvatureTensor.interchange_of_bianchi`. See [QuennevilleBelair2015, §2.3]. -/
theorem interchange_of_bianchi {C : T4 ι} (hs : PairSkew C) (hb : Bianchi1 C) :
    Interchange C :=
  CurvatureTensor.interchange_of_bianchi hs hb

/-- Shim of `Feec.CurvatureTensor.bianchi_iff`. See [QuennevilleBelair2015, §2.3]. -/
theorem bianchi_iff {C : T4 ι} (hs : PairSkew C) :
    Bianchi1 C ↔ Interchange C ∧ ∀ a b c d, alt4 C a b c d = 0 :=
  CurvatureTensor.bianchi_iff hs

/-- Shim of `Feec.CurvatureTensor.eq_zero_of_symm_bd`. See [QuennevilleBelair2015, §2.3]. -/
theorem eq_zero_of_symm_bd {C : T4 ι} (hs : PairSkew C) (hb : Bianchi1 C)
    (h : ∀ a b c d, C a b c d + C a d c b = 0) : C = 0 :=
  CurvatureTensor.eq_zero_of_symm_bd hs hb h

variable [Fintype ι] [DecidableEq ι]

/-- The scalar deviation form (`Feec.CurvatureTensor.deviationForm`). -/
abbrev deviationForm (C : T4 ι) (Y Tv X : ι → ℝ) : ℝ := CurvatureTensor.deviationForm C Y Tv X

/-- Shim of `Feec.CurvatureTensor.eq_zero_of_deviationForm`.
See [QuennevilleBelair2015, §2.3, after eq. (2.3)]. -/
theorem eq_zero_of_deviation {C : T4 ι} (hs : PairSkew C) (hb : Bianchi1 C)
    (h : ∀ Y Tv X : ι → ℝ, deviationForm C Y Tv X = 0) : C = 0 :=
  CurvatureTensor.eq_zero_of_deviationForm hs hb h

/-- The geodesic deviation (`Feec.CurvatureTensor.deviation`). -/
abbrev deviation (gi : Matrix ι ι ℝ) (C : T4 ι) (X Tv : ι → ℝ) : ι → ℝ :=
  CurvatureTensor.deviation gi C X Tv

/-- Shim of `Feec.CurvatureTensor.deviation_eq_zero_iff`.
See [QuennevilleBelair2015, §2.3, eq. (2.3)]. -/
theorem deviation_eq_zero_iff {C : T4 ι} (hs : PairSkew C) (hb : Bianchi1 C)
    (g gi : Matrix ι ι ℝ) (hinv : g * gi = 1) :
    (∀ X Tv : ι → ℝ, deviation gi C X Tv = 0) ↔ C = 0 :=
  CurvatureTensor.deviation_eq_zero_iff hs hb g gi hinv

omit [DecidableEq ι] in
/-- Shim of `Feec.CurvatureTensor.ricci_isSymm`. See [QuennevilleBelair2015, §2.3]. -/
theorem ricci_symm (gi : Matrix ι ι ℝ) (hgi : gi.IsSymm) {C : T4 ι}
    (hi : Interchange C) (a b : ι) :
    ∑ c, ∑ e, gi c e * C e a c b = ∑ c, ∑ e, gi c e * C e b c a :=
  ((CurvatureTensor.ricci_isSymm hgi hi).apply b a)

/-- Shim of `Feec.Metric.isSymm_of_mul_eq_one`. -/
lemma isSymm_of_mul_eq_one {g gi : Matrix ι ι ℝ} (hg : g.IsSymm)
    (hinv : gi * g = 1) : gi.IsSymm :=
  Metric.isSymm_of_mul_eq_one hg hinv

/-- Shim of `Feec.CurvatureTensor.ricci_isSymm_of_inv`. See [QuennevilleBelair2015, §2.3]. -/
theorem ricci_symm_of_inv (g gi : Matrix ι ι ℝ) (hg : g.IsSymm) (hinv : gi * g = 1)
    {C : T4 ι} (hi : Interchange C) (a b : ι) :
    ∑ c, ∑ e, gi c e * C e a c b = ∑ c, ∑ e, gi c e * C e b c a :=
  ((CurvatureTensor.ricci_isSymm_of_inv hg hinv hi).apply b a)

end AlgebraicCurvature

section Connection

variable {ι : Type*} [Fintype ι]

/-- The coordinate formula (2.2) (`Feec.CurvatureTensor.riemComp`).
See [QuennevilleBelair2015, §2.3, eq. (2.2)]. -/
abbrev riemComp (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ) : T4 ι :=
  CurvatureTensor.riemComp Γ dΓ

/-- Lower the first index (`Feec.CurvatureTensor.lower`). -/
abbrev lower (g : Matrix ι ι ℝ) (R : T4 ι) : T4 ι := CurvatureTensor.lower g R

/-- Shim of `Feec.CurvatureTensor.riemComp_skew`. See [QuennevilleBelair2015, Prop 2.1]. -/
theorem riemComp_skew (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ) (a b c d : ι) :
    riemComp Γ dΓ a b c d = -riemComp Γ dΓ a b d c :=
  CurvatureTensor.riemComp_skew Γ dΓ a b c d

/-- Shim of `Feec.CurvatureTensor.riemComp_bianchi`. See [QuennevilleBelair2015, Prop 2.1]. -/
theorem riemComp_bianchi (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (hdΓ : ∀ e a b c, dΓ e a b c = dΓ e a c b) :
    Bianchi1 (riemComp Γ dΓ) :=
  CurvatureTensor.riemComp_bianchi Γ dΓ hΓ hdΓ

variable [DecidableEq ι]

/-- Shim of `Feec.CurvatureTensor.lower_riemComp_skew`. See [QuennevilleBelair2015, Prop 2.1]. -/
theorem lower_riemComp_skew (g : Matrix ι ι ℝ) (hg : g.IsSymm)
    (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ) (dg : ι → ι → ι → ℝ)
    (ddg : ι → ι → ι → ι → ℝ)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (hdΓ : ∀ e a b c, dΓ e a b c = dΓ e a c b)
    (hcomp : ∀ e a b, dg e a b = ∑ r, (g r b * Γ r e a + g a r * Γ r e b))
    (hcomp' : ∀ f e a b, ddg f e a b =
      ∑ r, (dg f r b * Γ r e a + g r b * dΓ f r e a + dg f a r * Γ r e b + g a r * dΓ f r e b))
    (hddg : ∀ f e a b, ddg f e a b = ddg e f a b) (a b c d : ι) :
    lower g (riemComp Γ dΓ) a b c d = -lower g (riemComp Γ dΓ) b a c d :=
  CurvatureTensor.lower_riemComp_skew g hg Γ dΓ dg ddg hΓ hdΓ hcomp hcomp' hddg a b c d

/-- Shim of `Feec.CurvatureTensor.lower_riemComp_isAlgCurv`.
See [QuennevilleBelair2015, Prop 2.1]. -/
theorem prop_2_1_jet (g : Matrix ι ι ℝ) (hg : g.IsSymm)
    (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ) (dg : ι → ι → ι → ℝ)
    (ddg : ι → ι → ι → ι → ℝ)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (hdΓ : ∀ e a b c, dΓ e a b c = dΓ e a c b)
    (hcomp : ∀ e a b, dg e a b = ∑ r, (g r b * Γ r e a + g a r * Γ r e b))
    (hcomp' : ∀ f e a b, ddg f e a b =
      ∑ r, (dg f r b * Γ r e a + g r b * dΓ f r e a + dg f a r * Γ r e b + g a r * dΓ f r e b))
    (hddg : ∀ f e a b, ddg f e a b = ddg e f a b) :
    PairSkew (lower g (riemComp Γ dΓ)) ∧ Bianchi1 (lower g (riemComp Γ dΓ)) ∧
      Interchange (lower g (riemComp Γ dΓ)) := by
  obtain ⟨hs, hb⟩ :=
    CurvatureTensor.lower_riemComp_isAlgCurv g hg Γ dΓ dg ddg hΓ hdΓ hcomp hcomp' hddg
  exact ⟨hs, hb, CurvatureTensor.interchange_of_bianchi hs hb⟩

end Connection

section ConnectionField

variable {n : ℕ}

/-- Shim of `partialDeriv_comm`. -/
lemma pd_pd_comm (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (i j : Fin n)
    (x : Fin n → ℝ) : pd i (fun y => pd j f y) x = pd j (fun y => pd i f y) x :=
  partialDeriv_comm hf i j x

/-- The Riemann tensor field (`Feec.CurvatureTensor.riemField`). -/
abbrev riemField (Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ) (x : Fin n → ℝ) : T4 (Fin n) :=
  CurvatureTensor.riemField Γ x

/-- Shim of `Feec.CurvatureTensor.riemField_isAlgCurv` (any index type there).
See [QuennevilleBelair2015, Prop 2.1]; cf. [Wald1984, §3.2]. -/
theorem prop_2_1 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (hg : ∀ x, (g x).IsSymm) (hgC : ∀ a b, ContDiff ℝ 2 fun x => g x a b)
    (hΓd : ∀ a b c, Differentiable ℝ fun x => Γ x a b c)
    (hΓ : ∀ x a b c, Γ x a b c = Γ x a c b)
    (hcompat : ∀ x e a b,
      pd e (fun y => g y a b) x = ∑ r, (g x r b * Γ x r e a + g x a r * Γ x r e b))
    (x : Fin n → ℝ) :
    PairSkew (lower (g x) (riemField Γ x)) ∧ Bianchi1 (lower (g x) (riemField Γ x)) ∧
      Interchange (lower (g x) (riemField Γ x)) :=
  CurvatureTensor.riemField_isAlgCurv g Γ hg hgC hΓd hΓ hcompat x

/-- Shim of `Feec.CurvatureTensor.ricci_riemField_isSymm`. See [QuennevilleBelair2015, §2.3]. -/
theorem ricci_field_symm (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (hg : ∀ x, (g x).IsSymm) (hgC : ∀ a b, ContDiff ℝ 2 fun x => g x a b)
    (hΓd : ∀ a b c, Differentiable ℝ fun x => Γ x a b c)
    (hΓ : ∀ x a b c, Γ x a b c = Γ x a c b)
    (hcompat : ∀ x e a b,
      pd e (fun y => g y a b) x = ∑ r, (g x r b * Γ x r e a + g x a r * Γ x r e b))
    (x : Fin n → ℝ) (gi : Matrix (Fin n) (Fin n) ℝ) (hinv : gi * g x = 1) (a b : Fin n) :
    ∑ c, riemField Γ x c a c b = ∑ c, riemField Γ x c b c a :=
  CurvatureTensor.ricci_riemField_isSymm g Γ hg hgC hΓd hΓ hcompat x gi hinv a b

end ConnectionField

section Einstein

variable {n : ℕ}

/-- The Einstein tensor (`Feec.CurvatureTensor.einstein`).
See [QuennevilleBelair2015, §2.3]; cf. [Wald1984, §3.2]. -/
abbrev einstein (g gi Ric : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  CurvatureTensor.einstein g gi Ric

/-- Shim of `Feec.CurvatureTensor.einstein_isSymm`. See [QuennevilleBelair2015, §2.3]. -/
theorem einstein_symm (g gi Ric : Matrix (Fin n) (Fin n) ℝ) (hg : g.IsSymm)
    (hRic : Ric.IsSymm) : (einstein g gi Ric).IsSymm :=
  CurvatureTensor.einstein_isSymm hg hRic

/-- Shim of `Feec.CurvatureTensor.einstein_eq_zero_iff` (any field, any `n ≠ 2` there).
See [QuennevilleBelair2015, §2.4]; cf. [Wald1984, §4.3]. -/
theorem einstein_zero_iff (hn : n ≠ 2) (g gi Ric : Matrix (Fin n) (Fin n) ℝ)
    (hinv : gi * g = 1) : einstein g gi Ric = 0 ↔ Ric = 0 :=
  CurvatureTensor.einstein_eq_zero_iff (by simpa using (by exact_mod_cast hn : (n : ℝ) ≠ 2))
    g gi Ric hinv

/-- Shim of `Feec.Counterexamples.Curvature.exists_einstein_eq_zero_ne_zero_two`.
See [QuennevilleBelair2015, §2.4]. -/
theorem einstein_zero_iff_fails_two :
    ∃ g gi Ric : Matrix (Fin 2) (Fin 2) ℝ, gi * g = 1 ∧ einstein g gi Ric = 0 ∧ Ric ≠ 0 :=
  Counterexamples.Curvature.exists_einstein_eq_zero_ne_zero_two

end Einstein

section Dimension

/-- Shim (`Feec.CurvatureTensor.bivPair`). -/
abbrev bivPair : Fin 6 → Fin 4 × Fin 4 := CurvatureTensor.bivPair

/-- Shim (`Feec.CurvatureTensor.bivForm`). -/
abbrev bivForm (I : Fin 6) (a b : Fin 4) : ℝ := CurvatureTensor.bivForm I a b

lemma bivForm_swap (I : Fin 6) (a b : Fin 4) : bivForm I b a = -bivForm I a b :=
  CurvatureTensor.bivForm_swap I a b

lemma sum_bivForm (X : Fin 4 → Fin 4 → ℝ) (hX : ∀ a b, X a b = -X b a) (a b : Fin 4) :
    ∑ I, bivForm I a b * X (bivPair I).1 (bivPair I).2 = X a b :=
  CurvatureTensor.sum_bivForm X hX a b

lemma alt4_swap12 (C : T4 (Fin 4)) (a b c d : Fin 4) : alt4 C b a c d = -alt4 C a b c d :=
  CurvatureTensor.alt4_swap12 C a b c d

lemma alt4_swap23 (C : T4 (Fin 4)) (a b c d : Fin 4) : alt4 C a c b d = -alt4 C a b c d :=
  CurvatureTensor.alt4_swap23 C a b c d

lemma alt4_swap34 (C : T4 (Fin 4)) (a b c d : Fin 4) : alt4 C a b d c = -alt4 C a b c d :=
  CurvatureTensor.alt4_swap34 C a b c d

/-- Shim of `Feec.CurvatureTensor.alt4_all_iff`. -/
theorem alt4_all_iff (C : T4 (Fin 4)) :
    (∀ a b c d, alt4 C a b c d = 0) ↔ alt4 C 0 1 2 3 = 0 :=
  CurvatureTensor.alt4_all_iff C

lemma alt4_eq_of_interchange {C : T4 (Fin 4)} (hs : PairSkew C) (hi : Interchange C) :
    alt4 C 0 1 2 3 = 8 * (C 0 1 2 3 + C 0 2 3 1 + C 0 3 1 2) :=
  CurvatureTensor.alt4_eq_of_interchange hs hi

/-- Shim (`Feec.CurvatureTensor.recon`). -/
abbrev recon (M : Fin 6 → Fin 6 → ℝ) : T4 (Fin 4) := CurvatureTensor.recon M

/-- Shim (`Feec.CurvatureTensor.bivMat`). -/
abbrev bivMat (C : T4 (Fin 4)) : Fin 6 → Fin 6 → ℝ := CurvatureTensor.bivMat C

lemma bivForm_pair (I J : Fin 6) :
    bivForm I (bivPair J).1 (bivPair J).2 = if I = J then 1 else 0 :=
  CurvatureTensor.bivForm_pair I J

lemma recon_pair (M : Fin 6 → Fin 6 → ℝ) (I J : Fin 6) :
    recon M (bivPair I).1 (bivPair I).2 (bivPair J).1 (bivPair J).2 = M I J :=
  CurvatureTensor.recon_pair M I J

lemma recon_pairSkew (M : Fin 6 → Fin 6 → ℝ) : PairSkew (recon M) :=
  CurvatureTensor.recon_pairSkew M

lemma recon_interchange (M : Fin 6 → Fin 6 → ℝ) (hM : ∀ I J, M I J = M J I) :
    Interchange (recon M) :=
  CurvatureTensor.recon_interchange M hM

lemma eq_recon {C : T4 (Fin 4)} (hs : PairSkew C) : C = recon (bivMat C) :=
  CurvatureTensor.eq_recon hs

/-- The algebraic curvature tensors (`Feec.CurvatureTensor.algCurv`, any commutative ring). -/
abbrev algCurv (ι : Type*) : Submodule ℝ (T4 ι) := CurvatureTensor.algCurv ι ℝ

/-- Shim (`Feec.CurvatureTensor.parMat`). -/
abbrev parMat (p : Fin 20 → ℝ) : Fin 6 → Fin 6 → ℝ := CurvatureTensor.parMat p

/-- Shim (`Feec.CurvatureTensor.parIdx`). -/
abbrev parIdx : Fin 20 → Fin 6 × Fin 6 := CurvatureTensor.parIdx

lemma parMat_symm (p : Fin 20 → ℝ) (I J : Fin 6) : parMat p I J = parMat p J I :=
  CurvatureTensor.parMat_symm p I J

lemma recon_parMat_mem (p : Fin 20 → ℝ) : recon (parMat p) ∈ algCurv (Fin 4) :=
  CurvatureTensor.recon_parMat_mem p

/-- Shim (`Feec.CurvatureTensor.algCurvEquiv`). See [QuennevilleBelair2015, §2.3]. -/
def algCurvEquiv : algCurv (Fin 4) ≃ₗ[ℝ] (Fin 20 → ℝ) := CurvatureTensor.algCurvEquiv

/-- Shim of `Feec.CurvatureTensor.finrank_algCurv_four`. See [QuennevilleBelair2015, §2.3]. -/
theorem finrank_algCurv_four : Module.finrank ℝ (algCurv (Fin 4)) = 20 :=
  CurvatureTensor.finrank_algCurv_four

end Dimension

end Feec.Curvature
