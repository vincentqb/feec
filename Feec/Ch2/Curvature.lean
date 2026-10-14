import Feec.Foundation

/-!
# Ch 2.3–2.4: curvature tensors in components

Component-level (`T4 ι = ι → ι → ι → ι → ℝ`) algebra behind thesis §2.3–§2.4, filling the
results the thesis states without proof.

* `interchange_of_bianchi`, `bianchi_iff`: the lemma cited from [10] (Frauendiener): for
  pair-skew `C`, Bianchi ⇔ interchange ∧ `C_[abcd] = 0`.
* `eq_zero_of_symm_bd`, `eq_zero_of_deviation`, `deviation_eq_zero_iff`: the algebraic
  core of the unproved "iff" after the geodesic-deviation equation (2.3).
* `riemComp_skew`, `riemComp_bianchi`, `lower_riemComp_skew`, `prop_2_1_jet`, `prop_2_1`:
  Prop 2.1 (corrected) for the coordinate formula (2.2) of a torsion-free metric-compatible
  connection, at the jet level and for `C²` fields on `ℝⁿ`.
* `ricci_symm`, `ricci_symm_of_inv`, `ricci_field_symm`: symmetry of the Ricci tensor,
  abstractly and for the curvature (2.2) of the Levi-Civita connection; `einstein_symm`.
* `einstein_zero_iff`: vacuum `G = 0 ⇔ Ric = 0` for every `n ≠ 2` (the thesis' `n = 4`
  included); `einstein_zero_iff_fails_two` shows the hypothesis is needed.
* `algCurvEquiv`, `finrank_algCurv_four`: the component count `n²(n²−1)/12 = 20` for `n = 4`.

Not formalized: the geometric derivation of (2.3) and the existence of geodesic families
realizing given `T, X` (cited background); the differential Bianchi identity (2.4); the
count `n²(n²−1)/12` for general `n`. The thesis definition `R^a_bcd v^b := ∇_[c∇_d] v^a`
carries a spurious factor `½` relative to (2.2); we work with (2.2) (the commutator
convention) throughout.

Everything lives in `Feec.Curvature` to avoid clashes with other chapters.
-/

open Finset

noncomputable section

namespace Feec.Curvature

section AlgebraicCurvature

variable {ι : Type*}

/-- Total antisymmetrisation of `C` in its four slots, unnormalised (24 signed terms),
so `alt4 C a b c d = 24 C_[abcd]`. -/
def alt4 (C : T4 ι) (a b c d : ι) : ℝ :=
  C a b c d - C a b d c - C a c b d + C a c d b + C a d b c - C a d c b
  - C b a c d + C b a d c + C b c a d - C b c d a - C b d a c + C b d c a
  + C c a b d - C c a d b - C c b a d + C c b d a + C c d a b - C c d b a
  - C d a b c + C d a c b + C d b a c - C d b c a - C d c a b + C d c b a

/-- Thesis §2.3 (claim cited from [10]), forward half: pair skew-symmetry and the first
Bianchi identity imply the interchange symmetry `C_abcd = C_cdab`.

Thesis gap: the thesis gives no proof, only the citation. Here: add the Bianchi identity
at `(a,b,c,d)`, `(b,c,d,a)`, `(c,d,a,b)`, `(d,a,b,c)` and use pair skew. -/
theorem interchange_of_bianchi {C : T4 ι} (hs : PairSkew C) (hb : Bianchi1 C) :
    Interchange C := by
  intro a b c d
  have h1 := hb a b c d; have h2 := hb b c d a; have h3 := hb c d a b; have h4 := hb d a b c
  have := hs a b c d; have := hs a c d b; have := hs a d b c; have := hs b c d a
  have := hs b d a c; have := hs b a c d; have := hs c d a b; have := hs c a b d
  have := hs c b d a; have := hs d a b c; have := hs d b c a; have := hs d c a b
  have := hs a c b d; have := hs b d c a; have := hs c a d b; have := hs d b a c
  linarith

/-- Thesis §2.3 (claim cited from [10]): for `C` skew in each pair, `C` satisfies the first
Bianchi identity `C_a[bcd] = 0` iff it has the interchange symmetry and vanishing totally
antisymmetric part `C_[abcd] = 0`.

Thesis gap: stated by citation only; proved here. Under pair skew and interchange, the
24 terms of `alt4` fall into three classes of eight, so `alt4 C a b c d = 8 (C_abcd +
C_acdb + C_adbc)`. -/
theorem bianchi_iff {C : T4 ι} (hs : PairSkew C) :
    Bianchi1 C ↔ Interchange C ∧ ∀ a b c d, alt4 C a b c d = 0 := by
  constructor
  · intro hb
    have hi := interchange_of_bianchi hs hb
    refine ⟨hi, fun a b c d => ?_⟩
    unfold alt4
    have := hb a b c d; have := hb b a c d; have := hb c a b d; have := hb d a b c
    have := hs a b c d; have := hs a c b d; have := hs a d b c; have := hs a b d c
    have := hs a c d b; have := hs a d c b
    have := hi a b c d; have := hi a b d c; have := hi a c b d; have := hi a c d b
    have := hi a d b c; have := hi a d c b; have := hi b a c d; have := hi b a d c
    have := hi b c a d; have := hi b c d a; have := hi b d a c; have := hi b d c a
    have := hs b c a d; have := hs b d a c; have := hs c d a b; have := hs c b a d
    have := hs d b a c; have := hs d c a b; have := hs b a d c; have := hs c a d b
    have := hs d a c b; have := hs b c d a; have := hs b d c a
    linarith
  · rintro ⟨hi, ha⟩ a b c d
    have h := ha a b c d
    unfold alt4 at h
    have := hs a b c d; have := hs a c b d; have := hs a d b c; have := hs a b d c
    have := hs a c d b; have := hs a d c b
    have := hi a b c d; have := hi a b d c; have := hi a c b d; have := hi a c d b
    have := hi a d b c; have := hi a d c b; have := hi b a c d; have := hi b a d c
    have := hi b c a d; have := hi b c d a; have := hi b d a c; have := hi b d c a
    have := hs b c a d; have := hs b d a c; have := hs c d a b; have := hs c b a d
    have := hs d b a c; have := hs d c a b; have := hs b a d c; have := hs c a d b
    have := hs d a c b; have := hs b c d a; have := hs b d c a
    linarith

/-- Thesis §2.3, geodesic deviation (2.3), polarized algebraic core: an algebraic curvature
tensor (pair skew + first Bianchi) that is skew under the swap `b ↔ d` vanishes.

Proof: the swap symmetry and pair skew give `2 C_abcd = C_acbd`; applied twice,
`4 C_abcd = C_abcd`. -/
theorem eq_zero_of_symm_bd {C : T4 ι} (hs : PairSkew C) (hb : Bianchi1 C)
    (h : ∀ a b c d, C a b c d + C a d c b = 0) : C = 0 := by
  -- `2 C_abcd = C_acbd` for all indices
  have key : ∀ a b c d, 2 * C a b c d = C a c b d := by
    intro a b c d
    have := hb a b c d; have := h a c d b; have := h a d b c
    have := hs a c d b; have := hs a d b c; have := hs a c b d; have := hs a b d c
    have := hs a d c b; have := hs a b c d
    linarith
  funext a b c d
  have := key a b c d; have := key a c b d
  simp only [Pi.zero_apply]
  linarith

variable [Fintype ι] [DecidableEq ι]

/-- The scalar deviation form `C(Y, T, X, T) = C_abcd Y^a T^b X^c T^d`. -/
def deviationForm (C : T4 ι) (Y Tv X : ι → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, C a b c d * Y a * Tv b * X c * Tv d

/-- Thesis §2.3, after (2.3): "initially parallel geodesics fail to remain so iff the
Riemann tensor does not vanish", algebraic core. If an algebraic curvature tensor `C`
satisfies `C(Y, T, X, T) = 0` for all `Y, T, X`, then `C = 0`.

Thesis gap: the "iff" is asserted without proof. Here: polarize in `T` at `e_b + e_d`
to get `C_abcd + C_adcb = 0`, then apply `eq_zero_of_symm_bd`. (The geometric step,
realizing given `T, X` at a point by a family of geodesics, is not formalized.) -/
theorem eq_zero_of_deviation {C : T4 ι} (hs : PairSkew C) (hb : Bianchi1 C)
    (h : ∀ Y Tv X : ι → ℝ, deviationForm C Y Tv X = 0) : C = 0 := by
  apply eq_zero_of_symm_bd hs hb
  intro a b c d
  -- the quadratic form in `T` with `Y = e_a`, `X = e_c`
  have hQ : ∀ Tv : ι → ℝ, ∑ b, ∑ d, C a b c d * Tv b * Tv d = 0 := by
    intro Tv
    have := h (Pi.single a 1) Tv (Pi.single c 1)
    simpa [deviationForm, Pi.single_apply, mul_ite, ite_mul, Finset.sum_ite_eq'] using this
  -- bilinear expansion
  have hB : ∀ u v : ι → ℝ, ∑ b, ∑ d, C a b c d * (u + v) b * (u + v) d =
      ∑ b, ∑ d, C a b c d * u b * u d + ∑ b, ∑ d, C a b c d * u b * v d
      + ∑ b, ∑ d, C a b c d * v b * u d + ∑ b, ∑ d, C a b c d * v b * v d := by
    intro u v
    simp only [← Finset.sum_add_distrib, Pi.add_apply]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hE : ∀ i j, ∑ b, ∑ d, C a b c d * (Pi.single i 1 : ι → ℝ) b * (Pi.single j 1 : ι → ℝ) d
      = C a i c j := by
    intro i j
    simp [Pi.single_apply]
  have := hB (Pi.single b 1 : ι → ℝ) (Pi.single d 1)
  simp only [hQ, hE] at this
  linarith

/-- Raise the first index of `C` with the inverse metric `gi` and form the geodesic
deviation (2.3): `a^a = -R^a_cbd X^b T^c T^d`. -/
def deviation (gi : Matrix ι ι ℝ) (C : T4 ι) (X Tv : ι → ℝ) : ι → ℝ :=
  fun a => -∑ e, gi a e * ∑ c, ∑ b, ∑ d, C e c b d * X b * Tv c * Tv d

/-- Thesis §2.3, after (2.3), corrected and proved at the algebraic level: for an
algebraic curvature tensor `C` and an invertible inverse metric `gi`, all geodesic
deviations `a^a = -R^a_cbd X^b T^c T^d` vanish iff `C = 0`.

Thesis gap: the "iff" was asserted without proof (see `eq_zero_of_deviation`). -/
theorem deviation_eq_zero_iff {C : T4 ι} (hs : PairSkew C) (hb : Bianchi1 C)
    (g gi : Matrix ι ι ℝ) (hinv : g * gi = 1) :
    (∀ X Tv : ι → ℝ, deviation gi C X Tv = 0) ↔ C = 0 := by
  constructor
  · intro h
    apply eq_zero_of_deviation hs hb
    intro Y Tv X
    -- the lowered deviation vector vanishes
    have hv : ∀ e, ∑ c, ∑ b, ∑ d, C e c b d * X b * Tv c * Tv d = 0 := by
      have h0 : gi.mulVec (fun e => ∑ c, ∑ b, ∑ d, C e c b d * X b * Tv c * Tv d) = 0 := by
        funext a
        have := congrFun (h X Tv) a
        simp only [deviation, Pi.zero_apply, neg_eq_zero] at this
        simpa [Matrix.mulVec, dotProduct] using this
      intro e
      have := congrArg g.mulVec h0
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact congrFun this e
    unfold deviationForm
    refine Finset.sum_eq_zero fun a _ => ?_
    have := hv a
    calc ∑ b, ∑ c, ∑ d, C a b c d * Y a * Tv b * X c * Tv d
        = Y a * ∑ b, ∑ c, ∑ d, C a b c d * X c * Tv b * Tv d := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun _ _ => ?_
          ring
      _ = 0 := by rw [this, mul_zero]
  · rintro rfl X Tv
    funext a
    simp [deviation]

omit [DecidableEq ι] in
/-- Thesis §2.3: the Ricci tensor `R_ab = R^c_acb = g^{ce} R_eacb` is symmetric.

Formalization note: here `gi` is an arbitrary matrix, so its symmetry is assumed (`hgi`);
for the actual inverse of a symmetric metric this is automatic, see `ricci_symm_of_inv`. -/
theorem ricci_symm (gi : Matrix ι ι ℝ) (hgi : gi.IsSymm) {C : T4 ι}
    (hi : Interchange C) (a b : ι) :
    ∑ c, ∑ e, gi c e * C e a c b = ∑ c, ∑ e, gi c e * C e b c a := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hi e a c b, ← hgi.apply c e]

/-- A left inverse of a symmetric matrix is symmetric. -/
lemma isSymm_of_mul_eq_one {g gi : Matrix ι ι ℝ} (hg : g.IsSymm)
    (hinv : gi * g = 1) : gi.IsSymm := by
  have h1 : g * gi.transpose = 1 := by
    rw [← hg.eq, ← Matrix.transpose_mul, hinv, Matrix.transpose_one]
  unfold Matrix.IsSymm
  calc gi.transpose = (gi * g) * gi.transpose := by rw [hinv, Matrix.one_mul]
    _ = gi * (g * gi.transpose) := Matrix.mul_assoc _ _ _
    _ = gi := by rw [h1, Matrix.mul_one]

/-- Thesis §2.3: the Ricci tensor `R_ab = g^{ce} R_eacb` is symmetric, for `g` symmetric with
inverse `gi` and `C` having the interchange symmetry. -/
theorem ricci_symm_of_inv (g gi : Matrix ι ι ℝ) (hg : g.IsSymm) (hinv : gi * g = 1)
    {C : T4 ι} (hi : Interchange C) (a b : ι) :
    ∑ c, ∑ e, gi c e * C e a c b = ∑ c, ∑ e, gi c e * C e b c a :=
  ricci_symm gi (isSymm_of_mul_eq_one hg hinv) hi a b

end AlgebraicCurvature

section Connection

/-! ### Prop 2.1 at the jet level: the Riemann tensor of formula (2.2)

Index conventions: `Γ a b c = Γ^a_{bc}`, `dΓ e a b c = ∂_e Γ^a_{bc}`, `dg e a b = ∂_e g_ab`,
`ddg f e a b = ∂_f ∂_e g_ab`, and `riemComp Γ dΓ a b c d = R^a_{bcd}`. -/

variable {ι : Type*} [Fintype ι]

/-- The coordinate formula (2.2): `R^α_{μβν} = ∂_β Γ^α_{μν} − ∂_ν Γ^α_{μβ}
+ Γ^α_{γβ} Γ^γ_{μν} − Γ^α_{γν} Γ^γ_{μβ}`, from the values of `Γ` and `∂Γ` at a point. -/
def riemComp (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ) : T4 ι :=
  fun a b c d => dΓ c a b d - dΓ d a b c + ∑ e, (Γ a e c * Γ e b d - Γ a e d * Γ e b c)

/-- Lower the first index with the metric: `R_abcd = g_ae R^e_bcd`. -/
def lower (g : Matrix ι ι ℝ) (R : T4 ι) : T4 ι := fun a b c d => ∑ e, g a e * R e b c d

/-- Thesis Prop 2.1, skew-symmetry in the second pair, for formula (2.2) (any connection). -/
theorem riemComp_skew (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ) (a b c d : ι) :
    riemComp Γ dΓ a b c d = -riemComp Γ dΓ a b d c := by
  simp only [riemComp]
  have : ∑ e, (Γ a e c * Γ e b d - Γ a e d * Γ e b c)
      = -∑ e, (Γ a e d * Γ e b c - Γ a e c * Γ e b d) := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun _ _ => by ring
  linarith

/-- Thesis Prop 2.1, first Bianchi identity `R^a_{[bcd]} = 0`, for formula (2.2) with a
torsion-free connection (`Γ` and `∂Γ` symmetric in the lower indices); no metric is used.

Correction: the thesis proof concludes with `R_[abcd] v^b = 0` (a four-index
antisymmetrisation, which is not the Bianchi identity) and calls `v` a vector where a
1-form is meant. The correct statement is `R^a_{[bcd]} = 0`, proved here directly. -/
theorem riemComp_bianchi (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (hdΓ : ∀ e a b c, dΓ e a b c = dΓ e a c b) :
    Bianchi1 (riemComp Γ dΓ) := by
  intro a b c d
  simp only [riemComp]
  have hs : ∑ e, (Γ a e c * Γ e b d - Γ a e d * Γ e b c)
      + ∑ e, (Γ a e d * Γ e c b - Γ a e b * Γ e c d)
      + ∑ e, (Γ a e b * Γ e d c - Γ a e c * Γ e d b) = 0 := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_eq_zero fun e _ => ?_
    rw [hΓ e c b, hΓ e d c, hΓ e d b]; ring
  have := hdΓ c a b d; have := hdΓ d a b c; have := hdΓ b a c d
  linarith

private lemma sum_sum_eq_zero_of_antisymm (Q : ι → ι → ℝ) (hQ : ∀ r s, Q r s = -Q s r) :
    ∑ r, ∑ s, Q r s = 0 := by
  have h : ∑ r, ∑ s, Q r s = -∑ r, ∑ s, Q r s := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    exact sum_congr rfl fun r _ => sum_congr rfl fun s _ => hQ s r
  linarith

/-- Thesis Prop 2.1, skew-symmetry in the first pair `R_abcd = −R_bacd`, at the jet level.

Hypotheses: `g` symmetric; metric compatibility `∇g = 0` written at first order
(`hcomp`: `∂_e g_ab = g_rb Γ^r_ea + g_ar Γ^r_eb`) and its derivative (`hcomp'`, the
product rule applied to `hcomp`); symmetry of second derivatives (`hddg`, Schwarz); and a
torsion-free connection. This is the thesis' argument `0 = [∇_c, ∇_d] g_ab`.

Thesis gap: the thesis uses the action of the commutator on (0,2)-tensors without
deriving it, and (as far as the extracted text shows) its display carries a factor `2`
inconsistent with the `∇_[c∇_d]` definition and `+` signs where the (0,2) commutator gives
`−`; here the identity is proved from (2.2) directly. -/
theorem lower_riemComp_skew (g : Matrix ι ι ℝ) (hg : g.IsSymm)
    (Γ : ι → ι → ι → ℝ) (dΓ : ι → ι → ι → ι → ℝ) (dg : ι → ι → ι → ℝ)
    (ddg : ι → ι → ι → ι → ℝ)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (hdΓ : ∀ e a b c, dΓ e a b c = dΓ e a c b)
    (hcomp : ∀ e a b, dg e a b = ∑ r, (g r b * Γ r e a + g a r * Γ r e b))
    (hcomp' : ∀ f e a b, ddg f e a b =
      ∑ r, (dg f r b * Γ r e a + g r b * dΓ f r e a + dg f a r * Γ r e b + g a r * dΓ f r e b))
    (hddg : ∀ f e a b, ddg f e a b = ddg e f a b) (a b c d : ι) :
    lower g (riemComp Γ dΓ) a b c d = -lower g (riemComp Γ dΓ) b a c d := by
  have gs : ∀ i j, g i j = g j i := fun i j => hg.apply j i
  -- derivative terms, via the derivative of metric compatibility and Schwarz
  have hD : ∑ e, g a e * (dΓ c e b d - dΓ d e b c) + ∑ e, g b e * (dΓ c e a d - dΓ d e a c)
      = -∑ r, (dg c r b * Γ r d a - dg d r b * Γ r c a + dg c a r * Γ r d b
        - dg d a r * Γ r c b) := by
    have h0 : ddg c d a b - ddg d c a b = 0 := by rw [hddg]; ring
    rw [hcomp' c d a b, hcomp' d c a b, ← sum_sub_distrib] at h0
    rw [eq_neg_iff_add_eq_zero, ← h0, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [hdΓ c r d a, hdΓ d r c a, hdΓ c r d b, hdΓ d r c b, gs r b]; ring
  -- first-derivative terms, via metric compatibility; the `g_rs` part cancels by symmetry
  have hQ : ∑ r, (dg c r b * Γ r d a - dg d r b * Γ r c a + dg c a r * Γ r d b
        - dg d a r * Γ r c b) = ∑ r, ∑ s,
      (g s b * Γ s c r * Γ r d a - g s b * Γ s d r * Γ r c a + g a s * Γ s c r * Γ r d b
        - g a s * Γ s d r * Γ r c b) := by
    have hz := sum_sum_eq_zero_of_antisymm (fun r s =>
      g r s * Γ s c b * Γ r d a - g r s * Γ s d b * Γ r c a + g s r * Γ s c a * Γ r d b
        - g s r * Γ s d a * Γ r c b) (fun r s => by rw [gs r s]; ring)
    rw [← sub_eq_zero, ← hz, ← sum_sub_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [hcomp c r b, hcomp d r b, hcomp c a r, hcomp d a r]
    simp only [sum_mul, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun s _ => ?_
    ring
  -- quadratic terms of (2.2)
  have hG : ∑ e, g a e * ∑ r, (Γ e r c * Γ r b d - Γ e r d * Γ r b c)
      + ∑ e, g b e * ∑ r, (Γ e r c * Γ r a d - Γ e r d * Γ r a c) = ∑ r, ∑ s,
      (g s b * Γ s c r * Γ r d a - g s b * Γ s d r * Γ r c a + g a s * Γ s c r * Γ r d b
        - g a s * Γ s d r * Γ r c b) := by
    rw [Finset.sum_comm (f := fun r s => _)]
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun s _ => sum_congr rfl fun r _ => ?_
    rw [hΓ s r c, hΓ s r d, hΓ r b d, hΓ r b c, hΓ r a d, hΓ r a c, gs s b]; ring
  simp only [lower, riemComp, mul_add, sum_add_distrib]
  linarith

/-- Thesis Prop 2.1 (jet level, corrected): for a torsion-free metric-compatible
connection, the lowered Riemann tensor (2.2) is skew in each pair and satisfies the first
Bianchi identity; hence (by `interchange_of_bianchi`) it also has the interchange
symmetry. -/
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
  have hs : PairSkew (lower g (riemComp Γ dΓ)) := fun a b c d =>
    ⟨lower_riemComp_skew g hg Γ dΓ dg ddg hΓ hdΓ hcomp hcomp' hddg a b c d, by
      simp only [lower, ← sum_neg_distrib]
      exact sum_congr rfl fun e _ => by rw [riemComp_skew Γ dΓ e b c d]; ring⟩
  have hb : Bianchi1 (lower g (riemComp Γ dΓ)) := by
    intro a b c d
    simp only [lower, ← sum_add_distrib, ← mul_add]
    refine sum_eq_zero fun e _ => ?_
    rw [riemComp_bianchi Γ dΓ hΓ hdΓ e b c d, mul_zero]
  exact ⟨hs, hb, interchange_of_bianchi hs hb⟩

end Connection

section ConnectionField

/-! ### Prop 2.1 for fields on `ℝⁿ`

The jet-level hypotheses of `prop_2_1_jet` are discharged for a `C²` metric field and a
differentiable, torsion-free, metric-compatible connection field (the Levi-Civita
connection), with derivatives `pd` (Fréchet derivative along coordinate vectors). -/

variable {n : ℕ}

private lemma pd_fun_sum {κ : Type*} (s : Finset κ) (F : κ → (Fin n → ℝ) → ℝ) (i : Fin n)
    (x : Fin n → ℝ) (h : ∀ k ∈ s, DifferentiableAt ℝ (F k) x) :
    pd i (fun y => ∑ k ∈ s, F k y) x = ∑ k ∈ s, pd i (F k) x := by
  simp [pd, fderiv_fun_sum h]

private lemma pd_fun_add (f g : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y + g y) x = pd i f x + pd i g x := by
  simp [pd, fderiv_fun_add hf hg]

private lemma pd_fun_mul (f g : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x := by
  simp [pd, fderiv_fun_mul hf hg]; ring

/-- Schwarz: coordinate partial derivatives of a `C²` function commute. -/
lemma pd_pd_comm (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (i j : Fin n)
    (x : Fin n → ℝ) : pd i (fun y => pd j f y) x = pd j (fun y => pd i f y) x := by
  have hd : ∀ y, DifferentiableAt ℝ (fderiv ℝ f) y := fun y =>
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  have key : ∀ k l, pd k (fun y => pd l f y) x
      = fderiv ℝ (fderiv ℝ f) x (Pi.single k 1) (Pi.single l 1) := by
    intro k l
    simp only [pd]
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [key, key]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- The Riemann tensor field `R^a_bcd(x)` of a connection field `Γ`, by formula (2.2). -/
def riemField (Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ) (x : Fin n → ℝ) : T4 (Fin n) :=
  riemComp (Γ x) (fun e a b c => pd e (fun y => Γ y a b c) x)

/-- Thesis Prop 2.1 (corrected, see `riemComp_bianchi`, `lower_riemComp_skew`): for a `C²`
symmetric metric field `g` on `ℝⁿ` and a differentiable connection `Γ` that is torsion-free
and metric-compatible (i.e. the Levi-Civita connection), the lowered Riemann tensor
`R_abcd = g_ae R^e_bcd` of (2.2) satisfies `R_abcd = −R_bacd = −R_abdc`, the first Bianchi
identity `R_a[bcd] = 0`, and the interchange symmetry `R_abcd = R_cdab`. -/
theorem prop_2_1 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (hg : ∀ x, (g x).IsSymm) (hgC : ∀ a b, ContDiff ℝ 2 fun x => g x a b)
    (hΓd : ∀ a b c, Differentiable ℝ fun x => Γ x a b c)
    (hΓ : ∀ x a b c, Γ x a b c = Γ x a c b)
    (hcompat : ∀ x e a b,
      pd e (fun y => g y a b) x = ∑ r, (g x r b * Γ x r e a + g x a r * Γ x r e b))
    (x : Fin n → ℝ) :
    PairSkew (lower (g x) (riemField Γ x)) ∧ Bianchi1 (lower (g x) (riemField Γ x)) ∧
      Interchange (lower (g x) (riemField Γ x)) := by
  have hgd : ∀ a b, Differentiable ℝ fun x => g x a b := fun a b =>
    (hgC a b).differentiable (by norm_num)
  have hdg : ∀ e a b, Differentiable ℝ fun y => pd e (fun z => g z a b) y := by
    intro e a b
    have : (fun y => pd e (fun z => g z a b) y)
        = fun y => ∑ r, (g y r b * Γ y r e a + g y a r * Γ y r e b) := funext fun y =>
      hcompat y e a b
    rw [this]
    fun_prop
  refine prop_2_1_jet (g x) (hg x) (Γ x) (fun e a b c => pd e (fun y => Γ y a b c) x)
    (fun e a b => pd e (fun y => g y a b) x)
    (fun f e a b => pd f (fun y => pd e (fun z => g z a b) y) x) (hΓ x) ?_ (hcompat x) ?_ ?_
  · intro e a b c
    show pd e _ x = pd e _ x
    congr 1
    exact funext fun y => hΓ y a b c
  · intro f e a b
    have : (fun y => pd e (fun z => g z a b) y)
        = fun y => ∑ r, (g y r b * Γ y r e a + g y a r * Γ y r e b) := funext fun y =>
      hcompat y e a b
    rw [this, pd_fun_sum _ _ _ _ (fun r _ => by fun_prop)]
    refine sum_congr rfl fun r _ => ?_
    rw [pd_fun_add _ _ _ _ (by fun_prop) (by fun_prop),
      pd_fun_mul _ _ _ _ (by fun_prop) (by fun_prop),
      pd_fun_mul _ _ _ _ (by fun_prop) (by fun_prop)]
    ring
  · intro f e a b
    exact pd_pd_comm _ (hgC a b) f e x

/-- Thesis §2.3, "the Ricci tensor is symmetric", for the actual curvature (2.2) of the
Levi-Civita connection: under the hypotheses of `prop_2_1` and an inverse `gi` of `g x`,
the Ricci tensor `R_ab = R^c_acb` of `riemField Γ x` is symmetric.

Proof: `R^c_acb = g^{ce} R_eacb` (as `gi * g = 1`), then `ricci_symm_of_inv` with the
interchange symmetry from `prop_2_1`. -/
theorem ricci_field_symm (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (hg : ∀ x, (g x).IsSymm) (hgC : ∀ a b, ContDiff ℝ 2 fun x => g x a b)
    (hΓd : ∀ a b c, Differentiable ℝ fun x => Γ x a b c)
    (hΓ : ∀ x a b c, Γ x a b c = Γ x a c b)
    (hcompat : ∀ x e a b,
      pd e (fun y => g y a b) x = ∑ r, (g x r b * Γ x r e a + g x a r * Γ x r e b))
    (x : Fin n → ℝ) (gi : Matrix (Fin n) (Fin n) ℝ) (hinv : gi * g x = 1) (a b : Fin n) :
    ∑ c, riemField Γ x c a c b = ∑ c, riemField Γ x c b c a := by
  have hraise : ∀ a b, ∑ c, ∑ e, gi c e * lower (g x) (riemField Γ x) e a c b
      = ∑ c, riemField Γ x c a c b := by
    intro a b
    refine sum_congr rfl fun c _ => ?_
    simp only [lower, mul_sum]
    rw [Finset.sum_comm]
    have hcf : ∀ f, ∑ e, gi c e * (g x e f) = (1 : Matrix (Fin n) (Fin n) ℝ) c f := by
      intro f; rw [← hinv]; rfl
    calc ∑ f, ∑ e, gi c e * (g x e f * riemField Γ x f a c b)
        = ∑ f, (1 : Matrix (Fin n) (Fin n) ℝ) c f * riemField Γ x f a c b := by
          refine sum_congr rfl fun f _ => ?_
          rw [← hcf f, sum_mul]
          exact sum_congr rfl fun e _ => by ring
      _ = riemField Γ x c a c b := by simp [Matrix.one_apply]
  rw [← hraise a b, ← hraise b a]
  exact ricci_symm_of_inv (g x) gi (hg x) hinv
    (prop_2_1 g Γ hg hgC hΓd hΓ hcompat x).2.2 a b

end ConnectionField

section Einstein

variable {n : ℕ}

/-- The Einstein tensor `G = Ric - ½ (tr_g Ric) g` in matrix form, `tr_g Ric = tr(g⁻¹ Ric)`.
(Thesis §2.3 writes `G_ab = R_ac − ½ g_ac R`, an index typo for `R_ab − ½ g_ab R`.) -/
def einstein (g gi Ric : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Ric - ((1 / 2 : ℝ) * Matrix.trace (gi * Ric)) • g

/-- Thesis §2.3: the Einstein tensor "inherits symmetry from the Ricci tensor" (it also
needs `g` symmetric). -/
theorem einstein_symm (g gi Ric : Matrix (Fin n) (Fin n) ℝ) (hg : g.IsSymm)
    (hRic : Ric.IsSymm) : (einstein g gi Ric).IsSymm := by
  unfold einstein
  exact hRic.sub (hg.smul _)

/-- Thesis §2.4: in vacuum, Einstein's equations `G = 0` are equivalent to Ricci-flatness.

Thesis gap: the dimension dependence is implicit and the final step is omitted. The thesis
works in a four-dimensional spacetime and argues via "tr G = 0 iff tr Ric = 0", using
`tr_g G = (1 − n/2) tr_g Ric`; this needs `n ≠ 2` (see `einstein_zero_iff_fails_two`), and
one still has to conclude `Ric = G + ½ R g`. Stated here for every `n ≠ 2`, in particular
`n = 4`. Proof: `G = 0 ⇒ (1 − n/2) R = 0 ⇒ R = 0 ⇒
Ric = G + ½ R g = 0`. -/
theorem einstein_zero_iff (hn : n ≠ 2) (g gi Ric : Matrix (Fin n) (Fin n) ℝ)
    (hinv : gi * g = 1) : einstein g gi Ric = 0 ↔ Ric = 0 := by
  unfold einstein
  constructor
  · intro h
    have hR : Matrix.trace (gi * Ric) = 0 := by
      have h1 := congrArg (fun M => Matrix.trace (gi * M)) h
      simp only [Matrix.mul_sub, Matrix.mul_smul, hinv, Matrix.trace_sub, Matrix.trace_smul,
        Matrix.trace_one, Fintype.card_fin, Matrix.mul_zero, Matrix.trace_zero,
        smul_eq_mul] at h1
      have hn' : (n : ℝ) ≠ 2 := by exact_mod_cast hn
      have : (1 - (1 / 2 : ℝ) * n) * Matrix.trace (gi * Ric) = 0 := by linarith
      rcases mul_eq_zero.mp this with h2 | h2
      · exact absurd (by linarith) hn'
      · exact h2
    rw [hR, mul_zero, zero_smul, sub_zero] at h
    exact h
  · rintro rfl
    simp

/-- Thesis §2.4, sharpness of the hypothesis `n ≠ 2` in `einstein_zero_iff` (the thesis
itself works in dimension 4): for `n = 2` the algebraic equivalence `G = 0 ⇔ Ric = 0`
fails, witnessed by `g = gi = Ric = 1`.

Remark (not proved here): this is realized geometrically by the unit sphere `S²`, where
`Ric = g`; in fact in dimension 2 the Einstein tensor of every metric vanishes. -/
theorem einstein_zero_iff_fails_two :
    ∃ g gi Ric : Matrix (Fin 2) (Fin 2) ℝ, gi * g = 1 ∧ einstein g gi Ric = 0 ∧ Ric ≠ 0 := by
  refine ⟨1, 1, 1, by simp, ?_, one_ne_zero⟩
  unfold einstein
  simp only [Matrix.one_mul, Matrix.trace_one, Fintype.card_fin]
  norm_num

end Einstein


section Dimension

/-! ### Independent components for `n = 4`

Pair skew + interchange identify `C` with a symmetric `6 × 6` matrix on bivectors
(21 parameters); given these, Bianchi reduces to the single condition `C_[0123] = 0`. -/

/-- Bivector index pairs `01, 02, 03, 12, 13, 23`. -/
def bivPair : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The basis bivector `e_p ∧ e_q` for `bivPair I = (p, q)`, in components. -/
def bivForm (I : Fin 6) (a b : Fin 4) : ℝ :=
  if a = (bivPair I).1 ∧ b = (bivPair I).2 then 1
  else if a = (bivPair I).2 ∧ b = (bivPair I).1 then -1 else 0

lemma bivForm_swap (I : Fin 6) (a b : Fin 4) : bivForm I b a = -bivForm I a b := by
  fin_cases I <;> fin_cases a <;> fin_cases b <;> simp [bivForm, bivPair]

lemma sum_bivForm (X : Fin 4 → Fin 4 → ℝ) (hX : ∀ a b, X a b = -X b a) (a b : Fin 4) :
    ∑ I, bivForm I a b * X (bivPair I).1 (bivPair I).2 = X a b := by
  have h0 : ∀ a, X a a = 0 := fun a => by have := hX a a; linarith
  fin_cases a <;> fin_cases b <;> simp [bivForm, bivPair, Fin.sum_univ_six, h0] <;>
    linarith [hX 1 0, hX 2 0, hX 3 0, hX 2 1, hX 3 1, hX 3 2]

lemma alt4_swap12 (C : T4 (Fin 4)) (a b c d : Fin 4) : alt4 C b a c d = -alt4 C a b c d := by
  unfold alt4; ring
lemma alt4_swap23 (C : T4 (Fin 4)) (a b c d : Fin 4) : alt4 C a c b d = -alt4 C a b c d := by
  unfold alt4; ring
lemma alt4_swap34 (C : T4 (Fin 4)) (a b c d : Fin 4) : alt4 C a b d c = -alt4 C a b c d := by
  unfold alt4; ring

/-- `alt4` is totally antisymmetric, so on `Fin 4` it vanishes everywhere iff it vanishes
at `(0,1,2,3)`. -/
theorem alt4_all_iff (C : T4 (Fin 4)) :
    (∀ a b c d, alt4 C a b c d = 0) ↔ alt4 C 0 1 2 3 = 0 := by
  refine ⟨fun h => h 0 1 2 3, fun h a b c d => ?_⟩
  have s1 := alt4_swap12 C; have s2 := alt4_swap23 C; have s3 := alt4_swap34 C
  by_cases hab : a = b
  · subst hab; linarith [s1 a a c d]
  by_cases hbc : b = c
  · subst hbc; linarith [s2 a b b d]
  by_cases hcd : c = d
  · subst hcd; linarith [s3 a b c c]
  by_cases hac : a = c
  · subst hac; linarith [s2 a b a d, s1 a a b d]
  by_cases hbd : b = d
  · subst hbd; linarith [s3 a b c b, s2 a b b c]
  by_cases had : a = d
  · subst had; linarith [s3 a b c a, s2 a b a c, s1 a a b c]
  unfold alt4 at h
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (exfalso; revert hab hbc hcd hac hbd had; decide)
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]; unfold alt4; linarith)

/-- Under pair skew and interchange, `alt4 C 0 1 2 3 = 8 · (Bianchi sum at (0,1,2,3))`. -/
lemma alt4_eq_of_interchange {C : T4 (Fin 4)} (hs : PairSkew C) (hi : Interchange C) :
    alt4 C 0 1 2 3 = 8 * (C 0 1 2 3 + C 0 2 3 1 + C 0 3 1 2) := by
  unfold alt4
  have := hs 0 1 2 3; have := hs 0 2 1 3; have := hs 0 3 1 2; have := hs 0 1 3 2
  have := hs 0 2 3 1; have := hs 0 3 2 1
  have := hi 0 1 2 3; have := hi 0 1 3 2; have := hi 0 2 1 3; have := hi 0 2 3 1
  have := hi 0 3 1 2; have := hi 0 3 2 1; have := hi 1 0 2 3; have := hi 1 0 3 2
  have := hi 1 2 0 3; have := hi 1 2 3 0; have := hi 1 3 0 2; have := hi 1 3 2 0
  have := hs 1 2 0 3; have := hs 1 3 0 2; have := hs 2 3 0 1; have := hs 2 1 0 3
  have := hs 3 1 0 2; have := hs 3 2 0 1; have := hs 1 0 3 2; have := hs 2 0 3 1
  have := hs 3 0 2 1; have := hs 1 2 3 0; have := hs 1 3 2 0
  linarith

/-- Reconstruction of a pair-skew tensor from its `6 × 6` bivector matrix. -/
def recon (M : Fin 6 → Fin 6 → ℝ) : T4 (Fin 4) :=
  fun a b c d => ∑ I, ∑ J, bivForm I a b * bivForm J c d * M I J

/-- Bivector matrix of a tensor, `M_IJ = C(p_I, q_I, p_J, q_J)`. -/
def bivMat (C : T4 (Fin 4)) : Fin 6 → Fin 6 → ℝ :=
  fun I J => C (bivPair I).1 (bivPair I).2 (bivPair J).1 (bivPair J).2

lemma bivForm_pair (I J : Fin 6) :
    bivForm I (bivPair J).1 (bivPair J).2 = if I = J then 1 else 0 := by
  fin_cases I <;> fin_cases J <;> simp [bivForm, bivPair]

lemma recon_pair (M : Fin 6 → Fin 6 → ℝ) (I J : Fin 6) :
    recon M (bivPair I).1 (bivPair I).2 (bivPair J).1 (bivPair J).2 = M I J := by
  simp [recon, bivForm_pair]

lemma recon_pairSkew (M : Fin 6 → Fin 6 → ℝ) : PairSkew (recon M) := by
  intro a b c d
  simp only [recon]
  constructor
  · rw [← sum_neg_distrib]
    refine sum_congr rfl fun I _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun J _ => ?_
    rw [bivForm_swap I b a]; ring
  · rw [← sum_neg_distrib]
    refine sum_congr rfl fun I _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun J _ => ?_
    rw [bivForm_swap J d c]; ring

lemma recon_interchange (M : Fin 6 → Fin 6 → ℝ) (hM : ∀ I J, M I J = M J I) :
    Interchange (recon M) := by
  intro a b c d
  simp only [recon]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun I _ => sum_congr rfl fun J _ => by rw [hM]; ring

lemma eq_recon {C : T4 (Fin 4)} (hs : PairSkew C) : C = recon (bivMat C) := by
  funext a b c d
  simp only [recon, bivMat]
  rw [← sum_bivForm (fun x y => C x y c d) (fun x y => (hs x y c d).1) a b]
  refine sum_congr rfl fun I _ => ?_
  rw [← sum_bivForm (fun x y => C (bivPair I).1 (bivPair I).2 x y)
    (fun x y => (hs _ _ x y).2) c d, mul_sum]
  exact sum_congr rfl fun J _ => by ring


/-- The algebraic curvature tensors: pair skew and first Bianchi. -/
def algCurv (ι : Type*) : Submodule ℝ (T4 ι) where
  carrier := {C | PairSkew C ∧ Bianchi1 C}
  zero_mem' := ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩
  add_mem' := by
    rintro C D ⟨hC, hC'⟩ ⟨hD, hD'⟩
    refine ⟨fun a b c d => ?_, fun a b c d => ?_⟩
    · simp only [Pi.add_apply]
      constructor
      · rw [(hC a b c d).1, (hD a b c d).1]; ring
      · rw [(hC a b c d).2, (hD a b c d).2]; ring
    · simp only [Pi.add_apply]
      linarith [hC' a b c d, hD' a b c d]
  smul_mem' := by
    rintro r C ⟨hC, hC'⟩
    refine ⟨fun a b c d => ?_, fun a b c d => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      constructor
      · rw [(hC a b c d).1]; ring
      · rw [(hC a b c d).2]; ring
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_add, ← mul_add, hC' a b c d, mul_zero]

/-- 20 free parameters → bivector matrix (the entry `(03,12)` is fixed by Bianchi). -/
def parMat (p : Fin 20 → ℝ) : Fin 6 → Fin 6 → ℝ :=
  ![![p 0, p 1, p 2, p 3, p 4, p 5],
    ![p 1, p 6, p 7, p 8, p 9, p 10],
    ![p 2, p 7, p 11, p 9 - p 5, p 12, p 13],
    ![p 3, p 8, p 9 - p 5, p 14, p 15, p 16],
    ![p 4, p 9, p 12, p 15, p 17, p 18],
    ![p 5, p 10, p 13, p 16, p 18, p 19]]

/-- The bivector-matrix entries used as coordinates. -/
def parIdx : Fin 20 → Fin 6 × Fin 6 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5),
    (2, 2), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]

lemma parMat_symm (p : Fin 20 → ℝ) (I J : Fin 6) : parMat p I J = parMat p J I := by
  fin_cases I <;> fin_cases J <;> rfl

lemma recon_parMat_mem (p : Fin 20 → ℝ) : recon (parMat p) ∈ algCurv (Fin 4) := by
  have hs := recon_pairSkew (parMat p)
  have hi := recon_interchange (parMat p) (parMat_symm p)
  refine ⟨hs, (bianchi_iff hs).2 ⟨hi, (alt4_all_iff _).2 ?_⟩⟩
  rw [alt4_eq_of_interchange hs hi]
  have h1 : recon (parMat p) 0 1 2 3 = p 5 := recon_pair (parMat p) 0 5
  have h2 : recon (parMat p) 0 2 1 3 = p 9 := recon_pair (parMat p) 1 4
  have h3 : recon (parMat p) 0 3 1 2 = p 9 - p 5 := recon_pair (parMat p) 2 3
  have h4 := (hs 0 2 1 3).2
  linarith

/-- Thesis §2.3, independent-component count for `n = 4`: the space of algebraic curvature
tensors (pair skew + first Bianchi) is isomorphic to `ℝ²⁰`. -/
def algCurvEquiv : algCurv (Fin 4) ≃ₗ[ℝ] (Fin 20 → ℝ) where
  toFun C := fun k => bivMat C (parIdx k).1 (parIdx k).2
  map_add' C D := rfl
  map_smul' r C := rfl
  invFun p := ⟨recon (parMat p), recon_parMat_mem p⟩
  left_inv := by
    rintro ⟨C, hs, hb⟩
    apply Subtype.ext
    have hi := interchange_of_bianchi hs hb
    show recon _ = C
    conv_rhs => rw [eq_recon hs]
    congr 1
    funext I J
    fin_cases I <;> fin_cases J <;> simp [parMat, parIdx, bivMat, bivPair] <;>
      first
      | exact hi _ _ _ _
      | linarith [hb 0 1 2 3, (hs 0 2 3 1).2, hi 0 3 1 2, hi 1 2 0 3]
  right_inv := by
    intro p
    funext k
    simp only [bivMat, recon_pair]
    fin_cases k <;> rfl

/-- Thesis §2.3: "the Riemann tensor ... only has `n²(n²−1)/12` independent components
(20 when `n = 4`)", read as: the algebraic curvature tensors (the symmetries of Prop 2.1)
form a space of dimension `n²(n²−1)/12`.

Thesis gap: asserted without proof or reference. Proved here for `n = 4` via the
explicit isomorphism `algCurvEquiv`; general `n` is not formalized. -/
theorem finrank_algCurv_four : Module.finrank ℝ (algCurv (Fin 4)) = 20 := by
  rw [algCurvEquiv.finrank_eq]; simp

end Dimension

end Feec.Curvature
