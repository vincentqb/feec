module

public import Feec.Geometry.AlgebraicCurvature
public import Feec.ForMathlib.Calculus.Partial

/-!
# The Riemann tensor of a connection in coordinates

The coordinate formula (2.2) `R^a_{bcd} = ∂_c Γ^a_{bd} - ∂_d Γ^a_{bc} + Γ^a_{ec} Γ^e_{bd} -
Γ^a_{ed} Γ^e_{bc}` at the jet level (over any commutative ring and index type), and for
connection fields on `ℝ^ι`.

## Main results

* `riemComp_skew`, `riemComp_bianchi`: skew in the last pair, and the first Bianchi identity
  for a torsion-free connection (no metric needed);
* `lower_riemComp_skew`: skew in the first pair for a metric-compatible connection;
* `riemComp_isAlgCurv`: **Prop 2.1 (corrected), jet level**: the lowered Riemann tensor of a
  torsion-free metric-compatible connection is an algebraic curvature tensor, and has the
  interchange symmetry;
* `riemField_isAlgCurv`: Prop 2.1 for a `C²` metric field and its Levi-Civita connection on
  `ℝ^ι`; `ricci_riemField_isSymm`: the Ricci tensor is symmetric.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §2.3 (Prop 2.1, (2.2))
* [R. M. Wald, *General Relativity*][Wald1984], §3.2, §3.4
-/

open Finset Matrix

@[expose] public noncomputable section

namespace Feec.CurvatureTensor

section Jet

variable {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]

/-- The coordinate formula (2.2) for `R^a_{bcd}` from the values of `Γ^a_{bc} = Γ a b c` and
`∂_e Γ^a_{bc} = dΓ e a b c` at a point. [QuennevilleBelair2015], (2.2) -/
def riemComp (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R) : ι → ι → ι → ι → R :=
  fun a b c d => dΓ c a b d - dΓ d a b c + ∑ e, (Γ a e c * Γ e b d - Γ a e d * Γ e b c)

/-- Lower the first index with the metric: `R_abcd = g_ae R^e_bcd`. -/
def lower (g : Matrix ι ι R) (C : ι → ι → ι → ι → R) : ι → ι → ι → ι → R :=
  fun a b c d => ∑ e, g a e * C e b c d

/-- Skew-symmetry in the second pair, for any connection. [QuennevilleBelair2015], Prop 2.1 -/
theorem riemComp_skew (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R) (a b c d : ι) :
    riemComp Γ dΓ a b c d = -riemComp Γ dΓ a b d c := by
  simp only [riemComp]
  have : ∑ e, (Γ a e c * Γ e b d - Γ a e d * Γ e b c)
      = -∑ e, (Γ a e d * Γ e b c - Γ a e c * Γ e b d) := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun _ _ => by ring
  linear_combination this

/-- **First Bianchi identity** `R^a_{[bcd]} = 0` for a torsion-free connection.
Correction: the thesis concludes with a four-index antisymmetrisation, which is not the Bianchi
identity. [QuennevilleBelair2015], Prop 2.1 (corrected) -/
theorem riemComp_bianchi (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R)
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
  linear_combination hs + hdΓ c a b d - hdΓ d a b c - hdΓ b a c d

private theorem sum_sum_sub_swap (A : ι → ι → R) : ∑ r, ∑ s, (A r s - A s r) = 0 := by
  simp only [sum_sub_distrib]
  rw [Finset.sum_comm (f := fun r s => A s r), sub_self]

/-- Skew-symmetry in the first pair `R_abcd = -R_bacd`, at the jet level, for a symmetric `g`
and a torsion-free connection compatible with `g` to first order (`hcomp`:
`∂_e g_ab = g_rb Γ^r_ea + g_ar Γ^r_eb`) and second order (`hcomp'`, the product rule applied to
`hcomp`), with symmetric second derivatives of `g` (`hddg`). This is the thesis' argument
`0 = [∇_c, ∇_d] g_ab`, proved from (2.2) directly. [QuennevilleBelair2015], Prop 2.1 -/
theorem lower_riemComp_skew [DecidableEq ι] (g : Matrix ι ι R) (hg : g.IsSymm)
    (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R) (dg : ι → ι → ι → R)
    (ddg : ι → ι → ι → ι → R)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (hdΓ : ∀ e a b c, dΓ e a b c = dΓ e a c b)
    (hcomp : ∀ e a b, dg e a b = ∑ r, (g r b * Γ r e a + g a r * Γ r e b))
    (hcomp' : ∀ f e a b, ddg f e a b =
      ∑ r, (dg f r b * Γ r e a + g r b * dΓ f r e a + dg f a r * Γ r e b + g a r * dΓ f r e b))
    (hddg : ∀ f e a b, ddg f e a b = ddg e f a b) (a b c d : ι) :
    lower g (riemComp Γ dΓ) a b c d = -lower g (riemComp Γ dΓ) b a c d := by
  have gs : ∀ i j, g i j = g j i := fun i j => hg.apply j i
  have hD : ∑ e, g a e * (dΓ c e b d - dΓ d e b c) + ∑ e, g b e * (dΓ c e a d - dΓ d e a c)
      = -∑ r, (dg c r b * Γ r d a - dg d r b * Γ r c a + dg c a r * Γ r d b
        - dg d a r * Γ r c b) := by
    have h0 : ddg c d a b - ddg d c a b = 0 := by rw [hddg]; ring
    rw [hcomp' c d a b, hcomp' d c a b, ← sum_sub_distrib] at h0
    rw [eq_neg_iff_add_eq_zero, ← h0, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [hdΓ c r d a, hdΓ d r c a, hdΓ c r d b, hdΓ d r c b, gs r b]; ring
  have hQ : ∑ r, (dg c r b * Γ r d a - dg d r b * Γ r c a + dg c a r * Γ r d b
        - dg d a r * Γ r c b) = ∑ r, ∑ s,
      (g s b * Γ s c r * Γ r d a - g s b * Γ s d r * Γ r c a + g a s * Γ s c r * Γ r d b
        - g a s * Γ s d r * Γ r c b) := by
    have hz := sum_sum_sub_swap (fun r s => g r s * (Γ s c b * Γ r d a - Γ s d b * Γ r c a))
    rw [← sub_eq_zero, ← hz, ← sum_sub_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [hcomp c r b, hcomp d r b, hcomp c a r, hcomp d a r]
    simp only [sum_mul, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun s _ => ?_
    rw [gs a s]
    ring
  have hG : ∑ e, g a e * ∑ r, (Γ e r c * Γ r b d - Γ e r d * Γ r b c)
      + ∑ e, g b e * ∑ r, (Γ e r c * Γ r a d - Γ e r d * Γ r a c) = ∑ r, ∑ s,
      (g s b * Γ s c r * Γ r d a - g s b * Γ s d r * Γ r c a + g a s * Γ s c r * Γ r d b
        - g a s * Γ s d r * Γ r c b) := by
    rw [Finset.sum_comm (f := fun r s => _)]
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun s _ => sum_congr rfl fun r _ => ?_
    rw [hΓ s r c, hΓ s r d, hΓ r b d, hΓ r b c, hΓ r a d, hΓ r a c, gs s b]; ring
  simp only [lower, riemComp, mul_add, sum_add_distrib]
  linear_combination hD + hG - hQ

/-- **Prop 2.1 (corrected), jet level**: for a torsion-free metric-compatible connection, the
lowered Riemann tensor (2.2) is skew in each pair and satisfies the first Bianchi identity;
with `2` invertible it also has the interchange symmetry. [QuennevilleBelair2015], Prop 2.1 (corrected) -/
theorem lower_riemComp_isAlgCurv [DecidableEq ι] (g : Matrix ι ι R) (hg : g.IsSymm)
    (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R) (dg : ι → ι → ι → R)
    (ddg : ι → ι → ι → ι → R)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (hdΓ : ∀ e a b c, dΓ e a b c = dΓ e a c b)
    (hcomp : ∀ e a b, dg e a b = ∑ r, (g r b * Γ r e a + g a r * Γ r e b))
    (hcomp' : ∀ f e a b, ddg f e a b =
      ∑ r, (dg f r b * Γ r e a + g r b * dΓ f r e a + dg f a r * Γ r e b + g a r * dΓ f r e b))
    (hddg : ∀ f e a b, ddg f e a b = ddg e f a b) :
    PairSkew (lower g (riemComp Γ dΓ)) ∧ Bianchi1 (lower g (riemComp Γ dΓ)) := by
  have hs : PairSkew (lower g (riemComp Γ dΓ)) := fun a b c d =>
    ⟨lower_riemComp_skew g hg Γ dΓ dg ddg hΓ hdΓ hcomp hcomp' hddg a b c d, by
      simp only [lower, ← sum_neg_distrib]
      exact sum_congr rfl fun e _ => by rw [riemComp_skew Γ dΓ e b c d]; ring⟩
  refine ⟨hs, fun a b c d => ?_⟩
  simp only [lower, ← sum_add_distrib, ← mul_add]
  refine sum_eq_zero fun e _ => ?_
  rw [riemComp_bianchi Γ dΓ hΓ hdΓ e b c d, mul_zero]

end Jet

section Field

/-! ### Prop 2.1 for fields on `ℝ^ι`

The jet hypotheses of `lower_riemComp_isAlgCurv` are discharged for a `C²` symmetric metric
field and a differentiable, torsion-free, metric-compatible connection field (the Levi-Civita
connection), with coordinate partial derivatives `partialDeriv`. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Riemann tensor field `R^a_bcd(x)` of a connection field `Γ`, by formula (2.2).
[QuennevilleBelair2015], (2.2) -/
def riemField (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) : ι → ι → ι → ι → ℝ :=
  riemComp (Γ x) (fun e a b c => partialDeriv e (fun y => Γ y a b c) x)

/-- **Prop 2.1 (corrected)** for fields: for a `C²` symmetric metric field `g` on `ℝ^ι` and a
differentiable torsion-free connection `Γ` compatible with `g` (the Levi-Civita connection),
the lowered Riemann tensor `R_abcd = g_ae R^e_bcd` of (2.2) is skew in each pair and satisfies
the first Bianchi identity and the interchange symmetry. [QuennevilleBelair2015], Prop 2.1 (corrected) -/
theorem riemField_isAlgCurv (g : (ι → ℝ) → Matrix ι ι ℝ) (Γ : (ι → ℝ) → ι → ι → ι → ℝ)
    (hg : ∀ x, (g x).IsSymm) (hgC : ∀ a b, ContDiff ℝ 2 fun x => g x a b)
    (hΓd : ∀ a b c, Differentiable ℝ fun x => Γ x a b c)
    (hΓ : ∀ x a b c, Γ x a b c = Γ x a c b)
    (hcompat : ∀ x e a b,
      partialDeriv e (fun y => g y a b) x = ∑ r, (g x r b * Γ x r e a + g x a r * Γ x r e b))
    (x : ι → ℝ) :
    PairSkew (lower (g x) (riemField Γ x)) ∧ Bianchi1 (lower (g x) (riemField Γ x)) ∧
      Interchange (lower (g x) (riemField Γ x)) := by
  have hgd : ∀ a b, Differentiable ℝ fun x => g x a b := fun a b =>
    (hgC a b).differentiable (by norm_num)
  have hcf : ∀ e a b, (fun y => partialDeriv e (fun z => g z a b) y)
      = fun y => ∑ r, (g y r b * Γ y r e a + g y a r * Γ y r e b) := fun e a b =>
    funext fun y => hcompat y e a b
  obtain ⟨hs, hb⟩ := lower_riemComp_isAlgCurv (g x) (hg x) (Γ x)
    (fun e a b c => partialDeriv e (fun y => Γ y a b c) x)
    (fun e a b => partialDeriv e (fun y => g y a b) x)
    (fun f e a b => partialDeriv f (fun y => partialDeriv e (fun z => g z a b) y) x) (hΓ x)
    (fun e a b c => by
      show partialDeriv e _ x = partialDeriv e _ x
      congr 1
      exact funext fun y => hΓ y a b c)
    (hcompat x)
    (fun f e a b => by
      rw [hcf e a b, partialDeriv_sum _ (fun r _ => by fun_prop)]
      refine sum_congr rfl fun r _ => ?_
      rw [partialDeriv_add (by fun_prop) (by fun_prop),
        partialDeriv_mul (by fun_prop) (by fun_prop),
        partialDeriv_mul (by fun_prop) (by fun_prop)]
      ring)
    (fun f e a b => partialDeriv_comm (hgC a b) f e x)
  exact ⟨hs, hb, interchange_of_bianchi hs hb⟩

/-- **The Ricci tensor is symmetric** (§2.3) for the curvature (2.2) of the Levi-Civita
connection of a `C²` metric field, given an inverse `gi` of `g x`. [QuennevilleBelair2015], §2.3 -/
theorem ricci_riemField_isSymm (g : (ι → ℝ) → Matrix ι ι ℝ) (Γ : (ι → ℝ) → ι → ι → ι → ℝ)
    (hg : ∀ x, (g x).IsSymm) (hgC : ∀ a b, ContDiff ℝ 2 fun x => g x a b)
    (hΓd : ∀ a b c, Differentiable ℝ fun x => Γ x a b c)
    (hΓ : ∀ x a b c, Γ x a b c = Γ x a c b)
    (hcompat : ∀ x e a b,
      partialDeriv e (fun y => g y a b) x = ∑ r, (g x r b * Γ x r e a + g x a r * Γ x r e b))
    (x : ι → ℝ) (gi : Matrix ι ι ℝ) (hinv : gi * g x = 1) (a b : ι) :
    ∑ c, riemField Γ x c a c b = ∑ c, riemField Γ x c b c a := by
  have hraise : ∀ a b, ricci gi (lower (g x) (riemField Γ x)) a b = ∑ c, riemField Γ x c a c b := by
    intro a b
    simp only [ricci, of_apply]
    refine sum_congr rfl fun c _ => ?_
    simp only [lower, mul_sum]
    rw [Finset.sum_comm]
    have hcf : ∀ f, ∑ e, gi c e * (g x e f) = (1 : Matrix ι ι ℝ) c f := by
      intro f; rw [← hinv]; rfl
    calc ∑ f, ∑ e, gi c e * (g x e f * riemField Γ x f a c b)
        = ∑ f, (1 : Matrix ι ι ℝ) c f * riemField Γ x f a c b := by
          refine sum_congr rfl fun f _ => ?_
          rw [← hcf f, sum_mul]
          exact sum_congr rfl fun e _ => by ring
      _ = riemField Γ x c a c b := by simp [Matrix.one_apply]
  rw [← hraise a b, ← hraise b a]
  exact ((ricci_isSymm_of_inv (hg x) hinv
    (riemField_isAlgCurv g Γ hg hgC hΓd hΓ hcompat x).2.2).apply a b).symm

end Field

end Feec.CurvatureTensor
