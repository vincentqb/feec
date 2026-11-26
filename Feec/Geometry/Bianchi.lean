module

public import Feec.Geometry.Connection

/-!
# The second Bianchi identity and its contractions

The differential Bianchi identity `∇_[e R_cd]ab = 0` ([QuennevilleBelair2015], (2.4)) and its
contraction, for connection jets over any commutative ring; for metric fields on `ℝ^ι` of any
dimension and signature, also the twice-contracted identity and the vacuum divergence of the Weyl
tensor.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [R. M. Wald, *General Relativity*][Wald1984]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset Matrix

@[expose] public noncomputable section

namespace Feec.CurvatureTensor

section Jet

variable {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]

/-- The jet `∂_f R^a_{bcd}` of the curvature (2.2), from `Γ`, `∂Γ`, `∂∂Γ` by the product rule. -/
def dRiemComp (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R) (ddΓ : ι → ι → ι → ι → ι → R) :
    ι → ι → ι → ι → ι → R := fun f a b c d =>
  ddΓ f c a b d - ddΓ f d a b c + ∑ e, (dΓ f a e c * Γ e b d + Γ a e c * dΓ f e b d
    - dΓ f a e d * Γ e b c - Γ a e d * dΓ f e b c)

/-- The covariant derivative `∇_f T^a_bcd` of a `(1,3)` tensor jet `(T, ∂T)`. -/
def cov13 (Γ : ι → ι → ι → R) (T : ι → ι → ι → ι → R) (dT : ι → ι → ι → ι → ι → R) :
    ι → ι → ι → ι → ι → R := fun f a b c d =>
  dT f a b c d + ∑ e, (Γ a f e * T e b c d - Γ e f b * T a e c d - Γ e f c * T a b e d
    - Γ e f d * T a b c e)

/-- The terms of `∇_f R^a_bcd` linear in `∂Γ`. -/
private def bL (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R) (a b f c d e : ι) : R :=
  dΓ f a e c * Γ e b d + Γ a e c * dΓ f e b d - dΓ f a e d * Γ e b c - Γ a e d * dΓ f e b c
    + (Γ a f e * dΓ c e b d - Γ a f e * dΓ d e b c)
    - (Γ e f b * dΓ c a e d - Γ e f b * dΓ d a e c)

/-- The terms of `∇_f R^a_bcd` cubic in `Γ`. -/
private def bQ (Γ : ι → ι → ι → R) (a b f c d e g : ι) : R :=
  (Γ a f e * (Γ e g c * Γ g b d) - Γ a f e * (Γ e g d * Γ g b c))
    - (Γ e f b * (Γ a g c * Γ g e d) - Γ e f b * (Γ a g d * Γ g e c))

private theorem cov13_riem_eq (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R)
    (ddΓ : ι → ι → ι → ι → ι → R) (f a b c d : ι) :
    cov13 Γ (riemComp Γ dΓ) (dRiemComp Γ dΓ ddΓ) f a b c d =
      ddΓ f c a b d - ddΓ f d a b c + ∑ e, bL Γ dΓ a b f c d e + ∑ e, ∑ g, bQ Γ a b f c d e g
      - ∑ e, (Γ e f c * riemComp Γ dΓ a b e d + Γ e f d * riemComp Γ dΓ a b c e) := by
  simp only [cov13, dRiemComp, bL, bQ]
  simp only [riemComp, mul_add, mul_sub, mul_sum, sum_add_distrib, sum_sub_distrib]
  ring

/-- The second Bianchi identity `∇_f R^a_bcd + ∇_c R^a_bdf + ∇_d R^a_bfc = 0` for a torsion-free
connection jet with symmetric `∂∂Γ`. [QuennevilleBelair2015], (2.4); [Wald1984], §3.2 -/
theorem cov13_riem_cyclic (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R)
    (ddΓ : ι → ι → ι → ι → ι → R) (hΓ : ∀ a b c, Γ a b c = Γ a c b)
    (hddΓ : ∀ f e a b c, ddΓ f e a b c = ddΓ e f a b c) (f a b c d : ι) :
    cov13 Γ (riemComp Γ dΓ) (dRiemComp Γ dΓ ddΓ) f a b c d
      + cov13 Γ (riemComp Γ dΓ) (dRiemComp Γ dΓ ddΓ) c a b d f
      + cov13 Γ (riemComp Γ dΓ) (dRiemComp Γ dΓ ddΓ) d a b f c = 0 := by
  rw [cov13_riem_eq, cov13_riem_eq, cov13_riem_eq]
  have hL : ∑ e, bL Γ dΓ a b f c d e + ∑ e, bL Γ dΓ a b c d f e + ∑ e, bL Γ dΓ a b d f c e
      = 0 := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_eq_zero fun e _ => ?_
    simp only [bL]
    rw [hΓ a f e, hΓ a c e, hΓ a d e, hΓ e b d, hΓ e b c, hΓ e b f]
    ring
  let A : ι → ι → R := fun e g =>
    (Γ a f e * (Γ e g c * Γ g b d) - Γ a f e * (Γ e g d * Γ g b c))
    + (Γ a c e * (Γ e g d * Γ g b f) - Γ a c e * (Γ e g f * Γ g b d))
    + (Γ a d e * (Γ e g f * Γ g b c) - Γ a d e * (Γ e g c * Γ g b f))
  have hQ : ∑ e, ∑ g, bQ Γ a b f c d e g + ∑ e, ∑ g, bQ Γ a b c d f e g
      + ∑ e, ∑ g, bQ Γ a b d f c e g = 0 := by
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_sum_sub_swap A]
    refine sum_congr rfl fun e _ => ?_
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun g _ => ?_
    simp only [bQ, A]
    rw [hΓ e f b, hΓ e c b, hΓ e d b, hΓ a g c, hΓ a g d, hΓ a g f]
    ring
  have hP : ∑ e, (Γ e f c * riemComp Γ dΓ a b e d + Γ e f d * riemComp Γ dΓ a b c e)
      + ∑ e, (Γ e c d * riemComp Γ dΓ a b e f + Γ e c f * riemComp Γ dΓ a b d e)
      + ∑ e, (Γ e d f * riemComp Γ dΓ a b e c + Γ e d c * riemComp Γ dΓ a b f e) = 0 := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_eq_zero fun e _ => ?_
    rw [hΓ e c f, hΓ e d f, hΓ e d c, riemComp_skew Γ dΓ a b d e, riemComp_skew Γ dΓ a b e c,
      riemComp_skew Γ dΓ a b f e]
    ring
  linear_combination hL + hQ - hP + hddΓ f c a b d - hddΓ f d a b c + hddΓ c d a b f

theorem sum_swap_eq {F G : ι → ι → R} (h : ∀ x i, F x i = G i x) :
    ∑ x, ∑ i, F x i = ∑ x, ∑ i, G x i := by
  rw [Finset.sum_comm]; exact sum_congr rfl fun i _ => sum_congr rfl fun x _ => h x i

/-- The covariant derivative `∇_f T_abcd` of a `(0,4)` tensor jet `(T, ∂T)`. -/
def cov4 (Γ : ι → ι → ι → R) (T : ι → ι → ι → ι → R) (dT : ι → ι → ι → ι → ι → R) :
    ι → ι → ι → ι → ι → R := fun f a b c d =>
  dT f a b c d - ∑ e, (Γ e f a * T e b c d + Γ e f b * T a e c d + Γ e f c * T a b e d
    + Γ e f d * T a b c e)

/-- The product-rule jet `∂_f (g_ae T^e_bcd)` of `lower g T`. -/
def dLower (g : Matrix ι ι R) (dg : ι → ι → ι → R) (T : ι → ι → ι → ι → R)
    (dT : ι → ι → ι → ι → ι → R) : ι → ι → ι → ι → ι → R := fun f a b c d =>
  ∑ e, (dg f a e * T e b c d + g a e * dT f e b c d)

theorem cov4_lower (Γ : ι → ι → ι → R) (g : Matrix ι ι R) (dg : ι → ι → ι → R)
    (hcomp : ∀ e a b, dg e a b = ∑ r, (g r b * Γ r e a + g a r * Γ r e b))
    (T : ι → ι → ι → ι → R) (dT : ι → ι → ι → ι → ι → R) (f a b c d : ι) :
    cov4 Γ (lower g T) (dLower g dg T dT) f a b c d = ∑ e, g a e * cov13 Γ T dT f e b c d := by
  simp only [cov4, dLower, cov13, lower, hcomp]
  simp only [mul_add, mul_sub, add_mul, sum_add_distrib, sum_sub_distrib, sum_mul, mul_sum]
  have e1 : ∑ x, ∑ i, g i x * Γ i f a * T x b c d = ∑ x, ∑ i, Γ x f a * (g x i * T i b c d) :=
    sum_swap_eq fun x i => by ring
  have e2 : ∑ x, ∑ i, g a i * Γ i f x * T x b c d = ∑ x, ∑ i, g a x * (Γ x f i * T i b c d) :=
    sum_swap_eq fun x i => by ring
  have e3 : ∑ x, ∑ i, Γ x f b * (g a i * T i x c d) = ∑ x, ∑ i, g a x * (Γ i f b * T x i c d) :=
    sum_swap_eq fun x i => by ring
  have e4 : ∑ x, ∑ i, Γ x f c * (g a i * T i b x d) = ∑ x, ∑ i, g a x * (Γ i f c * T x b i d) :=
    sum_swap_eq fun x i => by ring
  have e5 : ∑ x, ∑ i, Γ x f d * (g a i * T i b c x) = ∑ x, ∑ i, g a x * (Γ i f d * T x b c i) :=
    sum_swap_eq fun x i => by ring
  linear_combination e1 + e2 - e3 - e4 - e5

theorem sum3_congr_perm {F G : ι → ι → ι → R} (σ : ι × ι × ι ≃ ι × ι × ι)
    (h : ∀ x, F x.1 x.2.1 x.2.2 = G (σ x).1 (σ x).2.1 (σ x).2.2) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ b, ∑ c, G a b c := by
  have e : ∀ H : ι → ι → ι → R, ∑ a, ∑ b, ∑ c, H a b c = ∑ x : ι × ι × ι, H x.1 x.2.1 x.2.2 := by
    intro H; rw [Fintype.sum_prod_type]; simp only [Fintype.sum_prod_type]
  rw [e, e]; exact Fintype.sum_equiv σ _ _ h

theorem sum5_congr_perm {F G : ι → ι → ι → ι → ι → R} (σ : ι × ι × ι × ι × ι ≃ ι × ι × ι × ι × ι)
    (h : ∀ x, F x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 =
      G (σ x).1 (σ x).2.1 (σ x).2.2.1 (σ x).2.2.2.1 (σ x).2.2.2.2) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ f, F a b c d f = ∑ a, ∑ b, ∑ c, ∑ d, ∑ f, G a b c d f := by
  have e : ∀ H : ι → ι → ι → ι → ι → R, ∑ a, ∑ b, ∑ c, ∑ d, ∑ f, H a b c d f =
      ∑ x : ι × ι × ι × ι × ι, H x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
    intro H; simp only [Fintype.sum_prod_type]
  rw [e, e]; exact Fintype.sum_equiv σ _ _ h

/-- `(a, b, c) ↦ (a, c, b)`. -/
def perm23 : ι × ι × ι ≃ ι × ι × ι :=
  ⟨fun x => (x.1, x.2.2, x.2.1), fun x => (x.1, x.2.2, x.2.1), fun _ => rfl, fun _ => rfl⟩

/-- `(a, b, c) ↦ (c, b, a)`. -/
def perm13 : ι × ι × ι ≃ ι × ι × ι :=
  ⟨fun x => (x.2.2, x.2.1, x.1), fun x => (x.2.2, x.2.1, x.1), fun _ => rfl, fun _ => rfl⟩

/-- `(a, b, c) ↦ (c, a, b)`. -/
def permCyc : ι × ι × ι ≃ ι × ι × ι :=
  ⟨fun x => (x.2.2, x.1, x.2.1), fun x => (x.2.1, x.2.2, x.1), fun _ => rfl, fun _ => rfl⟩

/-- `(a, b, c) ↦ (b, c, a)`. -/
def permCyc' : ι × ι × ι ≃ ι × ι × ι :=
  ⟨fun x => (x.2.1, x.2.2, x.1), fun x => (x.2.2, x.1, x.2.1), fun _ => rfl, fun _ => rfl⟩

/-- The covariant derivative `∇_f S_bd` of a `(0,2)` tensor jet. -/
def cov02 (Γ : ι → ι → ι → R) (S : ι → ι → R) (dS : ι → ι → ι → R) : ι → ι → ι → R :=
  fun f b d => dS f b d - ∑ e, (Γ e f b * S e d + Γ e f d * S b e)

/-- The covariant derivative `∇_f T^a_c` of a `(1,1)` tensor jet. -/
def cov11 (Γ : ι → ι → ι → R) (T : ι → ι → R) (dT : ι → ι → ι → R) : ι → ι → ι → R :=
  fun f a c => dT f a c + ∑ e, (Γ a f e * T e c - Γ e f c * T a e)

/-- The Ricci jet `R_bd = R^a_bad`. -/
def ricComp (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R) : ι → ι → R :=
  fun b d => ∑ a, riemComp Γ dΓ a b a d

/-- The jet `∂_f R_bd`. -/
def dRicComp (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R) (ddΓ : ι → ι → ι → ι → ι → R) :
    ι → ι → ι → R := fun f b d => ∑ a, dRiemComp Γ dΓ ddΓ f a b a d

theorem sum_cov13_contract (Γ : ι → ι → ι → R) (T : ι → ι → ι → ι → R)
    (dT : ι → ι → ι → ι → ι → R) (f b d : ι) :
    ∑ a, cov13 Γ T dT f a b a d =
      cov02 Γ (fun b d => ∑ a, T a b a d) (fun f b d => ∑ a, dT f a b a d) f b d := by
  have hz : ∑ a, ∑ e, (Γ a f e * T e b a d - Γ e f a * T a b e d) = 0 := by
    simp only [sum_sub_distrib]
    rw [sub_eq_zero]
    exact sum_swap_eq fun x i => by ring
  simp only [cov13, cov02, sum_add_distrib, mul_sum]
  simp only [sum_sub_distrib] at hz ⊢
  rw [Finset.sum_comm (f := fun a e => Γ e f b * T a e a d),
    Finset.sum_comm (f := fun a e => Γ e f d * T a b a e)]
  linear_combination hz

theorem dRiemComp_skew (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R)
    (ddΓ : ι → ι → ι → ι → ι → R) (f a b c d : ι) :
    dRiemComp Γ dΓ ddΓ f a b c d = -dRiemComp Γ dΓ ddΓ f a b d c := by
  simp only [dRiemComp]
  have : ∑ e, (dΓ f a e c * Γ e b d + Γ a e c * dΓ f e b d - dΓ f a e d * Γ e b c
      - Γ a e d * dΓ f e b c) = -∑ e, (dΓ f a e d * Γ e b c + Γ a e d * dΓ f e b c
      - dΓ f a e c * Γ e b d - Γ a e c * dΓ f e b d) := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun _ _ => by ring
  linear_combination this

theorem cov13_riem_skew (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R)
    (ddΓ : ι → ι → ι → ι → ι → R) (f a b c d : ι) :
    cov13 Γ (riemComp Γ dΓ) (dRiemComp Γ dΓ ddΓ) f a b c d =
      -cov13 Γ (riemComp Γ dΓ) (dRiemComp Γ dΓ ddΓ) f a b d c := by
  simp only [cov13]
  rw [dRiemComp_skew Γ dΓ ddΓ f a b c d, neg_add, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  rw [riemComp_skew Γ dΓ e b d c, riemComp_skew Γ dΓ a e d c, riemComp_skew Γ dΓ a b e c,
    riemComp_skew Γ dΓ a b d e]
  ring

theorem sum_cov13_riem (Γ : ι → ι → ι → R) (dΓ : ι → ι → ι → ι → R)
    (ddΓ : ι → ι → ι → ι → ι → R) (hΓ : ∀ a b c, Γ a b c = Γ a c b)
    (hddΓ : ∀ f e a b c, ddΓ f e a b c = ddΓ e f a b c) (b c d : ι) :
    ∑ a, cov13 Γ (riemComp Γ dΓ) (dRiemComp Γ dΓ ddΓ) a a b c d =
      cov02 Γ (ricComp Γ dΓ) (dRicComp Γ dΓ ddΓ) c b d
        - cov02 Γ (ricComp Γ dΓ) (dRicComp Γ dΓ ddΓ) d b c := by
  have h := sum_congr rfl fun a (_ : a ∈ univ) => cov13_riem_cyclic Γ dΓ ddΓ hΓ hddΓ a a b c d
  simp only [sum_add_distrib, sum_const_zero] at h
  have h1 : ∑ a, cov13 Γ (riemComp Γ dΓ) (dRiemComp Γ dΓ ddΓ) c a b d a =
      -∑ a, cov13 Γ (riemComp Γ dΓ) (dRiemComp Γ dΓ ddΓ) c a b a d := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun a _ => cov13_riem_skew Γ dΓ ddΓ c a b d a
  rw [h1, sum_cov13_contract, sum_cov13_contract] at h
  rw [show ricComp Γ dΓ = fun b d => ∑ a, riemComp Γ dΓ a b a d from rfl,
    show dRicComp Γ dΓ ddΓ = fun f b d => ∑ a, dRiemComp Γ dΓ ddΓ f a b a d from rfl]
  linear_combination h

/-- `∇_f g^{ab} = 0` for a jet `(gi, dgi)` of an inverse metric. -/
def IsParallelInv (Γ : ι → ι → ι → R) (gi : Matrix ι ι R) (dgi : ι → ι → ι → R) : Prop :=
  ∀ f a b, dgi f a b = -∑ c, (gi a c * Γ b f c + Γ a f c * gi c b)

theorem sum_gi_cov02 {Γ : ι → ι → ι → R} {gi : Matrix ι ι R} {dgi : ι → ι → ι → R}
    (hpar : IsParallelInv Γ gi dgi) (S : ι → ι → R) (dS : ι → ι → ι → R) (f : ι) :
    ∑ a, ∑ b, gi a b * cov02 Γ S dS f a b = ∑ a, ∑ b, (dgi f a b * S a b + gi a b * dS f a b) := by
  have hp : ∀ f a b, dgi f a b = _ := hpar
  simp only [cov02, hp]
  simp only [mul_add, mul_sub, add_mul, neg_mul, sum_add_distrib, sum_sub_distrib, sum_neg_distrib,
    sum_mul, mul_sum]
  have e1 : ∑ x, ∑ x_1, ∑ i, gi x x_1 * (Γ i f x * S i x_1) =
      ∑ x, ∑ x_1, ∑ i, Γ x f i * gi i x_1 * S x x_1 :=
    sum3_congr_perm perm13 fun x => by simp only [perm13, Equiv.coe_fn_mk]; ring
  have e2 : ∑ x, ∑ x_1, ∑ i, gi x x_1 * (Γ i f x_1 * S x i) =
      ∑ x, ∑ x_1, ∑ i, gi x i * Γ x_1 f i * S x x_1 :=
    sum3_congr_perm perm23 fun x => by simp only [perm23, Equiv.coe_fn_mk]; ring
  linear_combination -e1 - e2

theorem sum_gi_cov02_left {Γ : ι → ι → ι → R} {gi : Matrix ι ι R} {dgi : ι → ι → ι → R}
    (hpar : IsParallelInv Γ gi dgi) (S : ι → ι → R) (dS : ι → ι → ι → R) (f d c : ι) :
    ∑ b, gi d b * cov02 Γ S dS f b c = cov11 Γ (fun d c => ∑ b, gi d b * S b c)
      (fun f d c => ∑ b, (dgi f d b * S b c + gi d b * dS f b c)) f d c := by
  have hp : ∀ f a b, dgi f a b = _ := hpar
  simp only [cov02, cov11, hp]
  simp only [mul_add, mul_sub, add_mul, neg_mul, sum_add_distrib, sum_sub_distrib, sum_neg_distrib,
    sum_mul, mul_sum]
  have e1 : ∑ x, ∑ i, gi d x * (Γ i f x * S i c) = ∑ x, ∑ i, gi d i * Γ x f i * S x c :=
    sum_swap_eq fun x i => by ring
  have e2 : ∑ x, ∑ i, gi d x * (Γ i f c * S x i) = ∑ x, ∑ i, Γ x f c * (gi d i * S i x) :=
    sum_swap_eq fun x i => by ring
  have e3 : ∑ x, ∑ i, Γ d f i * gi i x * S x c = ∑ x, ∑ i, Γ d f x * (gi x i * S i c) :=
    sum_swap_eq fun x i => by ring
  linear_combination -e1 - e2 + e3

theorem sum_gi_cov13 {Γ : ι → ι → ι → R} {gi : Matrix ι ι R} {dgi : ι → ι → ι → R}
    (hpar : IsParallelInv Γ gi dgi) (T : ι → ι → ι → ι → R) (dT : ι → ι → ι → ι → ι → R)
    (f a c : ι) :
    ∑ b, ∑ d, gi b d * cov13 Γ T dT f a b c d = cov11 Γ (fun a c => ∑ b, ∑ d, gi b d * T a b c d)
      (fun f a c => ∑ b, ∑ d, (dgi f b d * T a b c d + gi b d * dT f a b c d)) f a c := by
  have hp : ∀ f a b, dgi f a b = _ := hpar
  simp only [cov13, cov11, hp]
  simp only [mul_add, mul_sub, add_mul, neg_mul, sum_add_distrib, sum_sub_distrib, sum_neg_distrib,
    sum_mul, mul_sum]
  have e1 : ∑ x, ∑ x_1, ∑ i, gi x x_1 * (Γ a f i * T i x c x_1) =
      ∑ x, ∑ x_1, ∑ i, Γ a f x * (gi x_1 i * T x x_1 c i) :=
    sum3_congr_perm permCyc fun x => by simp only [permCyc, Equiv.coe_fn_mk]; ring
  have e2 : ∑ x, ∑ x_1, ∑ i, gi x x_1 * (Γ i f x * T a i c x_1) =
      ∑ x, ∑ x_1, ∑ i, Γ x f i * gi i x_1 * T a x c x_1 :=
    sum3_congr_perm perm13 fun x => by simp only [perm13, Equiv.coe_fn_mk]; ring
  have e3 : ∑ x, ∑ x_1, ∑ i, gi x x_1 * (Γ i f c * T a x i x_1) =
      ∑ x, ∑ x_1, ∑ i, Γ x f c * (gi x_1 i * T a x_1 x i) :=
    sum3_congr_perm permCyc fun x => by simp only [permCyc, Equiv.coe_fn_mk]; ring
  have e4 : ∑ x, ∑ x_1, ∑ i, gi x x_1 * (Γ i f x_1 * T a x c i) =
      ∑ x, ∑ x_1, ∑ i, gi x i * Γ x_1 f i * T a x c x_1 :=
    sum3_congr_perm perm23 fun x => by simp only [perm23, Equiv.coe_fn_mk]; ring
  linear_combination e1 - e2 - e3 - e4

theorem cov4_interchange (Γ : ι → ι → ι → R) {T : ι → ι → ι → ι → R}
    {dT : ι → ι → ι → ι → ι → R} (hT : Interchange T) (hdT : ∀ f, Interchange (dT f))
    (f a b c d : ι) : cov4 Γ T dT f a b c d = cov4 Γ T dT f c d a b := by
  simp only [cov4]
  rw [hdT f a b c d]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  rw [hT e b c d, hT a e c d, hT a b e d, hT a b c e]
  ring

theorem cov4_pairSkew (Γ : ι → ι → ι → R) {T : ι → ι → ι → ι → R}
    {dT : ι → ι → ι → ι → ι → R} (hT : PairSkew T) (hdT : ∀ f, PairSkew (dT f)) (f : ι) :
    PairSkew (cov4 Γ T dT f) := by
  intro a b c d
  simp only [cov4]
  constructor
  · rw [(hdT f a b c d).1, neg_sub', ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun e _ => ?_
    rw [(hT e b c d).1, (hT a e c d).1, (hT a b e d).1, (hT a b c e).1]
    ring
  · rw [(hdT f a b c d).2, neg_sub', ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun e _ => ?_
    rw [(hT e b c d).2, (hT a e c d).2, (hT a b e d).2, (hT a b c e).2]
    ring

/-! ### Frame components -/

/-- Covariant derivative of a `(0,4)` jet with a separate connection array for each slot. -/
def cov4M (A B C D : ι → ι → ι → R) (T : ι → ι → ι → ι → R) (dT : ι → ι → ι → ι → ι → R) :
    ι → ι → ι → ι → ι → R := fun f a b c d =>
  dT f a b c d - ∑ e, (A e f a * T e b c d + B e f b * T a e c d + C e f c * T a b e d
    + D e f d * T a b c e)

/-- Frame components in the first slot: `T'_μbcd = e^a_μ T_abcd`. -/
def slot1 (e : ι → ι → R) (T : ι → ι → ι → ι → R) : ι → ι → ι → ι → R :=
  fun μ b c d => ∑ a, e a μ * T a b c d
/-- Frame components in the second slot. -/
def slot2 (e : ι → ι → R) (T : ι → ι → ι → ι → R) : ι → ι → ι → ι → R :=
  fun a μ c d => ∑ b, e b μ * T a b c d
/-- Frame components in the third slot. -/
def slot3 (e : ι → ι → R) (T : ι → ι → ι → ι → R) : ι → ι → ι → ι → R :=
  fun a b μ d => ∑ c, e c μ * T a b c d
/-- Frame components in the fourth slot. -/
def slot4 (e : ι → ι → R) (T : ι → ι → ι → ι → R) : ι → ι → ι → ι → R :=
  fun a b c μ => ∑ d, e d μ * T a b c d

/-- Product-rule jet of `slot1 e T`. -/
def dslot1 (e : ι → ι → R) (de : ι → ι → ι → R) (T : ι → ι → ι → ι → R)
    (dT : ι → ι → ι → ι → ι → R) : ι → ι → ι → ι → ι → R :=
  fun h μ b c d => ∑ a, (de h a μ * T a b c d + e a μ * dT h a b c d)
/-- Product-rule jet of `slot2 e T`. -/
def dslot2 (e : ι → ι → R) (de : ι → ι → ι → R) (T : ι → ι → ι → ι → R)
    (dT : ι → ι → ι → ι → ι → R) : ι → ι → ι → ι → ι → R :=
  fun h a μ c d => ∑ b, (de h b μ * T a b c d + e b μ * dT h a b c d)
/-- Product-rule jet of `slot3 e T`. -/
def dslot3 (e : ι → ι → R) (de : ι → ι → ι → R) (T : ι → ι → ι → ι → R)
    (dT : ι → ι → ι → ι → ι → R) : ι → ι → ι → ι → ι → R :=
  fun h a b μ d => ∑ c, (de h c μ * T a b c d + e c μ * dT h a b c d)
/-- Product-rule jet of `slot4 e T`. -/
def dslot4 (e : ι → ι → R) (de : ι → ι → ι → R) (T : ι → ι → ι → ι → R)
    (dT : ι → ι → ι → ι → ι → R) : ι → ι → ι → ι → ι → R :=
  fun h a b c μ => ∑ d, (de h d μ * T a b c d + e d μ * dT h a b c d)

/-- The mixed connection coefficients `Γ'` of a frame `e` (`∇_h e_μ = Γ'^λ_{hμ} e_λ`). -/
def IsFrameConn (Γ : ι → ι → ι → R) (e : ι → ι → R) (de : ι → ι → ι → R)
    (Γ' : ι → ι → ι → R) : Prop :=
  ∀ h a μ, ∑ l, Γ' l h μ * e a l = de h a μ + ∑ c, Γ a h c * e c μ

theorem cov4M_slot1 {Γ Γ' : ι → ι → ι → R} {e : ι → ι → R} {de : ι → ι → ι → R}
    (hrel : IsFrameConn Γ e de Γ') (B C D : ι → ι → ι → R) (T : ι → ι → ι → ι → R)
    (dT : ι → ι → ι → ι → ι → R) (h μ b c d : ι) :
    cov4M Γ' B C D (slot1 e T) (dslot1 e de T dT) h μ b c d =
      ∑ a, e a μ * cov4M Γ B C D T dT h a b c d := by
  have k : ∑ l, Γ' l h μ * ∑ a, e a l * T a b c d =
      ∑ a, de h a μ * T a b c d + ∑ a, ∑ l, e a μ * (Γ l h a * T l b c d) := by
    calc ∑ l, Γ' l h μ * ∑ a, e a l * T a b c d
        = ∑ a, (∑ l, Γ' l h μ * e a l) * T a b c d := by
          simp only [mul_sum, sum_mul]; exact sum_swap_eq fun x i => by ring
      _ = ∑ a, (de h a μ + ∑ c, Γ a h c * e c μ) * T a b c d :=
          sum_congr rfl fun a _ => by rw [hrel h a μ]
      _ = _ := by
          simp only [add_mul, sum_add_distrib, sum_mul]
          congr 1
          exact sum_swap_eq fun x i => by ring
  simp only [cov4M, slot1, dslot1, mul_sub, mul_add, sum_add_distrib, sum_sub_distrib, mul_sum]
  simp only [← mul_sum] at k ⊢
  rw [k]
  have e2 : ∑ x, B x h b * ∑ a, e a μ * T a x c d = ∑ x, e x μ * ∑ i, B i h b * T x i c d := by
    simp only [mul_sum]; exact sum_swap_eq fun x i => by ring
  have e3 : ∑ x, C x h c * ∑ a, e a μ * T a b x d = ∑ x, e x μ * ∑ i, C i h c * T x b i d := by
    simp only [mul_sum]; exact sum_swap_eq fun x i => by ring
  have e4 : ∑ x, D x h d * ∑ a, e a μ * T a b c x = ∑ x, e x μ * ∑ i, D i h d * T x b c i := by
    simp only [mul_sum]; exact sum_swap_eq fun x i => by ring
  rw [e2, e3, e4]
  simp only [mul_sum]
  ring

theorem cov4M_slot2 {Γ Γ' : ι → ι → ι → R} {e : ι → ι → R} {de : ι → ι → ι → R}
    (hrel : IsFrameConn Γ e de Γ') (A C D : ι → ι → ι → R) (T : ι → ι → ι → ι → R)
    (dT : ι → ι → ι → ι → ι → R) (h a μ c d : ι) :
    cov4M A Γ' C D (slot2 e T) (dslot2 e de T dT) h a μ c d =
      ∑ b, e b μ * cov4M A Γ C D T dT h a b c d := by
  have k : ∑ l, Γ' l h μ * ∑ b, e b l * T a b c d =
      ∑ b, de h b μ * T a b c d + ∑ b, ∑ l, e b μ * (Γ l h b * T a l c d) := by
    calc ∑ l, Γ' l h μ * ∑ b, e b l * T a b c d
        = ∑ b, (∑ l, Γ' l h μ * e b l) * T a b c d := by
          simp only [mul_sum, sum_mul]; exact sum_swap_eq fun x i => by ring
      _ = ∑ b, (de h b μ + ∑ c', Γ b h c' * e c' μ) * T a b c d :=
          sum_congr rfl fun b _ => by rw [hrel h b μ]
      _ = _ := by
          simp only [add_mul, sum_add_distrib, sum_mul]
          congr 1
          exact sum_swap_eq fun x i => by ring
  simp only [cov4M, slot2, dslot2, mul_sub, mul_add, sum_add_distrib, sum_sub_distrib, mul_sum]
  simp only [← mul_sum] at k ⊢
  rw [k]
  have e1 : ∑ x, A x h a * ∑ b, e b μ * T x b c d = ∑ x, e x μ * ∑ i, A i h a * T i x c d := by
    simp only [mul_sum]; exact sum_swap_eq fun x i => by ring
  have e3 : ∑ x, C x h c * ∑ b, e b μ * T a b x d = ∑ x, e x μ * ∑ i, C i h c * T a x i d := by
    simp only [mul_sum]; exact sum_swap_eq fun x i => by ring
  have e4 : ∑ x, D x h d * ∑ b, e b μ * T a b c x = ∑ x, e x μ * ∑ i, D i h d * T a x c i := by
    simp only [mul_sum]; exact sum_swap_eq fun x i => by ring
  rw [e1, e3, e4]
  simp only [mul_sum]
  ring

theorem cov4M_slot3 {Γ Γ' : ι → ι → ι → R} {e : ι → ι → R} {de : ι → ι → ι → R}
    (hrel : IsFrameConn Γ e de Γ') (A B D : ι → ι → ι → R) (T : ι → ι → ι → ι → R)
    (dT : ι → ι → ι → ι → ι → R) (h a b μ d : ι) :
    cov4M A B Γ' D (slot3 e T) (dslot3 e de T dT) h a b μ d =
      ∑ c, e c μ * cov4M A B Γ D T dT h a b c d := by
  have k : ∑ l, Γ' l h μ * ∑ c, e c l * T a b c d =
      ∑ c, de h c μ * T a b c d + ∑ c, ∑ l, e c μ * (Γ l h c * T a b l d) := by
    calc ∑ l, Γ' l h μ * ∑ c, e c l * T a b c d
        = ∑ c, (∑ l, Γ' l h μ * e c l) * T a b c d := by
          simp only [mul_sum, sum_mul]; exact sum_swap_eq fun x i => by ring
      _ = ∑ c, (de h c μ + ∑ c', Γ c h c' * e c' μ) * T a b c d :=
          sum_congr rfl fun c _ => by rw [hrel h c μ]
      _ = _ := by
          simp only [add_mul, sum_add_distrib, sum_mul]
          congr 1
          exact sum_swap_eq fun x i => by ring
  simp only [cov4M, slot3, dslot3, mul_sub, mul_add, sum_add_distrib, sum_sub_distrib, mul_sum]
  simp only [← mul_sum] at k ⊢
  rw [k]
  have e1 : ∑ x, A x h a * ∑ c, e c μ * T x b c d = ∑ x, e x μ * ∑ i, A i h a * T i b x d := by
    simp only [mul_sum]; exact sum_swap_eq fun x i => by ring
  have e2 : ∑ x, B x h b * ∑ c, e c μ * T a x c d = ∑ x, e x μ * ∑ i, B i h b * T a i x d := by
    simp only [mul_sum]; exact sum_swap_eq fun x i => by ring
  have e4 : ∑ x, D x h d * ∑ c, e c μ * T a b c x = ∑ x, e x μ * ∑ i, D i h d * T a b x i := by
    simp only [mul_sum]; exact sum_swap_eq fun x i => by ring
  rw [e1, e2, e4]
  simp only [mul_sum]
  ring

theorem cov4M_slot4 {Γ Γ' : ι → ι → ι → R} {e : ι → ι → R} {de : ι → ι → ι → R}
    (hrel : IsFrameConn Γ e de Γ') (A B C : ι → ι → ι → R) (T : ι → ι → ι → ι → R)
    (dT : ι → ι → ι → ι → ι → R) (h a b c μ : ι) :
    cov4M A B C Γ' (slot4 e T) (dslot4 e de T dT) h a b c μ =
      ∑ d, e d μ * cov4M A B C Γ T dT h a b c d := by
  have k : ∑ l, Γ' l h μ * ∑ d, e d l * T a b c d =
      ∑ d, de h d μ * T a b c d + ∑ d, ∑ l, e d μ * (Γ l h d * T a b c l) := by
    calc ∑ l, Γ' l h μ * ∑ d, e d l * T a b c d
        = ∑ d, (∑ l, Γ' l h μ * e d l) * T a b c d := by
          simp only [mul_sum, sum_mul]; exact sum_swap_eq fun x i => by ring
      _ = ∑ d, (de h d μ + ∑ c', Γ d h c' * e c' μ) * T a b c d :=
          sum_congr rfl fun d _ => by rw [hrel h d μ]
      _ = _ := by
          simp only [add_mul, sum_add_distrib, sum_mul]
          congr 1
          exact sum_swap_eq fun x i => by ring
  simp only [cov4M, slot4, dslot4, mul_sub, mul_add, sum_add_distrib, sum_sub_distrib, mul_sum]
  simp only [← mul_sum] at k ⊢
  rw [k]
  have e1 : ∑ x, A x h a * ∑ d, e d μ * T x b c d = ∑ x, e x μ * ∑ i, A i h a * T i b c x := by
    simp only [mul_sum]; exact sum_swap_eq fun x i => by ring
  have e2 : ∑ x, B x h b * ∑ d, e d μ * T a x c d = ∑ x, e x μ * ∑ i, B i h b * T a i c x := by
    simp only [mul_sum]; exact sum_swap_eq fun x i => by ring
  have e3 : ∑ x, C x h c * ∑ d, e d μ * T a b x d = ∑ x, e x μ * ∑ i, C i h c * T a b i x := by
    simp only [mul_sum]; exact sum_swap_eq fun x i => by ring
  rw [e1, e2, e3]
  simp only [mul_sum]
  ring

/-- The frame derivative jet `e_κ(T) = e^h_κ ∂_h T`. -/
def frameJet (e : ι → ι → R) (dT : ι → ι → ι → ι → ι → R) : ι → ι → ι → ι → ι → R :=
  fun κ μ ν ρ σ => ∑ h, e h κ * dT h μ ν ρ σ

/-- The frame connection coefficients `γ^λ_{κν} = e^h_κ Γ'^λ_{hν}`. -/
def frameConn (e : ι → ι → R) (Γ' : ι → ι → ι → R) : ι → ι → ι → R :=
  fun l κ ν => ∑ h, e h κ * Γ' l h ν

/-- Frame components `T_μνρσ = e^a_μ e^b_ν e^c_ρ e^d_σ T_abcd`. -/
def frame4 (e : ι → ι → R) (T : ι → ι → ι → ι → R) : ι → ι → ι → ι → R :=
  slot1 e (slot2 e (slot3 e (slot4 e T)))

/-- The product-rule jet of `frame4 e T`. -/
def dframe4 (e : ι → ι → R) (de : ι → ι → ι → R) (T : ι → ι → ι → ι → R)
    (dT : ι → ι → ι → ι → ι → R) : ι → ι → ι → ι → ι → R :=
  dslot1 e de (slot2 e (slot3 e (slot4 e T)))
    (dslot2 e de (slot3 e (slot4 e T)) (dslot3 e de (slot4 e T) (dslot4 e de T dT)))

theorem cov4_frameJet (e : ι → ι → R) (Γ' : ι → ι → ι → R) (T : ι → ι → ι → ι → R)
    (dT : ι → ι → ι → ι → ι → R) (κ μ ν ρ σ : ι) :
    cov4 (frameConn e Γ') T (frameJet e dT) κ μ ν ρ σ =
      ∑ h, e h κ * cov4M Γ' Γ' Γ' Γ' T dT h μ ν ρ σ := by
  simp only [cov4, cov4M, frameJet, frameConn, mul_sub, sum_sub_distrib, mul_sum, sum_mul]
  congr 1
  simp only [mul_add, sum_add_distrib]
  have k : ∀ F : ι → ι → R, ∑ x, ∑ i, e i κ * F x i = ∑ x, ∑ i, e x κ * F i x :=
    fun F => sum_swap_eq fun x i => rfl
  simp only [mul_assoc]
  rw [k fun x i => Γ' x i μ * T x ν ρ σ, k fun x i => Γ' x i ν * T μ x ρ σ,
    k fun x i => Γ' x i ρ * T μ ν x σ, k fun x i => Γ' x i σ * T μ ν ρ x]

theorem cov4_frame4 {Γ Γ' : ι → ι → ι → R} {e : ι → ι → R} {de : ι → ι → ι → R}
    (hrel : IsFrameConn Γ e de Γ') (T : ι → ι → ι → ι → R) (dT : ι → ι → ι → ι → ι → R)
    (κ μ ν ρ σ : ι) :
    cov4 (frameConn e Γ') (frame4 e T) (frameJet e (dframe4 e de T dT)) κ μ ν ρ σ =
      ∑ h, e h κ * ∑ a, e a μ * ∑ b, e b ν * ∑ c, e c ρ * ∑ d, e d σ *
        cov4 Γ T dT h a b c d := by
  rw [cov4_frameJet]
  refine sum_congr rfl fun h _ => ?_
  congr 1
  rw [frame4, dframe4, cov4M_slot1 hrel]
  refine sum_congr rfl fun a _ => ?_
  rw [cov4M_slot2 hrel]
  congr 1; refine sum_congr rfl fun b _ => ?_
  rw [cov4M_slot3 hrel]
  congr 1; refine sum_congr rfl fun c _ => ?_
  rw [cov4M_slot4 hrel]
  rfl

theorem frame_cyclic {Γ Γ' : ι → ι → ι → R} {e : ι → ι → R} {de : ι → ι → ι → R}
    (hrel : IsFrameConn Γ e de Γ') (T : ι → ι → ι → ι → R) (dT : ι → ι → ι → ι → ι → R)
    (hcyc : ∀ h a b c d, cov4 Γ T dT h a b c d + cov4 Γ T dT a b h c d
      + cov4 Γ T dT b h a c d = 0) (κ μ ν ρ σ : ι) :
    cov4 (frameConn e Γ') (frame4 e T) (frameJet e (dframe4 e de T dT)) κ μ ν ρ σ
      + cov4 (frameConn e Γ') (frame4 e T) (frameJet e (dframe4 e de T dT)) μ ν κ ρ σ
      + cov4 (frameConn e Γ') (frame4 e T) (frameJet e (dframe4 e de T dT)) ν κ μ ρ σ = 0 := by
  simp only [cov4_frame4 hrel]
  set Z : ι → ι → ι → R := fun h a b => ∑ c, e c ρ * ∑ d, e d σ * cov4 Γ T dT h a b c d
    with hZ
  have hZc : ∀ h a b, Z h a b + Z a b h + Z b h a = 0 := by
    intro h a b
    simp only [hZ, ← sum_add_distrib, ← mul_add]
    exact sum_eq_zero fun c _ => by
      rw [sum_eq_zero fun d _ => by rw [hcyc h a b c d, mul_zero], mul_zero]
  have hX : ∀ κ μ ν, ∑ h, e h κ * ∑ a, e a μ * ∑ b, e b ν * Z h a b =
      ∑ h, ∑ a, ∑ b, e h κ * e a μ * e b ν * Z h a b := fun κ μ ν => by
    simp only [mul_sum, mul_assoc]
  simp only [← hZ] at *
  rw [hX, hX, hX]
  have h2 : ∑ h, ∑ a, ∑ b, e h μ * e a ν * e b κ * Z h a b =
      ∑ h, ∑ a, ∑ b, e h κ * e a μ * e b ν * Z a b h :=
    sum3_congr_perm permCyc fun x => by simp only [permCyc, Equiv.coe_fn_mk]; ring
  have h3 : ∑ h, ∑ a, ∑ b, e h ν * e a κ * e b μ * Z h a b =
      ∑ h, ∑ a, ∑ b, e h κ * e a μ * e b ν * Z b h a :=
    sum3_congr_perm permCyc' fun x => by simp only [permCyc', Equiv.coe_fn_mk]; ring
  rw [h2, h3, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_eq_zero fun h _ => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_eq_zero fun a _ => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_eq_zero fun b _ => ?_
  rw [← mul_add, ← mul_add, hZc, mul_zero]

theorem frame4_eq (e : ι → ι → R) (T : ι → ι → ι → ι → R) (μ ν ρ σ : ι) :
    frame4 e T μ ν ρ σ = ∑ a, ∑ b, ∑ c, ∑ d, e a μ * e b ν * e c ρ * e d σ * T a b c d := by
  simp only [frame4, slot1, slot2, slot3, slot4, mul_sum, mul_assoc]

theorem frame4_pairSkew (e : ι → ι → R) {T : ι → ι → ι → ι → R} (hT : PairSkew T) :
    PairSkew (frame4 e T) := by
  intro μ ν ρ σ
  simp only [frame4_eq]
  constructor
  · rw [Finset.sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun c _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun d _ => ?_
    rw [(hT b a c d).1]; ring
  · rw [← sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun d _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun c _ => ?_
    rw [(hT a b d c).2]; ring

theorem frame4_bianchi1 (e : ι → ι → R) {T : ι → ι → ι → ι → R} (hT : Bianchi1 T) :
    Bianchi1 (frame4 e T) := by
  intro μ ν ρ σ
  simp only [frame4_eq, ← sum_add_distrib]
  refine sum_eq_zero fun a _ => ?_
  have h2 : ∑ b, ∑ c, ∑ d, e a μ * e b ρ * e c σ * e d ν * T a b c d =
      ∑ b, ∑ c, ∑ d, e a μ * e b ν * e c ρ * e d σ * T a c d b :=
    sum3_congr_perm permCyc fun x => by simp only [permCyc, Equiv.coe_fn_mk]; ring
  have h3 : ∑ b, ∑ c, ∑ d, e a μ * e b σ * e c ν * e d ρ * T a b c d =
      ∑ b, ∑ c, ∑ d, e a μ * e b ν * e c ρ * e d σ * T a d b c :=
    sum3_congr_perm permCyc' fun x => by simp only [permCyc', Equiv.coe_fn_mk]; ring
  simp only [sum_add_distrib] at h2 h3 ⊢
  rw [h2, h3, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_eq_zero fun b _ => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_eq_zero fun c _ => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_eq_zero fun d _ => ?_
  rw [← mul_add, ← mul_add, hT a b c d, mul_zero]

theorem frame4_trace13 (e : ι → ι → R) (w : ι → R) (T : ι → ι → ι → ι → R) (ν σ : ι) :
    ∑ μ, w μ * frame4 e T μ ν μ σ =
      ∑ b, ∑ d, e b ν * e d σ * ∑ a, ∑ c, (∑ μ, w μ * e a μ * e c μ) * T a b c d := by
  simp only [frame4_eq, mul_sum, sum_mul]
  exact sum5_congr_perm
    ⟨fun x => (x.2.2.1, x.2.2.2.2, x.2.1, x.2.2.2.1, x.1),
      fun y => (y.2.2.2.2, y.2.2.1, y.1, y.2.2.2.1, y.2.1), fun _ => rfl, fun _ => rfl⟩
    fun x => by simp only [Equiv.coe_fn_mk]; ring

end Jet

section Field

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The first jet `∂_e Γ^a_bc` of a connection field. -/
def dChr (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) : ι → ι → ι → ι → ℝ :=
  fun e a b c => partialDeriv e (fun y => Γ y a b c) x

/-- The second jet `∂_f ∂_e Γ^a_bc` of a connection field. -/
def ddChr (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) : ι → ι → ι → ι → ι → ℝ :=
  fun f e a b c => partialDeriv f (fun y => partialDeriv e (fun z => Γ z a b c) y) x

/-- A `C²` metric field `g` and its `C²` torsion-free compatible connection `Γ`. -/
structure IsLeviCivita (g : (ι → ℝ) → Matrix ι ι ℝ) (Γ : (ι → ℝ) → ι → ι → ι → ℝ) : Prop where
  symm : ∀ x, (g x).IsSymm
  contDiff_metric : ∀ a b, ContDiff ℝ 2 fun x => g x a b
  contDiff_chr : ∀ a b c, ContDiff ℝ 2 fun x => Γ x a b c
  torsionFree : ∀ x a b c, Γ x a b c = Γ x a c b
  compat : ∀ x e a b,
    partialDeriv e (fun y => g y a b) x = ∑ r, (g x r b * Γ x r e a + g x a r * Γ x r e b)

/-- The covariant derivative `∇_f R^a_bcd` of the Riemann tensor field. -/
def covRiemField (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) : ι → ι → ι → ι → ι → ℝ :=
  cov13 (Γ x) (riemField Γ x) fun f a b c d => partialDeriv f (fun y => riemField Γ y a b c d) x

theorem partialDeriv_riemField {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (hΓ : ∀ a b c, ContDiff ℝ 2 fun y => Γ y a b c) (x : ι → ℝ) (f a b c d : ι) :
    partialDeriv f (fun y => riemField Γ y a b c d) x =
      dRiemComp (Γ x) (dChr Γ x) (ddChr Γ x) f a b c d := by
  have h1 : ∀ a b c, Differentiable ℝ fun y => Γ y a b c := fun a b c =>
    (hΓ a b c).differentiable (by norm_num)
  have h2 : ∀ e a b c, Differentiable ℝ fun y => partialDeriv e (fun z => Γ z a b c) y :=
    fun e a b c => (hΓ a b c).differentiable_partialDeriv le_rfl e
  simp only [riemField, riemComp, dRiemComp, dChr, ddChr]
  rw [partialDeriv_add (by fun_prop) (by fun_prop), partialDeriv_sub (by fun_prop) (by fun_prop),
    partialDeriv_sum _ (fun e _ => by fun_prop)]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  rw [partialDeriv_sub (by fun_prop) (by fun_prop), partialDeriv_mul (by fun_prop) (by fun_prop),
    partialDeriv_mul (by fun_prop) (by fun_prop)]
  ring

theorem covRiemField_eq {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (hΓ : ∀ a b c, ContDiff ℝ 2 fun y => Γ y a b c) (x : ι → ℝ) :
    covRiemField Γ x =
      cov13 (Γ x) (riemComp (Γ x) (dChr Γ x)) (dRiemComp (Γ x) (dChr Γ x) (ddChr Γ x)) := by
  unfold covRiemField
  congr 1
  funext f a b c d
  exact partialDeriv_riemField hΓ x f a b c d

theorem covRiemField_cyclic {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (hΓC : ∀ a b c, ContDiff ℝ 2 fun y => Γ y a b c) (hΓ : ∀ x a b c, Γ x a b c = Γ x a c b)
    (x : ι → ℝ) (f a b c d : ι) :
    covRiemField Γ x f a b c d + covRiemField Γ x c a b d f + covRiemField Γ x d a b f c = 0 := by
  rw [covRiemField_eq hΓC]
  exact cov13_riem_cyclic _ _ _ (hΓ x)
    (fun f e a b c => partialDeriv_comm (hΓC a b c) f e x) f a b c d

theorem differentiable_riemField {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (hΓ : ∀ a b c, ContDiff ℝ 2 fun y => Γ y a b c) (a b c d : ι) :
    Differentiable ℝ fun y => riemField Γ y a b c d := by
  have h1 : ∀ a b c, Differentiable ℝ fun y => Γ y a b c := fun a b c =>
    (hΓ a b c).differentiable (by norm_num)
  have h2 : ∀ e a b c, Differentiable ℝ fun y => partialDeriv e (fun z => Γ z a b c) y :=
    fun e a b c => (hΓ a b c).differentiable_partialDeriv le_rfl e
  simp only [riemField, riemComp]
  fun_prop

/-- The lowered Riemann tensor field `R_abcd = g_ae R^e_bcd`. -/
def riemLowField (g : (ι → ℝ) → Matrix ι ι ℝ) (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) :
    ι → ι → ι → ι → ℝ := lower (g x) (riemField Γ x)

/-- The covariant derivative `∇_f R_abcd` of the lowered Riemann tensor field. -/
def covRiemLowField (g : (ι → ℝ) → Matrix ι ι ℝ) (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) :
    ι → ι → ι → ι → ι → ℝ :=
  cov4 (Γ x) (riemLowField g Γ x) fun f a b c d =>
    partialDeriv f (fun y => riemLowField g Γ y a b c d) x

theorem covRiemLowField_eq {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) (x : ι → ℝ) (f a b c d : ι) :
    covRiemLowField g Γ x f a b c d = ∑ e, g x a e * covRiemField Γ x f e b c d := by
  have hg : ∀ a b, Differentiable ℝ fun y => g y a b := fun a b =>
    (h.contDiff_metric a b).differentiable (by norm_num)
  have hR := differentiable_riemField h.contDiff_chr
  have hd : (fun f a b c d => partialDeriv f (fun y => riemLowField g Γ y a b c d) x) =
      dLower (g x) (fun e a b => partialDeriv e (fun y => g y a b) x) (riemField Γ x)
        (fun f a b c d => partialDeriv f (fun y => riemField Γ y a b c d) x) := by
    funext f a b c d
    simp only [riemLowField, lower, dLower]
    rw [partialDeriv_sum _ (fun e _ => by fun_prop)]
    refine sum_congr rfl fun e _ => ?_
    rw [partialDeriv_mul (by fun_prop) (by fun_prop)]
  unfold covRiemLowField
  rw [hd]
  exact cov4_lower (Γ x) (g x) _ (h.compat x) _ _ f a b c d

theorem covRiemLowField_cyclic {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) (x : ι → ℝ) (f a b c d : ι) :
    covRiemLowField g Γ x f a b c d + covRiemLowField g Γ x c a b d f
      + covRiemLowField g Γ x d a b f c = 0 := by
  simp only [covRiemLowField_eq h, ← sum_add_distrib, ← mul_add]
  exact sum_eq_zero fun e _ => by
    rw [covRiemField_cyclic h.contDiff_chr h.torsionFree x f e b c d, mul_zero]

theorem riemLowField_interchange {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) (x : ι → ℝ) : Interchange (riemLowField g Γ x) :=
  (riemField_isAlgCurv g Γ h.symm h.contDiff_metric
    (fun a b c => (h.contDiff_chr a b c).differentiable (by norm_num)) h.torsionFree h.compat x).2.2

theorem riemLowField_pairSkew {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) (x : ι → ℝ) : PairSkew (riemLowField g Γ x) :=
  (riemField_isAlgCurv g Γ h.symm h.contDiff_metric
    (fun a b c => (h.contDiff_chr a b c).differentiable (by norm_num)) h.torsionFree h.compat x).1

theorem riemLowField_bianchi1 {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) (x : ι → ℝ) : Bianchi1 (riemLowField g Γ x) :=
  (riemField_isAlgCurv g Γ h.symm h.contDiff_metric
    (fun a b c => (h.contDiff_chr a b c).differentiable (by norm_num)) h.torsionFree h.compat x).2.1

theorem covRiemLowField_cyclic_first {g : (ι → ℝ) → Matrix ι ι ℝ}
    {Γ : (ι → ℝ) → ι → ι → ι → ℝ} (h : IsLeviCivita g Γ) (x : ι → ℝ) (f a b c d : ι) :
    covRiemLowField g Γ x f a b c d + covRiemLowField g Γ x a b f c d
      + covRiemLowField g Γ x b f a c d = 0 := by
  have hI := riemLowField_interchange h
  have hX : ∀ f a b c d, covRiemLowField g Γ x f a b c d = covRiemLowField g Γ x f c d a b :=
    fun f a b c d => cov4_interchange _ (hI x) (fun f a b c d => by
      show partialDeriv f _ x = partialDeriv f _ x
      congr 1; funext y; exact hI y a b c d) f a b c d
  rw [hX f a b c d, hX a b f c d, hX b f a c d]
  exact covRiemLowField_cyclic h x f c d a b

/-- The Ricci tensor field `R_bd = R^a_bad`. -/
def ricField (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) : ι → ι → ℝ :=
  fun b d => ∑ a, riemField Γ x a b a d

/-- The covariant derivative `∇_f R_bd` of the Ricci tensor field. -/
def covRicField (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) : ι → ι → ι → ℝ :=
  cov02 (Γ x) (ricField Γ x) fun f b d => partialDeriv f (fun y => ricField Γ y b d) x

/-- The contracted second Bianchi identity `∇_a R^a_bcd = ∇_c R_bd - ∇_d R_bc` for a `C²`
torsion-free connection field. -/
theorem div_riemField {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (hΓC : ∀ a b c, ContDiff ℝ 2 fun y => Γ y a b c) (hΓ : ∀ x a b c, Γ x a b c = Γ x a c b)
    (x : ι → ℝ) (b c d : ι) :
    ∑ a, covRiemField Γ x a a b c d = covRicField Γ x c b d - covRicField Γ x d b c := by
  have hR := differentiable_riemField hΓC
  have e : covRicField Γ x =
      cov02 (Γ x) (ricComp (Γ x) (dChr Γ x)) (dRicComp (Γ x) (dChr Γ x) (ddChr Γ x)) := by
    unfold covRicField
    congr 1
    funext f b d
    simp only [ricField, dRicComp]
    rw [partialDeriv_sum _ (fun a _ => by fun_prop)]
    exact sum_congr rfl fun a _ => partialDeriv_riemField hΓC x f a b a d
  rw [e, covRiemField_eq hΓC]
  exact sum_cov13_riem _ _ _ (hΓ x) (fun f e a b c => partialDeriv_comm (hΓC a b c) f e x) b c d

theorem covRicField_eq_zero {Γ : (ι → ℝ) → ι → ι → ι → ℝ} (hvac : ∀ y, ricField Γ y = 0)
    (x : ι → ℝ) (f b d : ι) : covRicField Γ x f b d = 0 := by
  have e : ∀ b d, (fun y => ricField Γ y b d) = fun _ => 0 := fun b d =>
    funext fun y => by rw [hvac y]; rfl
  simp only [covRicField, cov02, e, partialDeriv_const, hvac x, Pi.zero_apply, mul_zero,
    add_zero, sum_const_zero, sub_zero]

theorem div_riemField_vacuum {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (hΓC : ∀ a b c, ContDiff ℝ 2 fun y => Γ y a b c) (hΓ : ∀ x a b c, Γ x a b c = Γ x a c b)
    (hvac : ∀ y, ricField Γ y = 0) (x : ι → ℝ) (b c d : ι) :
    ∑ a, covRiemField Γ x a a b c d = 0 := by
  rw [div_riemField hΓC hΓ, covRicField_eq_zero hvac, covRicField_eq_zero hvac, sub_zero]

theorem isParallelInv_field {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) {gi : (ι → ℝ) → Matrix ι ι ℝ} (hinv : ∀ y, gi y * g y = 1)
    (hgi : ∀ a b, Differentiable ℝ fun y => gi y a b) (x : ι → ℝ) :
    IsParallelInv (Γ x) (gi x) fun f a b => partialDeriv f (fun y => gi y a b) x := by
  intro f a b
  have hg : ∀ a b, Differentiable ℝ fun y => g y a b := fun a b =>
    (h.contDiff_metric a b).differentiable (by norm_num)
  let D : Matrix ι ι ℝ := Matrix.of fun a b => partialDeriv f (fun y => gi y a b) x
  let Dg : Matrix ι ι ℝ := Matrix.of fun a b => partialDeriv f (fun y => g y a b) x
  let C : Matrix ι ι ℝ := Matrix.of fun r c => Γ x r f c
  have hprod : D * g x + gi x * Dg = 0 := by
    ext a d
    have hc : (fun y => (gi y * g y) a d) = fun _ => (1 : Matrix ι ι ℝ) a d :=
      funext fun y => by rw [hinv y]
    have h0 := congrArg (fun F => partialDeriv f F x) hc
    simp only [partialDeriv_const, Matrix.mul_apply] at h0
    rw [partialDeriv_sum _ (fun c _ => by fun_prop)] at h0
    simp only [Matrix.add_apply, Matrix.mul_apply, D, Dg, Matrix.of_apply, ← sum_add_distrib,
      Matrix.zero_apply]
    rw [← h0]
    exact sum_congr rfl fun c _ => by rw [partialDeriv_mul (by fun_prop) (by fun_prop)]
  have hDg : Dg = Cᵀ * g x + g x * C := by
    ext c d
    simp only [Dg, C, Matrix.of_apply, h.compat, Matrix.add_apply, Matrix.mul_apply,
      Matrix.transpose_apply, sum_add_distrib]
    congr 1
    exact sum_congr rfl fun r _ => by ring
  have hginv : g x * gi x = 1 := Metric.mul_eq_one_comm'.1 (hinv x)
  have hD : D = -(gi x * Cᵀ + C * gi x) := by
    calc D = D * g x * gi x := by rw [Matrix.mul_assoc, hginv, Matrix.mul_one]
      _ = -(gi x * Dg) * gi x := by rw [eq_neg_of_add_eq_zero_left hprod]
      _ = -(gi x * Cᵀ + C * gi x) := by
        rw [hDg, Matrix.mul_add, Matrix.neg_mul, Matrix.add_mul, ← Matrix.mul_assoc,
          ← Matrix.mul_assoc, hinv x, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
          hginv, Matrix.mul_one]
  have := congrFun (congrFun hD a) b
  simp only [D, C, Matrix.of_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply] at this
  show partialDeriv f (fun y => gi y a b) x = _
  rw [this, sum_add_distrib]

/-- The mixed Ricci field `R^a_c = g^{ab} R_bc`. -/
def ricUpField (gi : (ι → ℝ) → Matrix ι ι ℝ) (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) :
    ι → ι → ℝ := fun a c => ∑ b, gi x a b * ricField Γ x b c

/-- The scalar curvature field `R = g^{bd} R_bd`. -/
def scalField (gi : (ι → ℝ) → Matrix ι ι ℝ) (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ b, ∑ d, gi x b d * ricField Γ x b d

/-- The mixed Einstein field `G^a_c = R^a_c - ½ δ^a_c R`. -/
def einsteinUpField (gi : (ι → ℝ) → Matrix ι ι ℝ) (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) :
    ι → ι → ℝ := fun a c => ricUpField gi Γ x a c - (if a = c then 1 else 0) * scalField gi Γ x / 2

/-- The covariant divergence `∇_a T^a_c` of a `(1,1)` tensor field. -/
def divMixed (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (T : (ι → ℝ) → ι → ι → ℝ) (x : ι → ℝ) (c : ι) : ℝ :=
  ∑ a, cov11 (Γ x) (T x) (fun f a c => partialDeriv f (fun y => T y a c) x) a a c

theorem riemField_eq_raise {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    {gi : Matrix ι ι ℝ} {x : ι → ℝ} (hinv : gi * g x = 1) (a b c d : ι) :
    riemField Γ x a b c d = ∑ e, gi a e * riemLowField g Γ x e b c d := by
  simp only [riemLowField, lower, mul_sum]
  rw [Finset.sum_comm]
  have hcf : ∀ h, ∑ e, gi a e * g x e h = (1 : Matrix ι ι ℝ) a h := fun h => by
    rw [← hinv]; rfl
  calc riemField Γ x a b c d = ∑ h, (1 : Matrix ι ι ℝ) a h * riemField Γ x h b c d := by
        simp [Matrix.one_apply]
    _ = _ := by
        refine sum_congr rfl fun h _ => ?_
        rw [← hcf h, sum_mul]
        exact sum_congr rfl fun e _ => by ring

theorem contract_riemLowField {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) {gi : Matrix ι ι ℝ} {x : ι → ℝ} (hinv : gi * g x = 1) (e c : ι) :
    ∑ b, ∑ d, gi b d * riemLowField g Γ x e b c d = ricField Γ x e c := by
  have hs := Metric.isSymm_of_mul_eq_one (h.symm x) hinv
  have hS := riemLowField_pairSkew h x
  simp only [ricField, riemField_eq_raise hinv]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun d _ => sum_congr rfl fun b _ => ?_
  rw [(hS b e d c).1, (hS e b d c).2, hs.apply d b]
  ring

theorem contract_riemField {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) {gi : (ι → ℝ) → Matrix ι ι ℝ} (hinv : ∀ y, gi y * g y = 1)
    (x : ι → ℝ) (a c : ι) :
    ∑ b, ∑ d, gi x b d * riemField Γ x a b c d = ricUpField gi Γ x a c := by
  simp only [ricUpField, ← contract_riemLowField h (hinv x), riemField_eq_raise (hinv x),
    mul_sum]
  exact sum3_congr_perm permCyc fun y => by simp only [permCyc, Equiv.coe_fn_mk]; ring

theorem two_mul_divMixed_ricUp {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) {gi : (ι → ℝ) → Matrix ι ι ℝ} (hinv : ∀ y, gi y * g y = 1)
    (hgi : ∀ a b, Differentiable ℝ fun y => gi y a b) (x : ι → ℝ) (c : ι) :
    2 * divMixed Γ (ricUpField gi Γ) x c = partialDeriv c (scalField gi Γ) x := by
  have hpar := isParallelInv_field h hinv hgi x
  have hR := differentiable_riemField h.contDiff_chr
  have hRic : ∀ b d, Differentiable ℝ fun y => ricField Γ y b d := fun b d => by
    simp only [ricField]; fun_prop
  have hs := Metric.isSymm_of_mul_eq_one (h.symm x) (hinv x)
  -- the mixed Ricci field and its jet as contractions
  have hM : ricUpField gi Γ = fun y a c => ∑ b, ∑ d, gi y b d * riemField Γ y a b c d :=
    funext fun y => funext fun a => funext fun c => (contract_riemField h hinv y a c).symm
  have hdM : (fun f a c => partialDeriv f (fun y => ricUpField gi Γ y a c) x) =
      fun f a c => ∑ b, ∑ d, (partialDeriv f (fun y => gi y b d) x * riemField Γ x a b c d
        + gi x b d * partialDeriv f (fun y => riemField Γ y a b c d) x) := by
    funext f a c
    rw [hM]
    rw [partialDeriv_sum _ (fun b _ => by fun_prop)]
    refine sum_congr rfl fun b _ => ?_
    rw [partialDeriv_sum _ (fun d _ => by fun_prop)]
    exact sum_congr rfl fun d _ => partialDeriv_mul (by fun_prop) (by fun_prop) f
  have hdU : (fun f d c => partialDeriv f (fun y => ricUpField gi Γ y d c) x) =
      fun f d c => ∑ b, (partialDeriv f (fun y => gi y d b) x * ricField Γ x b c
        + gi x d b * partialDeriv f (fun y => ricField Γ y b c) x) := by
    funext f d c
    simp only [ricUpField]
    rw [partialDeriv_sum _ (fun b _ => by fun_prop)]
    exact sum_congr rfl fun b _ => partialDeriv_mul (by fun_prop) (by fun_prop) f
  -- (A) the divergence of `R^a_c` is the contraction of `∇_a R^a_bcd`
  have hA : divMixed Γ (ricUpField gi Γ) x c =
      ∑ b, ∑ d, gi x b d * ∑ a, covRiemField Γ x a a b c d := by
    have e1 : ∀ a, cov11 (Γ x) (ricUpField gi Γ x)
        (fun f a c => partialDeriv f (fun y => ricUpField gi Γ y a c) x) a a c =
        ∑ b, ∑ d, gi x b d * covRiemField Γ x a a b c d := by
      intro a
      rw [hdM, show ricUpField gi Γ x = fun a c => ∑ b, ∑ d, gi x b d * riemField Γ x a b c d
        from congrFun hM x]
      exact (sum_gi_cov13 hpar _ _ a a c).symm
    simp only [divMixed, e1, mul_sum]
    exact sum3_congr_perm permCyc' fun y => by simp only [permCyc', Equiv.coe_fn_mk]
  -- (C) `g^{bd} ∇_c R_bd = ∂_c R`
  have hC : ∑ b, ∑ d, gi x b d * covRicField Γ x c b d = partialDeriv c (scalField gi Γ) x := by
    unfold covRicField
    rw [sum_gi_cov02 hpar, show scalField gi Γ = fun y => ∑ b, ∑ d, gi y b d * ricField Γ y b d
      from rfl]
    rw [partialDeriv_sum _ (fun b _ => by fun_prop)]
    refine sum_congr rfl fun b _ => ?_
    rw [partialDeriv_sum _ (fun d _ => by fun_prop)]
    exact sum_congr rfl fun d _ =>
      (partialDeriv_mul (f := fun y => gi y b d) (g := fun y => ricField Γ y b d) (hgi b d x)
        (hRic b d x) c).symm
  -- (D) `g^{bd} ∇_d R_bc = ∇_d R^d_c`
  have hD : ∑ b, ∑ d, gi x b d * covRicField Γ x d b c = divMixed Γ (ricUpField gi Γ) x c := by
    rw [Finset.sum_comm]
    simp only [divMixed]
    refine sum_congr rfl fun d _ => ?_
    have := sum_gi_cov02_left hpar (ricField Γ x)
      (fun f b d => partialDeriv f (fun y => ricField Γ y b d) x) d d c
    simp only [covRicField]
    rw [hdU]
    refine Eq.trans ?_ this
    exact sum_congr rfl fun b _ => by rw [hs.apply b d]
  have hB : ∑ b, ∑ d, gi x b d * ∑ a, covRiemField Γ x a a b c d =
      ∑ b, ∑ d, gi x b d * covRicField Γ x c b d - ∑ b, ∑ d, gi x b d * covRicField Γ x d b c := by
    simp only [div_riemField h.contDiff_chr h.torsionFree, mul_sub, sum_sub_distrib]
  linarith [hA, hB, hC, hD]

omit [DecidableEq ι] in
theorem cov11_sub (Γ : ι → ι → ι → ℝ) (T₁ T₂ : ι → ι → ℝ) (dT₁ dT₂ : ι → ι → ι → ℝ) (f a c : ι) :
    cov11 Γ (fun a c => T₁ a c - T₂ a c) (fun f a c => dT₁ f a c - dT₂ f a c) f a c =
      cov11 Γ T₁ dT₁ f a c - cov11 Γ T₂ dT₂ f a c := by
  simp only [cov11, mul_sub, sum_sub_distrib]
  ring

theorem sum_cov11_delta (Γ : ι → ι → ι → ℝ) (S : ℝ) (dS : ι → ℝ) (c : ι) :
    ∑ a, cov11 Γ (fun a c => (if a = c then 1 else 0) * S / 2)
      (fun f a c => (if a = c then 1 else 0) * dS f / 2) a a c = dS c / 2 := by
  simp only [cov11, ite_mul, one_mul, zero_mul, ite_div, zero_div, mul_ite, mul_zero,
    sum_add_distrib, sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  ring

theorem divMixed_einsteinUp {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) {gi : (ι → ℝ) → Matrix ι ι ℝ} (hinv : ∀ y, gi y * g y = 1)
    (hgi : ∀ a b, Differentiable ℝ fun y => gi y a b) (x : ι → ℝ) (c : ι) :
    divMixed Γ (einsteinUpField gi Γ) x c = 0 := by
  have hR := differentiable_riemField h.contDiff_chr
  have hRic : ∀ b d, Differentiable ℝ fun y => ricField Γ y b d := fun b d => by
    simp only [ricField]; fun_prop
  have hU : ∀ a c, Differentiable ℝ fun y => ricUpField gi Γ y a c := fun a c => by
    simp only [ricUpField]; fun_prop
  have hSd : Differentiable ℝ (scalField gi Γ) := by
    unfold scalField; fun_prop
  have key := two_mul_divMixed_ricUp h hinv hgi x c
  have e : (fun f a c => partialDeriv f (fun y => einsteinUpField gi Γ y a c) x) =
      fun f a c => partialDeriv f (fun y => ricUpField gi Γ y a c) x
        - (if a = c then 1 else 0) * partialDeriv f (scalField gi Γ) x / 2 := by
    funext f a c
    simp only [einsteinUpField]
    rw [partialDeriv_sub (by fun_prop) (by fun_prop)]
    congr 1
    have : (fun y => (if a = c then (1 : ℝ) else 0) * scalField gi Γ y / 2) =
        fun y => ((if a = c then (1 : ℝ) else 0) / 2) • scalField gi Γ y := by
      funext y; rw [smul_eq_mul]; ring
    rw [this, partialDeriv_const_smul (hSd x), smul_eq_mul]
    ring
  unfold divMixed at key ⊢
  rw [e, show einsteinUpField gi Γ x = fun a c => ricUpField gi Γ x a c
    - (if a = c then 1 else 0) * scalField gi Γ x / 2 from rfl]
  simp only [cov11_sub, sum_sub_distrib, sum_cov11_delta]
  linarith

/-- The (lowered) Einstein tensor field `G_bc = R_bc - ½ R g_bc`. -/
def einsteinField (g gi : (ι → ℝ) → Matrix ι ι ℝ) (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) :
    Matrix ι ι ℝ := einstein (g x) (gi x) (Matrix.of (ricField Γ x))

theorem raise_einsteinField {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) {gi : (ι → ℝ) → Matrix ι ι ℝ} (hinv : ∀ y, gi y * g y = 1)
    (x : ι → ℝ) (d c : ι) :
    ∑ b, gi x d b * einsteinField g gi Γ x b c = einsteinUpField gi Γ x d c := by
  have hs := Metric.isSymm_of_mul_eq_one (h.symm x) (hinv x)
  have htr : (gi x * Matrix.of (ricField Γ x)).trace = scalField gi Γ x := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, scalField]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun b _ => sum_congr rfl fun d _ => by rw [hs.apply d b]
  have hδ : ∑ b, gi x d b * g x b c = if d = c then 1 else 0 := by
    have := congrFun (congrFun (hinv x) d) c
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  simp only [einsteinField, einstein, htr, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, mul_sub, sum_sub_distrib, einsteinUpField, ricUpField]
  congr 1
  rw [show ∑ b, gi x d b * (⅟2 * scalField gi Γ x * g x b c)
      = (⅟2 * scalField gi Γ x) * ∑ b, gi x d b * g x b c by
    rw [mul_sum]; exact sum_congr rfl fun b _ => by ring, hδ]
  split_ifs <;> simp [invOf_eq_inv]; ring

theorem div_einsteinField {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) {gi : (ι → ℝ) → Matrix ι ι ℝ} (hinv : ∀ y, gi y * g y = 1)
    (hgi : ∀ a b, Differentiable ℝ fun y => gi y a b) (x : ι → ℝ) (c : ι) :
    ∑ a, ∑ b, gi x a b * cov02 (Γ x) (einsteinField g gi Γ x)
      (fun f b c => partialDeriv f (fun y => einsteinField g gi Γ y b c) x) a b c = 0 := by
  have hpar := isParallelInv_field h hinv hgi x
  have hR := differentiable_riemField h.contDiff_chr
  have hg : ∀ a b, Differentiable ℝ fun y => g y a b := fun a b =>
    (h.contDiff_metric a b).differentiable (by norm_num)
  have hRic : ∀ b d, Differentiable ℝ fun y => ricField Γ y b d := fun b d => by
    simp only [ricField]; fun_prop
  have hG : ∀ b c, Differentiable ℝ fun y => einsteinField g gi Γ y b c := fun b c => by
    simp only [einsteinField, einstein, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    fun_prop
  have hUp : einsteinUpField gi Γ = fun y d c => ∑ b, gi y d b * einsteinField g gi Γ y b c :=
    funext fun y => funext fun d => funext fun c => (raise_einsteinField h hinv y d c).symm
  rw [← divMixed_einsteinUp h hinv hgi x c, hUp]
  unfold divMixed
  refine sum_congr rfl fun a _ => ?_
  refine (sum_gi_cov02_left hpar (einsteinField g gi Γ x) _ a a c).trans ?_
  congr 1
  funext f d c
  simp only
  rw [partialDeriv_sum _ (fun b _ => by fun_prop)]
  exact sum_congr rfl fun b _ => (partialDeriv_mul (f := fun y => gi y d b)
    (g := fun y => einsteinField g gi Γ y b c) (hgi d b x) (hG b c x) f).symm

/-- The Weyl tensor of an algebraic curvature tensor `Rm` in dimension `n = card ι`. -/
def weylTensor (g gi : Matrix ι ι ℝ) (Rm : ι → ι → ι → ι → ℝ) : ι → ι → ι → ι → ℝ :=
  fun a b c d =>
    Rm a b c d - (g a c * ricci gi Rm b d - g a d * ricci gi Rm b c - g b c * ricci gi Rm a d
      + g b d * ricci gi Rm a c) / ((Fintype.card ι : ℝ) - 2)
    + (∑ p, ∑ q, gi p q * ricci gi Rm p q) * (g a c * g b d - g a d * g b c)
      / (((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2))

omit [DecidableEq ι] in
theorem weylTensor_eq_self {g gi : Matrix ι ι ℝ} {Rm : ι → ι → ι → ι → ℝ}
    (h : ricci gi Rm = 0) : weylTensor g gi Rm = Rm := by
  funext a b c d
  simp [weylTensor, h]

theorem weylTensor_traceFree {g gi : Matrix ι ι ℝ} (hg : g.IsSymm) (hinv : gi * g = 1)
    {Rm : ι → ι → ι → ι → ℝ} (hI : Interchange Rm)
    (hn1 : (Fintype.card ι : ℝ) ≠ 1) (hn2 : (Fintype.card ι : ℝ) ≠ 2) (b d : ι) :
    ∑ a, ∑ c, gi a c * weylTensor g gi Rm a b c d = 0 := by
  have hs := Metric.isSymm_of_mul_eq_one hg hinv
  have hginv : g * gi = 1 := Metric.mul_eq_one_comm'.1 hinv
  set Ric := ricci gi Rm
  set S := ∑ p, ∑ q, gi p q * Ric p q
  have hRs : ∀ i j, Ric i j = Ric j i := fun i j => ((ricci_isSymm hs hI).apply j i)
  have hδ : ∀ c d, ∑ a, gi c a * g a d = if c = d then 1 else 0 := fun c d => by
    have := congrFun (congrFun hinv c) d
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hn : ∑ a, ∑ c, gi a c * g a c = (Fintype.card ι : ℝ) := Metric.trace_metric hg hinv
  have h1 : ∑ a, ∑ c, gi a c * Rm a b c d = Ric b d := by
    simp only [Ric, ricci, Matrix.of_apply]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun c _ => sum_congr rfl fun a _ => by rw [hs.apply a c]
  have h3 : ∑ a, ∑ c, gi a c * g a d * Ric b c = Ric b d := by
    rw [Finset.sum_comm]
    calc ∑ c, ∑ a, gi a c * g a d * Ric b c = ∑ c, (∑ a, gi c a * g a d) * Ric b c := by
          refine sum_congr rfl fun c _ => ?_
          rw [sum_mul]; exact sum_congr rfl fun a _ => by rw [hs.apply a c]
      _ = Ric b d := by simp [hδ]
  have h4 : ∑ a, (∑ c, gi a c * g b c) * Ric a d = Ric b d := by
    calc ∑ a, (∑ c, gi a c * g b c) * Ric a d = ∑ a, (∑ c, gi a c * g c b) * Ric a d := by
          refine sum_congr rfl fun a _ => ?_
          congr 1; exact sum_congr rfl fun c _ => by rw [hg.apply b c]
      _ = Ric b d := by simp [hδ]
  have h6 : ∑ x, ∑ y, gi x y * Ric x y = S := rfl
  have h5 : ∑ a, ∑ c, gi a c * g a d * g b c = g b d := by
    rw [Finset.sum_comm]
    calc ∑ c, ∑ a, gi a c * g a d * g b c = ∑ c, (∑ a, gi c a * g a d) * g b c := by
          refine sum_congr rfl fun c _ => ?_
          rw [sum_mul]; exact sum_congr rfl fun a _ => by rw [hs.apply a c]
      _ = g b d := by simp [hδ]
  have key : ∀ a c, gi a c * weylTensor g gi Rm a b c d = gi a c * Rm a b c d
      - (gi a c * g a c * Ric b d - gi a c * g a d * Ric b c - gi a c * g b c * Ric a d
        + g b d * (gi a c * Ric a c)) / ((Fintype.card ι : ℝ) - 2)
      + S * (gi a c * g a c * g b d - gi a c * g a d * g b c)
        / (((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2)) := by
    intro a c; simp only [weylTensor, Ric, S]; ring
  simp only [key, sum_add_distrib, sum_sub_distrib, ← sum_div, ← mul_sum, ← sum_mul, h1, h3,
    h4, h5, hn, h6]
  have hn1' : (Fintype.card ι : ℝ) - 1 ≠ 0 := sub_ne_zero.2 hn1
  have hn2' : (Fintype.card ι : ℝ) - 2 ≠ 0 := sub_ne_zero.2 hn2
  field_simp
  ring

theorem ricci_riemLowField {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    {gi : Matrix ι ι ℝ} {x : ι → ℝ} (hinv : gi * g x = 1) :
    ricci gi (riemLowField g Γ x) = Matrix.of (ricField Γ x) := by
  ext a b
  simp only [ricci, Matrix.of_apply, ricField]
  refine sum_congr rfl fun c _ => ?_
  rw [riemField_eq_raise (Γ := Γ) hinv c a c b]

/-- The Weyl tensor field `C_abcd` of a metric. -/
def weylField (g gi : (ι → ℝ) → Matrix ι ι ℝ) (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (x : ι → ℝ) :
    ι → ι → ι → ι → ℝ := weylTensor (g x) (gi x) (riemLowField g Γ x)

theorem div_weylField_vacuum {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) {gi : (ι → ℝ) → Matrix ι ι ℝ} (hinv : ∀ y, gi y * g y = 1)
    (hvac : ∀ y, ricField Γ y = 0) (x : ι → ℝ) (b c d : ι) :
    ∑ a, ∑ e, gi x a e * cov4 (Γ x) (weylField g gi Γ x)
      (fun f a b c d => partialDeriv f (fun y => weylField g gi Γ y a b c d) x) e a b c d = 0 := by
  have hW : weylField g gi Γ = riemLowField g Γ := funext fun y =>
    weylTensor_eq_self (by rw [ricci_riemLowField (hinv y), hvac y]; rfl)
  have hs := Metric.isSymm_of_mul_eq_one (h.symm x) (hinv x)
  have hginv : g x * gi x = 1 := Metric.mul_eq_one_comm'.1 (hinv x)
  rw [hW]
  change ∑ a, ∑ e, gi x a e * covRiemLowField g Γ x e a b c d = 0
  simp only [covRiemLowField_eq h, mul_sum]
  have hδ : ∀ e h', ∑ a, gi x a e * g x a h' = if e = h' then 1 else 0 := fun e h' => by
    have := congrFun (congrFun (hinv x) e) h'
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]; exact sum_congr rfl fun a _ => by rw [hs.apply a e]
  rw [← div_riemField_vacuum h.contDiff_chr h.torsionFree hvac x b c d]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← sum_mul, hδ, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-! ### Frame components of fields -/

/-- The partial-derivative jet of a `(0,4)` tensor field. -/
def pd4 (T : (ι → ℝ) → ι → ι → ι → ι → ℝ) (x : ι → ℝ) : ι → ι → ι → ι → ι → ℝ :=
  fun h a b c d => partialDeriv h (fun y => T y a b c d) x

/-- The partial-derivative jet of a frame field. -/
def pdFrame (e : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ) : ι → ι → ι → ℝ :=
  fun h a μ => partialDeriv h (fun y => e y a μ) x

omit [DecidableEq ι] in
theorem differentiable_slot1 {e : (ι → ℝ) → Matrix ι ι ℝ} {T : (ι → ℝ) → ι → ι → ι → ι → ℝ}
    (he : ∀ a μ, Differentiable ℝ fun y => e y a μ)
    (hT : ∀ a b c d, Differentiable ℝ fun y => T y a b c d) (a b c d : ι) :
    Differentiable ℝ fun y => slot1 (e y) (T y) a b c d := by
  simp only [slot1]; fun_prop

theorem pd4_slot1 {e : (ι → ℝ) → Matrix ι ι ℝ} {T : (ι → ℝ) → ι → ι → ι → ι → ℝ}
    (he : ∀ a μ, Differentiable ℝ fun y => e y a μ)
    (hT : ∀ a b c d, Differentiable ℝ fun y => T y a b c d) (x : ι → ℝ) :
    pd4 (fun y => slot1 (e y) (T y)) x = dslot1 (e x) (pdFrame e x) (T x) (pd4 T x) := by
  funext h μ b c d
  simp only [pd4, slot1, dslot1, pdFrame]
  rw [partialDeriv_sum _ (fun a _ => by fun_prop)]
  exact sum_congr rfl fun a _ => partialDeriv_mul (by fun_prop) (by fun_prop) h

omit [DecidableEq ι] in
theorem differentiable_slot2 {e : (ι → ℝ) → Matrix ι ι ℝ} {T : (ι → ℝ) → ι → ι → ι → ι → ℝ}
    (he : ∀ a μ, Differentiable ℝ fun y => e y a μ)
    (hT : ∀ a b c d, Differentiable ℝ fun y => T y a b c d) (a b c d : ι) :
    Differentiable ℝ fun y => slot2 (e y) (T y) a b c d := by
  simp only [slot2]; fun_prop

theorem pd4_slot2 {e : (ι → ℝ) → Matrix ι ι ℝ} {T : (ι → ℝ) → ι → ι → ι → ι → ℝ}
    (he : ∀ a μ, Differentiable ℝ fun y => e y a μ)
    (hT : ∀ a b c d, Differentiable ℝ fun y => T y a b c d) (x : ι → ℝ) :
    pd4 (fun y => slot2 (e y) (T y)) x = dslot2 (e x) (pdFrame e x) (T x) (pd4 T x) := by
  funext h a μ c d
  simp only [pd4, slot2, dslot2, pdFrame]
  rw [partialDeriv_sum _ (fun b _ => by fun_prop)]
  exact sum_congr rfl fun b _ => partialDeriv_mul (by fun_prop) (by fun_prop) h

omit [DecidableEq ι] in
theorem differentiable_slot3 {e : (ι → ℝ) → Matrix ι ι ℝ} {T : (ι → ℝ) → ι → ι → ι → ι → ℝ}
    (he : ∀ a μ, Differentiable ℝ fun y => e y a μ)
    (hT : ∀ a b c d, Differentiable ℝ fun y => T y a b c d) (a b c d : ι) :
    Differentiable ℝ fun y => slot3 (e y) (T y) a b c d := by
  simp only [slot3]; fun_prop

theorem pd4_slot3 {e : (ι → ℝ) → Matrix ι ι ℝ} {T : (ι → ℝ) → ι → ι → ι → ι → ℝ}
    (he : ∀ a μ, Differentiable ℝ fun y => e y a μ)
    (hT : ∀ a b c d, Differentiable ℝ fun y => T y a b c d) (x : ι → ℝ) :
    pd4 (fun y => slot3 (e y) (T y)) x = dslot3 (e x) (pdFrame e x) (T x) (pd4 T x) := by
  funext h a b μ d
  simp only [pd4, slot3, dslot3, pdFrame]
  rw [partialDeriv_sum _ (fun c _ => by fun_prop)]
  exact sum_congr rfl fun c _ => partialDeriv_mul (by fun_prop) (by fun_prop) h

omit [DecidableEq ι] in
theorem differentiable_slot4 {e : (ι → ℝ) → Matrix ι ι ℝ} {T : (ι → ℝ) → ι → ι → ι → ι → ℝ}
    (he : ∀ a μ, Differentiable ℝ fun y => e y a μ)
    (hT : ∀ a b c d, Differentiable ℝ fun y => T y a b c d) (a b c d : ι) :
    Differentiable ℝ fun y => slot4 (e y) (T y) a b c d := by
  simp only [slot4]; fun_prop

theorem pd4_slot4 {e : (ι → ℝ) → Matrix ι ι ℝ} {T : (ι → ℝ) → ι → ι → ι → ι → ℝ}
    (he : ∀ a μ, Differentiable ℝ fun y => e y a μ)
    (hT : ∀ a b c d, Differentiable ℝ fun y => T y a b c d) (x : ι → ℝ) :
    pd4 (fun y => slot4 (e y) (T y)) x = dslot4 (e x) (pdFrame e x) (T x) (pd4 T x) := by
  funext h a b c μ
  simp only [pd4, slot4, dslot4, pdFrame]
  rw [partialDeriv_sum _ (fun d _ => by fun_prop)]
  exact sum_congr rfl fun d _ => partialDeriv_mul (by fun_prop) (by fun_prop) h

/-- The mixed connection coefficients `Γ'^λ_{hμ} = θ^λ_b (∂_h e^b_μ + Γ^b_{hc} e^c_μ)`. -/
def mixedConnField (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (e θ : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ) :
    ι → ι → ι → ℝ := fun l h μ =>
  ∑ b, θ x l b * (partialDeriv h (fun y => e y b μ) x + ∑ c, Γ x b h c * e x c μ)

/-- The frame connection coefficients `γ^λ_{κν}` of a frame field: `∇_{e_κ} e_ν = γ^λ_{κν} e_λ`. -/
def frameConnField (Γ : (ι → ℝ) → ι → ι → ι → ℝ) (e θ : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ) :
    ι → ι → ι → ℝ := frameConn (e x) (mixedConnField Γ e θ x)

theorem isFrameConn_field (Γ : (ι → ℝ) → ι → ι → ι → ℝ) {e θ : (ι → ℝ) → Matrix ι ι ℝ}
    (hθ : ∀ y, e y * θ y = 1) (x : ι → ℝ) :
    IsFrameConn (Γ x) (e x) (pdFrame e x) (mixedConnField Γ e θ x) := by
  intro h a μ
  simp only [mixedConnField, pdFrame, sum_mul]
  rw [Finset.sum_comm]
  have hc : ∀ b, ∑ l, θ x l b * e x a l = (1 : Matrix ι ι ℝ) a b := fun b => by
    rw [← hθ x, Matrix.mul_apply]; exact sum_congr rfl fun l _ => by ring
  calc ∑ b, ∑ l, θ x l b * (partialDeriv h (fun y => e y b μ) x + ∑ c, Γ x b h c * e x c μ)
        * e x a l
      = ∑ b, (1 : Matrix ι ι ℝ) a b
          * (partialDeriv h (fun y => e y b μ) x + ∑ c, Γ x b h c * e x c μ) := by
        refine sum_congr rfl fun b _ => ?_
        rw [← hc b, sum_mul]
        exact sum_congr rfl fun l _ => by ring
    _ = _ := by simp [Matrix.one_apply]

/-- The frame components `c^λ_{κν} = θ^λ_a [e_κ, e_ν]^a` of the Lie bracket of frame vectors. -/
def frameBracket (e θ : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ) : ι → ι → ι → ℝ := fun l κ ν =>
  ∑ a, θ x l a * ∑ h, (e x h κ * partialDeriv h (fun y => e y a ν) x
    - e x h ν * partialDeriv h (fun y => e y a κ) x)

theorem frameConnField_sub_swap {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (hΓ : ∀ x a b c, Γ x a b c = Γ x a c b) (e θ : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ)
    (l κ ν : ι) :
    frameConnField Γ e θ x l κ ν - frameConnField Γ e θ x l ν κ = frameBracket e θ x l κ ν := by
  simp only [frameConnField, frameConn, mixedConnField, frameBracket]
  have hΓsum : ∑ h, e x h κ * ∑ b, θ x l b * ∑ c, Γ x b h c * e x c ν
      = ∑ h, e x h ν * ∑ b, θ x l b * ∑ c, Γ x b h c * e x c κ := by
    simp only [mul_sum]
    exact sum3_congr_perm perm13 fun y => by
      simp only [perm13, Equiv.coe_fn_mk]; rw [hΓ x y.2.1 y.1 y.2.2]; ring
  have hsplit : ∀ μ ν', ∑ h, e x h μ * ∑ b, θ x l b *
      (partialDeriv h (fun y => e y b ν') x + ∑ c, Γ x b h c * e x c ν')
      = ∑ b, θ x l b * ∑ h, e x h μ * partialDeriv h (fun y => e y b ν') x
        + ∑ h, e x h μ * ∑ b, θ x l b * ∑ c, Γ x b h c * e x c ν' := by
    intro μ ν'
    simp only [mul_add, sum_add_distrib, mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact sum_congr rfl fun b _ => sum_congr rfl fun h _ => by ring
  rw [hsplit, hsplit, hΓsum]
  simp only [mul_sub, sum_sub_distrib]
  ring

/-- The frame components `R_μνρσ` of the Riemann tensor field. -/
def frameRiemField (g : (ι → ℝ) → Matrix ι ι ℝ) (Γ : (ι → ℝ) → ι → ι → ι → ℝ)
    (e : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ) : ι → ι → ι → ι → ℝ :=
  frame4 (e x) (riemLowField g Γ x)

/-- The second Bianchi identity `∇_κ R_μνρσ + ∇_μ R_νκρσ + ∇_ν R_κμρσ = 0` for the frame
components of the Riemann tensor of a metric, in a differentiable frame. -/
theorem frameRiemField_cyclic {g : (ι → ℝ) → Matrix ι ι ℝ} {Γ : (ι → ℝ) → ι → ι → ι → ℝ}
    (h : IsLeviCivita g Γ) {e θ : (ι → ℝ) → Matrix ι ι ℝ}
    (he : ∀ a μ, Differentiable ℝ fun y => e y a μ) (hθ : ∀ y, e y * θ y = 1) (x : ι → ℝ)
    (κ μ ν ρ σ : ι) :
    cov4 (frameConnField Γ e θ x) (frameRiemField g Γ e x)
        (frameJet (e x) (pd4 (frameRiemField g Γ e) x)) κ μ ν ρ σ
      + cov4 (frameConnField Γ e θ x) (frameRiemField g Γ e x)
        (frameJet (e x) (pd4 (frameRiemField g Γ e) x)) μ ν κ ρ σ
      + cov4 (frameConnField Γ e θ x) (frameRiemField g Γ e x)
        (frameJet (e x) (pd4 (frameRiemField g Γ e) x)) ν κ μ ρ σ = 0 := by
  have hg : ∀ a b, Differentiable ℝ fun y => g y a b := fun a b =>
    (h.contDiff_metric a b).differentiable (by norm_num)
  have hR := differentiable_riemField h.contDiff_chr
  have hR4 : ∀ a b c d, Differentiable ℝ fun y => riemLowField g Γ y a b c d := fun a b c d => by
    simp only [riemLowField, lower]; fun_prop
  have h4 := differentiable_slot4 he hR4
  have h3 := differentiable_slot3 he h4
  have h2 := differentiable_slot2 he h3
  have hd : pd4 (frameRiemField g Γ e) x =
      dframe4 (e x) (pdFrame e x) (riemLowField g Γ x) (pd4 (riemLowField g Γ) x) := by
    rw [show frameRiemField g Γ e = fun y => slot1 (e y)
      (slot2 (e y) (slot3 (e y) (slot4 (e y) (riemLowField g Γ y)))) from rfl,
      pd4_slot1 he h2, pd4_slot2 he h3, pd4_slot3 he h4, pd4_slot4 he hR4]
    rfl
  rw [hd]
  exact frame_cyclic (isFrameConn_field Γ hθ x) _ _
    (fun h' a b c d => covRiemLowField_cyclic_first h x h' a b c d) κ μ ν ρ σ

/-! ### The Christoffel symbols of a metric -/

theorem contDiff_det {n : ℕ∞} {M : (ι → ℝ) → Matrix ι ι ℝ}
    (hM : ∀ a b, ContDiff ℝ n fun y => M y a b) : ContDiff ℝ n fun y => (M y).det := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)

theorem contDiff_inv_apply {n : ℕ∞} {M : (ι → ℝ) → Matrix ι ι ℝ}
    (hM : ∀ a b, ContDiff ℝ n fun y => M y a b) (hdet : ∀ y, (M y).det ≠ 0) (a b : ι) :
    ContDiff ℝ n fun y => (M y)⁻¹ a b := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    Matrix.adjugate_apply]
  refine ((contDiff_det hM).inv hdet).mul (contDiff_det fun i j => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs <;> first | exact contDiff_const | exact hM i j

/-- The Christoffel symbols `Γ^a_bc = ½ g^{ad} (∂_b g_dc + ∂_c g_db - ∂_d g_bc)` of a metric. -/
def christoffel (g : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ) : ι → ι → ι → ℝ := fun a b c =>
  (1 / 2) * ∑ d, (g x)⁻¹ a d * (partialDeriv b (fun y => g y d c) x
    + partialDeriv c (fun y => g y d b) x - partialDeriv d (fun y => g y b c) x)

/-- The Christoffel symbols of a symmetric nondegenerate `C³` metric field, of any signature, are
`C²`, torsion-free and metric compatible. -/
theorem isLeviCivita_christoffel {g : (ι → ℝ) → Matrix ι ι ℝ} (hs : ∀ x, (g x).IsSymm)
    (hC : ∀ a b, ContDiff ℝ 3 fun y => g y a b) (hdet : ∀ x, (g x).det ≠ 0) :
    IsLeviCivita g (christoffel g) := by
  have hsym : ∀ y a b, g y a b = g y b a := fun y a b => (hs y).apply b a
  have hpd : ∀ k a b x, partialDeriv k (fun y => g y a b) x = partialDeriv k (fun y => g y b a) x :=
    fun k a b x => by congr 1; funext y; exact hsym y a b
  refine ⟨hs, fun a b => (hC a b).of_le (by norm_num), fun a b c => ?_, fun x a b c => ?_,
    fun x e a b => ?_⟩
  · have hi : ∀ a d, ContDiff ℝ 2 fun y => (g y)⁻¹ a d := fun a d =>
      (contDiff_inv_apply hC hdet a d).of_le (by norm_num)
    have hp : ∀ k a b, ContDiff ℝ 2 fun y => partialDeriv k (fun z => g z a b) y :=
      fun k a b => (hC a b).partialDeriv (m := 2) (by norm_num) k
    simp only [christoffel]
    exact contDiff_const.mul (ContDiff.sum fun d _ => (hi a d).mul
      (((hp b d c).add (hp c d b)).sub (hp d b c)))
  · simp only [christoffel]
    congr 1
    refine sum_congr rfl fun d _ => ?_
    rw [hpd d b c x]; ring
  · have hginv : g x * (g x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdet x))
    have hδ : ∀ b d, ∑ r, g x r b * (g x)⁻¹ r d = if b = d then 1 else 0 := fun b d => by
      have := congrFun (congrFun hginv b) d
      simp only [Matrix.mul_apply, Matrix.one_apply] at this
      rw [← this]; exact sum_congr rfl fun r _ => by rw [hsym x r b]
    have key : ∀ b (X : ι → ℝ), ∑ r, g x r b * ((1 / 2) * ∑ d, (g x)⁻¹ r d * X d) =
        (1 / 2) * X b := fun b X => by
      calc ∑ r, g x r b * ((1 / 2) * ∑ d, (g x)⁻¹ r d * X d)
          = (1 / 2) * ∑ d, (∑ r, g x r b * (g x)⁻¹ r d) * X d := by
            simp only [mul_sum, sum_mul]
            rw [Finset.sum_comm]
            exact sum_congr rfl fun d _ => sum_congr rfl fun r _ => by ring
        _ = (1 / 2) * X b := by simp [hδ]
    simp only [christoffel, sum_add_distrib]
    rw [key b, show ∑ r, g x a r * ((1 / 2) * ∑ d, (g x)⁻¹ r d *
        (partialDeriv e (fun y => g y d b) x + partialDeriv b (fun y => g y d e) x
          - partialDeriv d (fun y => g y e b) x)) = ∑ r, g x r a * ((1 / 2) * ∑ d, (g x)⁻¹ r d *
        (partialDeriv e (fun y => g y d b) x + partialDeriv b (fun y => g y d e) x
          - partialDeriv d (fun y => g y e b) x)) from
      sum_congr rfl fun r _ => by rw [hsym x a r], key a]
    rw [hpd e b a x, hpd a b e x, hpd b e a x, hpd a e b x]
    ring

section Metric

variable {g : (ι → ℝ) → Matrix ι ι ℝ} (hs : ∀ x, (g x).IsSymm)
  (hC : ∀ a b, ContDiff ℝ 3 fun y => g y a b) (hdet : ∀ x, (g x).det ≠ 0)
include hs hC hdet

/-- The second Bianchi identity `∇_[e R_cd]ab = 0` for the Levi-Civita connection of a symmetric
nondegenerate `C³` metric on `ℝ^ι`, of any signature. [QuennevilleBelair2015], (2.4) -/
theorem bianchi2_metric (x : ι → ℝ) (f a b c d : ι) :
    covRiemLowField g (christoffel g) x f a b c d + covRiemLowField g (christoffel g) x c a b d f
      + covRiemLowField g (christoffel g) x d a b f c = 0 :=
  covRiemLowField_cyclic (isLeviCivita_christoffel hs hC hdet) x f a b c d

/-- The twice-contracted Bianchi identity `∇^a G_ac = 0` for a symmetric nondegenerate `C³`
metric. [QuennevilleBelair2015], §2.3 -/
theorem div_einstein_metric (x : ι → ℝ) (c : ι) :
    ∑ a, ∑ b, (g x)⁻¹ a b * cov02 (christoffel g x) (einsteinField g (fun y => (g y)⁻¹)
      (christoffel g) x) (fun f b c => partialDeriv f (fun y => einsteinField g
        (fun y => (g y)⁻¹) (christoffel g) y b c) x) a b c = 0 :=
  div_einsteinField (isLeviCivita_christoffel hs hC hdet)
    (fun y => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hdet y)))
    (fun a b => (contDiff_inv_apply hC hdet a b).differentiable (by norm_num)) x c

/-- In vacuum (`R_ab = 0`) the Weyl tensor of a symmetric nondegenerate `C³` metric is
divergence-free: `∇^a C_abcd = 0`. -/
theorem div_weyl_metric_vacuum (hvac : ∀ y, ricField (christoffel g) y = 0) (x : ι → ℝ)
    (b c d : ι) :
    ∑ a, ∑ e, (g x)⁻¹ a e * cov4 (christoffel g x) (weylField g (fun y => (g y)⁻¹)
      (christoffel g) x) (fun f a b c d => partialDeriv f (fun y => weylField g
        (fun y => (g y)⁻¹) (christoffel g) y a b c d) x) e a b c d = 0 :=
  div_weylField_vacuum (isLeviCivita_christoffel hs hC hdet)
    (fun y => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hdet y))) hvac x b c d

end Metric

end Field

end Feec.CurvatureTensor
