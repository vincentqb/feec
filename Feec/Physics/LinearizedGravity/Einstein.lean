module

public import Feec.Algebra.Metric
public import Feec.Geometry.AlgebraicCurvature

/-!
# The linearized Einstein operator on jets, for any constant metric in any dimension

Linearized gravity about a constant (flat) metric `g` with inverse `gi` on an index type `ι`
(any dimension `n = card ι`, any signature), over a commutative ring with `2` invertible. The
linearized Einstein tensor `H` (thesis Thm 2.3) is a linear constant-coefficient second-order
operator, so it is a linear function of the 2-jet `D i j a b = ∂_i ∂_j h_ab`. All identities
below are exact identities on jets; only the trace-reversal involution needs `n = 4`.

Indices are lowered; `∂^c = gi^{cc'} ∂_{c'}`, `□ = gi^{ij} ∂_i ∂_j`, `h̄ = h - ½ (tr h) g`.

The thesis' Ch. 2 background (tensors, metric, covariant derivative, curvature, Einstein's
equations) follows [Wald1984] and also refers to [Alcubierre2008], [Carroll2004] and
[Stewart1991], among others. Here only its flat, linearized part is formalized: `H` is defined
directly as an operator on jets about a constant metric, and the one-parameter family
`g(ε) = η + εh + O(ε²)` of exact solutions behind it is not formalized.

## Main definitions

* `IsSymJet2 D` (Schwarz and `h` symmetric), `IsSymJet3ξ`, `IsSymJet3`.
* `boxJ`, `ddivJ` (`∂^c ∂^e h_ec`), `divJ` (`∂_i ∂^a h̄_ab`), `barJ` (jet of `h̄`).
* `Hjet g gi D`: Thm 2.3, first form; `HbarJet`: second form; `Rjet D`: the linearized Riemann
  tensor (2.6); `RicJ`, `scalJ`.
* Symbols: `symbolJet k h = k ⊗ k ⊗ h`, `Hsym`, `divSym`.

## Main results

* **Thm 2.3**: `Hjet_eq_bar` (both forms agree), `Hjet_eq_div` (the operator form
  `H = E(div h̄) - ½ □h̄ - ½ g div div h̄`), `Hjet_eq_einstein` (`H = Ric - ½ g R` for the
  linearized Riemann tensor (2.6), an algebraic curvature tensor: `Rjet_pairSkew`,
  `Rjet_bianchi1`).
* **Gauge invariance** `Hjet_gauge` (`H(2∂_(a ξ_b)) = 0`) and the **linearized Bianchi
  identity** `Hjet_bianchi` (`∂^b H_bd = 0`).
* **Prop 2.4(b), corrected**: `Hjet_lorentz` (`H = -½ □h̄` in Lorentz gauge), `Hjet_lorentz_eq_iff`.
* Symbol level: `Hsym_eq`, `Hsym_gauge`, `Hsym_div`, `Hsym_lorentz`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §2.7 ((2.5), Thm 2.3, (2.6)–(2.11)), §2.8 (Prop 2.4)
* [R. M. Wald, *General Relativity*][Wald1984], §4.4; pp. 75, 183, 441
* [M. Alcubierre, *Introduction to 3+1 Numerical Relativity*][Alcubierre2008], p. 39
* [S. M. Carroll, *Spacetime and Geometry: An Introduction to General Relativity*][Carroll2004],
  p. 277
* [J. Stewart, *Advanced General Relativity*][Stewart1991], p. 24

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Finset Matrix

@[expose] public noncomputable section

namespace Feec.LinearizedGravity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-! ### Jets -/

variable (ι R) in
/-- A 2-jet `D i j = ∂_i ∂_j h` of a symmetric 2-tensor field. -/
abbrev Jet2 := ι → ι → Matrix ι ι R

variable (ι R) in
/-- A 3-jet `Y m i j = ∂_m ∂_i ∂_j h`. -/
abbrev Jet3 := ι → Jet2 ι R

/-- Symmetry of the 2-jet of a `C²` symmetric 2-tensor field. -/
structure IsSymJet2 (D : Jet2 ι R) : Prop where
  deriv_symm : ∀ i j a b, D i j a b = D j i a b
  tensor_symm : ∀ i j a b, D i j a b = D i j b a

/-- Symmetry of the 3-jet `X i j c b = ∂_i ∂_j ∂_c ξ_b` of a `C³` covector field. -/
structure IsSymJet3ξ (X : ι → ι → ι → ι → R) : Prop where
  symm₁ : ∀ i j c b, X i j c b = X j i c b
  symm₂ : ∀ i j c b, X i j c b = X i c j b

/-- Symmetry of the 3-jet `Y m i j a b = ∂_m ∂_i ∂_j h_ab` of a `C³` symmetric field. -/
structure IsSymJet3 (Y : Jet3 ι R) : Prop where
  symm₁ : ∀ m i j a b, Y m i j a b = Y i m j a b
  symm₂ : ∀ m i j a b, Y m i j a b = Y m j i a b
  tensor_symm : ∀ m i j a b, Y m i j a b = Y m i j b a

variable (g gi : Matrix ι ι R)

/-- `□h_ab = gi^{ij} ∂_i ∂_j h_ab` on jets. -/
def boxJ (D : Jet2 ι R) (a b : ι) : R := ∑ i, ∑ j, gi i j * D i j a b

/-- The double divergence `∂^c ∂^e h_ec` on jets. -/
def ddivJ (D : Jet2 ι R) : R := ∑ c, ∑ c', ∑ e, ∑ e', gi c c' * gi e e' * D c' e' e c

/-- `∂^c ∂_b h_dc + ∂^c ∂_d h_bc`. -/
def mixJ (D : Jet2 ι R) (b d : ι) : R := ∑ c, ∑ c', gi c c' * (D c' b d c + D c' d b c)

/-- The trace of a jet `tr (∂_i ∂_j h) = ∂_i ∂_j tr h`. -/
def trJ (D : Jet2 ι R) (i j : ι) : R := Metric.trace gi (D i j)

/-- **Thm 2.3**, first form: `H_bd = ∂^c ∂_(b h_d)c - ½ (□h_bd + ∂_d ∂_b h)
- ½ g_bd (∂^c ∂^e h_ec - □h)`. [QuennevilleBelair2015], Thm 2.3; the linearization about a flat
metric follows [Wald1984], pp. 75, 183, 441, [Carroll2004], p. 277 and [Stewart1991], p. 24. -/
def Hjet (D : Jet2 ι R) (b d : ι) : R :=
  ⅟2 * mixJ gi D b d - ⅟2 * (boxJ gi D b d + trJ gi D d b) -
    ⅟2 * g b d * (ddivJ gi D - ∑ i, ∑ j, gi i j * trJ gi D i j)

/-- The 2-jet of the trace reversal `h̄`. -/
def barJ (D : Jet2 ι R) : Jet2 ι R := fun i j => Metric.trRev g gi (D i j)

/-- **Thm 2.3**, second form: `H_bd = ∂^a ∂_(b h̄_d)a - ½ (□h̄_bd + g_bd ∂^a ∂^e h̄_ea)`, as a
function of the 2-jet `E` of `h̄`. [QuennevilleBelair2015], Thm 2.3 -/
def HbarJet (E : Jet2 ι R) (b d : ι) : R :=
  ⅟2 * mixJ gi E b d - ⅟2 * (boxJ gi E b d + g b d * ddivJ gi E)

/-- `∂_i (∂^a h̄_ab)`: first derivatives of the divergence. -/
def divJ (E : Jet2 ι R) (i b : ι) : R := ∑ a, ∑ a', gi a a' * E i a' a b

/-- Lorentz gauge at the jet level: `∂_i (∂^a h̄_ab) = 0`. [QuennevilleBelair2015], Prop 2.4 -/
def LorentzJet (D : Jet2 ι R) : Prop := ∀ i b, divJ gi (barJ g gi D) i b = 0

/-! ### Contractions -/

variable {g gi}

omit [Invertible (2 : R)] in
theorem sum_g_mul_gi (hinv : gi * g = 1) (c d : ι) :
    ∑ a, g c a * gi a d = if c = d then 1 else 0 := by
  have h : g * gi = 1 := mul_eq_one_comm.1 hinv
  have := congrFun (congrFun h c) d
  simpa [mul_apply, one_apply] using this

omit [Invertible (2 : R)] in
/-- The basic contraction `gi^{aa'} g_da F_a' = F_d`. -/
theorem contract (hinv : gi * g = 1) (F : ι → R) (d : ι) :
    ∑ a, ∑ a', gi a a' * (F a' * g d a) = F d := by
  rw [Finset.sum_comm]
  have : ∀ a', ∑ a, gi a a' * (F a' * g d a) = F a' * (if d = a' then 1 else 0) := by
    intro a'
    rw [← sum_g_mul_gi hinv d a', mul_sum]
    exact sum_congr rfl fun a _ => by ring
  simp [this]

omit [Invertible (2 : R)] in
/-- The trace of the metric jet direction: `gi^{ab} g_ab = n`. -/
theorem trace_metric' (hg : g.IsSymm) (hinv : gi * g = 1) :
    Metric.trace gi g = Fintype.card ι := Metric.trace_metric hg hinv

/-! ### Thm 2.3 -/

omit [DecidableEq ι] in
theorem barJ_apply (D : Jet2 ι R) (i j a b : ι) :
    barJ g gi D i j a b = D i j a b - ⅟2 * trJ gi D i j * g a b := by
  simp [barJ, Metric.trRev_apply, trJ]

omit [DecidableEq ι] in
/-- The jet of `h̄` is again symmetric. -/
theorem IsSymJet2.barJ (hg : g.IsSymm) {D : Jet2 ι R} (hD : IsSymJet2 D) :
    IsSymJet2 (barJ g gi D) where
  deriv_symm i j a b := by
    simp only [barJ_apply, trJ, Metric.trace, hD.deriv_symm i j]
  tensor_symm i j a b := by
    rw [barJ_apply, barJ_apply, hD.tensor_symm i j a b, hg.apply a b]

omit [DecidableEq ι] [Invertible (2 : R)] in
theorem trJ_symm {D : Jet2 ι R} (hD : IsSymJet2 D) (i j : ι) : trJ gi D i j = trJ gi D j i := by
  simp only [trJ, Metric.trace, hD.deriv_symm i j]

/-- `mixJ` of the jet of `h̄`. -/
theorem mixJ_barJ (hinv : gi * g = 1) {D : Jet2 ι R} (hD : IsSymJet2 D) (b d : ι) :
    mixJ gi (barJ g gi D) b d = mixJ gi D b d - 2 * ⅟2 * trJ gi D b d := by
  have e : ∀ c c', gi c c' * (barJ g gi D c' b d c + barJ g gi D c' d b c) =
      gi c c' * (D c' b d c + D c' d b c) - ⅟2 * (gi c c' * (trJ gi D c' b * g d c)) -
        ⅟2 * (gi c c' * (trJ gi D c' d * g b c)) := fun c c' => by
    rw [barJ_apply, barJ_apply]; ring
  simp only [mixJ, e, sum_sub_distrib, ← mul_sum]
  rw [contract hinv, contract hinv, trJ_symm hD d b]
  ring

omit [DecidableEq ι] in
/-- `boxJ` of the jet of `h̄`. -/
theorem boxJ_barJ (D : Jet2 ι R) (b d : ι) :
    boxJ gi (barJ g gi D) b d =
      boxJ gi D b d - ⅟2 * (∑ i, ∑ j, gi i j * trJ gi D i j) * g b d := by
  have e : ∀ i j, gi i j * barJ g gi D i j b d =
      gi i j * D i j b d - (⅟2 * g b d) * (gi i j * trJ gi D i j) := fun i j => by
    rw [barJ_apply]; ring
  simp only [boxJ, e, sum_sub_distrib, ← mul_sum]
  ring

/-- `ddivJ` of the jet of `h̄`. -/
theorem ddivJ_barJ (hg : g.IsSymm) (hinv : gi * g = 1) {D : Jet2 ι R} (hD : IsSymJet2 D) :
    ddivJ gi (barJ g gi D) = ddivJ gi D - ⅟2 * ∑ i, ∑ j, gi i j * trJ gi D i j := by
  have e : ∀ c c' e e', gi c c' * gi e e' * barJ g gi D c' e' e c =
      gi c c' * gi e e' * D c' e' e c - ⅟2 * (gi c c' * (gi e e' * (trJ gi D c' e' * g c e))) :=
    fun c c' e e' => by rw [barJ_apply, hg.apply c e]; ring
  simp only [ddivJ, e, sum_sub_distrib, ← mul_sum]
  simp only [contract hinv]
  congr 2
  exact sum_congr rfl fun c _ => sum_congr rfl fun c' _ => by rw [trJ_symm hD c' c]

/-- **Thm 2.3** (equivalence of the two forms), for any constant metric in any dimension:
for the 2-jet of a symmetric `C²` field, `H` written in `h` equals `H` written in `h̄`.
(The thesis uses `n = 4`; the identity holds in every dimension.) [QuennevilleBelair2015], Thm 2.3,
whose proof follows [Alcubierre2008], p. 39. -/
theorem Hjet_eq_bar (hg : g.IsSymm) (hinv : gi * g = 1) {D : Jet2 ι R} (hD : IsSymJet2 D)
    (b d : ι) : Hjet g gi D b d = HbarJet g gi (barJ g gi D) b d := by
  have h2 : (⅟2 : R) * 2 = 1 := invOf_mul_self 2
  rw [HbarJet, mixJ_barJ hinv hD, boxJ_barJ, ddivJ_barJ hg hinv hD, Hjet, trJ_symm hD d b]
  linear_combination (⅟2 * trJ gi D b d - ⅟2 * g b d * ∑ i, ∑ j, gi i j * trJ gi D i j) * h2

/-- **Thm 2.3**, operator form: `H_bd = ½ (∂_b L_d + ∂_d L_b) - ½ □h̄_bd - ½ g_bd ∂^a L_a`
with `L_b = ∂^a h̄_ab`. [QuennevilleBelair2015], Thm 2.3 -/
theorem Hjet_eq_div (hg : g.IsSymm) (hinv : gi * g = 1) {D : Jet2 ι R}
    (hD : IsSymJet2 D) (b d : ι) :
    Hjet g gi D b d = ⅟2 * (divJ gi (barJ g gi D) b d + divJ gi (barJ g gi D) d b)
      - ⅟2 * boxJ gi (barJ g gi D) b d -
        ⅟2 * g b d * ∑ a, ∑ a', gi a a' * divJ gi (barJ g gi D) a' a := by
  rw [Hjet_eq_bar hg hinv hD]
  have hE := hD.barJ (gi := gi) hg
  have e1 : mixJ gi (barJ g gi D) b d =
      divJ gi (barJ g gi D) b d + divJ gi (barJ g gi D) d b := by
    simp only [mixJ, divJ, mul_add, sum_add_distrib]
    congr 1
    · refine sum_congr rfl fun a _ => sum_congr rfl fun a' _ => ?_
      rw [hE.deriv_symm a' b, hE.tensor_symm b a' d a]
    · refine sum_congr rfl fun a _ => sum_congr rfl fun a' _ => ?_
      rw [hE.deriv_symm a' d, hE.tensor_symm d a' b a]
  have e2 : ddivJ gi (barJ g gi D) = ∑ a, ∑ a', gi a a' * divJ gi (barJ g gi D) a' a := by
    simp only [ddivJ, divJ, mul_sum]
    refine sum_congr rfl fun c _ => sum_congr rfl fun c' _ => sum_congr rfl fun e _ =>
      sum_congr rfl fun e' _ => ?_
    ring
  rw [HbarJet, e1, e2]
  ring

/-! ### Reindexing finite sums -/

section Reindex

variable {α : Type*} [Fintype α] {M : Type*} [AddCommMonoid M]

theorem sum4_swap12 (f : α → α → α → α → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ a, ∑ c, ∑ d, f a b c d := Finset.sum_comm

theorem sum4_swap23 (f : α → α → α → α → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
  sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum4_swap34 (f : α → α → α → α → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d :=
  sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => Finset.sum_comm

/-- Reverse the order of four nested sums. -/
theorem sum4_reverse (f : α → α → α → α → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f d c b a = ∑ a, ∑ b, ∑ c, ∑ d, f a b c d := by
  rw [sum4_swap34, sum4_swap23, sum4_swap12, sum4_swap34, sum4_swap23, sum4_swap34]

end Reindex

omit [DecidableEq ι] [Invertible (2 : R)] in
theorem sum_sum_symm (hgi : gi.IsSymm) (F : ι → ι → R) :
    ∑ i, ∑ j, gi i j * F j i = ∑ i, ∑ j, gi i j * F i j := by
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hgi.apply i j]

/-! ### Gauge invariance -/

/-- 2-jet of the pure-gauge field `h_ab = ∂_a ξ_b + ∂_b ξ_a`, from the 3-jet
`X i j c b = ∂_i ∂_j ∂_c ξ_b`. -/
def gaugeJet (X : ι → ι → ι → ι → R) : Jet2 ι R := fun i j => Matrix.of fun a b =>
  X i j a b + X i j b a

omit [Fintype ι] [DecidableEq ι] [Invertible (2 : R)] in
@[simp] theorem gaugeJet_apply (X : ι → ι → ι → ι → R) (i j a b : ι) :
    gaugeJet X i j a b = X i j a b + X i j b a := rfl

omit [Fintype ι] [DecidableEq ι] [CommRing R] [Invertible (2 : R)] in
theorem IsSymJet3ξ.perm3 {X : ι → ι → ι → ι → R} (hX : IsSymJet3ξ X) (x y z w : ι) :
    X x y z w = X y z x w := by
  rw [hX.symm₁, hX.symm₂]

omit [DecidableEq ι] in
/-- **Gauge invariance** (end of §2.7), any constant metric, any dimension:
`H(2∂_(a ξ_b)) = 0` for every `C³` covector field `ξ` (at the level of its 3-jet); by linearity
`H(h + 2∂_(a ξ_b)) = H(h)`. [QuennevilleBelair2015], §2.7; see [Wald1984], pp. 75, 183, 441, [Carroll2004], p. 277 and [Stewart1991], p. 24.
-/
theorem Hjet_gauge (hgi : gi.IsSymm) {X : ι → ι → ι → ι → R} (hX : IsSymJet3ξ X) (b d : ι) :
    Hjet g gi (gaugeJet X) b d = 0 := by
  have hbox : boxJ gi (gaugeJet X) b d =
      ∑ i, ∑ j, gi i j * X i j b d + ∑ i, ∑ j, gi i j * X i j d b := by
    simp [boxJ, mul_add, sum_add_distrib]
  have hQsymm : ∑ p, ∑ q, gi p q * X d b p q = ∑ p, ∑ q, gi p q * X b d p q :=
    sum_congr rfl fun p _ => sum_congr rfl fun q _ => by rw [hX.symm₁]
  have hmix : mixJ gi (gaugeJet X) b d = 2 * ∑ p, ∑ q, gi p q * X b d p q +
      ∑ i, ∑ j, gi i j * X i j b d + ∑ i, ∑ j, gi i j * X i j d b := by
    have e : ∀ c c', gi c c' * (gaugeJet X c' b d c + gaugeJet X c' d b c) =
        gi c c' * X b d c' c + gi c c' * X c' c b d + gi c c' * X d b c' c +
          gi c c' * X c' c d b := fun c c' => by
      simp only [gaugeJet_apply]
      rw [hX.perm3 c' b d, hX.symm₂ c' b c d, hX.perm3 c' d b, hX.symm₂ c' d c b]
      ring
    simp only [mixJ, e, sum_add_distrib]
    rw [sum_sum_symm hgi (fun c' c => X b d c' c), sum_sum_symm hgi (fun c' c => X c' c b d),
      sum_sum_symm hgi (fun c' c => X d b c' c), sum_sum_symm hgi (fun c' c => X c' c d b),
      hQsymm]
    ring
  have htr : ∀ x y, trJ gi (gaugeJet X) x y = 2 * ∑ p, ∑ q, gi p q * X x y p q := fun x y => by
    simp only [trJ, Metric.trace, gaugeJet_apply, mul_add, sum_add_distrib]
    rw [sum_sum_symm hgi (fun q p => X x y q p)]
    ring
  have hddiv : ddivJ gi (gaugeJet X) =
      2 * ∑ i, ∑ j, ∑ p, ∑ q, gi i j * gi p q * X i j p q := by
    have e : ∀ c c' e e', gi c c' * gi e e' * gaugeJet X c' e' e c =
        gi e' e * gi c' c * X e' e c' c + gi c' c * gi e' e * X c' c e' e := fun c c' e e' => by
      simp only [gaugeJet_apply]
      rw [hX.perm3 c' e' e, hX.symm₂ c' e' c e, hgi.apply e' e, hgi.apply c' c]
      ring
    simp only [ddivJ, e, sum_add_distrib]
    rw [sum4_reverse (fun i j p q => gi i j * gi p q * X i j p q)]
    rw [sum4_swap12 (fun c c' e e' => gi c' c * gi e' e * X c' c e' e),
      sum4_swap34 (fun c' c e e' => gi c' c * gi e' e * X c' c e' e)]
    ring
  have htrbox : ∑ i, ∑ j, gi i j * trJ gi (gaugeJet X) i j =
      2 * ∑ i, ∑ j, ∑ p, ∑ q, gi i j * gi p q * X i j p q := by
    simp only [htr, mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun p _ =>
      sum_congr rfl fun q _ => by ring
  rw [Hjet, hmix, hbox, htr, hddiv, htrbox, hQsymm]
  ring

/-! ### The linearized Bianchi identity -/

/-- **Linearized Bianchi identity** `∂^b H_bd = 0` for every `C³` symmetric `h`, any constant
metric, any dimension (`∂_m H_bd = Hjet (Y m) b d` by linearity). Not stated in the thesis.
[QuennevilleBelair2015], §2.7; for the linearization see [Wald1984], pp. 75, 183, 441, [Carroll2004], p. 277 and [Stewart1991], p. 24. -/
theorem Hjet_bianchi (hg : g.IsSymm) (hgi : gi.IsSymm) (hinv : gi * g = 1) {Y : Jet3 ι R}
    (hY : IsSymJet3 Y) (d : ι) : ∑ b, ∑ b', gi b b' * Hjet g gi (Y b') b d = 0 := by
  set K : ι → R := fun m => ddivJ gi (Y m) - ∑ i, ∑ j, gi i j * trJ gi (Y m) i j with hK
  have e : ∀ b b', gi b b' * Hjet g gi (Y b') b d =
      ⅟2 * (gi b b' * mixJ gi (Y b') b d) - ⅟2 * (gi b b' * boxJ gi (Y b') b d) -
        ⅟2 * (gi b b' * trJ gi (Y b') d b) - ⅟2 * (gi b b' * (K b' * g d b)) := fun b b' => by
    rw [Hjet, hg.apply d b]; ring
  simp only [e, sum_sub_distrib, ← mul_sum]
  rw [contract hinv K d]
  -- the three building blocks
  have hT1 : ∑ b, ∑ b', gi b b' * mixJ gi (Y b') b d =
      ∑ i, ∑ j, ∑ c, ∑ c', gi i j * gi c c' * Y i j c' d c +
        ∑ b, ∑ b', ∑ c, ∑ c', gi b b' * gi c c' * Y d b' c' b c := by
    have e1 : ∀ b b' c c', gi b b' * (gi c c' * (Y b' c' b d c + Y b' c' d b c)) =
        gi b' b * gi c c' * Y b' b c' d c + gi b b' * gi c c' * Y d b' c' b c :=
      fun b b' c c' => by
        rw [hY.symm₂ b' c' b, hY.symm₂ b' c' d, hY.symm₁ b' d c', hgi.apply b' b]; ring
    simp only [mixJ, mul_sum, e1, sum_add_distrib]
    rw [sum4_swap12 (fun b b' c c' => gi b' b * gi c c' * Y b' b c' d c)]
  have hT2 : ∑ b, ∑ b', gi b b' * boxJ gi (Y b') b d =
      ∑ i, ∑ j, ∑ c, ∑ c', gi i j * gi c c' * Y i j c' d c := by
    have e2 : ∀ b b' i j, gi b b' * (gi i j * Y b' i j b d) = gi i j * gi b b' * Y i j b' d b :=
      fun b b' i j => by
        rw [hY.symm₁ b' i j, hY.symm₂ i b' j, hY.tensor_symm i j b' b d]; ring
    simp only [boxJ, mul_sum, e2]
    rw [sum4_swap23 (fun b b' i j => gi i j * gi b b' * Y i j b' d b),
      sum4_swap12 (fun b i b' j => gi i j * gi b b' * Y i j b' d b),
      sum4_swap34 (fun i b b' j => gi i j * gi b b' * Y i j b' d b),
      sum4_swap23 (fun i b j b' => gi i j * gi b b' * Y i j b' d b)]
  have hT3 : ∑ b, ∑ b', gi b b' * trJ gi (Y b') d b =
      ∑ b, ∑ b', ∑ p, ∑ q, gi b b' * gi p q * Y d b b' p q := by
    simp only [trJ, Metric.trace, mul_sum]
    refine sum_congr rfl fun b _ => sum_congr rfl fun b' _ => sum_congr rfl fun p _ =>
      sum_congr rfl fun q _ => ?_
    rw [hY.symm₁ b' d b, hY.symm₂ d b' b]; ring
  have hKd : K d = ∑ b, ∑ b', ∑ c, ∑ c', gi b b' * gi c c' * Y d b' c' b c -
      ∑ b, ∑ b', ∑ p, ∑ q, gi b b' * gi p q * Y d b b' p q := by
    simp only [K, ddivJ, trJ, Metric.trace, mul_sum]
    congr 1
    · refine sum_congr rfl fun c _ => sum_congr rfl fun c' _ => sum_congr rfl fun e _ =>
        sum_congr rfl fun e' _ => ?_
      rw [hY.tensor_symm d c' e' e c]
    · refine sum_congr rfl fun b _ => sum_congr rfl fun b' _ => sum_congr rfl fun p _ =>
        sum_congr rfl fun q _ => ?_
      ring
  rw [hT1, hT2, hT3, hKd]
  ring


/-! ### The linearized Riemann tensor (2.6) and `H = Ric - ½ g R` -/

/-- The linearized Riemann tensor (2.6),
`R_abcd = ½ (∂_c ∂_b h_da - ∂_c ∂_a h_bd - ∂_d ∂_b h_ca + ∂_d ∂_a h_bc)` (metric-free).
[QuennevilleBelair2015], (2.6), following [Alcubierre2008], p. 39. -/
def Rjet (D : Jet2 ι R) : ι → ι → ι → ι → R := fun a b c d =>
  ⅟2 * (D c b d a - D c a b d - D d b c a + D d a b c)

variable (gi) in
/-- The linearized Ricci tensor `R_bd = gi^{aa'} R_{a b a' d}`. [QuennevilleBelair2015], (2.7), following
[Alcubierre2008], p. 39. -/
def RicJ (D : Jet2 ι R) (b d : ι) : R := ∑ a, ∑ a', gi a a' * Rjet D a b a' d

variable (gi) in
/-- The linearized scalar curvature `R = gi^{bb'} R_bb'`. [QuennevilleBelair2015], (2.8), following [Alcubierre2008],
p. 39. -/
def scalJ (D : Jet2 ι R) : R := ∑ b, ∑ b', gi b b' * RicJ gi D b b'

omit [DecidableEq ι] [Fintype ι] in
/-- The linearized Riemann tensor of a symmetric `C²` field is pair-skew. [QuennevilleBelair2015], (2.6) -/
theorem Rjet_pairSkew {D : Jet2 ι R} (hD : IsSymJet2 D) : CurvatureTensor.PairSkew (Rjet D) := by
  intro a b c d
  simp only [Rjet]
  constructor
  · linear_combination ⅟2 * (hD.deriv_symm a c b d - hD.tensor_symm a c b d -
      hD.deriv_symm a c d b - hD.deriv_symm a d b c + hD.tensor_symm a d b c +
      hD.deriv_symm a d c b + hD.deriv_symm b c a d - hD.tensor_symm b c a d -
      hD.deriv_symm b c d a - hD.deriv_symm b d a c + hD.tensor_symm b d a c +
      hD.deriv_symm b d c a)
  · ring

omit [DecidableEq ι] [Fintype ι] in
/-- The linearized Riemann tensor satisfies the first Bianchi identity. [QuennevilleBelair2015], (2.6) -/
theorem Rjet_bianchi1 {D : Jet2 ι R} (hD : IsSymJet2 D) : CurvatureTensor.Bianchi1 (Rjet D) := by
  intro a b c d
  simp only [Rjet]
  linear_combination ⅟2 * (-hD.deriv_symm a b c d + hD.tensor_symm a b c d +
    hD.deriv_symm a b d c + hD.deriv_symm a c b d - hD.tensor_symm a c b d -
    hD.deriv_symm a c d b - hD.deriv_symm a d b c + hD.tensor_symm a d b c +
    hD.deriv_symm a d c b - hD.deriv_symm b c d a + hD.deriv_symm b d c a - hD.deriv_symm c d b a)

omit [DecidableEq ι] in
/-- **Thm 2.3** (derivation): `H` is the linearized Einstein tensor `Ric - ½ g R` of the
linearized Riemann tensor (2.6), for any constant metric in any dimension.
[QuennevilleBelair2015], Thm 2.3, (2.6)–(2.8). The derivation (linearized Christoffel symbols,
then (2.6)–(2.8)) follows [Alcubierre2008], p. 39; the linearization follows [Wald1984], pp. 75, 183, 441, [Carroll2004], p. 277 and [Stewart1991], p. 24. -/
theorem Hjet_eq_einstein (hgi : gi.IsSymm) {D : Jet2 ι R} (hD : IsSymJet2 D) (b d : ι) :
    Hjet g gi D b d = RicJ gi D b d - ⅟2 * g b d * scalJ gi D := by
  have hRic : ∀ b d, RicJ gi D b d = ⅟2 * mixJ gi D b d - ⅟2 * boxJ gi D b d -
      ⅟2 * trJ gi D d b := fun b d => by
    have e : ∀ a a', gi a a' * Rjet D a b a' d = ⅟2 * (gi a a' * D a' b d a) -
        ⅟2 * (gi a a' * D a' a b d) - ⅟2 * (gi a a' * D d b a' a) +
          ⅟2 * (gi a a' * D d a b a') := fun a a' => by
      simp only [Rjet]; ring
    simp only [RicJ, e, sum_add_distrib, sum_sub_distrib, ← mul_sum]
    rw [sum_sum_symm hgi (fun i j => D i j b d), sum_sum_symm hgi (fun i j => D d b i j)]
    have hm : mixJ gi D b d = ∑ a, ∑ a', gi a a' * D a' b d a +
        ∑ a, ∑ a', gi a a' * D d a b a' := by
      simp only [mixJ, mul_add, sum_add_distrib]
      congr 1
      rw [← sum_sum_symm hgi (fun i j => D d i b j)]
      exact sum_congr rfl fun a _ => sum_congr rfl fun a' _ => by rw [hD.deriv_symm a' d]
    rw [hm, boxJ, trJ, Metric.trace]
    ring
  have hscal : scalJ gi D = 2 * ⅟2 * ddivJ gi D - 2 * ⅟2 * ∑ i, ∑ j, gi i j * trJ gi D i j := by
    have e : ∀ b b', gi b b' * RicJ gi D b b' = ⅟2 * (gi b b' * mixJ gi D b b') -
        ⅟2 * (gi b b' * boxJ gi D b b') - ⅟2 * (gi b b' * trJ gi D b' b) := fun b b' => by
      rw [hRic]; ring
    simp only [scalJ, e, sum_sub_distrib, ← mul_sum]
    rw [sum_sum_symm hgi (fun i j => trJ gi D i j)]
    have hA : ∑ b, ∑ b', gi b b' * mixJ gi D b b' = 2 * ddivJ gi D := by
      have e1 : ∀ b b' c c', gi b b' * (gi c c' * (D c' b b' c + D c' b' b c)) =
          gi c c' * gi b' b * D c' b b' c + gi c c' * gi b b' * D c' b' b c := fun b b' c c' => by
        rw [hgi.apply b' b]; ring
      simp only [mixJ, mul_sum, e1, sum_add_distrib]
      rw [sum4_swap23 (fun b b' c c' => gi c c' * gi b' b * D c' b b' c),
        sum4_swap12 (fun b c b' c' => gi c c' * gi b' b * D c' b b' c),
        sum4_swap34 (fun c b b' c' => gi c c' * gi b' b * D c' b b' c),
        sum4_swap23 (fun c b c' b' => gi c c' * gi b' b * D c' b b' c),
        sum4_swap34 (fun c c' b b' => gi c c' * gi b' b * D c' b b' c),
        sum4_swap23 (fun b b' c c' => gi c c' * gi b b' * D c' b' b c),
        sum4_swap12 (fun b c b' c' => gi c c' * gi b b' * D c' b' b c),
        sum4_swap34 (fun c b b' c' => gi c c' * gi b b' * D c' b' b c),
        sum4_swap23 (fun c b c' b' => gi c c' * gi b b' * D c' b' b c)]
      simp only [ddivJ]
      ring
    have hB : ∑ b, ∑ b', gi b b' * boxJ gi D b b' = ∑ i, ∑ j, gi i j * trJ gi D i j := by
      have e2 : ∀ b b' i j, gi b b' * (gi i j * D i j b b') = gi i j * gi b b' * D i j b b' :=
        fun b b' i j => by ring
      simp only [boxJ, trJ, Metric.trace, mul_sum, e2]
      rw [sum4_swap23 (fun b b' i j => gi i j * gi b b' * D i j b b'),
        sum4_swap12 (fun b i b' j => gi i j * gi b b' * D i j b b'),
        sum4_swap34 (fun i b b' j => gi i j * gi b b' * D i j b b'),
        sum4_swap23 (fun i b j b' => gi i j * gi b b' * D i j b b')]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun p _ =>
        sum_congr rfl fun q _ => by ring
    rw [hA, hB]
    ring
  have h2 : (⅟2 : R) * 2 = 1 := invOf_mul_self 2
  rw [Hjet, hRic, hscal]
  linear_combination (⅟2 * g b d * (ddivJ gi D - ∑ i, ∑ j, gi i j * trJ gi D i j)) * h2

/-! ### Prop 2.4(b): Lorentz gauge -/

/-- **Prop 2.4(b), corrected**, any metric, any dimension: in Lorentz gauge `H = -½ □h̄`.
(The thesis states `H = -□h̄`, contradicting its own (2.11).) [QuennevilleBelair2015], Prop 2.4 (corrected) -/
theorem Hjet_lorentz (hg : g.IsSymm) (hinv : gi * g = 1) {D : Jet2 ι R} (hD : IsSymJet2 D)
    (hL : LorentzJet g gi D) (b d : ι) :
    Hjet g gi D b d = -⅟2 * boxJ gi (barJ g gi D) b d := by
  rw [Hjet_eq_div hg hinv hD]
  simp only [show ∀ i b, divJ gi (barJ g gi D) i b = 0 from hL, mul_zero, sum_const_zero]
  ring

/-- **(2.11)**: in Lorentz gauge, `H = c T ⟺ □h̄ = -2 c T` (the thesis has `c = 8π`).
[QuennevilleBelair2015], (2.11) -/
theorem Hjet_lorentz_eq_iff (hg : g.IsSymm) (hinv : gi * g = 1) {D : Jet2 ι R}
    (hD : IsSymJet2 D) (hL : LorentzJet g gi D) (c : R) (T : Matrix ι ι R) (b d : ι) :
    Hjet g gi D b d = c * T b d ↔ boxJ gi (barJ g gi D) b d = -2 * c * T b d := by
  rw [Hjet_lorentz hg hinv hD hL]
  have h2 : (⅟2 : R) * 2 = 1 := invOf_mul_self 2
  constructor
  · intro h; linear_combination -2 * h - boxJ gi (barJ g gi D) b d * h2
  · intro h; linear_combination -⅟2 * h + c * T b d * h2

/-! ### Linearity -/

omit [DecidableEq ι] in
theorem Hjet_add (D G : Jet2 ι R) (b d : ι) :
    Hjet g gi (D + G) b d = Hjet g gi D b d + Hjet g gi G b d := by
  simp only [Hjet, mixJ, boxJ, trJ, ddivJ, Metric.trace, Pi.add_apply, Matrix.add_apply, mul_add,
    sum_add_distrib]
  ring

omit [DecidableEq ι] [Invertible (2 : R)] in
theorem mixJ_smul (c : R) (D : Jet2 ι R) (b d : ι) : mixJ gi (c • D) b d = c * mixJ gi D b d := by
  simp only [mixJ, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

omit [DecidableEq ι] [Invertible (2 : R)] in
theorem boxJ_smul (c : R) (D : Jet2 ι R) (b d : ι) : boxJ gi (c • D) b d = c * boxJ gi D b d := by
  simp only [boxJ, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

omit [DecidableEq ι] [Invertible (2 : R)] in
theorem trJ_smul (c : R) (D : Jet2 ι R) (i j : ι) : trJ gi (c • D) i j = c * trJ gi D i j := by
  simp only [trJ, Metric.trace, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

omit [DecidableEq ι] [Invertible (2 : R)] in
theorem ddivJ_smul (c : R) (D : Jet2 ι R) : ddivJ gi (c • D) = c * ddivJ gi D := by
  simp only [ddivJ, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ =>
    sum_congr rfl fun _ _ => by ring

omit [DecidableEq ι] in
theorem Hjet_smul (c : R) (D : Jet2 ι R) (b d : ι) :
    Hjet g gi (c • D) b d = c * Hjet g gi D b d := by
  simp only [Hjet, mixJ_smul, boxJ_smul, trJ_smul, ddivJ_smul]
  have : ∑ i, ∑ j, gi i j * (c * trJ gi D i j) = c * ∑ i, ∑ j, gi i j * trJ gi D i j := by
    simp only [mul_sum]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

/-! ### Symbol level (`∂_i ↦ k_i`) -/

/-- The symbol jet `D i j = k_i k_j h` (the 2-jet of `h f(k·x)` up to `f''`). -/
def symbolJet (k : ι → R) (h : Matrix ι ι R) : Jet2 ι R := fun i j => (k i * k j) • h

omit [Fintype ι] [DecidableEq ι] [Invertible (2 : R)] in
@[simp] theorem symbolJet_apply (k : ι → R) (h : Matrix ι ι R) (i j a b : ι) :
    symbolJet k h i j a b = k i * k j * h a b := by
  simp [symbolJet]

omit [Fintype ι] [DecidableEq ι] [Invertible (2 : R)] in
/-- The symbol jet of a symmetric amplitude is symmetric. -/
theorem symbolJet_isSymJet2 (k : ι → R) {h : Matrix ι ι R} (hs : hᵀ = h) :
    IsSymJet2 (symbolJet k h) where
  deriv_symm i j a b := by simp only [symbolJet_apply]; ring
  tensor_symm i j a b := by
    simp only [symbolJet_apply]
    rw [show h a b = h b a by simpa using congrFun (congrFun hs b) a]

variable (g gi) in
/-- The symbol of `H` (Thm 2.3, `∂ ↦ k`). -/
def Hsym (k : ι → R) (h : Matrix ι ι R) (b d : ι) : R := Hjet g gi (symbolJet k h) b d

variable (g gi) in
/-- The divergence symbol `L_b = k^a h̄_ab`. -/
def divSym (k : ι → R) (h : Matrix ι ι R) (b : ι) : R :=
  ∑ a, ∑ a', gi a a' * k a' * Metric.trRev g gi h a b

variable (gi) in
/-- The metric pairing `k·k = gi^{ij} k_i k_j`. -/
def dot (k k' : ι → R) : R := ∑ i, ∑ j, gi i j * k i * k' j

omit [DecidableEq ι] in
theorem barJ_symbolJet (k : ι → R) (h : Matrix ι ι R) (i j : ι) :
    barJ g gi (symbolJet k h) i j = (k i * k j) • Metric.trRev g gi h := by
  simp [barJ, symbolJet, Metric.trRev_smul]

omit [DecidableEq ι] in
/-- `∂_i L_b ↦ k_i L_b`. -/
theorem divJ_symbolJet (k : ι → R) (h : Matrix ι ι R) (i b : ι) :
    divJ gi (barJ g gi (symbolJet k h)) i b = k i * divSym g gi k h b := by
  simp only [divJ, barJ_symbolJet, Matrix.smul_apply, smul_eq_mul, divSym, mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

omit [DecidableEq ι] in
/-- `□h̄ ↦ (k·k) h̄`. -/
theorem boxJ_symbolJet (k : ι → R) (h : Matrix ι ι R) (a b : ι) :
    boxJ gi (barJ g gi (symbolJet k h)) a b = dot gi k k * Metric.trRev g gi h a b := by
  simp only [boxJ, barJ_symbolJet, Matrix.smul_apply, smul_eq_mul, dot, sum_mul]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- **Thm 2.3** at the symbol level:
`H = ½ (k_b L_d + k_d L_b) - ½ (k·k) h̄_bd - ½ g_bd k^a L_a`. [QuennevilleBelair2015], Thm 2.3 -/
theorem Hsym_eq (hg : g.IsSymm) (hinv : gi * g = 1) (k : ι → R) {h : Matrix ι ι R}
    (hs : hᵀ = h) (b d : ι) :
    Hsym g gi k h b d = ⅟2 * (k b * divSym g gi k h d + k d * divSym g gi k h b)
      - ⅟2 * dot gi k k * Metric.trRev g gi h b d -
        ⅟2 * g b d * ∑ a, ∑ a', gi a a' * k a' * divSym g gi k h a := by
  rw [Hsym, Hjet_eq_div hg hinv (symbolJet_isSymJet2 k hs)]
  simp only [divJ_symbolJet, boxJ_symbolJet, mul_assoc]

omit [DecidableEq ι] in
/-- Gauge invariance at the symbol level: `H(k ⊗ ξ + ξ ⊗ k) = 0`. [QuennevilleBelair2015], §2.7; see
[Wald1984], pp. 75, 183, 441, [Carroll2004], p. 277 and [Stewart1991], p. 24. -/
theorem Hsym_gauge (hgi : gi.IsSymm) (k ξ : ι → R) (b d : ι) :
    Hsym g gi k (Matrix.of fun a c => k a * ξ c + k c * ξ a) b d = 0 := by
  have hX : IsSymJet3ξ (fun i j c b => k i * k j * k c * ξ b) :=
    ⟨fun _ _ _ _ => by ring, fun _ _ _ _ => by ring⟩
  have e : symbolJet k (Matrix.of fun a c => k a * ξ c + k c * ξ a) =
      gaugeJet (fun i j c b => k i * k j * k c * ξ b) := by
    funext i j; ext a b; simp only [symbolJet_apply, gaugeJet_apply, Matrix.of_apply]; ring
  rw [Hsym, e]; exact Hjet_gauge hgi hX b d

/-- The linearized Bianchi identity at the symbol level: `k^b H_bd = 0`. [QuennevilleBelair2015], §2.7 -/
theorem Hsym_div (hg : g.IsSymm) (hgi : gi.IsSymm) (hinv : gi * g = 1) (k : ι → R)
    {h : Matrix ι ι R} (hs : hᵀ = h) (d : ι) :
    ∑ b, ∑ b', gi b b' * k b' * Hsym g gi k h b d = 0 := by
  have hY : IsSymJet3 (fun m => k m • symbolJet k h) :=
    ⟨fun _ _ _ _ _ => by simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
        symbolJet_apply]; ring,
      fun _ _ _ _ _ => by simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
        symbolJet_apply]; ring,
      fun _ _ _ a b => by
        simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, symbolJet_apply]
        rw [show h a b = h b a by simpa using congrFun (congrFun hs b) a]⟩
  have := Hjet_bianchi hg hgi hinv hY d
  simp only [Hjet_smul] at this
  rw [← this]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by rw [Hsym]; ring

/-- **Prop 2.4(b), corrected**, symbol level: if `k^a h̄_ab = 0`, then `H = -½ (k·k) h̄`.
[QuennevilleBelair2015], Prop 2.4 (corrected) -/
theorem Hsym_lorentz (hg : g.IsSymm) (hinv : gi * g = 1) (k : ι → R) {h : Matrix ι ι R}
    (hs : hᵀ = h) (hL : ∀ b, divSym g gi k h b = 0) (b d : ι) :
    Hsym g gi k h b d = -⅟2 * dot gi k k * Metric.trRev g gi h b d := by
  rw [Hsym_eq hg hinv k hs]; simp [hL]

omit [DecidableEq ι] in
/-- Symbol-level Lorentz gauge implies jet-level Lorentz gauge. -/
theorem lorentzJet_symbolJet (k : ι → R) (h : Matrix ι ι R) (hL : ∀ b, divSym g gi k h b = 0) :
    LorentzJet g gi (symbolJet k h) := fun i b => by rw [divJ_symbolJet, hL, mul_zero]

end Feec.LinearizedGravity
