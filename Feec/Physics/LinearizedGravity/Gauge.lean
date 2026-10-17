module

public import Feec.Physics.LinearizedGravity.Einstein
public import Feec.ForMathlib.Calculus.Partial

/-!
# Linearized gravity for fields: gauge invariance, Bianchi identity, Lorentz gauge

Genuine fields `h : ℝ^ι → Sym(ι)` (any dimension, any constant metric `g` with inverse `gi`),
with coordinate derivatives `partialDeriv`. The jet identities of
`Feec.Physics.LinearizedGravity.Einstein` apply through `jet2_isSymJet2` (Schwarz).

## Main definitions

* `jet2 h x`: the genuine 2-jet `∂_i ∂_j h_ab (x)`; `Hfun g gi h x = Hjet g gi (jet2 h x)`.
* `box gi u` (`□u = gi^{ij} ∂_i ∂_j u`), `divF gi h` (`∂^a h_ab`), `gaugeTR g gi ξ`
  (`2∂_(a ξ_b) - g_ab ∂·ξ`), `WaveSolvable gi`.

## Main results

* `Hfun_eq_bar` (Thm 2.3), `Hfun_lorentz` and `Hfun_lorentz_eq_iff` (Prop 2.4(b) corrected,
  (2.11)), `Hfun_gauge` (`H(h + 2∂_(a ξ_b)) = H(h)`), `Hfun_bianchi` (`∂^b H_bd = 0`).
* `divF_gaugeTR` (`∂^a (2∂_(a ξ_b) - g_ab ∂·ξ) = □ξ_b`) and `exists_lorentz_gauge`
  (Prop 2.4(a), with the wave solver as the explicit hypothesis `WaveSolvable`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §2.7 (Thm 2.3, (2.5), (2.10)–(2.11)), §2.8 (Prop 2.4)
* [R. M. Wald, *General Relativity*][Wald1984], §4.4; pp. 75, 183, 441
* [S. M. Carroll, *Spacetime and Geometry: An Introduction to General Relativity*][Carroll2004],
  p. 277
* [J. Stewart, *Advanced General Relativity*][Stewart1991], p. 24
* [M. Alcubierre, *Introduction to 3+1 Numerical Relativity*][Alcubierre2008], p. 39
-/

open Finset Matrix
open scoped ContDiff

@[expose] public noncomputable section

namespace Feec.LinearizedGravity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Genuine jets -/

/-- The 2-jet `∂_i ∂_j h_ab (x)` of a field `h : ℝ^ι → Sym(ι)`. -/
def jet2 (h : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ) : Jet2 ι ℝ := fun i j => Matrix.of fun a b =>
  partialDeriv i (partialDeriv j (fun y => h y a b)) x

variable (g gi : Matrix ι ι ℝ)

/-- The linearized Einstein tensor `H(h)(x)` (Thm 2.3) of a `C²` field. [QuennevilleBelair2015], Thm 2.3; the
linearization follows [Wald1984], pp. 75, 183, 441, [Carroll2004], p. 277 and [Stewart1991], p. 24. -/
def Hfun (h : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ) (b d : ι) : ℝ := Hjet g gi (jet2 h x) b d

/-- d'Alembertian `□u = gi^{ij} ∂_i ∂_j u`. -/
def box (u : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ := ∑ i, ∑ j, gi i j * partialDeriv i (partialDeriv j u) x

/-- Divergence `∂^a h_ab = gi^{aa'} ∂_a' h_ab`. -/
def divF (h : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ) (b : ι) : ℝ :=
  ∑ a, ∑ a', gi a a' * partialDeriv a' (fun y => h y a b) x

variable {g gi}

/-- Schwarz: the 2-jet of a `C²` symmetric field satisfies `IsSymJet2`. [QuennevilleBelair2015], §2.7 -/
theorem jet2_isSymJet2 {h : (ι → ℝ) → Matrix ι ι ℝ} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b)
    (hs : ∀ y a b, h y a b = h y b a) (x : ι → ℝ) : IsSymJet2 (jet2 h x) where
  deriv_symm i j a b := partialDeriv_comm (hC a b) i j x
  tensor_symm i j a b := by
    simp only [jet2, of_apply]; congr 2; funext y; rw [hs]

/-- `∂_i` commutes with trace reversal. -/
theorem partialDeriv_trRev {F : (ι → ℝ) → Matrix ι ι ℝ} {x : ι → ℝ}
    (hF : ∀ a b, DifferentiableAt ℝ (fun y => F y a b) x) (i a b : ι) :
    partialDeriv i (fun y => Metric.trRev g gi (F y) a b) x =
      Metric.trRev g gi (Matrix.of fun a' b' => partialDeriv i (fun y => F y a' b') x) a b := by
  have hT : DifferentiableAt ℝ (fun y => Metric.trace gi (F y)) x := by
    simp only [Metric.trace]
    exact DifferentiableAt.fun_sum fun j _ => DifferentiableAt.fun_sum fun k _ =>
      (hF j k).const_mul _
  have e1 : (fun y => Metric.trRev g gi (F y) a b) =
      fun y => F y a b - (⅟2 * g a b) * Metric.trace gi (F y) := by
    funext y; rw [Metric.trRev_apply]; ring
  have e2 : partialDeriv i (fun y => Metric.trace gi (F y)) x =
      Metric.trace gi (Matrix.of fun a' b' => partialDeriv i (fun y => F y a' b') x) := by
    simp only [Metric.trace]
    rw [partialDeriv_sum (f := fun j y => ∑ k, gi j k * F y j k) univ
      (fun j _ => DifferentiableAt.fun_sum fun k _ => (hF j k).const_mul _)]
    refine sum_congr rfl fun j _ => ?_
    rw [partialDeriv_sum (f := fun k y => gi j k * F y j k) univ
      (fun k _ => (hF j k).const_mul _)]
    refine sum_congr rfl fun k _ => ?_
    rw [show (fun y => gi j k * F y j k) = fun y => gi j k • F y j k from rfl,
      partialDeriv_const_smul (hF j k)]
    simp
  rw [e1, partialDeriv_sub (hF a b) (hT.const_mul _),
    show (fun y => ⅟2 * g a b * Metric.trace gi (F y)) =
      fun y => (⅟2 * g a b) • Metric.trace gi (F y) from rfl,
    partialDeriv_const_smul hT, e2, Metric.trRev_apply]
  simp only [of_apply, smul_eq_mul]; ring

/-- The 2-jet of `h̄ = trRev h` is the trace reversal of the 2-jet of `h`. -/
theorem jet2_trRev {h : (ι → ℝ) → Matrix ι ι ℝ} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b)
    (x : ι → ℝ) : jet2 (fun y => Metric.trRev g gi (h y)) x = barJ g gi (jet2 h x) := by
  funext i j; ext a b
  have e : partialDeriv j (fun y => Metric.trRev g gi (h y) a b) =
      fun y => Metric.trRev g gi
        (Matrix.of fun a' b' => partialDeriv j (fun z => h z a' b') y) a b := by
    funext y
    exact partialDeriv_trRev (fun a' b' => ((hC a' b').differentiable (by norm_num)) y) j a b
  simp only [jet2, of_apply, e, barJ]
  exact partialDeriv_trRev
    (fun a' b' => by simpa using (hC a' b').differentiable_partialDeriv le_rfl j x) i a b

/-- **Thm 2.3** for a genuine `C²` symmetric field, any constant metric, any dimension: both
forms of `H` agree, with the genuine 2-jet of `h̄`. [QuennevilleBelair2015], Thm 2.3, whose proof
follows [Alcubierre2008], p. 39. -/
theorem Hfun_eq_bar (hg : g.IsSymm) (hinv : gi * g = 1) {h : (ι → ℝ) → Matrix ι ι ℝ}
    (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b) (hs : ∀ y a b, h y a b = h y b a) (x : ι → ℝ)
    (b d : ι) :
    Hfun g gi h x b d = HbarJet g gi (jet2 (fun y => Metric.trRev g gi (h y)) x) b d := by
  rw [Hfun, Hjet_eq_bar hg hinv (jet2_isSymJet2 hC hs x), jet2_trRev hC]

omit [DecidableEq ι] in
/-- Trace reversal of a `C²` field is `C²`. -/
theorem contDiff_trRev {h : (ι → ℝ) → Matrix ι ι ℝ} {k : WithTop ℕ∞}
    (hC : ∀ a b, ContDiff ℝ k fun y => h y a b) (a b : ι) :
    ContDiff ℝ k fun y => Metric.trRev g gi (h y) a b := by
  simp only [Metric.trRev_apply, Metric.trace]
  exact (hC a b).sub ((contDiff_const.mul (ContDiff.sum fun j _ => ContDiff.sum fun l _ =>
    contDiff_const.mul (hC j l))).mul contDiff_const)

/-- **Prop 2.4(b), corrected**, for a genuine `C²` symmetric field (any constant metric, any
dimension): if `h̄ = trRev h` is in Lorentz gauge everywhere, then `H(h) = -½ □h̄`.
(The thesis states `H = -□h̄`.) [QuennevilleBelair2015], Prop 2.4 (corrected) -/
theorem Hfun_lorentz (hg : g.IsSymm) (hinv : gi * g = 1) {h : (ι → ℝ) → Matrix ι ι ℝ}
    (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b) (hs : ∀ y a b, h y a b = h y b a)
    (hL : ∀ y b, divF gi (fun z => Metric.trRev g gi (h z)) y b = 0) (x : ι → ℝ) (b d : ι) :
    Hfun g gi h x b d = -⅟2 * box gi (fun y => Metric.trRev g gi (h y) b d) x := by
  have hbC : ∀ a b, ContDiff ℝ 2 fun y => Metric.trRev g gi (h y) a b := contDiff_trRev hC
  have hJ : LorentzJet g gi (jet2 h x) := by
    intro i c
    rw [← jet2_trRev hC]
    have e : partialDeriv i (fun y => divF gi (fun z => Metric.trRev g gi (h z)) y c) x = 0 := by
      simp only [hL]; simp
    rw [← e]
    simp only [divF, divJ, jet2, of_apply]
    rw [partialDeriv_sum (f := fun a y => ∑ a', gi a a' *
      partialDeriv a' (fun z => Metric.trRev g gi (h z) a c) y) univ
      (fun a _ => DifferentiableAt.fun_sum fun a' _ =>
        ((hbC a c).differentiable_partialDeriv le_rfl a' x).const_mul _)]
    refine sum_congr rfl fun a _ => ?_
    rw [partialDeriv_sum (f := fun a' y => gi a a' *
      partialDeriv a' (fun z => Metric.trRev g gi (h z) a c) y) univ
      (fun a' _ => ((hbC a c).differentiable_partialDeriv le_rfl a' x).const_mul _)]
    refine sum_congr rfl fun a' _ => ?_
    rw [show (fun y => gi a a' * partialDeriv a' (fun z => Metric.trRev g gi (h z) a c) y) =
      fun y => gi a a' • partialDeriv a' (fun z => Metric.trRev g gi (h z) a c) y from rfl,
      partialDeriv_const_smul ((hbC a c).differentiable_partialDeriv le_rfl a' x), smul_eq_mul]
  rw [Hfun, Hjet_lorentz hg hinv (jet2_isSymJet2 hC hs x) hJ, ← jet2_trRev hC]
  rfl

/-- **(2.11)** for genuine fields: in Lorentz gauge, `H(h) = c T ⟺ □h̄ = -2 c T` (the thesis
has `c = 8π`). [QuennevilleBelair2015], (2.11) -/
theorem Hfun_lorentz_eq_iff (hg : g.IsSymm) (hinv : gi * g = 1) {h : (ι → ℝ) → Matrix ι ι ℝ}
    (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b) (hs : ∀ y a b, h y a b = h y b a)
    (hL : ∀ y b, divF gi (fun z => Metric.trRev g gi (h z)) y b = 0) (c : ℝ)
    (T : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ) (b d : ι) :
    Hfun g gi h x b d = c * T x b d ↔
      box gi (fun y => Metric.trRev g gi (h y) b d) x = -2 * c * T x b d := by
  rw [Hfun_lorentz hg hinv hC hs hL, invOf_eq_inv]
  constructor <;> intro h <;> linarith

/-! ### Gauge invariance for fields -/

/-- **Gauge invariance** for genuine fields: `H(h + 2∂_(a ξ_b)) = H(h)` for `h ∈ C²`,
`ξ ∈ C³`, any constant metric, any dimension. [QuennevilleBelair2015], §2.7; see
[Wald1984], pp. 75, 183, 441, [Carroll2004], p. 277 and [Stewart1991], p. 24. -/
theorem Hfun_gauge (hgi : gi.IsSymm) {h : (ι → ℝ) → Matrix ι ι ℝ}
    (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b) {ξ : ι → (ι → ℝ) → ℝ}
    (hξ : ∀ a, ContDiff ℝ 3 (ξ a)) (x : ι → ℝ) (b d : ι) :
    Hfun g gi (fun y => Matrix.of fun a b => h y a b +
      (partialDeriv a (ξ b) y + partialDeriv b (ξ a) y)) x b d = Hfun g gi h x b d := by
  have hξ2 : ∀ a, ContDiff ℝ 2 (ξ a) := fun a => (hξ a).of_le (by norm_num)
  have hP : ∀ c a, ContDiff ℝ 2 (partialDeriv c (ξ a)) := fun c a =>
    (hξ a).partialDeriv (by norm_num) c
  set X : ι → ι → ι → ι → ℝ := fun i j c b =>
    partialDeriv i (partialDeriv j (partialDeriv c (ξ b))) x
  have hX : IsSymJet3ξ X := ⟨fun i j c b => partialDeriv_comm (hP c b) i j x, fun i j c b => by
      simp only [X]; congr 1; funext y; exact partialDeriv_comm (hξ2 b) j c y⟩
  have e : jet2 (fun y => Matrix.of fun a b => h y a b +
      (partialDeriv a (ξ b) y + partialDeriv b (ξ a) y)) x = jet2 h x + gaugeJet X := by
    funext i j; ext a b
    have hd := fun a b => (hC a b).differentiable (by norm_num)
    have hdP := fun c a => (hP c a).differentiable (by norm_num)
    have e1 : partialDeriv j (fun y => h y a b + (partialDeriv a (ξ b) y + partialDeriv b (ξ a) y))
        = fun y => partialDeriv j (fun z => h z a b) y +
          (partialDeriv j (partialDeriv a (ξ b)) y + partialDeriv j (partialDeriv b (ξ a)) y) := by
      funext y
      rw [partialDeriv_add (hd a b y) ((hdP a b y).fun_add (hdP b a y)),
        partialDeriv_add (hdP a b y) (hdP b a y)]
    simp only [jet2, of_apply, e1, Pi.add_apply, Matrix.add_apply, gaugeJet_apply, X]
    rw [partialDeriv_add ((hC a b).differentiable_partialDeriv le_rfl j x)
      (((hP a b).differentiable_partialDeriv le_rfl j x).fun_add
        ((hP b a).differentiable_partialDeriv le_rfl j x)),
      partialDeriv_add ((hP a b).differentiable_partialDeriv le_rfl j x)
        ((hP b a).differentiable_partialDeriv le_rfl j x)]
  rw [Hfun, e, Hjet_add, Hjet_gauge hgi hX, add_zero, Hfun]

/-! ### The linearized Bianchi identity for fields -/

variable (g gi) in
/-- `H` as a continuous linear functional on jets written as arrays. -/
def HjetL (b d : ι) : (ι → ι → ι → ι → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Hjet g gi (fun i j => Matrix.of (D i j)) b d
      map_add' := fun D G => Hjet_add (fun i j => Matrix.of (D i j)) (fun i j => Matrix.of (G i j))
        b d
      map_smul' := fun c D => Hjet_smul c (fun i j => Matrix.of (D i j)) b d }

/-- Evaluation of a jet array at an index, as a continuous linear functional. -/
def evalJet (i j a b : ι) : (ι → ι → ι → ι → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun D => D i j a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- **Linearized Bianchi identity** for genuine fields: `∂^b H_bd(h) = 0` for every `C³`
symmetric `h`, any constant metric, any dimension. Not stated in the thesis. [QuennevilleBelair2015], §2.7 -/
theorem Hfun_bianchi (hg : g.IsSymm) (hgi : gi.IsSymm) (hinv : gi * g = 1)
    {h : (ι → ℝ) → Matrix ι ι ℝ} (hC : ∀ a b, ContDiff ℝ 3 fun y => h y a b)
    (hs : ∀ y a b, h y a b = h y b a) (x : ι → ℝ) (d : ι) :
    ∑ b, ∑ b', gi b b' * partialDeriv b' (fun y => Hfun g gi h y b d) x = 0 := by
  have h2 : ∀ a b, ContDiff ℝ 2 fun y => h y a b := fun a b => (hC a b).of_le (by norm_num)
  have hP : ∀ j a b, ContDiff ℝ 2 (partialDeriv j fun y => h y a b) :=
    fun j a b => (hC a b).partialDeriv (by norm_num) j
  set J : (ι → ℝ) → ι → ι → ι → ι → ℝ := fun y i j a b => jet2 h y i j a b with hJdef
  have hJ : DifferentiableAt ℝ J x := by
    refine differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j =>
      differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun b => ?_
    exact (hP j a b).differentiable_partialDeriv le_rfl i x
  have hent : ∀ m i j a b, partialDeriv m J x i j a b =
      partialDeriv m (fun y => J y i j a b) x := fun m i j a b => by
    have := ContinuousLinearMap.partialDeriv_comp (evalJet i j a b) hJ m
    simpa [evalJet] using this.symm
  set Y : Jet3 ι ℝ := fun m i j => Matrix.of fun a b =>
    partialDeriv m (partialDeriv i (partialDeriv j fun y => h y a b)) x with hY
  have hYs : IsSymJet3 Y := ⟨fun m i j a b => partialDeriv_comm (hP j a b) m i x,
    fun m i j a b => by
      simp only [Y, of_apply]; congr 1; funext y; exact partialDeriv_comm (h2 a b) i j y,
    fun m i j a b => by simp only [Y, of_apply]; congr 3; funext y; rw [hs]⟩
  have e : ∀ b b', partialDeriv b' (fun y => Hfun g gi h y b d) x = Hjet g gi (Y b') b d := by
    intro b b'
    have e1 : (fun y => Hfun g gi h y b d) = fun y => HjetL g gi b d (J y) := rfl
    rw [e1, ContinuousLinearMap.partialDeriv_comp (HjetL g gi b d) hJ b']
    show Hjet g gi (fun i j => Matrix.of (partialDeriv b' J x i j)) b d = Hjet g gi (Y b') b d
    congr 1
    funext i j; ext a c
    show partialDeriv b' J x i j a c = Y b' i j a c
    rw [hent]; rfl
  simp only [e]
  exact Hjet_bianchi hg hgi hinv hYs d

/-! ### Prop 2.4(a): existence of the Lorentz gauge -/

variable (g gi) in
/-- The trace-reversed pure-gauge field `2∂_(a ξ_b) - g_ab ∂·ξ`, `∂·ξ = gi^{cc'} ∂_c ξ_c'`
(cf. (2.5)). -/
def gaugeTR (ξ : ι → (ι → ℝ) → ℝ) (y : ι → ℝ) : Matrix ι ι ℝ := Matrix.of fun a b =>
  partialDeriv a (ξ b) y + partialDeriv b (ξ a) y -
    g a b * ∑ c, ∑ c', gi c c' * partialDeriv c (ξ c') y

variable (gi) in
/-- **Hypothesis** (classical, absent from Mathlib): `□u = S` has a smooth solution for every
smooth source `S`. This is the solver Prop 2.4(a) uses without citation. -/
def WaveSolvable : Prop :=
  ∀ S : (ι → ℝ) → ℝ, ContDiff ℝ ∞ S → ∃ u : (ι → ℝ) → ℝ, ContDiff ℝ ∞ u ∧ ∀ x, box gi u x = S x

/-- `∂^a (2∂_(a ξ_b) - g_ab ∂·ξ) = □ξ_b` (Schwarz and `gi g = 1`). -/
theorem divF_gaugeTR (hg : g.IsSymm) (hgi : gi.IsSymm) (hinv : gi * g = 1) {ξ : ι → (ι → ℝ) → ℝ}
    (hξ : ∀ a, ContDiff ℝ ∞ (ξ a)) (x : ι → ℝ) (b : ι) :
    divF gi (gaugeTR g gi ξ) x b = box gi (ξ b) x := by
  have h2 : ∀ a, ContDiff ℝ 2 (ξ a) := fun a => (hξ a).of_le (by simp)
  have hd : ∀ a c, Differentiable ℝ (partialDeriv a (ξ c)) := fun a c =>
    (h2 c).differentiable_partialDeriv le_rfl a
  have hS : Differentiable ℝ (fun y => ∑ c, ∑ c', gi c c' * partialDeriv c (ξ c') y) :=
    Differentiable.fun_sum fun c _ => Differentiable.fun_sum fun c' _ => (hd c c').const_mul _
  set Div : (ι → ℝ) → ℝ := fun y => ∑ c, ∑ c', gi c c' * partialDeriv c (ξ c') y with hDiv
  have e : ∀ a a', partialDeriv a' (fun y => gaugeTR g gi ξ y a b) x =
      partialDeriv a' (partialDeriv a (ξ b)) x + partialDeriv a' (partialDeriv b (ξ a)) x -
        g a b * partialDeriv a' Div x := by
    intro a a'
    simp only [gaugeTR, of_apply]
    rw [partialDeriv_sub ((hd a b x).fun_add (hd b a x)) ((hS x).const_mul _),
      partialDeriv_add (hd a b x) (hd b a x),
      show (fun y => g a b * Div y) = fun y => g a b • Div y from rfl,
      partialDeriv_const_smul (hS x), smul_eq_mul]
  have eQ : ∑ a, ∑ a', gi a a' * partialDeriv a' (partialDeriv b (ξ a)) x =
      partialDeriv b Div x := by
    simp only [Div]
    rw [partialDeriv_sum (f := fun c y => ∑ c', gi c c' * partialDeriv c (ξ c') y) univ
      (fun c _ => DifferentiableAt.fun_sum fun c' _ => ((hd c c').const_mul _) x)]
    rw [sum_sum_symm hgi (fun a' a => partialDeriv a' (partialDeriv b (ξ a)) x)]
    refine sum_congr rfl fun c _ => ?_
    rw [partialDeriv_sum (f := fun c' y => gi c c' * partialDeriv c (ξ c') y) univ
      (fun c' _ => ((hd c c').const_mul _) x)]
    refine sum_congr rfl fun c' _ => ?_
    rw [show (fun y => gi c c' * partialDeriv c (ξ c') y) =
      fun y => gi c c' • partialDeriv c (ξ c') y from rfl, partialDeriv_const_smul (hd c c' x),
      smul_eq_mul, partialDeriv_comm (h2 c') c b x]
  have eC : ∑ a, ∑ a', gi a a' * (g a b * partialDeriv a' Div x) = partialDeriv b Div x := by
    have := contract hinv (fun a' => partialDeriv a' Div x) b
    rw [← this]
    exact sum_congr rfl fun a _ => sum_congr rfl fun a' _ => by rw [hg.apply b a]; ring
  simp only [divF, e, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]
  rw [eQ, eC, sum_sum_symm hgi (fun a' a => partialDeriv a' (partialDeriv a (ξ b)) x), box]
  ring

/-- **Prop 2.4(a)** (any constant metric, any dimension): assuming the wave solver
`WaveSolvable`, every smooth `h̄` is gauge-equivalent to one in Lorentz gauge: there is a
smooth `ξ` with `∂^a (h̄ - (2∂_(a ξ_b) - g_ab ∂·ξ))_ab = 0`. By (2.5) the new `h̄` is the trace
reversal of `h - 2∂_(a ξ_b)`. The thesis uses the solver without citation, and produces only the
infinitesimal gauge vector `ξ` (not a diffeomorphism). [QuennevilleBelair2015], Prop 2.4 -/
theorem exists_lorentz_gauge (hg : g.IsSymm) (hgi : gi.IsSymm) (hinv : gi * g = 1)
    (hW : WaveSolvable gi) {hb : (ι → ℝ) → Matrix ι ι ℝ}
    (hsm : ∀ a b, ContDiff ℝ ∞ fun y => hb y a b) :
    ∃ ξ : ι → (ι → ℝ) → ℝ, (∀ a, ContDiff ℝ ∞ (ξ a)) ∧
      ∀ x b, divF gi (fun y => hb y - gaugeTR g gi ξ y) x b = 0 := by
  have hS : ∀ b, ContDiff ℝ ∞ fun x => divF gi hb x b := fun b =>
    ContDiff.sum fun a _ => ContDiff.sum fun a' _ =>
      contDiff_const.mul ((hsm a b).partialDeriv (by simp) a')
  choose ξ hξ hbox using fun b => hW _ (hS b)
  refine ⟨ξ, hξ, fun x b => ?_⟩
  have h2 : ∀ a, ContDiff ℝ 2 (ξ a) := fun a => (hξ a).of_le (by simp)
  have hd : ∀ a c, Differentiable ℝ (partialDeriv a (ξ c)) := fun a c =>
    (h2 c).differentiable_partialDeriv le_rfl a
  have hG : ∀ a, DifferentiableAt ℝ (fun y => gaugeTR g gi ξ y a b) x := fun a => by
    simp only [gaugeTR, of_apply]
    exact (((hd a b).fun_add (hd b a)).fun_sub
      ((Differentiable.fun_sum fun c _ => Differentiable.fun_sum fun c' _ =>
        (hd c c').const_mul _).const_mul _)) x
  have hH : ∀ a, DifferentiableAt ℝ (fun y => hb y a b) x := fun a =>
    ((hsm a b).differentiable (by simp)) x
  have e : ∀ a', ∀ a, partialDeriv a' (fun y => (hb y - gaugeTR g gi ξ y) a b) x =
      partialDeriv a' (fun y => hb y a b) x - partialDeriv a' (fun y => gaugeTR g gi ξ y a b) x :=
    fun a' a => partialDeriv_sub (hH a) (hG a) a'
  have h1 := divF_gaugeTR hg hgi hinv hξ x b
  have h2' := hbox b x
  simp only [divF] at h1 h2' ⊢
  have e' : ∀ a a', gi a a' * partialDeriv a' (fun y => (hb y - gaugeTR g gi ξ y) a b) x =
      gi a a' * partialDeriv a' (fun y => hb y a b) x -
        gi a a' * partialDeriv a' (fun y => gaugeTR g gi ξ y a b) x := fun a a' => by
    rw [e a' a]; ring
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => e' a a']
  simp only [Finset.sum_sub_distrib]
  rw [h1, h2', sub_self]

end Feec.LinearizedGravity
