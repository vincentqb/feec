import Feec.Foundation

/-!
# Ch 2: linearized gravity on Minkowski space (jet, symbol and plane-wave level)

Formalizes §2.7–§2.8 of the thesis (Thm 2.3, (2.5), (2.10), Prop 2.4, (2.11), Prop 2.5,
(2.12)–(2.13), Prop 2.6, (2.15)) in components over `Fin 4`.

## Conventions (thesis: signature (−+++), `n = 4`)

* All tensors carry **lower** indices: `h a b = h_ab`, `k i = k_i`, `ξ a = ξ_a`.
  Indices are raised with `η^{ab} = diag(η)`; numerically `η^{aa} = η_aa = η a`
  (`Feec.η = ![-1, 1, 1, 1]`), so every contraction `u^a v_a` is written `∑ a, η a * u a * v a`.
* Coordinates `x = (x^0, …, x^3)` are contravariant; `∂_i = pd i`, and the phase of a plane
  wave is `k_c x^c = ∑ c, k c * x c`. Hence `∂_i f(k·x) = k_i f'(k·x)`, and
  `□ = η^{ij} ∂_i ∂_j = ∑ i, η i * ∂_i ∂_i`, `k·k = ∑ i, η i * k i * k i` (`dot k k`).
* **Jets.** `H` (Thm 2.3) is a linear constant-coefficient second-order operator, so it is
  a linear function of the 2-jet `D i j a b = ∂_i ∂_j h_ab`, which is symmetric in `(i, j)`
  (Schwarz) and in `(a, b)`. Thm 2.3, its trace-reversed form, gauge invariance (3-jets of
  `ξ`), the linearized Bianchi identity (3-jets of `h`) and Prop 2.4(b) are proved as exact
  identities on such jets (`IsSymJet2`, …). The **symbol** level (`∂_i ↦ k_i`,
  `D = k ⊗ k ⊗ h`) is the special case `symbolJet`.
* **Functions.** `jet2 h x` is the genuine 2-jet (via `fderiv`) of a field
  `h : (Fin 4 → ℝ) → Sym2`; `jet2_isSymJet2` (Schwarz) connects the two levels, so
  `Hfun h x := Hjet (jet2 h x)` is the genuine linearized Einstein tensor of a `C²` field.

## Main results

* `trRev_trace`, `trRev_trRev`, `trRev_gauge`: (2.5) (trace reversal, `n = 4`).
* `Hjet_eq_bar`, `Hjet_eq_div`: Thm 2.3, both forms, and the exact operator form
  `H = E(div h̄) − ½ □h̄ − ½ η div div h̄`. `Hjet_eq_einstein`: `H = Ric − ½ η R` for the
  linearized Riemann tensor (2.6), which is an algebraic curvature tensor
  (`Rjet_pairSkew`, `Rjet_bianchi1`).
* `Hjet_gauge`: gauge invariance `H(2∂_(a ξ_b)) = 0` (end of §2.7);
  `Hjet_bianchi`: linearized Bianchi `∂^b H_bd = 0` (new).
* `Hjet_lorentz`, `lorentz_eq_iff`, `Hsym_lorentz_eq_iff`: **Prop 2.4(b) corrected**
  (`H = −½ □h̄`) and (2.11) (jet and symbol level);
  `thesis_prop_2_4b_false`: the printed `H = −□h̄` is false.
* `exists_lorentz_gauge`: Prop 2.4(a), with the wave solver as the explicit hypothesis
  `WaveSolvable`.
* `plane_wave`: Prop 2.5 with genuine derivatives (`□h̄ = 0`, `∂^a h̄_ab = 0`, `H = 0`).
* `isTT_iff`, `finrank_ttSub`: the TT normal form (2.13) and its two degrees of freedom.
* `tt_gauge`, `tt_gauge_fun`: **Prop 2.6 corrected** (gauge vector `−B`, amplitudes
  `A'₊ = (A₁₁ − A₂₂)/2`, `A'ₓ = A₁₂`); `thesis_gauge_fails`, `thesis_gauge_fails_contra`:
  the printed `B` fails (covariant and contravariant readings).
* `Rjet_tt`, `Rjet_tt_support`, `Rjet_ttWave`: (2.15a–c), `R_{αiβj} = −½ ∂_α∂_β h_ij` in TT
  gauge, and these are the only non-zero components.
* `tt_accel`, `tt_accel_fun`: **(2.15) corrected** accelerations
  `a¹ = (κ²/2)(A₊v¹ + Aₓv²) f''`; `thesis_accel_fails`.
* Function level (genuine `fderiv` derivatives): `jet2_isSymJet2` (Schwarz), `jet2_trRev`,
  `Hfun_eq_bar` (Thm 2.3), `Hfun_lorentz`, `lorentz_fun_iff` (Prop 2.4(b), (2.11)),
  `Hfun_gauge` (`H(h + 2∂_(a ξ_b)) = H(h)`), `Hfun_bianchi` (`∂^b H_bd = 0`).
* `einstein_const_bounds`: `8πG/c⁴ ≈ 2.08·10⁻⁴³` (the thesis' `5·10⁻⁴⁴` is `2πG/c⁴`).

## Not formalized

Thm 2.2 (`d/dε ψ_ε^* g(ε) = h + 2Eξ`) and the ε-expansion of the Einstein tensor itself
(the step "`H = dG/dε` at `η`" before (2.6)) are not formalized; `H` enters through the
linearized Riemann tensor (2.6), with `Hjet_eq_einstein` checking `H = Ric − ½ η R`.

## References

* [QuennevilleBelair2015], §2.4 (coupling constant), §2.7 (linearization: (2.5), Thm 2.3,
  (2.6)–(2.11)), §2.8 (gravitational waves: Props 2.4–2.6, (2.12)–(2.15)).
* [Wald1984], §4.4 (linearized gravity, Lorentz and TT gauges, gravitational radiation);
  the thesis cites pp. 75, 183, 441.
* [Alcubierre2008], pp. 39, 44–45 (linearized Einstein tensor; geodesic deviation in a
  TT plane wave), as cited by the thesis.
* [Stewart1991], p. 24, as cited by the thesis (§2.7).
-/

open Finset
open scoped ContDiff

noncomputable section

namespace Feec.Linearized

/-! ## Basic tensors -/

/-- A covariant 2-tensor `h_ab` in components. -/
abbrev Sym2 := Fin 4 → Fin 4 → ℝ

/-- A 2-jet `D i j a b = ∂_i ∂_j h_ab`. -/
abbrev Jet2 := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- A 3-jet `Y m i j a b = ∂_m ∂_i ∂_j h_ab`. -/
abbrev Jet3 := Fin 4 → Jet2

/-- The Minkowski metric `η_ab` (equal, entrywise, to `η^{ab}`). -/
def etaM (a b : Fin 4) : ℝ := if a = b then η a else 0

/-- Minkowski product `u·v = η^{ab} u_a v_b` of two covectors. -/
def dot (u v : Fin 4 → ℝ) : ℝ := ∑ i, η i * u i * v i

/-- Index raising `v^a = η^{ab} v_b`. -/
def raise (v : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => η i * v i

/-- Trace `h = η^{ab} h_ab`. -/
def tr (h : Sym2) : ℝ := ∑ i, η i * h i i

/-- Trace reversal `h̄_ab = h_ab − ½ η_ab h` (thesis §2.7, `n = 4`). -/
def trRev (h : Sym2) : Sym2 := fun a b => h a b - etaM a b * tr h / 2

/-- (2.5): `tr h̄ = −tr h`.

See [QuennevilleBelair2015, §2.7, (2.5)]; cf. [Wald1984, §4.4]. -/
theorem trRev_trace (h : Sym2) : tr (trRev h) = -tr h := by
  simp only [tr, trRev, etaM, Fin.sum_univ_four, η]; simp; ring

/-- (2.5): trace reversal is an involution in dimension 4, `h = h̄ − ½ η tr h̄`.

Thesis gap: this uses `n = 4` silently (`tr η = 4`); in dimension `n` one has
`tr h̄ = (1 − n/2) tr h` and `h = h̄ − η tr h̄/(n − 2)`, so the formula fails at `n = 2`.

See [QuennevilleBelair2015, §2.7, (2.5)]; cf. [Wald1984, §4.4]. -/
theorem trRev_trRev (h : Sym2) : trRev (trRev h) = h := by
  funext a b
  simp only [trRev, trRev_trace]
  ring

/-- Trace reversal preserves symmetry. -/
lemma trRev_symm {h : Sym2} (hs : ∀ a b, h a b = h b a) (a b : Fin 4) :
    trRev h a b = trRev h b a := by
  simp only [trRev, hs a b, etaM, eq_comm (a := a)]
  split_ifs with hab <;> simp [hab]

/-- Gauge law (2.5): if `h ↦ h + ∂_a ξ_b + ∂_b ξ_a` (`P a b = ∂_a ξ_b`), then
`h̄ ↦ h̄ + ∂_a ξ_b + ∂_b ξ_a − η_ab ∂^c ξ_c`.

See [QuennevilleBelair2015, §2.7, (2.5)]; cf. [Wald1984, §4.4]. -/
theorem trRev_gauge (h P : Sym2) :
    trRev (fun a b => h a b + P a b + P b a) =
      fun a b => trRev h a b + P a b + P b a - etaM a b * ∑ c, η c * P c c := by
  funext a b
  simp only [trRev, tr, Fin.sum_univ_four]
  ring

/-! ## Jets and the linearized Einstein operator (Thm 2.3) -/

/-- Symmetry of the 2-jet of a `C²` symmetric 2-tensor field. -/
structure IsSymJet2 (D : Jet2) : Prop where
  deriv_symm : ∀ i j a b, D i j a b = D j i a b
  tensor_symm : ∀ i j a b, D i j a b = D i j b a

/-- Symmetry of the 3-jet `X i j c b = ∂_i ∂_j ∂_c ξ_b` of a `C³` covector field. -/
structure IsSymJet3ξ (X : Jet2) : Prop where
  symm₁ : ∀ i j c b, X i j c b = X j i c b
  symm₂ : ∀ i j c b, X i j c b = X i c j b

/-- Symmetry of the 3-jet `Y m i j a b = ∂_m ∂_i ∂_j h_ab` of a `C³` symmetric field. -/
structure IsSymJet3 (Y : Jet3) : Prop where
  symm₁ : ∀ m i j a b, Y m i j a b = Y i m j a b
  symm₂ : ∀ m i j a b, Y m i j a b = Y m j i a b
  tensor_symm : ∀ m i j a b, Y m i j a b = Y m i j b a

/-- `□h_ab = ∂^i ∂_i h_ab` on jets. -/
def boxJ (D : Jet2) (a b : Fin 4) : ℝ := ∑ i, η i * D i i a b

/-- Thm 2.3, first form: `H_bd = ∂^c∂_(b h_d)c − ½(□h_bd + ∂_d∂_b h) − ½η_bd(∂^c∂^e h_ec − □h)`,
as a function of the 2-jet `D i j a b = ∂_i ∂_j h_ab`. -/
def Hjet (D : Jet2) (b d : Fin 4) : ℝ :=
  (1/2) * ∑ c, η c * (D c b d c + D c d b c)
  - (1/2) * (boxJ D b d + tr (D d b))
  - etaM b d / 2 * (∑ c, ∑ e, η c * η e * D c e e c - ∑ i, η i * tr (D i i))

/-- 2-jet of the trace-reversed field `h̄` (trace reversal is linear). -/
def barJ (D : Jet2) : Jet2 := fun i j => trRev (D i j)

/-- Thm 2.3, second form: `H_bd = ∂^a∂_(b h̄_d)a − ½(□h̄_bd + η_bd ∂^a∂^e h̄_ea)`,
as a function of the 2-jet `E` of `h̄`. -/
def HbarJet (E : Jet2) (b d : Fin 4) : ℝ :=
  (1/2) * ∑ a, η a * (E a b d a + E a d b a)
  - (1/2) * (boxJ E b d + etaM b d * ∑ a, ∑ e, η a * η e * E a e e a)

/-- `divJ E i b = ∂_i (∂^a h̄_ab)`: first derivatives of the divergence of `h̄`. -/
def divJ (E : Jet2) (i b : Fin 4) : ℝ := ∑ a, η a * E i a a b

/-- Symmetrization of a 2-jet in `(i, j)` and `(a, b)`. -/
def symJ (D : Jet2) : Jet2 := fun i j a b =>
  (D i j a b + D j i a b + D i j b a + D j i b a) / 4

/-- A symmetric jet equals its symmetrization. -/
lemma IsSymJet2.symJ_eq {D : Jet2} (hD : IsSymJet2 D) : symJ D = D := by
  funext i j a b
  have h1 := hD.deriv_symm i j a b
  have h2 := hD.tensor_symm i j a b
  have h3 := hD.tensor_symm j i a b
  simp only [symJ]
  linarith

/-- The jet of `h̄` is again symmetric. -/
lemma IsSymJet2.barJ {D : Jet2} (hD : IsSymJet2 D) : IsSymJet2 (barJ D) where
  deriv_symm i j a b := by simp only [Linearized.barJ, trRev, tr, hD.deriv_symm i j]
  tensor_symm i j a b := trRev_symm (hD.tensor_symm i j) a b

/-- Auxiliary polynomial identity behind `Hjet_eq_bar` (any jet, symmetrized). -/
theorem Hjet_eq_bar_symJ (D : Jet2) (b d : Fin 4) :
    Hjet (symJ D) b d = HbarJet (barJ (symJ D)) b d := by
  simp only [Hjet, HbarJet, barJ, symJ, trRev, boxJ, tr, etaM, Fin.sum_univ_four, η]
  fin_cases b <;> fin_cases d <;> simp <;> ring

/-- **Thesis Thm 2.3** (equivalence of the two forms): for the 2-jet of a symmetric `C²`
field, `H` written in `h` equals `H` written in `h̄`.

Thesis gap: the computation uses `n = 4` (via `h = h̄ − ½ η tr h̄`) and commuting partials
silently; both are explicit here (`Fin 4`, `IsSymJet2`).

See [QuennevilleBelair2015, Thm 2.3]; cf. [Wald1984, §4.4] and
[Alcubierre2008, p. 39] (followed by the thesis). -/
theorem Hjet_eq_bar {D : Jet2} (hD : IsSymJet2 D) (b d : Fin 4) :
    Hjet D b d = HbarJet (barJ D) b d := by
  rw [← hD.symJ_eq]; exact Hjet_eq_bar_symJ D b d

/-- **Thesis Thm 2.3**, operator form `H = E(div h̄) − ½ □h̄ − ½ η div div h̄`:
`H_bd = ½(∂_b L_d + ∂_d L_b) − ½ □h̄_bd − ½ η_bd ∂^a L_a` with `L_b = ∂^a h̄_ab`.
This exact identity is what Prop 2.4(b) rests on.

See [QuennevilleBelair2015, Thm 2.3]; cf. [Wald1984, §4.4]. -/
theorem Hjet_eq_div {D : Jet2} (hD : IsSymJet2 D) (b d : Fin 4) :
    Hjet D b d = (1/2) * (divJ (barJ D) b d + divJ (barJ D) d b)
      - (1/2) * boxJ (barJ D) b d - etaM b d / 2 * ∑ a, η a * divJ (barJ D) a a := by
  rw [Hjet_eq_bar hD]
  have hE := hD.barJ
  have e1 : ∑ a, η a * (barJ D a b d a + barJ D a d b a) =
      divJ (barJ D) b d + divJ (barJ D) d b := by
    simp only [divJ, ← sum_add_distrib, mul_add]
    refine sum_congr rfl fun a _ => ?_
    rw [hE.deriv_symm a b, hE.tensor_symm b a d a, hE.deriv_symm a d, hE.tensor_symm d a b a]
  have e2 : ∑ a, ∑ e, η a * η e * barJ D a e e a = ∑ a, η a * divJ (barJ D) a a := by
    simp only [divJ, mul_sum, mul_assoc]
  simp only [HbarJet, e1, e2]
  ring

/-! ## Gauge invariance and the linearized Bianchi identity -/

/-- 2-jet of the pure-gauge field `h_ab = ∂_a ξ_b + ∂_b ξ_a = 2∂_(a ξ_b)`, from the 3-jet
`X i j c b = ∂_i ∂_j ∂_c ξ_b`. -/
def gaugeJet (X : Jet2) : Jet2 := fun i j a b => X i j a b + X i j b a

/-- Symmetrization of a 3-jet of a covector in its three derivative slots. -/
def sym3 (X : Jet2) : Jet2 := fun i j c b =>
  (X i j c b + X j i c b + X i c j b + X c j i b + X j c i b + X c i j b) / 6

/-- A symmetric 3-jet of a covector equals its symmetrization. -/
lemma IsSymJet3ξ.sym3_eq {X : Jet2} (hX : IsSymJet3ξ X) : sym3 X = X := by
  funext i j c b
  have h1 := hX.symm₁ i j c b
  have h2 := hX.symm₂ i j c b
  have h3 := hX.symm₁ i c j b
  have h4 := hX.symm₂ c i j b
  have h5 := hX.symm₁ c j i b
  simp only [sym3]
  linarith

/-- Auxiliary polynomial identity behind `Hjet_gauge`. -/
theorem Hjet_gauge_sym3 (X : Jet2) (b d : Fin 4) : Hjet (gaugeJet (sym3 X)) b d = 0 := by
  simp only [Hjet, gaugeJet, sym3, boxJ, tr, etaM, Fin.sum_univ_four, η]
  fin_cases b <;> fin_cases d <;> simp <;> ring

/-- **Gauge invariance** (thesis, end of §2.7): `H(2∂_(a ξ_b)) = 0` for every `C³` covector
field `ξ`, at the level of its 3-jet. By linearity `H(h + 2∂_(a ξ_b)) = H(h)`.

Thesis gap: the thesis writes the trace as `4∇·ξ` (it is `2∇·ξ`), its displayed line
equals `2H`, and the `η_bd` group is silently dropped; the conclusion is nevertheless
correct, as proved here.

See [QuennevilleBelair2015, §2.7]; cf. [Wald1984, §4.4]. -/
theorem Hjet_gauge {X : Jet2} (hX : IsSymJet3ξ X) (b d : Fin 4) :
    Hjet (gaugeJet X) b d = 0 := by
  rw [← hX.sym3_eq]; exact Hjet_gauge_sym3 X b d

/-- Symmetrization of a 3-jet of a 2-tensor. -/
def sym3J (Y : Jet3) : Jet3 := fun m i j a b =>
  (Y m i j a b + Y i m j a b + Y m j i a b + Y j i m a b + Y i j m a b + Y j m i a b
   + Y m i j b a + Y i m j b a + Y m j i b a + Y j i m b a + Y i j m b a + Y j m i b a) / 12

/-- A symmetric 3-jet of a 2-tensor equals its symmetrization. -/
lemma IsSymJet3.sym3J_eq {Y : Jet3} (hY : IsSymJet3 Y) : sym3J Y = Y := by
  funext m i j a b
  have t : ∀ m i j, Y m i j b a = Y m i j a b := fun m i j => (hY.tensor_symm m i j a b).symm
  have h1 := hY.symm₁ m i j a b
  have h2 := hY.symm₂ m i j a b
  have h3 := hY.symm₁ m j i a b
  have h4 := hY.symm₂ j m i a b
  have h5 := hY.symm₁ j i m a b
  simp only [sym3J, t]
  linarith

/-- Auxiliary polynomial identity behind `Hjet_bianchi`. -/
theorem Hjet_bianchi_sym (Y : Jet3) (d : Fin 4) : ∑ b, η b * Hjet (sym3J Y b) b d = 0 := by
  simp only [Hjet, sym3J, boxJ, tr, etaM, Fin.sum_univ_four, η]
  fin_cases d <;> simp <;> ring

/-- **Linearized Bianchi identity** `∂^b H_bd = 0` for every `C³` symmetric `h`
(`∂_m H_bd = Hjet (Y m) b d` by linearity of `H`).

Thesis gap: not stated in the thesis; it is the companion of gauge invariance that forces
`∂^b T_bd = 0` for the linearized source and makes the gauge freedom consistent.

See [QuennevilleBelair2015, §2.7] (the identity is not stated there); cf. [Wald1984, §4.4]. -/
theorem Hjet_bianchi {Y : Jet3} (hY : IsSymJet3 Y) (d : Fin 4) :
    ∑ b, η b * Hjet (Y b) b d = 0 := by
  rw [← hY.sym3J_eq]; exact Hjet_bianchi_sym Y d

/-! ## Linearized Riemann tensor (2.6) and `H = Ric − ½ η R` -/

/-- Linearized Riemann tensor (2.6):
`R_abcd = ½(∂_c∂_b h_da − ∂_c∂_a h_bd − ∂_d∂_b h_ca + ∂_d∂_a h_bc)`.

See [QuennevilleBelair2015, (2.6)]; cf. [Wald1984, §4.4], and [Alcubierre2008]. -/
def Rjet (D : Jet2) : T4 (Fin 4) := fun a b c d =>
  (1/2) * (D c b d a - D c a b d - D d b c a + D d a b c)

/-- Linearized Ricci tensor `R_bd = η^{ac} R_abcd`. -/
def RicJ (D : Jet2) (b d : Fin 4) : ℝ := ∑ a, η a * Rjet D a b a d

/-- Linearized scalar curvature `R = η^{bd} R_bd`. -/
def scalJ (D : Jet2) : ℝ := ∑ b, η b * RicJ D b b

/-- The linearized Riemann tensor of a symmetric `C²` field is pair-skew. -/
theorem Rjet_pairSkew {D : Jet2} (hD : IsSymJet2 D) : PairSkew (Rjet D) := by
  intro a b c d
  have := hD.tensor_symm c b d a; have := hD.tensor_symm c a b d
  have := hD.tensor_symm d b c a; have := hD.tensor_symm d a b c
  constructor <;> simp only [Rjet] <;> linarith

/-- The linearized Riemann tensor satisfies the first Bianchi identity. -/
theorem Rjet_bianchi1 {D : Jet2} (hD : IsSymJet2 D) : Bianchi1 (Rjet D) := by
  intro a b c d
  have := hD.deriv_symm c b d a; have := hD.deriv_symm d b c a; have := hD.deriv_symm d c b a
  have := hD.tensor_symm c a b d; have := hD.tensor_symm d a b c; have := hD.tensor_symm b a c d
  simp only [Rjet]
  linarith

/-- **Thesis Thm 2.3** (derivation): the operator `H` of Thm 2.3 is the linearized Einstein
tensor `Ric − ½ η R` built from the linearized Riemann tensor (2.6).

See [QuennevilleBelair2015, Thm 2.3 and (2.6)–(2.8)]; cf. [Alcubierre2008, p. 39]
(followed by the thesis). -/
theorem Hjet_eq_einstein {D : Jet2} (hD : IsSymJet2 D) (b d : Fin 4) :
    Hjet D b d = RicJ D b d - etaM b d / 2 * scalJ D := by
  rw [← hD.symJ_eq]
  simp only [Hjet, RicJ, scalJ, Rjet, symJ, boxJ, tr, etaM, Fin.sum_univ_four, η]
  fin_cases b <;> fin_cases d <;> simp <;> ring

/-! ## Prop 2.4(b) and (2.11): Lorentz gauge -/

/-- Lorentz gauge at the jet level: `∂_i (∂^a h̄_ab) = 0` for all `i, b`. -/
def LorentzJet (D : Jet2) : Prop := ∀ i b, divJ (barJ D) i b = 0

/-- **Thesis Prop 2.4(b), corrected**: in Lorentz gauge `H_bd = −½ □h̄_bd`.

Correction: the thesis states `H = −□h̄`, which contradicts its own (2.11)
(`□h̄ = −16πT` with `H = 8πT`); the factor `½` is restored (see `thesis_prop_2_4b_false`).

See [QuennevilleBelair2015, Prop 2.4(b)]; cf. [Wald1984, §4.4]. -/
theorem Hjet_lorentz {D : Jet2} (hD : IsSymJet2 D) (hL : LorentzJet D) (b d : Fin 4) :
    Hjet D b d = -(1/2) * boxJ (barJ D) b d := by
  have hL' : ∀ i b, divJ (barJ D) i b = 0 := hL
  rw [Hjet_eq_div hD]; simp only [hL', mul_zero, sum_const_zero]; ring

/-- **Thesis (2.11)**: in Lorentz gauge, `H_bd = 8πT_bd ⟺ □h̄_bd = −16πT_bd`.

Correction: the thesis cites the nonexistent "Theorem 2.4" and writes `T_ab` for `T_bd`;
this follows from the corrected Prop 2.4(b).

See [QuennevilleBelair2015, (2.11)]; cf. [Wald1984, §4.4]. -/
theorem lorentz_eq_iff {D : Jet2} (hD : IsSymJet2 D) (hL : LorentzJet D) (T : Sym2)
    (b d : Fin 4) :
    Hjet D b d = 8 * Real.pi * T b d ↔ boxJ (barJ D) b d = -16 * Real.pi * T b d := by
  rw [Hjet_lorentz hD hL]
  constructor <;> intro h <;> linarith

/-! ## Symbol level (`∂_i ↦ k_i`) -/

/-- The symbol jet `D i j a b = k_i k_j h_ab` (the 2-jet of `h f(k·x)` up to `f''`). -/
def symbolJet (k : Fin 4 → ℝ) (h : Sym2) : Jet2 := fun i j a b => k i * k j * h a b

/-- The symbol jet of a symmetric amplitude is symmetric. -/
lemma symbolJet_isSymJet2 (k : Fin 4 → ℝ) {h : Sym2} (hs : ∀ a b, h a b = h b a) :
    IsSymJet2 (symbolJet k h) :=
  ⟨fun i j a b => by simp only [symbolJet]; ring, fun i j a b => by simp only [symbolJet, hs a b]⟩

/-- Symbol of `H` (Thm 2.3, first form, `∂ ↦ k`). -/
def Hsym (k : Fin 4 → ℝ) (h : Sym2) (b d : Fin 4) : ℝ := Hjet (symbolJet k h) b d

/-- Divergence symbol `L_b = k^a h̄_ab`. -/
def divSym (k : Fin 4 → ℝ) (h : Sym2) (b : Fin 4) : ℝ := ∑ a, η a * k a * trRev h a b

/-- Trace reversal commutes with scalars (left). -/
lemma trRev_const_mul (c : ℝ) (h : Sym2) :
    trRev (fun a b => c * h a b) = fun a b => c * trRev h a b := by
  funext a b; simp only [trRev, tr, Fin.sum_univ_four]; ring

/-- Divergence jet of a symbol jet: `∂_i L_b ↦ k_i L_b`. -/
lemma divJ_symbolJet (k : Fin 4 → ℝ) (h : Sym2) (i b : Fin 4) :
    divJ (barJ (symbolJet k h)) i b = k i * divSym k h b := by
  have e : ∀ a, symbolJet k h i a = fun a' b' => (k i * k a) * h a' b' := fun _ => rfl
  simp only [divJ, barJ, e, trRev_const_mul, divSym, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

/-- The thesis' Prop 2.4(b), `H = −□h̄` in Lorentz gauge, is false: a symmetric jet in
Lorentz gauge with `H₁₁ ≠ −□h̄₁₁`.

See [QuennevilleBelair2015, Prop 2.4(b)]. -/
theorem thesis_prop_2_4b_false :
    ∃ D : Jet2, IsSymJet2 D ∧ LorentzJet D ∧ Hjet D 1 1 ≠ -boxJ (barJ D) 1 1 := by
  -- `D = k ⊗ k ⊗ h` with `k = (1,0,0,0)`, `h = e₁ ⊗ e₁ − e₂ ⊗ e₂` (trace-free, `h̄ = h`).
  let h : Sym2 := ![![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, 0]]
  have hs : ∀ a b, h a b = h b a := by intro a b; fin_cases a <;> fin_cases b <;> rfl
  refine ⟨symbolJet ![1, 0, 0, 0] h, symbolJet_isSymJet2 _ hs, fun i b => ?_, ?_⟩
  · rw [divJ_symbolJet]
    fin_cases b <;> simp [divSym, trRev, tr, etaM, h, Fin.sum_univ_four, η]
  · simp only [Hjet, boxJ, barJ, symbolJet, trRev, tr, etaM, h, Fin.sum_univ_four, η]
    norm_num

/-- `H` is linear in the jet (scalar multiples). -/
lemma Hjet_const_mul (c : ℝ) (D : Jet2) (b d : Fin 4) :
    Hjet (fun i j a b => c * D i j a b) b d = c * Hjet D b d := by
  simp only [Hjet, boxJ, tr, etaM, Fin.sum_univ_four]; ring

/-- `□h̄ ↦ (k·k) h̄` at the symbol level. -/
lemma boxJ_symbolJet (k : Fin 4 → ℝ) (h : Sym2) (a b : Fin 4) :
    boxJ (barJ (symbolJet k h)) a b = dot k k * trRev h a b := by
  have e : ∀ i, symbolJet k h i i = fun a' b' => (k i * k i) * h a' b' := fun _ => rfl
  simp only [boxJ, barJ, e, trRev_const_mul, dot, sum_mul]
  exact sum_congr rfl fun _ _ => by ring

/-- **Thesis Thm 2.3** at the symbol level (`∂ ↦ k`, `□ ↦ k·k`):
`H = ½(k_b L_d + k_d L_b) − ½ (k·k) h̄_bd − ½ η_bd k^a L_a`, `L = divSym k h`.

See [QuennevilleBelair2015, Thm 2.3]. -/
theorem Hsym_eq (k : Fin 4 → ℝ) {h : Sym2} (hs : ∀ i j, h i j = h j i) (b d : Fin 4) :
    Hsym k h b d = (1/2) * (k b * divSym k h d + k d * divSym k h b)
      - (1/2) * dot k k * trRev h b d - etaM b d / 2 * ∑ a, η a * k a * divSym k h a := by
  rw [Hsym, Hjet_eq_div (symbolJet_isSymJet2 k hs)]
  simp only [divJ_symbolJet, boxJ_symbolJet, mul_assoc]

/-- Gauge invariance at the symbol level: `H(k ⊗ ξ + ξ ⊗ k) = 0`. -/
theorem Hsym_gauge (k ξ : Fin 4 → ℝ) (b d : Fin 4) :
    Hsym k (fun a c => k a * ξ c + k c * ξ a) b d = 0 := by
  have hX : IsSymJet3ξ (fun i j c b => k i * k j * k c * ξ b) :=
    ⟨fun _ _ _ _ => by ring, fun _ _ _ _ => by ring⟩
  have e : symbolJet k (fun a c => k a * ξ c + k c * ξ a) =
      gaugeJet (fun i j c b => k i * k j * k c * ξ b) := by
    funext i j a b; simp only [symbolJet, gaugeJet]; ring
  rw [Hsym, e]; exact Hjet_gauge hX b d

/-- Linearized Bianchi identity at the symbol level: `k^b H_bd = 0`. -/
theorem Hsym_div (k : Fin 4 → ℝ) {h : Sym2} (hs : ∀ i j, h i j = h j i) (d : Fin 4) :
    ∑ b, η b * k b * Hsym k h b d = 0 := by
  have hY : IsSymJet3 (fun m i j a b => k m * k i * k j * h a b) :=
    ⟨fun _ _ _ _ _ => by ring, fun _ _ _ _ _ => by ring, fun _ _ _ a b => by rw [hs a b]⟩
  have := Hjet_bianchi hY d
  have e : ∀ m, (fun i j a b => k m * k i * k j * h a b) =
      fun i j a b => k m * symbolJet k h i j a b := fun m => by
    funext i j a b; simp only [symbolJet]; ring
  simp only [e, Hjet_const_mul] at this
  rw [← this]; exact sum_congr rfl fun _ _ => by rw [Hsym]; ring

/-- **Thesis Prop 2.4(b), corrected**, symbol level: in Lorentz gauge `k^a h̄_ab = 0`,
`H = −½ (k·k) h̄`, i.e. `H = −½ □h̄` with `□ ↦ k·k`.

See [QuennevilleBelair2015, Prop 2.4(b)]. -/
theorem Hsym_lorentz (k : Fin 4 → ℝ) {h : Sym2} (hs : ∀ i j, h i j = h j i)
    (hL : ∀ b, divSym k h b = 0) (b d : Fin 4) :
    Hsym k h b d = -(1/2) * dot k k * trRev h b d := by
  rw [Hsym_eq k hs]; simp [hL]

/-- Symbol-level Lorentz gauge implies jet-level Lorentz gauge. -/
lemma lorentzJet_symbolJet (k : Fin 4 → ℝ) (h : Sym2) (hL : ∀ b, divSym k h b = 0) :
    LorentzJet (symbolJet k h) := fun i b => by rw [divJ_symbolJet, hL, mul_zero]

/-- **Thesis (2.11)**, symbol level: in Lorentz gauge `k^a h̄_ab = 0`,
`H_bd = 8πT_bd ⟺ (k·k) h̄_bd = −16πT_bd`.

See [QuennevilleBelair2015, (2.11)]. -/
theorem Hsym_lorentz_eq_iff (k : Fin 4 → ℝ) {h : Sym2} (hs : ∀ i j, h i j = h j i)
    (hL : ∀ b, divSym k h b = 0) (T : Sym2) (b d : Fin 4) :
    Hsym k h b d = 8 * Real.pi * T b d ↔ dot k k * trRev h b d = -16 * Real.pi * T b d := by
  rw [Hsym_lorentz k hs hL]
  constructor <;> intro h <;> linarith

/-! ## Prop 2.5 algebra, TT gauge (2.12)–(2.13), Prop 2.6 -/

/-- Covector `k_a = κ(−1, 0, 0, 1)` of the wave vector `k^a = κ(1, 0, 0, 1)`. -/
def kTT (κ : ℝ) : Fin 4 → ℝ := ![-κ, 0, 0, κ]

/-- Observer `u^a = (1, 0, 0, 0)` (contravariant). -/
def uObs : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The TT conditions (2.12) on a constant amplitude: symmetric, `A_ab k^b = 0`,
`A_ab u^b = 0`, `η^{ab} A_ab = 0`.

See [QuennevilleBelair2015, §2.8, (2.12)]; cf. [Wald1984, §4.4]. -/
structure IsTT (κ : ℝ) (A : Sym2) : Prop where
  symm : ∀ a b, A a b = A b a
  lorentz : ∀ a, ∑ b, A a b * raise (kTT κ) b = 0
  transverse : ∀ a, ∑ b, A a b * uObs b = 0
  traceless : tr A = 0

/-- The `+`/`×` amplitude (2.13). -/
def ttAmp (Ap Ax : ℝ) : Sym2 := ![![0, 0, 0, 0], ![0, Ap, Ax, 0], ![0, Ax, -Ap, 0], ![0, 0, 0, 0]]

/-- The `+`/`×` amplitudes (2.13) satisfy the TT conditions (2.12). -/
lemma ttAmp_isTT (κ Ap Ax : ℝ) : IsTT κ (ttAmp Ap Ax) where
  symm a b := by fin_cases a <;> fin_cases b <;> rfl
  lorentz a := by fin_cases a <;> simp [ttAmp, raise, kTT, Fin.sum_univ_four]
  transverse a := by fin_cases a <;> simp [ttAmp, uObs, Fin.sum_univ_four]
  traceless := by simp [tr, ttAmp, Fin.sum_univ_four, η]

/-- **Thesis (2.13)**: for `κ ≠ 0`, the TT conditions (2.12) hold iff `A` has the `+`/`×`
form, with `A₊ = A₁₁`, `Aₓ = A₁₂`.

Thesis gap: `κ ≠ 0` is needed; it is only implicit in the thesis (`k^a = k(1,0,0,1)`, later
divided by `k`).

See [QuennevilleBelair2015, §2.8, (2.12)–(2.13)]; cf. [Wald1984, §4.4]. -/
theorem isTT_iff {κ : ℝ} (hκ : κ ≠ 0) (A : Sym2) : IsTT κ A ↔ A = ttAmp (A 1 1) (A 1 2) := by
  refine ⟨fun h => ?_, fun h => h ▸ ttAmp_isTT κ _ _⟩
  have hu : ∀ a, A a 0 = 0 := fun a => by
    simpa [uObs, Fin.sum_univ_four] using h.transverse a
  have h3 : ∀ a, A a 3 = 0 := fun a => by
    have := h.lorentz a
    simp only [raise, kTT, Fin.sum_univ_four, η] at this
    simp [hu a] at this
    exact this.resolve_right hκ
  have htr := h.traceless
  simp only [tr, Fin.sum_univ_four, η] at htr
  simp at htr
  have h00 := hu 0; have h33 := h3 3
  funext a b
  fin_cases a <;> fin_cases b <;> simp [ttAmp] <;>
    first
    | exact hu _ | exact h3 _
    | (rw [h.symm]; exact hu _) | (rw [h.symm]; exact h3 _)
    | exact h.symm _ _
    | linarith

/-- The linear parametrisation `(A₊, Aₓ) ↦ ttAmp A₊ Aₓ`. -/
def ttLin : (Fin 2 → ℝ) →ₗ[ℝ] Sym2 where
  toFun p := ttAmp (p 0) (p 1)
  map_add' p q := by
    funext a b; fin_cases a <;> fin_cases b <;> simp [ttAmp]; ring
  map_smul' c p := by
    funext a b; fin_cases a <;> fin_cases b <;> simp [ttAmp]

/-- The space of TT amplitudes. -/
def ttSpace : Submodule ℝ Sym2 := LinearMap.range ttLin

/-- **Thesis (2.12)–(2.13)**: for `κ ≠ 0`, `ttSpace` is exactly the set of TT amplitudes.

See [QuennevilleBelair2015, (2.12)–(2.13)]. -/
theorem mem_ttSpace_iff {κ : ℝ} (hκ : κ ≠ 0) (A : Sym2) : A ∈ ttSpace ↔ IsTT κ A := by
  constructor
  · rintro ⟨p, rfl⟩; exact ttAmp_isTT κ _ _
  · intro h; exact ⟨![A 1 1, A 1 2], by simpa [ttLin] using ((isTT_iff hκ A).1 h).symm⟩

/-- **Thesis (2.13)**, "only two degrees of freedom": the TT amplitudes form a
2-dimensional space.

See [QuennevilleBelair2015, (2.13)]; cf. [Wald1984, §4.4]. -/
theorem finrank_ttSpace : Module.finrank ℝ ttSpace = 2 := by
  have hinj : Function.Injective ttLin := by
    intro p q h
    have h1 := congrFun (congrFun h 1) 1
    have h2 := congrFun (congrFun h 1) 2
    simp [ttLin, ttAmp] at h1 h2
    funext i; fin_cases i <;> simp [h1, h2]
  rw [ttSpace, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

/-- The TT amplitudes (2.12) as a submodule (the conditions are linear in `A`). -/
def ttSub (κ : ℝ) : Submodule ℝ Sym2 where
  carrier := {A | IsTT κ A}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => by simp, fun _ => by simp, by simp [tr]⟩
  add_mem' {A B} hA hB :=
    ⟨fun a b => by simp [hA.symm a b, hB.symm a b],
      fun a => by simp [add_mul, sum_add_distrib, hA.lorentz a, hB.lorentz a],
      fun a => by simp [add_mul, sum_add_distrib, hA.transverse a, hB.transverse a],
      by have := hA.traceless; have := hB.traceless; simp_all [tr, mul_add, sum_add_distrib]⟩
  smul_mem' c A hA :=
    ⟨fun a b => by simp [hA.symm a b],
      fun a => by simp [mul_assoc, ← mul_sum, hA.lorentz a],
      fun a => by simp [mul_assoc, ← mul_sum, hA.transverse a],
      by have := hA.traceless; simp only [tr] at this ⊢; simp [mul_left_comm _ c, ← mul_sum, this]⟩

/-- **Thesis (2.13)**, "only two degrees of freedom", stated directly: for `κ ≠ 0` the space
`{A | A satisfies (2.12)}` has dimension `2`.

See [QuennevilleBelair2015, (2.13)]; cf. [Wald1984, §4.4]. -/
theorem finrank_ttSub {κ : ℝ} (hκ : κ ≠ 0) : Module.finrank ℝ (ttSub κ) = 2 := by
  have : ttSub κ = ttSpace := by
    ext A; exact (mem_ttSpace_iff hκ A).symm
  rw [this, finrank_ttSpace]

/-- Amplitude after the gauge change `ξ_a = B_a g(k·x)`, `g' = f`:
`A'_ab = A_ab − k_a B_b − k_b B_a + η_ab (k^c B_c)`. -/
def gaugeAmp (k : Fin 4 → ℝ) (A : Sym2) (B : Fin 4 → ℝ) : Sym2 :=
  fun a b => A a b - k a * B b - k b * B a + etaM a b * dot k B

/-- Corrected gauge vector (covariant): `B₀ = −(A₀₀ + τ/2)/(2κ)`, `B_j = (k_j B₀ − A_j0)/κ`,
`τ = tr A`. -/
def Bcorr (κ : ℝ) (A : Sym2) : Fin 4 → ℝ :=
  let B0 := -(A 0 0 + tr A / 2) / (2 * κ)
  fun j => if j = 0 then B0 else (kTT κ j * B0 - A j 0) / κ

/-- The thesis' gauge vector: `B₀ = (A₀₀ + τ/2)/(2κ)`, `B_j = (A_j0 − k_j B₀)/κ`, read as
**covariant** components `B_a`. (The thesis writes `B^a` but mixes index positions; the
contravariant reading fails too, on the same witness of `thesis_gauge_fails`.) -/
def Bthesis (κ : ℝ) (A : Sym2) : Fin 4 → ℝ :=
  let B0 := (A 0 0 + tr A / 2) / (2 * κ)
  fun j => if j = 0 then B0 else (A j 0 - kTT κ j * B0) / κ

/-- **Thesis Prop 2.6, corrected** (algebraic core): for `κ ≠ 0` and `A` symmetric with
`A_ab k^b = 0`, the gauge vector `Bcorr` produces a TT amplitude, namely
`A' = ttAmp ((A₁₁ − A₂₂)/2) A₁₂`.

Correction: the thesis' derivation uses `η₀₀ = +1`, `k₀ = +κ`, contradicting (−+++); its
`B` has the wrong sign and fails (`thesis_gauge_fails`). The resulting amplitudes
`A'₊ = (A₁₁ − A₂₂)/2`, `A'ₓ = A₁₂` are not recorded in the thesis.

See [QuennevilleBelair2015, Prop 2.6]; cf. [Wald1984, §4.4]. -/
theorem tt_gauge {κ : ℝ} (hκ : κ ≠ 0) {A : Sym2} (hA : ∀ i j, A i j = A j i)
    (hker : ∀ a, ∑ b, A a b * raise (kTT κ) b = 0) :
    gaugeAmp (kTT κ) A (Bcorr κ A) = ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) ∧
      IsTT κ (gaugeAmp (kTT κ) A (Bcorr κ A)) := by
  have hk : ∀ a, A a 0 + A a 3 = 0 := fun a => by
    have := hker a
    simp only [raise, kTT, Fin.sum_univ_four, η] at this
    simp at this
    have : (A a 0 + A a 3) * κ = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hκ
  have e : gaugeAmp (kTT κ) A (Bcorr κ A) = ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) := by
    have k0 := hk 0; have k1 := hk 1; have k2 := hk 2; have k3 := hk 3
    have s01 := hA 0 1; have s02 := hA 0 2; have s03 := hA 0 3; have s12 := hA 1 2
    have s13 := hA 1 3; have s23 := hA 2 3
    funext a b
    fin_cases a <;> fin_cases b <;>
      simp [gaugeAmp, Bcorr, kTT, dot, tr, etaM, ttAmp, Fin.sum_univ_four, η] <;>
      (try field_simp) <;> linarith
  exact ⟨e, e ▸ ttAmp_isTT κ _ _⟩

/-- The thesis' gauge vector `B` (Prop 2.6) does **not** reach TT gauge: for `κ = 1` and an
admissible symmetric `A` with `A k = 0`, the transformed amplitude is not transverse.
`Bthesis` uses the covariant reading of the printed `B`; `thesis_gauge_fails_contra` covers
the contravariant reading.

See [QuennevilleBelair2015, Prop 2.6]. -/
theorem thesis_gauge_fails :
    ∃ κ : ℝ, ∃ A : Sym2, κ ≠ 0 ∧ (∀ i j, A i j = A j i) ∧
      (∀ a, ∑ b, A a b * raise (kTT κ) b = 0) ∧ ¬ IsTT κ (gaugeAmp (kTT κ) A (Bthesis κ A)) := by
  let A : Sym2 := ![![1, 0, 0, -1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![-1, 0, 0, 1]]
  refine ⟨1, A, one_ne_zero, fun i j => by fin_cases i <;> fin_cases j <;> rfl, fun a => by
    fin_cases a <;> simp [A, raise, kTT, Fin.sum_univ_four, η], fun h => ?_⟩
  have := h.transverse 0
  simp [A, gaugeAmp, Bthesis, kTT, dot, tr, etaM, uObs, Fin.sum_univ_four, η] at this
  norm_num at this

/-- The thesis' gauge vector read as **contravariant** components `B^a` (lowered to
`B_a = η_aa B^a`) also fails to reach TT gauge, on the same witness.

See [QuennevilleBelair2015, Prop 2.6]. -/
theorem thesis_gauge_fails_contra :
    ∃ κ : ℝ, ∃ A : Sym2, κ ≠ 0 ∧ (∀ i j, A i j = A j i) ∧
      (∀ a, ∑ b, A a b * raise (kTT κ) b = 0) ∧
        ¬ IsTT κ (gaugeAmp (kTT κ) A (raise (Bthesis κ A))) := by
  let A : Sym2 := ![![1, 0, 0, -1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![-1, 0, 0, 1]]
  refine ⟨1, A, one_ne_zero, fun i j => by fin_cases i <;> fin_cases j <;> rfl, fun a => by
    fin_cases a <;> simp [A, raise, kTT, Fin.sum_univ_four, η], fun h => ?_⟩
  have := h.transverse 0
  simp [A, gaugeAmp, Bthesis, raise, kTT, dot, tr, etaM, uObs, Fin.sum_univ_four, η] at this
  norm_num at this

/-! ## Geodesic deviation in TT gauge (2.15) -/

/-- Relative acceleration `a^i = −R^i_{0j0} v^j` (particles at rest, separation `v^j`). -/
def accelJ (D : Jet2) (v : Fin 4 → ℝ) (i : Fin 4) : ℝ := -∑ j, η i * Rjet D i 0 j 0 * v j

/-- **Thesis (2.15), corrected**: for the 2-jet `k_i k_j A_ab s` of the TT plane wave
(`s = f''(k·x)`), `a¹ = (κ²/2)(A₊v¹ + Aₓv²) s`, `a² = (κ²/2)(Aₓv¹ − A₊v²) s`, `a⁰ = a³ = 0`.

Correction: the thesis gives `−(κ²/2)(…) f(k·x)` (sign, and `f` for `f''`).

See [QuennevilleBelair2015, §2.8, (2.15)]; cf. [Alcubierre2008, pp. 44–45]
(followed by the thesis). -/
theorem tt_accel (κ Ap Ax s : ℝ) (v : Fin 4 → ℝ) :
    let D : Jet2 := fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s
    accelJ D v 1 = κ ^ 2 / 2 * (Ap * v 1 + Ax * v 2) * s ∧
      accelJ D v 2 = κ ^ 2 / 2 * (Ax * v 1 - Ap * v 2) * s ∧
      accelJ D v 0 = 0 ∧ accelJ D v 3 = 0 := by
  simp only [accelJ, Rjet, kTT, ttAmp, Fin.sum_univ_four, η]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> ring

/-! ### Riemann components in TT gauge (2.15a–c) -/

/-- Longitudinal indices `{0, 3}` (time and the propagation direction `x³`). -/
def IsLong (i : Fin 4) : Prop := i = 0 ∨ i = 3

instance (i : Fin 4) : Decidable (IsLong i) := inferInstanceAs (Decidable (_ ∨ _))

/-- The 2-jet of a TT-gauge field depending only on `(x⁰, x³)`: `∂_i ∂_j h_ab = 0` unless
`i, j ∈ {0, 3}`, and `h_ab = 0` unless `a, b ∈ {1, 2}`. -/
structure IsTTJet (D : Jet2) : Prop where
  long_i : ∀ i j a b, ¬ IsLong i → D i j a b = 0
  long_j : ∀ i j a b, ¬ IsLong j → D i j a b = 0
  trans_a : ∀ i j a b, IsLong a → D i j a b = 0
  trans_b : ∀ i j a b, IsLong b → D i j a b = 0

lemma IsTTJet.support {D : Jet2} (hD : IsTTJet D) {i j a b : Fin 4} (h : D i j a b ≠ 0) :
    IsLong i ∧ IsLong j ∧ ¬ IsLong a ∧ ¬ IsLong b := by
  refine ⟨?_, ?_, fun hc => h (hD.trans_a _ _ _ _ hc), fun hc => h (hD.trans_b _ _ _ _ hc)⟩ <;>
    by_contra hc
  exacts [h (hD.long_i _ _ _ _ hc), h (hD.long_j _ _ _ _ hc)]

/-- **Thesis (2.15a–c)**: in TT gauge, for `i, j ∈ {1, 2}`,
`R_{αiβj} = −½ ∂_α ∂_β h_ij` (exactly, at the jet level). The thesis restricts to
`α, β ∈ {0, 3}`; for other `α, β` both sides vanish.

See [QuennevilleBelair2015, (2.15a–c)]; cf. [Alcubierre2008]. -/
theorem Rjet_tt {D : Jet2} (hD : IsSymJet2 D) (hT : IsTTJet D) {α β i j : Fin 4}
    (hi : ¬ IsLong i) (hj : ¬ IsLong j) :
    Rjet D α i β j = -(1/2) * D α β i j := by
  simp only [Rjet]
  rw [hT.long_j _ _ _ _ hi, hT.long_i _ _ _ _ hj, hT.long_i _ _ _ _ hj, hD.deriv_symm β α]
  ring

/-- **Thesis (2.15)**, "the only non-zero components": in TT gauge, `R_abcd = 0` unless each
of the pairs `(a, b)` and `(c, d)` has exactly one longitudinal index. With pair-skewness
(`Rjet_pairSkew`) every non-zero component is thus `±R_{αiβj}`, given by `Rjet_tt`.

See [QuennevilleBelair2015, (2.15a–c)]. -/
theorem Rjet_tt_support {D : Jet2} (hT : IsTTJet D) {a b c d : Fin 4}
    (h : Rjet D a b c d ≠ 0) : (IsLong a ↔ ¬ IsLong b) ∧ (IsLong c ↔ ¬ IsLong d) := by
  by_contra hm
  apply h
  have z : ∀ p q r t, (IsLong p ∧ IsLong q ∧ ¬ IsLong r ∧ ¬ IsLong t →
      (IsLong a ↔ ¬ IsLong b) ∧ (IsLong c ↔ ¬ IsLong d)) → D p q r t = 0 := by
    intro p q r t himp
    by_contra hne
    exact hm (himp (hT.support hne))
  simp only [Rjet]
  rw [z c b d a (by tauto), z c a b d (by tauto), z d b c a (by tauto), z d a b c (by tauto)]
  ring

/-- The 2-jet `k_i k_j A_ab s` of the TT plane wave `ttAmp A₊ Aₓ · f(k·x)` (`s = f''`) is a
symmetric TT jet. -/
lemma ttWaveJet_props (κ Ap Ax s : ℝ) :
    IsSymJet2 (fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s) ∧
      IsTTJet (fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s) := by
  refine ⟨⟨fun i j a b => by ring, fun i j a b => ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · fin_cases a <;> fin_cases b <;> simp [ttAmp]
  · intro i j a b h; fin_cases i <;> simp [IsLong, kTT] at h ⊢
  · intro i j a b h; fin_cases j <;> simp [IsLong, kTT] at h ⊢
  · intro i j a b h; fin_cases a <;> simp [IsLong] at h ⊢ <;> fin_cases b <;> simp [ttAmp]
  · intro i j a b h; fin_cases b <;> simp [IsLong] at h ⊢ <;> fin_cases a <;> simp [ttAmp]

/-- **Thesis (2.15a–c)** for the TT plane wave (cf. the components `C_{αiβj}` in §2.9):
`R_{α1β1} = −½ k_α k_β A₊ s`, `R_{α2β2} = ½ k_α k_β A₊ s`, `R_{α1β2} = −½ k_α k_β Aₓ s`,
with `s = f''(k·x)` (valid for all `α, β`; both sides vanish unless `α, β ∈ {0, 3}`).

See [QuennevilleBelair2015, (2.15a–c)]. -/
theorem Rjet_ttWave (κ Ap Ax s : ℝ) (α β : Fin 4) :
    let D : Jet2 := fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s
    Rjet D α 1 β 1 = -(1/2) * kTT κ α * kTT κ β * Ap * s ∧
      Rjet D α 2 β 2 = (1/2) * kTT κ α * kTT κ β * Ap * s ∧
      Rjet D α 1 β 2 = -(1/2) * kTT κ α * kTT κ β * Ax * s := by
  intro D
  obtain ⟨hS, hT⟩ := ttWaveJet_props κ Ap Ax s
  have n1 : ¬ IsLong 1 := by decide
  have n2 : ¬ IsLong 2 := by decide
  rw [Rjet_tt hS hT n1 n1, Rjet_tt hS hT n2 n2, Rjet_tt hS hT n1 n2]
  simp only [ttAmp]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> ring

/-! ## The coupling constant (§2.4) -/

/-- **Thesis §2.4 constant, corrected**: with `G = 6.67430·10⁻¹¹` and `c = 299792458` (SI),
`8πG/c⁴ ∈ (2.07, 2.09)·10⁻⁴³ s²/(m·kg)`, whereas the thesis' value `≈ 5·10⁻⁴⁴` is
`2πG/c⁴ ∈ (5.1, 5.3)·10⁻⁴⁴`.

See [QuennevilleBelair2015, §2.4]; cf. [Wald1984, Ch. 4]. -/
theorem einstein_const_bounds :
    let G : ℝ := 6.67430e-11
    let c : ℝ := 299792458
    (2.07e-43 < 8 * Real.pi * G / c ^ 4 ∧ 8 * Real.pi * G / c ^ 4 < 2.09e-43) ∧
      (5.1e-44 < 2 * Real.pi * G / c ^ 4 ∧ 2 * Real.pi * G / c ^ 4 < 5.3e-44) := by
  intro G c
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  have hc : (0 : ℝ) < c ^ 4 := by positivity
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    first
    | (rw [lt_div_iff₀ hc]; simp only [G, c]; norm_num; linarith)
    | (rw [div_lt_iff₀ hc]; simp only [G, c]; norm_num; linarith)


/-! ## Function level -/

/-- Coordinate space `ℝ⁴` (contravariant coordinates `x^a`). -/
abbrev E4 := Fin 4 → ℝ

/-! ### Partial derivatives -/

section pd
variable {f g : E4 → ℝ} {x : E4}

/-- Linearity of `pd` (sum). -/
lemma pd_add (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd i (fun y => f y + g y) x = pd i f x + pd i g x := by
  simp [pd, (hf.hasFDerivAt.fun_add hg.hasFDerivAt).fderiv]

/-- Linearity of `pd` (difference). -/
lemma pd_sub (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  simp [pd, (hf.hasFDerivAt.fun_sub hg.hasFDerivAt).fderiv]

/-- Linearity of `pd` (scalar). -/
lemma pd_const_mul (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : Fin 4) :
    pd i (fun y => c * f y) x = c * pd i f x := by
  simp [pd, (hf.hasFDerivAt.const_mul c).fderiv]

/-- Linearity of `pd` (finite sums). -/
lemma pd_sum {F : Fin 4 → E4 → ℝ} (hF : ∀ c, DifferentiableAt ℝ (F c) x) (i : Fin 4) :
    pd i (fun y => ∑ c, F c y) x = ∑ c, pd i (F c) x := by
  have := HasFDerivAt.fun_sum (u := univ) (fun c _ => (hF c).hasFDerivAt)
  simp [pd, this.fderiv]

/-- Second partials via the second Fréchet derivative. -/
lemma pd_pd_eq (hf : ContDiff ℝ 2 f) (i j : Fin 4) (x : E4) :
    pd i (pd j f) x = fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have : pd j f = fun y => fderiv ℝ f y (Pi.single j 1) := rfl
  rw [pd, this, fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simp

/-- Schwarz: partial derivatives of a `C²` function commute. -/
lemma pd_pd_comm (hf : ContDiff ℝ 2 f) (i j : Fin 4) (x : E4) :
    pd i (pd j f) x = pd j (pd i f) x := by
  rw [pd_pd_eq hf, pd_pd_eq hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- Partial derivatives lose one order of smoothness. -/
lemma contDiff_pd {m n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) (i : Fin 4) :
    ContDiff ℝ m (pd i f) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

/-- Partial derivatives of smooth functions are smooth. -/
lemma contDiff_pd_smooth (hf : ContDiff ℝ ∞ f) (i : Fin 4) : ContDiff ℝ ∞ (pd i f) :=
  contDiff_pd hf (by simp) i

/-- Partial derivatives of `C²` functions are differentiable. -/
lemma differentiable_pd (hf : ContDiff ℝ 2 f) (i : Fin 4) : Differentiable ℝ (pd i f) :=
  (contDiff_pd (m := 1) hf (by norm_num) i).differentiable (by norm_num)

end pd

/-! ### Genuine 2-jets and the linearized Einstein tensor of a field -/

/-- The 2-jet `∂_i ∂_j h_ab (x)` of a field `h : ℝ⁴ → Sym2`. -/
def jet2 (h : E4 → Sym2) (x : E4) : Jet2 := fun i j a b => pd i (pd j (fun y => h y a b)) x

/-- The linearized Einstein tensor `H(h)(x)` (Thm 2.3) of a `C²` field. -/
def Hfun (h : E4 → Sym2) (x : E4) (b d : Fin 4) : ℝ := Hjet (jet2 h x) b d

/-- Schwarz: the 2-jet of a `C²` symmetric field satisfies `IsSymJet2`, so all jet-level
identities apply to genuine fields.

See [QuennevilleBelair2015, §2.7] (function-level bridge). -/
theorem jet2_isSymJet2 {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b)
    (hs : ∀ y a b, h y a b = h y b a) (x : E4) : IsSymJet2 (jet2 h x) where
  deriv_symm i j a b := pd_pd_comm (hC a b) i j x
  tensor_symm i j a b := by
    simp only [jet2]; congr 2; funext y; rw [hs]

/-! ### Plane waves -/

/-- The phase `k_c x^c` as a continuous linear functional. -/
def phaseL (k : Fin 4 → ℝ) : E4 →L[ℝ] ℝ := ∑ c, k c • ContinuousLinearMap.proj c

@[simp] lemma phaseL_apply (k : Fin 4 → ℝ) (y : E4) : phaseL k y = ∑ c, k c * y c := by
  simp [phaseL]

/-- Chain rule: `∂_i (c f(k·x)) = c k_i f'(k·x)`. -/
lemma pd_wave {f : ℝ → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (k : Fin 4 → ℝ) (i : Fin 4)
    (x : E4) : pd i (fun y => c * f (phaseL k y)) x = c * k i * deriv f (phaseL k x) := by
  have h1 : HasFDerivAt (fun y => f (phaseL k y)) (deriv f (phaseL k x) • phaseL k) x :=
    (hf _).hasDerivAt.comp_hasFDerivAt x (phaseL k).hasFDerivAt
  rw [pd, (h1.const_mul c).fderiv]
  simp [Pi.single_apply]
  ring

/-- The 2-jet of a plane wave `M_ab f(k·x)`: `∂_i∂_j = k_i k_j M_ab f''(k·x)`. -/
theorem jet2_wave {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (M : Sym2) (k : Fin 4 → ℝ) (x : E4) :
    jet2 (fun y a b => M a b * f (phaseL k y)) x =
      fun i j a b => k i * k j * M a b * deriv (deriv f) (phaseL k x) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv f) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2.differentiable (by norm_num)
  funext i j a b
  have e : pd j (fun y => M a b * f (phaseL k y)) =
      fun y => (M a b * k j) * deriv f (phaseL k y) := by
    funext y; exact pd_wave hd _ k j y
  simp only [jet2, e, pd_wave hd' _ k i x]
  ring

/-- d'Alembertian `□u = η^{ij} ∂_i ∂_j u`. -/
def box (u : E4 → ℝ) (x : E4) : ℝ := ∑ i, η i * pd i (pd i u) x

/-- Divergence `(∂^a h_ab)(x)` of a 2-tensor field. -/
def divF (h : E4 → Sym2) (x : E4) (b : Fin 4) : ℝ := ∑ a, η a * pd a (fun y => h y a b) x

/-- Trace reversal commutes with scalars (right). -/
lemma trRev_mul_const (h : Sym2) (c : ℝ) :
    trRev (fun a b => h a b * c) = fun a b => trRev h a b * c := by
  funext a b; simp only [trRev, tr, Fin.sum_univ_four]; ring

/-- **Thesis Prop 2.5** (plane waves), with genuine derivatives: for a null covector `k`
(`k·k = 0`), a constant symmetric amplitude with `A_ab k^b = 0` and `f ∈ C²`, the field
`h̄_ab = A_ab f(k·x)` satisfies `□h̄ = 0` and the Lorentz gauge `∂^a h̄_ab = 0`, and the
perturbation `h` with trace reversal `h̄` (`h = trRev h̄`, `trRev_trRev`) solves the vacuum
linearized equations `H(h) = 0`.

Convention: `k` is covariant, `k·k = ∑ η i k_i k_i` and the phase is `k_c x^c` (see the
module docstring); the thesis leaves these index placements implicit.

See [QuennevilleBelair2015, Prop 2.5]; cf. [Wald1984, §4.4]. -/
theorem plane_wave {k : Fin 4 → ℝ} (hk : dot k k = 0) {A : Sym2} (hA : ∀ a b, A a b = A b a)
    (hker : ∀ a, ∑ b, A a b * raise k b = 0) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    let hbar : E4 → Sym2 := fun y a b => A a b * f (phaseL k y)
    (∀ x a b, box (fun y => hbar y a b) x = 0) ∧ (∀ x b, divF hbar x b = 0) ∧
      ∀ x b d, Hfun (fun y => trRev (hbar y)) x b d = 0 := by
  intro hbar
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdiv : ∀ b, ∑ a, η a * k a * A a b = 0 := fun b => by
    rw [← hker b]; exact sum_congr rfl fun a _ => by rw [hA, raise]; ring
  refine ⟨fun x a b => ?_, fun x b => ?_, fun x b d => ?_⟩
  · show ∑ i, η i * jet2 hbar x i i a b = 0
    simp only [hbar, jet2_wave hf A k x]
    have : ∑ i, η i * (k i * k i * A a b * deriv (deriv f) (phaseL k x)) =
        dot k k * (A a b * deriv (deriv f) (phaseL k x)) := by
      simp only [dot, sum_mul]; exact sum_congr rfl fun _ _ => by ring
    rw [this, hk, zero_mul]
  · simp only [divF, hbar, pd_wave hd]
    have : ∑ a, η a * (A a b * k a * deriv f (phaseL k x)) =
        (∑ a, η a * k a * A a b) * deriv f (phaseL k x) := by
      rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
    rw [this, hdiv, zero_mul]
  · have e1 : (fun y => trRev (hbar y)) = fun y a b => trRev A a b * f (phaseL k y) := by
      funext y; exact trRev_mul_const A _
    set s := deriv (deriv f) (phaseL k x)
    have e2 : jet2 (fun y => trRev (hbar y)) x = fun i j a b => s * symbolJet k (trRev A) i j a b := by
      rw [e1, jet2_wave hf]; funext i j a b; simp only [symbolJet, s]; ring
    have hL : ∀ b, divSym k (trRev A) b = 0 := fun b => by simp only [divSym, trRev_trRev, hdiv]
    rw [Hfun, e2, Hjet_const_mul, ← Hsym, Hsym_lorentz k (trRev_symm hA) hL, hk]
    ring

/-! ### Prop 2.4(a): existence of the Lorentz gauge -/

/-- **Hypothesis** (classical, absent from Mathlib): the inhomogeneous wave equation `□u = S`
has a smooth solution on ℝ⁴ for every smooth source `S` (e.g. zero Cauchy data and
Duhamel/Kirchhoff). This is the solver Prop 2.4(a) uses without citation.

Cf. [Wald1984, §4.4], where the Lorentz gauge is likewise reached by solving a wave
equation. -/
def WaveSolvable : Prop :=
  ∀ S : E4 → ℝ, ContDiff ℝ ∞ S → ∃ u : E4 → ℝ, ContDiff ℝ ∞ u ∧ ∀ x, box u x = S x

/-- Trace-reversed pure-gauge field `2∂_(a ξ_b) − η_ab ∂^c ξ_c` (cf. (2.5)). -/
def gaugeTR (ξ : Fin 4 → E4 → ℝ) (y : E4) : Sym2 :=
  fun a b => pd a (ξ b) y + pd b (ξ a) y - etaM a b * ∑ c, η c * pd c (ξ c) y

/-- Contraction `η^{aa} η_ab R_a = R_b`. -/
lemma sum_eta_etaM (R : Fin 4 → ℝ) (b : Fin 4) : ∑ a, η a * (etaM a b * R a) = R b := by
  fin_cases b <;> simp [etaM, η]

/-- `∂^a (2∂_(a ξ_b) − η_ab ∂·ξ) = □ξ_b` (uses Schwarz). -/
lemma divF_gaugeTR {ξ : Fin 4 → E4 → ℝ} (hξ : ∀ a, ContDiff ℝ ∞ (ξ a)) (x : E4) (b : Fin 4) :
    divF (gaugeTR ξ) x b = box (ξ b) x := by
  have h2 : ∀ a, ContDiff ℝ 2 (ξ a) := fun a => (hξ a).of_le (by simp)
  have hd : ∀ a c, Differentiable ℝ (pd a (ξ c)) := fun a c => differentiable_pd (h2 c) a
  have hS : Differentiable ℝ (fun y => ∑ c, η c * pd c (ξ c) y) :=
    Differentiable.fun_sum fun c _ => (hd c c).const_mul _
  have e : ∀ a, pd a (fun y => gaugeTR ξ y a b) x = pd a (pd a (ξ b)) x
      + pd a (pd b (ξ a)) x - etaM a b * ∑ c, η c * pd a (pd c (ξ c)) x := by
    intro a
    simp only [gaugeTR]
    rw [pd_sub ((hd a b x).fun_add (hd b a x)) ((hS x).const_mul _), pd_add (hd a b x) (hd b a x),
      pd_const_mul (hS x), pd_sum fun c => (hd c c x).const_mul _]
    simp only [pd_const_mul (hd _ _ x)]
  have eQ : ∑ a, η a * pd a (pd b (ξ a)) x = ∑ c, η c * pd b (pd c (ξ c)) x :=
    sum_congr rfl fun a _ => by rw [pd_pd_comm (h2 a)]
  simp only [divF, e, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]
  rw [sum_eta_etaM (fun a => ∑ c, η c * pd a (pd c (ξ c)) x), eQ, box]
  ring

/-- **Thesis Prop 2.4(a)**: assuming the wave solver `WaveSolvable`, every smooth `h̄` is
gauge-equivalent to one in Lorentz gauge: there is a smooth `ξ` with
`∂^a (h̄ − (2∂_(a ξ_b) − η_ab ∂·ξ))_ab = 0`. By (2.5) (`trRev_gauge`) the new `h̄` is the
trace reversal of `h − 2∂_(a ξ_b)`.

Thesis gap: the existence of `ξ` (solving `□ξ_b = ∂^a h̄_ab` on ℝ⁴) is used without
citation; it is the explicit hypothesis `WaveSolvable`. Also, the thesis says it finds a
diffeomorphism, but only the infinitesimal gauge vector `ξ` is produced (and needed).

See [QuennevilleBelair2015, Prop 2.4(a)]; cf. [Wald1984, §4.4]. -/
theorem exists_lorentz_gauge (hW : WaveSolvable) {hb : E4 → Sym2}
    (hsm : ∀ a b, ContDiff ℝ ∞ fun y => hb y a b) :
    ∃ ξ : Fin 4 → E4 → ℝ, (∀ a, ContDiff ℝ ∞ (ξ a)) ∧
      ∀ x b, divF (fun y => hb y - gaugeTR ξ y) x b = 0 := by
  have hS : ∀ b, ContDiff ℝ ∞ fun x => divF hb x b := fun b =>
    ContDiff.sum fun a _ => contDiff_const.mul (contDiff_pd_smooth (hsm a b) a)
  choose ξ hξ hbox using fun b => hW _ (hS b)
  refine ⟨ξ, hξ, fun x b => ?_⟩
  have h2 : ∀ a, ContDiff ℝ 2 (ξ a) := fun a => (hξ a).of_le (by simp)
  have hd : ∀ a c, Differentiable ℝ (pd a (ξ c)) := fun a c => differentiable_pd (h2 c) a
  have hG : ∀ a, DifferentiableAt ℝ (fun y => gaugeTR ξ y a b) x := fun a => by
    simp only [gaugeTR]
    exact (((hd a b).fun_add (hd b a)).fun_sub
      ((Differentiable.fun_sum fun c _ => (hd c c).const_mul _).const_mul _)) x
  have hH : ∀ a, DifferentiableAt ℝ (fun y => hb y a b) x := fun a =>
    ((hsm a b).differentiable (by simp)) x
  have e : ∀ a, pd a (fun y => (hb y - gaugeTR ξ y) a b) x =
      pd a (fun y => hb y a b) x - pd a (fun y => gaugeTR ξ y a b) x := fun a =>
    pd_sub (hH a) (hG a) a
  have := divF_gaugeTR hξ x b
  simp only [divF] at this ⊢
  simp only [e, mul_sub, sum_sub_distrib, this, hbox]
  simp [divF]

/-! ### Prop 2.6 and (2.15) for genuine plane-wave fields -/

/-- **Thesis Prop 2.6, corrected** (field level): with `ξ_b = B_b g(k·x)`, `g' = f`,
`B = Bcorr κ A`, the gauge-transformed field `h̄ − (2∂_(a ξ_b) − η_ab ∂·ξ)` is the TT plane
wave `ttAmp ((A₁₁ − A₂₂)/2) A₁₂ · f(k·x)`; by `plane_wave` it is again a Lorentz-gauge
vacuum solution.

Remark: the thesis takes `g ∈ C³` with `g' = f`; here only `g` differentiable with
`deriv g = f` is needed. `κ ≠ 0` is explicit (the thesis divides by `k`).

See [QuennevilleBelair2015, Prop 2.6]; cf. [Wald1984, §4.4]. -/
theorem tt_gauge_fun {κ : ℝ} (hκ : κ ≠ 0) {A : Sym2} (hA : ∀ i j, A i j = A j i)
    (hker : ∀ a, ∑ b, A a b * raise (kTT κ) b = 0) {f g : ℝ → ℝ} (hg : Differentiable ℝ g)
    (hgf : deriv g = f) (y : E4) :
    (fun a b => A a b * f (phaseL (kTT κ) y)) -
        gaugeTR (fun b z => Bcorr κ A b * g (phaseL (kTT κ) z)) y =
      fun a b => ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) a b * f (phaseL (kTT κ) y) := by
  rw [← (tt_gauge hκ hA hker).1]
  funext a b
  simp only [Pi.sub_apply, gaugeTR, pd_wave hg, hgf, gaugeAmp, dot]
  have : ∑ c, η c * (Bcorr κ A c * kTT κ c * f (phaseL (kTT κ) y)) =
      (∑ c, η c * kTT κ c * Bcorr κ A c) * f (phaseL (kTT κ) y) := by
    rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

/-- **Thesis (2.15), corrected** (field level): for the TT plane wave
`h_ab = ttAmp A₊ Aₓ · f(k·x)` with `f ∈ C²`, `a¹ = (κ²/2)(A₊v¹ + Aₓv²) f''(k·x)` and
`a² = (κ²/2)(Aₓv¹ − A₊v²) f''(k·x)`.

See [QuennevilleBelair2015, (2.15)]; cf. [Alcubierre2008]. -/
theorem tt_accel_fun (κ Ap Ax : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (v : Fin 4 → ℝ) (x : E4) :
    let D := jet2 (fun y a b => ttAmp Ap Ax a b * f (phaseL (kTT κ) y)) x
    let s := deriv (deriv f) (phaseL (kTT κ) x)
    accelJ D v 1 = κ ^ 2 / 2 * (Ap * v 1 + Ax * v 2) * s ∧
      accelJ D v 2 = κ ^ 2 / 2 * (Ax * v 1 - Ap * v 2) * s ∧
      accelJ D v 0 = 0 ∧ accelJ D v 3 = 0 := by
  intro D s
  have e : D = fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s := jet2_wave hf _ _ x
  rw [e]
  exact tt_accel κ Ap Ax s v

/-- The thesis' accelerations `a¹ = −(κ²/2)(A₊v¹ + Aₓv²) f(k·x)` (after (2.15)) are wrong:
for `f(t) = t²`, `κ = A₊ = v¹ = 1`, `Aₓ = 0` at `x = 0` the true value is `1`, not `0`.

See [QuennevilleBelair2015, §2.8, after (2.15)]. -/
theorem thesis_accel_fails :
    ¬ ∀ (κ Ap Ax : ℝ) (f : ℝ → ℝ), ContDiff ℝ 2 f → ∀ (v : Fin 4 → ℝ) (x : E4),
      accelJ (jet2 (fun y a b => ttAmp Ap Ax a b * f (phaseL (kTT κ) y)) x) v 1 =
        -(κ ^ 2 / 2) * (Ap * v 1 + Ax * v 2) * f (phaseL (kTT κ) x) := by
  intro h
  have hf : ContDiff ℝ 2 (fun t : ℝ => t ^ 2) := contDiff_id.pow 2
  have h1 := h 1 1 0 _ hf ![0, 1, 0, 0] 0
  rw [(tt_accel_fun 1 1 0 hf ![0, 1, 0, 0] 0).1] at h1
  have hd : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t; simp
  simp [hd] at h1

/-! ### Thm 2.3 and Prop 2.4(b) for genuine fields -/

/-- `∂_i` commutes with trace reversal. -/
lemma pd_trRev {F : E4 → Sym2} {x : E4} (hF : ∀ a b, DifferentiableAt ℝ (fun y => F y a b) x)
    (i a b : Fin 4) :
    pd i (fun y => trRev (F y) a b) x = trRev (fun a' b' => pd i (fun y => F y a' b') x) a b := by
  have hT : DifferentiableAt ℝ (fun y => tr (F y)) x := by
    simp only [tr]; exact DifferentiableAt.fun_sum fun j _ => (hF j j).const_mul _
  have e1 : (fun y => trRev (F y) a b) = fun y => F y a b - (etaM a b / 2) * tr (F y) := by
    funext y; simp only [trRev]; ring
  have e2 : pd i (fun y => tr (F y)) x = tr (fun a' b' => pd i (fun y => F y a' b') x) := by
    simp only [tr]; rw [pd_sum fun j => (hF j j).const_mul _]; simp only [pd_const_mul (hF _ _)]
  rw [e1, pd_sub (hF a b) (hT.const_mul _), pd_const_mul hT, e2]
  simp only [trRev]; ring

/-- The 2-jet of `h̄ = trRev h` is the trace reversal of the 2-jet of `h`. -/
theorem jet2_trRev {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b) (x : E4) :
    jet2 (fun y => trRev (h y)) x = barJ (jet2 h x) := by
  funext i j a b
  have e : pd j (fun y => trRev (h y) a b) =
      fun y => trRev (fun a' b' => pd j (fun z => h z a' b') y) a b := by
    funext y
    exact pd_trRev (fun a' b' => ((hC a' b').differentiable (by norm_num)) y) j a b
  simp only [jet2, e]
  exact pd_trRev (fun a' b' => differentiable_pd (hC a' b') j x) i a b

/-- **Thesis Thm 2.3** for a genuine `C²` symmetric field: both forms of `H` agree,
`H(h) = ∂^a∂_(b h̄_d)a − ½(□h̄_bd + η_bd ∂^a∂^e h̄_ea)` with the genuine 2-jet of `h̄`.

See [QuennevilleBelair2015, Thm 2.3]; cf. [Wald1984, §4.4]. -/
theorem Hfun_eq_bar {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b)
    (hs : ∀ y a b, h y a b = h y b a) (x : E4) (b d : Fin 4) :
    Hfun h x b d = HbarJet (jet2 (fun y => trRev (h y)) x) b d := by
  rw [Hfun, Hjet_eq_bar (jet2_isSymJet2 hC hs x), jet2_trRev hC]

/-- **Thesis Prop 2.4(b), corrected**, for a genuine `C²` symmetric field: if `h̄ = trRev h`
is in Lorentz gauge (`∂^a h̄_ab = 0` everywhere), then `H(h) = −½ □h̄`.

Correction: the thesis states `H = −□h̄` (see `thesis_prop_2_4b_false`).

See [QuennevilleBelair2015, Prop 2.4(b)]; cf. [Wald1984, §4.4]. -/
theorem Hfun_lorentz {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b)
    (hs : ∀ y a b, h y a b = h y b a) (hL : ∀ y b, divF (fun z => trRev (h z)) y b = 0)
    (x : E4) (b d : Fin 4) :
    Hfun h x b d = -(1/2) * box (fun y => trRev (h y) b d) x := by
  have hbC : ∀ a b, ContDiff ℝ 2 fun y => trRev (h y) a b := fun a b => by
    have ht : ContDiff ℝ 2 fun y => tr (h y) :=
      ContDiff.sum fun j _ => contDiff_const.mul (hC j j)
    exact (hC a b).sub ((contDiff_const.mul ht).div_const 2)
  have hJ : LorentzJet (jet2 h x) := by
    intro i c
    rw [← jet2_trRev hC]
    have e : pd i (fun y => divF (fun z => trRev (h z)) y c) x = 0 := by
      simp only [hL]; simp [pd]
    rw [← e]; simp only [divF]
    rw [pd_sum fun a => (differentiable_pd (hbC a c) a x).const_mul _]
    simp only [divJ, jet2, pd_const_mul (differentiable_pd (hbC _ c) _ x)]
  rw [Hfun, Hjet_lorentz (jet2_isSymJet2 hC hs x) hJ, ← jet2_trRev hC]
  rfl

/-- **Thesis (2.11)** for genuine fields: in Lorentz gauge,
`H(h) = 8πT ⟺ □h̄ = −16πT`.

See [QuennevilleBelair2015, (2.11)]; cf. [Wald1984, §4.4]. -/
theorem lorentz_fun_iff {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b)
    (hs : ∀ y a b, h y a b = h y b a) (hL : ∀ y b, divF (fun z => trRev (h z)) y b = 0)
    (T : E4 → Sym2) (x : E4) (b d : Fin 4) :
    Hfun h x b d = 8 * Real.pi * T x b d ↔
      box (fun y => trRev (h y) b d) x = -16 * Real.pi * T x b d := by
  rw [Hfun_lorentz hC hs hL]
  constructor <;> intro h <;> linarith

/-! ### Gauge invariance and the linearized Bianchi identity for genuine fields -/

/-- `H` is additive in the jet. -/
lemma Hjet_add (D G : Jet2) (b d : Fin 4) :
    Hjet (fun i j a b => D i j a b + G i j a b) b d = Hjet D b d + Hjet G b d := by
  simp only [Hjet, boxJ, tr, etaM, Fin.sum_univ_four]; ring

/-- **Gauge invariance** (end of §2.7) for genuine fields: `H(h + 2∂_(a ξ_b)) = H(h)` for
`h ∈ C²` and `ξ ∈ C³`.

Thesis gap: the thesis' check has the trace `4∇·ξ` (should be `2∇·ξ`) and displays `2H`;
the needed regularity (`ξ ∈ C³`, to commute third derivatives) is unstated.

See [QuennevilleBelair2015, §2.7]; cf. [Wald1984, §4.4]. -/
theorem Hfun_gauge {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b)
    {ξ : Fin 4 → E4 → ℝ} (hξ : ∀ a, ContDiff ℝ 3 (ξ a)) (x : E4) (b d : Fin 4) :
    Hfun (fun y a b => h y a b + (pd a (ξ b) y + pd b (ξ a) y)) x b d = Hfun h x b d := by
  have hξ2 : ∀ a, ContDiff ℝ 2 (ξ a) := fun a => (hξ a).of_le (by norm_num)
  have hP : ∀ c a, ContDiff ℝ 2 (pd c (ξ a)) := fun c a => contDiff_pd (hξ a) (by norm_num) c
  set X : Jet2 := fun i j c b => pd i (pd j (pd c (ξ b))) x
  have hX : IsSymJet3ξ X := ⟨fun i j c b => pd_pd_comm (hP c b) i j x, fun i j c b => by
      simp only [X]; congr 1; funext y; exact pd_pd_comm (hξ2 b) j c y⟩
  have e : jet2 (fun y a b => h y a b + (pd a (ξ b) y + pd b (ξ a) y)) x =
      fun i j a b => jet2 h x i j a b + gaugeJet X i j a b := by
    funext i j a b
    have hd := fun a b => (hC a b).differentiable (by norm_num)
    have hdP := fun c a => (hP c a).differentiable (by norm_num)
    have e1 : pd j (fun y => h y a b + (pd a (ξ b) y + pd b (ξ a) y)) =
        fun y => pd j (fun z => h z a b) y + (pd j (pd a (ξ b)) y + pd j (pd b (ξ a)) y) := by
      funext y
      rw [pd_add (hd a b y) ((hdP a b y).fun_add (hdP b a y)), pd_add (hdP a b y) (hdP b a y)]
    simp only [jet2, e1, gaugeJet, X]
    rw [pd_add (differentiable_pd (hC a b) j x)
      ((differentiable_pd (hP a b) j x).fun_add (differentiable_pd (hP b a) j x)),
      pd_add (differentiable_pd (hP a b) j x) (differentiable_pd (hP b a) j x)]
  rw [Hfun, e, Hjet_add, Hjet_gauge hX, add_zero, Hfun]

/-- `H` as a continuous linear functional on jets. -/
def HjetL (b d : Fin 4) : Jet2 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Hjet D b d
      map_add' := fun D G => Hjet_add D G b d
      map_smul' := fun c D => Hjet_const_mul c D b d }

/-- Evaluation of a jet at an index, as a continuous linear functional. -/
def evalJ (i j a b : Fin 4) : Jet2 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun D => D i j a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Chain rule for a continuous linear functional of a jet-valued map. -/
lemma pd_clm_comp {J : E4 → Jet2} {x : E4} (hJ : DifferentiableAt ℝ J x) (P : Jet2 →L[ℝ] ℝ)
    (m : Fin 4) : pd m (fun y => P (J y)) x = P (fderiv ℝ J x (Pi.single m 1)) := by
  have := (P.hasFDerivAt.comp x hJ.hasFDerivAt).fderiv
  simp only [pd]
  rw [show (fun y => P (J y)) = ⇑P ∘ J from rfl, this]
  simp

/-- `∂_m` commutes with `H`. -/
lemma pd_Hjet {J : E4 → Jet2} {x : E4} (hJ : DifferentiableAt ℝ J x) (m b d : Fin 4) :
    pd m (fun y => Hjet (J y) b d) x =
      Hjet (fun i j a b => pd m (fun y => J y i j a b) x) b d := by
  have e1 := pd_clm_comp hJ (HjetL b d) m
  have e2 : ∀ i j a b, pd m (fun y => J y i j a b) x = fderiv ℝ J x (Pi.single m 1) i j a b :=
    fun i j a b => by simpa [evalJ] using pd_clm_comp hJ (evalJ i j a b) m
  simp only [e2]
  simpa [HjetL] using e1

/-- **Linearized Bianchi identity** for genuine fields: `∂^b H_bd(h) = 0` for every `C³`
symmetric `h`.

Thesis gap: not in the thesis; it is the consistency condition `∂^b T_bd = 0` behind the
linearized equations (2.10) and their gauge freedom.

See [QuennevilleBelair2015, §2.7]; cf. [Wald1984, §4.4]. -/
theorem Hfun_bianchi {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 3 fun y => h y a b)
    (hs : ∀ y a b, h y a b = h y b a) (x : E4) (d : Fin 4) :
    ∑ b, η b * pd b (fun y => Hfun h y b d) x = 0 := by
  have h2 : ∀ a b, ContDiff ℝ 2 fun y => h y a b := fun a b => (hC a b).of_le (by norm_num)
  have hP : ∀ j a b, ContDiff ℝ 2 (pd j fun y => h y a b) :=
    fun j a b => contDiff_pd (hC a b) (by norm_num) j
  have hJ : DifferentiableAt ℝ (jet2 h) x := by
    refine differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j =>
      differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun b => ?_
    exact differentiable_pd (hP j a b) i x
  set Y : Jet3 := fun m i j a b => pd m (pd i (pd j fun y => h y a b)) x
  have hY : IsSymJet3 Y := ⟨fun m i j a b => pd_pd_comm (hP j a b) m i x,
    fun m i j a b => by simp only [Y]; congr 1; funext y; exact pd_pd_comm (h2 a b) i j y,
    fun m i j a b => by simp only [Y]; congr 3; funext y; rw [hs]⟩
  have e : ∀ b, pd b (fun y => Hfun h y b d) x = Hjet (Y b) b d := fun b => by
    simp only [Hfun]; rw [pd_Hjet hJ]; rfl
  simp only [e]
  exact Hjet_bianchi hY d

end Feec.Linearized
