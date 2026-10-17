module

public import Feec.Foundation.Tensor
public import Feec.Physics.LinearizedGravity.PlaneWave
public import Feec.Counterexamples.LinearizedGravity

/-!
# Ch 2: linearized gravity on Minkowski space (shim)

Strangler shim over `Feec.Physics.LinearizedGravity.{Einstein,Gauge,PlaneWave}`, where the jet
identities (Thm 2.3 in both forms, `H = Ric - ½ g R`, gauge invariance, the linearized Bianchi
identity, Prop 2.4) hold for **every constant metric in every dimension** over any commutative
ring with `2` invertible, and the field identities for every constant metric on `ℝ^ι`. The
declarations below keep their old statements; the old definitions are abbreviations of the new
ones at the Minkowski metric `η4 = diag(-1, 1, 1, 1)`.

## References

* [QuennevilleBelair2015], §2.4, §2.7–§2.8
* [Wald1984], §4.4; [Alcubierre2008]; [Stewart1991]
-/

open Finset
open scoped ContDiff

@[expose] public noncomputable section

namespace Feec.Linearized

/-- A covariant 2-tensor `h_ab` in components. -/
abbrev Sym2 := Fin 4 → Fin 4 → ℝ

/-- A 2-jet `D i j a b = ∂_i ∂_j h_ab`. -/
abbrev Jet2 := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- A 3-jet `Y m i j a b = ∂_m ∂_i ∂_j h_ab`. -/
abbrev Jet3 := Fin 4 → Jet2

/-- The Minkowski metric `η_ab` (equal, entrywise, to `η^{ab}`). -/
abbrev etaM (a b : Fin 4) : ℝ :=
  LinearizedGravity.η4 a b

/-- Minkowski product `u·v = η^{ab} u_a v_b` of two covectors. -/
abbrev dot (u v : Fin 4 → ℝ) : ℝ :=
  LinearizedGravity.dot LinearizedGravity.η4 u v

/-- Index raising `v^a = η^{ab} v_b`. -/
abbrev raise (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  LinearizedGravity.raise v

/-- Trace `h = η^{ab} h_ab`. -/
abbrev tr (h : Sym2) : ℝ :=
  Metric.trace LinearizedGravity.η4 h

/-- Trace reversal `h̄_ab = h_ab − ½ η_ab h` (thesis §2.7, `n = 4`). -/
abbrev trRev (h : Sym2) : Sym2 :=
  Metric.trRev LinearizedGravity.η4 LinearizedGravity.η4 h

/-- Old-form evaluation of the trace (bridge to `Feec.LinearizedGravity.trace_η4`). -/
theorem tr_apply' (h : Sym2) : tr h = ∑ i, η i * h i i := LinearizedGravity.trace_η4 h

/-- Old-form evaluation of the trace reversal (bridge to
`Feec.LinearizedGravity.trRev_η4_apply`). -/
theorem trRev_apply' (h : Sym2) (a b : Fin 4) :
    trRev h a b = h a b - etaM a b * (∑ i, η i * h i i) / 2 :=
  LinearizedGravity.trRev_η4_apply h a b

/-- (2.5): `tr h̄ = −tr h`.

See [QuennevilleBelair2015, §2.7, (2.5)]; cf. [Wald1984, §4.4]. -/
theorem trRev_trace (h : Sym2) : tr (trRev h) = -tr h :=
  by
  have := Metric.trace_trRev (g := LinearizedGravity.η4) (gi := LinearizedGravity.η4) LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self h
  rw [Fintype.card_fin, invOf_eq_inv] at this
  exact this.trans (by norm_num)

/-- (2.5): trace reversal is an involution in dimension 4, `h = h̄ − ½ η tr h̄`.

Thesis gap: this uses `n = 4` silently (`tr η = 4`); in dimension `n` one has
`tr h̄ = (1 − n/2) tr h` and `h = h̄ − η tr h̄/(n − 2)`, so the formula fails at `n = 2`.

See [QuennevilleBelair2015, §2.7, (2.5)]; cf. [Wald1984, §4.4]. -/
theorem trRev_trRev (h : Sym2) : trRev (trRev h) = h :=
  Metric.trRev_trRev LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self (by simp) h

/-- Trace reversal preserves symmetry. -/
lemma trRev_symm {h : Sym2} (hs : ∀ a b, h a b = h b a) (a b : Fin 4) :
    trRev h a b = trRev h b a :=
  by
  have hh : Matrix.transpose (h : Matrix (Fin 4) (Fin 4) ℝ) = h := by ext i j; exact hs j i
  have := congrFun (congrFun (Metric.transpose_trRev (gi := LinearizedGravity.η4) LinearizedGravity.η4_isSymm hh) b) a
  simpa using this

/-- Gauge law (2.5): if `h ↦ h + ∂_a ξ_b + ∂_b ξ_a` (`P a b = ∂_a ξ_b`), then
`h̄ ↦ h̄ + ∂_a ξ_b + ∂_b ξ_a − η_ab ∂^c ξ_c`.

See [QuennevilleBelair2015, §2.7, (2.5)]; cf. [Wald1984, §4.4]. -/
theorem trRev_gauge (h P : Sym2) :
    trRev (fun a b => h a b + P a b + P b a) =
      fun a b => trRev h a b + P a b + P b a - etaM a b * ∑ c, η c * P c c :=
  by
  funext a b; simp only [trRev_apply', Fin.sum_univ_four]; ring

/-- Symmetry of the 2-jet of a `C²` symmetric 2-tensor field. -/
abbrev IsSymJet2 (D : Jet2) : Prop :=
  LinearizedGravity.IsSymJet2 D

/-- Symmetry of the 3-jet `X i j c b = ∂_i ∂_j ∂_c ξ_b` of a `C³` covector field. -/
abbrev IsSymJet3ξ (X : Jet2) : Prop :=
  LinearizedGravity.IsSymJet3ξ X

/-- Symmetry of the 3-jet `Y m i j a b = ∂_m ∂_i ∂_j h_ab` of a `C³` symmetric field. -/
abbrev IsSymJet3 (Y : Jet3) : Prop :=
  LinearizedGravity.IsSymJet3 Y

/-- `□h_ab = ∂^i ∂_i h_ab` on jets. -/
abbrev boxJ (D : Jet2) (a b : Fin 4) : ℝ :=
  LinearizedGravity.boxJ LinearizedGravity.η4 D a b

/-- Thm 2.3, first form: `H_bd = ∂^c∂_(b h_d)c − ½(□h_bd + ∂_d∂_b h) − ½η_bd(∂^c∂^e h_ec − □h)`,
as a function of the 2-jet `D i j a b = ∂_i ∂_j h_ab`. -/
abbrev Hjet (D : Jet2) (b d : Fin 4) : ℝ :=
  LinearizedGravity.Hjet LinearizedGravity.η4 LinearizedGravity.η4 D b d

/-- 2-jet of the trace-reversed field `h̄` (trace reversal is linear). -/
abbrev barJ (D : Jet2) : Jet2 :=
  LinearizedGravity.barJ LinearizedGravity.η4 LinearizedGravity.η4 D

/-- Thm 2.3, second form: `H_bd = ∂^a∂_(b h̄_d)a − ½(□h̄_bd + η_bd ∂^a∂^e h̄_ea)`,
as a function of the 2-jet `E` of `h̄`. -/
abbrev HbarJet (E : Jet2) (b d : Fin 4) : ℝ :=
  LinearizedGravity.HbarJet LinearizedGravity.η4 LinearizedGravity.η4 E b d

/-- `divJ E i b = ∂_i (∂^a h̄_ab)`: first derivatives of the divergence of `h̄`. -/
abbrev divJ (E : Jet2) (i b : Fin 4) : ℝ :=
  LinearizedGravity.divJ LinearizedGravity.η4 E i b

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
lemma IsSymJet2.barJ {D : Jet2} (hD : IsSymJet2 D) : IsSymJet2 (barJ D) :=
  LinearizedGravity.IsSymJet2.barJ LinearizedGravity.η4_isSymm hD

/-- Auxiliary polynomial identity behind `Hjet_eq_bar` (any jet, symmetrized). -/
theorem Hjet_eq_bar_symJ (D : Jet2) (b d : Fin 4) :
    Hjet (symJ D) b d = HbarJet (barJ (symJ D)) b d :=
  LinearizedGravity.Hjet_eq_bar LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self ⟨fun i j a b => by simp only [symJ]; ring, fun i j a b => by simp only [symJ]; ring⟩ b d

/-- **Thesis Thm 2.3** (equivalence of the two forms): for the 2-jet of a symmetric `C²`
field, `H` written in `h` equals `H` written in `h̄`.

Thesis gap: the computation uses `n = 4` (via `h = h̄ − ½ η tr h̄`) and commuting partials
silently; both are explicit here (`Fin 4`, `IsSymJet2`).

See [QuennevilleBelair2015, Thm 2.3]; cf. [Wald1984, §4.4] and
[Alcubierre2008, p. 39] (followed by the thesis). -/
theorem Hjet_eq_bar {D : Jet2} (hD : IsSymJet2 D) (b d : Fin 4) :
    Hjet D b d = HbarJet (barJ D) b d :=
  LinearizedGravity.Hjet_eq_bar LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self hD b d

/-- **Thesis Thm 2.3**, operator form `H = E(div h̄) − ½ □h̄ − ½ η div div h̄`:
`H_bd = ½(∂_b L_d + ∂_d L_b) − ½ □h̄_bd − ½ η_bd ∂^a L_a` with `L_b = ∂^a h̄_ab`.
This exact identity is what Prop 2.4(b) rests on.

See [QuennevilleBelair2015, Thm 2.3]; cf. [Wald1984, §4.4]. -/
theorem Hjet_eq_div {D : Jet2} (hD : IsSymJet2 D) (b d : Fin 4) :
    Hjet D b d = (1/2) * (divJ (barJ D) b d + divJ (barJ D) d b)
      - (1/2) * boxJ (barJ D) b d - etaM b d / 2 * ∑ a, η a * divJ (barJ D) a a :=
  by
  have := LinearizedGravity.Hjet_eq_div LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self hD b d
  rw [LinearizedGravity.sum_η4 (fun a a' => LinearizedGravity.divJ LinearizedGravity.η4 (LinearizedGravity.barJ LinearizedGravity.η4 LinearizedGravity.η4 D) a' a)] at this
  simp only [Hjet, divJ, barJ, boxJ, etaM, invOf_eq_inv] at this ⊢
  rw [this]; simp only [η, Metric.minkowski4]; ring

/-- 2-jet of the pure-gauge field `h_ab = ∂_a ξ_b + ∂_b ξ_a = 2∂_(a ξ_b)`, from the 3-jet
`X i j c b = ∂_i ∂_j ∂_c ξ_b`. -/
abbrev gaugeJet (X : Jet2) : Jet2 :=
  LinearizedGravity.gaugeJet X

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
theorem Hjet_gauge_sym3 (X : Jet2) (b d : Fin 4) : Hjet (gaugeJet (sym3 X)) b d = 0 :=
  LinearizedGravity.Hjet_gauge LinearizedGravity.η4_isSymm ⟨fun i j c b => by simp only [sym3]; ring, fun i j c b => by simp only [sym3]; ring⟩ b d

/-- **Gauge invariance** (thesis, end of §2.7): `H(2∂_(a ξ_b)) = 0` for every `C³` covector
field `ξ`, at the level of its 3-jet. By linearity `H(h + 2∂_(a ξ_b)) = H(h)`.

Thesis gap: the thesis writes the trace as `4∇·ξ` (it is `2∇·ξ`), its displayed line
equals `2H`, and the `η_bd` group is silently dropped; the conclusion is nevertheless
correct, as proved here.

See [QuennevilleBelair2015, §2.7]; cf. [Wald1984, §4.4]. -/
theorem Hjet_gauge {X : Jet2} (hX : IsSymJet3ξ X) (b d : Fin 4) :
    Hjet (gaugeJet X) b d = 0 :=
  LinearizedGravity.Hjet_gauge LinearizedGravity.η4_isSymm hX b d

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
theorem Hjet_bianchi_sym (Y : Jet3) (d : Fin 4) : ∑ b, η b * Hjet (sym3J Y b) b d = 0 :=
  by
  have hY : LinearizedGravity.IsSymJet3 (sym3J Y) := ⟨fun _ _ _ _ _ => by simp only [sym3J]; ring,
    fun _ _ _ _ _ => by simp only [sym3J]; ring, fun _ _ _ _ _ => by simp only [sym3J]; ring⟩
  have := LinearizedGravity.Hjet_bianchi LinearizedGravity.η4_isSymm LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self hY d
  rw [LinearizedGravity.sum_η4 (fun b b' => LinearizedGravity.Hjet LinearizedGravity.η4 LinearizedGravity.η4 (sym3J Y b') b d)] at this
  simpa [Hjet, η, Metric.minkowski4] using this

/-- **Linearized Bianchi identity** `∂^b H_bd = 0` for every `C³` symmetric `h`
(`∂_m H_bd = Hjet (Y m) b d` by linearity of `H`).

Thesis gap: not stated in the thesis; it is the companion of gauge invariance that forces
`∂^b T_bd = 0` for the linearized source and makes the gauge freedom consistent.

See [QuennevilleBelair2015, §2.7] (the identity is not stated there); cf. [Wald1984, §4.4]. -/
theorem Hjet_bianchi {Y : Jet3} (hY : IsSymJet3 Y) (d : Fin 4) :
    ∑ b, η b * Hjet (Y b) b d = 0 :=
  by
  have := LinearizedGravity.Hjet_bianchi LinearizedGravity.η4_isSymm LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self hY d
  rw [LinearizedGravity.sum_η4 (fun b b' => LinearizedGravity.Hjet LinearizedGravity.η4 LinearizedGravity.η4 (Y b') b d)] at this
  simpa [Hjet, η, Metric.minkowski4] using this

/-- Linearized Riemann tensor (2.6):
`R_abcd = ½(∂_c∂_b h_da − ∂_c∂_a h_bd − ∂_d∂_b h_ca + ∂_d∂_a h_bc)`.

See [QuennevilleBelair2015, (2.6)]; cf. [Wald1984, §4.4], and [Alcubierre2008]. -/
abbrev Rjet (D : Jet2) : T4 (Fin 4) :=
  LinearizedGravity.Rjet D

/-- Linearized Ricci tensor `R_bd = η^{ac} R_abcd`. -/
abbrev RicJ (D : Jet2) (b d : Fin 4) : ℝ :=
  LinearizedGravity.RicJ LinearizedGravity.η4 D b d

/-- Linearized scalar curvature `R = η^{bd} R_bd`. -/
abbrev scalJ (D : Jet2) : ℝ :=
  LinearizedGravity.scalJ LinearizedGravity.η4 D

/-- The linearized Riemann tensor of a symmetric `C²` field is pair-skew. -/
theorem Rjet_pairSkew {D : Jet2} (hD : IsSymJet2 D) : PairSkew (Rjet D) :=
  LinearizedGravity.Rjet_pairSkew hD

/-- The linearized Riemann tensor satisfies the first Bianchi identity. -/
theorem Rjet_bianchi1 {D : Jet2} (hD : IsSymJet2 D) : Bianchi1 (Rjet D) :=
  LinearizedGravity.Rjet_bianchi1 hD

/-- **Thesis Thm 2.3** (derivation): the operator `H` of Thm 2.3 is the linearized Einstein
tensor `Ric − ½ η R` built from the linearized Riemann tensor (2.6).

See [QuennevilleBelair2015, Thm 2.3 and (2.6)–(2.8)]; cf. [Alcubierre2008, p. 39]
(followed by the thesis). -/
theorem Hjet_eq_einstein {D : Jet2} (hD : IsSymJet2 D) (b d : Fin 4) :
    Hjet D b d = RicJ D b d - etaM b d / 2 * scalJ D :=
  by
  rw [Hjet, LinearizedGravity.Hjet_eq_einstein LinearizedGravity.η4_isSymm hD b d, invOf_eq_inv]
  simp only [RicJ, scalJ, etaM]; ring

/-- Lorentz gauge at the jet level: `∂_i (∂^a h̄_ab) = 0` for all `i, b`. -/
abbrev LorentzJet (D : Jet2) : Prop :=
  LinearizedGravity.LorentzJet LinearizedGravity.η4 LinearizedGravity.η4 D

/-- **Thesis Prop 2.4(b), corrected**: in Lorentz gauge `H_bd = −½ □h̄_bd`.

Correction: the thesis states `H = −□h̄`, which contradicts its own (2.11)
(`□h̄ = −16πT` with `H = 8πT`); the factor `½` is restored (see `thesis_prop_2_4b_false`).

See [QuennevilleBelair2015, Prop 2.4(b)]; cf. [Wald1984, §4.4]. -/
theorem Hjet_lorentz {D : Jet2} (hD : IsSymJet2 D) (hL : LorentzJet D) (b d : Fin 4) :
    Hjet D b d = -(1/2) * boxJ (barJ D) b d :=
  by
  rw [Hjet, LinearizedGravity.Hjet_lorentz LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self hD hL, invOf_eq_inv]; norm_num

/-- **Thesis (2.11)**: in Lorentz gauge, `H_bd = 8πT_bd ⟺ □h̄_bd = −16πT_bd`.

Correction: the thesis cites the nonexistent "Theorem 2.4" and writes `T_ab` for `T_bd`;
this follows from the corrected Prop 2.4(b).

See [QuennevilleBelair2015, (2.11)]; cf. [Wald1984, §4.4]. -/
theorem lorentz_eq_iff {D : Jet2} (hD : IsSymJet2 D) (hL : LorentzJet D) (T : Sym2)
    (b d : Fin 4) :
    Hjet D b d = 8 * Real.pi * T b d ↔ boxJ (barJ D) b d = -16 * Real.pi * T b d :=
  by
  have := LinearizedGravity.Hjet_lorentz_eq_iff LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self hD hL (8 * Real.pi) T b d
  constructor
  · intro h; have := this.1 h; linarith
  · intro h; exact this.2 (by linarith)

/-- The symbol jet `D i j a b = k_i k_j h_ab` (the 2-jet of `h f(k·x)` up to `f''`). -/
abbrev symbolJet (k : Fin 4 → ℝ) (h : Sym2) : Jet2 :=
  LinearizedGravity.symbolJet k h

/-- The symbol jet of a symmetric amplitude is symmetric. -/
lemma symbolJet_isSymJet2 (k : Fin 4 → ℝ) {h : Sym2} (hs : ∀ a b, h a b = h b a) :
    IsSymJet2 (symbolJet k h) :=
  LinearizedGravity.symbolJet_isSymJet2 k (by ext a b; exact hs b a)

/-- Symbol of `H` (Thm 2.3, first form, `∂ ↦ k`). -/
abbrev Hsym (k : Fin 4 → ℝ) (h : Sym2) (b d : Fin 4) : ℝ :=
  LinearizedGravity.Hsym LinearizedGravity.η4 LinearizedGravity.η4 k h b d

/-- Divergence symbol `L_b = k^a h̄_ab`. -/
abbrev divSym (k : Fin 4 → ℝ) (h : Sym2) (b : Fin 4) : ℝ :=
  LinearizedGravity.divSym LinearizedGravity.η4 LinearizedGravity.η4 k h b

/-- Trace reversal commutes with scalars (left). -/
lemma trRev_const_mul (c : ℝ) (h : Sym2) :
    trRev (fun a b => c * h a b) = fun a b => c * trRev h a b :=
  by
  funext a b; simp only [trRev_apply', Fin.sum_univ_four]; ring

/-- Divergence jet of a symbol jet: `∂_i L_b ↦ k_i L_b`. -/
lemma divJ_symbolJet (k : Fin 4 → ℝ) (h : Sym2) (i b : Fin 4) :
    divJ (barJ (symbolJet k h)) i b = k i * divSym k h b :=
  LinearizedGravity.divJ_symbolJet k h i b

/-- The thesis' Prop 2.4(b), `H = −□h̄` in Lorentz gauge, is false: a symmetric jet in
Lorentz gauge with `H₁₁ ≠ −□h̄₁₁`.

See [QuennevilleBelair2015, Prop 2.4(b)]. -/
theorem thesis_prop_2_4b_false :
    ∃ D : Jet2, IsSymJet2 D ∧ LorentzJet D ∧ Hjet D 1 1 ≠ -boxJ (barJ D) 1 1 :=
  Counterexamples.LinearizedGravity.not_Hjet_eq_neg_boxJ

/-- `H` is linear in the jet (scalar multiples). -/
lemma Hjet_const_mul (c : ℝ) (D : Jet2) (b d : Fin 4) :
    Hjet (fun i j a b => c * D i j a b) b d = c * Hjet D b d :=
  LinearizedGravity.Hjet_smul c D b d

/-- `□h̄ ↦ (k·k) h̄` at the symbol level. -/
lemma boxJ_symbolJet (k : Fin 4 → ℝ) (h : Sym2) (a b : Fin 4) :
    boxJ (barJ (symbolJet k h)) a b = dot k k * trRev h a b :=
  LinearizedGravity.boxJ_symbolJet k h a b

/-- **Thesis Thm 2.3** at the symbol level (`∂ ↦ k`, `□ ↦ k·k`):
`H = ½(k_b L_d + k_d L_b) − ½ (k·k) h̄_bd − ½ η_bd k^a L_a`, `L = divSym k h`.

See [QuennevilleBelair2015, Thm 2.3]. -/
theorem Hsym_eq (k : Fin 4 → ℝ) {h : Sym2} (hs : ∀ i j, h i j = h j i) (b d : Fin 4) :
    Hsym k h b d = (1/2) * (k b * divSym k h d + k d * divSym k h b)
      - (1/2) * dot k k * trRev h b d - etaM b d / 2 * ∑ a, η a * k a * divSym k h a :=
  by
  have := LinearizedGravity.Hsym_eq LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self k (h := h) (by ext a c; exact hs c a) b d
  simp only [mul_assoc] at this
  rw [LinearizedGravity.sum_η4 (fun a a' => k a' * LinearizedGravity.divSym LinearizedGravity.η4 LinearizedGravity.η4 k h a)] at this
  rw [Hsym, this, invOf_eq_inv]
  simp only [etaM, η, Metric.minkowski4, dot, divSym, trRev]; ring

/-- Gauge invariance at the symbol level: `H(k ⊗ ξ + ξ ⊗ k) = 0`. -/
theorem Hsym_gauge (k ξ : Fin 4 → ℝ) (b d : Fin 4) :
    Hsym k (fun a c => k a * ξ c + k c * ξ a) b d = 0 :=
  LinearizedGravity.Hsym_gauge LinearizedGravity.η4_isSymm k ξ b d

/-- Linearized Bianchi identity at the symbol level: `k^b H_bd = 0`. -/
theorem Hsym_div (k : Fin 4 → ℝ) {h : Sym2} (hs : ∀ i j, h i j = h j i) (d : Fin 4) :
    ∑ b, η b * k b * Hsym k h b d = 0 :=
  by
  have := LinearizedGravity.Hsym_div LinearizedGravity.η4_isSymm LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self k (h := h) (by ext a c; exact hs c a) d
  simp only [mul_assoc] at this
  rw [LinearizedGravity.sum_η4 (fun b b' => k b' * LinearizedGravity.Hsym LinearizedGravity.η4 LinearizedGravity.η4 k h b d)] at this
  simpa [Hsym, η, Metric.minkowski4, mul_assoc] using this

/-- **Thesis Prop 2.4(b), corrected**, symbol level: in Lorentz gauge `k^a h̄_ab = 0`,
`H = −½ (k·k) h̄`, i.e. `H = −½ □h̄` with `□ ↦ k·k`.

See [QuennevilleBelair2015, Prop 2.4(b)]. -/
theorem Hsym_lorentz (k : Fin 4 → ℝ) {h : Sym2} (hs : ∀ i j, h i j = h j i)
    (hL : ∀ b, divSym k h b = 0) (b d : Fin 4) :
    Hsym k h b d = -(1/2) * dot k k * trRev h b d :=
  by
  rw [Hsym, LinearizedGravity.Hsym_lorentz LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self k (by ext a b; exact hs b a) hL, invOf_eq_inv]; norm_num

/-- Symbol-level Lorentz gauge implies jet-level Lorentz gauge. -/
lemma lorentzJet_symbolJet (k : Fin 4 → ℝ) (h : Sym2) (hL : ∀ b, divSym k h b = 0) :
    LorentzJet (symbolJet k h) :=
  LinearizedGravity.lorentzJet_symbolJet k h hL

/-- **Thesis (2.11)**, symbol level: in Lorentz gauge `k^a h̄_ab = 0`,
`H_bd = 8πT_bd ⟺ (k·k) h̄_bd = −16πT_bd`.

See [QuennevilleBelair2015, (2.11)]. -/
theorem Hsym_lorentz_eq_iff (k : Fin 4 → ℝ) {h : Sym2} (hs : ∀ i j, h i j = h j i)
    (hL : ∀ b, divSym k h b = 0) (T : Sym2) (b d : Fin 4) :
    Hsym k h b d = 8 * Real.pi * T b d ↔ dot k k * trRev h b d = -16 * Real.pi * T b d :=
  by
  rw [Hsym_lorentz k hs hL]
  constructor <;> intro h <;> linarith

/-- Covector `k_a = κ(−1, 0, 0, 1)` of the wave vector `k^a = κ(1, 0, 0, 1)`. -/
abbrev kTT (κ : ℝ) : Fin 4 → ℝ :=
  LinearizedGravity.kTT κ

/-- Observer `u^a = (1, 0, 0, 0)` (contravariant). -/
abbrev uObs : Fin 4 → ℝ :=
  LinearizedGravity.uObs

/-- The TT conditions (2.12) on a constant amplitude: symmetric, `A_ab k^b = 0`,
`A_ab u^b = 0`, `η^{ab} A_ab = 0`.

See [QuennevilleBelair2015, §2.8, (2.12)]; cf. [Wald1984, §4.4]. -/
abbrev IsTT (κ : ℝ) (A : Sym2) : Prop :=
  LinearizedGravity.IsTT κ A

/-- The `+`/`×` amplitude (2.13). -/
abbrev ttAmp (Ap Ax : ℝ) : Sym2 :=
  LinearizedGravity.ttAmp Ap Ax

/-- The `+`/`×` amplitudes (2.13) satisfy the TT conditions (2.12). -/
lemma ttAmp_isTT (κ Ap Ax : ℝ) : IsTT κ (ttAmp Ap Ax) :=
  LinearizedGravity.ttAmp_isTT κ Ap Ax

/-- **Thesis (2.13)**: for `κ ≠ 0`, the TT conditions (2.12) hold iff `A` has the `+`/`×`
form, with `A₊ = A₁₁`, `Aₓ = A₁₂`.

Thesis gap: `κ ≠ 0` is needed; it is only implicit in the thesis (`k^a = k(1,0,0,1)`, later
divided by `k`).

See [QuennevilleBelair2015, §2.8, (2.12)–(2.13)]; cf. [Wald1984, §4.4]. -/
theorem isTT_iff {κ : ℝ} (hκ : κ ≠ 0) (A : Sym2) : IsTT κ A ↔ A = ttAmp (A 1 1) (A 1 2) :=
  LinearizedGravity.isTT_iff hκ A

/-- The linear parametrisation `(A₊, Aₓ) ↦ ttAmp A₊ Aₓ`. -/
abbrev ttLin : (Fin 2 → ℝ) →ₗ[ℝ] Sym2 :=
  LinearizedGravity.ttLin

/-- The space of TT amplitudes. -/
abbrev ttSpace : Submodule ℝ Sym2 :=
  LinearizedGravity.ttSpace

/-- **Thesis (2.12)–(2.13)**: for `κ ≠ 0`, `ttSpace` is exactly the set of TT amplitudes.

See [QuennevilleBelair2015, (2.12)–(2.13)]. -/
theorem mem_ttSpace_iff {κ : ℝ} (hκ : κ ≠ 0) (A : Sym2) : A ∈ ttSpace ↔ IsTT κ A :=
  LinearizedGravity.mem_ttSpace_iff hκ A

/-- **Thesis (2.13)**, "only two degrees of freedom": the TT amplitudes form a
2-dimensional space.

See [QuennevilleBelair2015, (2.13)]; cf. [Wald1984, §4.4]. -/
theorem finrank_ttSpace : Module.finrank ℝ ttSpace = 2 :=
  LinearizedGravity.finrank_ttSpace

/-- The TT amplitudes (2.12) as a submodule (the conditions are linear in `A`). -/
abbrev ttSub (κ : ℝ) : Submodule ℝ Sym2 :=
  LinearizedGravity.ttSub κ

/-- **Thesis (2.13)**, "only two degrees of freedom", stated directly: for `κ ≠ 0` the space
`{A | A satisfies (2.12)}` has dimension `2`.

See [QuennevilleBelair2015, (2.13)]; cf. [Wald1984, §4.4]. -/
theorem finrank_ttSub {κ : ℝ} (hκ : κ ≠ 0) : Module.finrank ℝ (ttSub κ) = 2 :=
  LinearizedGravity.finrank_ttSub hκ

/-- Amplitude after the gauge change `ξ_a = B_a g(k·x)`, `g' = f`:
`A'_ab = A_ab − k_a B_b − k_b B_a + η_ab (k^c B_c)`. -/
abbrev gaugeAmp (k : Fin 4 → ℝ) (A : Sym2) (B : Fin 4 → ℝ) : Sym2 :=
  LinearizedGravity.gaugeAmp k A B

/-- Corrected gauge vector (covariant): `B₀ = −(A₀₀ + τ/2)/(2κ)`, `B_j = (k_j B₀ − A_j0)/κ`,
`τ = tr A`. -/
abbrev Bcorr (κ : ℝ) (A : Sym2) : Fin 4 → ℝ :=
  LinearizedGravity.Bcorr κ A

/-- The thesis' gauge vector: `B₀ = (A₀₀ + τ/2)/(2κ)`, `B_j = (A_j0 − k_j B₀)/κ`, read as
**covariant** components `B_a`. (The thesis writes `B^a` but mixes index positions; the
contravariant reading fails too, on the same witness of `thesis_gauge_fails`.) -/
abbrev Bthesis (κ : ℝ) (A : Sym2) : Fin 4 → ℝ :=
  LinearizedGravity.BPrinted κ A

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
      IsTT κ (gaugeAmp (kTT κ) A (Bcorr κ A)) :=
  LinearizedGravity.tt_gauge hκ hA hker

/-- The thesis' gauge vector `B` (Prop 2.6) does **not** reach TT gauge: for `κ = 1` and an
admissible symmetric `A` with `A k = 0`, the transformed amplitude is not transverse.
`Bthesis` uses the covariant reading of the printed `B`; `thesis_gauge_fails_contra` covers
the contravariant reading.

See [QuennevilleBelair2015, Prop 2.6]. -/
theorem thesis_gauge_fails :
    ∃ κ : ℝ, ∃ A : Sym2, κ ≠ 0 ∧ (∀ i j, A i j = A j i) ∧
      (∀ a, ∑ b, A a b * raise (kTT κ) b = 0) ∧ ¬ IsTT κ (gaugeAmp (kTT κ) A (Bthesis κ A)) :=
  Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed

/-- The thesis' gauge vector read as **contravariant** components `B^a` (lowered to
`B_a = η_aa B^a`) also fails to reach TT gauge, on the same witness.

See [QuennevilleBelair2015, Prop 2.6]. -/
theorem thesis_gauge_fails_contra :
    ∃ κ : ℝ, ∃ A : Sym2, κ ≠ 0 ∧ (∀ i j, A i j = A j i) ∧
      (∀ a, ∑ b, A a b * raise (kTT κ) b = 0) ∧
        ¬ IsTT κ (gaugeAmp (kTT κ) A (raise (Bthesis κ A))) :=
  Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed_contra

/-- Relative acceleration `a^i = −R^i_{0j0} v^j` (particles at rest, separation `v^j`). -/
abbrev accelJ (D : Jet2) (v : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  LinearizedGravity.accelJ D v i

/-- **Thesis (2.15), corrected**: for the 2-jet `k_i k_j A_ab s` of the TT plane wave
(`s = f''(k·x)`), `a¹ = (κ²/2)(A₊v¹ + Aₓv²) s`, `a² = (κ²/2)(Aₓv¹ − A₊v²) s`, `a⁰ = a³ = 0`.

Correction: the thesis gives `−(κ²/2)(…) f(k·x)` (sign, and `f` for `f''`).

See [QuennevilleBelair2015, §2.8, (2.15)]; cf. [Alcubierre2008, pp. 44–45]
(followed by the thesis). -/
theorem tt_accel (κ Ap Ax s : ℝ) (v : Fin 4 → ℝ) :
    let D : Jet2 := fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s
    accelJ D v 1 = κ ^ 2 / 2 * (Ap * v 1 + Ax * v 2) * s ∧
      accelJ D v 2 = κ ^ 2 / 2 * (Ax * v 1 - Ap * v 2) * s ∧
      accelJ D v 0 = 0 ∧ accelJ D v 3 = 0 :=
  LinearizedGravity.tt_accel κ Ap Ax s v

/-- Longitudinal indices `{0, 3}` (time and the propagation direction `x³`). -/
abbrev IsLong (i : Fin 4) : Prop :=
  LinearizedGravity.IsLong i

instance (i : Fin 4) : Decidable (IsLong i) := inferInstanceAs (Decidable (_ ∨ _))

/-- The 2-jet of a TT-gauge field depending only on `(x⁰, x³)`: `∂_i ∂_j h_ab = 0` unless
`i, j ∈ {0, 3}`, and `h_ab = 0` unless `a, b ∈ {1, 2}`. -/
abbrev IsTTJet (D : Jet2) : Prop :=
  LinearizedGravity.IsTTJet D

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
    Rjet D α i β j = -(1/2) * D α β i j :=
  LinearizedGravity.Rjet_tt hD hT hi hj

/-- **Thesis (2.15)**, "the only non-zero components": in TT gauge, `R_abcd = 0` unless each
of the pairs `(a, b)` and `(c, d)` has exactly one longitudinal index. With pair-skewness
(`Rjet_pairSkew`) every non-zero component is thus `±R_{αiβj}`, given by `Rjet_tt`.

See [QuennevilleBelair2015, (2.15a–c)]. -/
theorem Rjet_tt_support {D : Jet2} (hT : IsTTJet D) {a b c d : Fin 4}
    (h : Rjet D a b c d ≠ 0) : (IsLong a ↔ ¬ IsLong b) ∧ (IsLong c ↔ ¬ IsLong d) :=
  LinearizedGravity.Rjet_tt_support hT h

/-- The 2-jet `k_i k_j A_ab s` of the TT plane wave `ttAmp A₊ Aₓ · f(k·x)` (`s = f''`) is a
symmetric TT jet. -/
lemma ttWaveJet_props (κ Ap Ax s : ℝ) :
    IsSymJet2 (fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s) ∧
      IsTTJet (fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s) :=
  LinearizedGravity.ttWaveJet_props κ Ap Ax s

/-- **Thesis (2.15a–c)** for the TT plane wave (cf. the components `C_{αiβj}` in §2.9):
`R_{α1β1} = −½ k_α k_β A₊ s`, `R_{α2β2} = ½ k_α k_β A₊ s`, `R_{α1β2} = −½ k_α k_β Aₓ s`,
with `s = f''(k·x)` (valid for all `α, β`; both sides vanish unless `α, β ∈ {0, 3}`).

See [QuennevilleBelair2015, (2.15a–c)]. -/
theorem Rjet_ttWave (κ Ap Ax s : ℝ) (α β : Fin 4) :
    let D : Jet2 := fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s
    Rjet D α 1 β 1 = -(1/2) * kTT κ α * kTT κ β * Ap * s ∧
      Rjet D α 2 β 2 = (1/2) * kTT κ α * kTT κ β * Ap * s ∧
      Rjet D α 1 β 2 = -(1/2) * kTT κ α * kTT κ β * Ax * s :=
  LinearizedGravity.Rjet_ttWave κ Ap Ax s α β

/-- **Thesis §2.4 constant, corrected**: with `G = 6.67430·10⁻¹¹` and `c = 299792458` (SI),
`8πG/c⁴ ∈ (2.07, 2.09)·10⁻⁴³ s²/(m·kg)`, whereas the thesis' value `≈ 5·10⁻⁴⁴` is
`2πG/c⁴ ∈ (5.1, 5.3)·10⁻⁴⁴`.

See [QuennevilleBelair2015, §2.4]; cf. [Wald1984, Ch. 4]. -/
theorem einstein_const_bounds :
    let G : ℝ := 6.67430e-11
    let c : ℝ := 299792458
    (2.07e-43 < 8 * Real.pi * G / c ^ 4 ∧ 8 * Real.pi * G / c ^ 4 < 2.09e-43) ∧
      (5.1e-44 < 2 * Real.pi * G / c ^ 4 ∧ 2 * Real.pi * G / c ^ 4 < 5.3e-44) :=
  LinearizedGravity.einstein_const_bounds

/-- Coordinate space `ℝ⁴` (contravariant coordinates `x^a`). -/
abbrev E4 := Fin 4 → ℝ



section pd
variable {f g : E4 → ℝ} {x : E4}

/-- Linearity of `pd` (sum). -/
lemma pd_add (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd i (fun y => f y + g y) x = pd i f x + pd i g x :=
  partialDeriv_add hf hg i

/-- Linearity of `pd` (difference). -/
lemma pd_sub (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x :=
  partialDeriv_sub hf hg i

/-- Linearity of `pd` (scalar). -/
lemma pd_const_mul (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : Fin 4) :
    pd i (fun y => c * f y) x = c * pd i f x :=
  partialDeriv_const_smul hf c i

/-- Linearity of `pd` (finite sums). -/
lemma pd_sum {F : Fin 4 → E4 → ℝ} (hF : ∀ c, DifferentiableAt ℝ (F c) x) (i : Fin 4) :
    pd i (fun y => ∑ c, F c y) x = ∑ c, pd i (F c) x :=
  partialDeriv_sum univ (fun c _ => hF c) i

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
    pd i (pd j f) x = pd j (pd i f) x :=
  partialDeriv_comm hf i j x

/-- Partial derivatives lose one order of smoothness. -/
lemma contDiff_pd {m n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) (i : Fin 4) :
    ContDiff ℝ m (pd i f) :=
  hf.partialDeriv hmn i

/-- Partial derivatives of smooth functions are smooth. -/
lemma contDiff_pd_smooth (hf : ContDiff ℝ ∞ f) (i : Fin 4) : ContDiff ℝ ∞ (pd i f) :=
  hf.partialDeriv (by simp) i

/-- Partial derivatives of `C²` functions are differentiable. -/
lemma differentiable_pd (hf : ContDiff ℝ 2 f) (i : Fin 4) : Differentiable ℝ (pd i f) :=
  hf.differentiable_partialDeriv le_rfl i

end pd

/-- The 2-jet `∂_i ∂_j h_ab (x)` of a field `h : ℝ⁴ → Sym2`. -/
abbrev jet2 (h : E4 → Sym2) (x : E4) : Jet2 :=
  LinearizedGravity.jet2 h x

/-- The linearized Einstein tensor `H(h)(x)` (Thm 2.3) of a `C²` field. -/
abbrev Hfun (h : E4 → Sym2) (x : E4) (b d : Fin 4) : ℝ :=
  LinearizedGravity.Hfun LinearizedGravity.η4 LinearizedGravity.η4 h x b d

/-- Schwarz: the 2-jet of a `C²` symmetric field satisfies `IsSymJet2`, so all jet-level
identities apply to genuine fields.

See [QuennevilleBelair2015, §2.7] (function-level bridge). -/
theorem jet2_isSymJet2 {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b)
    (hs : ∀ y a b, h y a b = h y b a) (x : E4) : IsSymJet2 (jet2 h x) :=
  LinearizedGravity.jet2_isSymJet2 hC hs x

/-- The phase `k_c x^c` as a continuous linear functional. -/
abbrev phaseL (k : Fin 4 → ℝ) : E4 →L[ℝ] ℝ :=
  LinearizedGravity.phaseL k

lemma phaseL_apply (k : Fin 4 → ℝ) (y : E4) : phaseL k y = ∑ c, k c * y c :=
  LinearizedGravity.phaseL_apply k y

/-- Chain rule: `∂_i (c f(k·x)) = c k_i f'(k·x)`. -/
lemma pd_wave {f : ℝ → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (k : Fin 4 → ℝ) (i : Fin 4)
    (x : E4) : pd i (fun y => c * f (phaseL k y)) x = c * k i * deriv f (phaseL k x) :=
  LinearizedGravity.partialDeriv_wave hf c k i x

/-- The 2-jet of a plane wave `M_ab f(k·x)`: `∂_i∂_j = k_i k_j M_ab f''(k·x)`. -/
theorem jet2_wave {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (M : Sym2) (k : Fin 4 → ℝ) (x : E4) :
    jet2 (fun y a b => M a b * f (phaseL k y)) x =
      fun i j a b => k i * k j * M a b * deriv (deriv f) (phaseL k x) :=
  by
  have := LinearizedGravity.jet2_wave hf M k x
  funext i j a b
  have h2 := congrFun (congrFun (congrFun (congrFun this i) j) a) b
  exact h2.trans ((congrArg (deriv (deriv f) (LinearizedGravity.phaseL k x) * ·)
    (LinearizedGravity.symbolJet_apply k M i j a b)).trans (by ring))

/-- d'Alembertian `□u = η^{ij} ∂_i ∂_j u`. -/
abbrev box (u : E4 → ℝ) (x : E4) : ℝ :=
  LinearizedGravity.box LinearizedGravity.η4 u x

/-- Divergence `(∂^a h_ab)(x)` of a 2-tensor field. -/
abbrev divF (h : E4 → Sym2) (x : E4) (b : Fin 4) : ℝ :=
  LinearizedGravity.divF LinearizedGravity.η4 h x b

/-- Trace reversal commutes with scalars (right). -/
lemma trRev_mul_const (h : Sym2) (c : ℝ) :
    trRev (fun a b => h a b * c) = fun a b => trRev h a b * c :=
  by
  funext a b; simp only [trRev_apply', Fin.sum_univ_four]; ring

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
      ∀ x b d, Hfun (fun y => trRev (hbar y)) x b d = 0 :=
  LinearizedGravity.plane_wave hk hA hker hf

/-- **Hypothesis** (classical, absent from Mathlib): the inhomogeneous wave equation `□u = S`
has a smooth solution on ℝ⁴ for every smooth source `S` (e.g. zero Cauchy data and
Duhamel/Kirchhoff). This is the solver Prop 2.4(a) uses without citation.

Cf. [Wald1984, §4.4], where the Lorentz gauge is likewise reached by solving a wave
equation. -/
abbrev WaveSolvable : Prop :=
  LinearizedGravity.WaveSolvable LinearizedGravity.η4

/-- Trace-reversed pure-gauge field `2∂_(a ξ_b) − η_ab ∂^c ξ_c` (cf. (2.5)). -/
abbrev gaugeTR (ξ : Fin 4 → E4 → ℝ) (y : E4) : Sym2 :=
  LinearizedGravity.gaugeTR LinearizedGravity.η4 LinearizedGravity.η4 ξ y

/-- Contraction `η^{aa} η_ab R_a = R_b`. -/
lemma sum_eta_etaM (R : Fin 4 → ℝ) (b : Fin 4) : ∑ a, η a * (etaM a b * R a) = R b :=
  by fin_cases b <;> simp [etaM, η, LinearizedGravity.η4_apply, Metric.minkowski4]

/-- `∂^a (2∂_(a ξ_b) − η_ab ∂·ξ) = □ξ_b` (uses Schwarz). -/
lemma divF_gaugeTR {ξ : Fin 4 → E4 → ℝ} (hξ : ∀ a, ContDiff ℝ ∞ (ξ a)) (x : E4) (b : Fin 4) :
    divF (gaugeTR ξ) x b = box (ξ b) x :=
  LinearizedGravity.divF_gaugeTR LinearizedGravity.η4_isSymm LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self hξ x b

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
      ∀ x b, divF (fun y => hb y - gaugeTR ξ y) x b = 0 :=
  LinearizedGravity.exists_lorentz_gauge LinearizedGravity.η4_isSymm LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self hW hsm

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
      fun a b => ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) a b * f (phaseL (kTT κ) y) :=
  LinearizedGravity.tt_gauge_fun hκ hA hker hg hgf y

/-- **Thesis (2.15), corrected** (field level): for the TT plane wave
`h_ab = ttAmp A₊ Aₓ · f(k·x)` with `f ∈ C²`, `a¹ = (κ²/2)(A₊v¹ + Aₓv²) f''(k·x)` and
`a² = (κ²/2)(Aₓv¹ − A₊v²) f''(k·x)`.

See [QuennevilleBelair2015, (2.15)]; cf. [Alcubierre2008]. -/
theorem tt_accel_fun (κ Ap Ax : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (v : Fin 4 → ℝ) (x : E4) :
    let D := jet2 (fun y a b => ttAmp Ap Ax a b * f (phaseL (kTT κ) y)) x
    let s := deriv (deriv f) (phaseL (kTT κ) x)
    accelJ D v 1 = κ ^ 2 / 2 * (Ap * v 1 + Ax * v 2) * s ∧
      accelJ D v 2 = κ ^ 2 / 2 * (Ax * v 1 - Ap * v 2) * s ∧
      accelJ D v 0 = 0 ∧ accelJ D v 3 = 0 :=
  LinearizedGravity.tt_accel_fun κ Ap Ax hf v x

/-- The thesis' accelerations `a¹ = −(κ²/2)(A₊v¹ + Aₓv²) f(k·x)` (after (2.15)) are wrong:
for `f(t) = t²`, `κ = A₊ = v¹ = 1`, `Aₓ = 0` at `x = 0` the true value is `1`, not `0`.

See [QuennevilleBelair2015, §2.8, after (2.15)]. -/
theorem thesis_accel_fails :
    ¬ ∀ (κ Ap Ax : ℝ) (f : ℝ → ℝ), ContDiff ℝ 2 f → ∀ (v : Fin 4 → ℝ) (x : E4),
      accelJ (jet2 (fun y a b => ttAmp Ap Ax a b * f (phaseL (kTT κ) y)) x) v 1 =
        -(κ ^ 2 / 2) * (Ap * v 1 + Ax * v 2) * f (phaseL (kTT κ) x) :=
  Counterexamples.LinearizedGravity.not_accel_printed

/-- `∂_i` commutes with trace reversal. -/
lemma pd_trRev {F : E4 → Sym2} {x : E4} (hF : ∀ a b, DifferentiableAt ℝ (fun y => F y a b) x)
    (i a b : Fin 4) :
    pd i (fun y => trRev (F y) a b) x = trRev (fun a' b' => pd i (fun y => F y a' b') x) a b :=
  LinearizedGravity.partialDeriv_trRev hF i a b

/-- The 2-jet of `h̄ = trRev h` is the trace reversal of the 2-jet of `h`. -/
theorem jet2_trRev {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b) (x : E4) :
    jet2 (fun y => trRev (h y)) x = barJ (jet2 h x) :=
  LinearizedGravity.jet2_trRev hC x

/-- **Thesis Thm 2.3** for a genuine `C²` symmetric field: both forms of `H` agree,
`H(h) = ∂^a∂_(b h̄_d)a − ½(□h̄_bd + η_bd ∂^a∂^e h̄_ea)` with the genuine 2-jet of `h̄`.

See [QuennevilleBelair2015, Thm 2.3]; cf. [Wald1984, §4.4]. -/
theorem Hfun_eq_bar {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b)
    (hs : ∀ y a b, h y a b = h y b a) (x : E4) (b d : Fin 4) :
    Hfun h x b d = HbarJet (jet2 (fun y => trRev (h y)) x) b d :=
  LinearizedGravity.Hfun_eq_bar LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self hC hs x b d

/-- **Thesis Prop 2.4(b), corrected**, for a genuine `C²` symmetric field: if `h̄ = trRev h`
is in Lorentz gauge (`∂^a h̄_ab = 0` everywhere), then `H(h) = −½ □h̄`.

Correction: the thesis states `H = −□h̄` (see `thesis_prop_2_4b_false`).

See [QuennevilleBelair2015, Prop 2.4(b)]; cf. [Wald1984, §4.4]. -/
theorem Hfun_lorentz {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b)
    (hs : ∀ y a b, h y a b = h y b a) (hL : ∀ y b, divF (fun z => trRev (h z)) y b = 0)
    (x : E4) (b d : Fin 4) :
    Hfun h x b d = -(1/2) * box (fun y => trRev (h y) b d) x :=
  by
  rw [Hfun, LinearizedGravity.Hfun_lorentz LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self hC hs hL x b d, invOf_eq_inv]; norm_num

/-- **Thesis (2.11)** for genuine fields: in Lorentz gauge,
`H(h) = 8πT ⟺ □h̄ = −16πT`.

See [QuennevilleBelair2015, (2.11)]; cf. [Wald1984, §4.4]. -/
theorem lorentz_fun_iff {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b)
    (hs : ∀ y a b, h y a b = h y b a) (hL : ∀ y b, divF (fun z => trRev (h z)) y b = 0)
    (T : E4 → Sym2) (x : E4) (b d : Fin 4) :
    Hfun h x b d = 8 * Real.pi * T x b d ↔
      box (fun y => trRev (h y) b d) x = -16 * Real.pi * T x b d :=
  by
  rw [Hfun_lorentz hC hs hL]
  constructor <;> intro h <;> linarith

/-- `H` is additive in the jet. -/
lemma Hjet_add (D G : Jet2) (b d : Fin 4) :
    Hjet (fun i j a b => D i j a b + G i j a b) b d = Hjet D b d + Hjet G b d :=
  LinearizedGravity.Hjet_add D G b d

/-- **Gauge invariance** (end of §2.7) for genuine fields: `H(h + 2∂_(a ξ_b)) = H(h)` for
`h ∈ C²` and `ξ ∈ C³`.

Thesis gap: the thesis' check has the trace `4∇·ξ` (should be `2∇·ξ`) and displays `2H`;
the needed regularity (`ξ ∈ C³`, to commute third derivatives) is unstated.

See [QuennevilleBelair2015, §2.7]; cf. [Wald1984, §4.4]. -/
theorem Hfun_gauge {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 2 fun y => h y a b)
    {ξ : Fin 4 → E4 → ℝ} (hξ : ∀ a, ContDiff ℝ 3 (ξ a)) (x : E4) (b d : Fin 4) :
    Hfun (fun y a b => h y a b + (pd a (ξ b) y + pd b (ξ a) y)) x b d = Hfun h x b d :=
  LinearizedGravity.Hfun_gauge LinearizedGravity.η4_isSymm hC hξ x b d

/-- `H` as a continuous linear functional on jets. -/
abbrev HjetL (b d : Fin 4) : Jet2 →L[ℝ] ℝ :=
  LinearizedGravity.HjetL LinearizedGravity.η4 LinearizedGravity.η4 b d

/-- Evaluation of a jet at an index, as a continuous linear functional. -/
abbrev evalJ (i j a b : Fin 4) : Jet2 →L[ℝ] ℝ :=
  LinearizedGravity.evalJet i j a b

/-- Chain rule for a continuous linear functional of a jet-valued map. -/
lemma pd_clm_comp {J : E4 → Jet2} {x : E4} (hJ : DifferentiableAt ℝ J x) (P : Jet2 →L[ℝ] ℝ)
    (m : Fin 4) : pd m (fun y => P (J y)) x = P (fderiv ℝ J x (Pi.single m 1)) :=
  ContinuousLinearMap.partialDeriv_comp P hJ m

/-- `∂_m` commutes with `H`. -/
lemma pd_Hjet {J : E4 → Jet2} {x : E4} (hJ : DifferentiableAt ℝ J x) (m b d : Fin 4) :
    pd m (fun y => Hjet (J y) b d) x =
      Hjet (fun i j a b => pd m (fun y => J y i j a b) x) b d :=
  by
  have e1 : (fun y => Hjet (J y) b d) = fun y => LinearizedGravity.HjetL LinearizedGravity.η4 LinearizedGravity.η4 b d (J y) := rfl
  rw [e1]
  show partialDeriv m (fun y => LinearizedGravity.HjetL LinearizedGravity.η4 LinearizedGravity.η4 b d (J y)) x = _
  rw [ContinuousLinearMap.partialDeriv_comp _ hJ m]
  show LinearizedGravity.Hjet LinearizedGravity.η4 LinearizedGravity.η4 (fun i j => Matrix.of (partialDeriv m J x i j)) b d = _
  congr 1
  funext i j; ext a c
  show partialDeriv m J x i j a c = partialDeriv m (fun y => J y i j a c) x
  have := ContinuousLinearMap.partialDeriv_comp (LinearizedGravity.evalJet i j a c) hJ m
  simpa [LinearizedGravity.evalJet] using this.symm

/-- **Linearized Bianchi identity** for genuine fields: `∂^b H_bd(h) = 0` for every `C³`
symmetric `h`.

Thesis gap: not in the thesis; it is the consistency condition `∂^b T_bd = 0` behind the
linearized equations (2.10) and their gauge freedom.

See [QuennevilleBelair2015, §2.7]; cf. [Wald1984, §4.4]. -/
theorem Hfun_bianchi {h : E4 → Sym2} (hC : ∀ a b, ContDiff ℝ 3 fun y => h y a b)
    (hs : ∀ y a b, h y a b = h y b a) (x : E4) (d : Fin 4) :
    ∑ b, η b * pd b (fun y => Hfun h y b d) x = 0 :=
  by
  have := LinearizedGravity.Hfun_bianchi LinearizedGravity.η4_isSymm LinearizedGravity.η4_isSymm LinearizedGravity.η4_mul_self hC hs x d
  rw [LinearizedGravity.sum_η4 (fun b b' => partialDeriv b' (fun y => LinearizedGravity.Hfun LinearizedGravity.η4 LinearizedGravity.η4 h y b d) x)] at this
  show ∑ b, η b * partialDeriv b (fun y => LinearizedGravity.Hfun LinearizedGravity.η4 LinearizedGravity.η4 h y b d) x = 0
  simpa [η, Metric.minkowski4] using this

/-! ### Structure fields (shims) -/

theorem IsSymJet2.deriv_symm {D : Jet2} (h : IsSymJet2 D) : ∀ i j a b, D i j a b = D j i a b :=
  LinearizedGravity.IsSymJet2.deriv_symm h
theorem IsSymJet2.tensor_symm {D : Jet2} (h : IsSymJet2 D) : ∀ i j a b, D i j a b = D i j b a :=
  LinearizedGravity.IsSymJet2.tensor_symm h
theorem IsSymJet3ξ.symm₁ {X : Jet2} (h : IsSymJet3ξ X) : ∀ i j c b, X i j c b = X j i c b :=
  LinearizedGravity.IsSymJet3ξ.symm₁ h
theorem IsSymJet3ξ.symm₂ {X : Jet2} (h : IsSymJet3ξ X) : ∀ i j c b, X i j c b = X i c j b :=
  LinearizedGravity.IsSymJet3ξ.symm₂ h
theorem IsSymJet3.symm₁ {Y : Jet3} (h : IsSymJet3 Y) : ∀ m i j a b, Y m i j a b = Y i m j a b :=
  LinearizedGravity.IsSymJet3.symm₁ h
theorem IsSymJet3.symm₂ {Y : Jet3} (h : IsSymJet3 Y) : ∀ m i j a b, Y m i j a b = Y m j i a b :=
  LinearizedGravity.IsSymJet3.symm₂ h
theorem IsSymJet3.tensor_symm {Y : Jet3} (h : IsSymJet3 Y) :
    ∀ m i j a b, Y m i j a b = Y m i j b a :=
  LinearizedGravity.IsSymJet3.tensor_symm h
theorem IsTT.symm {κ : ℝ} {A : Sym2} (h : IsTT κ A) : ∀ a b, A a b = A b a :=
  LinearizedGravity.IsTT.symm h
theorem IsTT.lorentz {κ : ℝ} {A : Sym2} (h : IsTT κ A) : ∀ a, ∑ b, A a b * raise (kTT κ) b = 0 :=
  LinearizedGravity.IsTT.lorentz h
theorem IsTT.transverse {κ : ℝ} {A : Sym2} (h : IsTT κ A) : ∀ a, ∑ b, A a b * uObs b = 0 :=
  LinearizedGravity.IsTT.transverse h
theorem IsTT.traceless {κ : ℝ} {A : Sym2} (h : IsTT κ A) : tr A = 0 :=
  LinearizedGravity.IsTT.traceless h
theorem IsTTJet.long_i {D : Jet2} (h : IsTTJet D) : ∀ i j a b, ¬ IsLong i → D i j a b = 0 :=
  LinearizedGravity.IsTTJet.long_i h
theorem IsTTJet.long_j {D : Jet2} (h : IsTTJet D) : ∀ i j a b, ¬ IsLong j → D i j a b = 0 :=
  LinearizedGravity.IsTTJet.long_j h
theorem IsTTJet.trans_a {D : Jet2} (h : IsTTJet D) : ∀ i j a b, IsLong a → D i j a b = 0 :=
  LinearizedGravity.IsTTJet.trans_a h
theorem IsTTJet.trans_b {D : Jet2} (h : IsTTJet D) : ∀ i j a b, IsLong b → D i j a b = 0 :=
  LinearizedGravity.IsTTJet.trans_b h

end Feec.Linearized
