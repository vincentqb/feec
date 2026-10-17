module

public import Feec.Physics.LinearizedGravity.Gauge
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gravitational plane waves in four-dimensional Minkowski space

The thesis-specific part of linearized gravity (§2.8): Minkowski space `η = diag(-1,1,1,1)`,
the general linearized Einstein operator `Hjet η4 η4` of `Feec.Physics.LinearizedGravity.Einstein`,
plane waves `h̄ = A f(k·x)` (Prop 2.5), the TT gauge (2.12)–(2.13) and its two degrees of
freedom, the gauge change to TT (Prop 2.6, corrected), and the geodesic deviation of a TT wave
((2.15), corrected; (2.15a–c)).

## Main results

* `plane_wave` (**Prop 2.5**): `□h̄ = 0`, Lorentz gauge and `H(h) = 0` for `h̄ = A f(k·x)`.
* `isTT_iff`, `finrank_ttSub` (**(2.13)**): TT amplitudes are `ttAmp A₊ Aₓ`, a 2-dimensional
  space.
* `tt_gauge`, `tt_gauge_fun` (**Prop 2.6, corrected**); `exists_ttGauge` (the existence
  statement, with an explicit `C³` gauge vector built by the fundamental theorem of calculus).
* `tt_accel`, `tt_accel_fun` (**(2.15), corrected**); `Rjet_tt`, `Rjet_tt_support`,
  `Rjet_ttWave` (**(2.15a–c)**).
* `einstein_const_bounds`: `8πG/c⁴ ≈ 2.08·10⁻⁴³` (the thesis' `5·10⁻⁴⁴` is `2πG/c⁴`).
* The counterexamples to the printed statements (Prop 2.4(b), the gauge vector of Prop 2.6, the
  accelerations after (2.15)) are in `Feec.Counterexamples.LinearizedGravity`.

## References

* [QuennevilleBelair2015], §2.4 (coupling constant), §2.8 (Props 2.4–2.6, (2.12)–(2.15))
* [Wald1984], §4.4; [Alcubierre2008], pp. 44–45
-/

open Finset Matrix
open scoped ContDiff

@[expose] public noncomputable section

namespace Feec.LinearizedGravity

/-! ### The Minkowski metric matrix -/

/-- The Minkowski metric matrix `η = diag(-1, 1, 1, 1)` (its own inverse). Thesis: §2.2 -/
abbrev η4 : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal (Metric.minkowski4 ℝ)

theorem η4_apply (a b : Fin 4) : η4 a b = if a = b then Metric.minkowski4 ℝ a else 0 :=
  Matrix.diagonal_apply _ _ _

theorem η4_isSymm : η4.IsSymm := by simp [Matrix.IsSymm]

theorem η4_mul_self : η4 * η4 = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; exact Metric.minkowski4_mul_self i

theorem sum_η4 (F : Fin 4 → Fin 4 → ℝ) :
    ∑ i, ∑ j, η4 i j * F i j = ∑ i, Metric.minkowski4 ℝ i * F i i := by
  simp [η4_apply, ite_mul]

theorem trace_η4 (h : Matrix (Fin 4) (Fin 4) ℝ) :
    Metric.trace η4 h = ∑ i, Metric.minkowski4 ℝ i * h i i := sum_η4 _

theorem dot_η4 (k k' : Fin 4 → ℝ) : dot η4 k k' = ∑ i, Metric.minkowski4 ℝ i * k i * k' i := by
  rw [dot]; simp only [mul_assoc]; exact sum_η4 _

theorem trRev_η4_apply (h : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin 4) :
    Metric.trRev η4 η4 h a b =
      h a b - η4 a b * (∑ i, Metric.minkowski4 ℝ i * h i i) / 2 := by
  rw [Metric.trRev_apply, trace_η4, invOf_eq_inv]; ring

/-- Index raising `v^a = η^{ab} v_b`. -/
def raise (v : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => Metric.minkowski4 ℝ i * v i

/-! ## Prop 2.5 algebra, TT gauge (2.12)–(2.13), Prop 2.6 -/

/-- Covector `k_a = κ(−1, 0, 0, 1)` of the wave vector `k^a = κ(1, 0, 0, 1)`. -/
def kTT (κ : ℝ) : Fin 4 → ℝ := ![-κ, 0, 0, κ]

/-- Observer `u^a = (1, 0, 0, 0)` (contravariant). -/
def uObs : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The TT conditions (2.12) on a constant amplitude: symmetric, `A_ab k^b = 0`,
`A_ab u^b = 0`, `η^{ab} A_ab = 0`.

See [QuennevilleBelair2015, §2.8, (2.12)]; cf. [Wald1984, §4.4]. -/
structure IsTT (κ : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  symm : ∀ a b, A a b = A b a
  lorentz : ∀ a, ∑ b, A a b * raise (kTT κ) b = 0
  transverse : ∀ a, ∑ b, A a b * uObs b = 0
  traceless : Metric.trace η4 A = 0

/-- The `+`/`×` amplitude (2.13). -/
def ttAmp (Ap Ax : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, 0; 0, Ap, Ax, 0; 0, Ax, -Ap, 0; 0, 0, 0, 0]

/-- The `+`/`×` amplitudes (2.13) satisfy the TT conditions (2.12). -/
lemma ttAmp_isTT (κ Ap Ax : ℝ) : IsTT κ (ttAmp Ap Ax) where
  symm a b := by fin_cases a <;> fin_cases b <;> rfl
  lorentz a := by fin_cases a <;> simp [ttAmp, raise, kTT, Fin.sum_univ_four]
  transverse a := by fin_cases a <;> simp [ttAmp, uObs, Fin.sum_univ_four]
  traceless := by simp [trace_η4, ttAmp, Fin.sum_univ_four, Metric.minkowski4]

/-- **Thesis (2.13)**: for `κ ≠ 0`, the TT conditions (2.12) hold iff `A` has the `+`/`×`
form, with `A₊ = A₁₁`, `Aₓ = A₁₂`.

Thesis gap: `κ ≠ 0` is needed; it is only implicit in the thesis (`k^a = k(1,0,0,1)`, later
divided by `k`).

See [QuennevilleBelair2015, §2.8, (2.12)–(2.13)]; cf. [Wald1984, §4.4]. -/
theorem isTT_iff {κ : ℝ} (hκ : κ ≠ 0) (A : Matrix (Fin 4) (Fin 4) ℝ) : IsTT κ A ↔ A = ttAmp (A 1 1) (A 1 2) := by
  refine ⟨fun h => ?_, fun h => h ▸ ttAmp_isTT κ _ _⟩
  have hu : ∀ a, A a 0 = 0 := fun a => by
    simpa [uObs, Fin.sum_univ_four] using h.transverse a
  have h3 : ∀ a, A a 3 = 0 := fun a => by
    have := h.lorentz a
    simp only [raise, kTT, Fin.sum_univ_four, Metric.minkowski4] at this
    simp [hu a] at this
    exact this.resolve_right hκ
  have htr := h.traceless
  simp only [trace_η4, Fin.sum_univ_four, Metric.minkowski4] at htr
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
def ttLin : (Fin 2 → ℝ) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ where
  toFun p := ttAmp (p 0) (p 1)
  map_add' p q := by
    funext a b; fin_cases a <;> fin_cases b <;> simp [ttAmp]; ring
  map_smul' c p := by
    funext a b; fin_cases a <;> fin_cases b <;> simp [ttAmp]

/-- The space of TT amplitudes. -/
def ttSpace : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) := LinearMap.range ttLin

/-- **Thesis (2.12)–(2.13)**: for `κ ≠ 0`, `ttSpace` is exactly the set of TT amplitudes.

See [QuennevilleBelair2015, (2.12)–(2.13)]. -/
theorem mem_ttSpace_iff {κ : ℝ} (hκ : κ ≠ 0) (A : Matrix (Fin 4) (Fin 4) ℝ) : A ∈ ttSpace ↔ IsTT κ A := by
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
def ttSub (κ : ℝ) : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) where
  carrier := {A | IsTT κ A}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => by simp, fun _ => by simp, by simp [trace_η4]⟩
  add_mem' {A B} hA hB :=
    ⟨fun a b => by simp [hA.symm a b, hB.symm a b],
      fun a => by simp [add_mul, sum_add_distrib, hA.lorentz a, hB.lorentz a],
      fun a => by simp [add_mul, sum_add_distrib, hA.transverse a, hB.transverse a],
      by have := hA.traceless; have := hB.traceless; simp_all [trace_η4, mul_add, sum_add_distrib]⟩
  smul_mem' c A hA :=
    ⟨fun a b => by simp [hA.symm a b],
      fun a => by simp [mul_assoc, ← mul_sum, hA.lorentz a],
      fun a => by simp [mul_assoc, ← mul_sum, hA.transverse a],
      by have := hA.traceless; simp only [trace_η4] at this ⊢; simp [mul_left_comm _ c, ← mul_sum, this]⟩

/-- **Thesis (2.13)**, "only two degrees of freedom", stated directly: for `κ ≠ 0` the space
`{A | A satisfies (2.12)}` has dimension `2`.

See [QuennevilleBelair2015, (2.13)]; cf. [Wald1984, §4.4]. -/
theorem finrank_ttSub {κ : ℝ} (hκ : κ ≠ 0) : Module.finrank ℝ (ttSub κ) = 2 := by
  have : ttSub κ = ttSpace := by
    ext A; exact (mem_ttSpace_iff hκ A).symm
  rw [this, finrank_ttSpace]

/-- Amplitude after the gauge change `ξ_a = B_a g(k·x)`, `g' = f`:
`A'_ab = A_ab − k_a B_b − k_b B_a + η_ab (k^c B_c)`. -/
def gaugeAmp (k : Fin 4 → ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) (B : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun a b => A a b - k a * B b - k b * B a + η4 a b * dot η4 k B

/-- Corrected gauge vector (covariant): `B₀ = −(A₀₀ + τ/2)/(2κ)`, `B_j = (k_j B₀ − A_j0)/κ`,
`τ = Metric.trace η4 A`. -/
def Bcorr (κ : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) : Fin 4 → ℝ :=
  let B0 := -(A 0 0 + Metric.trace η4 A / 2) / (2 * κ)
  fun j => if j = 0 then B0 else (kTT κ j * B0 - A j 0) / κ

/-- The thesis' gauge vector: `B₀ = (A₀₀ + τ/2)/(2κ)`, `B_j = (A_j0 − k_j B₀)/κ`, read as
**covariant** components `B_a`. (The thesis writes `B^a` but mixes index positions; the
contravariant reading fails too, on the same witness of
`Feec.Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed`.) -/
def BPrinted (κ : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) : Fin 4 → ℝ :=
  let B0 := (A 0 0 + Metric.trace η4 A / 2) / (2 * κ)
  fun j => if j = 0 then B0 else (A j 0 - kTT κ j * B0) / κ

/-- **Thesis Prop 2.6, corrected** (algebraic core): for `κ ≠ 0` and `A` symmetric with
`A_ab k^b = 0`, the gauge vector `Bcorr` produces a TT amplitude, namely
`A' = ttAmp ((A₁₁ − A₂₂)/2) A₁₂`.

Correction: the thesis' derivation uses `η₀₀ = +1`, `k₀ = +κ`, contradicting (−+++); its
`B` has the wrong sign and fails
(`Feec.Counterexamples.LinearizedGravity.not_isTT_gaugeAmp_printed`). The resulting amplitudes
`A'₊ = (A₁₁ − A₂₂)/2`, `A'ₓ = A₁₂` are not recorded in the thesis.

See [QuennevilleBelair2015, Prop 2.6]; cf. [Wald1984, §4.4]. -/
theorem tt_gauge {κ : ℝ} (hκ : κ ≠ 0) {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ i j, A i j = A j i)
    (hker : ∀ a, ∑ b, A a b * raise (kTT κ) b = 0) :
    gaugeAmp (kTT κ) A (Bcorr κ A) = ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) ∧
      IsTT κ (gaugeAmp (kTT κ) A (Bcorr κ A)) := by
  have hk : ∀ a, A a 0 + A a 3 = 0 := fun a => by
    have := hker a
    simp only [raise, kTT, Fin.sum_univ_four, Metric.minkowski4] at this
    simp at this
    have : (A a 0 + A a 3) * κ = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hκ
  have e : gaugeAmp (kTT κ) A (Bcorr κ A) = ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) := by
    have k0 := hk 0; have k1 := hk 1; have k2 := hk 2; have k3 := hk 3
    have s01 := hA 0 1; have s02 := hA 0 2; have s03 := hA 0 3; have s12 := hA 1 2
    have s13 := hA 1 3; have s23 := hA 2 3
    funext a b
    fin_cases a <;> fin_cases b <;>
      simp [gaugeAmp, Bcorr, kTT, dot_η4, trace_η4, η4_apply, ttAmp, Fin.sum_univ_four, Metric.minkowski4] <;>
      (try field_simp) <;> linarith
  exact ⟨e, e ▸ ttAmp_isTT κ _ _⟩

/-! ## Geodesic deviation in TT gauge (2.15) -/

/-- Relative acceleration `a^i = −R^i_{0j0} v^j` (particles at rest, separation `v^j`). -/
def accelJ (D : Jet2 (Fin 4) ℝ) (v : Fin 4 → ℝ) (i : Fin 4) : ℝ := -∑ j, Metric.minkowski4 ℝ i * Rjet D i 0 j 0 * v j

/-- **Thesis (2.15), corrected**: for the 2-jet `k_i k_j A_ab s` of the TT plane wave
(`s = f''(k·x)`), `a¹ = (κ²/2)(A₊v¹ + Aₓv²) s`, `a² = (κ²/2)(Aₓv¹ − A₊v²) s`, `a⁰ = a³ = 0`.

Correction: the thesis gives `−(κ²/2)(…) f(k·x)` (sign, and `f` for `f''`).

See [QuennevilleBelair2015, §2.8, (2.15)]; cf. [Alcubierre2008, pp. 44–45]
(followed by the thesis). -/
theorem tt_accel (κ Ap Ax s : ℝ) (v : Fin 4 → ℝ) :
    let D : Jet2 (Fin 4) ℝ := fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s
    accelJ D v 1 = κ ^ 2 / 2 * (Ap * v 1 + Ax * v 2) * s ∧
      accelJ D v 2 = κ ^ 2 / 2 * (Ax * v 1 - Ap * v 2) * s ∧
      accelJ D v 0 = 0 ∧ accelJ D v 3 = 0 := by
  simp only [accelJ, Rjet, kTT, ttAmp, Fin.sum_univ_four, Metric.minkowski4]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> ring

/-! ### Riemann components in TT gauge (2.15a–c) -/

/-- Longitudinal indices `{0, 3}` (time and the propagation direction `x³`). -/
def IsLong (i : Fin 4) : Prop := i = 0 ∨ i = 3

instance (i : Fin 4) : Decidable (IsLong i) := inferInstanceAs (Decidable (_ ∨ _))

/-- The 2-jet of a TT-gauge field depending only on `(x⁰, x³)`: `∂_i ∂_j h_ab = 0` unless
`i, j ∈ {0, 3}`, and `h_ab = 0` unless `a, b ∈ {1, 2}`. -/
structure IsTTJet (D : Jet2 (Fin 4) ℝ) : Prop where
  long_i : ∀ i j a b, ¬ IsLong i → D i j a b = 0
  long_j : ∀ i j a b, ¬ IsLong j → D i j a b = 0
  trans_a : ∀ i j a b, IsLong a → D i j a b = 0
  trans_b : ∀ i j a b, IsLong b → D i j a b = 0

lemma IsTTJet.support {D : Jet2 (Fin 4) ℝ} (hD : IsTTJet D) {i j a b : Fin 4} (h : D i j a b ≠ 0) :
    IsLong i ∧ IsLong j ∧ ¬ IsLong a ∧ ¬ IsLong b := by
  refine ⟨?_, ?_, fun hc => h (hD.trans_a _ _ _ _ hc), fun hc => h (hD.trans_b _ _ _ _ hc)⟩ <;>
    by_contra hc
  exacts [h (hD.long_i _ _ _ _ hc), h (hD.long_j _ _ _ _ hc)]

/-- **Thesis (2.15a–c)**: in TT gauge, for `i, j ∈ {1, 2}`,
`R_{αiβj} = −½ ∂_α ∂_β h_ij` (exactly, at the jet level). The thesis restricts to
`α, β ∈ {0, 3}`; for other `α, β` both sides vanish.

See [QuennevilleBelair2015, (2.15a–c)]; cf. [Alcubierre2008]. -/
theorem Rjet_tt {D : Jet2 (Fin 4) ℝ} (hD : IsSymJet2 D) (hT : IsTTJet D) {α β i j : Fin 4}
    (hi : ¬ IsLong i) (hj : ¬ IsLong j) :
    Rjet D α i β j = -(1/2) * D α β i j := by
  simp only [Rjet]
  rw [hT.long_j _ _ _ _ hi, hT.long_i _ _ _ _ hj, hT.long_i _ _ _ _ hj, hD.deriv_symm β α,
    invOf_eq_inv]
  ring

/-- **Thesis (2.15)**, "the only non-zero components": in TT gauge, `R_abcd = 0` unless each
of the pairs `(a, b)` and `(c, d)` has exactly one longitudinal index. With pair-skewness
(`Rjet_pairSkew`) every non-zero component is thus `±R_{αiβj}`, given by `Rjet_tt`.

See [QuennevilleBelair2015, (2.15a–c)]. -/
theorem Rjet_tt_support {D : Jet2 (Fin 4) ℝ} (hT : IsTTJet D) {a b c d : Fin 4}
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
    let D : Jet2 (Fin 4) ℝ := fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s
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
`2πG/c⁴ ∈ (5.1, 5.3)·10⁻⁴⁴`. Thesis: §2.4 (corrected) -/
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

/-! ### Plane waves -/

/-- The phase `k_c x^c` as a continuous linear functional. -/
def phaseL (k : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ := ∑ c, k c • ContinuousLinearMap.proj c

@[simp] theorem phaseL_apply (k : Fin 4 → ℝ) (y : Fin 4 → ℝ) : phaseL k y = ∑ c, k c * y c := by
  simp [phaseL]

/-- Chain rule: `∂_i (c f(k·x)) = c k_i f'(k·x)`. -/
theorem partialDeriv_wave {f : ℝ → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (k : Fin 4 → ℝ)
    (i : Fin 4) (x : Fin 4 → ℝ) :
    partialDeriv i (fun y => c * f (phaseL k y)) x = c * k i * deriv f (phaseL k x) := by
  have h1 : HasFDerivAt (fun y => f (phaseL k y)) (deriv f (phaseL k x) • phaseL k) x :=
    (hf _).hasDerivAt.comp_hasFDerivAt x (phaseL k).hasFDerivAt
  rw [(h1.const_mul c).partialDeriv_eq]
  simp [Pi.single_apply]
  ring

/-- The 2-jet of a plane wave `M_ab f(k·x)`: `∂_i ∂_j = k_i k_j M_ab f''(k·x)`. -/
theorem jet2_wave {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (k : Fin 4 → ℝ) (x : Fin 4 → ℝ) :
    jet2 (fun y => Matrix.of fun a b => M a b * f (phaseL k y)) x =
      deriv (deriv f) (phaseL k x) • symbolJet k M := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv f) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2.differentiable (by norm_num)
  funext i j; ext a b
  have e : partialDeriv j (fun y => M a b * f (phaseL k y)) =
      fun y => (M a b * k j) * deriv f (phaseL k y) := by
    funext y; exact partialDeriv_wave hd _ k j y
  simp only [jet2, of_apply]
  rw [e, partialDeriv_wave hd' _ k i x]
  simp only [Pi.smul_apply, Matrix.smul_apply, symbolJet_apply, smul_eq_mul]
  ring

/-- **Thesis Prop 2.5** (plane waves), with genuine derivatives: for a null covector `k`
(`k·k = 0`), a constant symmetric amplitude with `A_ab k^b = 0` and `f ∈ C²`, the field
`h̄_ab = A_ab f(k·x)` satisfies `□h̄ = 0` and the Lorentz gauge `∂^a h̄_ab = 0`, and the
perturbation `h` with trace reversal `h̄` (`h = trRev h̄`, `Metric.trRev_trRev`) solves the
vacuum linearized equations `H(h) = 0`. (`k` is covariant, `k·k = η^{ij} k_i k_j`, and the
phase is `k_c x^c`.) Thesis: Prop 2.5 -/
theorem plane_wave {k : Fin 4 → ℝ} (hk : dot η4 k k = 0) {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : ∀ a b, A a b = A b a) (hker : ∀ a, ∑ b, A a b * raise k b = 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) :
    let hbar : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
      fun y => Matrix.of fun a b => A a b * f (phaseL k y)
    (∀ x a b, box η4 (fun y => hbar y a b) x = 0) ∧ (∀ x b, divF η4 hbar x b = 0) ∧
      ∀ x b d, Hfun η4 η4 (fun y => Metric.trRev η4 η4 (hbar y)) x b d = 0 := by
  intro hbar
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hAs : Aᵀ = A := by ext a b; exact (hA b a)
  have hdiv : ∀ b, ∑ a, Metric.minkowski4 ℝ a * k a * A a b = 0 := fun b => by
    rw [← hker b]; exact sum_congr rfl fun a _ => by rw [hA, raise]; ring
  refine ⟨fun x a b => ?_, fun x b => ?_, fun x b d => ?_⟩
  · have e : ∀ i j, partialDeriv i (partialDeriv j fun y => hbar y a b) x =
        jet2 hbar x i j a b := fun _ _ => rfl
    simp only [box, e, hbar, jet2_wave hf A k x, Pi.smul_apply, Matrix.smul_apply,
      symbolJet_apply, smul_eq_mul]
    have : ∑ i, ∑ j, η4 i j * (deriv (deriv f) (phaseL k x) * (k i * k j * A a b)) =
        dot η4 k k * (A a b * deriv (deriv f) (phaseL k x)) := by
      simp only [dot, sum_mul]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    rw [this, hk, zero_mul]
  · simp only [divF, hbar, of_apply, partialDeriv_wave hd, sum_η4]
    have : ∑ a, Metric.minkowski4 ℝ a * (A a b * k a * deriv f (phaseL k x)) =
        (∑ a, Metric.minkowski4 ℝ a * k a * A a b) * deriv f (phaseL k x) := by
      rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
    rw [this, hdiv, zero_mul]
  · have e1 : (fun y => Metric.trRev η4 η4 (hbar y)) =
        fun y => Matrix.of fun a b => Metric.trRev η4 η4 A a b * f (phaseL k y) := by
      funext y
      have : hbar y = f (phaseL k y) • A := by ext a b; simp [hbar, mul_comm]
      rw [this, Metric.trRev_smul]; ext a b; simp [mul_comm]
    have hL : ∀ b, divSym η4 η4 k (Metric.trRev η4 η4 A) b = 0 := fun b => by
      simp only [divSym, Metric.trRev_trRev η4_isSymm η4_mul_self (by simp), mul_assoc, sum_η4]
      rw [← hdiv b]; exact sum_congr rfl fun _ _ => by ring
    rw [Hfun, e1, jet2_wave hf, Hjet_smul, ← Hsym,
      Hsym_lorentz η4_isSymm η4_mul_self k (Metric.transpose_trRev η4_isSymm hAs) hL, hk]
    ring

/-! ### Prop 2.6 and (2.15) for genuine plane-wave fields -/

/-- **Thesis Prop 2.6, corrected** (field level): with `ξ_b = B_b g(k·x)`, `g' = f`,
`B = Bcorr κ A`, the gauge-transformed field `h̄ - (2∂_(a ξ_b) - η_ab ∂·ξ)` is the TT plane
wave `ttAmp ((A₁₁ - A₂₂)/2) A₁₂ · f(k·x)`. Only `g` differentiable with `deriv g = f` is needed
(the thesis takes `g ∈ C³`); `κ ≠ 0` is explicit. Thesis: Prop 2.6 (corrected) -/
theorem tt_gauge_fun {κ : ℝ} (hκ : κ ≠ 0) {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : ∀ i j, A i j = A j i) (hker : ∀ a, ∑ b, A a b * raise (kTT κ) b = 0) {f g : ℝ → ℝ}
    (hg : Differentiable ℝ g) (hgf : deriv g = f) (y : Fin 4 → ℝ) :
    (Matrix.of fun a b => A a b * f (phaseL (kTT κ) y)) -
        gaugeTR η4 η4 (fun b z => Bcorr κ A b * g (phaseL (kTT κ) z)) y =
      Matrix.of fun a b => ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) a b * f (phaseL (kTT κ) y) := by
  rw [← (tt_gauge hκ hA hker).1]
  ext a b
  simp only [Matrix.sub_apply, of_apply, gaugeTR, partialDeriv_wave hg, hgf, gaugeAmp, dot_η4,
    sum_η4]
  have : ∑ c, Metric.minkowski4 ℝ c * (Bcorr κ A c * kTT κ c * f (phaseL (kTT κ) y)) =
      (∑ c, Metric.minkowski4 ℝ c * kTT κ c * Bcorr κ A c) * f (phaseL (kTT κ) y) := by
    rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

/-- **Thesis (2.15), corrected** (field level): for the TT plane wave
`h_ab = ttAmp A₊ Aₓ · f(k·x)` with `f ∈ C²`, `a¹ = (κ²/2)(A₊v¹ + Aₓv²) f''(k·x)` and
`a² = (κ²/2)(Aₓv¹ - A₊v²) f''(k·x)`. Thesis: (2.15) (corrected) -/
theorem tt_accel_fun (κ Ap Ax : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (v : Fin 4 → ℝ)
    (x : Fin 4 → ℝ) :
    let D := jet2 (fun y => Matrix.of fun a b => ttAmp Ap Ax a b * f (phaseL (kTT κ) y)) x
    let s := deriv (deriv f) (phaseL (kTT κ) x)
    accelJ D v 1 = κ ^ 2 / 2 * (Ap * v 1 + Ax * v 2) * s ∧
      accelJ D v 2 = κ ^ 2 / 2 * (Ax * v 1 - Ap * v 2) * s ∧
      accelJ D v 0 = 0 ∧ accelJ D v 3 = 0 := by
  intro D s
  have e : D = fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s := by
    simp only [D, jet2_wave hf]
    funext i j; ext a b
    simp only [Pi.smul_apply, Matrix.smul_apply, symbolJet_apply, smul_eq_mul, s]
    ring
  rw [e]
  exact tt_accel κ Ap Ax s v

/-! ### Prop 2.6: existence of the TT gauge -/

/-- The antiderivative `g(t) = ∫₀ᵗ f` used to build the gauge vector of Prop 2.6. -/
def antideriv (f : ℝ → ℝ) : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, f s

/-- FTC: `g' = f` for continuous `f`. -/
theorem deriv_antideriv {f : ℝ → ℝ} (hf : Continuous f) : deriv (antideriv f) = f :=
  funext fun t => Continuous.deriv_integral f hf 0 t

theorem differentiable_antideriv {f : ℝ → ℝ} (hf : Continuous f) :
    Differentiable ℝ (antideriv f) := fun t =>
  (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.differentiableAt

/-- If `f ∈ C²` then `g = ∫₀ f ∈ C³`. -/
theorem contDiff_antideriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 3 (antideriv f) := by
  have hc : Continuous f := hf.continuous
  exact (contDiff_succ_iff_deriv (𝕜 := ℝ) (f := antideriv f) (n := 2)).mpr
    ⟨differentiable_antideriv hc, by simp, by rw [deriv_antideriv hc]; exact hf⟩

/-- The gauge vector of Prop 2.6 (corrected): `ξ_b(z) = (Bcorr κ A)_b · g(k·z)`, `g = ∫₀ f`. -/
def ttGaugeVec (κ : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) (f : ℝ → ℝ) : Fin 4 → (Fin 4 → ℝ) → ℝ :=
  fun b z => Bcorr κ A b * antideriv f (phaseL (kTT κ) z)

theorem contDiff_ttGaugeVec (κ : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (b : Fin 4) : ContDiff ℝ 3 (ttGaugeVec κ A f b) :=
  contDiff_const.mul ((contDiff_antideriv hf).comp (phaseL (kTT κ)).contDiff)

theorem dot_kTT (κ : ℝ) : dot η4 (kTT κ) (kTT κ) = 0 := by
  simp [dot_η4, kTT, Fin.sum_univ_four, Metric.minkowski4]

/-- The gauge vector of Prop 2.6 is a residual gauge: `□ξ_b = 0` (`k` is null). -/
theorem box_ttGaugeVec (κ : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (b : Fin 4) (x : Fin 4 → ℝ) : box η4 (ttGaugeVec κ A f b) x = 0 := by
  have hc : Continuous f := hf.continuous
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have e : ∀ i, partialDeriv i (ttGaugeVec κ A f b) =
      fun y => (Bcorr κ A b * kTT κ i) * f (phaseL (kTT κ) y) := by
    intro i; funext y
    have := partialDeriv_wave (differentiable_antideriv hc) (Bcorr κ A b) (kTT κ) i y
    rw [deriv_antideriv hc] at this
    exact this
  simp only [box, e, partialDeriv_wave hd, sum_η4]
  have : ∑ i, Metric.minkowski4 ℝ i *
      (Bcorr κ A b * kTT κ i * kTT κ i * deriv f (phaseL (kTT κ) x)) =
      dot η4 (kTT κ) (kTT κ) * (Bcorr κ A b * deriv f (phaseL (kTT κ) x)) := by
    rw [dot_η4, sum_mul]; exact sum_congr rfl fun _ _ => by ring
  rw [this, dot_kTT, zero_mul]

/-- **Thesis Prop 2.6, repaired** (existence of the TT gauge for a plane wave): for `κ ≠ 0`,
`A` symmetric with `A_ab k^b = 0` and every `f ∈ C²` there are a `C³` gauge vector `ξ`
(explicitly `ttGaugeVec κ A f`, with minus the printed `B`) and an amplitude
`A' = ttAmp ((A₁₁ - A₂₂)/2) A₁₂` satisfying the TT conditions (2.12) such that
`h̄ - (2∂_(a ξ_b) - η_ab ∂^c ξ_c) = A' f(k·x)`; the new field is a plane-wave solution of
Prop 2.5 (`□h̄' = 0`, `∂^a h̄'_ab = 0`, `H(trRev h̄') = 0`). Thesis: Prop 2.6 (corrected) -/
theorem exists_ttGauge {κ : ℝ} (hκ : κ ≠ 0) {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : ∀ i j, A i j = A j i) (hker : ∀ a, ∑ b, A a b * raise (kTT κ) b = 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) :
    ∃ ξ : Fin 4 → (Fin 4 → ℝ) → ℝ, ξ = ttGaugeVec κ A f ∧ (∀ a, ContDiff ℝ 3 (ξ a)) ∧
      ∃ A' : Matrix (Fin 4) (Fin 4) ℝ, IsTT κ A' ∧ A' = ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) ∧
        (∀ y, (Matrix.of fun a b => A a b * f (phaseL (kTT κ) y)) - gaugeTR η4 η4 ξ y =
          Matrix.of fun a b => A' a b * f (phaseL (kTT κ) y)) ∧
        (∀ x a b, box η4 (fun y => A' a b * f (phaseL (kTT κ) y)) x = 0) ∧
        (∀ x b, divF η4 (fun y => Matrix.of fun a b => A' a b * f (phaseL (kTT κ) y)) x b = 0) ∧
        (∀ x b d, Hfun η4 η4 (fun y => Metric.trRev η4 η4
          (Matrix.of fun a b => A' a b * f (phaseL (kTT κ) y))) x b d = 0) := by
  have hc : Continuous f := hf.continuous
  have hTT := tt_gauge hκ hA hker
  have hIs : IsTT κ (ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2)) := hTT.1 ▸ hTT.2
  obtain ⟨hbox, hdiv, hH⟩ := plane_wave (dot_kTT κ) hIs.symm hIs.lorentz hf
  refine ⟨_, rfl, contDiff_ttGaugeVec κ A hf, _, hIs, rfl, fun y => ?_, hbox, hdiv, hH⟩
  exact tt_gauge_fun hκ hA hker (differentiable_antideriv hc) (deriv_antideriv hc) y

/-- **Thesis Prop 2.6, repaired**, on the metric perturbation `h = trRev h̄` (the gauge freedom
`h ↦ h - 2∂_(a ξ_b)` of (2.5)): with the gauge vector of `exists_ttGauge`, the trace reversal
of `h - ∂_a ξ_b - ∂_b ξ_a` is the TT plane wave `ttAmp ((A₁₁ - A₂₂)/2) A₁₂ · f(k·x)`.
Thesis: Prop 2.6 (corrected), (2.5) -/
theorem trRev_sub_gauge_eq_ttAmp {κ : ℝ} (hκ : κ ≠ 0) {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : ∀ i j, A i j = A j i) (hker : ∀ a, ∑ b, A a b * raise (kTT κ) b = 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (y : Fin 4 → ℝ) :
    let ξ := ttGaugeVec κ A f
    let h : Matrix (Fin 4) (Fin 4) ℝ :=
      Metric.trRev η4 η4 (Matrix.of fun a b => A a b * f (phaseL (kTT κ) y))
    Metric.trRev η4 η4 (Matrix.of fun a b => h a b - partialDeriv a (ξ b) y -
      partialDeriv b (ξ a) y) =
      Matrix.of fun a b => ttAmp ((A 1 1 - A 2 2) / 2) (A 1 2) a b * f (phaseL (kTT κ) y) := by
  intro ξ h
  have hc : Continuous f := hf.continuous
  have e := tt_gauge_fun hκ hA hker (differentiable_antideriv hc) (deriv_antideriv hc) y
  have h1 : (Matrix.of fun a b => h a b - partialDeriv a (ξ b) y - partialDeriv b (ξ a) y) =
      h + (Matrix.of fun a b => -partialDeriv a (ξ b) y) +
        (Matrix.of fun a b => -partialDeriv a (ξ b) y)ᵀ := by
    ext a b; simp only [of_apply, Matrix.add_apply, transpose_apply]; ring
  rw [h1, Metric.trRev_add_sym (gi := η4) η4_isSymm,
    Metric.trRev_trRev η4_isSymm η4_mul_self (by simp), ← e]
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, of_apply, transpose_apply, gaugeTR,
    Matrix.smul_apply, smul_eq_mul, Metric.trace, sum_η4, ξ, sum_neg_distrib, mul_neg]
  simp only [show ∀ b, ttGaugeVec κ A f b = fun z => Bcorr κ A b * antideriv f (phaseL (kTT κ) z)
    from fun b => rfl]
  ring

end Feec.LinearizedGravity
