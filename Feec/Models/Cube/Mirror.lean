module

public import Feec.Models.Cube.MirrorBase
public import Feec.Models.Cube.MirrorExt
public import Feec.Models.Torus.GradCurl
public import Feec.Models.BoundedDomain.GradCurl
public import Feec.Domain.Affine
public import Feec.HilbertComplex.RestrictScalars

/-!
# The cube with tensorial mirror boundary conditions: TSD data propagate

With the thesis' row-wise boundary conditions only stationary TSD data propagate on the cube
(`Feec.Models.Cube.Parity`, `Feec.Models.Cube.Static`): row-wise conditions give `E_{ab}` and
`E_{ba}` different parities. The **mirror conditions** let the reflection `x_k ↦ -x_k` of the
torus `𝕋³` act on vectors by `D_k = diag(s_k)` and on matrices by `M ↦ ± D_k M D_k`
(`s_k(a) = -1` if `a = k`, `1` otherwise). On the Fourier side of the torus grad–curl complex
`Feec.Models.Torus.GradCurl.complex` these are the fibre symmetries `n ↦ flip_k n`,
`v ↦ D_k v`, `E ↦ D_k E D_k`, `B ↦ -D_k B D_k` (`symmetries`): the symbols intertwine
(`grad_flip`, `curl_flip`), and the TSD fibres are permuted (`matR_mem_tsd`). So the torus
constraint `{0} × L²(TSD) × L²(TSD)` is invariant under the generated action of `(ℤ/2)³` and
descends to every complex built from the fixed fields (`Feec.HilbertComplex.Action`,
`Feec.HilbertComplex.ScaledEmbedding.reducingSubcomplex_comap`). Constraint propagation,
existence and uniqueness, and `K* = K` follow from the general theorems
(`Feec.HilbertComplex.ReducingSubcomplex.propagates`, `.existsUnique_mem`, `.invariantCore_eq`).

Three realizations are treated, over `ℂ`:

* the **parity model** `Mirror.complex`: the subcomplex of the torus complex fixed by the mirror
  action (the method of images);
* the **cube `Q = (0, ½)³`** `Mirror.complexQ`: genuine fields
  `L²(Q; ℂ³) → L²(Q; ℂ³ˣ³) → L²(Q; ℂ³ˣ³)`, the compression of the torus complex along the mirror
  extensions (`Mirror.J`, `Feec.Models.Cube.MirrorExt.extF`; a scaled embedding with scale `8`,
  `Mirror.embeddingQ`). Its differentials are the weak gradient and curl on `Q`, between the
  minimal and the maximal realizations (`Feec.Models.Cube.MirrorDirichlet`); the boundary
  conditions are `σ · n = 0` and `E_{nτ} = 0` (encoded by the parities), the constraint is
  `{0} × TSD × TSD` with the wall conditions `E_{τn} = 0`, `B_{nn} = 0` (`Mirror.tsdQ`,
  `Mirror.mem_tsdQ_one`);
* **every open cube** `∏ (bᵢ, bᵢ + s)` (`Mirror.complexCube`), the transport of `complexQ` along
  the pull-back by `x ↦ (x - b)/(2s)` (`Feec.Domain.pullF`, chain-rule factor `(2s)⁻¹`).

A non-stationary TSD datum, `E₀ = 2 cos(2π x₃) diag(1, -1, 0)`, shows that the constraint has
dynamical content in every realization (`Mirror.exists_nonstationary`, `_Q`, `_Cube`).

## Main definitions

* `Mirror.symmetries`, `Mirror.action`, `Mirror.complex`, `Mirror.constraint`.
* `Mirror.J`, `Mirror.complexQ`, `Mirror.embeddingQ`, `Mirror.tsdQ`.
* `Mirror.complexCube`, `Mirror.embeddingCube`, `Mirror.tsdCube`.

## Main results

* **`Mirror.reducingSubcomplex`**, `Mirror.propagates`, `Mirror.existsUnique_mem`,
  `Mirror.invariantCore_eq`, `Mirror.exists_nonstationary`.
* **`Mirror.reducingSubcomplexQ`**, `Mirror.propagatesQ`, `Mirror.existsUnique_memQ`,
  `Mirror.invariantCore_eqQ`, `Mirror.exists_nonstationaryQ`; `Mirror.range_J`
  (the mirror extensions are onto the fixed fields).
* **`Mirror.reducingSubcomplexCube`**, `Mirror.propagatesCube`, `Mirror.existsUnique_memCube`,
  `Mirror.invariantCore_eqCube`, `Mirror.exists_nonstationaryCube`, and the cases `(0, π)³`,
  `(0, 1)³`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17, (4.14), (4.15)); Ch. 7 (the unit cube)
* [Brezis2011], §9.2 (extension by reflection)
-/

open scoped InnerProductSpace
open Set LinearPMap MeasureTheory

@[expose] public noncomputable section

namespace Feec.Models.Cube.Mirror

open Feec.Fourier Feec.Fourier.GradCurl Feec.ShortHilbertComplex Feec.Models.Cube.MirrorExt
open Feec.HilbertComplex (ScaledEmbedding totalSub ReducingSubcomplex)

/-! ### Signs -/

/-- The sign `s_k(a)`: `-1` if `a = k`, `1` otherwise. -/
def sgn (k a : Fin 3) : ℂ := if a = k then -1 else 1

theorem sgn_mul_self (k a : Fin 3) : sgn k a * sgn k a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem conj_sgn (k a : Fin 3) : (starRingEnd ℂ) (sgn k a) = sgn k a := by
  unfold sgn; split_ifs <;> simp

/-- `ε_{bcd} s_c s_d = -s_b ε_{bcd}` (`det D_k = -1`). -/
theorem leviCivita3_sgn (k b c d : Fin 3) :
    leviCivita3 ℂ b c d * (sgn k c * sgn k d) = -(sgn k b * leviCivita3 ℂ b c d) := by
  fin_cases k <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [sgn, leviCivita3_apply]

theorem freq_flipAt (k : Fin 3) (n : Fin 3 → ℤ) (a : Fin 3) :
    ((Fourier.Torus.freq (flipAt k n) a : ℝ) : ℂ) = sgn k a * (Fourier.Torus.freq n a : ℂ) := by
  simp only [Fourier.Torus.freq_apply, flipAt_apply, sgn]
  split_ifs <;> push_cast <;> ring

/-- The parity of the component `σ_a` of a mirror vector in `x_k`: `s_k(a)` (`σ · n = 0`). -/
def cV (a k : Fin 3) : ℂ := sgn k a

/-- The parity of the entry `E_{ab}` of a mirror tensor in `x_k`: `s_k(a) s_k(b)`
(`E_{nτ} = 0`). -/
def cE (p : Fin 3 × Fin 3) (k : Fin 3) : ℂ := sgn k p.1 * sgn k p.2

/-- The parity of the entry `B_{ab}` of a mirror pseudo-tensor in `x_k`: `-s_k(a) s_k(b)`. -/
def cB (p : Fin 3 × Fin 3) (k : Fin 3) : ℂ := -(sgn k p.1 * sgn k p.2)

theorem cV_sq (a k : Fin 3) : cV a k * cV a k = 1 := sgn_mul_self k a

theorem cE_sq (p : Fin 3 × Fin 3) (k : Fin 3) : cE p k * cE p k = 1 := by
  simp only [cE]
  linear_combination (sgn k p.2 * sgn k p.2) * sgn_mul_self k p.1 + sgn_mul_self k p.2

theorem cB_sq (p : Fin 3 × Fin 3) (k : Fin 3) : cB p k * cB p k = 1 := by
  rw [cB, neg_mul_neg]; exact cE_sq p k

theorem conj_cV (a k : Fin 3) : (starRingEnd ℂ) (cV a k) = cV a k := conj_sgn k a

theorem conj_cE (p : Fin 3 × Fin 3) (k : Fin 3) : (starRingEnd ℂ) (cE p k) = cE p k := by
  simp [cE, conj_sgn]

theorem conj_cB (p : Fin 3 × Fin 3) (k : Fin 3) : (starRingEnd ℂ) (cB p k) = cB p k := by
  simp [cB, conj_sgn]

/-! ### The mirror symmetries of the torus complex -/

theorem grad_flip (k : Fin 3) (n : Fin 3 → ℤ) (v : Vec) :
    grad (Fourier.Torus.freq (flipAt k n)) (sgnCLM (Fin 3) (fun a => cV a k) v) =
      sgnCLM (Fin 3 × Fin 3) (fun p => cE p k) (grad (Fourier.Torus.freq n) v) := by
  ext ⟨a, b⟩
  rw [grad_apply, sgnCLM_apply, sgnCLM_apply, grad_apply, freq_flipAt]
  simp only [cV, cE]
  ring

theorem curl_flip (k : Fin 3) (n : Fin 3 → ℤ) (M : Mat) :
    curl (Fourier.Torus.freq (flipAt k n)) (sgnCLM (Fin 3 × Fin 3) (fun p => cE p k) M) =
      sgnCLM (Fin 3 × Fin 3) (fun p => cB p k) (curl (Fourier.Torus.freq n) M) := by
  ext ⟨a, b⟩
  rw [sgnCLM_apply, curl_apply, curl_apply]
  simp only [sgnCLM_apply, freq_flipAt, Finset.mul_sum, cE, cB]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  linear_combination (Complex.I * sgn k a * (Fourier.Torus.freq n c : ℂ) * M (a, d)) *
    leviCivita3_sgn k b c d

/-- The TSD fibres are permuted by the reflections. -/
theorem matR_mem_tsd (k : Fin 3) (n : Fin 3 → ℤ) {s : Fin 3 × Fin 3 → ℂ}
    (hs : ∀ p, s p = s (p.2, p.1)) (hd : ∀ a, s (a, a) = s (0, 0))
    (hsgn : ∀ p, s p = s (0, 0) * (sgn k p.1 * sgn k p.2)) {M : Mat}
    (hM : M ∈ tsd (Fourier.Torus.freq (flipAt k n))) :
    sgnCLM (Fin 3 × Fin 3) s M ∈ tsd (Fourier.Torus.freq n) := by
  obtain ⟨h1, h2, h3⟩ := mem_tsd.1 hM
  refine mem_tsd.2 ⟨?_, ?_, ?_⟩
  · ext a b
    have := congrFun (congrFun h1 a) b
    simp only [Matrix.transpose_apply, toMatrix_apply] at this ⊢
    rw [sgnCLM_apply, sgnCLM_apply, this, hs (b, a)]
  · have e : (toMatrix (sgnCLM (Fin 3 × Fin 3) s M)).trace = s (0, 0) * (toMatrix M).trace := by
      simp only [Matrix.trace, Matrix.diag, toMatrix_apply, sgnCLM_apply, hd, Finset.mul_sum]
    rw [e, h2, mul_zero]
  · ext a
    have := congrFun h3 a
    simp only [Matrix.mulVec, dotProduct, toMatrix_apply, cfreq, Pi.zero_apply] at this ⊢
    simp only [freq_flipAt] at this
    rw [show (∑ b, sgnCLM (Fin 3 × Fin 3) s M (a, b) * (Fourier.Torus.freq n b : ℂ)) =
        s (0, 0) * sgn k a * ∑ b, M (a, b) * (sgn k b * (Fourier.Torus.freq n b : ℂ)) by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [sgnCLM_apply, hsgn]; ring, this, mul_zero]

/-- The fibre maps of the `k`-th reflection on the three spaces. -/
def fib (k : Fin 3) : ∀ i : Fin 3, W3 Vec Mat Mat i →L[ℂ] W3 Vec Mat Mat i
  | 0 => sgnCLM (Fin 3) fun a => cV a k
  | 1 => sgnCLM (Fin 3 × Fin 3) fun p => cE p k
  | 2 => sgnCLM (Fin 3 × Fin 3) fun p => cB p k

/-- **The tensorial reflections of the torus grad–curl complex**, as fibre symmetries. -/
def symmetries : (Fourier.Torus.symbolComplex gradCurl).Symmetries (Fin 3) where
  R := flipRefl
  ρ := fib
  invol k i v := by
    fin_cases i
    · exact sgnCLM_sgnCLM (fun a => cV_sq a k) v
    · exact sgnCLM_sgnCLM (fun p => cE_sq p k) v
    · exact sgnCLM_sgnCLM (fun p => cB_sq p k) v
  inner_ρ k i v w := by
    fin_cases i
    · exact inner_sgnCLM (fun a => cV_sq a k) (fun a => conj_cV a k) v w
    · exact inner_sgnCLM (fun p => cE_sq p k) (fun p => conj_cE p k) v w
    · exact inner_sgnCLM (fun p => cB_sq p k) (fun p => conj_cB p k) v w
  symm k i j n v := by
    change gradCurl.m i j (Fourier.Torus.freq (flipAt k n)) (fib k i v) =
      fib k j (gradCurl.m i j _ v)
    fin_cases i <;> fin_cases j
    all_goals first
      | (change (0 : _ →L[ℂ] _) _ = fib k _ ((0 : _ →L[ℂ] _) v); simp)
      | exact grad_flip k n v
      | exact curl_flip k n v
  comm_σ k l n := flipAt_comm k l n
  comm_ρ k l i v := by
    fin_cases i <;> exact sgnCLM_comm _ _ v

/-- **The mirror action of `(ℤ/2)³`** on the torus grad–curl complex. -/
abbrev action : Models.Torus.GradCurl.complex.Action (Multiplicative (Fin 3 → ZMod 2)) :=
  symmetries.toAction

/-- **The mirror cube complex** (parity model): the fields of the torus complex with the mirror
parities, i.e. the fixed complex of `action` (method of images). -/
abbrev complex := action.fixedComplex

/-- The fields with the mirror parities are those fixed by each reflection. -/
theorem mem_fixed_iff {i : Fin 3} {x : Models.Torus.GradCurl.Space i} :
    x ∈ action.fixed i ↔ ∀ k, symLp (symmetries.R k) (fib k i) x = x :=
  symmetries.mem_fixed_toAction

/-- The fixed vector fields are the coefficient sequences with the parities `cV`. -/
theorem mem_fixed_zero {x : Models.Torus.GradCurl.Space 0} :
    x ∈ action.fixed 0 ↔ x ∈ fieldParity cV :=
  mem_fixed_iff.trans (mem_fieldParity_iff_symLp cV_sq).symm

/-- The fixed matrix fields of the second slot have the tensor parities `cE`. -/
theorem mem_fixed_one {x : Models.Torus.GradCurl.Space 1} :
    x ∈ action.fixed 1 ↔ x ∈ fieldParity cE :=
  mem_fixed_iff.trans (mem_fieldParity_iff_symLp cE_sq).symm

/-- The fixed matrix fields of the third slot have the pseudo-tensor parities `cB`. -/
theorem mem_fixed_two {x : Models.Torus.GradCurl.Space 2} :
    x ∈ action.fixed 2 ↔ x ∈ fieldParity cB :=
  mem_fixed_iff.trans (mem_fieldParity_iff_symLp cB_sq).symm

/-- The TSD constraint fibres are permuted by the reflections. -/
theorem fib_mem_tsdK (k i : Fin 3) (n : Fin 3 → ℤ) {v : W3 Vec Mat Mat i}
    (hv : v ∈ tsdK i (Fourier.Torus.freq (flipAt k n))) :
    fib k i v ∈ tsdK i (Fourier.Torus.freq n) := by
  fin_cases i
  · have h0 : (v : Vec) = 0 := (Submodule.mem_bot ℂ).1 hv
    change sgnCLM (Fin 3) (fun a => cV a k) v ∈ (⊥ : Submodule ℂ Vec)
    have h1 : sgnCLM (Fin 3) (fun a => cV a k) (v : Vec) = 0 := by
      rw [h0]; exact (sgnCLM (Fin 3) fun a => cV a k).map_zero
    rw [h1]
    exact Submodule.zero_mem _
  · exact matR_mem_tsd k n (s := fun p => cE p k) (fun p => by simp only [cE]; ring)
      (fun a => by simp only [cE, sgn_mul_self]) (fun p => by simp only [cE, sgn_mul_self]; ring) hv
  · exact matR_mem_tsd k n (s := fun p => cB p k) (fun p => by simp only [cB]; ring)
      (fun a => by simp only [cB, sgn_mul_self]) (fun p => by simp only [cB, sgn_mul_self]; ring) hv

/-- The mirror action preserves the TSD constraint `{0} × L²(TSD) × L²(TSD)`. -/
theorem act_mem_constraint (g : Multiplicative (Fin 3 → ZMod 2)) (i : Fin 3)
    {x : Models.Torus.GradCurl.Space i} (hx : x ∈ Models.Torus.GradCurl.constraint i) :
    action.act g i x ∈ Models.Torus.GradCurl.constraint i :=
  symmetries.act_mem_fibreSub (K := fun i n => tsdK i (Fourier.Torus.freq n))
    (fun k i n _ hv => fib_mem_tsdK k i n hv) g i hx

/-- The TSD constraint of the mirror cube complex. -/
abbrev constraint (i : Fin 3) : Submodule ℂ (action.fixed i) :=
  (Models.Torus.GradCurl.constraint i).comap (action.fixed i).subtype

/-- **The TSD constraint reduces the mirror cube complex** (the projection hypothesis of
Prop 4.17 holds with mirror boundary conditions).
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem reducingSubcomplex : complex.ReducingSubcomplex constraint :=
  action.reducingSubcomplex_comap_fixed Models.Torus.GradCurl.reducingSubcomplex
    act_mem_constraint

/-- **Prop 4.17 on the cube with mirror boundary conditions** (parity model, any time interval,
with forcing): TSD data and forcing give strong solutions that stay TSD.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem propagates {a b : ℝ} {F U : ℝ → PiLp 2 fun i => action.fixed i}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ totalSub constraint) (hF : ∀ t ∈ Icc a b, F t ∈ totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ totalSub constraint :=
  reducingSubcomplex.propagates hU h0 hF

/-- Prop 4.17 on the mirror cube with existence and uniqueness (parity model).
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem existsUnique_mem {U₀ : PiLp 2 fun i => action.fixed i} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀K : U₀ ∈ totalSub constraint) {F : ℝ → PiLp 2 fun i => action.fixed i} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFK : ∀ t ∈ Icc a b, F t ∈ totalSub constraint) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub constraint) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  reducingSubcomplex.existsUnique_mem hU₀ hU₀K hF hFK

/-- `K* = K` on the mirror cube (parity model): the constraint is its own invariant core.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem invariantCore_eq :
    complex.waveGroup.invariantCore (totalSub constraint) = totalSub constraint :=
  reducingSubcomplex.invariantCore_eq

/-! ### A non-stationary TSD datum -/

/-- The frequency `k₀ = (0, 0, 1)`. -/
def k0 : Fin 3 → ℤ := ![0, 0, 1]

/-- `diag(1, -1, 0)`. -/
def M0 : Mat := WithLp.toLp 2 fun p =>
  if p.1 = p.2 then (if p.1 = 0 then 1 else if p.1 = 1 then -1 else 0) else 0

theorem M0_apply (p : Fin 3 × Fin 3) :
    M0 p = if p.1 = p.2 then (if p.1 = 0 then 1 else if p.1 = 1 then -1 else 0) else 0 := rfl

/-- The coefficients `±k₀ ↦ diag(1, -1, 0)` of `2 cos(2π x₃) diag(1, -1, 0)`. -/
def cosCoeff (n : Fin 3 → ℤ) : Mat := if n = k0 ∨ n = -k0 then M0 else 0

theorem cosCoeff_eq_zero {n : Fin 3 → ℤ} (hn : n ∉ ({k0, -k0} : Finset (Fin 3 → ℤ))) :
    cosCoeff n = 0 := by
  have : ¬(n = k0 ∨ n = -k0) := by simpa using hn
  simp [cosCoeff, this]

theorem memLp_cosCoeff : MemLp cosCoeff 2 (Measure.count : Measure (Fin 3 → ℤ)) :=
  memLp_count_of_finite _ fun _ hn => cosCoeff_eq_zero hn

/-- **The electric datum** `E₀ = 2 cos(2π x₃) diag(1, -1, 0)` (Fourier side). -/
def cosE : Lp Mat 2 (Measure.count : Measure (Fin 3 → ℤ)) := memLp_cosCoeff.toLp cosCoeff

theorem coe_cosE (n : Fin 3 → ℤ) : (cosE : (Fin 3 → ℤ) → Mat) n = cosCoeff n :=
  Measure.ae_count_iff.1 memLp_cosCoeff.coeFn_toLp n

theorem flipAt_neg (k : Fin 3) (n : Fin 3 → ℤ) : flipAt k (-n) = -flipAt k n := by
  funext j; simp only [flipAt_apply, Pi.neg_apply]; split_ifs <;> rfl

theorem flipAt_mem_k0 (k : Fin 3) (n : Fin 3 → ℤ) :
    (flipAt k n = k0 ∨ flipAt k n = -k0) ↔ (n = k0 ∨ n = -k0) := by
  have inj : ∀ a b, flipAt k a = flipAt k b ↔ a = b := fun a b =>
    ⟨fun h => by simpa using congrArg (flipAt k) h, fun h => h ▸ rfl⟩
  have hk0 : flipAt k k0 = k0 ∨ flipAt k k0 = -k0 := by
    fin_cases k
    · left; funext j; fin_cases j <;> simp [flipAt_apply, k0]
    · left; funext j; fin_cases j <;> simp [flipAt_apply, k0]
    · right; funext j; fin_cases j <;> simp [flipAt_apply, k0]
  constructor
  · rintro (h | h) <;> rcases hk0 with e | e
    · left; rw [← inj, h, e]
    · right; rw [← inj, h, flipAt_neg, e, neg_neg]
    · right; rw [← inj, h, flipAt_neg, e]
    · left; rw [← inj, h, e]
  · rintro (h | h) <;> subst h <;> rcases hk0 with e | e
    · left; exact e
    · right; exact e
    · right; rw [flipAt_neg, e]
    · left; rw [flipAt_neg, e, neg_neg]

theorem cosE_mem_fieldParity : cosE ∈ fieldParity cE := by
  refine mem_fieldParity_iff.2 fun k n p => ?_
  rw [coe_cosE, coe_cosE]
  unfold cosCoeff
  by_cases h : n = k0 ∨ n = -k0
  · rw [show (if flipAt k n = k0 ∨ flipAt k n = -k0 then M0 else 0) = M0 from
      ite_eq_left ((flipAt_mem_k0 k n).2 h), show (if n = k0 ∨ n = -k0 then M0 else 0) = M0 from
      ite_eq_left h]
    by_cases hp : p.1 = p.2
    · have hc : cE p k = 1 := by simp only [cE, hp, sgn_mul_self]
      rw [hc, one_mul]
    · rw [M0_apply, ite_eq_right hp, mul_zero]
  · rw [show (if flipAt k n = k0 ∨ flipAt k n = -k0 then M0 else 0) = 0 from
      ite_eq_right fun h' => h ((flipAt_mem_k0 k n).1 h'),
      show (if n = k0 ∨ n = -k0 then M0 else 0) = 0 from ite_eq_right h]
    simp

theorem cosE_mem_fixed : cosE ∈ action.fixed 1 := mem_fixed_one.2 cosE_mem_fieldParity

theorem M0_mem_tsd {n : Fin 3 → ℤ} (hn : n = k0 ∨ n = -k0) :
    M0 ∈ tsd (Fourier.Torus.freq n) := by
  have h0 : n 0 = 0 ∧ n 1 = 0 := by
    rcases hn with rfl | rfl <;> simp [k0]
  refine mem_tsd.2 ⟨?_, ?_, ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, toMatrix_apply, M0_apply]
    split_ifs <;> simp_all
  · simp [Matrix.trace, toMatrix_apply, M0_apply, Fin.sum_univ_three]
  · ext a
    simp only [Matrix.mulVec, dotProduct, toMatrix_apply, M0_apply, cfreq, Fin.sum_univ_three,
      Pi.zero_apply]
    fin_cases a <;> simp [Fourier.Torus.freq_apply, h0.1, h0.2]

theorem cosE_mem_constraint : cosE ∈ Models.Torus.GradCurl.constraint 1 := by
  refine Operator.mem_fibreSub.2 (Measure.ae_count_iff.2 fun n => ?_)
  change (cosE : (Fin 3 → ℤ) → Mat) n ∈ tsd (Fourier.Torus.freq n)
  rw [coe_cosE]
  unfold cosCoeff
  split_ifs with h
  · exact M0_mem_tsd h
  · exact Submodule.zero_mem _

/-- `curl (2 cos(2π x₃) diag(1, -1, 0)) ≠ 0`: the `(0, 1)` entry of `curl_{ξ(k₀)} M₀` is
`2π i`. -/
theorem curl_M0_ne : curl (Fourier.Torus.freq k0) M0 ≠ 0 := by
  intro h
  have := congrArg (fun M : Mat => M (0, 1)) h
  simp only [curl_apply, Fin.sum_univ_three, leviCivita3_apply, M0_apply,
    Fourier.Torus.freq_apply, k0] at this
  norm_num [Real.pi_ne_zero, Complex.I_ne_zero] at this

theorem cosE_mem_domain : cosE ∈ (Models.Torus.GradCurl.complex.d 1 2).domain :=
  mem_mulDomain_of_finite _ {k0, -k0} fun _ hn => (coe_cosE _).trans (cosCoeff_eq_zero hn)

theorem cosE_mem_adjoint_domain : cosE ∈ ((Models.Torus.GradCurl.complex.d 0 1)†).domain := by
  rw [show (Models.Torus.GradCurl.complex.d 0 1)† = Operator.mulOp Measure.count fun n =>
      ContinuousLinearMap.adjoint (gradCurl.m 0 1 (Fourier.Torus.freq n)) from
    (Fourier.Torus.symbolComplex gradCurl).adjoint_d 0 1]
  exact mem_mulDomain_of_finite _ {k0, -k0} fun _ hn => (coe_cosE _).trans (cosCoeff_eq_zero hn)

/-- The datum `(0, E₀, 0)` on the torus. -/
def cosState : PiLp 2 Models.Torus.GradCurl.Space := WithLp.toLp 2 (Pi.single 1 cosE)

theorem cosState_zero : cosState 0 = 0 :=
  Pi.single_eq_of_ne (M := Models.Torus.GradCurl.Space) (by decide : (0 : Fin 3) ≠ 1) cosE
theorem cosState_one : cosState 1 = cosE :=
  Pi.single_eq_same (M := Models.Torus.GradCurl.Space) (1 : Fin 3) cosE
theorem cosState_two : cosState 2 = 0 :=
  Pi.single_eq_of_ne (M := Models.Torus.GradCurl.Space) (by decide : (2 : Fin 3) ≠ 1) cosE

theorem cosState_mem_domain : cosState ∈ Models.Torus.GradCurl.complex.wave.domain :=
  HilbertComplex.mem_wave_domain_fin3 _
    (by rw [cosState_zero]; exact Submodule.zero_mem _)
    (by rw [cosState_one]; exact cosE_mem_domain)
    (by rw [cosState_one]; exact cosE_mem_adjoint_domain)
    (by rw [cosState_two]; exact Submodule.zero_mem _)

theorem curl_cosE_apply :
    ((Models.Torus.GradCurl.complex.d 1 2 ⟨cosE, cosE_mem_domain⟩ :
      Lp Mat 2 (Measure.count : Measure (Fin 3 → ℤ))) : (Fin 3 → ℤ) → Mat) k0 =
      curl (Fourier.Torus.freq k0) M0 := by
  refine (Operator.coeFn_mulOp_count (fun n => gradCurl.m 1 2 (Fourier.Torus.freq n))
    ⟨cosE, cosE_mem_domain⟩ k0).trans ?_
  change curl (Fourier.Torus.freq k0) ((cosE : (Fin 3 → ℤ) → Mat) k0) = _
  rw [coe_cosE]
  simp [cosCoeff]

/-- **`L (0, E₀, 0) ≠ 0`**: its `B`-component is `curl E₀ ≠ 0`. -/
theorem wave_cosState_ne :
    Models.Torus.GradCurl.complex.wave ⟨cosState, cosState_mem_domain⟩ ≠ 0 := by
  intro h
  have h2 := congrArg (fun y : PiLp 2 Models.Torus.GradCurl.Space => y 2) h
  rw [HilbertComplex.wave_apply_fin3_two] at h2
  have h3 : Models.Torus.GradCurl.complex.d 1 2 ⟨cosE, cosE_mem_domain⟩ = 0 :=
    (apply_congr' _ _ _ cosState_one.symm).trans h2
  apply curl_M0_ne
  rw [← curl_cosE_apply, h3]
  exact Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) k0

theorem cosState_mem_fixed (i : Fin 3) : cosState i ∈ action.fixed i := by
  fin_cases i
  · change cosState 0 ∈ _; rw [cosState_zero]; exact Submodule.zero_mem _
  · change cosState 1 ∈ _; rw [cosState_one]; exact cosE_mem_fixed
  · change cosState 2 ∈ _; rw [cosState_two]; exact Submodule.zero_mem _

theorem cosState_mem_constraint (i : Fin 3) :
    cosState i ∈ Models.Torus.GradCurl.constraint i := by
  fin_cases i
  · change cosState 0 ∈ _; rw [cosState_zero]; exact Submodule.zero_mem _
  · change cosState 1 ∈ _; rw [cosState_one]; exact cosE_mem_constraint
  · change cosState 2 ∈ _; rw [cosState_two]; exact Submodule.zero_mem _

/-- The cos datum in the mirror cube complex. -/
def cosStateFixed : PiLp 2 fun i => action.fixed i :=
  WithLp.toLp 2 fun i => ⟨cosState i, cosState_mem_fixed i⟩

/-- **A non-stationary TSD datum propagates on the mirror cube** (parity model):
`(0, 2 cos(2π x₃) diag(1, -1, 0), 0)` lies in `D(L) ∩ K` and is not stationary.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem exists_nonstationary :
    ∃ y ∈ complex.wave.domain, y ∈ totalSub constraint ∧ y ∉ complex.waveGroup.stationary := by
  obtain ⟨h1, h2⟩ := action.reducingSubcomplex_fixed.not_mem_stationary
    (y := cosStateFixed) cosState_mem_domain wave_cosState_ne
  exact ⟨cosStateFixed, h1, fun i => cosState_mem_constraint i, h2⟩

/-! ### The cube `Q = (0, ½)³` -/

open Geometry (Q)

/-- `L²(Q; ℂ³)`. -/
abbrev VQ : Type := Domain.L2F ℂ (Q (Fin 3)) (Fin 3)

/-- `L²(Q; ℂ³ˣ³)`. -/
abbrev MQ : Type := Domain.L2F ℂ (Q (Fin 3)) (Fin 3 × Fin 3)

/-- The spaces `L²(Q; ℂ³)`, `L²(Q; ℂ³ˣ³)`, `L²(Q; ℂ³ˣ³)` of the mirror complex on `Q`. -/
abbrev SpaceQ (i : Fin 3) : Type := W3 VQ MQ MQ i

/-- **The mirror extensions** `L²(Q) → ℓ²(ℤ³)`: `σ_a` extended with parity `s_k(a)`, `E_{ab}`
with `s_k(a) s_k(b)`, `B_{ab}` with `-s_k(a) s_k(b)` in `x_k`, then Fourier coefficients. -/
def J : ∀ i : Fin 3, SpaceQ i →L[ℂ] Models.Torus.GradCurl.Space i
  | 0 => extF (c := cV) cV_sq
  | 1 => extF (c := cE) cE_sq
  | 2 => extF (c := cB) cB_sq

theorem two_pow_card : ((2 ^ Fintype.card (Fin 3) : ℝ) : ℂ) = ((8 : ℝ) : ℂ) := by
  norm_num [Fintype.card_fin]

/-- **The mirror extensions multiply inner products by `8`.** -/
theorem inner_J (i : Fin 3) (x y : SpaceQ i) :
    ⟪J i x, J i y⟫_ℂ = ((8 : ℝ) : ℂ) * ⟪x, y⟫_ℂ := by
  fin_cases i
  · exact (inner_extF cV_sq x y).trans (by rw [two_pow_card]; rfl)
  · exact (inner_extF cE_sq x y).trans (by rw [two_pow_card]; rfl)
  · exact (inner_extF cB_sq x y).trans (by rw [two_pow_card]; rfl)

theorem eight_pos : (0 : ℝ) < 8 := by norm_num

/-- **The mirror extensions are onto the fields with the mirror parities.** -/
theorem range_J (i : Fin 3) :
    LinearMap.range (J i : SpaceQ i →ₗ[ℂ] Models.Torus.GradCurl.Space i) = action.fixed i := by
  ext x
  fin_cases i
  · constructor
    · rintro ⟨y, rfl⟩; exact mem_fixed_zero.2 (extF_mem cV_sq y)
    · intro hx; exact ⟨_, extF_resQF cV_sq (mem_fixed_zero.1 hx)⟩
  · constructor
    · rintro ⟨y, rfl⟩; exact mem_fixed_one.2 (extF_mem cE_sq y)
    · intro hx; exact ⟨_, extF_resQF cE_sq (mem_fixed_one.1 hx)⟩
  · constructor
    · rintro ⟨y, rfl⟩; exact mem_fixed_two.2 (extF_mem cB_sq y)
    · intro hx; exact ⟨_, extF_resQF cB_sq (mem_fixed_two.1 hx)⟩

instance (i : Fin 3) : (LinearMap.range
    (J i : SpaceQ i →ₗ[ℂ] Models.Torus.GradCurl.Space i)).HasOrthogonalProjection := by
  rw [range_J]; infer_instance

/-- The ranges of the mirror extensions form a reducing subcomplex (the fixed fields). -/
theorem reducingSubcomplex_range :
    Models.Torus.GradCurl.complex.ReducingSubcomplex fun i =>
      LinearMap.range (J i : SpaceQ i →ₗ[ℂ] Models.Torus.GradCurl.Space i) := by
  convert action.reducingSubcomplex_fixed using 1
  exact funext range_J

/-- **The mirror complex of genuine fields on `Q`**:
`L²(Q; ℂ³) --grad--> L²(Q; ℂ³ˣ³) --curl--> L²(Q; ℂ³ˣ³)` with `σ · n = 0` and `E_{nτ} = 0`, the
compression of the torus complex along the mirror extensions (`d = J⁻¹ d_{𝕋³} J`). -/
abbrev complexQ : HilbertComplex ℂ ComplexShape.fin3 SpaceQ :=
  Models.Torus.GradCurl.complex.compress J eight_pos inner_J reducingSubcomplex_range

/-- The mirror extensions embed the cube complex in the torus complex (scale `8`). -/
def embeddingQ : ScaledEmbedding complexQ Models.Torus.GradCurl.complex :=
  ScaledEmbedding.ofCompress eight_pos inner_J reducingSubcomplex_range

@[simp] theorem embeddingQ_J (i : Fin 3) : embeddingQ.J i = J i := rfl

/-- `J d = d_{𝕋³} J`. -/
theorem J_complexQ_d {i j : Fin 3} (x : (complexQ.d i j).domain) :
    J j (complexQ.d i j x) = Models.Torus.GradCurl.complex.d i j
      ⟨J i x, (HilbertComplex.mem_compress_domain_iff eight_pos inner_J _).1 x.2⟩ :=
  HilbertComplex.J_compress_d eight_pos inner_J reducingSubcomplex_range x

theorem mem_complexQ_domain_iff {i j : Fin 3} {x : SpaceQ i} :
    x ∈ (complexQ.d i j).domain ↔ J i x ∈ (Models.Torus.GradCurl.complex.d i j).domain :=
  HilbertComplex.mem_compress_domain_iff eight_pos inner_J reducingSubcomplex_range

theorem mem_complexQ_adjoint_domain_iff {i j : Fin 3} {y : SpaceQ j} :
    y ∈ ((complexQ.d i j)†).domain ↔
      J j y ∈ ((Models.Torus.GradCurl.complex.d i j)†).domain :=
  HilbertComplex.mem_adjoint_compress_iff eight_pos inner_J reducingSubcomplex_range

/-- `J d† = d_{𝕋³}† J`. -/
theorem J_complexQ_adjoint {i j : Fin 3} (y : ((complexQ.d i j)†).domain) :
    J i ((complexQ.d i j)† y) = (Models.Torus.GradCurl.complex.d i j)†
      ⟨J j y, mem_complexQ_adjoint_domain_iff.1 y.2⟩ :=
  HilbertComplex.J_adjoint_compress_d eight_pos inner_J reducingSubcomplex_range y

/-! ### The mirror extensions of test fields intertwine the classical operators -/

section TestFields

open Feec.Domain (IsTestField testField gradOp curlOp ConstCoeffOp)
open Feec.Models.BoundedDomain (R3)
open UnitAddTorus (mFourierCoeff)

theorem cE_eq_update (a b : Fin 3) : cE (a, b) = Function.update (cV a) b (-cV a b) := by
  funext k
  fin_cases a <;> fin_cases b <;> fin_cases k <;> simp [cE, cV, sgn, Function.update]

theorem cV_eq_update (a b : Fin 3) : cV a = Function.update (cE (a, b)) b (-cE (a, b) b) := by
  funext k
  fin_cases a <;> fin_cases b <;> fin_cases k <;> simp [cE, cV, sgn, Function.update]

theorem cB_eq_update₁ (a b : Fin 3) :
    cB (a, b) = Function.update (cE (a, b + 2)) (b + 1) (-cE (a, b + 2) (b + 1)) := by
  funext k
  fin_cases a <;> fin_cases b <;> fin_cases k <;> simp [cE, cB, sgn, Function.update]

theorem cB_eq_update₂ (a b : Fin 3) :
    cB (a, b) = Function.update (cE (a, b + 1)) (b + 2) (-cE (a, b + 1) (b + 2)) := by
  funext k
  fin_cases a <;> fin_cases b <;> fin_cases k <;> simp [cE, cB, sgn, Function.update]

theorem cE_eq_update₁ (a b : Fin 3) :
    cE (a, b) = Function.update (cB (a, b + 2)) (b + 1) (-cB (a, b + 2) (b + 1)) := by
  funext k
  fin_cases a <;> fin_cases b <;> fin_cases k <;> simp [cE, cB, sgn, Function.update]

theorem cE_eq_update₂ (a b : Fin 3) :
    cE (a, b) = Function.update (cB (a, b + 1)) (b + 2) (-cB (a, b + 1) (b + 2)) := by
  funext k
  fin_cases a <;> fin_cases b <;> fin_cases k <;> simp [cE, cB, sgn, Function.update]

/-- The coefficients of the extension of a test field. -/
theorem coeff_extPi_testField {P : Type*} [Fintype P] [DecidableEq P] {c : P → Fin 3 → ℂ}
    (hc : ∀ p k, c p k * c p k = 1) {Φ : P → R3 → ℂ} (hΦ : IsTestField (Q (Fin 3)) Φ)
    (n : Fin 3 → ℤ) (p : P) :
    TorusWeak.coeff (extPi hc (testField hΦ)) n p = mFourierCoeff (Geometry.ext (c p) (Φ p)) n := by
  rw [TorusWeak.coeff_apply, extPi_testField, TorusWeak.mFourierCoeff_toL2]

theorem coeff_extPi_testField' {P : Type*} [Fintype P] [DecidableEq P] {c : P → Fin 3 → ℂ}
    (hc : ∀ p k, c p k * c p k = 1) {Φ : P → R3 → ℂ} (hΦ : IsTestField (Q (Fin 3)) Φ)
    (n : Fin 3 → ℤ) :
    TorusWeak.coeff (extPi hc (testField hΦ)) n =
      WithLp.toLp 2 fun p => mFourierCoeff (Geometry.ext (c p) (Φ p)) n :=
  PiLp.ext fun p => coeff_extPi_testField hc hΦ n p

/-- The curl of extensions: the coefficient identity for the row-wise curl, for parities with
`c_out (a, b) = c_in (a, b + 2)` and `c_in (a, b + 1)` with the parity of `x_{b+1}`, resp.
`x_{b+2}`, reversed. -/
theorem coeff_ext_curl {cin cout : Fin 3 × Fin 3 → Fin 3 → ℂ}
    (h₁ : ∀ a b, cout (a, b) = Function.update (cin (a, b + 2)) (b + 1) (-cin (a, b + 2) (b + 1)))
    (h₂ : ∀ a b, cout (a, b) = Function.update (cin (a, b + 1)) (b + 2) (-cin (a, b + 1) (b + 2)))
    {Φ : Fin 3 × Fin 3 → R3 → ℂ} (hΦ : IsTestField (Q (Fin 3)) Φ) (n : Fin 3 → ℤ)
    (a b : Fin 3) :
    mFourierCoeff
        (Geometry.ext (cout (a, b)) ((curlOp 3 : ConstCoeffOp R3 ℂ _ _).apply Φ (a, b))) n =
      curl (Fourier.Torus.freq n)
        (WithLp.toLp 2 fun p => mFourierCoeff (Geometry.ext (cin p) (Φ p)) n) (a, b) := by
  have e : (curlOp 3 : ConstCoeffOp R3 ℂ _ _).apply Φ (a, b) = fun x =>
      fderiv ℝ (Φ (a, b + 2)) x (Pi.single (b + 1) 1) -
        fderiv ℝ (Φ (a, b + 1)) x (Pi.single (b + 2) 1) :=
    funext fun x => Domain.curlOp_apply Φ (a, b) x
  rw [e, mFourierCoeff_ext_sub _ ((hΦ _).fderiv_apply _) ((hΦ _).fderiv_apply _),
    mFourierCoeff_ext_fderiv' (b + 1) (h₁ a b) (hΦ _),
    mFourierCoeff_ext_fderiv' (b + 2) (h₂ a b) (hΦ _), curl_apply]
  simp only [Fin.sum_univ_three, leviCivita3_apply, Fourier.Torus.freq_apply]
  fin_cases b <;> simp <;> ring

variable {cv : Fin 3 → Fin 3 → ℂ} {cm cm' : Fin 3 × Fin 3 → Fin 3 → ℂ}
  (hcv : ∀ a k, cv a k * cv a k = 1) (hcm : ∀ p k, cm p k * cm p k = 1)
  (hcm' : ∀ p k, cm' p k * cm' p k = 1)

/-- **`grad` commutes with extensions of test fields** whenever the matrix parities are the
vector parities with the parity of the differentiated variable reversed. -/
theorem grad_extF_testField (h : ∀ a b, cm (a, b) = Function.update (cv a) b (-cv a b))
    {φ : Fin 3 → R3 → ℂ} (hφ : IsTestField (Q (Fin 3)) φ) :
    ∃ h : extF hcv (testField hφ) ∈ (Models.Torus.GradCurl.complex.d 0 1).domain,
      Models.Torus.GradCurl.complex.d 0 1 ⟨_, h⟩ =
        extF hcm (testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).isTestField_apply hφ)) := by
  refine (Models.Torus.GradCurl.mem_domain_grad_iff_weak (extPi hcv (testField hφ))
    (extPi hcm (testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).isTestField_apply hφ)))).2
    ((TorusWeak.isWeak_iff Models.Torus.GradCurl.grad_isLinear _ _).2 fun n => ?_)
  refine PiLp.ext fun ⟨a, b⟩ => ?_
  rw [coeff_extPi_testField, gradCurl_m01, grad_apply, coeff_extPi_testField]
  have e : (gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).apply φ (a, b) =
      fun x => fderiv ℝ (φ a) x (Pi.single b 1) := funext fun x => Domain.gradOp_apply φ (a, b) x
  rw [e, mFourierCoeff_ext_fderiv' b (h a b) (hφ a), Fourier.Torus.freq_apply]
  push_cast; ring

/-- **`div` commutes with extensions of test fields** (`grad† = -div` on `𝕋³`). -/
theorem adjoint_grad_extF_testField (h : ∀ a b, cv a = Function.update (cm (a, b)) b (-cm (a, b) b))
    {Ψ : Fin 3 × Fin 3 → R3 → ℂ} (hΨ : IsTestField (Q (Fin 3)) Ψ) :
    ∃ h : extF hcm (testField hΨ) ∈ ((Models.Torus.GradCurl.complex.d 0 1)†).domain,
      (Models.Torus.GradCurl.complex.d 0 1)† ⟨_, h⟩ =
        extF hcv (testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply
          hΨ)) := by
  refine (Models.Torus.GradCurl.mem_domain_adjoint_grad_iff_weak (extPi hcm (testField hΨ))
    (extPi hcv (testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply
      hΨ)))).2 ((TorusWeak.isWeak_iff Models.Torus.GradCurl.adjoint_grad_isLinear _ _).2
      fun n => ?_)
  refine PiLp.ext fun a => ?_
  rw [coeff_extPi_testField]
  erw [gradCurl_m01, adjoint_grad, div_apply]
  have e : (gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.apply Ψ a =
      fun x => ∑ b, (-1 : ℂ) * fderiv ℝ (Ψ (a, b)) x (Pi.single b 1) := funext fun x => by
    rw [Domain.gradOp_formalAdj_apply]; simp [Finset.sum_neg_distrib]
  rw [e, mFourierCoeff_ext_sum _ _ _ fun b => (hΨ _).fderiv_apply _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mFourierCoeff_ext_fderiv' b (h a b) (hΨ _), coeff_extPi_testField,
    Fourier.Torus.freq_apply]
  push_cast; ring

/-- **`curl` commutes with extensions of test fields** (tensor parities in, pseudo-tensor parities
out, or conversely). -/
theorem curl_extF_testField
    (h₁ : ∀ a b, cm' (a, b) = Function.update (cm (a, b + 2)) (b + 1) (-cm (a, b + 2) (b + 1)))
    (h₂ : ∀ a b, cm' (a, b) = Function.update (cm (a, b + 1)) (b + 2) (-cm (a, b + 1) (b + 2)))
    {Φ : Fin 3 × Fin 3 → R3 → ℂ} (hΦ : IsTestField (Q (Fin 3)) Φ) :
    ∃ h : extF hcm (testField hΦ) ∈ (Models.Torus.GradCurl.complex.d 1 2).domain,
      Models.Torus.GradCurl.complex.d 1 2 ⟨_, h⟩ =
        extF hcm' (testField ((curlOp 3 : ConstCoeffOp R3 ℂ _ _).isTestField_apply hΦ)) := by
  refine (Models.Torus.GradCurl.mem_domain_curl_iff_weak (extPi hcm (testField hΦ))
    (extPi hcm' (testField ((curlOp 3 : ConstCoeffOp R3 ℂ _ _).isTestField_apply hΦ)))).2
    ((TorusWeak.isWeak_iff Models.Torus.GradCurl.curl_isLinear _ _).2 fun n => ?_)
  refine PiLp.ext fun ⟨a, b⟩ => ?_
  rw [coeff_extPi_testField, gradCurl_m12, coeff_ext_curl h₁ h₂ hΦ n a b,
    coeff_extPi_testField']

/-- **`curl† = curl` commutes with extensions of test fields.** -/
theorem adjoint_curl_extF_testField
    (h₁ : ∀ a b, cm' (a, b) = Function.update (cm (a, b + 2)) (b + 1) (-cm (a, b + 2) (b + 1)))
    (h₂ : ∀ a b, cm' (a, b) = Function.update (cm (a, b + 1)) (b + 2) (-cm (a, b + 1) (b + 2)))
    {Ψ : Fin 3 × Fin 3 → R3 → ℂ} (hΨ : IsTestField (Q (Fin 3)) Ψ) :
    ∃ h : extF hcm (testField hΨ) ∈ ((Models.Torus.GradCurl.complex.d 1 2)†).domain,
      (Models.Torus.GradCurl.complex.d 1 2)† ⟨_, h⟩ =
        extF hcm' (testField ((curlOp 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply
          hΨ)) := by
  have hadj : (Models.Torus.GradCurl.complex.d 1 2)† = Operator.mulOp Measure.count fun n =>
      gradCurl.m 1 2 (Fourier.Torus.freq n) := by
    rw [show (Models.Torus.GradCurl.complex.d 1 2)† = Operator.mulOp Measure.count fun n =>
        ContinuousLinearMap.adjoint (gradCurl.m 1 2 (Fourier.Torus.freq n)) from
      (Fourier.Torus.symbolComplex gradCurl).adjoint_d 1 2]
    congr 1
    funext n
    exact adjoint_curl _
  have key := (TorusWeak.mem_graph_iff_isWeak Models.Torus.GradCurl.curl_isLinear
    (extPi hcm (testField hΨ))
    (extPi hcm' (testField ((curlOp 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply
      hΨ)))).2 ((TorusWeak.isWeak_iff Models.Torus.GradCurl.curl_isLinear _ _).2 fun n => by
        refine PiLp.ext fun ⟨a, b⟩ => ?_
        rw [coeff_extPi_testField, gradCurl_m12]
        have e : (curlOp 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.apply Ψ (a, b) =
            (curlOp 3 : ConstCoeffOp R3 ℂ _ _).apply Ψ (a, b) := by
          rw [Domain.curlOp_formalAdj_apply]
        rw [e, coeff_ext_curl h₁ h₂ hΨ n a b, coeff_extPi_testField'])
  obtain ⟨h, e⟩ := key
  refine ⟨hadj ▸ h, ?_⟩
  rw [apply_eq_of_eq hadj _ ⟨_, h⟩ rfl]
  exact e

/-- **`grad ∘ J₀ = J₁ ∘ grad` on test fields**: the mirror extension of a test vector field lies
in `H¹(𝕋³)` and its gradient is the mirror extension of the gradient. -/
theorem grad_J_testField {φ : Fin 3 → R3 → ℂ} (hφ : IsTestField (Q (Fin 3)) φ) :
    ∃ h : J 0 (testField hφ) ∈ (Models.Torus.GradCurl.complex.d 0 1).domain,
      Models.Torus.GradCurl.complex.d 0 1 ⟨_, h⟩ =
        J 1 (testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).isTestField_apply hφ)) :=
  grad_extF_testField cV_sq cE_sq cE_eq_update hφ

/-- **`curl ∘ J₁ = J₂ ∘ curl` on test fields.** -/
theorem curl_J_testField {Φ : Fin 3 × Fin 3 → R3 → ℂ} (hΦ : IsTestField (Q (Fin 3)) Φ) :
    ∃ h : J 1 (testField hΦ) ∈ (Models.Torus.GradCurl.complex.d 1 2).domain,
      Models.Torus.GradCurl.complex.d 1 2 ⟨_, h⟩ =
        J 2 (testField ((curlOp 3 : ConstCoeffOp R3 ℂ _ _).isTestField_apply hΦ)) :=
  curl_extF_testField cE_sq cB_sq cB_eq_update₁ cB_eq_update₂ hΦ

/-- **`div ∘ J₁ = J₀ ∘ div` on test fields**: the mirror extension of a test matrix field (tensor
parities) lies in `D(grad†) = H(div; 𝕋³)` and `grad† = -div` maps it to the mirror extension of
`-div`. -/
theorem adjoint_grad_J_testField {Ψ : Fin 3 × Fin 3 → R3 → ℂ} (hΨ : IsTestField (Q (Fin 3)) Ψ) :
    ∃ h : J 1 (testField hΨ) ∈ ((Models.Torus.GradCurl.complex.d 0 1)†).domain,
      (Models.Torus.GradCurl.complex.d 0 1)† ⟨_, h⟩ =
        J 0 (testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply hΨ)) :=
  adjoint_grad_extF_testField cV_sq cE_sq cV_eq_update hΨ

/-- **`curl† ∘ J₂ = J₁ ∘ curl` on test fields** (`curl† = curl`, pseudo-tensor parities in,
tensor parities out). -/
theorem adjoint_curl_J_testField {Ψ : Fin 3 × Fin 3 → R3 → ℂ} (hΨ : IsTestField (Q (Fin 3)) Ψ) :
    ∃ h : J 2 (testField hΨ) ∈ ((Models.Torus.GradCurl.complex.d 1 2)†).domain,
      (Models.Torus.GradCurl.complex.d 1 2)† ⟨_, h⟩ =
        J 1 (testField ((curlOp 3 : ConstCoeffOp R3 ℂ _ _).formalAdj.isTestField_apply hΨ)) :=
  adjoint_curl_extF_testField cB_sq cE_sq cE_eq_update₁ cE_eq_update₂ hΨ

end TestFields

/-! ### TSD fields on `Q` -/

/-- The parity of the component `M_a` of a mirror pseudo-vector in `x_k`: `-s_k(a)`. -/
def cPV (a k : Fin 3) : ℂ := -sgn k a

theorem cPV_sq (a k : Fin 3) : cPV a k * cPV a k = 1 := by rw [cPV, neg_mul_neg]; exact cV_sq a k

theorem cB_eq_update (a b : Fin 3) : cB (a, b) = Function.update (cPV a) b (-cPV a b) := by
  funext k
  fin_cases a <;> fin_cases b <;> fin_cases k <;> simp [cB, cPV, sgn, Function.update]

theorem cPV_eq_update (a b : Fin 3) : cPV a = Function.update (cB (a, b)) b (-cB (a, b) b) := by
  funext k
  fin_cases a <;> fin_cases b <;> fin_cases k <;> simp [cB, cPV, sgn, Function.update]

/-- **TSD fields are divergence-free**: `L²(TSD) ⊆ ker grad† = ker div` on `𝕋³`. -/
theorem constraint_le_ker_adjoint :
    Models.Torus.GradCurl.constraint 1 ≤ ((Models.Torus.GradCurl.complex.d 0 1)†).ker := by
  intro u hu
  change u ∈ ((Fourier.Torus.symbolComplex gradCurl).toHilbertComplex.d 0 1)†.ker
  rw [(Fourier.Torus.symbolComplex gradCurl).adjoint_d 0 1]
  refine Operator.mem_ker_mulOp.2 ?_
  filter_upwards [Operator.mem_fibreSub.1 hu] with k hk
  exact (Submodule.mem_bot ℂ).1
    (Models.Torus.GradCurl.fibreReducing.map_adj 0 1 k ⟨_, hk, rfl⟩)

theorem extL2_congr {c c' : Fin 3 → ℂ} (h : c = c') (hc : ∀ j, c j * c j = 1)
    (hc' : ∀ j, c' j * c' j = 1) (g : Domain.L2 ℂ (Q (Fin 3))) : extL2 hc g = extL2 hc' g := by
  subst h; rfl

section TSD

open Feec.Domain (IsTestField testField gradOp ConstCoeffOp)
open Feec.Models.BoundedDomain (R3)
open UnitAddTorus (mFourierCoeff)

variable {cv : Fin 3 → Fin 3 → ℂ} {cm : Fin 3 × Fin 3 → Fin 3 → ℂ}
  (hcv : ∀ a k, cv a k * cv a k = 1) (hcm : ∀ p k, cm p k * cm p k = 1)

include hcv in
/-- **A field on `Q` whose extension is TSD on `𝕋³` is TSD on `Q`**: symmetric, trace-free and
weakly divergence-free (`⟪E, grad φ⟫ = 0` for every test field `φ`, no boundary condition), for
parities `cm` symmetric in the indices, constant on the diagonal, and obtained from vector
parities `cv` by `grad`. -/
theorem tsd_of_extF_mem (hsym : ∀ a b, cm (a, b) = cm (b, a)) (hdiag : ∀ a, cm (a, a) = cm (0, 0))
    (hgrad : ∀ a b, cm (a, b) = Function.update (cv a) b (-cv a b)) {E : MQ}
    (hE : extF hcm E ∈ Models.Torus.GradCurl.constraint 1) :
    (∀ i j, E (i, j) = E (j, i)) ∧ ∑ i, E (i, i) = 0 ∧
      ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : IsTestField (Q (Fin 3)) φ,
        ⟪E, testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).isTestField_apply hφ)⟫_ℂ = 0 := by
  have hfib : ∀ n, (extF hcm E : (Fin 3 → ℤ) → Mat) n ∈ tsd (Fourier.Torus.freq n) :=
    Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 hE)
  refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · have h : extL2 (hcm (i, j)) (E (i, j)) = extL2 (hcm (j, i)) (E (j, i)) := by
      refine TorusWeak.eq_of_mFourierCoeff_eq fun n => ?_
      rw [← extF_coeff, ← extF_coeff]
      have := congrFun (congrFun (mem_tsd.1 (hfib n)).1 j) i
      simpa [Matrix.transpose_apply, toMatrix_apply] using this
    rw [extL2_congr (hsym i j) _ (hcm (j, i))] at h
    rw [← resQ_extL2 (hcm (j, i)) (E (i, j)), h, resQ_extL2]
  · have hc0 : ∀ j, cm (0, 0) j * cm (0, 0) j = 1 := hcm (0, 0)
    have h : extL2 hc0 (∑ i, E (i, i)) = 0 := by
      refine TorusWeak.eq_of_mFourierCoeff_eq fun n => ?_
      have htr := (mem_tsd.1 (hfib n)).2.1
      simp only [Matrix.trace, Matrix.diag, toMatrix_apply] at htr
      rw [map_sum, ← coeffCLM_apply, map_sum]
      simp only [coeffCLM_apply]
      rw [show (0 : T2 (Fin 3)) = extL2 hc0 0 from (_root_.map_zero _).symm, ← coeffCLM_apply,
        _root_.map_zero, _root_.map_zero, ← htr]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [extF_coeff, extL2_congr (hdiag i) (hcm (i, i)) hc0]
    rw [← resQ_extL2 hc0 (∑ i, E (i, i)), h, _root_.map_zero]
  · obtain ⟨hd, he⟩ := grad_extF_testField hcv hcm hgrad hφ
    have hker := constraint_le_ker_adjoint hE
    obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 hker
    have h8 : ((8 : ℝ) : ℂ) * ⟪E, testField ((gradOp 3 3 : ConstCoeffOp R3 ℂ _ _).isTestField_apply
        hφ)⟫_ℂ = 0 := by
      rw [← two_pow_card, ← inner_extF hcm, ← he]
      have := LinearPMap.adjoint_isFormalAdjoint
        (Models.Torus.GradCurl.complex.dense 0 1) y ⟨_, hd⟩
      rw [hy0, inner_zero_left] at this
      rw [hy]
      exact this.symm
    exact (mul_eq_zero.1 h8).resolve_left (by norm_num)

end TSD

/-- **The constraint on `Q`**: the pull-back `{0} × J₁⁻¹ L²(TSD) × J₂⁻¹ L²(TSD)` of the torus
constraint, TSD fields on `Q` with the wall conditions `E_{τn} = 0`, `B_{nn} = 0`
(`mem_tsdQ_one`). -/
abbrev tsdQ (i : Fin 3) : Submodule ℂ (SpaceQ i) :=
  (Models.Torus.GradCurl.constraint i).comap (J i : SpaceQ i →ₗ[ℂ] Models.Torus.GradCurl.Space i)

instance (i : Fin 3) : (tsdQ i).HasOrthogonalProjection :=
  embeddingQ.comap_hasOrthogonalProjection i _

/-- The first slot of the constraint is `{0}`. -/
theorem mem_tsdQ_zero {σ : VQ} : σ ∈ tsdQ 0 ↔ σ = 0 := by
  constructor
  · intro h
    have h0 : J 0 σ = 0 := Lp.ext_count fun n => by
      rw [Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) n]
      exact (Submodule.mem_bot ℂ).1 (Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 h) n)
    exact embeddingQ.J_injective 0 (h0.trans (_root_.map_zero _).symm)
  · rintro rfl; exact Submodule.zero_mem _

/-- **The electric constraint on `Q` consists of TSD fields**: symmetric, trace-free and weakly
divergence-free in `Q` (and, by construction, divergence-free across the faces: `E_{τn} = 0`). -/
theorem mem_tsdQ_one {E : MQ} (hE : E ∈ tsdQ 1) :
    (∀ i j, E (i, j) = E (j, i)) ∧ ∑ i, E (i, i) = 0 ∧
      ∀ φ : Fin 3 → Feec.Models.BoundedDomain.R3 → ℂ, ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
        ⟪E, Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
          hφ)⟫_ℂ = 0 :=
  tsd_of_extF_mem cV_sq cE_sq (fun a b => funext fun k => by simp only [cE]; ring)
    (fun a => funext fun k => by simp only [cE, sgn_mul_self]) cE_eq_update hE

/-- **The magnetic constraint on `Q` consists of TSD fields** (with `B_{nn} = 0` across the
faces). -/
theorem mem_tsdQ_two {B : MQ} (hB : B ∈ tsdQ 2) :
    (∀ i j, B (i, j) = B (j, i)) ∧ ∑ i, B (i, i) = 0 ∧
      ∀ φ : Fin 3 → Feec.Models.BoundedDomain.R3 → ℂ, ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
        ⟪B, Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
          hφ)⟫_ℂ = 0 :=
  tsd_of_extF_mem cPV_sq cB_sq (fun a b => funext fun k => by simp only [cB]; ring)
    (fun a => funext fun k => by simp only [cB, sgn_mul_self]) cB_eq_update hB

/-- The TSD projections preserve the fixed fields, i.e. the range of `J`. -/
theorem exists_J_eq_starProjection (i : Fin 3) (x : SpaceQ i) :
    ∃ y, J i y = (Models.Torus.GradCurl.constraint i).starProjection (J i x) := by
  have hx : J i x ∈ action.fixed i := range_J i ▸ LinearMap.mem_range_self _ x
  have h := action.starProjection_mem_fixed (fun g y hy => act_mem_constraint g i hy) hx
  rw [← range_J] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy⟩

/-- **TSD reduces the mirror complex on `Q`** (pull-back of the torus constraint along the
mirror extensions).
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem reducingSubcomplexQ : complexQ.ReducingSubcomplex tsdQ :=
  embeddingQ.reducingSubcomplex_comap Models.Torus.GradCurl.reducingSubcomplex
    exists_J_eq_starProjection

/-- **Prop 4.17 on `Q` with mirror boundary conditions**: TSD data and forcing give TSD
solutions (any time interval).
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem propagatesQ {a b : ℝ} {F U : ℝ → PiLp 2 SpaceQ}
    (hU : Evolution.IsStrongSolution complexQ.wave (Icc a b) F U) (h0 : U a ∈ totalSub tsdQ)
    (hF : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) : ∀ t ∈ Icc a b, U t ∈ totalSub tsdQ :=
  reducingSubcomplexQ.propagates hU h0 hF

/-- Prop 4.17 on `Q` with existence and uniqueness: for `(0, E₀, B₀) ∈ D(L)` with `E₀`, `B₀`
in the constraint, the Hodge wave equation (4.14) has a classical solution, unique among strong
solutions, with `σ ≡ 0` and `E`, `B` TSD for all time.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem existsUnique_memQ {U₀ : PiLp 2 SpaceQ} (hU₀ : U₀ ∈ complexQ.wave.domain)
    (hU₀S : U₀ ∈ totalSub tsdQ) {F : ℝ → PiLp 2 SpaceQ} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complexQ.wave a b F)
    (hFS : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complexQ.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub tsdQ) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complexQ.wave (Icc a b) F V →
        EqOn V U (Icc a b) :=
  reducingSubcomplexQ.existsUnique_mem hU₀ hU₀S hF hFS

/-- `K* = K` on `Q`.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem invariantCore_eqQ : complexQ.waveGroup.invariantCore (totalSub tsdQ) = totalSub tsdQ :=
  reducingSubcomplexQ.invariantCore_eq

/-- The electric datum on `Q`: `E₀ = (2 cos(2π x₃) diag(1, -1, 0))|_Q`. -/
def cosEQ : MQ := Geometry.resQF ((Fourier.Torus.fieldFourier (Fin 3) (Fin 3 × Fin 3)).symm cosE)

theorem J_cosEQ : J 1 cosEQ = cosE := extF_resQF cE_sq cosE_mem_fieldParity

/-- The datum `(0, E₀, 0)` on `Q`. -/
def cosStateQ : PiLp 2 SpaceQ := WithLp.toLp 2 (Pi.single 1 cosEQ)

theorem cosStateQ_zero : cosStateQ 0 = 0 :=
  Pi.single_eq_of_ne (M := SpaceQ) (by decide : (0 : Fin 3) ≠ 1) cosEQ
theorem cosStateQ_one : cosStateQ 1 = cosEQ := Pi.single_eq_same (M := SpaceQ) (1 : Fin 3) cosEQ
theorem cosStateQ_two : cosStateQ 2 = 0 :=
  Pi.single_eq_of_ne (M := SpaceQ) (by decide : (2 : Fin 3) ≠ 1) cosEQ

theorem totalJ_cosStateQ : HilbertComplex.totalJ J cosStateQ = cosState := by
  refine PiLp.ext fun i => ?_
  rw [HilbertComplex.totalJ_apply]
  fin_cases i
  · change J 0 (cosStateQ 0) = cosState 0
    rw [cosStateQ_zero, _root_.map_zero, cosState_zero]
  · change J 1 (cosStateQ 1) = cosState 1
    rw [cosStateQ_one, J_cosEQ, cosState_one]
  · change J 2 (cosStateQ 2) = cosState 2
    rw [cosStateQ_two, _root_.map_zero, cosState_two]

theorem cosStateQ_mem_domain : cosStateQ ∈ complexQ.wave.domain :=
  (HilbertComplex.mem_wave_domain_compress_iff eight_pos inner_J reducingSubcomplex_range).2
    (totalJ_cosStateQ ▸ cosState_mem_domain)

theorem cosEQ_mem_domain : cosEQ ∈ (complexQ.d 1 2).domain := by
  rw [← cosStateQ_one]; exact cosStateQ_mem_domain.1 1 2

/-- **`curl E₀ ≠ 0` on `Q`.** -/
theorem complexQ_d_cosEQ_ne : complexQ.d 1 2 ⟨cosEQ, cosEQ_mem_domain⟩ ≠ 0 := by
  intro h
  have h1 := J_complexQ_d (i := 1) (j := 2) ⟨cosEQ, cosEQ_mem_domain⟩
  rw [h, _root_.map_zero] at h1
  have h2 : Models.Torus.GradCurl.complex.d 1 2 ⟨cosE, cosE_mem_domain⟩ = 0 :=
    (apply_congr' _ _ _ J_cosEQ.symm).trans h1.symm
  apply curl_M0_ne
  rw [← curl_cosE_apply, h2]
  exact Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) k0

/-- **A non-stationary TSD datum on `Q`**: `(0, (2 cos(2π x₃) diag(1, -1, 0))|_Q, 0)` lies in
`D(L) ∩ K` and is not stationary.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem exists_nonstationaryQ :
    ∃ y ∈ complexQ.wave.domain, y ∈ totalSub tsdQ ∧ y ∉ complexQ.waveGroup.stationary := by
  have hd : HilbertComplex.totalJ J cosStateQ ∈ Models.Torus.GradCurl.complex.wave.domain :=
    totalJ_cosStateQ ▸ cosState_mem_domain
  obtain ⟨h1, h2⟩ := HilbertComplex.not_mem_stationary_compress eight_pos inner_J
    reducingSubcomplex_range hd fun h0 =>
      wave_cosState_ne ((apply_congr' _ _ _ totalJ_cosStateQ.symm).trans h0)
  refine ⟨cosStateQ, h1, fun i => ?_, h2⟩
  change J i (cosStateQ i) ∈ Models.Torus.GradCurl.constraint i
  rw [← HilbertComplex.totalJ_apply, totalJ_cosStateQ]
  exact cosState_mem_constraint i

/-! ### Every open cube -/

section Cube

open Geometry (openCube)
open Feec.Models.BoundedDomain (R3)

variable {b : R3} {s : ℝ} (hs : 0 < s)

theorem inv_two_mul_ne (hs : 0 < s) : (2 * s)⁻¹ ≠ 0 := inv_ne_zero (by positivity)

/-- `T x = (x - b)/(2s)` maps the open cube `∏ (bᵢ, bᵢ + s)` onto `Q`. -/
theorem preimage_aff_Q (hs : 0 < s) (b : R3) :
    Domain.aff (2 * s)⁻¹ (-((2 * s)⁻¹ • b)) ⁻¹' Q (Fin 3) = openCube b s := by
  have h2s : 0 < 2 * s := by positivity
  ext x
  simp only [Set.mem_preimage, Geometry.mem_Q, Domain.aff, openCube, Set.mem_pi, Set.mem_univ,
    true_implies, Set.mem_Ioo, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  refine forall_congr' fun i => ?_
  rw [show (2 * s)⁻¹ * x i + -((2 * s)⁻¹ * b i) = (x i - b i) / (2 * s) by ring,
    div_pos_iff_of_pos_right h2s, div_lt_iff₀ h2s, sub_pos]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

/-- The pull-back `u ↦ u ∘ T` of fields from `Q` to the cube `∏ (bᵢ, bᵢ + s)`. -/
abbrev pullCube (b : R3) (s : ℝ) (hs : 0 < s) (P : Type*) [Fintype P] :
    Domain.L2F ℂ (Q (Fin 3)) P ≃L[ℂ] Domain.L2F ℂ (openCube b s) P :=
  Domain.pullF (inv_two_mul_ne hs) (-((2 * s)⁻¹ • b)) Geometry.measurableSet_Q
    (preimage_aff_Q hs b) P

theorem inner_pullCube {P : Type*} [Fintype P] (u v : Domain.L2F ℂ (Q (Fin 3)) P) :
    ⟪pullCube b s hs P u, pullCube b s hs P v⟫_ℂ =
      (((Domain.jac (E := R3) (2 * s)⁻¹)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ :=
  Domain.inner_pullF _ _ _ _ u v

/-- The spaces `L²(C; ℂ³)`, `L²(C; ℂ³ˣ³)`, `L²(C; ℂ³ˣ³)` on the cube `C = ∏ (bᵢ, bᵢ + s)`. -/
abbrev SpaceCube (b : R3) (s : ℝ) (i : Fin 3) : Type :=
  W3 (Domain.L2F ℂ (openCube b s) (Fin 3)) (Domain.L2F ℂ (openCube b s) (Fin 3 × Fin 3))
    (Domain.L2F ℂ (openCube b s) (Fin 3 × Fin 3)) i

/-- The pull-backs on the three spaces. -/
def eCube (b : R3) (s : ℝ) (hs : 0 < s) : ∀ i : Fin 3, SpaceQ i ≃L[ℂ] SpaceCube b s i
  | 0 => pullCube b s hs (Fin 3)
  | 1 => pullCube b s hs (Fin 3 × Fin 3)
  | 2 => pullCube b s hs (Fin 3 × Fin 3)

theorem inner_eCube (i : Fin 3) (u v : SpaceQ i) :
    ⟪eCube b s hs i u, eCube b s hs i v⟫_ℂ =
      (((Domain.jac (E := R3) (2 * s)⁻¹)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  fin_cases i
  · exact inner_pullCube hs u v
  · exact inner_pullCube hs u v
  · exact inner_pullCube hs u v

theorem jac_inv_pos (hs : 0 < s) : 0 < (Domain.jac (E := R3) (2 * s)⁻¹)⁻¹ :=
  inv_pos.2 (Domain.jac_pos (inv_two_mul_ne hs))

/-- The chain-rule factor `(2s)⁻¹` of first-order operators. -/
def kappa (s : ℝ) : Fin 3 → Fin 3 → ℂ := fun _ _ => (((2 * s)⁻¹ : ℝ) : ℂ)

theorem kappa_ne_zero (hs : 0 < s) (i j : Fin 3) : kappa s i j ≠ 0 :=
  RCLike.ofReal_ne_zero.2 (inv_two_mul_ne hs)

/-- **The mirror complex on the open cube** `∏ (bᵢ, bᵢ + s)`: the transport of `complexQ` along the
pull-back by `x ↦ (x - b)/(2s)`, with the chain-rule factor `(2s)⁻¹`; the boundary conditions are
`σ · n = 0`, `E_{nτ} = 0` on the faces. -/
abbrev complexCube (b : R3) (s : ℝ) (hs : 0 < s) :
    HilbertComplex ℂ ComplexShape.fin3 (SpaceCube b s) :=
  complexQ.transport (eCube b s hs) (kappa s) (kappa_ne_zero hs)

/-- The pull-back to `Q` embeds the cube complex in the complex on `Q`. -/
def embeddingCube : ScaledEmbedding (complexCube b s hs) complexQ :=
  ScaledEmbedding.ofTransportSymm (eCube b s hs) (kappa s) (kappa_ne_zero hs)
    (fun _ => (Domain.jac (E := R3) (2 * s)⁻¹)⁻¹) (fun _ => jac_inv_pos hs) (inner_eCube hs)

/-- The constraint on the cube: the fields whose transplant to `Q` satisfies the constraint
`tsdQ` (TSD with the mirror wall conditions). -/
abbrev tsdCube (b : R3) (s : ℝ) (hs : 0 < s) (i : Fin 3) : Submodule ℂ (SpaceCube b s i) :=
  (tsdQ i).comap ((eCube b s hs i).symm : SpaceCube b s i →ₗ[ℂ] SpaceQ i)

instance (i : Fin 3) : (tsdCube b s hs i).HasOrthogonalProjection :=
  (embeddingCube hs).comap_hasOrthogonalProjection i _

/-- **TSD reduces the mirror complex on every open cube.**
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem reducingSubcomplexCube : (complexCube b s hs).ReducingSubcomplex (tsdCube b s hs) :=
  (embeddingCube hs).reducingSubcomplex_comap reducingSubcomplexQ fun i x =>
    ⟨eCube b s hs i ((tsdQ i).starProjection ((eCube b s hs i).symm x)),
      (eCube b s hs i).symm_apply_apply _⟩

/-- **Prop 4.17 on every open cube with mirror boundary conditions**: TSD data and forcing give
TSD solutions; in particular on `(0, π)³` and on the unit cube `(0, 1)³` meshed in Ch. 7.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem propagatesCube {a c : ℝ} {F U : ℝ → PiLp 2 (SpaceCube b s)}
    (hU : Evolution.IsStrongSolution (complexCube b s hs).wave (Icc a c) F U)
    (h0 : U a ∈ totalSub (tsdCube b s hs)) (hF : ∀ t ∈ Icc a c, F t ∈ totalSub (tsdCube b s hs)) :
    ∀ t ∈ Icc a c, U t ∈ totalSub (tsdCube b s hs) :=
  (reducingSubcomplexCube hs).propagates hU h0 hF

/-- Prop 4.17 on every open cube, with existence and uniqueness.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem existsUnique_memCube {U₀ : PiLp 2 (SpaceCube b s)}
    (hU₀ : U₀ ∈ (complexCube b s hs).wave.domain) (hU₀S : U₀ ∈ totalSub (tsdCube b s hs))
    {F : ℝ → PiLp 2 (SpaceCube b s)} {a c : ℝ}
    (hF : Evolution.ForcingClass.admissible (complexCube b s hs).wave a c F)
    (hFS : ∀ t ∈ Icc a c, F t ∈ totalSub (tsdCube b s hs)) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (complexCube b s hs).wave (Icc a c) F U ∧
      (∀ t ∈ Icc a c, U t ∈ totalSub (tsdCube b s hs)) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (complexCube b s hs).wave (Icc a c) F V →
        EqOn V U (Icc a c) :=
  (reducingSubcomplexCube hs).existsUnique_mem hU₀ hU₀S hF hFS

/-- `K* = K` on every open cube.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem invariantCore_eqCube :
    (complexCube b s hs).waveGroup.invariantCore (totalSub (tsdCube b s hs)) =
      totalSub (tsdCube b s hs) :=
  (reducingSubcomplexCube hs).invariantCore_eq

/-- Prop 4.17 with mirror boundary conditions on `(0, π)³`.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem existsUnique_memCube_pi {U₀ : PiLp 2 (SpaceCube 0 Real.pi)}
    (hU₀ : U₀ ∈ (complexCube 0 Real.pi Real.pi_pos).wave.domain)
    (hU₀S : U₀ ∈ totalSub (tsdCube 0 Real.pi Real.pi_pos)) {F : ℝ → PiLp 2 (SpaceCube 0 Real.pi)}
    {a c : ℝ}
    (hF : Evolution.ForcingClass.admissible (complexCube 0 Real.pi Real.pi_pos).wave a c F)
    (hFS : ∀ t ∈ Icc a c, F t ∈ totalSub (tsdCube 0 Real.pi Real.pi_pos)) :
    ∃ U, U a = U₀ ∧
      Evolution.IsClassicalSolution (complexCube 0 Real.pi Real.pi_pos).wave (Icc a c) F U ∧
      (∀ t ∈ Icc a c, U t ∈ totalSub (tsdCube 0 Real.pi Real.pi_pos)) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (complexCube 0 Real.pi Real.pi_pos).wave
        (Icc a c) F V → EqOn V U (Icc a c) :=
  existsUnique_memCube Real.pi_pos hU₀ hU₀S hF hFS

/-- Prop 4.17 with mirror boundary conditions on the unit cube `(0, 1)³` (the domain meshed in
Ch. 7; the Ch. 7 test solution, with time-dependent boundary values, is not covered).
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected), Ch. 7. -/
theorem existsUnique_memCube_unit {U₀ : PiLp 2 (SpaceCube 0 1)}
    (hU₀ : U₀ ∈ (complexCube 0 1 one_pos).wave.domain)
    (hU₀S : U₀ ∈ totalSub (tsdCube 0 1 one_pos)) {F : ℝ → PiLp 2 (SpaceCube 0 1)}
    {a c : ℝ} (hF : Evolution.ForcingClass.admissible (complexCube 0 1 one_pos).wave a c F)
    (hFS : ∀ t ∈ Icc a c, F t ∈ totalSub (tsdCube 0 1 one_pos)) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (complexCube 0 1 one_pos).wave (Icc a c) F U ∧
      (∀ t ∈ Icc a c, U t ∈ totalSub (tsdCube 0 1 one_pos)) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (complexCube 0 1 one_pos).wave (Icc a c) F V →
        EqOn V U (Icc a c) :=
  existsUnique_memCube one_pos hU₀ hU₀S hF hFS

/-- The datum `(0, E₀ ∘ T, 0)` on the cube, `E₀ = (2 cos(2π x₃) diag(1, -1, 0))|_Q`. -/
def cosStateCube (b : R3) (s : ℝ) (hs : 0 < s) : PiLp 2 (SpaceCube b s) :=
  HilbertComplex.totalMap (eCube b s hs) cosStateQ

theorem totalMap_symm_cosStateCube :
    HilbertComplex.totalMap (fun i => (eCube b s hs i).symm) (cosStateCube b s hs) = cosStateQ :=
  PiLp.ext fun i => (eCube b s hs i).symm_apply_apply _

/-- **A non-stationary TSD datum on every open cube.**
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem exists_nonstationaryCube :
    ∃ y ∈ (complexCube b s hs).wave.domain, y ∈ totalSub (tsdCube b s hs) ∧
      y ∉ (complexCube b s hs).waveGroup.stationary := by
  have hd : cosStateCube b s hs ∈ (complexCube b s hs).wave.domain :=
    (HilbertComplex.mem_wave_domain_transport_iff (kappa_ne_zero hs) (jac_inv_pos hs)
      (inner_eCube hs)).2 (totalMap_symm_cosStateCube hs ▸ cosStateQ_mem_domain)
  refine ⟨cosStateCube b s hs, hd, fun i => ?_, HilbertComplex.not_mem_stationary_of_wave_ne_zero
    ⟨_, hd⟩ fun h => ?_⟩
  · change (eCube b s hs i).symm (eCube b s hs i (cosStateQ i)) ∈ tsdQ i
    rw [ContinuousLinearEquiv.symm_apply_apply]
    change J i (cosStateQ i) ∈ Models.Torus.GradCurl.constraint i
    rw [← HilbertComplex.totalJ_apply, totalJ_cosStateQ]
    exact cosState_mem_constraint i
  · have h2 := congrArg (fun y : PiLp 2 (SpaceCube b s) => y 2) h
    rw [HilbertComplex.wave_apply_fin3_two] at h2
    change kappa s 1 2 • eCube b s hs 2 (complexQ.d 1 2 ⟨(eCube b s hs 1).symm
      (eCube b s hs 1 (cosStateQ 1)), _⟩) = 0 at h2
    rw [smul_eq_zero, or_iff_right (kappa_ne_zero hs 1 2),
      (eCube b s hs 2).map_eq_zero_iff] at h2
    apply complexQ_d_cosEQ_ne
    rw [← h2]
    exact apply_congr' _ _ _ (by rw [ContinuousLinearEquiv.symm_apply_apply, cosStateQ_one])

/-! #### The constraint on the cube consists of TSD fields -/

theorem gradOp_isHomogeneous :
    (Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℂ _ _).IsHomogeneous 1 := by
  intro j i t ht
  simp only [Domain.gradOp] at ht
  split_ifs at ht <;> simp_all

/-- **TSD fields pull back to TSD fields**: the conditions symmetric, trace-free and weakly
divergence-free on `Q` transfer to the cube `∏ (bᵢ, bᵢ + s)` along `T x = (x - b)/(2s)`. -/
theorem tsd_of_pullCube {E₀ : MQ}
    (h : (∀ i j, E₀ (i, j) = E₀ (j, i)) ∧ ∑ i, E₀ (i, i) = 0 ∧
      ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
        ⟪E₀, Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
          hφ)⟫_ℂ = 0) :
    let E := pullCube b s hs (Fin 3 × Fin 3) E₀
    (∀ i j, E (i, j) = E (j, i)) ∧ ∑ i, E (i, i) = 0 ∧
      ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : Domain.IsTestField (openCube b s) φ,
        ⟪E, Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
          hφ)⟫_ℂ = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  intro E
  refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · change pullCube b s hs (Fin 3 × Fin 3) E₀ (i, j) = pullCube b s hs (Fin 3 × Fin 3) E₀ (j, i)
    rw [Domain.pullF_apply, Domain.pullF_apply, h1]
  · change ∑ i, pullCube b s hs (Fin 3 × Fin 3) E₀ (i, i) = 0
    simp only [Domain.pullF_apply]
    rw [← map_sum, h2, _root_.map_zero]
  · have hmem : (Domain.testField hφ, Domain.testField
        ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply hφ)) ∈
        ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).testGraph (openCube b s) : Set _) :=
      ⟨φ, hφ, rfl⟩
    rw [Domain.ConstCoeffOp.testGraph_eq_preimage (𝕜 := ℂ) gradOp_isHomogeneous
      (inv_two_mul_ne hs) (-((2 * s)⁻¹ • b)) Geometry.measurableSet_Q (preimage_aff_Q hs b)]
      at hmem
    obtain ⟨ψ, hψ, hψe⟩ := hmem
    rw [Domain.ConstCoeffOp.graphHomeomorph_apply] at hψe
    have e2 := congrArg Prod.snd hψe
    simp only at e2
    have hκ : (RCLike.ofReal ((2 * s)⁻¹ ^ 1) : ℂ) ≠ 0 :=
      RCLike.ofReal_ne_zero.2 (pow_ne_zero 1 (inv_two_mul_ne hs))
    have e3 : Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
        hφ) = (RCLike.ofReal ((2 * s)⁻¹ ^ 1) : ℂ) • pullCube b s hs (Fin 3 × Fin 3)
          (Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
            hψ)) := by
      rw [← e2, _root_.map_smul, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
        mul_inv_cancel₀ hκ, one_smul]
    rw [e3, inner_smul_right]
    change _ * ⟪pullCube b s hs (Fin 3 × Fin 3) E₀, pullCube b s hs (Fin 3 × Fin 3) _⟫_ℂ = 0
    rw [inner_pullCube hs, h3 ψ hψ, mul_zero, mul_zero]

/-- **The electric constraint on the cube consists of TSD fields.** -/
theorem mem_tsdCube_one {E : Domain.L2F ℂ (openCube b s) (Fin 3 × Fin 3)}
    (hE : E ∈ tsdCube b s hs 1) :
    (∀ i j, E (i, j) = E (j, i)) ∧ ∑ i, E (i, i) = 0 ∧
      ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : Domain.IsTestField (openCube b s) φ,
        ⟪E, Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
          hφ)⟫_ℂ = 0 := by
  have hE' : (eCube b s hs 1).symm E ∈ tsdQ 1 := hE
  have h := tsd_of_pullCube (b := b) hs (mem_tsdQ_one hE')
  have e : pullCube b s hs (Fin 3 × Fin 3) ((eCube b s hs 1).symm E) = E :=
    (eCube b s hs 1).apply_symm_apply E
  simp only [e] at h
  exact h

/-- **The magnetic constraint on the cube consists of TSD fields.** -/
theorem mem_tsdCube_two {B : Domain.L2F ℂ (openCube b s) (Fin 3 × Fin 3)}
    (hB : B ∈ tsdCube b s hs 2) :
    (∀ i j, B (i, j) = B (j, i)) ∧ ∑ i, B (i, i) = 0 ∧
      ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : Domain.IsTestField (openCube b s) φ,
        ⟪B, Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
          hφ)⟫_ℂ = 0 := by
  have hB' : (eCube b s hs 2).symm B ∈ tsdQ 2 := hB
  have h := tsd_of_pullCube (b := b) hs (mem_tsdQ_two hB')
  have e : pullCube b s hs (Fin 3 × Fin 3) ((eCube b s hs 2).symm B) = B :=
    (eCube b s hs 2).apply_symm_apply B
  simp only [e] at h
  exact h

end Cube

end Feec.Models.Cube.Mirror
