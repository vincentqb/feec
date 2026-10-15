module

public import Feec.Ch4.Box
public import Feec.Ch4.BoxReduce
public import Feec.Ch4.TorusSym

/-!
# Props 4.17 and 4.19 on a box with tensorial mirror boundary conditions

`Feec.Ch4.Box` shows that with the thesis' row-wise boundary conditions on the box
`Q = (0, ½)³` only stationary TSD data propagate. The obstruction is that row-wise conditions
give `E_{ab}` and `E_{ba}` different parities, so symmetry on `Q` is not a condition on each
Fourier mode. This file shows that boundary conditions compatible with the tensor structure
repair Props 4.17 and 4.19 on the box.

## Tensorial mirror conditions

Let `s_i(a) = -1` if `a = i` and `1` otherwise (`sgn`). The reflection `x_i ↦ -x_i` acts on
vectors by `D_i = diag(s_i)` and on matrices by `M ↦ D_i M D_i`. The *mirror* parities are
* `σ_a(R_i x) = s_i(a) σ_a(x)` (a vector field; `mirrorV`),
* `E(R_i x) = D_i E(x) D_i` (an even tensor; `mirrorM 1`),
* `B(R_i x) = -D_i B(x) D_i` (a pseudo-tensor; `mirrorM (-1)`),
and for the complex (4.16) of Prop 4.19, `u` even (`mirrorR`), `S` even, `T` odd. These are the
parities forced by the complex: the symbols intertwine (`gradSym_mirror`, `curlSym_mirror`,
`hessS_mirror`, `curlS_mirror`). On a face `x_i ∈ {0, ½}` an entry odd in `x_i` vanishes, and
the trace conditions of the domains are those of the odd entries that the operator
differentiates across the face: `σ · n = 0` for `σ ∈ D(grad)`; `E_{nτ} = 0` for `E ∈ D(curl)`
and `E_{τn} = 0` for `E ∈ D(grad*) = H(div)`; `B_{ττ} = 0` for `B ∈ D(curl*)`. For (4.16): `u`
even (`∂_n u = 0`), `S_{nτ} = 0`, `T_{ττ} = 0`. Unlike the row-wise conditions, `D_i M D_i`
preserves symmetry and trace, so `E_{ab}` and `E_{ba}` have the same parity and the TSD fibres
are permuted by the reflections (`matSgn_mem_tsd`).

The box complexes are `mirrorComplex` (for Prop 4.17) and `mirrorSymComplex` (for Prop 4.19):
the periodic complexes of `Feec.Ch4.Torus`, `Feec.Ch4.TorusSym` restricted to the parity
subspaces (`Feec.Box.resComplex`). Their constraint spaces are `L²(TSD) ∩ fix`, i.e. TSD fields
with the mirror parities; as in `Feec.Ch4.Box`, divergence-free here means divergence-free
on `𝕋³` after extension, which on `Q` includes the normal condition of the mirror walls. That
these parity spaces are the bounded-domain Sobolev spaces with the stated traces is not proved
(it needs traces on `∂Q`).

## Main results

* `Refl3.lift`: a fibrewise reflection action on `ℓ²(ℤ³)` (`(R_i u)(k) = ρ_i(u(R_i k))`), and
  `intertwines_mulOp`: Fourier multipliers whose symbols intertwine the fibre actions intertwine
  the lifted actions.
* **`mirror_projection_hyp`**: the projection hypothesis `P_K D(L) ⊆ D(L)` of Prop 4.17 holds for
  the mirror box complex (it fails for the thesis' conditions on every bounded domain,
  `Feec.BoundedDomain.thesisComplex_not_projection_hyp`).
* **`mirror_prop_4_17`**, **`mirror_prop_4_17_exists`**: Prop 4.17 on the box with mirror
  conditions: TSD data propagate, with existence and uniqueness of the strong solution.
* **`mirror_prop_4_19`**, **`mirror_prop_4_19_exists`**: the same for Prop 4.19 (complex (4.16)).

Correction: on a bounded domain the conclusions of Props 4.17 and 4.19 depend on the boundary
conditions. With the thesis' (row-wise) conditions they fail
(`Feec.BoundedDomain.thesisComplex_orbit_not_propagate_unconditional`), and on the box only
static data propagate (`Feec.Box.mem_Kmax_boxTSD_iff`); with tensorial mirror conditions they
hold on the box.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17), §4.11 (Prop 4.19, (4.16))
* [AFW2010] (Hilbert complexes), [ArnoldHu2021] (the complex (4.16))
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace
open LinearPMap Set

namespace Feec.Box

open Feec.Torus Feec.Constraints HilbertComplex2

/-! ## Lifting a fibre action to `ℓ²(ℤ³)` -/

section Lift

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The reflection of indices as an equivalence. -/
def reflEquiv (i : Fin 3) : Z3 ≃ Z3 where
  toFun := refl i
  invFun := refl i
  left_inv := refl_refl i
  right_inv := refl_refl i

theorem refl_comm (i j : Fin 3) (k : Z3) : refl i (refl j k) = refl j (refl i k) := by
  ext c
  by_cases hi : c = i <;> by_cases hj : c = j
  · subst hi; subst hj; rfl
  · subst hi; simp [refl, hj]
  · subst hj; simp [refl, hi]
  · simp [refl, Function.update_of_ne hi, Function.update_of_ne hj]

/-- The lifted sequence is square-summable. -/
theorem memℓp_lift (g : Refl3 F) (i : Fin 3) (u : L2 Z3 F) :
    Memℓp (fun k => g.R i (u (refl i k))) 2 := by
  rw [memℓp_two_iff]
  have hn : ∀ k, ‖g.R i (u (refl i k))‖ = ‖u (refl i k)‖ := fun k => by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℝ), norm_eq_sqrt_re_inner (𝕜 := ℝ), g.inner_map]
  simp_rw [hn]
  exact (reflEquiv i).summable_iff.2 (summable_norm_sq_L2 u)

/-- One lifted reflection. -/
def liftR (g : Refl3 F) (i : Fin 3) : L2 Z3 F →L[ℝ] L2 Z3 F :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun k => g.R i (u (refl i k)), memℓp_lift g i u⟩
      map_add' := fun u v => by ext k; simp; rfl
      map_smul' := fun r u => by ext k; simp [Pi.smul_apply] }
    1 fun u => by
      rw [one_mul]
      refine le_of_eq ?_
      have h1 := norm_sq_L2 (⟨fun k => g.R i (u (refl i k)), memℓp_lift g i u⟩ : L2 Z3 F)
      have h2 := norm_sq_L2 u
      have hn : ∀ k, ‖g.R i (u (refl i k))‖ = ‖u (refl i k)‖ := fun k => by
        rw [norm_eq_sqrt_re_inner (𝕜 := ℝ), norm_eq_sqrt_re_inner (𝕜 := ℝ), g.inner_map]
      have h3 : ∑' k, ‖u (refl i k)‖ ^ 2 = ∑' k, ‖u k‖ ^ 2 :=
        (reflEquiv i).tsum_eq fun k => ‖u k‖ ^ 2
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
      rw [h1, h2]
      simp_rw [hn]
      exact h3

@[simp] theorem liftR_apply (g : Refl3 F) (i : Fin 3) (u : L2 Z3 F) (k : Z3) :
    liftR g i u k = g.R i (u (refl i k)) := rfl

/-- **The fibrewise action lifted to `ℓ²(ℤ³)`**: `(R_i u)(k) = ρ_i(u(R_i k))`. -/
def Refl3.lift (g : Refl3 F) : Refl3 (L2 Z3 F) where
  R := liftR g
  invol i u := by ext k; simp [g.invol]
  inner_map i u v := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    simp only [liftR_apply, g.inner_map]
    exact (reflEquiv i).tsum_eq fun k => ⟪u k, v k⟫
  comm i j u := by
    ext k
    simp only [liftR_apply]
    rw [g.comm, refl_comm]

/-- **Multipliers intertwine the lifted actions** when their symbols intertwine the fibre
actions: `m_{R_i k} ρ_i = ρ'_i m_k`. -/
theorem intertwines_mulOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : Refl3 E) (g' : Refl3 F) (m : Z3 → E →L[ℝ] F)
    (hm : ∀ i k x, m (refl i k) (g.R i x) = g'.R i (m k x)) :
    Intertwines g.lift g'.lift (mulOp m) := by
  intro i u
  have hfun : (fun k => m k ((g.lift.R i (u : L2 Z3 E)) k)) =
      ⇑(g'.lift.R i (mulOp m u)) := by
    funext k
    change m k (g.R i ((u : L2 Z3 E) (refl i k))) = g'.R i (mulOp m u (refl i k))
    rw [mulOp_apply]
    have := hm i (refl i k) ((u : L2 Z3 E) (refl i k))
    rwa [refl_refl] at this
  have hmem : g.lift.R i (u : L2 Z3 E) ∈ (mulOp m).domain := by
    change Memℓp _ 2
    rw [hfun]; exact lp.memℓp _
  refine ⟨hmem, lp.ext ?_⟩
  funext k
  rw [mulOp_apply]
  exact congrFun hfun k

end Lift

/-! ## The mirror sign actions -/

section Signs

/-- `s_i(a) = -1` if `a = i`, `1` otherwise. -/
def sgn (i a : Fin 3) : ℝ := if a = i then -1 else 1

theorem sgn_mul_self (i a : Fin 3) : sgn i a * sgn i a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem sgn_sq (i a : Fin 3) : (sgn i a : ℂ) * sgn i a = 1 := by
  rw [← Complex.ofReal_mul, sgn_mul_self, Complex.ofReal_one]

/-- `ξ_{R_i k} = D_i ξ_k`. -/
theorem freq_refl_eq_sgn (i : Fin 3) (k : Z3) (b : Fin 3) :
    freq (refl i k) b = sgn i b * freq k b := by
  rw [freq_refl_apply, sgn]; split_ifs <;> ring

/-- `σ ↦ D_i σ` on vectors. -/
def vecSgn (i : Fin 3) : Vec3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => vec fun a => (sgn i a : ℂ) * u a
      map_add' := fun u v => by ext a; simp [mul_add]
      map_smul' := fun r u => by ext a; simp [Complex.real_smul]; ring }

@[simp] theorem vecSgn_apply (i : Fin 3) (u : Vec3) (a : Fin 3) :
    vecSgn i u a = (sgn i a : ℂ) * u a := rfl

/-- `M ↦ ε D_i M D_i` on matrices. -/
def matSgn (ε : ℝ) (i : Fin 3) : Mat3 →L[ℝ] Mat3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => mat fun a b => (ε * sgn i a * sgn i b : ℝ) * M (a, b)
      map_add' := fun M N => by ext ⟨a, b⟩; simp [mul_add]
      map_smul' := fun r M => by ext ⟨a, b⟩; simp [Complex.real_smul]; ring }

@[simp] theorem matSgn_apply (ε : ℝ) (i : Fin 3) (M : Mat3) (a b : Fin 3) :
    matSgn ε i M (a, b) = ((ε * sgn i a * sgn i b : ℝ) : ℂ) * M (a, b) := rfl

/-- The mirror action on vector fields. -/
def mirrorVf : Refl3 Vec3 where
  R := vecSgn
  invol i u := by ext a; simp only [vecSgn_apply, ← mul_assoc, sgn_sq, one_mul]
  inner_map i u v := by
    simp only [inner_vec, vecSgn_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := sgn_mul_self i a
    linear_combination ((u a).re * (v a).re + (u a).im * (v a).im) * this
  comm i j u := by ext a; simp only [vecSgn_apply]; ring

/-- The mirror action on matrix fields, `M ↦ ε D_i M D_i` (`ε = ±1`). -/
def mirrorMf (ε : ℝ) (hε : ε * ε = 1) : Refl3 Mat3 where
  R := matSgn ε
  invol i M := by
    ext ⟨a, b⟩
    simp only [matSgn_apply, ← mul_assoc, ← Complex.ofReal_mul]
    have : ε * sgn i a * sgn i b * ε * sgn i a * sgn i b = 1 := by
      have h1 := sgn_mul_self i a; have h2 := sgn_mul_self i b
      linear_combination (sgn i a * sgn i a * (sgn i b * sgn i b)) * hε +
        (sgn i b * sgn i b) * h1 + h2
    rw [this, Complex.ofReal_one, one_mul]
  inner_map i M N := by
    simp only [inner_mat, matSgn_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h1 := sgn_mul_self i a; have h2 := sgn_mul_self i b
    have : (ε * sgn i a * sgn i b) * (ε * sgn i a * sgn i b) = 1 := by
      linear_combination (sgn i a * sgn i a * (sgn i b * sgn i b)) * hε +
        (sgn i b * sgn i b) * h1 + h2
    linear_combination ((M (a, b)).re * (N (a, b)).re + (M (a, b)).im * (N (a, b)).im) * this
  comm i j M := by ext ⟨a, b⟩; simp only [matSgn_apply]; push_cast; ring

/-- The reflection permutes the TSD fibres: `ε D_i tsd(ξ_{R_i k}) D_i = tsd(ξ_k)`. -/
theorem matSgn_mem_tsd (ε : ℝ) (i : Fin 3) (k : Z3) {M : Mat3} (hM : M ∈ tsd (freq (refl i k))) :
    matSgn ε i M ∈ tsd (freq k) := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun a b => ?_, ?_, fun a => ?_⟩
  · simp only [matSgn_apply, h1 a b]; push_cast; ring
  · simp only [matSgn_apply]
    have : ∀ a, ((ε * sgn i a * sgn i a : ℝ) : ℂ) * M (a, a) = ε * M (a, a) := fun a => by
      rw [mul_assoc, sgn_mul_self, mul_one]
    simp only [this, ← Finset.mul_sum, h2, mul_zero]
  · simp only [matSgn_apply]
    have h := h3 a
    simp only [freq_refl_eq_sgn] at h
    have : ∑ b, ((ε * sgn i a * sgn i b : ℝ) : ℂ) * M (a, b) * (freq k b : ℂ) =
        (ε * sgn i a : ℂ) * ∑ b, M (a, b) * ((sgn i b * freq k b : ℝ) : ℂ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; push_cast; ring
    rw [this, h, mul_zero]

/-- **The gradient symbol intertwines the mirror actions**: `grad_{R_i ξ} (D_i σ) = D_i (grad_ξ σ)
D_i`. -/
theorem gradSym_mirror (i : Fin 3) (k : Z3) (u : Vec3) :
    gradSym (freq (refl i k)) (vecSgn i u) = matSgn 1 i (gradSym (freq k) u) := by
  ext ⟨a, b⟩
  simp only [gradSym_apply, vecSgn_apply, matSgn_apply, freq_refl_eq_sgn]
  push_cast; ring

/-- **The curl symbol intertwines the mirror actions with a sign** (`curl` maps tensors to
pseudo-tensors): `curl_{R_i ξ} (ε D_i M D_i) = -ε D_i (curl_ξ M) D_i`. -/
theorem curlSym_mirror (ε : ℝ) (i : Fin 3) (k : Z3) (M : Mat3) :
    curlSym (freq (refl i k)) (matSgn ε i M) = matSgn (-ε) i (curlSym (freq k) M) := by
  ext ⟨a, b⟩
  simp only [curlSym_apply, jM_apply, curlR_apply, cross, matSgn_apply, freq_refl_eq_sgn]
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [sgn] <;> ring

end Signs

/-! ## Prop 4.17 on the box with mirror conditions -/

section Mirror417

/-- The mirror action on `L²(V)`. -/
def mirrorV : Refl3 L2V := mirrorVf.lift

/-- The mirror action on `L²(M)`, even (`ε = 1`) or odd (`ε = -1`). -/
def mirrorM (ε : ℝ) (hε : ε * ε = 1) : Refl3 L2M := (mirrorMf ε hε).lift

theorem one_mul_one : (1 : ℝ) * 1 = 1 := one_mul 1
theorem neg_one_mul_neg_one : (-1 : ℝ) * -1 = 1 := by norm_num

/-- `grad` intertwines the vector and even-tensor mirror actions. -/
theorem intertwines_grad : Intertwines mirrorV (mirrorM 1 one_mul_one) periodicComplex.d0 :=
  intertwines_mulOp mirrorVf (mirrorMf 1 one_mul_one) (fun k => gradSym (freq k))
    fun i k u => gradSym_mirror i k u

/-- `curl` intertwines the even-tensor and pseudo-tensor mirror actions. -/
theorem intertwines_curl :
    Intertwines (mirrorM 1 one_mul_one) (mirrorM (-1) neg_one_mul_neg_one) periodicComplex.d1 :=
  intertwines_mulOp (mirrorMf 1 one_mul_one) (mirrorMf (-1) neg_one_mul_neg_one)
    (fun k => curlSym (freq k)) fun i k M => curlSym_mirror 1 i k M

/-- **The box complex with mirror conditions**: `H¹(V) → H(curl; M) → L²(M)` on the parity
subspaces (`σ · n = 0`, `E_{nτ} = 0`). -/
def mirrorComplex : HilbertComplex2 mirrorV.fix (mirrorM 1 one_mul_one).fix
    (mirrorM (-1) neg_one_mul_neg_one).fix :=
  resComplex periodicComplex mirrorV (mirrorM 1 one_mul_one) (mirrorM (-1) neg_one_mul_neg_one)
    intertwines_grad intertwines_curl

/-- The mirror actions preserve `L²(TSD)`. -/
theorem mirrorM_mem_L2TSD (ε : ℝ) (hε : ε * ε = 1) (i : Fin 3) {A : L2M} (hA : A ∈ L2TSD) :
    (mirrorM ε hε).R i A ∈ L2TSD := fun k => matSgn_mem_tsd ε i k (hA (refl i k))

/-- `L²(TSD)` on the box with mirror conditions (even tensors). -/
abbrev mirrorTSD1 : Submodule ℝ (mirrorM 1 one_mul_one).fix :=
  L2TSD.comap (mirrorM 1 one_mul_one).fix.subtype

/-- `L²(TSD)` on the box with mirror conditions (pseudo-tensors). -/
abbrev mirrorTSD2 : Submodule ℝ (mirrorM (-1) neg_one_mul_neg_one).fix :=
  L2TSD.comap (mirrorM (-1) neg_one_mul_neg_one).fix.subtype

instance : mirrorTSD1.HasOrthogonalProjection := by
  have hc : _root_.IsClosed (mirrorTSD1 : Set (mirrorM 1 one_mul_one).fix) :=
    (isClosed_of_hasOrthogonalProjection L2TSD).preimage continuous_subtype_val
  have : CompleteSpace mirrorTSD1 := hc.completeSpace_coe
  infer_instance

instance : mirrorTSD2.HasOrthogonalProjection := by
  have hc : _root_.IsClosed (mirrorTSD2 : Set (mirrorM (-1) neg_one_mul_neg_one).fix) :=
    (isClosed_of_hasOrthogonalProjection L2TSD).preimage continuous_subtype_val
  have : CompleteSpace mirrorTSD2 := hc.completeSpace_coe
  infer_instance

/-- **The projection hypothesis of Prop 4.17 holds on the box with mirror conditions**:
`P_K D(L) ⊆ D(L)` for `K = {0} × L²(TSD) × L²(TSD)`. (For the thesis' conditions it fails on
every bounded domain, `Feec.BoundedDomain.thesisComplex_not_projection_hyp`.) -/
theorem mirror_projection_hyp : ∀ x ∈ mirrorComplex.domL,
    projKc mirrorV.fix mirrorTSD1 mirrorTSD2 x ∈ mirrorComplex.domL :=
  (prop_4_17_hyps_res (H := periodicComplex) (G0 := mirrorV) (h0 := intertwines_grad)
    (h1 := intertwines_curl) L2TSD L2TSD L2TSD_le_ker projKc_mem_domL curlT_mem_L2TSD
    adjoint_curlT_mem_L2TSD (fun i _ hA => mirrorM_mem_L2TSD 1 _ i hA)
    (fun i _ hA => mirrorM_mem_L2TSD (-1) _ i hA)).2.1

/-- **Thesis Prop 4.17 on the box with mirror conditions.** For the box complex
`H¹(V) → H(curl; M) → L²(M)` with the tensorial mirror boundary conditions, every strong solution
of (4.14) with data `(0, E₀, B₀)`, `E₀, B₀ ∈ L²(TSD)`, keeps `σ ≡ 0` and `E, B ∈ L²(TSD)`, and
`(E, B)` solves (4.15). No hypothesis beyond the solution.

Correction: on the box this holds for the mirror conditions; for the thesis' conditions only
static data propagate (`Feec.Box.mem_Kmax_boxTSD_iff`).

See [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem mirror_prop_4_17 {T : ℝ} {E₀ : (mirrorM 1 one_mul_one).fix}
    {B₀ : (mirrorM (-1) neg_one_mul_neg_one).fix}
    {U : ℝ → Tot mirrorV.fix (mirrorM 1 one_mul_one).fix (mirrorM (-1) neg_one_mul_neg_one).fix}
    (hE₀ : E₀ ∈ mirrorTSD1) (hB₀ : B₀ ∈ mirrorTSD2)
    (hU : IsStrongSolution (-mirrorComplex.waveOp) T (ini mirrorV.fix E₀ B₀) 0 U) :
    (∀ t ∈ Icc 0 T, U t ∈ Kc mirrorV.fix mirrorTSD1 mirrorTSD2) ∧
      IsReducedSolution mirrorComplex T E₀ B₀ (fun t => (tot _ _ _ (U t)).2.1)
        (fun t => (tot _ _ _ (U t)).2.2) :=
  prop_4_17_res (H := periodicComplex) (G0 := mirrorV) (h0 := intertwines_grad)
    (h1 := intertwines_curl) L2TSD L2TSD L2TSD_le_ker projKc_mem_domL curlT_mem_L2TSD
    adjoint_curlT_mem_L2TSD (fun i _ hA => mirrorM_mem_L2TSD 1 _ i hA)
    (fun i _ hA => mirrorM_mem_L2TSD (-1) _ i hA) hE₀ hB₀ hU

/-- **Thesis Prop 4.17 on the box with mirror conditions, with existence**: for TSD data
`(0, E₀, B₀) ∈ D(L)` the Hodge wave (4.14) has a strong solution on `[0, T]` (Stone's theorem,
`Feec.HilbertComplex2.waveGroup`), unique among strong solutions; it stays TSD and `(E, B)`
solves (4.15).

See [QuennevilleBelair2015, §4.10, Prop 4.17, Thm 4.3]. -/
theorem mirror_prop_4_17_exists (T : ℝ) {E₀ : (mirrorM 1 one_mul_one).fix}
    {B₀ : (mirrorM (-1) neg_one_mul_neg_one).fix}
    (hE₀ : E₀ ∈ mirrorTSD1) (hB₀ : B₀ ∈ mirrorTSD2)
    (hD : ini mirrorV.fix E₀ B₀ ∈ mirrorComplex.domL) :
    ∃ U : ℝ → Tot mirrorV.fix (mirrorM 1 one_mul_one).fix (mirrorM (-1) neg_one_mul_neg_one).fix,
      IsStrongSolution (-mirrorComplex.waveOp) T (ini mirrorV.fix E₀ B₀) 0 U ∧
      (∀ U', IsStrongSolution (-mirrorComplex.waveOp) T (ini mirrorV.fix E₀ B₀) 0 U' →
        EqOn U' U (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, U t ∈ Kc mirrorV.fix mirrorTSD1 mirrorTSD2) ∧
      IsReducedSolution mirrorComplex T E₀ B₀ (fun t => (tot _ _ _ (U t)).2.1)
        (fun t => (tot _ _ _ (U t)).2.2) :=
  prop_4_17_res_exists (H := periodicComplex) (G0 := mirrorV) (h0 := intertwines_grad)
    (h1 := intertwines_curl) L2TSD L2TSD L2TSD_le_ker projKc_mem_domL curlT_mem_L2TSD
    adjoint_curlT_mem_L2TSD (fun i _ hA => mirrorM_mem_L2TSD 1 _ i hA)
    (fun i _ hA => mirrorM_mem_L2TSD (-1) _ i hA) T hE₀ hB₀ hD

end Mirror417

/-! ## Prop 4.19 on the box with mirror conditions -/

section Mirror419

open Feec.TorusSym

/-- `ε D_i M D_i` preserves symmetry. -/
theorem matSgn_mem_symSub (ε : ℝ) (i : Fin 3) {M : Mat3} (hM : M ∈ symSub) :
    matSgn ε i M ∈ symSub := fun a b => by
  simp only [matSgn_apply, hM a b]; push_cast; ring

/-- `ε D_i M D_i` preserves the trace condition. -/
theorem matSgn_mem_trSub (ε : ℝ) (i : Fin 3) {M : Mat3} (hM : M ∈ trSub) :
    matSgn ε i M ∈ trSub := by
  change ∑ a, _ = 0
  have : ∀ a, matSgn ε i M (a, a) = ε * M (a, a) := fun a => by
    rw [matSgn_apply, mul_assoc, sgn_mul_self, mul_one]
  simp only [this, ← Finset.mul_sum]
  rw [show ∑ a, M (a, a) = 0 from hM, mul_zero]

/-- The even mirror action on symmetric matrices. -/
def symSgn (i : Fin 3) : Sym3 →L[ℝ] Sym3 :=
  (matSgn 1 i ∘L symSub.subtypeL).codRestrict symSub fun M => matSgn_mem_symSub 1 i M.2

/-- The odd mirror action on trace-free matrices. -/
def trSgn (i : Fin 3) : Tr3 →L[ℝ] Tr3 :=
  (matSgn (-1) i ∘L trSub.subtypeL).codRestrict trSub fun M => matSgn_mem_trSub (-1) i M.2

@[simp] theorem coe_symSgn (i : Fin 3) (M : Sym3) : (symSgn i M : Mat3) = matSgn 1 i M := rfl

@[simp] theorem coe_trSgn (i : Fin 3) (M : Tr3) : (trSgn i M : Mat3) = matSgn (-1) i M := rfl

/-- The trivial action (even scalars `u`). -/
def mirrorRf : Refl3 ℂ where
  R _ := ContinuousLinearMap.id ℝ ℂ
  invol _ _ := rfl
  inner_map _ _ _ := rfl
  comm _ _ _ := rfl

/-- The even mirror action on `S`. -/
def mirrorSf : Refl3 Sym3 where
  R := symSgn
  invol i M := Subtype.ext ((mirrorMf 1 one_mul_one).invol i (M : Mat3))
  inner_map i M N := by
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact (mirrorMf 1 one_mul_one).inner_map i M N
  comm i j M := Subtype.ext ((mirrorMf 1 one_mul_one).comm i j (M : Mat3))

/-- The odd mirror action on `T`. -/
def mirrorTf : Refl3 Tr3 where
  R := trSgn
  invol i M := Subtype.ext ((mirrorMf (-1) neg_one_mul_neg_one).invol i (M : Mat3))
  inner_map i M N := by
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact (mirrorMf (-1) neg_one_mul_neg_one).inner_map i M N
  comm i j M := Subtype.ext ((mirrorMf (-1) neg_one_mul_neg_one).comm i j (M : Mat3))

/-- The Hessian symbol intertwines (even `u`, even `S`). -/
theorem hessS_mirror (i : Fin 3) (k : Z3) (c : ℂ) :
    hessS (freq (refl i k)) (mirrorRf.R i c) = mirrorSf.R i (hessS (freq k) c) := by
  apply Subtype.ext
  ext ⟨a, b⟩
  change hessM _ c (a, b) = matSgn 1 i (hessM _ c) (a, b)
  simp only [hessM_apply, matSgn_apply, freq_refl_eq_sgn]
  push_cast; ring

/-- The curl symbol intertwines (even `S`, odd `T`). -/
theorem curlS_mirror (i : Fin 3) (k : Z3) (M : Sym3) :
    curlS (freq (refl i k)) (mirrorSf.R i M) = mirrorTf.R i (curlS (freq k) M) :=
  Subtype.ext (curlSym_mirror 1 i k M)

/-- The mirror action on `L²(R)` (even scalars). -/
def mirrorR : Refl3 L2R := mirrorRf.lift
/-- The mirror action on `L²(S)` (even tensors). -/
def mirrorS : Refl3 L2S := mirrorSf.lift
/-- The mirror action on `L²(T)` (pseudo-tensors). -/
def mirrorT : Refl3 L2T := mirrorTf.lift

theorem intertwines_hess : Intertwines mirrorR mirrorS symComplex.d0 :=
  intertwines_mulOp mirrorRf mirrorSf (fun k => hessS (freq k)) fun i k c => hessS_mirror i k c

theorem intertwines_curlS : Intertwines mirrorS mirrorT symComplex.d1 :=
  intertwines_mulOp mirrorSf mirrorTf (fun k => curlS (freq k)) fun i k M => curlS_mirror i k M

/-- **The box complex (4.16) with mirror conditions**: `H²(R) → H(curl, S) → L²(T)` on the
parity subspaces (`u` even, `S` even, `T` odd). -/
def mirrorSymComplex : HilbertComplex2 mirrorR.fix mirrorS.fix mirrorT.fix :=
  resComplex symComplex mirrorR mirrorS mirrorT intertwines_hess intertwines_curlS

theorem mirrorS_mem_L2TSDS (i : Fin 3) {A : L2S} (hA : A ∈ L2TSDS) : mirrorS.R i A ∈ L2TSDS :=
  fun k => matSgn_mem_tsd 1 i k (hA (refl i k))

theorem mirrorT_mem_L2TSDT (i : Fin 3) {A : L2T} (hA : A ∈ L2TSDT) : mirrorT.R i A ∈ L2TSDT :=
  fun k => matSgn_mem_tsd (-1) i k (hA (refl i k))

/-- `L²(TSD; S)` on the box with mirror conditions. -/
abbrev mirrorTSDS : Submodule ℝ mirrorS.fix := L2TSDS.comap mirrorS.fix.subtype

/-- `L²(TSD; T)` on the box with mirror conditions. -/
abbrev mirrorTSDT : Submodule ℝ mirrorT.fix := L2TSDT.comap mirrorT.fix.subtype

instance : mirrorTSDS.HasOrthogonalProjection := by
  have hc : _root_.IsClosed (mirrorTSDS : Set mirrorS.fix) :=
    (isClosed_of_hasOrthogonalProjection L2TSDS).preimage continuous_subtype_val
  have : CompleteSpace mirrorTSDS := hc.completeSpace_coe
  infer_instance

instance : mirrorTSDT.HasOrthogonalProjection := by
  have hc : _root_.IsClosed (mirrorTSDT : Set mirrorT.fix) :=
    (isClosed_of_hasOrthogonalProjection L2TSDT).preimage continuous_subtype_val
  have : CompleteSpace mirrorTSDT := hc.completeSpace_coe
  infer_instance

/-- The projection hypothesis of Prop 4.19 holds on the box with mirror conditions. -/
theorem mirror_projection_hyp_419 : ∀ x ∈ mirrorSymComplex.domL,
    projKc mirrorR.fix mirrorTSDS mirrorTSDT x ∈ mirrorSymComplex.domL :=
  (prop_4_17_hyps_res (H := symComplex) (G0 := mirrorR) (h0 := intertwines_hess)
    (h1 := intertwines_curlS) L2TSDS L2TSDT L2TSDS_le_ker TorusSym.projKc_mem_domL
    curlST_mem_L2TSDT adjoint_curlST_mem_L2TSDS (fun i _ hA => mirrorS_mem_L2TSDS i hA)
    (fun i _ hA => mirrorT_mem_L2TSDT i hA)).2.1

/-- **Thesis Prop 4.19 on the box with mirror conditions.** For the box complex (4.16)
`H²(R) → H(curl, S) → L²(T)` with mirror boundary conditions, every strong solution of (4.18)
with data `(0, E₀, B₀)`, `E₀ ∈ L²(TSD; S)`, `B₀ ∈ L²(TSD; T)`, stays in
`{0} × L²(TSD) × L²(TSD)` and `(E, B)` solves the reduced system.

See [QuennevilleBelair2015, §4.11, Prop 4.19]. -/
theorem mirror_prop_4_19 {T : ℝ} {E₀ : mirrorS.fix} {B₀ : mirrorT.fix}
    {U : ℝ → Tot mirrorR.fix mirrorS.fix mirrorT.fix}
    (hE₀ : E₀ ∈ mirrorTSDS) (hB₀ : B₀ ∈ mirrorTSDT)
    (hU : IsStrongSolution (-mirrorSymComplex.waveOp) T (ini mirrorR.fix E₀ B₀) 0 U) :
    (∀ t ∈ Icc 0 T, U t ∈ Kc mirrorR.fix mirrorTSDS mirrorTSDT) ∧
      IsReducedSolution mirrorSymComplex T E₀ B₀ (fun t => (tot _ _ _ (U t)).2.1)
        (fun t => (tot _ _ _ (U t)).2.2) :=
  prop_4_17_res (H := symComplex) (G0 := mirrorR) (h0 := intertwines_hess)
    (h1 := intertwines_curlS) L2TSDS L2TSDT L2TSDS_le_ker TorusSym.projKc_mem_domL
    curlST_mem_L2TSDT adjoint_curlST_mem_L2TSDS (fun i _ hA => mirrorS_mem_L2TSDS i hA)
    (fun i _ hA => mirrorT_mem_L2TSDT i hA) hE₀ hB₀ hU

/-- **Thesis Prop 4.19 on the box with mirror conditions, with existence** (Stone's theorem):
for TSD data in `D(L)`, (4.18) has a unique strong solution on `[0, T]`, which stays TSD.

See [QuennevilleBelair2015, §4.11, Prop 4.19, Thm 4.3]. -/
theorem mirror_prop_4_19_exists (T : ℝ) {E₀ : mirrorS.fix} {B₀ : mirrorT.fix}
    (hE₀ : E₀ ∈ mirrorTSDS) (hB₀ : B₀ ∈ mirrorTSDT)
    (hD : ini mirrorR.fix E₀ B₀ ∈ mirrorSymComplex.domL) :
    ∃ U : ℝ → Tot mirrorR.fix mirrorS.fix mirrorT.fix,
      IsStrongSolution (-mirrorSymComplex.waveOp) T (ini mirrorR.fix E₀ B₀) 0 U ∧
      (∀ U', IsStrongSolution (-mirrorSymComplex.waveOp) T (ini mirrorR.fix E₀ B₀) 0 U' →
        EqOn U' U (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, U t ∈ Kc mirrorR.fix mirrorTSDS mirrorTSDT) ∧
      IsReducedSolution mirrorSymComplex T E₀ B₀ (fun t => (tot _ _ _ (U t)).2.1)
        (fun t => (tot _ _ _ (U t)).2.2) :=
  prop_4_17_res_exists (H := symComplex) (G0 := mirrorR) (h0 := intertwines_hess)
    (h1 := intertwines_curlS) L2TSDS L2TSDT L2TSDS_le_ker TorusSym.projKc_mem_domL
    curlST_mem_L2TSDT adjoint_curlST_mem_L2TSDS (fun i _ hA => mirrorS_mem_L2TSDS i hA)
    (fun i _ hA => mirrorT_mem_L2TSDT i hA) T hE₀ hB₀ hD

end Mirror419

end Feec.Box
