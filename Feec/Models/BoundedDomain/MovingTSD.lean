module

public import Feec.Models.BoundedDomain.InvariantCore
public import Feec.Domain.WholeSpace
public import Feec.HilbertComplex.Transport

/-!
# Moving data in `K*` on bounded domains: eigenfields with both boundary conditions vanish

For the thesis' complex `H̊¹(Ω; ℝ³) → H̊(curl, Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` on a bounded open
`Ω ⊆ ℝ³` and `K = {0} × L²(TSD) × L²(TSD)`, `Feec.Models.BoundedDomain.gradCurl_coreSub_spectral`
reduces the existence of a moving datum in the invariant core `K*` (under a complete set of
eigenvectors of `L²`) to the existence of a nonzero **TSD eigenfield**
`u ∈ L²(TSD) ∩ H̊(curl)`, `curl† curl u = ξ² u`, `ξ > 0`. Here `curl†` is the maximal curl:
the eigenproblem imposes the electric condition on `u` only.

This file proves that such an eigenfield cannot satisfy the condition a second time: if moreover
`curl u ∈ H̊(curl)`, then `u = 0`, on **every** bounded open `Ω` and with no symmetry or
divergence condition (`eq_zero_of_isEigenfield_of_mem_minimal`). Proof:

1. extension by zero (`Feec.Domain.ConstCoeffOp.extendL2F`): Green's formula for `H̊(curl)`
   against smooth fields with no boundary condition (`Feec.Domain.ConstCoeffOp.minimal_green`)
   gives `curl ũ = (curl u)~` and `curl (curl u)~ = ξ² ũ` weakly on `ℝ³`;
2. mollification (`Feec.Domain.kconv`, `Feec.Domain.ConstCoeffOp.apply_kconv`): `V = ρ ⋆ ũ` is a
   smooth compactly supported field with `curl curl V = ξ² V` pointwise;
3. `div V = 0` (`div curl = 0`), so `ΔV = -ξ² V` (`curlM_curlM_eq`), and a **Pohozaev identity**
   kills compactly supported solutions of the Helmholtz equation (`eq_zero_of_laplacian_eq`):
   testing `ΔV = -ξ² V` against `V` and against the dilation field `x · ∇V` gives
   `‖∇V‖² = ξ² ‖V‖²` and `½ ‖∇V‖² = (3/2) ξ² ‖V‖²`;
4. `ρ_m ⋆ ũ → ũ` in `L²`, so `ũ = 0`.

Consequently (`not_coreSub_le_stationary_iff`), a moving datum of `K*` comes from a TSD
eigenfield whose magnetic field `curl u` violates the electric boundary condition, i.e. has a
nonzero tangential trace (weakly: `curl u ∉ H̊(curl)`).

## What remains open

The extension-by-zero argument does not decide whether TSD eigenfields exist: for an eigenfield
`u`, `(-Δ - ξ²) ũ` is the boundary layer `(n × curl u) δ_{∂Ω}` (row-wise), which need not vanish.
For vector fields the corresponding claim is false (on the unit ball the toroidal fields
`j_l(k r) (x × ∇ Y_l^m)`, `j_l(k) = 0`, lie in `H̊¹ ∩ ker div` and solve `curl curl u = k² u`), so
the matrix structure must enter. Heuristically, for smooth `Ω` the layer is then a
transverse-traceless tensor on `∂Ω` (symmetric, trace-free, divergence-free, orthogonal to the
second fundamental form), hence zero when every boundary component is a sphere (no holomorphic
quadratic differentials in genus `0`), which would make `K*` stationary on such domains; higher
genus is not decided. None of this is formalized (it needs traces on curved boundaries and the
Riemann–Roch count).

The spectral hypothesis (`EigenDense`) is proved on cubes (`Feec.Models.Cube.EigenDense`) and on
boxes with arbitrary, possibly unequal, sides (`Feec.Models.Box.eigenDense_gradCurl_box`); on both,
no TSD eigenfield exists and `K*` is stationary (`Feec.Models.Cube.Ident.mem_invariantCore_tsd_iff`,
`Feec.Models.Box.not_exists_tsd_eigenfield_box`, `Feec.Models.Box.mem_invariantCore_tsd_iff`).
On a general bounded `Ω` (a ball, a Lipschitz domain) the question is **still open**: neither
`EigenDense` nor the (non)existence of a TSD eigenfield with `curl u ∉ H̊(curl)` is proved, and
`not_coreSub_le_stationary_iff` below is the strongest general statement.

## Main results

* `eq_zero_of_laplacian_eq`: compactly supported smooth solutions of `Δf = -c f`, `c ≠ 0`,
  vanish (Pohozaev).
* `eq_zero_of_curlM_curlM_eq`: the same for `curl curl V = c V` (row-wise, matrix fields).
* **`eq_zero_of_isEigenfield_of_mem_minimal`**: no nonzero electric eigenfield `u` with
  `curl u ∈ H̊(curl)`, on any bounded open `Ω`.
* **`not_coreSub_le_stationary_iff`**: `K*` is not stationary iff some nonzero TSD eigenfield has
  `curl u ∉ H̊(curl)` (under the eigenvector hypothesis).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §4.4 (mollification), §9.1 (weak derivatives)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace LinearPMap ContDiff
open MeasureTheory Set Filter Topology Feec.Domain

namespace Feec.Models.BoundedDomain

/-! ### A Pohozaev identity: compactly supported Helmholtz solutions vanish -/

section Pohozaev

variable {f g : R3 → ℝ}

theorem hasCompactSupport_pd (hf : HasCompactSupport f) (k : Fin 3) :
    HasCompactSupport (pd k f) :=
  hf.fderiv_apply (𝕜 := ℝ) _

/-- Integration by parts on `ℝ³`: `∫ ∂_k g · h = -∫ g ∂_k h` for `g ∈ C_c^∞`, `h ∈ C¹`. -/
theorem integral_pd_mul_univ (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {h : R3 → ℝ} (hh : ContDiff ℝ 1 h) (k : Fin 3) :
    ∫ x, pd k g x * h x = -∫ x, g x * pd k h x := by
  have := integral_pd_mul (Ω := (univ : Set R3)) ⟨hg, hgc, subset_univ _⟩ hh k
  simpa only [Measure.restrict_univ] using this

theorem contDiff_coord_mul (hg : ContDiff ℝ ∞ g) (k : Fin 3) :
    ContDiff ℝ ∞ (fun y : R3 => y k * g y) := by
  fun_prop

theorem pd_coord_mul (hg : Differentiable ℝ g) (k j : Fin 3) (x : R3) :
    pd j (fun y : R3 => y k * g y) x = x k * pd j g x + (if j = k then g x else 0) := by
  rw [pd_mul (differentiable_apply k x) (hg x), pd_coord]
  split_ifs <;> ring

/-- **The virial identity** `∫ g (x_k ∂_k g) = -½ ∫ g²` for `g ∈ C_c^∞(ℝ³)`. -/
theorem integral_mul_coord_mul_pd (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (k : Fin 3) :
    ∫ x, g x * (x k * pd k g x) = -(1 / 2) * ∫ x, g x * g x := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have hpd := contDiff_pd_top hg k
  have h1 := integral_pd_mul_univ hg hgc ((contDiff_coord_mul hg k).of_le (by simp)) k
  have e1 : ∫ x, pd k g x * (x k * g x) = ∫ x, g x * (x k * pd k g x) :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have hA : Integrable fun x => g x * (x k * pd k g x) :=
    (hg.continuous.mul ((continuous_apply k).mul hpd.continuous)).integrable_of_hasCompactSupport
      hgc.mul_right
  have hB : Integrable fun x => g x * g x :=
    (hg.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_right
  have e2 : ∫ x, g x * pd k (fun y => y k * g y) x =
      (∫ x, g x * (x k * pd k g x)) + ∫ x, g x * g x := by
    rw [← integral_add hA hB]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [pd_coord_mul hd k k x]
    ring
  rw [e1, e2] at h1
  linarith

/-- `∫ g Δg`-type identity: `∫ ∂_j ∂_j f · f = -∫ (∂_j f)²`. -/
theorem integral_pd_pd_mul (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (j : Fin 3) :
    ∫ x, pd j (pd j f) x * f x = -∫ x, pd j f x * pd j f x :=
  integral_pd_mul_univ (contDiff_pd_top hf j) (hasCompactSupport_pd hfc j)
    (hf.of_le (by simp)) j

/-- `∫ ∂_j ∂_j f · (x_k ∂_k f) = ½ ∫ (∂_j f)² - δ_{jk} ∫ (∂_j f)²`. -/
theorem integral_pd_pd_mul_coord (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (j k : Fin 3) :
    ∫ x, pd j (pd j f) x * (x k * pd k f x) =
      (1 / 2) * (∫ x, pd j f x * pd j f x) -
        (if j = k then ∫ x, pd j f x * pd j f x else 0) := by
  have hj := contDiff_pd_top hf j
  have hk := contDiff_pd_top hf k
  have hjc := hasCompactSupport_pd hfc j
  have hkd : Differentiable ℝ (pd k f) := hk.differentiable (by simp)
  have h1 := integral_pd_mul_univ hj hjc ((contDiff_coord_mul hk k).of_le (by simp)) j
  have hcomm : ∀ x, pd j (pd k f) x = pd k (pd j f) x := fun x =>
    pd_pd_comm (hf.of_le (by simp)) j k x
  have hcont1 : Continuous fun x => pd j f x * (x k * pd k (pd j f) x) :=
    hj.continuous.mul ((continuous_apply k).mul (contDiff_pd_top hj k).continuous)
  have hI1 : Integrable fun x => pd j f x * (x k * pd k (pd j f) x) :=
    hcont1.integrable_of_hasCompactSupport hjc.mul_right
  have hI2 : Integrable fun x => pd j f x * pd j f x :=
    (hj.continuous.mul hj.continuous).integrable_of_hasCompactSupport hjc.mul_right
  have e2 : ∫ x, pd j f x * pd j (fun y => y k * pd k f y) x =
      (∫ x, pd j f x * (x k * pd k (pd j f) x)) +
        (if j = k then ∫ x, pd j f x * pd j f x else 0) := by
    split_ifs with hjk
    · subst hjk
      rw [← integral_add hI1 hI2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [pd_coord_mul hkd j j x]
      ring
    · rw [add_zero]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [pd_coord_mul hkd k j x, hjk, hcomm x]
  rw [e2, integral_mul_coord_mul_pd hj hjc k] at h1
  rw [h1]
  ring

/-- **Compactly supported Helmholtz solutions vanish** (Pohozaev): if `f ∈ C_c^∞(ℝ³)` and
`Δf = -c f` with `c ≠ 0`, then `f = 0`. Testing the equation against `f` gives
`‖∇f‖² = c ‖f‖²`, against the dilation field `x · ∇f` gives `½ ‖∇f‖² = (3/2) c ‖f‖²`. -/
theorem eq_zero_of_laplacian_eq (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) {c : ℝ}
    (hc : c ≠ 0) (h : ∀ x, ∑ j, pd j (pd j f) x = -c * f x) : f = 0 := by
  have hint2 : ∀ j k, Integrable fun x => pd j (pd j f) x * (x k * pd k f x) := fun j k =>
    ((contDiff_pd_top (contDiff_pd_top hf j) j).continuous.mul
      ((continuous_apply k).mul (contDiff_pd_top hf k).continuous)).integrable_of_hasCompactSupport
      ((hasCompactSupport_pd hfc k).mul_left.mul_left)
  have hint1 : ∀ j, Integrable fun x => pd j (pd j f) x * f x := fun j =>
    ((contDiff_pd_top (contDiff_pd_top hf j) j).continuous.mul hf.continuous).integrable_of_hasCompactSupport
      hfc.mul_left
  set F := ∫ x, f x * f x
  set G := ∑ j, ∫ x, pd j f x * pd j f x with hG
  -- testing against `f`
  have hA : -c * F = -G := by
    have e : ∫ x, (∑ j, pd j (pd j f) x) * f x = ∑ j, ∫ x, pd j (pd j f) x * f x := by
      rw [← integral_finsetSum _ fun j _ => hint1 j]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only [Finset.sum_mul])
    simp only [h] at e
    rw [show (fun x => -c * f x * f x) = fun x => -c * (f x * f x) from
      funext fun x => by ring, integral_const_mul] at e
    rw [e, show -G = ∑ j, -∫ x, pd j f x * pd j f x by simp [G, Finset.sum_neg_distrib]]
    exact Finset.sum_congr rfl fun j _ => integral_pd_pd_mul hf hfc j
  -- testing against `x · ∇f`
  have hC : (3 / 2) * c * F = (1 / 2) * G := by
    have e1 : ∑ k, ∫ x, (∑ j, pd j (pd j f) x) * (x k * pd k f x) =
        ∑ k, ∑ j, ∫ x, pd j (pd j f) x * (x k * pd k f x) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← integral_finsetSum _ fun j _ => hint2 j k]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only [Finset.sum_mul])
    have e2 : ∑ k, ∫ x, (∑ j, pd j (pd j f) x) * (x k * pd k f x) = (3 / 2) * c * F := by
      simp only [h]
      have : ∀ k : Fin 3, ∫ x, -c * f x * (x k * pd k f x) = (1 / 2) * c * F := fun k => by
        rw [show (fun x => -c * f x * (x k * pd k f x)) = fun x => -c * (f x * (x k * pd k f x))
          from funext fun x => by ring, integral_const_mul, integral_mul_coord_mul_pd hf hfc k]
        ring
      simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    have e3 : ∑ k, ∑ j, ∫ x, pd j (pd j f) x * (x k * pd k f x) = (1 / 2) * G := by
      simp only [integral_pd_pd_mul_coord hf hfc]
      rw [Finset.sum_comm, hG, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      fin_cases j <;> simp <;> ring
    rw [← e2, e1, e3]
  have hF : F = 0 := by
    have : c * F = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hc
  have hcont : Continuous fun x => f x * f x := hf.continuous.mul hf.continuous
  have hae : (fun x => f x * f x) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (f x))
      (hcont.integrable_of_hasCompactSupport hfc.mul_right)).1 hF
  have h0 : (fun x => f x * f x) = 0 := Continuous.ae_eq_iff_eq volume hcont continuous_const |>.1 hae
  funext x
  exact mul_self_eq_zero.1 (congrFun h0 x)

end Pohozaev

/-! ### Matrix fields with `curl curl V = c V` -/

section CurlCurl

private theorem pd_fun_sub {f g : R3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (k : Fin 3) (x : R3) : pd k (fun y => f y - g y) x = pd k f x - pd k g x :=
  pd_sub hf hg k x

private theorem sum_fin3_rot (k : Fin 3) (f : Fin 3 → ℝ) :
    ∑ l, f l = f k + f (k + 1) + f (k + 2) := by
  fin_cases k <;> simp [Fin.sum_univ_three] <;> ring

private theorem fin3_add_two_add_one (k : Fin 3) : k + 2 + 1 = k := by fin_cases k <;> rfl
private theorem fin3_add_two_add_two (k : Fin 3) : k + 2 + 2 = k + 1 := by fin_cases k <;> rfl
private theorem fin3_add_one_add_one (k : Fin 3) : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
private theorem fin3_add_one_add_two (k : Fin 3) : k + 1 + 2 = k := by fin_cases k <;> rfl

variable {V : Ix → R3 → ℝ}

/-- `div curl = 0` row-wise, for smooth matrix fields. -/
theorem sum_pd_curlM (hV : ∀ ij, ContDiff ℝ ∞ (V ij)) (i : Fin 3) (x : R3) :
    ∑ k, pd k (curlM V (i, k)) x = 0 := by
  have hd : ∀ ij a, Differentiable ℝ (pd a (V ij)) := fun ij a =>
    (contDiff_pd_top (hV ij) a).differentiable (by simp)
  have hc : ∀ ij a b, pd a (pd b (V ij)) x = pd b (pd a (V ij)) x := fun ij a b =>
    pd_pd_comm ((hV ij).of_le (by simp)) a b x
  have e : ∀ k : Fin 3, pd k (curlM V (i, k)) x =
      pd k (pd (k + 1) (V (i, k + 2))) x - pd k (pd (k + 2) (V (i, k + 1))) x := fun k =>
    pd_fun_sub (hd _ _) (hd _ _) k x
  simp only [e, Fin.sum_univ_three]
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  linarith [hc (i, 2) 0 1, hc (i, 1) 0 2, hc (i, 0) 1 2]

/-- `curl curl V = ∇ div V - ΔV` row-wise, for smooth matrix fields. -/
theorem curlM_curlM_eq (hV : ∀ ij, ContDiff ℝ ∞ (V ij)) (i k : Fin 3) (x : R3) :
    curlM (curlM V) (i, k) x =
      pd k (fun y => ∑ l, pd l (V (i, l)) y) x - ∑ j, pd j (pd j (V (i, k))) x := by
  have hd : ∀ ij a, Differentiable ℝ (pd a (V ij)) := fun ij a =>
    (contDiff_pd_top (hV ij) a).differentiable (by simp)
  have hc : ∀ ij a b, pd a (pd b (V ij)) x = pd b (pd a (V ij)) x := fun ij a b =>
    pd_pd_comm ((hV ij).of_le (by simp)) a b x
  rw [pd_sum Finset.univ (fun l _ => hd _ _) k x, sum_fin3_rot k, sum_fin3_rot k]
  have e1 : curlM V (i, k + 2) = fun y => pd k (V (i, k + 1)) y - pd (k + 1) (V (i, k)) y := by
    funext y
    simp only [curlM, fin3_add_two_add_one, fin3_add_two_add_two]
  have e2 : curlM V (i, k + 1) = fun y => pd (k + 2) (V (i, k)) y - pd k (V (i, k + 2)) y := by
    funext y
    simp only [curlM, fin3_add_one_add_one, fin3_add_one_add_two]
  have e3 : curlM (curlM V) (i, k) x =
      pd (k + 1) (curlM V (i, k + 2)) x - pd (k + 2) (curlM V (i, k + 1)) x := rfl
  rw [e3, e1, e2, pd_fun_sub (hd _ _) (hd _ _), pd_fun_sub (hd _ _) (hd _ _)]
  linarith [hc (i, k + 1) (k + 1) k, hc (i, k + 2) (k + 2) k]

/-- **Compactly supported smooth solutions of `curl curl V = c V`, `c ≠ 0`, vanish**: `div V = 0`
(`div curl = 0`), so `ΔV = -c V` and each entry vanishes (`eq_zero_of_laplacian_eq`). -/
theorem eq_zero_of_curlM_curlM_eq (hV : ∀ ij, ContDiff ℝ ∞ (V ij))
    (hVc : ∀ ij, HasCompactSupport (V ij)) {c : ℝ} (hc : c ≠ 0)
    (h : ∀ ij x, curlM (curlM V) ij x = c * V ij x) : V = 0 := by
  have hW : ∀ ij, ContDiff ℝ ∞ (curlM V ij) := fun ij =>
    (contDiff_pd_top (hV _) _).sub (contDiff_pd_top (hV _) _)
  have hdiv : ∀ i, (fun y => ∑ l, pd l (V (i, l)) y) = 0 := by
    intro i
    funext y
    have e := sum_pd_curlM hW i y
    have e' : ∀ k, pd k (curlM (curlM V) (i, k)) y = c * pd k (V (i, k)) y := fun k => by
      rw [show curlM (curlM V) (i, k) = fun z => c * V (i, k) z from funext (h (i, k)),
        pd_const_mul ((hV _).differentiable (by simp))]
    simp only [e', ← Finset.mul_sum] at e
    exact (mul_eq_zero.1 e).resolve_left hc
  funext ij
  obtain ⟨i, k⟩ := ij
  refine eq_zero_of_laplacian_eq (hV (i, k)) (hVc (i, k)) hc fun x => ?_
  have e := curlM_curlM_eq hV i k x
  rw [hdiv i, h] at e
  simp only [pd_zero] at e
  linarith

end CurlCurl

/-! ### Eigenfields with both boundary conditions -/

section Eigenfield

variable {Ω : Set R3}

/-- Pairing the extension by zero with a test field of `ℝ³` is pairing on `Ω`. -/
theorem sum_integral_extendL2F {ι : Type*} [Fintype ι] (hΩ : MeasurableSet Ω) (v : L2F ℝ Ω ι)
    {ψ : ι → R3 → ℝ} (hψ : IsTestField (univ : Set R3) ψ) :
    ∑ i, ∫ x, (starRingEnd ℝ) (ConstCoeffOp.extendL2F hΩ v i x) * ψ i x =
      ⟪v, toL2F (fun i => (memLp_of_isTest (hψ i)).restrict Ω)⟫_ℝ := by
  have h := ConstCoeffOp.inner_extendL2F_testField hΩ v hψ
  rw [inner_testField] at h
  rw [inner_toL2F, ← h]
  exact Finset.sum_congr rfl fun i _ => setIntegral_univ.symm

theorem extendL2F_smul {ι : Type*} [Fintype ι] (hΩ : MeasurableSet Ω) (c : ℝ) (v : L2F ℝ Ω ι) :
    ConstCoeffOp.extendL2F hΩ (c • v) = c • ConstCoeffOp.extendL2F hΩ v := by
  refine PiLp.ext fun i => Lp.ext ?_
  filter_upwards [(ae_restrict_iff' MeasurableSet.univ).2 (Eventually.of_forall
      fun x (_ : x ∈ univ) => trivial),
    ae_restrict_of_ae (ConstCoeffOp.coeFn_extendL2F hΩ (c • v) i), ae_restrict_of_ae (ConstCoeffOp.coeFn_extendL2F hΩ v i),
    Lp.coeFn_smul c (ConstCoeffOp.extendL2F hΩ v i),
    ae_restrict_of_ae ((ae_restrict_iff' hΩ).1 (Lp.coeFn_smul c (v i)))] with x _ h1 h2 h3 h4
  rw [PiLp.smul_apply, h3, Pi.smul_apply, h1, h2]
  by_cases hx : x ∈ Ω
  · rw [indicator_of_mem hx, indicator_of_mem hx, PiLp.smul_apply, h4 hx, Pi.smul_apply]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]

/-- The kernel convolution commutes with multiplication by a constant. -/
private theorem kconv_const_mul (k : R3 → ℝ) (c : ℝ) (f : R3 → ℝ) :
    kconv k (fun x => c * f x) = fun x => c * kconv k f x := by
  funext x
  simp only [kconv_apply]
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)

/-- `curl_min w = curl† w` for `w ∈ H̊(curl)`: the row-wise curl is formally self-adjoint. -/
theorem minimal_curl_eq_adjoint (hΩ : IsOpen Ω) (w : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain)
    (hw : (w : L2F ℝ Ω Ix) ∈ (gradCurl ℝ hΩ).d₁†.domain) :
    (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω w = (gradCurl ℝ hΩ).d₁† ⟨w, hw⟩ := by
  refine L2F.ext_of_forall_inner_testField hΩ fun φ hφ => ?_
  have h1 : (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω w =
      (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).maximal Ω ⟨w, ((curlOp 3).minimal_le_maximal hΩ).1 w.2⟩ :=
    ((curlOp 3).minimal_le_maximal hΩ).2 rfl
  have hw' : (w : L2F ℝ Ω Ix) ∈
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain := by
    rw [← adjoint_gradCurl_d₁ hΩ]; exact hw
  have h2 : (gradCurl ℝ hΩ).d₁† ⟨w, hw⟩ =
      (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω ⟨w, hw'⟩ :=
    LinearPMap.apply_eq_of_eq (adjoint_gradCurl_d₁ hΩ) _ _ rfl
  rw [h1, h2, (curlOp 3).maximal_inner_testField hΩ _ hφ,
    (curlOp 3).formalAdj.maximal_inner_testField hΩ _ hφ,
    (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).testField_formalAdj_formalAdj hφ]
  congr 1
  exact testField_congr _ _ (curlOp_formalAdj_apply φ)

/-- **No electric eigenfield satisfies both boundary conditions**: on a bounded open `Ω ⊆ ℝ³`,
if `u ∈ H̊(curl)`, `curl† curl u = ξ² u` with `ξ ≠ 0`, and moreover `curl u ∈ H̊(curl)`, then
`u = 0`. The extensions by zero `ũ`, `(curl u)~` satisfy `curl ũ = (curl u)~` and
`curl (curl u)~ = ξ² ũ` weakly on `ℝ³` (both tangential traces vanish); their mollifications are
compactly supported smooth solutions of `curl curl V = ξ² V`, hence zero
(`eq_zero_of_curlM_curlM_eq`, a Pohozaev identity), and so is `ũ`. -/
theorem eq_zero_of_isEigenfield_of_mem_minimal (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {ξ : ℝ} (hξ : ξ ≠ 0) {v : L2F ℝ Ω Ix} (hE : (gradCurl ℝ hΩ).IsEigenfield ξ v)
    (hm : ∀ h1 : v ∈ (gradCurl ℝ hΩ).d₁.domain,
      ((gradCurl ℝ hΩ).d₁ ⟨v, h1⟩ : L2F ℝ Ω Ix) ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) :
    v = 0 := by
  obtain ⟨h1, h3, e⟩ := hE
  have hΩm := hΩ.measurableSet
  have hw := hm h1
  have hgreen1 := fun {ψ : Ix → R3 → ℝ} (hψ : IsTestField (univ : Set R3) ψ) =>
    (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal_green hΩ curlOp_isOrderLE ⟨v, h1⟩
      (fun j => (hψ j).contDiff.of_le (by simp)) (fun j => (memLp_of_isTest (hψ j)).restrict Ω)
      (fun i => (memLp_of_isTest
        ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.isTestField_apply hψ i)).restrict Ω)
  generalize hwd : (gradCurl ℝ hΩ).d₁ ⟨v, h1⟩ = w at h3 e hw
  have hgreen1' : ∀ {ψ : Ix → R3 → ℝ} (hψ : IsTestField (univ : Set R3) ψ),
      ⟪w, toL2F (fun j => (memLp_of_isTest (hψ j)).restrict Ω)⟫_ℝ =
        ⟪v, toL2F (fun i => (memLp_of_isTest
          ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.isTestField_apply hψ i)).restrict Ω)⟫_ℝ :=
    fun hψ => by rw [← hwd]; exact hgreen1 hψ
  have hAw : (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω ⟨w, hw⟩ = (ξ ^ 2 : ℝ) • v := by
    rw [minimal_curl_eq_adjoint hΩ ⟨w, hw⟩ h3, e]
    rfl
  have hc : (ξ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hξ
  set U := ConstCoeffOp.extendL2F hΩm v
  set W := ConstCoeffOp.extendL2F hΩm w
  set U' := ConstCoeffOp.extendL2F hΩm ((ξ ^ 2 : ℝ) • v)
  have hU2 : ∀ i, MemLp (U i : R3 → ℝ) 2 volume := fun i =>
    ConstCoeffOp.memLp_univ_iff.1 (Lp.memLp _)
  have hW2 : ∀ i, MemLp (W i : R3 → ℝ) 2 volume := fun i =>
    ConstCoeffOp.memLp_univ_iff.1 (Lp.memLp _)
  -- `curl ũ = (curl u)~` weakly on `ℝ³`
  have weak1 : ∀ ψ : Ix → R3 → ℝ, IsTestField (univ : Set R3) ψ →
      ∑ j, ∫ x, (starRingEnd ℝ) (W j x) * ψ j x =
        ∑ i, ∫ x, (starRingEnd ℝ) (U i x) *
          (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.apply ψ i x := by
    intro ψ hψ
    rw [sum_integral_extendL2F hΩm w hψ,
      sum_integral_extendL2F hΩm v ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.isTestField_apply hψ)]
    exact hgreen1' hψ
  -- `curl (curl u)~ = ξ² ũ` weakly on `ℝ³`
  have weak2 : ∀ ψ : Ix → R3 → ℝ, IsTestField (univ : Set R3) ψ →
      ∑ j, ∫ x, (starRingEnd ℝ) (U' j x) * ψ j x =
        ∑ i, ∫ x, (starRingEnd ℝ) (W i x) *
          (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.apply ψ i x := by
    intro ψ hψ
    rw [sum_integral_extendL2F hΩm _ hψ,
      sum_integral_extendL2F hΩm w ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.isTestField_apply hψ),
      ← hAw]
    exact (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal_green hΩ curlOp_isOrderLE ⟨w, hw⟩
      (fun j => (hψ j).contDiff.of_le (by simp)) _ _
  have hU' : ∀ j, (U' j : R3 → ℝ) =ᵐ[volume] fun x => ξ ^ 2 * U j x := by
    intro j
    have hUU : U' = (ξ ^ 2 : ℝ) • U := extendL2F_smul hΩm _ v
    have h := (ae_restrict_iff' MeasurableSet.univ).1 (Lp.coeFn_smul (ξ ^ 2 : ℝ) (U j))
    filter_upwards [h] with x hx
    rw [hUU, PiLp.smul_apply, hx (mem_univ x), Pi.smul_apply, smul_eq_mul]
  -- the mollifications vanish
  have hzero : ∀ m : ℕ, (fun ij => kconv ((bumpSeq m : ContDiffBump (0 : R3)).normed volume)
      (U ij : R3 → ℝ)) = 0 := by
    intro m
    set ρ := (bumpSeq m : ContDiffBump (0 : R3)).normed volume
    have hρ : IsTest (univ : Set R3) ρ := isTest_bumpSeq m
    have hloc : ∀ i, LocallyIntegrable (U i : R3 → ℝ) volume := fun i =>
      (hU2 i).locallyIntegrable (by norm_num)
    have c1 := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply_kconv hρ hU2 weak1
    have c2 := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply_kconv hρ hW2 weak2
    refine eq_zero_of_curlM_curlM_eq (fun ij => contDiff_kconv hρ (hloc ij)) (fun ij => ?_) hc
      fun ij x => ?_
    · rw [kconv_congr_ae ρ (ConstCoeffOp.coeFn_extendL2F hΩm v ij)]
      exact HasCompactSupport.convolution _
        (HasCompactSupport.intro' hb.isCompact_closure isClosed_closure fun x hx =>
          indicator_of_notMem (fun h => hx (subset_closure h)) _) hρ.hasCompactSupport
    · simp only [curlM_eq_apply]
      rw [c1, c2]
      dsimp only
      rw [kconv_congr_ae ρ (hU' ij), kconv_const_mul]
  have hU0 : ∀ ij, (U ij : R3 → ℝ) =ᵐ[volume] 0 := by
    intro ij
    have hlim := tendsto_eLpNorm_kconv_sub (hU2 ij)
    simp only [fun m => congrFun (hzero m) ij, Pi.zero_apply, zero_sub, eLpNorm_neg] at hlim
    have h0 : eLpNorm (U ij : R3 → ℝ) 2 volume = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
    exact (eLpNorm_eq_zero_iff (by norm_num)).1 h0
  rw [← ConstCoeffOp.restrictL2F_extendL2F hΩm v]
  refine PiLp.ext fun ij => Lp.ext ?_
  filter_upwards [ConstCoeffOp.coeFn_restrictL2F Ω U ij, ae_restrict_of_ae (hU0 ij),
    Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h1 h2 h3
  rw [h1, h2, PiLp.zero_apply, h3]

end Eigenfield

/-! ### Moving data in `K*` -/

section Moving

-- Over `ℝ` the generic real structure on the window spaces duplicates the inner-product one.
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {Ω : Set R3}

/-- **Moving data of `K*` violate the electric boundary condition in the magnetic slot**: on a
bounded open `Ω ⊆ ℝ³`, for the thesis' complex `H̊¹ → H̊(curl) → L²` and
`K = {0} × L²(TSD) × L²(TSD)`, under a complete set of eigenvectors of `L²` (`hD`), `K*`
contains a non-stationary datum iff there are `ξ > 0` and a nonzero
`u ∈ L²(TSD) ∩ H̊(curl)` with `curl† curl u = ξ² u` and `curl u ∉ H̊(curl)`. This refines the
spectral reduction `gradCurl_coreSub_spectral` (whose TSD eigenfields give the non-stationary
data): every such eigenfield has `curl u ∉ H̊(curl)` (`eq_zero_of_isEigenfield_of_mem_minimal`). -/
theorem not_coreSub_le_stationary_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hD : (gradCurl ℝ hΩ).EigenDense) :
    ¬ (gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω) ≤ (gradCurl ℝ hΩ).stationary ↔
      ∃ ξ : ℝ, 0 < ξ ∧ ∃ v : L2F ℝ Ω Ix, v ≠ 0 ∧ v ∈ tsd Ω ∧ (gradCurl ℝ hΩ).IsEigenfield ξ v ∧
        ∀ h1 : v ∈ (gradCurl ℝ hΩ).d₁.domain, ((gradCurl ℝ hΩ).d₁ ⟨v, h1⟩ : L2F ℝ Ω Ix) ∉
          ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain := by
  rw [(gradCurl_coreSub_spectral hΩ hb hD).2.2.1]
  refine exists_congr fun ξ => and_congr_right fun hξ => exists_congr fun v =>
    and_congr_right fun hv => and_congr_right fun _ => ⟨fun hE => ⟨hE, fun h1 hm => hv ?_⟩,
      And.left⟩
  exact eq_zero_of_isEigenfield_of_mem_minimal hΩ hb hξ.ne' hE fun _ => hm

end Moving

end Feec.Models.BoundedDomain
