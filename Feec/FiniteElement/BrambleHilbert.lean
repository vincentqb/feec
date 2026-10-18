module

public import Feec.Algebra.PolynomialForm
public import Feec.Mesh.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Bramble–Hilbert lemma on the reference simplex (classical form)

For a function `f` that is `C^{r+1}` on a neighbourhood of a convex set `K`, the Taylor
polynomial `p = T_{r+1} f` of degree `≤ r` at a point `x₀ ∈ K`,
`p x = ∑_{i ≤ r} (1/i!) D^i f(x₀)(x - x₀, …, x - x₀)`, satisfies
`‖D^j (f - p)(x)‖ ≤ d^{r+1-j} sup_K ‖D^{r+1} f‖` on `K` for all `0 ≤ j ≤ r + 1`, where
`d = sup_{y ∈ K} ‖y - x₀‖` (`norm_iteratedFDeriv_sub_taylorPoly_le`). This is the classical
(`C^{r+1}`, sup-norm) form of the Bramble–Hilbert lemma ([BrambleHilbert1970];
[Ciarlet2002], Thm 3.1.1 and §3.1; [Arnold2018], Ch. 7): polynomials of degree `≤ r`
approximate `f` up to `|f|_{r+1}`. Sobolev spaces do not appear; all seminorms are suprema of
iterated Fréchet derivatives.

The proof is an induction on the order: `D (f - T_{k+1} f) = D f - T_k (D f)`
(`hasFDerivAt_taylorPoly`), so the estimate for `D^{j+1}` is the estimate of order `k` for
`D f`, and the case `j = 0` follows from the mean value inequality, since `f - T_{k+1} f`
vanishes at `x₀`. The identity `D (T_{k+1} f) = T_k (D f)` uses the symmetry of the iterated
derivatives `D^i f(x₀)`, `i ≤ k`, of a `C^k` function, which is proved here
(`iteratedFDeriv_comp_perm_of_contDiffAt`) from Mathlib's symmetry of second derivatives;
Mathlib states it only for analytic functions.

On the reference simplex `T̂ = conv {0, e₀, …, e_{n-1}}` (`Feec.Mesh.refSimplex`) with the sup
norm of `ℝⁿ = Fin n → ℝ` (Mathlib's norm), every two points are at distance `≤ 1`, so with
`x₀` the barycenter the constant is `1`:
`sup_{T̂} ‖D^j (f - p)‖ ≤ sup_{T̂} ‖D^{r+1} f‖`, `j ≤ r + 1`
(`norm_iteratedFDeriv_sub_taylorPoly_refSimplex_le`). The polynomial space is
`P_r(ℝⁿ; G)` (`polyFunctions n r G`), the span of the maps `x ↦ q(x) • c` with `q` an
`MvPolynomial` of total degree `≤ r` and `c ∈ G`; the Taylor polynomial lies in it
(`taylorPoly_mem_polyFunctions`). Values in a normed space `G` cover scalar functions,
vector fields and differential forms (coefficients in a fibre space) at once.

The abstract consequence ([Ciarlet2002], Thm 3.1.4): if a reference interpolant `I` is
additive on `C^{r+1}` functions, reproduces `P_r` on `T̂`, and is stable,
`sup_{T̂} ‖I g‖ ≤ C_I ∑_{j ≤ m} sup_{T̂} ‖D^j g‖` with `m ≤ r + 1` (`IsRefInterpolant`), then
`sup_{T̂} ‖f - I f‖ ≤ (1 + C_I (m + 1)) sup_{T̂} ‖D^{r+1} f‖`
(`IsRefInterpolant.norm_sub_le`), and the `L²(T̂)` versions follow
(`IsRefInterpolant.lintegral_sub_le`, `IsRefInterpolant.eLpNorm_sub_le`). The Taylor
polynomial at the barycenter is such an interpolant (`isRefInterpolant_taylorPoly`; its
reproduction of `P_r` uses `D^{r+1} p = 0` for `p ∈ P_r`, proved from `D P_{r+1} ⊆ P_r`).
The reference error estimate in higher seminorms,
`sup_{T̂} ‖D^j (f - I f)‖ ≤ K sup_{T̂} ‖D^{r+1} f‖`, is the hypothesis `HasRefDerivEstimate`;
it holds for `j = 0` for every `IsRefInterpolant` (`IsRefInterpolant.hasRefDerivEstimate_zero`)
and for all `j ≤ r + 1` for the Taylor interpolant (`hasRefDerivEstimate_taylorPoly`). A
degree-of-freedom instance of `IsRefInterpolant` is `P₁` Lagrange interpolation at the vertices,
`I g = ∑ᵢ λᵢ g(vᵢ)` (`lagrangeP1`, `isRefInterpolant_lagrangeP1`: `r = 1`, `m = 0`, `C = 1`).
Suprema are written as bounds: a hypothesis `∀ y ∈ T̂, ‖D^{r+1} f y‖ ≤ M` stands for
`sup_{T̂} ‖D^{r+1} f‖ ≤ M`. The Taylor estimate passes from `f` to `D f`, so its domain and
codomain live in one universe; from the reference simplex on, the value space `G` is in `Type`
(this covers `ℝ`, `ℝⁿ` and the alternating forms on `ℝⁿ`).

## Main definitions

* `Feec.FiniteElement.taylorPoly f x₀ k`: the Taylor polynomial of degree `< k` of `f` at `x₀`.
* `Feec.FiniteElement.polyFunctions n r G`: `P_r(ℝⁿ; G)`.
* `Feec.FiniteElement.refBarycenter n`: the barycenter of `T̂`.
* `Feec.FiniteElement.IsRefInterpolant n r m G I C`: hypotheses on a reference interpolant.
* `Feec.FiniteElement.HasRefDerivEstimate n r j G I K`: the order-`j` reference error
  estimate.
* `Feec.FiniteElement.lagrangeP1`: `P₁` Lagrange interpolation on `T̂`.

## Main results

* `iteratedFDeriv_comp_perm_of_contDiffAt`: the `k`-th derivative of a `C^k` function is
  symmetric.
* `hasFDerivAt_taylorPoly`: `D (T_{k+1} f) = T_k (D f)`.
* `norm_iteratedFDeriv_sub_taylorPoly_le`: the Taylor estimate on a convex set, all orders
  `j ≤ k`.
* `norm_iteratedFDeriv_sub_taylorPoly_refSimplex_le`,
  `exists_polyFunctions_norm_iteratedFDeriv_sub_le`: **Bramble–Hilbert on `T̂`**.
* `IsRefInterpolant.norm_sub_le`, `IsRefInterpolant.lintegral_sub_le`,
  `IsRefInterpolant.eLpNorm_sub_le`: the reference interpolation error in `L^∞` and `L²`.
* `fderiv_mem_polyFunctions`, `iteratedFDeriv_eq_zero_of_mem_polyFunctions`: `D P_{r+1} ⊆ P_r`
  and `D^{r+1} p = 0` on `P_r`; `taylorPoly_eq_of_mem_polyFunctions`: `T_{r+1} p = p`.
* `isRefInterpolant_taylorPoly`: the Taylor polynomial at the barycenter satisfies
  `IsRefInterpolant` with `m = r`, `C = 1`, so the hypotheses are consistent.
* `IsRefInterpolant.hasRefDerivEstimate_zero`, `hasRefDerivEstimate_taylorPoly`: reference
  estimates of order `j` (`HasRefDerivEstimate`).
* `isRefInterpolant_lagrangeP1`: `P₁` Lagrange interpolation satisfies `IsRefInterpolant`
  with `r = 1`, `m = 0`, `C = 1`.

## References

* [J. H. Bramble, S. R. Hilbert, *Estimation of Linear Functionals on Sobolev Spaces with Application to Fourier Transforms and Spline Interpolation*][BrambleHilbert1970]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], Thm 3.1.1
  (polynomial approximation), Thm 3.1.4 (error estimate for `P_r`-invariant interpolants), §3.1
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (approximation
  estimates)
-/

@[expose] public section

noncomputable section

open Filter Function Topology MeasureTheory

namespace Feec.FiniteElement

/-! ### Symmetry of iterated derivatives -/

section Symmetry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The `k`-th iterated derivative of a function that is `C^k` at `x` is symmetric. (Mathlib's
`ContDiffAt.iteratedFDeriv_comp_perm` assumes analyticity.) The permutations fixing `0` are
handled by induction (the `(k-1)`-st derivative is symmetric near `x`), the transposition
`(0 1)` by the symmetry of second derivatives, and these generate all permutations. -/
theorem iteratedFDeriv_comp_perm_of_contDiffAt {k : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ k f x) (v : Fin k → E) (σ : Equiv.Perm (Fin k)) :
    iteratedFDeriv ℝ k f x (v ∘ σ) = iteratedFDeriv ℝ k f x v := by
  induction k generalizing f x with
  | zero => exact congrArg _ (funext fun i => i.elim0)
  | succ k ih =>
    set P : Equiv.Perm (Fin (k + 1)) → Prop :=
      fun σ => ∀ v, iteratedFDeriv ℝ (k + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (k + 1) f x v
    have hmul : ∀ σ τ, P σ → P τ → P (σ * τ) := fun σ τ hσ hτ v => by
      rw [Equiv.Perm.coe_mul, ← comp_assoc, hτ, hσ]
    -- permutations fixing `0`
    have hfix : ∀ τ : Equiv.Perm (Fin k), P (Equiv.Perm.decomposeFin.symm (0, τ)) := by
      intro τ v
      have hev : iteratedFDeriv ℝ k f =ᶠ[𝓝 x]
          (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E F τ) ∘ iteratedFDeriv ℝ k f := by
        filter_upwards [hf.eventually (by simp)] with y hy
        ext u
        exact (ih (hy.of_le (by norm_cast; omega)) _ _).symm
      have hD : fderiv ℝ (iteratedFDeriv ℝ k f) x =
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E F τ :
            _ ≃ₗᵢ[ℝ] _) : _ →L[ℝ] _).comp (fderiv ℝ (iteratedFDeriv ℝ k f) x) := by
        rw [← LinearIsometryEquiv.comp_fderiv, ← hev.fderiv_eq]
      rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
      conv_rhs => rw [hD]
      change fderiv ℝ (iteratedFDeriv ℝ k f) x (v (Equiv.Perm.decomposeFin.symm (0, τ) 0)) _ =
        fderiv ℝ (iteratedFDeriv ℝ k f) x (v 0) (Fin.tail v ∘ τ)
      rw [Equiv.Perm.decomposeFin_symm_apply_zero]
      congr 1
    have hfix' : ∀ τ : Equiv.Perm (Fin (k + 1)), τ 0 = 0 → P τ := by
      intro τ h0
      obtain ⟨⟨p, τ'⟩, rfl⟩ := Equiv.Perm.decomposeFin.symm.surjective τ
      rw [Equiv.Perm.decomposeFin_symm_apply_zero] at h0
      subst h0
      exact hfix τ'
    -- the transposition `(0 p)`
    have hswap : ∀ p : Fin (k + 1), P (Equiv.swap 0 p) := by
      intro p
      rcases eq_or_ne p 0 with rfl | hp0
      · intro v; rw [Equiv.swap_self]; rfl
      cases k with
      | zero => exact absurd (Fin.ext (by have := p.isLt; omega)) hp0
      | succ k =>
        have key : ∀ m : Fin (k + 2) → E, iteratedFDeriv ℝ (k + 2) f x m =
            fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ k f)) x (m 0) (m 1) (Fin.tail (Fin.tail m)) := by
          intro m
          rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left,
            LinearIsometryEquiv.comp_fderiv (𝕜 := ℝ) (G := E)
              (E := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
              (F := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) F)]
          rfl
        have h01 : P (Equiv.swap 0 1) := by
          intro v
          have hs : IsSymmSndFDerivAt ℝ (iteratedFDeriv ℝ k f) x :=
            (hf.iteratedFDeriv_right (m := 2) (by norm_cast; omega)).isSymmSndFDerivAt (by simp)
          rw [key, key]
          simp only [comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
          rw [hs (v 1) (v 0)]
          congr 1
        rcases eq_or_ne p 1 with rfl | hp1
        · exact h01
        have hconj : Equiv.swap (0 : Fin (k + 2)) p =
            Equiv.swap 1 p * Equiv.swap 0 1 * Equiv.swap 1 p := by
          rw [Equiv.swap_mul_swap_mul_swap (by simp) hp0.symm, Equiv.swap_comm]
        have h1p : P (Equiv.swap 1 p) :=
          hfix' _ (Equiv.swap_apply_of_ne_of_ne (by simp) hp0.symm)
        rw [hconj]
        exact hmul _ _ (hmul _ _ h1p h01) h1p
    obtain ⟨⟨p, τ'⟩, rfl⟩ := Equiv.Perm.decomposeFin.symm.surjective σ
    have hdec : Equiv.Perm.decomposeFin.symm (p, τ') =
        Equiv.swap 0 p * Equiv.Perm.decomposeFin.symm (0, τ') := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Equiv.Perm.decomposeFin_symm_apply_zero]
      · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
    rw [hdec]
    exact hmul _ _ (hswap p) (hfix τ') v

end Symmetry

/-! ### Taylor polynomials -/

section Taylor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The Taylor polynomial of degree `< k` of `f` at `x₀`:
`T_k f (x) = ∑_{i < k} (1/i!) D^i f(x₀)(x - x₀, …, x - x₀)`. -/
def taylorPoly (f : E → F) (x₀ : E) (k : ℕ) (x : E) : F :=
  ∑ i ∈ Finset.range k, ((i.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ i f x₀ (fun _ => x - x₀))

theorem taylorPoly_zero (f : E → F) (x₀ : E) : taylorPoly f x₀ 0 = 0 := by
  funext x; simp [taylorPoly]

/-- `T_{k+1} f (x₀) = f (x₀)`. -/
theorem taylorPoly_self (f : E → F) (x₀ : E) (k : ℕ) :
    taylorPoly f x₀ (k + 1) x₀ = f x₀ := by
  rw [taylorPoly, Finset.sum_range_succ']
  simp only [sub_self, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_zero_apply]
  rw [Finset.sum_eq_zero fun i _ => by
    rw [ContinuousMultilinearMap.map_coord_zero _ (0 : Fin (i + 1)) rfl, smul_zero], zero_add]

/-- `D (T_{k+1} f) = T_k (D f)`, for `f` of class `C^k` at `x₀` (symmetry of `D^i f(x₀)` is
used). -/
theorem hasFDerivAt_taylorPoly {f : E → F} {x₀ : E} {k : ℕ} (hf : ContDiffAt ℝ k f x₀)
    (x : E) : HasFDerivAt (taylorPoly f x₀ (k + 1)) (taylorPoly (fderiv ℝ f) x₀ k x) x := by
  have hlin : ∀ i : ℕ, HasFDerivAt (fun y : E => fun _ : Fin i => y - x₀)
      (ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ E) x :=
    fun i => hasFDerivAt_pi.2 fun _ => (hasFDerivAt_id x).sub_const x₀
  have hsum := HasFDerivAt.fun_sum (u := Finset.range (k + 1)) fun i _ =>
    (((iteratedFDeriv ℝ i f x₀).hasFDerivAt _).comp x (hlin i)).const_smul
      ((i.factorial : ℝ)⁻¹)
  refine hsum.congr_fderiv ?_
  ext h
  rw [Finset.sum_range_succ', add_apply, sum_apply]
  refine (add_eq_left.2 ?_).trans ?_
  · simp [ContinuousMultilinearMap.linearDeriv_apply]
  rw [taylorPoly, sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : ((i + 1 : ℕ) : WithTop ℕ∞) ≤ k := by
    norm_cast; exact Finset.mem_range.1 hi
  have hsym : ∀ l : Fin (i + 1), iteratedFDeriv ℝ (i + 1) f x₀ (update (fun _ => x - x₀) l h) =
      iteratedFDeriv ℝ (i + 1) f x₀ (update (fun _ => x - x₀) (Fin.last i) h) := by
    intro l
    rw [← iteratedFDeriv_comp_perm_of_contDiffAt (hf.of_le hi') _ (Equiv.swap l (Fin.last i)),
      Function.update_comp_equiv]
    simp only [Equiv.symm_swap, Equiv.swap_apply_left]
    rfl
  rw [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.linearDeriv_apply, smul_apply]
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply]
  rw [Finset.sum_congr rfl fun l _ => hsym l, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    iteratedFDeriv_succ_apply_right, Fin.init_update_last, Function.update_self,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Taylor polynomials are smooth. -/
theorem contDiff_taylorPoly (f : E → F) (x₀ : E) (k : ℕ) {N : WithTop ℕ∞} :
    ContDiff ℝ N (taylorPoly f x₀ k) := by
  unfold taylorPoly
  exact ContDiff.sum fun i _ => ((iteratedFDeriv ℝ i f x₀).contDiff.comp
    (contDiff_pi.2 fun _ => contDiff_id.sub contDiff_const)).const_smul _

end Taylor

/-! ### The Taylor estimate -/

section TaylorEstimate

universe u

variable {E' F' : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F']
  [NormedSpace ℝ F']

/-- **Taylor estimate on a convex set, all orders.** If `f` is `C^k` on an open `U ⊇ K`, `K` is
convex, `x₀ ∈ K`, `‖y - x₀‖ ≤ d` and `‖D^k f(y)‖ ≤ M` for `y ∈ K`, then
`‖D^j (f - T_k f)(x)‖ ≤ d^{k-j} M` on `K` for every `j ≤ k`. (Domain and codomain lie in one
universe because the induction passes from `f` to `D f`.) -/
theorem norm_iteratedFDeriv_sub_taylorPoly_le {k : ℕ} {f : E' → F'} {U K : Set E'} {x₀ : E'}
    {d M : ℝ} (hU : IsOpen U) (hKU : K ⊆ U) (hK : Convex ℝ K) (hx₀ : x₀ ∈ K)
    (hf : ContDiffOn ℝ k f U) (hd : ∀ y ∈ K, ‖y - x₀‖ ≤ d)
    (hM : ∀ y ∈ K, ‖iteratedFDeriv ℝ k f y‖ ≤ M) {x : E'} (hx : x ∈ K) {j : ℕ} (hj : j ≤ k) :
    ‖iteratedFDeriv ℝ j (fun y => f y - taylorPoly f x₀ k y) x‖ ≤ d ^ (k - j) * M := by
  induction k generalizing F' f M j x with
  | zero =>
    obtain rfl : j = 0 := Nat.le_zero.1 hj
    simpa [taylorPoly_zero] using hM x hx
  | succ k ih =>
    have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd x₀ hx₀)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ hx₀)
    set g := fderiv ℝ f with hg_def
    have hg : ContDiffOn ℝ k g U := hf.fderiv_of_isOpen hU (by push_cast; exact le_rfl)
    have hMg : ∀ y ∈ K, ‖iteratedFDeriv ℝ k g y‖ ≤ M := fun y hy => by
      rw [hg_def, norm_iteratedFDeriv_fderiv]; exact hM y hy
    have hfx₀ : ContDiffAt ℝ k f x₀ :=
      (hf.contDiffAt (hU.mem_nhds (hKU hx₀))).of_le (by push_cast; exact le_self_add)
    have hderiv : ∀ y ∈ U, HasFDerivAt (fun y => f y - taylorPoly f x₀ (k + 1) y)
        (g y - taylorPoly g x₀ k y) y := fun y hy =>
      (((hf.differentiableOn (by simp)) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt.sub
        (hasFDerivAt_taylorPoly hfx₀ y)
    have hfeq : ∀ y ∈ U, fderiv ℝ (fun y => f y - taylorPoly f x₀ (k + 1) y) =ᶠ[𝓝 y]
        fun y => g y - taylorPoly g x₀ k y := fun y hy => by
      filter_upwards [hU.mem_nhds hy] with z hz using (hderiv z hz).fderiv
    rcases j with _ | j
    · -- the mean value theorem along `[x₀, x]`
      have hbound : ∀ y ∈ K, ‖fderiv ℝ (fun y => f y - taylorPoly f x₀ (k + 1) y) y‖ ≤
          d ^ k * M := fun y hy => by
        rw [(hderiv y (hKU hy)).fderiv]
        simpa using ih hg hMg hy (Nat.zero_le k)
      have h := hK.norm_image_sub_le_of_norm_fderiv_le
        (fun y hy => (hderiv y (hKU hy)).differentiableAt) hbound hx₀ hx
      rw [taylorPoly_self, sub_self, sub_zero] at h
      rw [norm_iteratedFDeriv_zero, Nat.sub_zero, pow_succ]
      calc _ ≤ d ^ k * M * ‖x - x₀‖ := h
        _ ≤ d ^ k * M * d := by gcongr; exact hd x hx
        _ = _ := by ring
    · rw [← norm_iteratedFDeriv_fderiv,
        ((hfeq x (hKU hx)).iteratedFDeriv ℝ j).eq_of_nhds, Nat.add_sub_add_right]
      exact ih hg hMg hx (Nat.le_of_succ_le_succ hj)


end TaylorEstimate

/-! ### Polynomial functions -/

section Poly

universe v

open MvPolynomial

variable {n : ℕ} {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `P_r(ℝⁿ; G)`: the span of the maps `x ↦ q(x) • c`, `q` a polynomial of total degree `≤ r`
in the coordinates of `ℝⁿ = Fin n → ℝ` and `c ∈ G`. -/
def polyFunctions (n r : ℕ) (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G] :
    Submodule ℝ ((Fin n → ℝ) → G) :=
  Submodule.span ℝ {g | ∃ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ r ∧
    ∃ c : G, g = fun x => MvPolynomial.eval x q • c}

theorem polyFunctions_mono {r s : ℕ} (h : r ≤ s) : polyFunctions n r G ≤ polyFunctions n s G :=
  Submodule.span_mono fun _ ⟨q, hq, c, hc⟩ => ⟨q, hq.trans h, c, hc⟩

/-- `x ↦ A(x - x₀, …, x - x₀)` is a polynomial of degree `≤ i` for an `i`-linear map `A`. -/
theorem multilinear_diag_mem_polyFunctions {i r : ℕ} (hi : i ≤ r)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin n → ℝ) G) (x₀ : Fin n → ℝ) :
    (fun x => A (fun _ => x - x₀)) ∈ polyFunctions n r G := by
  set b : Fin n → Fin n → ℝ := fun j k => if j = k then 1 else 0
  have hexp : (fun x => A (fun _ => x - x₀)) = ∑ σ : Fin i → Fin n,
      fun x => MvPolynomial.eval x (∏ l, (MvPolynomial.X (σ l) - MvPolynomial.C (x₀ (σ l)))) •
        A (fun l => b (σ l)) := by
    funext x
    have hx : x - x₀ = ∑ j, (x - x₀) j • b j := pi_eq_sum_univ (x - x₀)
    rw [Finset.sum_apply, hx, A.map_sum (fun _ j => (x - x₀) j • b j)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [A.map_smul_univ (fun l => (x - x₀) (σ l)) (fun l => b (σ l))]
    simp
  rw [hexp]
  refine Submodule.sum_mem _ fun σ _ => Submodule.subset_span ⟨_, ?_, _, rfl⟩
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ l, (MvPolynomial.X (σ l) - MvPolynomial.C (x₀ (σ l)) :
        MvPolynomial (Fin n) ℝ).totalDegree
      ≤ ∑ _l : Fin i, 1 := Finset.sum_le_sum fun l _ =>
        (MvPolynomial.totalDegree_sub_C_le _ _).trans (MvPolynomial.totalDegree_X _).le
    _ ≤ r := by simpa using hi

/-- The Taylor polynomial `T_{r+1} f` lies in `P_r`. -/
theorem taylorPoly_mem_polyFunctions (f : (Fin n → ℝ) → G) (x₀ : Fin n → ℝ) (r : ℕ) :
    taylorPoly f x₀ (r + 1) ∈ polyFunctions n r G := by
  have : taylorPoly f x₀ (r + 1) = ∑ i ∈ Finset.range (r + 1),
      ((i.factorial : ℝ)⁻¹ • fun x => iteratedFDeriv ℝ i f x₀ (fun _ => x - x₀)) := by
    funext x; simp [taylorPoly, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (multilinear_diag_mem_polyFunctions (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) _ x₀)


/-! ### Calculus of polynomial functions -/


/-- The derivative of a polynomial function: `D q(x) = ∑ᵢ ∂ᵢ q(x) dxᵢ`. -/
theorem hasFDerivAt_eval (q : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y => eval y q)
      (∑ i, eval x (pderiv i q) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) x := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const (eval x (C a)) x
  | add p q hp hq =>
    convert hp.fun_add hq using 1
    · funext y; simp
    · simp [map_add, add_smul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have hX : HasFDerivAt (fun y : Fin n → ℝ => y i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) x :=
      hasFDerivAt_apply i x
    convert hp.mul hX using 1
    · funext y; simp
    · ext h
      simp [pderiv_X, Pi.single_apply, mul_comm, Finset.mul_sum]
      simp only [apply_ite, map_zero, mul_add, Finset.sum_add_distrib, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring


/-- Polynomial functions are smooth. -/
theorem contDiff_eval (q : MvPolynomial (Fin n) ℝ) {N : WithTop ℕ∞} :
    ContDiff ℝ N fun y : Fin n → ℝ => eval y q := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    simpa using hp.mul (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).contDiff

theorem contDiff_of_mem_polyFunctions {r : ℕ} {p : (Fin n → ℝ) → G}
    (hp : p ∈ polyFunctions n r G) {N : WithTop ℕ∞} : ContDiff ℝ N p := by
  induction hp using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨q, -, c, rfl⟩ := hg
    exact (contDiff_eval q).smul contDiff_const
  | zero => exact contDiff_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul a f _ hf => exact hf.const_smul a

theorem hasFDerivAt_eval_smul (q : MvPolynomial (Fin n) ℝ) (c : G) (x : Fin n → ℝ) :
    HasFDerivAt (fun y => eval y q • c)
      (∑ i, eval x (pderiv i q) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).smulRight c) x := by
  convert (hasFDerivAt_eval q x).smul_const c using 1
  ext h
  simp [Finset.sum_smul, smul_smul]

/-- Derivatives lower the degree of polynomial functions. -/
theorem fderiv_mem_polyFunctions {r : ℕ} {p : (Fin n → ℝ) → G}
    (hp : p ∈ polyFunctions n (r + 1) G) :
    fderiv ℝ p ∈ polyFunctions n r ((Fin n → ℝ) →L[ℝ] G) := by
  induction hp using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨q, hq, c, rfl⟩ := hg
    have : fderiv ℝ (fun y => eval y q • c) = ∑ i, fun x => eval x (pderiv i q) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).smulRight c := by
      funext x; rw [(hasFDerivAt_eval_smul q c x).fderiv, Finset.sum_apply]
    rw [this]
    refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, ?_, _, rfl⟩
    exact (Feec.Koszul.totalDegree_pderiv_le i q).trans (by omega)
  | zero => simp
  | add f g hf hg hf' hg' =>
    have : fderiv ℝ (f + g) = fderiv ℝ f + fderiv ℝ g := by
      funext x
      exact fderiv_add ((contDiff_of_mem_polyFunctions hf (N := 1)).differentiable one_ne_zero x)
        ((contDiff_of_mem_polyFunctions hg (N := 1)).differentiable one_ne_zero x)
    rw [this]; exact Submodule.add_mem _ hf' hg'
  | smul a f hf hf' =>
    have : fderiv ℝ (a • f) = a • fderiv ℝ f := by
      funext x
      exact fderiv_const_smul
        ((contDiff_of_mem_polyFunctions hf (N := 1)).differentiable one_ne_zero x) a
    rw [this]; exact Submodule.smul_mem _ a hf'

/-- Elements of `P_0` are constant. -/
theorem fderiv_eq_zero_of_mem_polyFunctions_zero {p : (Fin n → ℝ) → G}
    (hp : p ∈ polyFunctions n 0 G) : fderiv ℝ p = 0 := by
  induction hp using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨q, hq, c, rfl⟩ := hg
    rw [totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hq)]
    simp
  | zero => simp
  | add f g hf hg hf' hg' =>
    funext x
    rw [fderiv_add ((contDiff_of_mem_polyFunctions hf (N := 1)).differentiable one_ne_zero x)
        ((contDiff_of_mem_polyFunctions hg (N := 1)).differentiable one_ne_zero x), hf', hg']
    simp
  | smul a f hf hf' =>
    funext x
    rw [fderiv_const_smul
      ((contDiff_of_mem_polyFunctions hf (N := 1)).differentiable one_ne_zero x) a,
      hf']
    simp

/-- `D^{r+1} p = 0` for `p ∈ P_r`. -/
theorem iteratedFDeriv_eq_zero_of_mem_polyFunctions (r : ℕ) :
    ∀ {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] {p : (Fin n → ℝ) → H},
      p ∈ polyFunctions n r H → ∀ x, iteratedFDeriv ℝ (r + 1) p x = 0 := by
  induction r with
  | zero =>
    intro H _ _ p hp x
    rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv, fderiv_eq_zero_of_mem_polyFunctions_zero hp]
    simp
  | succ r ih =>
    intro H _ _ p hp x
    have h := ih (fderiv_mem_polyFunctions hp) x
    rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv, h, norm_zero]


end Poly

/-! ### The reference simplex -/

section RefSimplex

open Feec.Mesh

variable {n : ℕ} {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The barycenter `(1/(n+1), …, 1/(n+1))` of the reference simplex. -/
def refBarycenter (n : ℕ) : Fin n → ℝ := fun _ => ((n : ℝ) + 1)⁻¹

theorem refBarycenter_mem : refBarycenter n ∈ (refSimplex n).closedInterior := by
  rw [mem_closedInterior_refSimplex]
  refine ⟨fun _ => by unfold refBarycenter; positivity, ?_⟩
  simp only [refBarycenter, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  linarith

/-- In the sup norm, points of `T̂` are at distance `≤ 1`. -/
theorem norm_sub_le_one_of_mem_refSimplex {x y : Fin n → ℝ}
    (hx : x ∈ (refSimplex n).closedInterior) (hy : y ∈ (refSimplex n).closedInterior) :
    ‖x - y‖ ≤ 1 := by
  rw [mem_closedInterior_refSimplex] at hx hy
  have hle : ∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i ≤ 1 → ∀ i, z i ≤ 1 := fun z h0 h1 i =>
    (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)).trans h1
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hx.1 i, hy.1 i, hle x hx.1 hx.2 i, hle y hy.1 hy.2 i]

/-- **Bramble–Hilbert on the reference simplex** (classical form): for `f` of class `C^{r+1}` on an
open neighbourhood of `T̂`, its Taylor polynomial `p ∈ P_r` at the barycenter satisfies
`sup_{T̂} ‖D^j (f - p)‖ ≤ sup_{T̂} ‖D^{r+1} f‖` for `0 ≤ j ≤ r + 1` (sup norm on `ℝⁿ`). -/
theorem norm_iteratedFDeriv_sub_taylorPoly_refSimplex_le {r : ℕ} {f : (Fin n → ℝ) → G}
    {U : Set (Fin n → ℝ)} {M : ℝ} (hU : IsOpen U) (hTU : (refSimplex n).closedInterior ⊆ U)
    (hf : ContDiffOn ℝ (r + 1) f U)
    (hM : ∀ y ∈ (refSimplex n).closedInterior, ‖iteratedFDeriv ℝ (r + 1) f y‖ ≤ M)
    {x : Fin n → ℝ} (hx : x ∈ (refSimplex n).closedInterior) {j : ℕ} (hj : j ≤ r + 1) :
    ‖iteratedFDeriv ℝ j (fun y => f y - taylorPoly f (refBarycenter n) (r + 1) y) x‖ ≤ M := by
  have h := norm_iteratedFDeriv_sub_taylorPoly_le (k := r + 1) hU hTU
    (convex_closedInterior _) refBarycenter_mem (by exact_mod_cast hf)
    (fun y hy => norm_sub_le_one_of_mem_refSimplex hy refBarycenter_mem) hM hx hj
  rwa [one_pow, one_mul] at h

/-- **Bramble–Hilbert on `T̂`**, existence form: some `p ∈ P_r` approximates `f` with all its
derivatives of order `≤ r + 1` up to `sup_{T̂} ‖D^{r+1} f‖`. -/
theorem exists_polyFunctions_norm_iteratedFDeriv_sub_le {r : ℕ} {f : (Fin n → ℝ) → G}
    {U : Set (Fin n → ℝ)} {M : ℝ} (hU : IsOpen U) (hTU : (refSimplex n).closedInterior ⊆ U)
    (hf : ContDiffOn ℝ (r + 1) f U)
    (hM : ∀ y ∈ (refSimplex n).closedInterior, ‖iteratedFDeriv ℝ (r + 1) f y‖ ≤ M) :
    ∃ p ∈ polyFunctions n r G, ∀ x ∈ (refSimplex n).closedInterior, ∀ j ≤ r + 1,
      ‖iteratedFDeriv ℝ j (fun y => f y - p y) x‖ ≤ M :=
  ⟨_, taylorPoly_mem_polyFunctions f _ r, fun _ hx _ hj =>
    norm_iteratedFDeriv_sub_taylorPoly_refSimplex_le hU hTU hf hM hx hj⟩

/-- Hypotheses on a reference interpolant `I` acting on `G`-valued functions on `ℝⁿ`, of order
`r` with stability order `m ≤ r + 1` and stability constant `C`, for functions that are
`C^{r+1}` near `T̂` ([Ciarlet2002], Thm 3.1.4): `I` is additive on such functions (on `T̂`),
reproduces `P_r` on `T̂`, and `sup_{T̂} ‖I g‖ ≤ C ∑_{j ≤ m} sup_{T̂} ‖D^j g‖` (with the suprema
written as bounds `B j`). For a Lagrange or Whitney-type interpolant, `m` is the highest order
of derivative entering its degrees of freedom. -/
structure IsRefInterpolant (n r m : ℕ) (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G) (C : ℝ) : Prop where
  /-- The degrees of freedom use derivatives of order at most `r + 1`. -/
  le_succ : m ≤ r + 1
  /-- Additivity on `C^{r+1}` functions, on `T̂`. -/
  map_sub : ∀ V : Set (Fin n → ℝ), IsOpen V → (refSimplex n).closedInterior ⊆ V →
    ∀ f g, ContDiffOn ℝ (r + 1) f V → ContDiffOn ℝ (r + 1) g V →
    ∀ x ∈ (refSimplex n).closedInterior, I (f - g) x = I f x - I g x
  /-- `I p = p` on `T̂` for `p ∈ P_r`. -/
  apply_eq : ∀ p ∈ polyFunctions n r G, ∀ x ∈ (refSimplex n).closedInterior, I p x = p x
  /-- Stability in the `C^m(T̂)` norm. -/
  norm_le : ∀ V : Set (Fin n → ℝ), IsOpen V → (refSimplex n).closedInterior ⊆ V →
    ∀ g, ContDiffOn ℝ (r + 1) g V → ∀ B : ℕ → ℝ,
    (∀ j ≤ m, ∀ y ∈ (refSimplex n).closedInterior, ‖iteratedFDeriv ℝ j g y‖ ≤ B j) →
    ∀ x ∈ (refSimplex n).closedInterior, ‖I g x‖ ≤ C * ∑ j ∈ Finset.range (m + 1), B j

/-- **Interpolation error on `T̂`** ([Ciarlet2002], Thm 3.1.4, classical form):
`sup_{T̂} ‖f - I f‖ ≤ (1 + C (m + 1)) sup_{T̂} ‖D^{r+1} f‖`. -/
theorem IsRefInterpolant.norm_sub_le {r m : ℕ} {I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G} {C : ℝ}
    (hI : IsRefInterpolant n r m G I C) {f : (Fin n → ℝ) → G}
    {U : Set (Fin n → ℝ)} {M : ℝ} (hU : IsOpen U) (hTU : (refSimplex n).closedInterior ⊆ U)
    (hf : ContDiffOn ℝ (r + 1) f U)
    (hM : ∀ y ∈ (refSimplex n).closedInterior, ‖iteratedFDeriv ℝ (r + 1) f y‖ ≤ M)
    {x : Fin n → ℝ} (hx : x ∈ (refSimplex n).closedInterior) :
    ‖f x - I f x‖ ≤ (1 + C * (m + 1)) * M := by
  set p := taylorPoly f (refBarycenter n) (r + 1)
  have hp : ContDiffOn ℝ (r + 1) p U := (contDiff_taylorPoly _ _ _).contDiffOn
  have he : ∀ y ∈ (refSimplex n).closedInterior, ∀ j ≤ r + 1,
      ‖iteratedFDeriv ℝ j (f - p) y‖ ≤ M := fun y hy j hj =>
    norm_iteratedFDeriv_sub_taylorPoly_refSimplex_le hU hTU hf hM hy hj
  have hsub := hI.map_sub U hU hTU f p hf hp x hx
  rw [hI.apply_eq p (taylorPoly_mem_polyFunctions f _ r) x hx] at hsub
  have hstab := hI.norm_le U hU hTU (f - p) (hf.sub hp) (fun _ => M)
    (fun j hj y hy => he y hy j (hj.trans hI.le_succ)) x hx
  have he0 : ‖(f - p) x‖ ≤ M := by simpa using he x hx 0 (Nat.zero_le _)
  have : f x - I f x = (f - p) x - I (f - p) x := by rw [hsub, Pi.sub_apply]; abel
  rw [this]
  calc _ ≤ ‖(f - p) x‖ + ‖I (f - p) x‖ := _root_.norm_sub_le _ _
    _ ≤ M + C * ∑ _j ∈ Finset.range (m + 1), M := add_le_add he0 hstab
    _ = _ := by simp; ring

/-- `∫_s ‖f‖^q ≤ μ(s) C^q` if `‖f‖ ≤ C` on `s`; no measurability is needed. -/
theorem lintegral_enorm_rpow_le_of_forall_norm_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {s : Set α} (hs : MeasurableSet s) {f : α → E}
    {C : ℝ} (hf : ∀ x ∈ s, ‖f x‖ ≤ C) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ x in s, ‖f x‖ₑ ^ q ∂μ ≤ μ s * ENNReal.ofReal C ^ q := by
  calc ∫⁻ x in s, ‖f x‖ₑ ^ q ∂μ ≤ ∫⁻ _x in s, ENNReal.ofReal C ^ q ∂μ := by
        refine lintegral_mono_ae ((ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx => ?_))
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hf x hx)
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]

theorem measurableSet_closedInterior (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    MeasurableSet T.closedInterior :=
  T.isCompact_closedInterior.isClosed.measurableSet

/-- **`L²(T̂)` interpolation error**:
`∫_{T̂} ‖f - I f‖² ≤ |T̂| ((1 + C (m + 1)) sup_{T̂} ‖D^{r+1} f‖)²`. -/
theorem IsRefInterpolant.lintegral_sub_le {r m : ℕ} {I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G}
    {C : ℝ} (hI : IsRefInterpolant n r m G I C) {f : (Fin n → ℝ) → G}
    {U : Set (Fin n → ℝ)} {M : ℝ} (hU : IsOpen U) (hTU : (refSimplex n).closedInterior ⊆ U)
    (hf : ContDiffOn ℝ (r + 1) f U)
    (hM : ∀ y ∈ (refSimplex n).closedInterior, ‖iteratedFDeriv ℝ (r + 1) f y‖ ≤ M) :
    ∫⁻ x in (refSimplex n).closedInterior, ‖f x - I f x‖ₑ ^ 2 ≤
      volume (refSimplex n).closedInterior * ENNReal.ofReal ((1 + C * (m + 1)) * M) ^ 2 := by
  exact_mod_cast lintegral_enorm_rpow_le_of_forall_norm_le (μ := volume)
    (measurableSet_closedInterior _)
    (fun x hx => hI.norm_sub_le hU hTU hf hM hx) (q := 2) zero_le_two

/-- **`L²(T̂)` interpolation error**, `eLpNorm` form:
`‖f - I f‖_{L²(T̂)} ≤ |T̂|^{1/2} (1 + C (m + 1)) sup_{T̂} ‖D^{r+1} f‖`. Mathlib's `eLpNorm` is
`∞` on non-measurable functions, hence the measurability hypothesis (the `lintegral` form needs
none). -/
theorem IsRefInterpolant.eLpNorm_sub_le {r m : ℕ} {I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G}
    {C : ℝ} (hI : IsRefInterpolant n r m G I C) {f : (Fin n → ℝ) → G}
    {U : Set (Fin n → ℝ)} {M : ℝ} (hU : IsOpen U) (hTU : (refSimplex n).closedInterior ⊆ U)
    (hf : ContDiffOn ℝ (r + 1) f U)
    (hM : ∀ y ∈ (refSimplex n).closedInterior, ‖iteratedFDeriv ℝ (r + 1) f y‖ ≤ M)
    (hmeas : AEStronglyMeasurable (fun x => f x - I f x)
      (volume.restrict (refSimplex n).closedInterior)) :
    eLpNorm (fun x => f x - I f x) 2 (volume.restrict (refSimplex n).closedInterior) ≤
      volume (refSimplex n).closedInterior ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((1 + C * (m + 1)) * M) := by
  have h := eLpNorm_le_of_ae_bound (p := 2) hmeas
    ((ae_restrict_iff' (measurableSet_closedInterior _)).2
      (Eventually.of_forall fun x hx => hI.norm_sub_le hU hTU hf hM hx))
  simpa using h

/-! ### A reference interpolant: the Taylor polynomial at the barycenter -/

/-- Taylor polynomials of order `r + 1` reproduce `P_r`. -/
theorem taylorPoly_eq_of_mem_polyFunctions {r : ℕ} {p : (Fin n → ℝ) → G}
    (hp : p ∈ polyFunctions n r G) (x₀ x : Fin n → ℝ) : taylorPoly p x₀ (r + 1) x = p x := by
  have h := norm_iteratedFDeriv_sub_taylorPoly_le (k := r + 1) (U := Set.univ)
    (K := Metric.closedBall x₀ ‖x - x₀‖) (M := 0) isOpen_univ (Set.subset_univ _)
    (convex_closedBall _ _) (Metric.mem_closedBall_self (norm_nonneg _))
    (contDiff_of_mem_polyFunctions hp).contDiffOn (fun y hy => by simpa [dist_eq_norm] using hy)
    (fun y _ => by rw [iteratedFDeriv_eq_zero_of_mem_polyFunctions r hp y, norm_zero])
    (Metric.mem_closedBall.2 (by rw [dist_eq_norm])) (Nat.zero_le _)
  rw [mul_zero, norm_iteratedFDeriv_zero, norm_le_zero_iff, sub_eq_zero] at h
  exact h.symm

/-- The Taylor polynomial at the barycenter is a reference interpolant of order `r` with `m = r`
and `C = 1`. -/
theorem isRefInterpolant_taylorPoly (n r : ℕ) (G : Type) [NormedAddCommGroup G]
    [NormedSpace ℝ G] :
    IsRefInterpolant n r r G (fun g => taylorPoly g (refBarycenter n) (r + 1)) 1 where
  le_succ := Nat.le_succ r
  map_sub V hV hTV f g hf hg x _ := by
    simp only [taylorPoly, ← Finset.sum_sub_distrib, ← smul_sub]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : (i : WithTop ℕ∞) ≤ r + 1 := by
      have := Finset.mem_range.1 hi; norm_cast; omega
    have hx₀ := hV.mem_nhds (hTV refBarycenter_mem)
    rw [iteratedFDeriv_sub_apply ((hf.contDiffAt hx₀).of_le hi') ((hg.contDiffAt hx₀).of_le hi')]
    rfl
  apply_eq p hp x _ := taylorPoly_eq_of_mem_polyFunctions hp _ x
  norm_le V hV hTV g hg B hB x hx := by
    rw [one_mul, taylorPoly]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hd := norm_sub_le_one_of_mem_refSimplex hx refBarycenter_mem
    have hB' := hB i hi' _ refBarycenter_mem
    have hfac : (i.factorial : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast i.factorial_pos)
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (i.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ i g (refBarycenter n)
          (fun _ => x - refBarycenter n)‖
        ≤ 1 * (‖iteratedFDeriv ℝ i g (refBarycenter n)‖ * ∏ _j : Fin i, ‖x - refBarycenter n‖) :=
          mul_le_mul hfac (ContinuousMultilinearMap.le_opNorm _ _) (norm_nonneg _) zero_le_one
      _ ≤ 1 * (B i * 1) := by
          have hprod : ∏ _j : Fin i, ‖x - refBarycenter n‖ ≤ 1 := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            exact pow_le_one₀ (norm_nonneg _) hd
          exact mul_le_mul_of_nonneg_left (mul_le_mul hB' hprod (by positivity)
            ((norm_nonneg _).trans hB')) zero_le_one
      _ = B i := by ring

/-! ### Derivative estimates for reference interpolants -/

/-- `I` satisfies the **reference error estimate of order `j`** with constant `K`: for every `f`
of class `C^{r+1}` on an open neighbourhood of `T̂`,
`sup_{T̂} ‖D^j (f - I f)‖ ≤ K sup_{T̂} ‖D^{r+1} f‖` ([Ciarlet2002], Thm 3.1.4, `W^{j,∞}`
seminorm in its classical form). This is the hypothesis transported to the physical simplex for
the derivative estimates (`Feec.FiniteElement.norm_iteratedFDeriv_sub_transportInterp_le`). -/
def HasRefDerivEstimate (n r j : ℕ) (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G) (K : ℝ) : Prop :=
  ∀ (V : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → G) (M : ℝ), IsOpen V →
    (refSimplex n).closedInterior ⊆ V → ContDiffOn ℝ (r + 1) f V →
    (∀ y ∈ (refSimplex n).closedInterior, ‖iteratedFDeriv ℝ (r + 1) f y‖ ≤ M) →
    ∀ y ∈ (refSimplex n).closedInterior, ‖iteratedFDeriv ℝ j (fun z => f z - I f z) y‖ ≤ K * M

/-- An interpolant satisfying `IsRefInterpolant` has the order-`0` estimate with constant
`1 + C (m + 1)`. -/
theorem IsRefInterpolant.hasRefDerivEstimate_zero {r m : ℕ}
    {I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G} {C : ℝ} (hI : IsRefInterpolant n r m G I C) :
    HasRefDerivEstimate n r 0 G I (1 + C * (m + 1)) := fun _ _ _ hV hTV hf hM _ hy => by
  rw [norm_iteratedFDeriv_zero]
  exact hI.norm_sub_le hV hTV hf hM hy

/-- The Taylor polynomial at the barycenter has the reference estimate of every order
`j ≤ r + 1` with constant `1` (`norm_iteratedFDeriv_sub_taylorPoly_refSimplex_le`). -/
theorem hasRefDerivEstimate_taylorPoly (n r : ℕ) (G : Type) [NormedAddCommGroup G]
    [NormedSpace ℝ G] {j : ℕ} (hj : j ≤ r + 1) :
    HasRefDerivEstimate n r j G (fun g => taylorPoly g (refBarycenter n) (r + 1)) 1 :=
  fun _ _ _ hV hTV hf hM _ hy => by
    rw [one_mul]
    exact norm_iteratedFDeriv_sub_taylorPoly_refSimplex_le hV hTV hf hM hy hj

/-! ### A degree-of-freedom interpolant: `P₁` Lagrange interpolation -/

/-- Elements of `P₁` are affine: `p y = p 0 + ℓ y` with `ℓ` linear. -/
theorem exists_eq_add_of_mem_polyFunctions_one {p : (Fin n → ℝ) → G}
    (hp : p ∈ polyFunctions n 1 G) :
    ∃ ℓ : (Fin n → ℝ) →L[ℝ] G, ∀ y, p y = p 0 + ℓ y := by
  refine ⟨continuousMultilinearCurryFin1 ℝ (Fin n → ℝ) G (iteratedFDeriv ℝ 1 p 0), fun y => ?_⟩
  rw [← taylorPoly_eq_of_mem_polyFunctions hp 0 y, taylorPoly, Finset.sum_range_succ,
    Finset.sum_range_one, continuousMultilinearCurryFin1_apply]
  simp

/-- The barycentric coordinates `(1 - ∑ xᵢ, x₀, …, x_{n-1})` of `x` with respect to the vertices
`0, e₀, …, e_{n-1}` of `T̂`. -/
def refBaryCoord (x : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cons (1 - ∑ i, x i) x

theorem sum_refBaryCoord (x : Fin n → ℝ) : ∑ i, refBaryCoord x i = 1 := by
  simp [refBaryCoord, Fin.sum_univ_succ]

theorem sum_refBaryCoord_smul (x : Fin n → ℝ) : ∑ i, refBaryCoord x i • refPoints n i = x := by
  rw [sum_smul_refPoints]; rfl

theorem refBaryCoord_nonneg {x : Fin n → ℝ} (hx : x ∈ (refSimplex n).closedInterior)
    (i : Fin (n + 1)) : 0 ≤ refBaryCoord x i := by
  rw [mem_closedInterior_refSimplex] at hx
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [refBaryCoord]; linarith [hx.2]
  · simpa [refBaryCoord] using hx.1 i

/-- The `P₁` **Lagrange interpolant** on `T̂`, determined by the vertex values (its degrees of
freedom): `I g (x) = ∑ᵢ λᵢ(x) g(vᵢ)`. -/
def lagrangeP1 (g : (Fin n → ℝ) → G) (x : Fin n → ℝ) : G :=
  ∑ i, refBaryCoord x i • g (refPoints n i)

/-- `P₁` Lagrange interpolation is a reference interpolant of order `r = 1` with stability order
`m = 0` and constant `C = 1` (`sup_{T̂} ‖I g‖ ≤ sup_{T̂} ‖g‖`): a degree-of-freedom instance of
`IsRefInterpolant`, giving the `O(h²)` estimate for `C²` functions. -/
theorem isRefInterpolant_lagrangeP1 (n : ℕ) (G : Type) [NormedAddCommGroup G]
    [NormedSpace ℝ G] : IsRefInterpolant n 1 0 G lagrangeP1 1 where
  le_succ := Nat.zero_le _
  map_sub _ _ _ f g _ _ x _ := by
    simp only [lagrangeP1, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
  apply_eq p hp x _ := by
    obtain ⟨ℓ, hℓ⟩ := exists_eq_add_of_mem_polyFunctions_one hp
    have hs : ∑ i, refBaryCoord x i • ℓ (refPoints n i) = ℓ x := by
      rw [← sum_refBaryCoord_smul x, map_sum]
      simp only [map_smul]
      rw [sum_refBaryCoord_smul]
    rw [lagrangeP1, hℓ x, Finset.sum_congr rfl fun i _ => by rw [hℓ (refPoints n i), smul_add],
      Finset.sum_add_distrib, ← Finset.sum_smul, sum_refBaryCoord, one_smul, hs]
  norm_le _ _ _ g _ B hB x hx := by
    rw [one_mul, Finset.sum_range_one, lagrangeP1]
    calc ‖∑ i, refBaryCoord x i • g (refPoints n i)‖
        ≤ ∑ i, refBaryCoord x i * B 0 := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_smul, Real.norm_of_nonneg (refBaryCoord_nonneg hx i)]
          gcongr
          · exact refBaryCoord_nonneg hx i
          · simpa using hB 0 le_rfl _ ((refSimplex n).point_mem_closedInterior i)
      _ = B 0 := by rw [← Finset.sum_mul, sum_refBaryCoord, one_mul]

end RefSimplex

end Feec.FiniteElement
