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

Taylor polynomials give the classical (`C^{r+1}`, sup-norm) Bramble–Hilbert lemma
([BrambleHilbert1970]; [Ciarlet2002], Thm 3.1.1; [Arnold2018], Ch. 7) and the error of reference
interpolants.

## Main results

* `norm_iteratedFDeriv_sub_taylorPoly_le`: the Taylor estimate on a convex set.
* `norm_iteratedFDeriv_sub_taylorPoly_refSimplex_le`: the Bramble–Hilbert lemma on `T̂`.
* `IsRefInterpolant.norm_sub_le`: the interpolation error of a reference interpolant.

## References

* [J. H. Bramble, S. R. Hilbert, *Estimation of Linear Functionals on Sobolev Spaces with Application to Fourier Transforms and Spline Interpolation*][BrambleHilbert1970]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public section

noncomputable section

open Filter Function Topology MeasureTheory

namespace Feec.FiniteElement

/-! ### Symmetry of iterated derivatives -/

section Symmetry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

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

/-- The Taylor polynomial `T_k f (x) = ∑_{i < k} (1/i!) D^i f(x₀)(x - x₀, …, x - x₀)`. -/
def taylorPoly (f : E → F) (x₀ : E) (k : ℕ) (x : E) : F :=
  ∑ i ∈ Finset.range k, ((i.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ i f x₀ (fun _ => x - x₀))

theorem taylorPoly_zero (f : E → F) (x₀ : E) : taylorPoly f x₀ 0 = 0 := by
  funext x; simp [taylorPoly]

theorem taylorPoly_self (f : E → F) (x₀ : E) (k : ℕ) :
    taylorPoly f x₀ (k + 1) x₀ = f x₀ := by
  rw [taylorPoly, Finset.sum_range_succ']
  simp only [sub_self, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_zero_apply]
  rw [Finset.sum_eq_zero fun i _ => by
    rw [ContinuousMultilinearMap.map_coord_zero _ (0 : Fin (i + 1)) rfl, smul_zero], zero_add]

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

/-- The Taylor estimate on a convex set `K`: for `f` of class `C^k` near `K`, `x₀ ∈ K`,
`‖D^j (f - T_k f)‖ ≤ d^{k-j} sup_K ‖D^k f‖` on `K` for `j ≤ k`, `d ≥ ‖y - x₀‖` on `K`. -/
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

/-- `P_r(ℝⁿ; G)`: the span of the maps `x ↦ q(x) • c`, `q` of total degree `≤ r`, `c ∈ G`. -/
def polyFunctions (n r : ℕ) (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G] :
    Submodule ℝ ((Fin n → ℝ) → G) :=
  Submodule.span ℝ {g | ∃ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ r ∧
    ∃ c : G, g = fun x => MvPolynomial.eval x q • c}

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

theorem taylorPoly_mem_polyFunctions (f : (Fin n → ℝ) → G) (x₀ : Fin n → ℝ) (r : ℕ) :
    taylorPoly f x₀ (r + 1) ∈ polyFunctions n r G := by
  have : taylorPoly f x₀ (r + 1) = ∑ i ∈ Finset.range (r + 1),
      ((i.factorial : ℝ)⁻¹ • fun x => iteratedFDeriv ℝ i f x₀ (fun _ => x - x₀)) := by
    funext x; simp [taylorPoly, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (multilinear_diag_mem_polyFunctions (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) _ x₀)

/-! ### Calculus of polynomial functions -/

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

theorem norm_sub_le_one_of_mem_refSimplex {x y : Fin n → ℝ}
    (hx : x ∈ (refSimplex n).closedInterior) (hy : y ∈ (refSimplex n).closedInterior) :
    ‖x - y‖ ≤ 1 := by
  rw [mem_closedInterior_refSimplex] at hx hy
  have hle : ∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i ≤ 1 → ∀ i, z i ≤ 1 := fun z h0 h1 i =>
    (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)).trans h1
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hx.1 i, hy.1 i, hle x hx.1 hx.2 i, hle y hy.1 hy.2 i]

/-- The Bramble–Hilbert lemma on `T̂`: for `f` of class `C^{r+1}` near `T̂` and `p` its Taylor
polynomial at the barycenter, `sup_{T̂} ‖D^j (f - p)‖ ≤ sup_{T̂} ‖D^{r+1} f‖` for `j ≤ r + 1`. -/
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

/-- A reference interpolant ([Ciarlet2002], Thm 3.1.4): additive, exact on `P_r`, `C^m`-stable. -/
structure IsRefInterpolant (n r m : ℕ) (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G) (C : ℝ) : Prop where
  le_succ : m ≤ r + 1
  /-- additivity on `C^{r+1}` functions -/
  map_sub : ∀ V : Set (Fin n → ℝ), IsOpen V → (refSimplex n).closedInterior ⊆ V →
    ∀ f g, ContDiffOn ℝ (r + 1) f V → ContDiffOn ℝ (r + 1) g V →
    ∀ x ∈ (refSimplex n).closedInterior, I (f - g) x = I f x - I g x
  /-- exactness on `P_r` -/
  apply_eq : ∀ p ∈ polyFunctions n r G, ∀ x ∈ (refSimplex n).closedInterior, I p x = p x
  /-- stability in `C^m(T̂)` -/
  norm_le : ∀ V : Set (Fin n → ℝ), IsOpen V → (refSimplex n).closedInterior ⊆ V →
    ∀ g, ContDiffOn ℝ (r + 1) g V → ∀ B : ℕ → ℝ,
    (∀ j ≤ m, ∀ y ∈ (refSimplex n).closedInterior, ‖iteratedFDeriv ℝ j g y‖ ≤ B j) →
    ∀ x ∈ (refSimplex n).closedInterior, ‖I g x‖ ≤ C * ∑ j ∈ Finset.range (m + 1), B j

/-- The interpolation error on `T̂`: `sup_{T̂} ‖f - I f‖ ≤ (1 + C (m + 1)) sup_{T̂} ‖D^{r+1} f‖`
([Ciarlet2002], Thm 3.1.4, classical form). -/
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

theorem measurableSet_closedInterior (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    MeasurableSet T.closedInterior :=
  T.isCompact_closedInterior.isClosed.measurableSet

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

/-! ### Derivative estimates for reference interpolants -/

/-- The reference error estimate of order `j`: `sup ‖D^j (f - I f)‖ ≤ K sup ‖D^{r+1} f‖` on `T̂`. -/
def HasRefDerivEstimate (n r j : ℕ) (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G) (K : ℝ) : Prop :=
  ∀ (V : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → G) (M : ℝ), IsOpen V →
    (refSimplex n).closedInterior ⊆ V → ContDiffOn ℝ (r + 1) f V →
    (∀ y ∈ (refSimplex n).closedInterior, ‖iteratedFDeriv ℝ (r + 1) f y‖ ≤ M) →
    ∀ y ∈ (refSimplex n).closedInterior, ‖iteratedFDeriv ℝ j (fun z => f z - I f z) y‖ ≤ K * M

end RefSimplex

end Feec.FiniteElement
