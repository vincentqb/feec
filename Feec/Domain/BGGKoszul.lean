module

public import Feec.Domain.DivDivBGG
public import Feec.Domain.HessianBGG

/-!
# Koszul null-homotopies and the explicit cochain map (30) for the Hessian, elasticity and div-div complexes

Let the de Rham complexes of `ℝ³` with values in `𝕜ᵐ'` (bottom row) and `𝕜ᵐ` (top row), in vector
proxies (`deRhamVec`), be linked by constant matrices. A tensor `c_{abl}` gives connecting matrices
(`koszulSMat c`) and the **Koszul operators** `Kᵏ = k(x) ⊗ id`, multiplication of the value index
by `k(x)_{ab} = Σₗ c_{abl} xₗ` (`koszulK c`). When the connecting operators are the matrices of
`c`, they are **null-homotopic on smooth fields**, `Sᵏ = d Kᵏ - Kᵏ⁺¹ d̃` (`koszul_isNullHomotopy`,
(28) of [ArnoldHu2021]): the product rule `∂ⱼ (k(x) u) = k(eⱼ) u + k(x) ∂ⱼ u` leaves the algebraic
part. The Hessian, elasticity and div-div diagrams are of this kind, with `k(x) u = x · u`,
`k(x) ψ = ψ × x` and `k(x) ψ = ψ x` (`hessianS_apply_eq_koszul`, `elasticityS_apply_eq_koszul`,
`divDivS_apply_eq_koszul`), and they satisfy the injectivity/surjectivity condition with explicit
right inverses on smooth fields (`injSurjWith_hessianBGG`, `injSurjWith_elasticityBGG`,
`injSurjWith_divDivBGG`). So **Theorem 7 and Corollary 1 of [ArnoldHu2021] apply to the smooth
Hessian, elasticity and div-div complexes without hypotheses**: the explicit cochain map (30) from
the sum complex of the two de Rham complexes is a quasi-isomorphism
(`quasiIso_hessianSumMap`, …) carrying cohomology representatives of the rows to cohomology
representatives (`hessianBGG_represents`, …). In degree `0` the cohomology of the rows is the
constant fields (`ker_gradOp_smoothMap`, `rowTop_represents_zero`, `rowBot_represents_zero`), so
**the kernel of the first differential is represented by `(30)(c, c̃) = [c + K⁰ c̃]`**
(`Feec.BGG.Data.bggXEquivOfBijective_bggSumMap`, `Feec.BGG.Data.bggXEquivOfLt_bggSumMap`), `c`,
`c̃` constant: the affine functions `c + x · c̃`, the infinitesimal rigid motions `c + c̃ × x`, and
the lowest-order Raviart–Thomas fields `c + c̃ x` (`hessianBGG_represents_zero`,
`elasticityBGG_represents_zero`, `divDivBGG_represents_zero`, with `K⁰` in
`koszulK_hessC_zero_apply`, `koszulK_elC_zero_apply`, `koszulK_ddC_zero_apply`; collected in
`smoothBGGVerdict`).

**Scope.** The explicit-map fields of `Feec.BGG.HilbertData.BGGVerdict` assume the condition
`Feec.BGG.Data.InjSurjWith` between the domain complexes of the `L²` realizations
(`Feec.Domain.hessianMaximalData`, …), and it fails there: `Sᴶ` is not onto between the domains
(for the Hessian, `S⁰ = I` maps `H¹(Ω; 𝕜³)` into `H(curl; Ω)`, a proper subspace for every
nonempty open `Ω`; this is not formalized). Pointwise surjectivity gives right inverses on smooth
fields, not on the graph spaces, so the explicit map is stated here on smooth fields, as in the
smooth and Sobolev settings of [ArnoldHu2021], §4. The cohomology of the smooth de Rham complexes
in positive degrees (the Poincaré lemma on `ℝ³`) is not formalized: Corollary 1 is stated for any
representatives of the rows.

## Main definitions

* `Feec.Domain.smoothMatMul`: multiplication by a smooth matrix field.
* `Feec.Domain.koszulMat`, `koszulK`, `koszulSMat`: the Koszul operators and connecting matrices
  of a tensor; `hessC`, `elC`, `ddC`: the tensors of the three diagrams.
* `Feec.Domain.constFields`; `SmoothBGGVerdict`.

## Main results

* `fderiv_linFun_mul`, **`koszul_isNullHomotopy`**.
* `isNullHomotopy_hessianBGG`, `isNullHomotopy_elasticityBGG`, `isNullHomotopy_divDivBGG`.
* **`quasiIso_hessianSumMap`**, **`quasiIso_elasticitySumMap`**,
  **`quasiIso_divDivSumMap`** ([ArnoldHu2021], Theorem 7); `hessianBGG_represents`,
  `elasticityBGG_represents`, `divDivBGG_represents` (Corollary 1).
* `ker_gradOp_smoothMap`, `represents_zero_ker`, `rowTop_represents_zero`,
  `rowBot_represents_zero`; **`hessianBGG_represents_zero`**, **`elasticityBGG_represents_zero`**,
  **`divDivBGG_represents_zero`**; **`smoothBGGVerdict`**.

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3 ((28)–(31), Theorem 7,
  Corollary 1), §4.1 ((32), the Hessian, elasticity and div-div complexes)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace Feec.Domain

open ConstCoeffOp

variable {𝕜 : Type*} [RCLike 𝕜] {m m' : ℕ}

/-! ## Multiplication by a smooth matrix field -/

section MatField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type*} [Fintype ι]

/-- Multiplication by a smooth matrix field `A : E → 𝕜^{κ×ι}` on smooth fields. -/
def smoothMatMul (A : E → Matrix κ ι 𝕜) (hA : ∀ a b, ContDiff ℝ ∞ fun x => A x a b) :
    smoothFields E 𝕜 ι →ₗ[𝕜] smoothFields E 𝕜 κ where
  toFun f := ⟨fun a x => ∑ b, A x a b * f.1 b x, fun a =>
    ContDiff.sum fun b _ => (hA a b).mul (f.2 b)⟩
  map_add' f g := Subtype.ext (funext fun a => funext fun x => by
    simp [mul_add, Finset.sum_add_distrib])
  map_smul' c f := Subtype.ext (funext fun a => funext fun x => by
    simp [Finset.mul_sum, mul_left_comm])

theorem coe_smoothMatMul (A : E → Matrix κ ι 𝕜) (hA : ∀ a b, ContDiff ℝ ∞ fun x => A x a b)
    (f : smoothFields E 𝕜 ι) (a : κ) (x : E) :
    (smoothMatMul A hA f : κ → E → 𝕜) a x = ∑ b, A x a b * f.1 b x := rfl

end MatField

/-! ## The Koszul operators -/

/-- The linear function `x ↦ Σₗ cₗ xₗ` on `ℝ³`. -/
def linFun (c : Fin 3 → 𝕜) (x : Fin 3 → ℝ) : 𝕜 := ∑ l, c l * (x l : 𝕜)

/-- `linFun c` as a continuous linear map. -/
def linCLM (c : Fin 3 → 𝕜) : (Fin 3 → ℝ) →L[ℝ] 𝕜 :=
  ∑ l, c l • (RCLike.ofRealCLM.comp (ContinuousLinearMap.proj l))

theorem linCLM_apply (c : Fin 3 → 𝕜) (x : Fin 3 → ℝ) : linCLM c x = linFun c x := by
  simp [linCLM, linFun]

theorem contDiff_linFun (c : Fin 3 → 𝕜) : ContDiff ℝ ∞ (linFun c) := by
  have : linFun c = linCLM c := funext fun x => (linCLM_apply c x).symm
  rw [this]
  exact (linCLM c).contDiff

/-- **The product rule for a linear coefficient**: `∂ⱼ (ℓ g) = cⱼ g + ℓ ∂ⱼ g` with
`ℓ = Σₗ cₗ xₗ`. -/
theorem fderiv_linFun_mul (c : Fin 3 → 𝕜) {g : (Fin 3 → ℝ) → 𝕜} (hg : ContDiff ℝ ∞ g)
    (x : Fin 3 → ℝ) (j : Fin 3) :
    fderiv ℝ (fun y => linFun c y * g y) x (coordDir j) =
      c j * g x + linFun c x * fderiv ℝ g x (coordDir j) := by
  have hl : linFun c = linCLM c := funext fun x => (linCLM_apply c x).symm
  have hd : DifferentiableAt ℝ g x := (hg.differentiable (by simp)).differentiableAt
  rw [fderiv_fun_mul (hl ▸ (linCLM c).differentiableAt) hd, hl, (linCLM c).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, linCLM_apply]
  rw [add_comm, mul_comm]
  congr 1
  simp [linFun, Pi.single_apply]

variable (c : Fin m → Fin m' → Fin 3 → 𝕜)

/-- **The Koszul matrix field** of a tensor `c`: `k(x) ⊗ id` in degree `k`, with
`k(x)_{ab} = Σₗ c_{abl} xₗ` acting on the value index and the identity on the form index. -/
def koszulMat : ∀ k : ℤ, (Fin 3 → ℝ) → Matrix (vecIdx m k) (vecIdx m' k) 𝕜
  | .ofNat 0, x => fun a b => linFun (c a b) x
  | .ofNat 1, x => fun a b => if a.2 = b.2 then linFun (c a.1 b.1) x else 0
  | .ofNat 2, x => fun a b => if a.2 = b.2 then linFun (c a.1 b.1) x else 0
  | .ofNat 3, x => fun a b => linFun (c a b) x
  | .ofNat (_ + 4), _ => 0
  | .negSucc _, _ => 0

theorem contDiff_koszulMat : ∀ (k : ℤ) a b, ContDiff ℝ ∞ fun x => koszulMat c k x a b
  | .ofNat 0, _, _ => contDiff_linFun _
  | .ofNat 1, a, b => by
    by_cases h : a.2 = b.2
    · simpa [koszulMat, h] using contDiff_linFun _
    · simpa [koszulMat, h] using contDiff_const
  | .ofNat 2, a, b => by
    by_cases h : a.2 = b.2
    · simpa [koszulMat, h] using contDiff_linFun _
    · simpa [koszulMat, h] using contDiff_const
  | .ofNat 3, _, _ => contDiff_linFun _
  | .ofNat (_ + 4), _, _ => contDiff_const
  | .negSucc _, _, _ => contDiff_const

/-- **The Koszul operators** `Kᵏ : Ṽᵏ → Vᵏ` on smooth fields: multiplication by `koszulMat c k`. -/
def koszulK (k : ℤ) :
    smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx m' k) →ₗ[𝕜] smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx m k) :=
  smoothMatMul (koszulMat c k) (contDiff_koszulMat c k)

theorem koszulK_zero_apply (f : smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx m' 0)) (a : Fin m)
    (x : Fin 3 → ℝ) :
    (koszulK c 0 f : vecIdx m 0 → _ → 𝕜) a x = ∑ b, linFun (c a b) x * f.1 b x := rfl

theorem koszulK_one_apply (f : smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx m' 1)) (a : Fin m)
    (i : Fin 3) (x : Fin 3 → ℝ) :
    (koszulK c 1 f : vecIdx m 1 → _ → 𝕜) (a, i) x = ∑ b, linFun (c a b) x * f.1 (b, i) x := by
  change ∑ bj : Fin m' × Fin 3, (if i = bj.2 then linFun (c a bj.1) x else 0) * f.1 bj x = _
  simp [Fintype.sum_prod_type, ite_mul]

theorem koszulK_two_apply (f : smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx m' 2)) (a : Fin m)
    (i : Fin 3) (x : Fin 3 → ℝ) :
    (koszulK c 2 f : vecIdx m 2 → _ → 𝕜) (a, i) x = ∑ b, linFun (c a b) x * f.1 (b, i) x := by
  change ∑ bj : Fin m' × Fin 3, (if i = bj.2 then linFun (c a bj.1) x else 0) * f.1 bj x = _
  simp [Fintype.sum_prod_type, ite_mul]

theorem koszulK_three_apply (f : smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx m' 3)) (a : Fin m)
    (x : Fin 3 → ℝ) :
    (koszulK c 3 f : vecIdx m 3 → _ → 𝕜) a x = ∑ b, linFun (c a b) x * f.1 b x := rfl

/-- **The connecting matrices of a Koszul tensor** `c`, `Sᵏ = d Kᵏ - Kᵏ⁺¹ d̃` (`koszul_null`):
`(S⁰ u)_{a,j} = Σ_b c_{abj} u_b`,
`(S¹ u)_{a,k} = Σ_b (c_{a,b,k+1} u_{b,k+2} - c_{a,b,k+2} u_{b,k+1})`,
`(S² u)_a = Σ_{b,k} c_{abk} u_{b,k}`. -/
def koszulSMat : ∀ k : ℤ, Matrix (vecIdx m (k + 1)) (vecIdx m' k) 𝕜
  | .ofNat 0 => fun a b => c a.1 b a.2
  | .ofNat 1 => fun a b =>
    if b.2 = a.2 + 2 then c a.1 b.1 (a.2 + 1) else if b.2 = a.2 + 1 then -c a.1 b.1 (a.2 + 2) else 0
  | .ofNat 2 => fun a b => c a b.1 b.2
  | .ofNat (_ + 3) => 0
  | .negSucc _ => 0

theorem ofMatrix_koszulSMat_zero_apply (f : vecIdx m' 0 → (Fin 3 → ℝ) → 𝕜) (a : Fin m)
    (j : Fin 3) (x : Fin 3 → ℝ) :
    (ofMatrix (koszulSMat c 0) : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f (a, j) x =
      ∑ b, c a b j * f b x := by
  rw [ofMatrix_apply]; rfl

theorem ofMatrix_koszulSMat_one_apply (f : vecIdx m' 1 → (Fin 3 → ℝ) → 𝕜) (a : Fin m)
    (k : Fin 3) (x : Fin 3 → ℝ) :
    (ofMatrix (koszulSMat c 1) : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f (a, k) x =
      ∑ b, (c a b (k + 1) * f (b, k + 2) x - c a b (k + 2) * f (b, k + 1) x) := by
  rw [ofMatrix_apply]
  change ∑ bl : Fin m' × Fin 3, (if bl.2 = k + 2 then c a bl.1 (k + 1) else
    if bl.2 = k + 1 then -c a bl.1 (k + 2) else 0) * f bl x = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.sum_univ_three]
  fin_cases k <;> simp <;> ring

theorem ofMatrix_koszulSMat_two_apply (f : vecIdx m' 2 → (Fin 3 → ℝ) → 𝕜) (a : Fin m)
    (x : Fin 3 → ℝ) :
    (ofMatrix (koszulSMat c 2) : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f a x =
      ∑ b, ∑ k, c a b k * f (b, k) x := by
  rw [ofMatrix_apply]
  exact Fintype.sum_prod_type _

/-- `∂ⱼ Σ_b ℓ_b g_b = Σ_b (c_{b,j} g_b + ℓ_b ∂ⱼ g_b)`. -/
theorem fderiv_sum_linFun_mul {β : Type*} [Fintype β] (c : β → Fin 3 → 𝕜)
    {g : β → (Fin 3 → ℝ) → 𝕜} (hg : ∀ b, ContDiff ℝ ∞ (g b)) (x : Fin 3 → ℝ) (j : Fin 3) :
    fderiv ℝ (fun y => ∑ b, linFun (c b) y * g b y) x (coordDir j) =
      ∑ b, (c b j * g b x + linFun (c b) x * fderiv ℝ (g b) x (coordDir j)) := by
  have hd : ∀ b, DifferentiableAt ℝ (fun y => linFun (c b) y * g b y) x := fun b =>
    (((contDiff_linFun (c b)).mul (hg b)).differentiable (by simp)).differentiableAt
  rw [fderiv_fun_sum fun b _ => hd b, sum_apply]
  exact Finset.sum_congr rfl fun b _ => fderiv_linFun_mul (c b) (hg b) x j

/-- **Koszul null-homotopy**: for BGG data of the de Rham complexes with values in `𝕜ᵐ`, `𝕜ᵐ'`
whose connecting operators are the matrices of a tensor `c` (`koszulSMat c`), the connecting maps
are null-homotopic on smooth fields, `Sᵏ = d Kᵏ - Kᵏ⁺¹ d̃` with `K = koszulK c`, multiplication by
`k(x) ⊗ id`, `k(x)_{ab} = Σₗ c_{abl} xₗ` ([ArnoldHu2021], (28)). -/
theorem koszul_isNullHomotopy
    {S : ∀ k : ℤ, ConstCoeffOp (Fin 3 → ℝ) 𝕜 (vecIdx m' k) (vecIdx m (k + 1))}
    (hS : ∀ k f, (S k).apply f = (ofMatrix (koszulSMat c k)).apply f)
    (hanti : ∀ k (f : vecIdx m' k → (Fin 3 → ℝ) → 𝕜), (∀ i, ContDiff ℝ ∞ (f i)) →
      (vecOp 𝕜 m (k + 1)).apply ((S k).apply f) = -(S (k + 1)).apply ((vecOp 𝕜 m' k).apply f)) :
    (ConstCoeffBGG.mk (deRhamVec 𝕜 m) (deRhamVec 𝕜 m') S hanti).smoothData.IsNullHomotopy
      (koszulK c) := by
  rintro i _ rfl μ
  simp only [ConstCoeffBGG.smoothData_S, ConstCoeffBGG.smoothData_d, ConstCoeffBGG.smoothData_dt]
  refine Subtype.ext ?_
  rw [Submodule.coe_sub, coe_smoothMap, coe_smoothMap, hS]
  match i with
  | .ofNat 0 =>
    funext ⟨a, j⟩ x
    change (ofMatrix (koszulSMat c 0)).apply μ.1 (a, j) x =
      (gradOp 3 m).apply (koszulK c 0 μ).1 (a, j) x -
        (koszulK c 1 ((gradOp 3 m').smoothMap μ)).1 (a, j) x
    rw [ofMatrix_koszulSMat_zero_apply, gradOp_apply, koszulK_one_apply]
    change _ = fderiv ℝ (fun y => ∑ b, linFun (c a b) y * μ.1 b y) x (coordDir j) - _
    simp only [fderiv_sum_linFun_mul (c a) μ.2, coe_smoothMap, gradOp_apply,
      Finset.sum_add_distrib, add_sub_cancel_right]
  | .ofNat 1 =>
    funext ⟨a, k⟩ x
    change (ofMatrix (koszulSMat c 1)).apply μ.1 (a, k) x =
      (curlOp m).apply (koszulK c 1 μ).1 (a, k) x -
        (koszulK c 2 ((curlOp m').smoothMap μ)).1 (a, k) x
    have hK : ∀ i, (koszulK c 1 μ).1 (a, i) = fun y => ∑ b, linFun (c a b) y * μ.1 (b, i) y :=
      fun i => funext (koszulK_one_apply c μ a i)
    rw [ofMatrix_koszulSMat_one_apply, curlOp_apply, koszulK_two_apply, hK, hK,
      fderiv_sum_linFun_mul (c a) (g := fun b => μ.1 (b, k + 2)) (fun b => μ.2 _),
      fderiv_sum_linFun_mul (c a) (g := fun b => μ.1 (b, k + 1)) (fun b => μ.2 _)]
    simp only [coe_smoothMap, curlOp_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  | .ofNat 2 =>
    funext a x
    change (ofMatrix (koszulSMat c 2)).apply μ.1 a x =
      (divOp 3 m).apply (koszulK c 2 μ).1 a x -
        (koszulK c 3 ((divOp 3 m').smoothMap μ)).1 a x
    have hK : ∀ i, (koszulK c 2 μ).1 (a, i) = fun y => ∑ b, linFun (c a b) y * μ.1 (b, i) y :=
      fun i => funext (koszulK_two_apply c μ a i)
    rw [ofMatrix_koszulSMat_two_apply, divOp_apply, koszulK_three_apply]
    simp only [hK, coe_smoothMap, divOp_apply]
    rw [Finset.sum_congr rfl fun i _ =>
      fderiv_sum_linFun_mul (c a) (g := fun b => μ.1 (b, i)) (fun b => μ.2 _) x i]
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun i b => linFun (c a b) x * _)]
    rw [Finset.sum_comm (f := fun i b => c a b i * _), add_sub_cancel_right]
  | .ofNat (n + 3) =>
    have := isEmpty_vecIdx m (k := .ofNat (n + 3) + 1)
      (Or.inr (by simp only [Int.ofNat_eq_natCast]; omega))
    exact funext fun i => isEmptyElim i
  | .negSucc 0 =>
    have := isEmpty_vecIdx m' (k := .negSucc 0) (Or.inl (by decide))
    have := isEmpty_vecIdx m (k := .negSucc 0) (Or.inl (by decide))
    rw [apply_of_isEmpty, apply_of_isEmpty,
      show (vecOp 𝕜 m' (.negSucc 0)).smoothMap μ = 0 from
        Subtype.ext ((coe_smoothMap _ _).trans (apply_of_isEmpty _ _)), map_zero,
      Submodule.coe_zero, sub_zero]
  | .negSucc (n + 1) =>
    have := isEmpty_vecIdx m (k := .negSucc (n + 1) + 1) (Or.inl (by omega))
    exact funext fun i => isEmptyElim i

/-! ## The Hessian, elasticity and div-div diagrams -/

variable (𝕜) in
/-- The Koszul tensor of the Hessian diagram, `k(x) u = x · u`. -/
def hessC : Fin 1 → Fin 3 → Fin 3 → 𝕜 := fun _ b l => if b = l then 1 else 0

variable (𝕜) in
/-- The Koszul tensor of the elasticity diagram, `k(x)_{ab} = Σₗ ε_{abl} xₗ`, `k(x) ψ = ψ × x`. -/
def elC : Fin 3 → Fin 3 → Fin 3 → 𝕜 := fun a b l =>
  if b = a + 1 ∧ l = a + 2 then 1 else if b = a + 2 ∧ l = a + 1 then -1 else 0

variable (𝕜) in
/-- The Koszul tensor of the div-div diagram, `k(x) ψ = ψ x`. -/
def ddC : Fin 3 → Fin 1 → Fin 3 → 𝕜 := fun a _ l => if a = l then 1 else 0

theorem ofMatrix_koszulSMat_apply_of_not {m m' : ℕ} (c : Fin m → Fin m' → Fin 3 → 𝕜) {k : ℤ}
    (hk : k < 0 ∨ 2 < k) (f : vecIdx m' k → (Fin 3 → ℝ) → 𝕜) :
    (ofMatrix (koszulSMat c k)).apply f = (zeroOp (E := Fin 3 → ℝ) (𝕜 := 𝕜) _ _).apply f := by
  have h0 : koszulSMat c k = 0 := by
    match k, hk with
    | .ofNat (_ + 3), _ => rfl
    | .negSucc _, _ => rfl
    | .ofNat 0, hk | .ofNat 1, hk | .ofNat 2, hk => exact absurd hk (by decide)
  rw [h0]
  funext j x
  rw [ofMatrix_apply]
  simp [ConstCoeffOp.apply, zeroOp]

/-- The connecting operators of the Hessian diagram are those of its Koszul tensor. -/
theorem hessianS_apply_eq_koszul (k : ℤ) (f : vecIdx 3 k → (Fin 3 → ℝ) → 𝕜) :
    (hessianS 𝕜 k).apply f = (ofMatrix (koszulSMat (hessC 𝕜) k)).apply f := by
  match k with
  | .ofNat 0 =>
    refine congrArg (fun M => (ofMatrix M : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f) ?_
    ext ⟨a, j⟩ b
    fin_cases a; fin_cases j <;> fin_cases b <;> simp [koszulSMat, hessC, hessS0]
  | .ofNat 1 =>
    refine congrArg (fun M => (ofMatrix M : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f) ?_
    ext ⟨a, k⟩ ⟨b, l⟩
    fin_cases a; fin_cases k <;> fin_cases b <;> fin_cases l <;> simp [koszulSMat, hessC, hessS1]
  | .ofNat 2 =>
    refine congrArg (fun M => (ofMatrix M : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f) ?_
    ext a ⟨b, l⟩
    fin_cases a; fin_cases b <;> fin_cases l <;> simp [koszulSMat, hessC, hessS2]
  | .ofNat (n + 3) => exact (ofMatrix_koszulSMat_apply_of_not _
      (Or.inr (by simp only [Int.ofNat_eq_natCast]; omega)) f).symm
  | .negSucc n => exact (ofMatrix_koszulSMat_apply_of_not _ (Or.inl (Int.negSucc_lt_zero n)) f).symm

/-- **The connecting maps of the Hessian diagram are null-homotopic** on smooth fields, with the
Koszul operators of `k(x) u = x · u` ([ArnoldHu2021], (28)). -/
theorem isNullHomotopy_hessianBGG :
    (hessianBGG 𝕜).smoothData.IsNullHomotopy (koszulK (hessC 𝕜)) :=
  koszul_isNullHomotopy _ hessianS_apply_eq_koszul hessianS_anticomm

/-- The connecting operators of the elasticity diagram are those of its Koszul tensor. -/
theorem elasticityS_apply_eq_koszul (k : ℤ) (f : vecIdx 3 k → (Fin 3 → ℝ) → 𝕜) :
    (elasticityS 𝕜 k).apply f = (ofMatrix (koszulSMat (elC 𝕜) k)).apply f := by
  match k with
  | .ofNat 0 =>
    refine congrArg (fun M => (ofMatrix M : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f) ?_
    ext ⟨a, j⟩ b
    fin_cases a <;> fin_cases j <;> fin_cases b <;> simp [koszulSMat, elC, elS0]
  | .ofNat 1 =>
    refine congrArg (fun M => (ofMatrix M : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f) ?_
    ext ⟨a, k⟩ ⟨b, l⟩
    fin_cases a <;> fin_cases k <;> fin_cases b <;> fin_cases l <;>
      simp [koszulSMat, elC, elS1]
  | .ofNat 2 =>
    refine congrArg (fun M => (ofMatrix M : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f) ?_
    ext a ⟨b, l⟩
    fin_cases a <;> fin_cases b <;> fin_cases l <;> simp [koszulSMat, elC, elS2]
  | .ofNat (n + 3) => exact (ofMatrix_koszulSMat_apply_of_not _
      (Or.inr (by simp only [Int.ofNat_eq_natCast]; omega)) f).symm
  | .negSucc n => exact (ofMatrix_koszulSMat_apply_of_not _ (Or.inl (Int.negSucc_lt_zero n)) f).symm

/-- **The connecting maps of the elasticity diagram are null-homotopic** on smooth fields, with the
Koszul operators of `k(x) ψ = ψ × x` ([ArnoldHu2021], (28)). -/
theorem isNullHomotopy_elasticityBGG :
    (elasticityBGG 𝕜).smoothData.IsNullHomotopy (koszulK (elC 𝕜)) :=
  koszul_isNullHomotopy _ elasticityS_apply_eq_koszul elasticityS_anticomm

/-- The connecting operators of the div-div diagram are those of its Koszul tensor. -/
theorem divDivS_apply_eq_koszul (k : ℤ) (f : vecIdx 1 k → (Fin 3 → ℝ) → 𝕜) :
    (divDivS 𝕜 k).apply f = (ofMatrix (koszulSMat (ddC 𝕜) k)).apply f := by
  match k with
  | .ofNat 0 =>
    refine congrArg (fun M => (ofMatrix M : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f) ?_
    ext ⟨a, j⟩ b
    fin_cases a <;> fin_cases j <;> fin_cases b <;> simp [koszulSMat, ddC, ddS0]
  | .ofNat 1 =>
    refine congrArg (fun M => (ofMatrix M : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f) ?_
    ext ⟨a, k⟩ ⟨b, l⟩
    fin_cases a <;> fin_cases k <;> fin_cases b <;> fin_cases l <;>
      simp [koszulSMat, ddC, ddS1, elS0]
  | .ofNat 2 =>
    refine congrArg (fun M => (ofMatrix M : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).apply f) ?_
    ext a ⟨b, l⟩
    fin_cases a <;> fin_cases b <;> fin_cases l <;> simp [koszulSMat, ddC, ddS2]
  | .ofNat (n + 3) => exact (ofMatrix_koszulSMat_apply_of_not _
      (Or.inr (by simp only [Int.ofNat_eq_natCast]; omega)) f).symm
  | .negSucc n => exact (ofMatrix_koszulSMat_apply_of_not _ (Or.inl (Int.negSucc_lt_zero n)) f).symm

/-- **The connecting maps of the div-div diagram are null-homotopic** on smooth fields, with the
Koszul operators of `k(x) ψ = ψ x` ([ArnoldHu2021], (28)). -/
theorem isNullHomotopy_divDivBGG :
    (divDivBGG 𝕜).smoothData.IsNullHomotopy (koszulK (ddC 𝕜)) :=
  koszul_isNullHomotopy _ divDivS_apply_eq_koszul divDivS_anticomm

/-! ### The Koszul operators in degree `0` -/

/-- `K⁰ u = x · u` for the Hessian diagram. -/
theorem koszulK_hessC_zero_apply (f : smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx 3 0)) (x : Fin 3 → ℝ) :
    (koszulK (hessC 𝕜) 0 f : vecIdx 1 0 → _ → 𝕜) 0 x = ∑ l, (x l : 𝕜) * f.1 l x := by
  rw [koszulK_zero_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [linFun, hessC]

/-- `K⁰ ψ = ψ × x` for the elasticity diagram. -/
theorem koszulK_elC_zero_apply (f : smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx 3 0)) (a : Fin 3)
    (x : Fin 3 → ℝ) :
    (koszulK (elC 𝕜) 0 f : vecIdx 3 0 → _ → 𝕜) a x =
      f.1 (a + 1) x * x (a + 2) - f.1 (a + 2) x * x (a + 1) := by
  rw [koszulK_zero_apply]
  simp only [linFun, elC, Fin.sum_univ_three]
  fin_cases a <;> simp <;> ring

/-- `K⁰ ψ = ψ x` for the div-div diagram. -/
theorem koszulK_ddC_zero_apply (f : smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx 1 0)) (a : Fin 3)
    (x : Fin 3 → ℝ) :
    (koszulK (ddC 𝕜) 0 f : vecIdx 3 0 → _ → 𝕜) a x = (x a : 𝕜) * f.1 0 x := by
  rw [koszulK_zero_apply, Fin.sum_univ_one]
  simp [linFun, ddC, mul_comm]

/-! ## Constant fields: the cohomology of the rows in degree `0` -/

/-- The constant smooth fields. -/
def constFields (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (𝕜 : Type*) [RCLike 𝕜]
    (ι : Type*) : Submodule 𝕜 (smoothFields E 𝕜 ι) where
  carrier := {f | ∀ i x y, f.1 i x = f.1 i y}
  add_mem' hf hg i x y := by simp [hf i x y, hg i x y]
  zero_mem' _ _ _ := rfl
  smul_mem' c f hf i x y := by simp [hf i x y]

/-- **The smooth fields with vanishing gradient are the constants.** -/
theorem ker_gradOp_smoothMap :
    LinearMap.ker (gradOp 3 m : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).smoothMap =
      constFields (Fin 3 → ℝ) 𝕜 (Fin m) := by
  ext f
  rw [LinearMap.mem_ker]
  constructor
  · intro hf a x y
    have hd : Differentiable ℝ (f.1 a) := (f.2 a).differentiable (by simp)
    refine is_const_of_fderiv_eq_zero hd (fun z => ?_) x y
    refine ContinuousLinearMap.coe_injective ((Pi.basisFun ℝ (Fin 3)).ext fun j => ?_)
    have := congrFun (congrFun (congrArg Subtype.val hf) (a, j)) z
    rw [coe_smoothMap, gradOp_apply] at this
    simpa [Pi.basisFun_apply] using this
  · intro hf
    refine Subtype.ext (funext fun aj => funext fun z => ?_)
    rw [coe_smoothMap, gradOp_apply]
    have : f.1 aj.1 = fun _ => f.1 aj.1 0 := funext fun x => hf aj.1 x 0
    rw [this]
    simp

/-- In degree `0`, after a zero space, the cohomology is represented by the kernel. -/
theorem represents_zero_ker {R : Type*} [Ring R] {K : CochainComplex (ModuleCat R) ℤ}
    (h : Subsingleton (K.X (-1))) :
    K.Represents 0 (LinearMap.ker (K.d 0 1).hom) := by
  have hp : (ComplexShape.up ℤ).prev 0 = -1 := by simp
  have hn : (ComplexShape.up ℤ).next 0 = 1 := by simp
  have hr : LinearMap.range (K.d ((ComplexShape.up ℤ).prev 0) 0).hom = ⊥ := by
    rw [hp]
    refine eq_bot_iff.2 ?_
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y 0, map_zero]
    exact Submodule.zero_mem _
  refine ⟨?_, ?_⟩
  · rw [hr, bot_sup_eq, hn]
  · rw [hr]; exact disjoint_bot_left

/-- **The degree-`0` cohomology of the smooth de Rham complexes is the constants**: in the top row
of the smooth BGG data of `deRhamVec m` over `deRhamVec m'`. -/
theorem rowTop_represents_zero
    {S : ∀ k : ℤ, ConstCoeffOp (Fin 3 → ℝ) 𝕜 (vecIdx m' k) (vecIdx m (k + 1))} {hanti} :
    (ConstCoeffBGG.mk (deRhamVec 𝕜 m) (deRhamVec 𝕜 m') S hanti).smoothData.rowTop.Represents 0
      (constFields (Fin 3 → ℝ) 𝕜 (Fin m)) := by
  have := isEmpty_vecIdx m (k := -1) (Or.inl (by decide))
  have h := represents_zero_ker (K := (ConstCoeffBGG.mk (deRhamVec 𝕜 m) (deRhamVec 𝕜 m') S
    hanti).smoothData.rowTop) subsingleton_smoothFields
  rwa [show (LinearMap.ker (((ConstCoeffBGG.mk (deRhamVec 𝕜 m) (deRhamVec 𝕜 m') S
    hanti).smoothData.rowTop.d 0 1).hom)) = constFields (Fin 3 → ℝ) 𝕜 (Fin m) from
      (congrArg LinearMap.ker (ConstCoeffBGG.smoothData_d _ 0)).trans ker_gradOp_smoothMap] at h

/-- The degree-`0` cohomology of the bottom row is the constants. -/
theorem rowBot_represents_zero
    {S : ∀ k : ℤ, ConstCoeffOp (Fin 3 → ℝ) 𝕜 (vecIdx m' k) (vecIdx m (k + 1))} {hanti} :
    (ConstCoeffBGG.mk (deRhamVec 𝕜 m) (deRhamVec 𝕜 m') S hanti).smoothData.rowBot.Represents 0
      (constFields (Fin 3 → ℝ) 𝕜 (Fin m')) := by
  have := isEmpty_vecIdx m' (k := -1) (Or.inl (by decide))
  have h := represents_zero_ker (K := (ConstCoeffBGG.mk (deRhamVec 𝕜 m) (deRhamVec 𝕜 m') S
    hanti).smoothData.rowBot) subsingleton_smoothFields
  rwa [show (LinearMap.ker (((ConstCoeffBGG.mk (deRhamVec 𝕜 m) (deRhamVec 𝕜 m') S
    hanti).smoothData.rowBot.d 0 1).hom)) = constFields (Fin 3 → ℝ) 𝕜 (Fin m') from
      (congrArg LinearMap.ker (ConstCoeffBGG.smoothData_dt _ 0)).trans ker_gradOp_smoothMap] at h

variable (𝕜) in
/-- **The explicit cochain map (30) of the Hessian complex** on smooth fields, from the sum complex
of the two de Rham complexes to the Hessian BGG complex `bgg 0`, with the right inverses `hessianT`
and the Koszul null-homotopy of `k(x) u = x · u`. [ArnoldHu2021], (30) -/
abbrev hessianSumMap :
    (hessianBGG 𝕜).smoothData.sumComplex ⟶ (hessianBGG 𝕜).smoothData.bgg 0 :=
  (hessianBGG 𝕜).smoothData.bggSumMap ((hessianBGG 𝕜).predMap (hessianT 𝕜))
    isNullHomotopy_hessianBGG injSurjWith_hessianBGG

/-- **Theorem 7 for the Hessian complex**: the explicit cochain map (30) induces an isomorphism on
cohomology. [ArnoldHu2021], Theorem 7 -/
theorem quasiIso_hessianSumMap : QuasiIso (hessianSumMap 𝕜) :=
  BGG.Data.quasiIso_bggSumMap _ _

/-- **Corollary 1 for the Hessian complex**: (30) carries cohomology representatives `H × H̃` of the
two smooth de Rham complexes to cohomology representatives of the Hessian BGG complex.
[ArnoldHu2021], Corollary 1, (31) -/
theorem hessianBGG_represents {i : ℤ} {H : Submodule 𝕜 (smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx 1 i))}
    {Ht : Submodule 𝕜 (smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx 3 i))}
    (hH : (hessianBGG 𝕜).smoothData.rowTop.Represents i H)
    (hHt : (hessianBGG 𝕜).smoothData.rowBot.Represents i Ht) :
    ((hessianBGG 𝕜).smoothData.bgg 0).Represents i
      ((H.prod Ht).map ((hessianSumMap 𝕜).f i).hom) :=
  BGG.Data.bgg_represents _ _ hH hHt

/-- **The degree-`0` cohomology of the Hessian complex**: the kernel of the first differential of
the Hessian BGG complex is represented by `(30)(c, c̃) = [c + K⁰ c̃]` for constant fields `c`, `c̃`:
the affine functions `c + x · c̃`. [ArnoldHu2021], Corollary 1 -/
theorem hessianBGG_represents_zero :
    ((hessianBGG 𝕜).smoothData.bgg 0).Represents 0
      (((constFields (Fin 3 → ℝ) 𝕜 (Fin 1)).prod (constFields (Fin 3 → ℝ) 𝕜 (Fin 3))).map
        ((hessianSumMap 𝕜).f 0).hom) :=
  hessianBGG_represents rowTop_represents_zero rowBot_represents_zero

variable (𝕜) in
/-- **The explicit cochain map (30) of the elasticity complex** on smooth fields, from the sum
complex of the two de Rham complexes to the elasticity BGG complex `bgg 1`, with the right inverses
`elasticityT` and the Koszul null-homotopy of `k(x) ψ = ψ × x`. [ArnoldHu2021], (30) -/
abbrev elasticitySumMap :
    (elasticityBGG 𝕜).smoothData.sumComplex ⟶ (elasticityBGG 𝕜).smoothData.bgg 1 :=
  (elasticityBGG 𝕜).smoothData.bggSumMap ((elasticityBGG 𝕜).predMap (elasticityT 𝕜))
    isNullHomotopy_elasticityBGG injSurjWith_elasticityBGG

/-- **Theorem 7 for the elasticity complex**: the explicit cochain map (30) induces an isomorphism
on cohomology. [ArnoldHu2021], Theorem 7 -/
theorem quasiIso_elasticitySumMap : QuasiIso (elasticitySumMap 𝕜) :=
  BGG.Data.quasiIso_bggSumMap _ _

/-- **Corollary 1 for the elasticity complex**: (30) carries cohomology representatives `H × H̃` of
the two smooth de Rham complexes to cohomology representatives of the elasticity BGG complex.
[ArnoldHu2021], Corollary 1, (31) -/
theorem elasticityBGG_represents {i : ℤ} {H : Submodule 𝕜 (smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx 3 i))}
    {Ht : Submodule 𝕜 (smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx 3 i))}
    (hH : (elasticityBGG 𝕜).smoothData.rowTop.Represents i H)
    (hHt : (elasticityBGG 𝕜).smoothData.rowBot.Represents i Ht) :
    ((elasticityBGG 𝕜).smoothData.bgg 1).Represents i
      ((H.prod Ht).map ((elasticitySumMap 𝕜).f i).hom) :=
  BGG.Data.bgg_represents _ _ hH hHt

/-- **The degree-`0` cohomology of the elasticity complex**: the kernel of the first differential of
the elasticity BGG complex is represented by `(30)(c, c̃) = [c + K⁰ c̃]` for constant fields `c`,
`c̃`: the infinitesimal rigid motions `c + c̃ × x`. [ArnoldHu2021], Corollary 1 -/
theorem elasticityBGG_represents_zero :
    ((elasticityBGG 𝕜).smoothData.bgg 1).Represents 0
      (((constFields (Fin 3 → ℝ) 𝕜 (Fin 3)).prod (constFields (Fin 3 → ℝ) 𝕜 (Fin 3))).map
        ((elasticitySumMap 𝕜).f 0).hom) :=
  elasticityBGG_represents rowTop_represents_zero rowBot_represents_zero

variable (𝕜) in
/-- **The explicit cochain map (30) of the div-div complex** on smooth fields, from the sum complex
of the two de Rham complexes to the div-div BGG complex `bgg 2`, with the right inverses `divDivT`
and the Koszul null-homotopy of `k(x) ψ = ψ x`. [ArnoldHu2021], (30) -/
abbrev divDivSumMap :
    (divDivBGG 𝕜).smoothData.sumComplex ⟶ (divDivBGG 𝕜).smoothData.bgg 2 :=
  (divDivBGG 𝕜).smoothData.bggSumMap ((divDivBGG 𝕜).predMap (divDivT 𝕜))
    isNullHomotopy_divDivBGG injSurjWith_divDivBGG

/-- **Theorem 7 for the div-div complex**: the explicit cochain map (30) induces an isomorphism on
cohomology. [ArnoldHu2021], Theorem 7 -/
theorem quasiIso_divDivSumMap : QuasiIso (divDivSumMap 𝕜) :=
  BGG.Data.quasiIso_bggSumMap _ _

/-- **Corollary 1 for the div-div complex**: (30) carries cohomology representatives `H × H̃` of the
two smooth de Rham complexes to cohomology representatives of the div-div BGG complex.
[ArnoldHu2021], Corollary 1, (31) -/
theorem divDivBGG_represents {i : ℤ} {H : Submodule 𝕜 (smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx 3 i))}
    {Ht : Submodule 𝕜 (smoothFields (Fin 3 → ℝ) 𝕜 (vecIdx 1 i))}
    (hH : (divDivBGG 𝕜).smoothData.rowTop.Represents i H)
    (hHt : (divDivBGG 𝕜).smoothData.rowBot.Represents i Ht) :
    ((divDivBGG 𝕜).smoothData.bgg 2).Represents i
      ((H.prod Ht).map ((divDivSumMap 𝕜).f i).hom) :=
  BGG.Data.bgg_represents _ _ hH hHt

/-- **The degree-`0` cohomology of the div-div complex**: the kernel of the first differential of
the div-div BGG complex is represented by `(30)(c, c̃) = [c + K⁰ c̃]` for constant fields `c`, `c̃`:
the lowest-order Raviart–Thomas fields `c + c̃ x`. [ArnoldHu2021], Corollary 1 -/
theorem divDivBGG_represents_zero :
    ((divDivBGG 𝕜).smoothData.bgg 2).Represents 0
      (((constFields (Fin 3 → ℝ) 𝕜 (Fin 3)).prod (constFields (Fin 3 → ℝ) 𝕜 (Fin 1))).map
        ((divDivSumMap 𝕜).f 0).hom) :=
  divDivBGG_represents rowTop_represents_zero rowBot_represents_zero

universe u

/-- **The explicit cochain map (30) on the smooth Hessian, elasticity and div-div complexes**: for
each, Theorem 7 (the map is a quasi-isomorphism) and Corollary 1 in degree `0` (the kernel of the
first differential is the image of the constant fields). Each field is the statement of the named
theorem. [ArnoldHu2021], Theorem 7, Corollary 1 -/
structure SmoothBGGVerdict : Prop where
  /-- `quasiIso_hessianSumMap` -/
  hessian : type_of% @quasiIso_hessianSumMap.{u}
  /-- `hessianBGG_represents_zero`: the affine functions -/
  hessian_zero : type_of% @hessianBGG_represents_zero.{u}
  /-- `quasiIso_elasticitySumMap` -/
  elasticity : type_of% @quasiIso_elasticitySumMap.{u}
  /-- `elasticityBGG_represents_zero`: the infinitesimal rigid motions -/
  elasticity_zero : type_of% @elasticityBGG_represents_zero.{u}
  /-- `quasiIso_divDivSumMap` -/
  divDiv : type_of% @quasiIso_divDivSumMap.{u}
  /-- `divDivBGG_represents_zero`: the lowest-order Raviart–Thomas fields -/
  divDiv_zero : type_of% @divDivBGG_represents_zero.{u}

/-- **The explicit map (30) applies unconditionally to the smooth Hessian, elasticity and div-div
complexes** (`SmoothBGGVerdict`). -/
theorem smoothBGGVerdict : SmoothBGGVerdict.{u} :=
  ⟨quasiIso_hessianSumMap, hessianBGG_represents_zero, quasiIso_elasticitySumMap,
    elasticityBGG_represents_zero, quasiIso_divDivSumMap, divDivBGG_represents_zero⟩

end Feec.Domain
