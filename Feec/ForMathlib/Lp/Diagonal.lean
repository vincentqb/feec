module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Diagonal operators on `ℓ²`

For a sequence `a : ι → 𝕜`, the **diagonal operator** `(xᵢ) ↦ (aᵢ xᵢ)` on `ℓ²(ι, 𝕜)`, with its
maximal domain `{x | (aᵢ xᵢ) ∈ ℓ²}` (`lp.diagOp a`), is closed (`lp.isClosed_diagOp`) and densely
defined (`lp.dense_diagOp_domain`: the finitely supported sequences lie in its domain); it is `0`
for `a = 0` (`lp.diagOp_zero`) and onto when `1 ≤ ‖aᵢ‖` for every `i` (`lp.range_diagOp_eq_top`).
For `‖aᵢ‖ → ∞` it is unbounded: the closed operators diagonal in an orthonormal basis.

On `ℓ²(ℕ, 𝕜)`, the vectors of `𝕜ⁿ` are the sequences supported in `{0, …, n - 1}`: `lp.ofFin n` is
an isometry (`lp.inner_ofFin_ofFin`) whose adjoint is the truncation `lp.truncFin n` to the first
`n` coordinates (`lp.truncFin_apply`), `ofFin n (truncFin n x) → x` (`lp.tendsto_ofFin_truncFin`),
and a diagonal operator acts on these vectors coordinatewise (`lp.diagOp_ofFin`,
`lp.truncFin_diagOp`): the spectral Galerkin spaces of a diagonal operator.

## References

* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995] (closed operators;
  multiplication operators are the standard examples)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace lp
open Filter Topology

@[expose] public noncomputable section

namespace lp

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}

/-! ### The diagonal operator -/

/-- The maximal domain `{x | (aᵢ xᵢ) ∈ ℓ²}` of the diagonal operator of `a`. -/
def diagDomain (a : ι → 𝕜) : Submodule 𝕜 ℓ²(ι, 𝕜) where
  carrier := {x | Memℓp (fun i => a i * x i) 2}
  add_mem' {x y} hx hy := by
    change Memℓp (fun i => a i * (x i + y i)) 2
    simp_rw [mul_add]
    exact hx.add hy
  zero_mem' := by
    change Memℓp (fun i => a i * 0) 2
    simp_rw [mul_zero]
    exact zero_mem_ℓp'
  smul_mem' c x hx := by
    change Memℓp (fun i => a i * (c * x i)) 2
    simp_rw [mul_left_comm (a _) c]
    exact hx.const_mul c

/-- The **diagonal operator** `(xᵢ) ↦ (aᵢ xᵢ)` on `ℓ²(ι, 𝕜)`, with its maximal domain
`{x | (aᵢ xᵢ) ∈ ℓ²}`. -/
def diagOp (a : ι → 𝕜) : ℓ²(ι, 𝕜) →ₗ.[𝕜] ℓ²(ι, 𝕜) where
  domain := diagDomain a
  toFun :=
    { toFun := fun x => ⟨fun i => a i * (x : ℓ²(ι, 𝕜)) i, x.2⟩
      map_add' := fun x y => lp.ext (funext fun i => by
        change a i * ((x : ℓ²(ι, 𝕜)) i + (y : ℓ²(ι, 𝕜)) i) = _
        rw [mul_add]; rfl)
      map_smul' := fun c x => lp.ext (funext fun i => by
        change a i * (c * (x : ℓ²(ι, 𝕜)) i) = c * (a i * (x : ℓ²(ι, 𝕜)) i)
        ring) }

variable {a : ι → 𝕜}

theorem mem_diagOp_domain {x : ℓ²(ι, 𝕜)} :
    x ∈ (diagOp a).domain ↔ Memℓp (fun i => a i * x i) 2 := Iff.rfl

@[simp] theorem diagOp_apply (x : (diagOp a).domain) (i : ι) :
    diagOp a x i = a i * (x : ℓ²(ι, 𝕜)) i := rfl

/-- The graph of the diagonal operator: `(x, y) ∈ Γ(diagOp a)` iff `yᵢ = aᵢ xᵢ` for every `i`. -/
theorem mem_graph_diagOp_iff {x y : ℓ²(ι, 𝕜)} :
    (x, y) ∈ (diagOp a).graph ↔ ∀ i, y i = a i * x i := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    change a i * (z : ℓ²(ι, 𝕜)) i = a i * x i
    rw [hz]
  · intro h
    have hx : x ∈ (diagOp a).domain := by
      rw [mem_diagOp_domain, show (fun i => a i * x i) = ⇑y from funext fun i => (h i).symm]
      exact lp.memℓp y
    exact ⟨⟨x, hx⟩, rfl, lp.ext (funext fun i => (h i).symm)⟩

/-- **The diagonal operator is closed**: its graph `⋂ᵢ {(x, y) | yᵢ = aᵢ xᵢ}` is an intersection
of closed sets. -/
theorem isClosed_diagOp (a : ι → 𝕜) : (diagOp a).IsClosed := by
  have e : ((diagOp a).graph : Set (ℓ²(ι, 𝕜) × ℓ²(ι, 𝕜))) =
      ⋂ i, {p | p.2 i = a i * p.1 i} := by
    ext p
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_graph_diagOp_iff
  rw [LinearPMap.IsClosed, e]
  exact isClosed_iInter fun i =>
    isClosed_eq ((lp.evalCLM 𝕜 (fun _ : ι => 𝕜) 2 i).continuous.comp continuous_snd)
      (continuous_const.mul ((lp.evalCLM 𝕜 (fun _ : ι => 𝕜) 2 i).continuous.comp continuous_fst))

theorem single_mem_diagOp_domain [DecidableEq ι] (a : ι → 𝕜) (i : ι) (c : 𝕜) :
    lp.single 2 i c ∈ (diagOp a).domain := by
  rw [mem_diagOp_domain, show (fun j => a j * (lp.single 2 i c : ℓ²(ι, 𝕜)) j) =
      ⇑(lp.single 2 i (a i * c) : ℓ²(ι, 𝕜)) from funext fun j => by
    rw [lp.single_apply, lp.single_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]]
  exact lp.memℓp _

/-- **The diagonal operator is densely defined**: the finitely supported sequences lie in its
domain. -/
theorem dense_diagOp_domain (a : ι → 𝕜) : Dense ((diagOp a).domain : Set ℓ²(ι, 𝕜)) := by
  classical
  intro x
  refine mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top x)
    (Eventually.of_forall fun s => ?_)
  exact Submodule.sum_mem _ fun i _ => single_mem_diagOp_domain a i (x i)

/-- The diagonal operator of `0` is the operator `0` on all of `ℓ²`. -/
theorem diagOp_zero : diagOp (0 : ι → 𝕜) = 0 := by
  have hd : (diagOp (0 : ι → 𝕜)).domain = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    rw [mem_diagOp_domain]
    simp_rw [Pi.zero_apply, zero_mul]
    exact zero_mem_ℓp'
  refine LinearPMap.ext (hd.trans LinearPMap.zero_domain.symm) fun x hx hx' => ?_
  change diagOp 0 ⟨x, hx⟩ = 0
  exact lp.ext (funext fun i => by simp)

/-- **A diagonal operator with entries `1 ≤ ‖aᵢ‖` is onto**: `x = (aᵢ⁻¹ yᵢ)` has
`diagOp a x = y`. -/
theorem range_diagOp_eq_top (ha : ∀ i, 1 ≤ ‖a i‖) : LinearMap.range (diagOp a).toFun = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  have h0 : ∀ i, a i ≠ 0 := fun i h => by
    have := ha i
    simp [h] at this
    linarith
  have hx : Memℓp (fun i => (a i)⁻¹ * y i) 2 := (lp.memℓp y).mono' fun i => by
    rw [norm_mul, norm_inv]
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (ha i))
  set x : ℓ²(ι, 𝕜) := ⟨_, hx⟩
  have hax : ∀ i, a i * x i = y i := fun i => mul_inv_cancel_left₀ (h0 i) (y i)
  have hxd : x ∈ (diagOp a).domain := by
    rw [mem_diagOp_domain, show (fun i => a i * x i) = ⇑y from funext hax]
    exact lp.memℓp y
  exact ⟨⟨x, hxd⟩, lp.ext (funext hax)⟩

/-! ### Finite sequences in `ℓ²(ℕ, 𝕜)` -/

variable {n : ℕ}

variable (𝕜) in
/-- **The vectors of `𝕜ⁿ` as sequences** supported in `{0, …, n - 1}`:
`ofFin n v = ∑ₖ lp.single 2 k vₖ`. -/
def ofFin (n : ℕ) : EuclideanSpace 𝕜 (Fin n) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  ∑ k : Fin n, lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) 2 (k : ℕ) ∘L
    EuclideanSpace.proj k

theorem ofFin_apply' (v : EuclideanSpace 𝕜 (Fin n)) :
    ofFin 𝕜 n v = ∑ k : Fin n, lp.single 2 (k : ℕ) (v k) := by
  simp [ofFin]

/-- The coordinates of `ofFin n v`: `vⱼ` for `j < n`, `0` beyond. -/
theorem ofFin_apply (v : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    ofFin 𝕜 n v j = if h : j < n then v ⟨j, h⟩ else 0 := by
  rw [ofFin_apply', lp.coeFn_sum, Finset.sum_apply]
  simp_rw [lp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩
      (fun k _ hk => Pi.single_eq_of_ne (fun e => hk (Fin.ext e.symm)) _)
      (fun h' => absurd (Finset.mem_univ _) h')]
    exact Pi.single_eq_same _ _
  · exact Finset.sum_eq_zero fun k _ => Pi.single_eq_of_ne (fun e => h (by rw [e]; exact k.2)) _

@[simp] theorem ofFin_apply_val (v : EuclideanSpace 𝕜 (Fin n)) (k : Fin n) :
    ofFin 𝕜 n v k = v k := by
  simp [ofFin_apply]

/-- `⟪ofFin n v, x⟫ = ∑ₖ ⟪vₖ, xₖ⟫`. -/
theorem inner_ofFin_left (v : EuclideanSpace 𝕜 (Fin n)) (x : ℓ²(ℕ, 𝕜)) :
    ⟪ofFin 𝕜 n v, x⟫_𝕜 = ∑ k : Fin n, ⟪v k, x k⟫_𝕜 := by
  rw [ofFin_apply', sum_inner]
  exact Finset.sum_congr rfl fun k _ => lp.inner_single_left _ _ _

/-- `ofFin n` is an isometry: `⟪ofFin n v, ofFin n w⟫ = ⟪v, w⟫`. -/
theorem inner_ofFin_ofFin (v w : EuclideanSpace 𝕜 (Fin n)) :
    ⟪ofFin 𝕜 n v, ofFin 𝕜 n w⟫_𝕜 = ⟪v, w⟫_𝕜 := by
  rw [inner_ofFin_left, PiLp.inner_apply]
  simp

@[simp] theorem norm_ofFin (v : EuclideanSpace 𝕜 (Fin n)) : ‖ofFin 𝕜 n v‖ = ‖v‖ := by
  have e := congrArg RCLike.re (inner_ofFin_ofFin v v)
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at e
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e

theorem norm_ofFin_le : ‖ofFin 𝕜 n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [norm_ofFin, one_mul]

variable (𝕜) in
/-- **The truncation** `x ↦ (x₀, …, x_{n-1})` of `ℓ²(ℕ, 𝕜)` to `𝕜ⁿ`, the adjoint of `ofFin n`. -/
def truncFin (n : ℕ) : ℓ²(ℕ, 𝕜) →L[𝕜] EuclideanSpace 𝕜 (Fin n) := (ofFin 𝕜 n).adjoint

@[simp] theorem truncFin_apply (x : ℓ²(ℕ, 𝕜)) (k : Fin n) : truncFin 𝕜 n x k = x k := by
  have e := EuclideanSpace.inner_single_left k (1 : 𝕜) (truncFin 𝕜 n x)
  rw [map_one, one_mul] at e
  rw [← e, truncFin, ContinuousLinearMap.adjoint_inner_right, inner_ofFin_left,
    Finset.sum_eq_single k (fun l _ hl => by simp [hl])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

@[simp] theorem truncFin_ofFin (v : EuclideanSpace 𝕜 (Fin n)) : truncFin 𝕜 n (ofFin 𝕜 n v) = v :=
  PiLp.ext fun k => by rw [truncFin_apply, ofFin_apply_val]

theorem norm_truncFin_le : ‖truncFin 𝕜 n‖ ≤ 1 := by
  rw [truncFin, LinearIsometryEquiv.norm_map]
  exact norm_ofFin_le

/-- **The truncations converge**: `ofFin n (truncFin n x) = ∑_{k < n} xₖ eₖ → x`. -/
theorem tendsto_ofFin_truncFin (x : ℓ²(ℕ, 𝕜)) :
    Tendsto (fun n => ofFin 𝕜 n (truncFin 𝕜 n x)) atTop (𝓝 x) := by
  refine ((lp.hasSum_single ENNReal.ofNat_ne_top x).tendsto_sum_nat).congr fun n => ?_
  rw [ofFin_apply', ← Fin.sum_univ_eq_sum_range (fun i => lp.single 2 i (x i))]
  simp

/-- The finite sequences lie in the domain of every diagonal operator. -/
theorem ofFin_mem_diagOp_domain (a : ℕ → 𝕜) (v : EuclideanSpace 𝕜 (Fin n)) :
    ofFin 𝕜 n v ∈ (diagOp a).domain := by
  classical
  rw [ofFin_apply']
  exact Submodule.sum_mem _ fun k _ => single_mem_diagOp_domain a k (v k)

/-- **A diagonal operator acts on finite sequences coordinatewise**:
`diagOp a (ofFin n v) = ofFin n (aₖ vₖ)`. -/
theorem diagOp_ofFin (a : ℕ → 𝕜) (v : EuclideanSpace 𝕜 (Fin n)) :
    diagOp a ⟨ofFin 𝕜 n v, ofFin_mem_diagOp_domain a v⟩ =
      ofFin 𝕜 n (WithLp.toLp 2 fun k => a k * v k) :=
  lp.ext (funext fun j => by
    rw [diagOp_apply, ofFin_apply, ofFin_apply]
    split_ifs <;> simp)

/-- **A diagonal operator commutes with the truncations**: `(truncFin n (diagOp a x))ₖ = aₖ xₖ`. -/
theorem truncFin_diagOp (a : ℕ → 𝕜) (x : (diagOp a).domain) (k : Fin n) :
    truncFin 𝕜 n (diagOp a x) k = a k * truncFin 𝕜 n x k := by
  rw [truncFin_apply, truncFin_apply, diagOp_apply]

end lp
