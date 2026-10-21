module

public import Feec.HilbertComplex.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite windows of Hilbert complexes and the total differential

A Hilbert complex on a finite index type has a Hilbert total space `PiLp 2 W` (no summability
bookkeeping, unlike `lp` over all of `ℤ`) and a total differential `𝐝 = ∑ d i j` on it.

## Main definitions

* `ComplexShape.window n`: the non-wrapping shape `0 → 1 → ⋯ → n - 1` on `Fin n`
  (`ComplexShape.up (Fin n)` wraps `n - 1 → 0`); `ComplexShape.fin3 = window 3`.
* `HilbertComplex.restrict`: pull a complex back along a map of index types that reflects the
  relation; `HilbertComplex.window H a n`: the truncation of a complex on `ComplexShape.up α`
  (`α = ℕ, ℤ`) to the indices `a, a + 1, …, a + n - 1`. At the two ends the differentials
  leaving the window are dropped, so the adjoints of the window are those of the truncated
  complex, not restrictions of the adjoints of `H`.
* `HilbertComplex.totalDomain`, `HilbertComplex.totalD`: the total differential on `PiLp 2 W`,
  `(𝐝 x) j = ∑ i, d i j (x i)`, with domain `{x | ∀ i j, x i ∈ D(d i j)}`.

## Main results

* `HilbertComplex.adjoint_totalD`: `𝐝† = 𝐝*`, the total differential of the dual complex.
* `HilbertComplex.dense_totalDomain`, `HilbertComplex.isClosed_totalD`,
  `HilbertComplex.totalD_mapsTo`, `HilbertComplex.totalD_comp_totalD`: `𝐝` is a closed densely
  defined operator with `𝐝 𝐝 = 0`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (the total space `W = W⁰ × W¹ × W²` of the Hodge wave operator)
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992], §2 (the operator `D = d + d*` of a
  Hilbert complex)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Set

@[expose] public noncomputable section

/-- The non-wrapping shape `0 → 1 → ⋯ → n - 1` on `Fin n`: `i → j` iff `i + 1 = j` in `ℕ`. -/
def ComplexShape.window (n : ℕ) : ComplexShape (Fin n) where
  Rel i j := i.val + 1 = j.val
  next_eq h h' := Fin.ext (by omega)
  prev_eq h h' := Fin.ext (by omega)

/-- The shape `0 → 1 → 2` of a short complex. -/
abbrev ComplexShape.fin3 : ComplexShape (Fin 3) := ComplexShape.window 3

@[simp] theorem ComplexShape.window_rel {n : ℕ} {i j : Fin n} :
    (ComplexShape.window n).Rel i j ↔ i.val + 1 = j.val := Iff.rfl

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

/-! ### Restriction and windows -/

/-- Pull a Hilbert complex back along `f : ι' → ι` when `f` reflects the relation. -/
def restrict {ι' : Type*} {c' : ComplexShape ι'} (f : ι' → ι)
    (hf : ∀ i j, c.Rel (f i) (f j) → c'.Rel i j) : HilbertComplex 𝕜 c' (fun i => W (f i)) where
  d i j := H.d (f i) (f j)
  shape i j h := H.shape _ _ fun h' => h (hf i j h')
  dense _ _ := H.dense _ _
  closed _ _ := H.closed _ _
  mapsTo _ _ _ := H.mapsTo _ _ _
  d_comp_d _ _ _ := H.d_comp_d _ _ _

@[simp] theorem restrict_d {ι' : Type*} {c' : ComplexShape ι'} (f : ι' → ι)
    (hf : ∀ i j, c.Rel (f i) (f j) → c'.Rel i j) (i j : ι') :
    (H.restrict f hf).d i j = H.d (f i) (f j) := rfl

section Window

variable {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α] [CharZero α] {V : α → Type*}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]

/-- The window `V a → V (a + 1) → ⋯ → V (a + n - 1)` of a complex on `ComplexShape.up α`
(`α = ℕ, ℤ`), as a complex on `ComplexShape.window n`. -/
def window (H : HilbertComplex 𝕜 (ComplexShape.up α) V) (a : α) (n : ℕ) :
    HilbertComplex 𝕜 (ComplexShape.window n) (fun i : Fin n => V (a + i)) :=
  H.restrict (fun i : Fin n => a + (i : α)) fun i j h => by
    change a + (i : α) + 1 = a + j at h
    change i.val + 1 = j.val
    rw [add_assoc] at h
    exact_mod_cast add_left_cancel h

@[simp] theorem window_d (H : HilbertComplex 𝕜 (ComplexShape.up α) V) (a : α) (n : ℕ)
    (i j : Fin n) : (H.window a n).d i j = H.d (a + i) (a + j) := rfl

end Window

/-! ### The total differential of a finite complex -/

section Total

/-- The domain `{x | ∀ i j, x i ∈ D(d i j)}` of the total differential. -/
def totalDomain : Submodule 𝕜 (PiLp 2 W) where
  carrier := {x | ∀ i j, x i ∈ (H.d i j).domain}
  add_mem' hx hy i j := (H.d i j).domain.add_mem (hx i j) (hy i j)
  zero_mem' i j := (H.d i j).domain.zero_mem
  smul_mem' a _ hx i j := (H.d i j).domain.smul_mem a (hx i j)

theorem mem_totalDomain {x : PiLp 2 W} : x ∈ H.totalDomain ↔ ∀ i j, x i ∈ (H.d i j).domain :=
  Iff.rfl

/-- The `i`-th coordinate of a point of `totalDomain`, as a point of `D(d i j)`. -/
def totalCoord (i j : ι) : H.totalDomain →ₗ[𝕜] (H.d i j).domain :=
  LinearMap.codRestrict _ ((PiLp.projₗ 2 W i).comp H.totalDomain.subtype) fun x => x.2 i j

/-- Every `x i` lies in the domain of the unique nonzero differential leaving `i`. -/
theorem iInter_domain (i : ι) :
    (⋂ j, ((H.d i j).domain : Set (W i))) = (H.d i (c.next i)).domain := by
  refine Subset.antisymm (iInter_subset _ _) (subset_iInter fun j => ?_)
  by_cases hj : j = c.next i
  · subst hj; exact le_rfl
  · rw [H.d_eq_zero_of_ne_next hj]; exact subset_univ _

theorem dense_totalDomain : Dense (H.totalDomain : Set (PiLp 2 W)) := by
  have hs : Dense (Set.pi univ fun i => ⋂ j, ((H.d i j).domain : Set (W i))) :=
    dense_pi _ fun i _ => by rw [H.iInter_domain]; exact H.dense _ _
  have := hs.preimage (PiLp.homeomorph 2 W).isOpenMap
  convert this using 1
  ext x
  simp [mem_totalDomain, PiLp.homeomorph]

/-- `PiLp.single i v` lies in the total domain when `v ∈ D(d i (c.next i))`. -/
theorem single_mem_totalDomain [DecidableEq ι] (i : ι) {v : W i}
    (hv : v ∈ (H.d i (c.next i)).domain) : PiLp.single 2 i v ∈ H.totalDomain := by
  intro i' j
  by_cases hi : i' = i
  · subst hi
    rw [PiLp.single_eq_same]
    by_cases hj : j = c.next i'
    · subst hj; exact hv
    · rw [H.domain_eq_top_of_not_rel fun h => hj (c.next_eq' h).symm]; exact Submodule.mem_top
  · simp only [PiLp.single_eq_of_ne (p := 2) hi]; exact Submodule.zero_mem _

/-- A partial map sends a domain point equal to `0` to `0`. -/
theorem _root_.LinearPMap.apply_mk_eq_zero {R E F : Type*} [Ring R] [AddCommGroup E]
    [Module R E] [AddCommGroup F] [Module R F] (T : E →ₗ.[R] F) {x : E} (hx : x ∈ T.domain)
    (h : x = 0) : T ⟨x, hx⟩ = 0 := by
  subst h; exact T.map_zero

variable [Fintype ι]

/-- The total differential `(𝐝 x) j = ∑ i, d i j (x i)` on `PiLp 2 W`. -/
def totalD : PiLp 2 W →ₗ.[𝕜] PiLp 2 W where
  domain := H.totalDomain
  toFun := (WithLp.linearEquiv 2 𝕜 (∀ i, W i)).symm.toLinearMap.comp
    (LinearMap.pi fun j => ∑ i, (H.d i j).toFun.comp (H.totalCoord i j))

omit [Fintype ι] in
@[simp] theorem totalD_domain [Fintype ι] : H.totalD.domain = H.totalDomain := rfl

theorem totalD_apply (x : H.totalD.domain) (j : ι) :
    (H.totalD x) j = ∑ i, H.d i j ⟨(x : PiLp 2 W) i, x.2 i j⟩ := by
  change (∑ i, (H.d i j).toFun.comp (H.totalCoord i j)) (show H.totalDomain from x) = _
  rw [LinearMap.sum_apply]
  rfl

/-- `(𝐝 x) j ∈ D(d j k)`. -/
theorem totalD_mapsTo (x : H.totalD.domain) : (H.totalD x : PiLp 2 W) ∈ H.totalD.domain := by
  intro j k
  rw [totalD_apply]
  exact Submodule.sum_mem _ fun i _ => H.mapsTo i j k _

/-- `𝐝 𝐝 = 0`. -/
theorem totalD_comp_totalD (x : H.totalD.domain) : H.totalD ⟨_, H.totalD_mapsTo x⟩ = 0 := by
  refine PiLp.ext fun k => ?_
  rw [totalD_apply]
  refine (Finset.sum_eq_zero fun j _ => ?_).trans (by simp)
  have e : (⟨(H.totalD x : PiLp 2 W) j, H.totalD_mapsTo x j k⟩ : (H.d j k).domain) =
      ∑ i, (⟨_, H.mapsTo i j k ⟨(x : PiLp 2 W) i, x.2 i j⟩⟩ : (H.d j k).domain) := by
    ext1
    simp only [Submodule.coe_sum]
    exact H.totalD_apply x j
  refine (congrArg (H.d j k) e).trans ?_
  exact (map_sum (H.d j k).toFun _ _).trans (Finset.sum_eq_zero fun i _ => H.d_comp_d i j k _)

theorem inner_totalD_dual (x : H.totalD.domain) (y : H.dual.totalD.domain) :
    ⟪H.totalD x, (y : PiLp 2 W)⟫_𝕜 = ⟪(x : PiLp 2 W), H.dual.totalD y⟫_𝕜 := by
  simp only [PiLp.inner_apply, totalD_apply, sum_inner, inner_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := adjoint_isFormalAdjoint (H.dense i j) ⟨(y : PiLp 2 W) j, y.2 j i⟩
    ⟨(x : PiLp 2 W) i, x.2 i j⟩
  exact (inner_conj_symm _ _).symm.trans
    ((congrArg (starRingEnd 𝕜) this.symm).trans (inner_conj_symm _ _))

/-- Testing `𝐝 (single i v)` against `y` only sees the component `c.next i`. -/
theorem inner_totalD_single [DecidableEq ι] (y : PiLp 2 W) (i : ι) (v : W i)
    (hv : PiLp.single 2 i v ∈ H.totalDomain) :
    ⟪y, H.totalD ⟨_, hv⟩⟫_𝕜 = ⟪y (c.next i), H.d i (c.next i) ⟨v, by
      simpa using hv i (c.next i)⟩⟫_𝕜 := by
  have hz : ∀ (i' j : ι), i' ≠ i → ∀ h, H.d i' j ⟨(PiLp.single 2 i v) i', h⟩ = 0 :=
    fun i' j hi' h => apply_mk_eq_zero _ h (PiLp.single_eq_of_ne (p := 2) hi' v)
  rw [PiLp.inner_apply]
  refine (Finset.sum_eq_single (c.next i) (fun j _ hj => ?_) (by simp)).trans ?_
  · rw [totalD_apply, Finset.sum_eq_single i (fun i' _ hi' => hz i' j hi' _) (by simp),
      apply_eq_zero_of_eq_zero (H.d_eq_zero_of_ne_next hj), inner_zero_right]
  · rw [totalD_apply, Finset.sum_eq_single i (fun i' _ hi' => hz i' _ hi' _) (by simp)]
    congr 2; exact Subtype.ext (by simp)

/-- `𝐝† = 𝐝*`: the adjoint of the total differential is the total differential of the dual
complex, `(𝐝† y) i = ∑ j, (d i j)† (y j)`. -/
theorem adjoint_totalD : H.totalD† = H.dual.totalD := by
  classical
  have hle : H.dual.totalD ≤ H.totalD† :=
    IsFormalAdjoint.le_adjoint H.dense_totalDomain fun x y => H.inner_totalD_dual x y
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  intro j i
  change (y : PiLp 2 W) j ∈ ((H.d i j)†).domain
  by_cases hij : c.Rel i j
  · have hj : c.next i = j := c.next_eq' hij
    subst hj
    refine mem_adjoint_domain_of_exists _ ⟨(H.totalD† ⟨y, hy⟩) i, fun v => ?_⟩
    have hv := H.single_mem_totalDomain i v.2
    have := adjoint_isFormalAdjoint H.dense_totalDomain ⟨y, hy⟩ ⟨_, hv⟩
    rw [H.inner_totalD_single y i v hv, PiLp.inner_apply,
      Finset.sum_eq_single i (fun i' _ hi' => by
        simp [PiLp.single_eq_of_ne (p := 2) hi']) (by simp)] at this
    simpa using this
  · rw [H.shape i j hij, adjoint_zero]; exact Submodule.mem_top

theorem dual_dual_totalD : H.dual.dual.totalD = H.totalD := by
  rw [H.dual_dual]

/-- The total differential is closed: `𝐝 = (𝐝*)†`. -/
theorem isClosed_totalD : H.totalD.IsClosed := by
  have h := H.dual.adjoint_totalD
  rw [dual_dual_totalD] at h
  rw [← h]
  exact adjoint_isClosed H.dual.dense_totalDomain

theorem dense_totalD_domain : Dense (H.totalD.domain : Set (PiLp 2 W)) := H.dense_totalDomain

end Total

end Feec.HilbertComplex
