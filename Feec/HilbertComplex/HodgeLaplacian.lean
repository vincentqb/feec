module

public import Feec.HilbertComplex.Compactness
public import Feec.HilbertComplex.DomainComplex
public import Feec.Operator.Resolvent

/-!
# The abstract Hodge Laplacian

For a skew-adjoint `A` on a Hilbert space, `-A²` on `D(A²) = {x ∈ D(A) | A x ∈ D(A)}` is
self-adjoint and nonnegative, `⟪-A² x, x⟫ = ‖A x‖²`, `ker (-A²) = ker A`, and
`1 - A² = (1 + A)(1 - A)` is invertible with inverse `(1 - A²)⁻¹ = -R(-1) R(1)`, built from the
two resolvents `R(±1) = (±1 - A)⁻¹` of `A`. This works over `ℝ` and `ℂ` alike (no `i A` is needed).

Applied to the wave operator `L = 𝐝 − 𝐝*` of a finite Hilbert complex, `Δ = -L²` is the
**Hodge Laplacian** `𝐝 𝐝* + 𝐝* 𝐝`:

## Main results

* `LinearPMap.IsSkewAdjoint.isSelfAdjoint_neg_sq`, `LinearPMap.IsSkewAdjoint.dense_sq_domain`.
* `LinearPMap.isSelfAdjoint_of_isSymmetric_of_surjective`: a densely defined symmetric `T` with
  `1 + T` onto is self-adjoint.
* `LinearPMap.IsSkewAdjoint.isResolvent_sq`: the resolvent of `A²` at `1`, with norm `≤ 1`.
* `Feec.HilbertComplex.isSelfAdjoint_hodgeLaplacian`,
  `Feec.HilbertComplex.re_inner_hodgeLaplacian_self` (`re ⟪Δ x, x⟫ = ‖𝐝 x‖² + ‖𝐝* x‖²`),
  `Feec.HilbertComplex.mem_ker_hodgeLaplacian_iff` (`ker Δ = ⊕ ℌⁱ`, no closed range needed).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.2 (the abstract Hodge Laplacian)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 4
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992] (the Laplacian `D²` of a Hilbert
  complex)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Feec.Operator

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### The square of a partial map -/

/-- The domain `{x ∈ D(A) | A x ∈ D(A)}` of `A²`. -/
def sqDomain (A : E →ₗ.[𝕜] E) : Submodule 𝕜 E where
  carrier := {x | ∃ h : x ∈ A.domain, (A ⟨x, h⟩ : E) ∈ A.domain}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨A.domain.add_mem hx hy, ?_⟩
    have : A ⟨x + y, A.domain.add_mem hx hy⟩ = A ⟨x, hx⟩ + A ⟨y, hy⟩ :=
      A.map_add ⟨x, hx⟩ ⟨y, hy⟩
    rw [this]; exact A.domain.add_mem hx' hy'
  zero_mem' := ⟨A.domain.zero_mem, by
    have : A ⟨0, A.domain.zero_mem⟩ = 0 := A.map_zero
    rw [this]; exact A.domain.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨A.domain.smul_mem c hx, ?_⟩
    have : A ⟨c • x, A.domain.smul_mem c hx⟩ = c • A ⟨x, hx⟩ := A.map_smul c ⟨x, hx⟩
    rw [this]; exact A.domain.smul_mem c hx'

/-- `x ↦ A x` from `D(A²)` to `D(A)`. -/
def sqAux (A : E →ₗ.[𝕜] E) : A.sqDomain →ₗ[𝕜] A.domain where
  toFun x := ⟨A ⟨x, x.2.1⟩, x.2.2⟩
  map_add' x y := Subtype.ext (A.map_add ⟨x, x.2.1⟩ ⟨y, y.2.1⟩)
  map_smul' c x := Subtype.ext (A.map_smul c ⟨x, x.2.1⟩)

/-- The square `A²` of a partial map, on `{x ∈ D(A) | A x ∈ D(A)}`. -/
def sq (A : E →ₗ.[𝕜] E) : E →ₗ.[𝕜] E := ⟨A.sqDomain, A.toFun ∘ₗ A.sqAux⟩

variable {A : E →ₗ.[𝕜] E}

/-- `x ∈ D(A²)` as a point of `D(A)`. -/
def sqFst (x : A.sq.domain) : A.domain := ⟨x, x.2.1⟩

/-- `A x ∈ D(A)` for `x ∈ D(A²)`. -/
def sqSnd (x : A.sq.domain) : A.domain := ⟨A (sqFst x), x.2.2⟩

theorem sq_apply (x : A.sq.domain) : A.sq x = A (sqSnd x) := rfl

/-- `⟪A² x, y⟫ = -⟪A x, A y⟫` for skew-symmetric `A`. -/
theorem IsSkewSymmetric.inner_sq_left (hA : A.IsSkewSymmetric) (x : A.sq.domain)
    (y : A.domain) : ⟪A.sq x, (y : E)⟫ = -⟪A (sqFst x), A y⟫ :=
  hA (sqSnd x) y

/-- `-A²` is symmetric for skew-symmetric `A`. -/
theorem IsSkewSymmetric.isSymmetric_neg_sq (hA : A.IsSkewSymmetric) : (-A.sq).IsSymmetric := by
  intro x y
  change ⟪-A.sq x, (y : E)⟫ = ⟪(x : E), -A.sq y⟫
  have h1 : ⟪A.sq x, (y : E)⟫ = -⟪A (sqFst x), A (sqFst y)⟫ := hA.inner_sq_left x (sqFst y)
  have h2 : ⟪A (sqFst x), A (sqFst y)⟫ = -⟪(x : E), A.sq y⟫ := hA (sqFst x) (sqSnd y)
  rw [inner_neg_left, inner_neg_right, h1, h2, neg_neg]

/-- `⟪x - A² x, x⟫ = ‖x‖² + ‖A x‖²` for skew-symmetric `A`. -/
theorem IsSkewSymmetric.re_inner_sub_sq_self (hA : A.IsSkewSymmetric) (x : A.sq.domain) :
    RCLike.re ⟪(x : E) - A.sq x, (x : E)⟫ = ‖(x : E)‖ ^ 2 + ‖A (sqFst x)‖ ^ 2 := by
  have h1 : ⟪A.sq x, (x : E)⟫ = -⟪A (sqFst x), A (sqFst x)⟫ := hA.inner_sq_left x (sqFst x)
  rw [inner_sub_left, _root_.map_sub, h1, _root_.map_neg,
    inner_self_eq_norm_sq, inner_self_eq_norm_sq]
  ring

/-- `1 - A²` is injective on `D(A²)` for skew-symmetric `A`. -/
theorem IsSkewSymmetric.eq_zero_of_sub_sq_eq_zero (hA : A.IsSkewSymmetric) {x : A.sq.domain}
    (h : (x : E) - A.sq x = 0) : x = 0 := by
  have := hA.re_inner_sub_sq_self x
  rw [h, inner_zero_left, _root_.map_zero] at this
  have : ‖(x : E)‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖(x : E)‖, sq_nonneg ‖A (sqFst x)‖]
  exact Subtype.ext (by simpa using this)

/-- A densely defined symmetric `T` with `1 + T` onto `E` is self-adjoint. -/
theorem isSelfAdjoint_of_isSymmetric_of_surjective [CompleteSpace E] {T : E →ₗ.[𝕜] E}
    (hD : Dense (T.domain : Set E)) (hT : T.IsSymmetric)
    (hs : ∀ y, ∃ x : T.domain, (x : E) + T x = y) : IsSelfAdjoint T := by
  refine (isSelfAdjoint_iff hD).2 ⟨hT, fun y hy => ?_⟩
  obtain ⟨x, hx⟩ := hs (y + T† ⟨y, hy⟩)
  have horth : ∀ z : T.domain, ⟪y - x, (z : E) + T z⟫ = 0 := fun z => by
    have h1 : ⟪y, T z⟫ = ⟪T† ⟨y, hy⟩, (z : E)⟫ :=
      (adjoint_isFormalAdjoint hD ⟨y, hy⟩ z).symm
    have h2 : ⟪(x : E), T z⟫ = ⟪T x, (z : E)⟫ := (hT x z).symm
    have h3 : ⟪y + T† ⟨y, hy⟩, (z : E)⟫ = ⟪(x : E) + T x, (z : E)⟫ := by rw [hx]
    rw [inner_add_left, inner_add_left] at h3
    rw [inner_sub_left, inner_add_right, inner_add_right, h1, h2]
    linear_combination h3
  obtain ⟨z, hz⟩ := hs (y - x)
  have := horth z
  rw [hz, inner_self_eq_zero, sub_eq_zero] at this
  rw [this]; exact x.2

variable [CompleteSpace E]

namespace IsSkewAdjoint

/-- **`x - A² x = f` is solvable** for skew-adjoint `A`: `x = -R(-1) R(1) f`. -/
theorem neg_resolvent_mem_sq_domain (hA : A.IsSkewAdjoint) (f : E) :
    -resolvent A (-1) (resolvent A 1 f) ∈ A.sq.domain ∧
      ∀ h : -resolvent A (-1) (resolvent A 1 f) ∈ A.sq.domain,
        -resolvent A (-1) (resolvent A 1 f) - A.sq ⟨_, h⟩ = f := by
  have h1 : RCLike.re (1 : 𝕜) ≠ 0 := by simp
  have hm1 : RCLike.re (-1 : 𝕜) ≠ 0 := by simp
  have hR1 := isResolvent_resolvent hA h1
  have hRm := isResolvent_resolvent hA hm1
  set w := resolvent A 1 f
  set x := -resolvent A (-1) w
  have hwD : w ∈ A.domain := hR1.mem_domain f
  have hxD : x ∈ A.domain := A.domain.neg_mem (hRm.mem_domain w)
  have hAw : A ⟨w, hwD⟩ = w - f := by
    have := hR1.sub_apply f; rw [one_smul] at this
    change w - A ⟨w, hwD⟩ = f at this
    rw [← this]; abel
  have hAx : A ⟨x, hxD⟩ = w - x := by
    have := hRm.sub_apply w
    have e : A ⟨x, hxD⟩ = -A (hRm.toDomain w) := by
      rw [← A.map_neg]; rfl
    change (-1 : 𝕜) • resolvent A (-1) w - A (hRm.toDomain w) = w at this
    simp only [neg_smul, one_smul] at this
    have h3 : x - A (hRm.toDomain w) = w := this
    rw [e, eq_sub_iff_add_eq, add_comm, ← sub_eq_add_neg]
    exact h3
  have hAxD : (A ⟨x, hxD⟩ : E) ∈ A.domain := by
    rw [hAx]; exact A.domain.sub_mem hwD hxD
  refine ⟨⟨hxD, hAxD⟩, fun h => ?_⟩
  have e1 : A.sq ⟨x, h⟩ = A ⟨w - x, A.domain.sub_mem hwD hxD⟩ := by
    rw [sq_apply]; congr 1; exact Subtype.ext hAx
  have e2 : A ⟨w - x, A.domain.sub_mem hwD hxD⟩ = A ⟨w, hwD⟩ - A ⟨x, hxD⟩ :=
    A.map_sub ⟨w, hwD⟩ ⟨x, hxD⟩
  rw [e1, e2, hAw, hAx]; abel

/-- The solution operator `(1 - A²)⁻¹ = -R(-1) R(1)` of a skew-adjoint `A`. -/
def sqResolvent (A : E →ₗ.[𝕜] E) : E →L[𝕜] E := -(resolvent A (-1)).comp (resolvent A 1)

/-- **The resolvent of `A²` at `1`**: `(1 - A²)⁻¹ = -R(-1) R(1)` for skew-adjoint `A`. -/
theorem isResolvent_sq (hA : A.IsSkewAdjoint) : IsResolvent A.sq 1 (sqResolvent A) where
  mem_domain f := (hA.neg_resolvent_mem_sq_domain f).1
  sub_apply f := by
    rw [one_smul]
    exact (hA.neg_resolvent_mem_sq_domain f).2 _
  apply_sub x := by
    rw [one_smul]
    set f := (x : E) - A.sq x
    have hm := (hA.neg_resolvent_mem_sq_domain f).1
    have he := (hA.neg_resolvent_mem_sq_domain f).2 hm
    set x' : A.sq.domain := ⟨_, hm⟩
    have he' : (x' : E) - A.sq x' = f := he
    have : x' - x = 0 := by
      refine hA.isSkewSymmetric.eq_zero_of_sub_sq_eq_zero ?_
      change ((x' : E) - x) - A.sq (x' - x) = 0
      rw [A.sq.map_sub, show ((x' : E) - x) - (A.sq x' - A.sq x) =
        ((x' : E) - A.sq x') - ((x : E) - A.sq x) by abel, he']
      exact sub_self _
    exact congrArg Subtype.val (sub_eq_zero.1 this)

/-- `D(A²)` is dense for skew-adjoint `A`. -/
theorem dense_sq_domain (hA : A.IsSkewAdjoint) : Dense (A.sq.domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro y hy
  have hR := hA.isResolvent_sq
  set x := hR.toDomain y
  have hx : (x : E) - A.sq x = y := by
    have := hR.sub_apply_toDomain y
    rw [one_smul] at this
    exact this
  have h0 : ⟪(x : E) - A.sq x, (x : E)⟫ = 0 := by
    rw [hx]; exact Submodule.inner_left_of_mem_orthogonal x.2 hy
  have := hA.isSkewSymmetric.re_inner_sub_sq_self x
  rw [h0, _root_.map_zero] at this
  have : ‖(x : E)‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖(x : E)‖, sq_nonneg ‖A (sqFst x)‖]
  have hx0 : x = 0 := Subtype.ext (by simpa using this)
  rw [← hx, hx0]
  simp

/-- **`-A²` is self-adjoint** for skew-adjoint `A`. -/
theorem isSelfAdjoint_neg_sq (hA : A.IsSkewAdjoint) : IsSelfAdjoint (-A.sq) := by
  refine isSelfAdjoint_of_isSymmetric_of_surjective hA.dense_sq_domain
    hA.isSkewSymmetric.isSymmetric_neg_sq fun f => ?_
  have hR := hA.isResolvent_sq
  refine ⟨hR.toDomain f, ?_⟩
  rw [neg_apply, ← sub_eq_add_neg]
  simpa using hR.sub_apply_toDomain f

/-- `ker A² = ker A` for skew-symmetric `A`. -/
theorem mem_ker_sq_iff (hA : A.IsSkewAdjoint) {x : E} : x ∈ A.sq.ker ↔ x ∈ A.ker := by
  rw [mem_ker_iff, mem_ker_iff]
  constructor
  · rintro ⟨y, rfl, hy⟩
    refine ⟨sqFst y, rfl, ?_⟩
    have := hA.isSkewSymmetric.inner_sq_left y (sqFst y)
    rw [hy, inner_zero_left, eq_comm, neg_eq_zero, inner_self_eq_zero] at this
    exact this
  · rintro ⟨y, rfl, hy⟩
    have hAy : (A y : E) ∈ A.domain := by rw [hy]; exact A.domain.zero_mem
    refine ⟨⟨y, y.2, hAy⟩, rfl, ?_⟩
    rw [sq_apply]
    have : sqSnd (⟨y, y.2, hAy⟩ : A.sq.domain) = 0 := Subtype.ext hy
    rw [this, A.map_zero]

end IsSkewAdjoint

end LinearPMap

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W) [Fintype ι]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The **Hodge Laplacian** `Δ = -L² = 𝐝 𝐝* + 𝐝* 𝐝` of a finite Hilbert complex, where
`L = 𝐝 − 𝐝*` is the wave operator; its `i`-th component is the Hodge Laplacian
`d (d*)ⁱ + (d*) dⁱ` at index `i`. -/
def hodgeLaplacian : PiLp 2 W →ₗ.[𝕜] PiLp 2 W := -H.wave.sq

/-- **The Hodge Laplacian is self-adjoint**, with no closed-range hypothesis. -/
theorem isSelfAdjoint_hodgeLaplacian : IsSelfAdjoint H.hodgeLaplacian :=
  H.isSkewAdjoint_wave.isSelfAdjoint_neg_sq

theorem dense_hodgeLaplacian_domain : Dense (H.hodgeLaplacian.domain : Set (PiLp 2 W)) :=
  H.isSkewAdjoint_wave.dense_sq_domain

/-- `⟪Δ x, y⟫ = ⟪L x, L y⟫`. -/
theorem inner_hodgeLaplacian_left (x : H.hodgeLaplacian.domain) (y : H.wave.domain) :
    ⟪H.hodgeLaplacian x, (y : PiLp 2 W)⟫ = ⟪H.wave (sqFst x), H.wave y⟫ := by
  change ⟪-H.wave.sq x, (y : PiLp 2 W)⟫ = _
  rw [inner_neg_left, H.isSkewAdjoint_wave.isSkewSymmetric.inner_sq_left x y, neg_neg]

/-- **`Δ ≥ 0`**: `re ⟪Δ x, x⟫ = ‖𝐝 x‖² + ‖𝐝* x‖²`. -/
theorem re_inner_hodgeLaplacian_self (x : H.hodgeLaplacian.domain) :
    RCLike.re ⟪H.hodgeLaplacian x, (x : PiLp 2 W)⟫ =
      ‖H.totalD ⟨x, x.2.1.1⟩‖ ^ 2 + ‖H.dual.totalD ⟨x, x.2.1.2⟩‖ ^ 2 := by
  have h' : ⟪H.hodgeLaplacian x, (x : PiLp 2 W)⟫ = ⟪H.wave (sqFst x), H.wave (sqFst x)⟫ :=
    H.inner_hodgeLaplacian_left x (sqFst x)
  rw [h', inner_self_eq_norm_sq, H.norm_wave_sq]
  rfl

theorem re_inner_hodgeLaplacian_self_nonneg (x : H.hodgeLaplacian.domain) :
    0 ≤ RCLike.re ⟪H.hodgeLaplacian x, (x : PiLp 2 W)⟫ := by
  rw [re_inner_hodgeLaplacian_self]; positivity

/-- `𝐝 x = 0` iff every component is a cycle. -/
theorem totalD_eq_zero_iff (x : H.totalD.domain) :
    H.totalD x = 0 ↔ ∀ i, (x : PiLp 2 W) i ∈ H.cycles i := by
  constructor
  · intro h i
    refine mem_ker_iff.2 ⟨⟨_, x.2 i (c.next i)⟩, rfl, ?_⟩
    by_cases hi : c.Rel i (c.next i)
    · rw [← H.totalD_apply_of_rel x hi, h]; rfl
    · exact apply_eq_zero_of_not_rel _ hi _
  · intro h
    refine PiLp.ext fun j => ?_
    rw [totalD_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hj : j = c.next i
    · subst hj
      obtain ⟨y, hy, hy0⟩ := mem_ker_iff.1 (h i)
      rw [show (⟨(x : PiLp 2 W) i, x.2 i (c.next i)⟩ : (H.d i (c.next i)).domain) = y from
        Subtype.ext hy, hy0]
    · exact apply_eq_zero_of_eq_zero (H.d_eq_zero_of_ne_next hj) _

/-- **`ker L = ⊕ ℌⁱ`**: `x` is in the kernel of the wave operator iff every component is
harmonic. -/
theorem mem_ker_wave_iff {x : PiLp 2 W} : x ∈ H.wave.ker ↔ ∀ i, x i ∈ H.harmonic i := by
  constructor
  · intro hx
    obtain ⟨y, rfl, hy⟩ := mem_ker_iff.1 hx
    have hsq := H.norm_wave_sq y
    rw [hy, norm_zero] at hsq
    have h1 : H.totalD ⟨y, y.2.1⟩ = 0 := by
      rw [← norm_eq_zero]; nlinarith [sq_nonneg ‖H.totalD ⟨y, y.2.1⟩‖,
        sq_nonneg ‖H.dual.totalD ⟨y, y.2.2⟩‖, norm_nonneg (H.totalD ⟨y, y.2.1⟩)]
    have h2 : H.dual.totalD ⟨y, y.2.2⟩ = 0 := by
      rw [← norm_eq_zero]; nlinarith [sq_nonneg ‖H.totalD ⟨y, y.2.1⟩‖,
        sq_nonneg ‖H.dual.totalD ⟨y, y.2.2⟩‖, norm_nonneg (H.dual.totalD ⟨y, y.2.2⟩)]
    intro i
    rw [harmonic_eq_cycles_inf_dual]
    exact ⟨(H.totalD_eq_zero_iff ⟨y, y.2.1⟩).1 h1 i, (H.dual.totalD_eq_zero_iff ⟨y, y.2.2⟩).1 h2 i⟩
  · intro h
    have hc : ∀ i, x i ∈ H.cycles i := fun i => (H.harmonic_le_cycles i) (h i)
    have hd : ∀ i, x i ∈ H.dual.cycles i := fun i => (H.harmonic_le_dual_cycles i) (h i)
    have hx1 : x ∈ H.totalD.domain := fun i j =>
      H.domain_next_le i j (H.cycles_le_domain i (hc i))
    have hx2 : x ∈ H.dual.totalD.domain := fun i j =>
      H.dual.domain_next_le i j (H.dual.cycles_le_domain i (hd i))
    refine mem_ker_iff.2 ⟨⟨x, hx1, hx2⟩, rfl, ?_⟩
    change H.totalD ⟨x, hx1⟩ - H.dual.totalD ⟨x, hx2⟩ = 0
    rw [(H.totalD_eq_zero_iff ⟨x, hx1⟩).2 hc, (H.dual.totalD_eq_zero_iff ⟨x, hx2⟩).2 hd, sub_zero]

/-- **`ker Δ = ⊕ ℌⁱ`**: the kernel of the Hodge Laplacian consists of the families of harmonic
forms (no closed range needed). -/
theorem mem_ker_hodgeLaplacian_iff {x : PiLp 2 W} :
    x ∈ H.hodgeLaplacian.ker ↔ ∀ i, x i ∈ H.harmonic i := by
  rw [← H.mem_ker_wave_iff, ← H.isSkewAdjoint_wave.mem_ker_sq_iff, hodgeLaplacian,
    mem_ker_iff, mem_ker_iff]
  simp only [LinearPMap.neg_apply, neg_eq_zero]
  rfl

end Feec.HilbertComplex
