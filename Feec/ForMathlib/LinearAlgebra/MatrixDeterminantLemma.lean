module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The matrix determinant lemma over a commutative ring

Over every commutative ring, `det(A + u vᵀ) = det A + vᵀ adj(A) u`.
-/

open MvPolynomial

@[expose] public noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Unique ι]

private theorem det_add_replicateCol_mul_replicateRow_eq_det_add_of_ne_zero {R : Type*} [CommRing R]
    [IsDomain R] {A : Matrix n n R} (hA : A.det ≠ 0) (u v : n → R) :
    (A + replicateCol ι u * replicateRow ι v).det = A.det + v ⬝ᵥ (A.adjugate *ᵥ u) := by
  let φ := algebraMap R (FractionRing R)
  have hφ : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hdet : IsUnit (φ.mapMatrix A).det := by
    rw [← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff φ hφ).2 hA)
  have hmul : φ.mapMatrix (replicateCol ι u * replicateRow ι v) =
      replicateCol ι (φ ∘ u) * replicateRow ι (φ ∘ v) := by
    rw [RingHom.mapMatrix_apply, Matrix.map_mul]
    rfl
  have hadj : φ ∘ (A.adjugate *ᵥ u) = (φ.mapMatrix A).adjugate *ᵥ (φ ∘ u) := by
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec, ← RingHom.mapMatrix_apply, RingHom.map_adjugate]
  apply hφ
  rw [RingHom.map_det, map_add, hmul, det_add_replicateCol_mul_replicateRow hdet,
    Matrix.det_unique (n := ι), inv_def, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    ← replicateCol_mulVec, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply,
    replicateRow_mul_replicateCol_apply, map_add, RingHom.map_det, RingHom.map_dotProduct, hadj,
    smul_eq_mul, mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel _ hdet, one_mul]

theorem det_add_replicateCol_mul_replicateRow_eq_det_add {R : Type*} [CommRing R]
    (A : Matrix n n R) (u v : n → R) :
    (A + replicateCol ι u * replicateRow ι v).det = A.det + v ⬝ᵥ (A.adjugate *ᵥ u) := by
  -- the generic instance
  let X₀ : Matrix n n (MvPolynomial ((n × n) ⊕ (n ⊕ n)) ℤ) := of fun i j => X (Sum.inl (i, j))
  let u₀ : n → MvPolynomial ((n × n) ⊕ (n ⊕ n)) ℤ := fun i => X (Sum.inr (Sum.inl i))
  let v₀ : n → MvPolynomial ((n × n) ⊕ (n ⊕ n)) ℤ := fun i => X (Sum.inr (Sum.inr i))
  have h₀ : X₀.det ≠ 0 := by
    intro h
    let e : MvPolynomial ((n × n) ⊕ (n ⊕ n)) ℤ →+* ℤ :=
      eval₂Hom (RingHom.id ℤ) (Sum.elim (fun ij => if ij.1 = ij.2 then 1 else 0) fun _ => 0)
    have he : e.mapMatrix X₀ = 1 := by
      ext i j
      simp [e, X₀, one_apply]
    have := congrArg e h
    rw [RingHom.map_det, he, det_one, map_zero] at this
    exact one_ne_zero this
  have hg := det_add_replicateCol_mul_replicateRow_eq_det_add_of_ne_zero (ι := ι) h₀ u₀ v₀
  -- its image under the evaluation at `A`, `u`, `v`
  let f : MvPolynomial ((n × n) ⊕ (n ⊕ n)) ℤ →+* R :=
    eval₂Hom (Int.castRingHom R) (Sum.elim (fun ij => A ij.1 ij.2) (Sum.elim u v))
  have hA : f.mapMatrix X₀ = A := by
    ext i j
    simp [f, X₀]
  have hu : f ∘ u₀ = u := by
    funext i
    simp [f, u₀]
  have hv : f ∘ v₀ = v := by
    funext i
    simp [f, v₀]
  have hmul : f.mapMatrix (replicateCol ι u₀ * replicateRow ι v₀) =
      replicateCol ι (f ∘ u₀) * replicateRow ι (f ∘ v₀) := by
    rw [RingHom.mapMatrix_apply, Matrix.map_mul]
    rfl
  have hadj : f ∘ (X₀.adjugate *ᵥ u₀) = (f.mapMatrix X₀).adjugate *ᵥ (f ∘ u₀) := by
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec, ← RingHom.mapMatrix_apply, RingHom.map_adjugate]
  have h := congrArg f hg
  rw [RingHom.map_det, map_add, hmul, map_add, RingHom.map_det, RingHom.map_dotProduct, hadj, hA,
    hu, hv] at h
  exact h

end Matrix
