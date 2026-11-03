module

public import Feec.Models.Cube.DeRhamIdent

/-!
# Hodge theory of `HΛ((0, ½)ⁿ)` and `H̊Λ((0, ½)ⁿ)`: Poincaré, closed range, harmonic forms,
compactness

From the identification of the de Rham complexes of `Q = (0, ½)ⁿ` with the parity classes of the
torus de Rham complex (`Feec.Models.Cube.DeRhamIdent.HQmin_eq_compress`,
`Feec.Models.Cube.DeRhamIdent.HQmax_eq_compress`) this file proves, for the `ℤ`-indexed complexes
`Hmax n = HΛ(Q)` and `Hmin n = H̊Λ(Q)` (`Feec.Domain.DeRham` on `Q`), in every dimension `n` and
degree:

* **the Poincaré inequality** `‖z‖ ≤ (2π)⁻¹ ‖d z‖` on `D(d) ∩ (𝔷ⁱ)ᗮ` (`Hmax_norm_le`,
  `Hmin_norm_le`);
* **the compactness property** (`Hmax_hasCompactProperty`, `Hmin_hasCompactProperty`; Rellich and
  Gaffney on the cube);
* **the harmonic forms**: `ℌᵏ(HΛ(Q)) = 0` for `k ≠ 0` and `ℌ⁰(HΛ(Q))` is the line of the constants
  (`Hmax_harmonic_eq_bot`, `Hmax_harmonic_zero`); `ℌᵏ(H̊Λ(Q)) = 0` for `k ≠ n` and `ℌⁿ(H̊Λ(Q))` is
  the line of the constant volume form `dx₁ ∧ ⋯ ∧ dxₙ` (`Hmin_harmonic_eq_bot`,
  `Hmin_harmonic_top`).

The constant is the one of the torus, `(2π)⁻¹` (the first nonzero frequency `2π` of `𝕋ⁿ`); it is
sharp, since `cos 2πx` on `(0, ½)` is a Neumann eigenfunction, but sharpness is not formalized. The transfer from the torus uses two abstract
facts on compressions along scaled isometries: the Poincaré inequality passes with the same
constant (`Feec.HilbertComplex.norm_le_of_mem_orthogonal_compress`) and the harmonic forms are
those whose image is harmonic (`Feec.HilbertComplex.mem_harmonic_compress_iff`); the windows
`Λ⁰ → ⋯ → Λⁿ` pass to the `ℤ`-indexed complexes since the spaces outside `0 ≤ k ≤ n` are zero
(`Feec.HilbertComplex.norm_le_of_mem_orthogonal_cycles_of_window`,
`Feec.HilbertComplex.hasCompactProperty_of_window`, `Feec.HilbertComplex.harmonic_le_window`).
The statements on `Feec.Models.Cube.FEM.complex` and `Feec.Models.Cube.FEM.complexMin`, in the form
consumed by the finite element method, are in `Feec.Models.Cube.DeRhamIdentFEM`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1 (Poincaré inequality, closed range), §4.3 (compactness, harmonic forms of the de Rham
  complex)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6 (harmonic forms and
  cohomology of the de Rham complex with boundary conditions)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.2 (Poincaré ⇔ closed range, compactness property)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate Topology Finset
open Set MeasureTheory Filter LinearPMap

@[expose] public noncomputable section

/-! ### Compressions along scaled isometries: Poincaré and harmonic forms -/

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W W' : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)] [∀ i, CompleteSpace (W' i)]
  {H : HilbertComplex 𝕜 c W} {J : ∀ i, W' i →L[𝕜] W i} {s : ℝ}
  [∀ i, (LinearMap.range (J i : W' i →ₗ[𝕜] W i)).HasOrthogonalProjection]
  (hs : 0 < s) (hJ : ∀ i (x y : W' i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
  (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : W' i →ₗ[𝕜] W i))
include hs hJ hR

theorem J_injective_compress (i : ι) : Function.Injective (J i) :=
  (ScaledEmbedding.ofCompress hs hJ hR).J_injective i

/-- The kernels of a compression are the preimages of the kernels. -/
theorem mem_ker_compress_iff {i j : ι} {x : W' i} :
    x ∈ ((H.compress J hs hJ hR).d i j).ker ↔ J i x ∈ (H.d i j).ker := by
  rw [mem_ker_iff, mem_ker_iff]
  constructor
  · rintro ⟨y, rfl, hy⟩
    refine ⟨⟨_, (mem_compress_domain_iff hs hJ hR).1 y.2⟩, rfl, ?_⟩
    rw [← J_compress_d, hy, _root_.map_zero]
  · rintro ⟨y, hy1, hy2⟩
    have hx : x ∈ ((H.compress J hs hJ hR).d i j).domain :=
      (mem_compress_domain_iff hs hJ hR).2 (hy1 ▸ y.2)
    refine ⟨⟨x, hx⟩, rfl, J_injective_compress hs hJ hR j ?_⟩
    rw [J_compress_d, _root_.map_zero, ← hy2]
    exact apply_congr' _ _ _ hy1

/-- The kernels of the adjoints of a compression are the preimages of the kernels of the
adjoints. -/
theorem mem_ker_adjoint_compress_iff {i j : ι} {y : W' j} :
    y ∈ (((H.compress J hs hJ hR).d i j)†).ker ↔ J j y ∈ ((H.d i j)†).ker := by
  rw [mem_ker_iff, mem_ker_iff]
  constructor
  · rintro ⟨z, rfl, hz⟩
    refine ⟨⟨_, (mem_adjoint_compress_iff hs hJ hR).1 z.2⟩, rfl, ?_⟩
    rw [← J_adjoint_compress_d, hz, _root_.map_zero]
  · rintro ⟨z, hz1, hz2⟩
    have hy : y ∈ (((H.compress J hs hJ hR).d i j)†).domain :=
      (mem_adjoint_compress_iff hs hJ hR).2 (hz1 ▸ z.2)
    refine ⟨⟨y, hy⟩, rfl, J_injective_compress hs hJ hR i ?_⟩
    rw [J_adjoint_compress_d, _root_.map_zero, ← hz2]
    exact apply_congr' _ _ _ hz1

/-- **The harmonic forms of a compression** are those whose image is harmonic. -/
theorem mem_harmonic_compress_iff {i : ι} {x : W' i} :
    x ∈ (H.compress J hs hJ hR).harmonic i ↔ J i x ∈ H.harmonic i := by
  simp only [harmonic, cycles, Submodule.mem_inf, mem_ker_compress_iff hs hJ hR,
    mem_ker_adjoint_compress_iff hs hJ hR]

/-- **The Poincaré inequality passes to compressions with the same constant.** -/
theorem norm_le_of_mem_orthogonal_compress {i j : ι} {C : ℝ}
    (hP : ∀ u : (H.d i j).domain, (u : W i) ∈ (H.d i j).kerᗮ →
      ‖(u : W i)‖ ≤ C * ‖H.d i j u‖)
    (u : ((H.compress J hs hJ hR).d i j).domain)
    (hu : (u : W' i) ∈ ((H.compress J hs hJ hR).d i j).kerᗮ) :
    ‖(u : W' i)‖ ≤ C * ‖(H.compress J hs hJ hR).d i j u‖ := by
  have hJu : J i u ∈ (H.d i j).domain := (mem_compress_domain_iff hs hJ hR).1 u.2
  have hd : H.d i j ⟨J i u, hJu⟩ = J j ((H.compress J hs hJ hR).d i j u) :=
    (J_compress_d hs hJ hR u).symm
  set K := LinearMap.range (J i : W' i →ₗ[𝕜] W i)
  have horth : J i u ∈ (H.d i j).kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    obtain ⟨z', rfl, hz'⟩ := mem_ker_iff.1 hz
    have hred := hR.reduces i j
    have hPz : K.starProjection (z' : W i) ∈ (H.d i j).domain := hred.proj_mem z'
    have hdP : H.d i j ⟨_, hPz⟩ = 0 := by
      rw [hred.comm z', hz', _root_.map_zero]
    have hmem : K.starProjection (z' : W i) ∈ K := by
      rw [Submodule.starProjection_apply]; exact Submodule.coe_mem _
    obtain ⟨v, hv⟩ := hmem
    have hvd : v ∈ ((H.compress J hs hJ hR).d i j).domain :=
      (mem_compress_domain_iff hs hJ hR).2 (by
        rw [show J i v = K.starProjection (z' : W i) from hv]; exact hPz)
    have hv0 : (H.compress J hs hJ hR).d i j ⟨v, hvd⟩ = 0 := by
      refine J_injective_compress hs hJ hR j ?_
      rw [J_compress_d, _root_.map_zero, ← hdP]
      exact apply_congr' _ _ _ hv
    have hvu : ⟪v, (u : W' i)⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal _ _).1 hu v (mem_ker_iff.2 ⟨⟨v, hvd⟩, rfl, hv0⟩)
    have hKu : K.starProjection (J i u) = J i u :=
      (Submodule.starProjection_eq_self_iff).2 ⟨u, rfl⟩
    calc ⟪(z' : W i), J i u⟫_𝕜 = ⟪(z' : W i), K.starProjection (J i u)⟫_𝕜 := by rw [hKu]
      _ = ⟪K.starProjection (z' : W i), J i u⟫_𝕜 :=
          (Submodule.inner_starProjection_left_eq_right K _ _).symm
      _ = ⟪J i v, J i u⟫_𝕜 := by rw [← hv]; rfl
      _ = 0 := by rw [hJ, hvu, mul_zero]
  have h1 := hP ⟨J i u, hJu⟩ horth
  rw [hd] at h1
  change ‖J i u‖ ≤ C * ‖J j _‖ at h1
  rw [norm_apply_of_inner hs hJ, norm_apply_of_inner hs hJ, mul_left_comm] at h1
  exact le_of_mul_le_mul_left h1 (Real.sqrt_pos.2 hs)

end Feec.HilbertComplex

/-! ### The real torus window -/

namespace Feec.Models.Cube.DeRhamIdent

open Geometry
open Feec.Domain (formIdx extDerivOp L2F L2 toL2F)
open Feec.Fourier.Exterior (Form)

variable {n : ℕ}

theorem RT_adjoint (a b : Fin (Fintype.card (Fin n) + 1)) :
    ((RT n).d a b)† = (((Torus.DeRham.window (Fin n)).d a b)†).restrictScalars :=
  ((Torus.DeRham.window (Fin n)).d a b).adjoint_restrictScalars (real_inner_TW a)
    (real_inner_TW b) ((Torus.DeRham.window (Fin n)).dense a b)

/-- **The compactness property of the real torus window** (Rellich on `𝕋ⁿ`). -/
theorem RT_hasCompactProperty : (RT n).HasCompactProperty := fun a => by
  obtain ⟨K, hK, hsub⟩ := Torus.DeRham.window_hasCompactProperty (d := Fin n) a
  refine ⟨K, hK, fun x hx hx' h1 h2 h3 => ?_⟩
  set p := (ComplexShape.window (Fintype.card (Fin n) + 1)).prev a
  have hx'' : x ∈ (((Torus.DeRham.window (Fin n)).d p a)†).domain := by
    have := hx'; rw [RT_adjoint] at this; exact this
  refine hsub x hx hx'' h1 h2 ?_
  have e : ((RT n).d p a)† ⟨x, hx'⟩ = ((Torus.DeRham.window (Fin n)).d p a)† ⟨x, hx''⟩ :=
    apply_eq_of_eq (RT_adjoint p a) ⟨x, hx'⟩ ⟨x, hx''⟩ rfl
  rw [← e]; exact h3

/-- **The Poincaré inequality of the real torus window**: `‖u‖ ≤ (2π)⁻¹ ‖d u‖` on
`D(d) ∩ N(d)ᗮ` (real orthogonality). -/
theorem RT_norm_le (a b : Fin (Fintype.card (Fin n) + 1)) (u : ((RT n).d a b).domain)
    (hu : (u : TW n a) ∈ ((RT n).d a b).kerᗮ) :
    ‖(u : TW n a)‖ ≤ (2 * Real.pi)⁻¹ * ‖(RT n).d a b u‖ := by
  have hu' : (u : TW n a) ∈ ((Torus.DeRham.window (Fin n)).d a b).kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    have hzR : ∀ w ∈ ((Torus.DeRham.window (Fin n)).d a b).ker,
        ⟪w, (u : TW n a)⟫_ℝ = 0 := fun w hw => by
      refine (Submodule.mem_orthogonal _ _).1 hu w ?_
      obtain ⟨y, rfl, hy⟩ := mem_ker_iff.1 hw
      exact mem_ker_iff.2 ⟨⟨y.1, y.2⟩, rfl, hy⟩
    have h1 := hzR z hz
    have h2 := hzR (Complex.I • z) (Submodule.smul_mem _ _ hz)
    rw [real_inner_TW] at h1 h2
    rw [inner_smul_left, Complex.conj_I] at h2
    apply Complex.ext
    · simpa using h1
    · simpa using h2
  exact DeRham.window_norm_le_of_mem_orthogonal (d := Fin n) ⟨u.1, u.2⟩ hu'

/-- **The harmonic forms of the real torus window** are the constant forms. -/
theorem mem_RT_harmonic_iff {a : Fin (Fintype.card (Fin n) + 1)} {x : TW n a} :
    x ∈ (RT n).harmonic a ↔ ∀ m, m ≠ 0 → (x : (Fin n → ℤ) → Form ℂ (Fin n) a) m = 0 := by
  rw [← DeRham.mem_window_harmonic_iff]
  change x ∈ (RT n).cycles a ⊓ _ ↔ x ∈ (Torus.DeRham.window (Fin n)).cycles a ⊓ _
  rw [Submodule.mem_inf, Submodule.mem_inf, Feec.HilbertComplex.mem_cycles_restrictScalars]
  refine and_congr Iff.rfl ?_
  rw [RT_adjoint, mem_ker_iff, mem_ker_iff]
  exact ⟨fun ⟨y, h1, h2⟩ => ⟨⟨y.1, y.2⟩, h1, h2⟩, fun ⟨y, h1, h2⟩ => ⟨⟨y.1, y.2⟩, h1, h2⟩⟩

/-! ### The windows of `H̊Λ(Q)` and `HΛ(Q)` -/

/-- **The compactness property of `H̊Λ(Q)`** (window). -/
theorem HQmin_hasCompactProperty : (HQmin n).HasCompactProperty := by
  rw [HQmin_eq_compress]
  exact Feec.HilbertComplex.hasCompactProperty_compress two_pow_pos (inner_J true)
    (reducing_range true) RT_hasCompactProperty

/-- **The compactness property of `HΛ(Q)`** (window). -/
theorem HQmax_hasCompactProperty : (HQmax n).HasCompactProperty := by
  rw [HQmax_eq_compress]
  exact Feec.HilbertComplex.hasCompactProperty_compress two_pow_pos (inner_J false)
    (reducing_range false) RT_hasCompactProperty

/-- **The Poincaré inequality of `H̊Λ(Q)`** (window), constant `(2π)⁻¹`. -/
theorem HQmin_norm_le (a b : Fin (Fintype.card (Fin n) + 1)) (u : ((HQmin n).d a b).domain)
    (hu : (u : WQ n a) ∈ ((HQmin n).d a b).kerᗮ) :
    ‖(u : WQ n a)‖ ≤ (2 * Real.pi)⁻¹ * ‖(HQmin n).d a b u‖ := by
  have key : ∀ H' : HilbertComplex ℝ (ComplexShape.window (Fintype.card (Fin n) + 1)) (WQ n),
      H' = (RT n).compress (J true) two_pow_pos (inner_J true) (reducing_range true) →
      ∀ u : (H'.d a b).domain, (u : WQ n a) ∈ (H'.d a b).kerᗮ →
        ‖(u : WQ n a)‖ ≤ (2 * Real.pi)⁻¹ * ‖H'.d a b u‖ := by
    rintro _ rfl u hu
    exact Feec.HilbertComplex.norm_le_of_mem_orthogonal_compress two_pow_pos (inner_J true)
      (reducing_range true) (RT_norm_le a b) u hu
  exact key _ HQmin_eq_compress u hu

/-- **The Poincaré inequality of `HΛ(Q)`** (window), constant `(2π)⁻¹`. -/
theorem HQmax_norm_le (a b : Fin (Fintype.card (Fin n) + 1)) (u : ((HQmax n).d a b).domain)
    (hu : (u : WQ n a) ∈ ((HQmax n).d a b).kerᗮ) :
    ‖(u : WQ n a)‖ ≤ (2 * Real.pi)⁻¹ * ‖(HQmax n).d a b u‖ := by
  have key : ∀ H' : HilbertComplex ℝ (ComplexShape.window (Fintype.card (Fin n) + 1)) (WQ n),
      H' = (RT n).compress (J false) two_pow_pos (inner_J false) (reducing_range false) →
      ∀ u : (H'.d a b).domain, (u : WQ n a) ∈ (H'.d a b).kerᗮ →
        ‖(u : WQ n a)‖ ≤ (2 * Real.pi)⁻¹ * ‖H'.d a b u‖ := by
    rintro _ rfl u hu
    exact Feec.HilbertComplex.norm_le_of_mem_orthogonal_compress two_pow_pos (inner_J false)
      (reducing_range false) (RT_norm_le a b) u hu
  exact key _ HQmax_eq_compress u hu

theorem mem_HQmin_harmonic_iff {a : Fin (Fintype.card (Fin n) + 1)} {x : WQ n a} :
    x ∈ (HQmin n).harmonic a ↔
      ∀ m, m ≠ 0 → (Jf true (a : ℕ) x : (Fin n → ℤ) → Form ℂ (Fin n) a) m = 0 := by
  rw [HQmin_eq_compress, Feec.HilbertComplex.mem_harmonic_compress_iff, mem_RT_harmonic_iff]
  rfl

theorem mem_HQmax_harmonic_iff {a : Fin (Fintype.card (Fin n) + 1)} {x : WQ n a} :
    x ∈ (HQmax n).harmonic a ↔
      ∀ m, m ≠ 0 → (Jf false (a : ℕ) x : (Fin n → ℤ) → Form ℂ (Fin n) a) m = 0 := by
  rw [HQmax_eq_compress, Feec.HilbertComplex.mem_harmonic_compress_iff, mem_RT_harmonic_iff]
  rfl

/-- A harmonic real parity sequence has only the zero mode, whose coefficients are fixed by every
`± ε_j`. -/
theorem eq_zero_of_harmonic_parity {rel : Bool} {k : ℕ} {x : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (hx : ∀ m, m ≠ 0 → (Jf rel k x : (Fin n → ℤ) → Form ℂ (Fin n) k) m = 0)
    (ht : ∀ t : {s : Finset (Fin n) // #s = k}, ∃ j, DeRham.parSign rel * DeRham.reflSign j t.1 ≠ 1) :
    x = 0 := by
  refine injective_Jf rel k ((Lp.ext_count fun m => ?_).trans (_root_.map_zero _).symm)
  rw [DeRham.coeFn_zero_count]
  by_cases hm : m = 0
  · subst hm
    ext t
    obtain ⟨j, hj⟩ := ht t
    have e := (Jf_realPar rel k x).2 j 0 t
    rw [Fourier.Torus.flipAt_zero] at e
    have : (Jf rel k x : (Fin n → ℤ) → Form ℂ (Fin n) k) 0 t = 0 := by
      by_contra hne
      exact hj (mul_right_cancel₀ hne (e.symm.trans (one_mul _).symm))
    rw [this]; rfl
  · exact hx m hm

/-- **No harmonic forms of `HΛ(Q)` in positive degrees** (window). -/
theorem HQmax_harmonic_eq_bot {a : Fin (Fintype.card (Fin n) + 1)} (ha : (a : ℕ) ≠ 0) :
    (HQmax n).harmonic a = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  refine eq_zero_of_harmonic_parity (rel := false) (mem_HQmax_harmonic_iff.1 hx) fun t => ?_
  obtain ⟨j, hj⟩ : t.1.Nonempty := Finset.card_pos.1 (by rw [t.2]; omega)
  exact ⟨j, by simp [DeRham.parSign, DeRham.reflSign, hj]; norm_num⟩

/-- **No harmonic forms of `H̊Λ(Q)` below the top degree** (window). -/
theorem HQmin_harmonic_eq_bot {a : Fin (Fintype.card (Fin n) + 1)}
    (ha : (a : ℕ) ≠ Fintype.card (Fin n)) : (HQmin n).harmonic a = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  refine eq_zero_of_harmonic_parity (rel := true) (mem_HQmin_harmonic_iff.1 hx) fun t => ?_
  have hne : t.1 ≠ Finset.univ := fun h => ha (by rw [← t.2, h, Finset.card_univ])
  obtain ⟨j, hj⟩ : ∃ j, j ∉ t.1 := by
    by_contra h
    push Not at h
    exact hne (Finset.eq_univ_iff_forall.2 h)
  exact ⟨j, by simp [DeRham.parSign, DeRham.reflSign, hj]; norm_num⟩

/-- The real part of the zero-mode coefficient `t₀` of the extension. -/
def zeroCoeff (rel : Bool) (k : ℕ) (t₀ : {s : Finset (Fin n) // #s = k})
    (S : Submodule ℝ (L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)))) : S →ₗ[ℝ] ℝ where
  toFun x := ((Jf rel k x : (Fin n → ℤ) → Form ℂ (Fin n) k) 0 t₀).re
  map_add' x y := by
    simp only [Submodule.coe_add, _root_.map_add]
    rw [Measure.ae_count_iff.1 (Lp.coeFn_add _ _) 0]; simp
  map_smul' c x := by
    simp only [Submodule.coe_smul, _root_.map_smul, RingHom.id_apply, smul_eq_mul]
    rw [show (c • Jf rel k (x : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
        Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))) = (c : ℂ) • Jf rel k x
      from (RCLike.real_smul_eq_coe_smul c _), DeRham.coeFn_smul_count]
    simp

/-- **A degree with a single index set has at most one harmonic direction**: on forms whose
extension has only the zero mode, the real zero-mode coefficient is injective. -/
theorem injective_zeroCoeff {rel : Bool} {k : ℕ} (t₀ : {s : Finset (Fin n) // #s = k})
    (h₀ : ∀ t, t = t₀) (S : Submodule ℝ (L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))))
    (hS : ∀ x ∈ S, ∀ m, m ≠ 0 → (Jf rel k x : (Fin n → ℤ) → Form ℂ (Fin n) k) m = 0) :
    Function.Injective (zeroCoeff rel k t₀ S) := by
  intro x y hxy
  refine Subtype.ext (injective_Jf rel k (Lp.ext_count fun m => ?_))
  by_cases hm : m = 0
  · subst hm
    ext t
    rw [h₀ t]
    have hr : ∀ z : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)),
        (Jf rel k z : (Fin n → ℤ) → Form ℂ (Fin n) k) 0 t₀ =
          (((Jf rel k z : (Fin n → ℤ) → Form ℂ (Fin n) k) 0 t₀).re : ℂ) := fun z => by
      have e := (Jf_realPar rel k z).1 0 t₀
      rw [neg_zero] at e
      exact (Complex.conj_eq_iff_re.1 e.symm).symm
    rw [hr x, hr y]
    exact congrArg (fun r : ℝ => (r : ℂ)) hxy
  · rw [hS _ x.2 m hm, hS _ y.2 m hm]

theorem finiteDimensional_of_zeroCoeff {rel : Bool} {k : ℕ} (t₀ : {s : Finset (Fin n) // #s = k})
    (h₀ : ∀ t, t = t₀) (S : Submodule ℝ (L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))))
    (hS : ∀ x ∈ S, ∀ m, m ≠ 0 → (Jf rel k x : (Fin n → ℤ) → Form ℂ (Fin n) k) m = 0) :
    FiniteDimensional ℝ S :=
  Module.Finite.of_injective _ (injective_zeroCoeff t₀ h₀ S hS)

theorem finrank_le_one_of_zeroCoeff {rel : Bool} {k : ℕ} (t₀ : {s : Finset (Fin n) // #s = k})
    (h₀ : ∀ t, t = t₀) (S : Submodule ℝ (L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))))
    (hS : ∀ x ∈ S, ∀ m, m ≠ 0 → (Jf rel k x : (Fin n → ℤ) → Form ℂ (Fin n) k) m = 0) :
    Module.finrank ℝ S ≤ 1 := by
  have := finiteDimensional_of_zeroCoeff t₀ h₀ S hS
  calc Module.finrank ℝ S ≤ Module.finrank ℝ ℝ :=
        LinearMap.finrank_le_finrank_of_injective (injective_zeroCoeff t₀ h₀ S hS)
    _ = 1 := Module.finrank_self ℝ

end Feec.Models.Cube.DeRhamIdent

/-! ### From the window `0, …, N` to the complex on `ℤ` -/

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {V : ℤ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
  (H : HilbertComplex 𝕜 (ComplexShape.up ℤ) V) {N : ℕ}
  (hf : ∀ a b : Fin (N + 1), (ComplexShape.up ℤ).Rel ((a : ℕ) : ℤ) ((b : ℕ) : ℤ) →
    (ComplexShape.window (N + 1)).Rel a b)

/-- The adjoint of the zero map has full domain and vanishes. -/
theorem mem_adjoint_zero_domain {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace E] (y : F) :
    y ∈ ((0 : E →ₗ.[𝕜] F)†).domain :=
  mem_adjoint_domain_of_exists _ ⟨0, fun x => by simp⟩

theorem adjoint_zero_apply {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace E]
    (y : ((0 : E →ₗ.[𝕜] F)†).domain) : (0 : E →ₗ.[𝕜] F)† y = 0 :=
  adjoint_apply_eq (by simp [LinearPMap.zero_domain]) y fun x => by simp

theorem adjoint_mem_ker_of_eq_zero {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace E] {T : E →ₗ.[𝕜] F}
    (hT : T = 0) (y : F) : y ∈ (T†).ker := by
  subst hT
  exact mem_ker_iff.2 ⟨⟨y, mem_adjoint_zero_domain y⟩, rfl, adjoint_zero_apply _⟩

theorem mem_ker_adjoint_prev_iff {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    (G : HilbertComplex 𝕜 c W) {i j : ι} (h : c.Rel i j) {x : W j} :
    x ∈ ((G.d (c.prev j) j)†).ker ↔ x ∈ ((G.d i j)†).ker := by
  obtain rfl := c.prev_eq' h; rfl

theorem mem_ker_of_eq_zero {E F : Type*} [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
    [Module 𝕜 F] {T : E →ₗ.[𝕜] F} (hT : T = 0) (x : E) : x ∈ T.ker := by
  subst hT
  exact mem_ker_iff.2 ⟨⟨x, Submodule.mem_top⟩, rfl, rfl⟩

/-- At the last index of the window, the outgoing differential is `0`. -/
theorem window_d_next_last (a : Fin (N + 1)) (ha : ¬ (a : ℕ) < N) :
    (H.restrict (fun a : Fin (N + 1) => ((a : ℕ) : ℤ)) hf).d a
      ((ComplexShape.window (N + 1)).next a) = 0 :=
  (H.restrict _ hf).shape _ _ fun h => by
    change (a : ℕ) + 1 = ((ComplexShape.window (N + 1)).next a : ℕ) at h
    have := ((ComplexShape.window (N + 1)).next a).2
    omega

/-- At the first index of the window, the incoming differential is `0`. -/
theorem window_d_prev_zero (a : Fin (N + 1)) (ha : (a : ℕ) = 0) :
    (H.restrict (fun a : Fin (N + 1) => ((a : ℕ) : ℤ)) hf).d
      ((ComplexShape.window (N + 1)).prev a) a = 0 :=
  (H.restrict _ hf).shape _ _ fun h => by
    change (((ComplexShape.window (N + 1)).prev a : Fin (N + 1)) : ℕ) + 1 = (a : ℕ) at h
    omega

/-- **The Poincaré inequality on `ℤ` from the window**, when the spaces outside `0, …, N` are
zero. -/
theorem norm_le_of_mem_orthogonal_cycles_of_window {C : ℝ} (hC : 0 ≤ C)
    (hlow : ∀ i : ℤ, i < 0 → Subsingleton (V i)) (hhigh : ∀ i : ℤ, (N : ℤ) < i → Subsingleton (V i))
    (hP : ∀ (a b : Fin (N + 1))
      (u : ((H.restrict (fun a : Fin (N + 1) => ((a : ℕ) : ℤ)) hf).d a b).domain),
      (u : V ((a : ℕ) : ℤ)) ∈ ((H.restrict (fun a : Fin (N + 1) => ((a : ℕ) : ℤ)) hf).d a b).kerᗮ →
        ‖(u : V ((a : ℕ) : ℤ))‖ ≤
          C * ‖(H.restrict (fun a : Fin (N + 1) => ((a : ℕ) : ℤ)) hf).d a b u‖)
    {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (z : (H.d i j).domain)
    (hz : (z : V i) ∈ (H.cycles i)ᗮ) : ‖(z : V i)‖ ≤ C * ‖H.d i j z‖ := by
  change i + 1 = j at hij
  subst hij
  rw [H.cycles_eq (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)] at hz
  by_cases h0 : i < 0
  · have := hlow i h0
    rw [Subsingleton.elim (z : V i) 0, norm_zero]
    positivity
  by_cases hN : (N : ℤ) ≤ i
  · have := hhigh (i + 1) (by omega)
    have hz0 : (z : V i) ∈ (H.d i (i + 1)).ker := mem_ker_iff.2 ⟨z, rfl, Subsingleton.elim _ _⟩
    have h := (Submodule.mem_orthogonal _ _).1 hz _ hz0
    rw [inner_self_eq_zero] at h
    rw [h, norm_zero]
    positivity
  · push Not at h0 hN
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have hm : m < N := by omega
    exact hP ⟨m, by omega⟩ ⟨m + 1, by omega⟩ z hz

/-- **The compactness property on `ℤ` from the window**, when the spaces outside `0, …, N` are
zero. -/
theorem hasCompactProperty_of_window
    (hlow : ∀ i : ℤ, i < 0 → Subsingleton (V i)) (hhigh : ∀ i : ℤ, (N : ℤ) < i → Subsingleton (V i))
    (hW : (H.restrict (fun a : Fin (N + 1) => ((a : ℕ) : ℤ)) hf).HasCompactProperty) :
    H.HasCompactProperty := by
  intro i
  by_cases hout : i < 0 ∨ (N : ℤ) < i
  · have : Subsingleton (V i) := hout.elim (hlow i) (hhigh i)
    exact ⟨univ, Set.subsingleton_univ.isCompact, fun x _ _ _ _ _ => mem_univ x⟩
  push Not at hout
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hout.1
  have hmN : m ≤ N := by omega
  set a : Fin (N + 1) := ⟨m, by omega⟩
  refine (hW a).of_isClosedEmbedding (ContinuousLinearMap.id 𝕜 _) Topology.IsClosedEmbedding.id
    zero_le_one zero_le_one ?_ ?_
  · have hnext : (ComplexShape.up ℤ).next (m : ℤ) = (m : ℤ) + 1 :=
      (ComplexShape.up ℤ).next_eq' rfl
    by_cases hm : m < N
    · have hab : (ComplexShape.window (N + 1)).next a = ⟨m + 1, by omega⟩ :=
        (ComplexShape.window (N + 1)).next_eq' rfl
      revert a
      intro a hab
      rw [hnext, hab]
      intro x
      exact ⟨x.2, by rw [one_mul]; rfl⟩
    · intro x
      have h0 := window_d_next_last H hf a hm
      refine ⟨by rw [h0]; exact Submodule.mem_top, ?_⟩
      rw [apply_eq_zero_of_eq_zero h0, norm_zero]
      positivity
  · by_cases hm : 0 < m
    · obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
      have hprev : (ComplexShape.up ℤ).prev (((p + 1 : ℕ)) : ℤ) = (p : ℤ) :=
        (ComplexShape.up ℤ).prev_eq' (by change (p : ℤ) + 1 = ((p + 1 : ℕ) : ℤ); push_cast; ring)
      have hpa : (ComplexShape.window (N + 1)).prev a = ⟨p, by omega⟩ :=
        (ComplexShape.window (N + 1)).prev_eq' rfl
      revert a
      intro a hpa
      rw [hprev, hpa]
      intro x
      exact ⟨x.2, by rw [one_mul]; rfl⟩
    · intro x
      have h0 := window_d_prev_zero H hf a (by change m = 0; omega)
      have key : ∀ T : V (((ComplexShape.window (N + 1)).prev a : ℕ) : ℤ) →ₗ.[𝕜] V (m : ℤ),
          T = 0 → ∃ hx : (x : V (m : ℤ)) ∈ (T†).domain,
            ‖T† ⟨_, hx⟩‖ ≤ 1 * ‖(H.d ((ComplexShape.up ℤ).prev (m : ℤ)) (m : ℤ))† x‖ := by
        rintro T rfl
        refine ⟨mem_adjoint_zero_domain _, ?_⟩
        rw [adjoint_zero_apply, norm_zero]
        positivity
      exact key _ h0

/-- **The harmonic forms on `ℤ` are harmonic in the window.** -/
theorem harmonic_le_window (a : Fin (N + 1)) :
    H.harmonic ((a : ℕ) : ℤ) ≤
      (H.restrict (fun a : Fin (N + 1) => ((a : ℕ) : ℤ)) hf).harmonic a := by
  intro x hx
  obtain ⟨hc, hk⟩ := Submodule.mem_inf.1 hx
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · by_cases ha : (a : ℕ) < N
    · set b : Fin (N + 1) := ⟨(a : ℕ) + 1, by omega⟩
      rw [(H.restrict _ hf).cycles_eq (show (ComplexShape.window (N + 1)).Rel a b from rfl)]
      rw [H.cycles_eq (show (ComplexShape.up ℤ).Rel ((a : ℕ) : ℤ) ((b : ℕ) : ℤ) from rfl)] at hc
      exact hc
    · exact mem_ker_of_eq_zero (window_d_next_last H hf a ha) x
  · by_cases ha : 0 < (a : ℕ)
    · set p : Fin (N + 1) := ⟨(a : ℕ) - 1, by omega⟩
      have hpw : (ComplexShape.window (N + 1)).Rel p a := by
        change (a : ℕ) - 1 + 1 = (a : ℕ); omega
      have hpz : (ComplexShape.up ℤ).Rel ((p : ℕ) : ℤ) ((a : ℕ) : ℤ) := by
        change (((a : ℕ) - 1 : ℕ) : ℤ) + 1 = ((a : ℕ) : ℤ); omega
      rw [mem_ker_adjoint_prev_iff _ hpw]
      exact (mem_ker_adjoint_prev_iff H hpz).1 hk
    · exact adjoint_mem_ker_of_eq_zero (window_d_prev_zero H hf a (by omega)) x

end Feec.HilbertComplex

/-! ### The complexes on `ℤ`: `HΛ(Q)` and `H̊Λ(Q)` on `Q = (0, ½)ⁿ` -/

namespace Feec.Models.Cube.DeRhamIdent

open Geometry
open Feec.Domain (formIdx extDerivOp L2F L2 toL2F)
open Feec.Fourier.Exterior (Form)

variable {n : ℕ}

theorem isEmpty_formIdx_of_neg {i : ℤ} (hi : i < 0) : IsEmpty (formIdx n i) :=
  ⟨fun s => by have := s.2; omega⟩

theorem isEmpty_formIdx_of_gt {i : ℤ} (hi : (Fintype.card (Fin n) : ℤ) < i) :
    IsEmpty (formIdx n i) :=
  ⟨fun s => by
    have h1 := s.2
    have h2 : #s.1 ≤ Fintype.card (Fin n) := Finset.card_le_univ s.1
    omega⟩

theorem subsingleton_L2F {Ω : Set (Fin n → ℝ)} {ι : Type} [Fintype ι] [IsEmpty ι] :
    Subsingleton (L2F ℝ Ω ι) :=
  ⟨fun _ _ => PiLp.ext fun i => isEmptyElim i⟩

theorem hlow (Ω : Set (Fin n → ℝ)) (i : ℤ) (hi : i < 0) :
    Subsingleton (L2F ℝ Ω (formIdx n i)) :=
  have := isEmpty_formIdx_of_neg (n := n) hi
  subsingleton_L2F

theorem hhigh (Ω : Set (Fin n → ℝ)) (i : ℤ) (hi : ((Fintype.card (Fin n) : ℕ) : ℤ) < i) :
    Subsingleton (L2F ℝ Ω (formIdx n i)) :=
  have := isEmpty_formIdx_of_gt (n := n) hi
  subsingleton_L2F

variable (n) in
/-- `HΛ(Q)` on `ℤ`. -/
abbrev Hmax : HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ (Q (Fin n)) (formIdx n k) :=
  (Feec.Domain.deRham ℝ n).maximalComplex (isOpen_Q (d := Fin n))

variable (n) in
/-- `H̊Λ(Q)` on `ℤ`. -/
abbrev Hmin : HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ (Q (Fin n)) (formIdx n k) :=
  (Feec.Domain.deRham ℝ n).minimalComplex (isOpen_Q (d := Fin n))

/-- **The Poincaré inequality of `HΛ(Q)`**, `‖z‖ ≤ (2π)⁻¹ ‖d z‖` on `D(d) ∩ (𝔷ⁱ)ᗮ`. -/
theorem Hmax_norm_le {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (z : ((Hmax n).d i j).domain)
    (hz : (z : L2F ℝ (Q (Fin n)) (formIdx n i)) ∈ ((Hmax n).cycles i)ᗮ) :
    ‖(z : L2F ℝ (Q (Fin n)) (formIdx n i))‖ ≤ (2 * Real.pi)⁻¹ * ‖(Hmax n).d i j z‖ :=
  Feec.HilbertComplex.norm_le_of_mem_orthogonal_cycles_of_window (Hmax n) ι_rel (by positivity)
    (hlow _) (hhigh _) (fun a b u hu => HQmax_norm_le a b u hu) hij z hz

/-- **The Poincaré inequality of `H̊Λ(Q)`**, `‖z‖ ≤ (2π)⁻¹ ‖d z‖` on `D(d) ∩ (𝔷ⁱ)ᗮ`. -/
theorem Hmin_norm_le {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (z : ((Hmin n).d i j).domain)
    (hz : (z : L2F ℝ (Q (Fin n)) (formIdx n i)) ∈ ((Hmin n).cycles i)ᗮ) :
    ‖(z : L2F ℝ (Q (Fin n)) (formIdx n i))‖ ≤ (2 * Real.pi)⁻¹ * ‖(Hmin n).d i j z‖ :=
  Feec.HilbertComplex.norm_le_of_mem_orthogonal_cycles_of_window (Hmin n) ι_rel (by positivity)
    (hlow _) (hhigh _) (fun a b u hu => HQmin_norm_le a b u hu) hij z hz

theorem Hmax_hasCompactProperty : (Hmax n).HasCompactProperty :=
  Feec.HilbertComplex.hasCompactProperty_of_window (Hmax n) ι_rel (hlow _) (hhigh _)
    HQmax_hasCompactProperty

theorem Hmin_hasCompactProperty : (Hmin n).HasCompactProperty :=
  Feec.HilbertComplex.hasCompactProperty_of_window (Hmin n) ι_rel (hlow _) (hhigh _)
    HQmin_hasCompactProperty

/-! ### Constant forms and the harmonic forms -/

/-- The coefficients of the constant form `dx_{s₀}`. -/
def constFun {k : ℤ} (s₀ : formIdx n k) : formIdx n k → (Fin n → ℝ) → ℝ :=
  fun s _ => if s = s₀ then 1 else 0

theorem memLp_constFun {Ω : Set (Fin n → ℝ)} (hΩm : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    {k : ℤ} (s₀ : formIdx n k) (s : formIdx n k) : MemLp (constFun s₀ s) 2 (volume.restrict Ω) :=
  Feec.Domain.memLp_of_continuous hΩm hb continuous_const

/-- The constant form `dx_{s₀}` on a bounded measurable `Ω`. -/
def constForm {Ω : Set (Fin n → ℝ)} (hΩm : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) {k : ℤ}
    (s₀ : formIdx n k) : L2F ℝ Ω (formIdx n k) :=
  toL2F (memLp_constFun hΩm hb s₀)

theorem constForm_ne_zero {Ω : Set (Fin n → ℝ)} (hΩm : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : volume Ω ≠ 0) {k : ℤ} (s₀ : formIdx n k) :
    constForm hΩm hb s₀ ≠ 0 :=
  Feec.Domain.toL2F_ne_zero _ hpos (i := s₀) fun _ => by simp [constFun]

theorem volume_Q_ne_zero : volume (Q (Fin n)) ≠ 0 :=
  (isOpen_Q.measure_pos volume ⟨fun _ => 1 / 4, mem_Q.2 fun _ => by norm_num⟩).ne'

theorem formExt_const_eq {k : ℤ} (s₀ : formIdx n k) (r : Finset (Fin n)) :
    Feec.Domain.formExt (constFun s₀) r =
      fun _ => Feec.Domain.formExt (fun s => if s = s₀ then (1 : ℝ) else 0) r := by
  unfold Feec.Domain.formExt constFun
  split_ifs <;> first | rfl | simp_all

theorem extDerivOp_apply_const {k : ℤ} (s₀ : formIdx n k) (t : formIdx n (k + 1))
    (y : Fin n → ℝ) :
    (extDerivOp ℝ n k).apply (constFun s₀) t y = 0 := by
  rw [Feec.Domain.extDerivOp_apply, Feec.Domain.extD]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [formExt_const_eq, fderiv_const_apply, _root_.zero_apply, mul_zero]

theorem formalAdj_apply_const {k : ℤ} (s₀ : formIdx n (k + 1)) (r : formIdx n k)
    (y : Fin n → ℝ) :
    (extDerivOp ℝ n k).formalAdj.apply (constFun s₀) r y = 0 := by
  rw [Feec.Domain.formalAdj_extDerivOp_apply, Feec.Domain.extDAdj, neg_eq_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [formExt_const_eq, fderiv_const_apply, _root_.zero_apply, mul_zero]

theorem toL2F_eq_zero {Ω : Set (Fin n → ℝ)} {ι : Type} [Fintype ι] {ψ : ι → (Fin n → ℝ) → ℝ}
    (h0 : ∀ i y, ψ i y = 0) (hψ : ∀ i, MemLp (ψ i) 2 (volume.restrict Ω)) : toL2F hψ = 0 := by
  refine PiLp.ext fun i => ?_
  rw [PiLp.zero_apply]
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (hψ i), Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with y h1 h2
  change ((hψ i).toLp (ψ i) : (Fin n → ℝ) → ℝ) y = _
  rw [h1, h2, h0]; rfl

/-- The adjoint of an operator out of a zero space has full domain and vanishes. -/
theorem mem_ker_adjoint_of_subsingleton {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [Subsingleton E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (T : E →ₗ.[ℝ] F) (y : F) : y ∈ (T†).ker :=
  mem_ker_iff.2 ⟨⟨y, mem_adjoint_domain_of_exists _ ⟨0, fun x => by
    rw [Subsingleton.elim (x : E) 0, inner_zero_right, show T x = 0 by
      rw [show x = 0 from Subsingleton.elim _ _, T.map_zero], inner_zero_right]⟩⟩,
    rfl, Subsingleton.elim _ _⟩

/-- **Operators into a zero space have full minimal domain**: test fields are dense. -/
theorem minimal_domain_eq_top_of_isEmpty {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {ι κ : Type}
    [Fintype ι] [Fintype κ] [IsEmpty κ] (A : Feec.Domain.ConstCoeffOp (Fin n → ℝ) ℝ ι κ) :
    (A.minimal Ω).domain = ⊤ := by
  have : Subsingleton (L2F ℝ Ω κ) := subsingleton_L2F
  refine eq_top_iff.2 fun u _ => ?_
  set f : L2F ℝ Ω ι → L2F ℝ Ω ι × L2F ℝ Ω κ := fun v => (v, 0)
  have hf : Continuous f := continuous_id.prodMk continuous_const
  have hsub : f '' (Feec.Domain.testFieldSub ℝ Ω ι : Set (L2F ℝ Ω ι)) ⊆
      (A.testGraph Ω : Set (L2F ℝ Ω ι × L2F ℝ Ω κ)) := by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    exact ⟨φ, hφ, by simp only [f]; congr 1; exact Subsingleton.elim _ _⟩
  have hu : f u ∈ closure (A.testGraph Ω : Set (L2F ℝ Ω ι × L2F ℝ Ω κ)) := by
    refine closure_mono hsub (image_closure_subset_closure_image hf ⟨u, ?_, rfl⟩)
    rw [(Feec.Domain.dense_testFieldSub hΩ ι).closure_eq]; exact mem_univ u
  rw [← Submodule.topologicalClosure_coe, SetLike.mem_coe, ← A.minimal_graph hΩ] at hu
  exact LinearPMap.mem_domain_of_mem_graph hu

variable (n) in
/-- The constant function `1`, a `0`-form on `Q`. -/
abbrev oneQ : L2F ℝ (Q (Fin n)) (formIdx n 0) :=
  constForm measurableSet_Q (isBounded_openCube _ _) ⟨∅, by simp⟩

theorem oneQ_mem_harmonic : oneQ n ∈ (Hmax n).harmonic 0 := by
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [(Hmax n).cycles_eq (show (ComplexShape.up ℤ).Rel (0 : ℤ) (0 + 1) from rfl),
      Feec.Domain.deRham_maximalComplex_d isOpen_Q 0]
    obtain ⟨h, e⟩ := Feec.Domain.extDerivOp_smooth_mem_maximal_domain (Ω := Q (Fin n)) isOpen_Q
      (k := 0) (w := constFun (⟨∅, by simp⟩ : formIdx n 0))
      (fun _ => contDiff_const) (memLp_constFun measurableSet_Q (isBounded_openCube _ _) _)
      (fun t => Feec.Domain.memLp_of_continuous measurableSet_Q (isBounded_openCube _ _)
        ((extDerivOp ℝ n 0).continuous_apply (Feec.Domain.extDerivOp_isOrderLE 0)
          (fun _ => contDiff_const) t))
    refine mem_ker_iff.2 ⟨⟨_, h⟩, rfl, ?_⟩
    rw [e]
    exact toL2F_eq_zero (fun t y => extDerivOp_apply_const _ t y) _
  · rw [Feec.HilbertComplex.mem_ker_adjoint_prev_iff (Hmax n)
      (show (ComplexShape.up ℤ).Rel (-1 : ℤ) 0 from rfl)]
    have : Subsingleton (L2F ℝ (Q (Fin n)) (formIdx n (-1))) := hlow _ (-1) (by norm_num)
    exact mem_ker_adjoint_of_subsingleton _ _

/-- The constant volume form `dx₁ ∧ ⋯ ∧ dxₙ` on `Q`, in a degree `idx = n` given by its index
set. -/
abbrev volQ {idx : ℤ} (h : ((#(Finset.univ : Finset (Fin n)) : ℕ) : ℤ) = idx) :
    L2F ℝ (Q (Fin n)) (formIdx n idx) :=
  constForm measurableSet_Q (isBounded_openCube _ _) ⟨Finset.univ, h⟩

theorem volQ_mem_harmonic {idx : ℤ} (h : ((#(Finset.univ : Finset (Fin n)) : ℕ) : ℤ) = idx) :
    volQ h ∈ (Hmin n).harmonic idx := by
  obtain ⟨k, rfl⟩ : ∃ k, idx = k + 1 := ⟨idx - 1, by ring⟩
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · have hE : IsEmpty (formIdx n (k + 1 + 1)) := isEmpty_formIdx_of_gt (by
      rw [← Finset.card_univ]; omega)
    have hS : Subsingleton (L2F ℝ (Q (Fin n)) (formIdx n (k + 1 + 1))) := subsingleton_L2F
    rw [(Hmin n).cycles_eq (show (ComplexShape.up ℤ).Rel (k + 1) (k + 1 + 1) from rfl),
      Feec.Domain.deRham_minimalComplex_d isOpen_Q (k + 1)]
    have hd : volQ h ∈ ((extDerivOp ℝ n (k + 1)).minimal (Q (Fin n))).domain := by
      rw [minimal_domain_eq_top_of_isEmpty isOpen_Q]; exact Submodule.mem_top
    exact mem_ker_iff.2 ⟨⟨_, hd⟩, rfl, Subsingleton.elim _ _⟩
  · rw [Feec.HilbertComplex.mem_ker_adjoint_prev_iff (Hmin n)
      (show (ComplexShape.up ℤ).Rel k (k + 1) from rfl)]
    have e1 := Feec.Domain.deRham_minimalComplex_d (𝕜 := ℝ) (n := n) isOpen_Q k
    have e2 : ((Hmin n).d k (k + 1))† = (extDerivOp ℝ n k).formalAdj.maximal (Q (Fin n)) := by
      rw [e1]; exact Feec.Domain.ConstCoeffOp.adjoint_minimal _
    obtain ⟨hm, e⟩ := (extDerivOp ℝ n k).formalAdj.smooth_mem_maximal_domain (Ω := Q (Fin n))
      isOpen_Q (Feec.Domain.formalAdj_extDerivOp_isOrderLE k)
      (ψ := constFun (⟨Finset.univ, h⟩ : formIdx n (k + 1)))
      (fun _ => contDiff_const) (memLp_constFun measurableSet_Q (isBounded_openCube _ _) _)
      (fun r => Feec.Domain.memLp_of_continuous measurableSet_Q (isBounded_openCube _ _)
        ((extDerivOp ℝ n k).formalAdj.continuous_apply
          (Feec.Domain.formalAdj_extDerivOp_isOrderLE k) (fun _ => contDiff_const) r))
    have hm' : volQ h ∈ (((Hmin n).d k (k + 1))†).domain := by rw [e2]; exact hm
    refine mem_ker_iff.2 ⟨⟨_, hm'⟩, rfl, ?_⟩
    rw [apply_eq_of_eq e2 ⟨_, hm'⟩ ⟨_, hm⟩ rfl, e]
    exact toL2F_eq_zero (fun r y => formalAdj_apply_const _ r y) _

theorem harmonic_eq_bot_of_window {H : HilbertComplex ℝ (ComplexShape.up ℤ)
      fun k => L2F ℝ (Q (Fin n)) (formIdx n k)}
    (hf : ∀ a b : Fin (Fintype.card (Fin n) + 1),
      (ComplexShape.up ℤ).Rel ((a : ℕ) : ℤ) ((b : ℕ) : ℤ) →
        (ComplexShape.window (Fintype.card (Fin n) + 1)).Rel a b)
    {k : ℤ} (hW : ∀ (m : ℕ) (hm : m < Fintype.card (Fin n) + 1), (m : ℤ) = k →
      (H.restrict (fun a : Fin (Fintype.card (Fin n) + 1) => ((a : ℕ) : ℤ)) hf).harmonic
        ⟨m, hm⟩ = ⊥) : H.harmonic k = ⊥ := by
  by_cases hout : k < 0 ∨ ((Fintype.card (Fin n) : ℕ) : ℤ) < k
  · have : Subsingleton (L2F ℝ (Q (Fin n)) (formIdx n k)) :=
      hout.elim (hlow _ k) (hhigh _ k)
    exact Submodule.eq_bot_of_subsingleton
  push Not at hout
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hout.1
  have hm : m < Fintype.card (Fin n) + 1 := by omega
  rw [eq_bot_iff, ← hW m hm rfl]
  exact Feec.HilbertComplex.harmonic_le_window H hf ⟨m, hm⟩

/-- **No harmonic forms of `HΛ(Q)` in degrees `≠ 0`.** -/
theorem Hmax_harmonic_eq_bot {k : ℤ} (hk : k ≠ 0) : (Hmax n).harmonic k = ⊥ :=
  harmonic_eq_bot_of_window ι_rel fun m hm e =>
    HQmax_harmonic_eq_bot (a := ⟨m, hm⟩) (by change m ≠ 0; omega)

/-- **No harmonic forms of `H̊Λ(Q)` in degrees `≠ n`.** -/
theorem Hmin_harmonic_eq_bot {k : ℤ} (hk : k ≠ n) : (Hmin n).harmonic k = ⊥ :=
  harmonic_eq_bot_of_window ι_rel fun m hm e =>
    HQmin_harmonic_eq_bot (a := ⟨m, hm⟩) (by
      change m ≠ Fintype.card (Fin n)
      rw [Fintype.card_fin]; omega)

theorem Hmax_harmonic_zero_spec :
    FiniteDimensional ℝ ((Hmax n).harmonic 0) ∧ Module.finrank ℝ ((Hmax n).harmonic 0) ≤ 1 := by
  set a : Fin (Fintype.card (Fin n) + 1) := ⟨0, by omega⟩
  have key : FiniteDimensional ℝ ((Hmax n).harmonic ((a : ℕ) : ℤ)) ∧
      Module.finrank ℝ ((Hmax n).harmonic ((a : ℕ) : ℤ)) ≤ 1 := by
    have hS : ∀ x ∈ (Hmax n).harmonic ((a : ℕ) : ℤ), ∀ m, m ≠ 0 →
        (Jf false (a : ℕ) x : (Fin n → ℤ) → Form ℂ (Fin n) a) m = 0 := fun x hx =>
      mem_HQmax_harmonic_iff.1 (Feec.HilbertComplex.harmonic_le_window (Hmax n) ι_rel a hx)
    have h₀ : ∀ t : {s : Finset (Fin n) // #s = (a : ℕ)}, t = ⟨∅, by simp [a]⟩ := fun t =>
      Subtype.ext (Finset.card_eq_zero.1 t.2)
    exact ⟨finiteDimensional_of_zeroCoeff _ h₀ _ hS, finrank_le_one_of_zeroCoeff _ h₀ _ hS⟩
  have e : ((a : ℕ) : ℤ) = 0 := rfl
  rw [e] at key
  exact key

/-- **The harmonic `0`-forms of `HΛ(Q)` are the constants.** -/
theorem Hmax_harmonic_zero : (Hmax n).harmonic 0 = ℝ ∙ oneQ n := by
  obtain ⟨hfin, hle⟩ := Hmax_harmonic_zero_spec (n := n)
  have hne : oneQ n ≠ 0 := constForm_ne_zero _ _ volume_Q_ne_zero _
  have hpos : Module.finrank ℝ ((Hmax n).harmonic 0) ≠ 0 := fun h0 => by
    have := (Submodule.finrank_eq_zero (S := (Hmax n).harmonic 0)).1 h0
    exact hne (by simpa [this] using oneQ_mem_harmonic (n := n))
  exact eq_span_singleton_of_mem_of_finrank_eq_one (by omega) oneQ_mem_harmonic hne

theorem card_univ_eq (n : ℕ) : ((#(Finset.univ : Finset (Fin n)) : ℕ) : ℤ) = n := by
  simp

theorem Hmin_harmonic_top_spec :
    FiniteDimensional ℝ ((Hmin n).harmonic n) ∧ Module.finrank ℝ ((Hmin n).harmonic n) ≤ 1 := by
  set a : Fin (Fintype.card (Fin n) + 1) := ⟨Fintype.card (Fin n), by omega⟩
  have key : FiniteDimensional ℝ ((Hmin n).harmonic ((a : ℕ) : ℤ)) ∧
      Module.finrank ℝ ((Hmin n).harmonic ((a : ℕ) : ℤ)) ≤ 1 := by
    have hS : ∀ x ∈ (Hmin n).harmonic ((a : ℕ) : ℤ), ∀ m, m ≠ 0 →
        (Jf true (a : ℕ) x : (Fin n → ℤ) → Form ℂ (Fin n) a) m = 0 := fun x hx =>
      mem_HQmin_harmonic_iff.1 (Feec.HilbertComplex.harmonic_le_window (Hmin n) ι_rel a hx)
    have h₀ : ∀ t : {s : Finset (Fin n) // #s = (a : ℕ)},
        t = ⟨Finset.univ, by simp [a]⟩ := fun t =>
      Subtype.ext (Finset.eq_univ_of_card _ t.2)
    exact ⟨finiteDimensional_of_zeroCoeff _ h₀ _ hS, finrank_le_one_of_zeroCoeff _ h₀ _ hS⟩
  have e : ((a : ℕ) : ℤ) = (n : ℤ) := by simp [a]
  rw [e] at key
  exact key

/-- **The harmonic `n`-forms of `H̊Λ(Q)` are the constant volume forms.** -/
theorem Hmin_harmonic_top : (Hmin n).harmonic n = ℝ ∙ volQ (card_univ_eq n) := by
  obtain ⟨hfin, hle⟩ := Hmin_harmonic_top_spec (n := n)
  have hne : volQ (card_univ_eq n) ≠ 0 := constForm_ne_zero _ _ volume_Q_ne_zero _
  have hmem := volQ_mem_harmonic (card_univ_eq n)
  have hpos : Module.finrank ℝ ((Hmin n).harmonic n) ≠ 0 := fun h0 => by
    have := (Submodule.finrank_eq_zero (S := (Hmin n).harmonic n)).1 h0
    exact hne (by simpa [this] using hmem)
  exact eq_span_singleton_of_mem_of_finrank_eq_one (by omega) hmem hne

/-- `j - 1 → j` is an arrow of `ComplexShape.up ℤ`. -/
theorem rel_sub_one (j : ℤ) : (ComplexShape.up ℤ).Rel (j - 1) j := by
  change j - 1 + 1 = j; ring

end Feec.Models.Cube.DeRhamIdent
