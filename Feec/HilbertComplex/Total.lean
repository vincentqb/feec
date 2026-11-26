module

public import Feec.HilbertComplex.HodgeHeat
public import Feec.HilbertComplex.HodgeSolution
public import Feec.ForMathlib.Analysis.Inequalities

/-!
# The total complex of a finite Hilbert complex

A finite Hilbert complex rolls up into the total complex `W →𝐝 W`, `W = ⊕ Wⁱ`, on the shape
`ComplexShape.loop`; under closed range in every degree, its solution operator is the Green operator
`G` of the Hodge Laplacian.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

/-- The shape `() → ()` of a single space with a differential to itself. -/
def ComplexShape.loop : ComplexShape Unit where
  Rel _ _ := True
  next_eq _ _ := rfl
  prev_eq _ _ := rfl

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W) [Fintype ι]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **The total complex** `W →𝐝 W`, `W = ⊕ Wⁱ`, on `ComplexShape.loop`. -/
def total : HilbertComplex 𝕜 ComplexShape.loop (fun _ : Unit => PiLp 2 W) where
  d _ _ := H.totalD
  shape _ _ h := absurd trivial h
  dense _ _ := H.dense_totalD_domain
  closed _ _ := H.isClosed_totalD
  mapsTo _ _ _ x := H.totalD_mapsTo x
  d_comp_d _ _ _ x := H.totalD_comp_totalD x

theorem total_d (i j : Unit) : H.total.d i j = H.totalD := rfl

theorem loop_rel (i j : Unit) : ComplexShape.loop.Rel i j := trivial

theorem harmonic_total : H.total.harmonic () = H.harmonicSum := by
  rw [harmonicSum_eq_inf, ← adjoint_totalD]; rfl

instance [∀ i, FiniteDimensional 𝕜 (H.harmonic i)] : FiniteDimensional 𝕜 (H.total.harmonic ()) := by
  let f : H.total.harmonic () →ₗ[𝕜] ∀ i, H.harmonic i :=
    { toFun := fun x i => ⟨(x : PiLp 2 W) i, H.mem_ker_hodgeLaplacian_iff.1
        ((H.harmonic_total ▸ x.2 : (x : PiLp 2 W) ∈ H.harmonicSum)) i⟩
      map_add' := fun x y => funext fun i => Subtype.ext (by simp)
      map_smul' := fun a x => funext fun i => Subtype.ext (by simp) }
  exact Module.Finite.of_injective f fun x y hxy => Subtype.ext (PiLp.ext fun i =>
    congrArg Subtype.val (congrFun hxy i))

theorem exists_poincare_totalD (hcr : ∀ i, H.ClosedRangeAt i) : ∃ C : ℝ,
    ∀ x : H.totalD.domain, (x : PiLp 2 W) ∈ H.totalD.kerᗮ →
      ‖(x : PiLp 2 W)‖ ≤ C * ‖H.totalD x‖ := by
  classical
  have horth : ∀ i, ∀ x : PiLp 2 W, x ∈ H.totalD.kerᗮ → ∀ q ∈ H.cycles i, ⟪q, x i⟫ = 0 := by
    intro i x hx q hq
    have hs : PiLp.single 2 i q ∈ H.totalD.ker := H.mem_ker_totalD_iff.2 fun j => by
      by_cases hj : j = i
      · subst hj; rwa [PiLp.single_eq_same]
      · rw [PiLp.single_eq_of_ne (p := 2) hj]; exact Submodule.zero_mem _
    have h0 := Submodule.inner_right_of_mem_orthogonal hs hx
    rw [PiLp.inner_apply, Finset.sum_eq_single i (fun j _ hj => by
      rw [PiLp.single_eq_of_ne (p := 2) hj, inner_zero_left]) (by simp),
      PiLp.single_eq_same] at h0
    exact h0
  have hc : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : H.totalD.domain, (x : PiLp 2 W) ∈ H.totalD.kerᗮ →
      ‖(x : PiLp 2 W) i‖ ≤ C * ‖H.totalD x‖ := by
    intro i
    by_cases hi : c.Rel i (c.next i)
    · obtain ⟨cP, hcP, hP⟩ := H.exists_poincare_of_closedRangeAt hi (hcr _)
      refine ⟨cP, by linarith, fun x hx => ?_⟩
      refine (hP ⟨_, x.2 i _⟩ ((Submodule.mem_orthogonal _ _).2 (horth i _ hx))).trans ?_
      exact mul_le_mul_of_nonneg_left (H.norm_d_le_norm_totalD x i _) (by linarith)
    · refine ⟨0, le_rfl, fun x hx => ?_⟩
      have hmem : (x : PiLp 2 W) i ∈ H.cycles i := mem_ker_iff.2
        ⟨⟨_, by rw [H.domain_eq_top_of_not_rel hi]; trivial⟩, rfl, H.apply_eq_zero_of_not_rel hi _⟩
      have := horth i _ hx _ hmem
      rw [inner_self_eq_zero] at this
      rw [this, norm_zero, zero_mul]
  choose C hC0 hC using hc
  refine ⟨∑ i, C i, fun x hx => ?_⟩
  calc _ ≤ ∑ i, ‖(x : PiLp 2 W) i‖ := PiLp.norm_le_sum_norm _
    _ ≤ ∑ i, C i * ‖H.totalD x‖ := Finset.sum_le_sum fun i _ => hC i x hx
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem closedRangeAt_total (hcr : ∀ i, H.ClosedRangeAt i) (i : Unit) : H.total.ClosedRangeAt i :=
  let ⟨_, hP⟩ := H.exists_poincare_totalD hcr
  isClosed_range_of_norm_le H.isClosed_totalD hP

theorem hodgeLaplacian_apply_eq_adjoint (x : H.hodgeLaplacian.domain) :
    ∃ (h₁ : (x : PiLp 2 W) ∈ H.totalD.domain) (h₂ : (x : PiLp 2 W) ∈ H.totalD†.domain)
      (h₃ : (H.totalD ⟨_, h₁⟩ : PiLp 2 W) ∈ H.totalD†.domain)
      (h₄ : (H.totalD† ⟨_, h₂⟩ : PiLp 2 W) ∈ H.totalD.domain),
      H.hodgeLaplacian x = H.totalD ⟨_, h₄⟩ + H.totalD† ⟨_, h₃⟩ := by
  rw [adjoint_totalD]
  exact H.hodgeLaplacian_apply_eq x

theorem hodgeLaplacian_mem_orthogonal_harmonic_total (x : H.hodgeLaplacian.domain) :
    (H.hodgeLaplacian x : PiLp 2 W) ∈ (H.total.harmonic ())ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro q hq
  rw [harmonic_total] at hq
  have hw : q ∈ H.wave.ker := H.mem_ker_wave_iff.2 (H.mem_ker_hodgeLaplacian_iff.1 hq)
  obtain ⟨y, rfl, hy⟩ := mem_ker_iff.1 hw
  rw [H.inner_hodgeLaplacian_left x y, hy, inner_zero_right]

theorem starProjection_harmonic_total_hodgeLaplacian (x : H.hodgeLaplacian.domain) :
    (H.total.harmonic ()).starProjection (H.hodgeLaplacian x) = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).2
    (H.hodgeLaplacian_mem_orthogonal_harmonic_total x)

/-! ### `ker 𝐝†` reduces the Hodge Laplacian -/

theorem exists_hodgeLaplacian_eq_adjoint {x : PiLp 2 W} (h₁ : x ∈ H.totalD.domain)
    (h₂ : x ∈ H.totalD†.domain) (h₃ : (H.totalD ⟨x, h₁⟩ : PiLp 2 W) ∈ H.totalD†.domain)
    (h₄ : (H.totalD† ⟨x, h₂⟩ : PiLp 2 W) ∈ H.totalD.domain) :
    ∃ hx : x ∈ H.hodgeLaplacian.domain,
      H.hodgeLaplacian ⟨x, hx⟩ = H.totalD ⟨_, h₄⟩ + H.totalD† ⟨_, h₃⟩ := by
  revert h₂ h₃ h₄
  rw [adjoint_totalD]
  intro h₂ h₃ h₄
  have hd1 := H.totalD_mapsTo ⟨x, h₁⟩
  have hd2 := H.dual.totalD_mapsTo ⟨x, h₂⟩
  have hL : x ∈ H.wave.sqDomain := ⟨⟨h₁, h₂⟩, sub_mem hd1 h₄, sub_mem h₃ hd2⟩
  refine ⟨hL, ?_⟩
  change -(H.totalD ⟨_, hL.2.1⟩ - H.dual.totalD ⟨_, hL.2.2⟩) = _
  have e1 : H.totalD ⟨_, hL.2.1⟩ = H.totalD ⟨_, hd1⟩ - H.totalD ⟨_, h₄⟩ := by
    rw [← LinearPMap.map_sub]; rfl
  have e2 : H.dual.totalD ⟨_, hL.2.2⟩ = H.dual.totalD ⟨_, h₃⟩ - H.dual.totalD ⟨_, hd2⟩ := by
    rw [← LinearPMap.map_sub]; rfl
  rw [e1, e2, H.totalD_comp_totalD, H.dual.totalD_comp_totalD]
  abel

/-- `ker 𝐝†` has an orthogonal projection. -/
instance : (H.totalD†).ker.HasOrthogonalProjection :=
  hasOrthogonalProjection_ker _ (adjoint_isClosed H.dense_totalD_domain)

/-- **`ker 𝐝†` reduces the Hodge Laplacian** of every finite Hilbert complex. [AFW2010], §3.2 -/
theorem isReducing_hodgeLaplacian_ker_adjoint :
    H.hodgeLaplacian.IsReducing (H.totalD†).ker := by
  set K := (H.totalD†).ker
  have key : ∀ x : H.hodgeLaplacian.domain, ∃ hz : K.starProjection (x : PiLp 2 W) ∈
      H.hodgeLaplacian.domain,
        H.hodgeLaplacian ⟨_, hz⟩ = K.starProjection (H.hodgeLaplacian x) := by
    intro x
    obtain ⟨h₁, h₂, h₃, h₄, hΔ⟩ := H.hodgeLaplacian_apply_eq_adjoint x
    have hy : (x : PiLp 2 W) - K.starProjection x ∈ H.totalD.ker :=
      H.total.orthogonal_ker_adjoint_le_ker () () () (K.sub_starProjection_mem_orthogonal _)
    obtain ⟨y, hyx, hy0⟩ := mem_ker_iff.1 hy
    obtain ⟨z, hzx, hz0⟩ := mem_ker_iff.1 (K.starProjection_apply_mem (x : PiLp 2 W))
    have hz₁ : K.starProjection (x : PiLp 2 W) ∈ H.totalD.domain := by
      rw [show K.starProjection (x : PiLp 2 W) = x - (x - K.starProjection x) by abel, hyx]
      exact sub_mem h₁ y.2
    have hDz : H.totalD ⟨_, hz₁⟩ = H.totalD ⟨_, h₁⟩ := by
      have e : (⟨_, hz₁⟩ : H.totalD.domain) = ⟨_, h₁⟩ - y :=
        Subtype.ext (by rw [Submodule.coe_sub, ← hyx]; abel)
      rw [e, LinearPMap.map_sub, hy0, sub_zero]
    have hz₂ : K.starProjection (x : PiLp 2 W) ∈ H.totalD†.domain := hzx ▸ z.2
    have hA0 : H.totalD† ⟨_, hz₂⟩ = 0 := (congrArg _ (Subtype.ext hzx)).trans hz0
    obtain ⟨hz, hΔz⟩ := H.exists_hodgeLaplacian_eq_adjoint hz₁ hz₂ (by rw [hDz]; exact h₃)
      (by rw [hA0]; exact zero_mem _)
    refine ⟨hz, hΔz.trans ?_⟩
    have hR : ∀ w : H.totalD.domain, K.starProjection (H.totalD w) = 0 := fun w =>
      (Submodule.starProjection_apply_eq_zero_iff K).2 (by
        change _ ∈ (H.totalD†).kerᗮ
        rw [← orthogonal_range_eq_ker_adjoint _ H.dense_totalD_domain]
        exact Submodule.le_orthogonal_orthogonal _ ⟨w, rfl⟩)
    have hA : ∀ w : H.totalD†.domain, K.starProjection (H.totalD† w) = H.totalD† w := fun w =>
      (K.starProjection_eq_self_iff).2 (mem_ker_iff.2
        ⟨⟨_, H.total.adjoint_mapsTo () () () w⟩, rfl, H.total.adjoint_comp_eq_zero () () () w⟩)
    rw [hΔ, _root_.map_add, hR, zero_add, hA, apply_mk_eq_zero _ _ hA0, zero_add]
    exact congrArg _ (Subtype.ext hDz)
  exact ⟨fun x => (key x).1, fun x => (key x).2⟩

theorem single_mem_ker_adjoint_totalD_of_mem_orthogonal [DecidableEq ι] {i : ι} {v : W i}
    (hv : v ∈ (H.boundaries i)ᗮ) : PiLp.single 2 i v ∈ (H.totalD†).ker := by
  rw [← orthogonal_range_eq_ker_adjoint _ H.dense_totalD_domain, Submodule.mem_orthogonal]
  rintro _ ⟨w, rfl⟩
  change ⟪H.totalD w, _⟫ = 0
  rw [PiLp.inner_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp),
    PiLp.single_eq_same, totalD_apply, sum_inner]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : c.Rel j i
  · obtain rfl := c.prev_eq' hj
    exact Submodule.inner_right_of_mem_orthogonal (K := H.boundaries _) ⟨_, rfl⟩ hv
  · rw [H.apply_eq_zero_of_not_rel hj, inner_zero_left]

theorem single_mem_ker_adjoint_totalD [DecidableEq ι] {i : ι} (hi : ∀ j, ¬ c.Rel j i)
    (v : W i) : PiLp.single 2 i v ∈ (H.totalD†).ker :=
  H.single_mem_ker_adjoint_totalD_of_mem_orthogonal <| by
    rintro _ ⟨w, rfl⟩
    change ⟪H.d _ i w, v⟫ = 0
    rw [H.apply_eq_zero_of_not_rel (hi _), inner_zero_left]

/-- The solution `(σ, u, p)` of the mixed problem of the total complex with data `f`. -/
def totalMixedSolution (hcr : ∀ i, H.ClosedRangeAt i) :
    PiLp 2 W →L[𝕜] H.total.MixedSpace () () :=
  H.total.mixedSolution (loop_rel () ()) (loop_rel () ()) (H.closedRangeAt_total hcr ())
    (H.closedRangeAt_total hcr ())

theorem isMixedSolution_totalMixedSolution (hcr : ∀ i, H.ClosedRangeAt i) (f : PiLp 2 W) :
    H.total.IsMixedSolution () () () f (H.totalMixedSolution hcr f).fst
      (H.totalMixedSolution hcr f).snd.fst (H.totalMixedSolution hcr f).snd.snd :=
  H.total.isMixedSolution_mixedSolution _ _ _ _ f

theorem harmonic_totalMixedSolution (hcr : ∀ i, H.ClosedRangeAt i) (f : PiLp 2 W) :
    ((H.totalMixedSolution hcr f).snd.snd : PiLp 2 W) = (H.total.harmonic ()).starProjection f :=
  H.total.harmonic_mixedSolution _ _ _ _ f

/-- **The Green operator** `G` of the Hodge Laplacian on `W = ⊕ Wⁱ`: the solution operator of
the total complex. [AFW2010], §3.2 -/
def greenOp (hcr : ∀ i, H.ClosedRangeAt i) : PiLp 2 W →L[𝕜] PiLp 2 W :=
  H.total.solutionOp (loop_rel () ()) (loop_rel () ()) (H.closedRangeAt_total hcr ())
    (H.closedRangeAt_total hcr ())

theorem greenOp_apply (hcr : ∀ i, H.ClosedRangeAt i) (f : PiLp 2 W) :
    H.greenOp hcr f = H.total.domainIncl () (H.totalMixedSolution hcr f).snd.fst :=
  rfl

/-- **The Hodge decomposition through the Green operator**: `G (Δ x) = x - P_ℌ x` on `D(Δ)`.
[AFW2010], §3.2 -/
theorem greenOp_hodgeLaplacian (hcr : ∀ i, H.ClosedRangeAt i) (x : H.hodgeLaplacian.domain) :
    H.greenOp hcr (H.hodgeLaplacian x) =
      (x : PiLp 2 W) - (H.total.harmonic ()).starProjection (x : PiLp 2 W) := by
  set P := (H.total.harmonic ()).starProjection
  have hp : P x ∈ H.harmonicSum := by
    rw [← harmonic_total]; exact (H.total.harmonic ()).starProjection_apply_mem _
  obtain ⟨p, hp1, hp0⟩ := mem_ker_iff.1 hp
  have hu : (x : PiLp 2 W) - P x ∈ H.hodgeLaplacian.domain := by
    rw [hp1]; exact sub_mem x.2 p.2
  have hΔu : H.hodgeLaplacian ⟨_, hu⟩ = H.hodgeLaplacian x := by
    have e : (⟨_, hu⟩ : H.hodgeLaplacian.domain) = x - p := Subtype.ext (by simp [hp1])
    rw [e, LinearPMap.map_sub, hp0, sub_zero]
  obtain ⟨h₁, h₂, h₃, h₄, he⟩ := H.hodgeLaplacian_apply_eq_adjoint ⟨_, hu⟩
  refine (H.total.eq_solutionOp (loop_rel () ()) (loop_rel () ()) (H.closedRangeAt_total hcr ())
    (H.closedRangeAt_total hcr ()) (Submodule.sub_starProjection_mem_orthogonal _) h₁ h₂ h₃ h₄
    ?_).symm
  change H.totalD ⟨_, h₄⟩ + H.totalD† ⟨_, h₃⟩ = _
  rw [← he, hΔu, H.starProjection_harmonic_total_hodgeLaplacian x, sub_zero]

end Feec.HilbertComplex
