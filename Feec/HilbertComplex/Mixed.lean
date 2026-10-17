module

public import Feec.HilbertComplex.DomainComplex
public import Feec.Variational.BabuskaNecas

/-!
# The mixed Hodge Laplacian

Let `H` be a Hilbert complex and `i → j → k` two consecutive arrows. With the domain spaces
`Vⁱ`, `Vʲ` (graph norms) and the harmonic forms `ℌʲ`, the **mixed formulation of the Hodge
Laplacian** at `j` is: given `f ∈ Wʲ`, find `(σ, u, p) ∈ Vⁱ × Vʲ × ℌʲ` with

  `⟪τ, σ⟫ - ⟪d τ, u⟫ = 0`,   `⟪v, d σ⟫ + ⟪d v, d u⟫ + ⟪v, p⟫ = ⟪v, f⟫`,   `⟪q, u⟫ = 0`

for all `(τ, v, q)`. Equivalently `B x = F_f` for the bounded sesquilinear form `mixedForm` on
`X = Vⁱ × Vʲ × ℌʲ` (an `ℓ²` product). Under closed range at `j` and `k` (Poincaré inequalities
with constant `c_P ≥ 1`), `B` satisfies the inf-sup condition with constant `1 / (16 c_P²)`,
by the test map `(σ, u, p) ↦ (σ - c_P⁻² ρ, u + d σ + p, p - u_ℌ)` where `u = d ρ + u_ℌ + u_⊥`
is the Hodge decomposition of `u` and `ρ ⊥ 𝔷ⁱ`. This is the same proof pattern as the inf-sup
condition of the Hodge wave form (`Feec.Variational.InfSup.of_testMap`).

## Main results

* `mixedForm_apply`, `mixedForm_eq_mixedRHS_iff`: the form and the three equations.
* `exists_testVector`, `infSup_mixedForm`: the inf-sup condition, constant `1 / (16 c_P²)`.
* `mixedForm_sign`, `separatingRight_mixedForm`: `B x y = conj (B (S y) (S x))` for the sign
  flip `S`, hence separation.
* `existsUnique_mixed`, `norm_le_of_mixed`: **well-posedness** with `‖x‖ ≤ 16 c_P² ‖f‖`, over
  `ℝ` and `ℂ`, for every complex and every pair of consecutive arrows.
* `IsMixedSolution.harmonic_eq`, `IsMixedSolution.mem_adjoint_domain`,
  `IsMixedSolution.mem_adjoint_domain_d`: `p = P_ℌ f`, `u ∈ D(d†)` with `d† u = σ`, and
  `d u ∈ D(d†)` with `d† d u = f - p - d σ`; so `u` solves the Hodge Laplacian
  `(d d† + d† d) u = f - P_ℌ f`, `u ⊥ ℌ`: the mixed problem defines its solution operator.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.2, Thm 3.1 (well-posedness of the mixed Hodge Laplacian)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
  (the mixed Hodge Laplacian and its stable discretization)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Thm 4.9
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Prop 4.13 (the same test-function argument for the Hodge wave form)
-/

open scoped InnerProductSpace
open LinearPMap Feec.Variational

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

instance (j : ι) : CompleteSpace (H.harmonic j) := (H.isClosed_harmonic j).completeSpace_coe

/-! ### Domain-space elements -/

/-- At a related pair, `‖v‖²_V = ‖ι v‖² + ‖d i j (ι v)‖²`. -/
theorem norm_sq_domainSpace_of_rel {i j : ι} (h : c.Rel i j) (v : H.domainSpace i) :
    ‖v‖ ^ 2 = ‖H.domainIncl i v‖ ^ 2 + ‖H.d i j (H.domainCoord i j v)‖ ^ 2 := by
  obtain rfl := c.next_eq' h
  exact H.norm_sq_domainSpace i v

theorem domain_eq_of_rel {i j : ι} (h : c.Rel i j) :
    (H.d i j).domain = (H.d i (c.next i)).domain := by
  rw [c.next_eq' h]

/-- A point of `D(d i j)` as a point of the domain space `Vⁱ`, at a related pair. -/
def toDomainSpace {i j : ι} (h : c.Rel i j) (x : (H.d i j).domain) : H.domainSpace i :=
  (H.d i (c.next i)).toGraphSpace ⟨x, H.domain_eq_of_rel h ▸ x.2⟩

@[simp] theorem domainIncl_toDomainSpace {i j : ι} (h : c.Rel i j) (x : (H.d i j).domain) :
    H.domainIncl i (H.toDomainSpace h x) = x := rfl

theorem d_domainCoord_toDomainSpace {i j : ι} (h : c.Rel i j) (x : (H.d i j).domain) :
    H.d i j (H.domainCoord i j (H.toDomainSpace h x)) = H.d i j x :=
  congrArg (H.d i j) (Subtype.ext rfl)

/-- `d j k x = 0` for a cycle `x`. -/
theorem d_eq_zero_of_mem_cycles {j k : ι} {x : W j} (hx : x ∈ H.cycles j)
    (hk : x ∈ (H.d j k).domain) : H.d j k ⟨x, hk⟩ = 0 := by
  rw [H.cycles_eq_iInf] at hx
  obtain ⟨y, hy, hy0⟩ := mem_ker_iff.1 (Submodule.mem_iInf _ |>.1 hx k)
  rw [show (⟨x, hk⟩ : (H.d j k).domain) = y from Subtype.ext hy]
  exact hy0

/-- A harmonic form as a point of the domain space `Vʲ` (its differential vanishes). -/
def harmonicToDomainSpace {j : ι} (p : H.harmonic j) : H.domainSpace j :=
  (H.d j (c.next j)).toGraphSpace ⟨p, H.cycles_le_domain j (H.harmonic_le_cycles j p.2)⟩

@[simp] theorem domainIncl_harmonicToDomainSpace {j : ι} (p : H.harmonic j) :
    H.domainIncl j (H.harmonicToDomainSpace p) = p := rfl

theorem d_domainCoord_harmonicToDomainSpace {j : ι} (k : ι) (p : H.harmonic j) :
    H.d j k (H.domainCoord j k (H.harmonicToDomainSpace p)) = 0 :=
  H.d_eq_zero_of_mem_cycles (H.harmonic_le_cycles j p.2) _

/-! ### The mixed space and the mixed form -/

/-- The space `Vⁱ × Vʲ × ℌʲ` of the mixed Hodge Laplacian at `j` (an `ℓ²` product). -/
abbrev MixedSpace (i j : ι) : Type _ :=
  WithLp 2 (H.domainSpace i × WithLp 2 (H.domainSpace j × H.harmonic j))

variable {H}

/-- The point `(σ, u, p)` of the mixed space. -/
def MixedSpace.mk {i j : ι} (σ : H.domainSpace i) (u : H.domainSpace j) (p : H.harmonic j) :
    H.MixedSpace i j :=
  WithLp.toLp 2 (σ, WithLp.toLp 2 (u, p))

@[simp] theorem MixedSpace.mk_fst {i j : ι} (σ : H.domainSpace i) (u : H.domainSpace j)
    (p : H.harmonic j) : (MixedSpace.mk σ u p).fst = σ := rfl

@[simp] theorem MixedSpace.mk_snd_fst {i j : ι} (σ : H.domainSpace i) (u : H.domainSpace j)
    (p : H.harmonic j) : (MixedSpace.mk σ u p).snd.fst = u := rfl

@[simp] theorem MixedSpace.mk_snd_snd {i j : ι} (σ : H.domainSpace i) (u : H.domainSpace j)
    (p : H.harmonic j) : (MixedSpace.mk σ u p).snd.snd = p := rfl

theorem MixedSpace.eta {i j : ι} (x : H.MixedSpace i j) :
    MixedSpace.mk x.fst x.snd.fst x.snd.snd = x := rfl

/-- `‖(σ, u, p)‖² = ‖σ‖² + ‖u‖² + ‖p‖²`. -/
theorem MixedSpace.norm_sq {i j : ι} (x : H.MixedSpace i j) :
    ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd.fst‖ ^ 2 + ‖(x.snd.snd : W j)‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2, add_assoc]; rfl

variable (H)

/-- `(σ, u, p) ↦ σ ∈ Wⁱ`. -/
def mixedI0 (i j : ι) : H.MixedSpace i j →L[𝕜] W i :=
  (H.domainIncl i).comp (WithLp.fstL 2 𝕜 _ _)

/-- `(σ, u, p) ↦ d σ ∈ Wʲ`. -/
def mixedD0 (i j : ι) : H.MixedSpace i j →L[𝕜] W j :=
  (H.domainIncl j).comp ((H.domainD i j).comp (WithLp.fstL 2 𝕜 _ _))

/-- `(σ, u, p) ↦ u ∈ Wʲ`. -/
def mixedI1 (i j : ι) : H.MixedSpace i j →L[𝕜] W j :=
  (H.domainIncl j).comp ((WithLp.fstL 2 𝕜 _ _).comp (WithLp.sndL 2 𝕜 _ _))

/-- `(σ, u, p) ↦ d u ∈ Wᵏ`. -/
def mixedD1 (i j k : ι) : H.MixedSpace i j →L[𝕜] W k :=
  (H.domainIncl k).comp ((H.domainD j k).comp ((WithLp.fstL 2 𝕜 _ _).comp (WithLp.sndL 2 𝕜 _ _)))

/-- `(σ, u, p) ↦ p ∈ Wʲ`. -/
def mixedI2 (i j : ι) : H.MixedSpace i j →L[𝕜] W j :=
  (H.harmonic j).subtypeL.comp ((WithLp.sndL 2 𝕜 _ _).comp (WithLp.sndL 2 𝕜 _ _))

variable {H}

@[simp] theorem mixedI0_apply {i j : ι} (x : H.MixedSpace i j) :
    H.mixedI0 i j x = H.domainIncl i x.fst := rfl

@[simp] theorem mixedD0_apply {i j : ι} (x : H.MixedSpace i j) :
    H.mixedD0 i j x = H.d i j (H.domainCoord i j x.fst) := rfl

@[simp] theorem mixedI1_apply {i j : ι} (x : H.MixedSpace i j) :
    H.mixedI1 i j x = H.domainIncl j x.snd.fst := rfl

@[simp] theorem mixedD1_apply {i j k : ι} (x : H.MixedSpace i j) :
    H.mixedD1 i j k x = H.d j k (H.domainCoord j k x.snd.fst) := rfl

@[simp] theorem mixedI2_apply {i j : ι} (x : H.MixedSpace i j) :
    H.mixedI2 i j x = (x.snd.snd : W j) := rfl

variable (H)

/-- **The mixed form of the Hodge Laplacian** at `j`:
`B((σ,u,p),(τ,v,q)) = ⟪τ,σ⟫ - ⟪dτ,u⟫ + ⟪v,dσ⟫ + ⟪dv,du⟫ + ⟪v,p⟫ - ⟪q,u⟫`
(linear in `(σ,u,p)`, antilinear in `(τ,v,q)`). -/
def mixedForm (i j k : ι) : H.MixedSpace i j →L[𝕜] H.MixedSpace i j →L⋆[𝕜] 𝕜 :=
  (innerSLFlip 𝕜).bilinearComp (H.mixedI0 i j) (H.mixedI0 i j) -
    (innerSLFlip 𝕜).bilinearComp (H.mixedI1 i j) (H.mixedD0 i j) +
    (innerSLFlip 𝕜).bilinearComp (H.mixedD0 i j) (H.mixedI1 i j) +
    (innerSLFlip 𝕜).bilinearComp (H.mixedD1 i j k) (H.mixedD1 i j k) +
    (innerSLFlip 𝕜).bilinearComp (H.mixedI2 i j) (H.mixedI1 i j) -
    (innerSLFlip 𝕜).bilinearComp (H.mixedI1 i j) (H.mixedI2 i j)

/-- The right-hand side `(τ, v, q) ↦ ⟪v, f⟫`. -/
def mixedRHS (i j : ι) (f : W j) : H.MixedSpace i j →L⋆[𝕜] 𝕜 :=
  (innerSLFlip 𝕜 f).comp (H.mixedI1 i j)

variable {H}

theorem mixedForm_apply {i j k : ι} (x y : H.MixedSpace i j) :
    H.mixedForm i j k x y =
      ⟪H.mixedI0 i j y, H.mixedI0 i j x⟫ - ⟪H.mixedD0 i j y, H.mixedI1 i j x⟫ +
        ⟪H.mixedI1 i j y, H.mixedD0 i j x⟫ + ⟪H.mixedD1 i j k y, H.mixedD1 i j k x⟫ +
        ⟪H.mixedI1 i j y, H.mixedI2 i j x⟫ - ⟪H.mixedI2 i j y, H.mixedI1 i j x⟫ := by
  simp only [mixedForm, _root_.sub_apply, _root_.add_apply, ContinuousLinearMap.bilinearComp_apply,
    innerSLFlip_apply_apply]

theorem mixedRHS_apply {i j : ι} (f : W j) (y : H.MixedSpace i j) :
    H.mixedRHS i j f y = ⟪H.mixedI1 i j y, f⟫ := rfl

/-! ### The inf-sup condition -/

section InfSup

variable {i j k : ι}

/-- Hodge splitting under closed range at `j`: `u = b + h + w` with `b ∈ 𝔅ʲ`, `h ∈ ℌʲ`,
`w ∈ (𝔷ʲ)ᗮ`. -/
theorem exists_hodge_split (hcr : H.ClosedRangeAt j) (u : W j) :
    ∃ b h w, b ∈ H.boundaries j ∧ h ∈ H.harmonic j ∧ w ∈ (H.cycles j)ᗮ ∧ u = b + h + w := by
  have hz : (H.cycles j).starProjection u ∈ H.boundaries j ⊔ H.harmonic j := by
    rw [H.boundaries_sup_harmonic hcr]; exact Submodule.starProjection_apply_mem _ _
  obtain ⟨b, hb, h, hh, hbh⟩ := Submodule.mem_sup.1 hz
  exact ⟨b, h, u - (H.cycles j).starProjection u, hb, hh,
    Submodule.sub_starProjection_mem_orthogonal u, by rw [hbh]; abel⟩

/-- Poincaré preimage: under the Poincaré inequality for `d i j`, every `b ∈ 𝔅ʲ` is `d ρ` with
`ρ ⊥ 𝔷ⁱ` and `‖ρ‖ ≤ c_P ‖b‖`. -/
theorem exists_poincare_preimage (hij : c.Rel i j) {cP : ℝ}
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    {b : W j} (hb : b ∈ H.boundaries j) :
    ∃ ρ : (H.d i j).domain, (ρ : W i) ∈ (H.cycles i)ᗮ ∧ H.d i j ρ = b ∧
      ‖(ρ : W i)‖ ≤ cP * ‖b‖ := by
  rw [H.boundaries_eq hij] at hb
  obtain ⟨ρ', rfl⟩ := hb
  have hq : (H.cycles i).starProjection (ρ' : W i) ∈ (H.d i j).ker := by
    rw [← H.cycles_eq hij]; exact Submodule.starProjection_apply_mem _ _
  obtain ⟨qd, hqd, hq0⟩ := mem_ker_iff.1 hq
  have hρ : ((ρ' - qd : (H.d i j).domain) : W i) =
      (ρ' : W i) - (H.cycles i).starProjection (ρ' : W i) := by
    rw [Submodule.coe_sub, ← hqd]
  have ho : ((ρ' - qd : (H.d i j).domain) : W i) ∈ (H.cycles i)ᗮ :=
    hρ ▸ Submodule.sub_starProjection_mem_orthogonal _
  have hd : H.d i j (ρ' - qd) = H.d i j ρ' := by rw [LinearPMap.map_sub, hq0, sub_zero]
  refine ⟨ρ' - qd, ho, hd, ?_⟩
  have := hPi _ ho
  rw [hd] at this
  exact this

set_option maxHeartbeats 1000000 in
/-- **The test vector of the mixed Hodge Laplacian.** Under the Poincaré inequalities for
`d i j` and `d j k` with constant `c_P ≥ 1`, every `x = (σ, u, p)` has a `y` with
`‖x‖² / (2 c_P²) ≤ re B(x, y)` and `‖y‖ ≤ 8 ‖x‖`. -/
theorem exists_testVector (hij : c.Rel i j) (hjk : c.Rel j k) {cP : ℝ} (hcP : 1 ≤ cP)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (x : H.MixedSpace i j) :
    ∃ y, 1 / (2 * cP ^ 2) * ‖x‖ ^ 2 ≤ RCLike.re (H.mixedForm i j k x y) ∧ ‖y‖ ≤ 8 * ‖x‖ := by
  have hcr : H.ClosedRangeAt j := (H.closedRangeAt_iff_poincare_of_rel hij).2 ⟨cP, hPi⟩
  rw [← MixedSpace.eta x]
  generalize x.fst = σ, x.snd.fst = u, x.snd.snd = p
  -- the Hodge splitting of `u`
  obtain ⟨b, h, w, hb, hh, hw, hu⟩ := H.exists_hodge_split hcr (H.domainIncl j u)
  have hzc : b + h ∈ H.cycles j :=
    add_mem (H.boundaries_le_cycles j hb) (H.harmonic_le_cycles j hh)
  have hzD : b + h ∈ (H.d j k).domain := H.domain_next_le j k (H.cycles_le_domain j hzc)
  have hwD : w ∈ (H.d j k).domain := by
    have : w = H.domainIncl j u - (b + h) := by rw [hu, add_sub_cancel_left]
    rw [this]; exact Submodule.sub_mem _ (H.domainCoord j k u).2 hzD
  have hdw : H.d j k ⟨w, hwD⟩ = H.d j k (H.domainCoord j k u) := by
    have e : (⟨w, hwD⟩ : (H.d j k).domain) = H.domainCoord j k u - ⟨b + h, hzD⟩ :=
      Subtype.ext (by
        rw [Submodule.coe_sub, coe_domainCoord, hu, Submodule.coe_mk, add_sub_cancel_left])
    rw [e, LinearPMap.map_sub, H.d_eq_zero_of_mem_cycles hzc, sub_zero]
  have hwn : ‖w‖ ≤ cP * ‖H.d j k (H.domainCoord j k u)‖ := hdw ▸ hPj ⟨w, hwD⟩ hw
  -- the Poincaré preimage of `b`
  obtain ⟨ρ, -, hdρ, hρn⟩ := H.exists_poincare_preimage hij hPi hb
  -- the test vector
  set a : ℝ := 1 / cP ^ 2 with ha
  have hcP0 : 0 < cP := one_pos.trans_le hcP
  have haP : a * cP ^ 2 = 1 := by rw [ha]; field_simp
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by positivity)]; nlinarith
  set ρV := H.toDomainSpace hij ρ
  set pV := H.harmonicToDomainSpace p
  set hV : H.harmonic j := ⟨h, hh⟩
  -- abbreviations
  set σW := H.domainIncl i σ
  set dσ := H.d i j (H.domainCoord i j σ)
  set uW := H.domainIncl j u
  set du := H.d j k (H.domainCoord j k u)
  set pW : W j := (p : W j)
  have hdσB : dσ ∈ H.boundaries j := by rw [H.boundaries_eq hij]; exact ⟨_, rfl⟩
  have hpH : pW ∈ H.harmonic j := p.2
  -- orthogonality relations
  have hbh : ⟪b, h⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hb (H.mem_harmonic_iff.1 hh).2
  have hbw : ⟪b, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal (H.boundaries_le_cycles j hb) hw
  have hhw : ⟪h, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal (H.harmonic_le_cycles j hh) hw
  have hpdσ : ⟪pW, dσ⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hdσB (H.mem_harmonic_iff.1 hpH).2
  have hdσp : ⟪dσ, pW⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hdσB (H.mem_harmonic_iff.1 hpH).2
  have hhb : ⟪h, b⟫ = 0 := by rw [← inner_conj_symm, hbh, _root_.map_zero]
  have hwb : ⟪w, b⟫ = 0 := by rw [← inner_conj_symm, hbw, _root_.map_zero]
  have hwh : ⟪w, h⟫ = 0 := by rw [← inner_conj_symm, hhw, _root_.map_zero]
  have hbu : RCLike.re ⟪b, uW⟫ = ‖b‖ ^ 2 := by
    rw [hu, inner_add_right, inner_add_right, hbh, hbw, add_zero, add_zero,
      inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hhu : RCLike.re ⟪h, uW⟫ = ‖h‖ ^ 2 := by
    rw [hu, inner_add_right, inner_add_right, hhb, hhw, zero_add, add_zero,
      inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have huN : ‖uW‖ ^ 2 = ‖b‖ ^ 2 + ‖h‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [hu, @norm_add_sq 𝕜, @norm_add_sq 𝕜 _ _ _ _ b h, inner_add_left, hbw, hhw, hbh]
    simp
  -- components of `x` and `y`
  have e0 : H.mixedI0 i j (MixedSpace.mk (σ - (a : 𝕜) • ρV) (u + H.domainD i j σ + pV) (p - hV))
      = σW - (a : 𝕜) • (ρ : W i) := by
    simp only [mixedI0_apply, MixedSpace.mk_fst, _root_.map_sub, _root_.map_smul]; rfl
  have e1 : H.mixedD0 i j (MixedSpace.mk (σ - (a : 𝕜) • ρV) (u + H.domainD i j σ + pV) (p - hV))
      = dσ - (a : 𝕜) • b := by
    show H.domainIncl j (H.domainD i j (σ - (a : 𝕜) • ρV)) = _
    rw [_root_.map_sub, _root_.map_smul, _root_.map_sub, _root_.map_smul, domainIncl_domainD,
      domainIncl_domainD,
      d_domainCoord_toDomainSpace, hdρ]
  have e2 : H.mixedI1 i j (MixedSpace.mk (σ - (a : 𝕜) • ρV) (u + H.domainD i j σ + pV) (p - hV))
      = uW + dσ + pW := by
    simp only [mixedI1_apply, MixedSpace.mk_snd_fst, _root_.map_add]; rfl
  have e3 : H.mixedD1 i j k (MixedSpace.mk (σ - (a : 𝕜) • ρV) (u + H.domainD i j σ + pV) (p - hV))
      = du := by
    show H.domainIncl k (H.domainD j k (u + H.domainD i j σ + pV)) = _
    rw [_root_.map_add, _root_.map_add, _root_.map_add, _root_.map_add, domainIncl_domainD, domainIncl_domainD,
      domainIncl_domainD, d_domainCoord_domainD, d_domainCoord_harmonicToDomainSpace, add_zero,
      add_zero]
  have e4 : H.mixedI2 i j (MixedSpace.mk (σ - (a : 𝕜) • ρV) (u + H.domainD i j σ + pV) (p - hV))
      = pW - h := rfl
  have x0 : H.mixedI0 i j (MixedSpace.mk σ u p) = σW := rfl
  have x1 : H.mixedD0 i j (MixedSpace.mk σ u p) = dσ := rfl
  have x2 : H.mixedI1 i j (MixedSpace.mk σ u p) = uW := rfl
  have x3 : H.mixedD1 i j k (MixedSpace.mk σ u p) = du := rfl
  have x4 : H.mixedI2 i j (MixedSpace.mk σ u p) = pW := rfl
  have hxN : ‖MixedSpace.mk σ u p‖ ^ 2 = ‖σW‖ ^ 2 + ‖dσ‖ ^ 2 + (‖uW‖ ^ 2 + ‖du‖ ^ 2) + ‖pW‖ ^ 2 := by
    rw [MixedSpace.norm_sq, MixedSpace.mk_fst, MixedSpace.mk_snd_fst, MixedSpace.mk_snd_snd,
      H.norm_sq_domainSpace_of_rel hij, H.norm_sq_domainSpace_of_rel hjk]
  refine ⟨MixedSpace.mk (σ - (a : 𝕜) • ρV) (u + H.domainD i j σ + pV) (p - hV), ?_, ?_⟩
  · rw [mixedForm_apply, e0, e1, e2, e3, e4, x0, x1, x2, x3, x4]
    have T1 : RCLike.re ⟪σW - (a : 𝕜) • (ρ : W i), σW⟫ = ‖σW‖ ^ 2 - a * RCLike.re ⟪(ρ : W i), σW⟫ := by
      rw [inner_sub_left, inner_smul_real_left, _root_.map_sub, RCLike.smul_re, inner_self_eq_norm_sq]
    have T2 : RCLike.re ⟪dσ - (a : 𝕜) • b, uW⟫ = RCLike.re ⟪dσ, uW⟫ - a * ‖b‖ ^ 2 := by
      rw [inner_sub_left, inner_smul_real_left, _root_.map_sub, RCLike.smul_re, hbu]
    have T3 : RCLike.re ⟪uW + dσ + pW, dσ⟫ = RCLike.re ⟪uW, dσ⟫ + ‖dσ‖ ^ 2 := by
      rw [inner_add_left, inner_add_left, hpdσ, add_zero, _root_.map_add, inner_self_eq_norm_sq]
    have T4 : RCLike.re ⟪du, du⟫ = ‖du‖ ^ 2 := inner_self_eq_norm_sq _
    have T5 : RCLike.re ⟪uW + dσ + pW, pW⟫ = RCLike.re ⟪uW, pW⟫ + ‖pW‖ ^ 2 := by
      rw [inner_add_left, inner_add_left, hdσp, add_zero, _root_.map_add, inner_self_eq_norm_sq]
    have T6 : RCLike.re ⟪pW - h, uW⟫ = RCLike.re ⟪pW, uW⟫ - ‖h‖ ^ 2 := by
      rw [inner_sub_left, _root_.map_sub, hhu]
    have S1 := inner_re_symm (𝕜 := 𝕜) uW dσ
    have S2 := inner_re_symm (𝕜 := 𝕜) uW pW
    simp only [_root_.map_sub, _root_.map_add, T1, T2, T3, T4, T5, T6, S1, S2]
    -- the estimate
    have hre : RCLike.re ⟪(ρ : W i), σW⟫ ≤ cP * ‖b‖ * ‖σW‖ :=
      (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans (by gcongr))
    have h1 : a * RCLike.re ⟪(ρ : W i), σW⟫ ≤ a * (cP * ‖b‖ * ‖σW‖) :=
      mul_le_mul_of_nonneg_left hre ha0.le
    have h2 : a * (cP * ‖b‖ * ‖σW‖) ≤ ‖σW‖ ^ 2 / 2 + a * ‖b‖ ^ 2 / 2 := by
      have hsq := sq_nonneg (‖σW‖ - a * cP * ‖b‖)
      have e : a ^ 2 * cP ^ 2 * ‖b‖ ^ 2 = a * ‖b‖ ^ 2 := by
        rw [sq a, mul_assoc a a, haP, mul_one]
      linarith only [hsq, e]
    have h3 : a * ‖w‖ ^ 2 ≤ ‖du‖ ^ 2 := by
      have hw2 : ‖w‖ ^ 2 ≤ cP ^ 2 * ‖du‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg w) hwn 2
      calc a * ‖w‖ ^ 2 ≤ a * (cP ^ 2 * ‖du‖ ^ 2) := mul_le_mul_of_nonneg_left hw2 ha0.le
        _ = ‖du‖ ^ 2 := by rw [← mul_assoc, haP, one_mul]
    have hc : 1 / (2 * cP ^ 2) = a / 2 := by rw [ha]; field_simp
    rw [hc, hxN, huN]
    have p1 := mul_nonneg (sub_nonneg.2 ha1) (sq_nonneg ‖σW‖)
    have p2 := mul_nonneg (sub_nonneg.2 ha1) (sq_nonneg ‖dσ‖)
    have p3 := mul_nonneg (sub_nonneg.2 ha1) (sq_nonneg ‖du‖)
    have p4 := mul_nonneg (sub_nonneg.2 ha1) (sq_nonneg ‖pW‖)
    have p5 := mul_nonneg (sub_nonneg.2 ha1) (sq_nonneg ‖h‖)
    have p6 := mul_nonneg ha0.le (sq_nonneg ‖b‖)
    linarith only [h1, h2, h3, p1, p2, p3, p4, p5, p6, sq_nonneg ‖dσ‖, sq_nonneg ‖du‖,
      sq_nonneg ‖pW‖, sq_nonneg ‖h‖, sq_nonneg ‖σW‖]
  · -- the bound on the test vector
    have hσx : ‖σ‖ ≤ ‖MixedSpace.mk σ u p‖ := WithLp.norm_fst_le (x := MixedSpace.mk σ u p)
    have hux : ‖u‖ ≤ ‖MixedSpace.mk σ u p‖ :=
      (WithLp.norm_fst_le (x := (MixedSpace.mk σ u p).snd)).trans
        (WithLp.norm_snd_le (x := MixedSpace.mk σ u p))
    have hpx : ‖pW‖ ≤ ‖MixedSpace.mk σ u p‖ :=
      (WithLp.norm_snd_le (x := (MixedSpace.mk σ u p).snd)).trans
        (WithLp.norm_snd_le (x := MixedSpace.mk σ u p))
    have huW : ‖uW‖ ≤ ‖u‖ := H.norm_domainIncl_le j u
    have hbn : ‖b‖ ≤ ‖uW‖ := (abs_le_of_sq_le_sq' (by
      linarith only [huN, sq_nonneg ‖h‖, sq_nonneg ‖w‖]) (norm_nonneg _)).2
    have hhn : ‖h‖ ≤ ‖uW‖ := (abs_le_of_sq_le_sq' (by
      linarith only [huN, sq_nonneg ‖b‖, sq_nonneg ‖w‖]) (norm_nonneg _)).2
    -- `‖ρV‖² = ‖ρ‖² + ‖b‖²`
    have hρV : ‖ρV‖ ^ 2 = ‖(ρ : W i)‖ ^ 2 + ‖b‖ ^ 2 := by
      rw [H.norm_sq_domainSpace_of_rel hij, domainIncl_toDomainSpace, d_domainCoord_toDomainSpace,
        hdρ]
    have haρ : a * ‖ρV‖ ≤ 2 * ‖b‖ := by
      have hsq : (a * ‖ρV‖) ^ 2 ≤ (2 * ‖b‖) ^ 2 := by
        have hρ2 : ‖(ρ : W i)‖ ^ 2 ≤ cP ^ 2 * ‖b‖ ^ 2 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hρn 2
        have q1 : a ^ 2 * ‖(ρ : W i)‖ ^ 2 ≤ a ^ 2 * (cP ^ 2 * ‖b‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hρ2 (sq_nonneg a)
        have e : a ^ 2 * (cP ^ 2 * ‖b‖ ^ 2) = a * ‖b‖ ^ 2 := by
          rw [← mul_assoc, sq a, mul_assoc a a, haP, mul_one]
        have q2 : a * ‖b‖ ^ 2 ≤ 1 * ‖b‖ ^ 2 := mul_le_mul_of_nonneg_right ha1 (sq_nonneg _)
        have ha2 : a ^ 2 ≤ 1 := by rw [sq]; nlinarith
        have q3 : a ^ 2 * ‖b‖ ^ 2 ≤ 1 * ‖b‖ ^ 2 := mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)
        rw [mul_pow, hρV, mul_add, mul_pow]
        linarith only [q1, e, q2, q3, sq_nonneg ‖b‖]
      exact (abs_le_of_sq_le_sq' hsq (by positivity)).2
    have hτ : ‖σ - (a : 𝕜) • ρV‖ ≤ ‖σ‖ + 2 * ‖b‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, RCLike.norm_ofReal, abs_of_pos ha0]; linarith
    have hDσ : ‖H.domainD i j σ‖ ≤ ‖σ‖ := by
      have e : ‖H.domainD i j σ‖ ^ 2 = ‖dσ‖ ^ 2 := by
        rw [H.norm_sq_domainSpace_of_rel hjk, domainIncl_domainD, d_domainCoord_domainD,
          norm_zero]; ring
      rw [(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e]
      exact H.norm_d_domainCoord_le i j σ
    have hpV : ‖pV‖ = ‖pW‖ := by
      have e : ‖pV‖ ^ 2 = ‖pW‖ ^ 2 := by
        rw [H.norm_sq_domainSpace_of_rel hjk, domainIncl_harmonicToDomainSpace,
          d_domainCoord_harmonicToDomainSpace, norm_zero]; ring
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e
    have hv : ‖u + H.domainD i j σ + pV‖ ≤ ‖u‖ + ‖σ‖ + ‖pW‖ :=
      (norm_add₃_le).trans (by rw [hpV]; linarith)
    have hq : ‖((p - hV : H.harmonic j) : W j)‖ ≤ ‖pW‖ + ‖h‖ := norm_sub_le _ _
    have hyN := MixedSpace.norm_sq (MixedSpace.mk (σ - (a : 𝕜) • ρV) (u + H.domainD i j σ + pV) (p - hV))
    rw [MixedSpace.mk_fst, MixedSpace.mk_snd_fst, MixedSpace.mk_snd_snd] at hyN
    have hS : ‖MixedSpace.mk (σ - (a : 𝕜) • ρV) (u + H.domainD i j σ + pV) (p - hV)‖ ^ 2 ≤
        (8 * ‖MixedSpace.mk σ u p‖) ^ 2 := by
      rw [hyN]
      have n1 := norm_nonneg (σ - (a : 𝕜) • ρV)
      have n2 := norm_nonneg (u + H.domainD i j σ + pV)
      have n3 := norm_nonneg ((p - hV : H.harmonic j) : W j)
      have hX := norm_nonneg (MixedSpace.mk σ u p)
      have b1 : ‖σ - (a : 𝕜) • ρV‖ ≤ 3 * ‖MixedSpace.mk σ u p‖ := by linarith
      have b2 : ‖u + H.domainD i j σ + pV‖ ≤ 3 * ‖MixedSpace.mk σ u p‖ := by linarith
      have b3 : ‖((p - hV : H.harmonic j) : W j)‖ ≤ 2 * ‖MixedSpace.mk σ u p‖ := by linarith
      have c1 := pow_le_pow_left₀ n1 b1 2
      have c2 := pow_le_pow_left₀ n2 b2 2
      have c3 := pow_le_pow_left₀ n3 b3 2
      rw [mul_pow] at c1 c2 c3 ⊢
      linarith only [c1, c2, c3, sq_nonneg ‖MixedSpace.mk σ u p‖]
    exact (abs_le_of_sq_le_sq' hS (by positivity)).2

/-- **Inf-sup condition for the mixed Hodge Laplacian**, with constant `1 / (16 c_P²)`, under the
Poincaré inequalities for `d i j` and `d j k` with constant `c_P ≥ 1`. See [AFW2010], Thm 3.1;
its discrete counterpart, uniform in the subcomplex (`Subcomplex.CochainProjection.infSup_mixedForm`),
is the FEEC stability recalled as well known in [QuennevilleBelair2015], §4.6, citing [AFW2006],
[AFW2010]. -/
theorem infSup_mixedForm (hij : c.Rel i j) (hjk : c.Rel j k) {cP : ℝ} (hcP : 1 ≤ cP)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖) :
    InfSup (H.mixedForm i j k) (1 / (16 * cP ^ 2)) := by
  choose T hT using H.exists_testVector hij hjk hcP hPi hPj
  have hcP0 : 0 < cP := one_pos.trans_le hcP
  have h := InfSup.of_testMap (B := H.mixedForm i j k) T (c := 1 / (2 * cP ^ 2)) (M := 8)
    (by positivity) (by norm_num) (fun x => (hT x).2) (fun x => (hT x).1)
  refine h.mono (by positivity) (le_of_eq ?_)
  field_simp
  ring

/-- The sign flip `(σ, u, p) ↦ (-σ, u, -p)`. -/
def MixedSpace.sign (x : H.MixedSpace i j) : H.MixedSpace i j :=
  MixedSpace.mk (-x.fst) x.snd.fst (-x.snd.snd)

@[simp] theorem MixedSpace.sign_sign (x : H.MixedSpace i j) : (x.sign).sign = x := by
  simp only [MixedSpace.sign, MixedSpace.mk_fst, MixedSpace.mk_snd_fst, MixedSpace.mk_snd_snd,
    neg_neg]
  rfl

theorem MixedSpace.norm_sign (x : H.MixedSpace i j) : ‖x.sign‖ = ‖x‖ := by
  have h : ‖x.sign‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [MixedSpace.norm_sq, MixedSpace.norm_sq]
    simp [MixedSpace.sign]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- **Symmetry of the mixed form**: `B x y = conj (B (S y) (S x))` for the sign flip `S`. -/
theorem mixedForm_sign (x y : H.MixedSpace i j) :
    H.mixedForm i j k x y = starRingEnd 𝕜 (H.mixedForm i j k y.sign x.sign) := by
  have s0 : ∀ z : H.MixedSpace i j, H.mixedI0 i j z.sign = -H.mixedI0 i j z := fun z => by
    simp [MixedSpace.sign]
  have s1 : ∀ z : H.MixedSpace i j, H.mixedD0 i j z.sign = -H.mixedD0 i j z := fun z => by
    simp [MixedSpace.sign, LinearPMap.map_neg]
  have s2 : ∀ z : H.MixedSpace i j, H.mixedI1 i j z.sign = H.mixedI1 i j z := fun z => by
    simp [MixedSpace.sign]
  have s3 : ∀ z : H.MixedSpace i j, H.mixedD1 i j k z.sign = H.mixedD1 i j k z := fun z => by
    simp [MixedSpace.sign]
  have s4 : ∀ z : H.MixedSpace i j, H.mixedI2 i j z.sign = -H.mixedI2 i j z := fun z => by
    simp [MixedSpace.sign]
  rw [mixedForm_apply, mixedForm_apply, s0, s0, s1, s1, s2, s2, s3, s3, s4, s4]
  simp only [inner_neg_left, inner_neg_right, neg_neg, _root_.map_sub, _root_.map_add,
    _root_.map_neg, inner_conj_symm]
  ring

/-- **Separation for the mixed form**, from the inf-sup test vectors and the symmetry. -/
theorem separatingRight_mixedForm (hij : c.Rel i j) (hjk : c.Rel j k) {cP : ℝ} (hcP : 1 ≤ cP)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖) :
    SeparatingRight (H.mixedForm i j k) := by
  intro w hw
  obtain ⟨y, hy, -⟩ := H.exists_testVector hij hjk hcP hPi hPj w.sign
  have h0 : H.mixedForm i j k w.sign y = 0 := by
    rw [mixedForm_sign, MixedSpace.sign_sign, hw, _root_.map_zero]
  rw [h0, _root_.map_zero] at hy
  have hcP0 : 0 < cP := one_pos.trans_le hcP
  have : ‖w.sign‖ ^ 2 ≤ 0 := by
    have hc : 0 < 1 / (2 * cP ^ 2) := by positivity
    nlinarith [sq_nonneg ‖w.sign‖]
  rw [MixedSpace.norm_sign] at this
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg w])

/-- `‖(τ, v, q) ↦ ⟪v, f⟫‖ ≤ ‖f‖`. -/
theorem norm_mixedRHS_le (f : W j) : ‖H.mixedRHS i j f‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
  rw [mixedRHS_apply, mul_comm]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [mixedI1_apply]
  exact (H.norm_domainIncl_le j _).trans ((WithLp.norm_fst_le (x := y.snd)).trans
    (WithLp.norm_snd_le (x := y)))

/-- **Well-posedness of the mixed Hodge Laplacian**: under the Poincaré inequalities for `d i j`
and `d j k` (closed range at `j` and `k`), for every `f ∈ Wʲ` the mixed problem `B x = F_f` has a
unique solution. Over `ℝ` and `ℂ`, for every complex and every two consecutive arrows.
See [AFW2010], Thm 3.1; cf. [AFW2006]. -/
theorem existsUnique_mixed (hij : c.Rel i j) (hjk : c.Rel j k) {cP : ℝ} (hcP : 1 ≤ cP)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (f : W j) : ∃! x, H.mixedForm i j k x = H.mixedRHS i j f :=
  existsUnique_apply_eq (H.infSup_mixedForm hij hjk hcP hPi hPj)
    (H.separatingRight_mixedForm hij hjk hcP hPi hPj) _

/-- **Stability of the mixed Hodge Laplacian**: `‖(σ, u, p)‖ ≤ 16 c_P² ‖f‖`. See [AFW2010],
Thm 3.1. -/
theorem norm_le_of_mixed (hij : c.Rel i j) (hjk : c.Rel j k) {cP : ℝ} (hcP : 1 ≤ cP)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    {f : W j} {x : H.MixedSpace i j} (hx : H.mixedForm i j k x = H.mixedRHS i j f) :
    ‖x‖ ≤ 16 * cP ^ 2 * ‖f‖ := by
  have h := (H.infSup_mixedForm hij hjk hcP hPi hPj).norm_le_of_apply_eq hx
  have hcP0 : 0 < cP := one_pos.trans_le hcP
  rw [one_div, inv_inv] at h
  exact h.trans (mul_le_mul_of_nonneg_left (H.norm_mixedRHS_le f) (by positivity))

/-! ### The three equations -/

/-- `(σ, u, p)` solves the **mixed Hodge Laplacian** with data `f`:
`⟪τ, σ⟫ - ⟪dτ, u⟫ = 0`, `⟪v, dσ⟫ + ⟪dv, du⟫ + ⟪v, p⟫ = ⟪v, f⟫`, `⟪q, u⟫ = 0`. -/
structure IsMixedSolution (i j k : ι) (f : W j) (σ : H.domainSpace i) (u : H.domainSpace j)
    (p : H.harmonic j) : Prop where
  fst : ∀ τ : H.domainSpace i,
    ⟪H.domainIncl i τ, H.domainIncl i σ⟫ - ⟪H.d i j (H.domainCoord i j τ), H.domainIncl j u⟫ = 0
  snd : ∀ v : H.domainSpace j,
    ⟪H.domainIncl j v, H.d i j (H.domainCoord i j σ)⟫ +
      ⟪H.d j k (H.domainCoord j k v), H.d j k (H.domainCoord j k u)⟫ +
      ⟪H.domainIncl j v, (p : W j)⟫ = ⟪H.domainIncl j v, f⟫
  harm : ∀ q ∈ H.harmonic j, ⟪q, H.domainIncl j u⟫ = 0

theorem mixedForm_eq_mixedRHS_iff {f : W j} {σ : H.domainSpace i} {u : H.domainSpace j}
    {p : H.harmonic j} :
    H.mixedForm i j k (MixedSpace.mk σ u p) = H.mixedRHS i j f ↔
      H.IsMixedSolution i j k f σ u p := by
  constructor
  · intro h
    refine ⟨fun τ => ?_, fun v => ?_, fun q hq => ?_⟩
    · have e := congrArg (fun F => F (MixedSpace.mk τ 0 0)) h
      simp only [mixedForm_apply, mixedRHS_apply, mixedI0_apply, mixedD0_apply, mixedI1_apply,
        mixedD1_apply, mixedI2_apply, MixedSpace.mk_fst, MixedSpace.mk_snd_fst,
        MixedSpace.mk_snd_snd, _root_.map_zero, LinearPMap.map_zero, inner_zero_left,
        ZeroMemClass.coe_zero, add_zero, sub_zero] at e
      exact e
    · have e := congrArg (fun F => F (MixedSpace.mk 0 v 0)) h
      simp only [mixedForm_apply, mixedRHS_apply, mixedI0_apply, mixedD0_apply, mixedI1_apply,
        mixedD1_apply, mixedI2_apply, MixedSpace.mk_fst, MixedSpace.mk_snd_fst,
        MixedSpace.mk_snd_snd, _root_.map_zero, LinearPMap.map_zero, inner_zero_left,
        ZeroMemClass.coe_zero, sub_zero, zero_add] at e
      exact e
    · have e := congrArg (fun F => F (MixedSpace.mk 0 0 ⟨q, hq⟩)) h
      simp only [mixedForm_apply, mixedRHS_apply, mixedI0_apply, mixedD0_apply, mixedI1_apply,
        mixedD1_apply, mixedI2_apply, MixedSpace.mk_fst, MixedSpace.mk_snd_fst,
        MixedSpace.mk_snd_snd, _root_.map_zero, LinearPMap.map_zero, inner_zero_left,
        zero_sub, sub_zero, add_zero] at e
      simpa using e
  · intro hs
    refine ContinuousLinearMap.ext fun y => ?_
    rw [mixedForm_apply, mixedRHS_apply]
    have e1 := hs.fst y.fst
    have e2 := hs.snd y.snd.fst
    have e3 := hs.harm _ y.snd.snd.2
    simp only [mixedI0_apply, mixedD0_apply, mixedI1_apply, mixedD1_apply, mixedI2_apply,
      MixedSpace.mk_fst, MixedSpace.mk_snd_fst, MixedSpace.mk_snd_snd]
    linear_combination e1 + e2 - e3

/-- **Well-posedness of the mixed Hodge Laplacian**, in equation form. -/
theorem existsUnique_isMixedSolution (hij : c.Rel i j) (hjk : c.Rel j k) {cP : ℝ} (hcP : 1 ≤ cP)
    (hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖)
    (f : W j) : ∃! x : H.MixedSpace i j, H.IsMixedSolution i j k f x.fst x.snd.fst x.snd.snd := by
  obtain ⟨x, hx, hu⟩ := H.existsUnique_mixed hij hjk hcP hPi hPj f
  refine ⟨x, mixedForm_eq_mixedRHS_iff.1 hx, fun y hy => hu y ?_⟩
  exact mixedForm_eq_mixedRHS_iff.2 hy

/-- The harmonic part of the solution is the harmonic projection of the data: `p = P_ℌ f`. -/
theorem IsMixedSolution.harmonic_eq (hij : c.Rel i j) {f : W j} {σ : H.domainSpace i}
    {u : H.domainSpace j} {p : H.harmonic j} (hs : H.IsMixedSolution i j k f σ u p) :
    (H.harmonic j).starProjection f = p := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero p.2 fun q hq => ?_
  have e := hs.snd (H.harmonicToDomainSpace ⟨q, hq⟩)
  rw [domainIncl_harmonicToDomainSpace, d_domainCoord_harmonicToDomainSpace, inner_zero_left,
    add_zero] at e
  have hdσ : H.d i j (H.domainCoord i j σ) ∈ H.boundaries j := by
    rw [H.boundaries_eq hij]; exact ⟨_, rfl⟩
  have h0 : ⟪q, H.d i j (H.domainCoord i j σ)⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hdσ (H.mem_harmonic_iff.1 hq).2
  rw [h0, zero_add] at e
  rw [inner_sub_left, ← inner_conj_symm f, ← inner_conj_symm (p : W j), ← e, sub_self]

/-- The first equation says `u ∈ D(d†)` with `d† u = σ` (here `d = d i j`). -/
theorem IsMixedSolution.mem_adjoint_domain (hij : c.Rel i j) {f : W j} {σ : H.domainSpace i}
    {u : H.domainSpace j} {p : H.harmonic j} (hs : H.IsMixedSolution i j k f σ u p) :
    ∃ h : H.domainIncl j u ∈ (H.d i j)†.domain,
      (H.d i j)† ⟨H.domainIncl j u, h⟩ = H.domainIncl i σ := by
  have key : ∀ x : (H.d i j).domain,
      ⟪H.domainIncl i σ, (x : W i)⟫ = ⟪H.domainIncl j u, H.d i j x⟫ := fun x => by
    have e := hs.fst (H.toDomainSpace hij x)
    rw [domainIncl_toDomainSpace, d_domainCoord_toDomainSpace, sub_eq_zero] at e
    rw [← inner_conj_symm, e, inner_conj_symm]
  have hmem := mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, adjoint_apply_eq (H.dense i j) ⟨_, hmem⟩ key⟩

/-- The second equation says `d u ∈ D(d†)` with `d† d u = f - p - d σ` (here `d = d j k`); with
`IsMixedSolution.mem_adjoint_domain` this is the strong form `(d d† + d† d) u = f - P_ℌ f` of the
Hodge Laplacian. -/
theorem IsMixedSolution.mem_adjoint_domain_d (hjk : c.Rel j k) {f : W j} {σ : H.domainSpace i}
    {u : H.domainSpace j} {p : H.harmonic j} (hs : H.IsMixedSolution i j k f σ u p) :
    ∃ h : H.d j k (H.domainCoord j k u) ∈ (H.d j k)†.domain,
      (H.d j k)† ⟨_, h⟩ = f - (p : W j) - H.d i j (H.domainCoord i j σ) := by
  have key : ∀ x : (H.d j k).domain,
      ⟪f - (p : W j) - H.d i j (H.domainCoord i j σ), (x : W j)⟫ =
        ⟪H.d j k (H.domainCoord j k u), H.d j k x⟫ := fun x => by
    have e := hs.snd (H.toDomainSpace hjk x)
    rw [domainIncl_toDomainSpace, d_domainCoord_toDomainSpace] at e
    rw [← inner_conj_symm, ← inner_conj_symm (H.d j k (H.domainCoord j k u)), inner_sub_right,
      inner_sub_right]
    congr 1
    linear_combination -e
  have hmem := mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, adjoint_apply_eq (H.dense j k) ⟨_, hmem⟩ key⟩

/-- Poincaré constants `≥ 1` from closed range at a related pair. -/
theorem exists_poincare_of_closedRangeAt {i j : ι} (hij : c.Rel i j) (hj : H.ClosedRangeAt j) :
    ∃ cP : ℝ, 1 ≤ cP ∧ ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ →
      ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖ := by
  obtain ⟨C, hC⟩ := (H.closedRangeAt_iff_poincare_of_rel hij).1 hj
  exact ⟨max C 1, le_max_right _ _, fun z hz => (hC z hz).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩

/-- **Well-posedness of the mixed Hodge Laplacian under closed range** at `j` and `k`: unique
solvability with a stability constant `16 c_P²`, `c_P` the Poincaré constant. -/
theorem existsUnique_mixed_of_closedRangeAt (hij : c.Rel i j) (hjk : c.Rel j k)
    (hj : H.ClosedRangeAt j) (hk : H.ClosedRangeAt k) :
    ∃ C, ∀ f : W j, (∃! x, H.mixedForm i j k x = H.mixedRHS i j f) ∧
      ∀ x, H.mixedForm i j k x = H.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  obtain ⟨c₁, hc₁, h₁⟩ := H.exists_poincare_of_closedRangeAt hij hj
  obtain ⟨c₂, hc₂, h₂⟩ := H.exists_poincare_of_closedRangeAt hjk hk
  set cP := max c₁ c₂
  have hcP : 1 ≤ cP := hc₁.trans (le_max_left _ _)
  have hPi : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖ :=
    fun z hz => (h₁ z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hPj : ∀ z : (H.d j k).domain, (z : W j) ∈ (H.cycles j)ᗮ → ‖(z : W j)‖ ≤ cP * ‖H.d j k z‖ :=
    fun z hz => (h₂ z hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  exact ⟨16 * cP ^ 2, fun f => ⟨H.existsUnique_mixed hij hjk hcP hPi hPj f,
    fun x hx => H.norm_le_of_mixed hij hjk hcP hPi hPj hx⟩⟩

end InfSup

end Feec.HilbertComplex
