module

public import Feec.Models.Cube.DeRhamIdentTrunc

/-!
# `HΛ((0, ½)ⁿ)` and `H̊Λ((0, ½)ⁿ)` are the parity classes of the torus de Rham complex

On `Q = (0, ½)ⁿ` the parity extension `Jf rel k` (`Feec.Models.Cube.DeRhamIdent.Jf`) identifies
the de Rham complexes of `Feec.Domain.DeRham` with the two parity classes of the torus de Rham
complex `Feec.Models.Cube.DeRham`, in every dimension `n` and degree `k`, as Hilbert complexes:

* **the minimal complex** `H̊Λ(Q)` (vanishing tangential trace) is the compression of the real
  torus complex along the extension in the **relative** class (`HQmin_eq_compress`);
* **the maximal complex** `HΛ(Q)` (no boundary condition) is the compression along the extension
  in the **absolute** class (`HQmax_eq_compress`).

Both inclusions are proved: the extension maps the domains on `Q` into the torus domains and
intertwines `d` (`mapsTo_comm_min`, `mapsTo_comm_max`), and a form whose extension lies in the torus
domain lies in the domain on `Q` (`mem_domain_of_J_min`, `mem_domain_of_J_max`, the trace part).
Inner products are multiplied by `2ⁿ` (`inner_J`); the range is the real parity class
(`range_J`), a reducing subcomplex of the real torus complex (`reducing_range`), the fixed vectors
of the reflections `± R_j^*` together with the conjugation (`realInvolutions`). Here the complexes are the windows `Λ⁰ → ⋯ → Λⁿ`
(`HQmin`, `HQmax`, `RT`); the consequences on the `ℤ`-indexed complexes (Poincaré inequality,
compactness, harmonic forms) are in `Feec.Models.Cube.DeRhamIdentPoincare`, and their statements on
`Feec.Models.Cube.FEM.complex` and `Feec.Models.Cube.FEM.complexMin` in
`Feec.Models.Cube.DeRhamIdentFEM`.

## Main definitions

* `RT n`: the torus de Rham window over `ℝ`; `cnj`, `refl`, `realInvolutions`, `realAction`.
* `HQmin n`, `HQmax n`: the windows of `H̊Λ(Q)` and `HΛ(Q)`; `J rel`.

## Main results

* `mem_realFixed_iff`, **`range_J`**, **`inner_J`**, **`reducing_range`**.
* **`mapsTo_comm_min`**, **`mem_domain_of_J_min`**, **`HQmin_eq_compress`**.
* **`mapsTo_comm_max`**, **`mem_domain_of_J_max`**, **`HQmax_eq_compress`**.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4.3 (relative and absolute boundary conditions)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the cube by compression of the torus)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate Topology
open Set MeasureTheory Filter LinearPMap

@[expose] public noncomputable section

namespace Feec.Models.Cube.DeRhamIdent

open Geometry
open Feec.Domain (formIdx extDerivOp L2F L2)
open Feec.Fourier.Exterior (Form)
open Feec.Fourier (Reflection entryConj entryConj_apply conjLp coeFn_conjLp symLp coeFn_symLp)
open Feec.HilbertComplex (ScaledEmbedding)

variable (n : ℕ)

/-! ### The real torus de Rham window and its real parity classes -/

/-- The `i`-forms on the Fourier side of `𝕋ⁿ`. -/
abbrev TW (i : Fin (Fintype.card (Fin n) + 1)) : Type :=
  Lp (Form ℂ (Fin n) i) 2 (Measure.count : Measure (Fin n → ℤ))

/-- **The torus de Rham window over `ℝ`** (`Λ⁰ → ⋯ → Λⁿ`, real parts of the inner products). -/
abbrev RT : HilbertComplex ℝ (ComplexShape.window (Fintype.card (Fin n) + 1)) (TW n) :=
  (Torus.DeRham.window (Fin n)).restrictScalars

variable {n}

theorem real_inner_TW (i : Fin (Fintype.card (Fin n) + 1)) (x y : TW n i) :
    ⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_ℂ :=
  L2.real_inner_eq_re_inner EuclideanSpace.real_inner_eq_re_inner x y

/-- The conjugation `u ↦ conj u(-·)` of the torus forms, as a real unitary. -/
def cnj (i : Fin (Fintype.card (Fin n) + 1)) : TW n i ≃ₗᵢ[ℝ] TW n i where
  toLinearEquiv := LinearEquiv.ofInvolutive (Torus.DeRham.windowReal.toConj.C i).toLinearMap
    (Torus.DeRham.windowReal.toConj.invol i)
  norm_map' x := by
    have h := Torus.DeRham.windowReal.toConj.inner_C i x x
    change ‖Torus.DeRham.windowReal.toConj.C i x‖ = ‖x‖
    have h3 : ‖Torus.DeRham.windowReal.toConj.C i x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ) x, h]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

theorem cnj_apply (i : Fin (Fintype.card (Fin n) + 1)) (u : TW n i) :
    cnj i u = Torus.DeRham.windowReal.toConj.C i u := rfl

theorem coeFn_cnj (i : Fin (Fintype.card (Fin n) + 1)) (u : TW n i) (m : Fin n → ℤ) :
    (cnj i u : (Fin n → ℤ) → Form ℂ (Fin n) i) m = entryConj (u (-m)) := by
  rw [cnj_apply, Fourier.SymbolComplex.RealStructure.toConj_C]
  exact Measure.ae_count_iff.1 (coeFn_conjLp Reflection.count_neg _ u) m

/-- The reflection `± R_j^*` of the torus forms (class `rel`), as a real unitary. -/
def refl (rel : Bool) (j : Fin n) (i : Fin (Fintype.card (Fin n) + 1)) : TW n i ≃ₗᵢ[ℝ] TW n i where
  toLinearEquiv := ((DeRham.symmetries (Fin n) rel).toInvolutions.R j i).toLinearEquiv.restrictScalars ℝ
  norm_map' := ((DeRham.symmetries (Fin n) rel).toInvolutions.R j i).norm_map

theorem coeFn_refl (rel : Bool) (j : Fin n) (i : Fin (Fintype.card (Fin n) + 1)) (u : TW n i)
    (m : Fin n → ℤ) :
    (refl rel j i u : (Fin n → ℤ) → Form ℂ (Fin n) i) m =
      DeRham.parSign rel • DeRham.reflForm j i (u (DeRham.flipAt j m)) :=
  Measure.ae_count_iff.1 (coeFn_symLp ((DeRham.symmetries (Fin n) rel).R j)
    ((DeRham.symmetries (Fin n) rel).ρ j i) u) m

theorem refl_cnj (rel : Bool) (j : Fin n) (i : Fin (Fintype.card (Fin n) + 1)) (u : TW n i) :
    refl rel j i (cnj i u) = cnj i (refl rel j i u) := by
  refine Lp.ext_count fun m => ?_
  rw [coeFn_refl, coeFn_cnj, coeFn_cnj, coeFn_refl]
  have e : DeRham.flipAt j (-m) = -DeRham.flipAt j m := by
    funext a; by_cases h : a = j <;> simp [DeRham.flipAt, h]
  rw [e]
  ext t
  simp only [PiLp.smul_apply, DeRham.reflForm_apply, entryConj_apply, smul_eq_mul, map_mul]
  congr 1
  · simp [DeRham.parSign]; split_ifs <;> simp
  · congr 1; simp [DeRham.reflSign]; split_ifs <;> simp

/-- The real unitaries of the real parity model: the conjugation (`none`) and the reflections
(`some j`). -/
def realR (rel : Bool) : Option (Fin n) → ∀ i, TW n i ≃ₗᵢ[ℝ] TW n i
  | none => cnj
  | some j => refl rel j

/-- **The reflections `± R_j^*` together with the real structure**, as commuting real unitary
involutions of the real torus window. -/
def realInvolutions (rel : Bool) : (RT n).Involutions (Option (Fin n)) where
  R := realR rel
  invol k i u := by
    cases k
    · exact Torus.DeRham.windowReal.toConj.invol i u
    · exact (DeRham.symmetries (Fin n) rel).toInvolutions.invol _ i u
  comm k l i u := by
    cases k <;> cases l
    · rfl
    · exact (refl_cnj rel _ i u).symm
    · exact refl_cnj rel _ i u
    · exact (DeRham.symmetries (Fin n) rel).toInvolutions.comm _ _ i u
  mapsTo k i j x := by
    cases k
    · exact Torus.DeRham.windowReal.toConj.mapsTo i j ⟨x.1, x.2⟩
    · exact (DeRham.symmetries (Fin n) rel).toInvolutions.mapsTo _ i j ⟨x.1, x.2⟩
  comm_d k i j x := by
    cases k
    · exact Torus.DeRham.windowReal.toConj.comm i j ⟨x.1, x.2⟩
    · exact (DeRham.symmetries (Fin n) rel).toInvolutions.comm_d _ i j ⟨x.1, x.2⟩

/-- The action of `(ℤ/2)^{n+1}` by the reflections and the conjugation. -/
abbrev realAction (rel : Bool) : (RT n).Action (Multiplicative (Option (Fin n) → ZMod 2)) :=
  (realInvolutions rel).toAction

instance (rel : Bool) (i : Fin (Fintype.card (Fin n) + 1)) :
    CompleteSpace ((realAction (n := n) rel).fixed i) :=
  ((realAction rel).isClosed_fixed i).completeSpace_coe

/-- **The real parity class, coefficientwise**: the fixed vectors are the sequences with real
entries and the parities of `rel` (`RealPar`). -/
theorem mem_realFixed_iff {rel : Bool} {i : Fin (Fintype.card (Fin n) + 1)} {u : TW n i} :
    u ∈ (realAction rel).fixed i ↔ RealPar rel i u := by
  rw [(realInvolutions rel).mem_fixed_toAction]
  constructor
  · intro h
    refine ⟨fun m t => ?_, fun j m t => ?_⟩
    · have e := congrArg (fun v : TW n i => (v : (Fin n → ℤ) → Form ℂ (Fin n) i) (-m) t) (h none)
      simp only [realInvolutions, realR, coeFn_cnj, neg_neg, entryConj_apply] at e
      exact e.symm
    · have e := congrArg (fun v : TW n i => (v : (Fin n → ℤ) → Form ℂ (Fin n) i)
        (DeRham.flipAt j m) t) (h (some j))
      simp only [realInvolutions, realR, coeFn_refl, PiLp.smul_apply,
        DeRham.reflForm_apply, smul_eq_mul] at e
      rw [DeRham.flipAt_flipAt j m] at e
      rw [← e]; ring
  · rintro ⟨h1, h2⟩ k
    cases k with
    | none =>
      refine Lp.ext_count fun m => ?_
      ext t
      simp only [realInvolutions, realR, coeFn_cnj, entryConj_apply]
      rw [h1, RCLike.conj_conj]
    | some j =>
      refine Lp.ext_count fun m => ?_
      ext t
      simp only [realInvolutions, realR, coeFn_refl, PiLp.smul_apply, DeRham.reflForm_apply,
        smul_eq_mul]
      rw [h2]
      linear_combination (DeRham.reflSign j t.1 * DeRham.reflSign j t.1 *
          (u m : Form ℂ (Fin n) i) t) * DeRham.parSign_mul_self rel +
        ((u m : Form ℂ (Fin n) i) t) * DeRham.reflSign_mul_self j t.1

/-! ### The windows of `H̊Λ(Q)` and `HΛ(Q)` and the extension -/

variable (n) in
/-- The degrees `0, …, n` as integers. -/
def ι (a : Fin (Fintype.card (Fin n) + 1)) : ℤ := ((a : ℕ) : ℤ)

theorem ι_rel (a b : Fin (Fintype.card (Fin n) + 1)) (h : (ComplexShape.up ℤ).Rel (ι n a) (ι n b)) :
    (ComplexShape.window (Fintype.card (Fin n) + 1)).Rel a b := by
  change ((a : ℕ) : ℤ) + 1 = ((b : ℕ) : ℤ) at h
  change (a : ℕ) + 1 = (b : ℕ)
  omega

variable (n) in
/-- The `L²` forms on `Q` of degree `a`. -/
abbrev WQ (a : Fin (Fintype.card (Fin n) + 1)) : Type :=
  L2F ℝ (Q (Fin n)) (formIdx n ((a : ℕ) : ℤ))

variable (n) in
/-- **The window of `H̊Λ(Q)`**: `H̊Λ⁰(Q) → ⋯ → H̊Λⁿ(Q)`. -/
abbrev HQmin : HilbertComplex ℝ (ComplexShape.window (Fintype.card (Fin n) + 1)) (WQ n) :=
  ((Feec.Domain.deRham ℝ n).minimalComplex (isOpen_Q (d := Fin n))).restrict (ι n) ι_rel

variable (n) in
/-- **The window of `HΛ(Q)`**: `HΛ⁰(Q) → ⋯ → HΛⁿ(Q)`. -/
abbrev HQmax : HilbertComplex ℝ (ComplexShape.window (Fintype.card (Fin n) + 1)) (WQ n) :=
  ((Feec.Domain.deRham ℝ n).maximalComplex (isOpen_Q (d := Fin n))).restrict (ι n) ι_rel

/-- **The parity extension of the window** in the class `rel`. -/
def J (rel : Bool) (a : Fin (Fintype.card (Fin n) + 1)) : WQ n a →L[ℝ] TW n a := Jf rel (a : ℕ)

theorem J_apply (rel : Bool) (a : Fin (Fintype.card (Fin n) + 1)) (u : WQ n a) :
    J rel a u = Jf rel (a : ℕ) u := rfl

/-- **The extension scales inner products by `2ⁿ`.** -/
theorem inner_J (rel : Bool) (a : Fin (Fintype.card (Fin n) + 1)) (x y : WQ n a) :
    ⟪J rel a x, J rel a y⟫_ℝ = ((2 ^ n : ℝ) : ℝ) * ⟪x, y⟫_ℝ :=
  inner_Jf rel a x y

/-- **The range of the extension is the real parity class.** -/
theorem range_J (rel : Bool) (a : Fin (Fintype.card (Fin n) + 1)) :
    LinearMap.range (J rel a : WQ n a →ₗ[ℝ] TW n a) = (realAction rel).fixed a := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩; exact mem_realFixed_iff.2 (Jf_realPar rel _ u)
  · intro hx; exact ⟨Jinvf (a : ℕ) x, Jf_Jinvf (mem_realFixed_iff.1 hx)⟩

instance (rel : Bool) (a : Fin (Fintype.card (Fin n) + 1)) :
    (LinearMap.range (J rel a : WQ n a →ₗ[ℝ] TW n a)).HasOrthogonalProjection := by
  rw [range_J]; infer_instance

/-- **The ranges of the extension form a reducing subcomplex** of the real torus window. -/
theorem reducing_range (rel : Bool) :
    (RT n).ReducingSubcomplex fun a => LinearMap.range (J rel a : WQ n a →ₗ[ℝ] TW n a) := by
  have h := (realAction (n := n) rel).reducingSubcomplex_fixed
  refine ⟨fun a b => ?_⟩
  convert h.reduces a b using 1 <;> exact range_J _ _

/-- The torus differential is the multiplier by the de Rham symbol. -/
theorem RT_d_apply {a b : Fin (Fintype.card (Fin n) + 1)} (x : ((RT n).d a b).domain)
    (m : Fin n → ℤ) :
    ((RT n).d a b x : (Fin n → ℤ) → Form ℂ (Fin n) b) m =
      (Feec.Fourier.Exterior.deRham (Fin n)).m a b (Feec.Fourier.Torus.freq m)
        ((x : TW n a) m) :=
  Fourier.coeFn_d_count (Torus.DeRham.windowSymbol (Fin n)) (i := a) (j := b) ⟨x.1, x.2⟩ m

/-- A sequence mapped pointwise by the symbol onto an `ℓ²` sequence is in the torus domain. -/
theorem mem_RT_domain_of_pointwise {a b : Fin (Fintype.card (Fin n) + 1)} {x : TW n a}
    {y : TW n b}
    (h : ∀ m, (Feec.Fourier.Exterior.deRham (Fin n)).m a b (Feec.Fourier.Torus.freq m)
      ((x : (Fin n → ℤ) → Form ℂ (Fin n) a) m) = (y : (Fin n → ℤ) → Form ℂ (Fin n) b) m) :
    ∃ hx : x ∈ ((RT n).d a b).domain, (RT n).d a b ⟨x, hx⟩ = y := by
  have hm : x ∈ ((Torus.DeRham.windowSymbol (Fin n)).toHilbertComplex.d a b).domain :=
    (Fourier.SymbolComplex.mem_domain_d_iff _).2
      ((Lp.memLp y).ae_eq (Filter.Eventually.of_forall fun m => (h m).symm))
  refine ⟨hm, ?_⟩
  exact (Operator.mulOp_apply_eq_iff (μ := (Measure.count : Measure (Fin n → ℤ)))
    (m := (Torus.DeRham.windowSymbol (Fin n)).m a b) ⟨x, hm⟩ y).2
    (Filter.Eventually.of_forall h)

theorem RT_d_zero {a b : Fin (Fintype.card (Fin n) + 1)}
    (h : ¬ (ComplexShape.window (Fintype.card (Fin n) + 1)).Rel a b) : (RT n).d a b = 0 :=
  (RT n).shape a b h

/-- The differential of `H̊Λ(Q)` between consecutive degrees. -/
theorem HQmin_d_succ (a : Fin (Fintype.card (Fin n) + 1))
    (hb : (a : ℕ) + 1 < Fintype.card (Fin n) + 1) :
    (HQmin n).d a ⟨(a : ℕ) + 1, hb⟩ = (extDerivOp ℝ n ((a : ℕ) : ℤ)).minimal (Q (Fin n)) :=
  (Feec.Domain.deRham ℝ n).minimalComplex_d isOpen_Q ((a : ℕ) : ℤ)

/-- The differential of `HΛ(Q)` between consecutive degrees. -/
theorem HQmax_d_succ (a : Fin (Fintype.card (Fin n) + 1))
    (hb : (a : ℕ) + 1 < Fintype.card (Fin n) + 1) :
    (HQmax n).d a ⟨(a : ℕ) + 1, hb⟩ = (extDerivOp ℝ n ((a : ℕ) : ℤ)).maximal (Q (Fin n)) :=
  (Feec.Domain.deRham ℝ n).maximalComplex_d isOpen_Q ((a : ℕ) : ℤ)

/-- **The extension maps `H̊Λ(Q)` into the torus domains and intertwines `d`** (relative class). -/
theorem mapsTo_comm_min (a b : Fin (Fintype.card (Fin n) + 1)) (x : ((HQmin n).d a b).domain) :
    ∃ h : J true a x ∈ ((RT n).d a b).domain,
      (RT n).d a b ⟨_, h⟩ = J true b ((HQmin n).d a b x) := by
  by_cases hab : (ComplexShape.window (Fintype.card (Fin n) + 1)).Rel a b
  · obtain ⟨bv, hbv⟩ := b
    change (a : ℕ) + 1 = bv at hab
    subst hab
    have e := HQmin_d_succ a hbv
    set x' : ((extDerivOp ℝ n ((a : ℕ) : ℤ)).minimal (Q (Fin n))).domain := ⟨x.1, e ▸ x.2⟩
    have hx : (HQmin n).d a ⟨(a : ℕ) + 1, hbv⟩ x =
        (extDerivOp ℝ n ((a : ℕ) : ℤ)).minimal (Q (Fin n)) x' :=
      apply_eq_of_eq e x x' rfl
    rw [hx]
    exact mem_RT_domain_of_pointwise fun m => coeff_d_minimal true (a : ℕ) x' m
  · have h0 := RT_d_zero hab
    refine ⟨by rw [h0]; exact Submodule.mem_top, ?_⟩
    rw [LinearPMap.apply_eq_zero_of_eq_zero h0,
      LinearPMap.apply_eq_zero_of_eq_zero ((HQmin n).shape a b hab), _root_.map_zero]

/-- **The extension maps `HΛ(Q)` into the torus domains and intertwines `d`** (absolute class). -/
theorem mapsTo_comm_max (a b : Fin (Fintype.card (Fin n) + 1)) (x : ((HQmax n).d a b).domain) :
    ∃ h : J false a x ∈ ((RT n).d a b).domain,
      (RT n).d a b ⟨_, h⟩ = J false b ((HQmax n).d a b x) := by
  by_cases hab : (ComplexShape.window (Fintype.card (Fin n) + 1)).Rel a b
  · obtain ⟨bv, hbv⟩ := b
    change (a : ℕ) + 1 = bv at hab
    subst hab
    have e := HQmax_d_succ a hbv
    set x' : ((extDerivOp ℝ n ((a : ℕ) : ℤ)).maximal (Q (Fin n))).domain := ⟨x.1, e ▸ x.2⟩
    have hx : (HQmax n).d a ⟨(a : ℕ) + 1, hbv⟩ x =
        (extDerivOp ℝ n ((a : ℕ) : ℤ)).maximal (Q (Fin n)) x' :=
      apply_eq_of_eq e x x' rfl
    rw [hx]
    exact mem_RT_domain_of_pointwise fun m => coeff_d_maximal (a : ℕ) x' m
  · have h0 := RT_d_zero hab
    refine ⟨by rw [h0]; exact Submodule.mem_top, ?_⟩
    rw [LinearPMap.apply_eq_zero_of_eq_zero h0,
      LinearPMap.apply_eq_zero_of_eq_zero ((HQmax n).shape a b hab), _root_.map_zero]

/-- **The trace part, relative class**: a form whose extension lies in the torus domain lies in
`H̊Λ(Q)`. -/
theorem mem_domain_of_J_min (a b : Fin (Fintype.card (Fin n) + 1)) (x : WQ n a)
    (h : J true a x ∈ ((RT n).d a b).domain) : x ∈ ((HQmin n).d a b).domain := by
  by_cases hab : (ComplexShape.window (Fintype.card (Fin n) + 1)).Rel a b
  · obtain ⟨bv, hbv⟩ := b
    change (a : ℕ) + 1 = bv at hab
    subst hab
    rw [HQmin_d_succ a hbv]
    exact (mem_minimal_of_Jf (u := x) (y := (RT n).d a ⟨(a : ℕ) + 1, hbv⟩ ⟨_, h⟩)
      fun m => (RT_d_apply ⟨_, h⟩ m).symm).1
  · rw [(HQmin n).shape a b hab]; exact Submodule.mem_top

/-- **The trace part, absolute class**: a form whose extension lies in the torus domain lies in
`HΛ(Q)`. -/
theorem mem_domain_of_J_max (a b : Fin (Fintype.card (Fin n) + 1)) (x : WQ n a)
    (h : J false a x ∈ ((RT n).d a b).domain) : x ∈ ((HQmax n).d a b).domain := by
  by_cases hab : (ComplexShape.window (Fintype.card (Fin n) + 1)).Rel a b
  · obtain ⟨bv, hbv⟩ := b
    change (a : ℕ) + 1 = bv at hab
    subst hab
    rw [HQmax_d_succ a hbv]
    exact (mem_maximal_of_Jf (u := x) (y := (RT n).d a ⟨(a : ℕ) + 1, hbv⟩ ⟨_, h⟩)
      fun m => (RT_d_apply ⟨_, h⟩ m).symm).1
  · rw [(HQmax n).shape a b hab]; exact Submodule.mem_top

theorem two_pow_pos : (0 : ℝ) < 2 ^ n := by positivity

/-- **`H̊Λ(Q)` is the compression of the real torus de Rham complex along the parity extension in
the relative class** (vanishing tangential traces). -/
theorem HQmin_eq_compress :
    HQmin n = (RT n).compress (J true) two_pow_pos (inner_J true) (reducing_range true) := by
  refine Feec.HilbertComplex.ext_d (funext fun a => funext fun b => ?_)
  refine LinearPMap.ext (Submodule.ext fun x => ?_) fun x hx hx' => ?_
  · rw [Feec.HilbertComplex.mem_compress_domain_iff]
    exact ⟨fun h => (mapsTo_comm_min a b ⟨x, h⟩).1, mem_domain_of_J_min a b x⟩
  · refine injective_Jf true (b : ℕ) ?_
    change J true b _ = J true b _
    rw [Feec.HilbertComplex.J_compress_d, ← (mapsTo_comm_min a b ⟨x, hx⟩).2]

/-- **`HΛ(Q)` is the compression of the real torus de Rham complex along the parity extension in
the absolute class** (no boundary condition). -/
theorem HQmax_eq_compress :
    HQmax n = (RT n).compress (J false) two_pow_pos (inner_J false) (reducing_range false) := by
  refine Feec.HilbertComplex.ext_d (funext fun a => funext fun b => ?_)
  refine LinearPMap.ext (Submodule.ext fun x => ?_) fun x hx hx' => ?_
  · rw [Feec.HilbertComplex.mem_compress_domain_iff]
    exact ⟨fun h => (mapsTo_comm_max a b ⟨x, h⟩).1, mem_domain_of_J_max a b x⟩
  · refine injective_Jf false (b : ℕ) ?_
    change J false b _ = J false b _
    rw [Feec.HilbertComplex.J_compress_d, ← (mapsTo_comm_max a b ⟨x, hx⟩).2]

/-! ### The parity model is the complexification of the forms on `Q` -/

end Feec.Models.Cube.DeRhamIdent
