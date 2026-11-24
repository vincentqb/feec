module

public import Feec.Models.Cube.MirrorWeakSymmetryComplex
public import Feec.Models.Cube.ParitySmoothingEstimates
public import Feec.Models.Cube.MirrorWeakSymmetryFEM

/-!
# Convergence of the mirror scheme (6.5)

The scheme (6.5) of [QuennevilleBelair2015], §6.3, on the cube `Q = (0, ½)³` with the mirror
boundary conditions (`Feec.Models.Cube.MirrorWeakSymmetryFEM`: top row `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ²`
without boundary condition, bottom component `a` in `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ²` with vanishing degrees
of freedom on the faces normal to `eₐ`) converges to the solution of the continuous problem (6.2)
for the mirror data `mirrorBGGSegment` of `Feec.Models.Cube.MirrorWeakSymmetryComplex`.

**The abstract theorem modulo harmonic forms.** `Feec.BGG.ExactWave.exists_discreteSolution_rate_harm`
is the end-to-end `O(h)` theorem of `Feec.Models.Cube.WeakSymmetryWave` with `Feec.BGG.Stability`
replaced by `Feec.BGG.HarmonicStability` (`Feec.HilbertComplex.BGG.Harmonic`): the mirror rows carry
the constant mode of `HΛ⁰(Q)` and the harmonic forms `dxₐ ⊗ eₐ` of the bottom row, so `Stability`
fails, but neither matters (the shifted form has a mass term on the top row, and `𝔥 ⊆ Ṽₕ¹` with
`S¹𝔥 = 0`).

**The discretization** `mirrorFEM` (a `Feec.BGG.Discrete`) uses the parity-smoothed projections of a
single family of reflection kernels for the four complexes (`exists_mirror_estimates`), and couples
the rows by `S₀,ₕ = π¹S⁰`, `S₁,ₕ = π²S¹` (the convention of `Feec.Models.Cube.WeakSymmetryWave`;
the canonical coupling `S_h = Π¹S⁰` of `Feec.Models.Cube.MirrorWeakSymmetryFEM.mirrorSegment`
is a different scheme, not analysed here): (5.4)
(`mirrorFEM_compatible`, the parity smoother intertwines `S⁰` on the compatible classes),
uniform bounds (`mirrorFEM_bounded`), Prop 5.9(1) for `π¹` (`mirrorFEM_happ0`), regular
potentials of the bottom row with no regularity hypothesis (`mirrorFEMReg`, from the coexact
potentials of `Feec.Models.Cube.DeRhamIdent.exists_coexact_potential`), `S₀,ₕ` onto
(`mirrorWave_S0_surjective`) and `grad` injective on the bottom row (`mirrorWave_dt0_injective`).

**Rates.** For classical solutions whose states and time derivatives are `C²` up to `∂Q` with the
mirror tangential conditions and whose multiplier `M` lies in `D(curl*)` on `HΛ¹(Q)` (vanishing
normal trace; automatic for TSD data, `M ≡ 0`) (`IsSmoothStateMirror`; no flatness at `∂Q`), the
error is
`≤ K L (1 + t) h_N` (`mirrorWave_rate`). For TSD-type solutions (`σ ≡ 0`, `M ≡ 0`), `σₕ` and
`Mₕ` are `O(h)` and every bounded linear constraint of `B = ρ` (its symmetry) holds for `ρₕ` up to
`O(h)` (`mirrorWave_rate_tsd`).

**Convergence without rate.** For every classical solution in the energy class of
`Feec.BGG.ExactWave` (continuity in `L²` of `σ, u, M, ρ, dφ, du, S¹u`) with `L²`-bounded
multiplier functionals, the error tends to `0` uniformly on `[0,T]` (`mirrorWave_converges`): the
parity-smoothed projections converge strongly (`tendsto_norm_sub_proj`, by density of the
finite element spaces), hence uniformly on the compact trajectories (`eventually_mirrorClose`), and
the consistency constant `K₁` tends to `0` by density of `D(d_max*)` (`eventually_mirrorFEM_K1`).

**The TSD solution.** The theorems above are stated for every classical solution of (6.2) for the
mirror data. `Feec.Models.Cube.MirrorWeakSymmetryTSD` identifies the real part of the Hodge wave
solution of `Feec.Models.Cube.MirrorBGG.existsUnique_memQ` (data in `D(L²)`) with such a solution
and proves that the scheme converges to it (`mirror_waveFEM`).

## Main definitions

* `mirrorDiscrete`, **`mirrorFEM`**, `mirrorWave`, `mirrorSource`, `mirrorSrcFun`.
* `IsCsFormPart`, `IsSmoothStateMirror`, `MirrorClose`.

## Main results

* **`Feec.BGG.ExactWave.exists_discreteSolution_rate_harm`**.
* `mirrorFEM_compatible`, `mirrorFEM_bounded`, `mirrorFEM_happ0`, `mirrorFEMReg`, `harmBot_le`,
  `mirrorWave_S0_surjective`, `mirrorWave_dt0_injective`, `mirrorFEM_strangData_le`.
* **`mirrorWave_rate`**, **`mirrorWave_rate_tsd`**.
* `Feec.Models.Cube.FEM.ParitySmoothingEstimates.tendsto_norm_sub_proj`,
  `eventually_mirrorClose`, `exists_adjoint_approx`, `eventually_mirrorFEM_K1`,
  **`mirrorWave_converges`**.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3 (Prop 5.9), §6.2 ((6.4), Prop 6.2), §6.3 ((6.5), Table 6.1)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5 (smoothed projections)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002] (Strang's lemma)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace ContDiff
open MeasureTheory Set Filter Finset

@[expose] public noncomputable section

namespace Feec.BGG.Discrete

variable {V0 Vt1 W2 Wt2 V1 Vt0 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} (Q : Discrete D) {T : ℝ} {g : ℝ → Vt1 →ₗ[ℝ] ℝ}

/-- **End-to-end `O(h)` convergence of (6.3) for a classical solution of (6.2), modulo harmonic
forms**: `Feec.BGG.ExactWave.exists_discreteSolution_rate` with `Stability` replaced by
`Feec.BGG.HarmonicStability` (no hypothesis on the top row; harmonic forms on the bottom row).
See [QuennevilleBelair2015], §6.2, (6.3), (6.4), Prop 6.2, and Thm 4.14. -/
theorem _root_.Feec.BGG.ExactWave.exists_discreteSolution_rate_harm {Hh : Submodule ℝ Vt1}
    {Cp CS : ℝ} (HS : HarmonicStability D Hh Cp CS) (h54 : Q.Compatible) [FiniteDimensional ℝ Q.V0h]
    [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.W2h]
    [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h]
    [FiniteDimensional ℝ Q.Wt2h] (hS : Function.Surjective Q.toSegmentH.S0)
    (hT : 0 < T) (s : ExactWave D T g) {fh : ℝ → Q.Vt1h} (hfh : ContinuousOn fh (Icc 0 T))
    (hg : ∀ t ∈ Ico 0 T, ∀ v : Q.Vt1h, g t v = ⟪fh t, v⟫) {K0 K1 c h : ℝ}
    (hK0 : ∀ t ∈ Icc 0 T, ∀ ψ ∈ Q.Vt0h, |s.ℓ t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK0' : ∀ t ∈ Icc 0 T, ∀ ψ ∈ Q.Vt0h,
      |s.ℓ' t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ t ∈ Icc 0 T, ∀ v ∈ Q.Vt1h, |⟪s.M t, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hK1' : ∀ t ∈ Icc 0 T, ∀ v ∈ Q.Vt1h, |⟪s.M' t, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hdata : ∀ t ∈ Icc 0 T,
      Q.strangData (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) K0 K1 ≤ (c * h) ^ 2)
    (hdata' : ∀ t ∈ Icc 0 T,
      Q.strangData (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t) K0 K1 ≤ (c * h) ^ 2) :
    ∃ sh : DiscreteSolution Q.toSegmentH T fh,
      (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
        (ellipticProjection Q.toSegmentH HS.toSegmentH_dt0_injective
          (exists_sub_eq_of_surjective hS) (ellipticRhs (Q.ellipticDataH (s.σ 0) (s.φ 0)
            (s.u 0) (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
      ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 + ‖s.M t - sh.M t‖ ^ 2 +
        ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ √(2 * (strangConst Cp + 1)) * |c| * |h| * (2 + 2 * t) := by
  have hιc := isEnergyEmbedding_energyEmb (V0 := V0) (Vt1 := Vt1) (W2 := W2) (Wt2 := Wt2)
  obtain ⟨sh, hinit, hbd⟩ := HS.exists_discreteSolution_norm_sub_le_rate (Q := Q) h54 hS
    hιc LinearMap.id (skewBil V0 Vt1 W2 Wt2 D) (skewBil V0 Vt1 W2 Wt2 Q.hSegment)
    Q.constraintH (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun a ψ => Subtype.ext (by
      change Q.P1 (D.d0 (a.1 : V0)) - Q.S0h (ψ : Vt0) = D.d0 (a.1 : V0) - Q.S0h (ψ : Vt0)
      rw [Q.P1_id _ (Q.d0_mem _ a.1.2)]))
    hT hfh (fun t => (s.σ t, s.u t, s.M t, s.ρ t)) (fun t => (s.σ' t, s.u' t, s.M' t, s.ρ' t))
    s.φ s.φ' s.ℓ s.ℓ' (fun t => multTerm D (s.ℓ t)) (fun _ _ _ => rfl)
    (fun t => energyEmb V0 Vt1 W2 Wt2 (0, (fh t : Vt1), 0, 0))
    (fun t _ b => by
      rw [Discrete.embedH_apply, hιc]
      simp)
    (s.cσ.prodMk (s.cu.prodMk (s.cM.prodMk s.cρ)))
    (s.cσ'.prodMk (s.cu'.prodMk (s.cM'.prodMk s.cρ')))
    (by
      rintro t ht _ ⟨⟨b, ψ⟩, rfl⟩
      change ⟪energyEmb V0 Vt1 W2 Wt2 (s.σ' t, s.u' t, s.M' t, s.ρ' t),
          energyEmb V0 Vt1 W2 Wt2 ((b.1 : V0), (b.2.1 : Vt1), (b.2.2.1 : W2), (b.2.2.2 : Wt2))⟫ +
        discreteSkewForm D ((s.σ t, s.u t, s.M t, s.ρ t), s.φ t)
          (((b.1 : V0), (b.2.1 : Vt1), (b.2.2.1 : W2), (b.2.2.2 : Wt2)), (ψ : Vt0)) -
        s.ℓ t (D.d0 (b.1 : V0) - D.S0 (ψ : Vt0)) =
        ⟪energyEmb V0 Vt1 W2 Wt2 (0, (fh t : Vt1), 0, 0),
          energyEmb V0 Vt1 W2 Wt2 ((b.1 : V0), (b.2.1 : Vt1), (b.2.2.1 : W2), (b.2.2.2 : Wt2))⟫
      rw [hιc, hιc]
      simp only [discreteSkewForm, inner_zero_left]
      have ha := s.ea t ht b.1 ψ
      have hb := s.eb t ht b.2.1
      have hc := s.ec t ht b.2.2.1
      have hd := s.ed t ht b.2.2.2
      have he := hg t ht b.2.1
      rw [Submodule.coe_inner] at he
      linarith)
    (fun y => s.continuousOn_ellipticDataH Q y)
    (fun t ht y => s.hasDerivWithinAt_ellipticDataH Q ht y)
    (fun y => s.continuousOn_ellipticDataH' Q y) s.ee s.ee' hK0 hK0' hK1 hK1' hdata hdata'
  refine ⟨sh, ?_, fun t ht => ?_⟩
  · have e := energyEmb_injective hinit
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_)
      (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)))
    · exact congrArg Prod.fst e
    · exact congrArg (fun z => z.2.1) e
    · exact congrArg (fun z => z.2.2.1) e
    · exact congrArg (fun z => z.2.2.2) e
  · have hb := hbd t ht
    rw [Discrete.embedH_apply, norm_sub_of_isEnergyEmbedding hιc] at hb
    exact hb

end Feec.BGG.Discrete

namespace Feec.Models.Cube.MirrorWeakSymmetry

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv rel_m10 rel_01 rel_12)
open Feec.Models.Cube.DeRhamIdent (dPart)

/-! ### Subcomplexes of the rows -/

section Dpart

variable {J : Finset (Fin 3)} {S' : (complexPart 3 J).Subcomplex}

theorem d01_apply_part (x : ((complexPart 3 J).d 0 1).domain) :
    (complexPart 3 J).d 0 1 x = dPart (cubeDomain 3) J 0 ⟨x, complexPart_d01 J ▸ x.2⟩ :=
  LinearPMap.apply_eq_of_eq' (complexPart_d01 J) x

theorem d12_apply_part (x : ((complexPart 3 J).d 1 2).domain) :
    (complexPart 3 J).d 1 2 x = dPart (cubeDomain 3) J 1 ⟨x, complexPart_d12 J ▸ x.2⟩ :=
  LinearPMap.apply_eq_of_eq' (complexPart_d12 J) x

theorem mem_dom01_part {x : W0} (hx : x ∈ (dPart (cubeDomain 3) J 0).domain) :
    x ∈ ((complexPart 3 J).d 0 1).domain := (complexPart_d01 J).symm ▸ hx

theorem mem_dom12_part {x : W1} (hx : x ∈ (dPart (cubeDomain 3) J 1).domain) :
    x ∈ ((complexPart 3 J).d 1 2).domain := (complexPart_d12 J).symm ▸ hx

theorem mem_dPart0_of_mem_V {x : W0} (hx : x ∈ S'.V 0) :
    x ∈ (dPart (cubeDomain 3) J 0).domain :=
  complexPart_d01 J ▸ S'.le_domain 0 1 hx

theorem mem_dPart1_of_mem_V {x : W1} (hx : x ∈ S'.V 1) :
    x ∈ (dPart (cubeDomain 3) J 1).domain :=
  complexPart_d12 J ▸ S'.le_domain 1 2 hx

theorem dPart0_mem_V (x : (dPart (cubeDomain 3) J 0).domain) (hx : (x : W0) ∈ S'.V 0) :
    (dPart (cubeDomain 3) J 0 x : W1) ∈ S'.V 1 := by
  have h := S'.mapsTo 0 1 x hx
  rwa [d01_apply_part] at h

theorem dPart1_mem_V (x : (dPart (cubeDomain 3) J 1).domain) (hx : (x : W1) ∈ S'.V 1) :
    (dPart (cubeDomain 3) J 1 x : W2) ∈ S'.V 2 := by
  have h := S'.mapsTo 1 2 x hx
  rwa [d12_apply_part] at h

/-- `d π = π d` in degree `0`. -/
theorem dPart0_π (P : S'.CochainProjection) (x : (dPart (cubeDomain 3) J 0).domain) :
    dPart (cubeDomain 3) J 0 ⟨P.π 0 x, mem_dPart0_of_mem_V (P.mem 0 x)⟩ =
      P.π 1 (dPart (cubeDomain 3) J 0 x) := by
  have h := P.comm 0 1 ⟨x, mem_dom01_part x.2⟩
  rw [d01_apply_part, d01_apply_part] at h
  exact h

/-- `d π = π d` in degree `1`. -/
theorem dPart1_π (P : S'.CochainProjection) (x : (dPart (cubeDomain 3) J 1).domain) :
    dPart (cubeDomain 3) J 1 ⟨P.π 1 x, mem_dPart1_of_mem_V (P.mem 1 x)⟩ =
      P.π 2 (dPart (cubeDomain 3) J 1 x) := by
  have h := P.comm 1 2 ⟨x, mem_dom12_part x.2⟩
  rw [d12_apply_part, d12_apply_part] at h
  exact h

/-- A cochain projection in degree `0`, on `D(d_J)`. -/
def projD0 (P : S'.CochainProjection) :
    (dPart (cubeDomain 3) J 0).domain →ₗ[ℝ] (dPart (cubeDomain 3) J 0).domain :=
  LinearMap.codRestrict _ (P.π 0 ∘ₗ (dPart (cubeDomain 3) J 0).domain.subtype)
    fun x => mem_dPart0_of_mem_V (P.mem 0 x)

/-- A cochain projection in degree `1`, on `D(d_J)`. -/
def projD1 (P : S'.CochainProjection) :
    (dPart (cubeDomain 3) J 1).domain →ₗ[ℝ] (dPart (cubeDomain 3) J 1).domain :=
  LinearMap.codRestrict _ (P.π 1 ∘ₗ (dPart (cubeDomain 3) J 1).domain.subtype)
    fun x => mem_dPart1_of_mem_V (P.mem 1 x)

@[simp] theorem coe_projD0 (P : S'.CochainProjection) (x : (dPart (cubeDomain 3) J 0).domain) :
    ((projD0 P x : (dPart (cubeDomain 3) J 0).domain) : W0) = P.π 0 x := rfl

@[simp] theorem coe_projD1 (P : S'.CochainProjection) (x : (dPart (cubeDomain 3) J 1).domain) :
    ((projD1 P x : (dPart (cubeDomain 3) J 1).domain) : W1) = P.π 1 x := rfl

end Dpart

/-! ### The discretization of the mirror data by a pair of rows of subcomplexes -/

section Discretization

variable (ST : (complexPart 3 ∅).Subcomplex) (SB : ∀ a : Fin 3, (complexPart 3 {a}).Subcomplex)

/-- The bottom-row discrete `0`-forms `∏ₐ V_{h,a}⁰`. -/
def bSub0 : Submodule ℝ BU0 where
  carrier := {φ | ∀ a, (φ a : W0) ∈ (SB a).V 0}
  add_mem' hφ hψ a := Submodule.add_mem _ (hφ a) (hψ a)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' c _ hφ a := Submodule.smul_mem _ c (hφ a)

/-- The bottom-row discrete `1`-forms `∏ₐ V_{h,a}¹`. -/
def bSub1 : Submodule ℝ BU1 where
  carrier := {v | ∀ a, (v a : W1) ∈ (SB a).V 1}
  add_mem' hφ hψ a := Submodule.add_mem _ (hφ a) (hψ a)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' c _ hφ a := Submodule.smul_mem _ c (hφ a)

/-- The bottom-row discrete `2`-forms `∏ₐ V_{h,a}²`. -/
def bSub2 : Submodule ℝ (Wv W2) where
  carrier := {z | ∀ a, z a ∈ (SB a).V 2}
  add_mem' hφ hψ a := Submodule.add_mem _ (hφ a) (hψ a)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' c _ hφ a := Submodule.smul_mem _ c (hφ a)

variable {SB} in
/-- Componentwise cochain projections in degree `0`. -/
def projB0 (PB : ∀ a, (SB a).CochainProjection) : BU0 →ₗ[ℝ] BU0 where
  toFun φ := WithLp.toLp 2 fun a => projD0 (PB a) (φ a)
  map_add' _ _ := PiLp.ext fun a => map_add (projD0 (PB a)) _ _
  map_smul' _ _ := PiLp.ext fun a => map_smul (projD0 (PB a)) _ _

variable {SB} in
/-- Componentwise cochain projections in degree `1`. -/
def projB1 (PB : ∀ a, (SB a).CochainProjection) : BU1 →ₗ[ℝ] BU1 where
  toFun v := WithLp.toLp 2 fun a => projD1 (PB a) (v a)
  map_add' _ _ := PiLp.ext fun a => map_add (projD1 (PB a)) _ _
  map_smul' _ _ := PiLp.ext fun a => map_smul (projD1 (PB a)) _ _

variable {SB} in
/-- Componentwise cochain projections in degree `2`. -/
def projB2 (PB : ∀ a, (SB a).CochainProjection) : Wv W2 →ₗ[ℝ] Wv W2 where
  toFun z := WithLp.toLp 2 fun a => (PB a).π 2 (z a)
  map_add' _ _ := PiLp.ext fun a => map_add ((PB a).π 2) _ _
  map_smul' _ _ := PiLp.ext fun a => map_smul ((PB a).π 2) _ _

/-- **The discretization of the mirror data** by a subcomplex `ST` of the top row `HΛ(Q)` and
subcomplexes `SB a` of the bottom components `HΛ_{a}(Q)`, with cochain projections. -/
def mirrorDiscrete (PT : ST.CochainProjection) (PB : ∀ a, (SB a).CochainProjection) :
    Feec.BGG.Discrete mirrorBGGSegment where
  V0h := (ST.V 0).comap TD0.domain.subtype
  V1h := (ST.V 1).comap TD1.domain.subtype
  W2h := ST.V 2
  Vt0h := bSub0 SB
  Vt1h := bSub1 SB
  Wt2h := bSub2 SB
  d0_mem x hx := dPart0_mem_V x hx
  d1_mem x hx := dPart1_mem_V x hx
  dt0_mem x hx a := dPart0_mem_V (x a) (hx a)
  dt1_mem x hx a := dPart1_mem_V (x a) (hx a)
  P0 := projD0 PT
  P1 := projD1 PT
  P2 := PT.π 2
  Pt0 := projB0 PB
  Pt1 := projB1 PB
  Pt2 := projB2 PB
  P0_mem x := PT.mem 0 x
  P1_mem x := PT.mem 1 x
  P2_mem x := PT.mem 2 x
  Pt0_mem x a := (PB a).mem 0 (x a)
  Pt1_mem x a := (PB a).mem 1 (x a)
  Pt2_mem x a := (PB a).mem 2 (x a)
  P0_id x hx := Subtype.ext (PT.proj 0 x hx)
  P1_id x hx := Subtype.ext (PT.proj 1 x hx)
  P2_id x hx := PT.proj 2 x hx
  Pt0_id x hx := PiLp.ext fun a => Subtype.ext ((PB a).proj 0 (x a) (hx a))
  Pt1_id x hx := PiLp.ext fun a => Subtype.ext ((PB a).proj 1 (x a) (hx a))
  Pt2_id x hx := PiLp.ext fun a => (PB a).proj 2 (x a) (hx a)
  comm0 x := Subtype.ext (dPart0_π PT x)
  comm1 x := dPart1_π PT x
  commt0 x := PiLp.ext fun a => Subtype.ext (dPart0_π (PB a) (x a))
  commt1 x := PiLp.ext fun a => dPart1_π (PB a) (x a)

variable {ST SB}

theorem graphSq_bD1 (w : BU1) :
    Feec.BGG.graphSq bD1 w = ∑ a, (‖(w a : W1)‖ ^ 2 + ‖BD1 a (w a)‖ ^ 2) := by
  unfold Feec.BGG.graphSq
  rw [norm_sq_BU1, norm_sq_bD1, ← Finset.sum_add_distrib]

/-- **Uniform bounds of the mirror discretization** from graph-norm bounds of the projections in
degree `1 → 2` and an `L²` bound of the top projection in degree `2`. -/
theorem mirrorDiscrete_bounded {PT : ST.CochainProjection} {PB : ∀ a, (SB a).CochainProjection}
    {C : ℝ} (hC0 : 0 ≤ C) (hT : ∀ x, ‖PT.π 2 x‖ ≤ C * ‖x‖) (hTg : PT.IsGraphBounded 1 2 C)
    (hBg : ∀ a, (PB a).IsGraphBounded 1 2 C) : (mirrorDiscrete ST SB PT PB).Bounded C where
  CP_nonneg := hC0
  P1 x := by
    have h := hTg ⟨x, mem_dom12_part x.2⟩
    rw [d12_apply_part, d12_apply_part] at h
    exact h
  P2 z := hT z
  Pt1 v := by
    change Feec.BGG.graphSq bD1 (projB1 PB v) ≤ C ^ 2 * Feec.BGG.graphSq bD1 v
    rw [graphSq_bD1, graphSq_bD1, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := hBg a ⟨v a, mem_dom12_part (v a).2⟩
    rw [d12_apply_part, d12_apply_part] at h
    exact h

end Discretization


/-! ### The parity smoother and `S⁰`: compatibility (5.4) -/

section Compat

open Feec.Models.Cube.ParitySmoother

variable {n : ℕ} (ρ : ReflKernel n)

theorem smoothFun_zero' (pv : Fin n → ℝ) : smoothFun ρ pv (0 : (Fin n → ℝ) → ℝ) = 0 := by
  simpa using smoothFun_smul ρ pv 0 (0 : (Fin n → ℝ) → ℝ)

/-- The smoothed parity extension of a finite combination of `L²` functions. -/
theorem smoothFun_L2_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → L2 ℝ (Geometry.Q (Fin n))) (pv : Fin n → ℝ) :
    smoothFun ρ pv (((∑ i ∈ s, c i • f i : L2 ℝ (Geometry.Q (Fin n))) : (Fin n → ℝ) → ℝ)) =
      ∑ i ∈ s, c i • smoothFun ρ pv (f i : (Fin n → ℝ) → ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [smoothFun_congr_ae ρ pv (Lp.coeFn_zero ℝ 2 _), smoothFun_zero']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      smoothFun_congr_ae ρ pv (Lp.coeFn_add _ _),
      smoothFun_add ρ pv (integrableOn_L2 _) (integrableOn_L2 _), ih,
      smoothFun_congr_ae ρ pv (Lp.coeFn_smul _ _), smoothFun_smul]

theorem formExt_apply_pt {k : ℤ} (w : formIdx n k → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    (fun s => formExt w s x) = formExt (fun r => w r x) := by
  funext s
  unfold formExt
  split_ifs <;> rfl

theorem symmDiff_empty_singleton (a : Fin n) : symmDiff (∅ : Finset (Fin n)) {a} = {a} := by
  ext x; simp [Finset.mem_symmDiff]

/-- **The parity smoother intertwines `S⁰`** at the level of smooth forms, for compatible classes
(the components `a` in the classes `J ∆ {a}`): `R^J S⁰ y = S⁰ (R^{J ∆ {a}} yₐ)ₐ` pointwise, the
smooth-form version of `Feec.Models.Cube.ParitySmoother.wsL2_paritySmooth_symmDiff`. -/
theorem paritySmoothForm_wsL2_zero {Ω : Set (Fin n → ℝ)} (J : Finset (Fin n))
    (hΩ : Ω = Geometry.Q (Fin n))
    (y : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n ((0 : ℕ) : ℤ)))) :
    Submodule.inclusion c1Forms_le_contForms
        (paritySmoothForm ρ J hΩ (((0 : ℕ) : ℤ) + 1) (wsL2 (Ω := Ω) ((0 : ℕ) : ℤ) y)) =
      coordWedgeC (fun a => Submodule.inclusion c1Forms_le_contForms
        (paritySmoothForm ρ (symmDiff J {a}) hΩ ((0 : ℕ) : ℤ) (y a))) := by
  subst hΩ
  refine Subtype.ext (funext fun x => funext fun t => ?_)
  change formExt (parCoeff ρ J (wsL2 (Ω := Geometry.Q (Fin n)) ((0 : ℕ) : ℤ) y)) t x =
    coordWedgeSum (fun a s => formExt (parCoeff ρ (symmDiff J {a}) (y a)) s x) t
  rw [show (fun a s => formExt (parCoeff ρ (symmDiff J {a}) (y a)) s x) =
      fun a => formExt (fun r => parCoeff ρ (symmDiff J {a}) (y a) r x) from
    funext fun a => formExt_apply_pt _ x]
  by_cases ht : (#t : ℤ) = ((0 : ℕ) : ℤ) + 1
  · rw [formExt_of_card _ ht,
      coordWedgeSum_formExt (fun a r => parCoeff ρ (symmDiff J {a}) (y a) r x) ⟨t, ht⟩]
    simp only [parCoeff]
    rw [wsL2_apply, smoothFun_L2_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : wsCoeff ((0 : ℕ) : ℤ) ⟨t, ht⟩ p = 0
    · rw [hp, zero_mul, zero_mul]
    · congr 1
      rw [wsCoeff_eq] at hp
      split_ifs at hp with h
      · obtain ⟨ha, he⟩ := h
        rw [← he, pvec_symmDiff_erase J ha]
      · exact absurd rfl hp
  · have h1 : formExt (parCoeff ρ J (wsL2 (Ω := Geometry.Q (Fin n)) ((0 : ℕ) : ℤ) y)) t x = 0 := by
      unfold formExt; rw [dite_eq_right_iff.2 fun h => absurd h ht]; rfl
    rw [h1]
    refine (isDeg_coordWedgeSum (k := 0) (fun a s hs => ?_) t fun h => ht ?_).symm
    · have : ¬ ((#s : ℤ) = ((0 : ℕ) : ℤ)) := by exact_mod_cast hs
      unfold formExt; exact dite_eq_right_iff.2 fun h => absurd h this
    · rw [h]; push_cast

end Compat

section CompatMesh

open Feec.Models.Cube.ParitySmoother PolySeq

variable (ρ : ReflKernel 3)

/-- **(5.4) at the mesh level**: if the bottom-row parity-smoothed interpolants of `y`, `y'` agree
componentwise (classes `{a}`), so do the top-row parity-smoothed interpolants of `S⁰y`, `S⁰y'`
(class `∅`): `Π_h R S⁰ y = Π¹ S⁰ Π̃⁰ R̃ y` (corrected Prop 5.7, `bggS0h_tensorInterp`). -/
theorem paritySmoothedInterp_wsL2_zero_eq (M : SimplicialMesh 3) (hM : M.domain = Geometry.Q (Fin 3))
    {y y' : PiLp 2 (fun _ : Fin 3 => L2F ℝ M.domain (formIdx 3 0))}
    (h : ∀ a, Ebot.paritySmoothedInterp M ρ {a} hM ((0 : ℕ) : ℤ) (y a) =
      Ebot.paritySmoothedInterp M ρ {a} hM ((0 : ℕ) : ℤ) (y' a)) :
    Etop.paritySmoothedInterp M ρ ∅ hM (((0 : ℕ) : ℤ) + 1) (wsL2 (Ω := M.domain) 0 y) =
      Etop.paritySmoothedInterp M ρ ∅ hM (((0 : ℕ) : ℤ) + 1) (wsL2 (Ω := M.domain) 0 y') := by
  have hMo : IsOpen M.domain := isOpen_of_eq_Q hM
  have key : ∀ z : PiLp 2 (fun _ : Fin 3 => L2F ℝ M.domain (formIdx 3 0)),
      Etop.paritySmoothedInterp M ρ ∅ hM (((0 : ℕ) : ℤ) + 1) (wsL2 (Ω := M.domain) 0 z) =
        Etop.glue M ((1 : ℕ) : ℤ) ((bggS0h M (Ebot.tensorInterp M 3 0 fun a =>
          Submodule.inclusion c1Forms_le_contForms (paritySmoothForm ρ {a} hM ((0 : ℕ) : ℤ)
            (z a))) : Etop.globalSpace M 1) : Etop.Piecewise M 1) := by
    intro z
    change Etop.glue M ((1 : ℕ) : ℤ) (Etop.globalInterp M 1 (Submodule.inclusion
      c1Forms_le_contForms (paritySmoothForm ρ ∅ hM (((0 : ℕ) : ℤ) + 1)
        (wsL2 (Ω := M.domain) ((0 : ℕ) : ℤ) z))) : Etop.Piecewise M 1) = _
    rw [paritySmoothForm_wsL2_zero ρ ∅ hM z, bggS0h_tensorInterp]
    simp only [symmDiff_empty_singleton]
  rw [key, key]
  have ht : (Ebot.tensorInterp M 3 0 fun a => Submodule.inclusion c1Forms_le_contForms
      (paritySmoothForm ρ {a} hM ((0 : ℕ) : ℤ) (y a))) =
      Ebot.tensorInterp M 3 0 fun a => Submodule.inclusion c1Forms_le_contForms
        (paritySmoothForm ρ {a} hM ((0 : ℕ) : ℤ) (y' a)) := by
    funext a
    exact Subtype.ext (Ebot.glue_injective M hMo 0 (h a))
  rw [ht]


/-- `paritySmoothedInterp_wsL2_zero_eq` transported along `(mesh 3 N).domain = Θ`. -/
theorem commutingMapOfEqPart_wsL2_zero_eq (N : ℕ) {Θ : Set (Fin 3 → ℝ)}
    (e : (mesh 3 N).domain = Θ) (hΘ : IsOpen Θ) (hΘQ : Θ ⊆ Geometry.Q (Fin 3))
    {y y' : PiLp 2 (fun _ : Fin 3 => L2F ℝ Θ (formIdx 3 0))}
    (h : ∀ a, (commutingMapOfEqPart e (isOpen_of_eq_Q (mesh_domain_eq_Q N))
        (mesh_domain_eq_Q N).le hΘ hΘQ {a}
        (Ebot.paritySmoothedCommutingMap (mesh 3 N) ρ {a} (mesh_domain_eq_Q N))).Q 0 (y a) =
      (commutingMapOfEqPart e (isOpen_of_eq_Q (mesh_domain_eq_Q N))
        (mesh_domain_eq_Q N).le hΘ hΘQ {a}
        (Ebot.paritySmoothedCommutingMap (mesh 3 N) ρ {a} (mesh_domain_eq_Q N))).Q 0 (y' a)) :
    (commutingMapOfEqPart e (isOpen_of_eq_Q (mesh_domain_eq_Q N)) (mesh_domain_eq_Q N).le hΘ hΘQ
        ∅ (Etop.paritySmoothedCommutingMap (mesh 3 N) ρ ∅ (mesh_domain_eq_Q N))).Q 1
          (wsL2 (Ω := Θ) 0 y) =
      (commutingMapOfEqPart e (isOpen_of_eq_Q (mesh_domain_eq_Q N)) (mesh_domain_eq_Q N).le hΘ
        hΘQ ∅ (Etop.paritySmoothedCommutingMap (mesh 3 N) ρ ∅ (mesh_domain_eq_Q N))).Q 1
          (wsL2 (Ω := Θ) 0 y') := by
  subst e
  exact paritySmoothedInterp_wsL2_zero_eq ρ (mesh 3 N) (mesh_domain_eq_Q N) h

end CompatMesh


/-! ### The parity-smoothed projections of one smoother for both rows -/

section Estimates

open Feec.Models.Cube.ParitySmoother

theorem _root_.Feec.Models.Cube.FEM.ParitySmoothingEstimates.mono {n : ℕ} [NeZero n] {J : Finset (Fin n)} {S : PolySeq}
    {ρ : ℕ → ReflKernel n} {C C' : ℝ} (hE : ParitySmoothingEstimates n J S ρ C) (hC : C ≤ C') :
    ParitySmoothingEstimates n J S ρ C' where
  half_le := hE.half_le.trans hC
  bound N i x := (hE.bound N i x).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  close := hE.close

/-- **One smoother for both rows of the mirror scheme**: kernels `ρ_N` (of radius `γ h_N / 32`)
and a constant `C` for which the parity smoothing estimates hold for the top row (class `∅`,
`P₁⁻Λ`) and for every bottom component (class `{a}`, `P₂Λ ⊗ ℝ³`). -/
theorem exists_mirror_estimates : ∃ (ρ : ℕ → ReflKernel 3) (C : ℝ),
    ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C ∧
      ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C := by
  obtain ⟨γT, hγT, hγT2, hT⟩ := paritySmoothingEstimates_parKernel (n := 3) PolySeq.lowestOrder
  obtain ⟨γB, hγB, hγB2, hB⟩ := paritySmoothingEstimates_parKernel (n := 3) PolySeq.lagrangeP2
  set γ := min γT γB
  have hγ : 0 < γ := lt_min hγT hγB
  have hγ1 : γ ≤ 1 := (min_le_left _ _).trans (by linarith)
  obtain ⟨CT, hCT⟩ := hT γ hγ hγ1 (min_le_left _ _) ∅
  choose CB hCB using fun a : Fin 3 => hB γ hγ hγ1 (min_le_right _ _) {a}
  refine ⟨parKernel 3 γ hγ hγ1, max CT (∑ a, |CB a|), hCT.mono (le_max_left _ _), fun a =>
    (hCB a).mono ((le_abs_self _).trans ((Finset.single_le_sum (f := fun a => |CB a|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ a)).trans (le_max_right _ _)))⟩

end Estimates

section MirrorFEM

open Feec.Models.Cube.ParitySmoother PolySeq

variable {ρ : ℕ → ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- **(5.4) for the parity-smoothed projections**: `π¹ S⁰ π̃⁰ = π¹ S⁰` (common smoother;
`π̃⁰` componentwise, classes `{a}`). -/
theorem proj_wsL2_compatible (N : ℕ) (x : PiLp 2 (fun _ : Fin 3 => W0)) :
    (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0
        (WithLp.toLp 2 fun a => ((hB a).proj N).π 0 (x a))) =
      (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0 x) := by
  change ((paritySmoothed 3 PolySeq.lowestOrder N ∅ (ρ N)).toCochainProjection
      (θ := 1 / 2) (by norm_num) (hT.close N)).π 1 _ =
    ((paritySmoothed 3 PolySeq.lowestOrder N ∅ (ρ N)).toCochainProjection
      (θ := 1 / 2) (by norm_num) (hT.close N)).π 1 _
  rw [Subcomplex.CommutingMap.toCochainProjection_π,
    Subcomplex.CommutingMap.toCochainProjection_π]
  congr 3
  refine commutingMapOfEqPart_wsL2_zero_eq (ρ N) N (mesh_domain 3 N) (isOpen_cubeDomain 3)
    (cubeDomain_subset_Q 3) fun a => ?_
  exact (paritySmoothed 3 PolySeq.lagrangeP2 N {a} (ρ N)).Q_restrictVEquiv_symm
    (θ := 1 / 2) (by norm_num) ((hB a).close N) 0
    ⟨(paritySmoothed 3 PolySeq.lagrangeP2 N {a} (ρ N)).Q 0 (x a),
      (paritySmoothed 3 PolySeq.lagrangeP2 N {a} (ρ N)).mem 0 (x a)⟩

/-- **The mirror scheme (6.5) as a discretization of the mirror data**: the spaces of Table 6.1
with the mirror boundary conditions (`polyPartial`: top row `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ²` without
boundary condition, bottom component `a` `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ²` with vanishing degrees of freedom on
the faces normal to `eₐ`) on the level-`(N + 1)` Freudenthal mesh, with the parity-smoothed
projections `π = J⁻¹ Π_h R` of one smoother. -/
def mirrorFEM (N : ℕ) : Feec.BGG.Discrete mirrorBGGSegment :=
  mirrorDiscrete (polyPartial 3 PolySeq.lowestOrder N ∅)
    (fun a => polyPartial 3 PolySeq.lagrangeP2 N {a}) (hT.proj N) fun a => (hB a).proj N

/-- **(5.4) holds for the mirror scheme** (`Feec.BGG.Discrete.Compatible`). -/
theorem mirrorFEM_compatible (N : ℕ) : (mirrorFEM hT hB N).Compatible := fun ψ => by
  refine Subtype.ext ?_
  change (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0 (bIncl0 (projB0 (fun a => (hB a).proj N) ψ))) =
    (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0 (bIncl0 ψ))
  have e : bIncl0 (projB0 (fun a => (hB a).proj N) ψ) =
      WithLp.toLp 2 fun a => ((hB a).proj N).π 0 (bIncl0 ψ a) := PiLp.ext fun a => rfl
  rw [e, proj_wsL2_compatible]

/-- **Uniform bounds of the mirror projections**: `Discrete.Bounded (2C)` for every `N`. -/
theorem mirrorFEM_bounded (N : ℕ) : (mirrorFEM hT hB N).Bounded (2 * C) :=
  mirrorDiscrete_bounded hT.two_mul_nonneg (hT.norm_proj_le N 2)
    ((hT.proj N).isGraphBounded_of_norm_le (hT.norm_proj_le N 1) (hT.norm_proj_le N 2))
    fun a => ((hB a).proj N).isGraphBounded_of_norm_le ((hB a).norm_proj_le N 1)
      ((hB a).norm_proj_le N 2)

instance mirrorFEM_fd0 (N : ℕ) : FiniteDimensional ℝ (mirrorFEM hT hB N).V0h :=
  WeakSymmetry.finiteDimensional_comap _ _
instance mirrorFEM_fd1 (N : ℕ) : FiniteDimensional ℝ (mirrorFEM hT hB N).V1h :=
  WeakSymmetry.finiteDimensional_comap _ _
instance mirrorFEM_fd2 (N : ℕ) : FiniteDimensional ℝ (mirrorFEM hT hB N).W2h :=
  inferInstanceAs (FiniteDimensional ℝ ((polyPartial 3 PolySeq.lowestOrder N ∅).V 2))

end MirrorFEM


/-! ### Prop 5.9(1) for `π¹` on the mirror spaces -/

section ApproxS0

open PolySeq

/-- **Prop 5.9(1) on the mirror spaces (mesh level)**: for `ψ ∈ ∏ₐ P₂Λ⁰_{Γₐ}` the canonical
`w = Π¹S⁰ψ ∈ P₁⁻Λ¹` (no boundary condition on the top row) satisfies `‖S⁰ψ − w‖ ≤ C h ‖∇ψ‖`,
`C` independent of `N` (`norm_sub_glue_bggS0h_le`, which needs no boundary condition). -/
theorem exists_sub_wsL2_le_mesh_mirror : ∃ C, 0 ≤ C ∧ ∀ (N : ℕ)
    (ψ : PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 0)))
    (_ : ∀ a, ψ a ∈ Ebot.VPartial (mesh 3 N) (partialFaces 3 {a}) 0)
    (hd : ∀ a, ψ a ∈ (dPart (mesh 3 N).domain {a} 0).domain),
    ∃ w ∈ Etop.VPartial (mesh 3 N) (partialFaces 3 ∅) 1,
      ‖WeakSymmetry.wsZero (Ω := (mesh 3 N).domain) ψ - w‖ ≤ C * hN N *
        ‖(WithLp.toLp 2 fun a => dPart (mesh 3 N).domain {a} 0 ⟨ψ a, hd a⟩ :
          PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 1)))‖ := by
  obtain ⟨C, hC0, hC⟩ := WeakSymmetry.norm_sub_glue_bggS0h_le
  refine ⟨C, hC0, fun N ψ hψ hd => ?_⟩
  have hψ' : ∀ a, ∃ v : Ebot.globalSpacePartial (mesh 3 N) (partialFaces 3 {a}) 0,
      Ebot.glue (mesh 3 N) ((0 : ℕ) : ℤ) (v : Ebot.Piecewise (mesh 3 N) 0) = ψ a := fun a => hψ a
  choose u hu using hψ'
  set u' : Fin 3 → Ebot.globalSpace (mesh 3 N) 0 := fun a =>
    ⟨(u a : Ebot.Piecewise (mesh 3 N) 0), Ebot.globalSpacePartial_le _ _ 0 (u a).2⟩
  have hψe : ψ = Ebot.tensorGlue (mesh 3 N) 3 ((0 : ℕ) : ℤ) fun a =>
      ((u' a : Ebot.globalSpace (mesh 3 N) 0) : Ebot.Piecewise (mesh 3 N) 0) :=
    PiLp.ext fun a => (hu a).symm
  have hmem : Etop.glue (mesh 3 N) (((0 : ℕ) : ℤ) + 1)
      ((bggS0h (mesh 3 N) u' : Etop.globalSpace (mesh 3 N) 1) : Etop.Piecewise (mesh 3 N) 1) ∈
        Etop.VPartial (mesh 3 N) (partialFaces 3 ∅) 1 := by
    rw [VPartial_empty]
    exact ⟨bggS0h (mesh 3 N) u', rfl⟩
  refine ⟨_, hmem, ?_⟩
  have hd' : (WithLp.toLp 2 fun a => dPart (mesh 3 N).domain {a} 0 ⟨ψ a, hd a⟩ :
      PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 1))) =
      Ebot.tensorGlue (mesh 3 N) 3 ((0 + 1 : ℕ) : ℤ)
        fun a => Ebot.dPiecewise (mesh 3 N) 0
          ((u' a : Ebot.globalSpace (mesh 3 N) 0) : Ebot.Piecewise (mesh 3 N) 0) := by
    refine PiLp.ext fun a => ?_
    obtain ⟨h, hval⟩ := glue_mem_dPart Ebot (mesh_domain_eq_Q N) {a} 0 (u a)
    have e : (⟨ψ a, hd a⟩ : (dPart (mesh 3 N).domain {a} 0).domain) = ⟨_, h⟩ :=
      Subtype.ext (hu a).symm
    change dPart (mesh 3 N).domain {a} 0 ⟨ψ a, hd a⟩ = _
    rw [e]
    exact hval
  rw [hd', hψe]
  exact hC N u'

/-- `exists_sub_wsL2_le_mesh_mirror` transported to a domain `Θ = (mesh 3 N).domain`. -/
theorem exists_sub_wsL2_le_of_eq_mirror {C : ℝ} (N : ℕ)
    (hC : ∀ (ψ : PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 0)))
      (_ : ∀ a, ψ a ∈ Ebot.VPartial (mesh 3 N) (partialFaces 3 {a}) 0)
      (hd : ∀ a, ψ a ∈ (dPart (mesh 3 N).domain {a} 0).domain),
      ∃ w ∈ Etop.VPartial (mesh 3 N) (partialFaces 3 ∅) 1,
        ‖WeakSymmetry.wsZero (Ω := (mesh 3 N).domain) ψ - w‖ ≤ C * hN N *
          ‖(WithLp.toLp 2 fun a => dPart (mesh 3 N).domain {a} 0 ⟨ψ a, hd a⟩ :
            PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 1)))‖)
    {Θ : Set (Fin 3 → ℝ)} (e : (mesh 3 N).domain = Θ) (hΘ : IsOpen Θ)
    (hΘQ : Θ ⊆ Geometry.Q (Fin 3))
    (ψ : PiLp 2 (fun _ : Fin 3 => L2F ℝ Θ (formIdx 3 0)))
    (hψ : ∀ a, ψ a ∈ (partialSubcomplexOfEq e (isOpen_of_eq_Q (mesh_domain_eq_Q N))
      (mesh_domain_eq_Q N).le hΘ hΘQ {a}
      (subcomplexPart Ebot (mesh 3 N) (mesh_domain_eq_Q N) {a})).V 0)
    (hd : ∀ a, ψ a ∈ (dPart Θ {a} 0).domain) :
    ∃ w ∈ (partialSubcomplexOfEq e (isOpen_of_eq_Q (mesh_domain_eq_Q N))
      (mesh_domain_eq_Q N).le hΘ hΘQ ∅
      (subcomplexPart Etop (mesh 3 N) (mesh_domain_eq_Q N) ∅)).V 1,
      ‖WeakSymmetry.wsZero (Ω := Θ) ψ - @id (L2F ℝ Θ (formIdx 3 1)) w‖ ≤ C * hN N *
        ‖(WithLp.toLp 2 fun a => dPart Θ {a} 0 ⟨ψ a, hd a⟩ :
          PiLp 2 (fun _ : Fin 3 => L2F ℝ Θ (formIdx 3 1)))‖ := by
  subst e
  exact hC ψ hψ hd

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- **Consistency of `S₀,ₕ = π¹S⁰` on the mirror spaces** ([QuennevilleBelair2015], Prop 5.9(1),
transferred to the smoothed projection): `‖(I − π¹)S⁰ψ‖ ≤ C_app h ‖ψ‖_V` on
`Ṽₕ⁰ = ∏ₐ P₂Λ⁰_{Γₐ}`. -/
theorem mirrorFEM_happ0 : ∃ Capp, 0 ≤ Capp ∧ ∀ N, ∀ ψ ∈ (mirrorFEM hT hB N).Vt0h,
    ‖mirrorBGGSegment.S0 ψ - (mirrorFEM hT hB N).S0h ψ‖ ^ 2 ≤
      (Capp * meshSize N) ^ 2 * Feec.BGG.graphSq mirrorBGGSegment.dt0 ψ := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_sub_wsL2_le_mesh_mirror
  have hC := hT.two_mul_nonneg
  refine ⟨(1 + 2 * C) * C₁, by positivity, fun N ψ hψ => ?_⟩
  obtain ⟨w, hw, hwle⟩ := exists_sub_wsL2_le_of_eq_mirror N (hC₁ N) (mesh_domain 3 N)
    (isOpen_cubeDomain 3) (cubeDomain_subset_Q 3) (bIncl0 ψ) (fun a => hψ a) (fun a => (ψ a).2)
  have hd : ‖(WithLp.toLp 2 fun a => dPart (cubeDomain 3) {a} 0 ⟨bIncl0 ψ a, (ψ a).2⟩ :
      PiLp 2 (fun _ : Fin 3 => L2F ℝ (cubeDomain 3) (formIdx 3 1)))‖ =
      ‖mirrorBGGSegment.dt0 ψ‖ := norm_bIncl1 (bD0 ψ)
  have h1 : ‖mirrorBGGSegment.S0 ψ - (mirrorFEM hT hB N).S0h ψ‖ ≤
      (1 + 2 * C) * (C₁ * meshSize N * ‖mirrorBGGSegment.dt0 ψ‖) := by
    change ‖WeakSymmetry.wsZero (Ω := cubeDomain 3) (bIncl0 ψ) -
      (hT.proj N).π 1 (WeakSymmetry.wsZero (Ω := cubeDomain 3) (bIncl0 ψ))‖ ≤ _
    refine (norm_sub_π_le_of_mem (hT.proj N) (hT.norm_proj_le N 1) hw).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [← hd, ← hN_eq_meshSize]
    exact hwle
  have h2 : ‖mirrorBGGSegment.dt0 ψ‖ ^ 2 ≤ Feec.BGG.graphSq mirrorBGGSegment.dt0 ψ := by
    unfold Feec.BGG.graphSq; nlinarith [sq_nonneg ‖ψ‖]
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc _ ≤ ((1 + 2 * C) * (C₁ * meshSize N * ‖mirrorBGGSegment.dt0 ψ‖)) ^ 2 := h3
    _ = ((1 + 2 * C) * C₁ * meshSize N) ^ 2 * ‖mirrorBGGSegment.dt0 ψ‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

end ApproxS0


/-! ### Regular potentials of the bottom row -/

section Regular

open Feec.Models.Cube.ParitySmoother (zeroForm zeroForm_apply idx₀ eq_idx₀)

/-- `mem_dPart_of_coeff` on the cube domain. -/
theorem mem_dPart_of_coeff_cube (J : Finset (Fin 3)) (k : ℕ)
    (w : L2F ℝ (cubeDomain 3) (formIdx 3 (k : ℤ)))
    (g : formIdx 3 (k : ℤ) → L2F ℝ (cubeDomain 3) (formIdx 3 (((0 : ℕ) : ℤ) + 1)))
    (hg : ∀ s : formIdx 3 (k : ℤ), (zeroForm (w s), g s) ∈
      (dPart (cubeDomain 3) (symmDiff J s.1) ((0 : ℕ) : ℤ)).graph) :
    ∃ h : w ∈ (dPart (cubeDomain 3) J (k : ℤ)).domain,
      ‖dPart (cubeDomain 3) J (k : ℤ) ⟨w, h⟩‖ ^ 2 ≤ ∑ s, ‖g s‖ ^ 2 := by
  have key : ∀ (Ω : Set (Fin 3 → ℝ)) (_ : Ω = Geometry.Q (Fin 3))
      (w : L2F ℝ Ω (formIdx 3 (k : ℤ)))
      (g : formIdx 3 (k : ℤ) → L2F ℝ Ω (formIdx 3 (((0 : ℕ) : ℤ) + 1))),
      (∀ s : formIdx 3 (k : ℤ), (zeroForm (w s), g s) ∈
        (dPart Ω (symmDiff J s.1) ((0 : ℕ) : ℤ)).graph) →
      ∃ h : w ∈ (dPart Ω J (k : ℤ)).domain,
        ‖dPart Ω J (k : ℤ) ⟨w, h⟩‖ ^ 2 ≤ ∑ s, ‖g s‖ ^ 2 := by
    rintro Ω rfl w g hg
    exact DeRhamIdent.mem_dPart_of_coeff J k w g hg
  exact key _ (cubeDomain_eq_Q 3) w g hg

/-- The coefficients of a row of regular potentials: `H¹` in the class `{a} ∆ s`. -/
abbrev RegCoeff (a : Fin 3) (s : formIdx 3 ((1 : ℕ) : ℤ)) :=
  (dPart (cubeDomain 3) (symmDiff {a} s.1) ((0 : ℕ) : ℤ)).GraphSpace

/-- A row of regular potentials. -/
abbrev RegRow (a : Fin 3) := PiLp 2 fun s : formIdx 3 ((1 : ℕ) : ℤ) => RegCoeff a s

/-- **The regularity space** `X_reg = ∏ₐ ∏_s H¹_{{a} ∆ s}(Q)` (graph norms) of the bottom row:
`1`-forms in the component `a` whose parity extensions (class `{a}`) have `H¹` coefficients. -/
abbrev RegSp := PiLp 2 fun a : Fin 3 => RegRow a

instance : Subsingleton (formIdx 3 ((0 : ℕ) : ℤ)) := ⟨fun a b => (eq_idx₀ a).trans (eq_idx₀ b).symm⟩

theorem norm_zeroForm {Ω : Set (Fin 3 → ℝ)} (f : L2 ℝ Ω) : ‖(zeroForm f :
    L2F ℝ Ω (formIdx 3 ((0 : ℕ) : ℤ)))‖ = ‖f‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_subsingleton _ idx₀, zeroForm_apply]

/-- `exists_coexact_potential_cube` in degree `1`. -/
theorem exists_coexact_potential_one (J : Finset (Fin 3))
    (u : (dPart (cubeDomain 3) J 1).domain) :
    ∃ w : (dPart (cubeDomain 3) J 1).domain,
      dPart (cubeDomain 3) J 1 w = dPart (cubeDomain 3) J 1 u ∧
      ‖(w : W1)‖ ≤ (2 * Real.pi)⁻¹ * ‖dPart (cubeDomain 3) J 1 u‖ ∧
      ∃ g : formIdx 3 1 → W1,
        (∀ s : formIdx 3 1, (zeroForm ((w : W1) s), g s) ∈
          (dPart (cubeDomain 3) (symmDiff J s.1) ((0 : ℕ) : ℤ)).graph) ∧
        ∑ s, ‖g s‖ ^ 2 = ‖dPart (cubeDomain 3) J 1 u‖ ^ 2 :=
  exists_coexact_potential_cube J 1 u

/-- `zeroForm` as a linear map. -/
def zeroFormL {Ω : Set (Fin 3 → ℝ)} : L2 ℝ Ω →ₗ[ℝ] L2F ℝ Ω (formIdx 3 ((0 : ℕ) : ℤ)) where
  toFun := zeroForm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `1`-form of a row of regular potentials. -/
def assemble (a : Fin 3) : RegRow a →ₗ[ℝ] W1 where
  toFun z := WithLp.toLp 2 fun s =>
    (dPart (cubeDomain 3) (symmDiff {a} s.1) ((0 : ℕ) : ℤ)).graphFst (z s) idx₀
  map_add' _ _ := PiLp.ext fun s => by simp
  map_smul' _ _ := PiLp.ext fun s => by simp

theorem zeroForm_assemble (a : Fin 3) (z : RegRow a) (s : formIdx 3 ((1 : ℕ) : ℤ)) :
    zeroForm ((assemble a z : W1) s) =
      (dPart (cubeDomain 3) (symmDiff {a} s.1) ((0 : ℕ) : ℤ)).graphFst (z s) :=
  PiLp.ext fun r => by rw [eq_idx₀ r]; rfl

theorem graph_mem_assemble (a : Fin 3) (z : RegRow a) (s : formIdx 3 ((1 : ℕ) : ℤ)) :
    (zeroForm ((assemble a z : W1) s),
      (dPart (cubeDomain 3) (symmDiff {a} s.1) ((0 : ℕ) : ℤ)).graphSnd (z s)) ∈
        (dPart (cubeDomain 3) (symmDiff {a} s.1) ((0 : ℕ) : ℤ)).graph := by
  rw [zeroForm_assemble]
  exact LinearPMap.mem_graphL2.1 (z s).2

theorem assemble_mem (a : Fin 3) (z : RegRow a) : assemble a z ∈ (BD1 a).domain :=
  (mem_dPart_of_coeff_cube {a} 1 (assemble a z) _ (graph_mem_assemble a z)).1

theorem norm_assemble_le (a : Fin 3) (z : RegRow a) : ‖assemble a z‖ ≤ ‖z‖ := by
  refine (abs_le_of_sq_le_sq' ?_ (norm_nonneg _)).2
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum fun s _ => ?_
  have h1 := norm_zeroForm ((assemble a z : W1) s)
  rw [zeroForm_assemble] at h1
  rw [← h1]
  exact pow_le_pow_left₀ (norm_nonneg _) (LinearPMap.norm_graphFst_le _) 2

/-- **The map `R : X_reg → Ṽ¹`** of the regular potentials. -/
def regR : RegSp →ₗ[ℝ] BU1 where
  toFun y := WithLp.toLp 2 fun a => ⟨assemble a (y a), assemble_mem a (y a)⟩
  map_add' _ _ := PiLp.ext fun a => Subtype.ext (map_add (assemble a) _ _)
  map_smul' _ _ := PiLp.ext fun a => Subtype.ext (map_smul (assemble a) _ _)

@[simp] theorem coe_regR_apply (y : RegSp) (a : Fin 3) :
    ((regR y a : (BD1 a).domain) : W1) = assemble a (y a) := rfl

theorem norm_regR_le (y : RegSp) : ‖regR y‖ ≤ 1 * ‖y‖ := by
  rw [one_mul]
  refine (abs_le_of_sq_le_sq' ?_ (norm_nonneg _)).2
  rw [norm_sq_BU1, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum fun a _ => pow_le_pow_left₀ (norm_nonneg _) (norm_assemble_le a _) 2

/-- **Every bottom field has a regular potential** with `‖y‖ ≤ √(1 + (2π)⁻²) ‖dv‖`
(`exists_coexact_potential_cube` in each component). -/
theorem exists_regR (v : BU1) : ∃ y : RegSp, bD1 (regR y) = bD1 v ∧
    ‖y‖ ≤ √(1 + (2 * Real.pi)⁻¹ ^ 2) * ‖bD1 v‖ := by
  choose w hdw hwn g hg hsum using fun a => exists_coexact_potential_one {a} (v a)
  set y : RegSp := WithLp.toLp 2 fun a => WithLp.toLp 2 fun s =>
    ⟨WithLp.toLp 2 (zeroForm ((w a : W1) s), g a s), LinearPMap.mem_graphL2.2 (hg a s)⟩
  have hR : ∀ a, assemble a (y a) = (w a : W1) := fun a => PiLp.ext fun s => rfl
  refine ⟨y, PiLp.ext fun a => ?_, ?_⟩
  · change BD1 a (regR y a) = BD1 a (v a)
    rw [← hdw a]
    congr 1
  · refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
    rw [mul_pow, Real.sq_sqrt (by positivity), norm_sq_bD1, Finset.mul_sum, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum fun a _ => ?_
    have hya : ‖y a‖ ^ 2 = ‖(w a : W1)‖ ^ 2 + ‖BD1 a (v a)‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, ← hsum a]
      change ∑ s, ‖(⟨WithLp.toLp 2 (zeroForm ((w a : W1) s), g a s), _⟩ : RegCoeff a s)‖ ^ 2 = _
      simp only [LinearPMap.norm_sq_graphSpace]
      change ∑ s, (‖zeroForm ((w a : W1) s)‖ ^ 2 + ‖g a s‖ ^ 2) = _
      rw [Finset.sum_add_distrib, PiLp.norm_sq_eq_of_L2 _ (w a : W1)]
      simp only [norm_zeroForm]
    rw [hya]
    have := pow_le_pow_left₀ (norm_nonneg _) (hwn a) 2
    rw [mul_pow] at this
    nlinarith [sq_nonneg ‖BD1 a (v a)‖]


theorem graph_mem_of_eq {J₁ J₂ : Finset (Fin 3)} (h : J₁ = J₂)
    (v : (dPart (cubeDomain 3) J₁ ((0 : ℕ) : ℤ)).GraphSpace) :
    ((dPart (cubeDomain 3) J₁ ((0 : ℕ) : ℤ)).graphFst v,
      (dPart (cubeDomain 3) J₁ ((0 : ℕ) : ℤ)).graphSnd v) ∈
        (dPart (cubeDomain 3) J₂ ((0 : ℕ) : ℤ)).graph := by
  subst h; exact LinearPMap.mem_graphL2.1 v.2

theorem abs_wsCoeff_le_one {k : ℤ} (t : formIdx 3 (k + 1)) (p : Fin 3 × formIdx 3 k) :
    |wsCoeff k t p| ≤ 1 := by
  rw [wsCoeff_eq]
  split_ifs
  · rw [WeakSymmetry.abs_sgn]
  · simp

theorem sum_norm_graphSnd_le (a : Fin 3) (z : RegRow a) :
    ∑ s : formIdx 3 1, ‖(dPart (cubeDomain 3) (symmDiff {a} s.1) ((0 : ℕ) : ℤ)).graphSnd (z s)‖ ≤
      (Fintype.card (formIdx 3 1) : ℝ) * ‖z‖ := by
  calc ∑ s : formIdx 3 1, ‖(dPart (cubeDomain 3) (symmDiff {a} s.1) ((0 : ℕ) : ℤ)).graphSnd (z s)‖
      ≤ ∑ _s : formIdx 3 1, ‖z‖ :=
        Finset.sum_le_sum fun s _ => (LinearPMap.norm_graphSnd_le _).trans (PiLp.norm_apply_le z s)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem norm_sum_wsCoeff_graphSnd_le (y : RegSp) (t : formIdx 3 2) :
    ‖∑ p : Fin 3 × formIdx 3 1, wsCoeff 1 t p •
      (dPart (cubeDomain 3) (symmDiff {p.1} p.2.1) ((0 : ℕ) : ℤ)).graphSnd (y p.1 p.2)‖ ≤
        (∑ _p : Fin 3 × formIdx 3 1, (1 : ℝ)) * ‖y‖ := by
  have hterm : ∀ p : Fin 3 × formIdx 3 1, ‖wsCoeff 1 t p •
      (dPart (cubeDomain 3) (symmDiff {p.1} p.2.1) ((0 : ℕ) : ℤ)).graphSnd (y p.1 p.2)‖ ≤
        ‖y‖ := by
    intro p
    have h1 : ‖(dPart (cubeDomain 3) (symmDiff {p.1} p.2.1) ((0 : ℕ) : ℤ)).graphSnd (y p.1 p.2)‖
        ≤ ‖y‖ := (LinearPMap.norm_graphSnd_le _).trans
          ((PiLp.norm_apply_le (y p.1) p.2).trans (PiLp.norm_apply_le y p.1))
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, ← one_mul ‖y‖]
    exact mul_le_mul (abs_wsCoeff_le_one (k := 1) t p) h1 (norm_nonneg _) zero_le_one
  calc _ ≤ ∑ p : Fin 3 × formIdx 3 1, ‖wsCoeff 1 t p •
        (dPart (cubeDomain 3) (symmDiff {p.1} p.2.1) ((0 : ℕ) : ℤ)).graphSnd (y p.1 p.2)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _p : Fin 3 × formIdx 3 1, ‖y‖ := Finset.sum_le_sum fun p _ => hterm p
    _ = (∑ _p : Fin 3 × formIdx 3 1, (1 : ℝ)) * ‖y‖ := by rw [Finset.sum_mul, one_mul]

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- **The `H¹` approximation of the bottom projections on regular fields**:
`‖Ry − π̃¹Ry‖ ≤ 3 · 3 (1 + 2C) K h ‖y‖`. -/
theorem norm_regR_sub_Pt1_le (N : ℕ) (y : RegSp) :
    ‖regR y - (mirrorFEM hT hB N).Pt1 (regR y)‖ ≤
      ((Fintype.card (Fin 3) : ℝ) * ((1 + 2 * C) * h1ConstPar 3 PolySeq.lagrangeP2 1 *
        (Fintype.card (formIdx 3 1) : ℝ))) * meshSize N * ‖y‖ := by
  have hC := (hB 0).two_mul_nonneg
  have hK := h1ConstPar_nonneg (n := 3) PolySeq.lagrangeP2 1
  have hm := (meshSize_pos N).le
  have hcomp : ∀ a, ‖((regR y - (mirrorFEM hT hB N).Pt1 (regR y)) a : W1)‖ ≤
      (1 + 2 * C) * h1ConstPar 3 PolySeq.lagrangeP2 1 * meshSize N *
        ((Fintype.card (formIdx 3 1) : ℝ) * ‖y‖) := by
    intro a
    have hy : ∀ s : formIdx 3 ((1 : ℕ) : ℤ), zeroForm ((assemble a (y a) : W1) s) ∈
        (dPart (cubeDomain 3) (symmDiff {a} s.1) ((0 : ℕ) : ℤ)).domain := fun s =>
      LinearPMap.mem_domain_of_mem_graph (graph_mem_assemble a (y a) s)
    have h1 := (hB a).norm_sub_proj_le_grad N 1 (assemble a (y a)) hy
    have hval : ∀ s : formIdx 3 ((1 : ℕ) : ℤ),
        dPart (cubeDomain 3) (symmDiff {a} s.1) ((0 : ℕ) : ℤ) ⟨_, hy s⟩ =
          (dPart (cubeDomain 3) (symmDiff {a} s.1) ((0 : ℕ) : ℤ)).graphSnd (y a s) := fun s =>
      ((LinearPMap.image_iff (hy s)).2 (graph_mem_assemble a (y a) s)).symm
    simp only [hval] at h1
    change ‖assemble a (y a) - ((hB a).proj N).π 1 (assemble a (y a))‖ ≤ _
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ((sum_norm_graphSnd_le a (y a)).trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le y a) (Nat.cast_nonneg _)
  refine (PiLp.norm_le_sum_norm _).trans ?_
  calc ∑ a, ‖(regR y - (mirrorFEM hT hB N).Pt1 (regR y)) a‖ ≤
      ∑ _a : Fin 3, (1 + 2 * C) * h1ConstPar 3 PolySeq.lagrangeP2 1 * meshSize N *
        ((Fintype.card (formIdx 3 1) : ℝ) * ‖y‖) := Finset.sum_le_sum fun a _ => hcomp a
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **The `H¹` approximation of `S₁,ₕ = π²S¹` on regular fields**: the coefficient `t` of `S¹Ry`
is a combination of the coefficients `(Ry)ₐ_r`, `r = t ∖ a`, which are `H¹` in the class
`{a} ∆ r = t = ∅ ∆ t` (the compatible classes), so `‖(I − π²)S¹Ry‖ ≲ h ‖y‖`. -/
theorem norm_S1_sub_S1h_regR_le (N : ℕ) (y : RegSp) :
    ‖(mirrorBGGSegment.S1 - (mirrorFEM hT hB N).S1h) (regR y)‖ ≤
      ((1 + 2 * C) * h1ConstPar 3 PolySeq.lowestOrder 2 *
        (∑ _t : formIdx 3 2, ∑ _p : Fin 3 × formIdx 3 1, (1 : ℝ))) * meshSize N * ‖y‖ := by
  have hC := hT.two_mul_nonneg
  have hK := h1ConstPar_nonneg (n := 3) PolySeq.lowestOrder 2
  have hm := (meshSize_pos N).le
  let z : W2 := wsL2 (Ω := cubeDomain 3) 1 (bIncl1 (regR y))
  -- the coefficients of `z` and their gradients
  let G : formIdx 3 2 → L2F ℝ (cubeDomain 3) (formIdx 3 (((0 : ℕ) : ℤ) + 1)) := fun t =>
    ∑ p : Fin 3 × formIdx 3 1, wsCoeff 1 t p •
      (dPart (cubeDomain 3) (symmDiff {p.1} p.2.1) ((0 : ℕ) : ℤ)).graphSnd (y p.1 p.2)
  have hgraph : ∀ t : formIdx 3 ((2 : ℕ) : ℤ), (zeroForm (z t), G t) ∈
      (dPart (cubeDomain 3) (symmDiff ∅ t.1) ((0 : ℕ) : ℤ)).graph := by
    intro t
    have hz : zeroForm (z t) = ∑ p : Fin 3 × formIdx 3 1, wsCoeff 1 t p •
        (dPart (cubeDomain 3) (symmDiff {p.1} p.2.1) ((0 : ℕ) : ℤ)).graphFst (y p.1 p.2) := by
      have hzt : z t = ∑ p : Fin 3 × formIdx 3 1, wsCoeff 1 t p •
          (assemble p.1 (y p.1) : W1) p.2 := by
        rw [wsL2_apply]
        rfl
      rw [hzt, show zeroForm (∑ p : Fin 3 × formIdx 3 1, wsCoeff 1 t p •
          (assemble p.1 (y p.1) : W1) p.2) = zeroFormL (∑ p : Fin 3 × formIdx 3 1,
            wsCoeff 1 t p • (assemble p.1 (y p.1) : W1) p.2) from rfl, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul, show zeroFormL ((assemble p.1 (y p.1) : W1) p.2) =
        zeroForm ((assemble p.1 (y p.1) : W1) p.2) from rfl, zeroForm_assemble]
    rw [hz]
    have hmem : ∀ p : Fin 3 × formIdx 3 1,
        (wsCoeff 1 t p • (dPart (cubeDomain 3) (symmDiff {p.1} p.2.1) ((0 : ℕ) : ℤ)).graphFst
          (y p.1 p.2), wsCoeff 1 t p •
            (dPart (cubeDomain 3) (symmDiff {p.1} p.2.1) ((0 : ℕ) : ℤ)).graphSnd (y p.1 p.2)) ∈
          (dPart (cubeDomain 3) (symmDiff ∅ t.1) ((0 : ℕ) : ℤ)).graph := by
      intro p
      by_cases hp : wsCoeff 1 t p = 0
      · rw [hp, zero_smul, zero_smul]; exact Submodule.zero_mem _
      · have hp' := hp
        rw [wsCoeff_eq] at hp'
        split_ifs at hp' with h
        · obtain ⟨ha, he⟩ := h
          have hcls : symmDiff ({p.1} : Finset (Fin 3)) p.2.1 = symmDiff ∅ t.1 := by
            rw [← he]
            ext x
            by_cases hx : x = p.1
            · subst hx; simp [Finset.mem_symmDiff, ha]
            · simp [Finset.mem_symmDiff, hx]
          exact Submodule.smul_mem _ _ (graph_mem_of_eq hcls (y p.1 p.2))
        · exact absurd rfl hp'
    have := Submodule.sum_mem _ fun p (_ : p ∈ Finset.univ) => hmem p
    convert this using 1
    exact Prod.ext (by rw [Prod.fst_sum]) (by rw [Prod.snd_sum])
  have hzdom : ∀ t : formIdx 3 ((2 : ℕ) : ℤ), zeroForm (z t) ∈
      (dPart (cubeDomain 3) (symmDiff ∅ t.1) ((0 : ℕ) : ℤ)).domain := fun t =>
    LinearPMap.mem_domain_of_mem_graph (hgraph t)
  have h1 := hT.norm_sub_proj_le_grad N 2 z hzdom
  have hval : ∀ t : formIdx 3 ((2 : ℕ) : ℤ),
      dPart (cubeDomain 3) (symmDiff ∅ t.1) ((0 : ℕ) : ℤ) ⟨zeroForm (z t), hzdom t⟩ = G t := fun t =>
    ((LinearPMap.image_iff (hzdom t)).2 (hgraph t)).symm
  simp only [hval] at h1
  have hG : ∀ t : formIdx 3 2, ‖G t‖ ≤ (∑ _p : Fin 3 × formIdx 3 1, (1 : ℝ)) * ‖y‖ :=
    fun t => norm_sum_wsCoeff_graphSnd_le y t
  change ‖z - (hT.proj N).π 2 z‖ ≤ _
  refine h1.trans ?_
  have hsum : ∑ t : formIdx 3 ((2 : ℕ) : ℤ), ‖G t‖ ≤
      (∑ _t : formIdx 3 2, ∑ _p : Fin 3 × formIdx 3 1, (1 : ℝ)) * ‖y‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun t _ => hG t
  calc (1 + 2 * C) * h1ConstPar 3 PolySeq.lowestOrder 2 * meshSize N * ∑ t, ‖G t‖ ≤
      (1 + 2 * C) * h1ConstPar 3 PolySeq.lowestOrder 2 * meshSize N *
        ((∑ _t : formIdx 3 2, ∑ _p : Fin 3 × formIdx 3 1, (1 : ℝ)) * ‖y‖) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end Regular


/-! ### The discrete harmonic forms, regular potentials and `S₀,ₕ` onto -/

section Discrete

open Feec.Models.Cube.ParitySmoother (zeroForm)

/-- The constant `1`-form `dxₐ` as a form field. -/
def dxField (a : Fin 3) : FormField 3 := fun _ t => if t = {a} then 1 else 0

theorem contDiff_dxField (a : Fin 3) {m : WithTop ℕ∞} : ContDiff ℝ m (dxField a) :=
  contDiff_const

theorem formL2_dxField (a : Fin 3) :
    formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) 1
      ⟨dxField a, (contDiff_dxField a (m := 0)).continuous⟩ = dxForm a := by
  refine PiLp.ext fun s => Lp.ext ?_
  filter_upwards [coeFn_formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) 1
    ⟨dxField a, (contDiff_dxField a (m := 0)).continuous⟩ s,
    MemLp.coeFn_toLp (DeRhamIdent.memLp_constFun (isOpen_cubeDomain 3).measurableSet
      (isBounded_cubeDomain 3) (⟨{a}, rfl⟩ : formIdx 3 ((#({a} : Finset (Fin 3)) : ℕ) : ℤ)) s)]
    with y h1 h2
  refine h1.trans (Eq.trans ?_ h2.symm)
  simp only [dxField, DeRhamIdent.constFun]
  congr 1
  exact propext ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- **The harmonic forms are discrete**: `dxₐ ∈ P₂⁻Λ¹_{Γₐ}` (the constant form has vanishing
tangential trace on the faces normal to `eₐ`, and the interpolation of degree `0` is exact). -/
theorem dxForm_mem_polyPartial (N : ℕ) (a : Fin 3) :
    dxForm a ∈ (polyPartial 3 PolySeq.lagrangeP2 N {a}).V 1 := by
  have hs : polySpace 3 0 1 ≤ PolySeq.lagrangeP2.space 3 1 :=
    PolySeq.polySpace_le_space PolySeq.lagrangeP2 (by decide)
  obtain ⟨v, hv, hle⟩ := exists_mem_polyPartial_le_smooth (n := 3) PolySeq.lagrangeP2 {a} N 1 0
    hs (contDiff_dxField a) (fun x t ht => by
      simp only [dxField]
      split_ifs with h
      · exact absurd (by rw [h, Finset.card_singleton]) ht
      · rfl)
    (fun x j hj _ t hjt => by
      rw [Finset.mem_singleton] at hj
      subst hj
      simp only [dxField]
      split_ifs with h
      · exact absurd (h ▸ Finset.mem_singleton_self j) hjt
      · rfl)
    (L := 0) (fun y _ => by
      rw [show dxField a = fun _ => dxField a 0 from rfl,
        iteratedFDeriv_const_of_ne (by norm_num)]
      simp)
  rw [mul_zero, mul_zero] at hle
  have he := norm_le_zero_iff.1 hle
  rw [sub_eq_zero] at he
  have he' : dxForm a = v := by rw [← formL2_dxField]; exact he
  rw [he']; exact hv

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- **`𝔥 ⊆ Ṽₕ¹`**: the harmonic forms of the bottom row are discrete. -/
theorem harmBot_le (N : ℕ) : harmBot ≤ (mirrorFEM hT hB N).Vt1h := fun v hv a => by
  have h := hv a
  rw [harmonic_one_part, Submodule.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  rw [← hc]
  exact Submodule.smul_mem _ c (dxForm_mem_polyPartial N a)

variable (C) in
/-- The approximation constant of the mirror regular potentials. -/
def mirrorRegConst : ℝ :=
  (Fintype.card (Fin 3) : ℝ) * ((1 + 2 * C) * h1ConstPar 3 PolySeq.lagrangeP2 1 *
      (Fintype.card (formIdx 3 1) : ℝ)) +
    (1 + 2 * C) * h1ConstPar 3 PolySeq.lowestOrder 2 *
      (∑ _t : formIdx 3 2, ∑ _p : Fin 3 × formIdx 3 1, (1 : ℝ))

theorem mirrorRegConst_nonneg (hC : 0 ≤ 2 * C) : 0 ≤ mirrorRegConst C := by
  have := h1ConstPar_nonneg (n := 3) PolySeq.lagrangeP2 1
  have := h1ConstPar_nonneg (n := 3) PolySeq.lowestOrder 2
  have : (0 : ℝ) ≤ ∑ _t : formIdx 3 2, ∑ _p : Fin 3 × formIdx 3 1, (1 : ℝ) := by positivity
  unfold mirrorRegConst; positivity

/-- **Regular potentials of the mirror scheme** (`Feec.BGG.Discrete.RegularPotential`) with
`X_reg = ∏ₐ ∏_s H¹_{{a} ∆ s}(Q)` (`RegSp`), `C_inc = 1`, `C_reg = √(1 + (2π)⁻²)` (no hypothesis:
the coexact potentials of `HΛ_{a}(Q)`), and the `H¹` approximation of the parity-smoothed
projections. -/
def mirrorFEMReg (N : ℕ) {Capp : ℝ} (hCapp : mirrorRegConst C ≤ Capp) :
    (mirrorFEM hT hB N).RegularPotential RegSp 1 √(1 + (2 * Real.pi)⁻¹ ^ 2) Capp (meshSize N) where
  R := regR
  Cinc_nonneg := zero_le_one
  Creg_nonneg := Real.sqrt_nonneg _
  norm_R_le := norm_regR_le
  exists_potential v _ := exists_regR v
  approx_Pt1 y := by
    have hC := (hB 0).two_mul_nonneg
    have h1 := norm_regR_sub_Pt1_le hT hB N y
    refine h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
      (meshSize_pos N).le) (norm_nonneg _))
    refine le_trans ?_ hCapp
    unfold mirrorRegConst
    have := h1ConstPar_nonneg (n := 3) PolySeq.lowestOrder 2
    have : (0 : ℝ) ≤ ∑ _t : formIdx 3 2, ∑ _p : Fin 3 × formIdx 3 1, (1 : ℝ) := by positivity
    have : 0 ≤ (1 + 2 * C) * h1ConstPar 3 PolySeq.lowestOrder 2 *
        (∑ _t : formIdx 3 2, ∑ _p : Fin 3 × formIdx 3 1, (1 : ℝ)) := by positivity
    linarith
  approx_S1 y := by
    have hC := hT.two_mul_nonneg
    have h1 := norm_S1_sub_S1h_regR_le hT hB N y
    refine h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
      (meshSize_pos N).le) (norm_nonneg _))
    refine le_trans ?_ hCapp
    unfold mirrorRegConst
    have := h1ConstPar_nonneg (n := 3) PolySeq.lagrangeP2 1
    have : 0 ≤ (Fintype.card (Fin 3) : ℝ) * ((1 + 2 * C) * h1ConstPar 3 PolySeq.lagrangeP2 1 *
        (Fintype.card (formIdx 3 1) : ℝ)) := by positivity
    linarith

/-- **The discrete mirror scheme (6.5)** as the discrete BGG data of `mirrorFEM`: `d`,
`S₀,ₕ = π¹S⁰`, `S₁,ₕ = π²S¹` on the finite element spaces. -/
abbrev mirrorWave (N : ℕ) := (mirrorFEM hT hB N).toSegmentH

instance mirrorWave_fdt0 (N : ℕ) : FiniteDimensional ℝ (mirrorFEM hT hB N).Vt0h := by
  let f : (mirrorFEM hT hB N).Vt0h →ₗ[ℝ] (∀ a : Fin 3, (polyPartial 3 PolySeq.lagrangeP2 N {a}).V 0) :=
    { toFun := fun x a => ⟨((x : BU0) a : W0), x.2 a⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun x y h => Subtype.ext (PiLp.ext fun a => Subtype.ext ?_)
  exact congrArg (fun z : (polyPartial 3 PolySeq.lagrangeP2 N {a}).V 0 => (z : W0)) (congrFun h a)

instance mirrorWave_fdt1 (N : ℕ) : FiniteDimensional ℝ (mirrorFEM hT hB N).Vt1h := by
  let f : (mirrorFEM hT hB N).Vt1h →ₗ[ℝ] (∀ a : Fin 3, (polyPartial 3 PolySeq.lagrangeP2 N {a}).V 1) :=
    { toFun := fun x a => ⟨((x : BU1) a : W1), x.2 a⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun x y h => Subtype.ext (PiLp.ext fun a => Subtype.ext ?_)
  exact congrArg (fun z : (polyPartial 3 PolySeq.lagrangeP2 N {a}).V 1 => (z : W1)) (congrFun h a)

instance mirrorWave_fdt2 (N : ℕ) : FiniteDimensional ℝ (mirrorFEM hT hB N).Wt2h := by
  let f : (mirrorFEM hT hB N).Wt2h →ₗ[ℝ] (∀ a : Fin 3, (polyPartial 3 PolySeq.lagrangeP2 N {a}).V 2) :=
    { toFun := fun x a => ⟨(x : Wv W2) a, x.2 a⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun x y h => Subtype.ext (PiLp.ext fun a => ?_)
  exact congrArg Subtype.val (congrFun h a)

/-- `grad` is injective on `∏ₐ P₂Λ⁰_{Γₐ}` (Poincaré on the bottom row). -/
theorem mirrorWave_dt0_injective (N : ℕ) : Function.Injective (mirrorWave hT hB N).dt0 :=
  mirror_harmonicStability.toSegmentH_dt0_injective

/-- Every test `1`-form on `Q` is `S⁰ψ` for a vector `ψ` of test functions. -/
theorem exists_mS0_eq_testField {χ : formIdx 3 1 → (Fin 3 → ℝ) → ℝ}
    (hχ : IsTestField (cubeDomain 3) χ) :
    ∃ ψ : BU0, ((mS0 ψ : TU1) : W1) = testField hχ := by
  have hψ : ∀ a, IsTestField (cubeDomain 3) (WeakSymmetry.proxy0 χ a) := fun a r => hχ _
  refine ⟨WithLp.toLp 2 fun a => ⟨testField (hψ a),
    (DeRhamIdent.minimal_le_dPart (isOpen_cubeDomain 3) (cubeDomain_subset_Q 3) {a} 0).1
      (ConstCoeffOp.testField_mem_minimal_domain _ (isOpen_cubeDomain 3) (hψ a))⟩, ?_⟩
  rw [coe_mS0]
  exact (wsL2_testField (Ω := cubeDomain 3) (k := 0) hψ).trans
    (testField_congr _ _ (WeakSymmetry.wsFields_proxy0 χ))

/-- **`π¹S⁰` maps `∏ₐ H_{a}Λ⁰(Q)` onto `P₁⁻Λ¹`** (density of test forms). -/
theorem exists_mirror_S0h_eq (N : ℕ) {μ : TU1} (hμ : μ ∈ (mirrorFEM hT hB N).V1h) :
    ∃ ψ, (mirrorFEM hT hB N).S0h ψ = μ := by
  set π1 : W1 →ₗ[ℝ] W1 := (hT.proj N).π 1
  set K : Submodule ℝ W1 := LinearMap.range (π1 ∘ₗ TD1.domain.subtype ∘ₗ mS0)
  have hK : K ≤ (polyPartial 3 PolySeq.lowestOrder N ∅).V 1 := by
    rintro _ ⟨ψ, rfl⟩; exact (hT.proj N).mem 1 _
  have : FiniteDimensional ℝ K := Submodule.finiteDimensional_of_le hK
  have hKc : IsClosed (K : Set W1) := K.closed_of_finiteDimensional
  have hπc : Continuous π1 :=
    (LinearMap.mkContinuous π1 (2 * C) (hT.norm_proj_le N 1)).continuous
  have htest : ∀ x ∈ testFieldSub ℝ (cubeDomain 3) (formIdx 3 1), π1 x ∈ K := by
    rintro _ ⟨χ, hχ, rfl⟩
    obtain ⟨ψ, hψ⟩ := exists_mS0_eq_testField hχ
    refine ⟨ψ, ?_⟩
    change π1 ((mS0 ψ : TU1) : W1) = π1 (testField hχ)
    rw [hψ]
  have hall : ∀ x : W1, π1 x ∈ K := by
    intro x
    have hx : x ∈ closure (testFieldSub ℝ (cubeDomain 3) (formIdx 3 1) : Set W1) :=
      (dense_testFieldSub (isOpen_cubeDomain 3) _) x
    have := map_mem_closure hπc hx htest
    rwa [hKc.closure_eq] at this
  obtain ⟨ψ, hψ⟩ := hall μ
  refine ⟨ψ, Subtype.ext ?_⟩
  change π1 ((mS0 ψ : TU1) : W1) = (μ : W1)
  rw [show π1 ((mS0 ψ : TU1) : W1) = π1 μ from hψ]
  exact (hT.proj N).proj 1 _ hμ

set_option maxHeartbeats 1000000 in
/-- **`S₀,ₕ = π¹S⁰` maps `∏ₐ P₂Λ⁰_{Γₐ}` onto `P₁⁻Λ¹`** (`exists_mirror_S0h_eq` and (5.4)). -/
theorem mirrorWave_S0_surjective (N : ℕ) : Function.Surjective (mirrorWave hT hB N).S0 := by
  intro μ
  obtain ⟨ψ, hψ⟩ := exists_mirror_S0h_eq hT hB N (μ := (μ : TU1)) μ.2
  have hc : (mirrorFEM hT hB N).S0h ((mirrorFEM hT hB N).Pt0 ψ) = (μ : TU1) := by
    rw [Feec.BGG.Discrete.S0h_apply, mirrorFEM_compatible hT hB N ψ,
      ← Feec.BGG.Discrete.S0h_apply, hψ]
  exact ⟨⟨_, (mirrorFEM hT hB N).Pt0_mem ψ⟩, Subtype.ext hc⟩

end Discrete


/-! ### Smooth states with the mirror boundary conditions and their interpolation errors -/

section Smooth

open ExteriorFibre (IsDeg)

/-- A partial derivative along a hyperplane vanishes on a function vanishing on it. -/
theorem partialDeriv_eq_zero_of_hyperplane {f : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ} {i j : Fin 3}
    (hij : i ≠ j) (hf : ∀ y : Fin 3 → ℝ, y j = x j → f y = 0) :
    partialDeriv i f x = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have hline : HasDerivAt (fun h : ℝ => x + h • (Pi.single i 1 : Fin 3 → ℝ))
        (Pi.single i 1 : Fin 3 → ℝ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin 3 → ℝ)).const_add x
    have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    have h0 : (f ∘ fun h : ℝ => x + h • (Pi.single i 1 : Fin 3 → ℝ)) = fun _ => 0 := by
      funext h
      refine hf _ ?_
      simp [Ne.symm hij]
    rw [h0] at h1
    exact (h1.unique (hasDerivAt_const 0 0)).symm ▸ rfl
  · rw [partialDeriv_def, fderiv_zero_of_not_differentiableAt hd]; rfl

/-- **`d` preserves the vanishing of the tangential components on a face** `{y_j = c}`. -/
theorem extDeriv_tangential_zero {w : FormField 3} {j : Fin 3} {c : ℝ}
    (hw : ∀ y : Fin 3 → ℝ, y j = c → ∀ t, j ∉ t → w y t = 0) :
    ∀ y : Fin 3 → ℝ, y j = c → ∀ t, j ∉ t → extDeriv w y t = 0 := by
  intro y hy t ht
  rw [extDeriv_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hij : i ≠ j := fun h => ht (h ▸ hi)
  rw [partialDeriv_eq_zero_of_hyperplane hij (fun z hz => hw z (hz.trans hy) _
    (fun h => ht (Finset.mem_of_mem_erase h))), mul_zero]

/-- **`C²` forms up to `∂Q` with vanishing tangential components on the faces normal to `J`**:
`x ∈ L²(Q; Λʲ)` is the restriction of a `C²` `j`-form `w` on `ℝ³` (the restriction of a `C²` field
on `cl Q`, through an extension theorem for the cube, not formalized) whose components `w_t`,
`j' ∉ t`, vanish on `{y_{j'} ∈ {0, ½}}` for `j' ∈ J`, with `‖Dw‖, ‖D dw‖ ≤ L` on `cl Q`. For
`J = {a}` this is the mirror condition of the component `a` of the bottom row, for `J = ∅` no
condition (top row). The analogue of `FEM.IsCsFormTr` for partial boundary conditions. -/
def IsCsFormPart (J : Finset (Fin 3)) (j : ℕ) (L : ℝ) (x : L2F ℝ (cubeDomain 3) (formIdx 3 j)) :
    Prop :=
  ∃ w : FormField 3, ∃ hw : ContDiff ℝ 2 w, (∀ y, IsDeg j (w y)) ∧
    (∀ y : Fin 3 → ℝ, ∀ i ∈ J, (y i = 0 ∨ y i = 1 / 2) → ∀ t : Finset (Fin 3), i ∉ t →
      w y t = 0) ∧
    (∀ y ∈ closure (cubeDomain 3), ‖w y‖ ≤ L ∧ ‖iteratedFDeriv ℝ 1 w y‖ ≤ L ∧
      ‖iteratedFDeriv ℝ 1 (extDeriv w) y‖ ≤ L) ∧
    x = formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) j ⟨w, hw.continuous⟩

theorem IsCsFormPart.mono {J : Finset (Fin 3)} {j : ℕ} {L L' : ℝ}
    {x : L2F ℝ (cubeDomain 3) (formIdx 3 j)} (hx : IsCsFormPart J j L x) (h : L ≤ L') :
    IsCsFormPart J j L' x := by
  obtain ⟨w, hw, hdeg, hJ, hL, rfl⟩ := hx
  exact ⟨w, hw, hdeg, hJ, fun y hy => ⟨(hL y hy).1.trans h, (hL y hy).2.1.trans h,
    (hL y hy).2.2.trans h⟩, rfl⟩

/-- `d_max` on the restrictions of `C¹` forms, on the cube domain. -/
theorem formL2_maximal_cube (k : ℕ) {w : FormField 3} (hw : ContDiff ℝ 1 w)
    (hdeg : ∀ x, IsDeg k (w x)) :
    ∃ h : formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) k
        ⟨w, hw.continuous⟩ ∈ ((extDerivOp ℝ 3 k).maximal (cubeDomain 3)).domain,
      (extDerivOp ℝ 3 k).maximal (cubeDomain 3) ⟨_, h⟩ =
        formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) ((k : ℤ) + 1)
          ⟨extDeriv w, continuous_extDeriv hw⟩ := by
  have key : ∀ (Θ : Set (Fin 3 → ℝ)) (e : Θ = cubeDomain 3) (hΘ : MeasurableSet Θ)
      (hb : Bornology.IsBounded Θ),
      (∃ h : formL2 hΘ hb k ⟨w, hw.continuous⟩ ∈ ((extDerivOp ℝ 3 k).maximal Θ).domain,
        (extDerivOp ℝ 3 k).maximal Θ ⟨_, h⟩ =
          formL2 hΘ hb ((k : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv hw⟩) →
      ∃ h : formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) k
          ⟨w, hw.continuous⟩ ∈ ((extDerivOp ℝ 3 k).maximal (cubeDomain 3)).domain,
        (extDerivOp ℝ 3 k).maximal (cubeDomain 3) ⟨_, h⟩ =
          formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) ((k : ℤ) + 1)
            ⟨extDeriv w, continuous_extDeriv hw⟩ := by
    rintro Θ rfl _ _ h; exact h
  exact key _ (mesh_domain 3 0) _ _
    (formL2_mem_maximal (mesh 3 0) (isOpen_mesh_domain 3 0) k hw hdeg)

/-- `d_J` on the restriction of a `C²` form: `d_J x = (dw)|_Q`. -/
theorem dPart_formL2 {J : Finset (Fin 3)} (k : ℕ) {w : FormField 3} (hw : ContDiff ℝ 2 w)
    (hdeg : ∀ x, IsDeg k (w x)) (h : formL2 (isOpen_cubeDomain 3).measurableSet
      (isBounded_cubeDomain 3) k ⟨w, hw.continuous⟩ ∈ (dPart (cubeDomain 3) J (k : ℤ)).domain) :
    dPart (cubeDomain 3) J (k : ℤ) ⟨_, h⟩ =
      formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) ((k : ℤ) + 1)
        ⟨extDeriv w, continuous_extDeriv (hw.of_le (by norm_num))⟩ := by
  obtain ⟨h', e⟩ := formL2_maximal_cube k (hw.of_le (by norm_num)) hdeg
  rw [DeRhamIdent.dPart_apply_eq (isOpen_cubeDomain 3) J k ⟨_, h⟩]
  exact e

theorem IsCsFormPart.norm_le {J : Finset (Fin 3)} {j : ℕ} {L : ℝ}
    {x : L2F ℝ (cubeDomain 3) (formIdx 3 j)} (hx : IsCsFormPart J j L x) (hL0 : 0 ≤ L) :
    ‖x‖ ≤ Fintype.card (formIdx 3 j) * L := by
  obtain ⟨w, hw, -, -, hL, rfl⟩ := hx
  refine WeakSymmetry.norm_L2F_le_of_bound _ hL0 fun t => ?_
  filter_upwards [coeFn_formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) j
    ⟨w, hw.continuous⟩ t, ae_restrict_mem (isOpen_cubeDomain 3).measurableSet] with y h1 hy
  rw [h1]
  exact (norm_le_pi_norm (w y) t.1).trans (hL y (subset_closure hy)).1

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}

/-- **The `O(h)` interpolation error of a smooth field by a parity-smoothed projection**. -/
theorem norm_sub_proj_le_of_isCsFormPart {J : Finset (Fin 3)} {S : PolySeq}
    (hE : ParitySmoothingEstimates 3 J S ρ C) (N k : ℕ) (hs : polySpace 3 0 k ≤ S.space 3 k)
    {L : ℝ} {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)} (hx : IsCsFormPart J k L x) :
    ‖x - (hE.proj N).π k x‖ ≤ (1 + 2 * C) * polyInterpConst 3 S k * meshSize N * L := by
  obtain ⟨w, hw, hdeg, hJ, hL, rfl⟩ := hx
  have h := hE.norm_sub_proj_le_smooth N k 0 hs (hw.of_le (by norm_num)) hdeg hJ
    (L := L) fun y hy => (hL y hy).2.1
  simpa using h

/-- **The `O(h)` interpolation error of `d x`** (`d` commutes with the projections). -/
theorem norm_d_sub_proj_le_of_isCsFormPart {J : Finset (Fin 3)} {S : PolySeq}
    (hE : ParitySmoothingEstimates 3 J S ρ C) (N k : ℕ)
    (hs : polySpace 3 0 (k + 1) ≤ S.space 3 (k + 1))
    {L : ℝ} {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)} (hx : IsCsFormPart J k L x)
    (h : x ∈ (dPart (cubeDomain 3) J (k : ℤ)).domain) :
    ‖dPart (cubeDomain 3) J (k : ℤ) ⟨x, h⟩ -
        (hE.proj N).π ((k : ℤ) + 1) (dPart (cubeDomain 3) J (k : ℤ) ⟨x, h⟩)‖ ≤
      (1 + 2 * C) * polyInterpConst 3 S (k + 1) * meshSize N * L := by
  obtain ⟨w, hw, hdeg, hJ, hL, rfl⟩ := hx
  rw [dPart_formL2 k hw hdeg h]
  have hJd : ∀ y : Fin 3 → ℝ, ∀ i ∈ J, (y i = 0 ∨ y i = 1 / 2) → ∀ t : Finset (Fin 3), i ∉ t →
      extDeriv w y t = 0 := by
    intro y i hi hy t ht
    rcases hy with hy | hy
    · exact extDeriv_tangential_zero (fun z hz => hJ z i hi (Or.inl hz)) y hy t ht
    · exact extDeriv_tangential_zero (fun z hz => hJ z i hi (Or.inr hz)) y hy t ht
  have hd2 : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (extDeriv w) := contDiff_extDeriv
    (by exact_mod_cast hw)
  have h1 := hE.norm_sub_proj_le_smooth N (k + 1) 0 hs hd2 (IsDeg.extDeriv hdeg) hJd
    (L := L) fun y hy => (hL y hy).2.2
  simpa using h1

end Smooth


/-! ### The Strang data of smooth mirror states -/

section StrangData

/-- **Regularity of an exact state of the mirror scheme** for the `O(h)` rate: every field is
`C²` up to `∂Q` with the mirror tangential conditions (`IsCsFormPart`: none on the top row, on
the faces normal to `eₐ` in the component `a` of the bottom row), with bound `L`; `S¹u` is `C²`;
and `M` lies in the domain of the adjoint of `curl` on `HΛ¹(Q)` with `‖curl* M‖ ≤ L`
(`|⟪M, curl w⟫| ≤ L ‖w‖`, i.e. the normal trace of `M` vanishes; `M ≡ 0` for TSD data). -/
def IsSmoothStateMirror (L : ℝ) (σ : TU0) (φ : BU0) (u : BU1) (M : W2) (ρ : Wv W2) : Prop :=
  IsCsFormPart ∅ 0 L (σ : W0) ∧ (∀ a, IsCsFormPart {a} 0 L (φ a : W0)) ∧
    (∀ a, IsCsFormPart {a} 1 L (u a : W1)) ∧ IsCsFormPart ∅ 2 L (mS1 u) ∧
    IsCsFormPart ∅ 2 L M ∧ (∀ w : TU1, |⟪M, tD1 w⟫| ≤ L * ‖w‖) ∧
    ∀ a, IsCsFormPart {a} 2 L (ρ a)

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

theorem hs_lowestOrder (k : ℕ) : polySpace 3 0 k ≤ PolySeq.lowestOrder.space 3 k :=
  PolySeq.polySpace_le_space PolySeq.lowestOrder (by simp [PolySeq.lowestOrder])

theorem hs_lagrangeP2 (k : ℕ) : polySpace 3 0 k ≤ PolySeq.lagrangeP2.space 3 k :=
  PolySeq.polySpace_le_space PolySeq.lagrangeP2 (PolySeq.lagrangeP2.one_le_deg k)

/-- The interpolation constants of the two rows. -/
abbrev cT (C : ℝ) (k : ℕ) : ℝ := (1 + 2 * C) * polyInterpConst 3 PolySeq.lowestOrder k
abbrev cB (C : ℝ) (k : ℕ) : ℝ := (1 + 2 * C) * polyInterpConst 3 PolySeq.lagrangeP2 k

theorem mirrorFEM_err_P0 (N : ℕ) {L : ℝ} {σ : TU0} (hσ : IsCsFormPart ∅ 0 L (σ : W0)) :
    ‖(mirrorFEM hT hB N).P0 σ - σ‖ ≤ cT C 0 * meshSize N * L := by
  have h := norm_sub_proj_le_of_isCsFormPart hT N 0 (hs_lowestOrder 0) hσ
  rw [norm_sub_rev]
  exact h

theorem mirrorFEM_err_Pt0 (N : ℕ) {L : ℝ} {φ : BU0} (hφ : ∀ a, IsCsFormPart {a} 0 L (φ a : W0)) :
    ‖mirrorBGGSegment.dt0 ((mirrorFEM hT hB N).Pt0 φ - φ)‖ ^ 2 ≤
      3 * (cB C 1 * meshSize N * L) ^ 2 := by
  change ‖bD0 (projB0 (fun a => (hB a).proj N) φ - φ)‖ ^ 2 ≤ _
  rw [norm_sq_bD0]
  refine WeakSymmetry.sum_sq_le_three fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  have h := norm_d_sub_proj_le_of_isCsFormPart (hB a) N 0 (hs_lagrangeP2 1) (hφ a) (φ a).2
  have e : BD0 a ((projB0 (fun a => (hB a).proj N) φ - φ) a) =
      ((hB a).proj N).π 1 (BD0 a (φ a)) - BD0 a (φ a) := by
    rw [PiLp.sub_apply, LinearPMap.map_sub]
    congr 1
    exact dPart0_π ((hB a).proj N) (φ a)
  rw [e, norm_sub_rev]
  exact h

theorem mirrorFEM_err_Pt1 (N : ℕ) {L : ℝ} {u : BU1} (hu : ∀ a, IsCsFormPart {a} 1 L (u a : W1)) :
    ‖(mirrorFEM hT hB N).Pt1 u - u‖ ^ 2 ≤ 3 * (cB C 1 * meshSize N * L) ^ 2 := by
  change ‖projB1 (fun a => (hB a).proj N) u - u‖ ^ 2 ≤ _
  rw [norm_sq_BU1]
  refine WeakSymmetry.sum_sq_le_three fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  have h := norm_sub_proj_le_of_isCsFormPart (hB a) N 1 (hs_lagrangeP2 1) (hu a)
  change ‖((hB a).proj N).π 1 (u a : W1) - (u a : W1)‖ ≤ _
  rw [norm_sub_rev]
  exact h

theorem mirrorFEM_err_d1 (N : ℕ) {L : ℝ} {u : BU1} (hu : ∀ a, IsCsFormPart {a} 1 L (u a : W1)) :
    ‖mirrorBGGSegment.dt1 ((mirrorFEM hT hB N).Pt1 u - u)‖ ^ 2 ≤
      3 * (cB C 2 * meshSize N * L) ^ 2 := by
  change ‖bD1 (projB1 (fun a => (hB a).proj N) u - u)‖ ^ 2 ≤ _
  rw [norm_sq_bD1]
  refine WeakSymmetry.sum_sq_le_three fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  have h := norm_d_sub_proj_le_of_isCsFormPart (hB a) N 1 (hs_lagrangeP2 2) (hu a) (u a).2
  have e : BD1 a ((projB1 (fun a => (hB a).proj N) u - u) a) =
      ((hB a).proj N).π 2 (BD1 a (u a)) - BD1 a (u a) := by
    rw [PiLp.sub_apply, LinearPMap.map_sub]
    congr 1
    exact dPart1_π ((hB a).proj N) (u a)
  rw [e, norm_sub_rev]
  exact h

theorem mirrorFEM_err_S1h (N : ℕ) (x : BU1) :
    ‖(mirrorFEM hT hB N).S1h x‖ ^ 2 ≤ 8 * C ^ 2 * ‖x‖ ^ 2 := by
  have h1 : ‖(mirrorFEM hT hB N).S1h x‖ ≤ 2 * C * ‖mS1 x‖ := hT.norm_proj_le N 2 _
  have h2 : ‖mS1 x‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
    have h := norm_wsL2_sq_le (Ω := cubeDomain 3) 1 (bIncl1 x)
    have h1 : (((1 : ℤ) : ℝ) + 1) = 2 := by norm_num
    rwa [h1, norm_bIncl1] at h
  have hC := hT.two_mul_nonneg
  have := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow] at this
  nlinarith [sq_nonneg C, sq_nonneg ‖x‖]

theorem mirrorFEM_err_P2 (N : ℕ) {L : ℝ} {M : W2} (hM : IsCsFormPart ∅ 2 L M) :
    ‖(mirrorFEM hT hB N).P2 M - M‖ ≤ cT C 2 * meshSize N * L := by
  have h := norm_sub_proj_le_of_isCsFormPart hT N 2 (hs_lowestOrder 2) hM
  rw [norm_sub_rev]
  exact h

theorem mirrorFEM_err_Pt2 (N : ℕ) {L : ℝ} {ρ' : Wv W2} (hρ : ∀ a, IsCsFormPart {a} 2 L (ρ' a)) :
    ‖(mirrorFEM hT hB N).Pt2 ρ' - ρ'‖ ^ 2 ≤ 3 * (cB C 2 * meshSize N * L) ^ 2 := by
  change ‖projB2 (fun a => (hB a).proj N) ρ' - ρ'‖ ^ 2 ≤ _
  rw [PiLp.norm_sq_eq_of_L2]
  refine WeakSymmetry.sum_sq_le_three fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  have h := norm_sub_proj_le_of_isCsFormPart (hB a) N 2 (hs_lagrangeP2 2) (hρ a)
  change ‖((hB a).proj N).π 2 (ρ' a) - ρ' a‖ ≤ _
  rw [norm_sub_rev]
  exact h

theorem mirrorFEM_err_S1 (N : ℕ) {L : ℝ} {u : BU1} (hSu : IsCsFormPart ∅ 2 L (mS1 u)) :
    ‖mirrorBGGSegment.S1 u - (mirrorFEM hT hB N).S1h u‖ ≤ cT C 2 * meshSize N * L :=
  norm_sub_proj_le_of_isCsFormPart hT N 2 (hs_lowestOrder 2) hSu

/-- The interpolation constant of the Strang data of the mirror scheme. -/
def mirrorInterpConst (C : ℝ) : ℝ :=
  cT C 0 ^ 2 + 3 * cB C 1 ^ 2 + (1 + 8 * C ^ 2) * (3 * cB C 1 ^ 2) + 3 * cB C 2 ^ 2 +
    cT C 2 ^ 2 + 3 * cB C 2 ^ 2 + cT C 2 ^ 2

theorem mirrorInterpConst_nonneg (C : ℝ) : 0 ≤ mirrorInterpConst C := by
  unfold mirrorInterpConst; positivity

set_option maxHeartbeats 2000000 in
/-- **The Strang data of (6.4) for a smooth mirror state**: the interpolation part is
`≤ mirrorInterpConst C · (L h_N)²`, for every `N`. -/
theorem mirrorFEM_strangData_le (N : ℕ) {L : ℝ} {σ : TU0} {φ : BU0} {u : BU1}
    {M : W2} {ρ' : Wv W2} (hs : IsSmoothStateMirror L σ φ u M ρ') (K0 K1 : ℝ) :
    (mirrorFEM hT hB N).strangData σ φ u M ρ' K0 K1 ≤
      mirrorInterpConst C * (L * meshSize N) ^ 2 + K0 ^ 2 + K1 ^ 2 := by
  obtain ⟨hσ, hφ, hu, hSu, hM, -, hρ⟩ := hs
  have h1 := mirrorFEM_err_P0 hT hB N hσ
  have h2 := mirrorFEM_err_Pt0 hT hB N hφ
  have h3a := mirrorFEM_err_Pt1 hT hB N hu
  have h3b := mirrorFEM_err_S1h hT hB N ((mirrorFEM hT hB N).Pt1 u - u)
  have h3c := mirrorFEM_err_d1 hT hB N hu
  have h4 := mirrorFEM_err_P2 hT hB N hM
  have h5 := mirrorFEM_err_Pt2 hT hB N hρ
  have h6 := mirrorFEM_err_S1 hT hB N hSu
  have hm := (meshSize_pos N).le
  have hC := hT.two_mul_nonneg
  have q1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have q4 := pow_le_pow_left₀ (norm_nonneg _) h4 2
  have q6 := pow_le_pow_left₀ (norm_nonneg _) h6 2
  have e1 : (mirrorFEM hT hB N).strangData σ φ u M ρ' K0 K1 =
      ‖(mirrorFEM hT hB N).P0 σ - σ‖ ^ 2 +
        ‖mirrorBGGSegment.dt0 ((mirrorFEM hT hB N).Pt0 φ - φ)‖ ^ 2 +
        (‖(mirrorFEM hT hB N).Pt1 u - u‖ ^ 2 +
          ‖(mirrorFEM hT hB N).S1h ((mirrorFEM hT hB N).Pt1 u - u)‖ ^ 2 +
          ‖mirrorBGGSegment.dt1 ((mirrorFEM hT hB N).Pt1 u - u)‖ ^ 2) +
        ‖(mirrorFEM hT hB N).P2 M - M‖ ^ 2 + ‖(mirrorFEM hT hB N).Pt2 ρ' - ρ'‖ ^ 2 + K0 ^ 2 +
        K1 ^ 2 + ‖mirrorBGGSegment.S1 u - (mirrorFEM hT hB N).S1h u‖ ^ 2 := rfl
  have e2 : mirrorInterpConst C * (L * meshSize N) ^ 2 =
      (cT C 0 * meshSize N * L) ^ 2 + 3 * (cB C 1 * meshSize N * L) ^ 2 +
        (1 + 8 * C ^ 2) * (3 * (cB C 1 * meshSize N * L) ^ 2) +
        3 * (cB C 2 * meshSize N * L) ^ 2 + (cT C 2 * meshSize N * L) ^ 2 +
        3 * (cB C 2 * meshSize N * L) ^ 2 + (cT C 2 * meshSize N * L) ^ 2 := by
    unfold mirrorInterpConst; ring
  rw [e1, e2]
  have hS1h : ‖(mirrorFEM hT hB N).S1h ((mirrorFEM hT hB N).Pt1 u - u)‖ ^ 2 ≤
      8 * C ^ 2 * (3 * (cB C 1 * meshSize N * L) ^ 2) :=
    h3b.trans (mul_le_mul_of_nonneg_left h3a (by positivity))
  nlinarith

end StrangData


/-! ### The `O(h)` rate of the mirror scheme (6.5) -/

section Rate

/-- The source functional `v ↦ ⟪f, v⟫` on `∏ₐ H_{a}Λ¹(Q)` of an `L²` source `f ∈ (L²Λ¹)³`. -/
def mirrorSrcFun (f : ℝ → Wv W1) (t : ℝ) : BU1 →ₗ[ℝ] ℝ := (innerSL ℝ (f t)).toLinearMap ∘ₗ bIncl1

theorem mirrorSrcFun_apply (f : ℝ → Wv W1) (t : ℝ) (v : BU1) :
    mirrorSrcFun f t v = ⟪f t, bIncl1 v⟫ := rfl

/-- The inclusion `∏ₐ H_{a}Λ¹(Q) → (L²Λ¹(Q))³` as a bounded map (an isometry). -/
def bIncl1CLM : BU1 →L[ℝ] Wv W1 :=
  LinearMap.mkContinuous bIncl1 1 fun x => by rw [norm_bIncl1, one_mul]

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

instance mirrorWave_completeSpace_t1 (N : ℕ) : CompleteSpace (mirrorFEM hT hB N).Vt1h :=
  FiniteDimensional.complete ℝ _

/-- **The discrete source of the mirror scheme**: the representer in `∏ₐ P₂⁻Λ¹_{Γₐ}` of
`v ↦ ⟪f(t), v⟫` (the `L²` projection of `f(t)`). -/
def mirrorSource (N : ℕ) (f : ℝ → Wv W1) (t : ℝ) : (mirrorFEM hT hB N).Vt1h :=
  (InnerProductSpace.toDual ℝ (mirrorFEM hT hB N).Vt1h).symm
    ((innerSL ℝ (f t)).comp (bIncl1CLM.comp (mirrorFEM hT hB N).Vt1h.subtypeL))

theorem inner_mirrorSource (N : ℕ) (f : ℝ → Wv W1) (t : ℝ) (v : (mirrorFEM hT hB N).Vt1h) :
    ⟪mirrorSource hT hB N f t, v⟫ = ⟪f t, bIncl1 (v : BU1)⟫ := by
  rw [mirrorSource, InnerProductSpace.toDual_symm_apply]
  rfl

theorem continuousOn_mirrorSource (N : ℕ) {f : ℝ → Wv W1} {T : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) : ContinuousOn (mirrorSource hT hB N f) (Icc 0 T) := by
  have h1 : Continuous fun w : Wv W1 =>
      (innerSL ℝ w).comp (bIncl1CLM.comp (mirrorFEM hT hB N).Vt1h.subtypeL) :=
    ((ContinuousLinearMap.compL ℝ (mirrorFEM hT hB N).Vt1h (Wv W1) ℝ).flip
      (bIncl1CLM.comp (mirrorFEM hT hB N).Vt1h.subtypeL)).continuous.comp (innerSL ℝ).continuous
  exact (InnerProductSpace.toDual ℝ (mirrorFEM hT hB N).Vt1h).symm.continuous.comp_continuousOn
    (h1.comp_continuousOn hf)

set_option maxHeartbeats 4000000 in
/-- **`O(h)` convergence of the mirror scheme (6.5) on the cube**, without hypothesis: there is
`K`, independent of `N`, `T`, the data and the solution, such that for every `N`, every `T > 0`,
every `L²` source `f` continuous on `[0,T]` and every classical solution `s` of (6.2) for the
mirror data (`ExactWave mirrorBGGSegment`) whose states and time derivatives are `C²` up to `∂Q`
with the mirror tangential conditions and bound `L` (`IsSmoothStateMirror L`), with multiplier
functionals `L²`-bounded by `L`: the scheme (6.5) with source `P_{Ṽₕ¹} f` (`mirrorSource`) has a
solution starting from the dynamic part of the elliptic projection (6.4) of the exact initial
state, and for `t ∈ [0,T]`
`(‖σ − σₕ‖² + ‖u − uₕ‖² + ‖M − Mₕ‖² + ‖ρ − ρₕ‖²)^{1/2}(t) ≤ K L (1 + t) h_N`.
The hypotheses of `Feec.BGG.ExactWave.exists_discreteSolution_rate_harm` are discharged:
`HarmonicStability` modulo `𝔥 = span{dxₐ ⊗ eₐ}` (`mirror_harmonicStability`; `Stability` fails),
(5.4) (`mirrorFEM_compatible`), `S₀,ₕ` onto (`mirrorWave_S0_surjective`), `K₀` from Prop 5.9(1)
(`mirrorFEM_happ0`), `K₁` from the regular potentials of the bottom row (`mirrorFEMReg`,
proved, no regularity hypothesis) and `𝔥 ⊆ Ṽₕ¹` (`harmBot_le`), the interpolation errors from
the parity-smoothed projections (`mirrorFEM_strangData_le`).
See [QuennevilleBelair2015], §6.3, (6.5), Table 6.1, and §6.2, (6.4), Prop 6.2. -/
theorem mirrorWave_rate :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T) {f : ℝ → Wv W1}
      (_hf : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave mirrorBGGSegment T (mirrorSrcFun f))
      {L : ℝ}, 0 ≤ L →
      (∀ t ∈ Icc 0 T, IsSmoothStateMirror L (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) ∧
        IsSmoothStateMirror L (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t)) →
      (∀ t ∈ Icc 0 T, ∀ μ : TU1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖) →
      ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N f),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (mirrorWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((mirrorFEM hT hB N).ellipticDataH (s.σ 0) (s.φ 0) (s.u 0)
              (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 +
          ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ K * L * (1 + t) * meshSize N := by
  have hh0 := mirrorFEM_happ0 hT hB
  obtain ⟨C0, hh1⟩ := hh0
  have hC00 := hh1.1
  have hhapp := hh1.2
  have hC := hT.two_mul_nonneg
  have hreg := mirrorRegConst_nonneg hC
  have ex1 : ∃ x : ℝ, x = C0 + mirrorRegConst C := ⟨_, rfl⟩
  obtain ⟨Capp, hCapp_def⟩ := ex1
  have hCapp0 : 0 ≤ Capp := by rw [hCapp_def]; linarith
  have ex2 : ∃ x : ℝ, x = (2 * Real.pi)⁻¹ := ⟨_, rfl⟩
  obtain ⟨Cp, hCp⟩ := ex2
  have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
  have ex3 : ∃ x : ℝ, x = √(1 + (2 * Real.pi)⁻¹ ^ 2) := ⟨_, rfl⟩
  obtain ⟨Creg, hCreg⟩ := ex3
  have hCreg0 : 0 ≤ Creg := by rw [hCreg]; positivity
  have ex4 : ∃ x : ℝ, x = √(1 + Cp ^ 2) * (1 + 2 * C * (1 + 1 * Creg)) := ⟨_, rfl⟩
  obtain ⟨wa, hwa⟩ := ex4
  have ex5 : ∃ x : ℝ, x = (1 + (1 + 2 * C) * Real.sqrt 2) * Creg := ⟨_, rfl⟩
  obtain ⟨wb, hwb⟩ := ex5
  have hwa0 : 0 ≤ wa := by rw [hwa]; positivity
  have hwb0 : 0 ≤ wb := by rw [hwb]; positivity
  have ex6 : ∃ x : ℝ, x = 1 + (Fintype.card (formIdx 3 ((2 : ℕ) : ℤ)) : ℝ) := ⟨_, rfl⟩
  obtain ⟨cM, hcM⟩ := ex6
  have hcM0 : 0 ≤ cM := by rw [hcM]; positivity
  have ex7 : ∃ x : ℝ,
      x = mirrorInterpConst C + Capp ^ 2 + (Capp * ((wa + wb) * cM)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ := ex7
  have hKd0 : 0 ≤ Kd := by rw [hKd]; have := mirrorInterpConst_nonneg C; positivity
  have ex8 : ∃ x : ℝ, x = √(2 * (Feec.BGG.Discrete.strangConst Cp + 1)) := ⟨_, rfl⟩
  obtain ⟨Ks, hKs⟩ := ex8
  have hKs0 : 0 ≤ Ks := by rw [hKs]; positivity
  refine ⟨2 * Ks * √Kd, by positivity, fun N T hT0 f hf s L hL0 hsm hmult => ?_⟩
  have hh : 0 ≤ meshSize N := (meshSize_pos N).le
  have HS : Feec.BGG.HarmonicStability mirrorBGGSegment harmBot Cp (Real.sqrt 2) := by
    rw [hCp]; exact mirror_harmonicStability
  have Bd := mirrorFEM_bounded hT hB N
  have h54 := mirrorFEM_compatible hT hB N
  have happ : ∀ ψ ∈ (mirrorFEM hT hB N).Vt0h,
      ‖mirrorBGGSegment.S0 ψ - (mirrorFEM hT hB N).S0h ψ‖ ^ 2 ≤
        (Capp * meshSize N) ^ 2 * Feec.BGG.graphSq mirrorBGGSegment.dt0 ψ := fun ψ hψ => by
    refine (hhapp N ψ hψ).trans (mul_le_mul_of_nonneg_right ?_ (Feec.BGG.graphSq_nonneg _ _))
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right
      (by rw [hCapp_def]; linarith) hh) 2
  have Rg := mirrorFEMReg hT hB N (by rw [hCapp_def]; linarith : mirrorRegConst C ≤ Capp)
  have hK0 : ∀ ℓ : TU1 →ₗ[ℝ] ℝ, (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → ∀ ψ ∈ (mirrorFEM hT hB N).Vt0h,
      |ℓ ((mirrorBGGSegment.S0 - (mirrorFEM hT hB N).S0h) ψ)| ≤
        (L * Capp * meshSize N) * √(Feec.BGG.graphSq mirrorBGGSegment.dt0 ψ) := fun ℓ hℓ =>
    Feec.BGG.Discrete.consistency_S0_of_approx hh hCapp0 hL0 ℓ hℓ happ
  have hK1 : ∀ z : W2, IsCsFormPart ∅ 2 L z → (∀ w : TU1, |⟪z, tD1 w⟫| ≤ L * ‖w‖) →
      ∀ v ∈ (mirrorFEM hT hB N).Vt1h,
      |⟪z, (mirrorBGGSegment.S1 - (mirrorFEM hT hB N).S1h) v⟫| ≤
        (Capp * meshSize N * ((wa + wb) * (cM * L))) * √((mirrorFEM hT hB N).gnSq v) := by
    intro z hz hzd v hv
    have hzn : ‖z‖ ≤ cM * L := (hz.norm_le hL0).trans (by rw [hcM]; nlinarith)
    have hzd' : ∀ w : TU1, |⟪z, mirrorBGGSegment.d1 w⟫| ≤ (cM * L) * ‖w‖ := fun w =>
      (hzd w).trans (mul_le_mul_of_nonneg_right (by rw [hcM]; nlinarith) (norm_nonneg _))
    have hw := HS.weakConsistency_of_regularPotential_of_bound (harmBot_le hT hB N) Bd hh
      hCapp0 Rg happ (by positivity) hzd' v hv
    have hwc : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1
        √(1 + (2 * Real.pi)⁻¹ ^ 2) (‖z‖) (cM * L) ≤ (wa + wb) * (cM * L) := by
      have e : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1
          √(1 + (2 * Real.pi)⁻¹ ^ 2) (‖z‖) (cM * L) = (cM * L) * wa + ‖z‖ * wb := by
        rw [hwa, hwb, hCreg]; unfold Feec.BGG.Discrete.weakConsistencyConst; ring
      rw [e]; nlinarith
    refine hw.trans ?_
    have hg := Feec.BGG.Discrete.sqrt_graphSq_le_sqrt_gnSq (Q := mirrorFEM hT hB N) v
    have hm : 0 ≤ Capp * meshSize N := by positivity
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwc hm)
      (Real.sqrt_nonneg (Feec.BGG.graphSq mirrorBGGSegment.dt1 v))
    have h2 := mul_le_mul_of_nonneg_left hg
      (by positivity : 0 ≤ Capp * meshSize N * ((wa + wb) * (cM * L)))
    exact h1.trans h2
  have hdata : ∀ {σ : TU0} {φ : BU0} {u : BU1} {M : W2} {ρ' : Wv W2},
      IsSmoothStateMirror L σ φ u M ρ' → (mirrorFEM hT hB N).strangData σ φ u M ρ'
        (L * Capp * meshSize N) (Capp * meshSize N * ((wa + wb) * (cM * L))) ≤
          (√Kd * L * meshSize N) ^ 2 := by
    intro σ φ u M ρ' hs
    refine (mirrorFEM_strangData_le hT hB N hs _ _).trans (le_of_eq ?_)
    rw [show (√Kd * L * meshSize N) ^ 2 = √Kd ^ 2 * (L * meshSize N) ^ 2 by ring,
      Real.sq_sqrt hKd0, hKd]
    ring
  have hrate := s.exists_discreteSolution_rate_harm (mirrorFEM hT hB N) HS h54
    (K0 := L * Capp * meshSize N) (K1 := Capp * meshSize N * ((wa + wb) * (cM * L)))
    (c := √Kd * L) (h := meshSize N) (mirrorWave_S0_surjective hT hB N) hT0
    (continuousOn_mirrorSource hT hB N hf) (fun t _ v => (inner_mirrorSource hT hB N f t v).symm)
    (fun t ht => hK0 (s.ℓ t) fun μ => (hmult t ht μ).1)
    (fun t ht => hK0 (s.ℓ' t) fun μ => (hmult t ht μ).2)
    (fun t ht => hK1 (s.M t) (hsm t ht).1.2.2.2.2.1 (hsm t ht).1.2.2.2.2.2.1)
    (fun t ht => hK1 (s.M' t) (hsm t ht).2.2.2.2.2.1 (hsm t ht).2.2.2.2.2.2.1)
    (fun t ht => hdata (hsm t ht).1) (fun t ht => hdata (hsm t ht).2)
  obtain ⟨sh, h0, hb⟩ := hrate
  refine ⟨sh, h0, fun t ht => (hb t ht).trans (le_of_eq ?_)⟩
  rw [abs_of_nonneg (by positivity : 0 ≤ √Kd * L), abs_of_nonneg hh, ← hKs]
  ring

end Rate


/-! ### Non-vacuity: the stationary harmonic modes -/

section Witness

open ExteriorFibre (IsDeg)

end Witness


/-! ### Convergence without rate, by density -/

section Converge

open scoped Topology LinearPMap

/-- **The parity-smoothed projections converge strongly**: `‖x − π_N x‖ → 0` for every
`x ∈ L²Λᵏ(Q)` (`‖x − π_N x‖ ≤ (1 + 2C) dist(x, V̊ₕᵏ)` and `V̊ₕᵏ ⊆ V_{h,Γ_J}ᵏ` is dense). -/
theorem _root_.Feec.Models.Cube.FEM.ParitySmoothingEstimates.tendsto_norm_sub_proj
    {J : Finset (Fin 3)} {S : PolySeq} {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3}
    {C : ℝ} (hE : ParitySmoothingEstimates 3 J S ρ C) (k : ℤ)
    (x : L2F ℝ (cubeDomain 3) (formIdx 3 k)) :
    Tendsto (fun N => ‖x - (hE.proj N).π k x‖) atTop (𝓝 0) := by
  have hC := hE.two_mul_nonneg
  have hlim := (tendsto_infDist_polyMin (n := 3) S k x).const_mul (1 + 2 * C)
  rw [mul_zero] at hlim
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hlim
  refine ((hE.proj N).norm_sub_π_le_infDist hC (hE.norm_proj_le N k) x).trans ?_
  exact mul_le_mul_of_nonneg_left (Metric.infDist_le_infDist_of_subset
    (polyMin_V_le_polyPartial_V S N J k) ⟨0, Submodule.zero_mem _⟩) (by linarith)

/-- **Uniform convergence of the projections along a continuous trajectory** on `[0,T]`. -/
theorem _root_.Feec.Models.Cube.FEM.ParitySmoothingEstimates.eventually_norm_sub_proj_le
    {J : Finset (Fin 3)} {S : PolySeq} {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3}
    {C : ℝ} (hE : ParitySmoothingEstimates 3 J S ρ C) (k : ℤ) {T : ℝ}
    {g : ℝ → L2F ℝ (cubeDomain 3) (formIdx 3 k)} (hg : ContinuousOn g (Icc 0 T)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, ‖g t - (hE.proj N).π k (g t)‖ ≤ ε :=
  (Subcomplex.CochainProjection.eventually_forall_norm_sub_π_le hE.proj hE.two_mul_nonneg
    (fun N => hE.norm_proj_le N k) (hE.tendsto_norm_sub_proj k)
    (isCompact_Icc.image_of_continuousOn hg) hε).mono fun _ hN _ ht =>
      hN _ (mem_image_of_mem g ht)

/-- **Dense multipliers**: on a compact set of `L²Λ²(Q)`, every point is `δ`-close to a point of
`D(d_max*)` (here `|⟪z, d w⟫| ≤ c ‖w‖` on `HΛ¹(Q)`), with a common bound `c`. -/
theorem exists_adjoint_approx {K : Set W2} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ K, ∃ z : W2, ‖y - z‖ < δ ∧ ‖z‖ ≤ c ∧
      ∀ w : TU1, |⟪z, tD1 w⟫| ≤ c * ‖w‖ := by
  have hd : Dense ((TD1.domain : Set W1)) := by
    have h := (complexPart 3 ∅).dense 1 2
    rwa [complexPart_d12] at h
  have hdense : Dense (((TD1)†).domain : Set W2) := by
    have h := (complexPart 3 ∅).dense_adjoint_domain 1 2
    rwa [complexPart_d12] at h
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hK (half_pos hδ)
  have hz : ∀ y : W2, ∃ z ∈ ((TD1)†).domain, dist y z < δ / 2 := fun y =>
    hdense.exists_dist_lt y (half_pos hδ)
  choose Z hZ hZd using hz
  let c : ℝ := ∑ y ∈ htf.toFinset, (‖Z y‖ + ‖(TD1)† ⟨Z y, hZ y⟩‖)
  have hc : ∀ y ∈ t, ‖Z y‖ + ‖(TD1)† ⟨Z y, hZ y⟩‖ ≤ c := fun y hy =>
    Finset.single_le_sum (f := fun y => ‖Z y‖ + ‖(TD1)† ⟨Z y, hZ y⟩‖)
      (fun _ _ => by positivity) (htf.mem_toFinset.2 hy)
  refine ⟨c, Finset.sum_nonneg fun _ _ => by positivity, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcov hx)
  have hcy := hc y hy
  refine ⟨Z y, ?_, ?_, fun w => ?_⟩
  · have h1 := dist_triangle x y (Z y)
    have h2 := Metric.mem_ball.1 hxy
    have h3 := hZd y
    rw [← dist_eq_norm]
    linarith
  · have := norm_nonneg ((TD1)† ⟨Z y, hZ y⟩)
    linarith
  · have e : ⟪Z y, tD1 w⟫ = ⟪(TD1)† ⟨Z y, hZ y⟩, (w : W1)⟫ :=
      (LinearPMap.adjoint_isFormalAdjoint hd ⟨Z y, hZ y⟩ w).symm
    rw [e]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := norm_nonneg ((TD1)† ⟨Z y, hZ y⟩)
    have hw : ‖(w : W1)‖ = ‖w‖ := rfl
    rw [hw]
    exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg (Z y)]) (norm_nonneg _)


variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- **Closeness of a mirror state to its projections** at level `δ`: the `L²` projection errors of
`σ`, `dφ`, `u`, `du`, `M`, `ρ` and `S¹u` that make up the Strang data of (6.4). -/
def MirrorClose (N : ℕ) (δ : ℝ) (σ : TU0) (φ : BU0) (u : BU1) (M : W2) (ρ' : Wv W2) : Prop :=
  ‖(σ : W0) - (hT.proj N).π 0 (σ : W0)‖ ≤ δ ∧
    (∀ a, ‖BD0 a (φ a) - ((hB a).proj N).π 1 (BD0 a (φ a))‖ ≤ δ) ∧
    (∀ a, ‖(u a : W1) - ((hB a).proj N).π 1 (u a : W1)‖ ≤ δ) ∧
    (∀ a, ‖BD1 a (u a) - ((hB a).proj N).π 2 (BD1 a (u a))‖ ≤ δ) ∧
    ‖M - (hT.proj N).π 2 M‖ ≤ δ ∧
    (∀ a, ‖ρ' a - ((hB a).proj N).π 2 (ρ' a)‖ ≤ δ) ∧
    ‖mS1 u - (hT.proj N).π 2 (mS1 u)‖ ≤ δ

/-- The constant of `mirrorFEM_strangData_le_of_close`. -/
def mirrorCloseConst (C : ℝ) : ℝ := 1 + 3 + (1 + 8 * C ^ 2) * 3 + 3 + 1 + 3 + 1

theorem mirrorCloseConst_nonneg (C : ℝ) : 0 ≤ mirrorCloseConst C := by
  unfold mirrorCloseConst; positivity

set_option maxHeartbeats 1000000 in
/-- **The Strang data of (6.4) from the projection errors**: `≤ mirrorCloseConst C · δ² + K₀² + K₁²`
for a state `δ`-close to its projections (no regularity). -/
theorem mirrorFEM_strangData_le_of_close (N : ℕ) {δ : ℝ} {σ : TU0} {φ : BU0} {u : BU1}
    {M : W2} {ρ' : Wv W2} (hc : MirrorClose hT hB N δ σ φ u M ρ') (K0 K1 : ℝ) :
    (mirrorFEM hT hB N).strangData σ φ u M ρ' K0 K1 ≤
      mirrorCloseConst C * δ ^ 2 + K0 ^ 2 + K1 ^ 2 := by
  obtain ⟨hσ, hφ, hu, hdu, hM, hρ, hSu⟩ := hc
  have h1 : ‖(mirrorFEM hT hB N).P0 σ - σ‖ ≤ δ := by rw [norm_sub_rev]; exact hσ
  have h2 : ‖mirrorBGGSegment.dt0 ((mirrorFEM hT hB N).Pt0 φ - φ)‖ ^ 2 ≤ 3 * δ ^ 2 := by
    change ‖bD0 (projB0 (fun a => (hB a).proj N) φ - φ)‖ ^ 2 ≤ _
    rw [norm_sq_bD0]
    refine WeakSymmetry.sum_sq_le_three fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have e : BD0 a ((projB0 (fun a => (hB a).proj N) φ - φ) a) =
        ((hB a).proj N).π 1 (BD0 a (φ a)) - BD0 a (φ a) := by
      rw [PiLp.sub_apply, LinearPMap.map_sub]
      congr 1
      exact dPart0_π ((hB a).proj N) (φ a)
    rw [e, norm_sub_rev]
    exact hφ a
  have h3a : ‖(mirrorFEM hT hB N).Pt1 u - u‖ ^ 2 ≤ 3 * δ ^ 2 := by
    change ‖projB1 (fun a => (hB a).proj N) u - u‖ ^ 2 ≤ _
    rw [norm_sq_BU1]
    refine WeakSymmetry.sum_sq_le_three fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    change ‖((hB a).proj N).π 1 (u a : W1) - (u a : W1)‖ ≤ _
    rw [norm_sub_rev]
    exact hu a
  have h3b := mirrorFEM_err_S1h hT hB N ((mirrorFEM hT hB N).Pt1 u - u)
  have h3c : ‖mirrorBGGSegment.dt1 ((mirrorFEM hT hB N).Pt1 u - u)‖ ^ 2 ≤ 3 * δ ^ 2 := by
    change ‖bD1 (projB1 (fun a => (hB a).proj N) u - u)‖ ^ 2 ≤ _
    rw [norm_sq_bD1]
    refine WeakSymmetry.sum_sq_le_three fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have e : BD1 a ((projB1 (fun a => (hB a).proj N) u - u) a) =
        ((hB a).proj N).π 2 (BD1 a (u a)) - BD1 a (u a) := by
      rw [PiLp.sub_apply, LinearPMap.map_sub]
      congr 1
      exact dPart1_π ((hB a).proj N) (u a)
    rw [e, norm_sub_rev]
    exact hdu a
  have h4 : ‖(mirrorFEM hT hB N).P2 M - M‖ ≤ δ := by rw [norm_sub_rev]; exact hM
  have h5 : ‖(mirrorFEM hT hB N).Pt2 ρ' - ρ'‖ ^ 2 ≤ 3 * δ ^ 2 := by
    change ‖projB2 (fun a => (hB a).proj N) ρ' - ρ'‖ ^ 2 ≤ _
    rw [PiLp.norm_sq_eq_of_L2]
    refine WeakSymmetry.sum_sq_le_three fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    change ‖((hB a).proj N).π 2 (ρ' a) - ρ' a‖ ≤ _
    rw [norm_sub_rev]
    exact hρ a
  have h6 : ‖mirrorBGGSegment.S1 u - (mirrorFEM hT hB N).S1h u‖ ≤ δ := hSu
  have q1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have q4 := pow_le_pow_left₀ (norm_nonneg _) h4 2
  have q6 := pow_le_pow_left₀ (norm_nonneg _) h6 2
  have e1 : (mirrorFEM hT hB N).strangData σ φ u M ρ' K0 K1 =
      ‖(mirrorFEM hT hB N).P0 σ - σ‖ ^ 2 +
        ‖mirrorBGGSegment.dt0 ((mirrorFEM hT hB N).Pt0 φ - φ)‖ ^ 2 +
        (‖(mirrorFEM hT hB N).Pt1 u - u‖ ^ 2 +
          ‖(mirrorFEM hT hB N).S1h ((mirrorFEM hT hB N).Pt1 u - u)‖ ^ 2 +
          ‖mirrorBGGSegment.dt1 ((mirrorFEM hT hB N).Pt1 u - u)‖ ^ 2) +
        ‖(mirrorFEM hT hB N).P2 M - M‖ ^ 2 + ‖(mirrorFEM hT hB N).Pt2 ρ' - ρ'‖ ^ 2 + K0 ^ 2 +
        K1 ^ 2 + ‖mirrorBGGSegment.S1 u - (mirrorFEM hT hB N).S1h u‖ ^ 2 := rfl
  have hS1h : ‖(mirrorFEM hT hB N).S1h ((mirrorFEM hT hB N).Pt1 u - u)‖ ^ 2 ≤
      8 * C ^ 2 * (3 * δ ^ 2) :=
    h3b.trans (mul_le_mul_of_nonneg_left h3a (by positivity))
  rw [e1]
  unfold mirrorCloseConst
  nlinarith

/-- `K₀` of the Strang bound for an `L²`-bounded multiplier functional: `Λ C_app h_N`. -/
theorem exists_mirrorFEM_K0 : ∃ Capp : ℝ, 0 ≤ Capp ∧ ∀ (N : ℕ) (L : ℝ), 0 ≤ L →
    ∀ ℓ : TU1 →ₗ[ℝ] ℝ, (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → ∀ ψ ∈ (mirrorFEM hT hB N).Vt0h,
      |ℓ ((mirrorBGGSegment.S0 - (mirrorFEM hT hB N).S0h) ψ)| ≤
        L * Capp * meshSize N * √(Feec.BGG.graphSq mirrorBGGSegment.dt0 ψ) := by
  obtain ⟨C0, hC00, hhapp⟩ := mirrorFEM_happ0 hT hB
  exact ⟨C0, hC00, fun N L hL0 ℓ hℓ => Feec.BGG.Discrete.consistency_S0_of_approx
    (meshSize_pos N).le hC00 hL0 ℓ hℓ (hhapp N)⟩

set_option maxHeartbeats 1000000 in
/-- `K₁` of the Strang bound for a multiplier `z ∈ D(d_max*)`: `|⟪z, (S₁ − S₁,ₕ)v⟫| ≤ K h_N c ‖v‖`
when `‖z‖ ≤ c` and `|⟪z, dw⟫| ≤ c ‖w‖` (regular potentials of the bottom row). -/
theorem exists_mirrorFEM_K1 : ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (z : W2) (c : ℝ), 0 ≤ c → ‖z‖ ≤ c →
    (∀ w : TU1, |⟪z, tD1 w⟫| ≤ c * ‖w‖) → ∀ v ∈ (mirrorFEM hT hB N).Vt1h,
      |⟪z, (mirrorBGGSegment.S1 - (mirrorFEM hT hB N).S1h) v⟫| ≤
        K * meshSize N * c * √((mirrorFEM hT hB N).gnSq v) := by
  obtain ⟨C0, hh1⟩ := mirrorFEM_happ0 hT hB
  have hC00 := hh1.1
  have hhapp := hh1.2
  have hC := hT.two_mul_nonneg
  have hreg := mirrorRegConst_nonneg hC
  have ex1 : ∃ x : ℝ, x = C0 + mirrorRegConst C := ⟨_, rfl⟩
  obtain ⟨Capp, hCapp_def⟩ := ex1
  have hCapp0 : 0 ≤ Capp := by rw [hCapp_def]; linarith
  have ex2 : ∃ x : ℝ, x = (2 * Real.pi)⁻¹ := ⟨_, rfl⟩
  obtain ⟨Cp, hCp⟩ := ex2
  have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
  have ex3 : ∃ x : ℝ, x = √(1 + (2 * Real.pi)⁻¹ ^ 2) := ⟨_, rfl⟩
  obtain ⟨Creg, hCreg⟩ := ex3
  have hCreg0 : 0 ≤ Creg := by rw [hCreg]; positivity
  have ex4 : ∃ x : ℝ, x = √(1 + Cp ^ 2) * (1 + 2 * C * (1 + 1 * Creg)) := ⟨_, rfl⟩
  obtain ⟨wa, hwa⟩ := ex4
  have ex5 : ∃ x : ℝ, x = (1 + (1 + 2 * C) * Real.sqrt 2) * Creg := ⟨_, rfl⟩
  obtain ⟨wb, hwb⟩ := ex5
  have hwa0 : 0 ≤ wa := by rw [hwa]; positivity
  have hwb0 : 0 ≤ wb := by rw [hwb]; positivity
  refine ⟨Capp * (wa + wb), mul_nonneg hCapp0 (add_nonneg hwa0 hwb0), fun N z c hc0 hzn hzd v hv => ?_⟩
  have hh : 0 ≤ meshSize N := (meshSize_pos N).le
  have HS := mirror_harmonicStability
  rw [← hCp] at HS
  have Bd := mirrorFEM_bounded hT hB N
  have happ : ∀ ψ ∈ (mirrorFEM hT hB N).Vt0h,
      ‖mirrorBGGSegment.S0 ψ - (mirrorFEM hT hB N).S0h ψ‖ ^ 2 ≤
        (Capp * meshSize N) ^ 2 * Feec.BGG.graphSq mirrorBGGSegment.dt0 ψ := fun ψ hψ => by
    refine (hhapp N ψ hψ).trans (mul_le_mul_of_nonneg_right ?_ (Feec.BGG.graphSq_nonneg _ _))
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right
      (by rw [hCapp_def]; linarith) hh) 2
  have Rg := mirrorFEMReg hT hB N (by rw [hCapp_def]; linarith : mirrorRegConst C ≤ Capp)
  have hw := HS.weakConsistency_of_regularPotential_of_bound (harmBot_le hT hB N) Bd hh
    hCapp0 Rg happ hc0 hzd v hv
  have hwc : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1
      √(1 + (2 * Real.pi)⁻¹ ^ 2) (‖z‖) c ≤ (wa + wb) * c := by
    have e : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1
        √(1 + (2 * Real.pi)⁻¹ ^ 2) (‖z‖) c = c * wa + ‖z‖ * wb := by
      rw [hwa, hwb, hCreg]; unfold Feec.BGG.Discrete.weakConsistencyConst; ring
    rw [e]; nlinarith
  refine hw.trans ?_
  have hg := Feec.BGG.Discrete.sqrt_graphSq_le_sqrt_gnSq (Q := mirrorFEM hT hB N) v
  have hm : 0 ≤ Capp * meshSize N := by positivity
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwc hm)
    (Real.sqrt_nonneg (Feec.BGG.graphSq mirrorBGGSegment.dt1 v))
  have h2 := mul_le_mul_of_nonneg_left hg
    (by positivity : 0 ≤ Capp * meshSize N * ((wa + wb) * c))
  refine (h1.trans h2).trans (le_of_eq ?_)
  ring

/-- The `L²` part of `K₁`: `|⟪z, (S₁ − S₁,ₕ)v⟫| ≤ ‖z‖ (1 + 2C) √2 ‖v‖_{Γₕ}` for every `z`. -/
theorem mirrorFEM_K1_rest (N : ℕ) (z : W2) (v : BU1) :
    |⟪z, (mirrorBGGSegment.S1 - (mirrorFEM hT hB N).S1h) v⟫| ≤
      ‖z‖ * ((1 + 2 * C) * √2) * √((mirrorFEM hT hB N).gnSq v) := by
  have hC := hT.two_mul_nonneg
  have e : (mirrorBGGSegment.S1 - (mirrorFEM hT hB N).S1h) v =
      mS1 v - (hT.proj N).π 2 (mS1 v) := rfl
  have h1 : ‖mS1 v - (hT.proj N).π 2 (mS1 v)‖ ≤ (1 + 2 * C) * ‖mS1 v‖ := by
    have := hT.norm_proj_le N 2 (mS1 v)
    have := norm_sub_le (mS1 v) ((hT.proj N).π 2 (mS1 v))
    linarith
  have h2 : ‖mS1 v‖ ≤ √2 * ‖v‖ := by
    have h := norm_wsL2_sq_le (Ω := cubeDomain 3) 1 (bIncl1 v)
    have h1 : (((1 : ℤ) : ℝ) + 1) = 2 := by norm_num
    rw [h1, norm_bIncl1] at h
    have h' : ‖mS1 v‖ ^ 2 ≤ (√2 * ‖v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; exact h
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h'
  have h3 : ‖v‖ ≤ √((mirrorFEM hT hB N).gnSq v) := by
    have h := Real.abs_le_sqrt (x := ‖v‖) (y := (mirrorFEM hT hB N).gnSq v) (by
      unfold Feec.BGG.Discrete.gnSq
      exact le_add_of_le_of_nonneg (le_add_of_nonneg_right (by positivity)) (by positivity))
    rwa [abs_norm] at h
  rw [e]
  refine (abs_real_inner_le_norm _ _).trans ?_
  have h4 : ‖mS1 v - (hT.proj N).π 2 (mS1 v)‖ ≤
      (1 + 2 * C) * √2 * √((mirrorFEM hT hB N).gnSq v) := by
    refine h1.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
      (by linarith)
  calc ‖z‖ * ‖mS1 v - (hT.proj N).π 2 (mS1 v)‖ ≤
      ‖z‖ * ((1 + 2 * C) * √2 * √((mirrorFEM hT hB N).gnSq v)) :=
        mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = _ := by ring


/-- **`K₁ → 0` uniformly on a compact set of multipliers**, with no regularity of the multipliers:
split `z = z' + (z − z')` with `z' ∈ D(d_max*)` close to `z` (`exists_adjoint_approx`). -/
theorem eventually_mirrorFEM_K1 {K : Set W2} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ z ∈ K, ∀ v ∈ (mirrorFEM hT hB N).Vt1h,
      |⟪z, (mirrorBGGSegment.S1 - (mirrorFEM hT hB N).S1h) v⟫| ≤
        ε * √((mirrorFEM hT hB N).gnSq v) := by
  have hC := hT.two_mul_nonneg
  have hA : 0 ≤ (1 + 2 * C) * √2 := by positivity
  have ex : ∃ A : ℝ, A = (1 + 2 * C) * √2 := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ := ex
  rw [← hAdef] at hA
  have hδ : 0 < ε / (2 * (A + 1)) := by positivity
  obtain ⟨c, hc0, hc⟩ := exists_adjoint_approx hK hδ
  obtain ⟨K1, hK10, hK1⟩ := exists_mirrorFEM_K1 hT hB
  have hlim : Tendsto (fun N => K1 * meshSize N * c) atTop (𝓝 0) := by
    have := (tendsto_meshSize.const_mul K1).mul_const c
    simpa using this
  have hhalf : ∀ x : ℝ, x < ε / (2 * (A + 1)) → x * A ≤ ε / 2 := fun x hx => by
    have h4 : x * A ≤ ε / (2 * (A + 1)) * A := mul_le_mul_of_nonneg_right hx.le hA
    have h5 : ε / (2 * (A + 1)) * A ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  filter_upwards [hlim.eventually (Iic_mem_nhds (half_pos hε))] with N hN z hz v hv
  obtain ⟨z', hzz', hz'n, hz'd⟩ := hc z hz
  have h1 := hK1 N z' c hc0 hz'n hz'd v hv
  have h2 := mirrorFEM_K1_rest hT hB N (z - z') v
  rw [← hAdef] at h2
  have h3 := hhalf _ hzz'
  have hN' : K1 * meshSize N * c ≤ ε / 2 := hN
  have ex1 : ∃ X : W2, X = (mirrorBGGSegment.S1 - (mirrorFEM hT hB N).S1h) v := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ := ex1
  have ex2 : ∃ G : ℝ, G = √((mirrorFEM hT hB N).gnSq v) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ := ex2
  rw [← hX, ← hG] at h1 h2 ⊢
  have hg : 0 ≤ G := by rw [hG]; exact Real.sqrt_nonneg _
  clear hX hG hz'd hc hK1 hlim hN
  have e : ⟪z, X⟫ = ⟪z - z', X⟫ + ⟪z', X⟫ := by rw [inner_sub_left]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h6 : ‖z - z'‖ * A * G ≤ ε / 2 * G := mul_le_mul_of_nonneg_right h3 hg
  have h7 : K1 * meshSize N * c * G ≤ ε / 2 * G := mul_le_mul_of_nonneg_right hN' hg
  linarith

/-- **A continuous mirror trajectory is uniformly close to its projections** for `N` large. -/
theorem eventually_mirrorClose {T : ℝ} {σ : ℝ → TU0} {φ : ℝ → BU0} {u : ℝ → BU1}
    {M : ℝ → W2} {ρ' : ℝ → Wv W2} (hσ : ContinuousOn σ (Icc 0 T))
    (hφ : ContinuousOn (fun t => mirrorBGGSegment.dt0 (φ t)) (Icc 0 T))
    (hu : ContinuousOn u (Icc 0 T))
    (hdu : ContinuousOn (fun t => mirrorBGGSegment.dt1 (u t)) (Icc 0 T))
    (hM : ContinuousOn M (Icc 0 T)) (hρ : ContinuousOn ρ' (Icc 0 T))
    (hSu : ContinuousOn (fun t => mirrorBGGSegment.S1 (u t)) (Icc 0 T))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, MirrorClose hT hB N δ (σ t) (φ t) (u t) (M t) (ρ' t) := by
  have c1 : ContinuousOn (fun t => (σ t : W0)) (Icc 0 T) :=
    continuous_subtype_val.comp_continuousOn hσ
  have c2 : ∀ a : Fin 3, ContinuousOn (fun t => BD0 a (φ t a)) (Icc 0 T) := fun a =>
    (continuous_subtype_val.comp
      (PiLp.continuous_apply 2 (fun b : Fin 3 => (BD1 b).domain) a)).comp_continuousOn hφ
  have c3 : ∀ a : Fin 3, ContinuousOn (fun t => (u t a : W1)) (Icc 0 T) := fun a =>
    (continuous_subtype_val.comp
      (PiLp.continuous_apply 2 (fun b : Fin 3 => (BD1 b).domain) a)).comp_continuousOn hu
  have c4 : ∀ a : Fin 3, ContinuousOn (fun t => BD1 a (u t a)) (Icc 0 T) := fun a =>
    (PiLp.continuous_apply 2 _ a).comp_continuousOn hdu
  have c6 : ∀ a : Fin 3, ContinuousOn (fun t => ρ' t a) (Icc 0 T) := fun a =>
    (PiLp.continuous_apply 2 _ a).comp_continuousOn hρ
  have e1 := hT.eventually_norm_sub_proj_le 0 c1 hδ
  have e2 := Filter.eventually_all.2 fun a => (hB a).eventually_norm_sub_proj_le 1 (c2 a) hδ
  have e3 := Filter.eventually_all.2 fun a => (hB a).eventually_norm_sub_proj_le 1 (c3 a) hδ
  have e4 := Filter.eventually_all.2 fun a => (hB a).eventually_norm_sub_proj_le 2 (c4 a) hδ
  have e5 := hT.eventually_norm_sub_proj_le 2 hM hδ
  have e6 := Filter.eventually_all.2 fun a => (hB a).eventually_norm_sub_proj_le 2 (c6 a) hδ
  have e7 := hT.eventually_norm_sub_proj_le 2 hSu hδ
  filter_upwards [e1, e2, e3, e4, e5, e6, e7] with N h1 h2 h3 h4 h5 h6 h7 t ht
  exact ⟨h1 t ht, fun a => h2 a t ht, fun a => h3 a t ht, fun a => h4 a t ht, h5 t ht,
    fun a => h6 a t ht, h7 t ht⟩


set_option maxHeartbeats 4000000 in
/-- **Convergence of the mirror scheme (6.5) on the cube for energy-space solutions** (no rate,
by density): for every `T > 0`, every `L²` source `f` continuous on `[0,T]`, every classical
solution `s` of (6.2) for the mirror data (`ExactWave mirrorBGGSegment`, whose regularity is the
continuity of `σ, u, M, ρ, dφ, du, S¹u` in `L²`), with multiplier functionals `L²`-bounded on
`[0,T]`, and every `ε > 0`: for all `N` large the scheme (6.5) with source `P_{Ṽₕ¹} f` has a
solution starting from the dynamic part of the elliptic projection (6.4) of the exact initial
state with `(‖σ − σₕ‖² + ‖u − uₕ‖² + ‖M − Mₕ‖² + ‖ρ − ρₕ‖²)^{1/2}(t) ≤ ε` on `[0,T]`.
No smoothness and no boundary flatness: the projection errors tend to `0` uniformly on the
compact trajectories (`eventually_mirrorClose`), `K₀ = Λ C_app h_N` (`exists_mirrorFEM_K0`) and
`K₁ → 0` by density of `D(d_max*)` (`eventually_mirrorFEM_K1`).
See [QuennevilleBelair2015], §6.3, (6.5), and §6.2, (6.4), Prop 6.2. -/
theorem mirrorWave_converges {T : ℝ} (hT0 : 0 < T) {f : ℝ → Wv W1}
    (hf : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave mirrorBGGSegment T (mirrorSrcFun f))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hmult : ∀ t ∈ Icc 0 T, ∀ μ : TU1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop,
      ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N f),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (mirrorWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((mirrorFEM hT hB N).ellipticDataH (s.σ 0) (s.φ 0) (s.u 0)
              (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 +
          ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ ε := by
  have HS := mirror_harmonicStability
  have ex1 : ∃ Ks : ℝ, Ks = √(2 * (Feec.BGG.Discrete.strangConst (2 * Real.pi)⁻¹ + 1)) :=
    ⟨_, rfl⟩
  obtain ⟨Ks, hKs⟩ := ex1
  have hKs0 : 0 ≤ Ks := by rw [hKs]; exact Real.sqrt_nonneg _
  have ex2 : ∃ η : ℝ, η = ε / (Ks * (2 + 2 * T) + 1) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ := ex2
  have hden : 0 < Ks * (2 + 2 * T) + 1 := by nlinarith
  have hη0 : 0 < η := by rw [hη]; exact div_pos hε hden
  have hηε : η * (Ks * (2 + 2 * T) + 1) = ε := by rw [hη]; exact div_mul_cancel₀ _ hden.ne'
  have hmc := mirrorCloseConst_nonneg C
  have ex3 : ∃ θ : ℝ, θ = η / (mirrorCloseConst C + 2) := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ := ex3
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθη : θ * (mirrorCloseConst C + 2) = η := by
    rw [hθ]; exact div_mul_cancel₀ _ (by positivity)
  have hθle : θ ≤ η := by nlinarith
  have hdat : ∀ x : ℝ, x ≤ mirrorCloseConst C * θ ^ 2 + θ ^ 2 + θ ^ 2 → x ≤ (η * 1) ^ 2 :=
    fun x hx => by nlinarith
  have hK0all := exists_mirrorFEM_K0 hT hB
  obtain ⟨Capp, hK0pair⟩ := hK0all
  have hK0 := hK0pair.2
  have hlim : Tendsto (fun N => L * Capp * meshSize N) atTop (𝓝 0) := by
    have := tendsto_meshSize.const_mul (L * Capp)
    rwa [mul_zero] at this
  have hKc : IsCompact ((s.M '' Icc 0 T) ∪ (s.M' '' Icc 0 T)) :=
    (isCompact_Icc.image_of_continuousOn s.cM).union (isCompact_Icc.image_of_continuousOn s.cM')
  have ev2 := eventually_mirrorFEM_K1 hT hB hKc hθ0
  have ev3 := eventually_mirrorClose hT hB (σ := s.σ) (φ := s.φ) (u := s.u) (M := s.M)
    (ρ' := s.ρ) s.cσ s.cdφ s.cu s.cdu s.cM s.cρ s.cSu hθ0
  have ev4 := eventually_mirrorClose hT hB (σ := s.σ') (φ := s.φ') (u := s.u') (M := s.M')
    (ρ' := s.ρ') s.cσ' s.cdφ' s.cu' s.cdu' s.cM' s.cρ' s.cSu' hθ0
  filter_upwards [hlim.eventually (Iic_mem_nhds hθ0), ev2, ev3, ev4] with N h1 h2 h3 h4
  have h1' : L * Capp * meshSize N ≤ θ := h1
  have hK0' : ∀ ℓ : TU1 →ₗ[ℝ] ℝ, (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → ∀ ψ ∈ (mirrorFEM hT hB N).Vt0h,
      |ℓ ((mirrorBGGSegment.S0 - (mirrorFEM hT hB N).S0h) ψ)| ≤
        θ * √(Feec.BGG.graphSq mirrorBGGSegment.dt0 ψ) := fun ℓ hℓ ψ hψ =>
    (hK0 N L hL0 ℓ hℓ ψ hψ).trans (mul_le_mul_of_nonneg_right h1' (Real.sqrt_nonneg _))
  have hrate := s.exists_discreteSolution_rate_harm (mirrorFEM hT hB N) HS
    (mirrorFEM_compatible hT hB N) (K0 := θ) (K1 := θ) (c := η) (h := 1)
    (mirrorWave_S0_surjective hT hB N) hT0
    (continuousOn_mirrorSource hT hB N hf) (fun t _ v => (inner_mirrorSource hT hB N f t v).symm)
    (fun t ht => hK0' (s.ℓ t) fun μ => (hmult t ht μ).1)
    (fun t ht => hK0' (s.ℓ' t) fun μ => (hmult t ht μ).2)
    (fun t ht v hv => h2 (s.M t) (Or.inl (mem_image_of_mem _ ht)) v hv)
    (fun t ht v hv => h2 (s.M' t) (Or.inr (mem_image_of_mem _ ht)) v hv)
    (fun t ht => hdat _ (mirrorFEM_strangData_le_of_close hT hB N (h3 t ht) θ θ))
    (fun t ht => hdat _ (mirrorFEM_strangData_le_of_close hT hB N (h4 t ht) θ θ))
  obtain ⟨sh, h0, hb⟩ := hrate
  refine ⟨sh, h0, fun t ht => (hb t ht).trans ?_⟩
  rw [← hKs, abs_of_pos hη0, abs_one, mul_one]
  have ht2 : 2 + 2 * t ≤ 2 + 2 * T := by linarith [ht.2]
  have h5 : Ks * η * (2 + 2 * t) ≤ Ks * η * (2 + 2 * T) :=
    mul_le_mul_of_nonneg_left ht2 (by positivity)
  nlinarith


set_option maxHeartbeats 4000000 in
/-- **TSD-type solutions** (the class of [QuennevilleBelair2015], Ch. 6: `σ ≡ 0`, `M ≡ 0`): under
the hypotheses of `mirrorWave_rate`, the discrete `σₕ` and `Mₕ` are `O(h)`, and every bounded
linear constraint `Φ ρ = 0` satisfied by the exact `ρ = B` on `[0,T]` (for instance the symmetry
of `B`) holds for `ρₕ` up to `‖Φ‖ K L (1 + t) h_N`. -/
theorem mirrorWave_rate_tsd :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T) {f : ℝ → Wv W1}
      (_hf : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave mirrorBGGSegment T (mirrorSrcFun f))
      {L : ℝ}, 0 ≤ L →
      (∀ t ∈ Icc 0 T, IsSmoothStateMirror L (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) ∧
        IsSmoothStateMirror L (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t)) →
      (∀ t ∈ Icc 0 T, ∀ μ : TU1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖) →
      (∀ t ∈ Icc 0 T, s.σ t = 0 ∧ s.M t = 0) →
      ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N f),
        ∀ t ∈ Icc 0 T, ‖(sh.σ t : TU0)‖ ≤ K * L * (1 + t) * meshSize N ∧
          ‖(sh.M t : W2)‖ ≤ K * L * (1 + t) * meshSize N ∧
          ∀ Φ : Wv W2 →L[ℝ] Wv W2, Φ (s.ρ t) = 0 →
            ‖Φ (sh.ρ t : Wv W2)‖ ≤ ‖Φ‖ * (K * L * (1 + t) * meshSize N) := by
  have hrate := mirrorWave_rate hT hB
  obtain ⟨K, hKp⟩ := hrate
  refine ⟨K, hKp.1, fun N T hT0 f hf s L hL hsm hmult hz => ?_⟩
  have h := hKp.2 N hT0 hf s hL hsm hmult
  obtain ⟨sh, hsh⟩ := h
  refine ⟨sh, fun t ht => ?_⟩
  have hb := hsh.2 t ht
  have ex : ∃ E : ℝ, E = ‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 +
      ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ := ex
  rw [← hE] at hb
  have hcomp : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ E → x ≤ K * L * (1 + t) * meshSize N := fun x hx hxE =>
    ((abs_of_nonneg hx).symm.le.trans (Real.abs_le_sqrt hxE)).trans hb
  have p1 := sq_nonneg ‖s.σ t - sh.σ t‖
  have p2 := sq_nonneg ‖s.u t - sh.u t‖
  have p3 := sq_nonneg ‖s.M t - sh.M t‖
  have p4 := sq_nonneg ‖s.ρ t - sh.ρ t‖
  have hσ := hcomp ‖s.σ t - sh.σ t‖ (norm_nonneg _) (by rw [hE]; linarith)
  have hM := hcomp ‖s.M t - sh.M t‖ (norm_nonneg _) (by rw [hE]; linarith)
  have hρ := hcomp ‖s.ρ t - sh.ρ t‖ (norm_nonneg _) (by rw [hE]; linarith)
  rw [(hz t ht).1, zero_sub, norm_neg] at hσ
  rw [(hz t ht).2, zero_sub, norm_neg] at hM
  refine ⟨hσ, hM, fun Φ hΦ => ?_⟩
  have e : Φ (sh.ρ t : Wv W2) = -Φ (s.ρ t - sh.ρ t) := by
    rw [map_sub, hΦ, zero_sub, neg_neg]
  rw [e, norm_neg]
  exact (Φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left hρ (norm_nonneg _))

end Converge

end Feec.Models.Cube.MirrorWeakSymmetry
