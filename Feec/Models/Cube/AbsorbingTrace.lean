module

public import Feec.Models.Cube.MirrorTrace
public import Feec.Models.BoundedDomain.Interior

/-!
# Tangential traces and Green's formula for the row-wise curl on the cube

On the cube `Q = (0, ½)³` the boundary consists of the six faces `{x_m = s}`, `m : Fin 3`,
`s ∈ {0, ½}` (`face (m, s)`, with `s = ½` for `true`), each parametrized by the open square
`Sq = (0, ½)²` through `Fin.insertNth m s` (`faceMap`). The outward normal of `face (m, s)` is
`± e_m` (`faceSign`).

* **The boundary space** `Bdry = L²(Sq)^{faces × rows × tangential slots}` (`Bdry`): for every face
  `(m, s)`, every row `i` and every tangential direction `j = m.succAbove j'`, one `L²` function on
  the square. It is `L²(∂Q; ℝ^{3×3}_τ)`: the tangential parts of matrix fields on `∂Q`.
* **Tangential traces** of continuous fields `Φ : Ix → ℝ³ → ℝ`: `tanTrace Φ (m, s) i j' = Φ_{i,j}`
  on the face (`j = m.succAbove j'`), and the **flux trace**
  `fluxTrace Ψ (m, s) i j' = ± (Ψ_i × e_m)_j` (the boundary datum dual to the tangential trace in
  Green's formula).
* **Green's formula** (`inner_curl_sub_inner_curl`): for `C¹` fields `Φ`, `Ψ` on `ℝ³`,
  `⟪curl Φ, Ψ⟫_{L²(Q)} - ⟪Φ, curl Ψ⟫_{L²(Q)} = ⟪tanTrace Φ, fluxTrace Ψ⟫_{Bdry}`, i.e.
  `∫_Q (curl Φ · Ψ - Φ · curl Ψ) = ∫_{∂Q} Σᵢ (n × Φᵢ) · Ψᵢ`, from the divergence theorem on the box
  for `Σᵢ Φᵢ × Ψᵢ` (`integral_sum_pd_eq_faces`).
* **Flux traces separate boundary data** (`eq_zero_of_forall_inner_fluxTrace`): a `β ∈ Bdry`
  orthogonal to the flux traces of all smooth fields is `0` (fields supported near one face, equal
  to a test function of the square on it), i.e. flux traces span a dense subspace. The analogous
  density of tangential traces is not proved.

## References

* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003], §3.5 (traces of
  `H(curl)`, Green's formula)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (boundary conditions on the cube)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Set MeasureTheory Filter Topology Feec.Domain Feec.Models.BoundedDomain

@[expose] public noncomputable section

namespace Feec.Models.Cube.Absorbing

open Geometry

/-! ### Faces of the cube -/

/-- The faces `(m, s)` of the cube: `{x_m = ½}` for `s = true`, `{x_m = 0}` for `s = false`. -/
abbrev Face := Fin 3 × Bool

/-- The coordinate value of a face. -/
def faceVal (s : Bool) : ℝ := if s then 1 / 2 else 0

/-- The outward normal sign of a face: `+1` on `{x_m = ½}`, `-1` on `{x_m = 0}`. -/
def faceSign (s : Bool) : ℝ := if s then 1 else -1

/-- The open square `(0, ½)²` parametrizing each face. -/
abbrev Sq : Set (Fin 2 → ℝ) := Q (Fin 2)

/-- The parametrization `y ↦ Fin.insertNth m s y` of the face `(m, s)`. -/
def faceMap (f : Face) (y : Fin 2 → ℝ) : R3 := f.1.insertNth (faceVal f.2) y

theorem continuous_faceMap (f : Face) : Continuous (faceMap f) :=
  Continuous.finInsertNth f.1 continuous_const continuous_id

theorem Q_ae_eq_Icc {n : ℕ} :
    Q (Fin n) =ᵐ[volume] Icc (0 : Fin n → ℝ) (fun _ => 1 / 2) := by
  have : Q (Fin n) = univ.pi fun _ : Fin n => Ioo (0 : ℝ) (1 / 2) := by
    ext y; simp [Q, openCube]
  rw [this]
  exact Measure.univ_pi_Ioo_ae_eq_Icc

/-- **The divergence theorem on the cube**: for a `C¹` vector field `F` on `ℝ³`,
`∫_Q Σ_m ∂_m F_m = Σ_m (∫_{x_m = ½} F_m - ∫_{x_m = 0} F_m)`. -/
theorem integral_sum_pd_eq_faces {F : Fin 3 → R3 → ℝ} (hF : ∀ m, ContDiff ℝ 1 (F m)) :
    ∫ x in Q (Fin 3), ∑ m, partialDeriv m (F m) x =
      ∑ m, ((∫ y in Sq, F m (faceMap (m, true) y)) - ∫ y in Sq, F m (faceMap (m, false) y)) := by
  set a : Fin 3 → ℝ := 0
  set b : Fin 3 → ℝ := fun _ => 1 / 2
  have hle : a ≤ b := fun i => by simp [a, b]
  have hd : ∀ m y, HasFDerivAt (F m) (fderiv ℝ (F m) y) y :=
    fun m y => ((hF m).differentiable one_ne_zero y).hasFDerivAt
  have hcont : Continuous fun x => ∑ m, fderiv ℝ (F m) x (Pi.single m 1) :=
    continuous_finsetSum _ fun m _ => ((hF m).continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  have key := integral_divergence_of_hasFDerivAt_off_countable' a b hle F
    (fun m x => fderiv ℝ (F m) x) (∅ : Set (Fin 3 → ℝ)) countable_empty
    (fun m => (hF m).continuous.continuousOn) (fun x _ m => hd m x) hcont.integrableOn_Icc
  have hQ : ∫ x in Q (Fin 3), ∑ m, partialDeriv m (F m) x =
      ∫ x in Icc a b, ∑ m, fderiv ℝ (F m) x (Pi.single m 1) :=
    setIntegral_congr_set Q_ae_eq_Icc
  rw [hQ, key]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hface : Icc (a ∘ m.succAbove) (b ∘ m.succAbove) = Icc (0 : Fin 2 → ℝ) (fun _ => 1 / 2) := by
    rfl
  rw [hface, ← setIntegral_congr_set (Q_ae_eq_Icc (n := 2)),
    ← setIntegral_congr_set (Q_ae_eq_Icc (n := 2))]
  rfl

/-! ### Green's formula for the row-wise curl -/

/-- The flux `F_m = Σᵢ (Φᵢ × Ψᵢ)_m` of Green's formula for the row-wise curl. -/
def curlFlux (Φ Ψ : Ix → R3 → ℝ) (m : Fin 3) (x : R3) : ℝ :=
  ∑ i, (Φ (i, m + 1) x * Ψ (i, m + 2) x - Φ (i, m + 2) x * Ψ (i, m + 1) x)

theorem contDiff_curlFlux {Φ Ψ : Ix → R3 → ℝ} (hΦ : ∀ ij, ContDiff ℝ 1 (Φ ij))
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) (m : Fin 3) : ContDiff ℝ 1 (curlFlux Φ Ψ m) := by
  unfold curlFlux
  exact ContDiff.sum fun i _ => ((hΦ _).mul (hΨ _)).sub ((hΦ _).mul (hΨ _))

/-- **The pointwise Green identity**: `div (Σᵢ Φᵢ × Ψᵢ) = Σᵢ (curl Φᵢ · Ψᵢ - Φᵢ · curl Ψᵢ)`. -/
theorem sum_pd_curlFlux {Φ Ψ : Ix → R3 → ℝ} (hΦ : ∀ ij, Differentiable ℝ (Φ ij))
    (hΨ : ∀ ij, Differentiable ℝ (Ψ ij)) (x : R3) :
    ∑ m, partialDeriv m (curlFlux Φ Ψ m) x =
      ∑ ij : Ix, (curlM Φ ij x * Ψ ij x - Φ ij x * curlM Ψ ij x) := by
  have h1 : ∀ m, partialDeriv m (curlFlux Φ Ψ m) x = ∑ i, ((partialDeriv m (Φ (i, m + 1)) x * Ψ (i, m + 2) x +
      Φ (i, m + 1) x * partialDeriv m (Ψ (i, m + 2)) x) - (partialDeriv m (Φ (i, m + 2)) x * Ψ (i, m + 1) x +
      Φ (i, m + 2) x * partialDeriv m (Ψ (i, m + 1)) x)) := fun m => by
    unfold curlFlux
    rw [partialDeriv_sum Finset.univ (f := fun i y => Φ (i, m + 1) y * Ψ (i, m + 2) y -
      Φ (i, m + 2) y * Ψ (i, m + 1) y) (fun i _ => (((hΦ _).mul (hΨ _)).sub ((hΦ _).mul (hΨ _))) x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [partialDeriv_sub (f := fun y => Φ (i, m + 1) y * Ψ (i, m + 2) y)
      (g := fun y => Φ (i, m + 2) y * Ψ (i, m + 1) y) ((hΦ _).mul (hΨ _) x) ((hΦ _).mul (hΨ _) x),
      partialDeriv_mul (hΦ _ x) (hΨ _ x), partialDeriv_mul (hΦ _ x) (hΨ _ x)]
  simp only [h1, curlM, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  ring

/-- **Green's formula for the row-wise curl on the cube** (classical form): for `C¹` fields,
`∫_Q Σ (curl Φ · Ψ - Φ · curl Ψ) = Σ_m (∫_{x_m = ½} F_m - ∫_{x_m = 0} F_m)`,
`F_m = Σᵢ (Φᵢ × Ψᵢ)_m`. -/
theorem integral_curl_green {Φ Ψ : Ix → R3 → ℝ} (hΦ : ∀ ij, ContDiff ℝ 1 (Φ ij))
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) :
    ∫ x in Q (Fin 3), ∑ ij : Ix, (curlM Φ ij x * Ψ ij x - Φ ij x * curlM Ψ ij x) =
      ∑ m, ((∫ y in Sq, curlFlux Φ Ψ m (faceMap (m, true) y)) -
        ∫ y in Sq, curlFlux Φ Ψ m (faceMap (m, false) y)) := by
  rw [← integral_sum_pd_eq_faces (contDiff_curlFlux hΦ hΨ)]
  refine setIntegral_congr_fun measurableSet_Q fun x _ => ?_
  exact (sum_pd_curlFlux (fun ij => (hΦ ij).differentiable one_ne_zero)
    (fun ij => (hΨ ij).differentiable one_ne_zero) x).symm

/-! ### `L²` classes of continuous fields and their traces -/

/-- The `L²(Ω)` class of a continuous function, `Ω ⊆ ℝⁿ` bounded and measurable. -/
def cL2 {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : L2 ℝ Ω :=
  (memLp_of_continuous hΩ hb hf).toLp f

theorem inner_cL2 {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) {f g : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    (hg : Continuous g) : ⟪cL2 hΩ hb hf, cL2 hΩ hb hg⟫_ℝ = ∫ x in Ω, f x * g x := by
  rw [cL2, cL2, inner_toLp]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_of_continuous hΩ hb hf).coeFn_toLp] with x hx
  simp [hx]

theorem inner_cL2_right {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (u : L2 ℝ Ω) {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) :
    ⟪u, cL2 hΩ hb hg⟫_ℝ = ∫ x in Ω, u x * g x := by
  rw [cL2, inner_toLp]; simp

theorem isBounded_Q {n : ℕ} : Bornology.IsBounded (Q (Fin n)) := isBounded_openCube _ _

/-- A continuous matrix field as an element of `L²(Q; ℝ^{3×3})`. -/
def cField {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, Continuous (Φ ij)) : L2F ℝ (Q (Fin 3)) Ix :=
  WithLp.toLp 2 fun ij => cL2 measurableSet_Q isBounded_Q (hΦ ij)

@[simp] theorem cField_apply {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, Continuous (Φ ij)) (ij : Ix) :
    cField hΦ ij = cL2 measurableSet_Q isBounded_Q (hΦ ij) := rfl

theorem inner_cField {Φ Ψ : Ix → R3 → ℝ} (hΦ : ∀ ij, Continuous (Φ ij))
    (hΨ : ∀ ij, Continuous (Ψ ij)) :
    ⟪cField hΦ, cField hΨ⟫_ℝ = ∑ ij, ∫ x in Q (Fin 3), Φ ij x * Ψ ij x := by
  rw [L2F.inner_def]
  exact Finset.sum_congr rfl fun ij _ => inner_cL2 measurableSet_Q isBounded_Q (hΦ ij) (hΨ ij)

/-- Boundary index: a face, a row, a tangential slot. -/
abbrev BIx := Face × Fin 3 × Fin 2

/-- The tangential direction `m.succAbove j'` of slot `j'` on face `(m, s)`. -/
def tanDir (f : Face) (j' : Fin 2) : Fin 3 := f.1.succAbove j'

/-- **The boundary space** `L²(∂Q; ℝ^{3×3}_τ)`: one `L²(Sq)` function per face, row and
tangential slot. -/
abbrev Bdry := L2F ℝ Sq BIx

/-- The tangential component `Φ_{i,j}` on the face, for the slot `(f, i, j')`. -/
def tanFun (Φ : Ix → R3 → ℝ) (b : BIx) (y : Fin 2 → ℝ) : ℝ :=
  Φ (b.2.1, tanDir b.1 b.2.2) (faceMap b.1 y)

theorem continuous_tanFun {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, Continuous (Φ ij)) (b : BIx) :
    Continuous (tanFun Φ b) :=
  (hΦ _).comp (continuous_faceMap b.1)

/-- **The tangential trace** of a continuous field: `Φ_{i, j}` on the face, `j` tangential. -/
def tanTrace {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, Continuous (Φ ij)) : Bdry :=
  WithLp.toLp 2 fun b => cL2 measurableSet_Q isBounded_Q (continuous_tanFun hΦ b)

@[simp] theorem tanTrace_apply {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, Continuous (Φ ij)) (b : BIx) :
    tanTrace hΦ b = cL2 measurableSet_Q isBounded_Q (continuous_tanFun hΦ b) := rfl

/-- The flux value `(Ψᵢ × e_m)_j` for a tangential `j`: `Ψ_{i,m+2}` at `j = m + 1`, `-Ψ_{i,m+1}`
at `j = m + 2`. -/
def fluxVal (Ψ : Ix → R3 → ℝ) (m i j : Fin 3) (x : R3) : ℝ :=
  if j = m + 1 then Ψ (i, m + 2) x else -Ψ (i, m + 1) x

theorem continuous_fluxVal {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Continuous (Ψ ij)) (m i j : Fin 3) :
    Continuous (fluxVal Ψ m i j) := by
  unfold fluxVal; split_ifs
  exacts [hΨ _, (hΨ _).neg]

/-- The flux datum `± (Ψᵢ × e_m)_j` on the face, for the slot `(f, i, j')`. -/
def fluxFun (Ψ : Ix → R3 → ℝ) (b : BIx) (y : Fin 2 → ℝ) : ℝ :=
  faceSign b.1.2 * fluxVal Ψ b.1.1 b.2.1 (tanDir b.1 b.2.2) (faceMap b.1 y)

theorem continuous_fluxFun {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Continuous (Ψ ij)) (b : BIx) :
    Continuous (fluxFun Ψ b) :=
  continuous_const.mul ((continuous_fluxVal hΨ _ _ _).comp (continuous_faceMap b.1))

/-- **The flux trace** `± (Ψᵢ × e_m)_τ` on the face `(m, ±)`: the boundary datum paired with the
tangential trace in Green's formula. -/
def fluxTrace {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Continuous (Ψ ij)) : Bdry :=
  WithLp.toLp 2 fun b => cL2 measurableSet_Q isBounded_Q (continuous_fluxFun hΨ b)

@[simp] theorem fluxTrace_apply {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Continuous (Ψ ij)) (b : BIx) :
    fluxTrace hΨ b = cL2 measurableSet_Q isBounded_Q (continuous_fluxFun hΨ b) := rfl

theorem sum_slot_fluxVal (Φ Ψ : Ix → R3 → ℝ) (m i : Fin 3) (x : R3) :
    ∑ j' : Fin 2, Φ (i, tanDir (m, true) j') x * fluxVal Ψ m i (tanDir (m, true) j') x =
      Φ (i, m + 1) x * Ψ (i, m + 2) x - Φ (i, m + 2) x * Ψ (i, m + 1) x := by
  fin_cases m <;> simp [tanDir, fluxVal, Fin.sum_univ_two, Fin.succAbove] <;> ring

theorem integrableOn_Q {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    IntegrableOn f (Q (Fin n)) :=
  hf.integrableOn_Icc.congr_set_ae Q_ae_eq_Icc

theorem continuous_curlM {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, ContDiff ℝ 1 (Φ ij)) (ij : Ix) :
    Continuous (curlM Φ ij) :=
  (ContDiff.continuous_partialDeriv (hΦ _) _).sub (ContDiff.continuous_partialDeriv (hΦ _) _)

theorem inner_tanTrace_fluxTrace {Φ Ψ : Ix → R3 → ℝ} (hΦ : ∀ ij, Continuous (Φ ij))
    (hΨ : ∀ ij, Continuous (Ψ ij)) :
    ⟪tanTrace hΦ, fluxTrace hΨ⟫_ℝ = ∑ m, ((∫ y in Sq, curlFlux Φ Ψ m (faceMap (m, true) y)) -
        ∫ y in Sq, curlFlux Φ Ψ m (faceMap (m, false) y)) := by
  rw [L2F.inner_def]
  have hterm : ∀ b : BIx, ⟪(tanTrace hΦ) b, (fluxTrace hΨ) b⟫_ℝ =
      ∫ y in Sq, Φ (b.2.1, tanDir b.1 b.2.2) (faceMap b.1 y) *
        (faceSign b.1.2 * fluxVal Ψ b.1.1 b.2.1 (tanDir b.1 b.2.2) (faceMap b.1 y)) :=
    fun b => by rw [tanTrace_apply, fluxTrace_apply, inner_cL2]; rfl
  rw [Finset.sum_congr rfl fun b _ => hterm b]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hside : ∀ s : Bool, ∑ i : Fin 3, ∑ j' : Fin 2, ∫ y in Sq,
      Φ (i, tanDir (m, s) j') (faceMap (m, s) y) *
        (faceSign s * fluxVal Ψ m i (tanDir (m, s) j') (faceMap (m, s) y)) =
      faceSign s * ∫ y in Sq, curlFlux Φ Ψ m (faceMap (m, s) y) := by
    intro s
    have hint : ∀ i j', Integrable (fun y => Φ (i, tanDir (m, s) j') (faceMap (m, s) y) *
        (faceSign s * fluxVal Ψ m i (tanDir (m, s) j') (faceMap (m, s) y))) (volume.restrict Sq) :=
      fun i j' => integrableOn_Q (((hΦ _).comp (continuous_faceMap _)).mul (continuous_const.mul
        ((continuous_fluxVal hΨ _ _ _).comp (continuous_faceMap _))))
    calc ∑ i : Fin 3, ∑ j' : Fin 2, ∫ y in Sq,
          Φ (i, tanDir (m, s) j') (faceMap (m, s) y) *
            (faceSign s * fluxVal Ψ m i (tanDir (m, s) j') (faceMap (m, s) y)) =
        ∫ y in Sq, ∑ i : Fin 3, ∑ j' : Fin 2, Φ (i, tanDir (m, s) j') (faceMap (m, s) y) *
            (faceSign s * fluxVal Ψ m i (tanDir (m, s) j') (faceMap (m, s) y)) := by
          rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j' _ => hint i j']
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum _ fun j' _ => hint i j']
      _ = ∫ y in Sq, faceSign s * curlFlux Φ Ψ m (faceMap (m, s) y) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [curlFlux, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          have := sum_slot_fluxVal Φ Ψ m i (faceMap (m, s) y)
          simp only [tanDir] at this ⊢
          rw [← this, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j' _ => by ring
      _ = faceSign s * ∫ y in Sq, curlFlux Φ Ψ m (faceMap (m, s) y) := integral_const_mul _ _
  rw [hside, hside]
  simp [faceSign]
  ring

/-- **Green's formula for the row-wise curl in `L²`**: for `C¹` fields on `ℝ³`,
`⟪curl Φ, Ψ⟫_{L²(Q)} - ⟪Φ, curl Ψ⟫_{L²(Q)} = ⟪tanTrace Φ, fluxTrace Ψ⟫_{L²(∂Q)}`. -/
theorem inner_curl_sub_inner_curl {Φ Ψ : Ix → R3 → ℝ} (hΦ : ∀ ij, ContDiff ℝ 1 (Φ ij))
    (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)) :
    ⟪cField (continuous_curlM hΦ), cField fun ij => (hΨ ij).continuous⟫_ℝ -
      ⟪cField fun ij => (hΦ ij).continuous, cField (continuous_curlM hΨ)⟫_ℝ =
      ⟪tanTrace fun ij => (hΦ ij).continuous, fluxTrace fun ij => (hΨ ij).continuous⟫_ℝ := by
  rw [inner_cField, inner_cField, inner_tanTrace_fluxTrace, ← integral_curl_green hΦ hΨ,
    ← Finset.sum_sub_distrib]
  have hint : ∀ ij ∈ (Finset.univ : Finset Ix), Integrable
      (fun x => curlM Φ ij x * Ψ ij x - Φ ij x * curlM Ψ ij x) (volume.restrict (Q (Fin 3))) :=
    fun ij _ => (integrableOn_Q ((continuous_curlM hΦ ij).mul (hΨ ij).continuous)).sub
      (integrableOn_Q ((hΦ ij).continuous.mul (continuous_curlM hΨ ij)))
  rw [integral_finsetSum Finset.univ hint]
  refine Finset.sum_congr rfl fun ij _ => ?_
  exact (integral_sub (integrableOn_Q ((continuous_curlM hΦ ij).mul (hΨ ij).continuous))
    (integrableOn_Q ((hΦ ij).continuous.mul (continuous_curlM hΨ ij)))).symm

/-! ### Fields vanishing on the boundary; density of flux traces -/

theorem faceMap_apply_self (f : Face) (y : Fin 2 → ℝ) : faceMap f y f.1 = faceVal f.2 := by
  simp [faceMap]

theorem faceVal_notMem (s : Bool) : faceVal s ∉ Ioo (0 : ℝ) (1 / 2) := by
  cases s <;> simp [faceVal]

theorem faceMap_notMem_Q (f : Face) (y : Fin 2 → ℝ) : faceMap f y ∉ Q (Fin 3) := fun h =>
  faceVal_notMem f.2 (by rw [← faceMap_apply_self f y]; exact mem_Q.1 h f.1)

theorem cL2_eq_zero {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) (h0 : f = 0) :
    cL2 hΩ hb hf = 0 := by
  subst h0; exact MemLp.toLp_zero _

/-- A field vanishing off `Q` has zero tangential trace. -/
theorem tanTrace_eq_zero {Φ : Ix → R3 → ℝ} (hΦ : ∀ ij, Continuous (Φ ij))
    (h0 : ∀ ij, ∀ x ∉ Q (Fin 3), Φ ij x = 0) : tanTrace hΦ = 0 := by
  ext1 b
  rw [tanTrace_apply, PiLp.zero_apply]
  exact cL2_eq_zero _ _ _ (funext fun y => h0 _ _ (faceMap_notMem_Q b.1 y))

/-- A field vanishing off `Q` has zero flux trace. -/
theorem fluxTrace_eq_zero {Ψ : Ix → R3 → ℝ} (hΨ : ∀ ij, Continuous (Ψ ij))
    (h0 : ∀ ij, ∀ x ∉ Q (Fin 3), Ψ ij x = 0) : fluxTrace hΨ = 0 := by
  ext1 b
  rw [fluxTrace_apply, PiLp.zero_apply]
  refine cL2_eq_zero _ _ _ (funext fun y => ?_)
  simp only [fluxFun, fluxVal, Pi.zero_apply]
  split_ifs <;> simp [h0 _ _ (faceMap_notMem_Q b.1 y)]

/-- The coordinate `x_{m'}` of `faceMap (m', s') y`, `m' ≠ m`, puts `removeNth m` off the square. -/
theorem removeNth_faceMap_notMem {m : Fin 3} {f : Face} (hf : f.1 ≠ m) (y : Fin 2 → ℝ) :
    Fin.removeNth m (faceMap f y) ∉ Sq := by
  intro h
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hf
  have h1 := mem_Q.1 h k
  simp only [Fin.removeNth, hk] at h1
  exact faceVal_notMem f.2 (by rw [← faceMap_apply_self f y]; exact h1)

/-- The cutoff in the normal direction: `1` on the face `{x_m = s}`, `0` on the opposite face. -/
def sideCut (s : Bool) (t : ℝ) : ℝ := if s then 2 * t else 1 - 2 * t

theorem contDiff_sideCut (s : Bool) : ContDiff ℝ ∞ (sideCut s) := by
  unfold sideCut; split_ifs <;> fun_prop

theorem sideCut_faceVal (s : Bool) : sideCut s (faceVal s) = 1 := by
  cases s <;> simp [sideCut, faceVal]

theorem sideCut_faceVal_not (s : Bool) : sideCut s (faceVal (!s)) = 0 := by
  cases s <;> simp [sideCut, faceVal]

/-- The extension `φ̃(x) = φ(x_τ) sideCut s (x_m)` of a function `φ` of the square to `ℝ³`. -/
def faceExt (m : Fin 3) (s : Bool) (φ : (Fin 2 → ℝ) → ℝ) (x : R3) : ℝ :=
  φ (Fin.removeNth m x) * sideCut s (x m)

theorem contDiff_faceExt (m : Fin 3) (s : Bool) {φ : (Fin 2 → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (faceExt m s φ) := by
  unfold faceExt
  have hr : ContDiff ℝ ∞ fun x : R3 => Fin.removeNth m x :=
    contDiff_pi.2 fun k =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (m.succAbove k)).contDiff
  exact (hφ.comp hr).mul ((contDiff_sideCut s).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) m).contDiff)

/-- On the faces, `φ̃` is `φ` on `(m, s)` and vanishes elsewhere (`φ` vanishing off `Sq`). -/
theorem faceExt_faceMap (m : Fin 3) (s : Bool) {φ : (Fin 2 → ℝ) → ℝ}
    (hφ : ∀ y ∉ Sq, φ y = 0) (f : Face) (y : Fin 2 → ℝ) :
    faceExt m s φ (faceMap f y) = if f = (m, s) then φ y else 0 := by
  unfold faceExt
  by_cases hm : f.1 = m
  · obtain ⟨m', s'⟩ := f
    simp only at hm; subst hm
    by_cases hs : s' = s
    · subst hs; simp [faceMap, sideCut_faceVal]
    · have : s' = !s := by cases s <;> cases s' <;> simp_all
      subst this
      have h2 : faceMap (m', !s) y m' = faceVal (!s) := faceMap_apply_self _ y
      rw [h2, sideCut_faceVal_not, mul_zero]
      cases s <;> simp
  · rw [hφ _ (removeNth_faceMap_notMem hm y), zero_mul]
    split_ifs with h
    · exact absurd (congrArg Prod.fst h) hm
    · rfl

/-- The field attached to the face of `b = ((m, s), i, j')` whose flux trace is `φ` in the
slot `b` and `0` in the other slots (`φ̃ = faceExt m s φ`): `Ψ_{i,m+2} = ± φ̃` if `j = m + 1`,
`Ψ_{i,m+1} = ∓ φ̃` if `j = m + 2`. -/
def fluxField (b : BIx) (φ : (Fin 2 → ℝ) → ℝ) : Ix → R3 → ℝ := fun ij x =>
  if tanDir b.1 b.2.2 = b.1.1 + 1 then
    (if ij = (b.2.1, b.1.1 + 2) then faceSign b.1.2 * faceExt b.1.1 b.1.2 φ x else 0)
  else (if ij = (b.2.1, b.1.1 + 1) then -(faceSign b.1.2 * faceExt b.1.1 b.1.2 φ x) else 0)

theorem contDiff_fluxField (b : BIx) {φ : (Fin 2 → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (ij : Ix) :
    ContDiff ℝ ∞ (fluxField b φ ij) := by
  have h := contDiff_faceExt b.1.1 b.1.2 hφ
  unfold fluxField
  split_ifs
  · exact contDiff_const.mul h
  · exact contDiff_const
  · exact (contDiff_const.mul h).neg
  · exact contDiff_const

theorem faceSign_mul_self (s : Bool) : faceSign s * faceSign s = 1 := by
  cases s <;> simp [faceSign]

/-- A tangential direction is `m + 1` or `m + 2`, and these are distinct. -/
theorem tanDir_eq_or (f : Face) (j' : Fin 2) :
    tanDir f j' = f.1 + 1 ∨ tanDir f j' = f.1 + 2 := by
  obtain ⟨m, s⟩ := f
  simp only [tanDir]
  revert j'; revert m; decide

theorem add_one_ne_add_two (m : Fin 3) : m + 1 ≠ m + 2 := by
  fin_cases m <;> decide

/-- **The flux trace of `fluxField b φ` is `φ` in the slot `b` and `0` elsewhere** (for `φ`
vanishing off the square). -/
theorem fluxFun_fluxField (b : BIx) {φ : (Fin 2 → ℝ) → ℝ} (hφ : ∀ y ∉ Sq, φ y = 0)
    (b' : BIx) (y : Fin 2 → ℝ) : fluxFun (fluxField b φ) b' y = if b' = b then φ y else 0 := by
  obtain ⟨⟨m, s⟩, i, j'⟩ := b
  obtain ⟨⟨m', s'⟩, i', j''⟩ := b'
  have hext := faceExt_faceMap m s hφ (m', s') y
  simp only [fluxFun, fluxVal, fluxField]
  by_cases hf : (m', s') = (m, s)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hf
    simp only at hext
    rw [hext]
    have hinj : ∀ a b : Fin 2, tanDir (m', s') a = tanDir (m', s') b → a = b :=
      fun a b h => Fin.succAbove_right_injective h
    have hne := add_one_ne_add_two m'
    rcases tanDir_eq_or (m', s') j' with hj | hj <;>
    rcases tanDir_eq_or (m', s') j'' with hj' | hj'
    · -- same direction `m + 1`
      have hjj : j'' = j' := hinj _ _ (hj'.trans hj.symm)
      subst hjj
      by_cases hi : i' = i
      · subst hi; simp [hj, faceSign_mul_self, ← mul_assoc]
      · simp [hj, hi]
    · have hjj : j'' ≠ j' := fun h => hne (by rw [← hj, ← hj', h])
      simp [hj, hj', hne.symm, hjj, Prod.ext_iff]
    · have hjj : j'' ≠ j' := fun h => hne (by rw [← hj', ← hj, h])
      simp [hj, hj', hjj, Prod.ext_iff]
    · have hjj : j'' = j' := hinj _ _ (hj'.trans hj.symm)
      subst hjj
      by_cases hi : i' = i
      · subst hi; simp [hj, hne.symm, faceSign_mul_self, ← mul_assoc]
      · simp [hj, hne.symm, hi]
  · rw [ite_eq_right hf] at hext
    have hb : ((m', s'), i', j'') ≠ ((m, s), i, j') := fun h => hf (congrArg Prod.fst h)
    simp only [hext, mul_zero, neg_zero, hb]
    split_ifs <;> first | contradiction | simp_all

/-- **Flux traces of smooth fields separate `L²(∂Q; τ)`**: a boundary datum orthogonal to the flux
traces of all `C¹` fields vanishes. -/
theorem eq_zero_of_forall_inner_fluxTrace {β : Bdry}
    (h : ∀ (Ψ : Ix → R3 → ℝ) (hΨ : ∀ ij, ContDiff ℝ 1 (Ψ ij)),
      ⟪β, fluxTrace fun ij => (hΨ ij).continuous⟫_ℝ = 0) : β = 0 := by
  ext1 b
  rw [PiLp.zero_apply]
  refine L2.eq_zero_of_forall_inner_toL2 isOpen_Q (β b) fun φ hφ => ?_
  have hφ0 : ∀ y ∉ Sq, φ y = 0 := fun y hy => hφ.eq_zero_of_notMem hy
  have hΨ : ∀ ij, ContDiff ℝ 1 (fluxField b φ ij) := fun ij =>
    (contDiff_fluxField b hφ.contDiff ij).of_le (by simp)
  have hval : ∀ b', fluxTrace (fun ij => (hΨ ij).continuous) b' =
      if b' = b then toL2 hφ else 0 := by
    intro b'
    rw [fluxTrace_apply]
    by_cases hb : b' = b
    · subst hb
      rw [ite_eq_left rfl]
      unfold cL2 toL2
      congr 1
      funext y
      rw [fluxFun_fluxField b' hφ0 b' y, ite_eq_left rfl]
    · rw [ite_eq_right hb]
      exact cL2_eq_zero _ _ _ (funext fun y => by
        rw [fluxFun_fluxField b hφ0 b' y, ite_eq_right hb]; rfl)
  have := h _ hΨ
  rw [L2F.inner_def, Finset.sum_eq_single b (fun b' _ hb => by rw [hval, ite_eq_right hb,
    inner_zero_right]) (by simp), hval, ite_eq_left rfl] at this
  exact this

end Feec.Models.Cube.Absorbing
