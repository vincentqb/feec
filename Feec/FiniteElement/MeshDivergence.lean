module

public import Feec.FiniteElement.Whitney
public import Feec.Mesh.Basic
public import Mathlib.Analysis.Convex.Measure

/-!
# The divergence theorem on simplicial meshes

On a simplicial mesh, `C¹` fields `G_T` on the `n`-simplices `T` whose normal components agree
across interior facets and vanish on boundary facets satisfy `Σ_T ∫_T div G_T = 0`.

## Main results

* `setIntegral_closedInterior_divergence_rclike`: the divergence theorem on an `n`-simplex.
* `orient_eq_neg`: two `n`-simplices sharing an interior facet induce opposite orientations on it.
* `sum_setIntegral_divergence_eq_zero`: the divergence theorem on a mesh.
-/

open Finset MeasureTheory

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre

variable {m : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- The cofactor normal `Nⱼ = (-1)ʲ det (B_q without row j)` of `m + 1` points of `ℝ^{m+1}`. -/
def faceNormal (q : Fin (m + 1) → Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  fun j => (-1) ^ (j : ℕ) * ((Matrix.of (simplexMatrix q)).submatrix j.succAbove id).det

theorem det_edgeMatrix_cons (a : Fin (m + 1) → ℝ) (q : Fin (m + 1) → Fin (m + 1) → ℝ) :
    (edgeMatrix (Fin.cons a q : Fin (m + 2) → Fin (m + 1) → ℝ)).det =
      ∑ j, faceNormal q j * (q 0 j - a j) := by
  set C' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of fun i l => Fin.cases (q 0 i - a i) (fun l' => simplexMatrix q i l') l
  have h1 : (edgeMatrix (Fin.cons a q : Fin (m + 2) → Fin (m + 1) → ℝ)).det = C'.det := by
    rw [← Matrix.det_transpose, ← Matrix.det_transpose C']
    refine Matrix.det_eq_of_forall_row_eq_smul_add_const (fun l => Fin.cases 0 (fun _ => 1) l) 0
      (by simp) fun l i => ?_
    refine Fin.cases ?_ (fun l => ?_) l
    · simp [C', simplexMatrix]
    · simp [C', simplexMatrix]
  rw [h1, Matrix.det_succ_column_zero]
  refine sum_congr rfl fun j _ => ?_
  simp only [faceNormal, C', Matrix.of_apply, Fin.cases_zero]
  have : (Matrix.of fun i l => Fin.cases (q 0 i - a i) (fun l' => simplexMatrix q i l') l :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).submatrix j.succAbove Fin.succ =
      (Matrix.of (simplexMatrix q)).submatrix j.succAbove id := by
    ext i l; simp
  rw [this]; ring

theorem faceNormal_dot_edge (q : Fin (m + 1) → Fin (m + 1) → ℝ) (l : Fin m) :
    ∑ j, faceNormal q j * simplexMatrix q j l = 0 := by
  set C' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of fun i l' => Fin.cases (simplexMatrix q i l) (fun l'' => simplexMatrix q i l'') l'
  have h0 : C'.det = 0 := Matrix.det_zero_of_column_eq (i := 0) (j := l.succ)
    (Fin.succ_ne_zero l).symm fun k => by simp [C']
  rw [Matrix.det_succ_column_zero] at h0
  rw [← h0]
  refine sum_congr rfl fun j _ => ?_
  simp only [faceNormal, C', Matrix.of_apply, Fin.cases_zero]
  have : (Matrix.of fun i l' => Fin.cases (simplexMatrix q i l) (fun l'' => simplexMatrix q i l'')
      l' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).submatrix j.succAbove Fin.succ =
      (Matrix.of (simplexMatrix q)).submatrix j.succAbove id := by
    ext i l; simp
  rw [this]; ring

theorem faceNormal_dot_sub (q : Fin (m + 1) → Fin (m + 1) → ℝ) (l : Fin (m + 1)) :
    ∑ j, faceNormal q j * (q l j - q 0 j) = 0 := by
  refine Fin.cases (by simp) (fun l => ?_) l
  exact faceNormal_dot_edge q l

/-- `ν` is normal to the finite point set `F`: `ν · (a - b) = 0` for all `a, b ∈ F`. -/
def IsFaceNormal {n : ℕ} (F : Finset (Fin n → ℝ)) (ν : Fin n → ℝ) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, ∑ j, ν j * (a j - b j) = 0

theorem isFaceNormal_faceNormal {F : Finset (Fin (m + 1) → ℝ)}
    {q : Fin (m + 1) → Fin (m + 1) → ℝ} (hq : Set.range q = F) :
    IsFaceNormal F (faceNormal q) := by
  intro a ha b hb
  obtain ⟨l, rfl⟩ : a ∈ Set.range q := hq ▸ ha
  obtain ⟨l', rfl⟩ : b ∈ Set.range q := hq ▸ hb
  have h1 := faceNormal_dot_sub q l
  have h2 := faceNormal_dot_sub q l'
  rw [show (∑ j, faceNormal q j * (q l j - q l' j)) =
    (∑ j, faceNormal q j * (q l j - q 0 j)) - ∑ j, faceNormal q j * (q l' j - q 0 j) by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring, h1, h2, sub_zero]

theorem wedgeProd_simplexMatrix_erase (q : Fin (m + 1) → Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    wedgeProd (simplexMatrix q) (univ.erase j) univ =
      ((Matrix.of (simplexMatrix q)).submatrix j.succAbove id).det := by
  rw [← map_succAboveOrderEmb_univ, wedgeProd_map, wedgeProd_univ_apply_univ]
  rfl

theorem simplexIntegral_fluxForm (q : Fin (m + 1) → Fin (m + 1) → ℝ)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) :
    simplexIntegral q (fluxForm F) =
      ∫ y in refSimplex m, ∑ j, F j (simplexMap q y) * faceNormal q j := by
  rw [simplexIntegral_def]
  refine setIntegral_congr_fun (measurableSet_refSimplex m) fun y _ => ?_
  simp only [fluxForm, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_eq_single (univ.erase j) (fun s _ hs => by simp [hs]) (by simp)]
  simp only [ite_true, wedgeProd_simplexMatrix_erase, faceNormal]
  ring

/-- The flux `∫_q ι_G vol` of a `𝕜ⁿ`-valued field `G` through the oriented face `q`. -/
def faceFlux (q : Fin (m + 1) → Fin (m + 1) → ℝ) (G : Fin (m + 1) → (Fin (m + 1) → ℝ) → 𝕜) :
    𝕜 :=
  (simplexIntegral q (fluxForm fun j x => RCLike.re (G j x)) : 𝕜) +
    (simplexIntegral q (fluxForm fun j x => RCLike.im (G j x)) : 𝕜) * RCLike.I

theorem faceFlux_comp_perm (q : Fin (m + 1) → Fin (m + 1) → ℝ) (π : Equiv.Perm (Fin (m + 1)))
    (G : Fin (m + 1) → (Fin (m + 1) → ℝ) → 𝕜) :
    faceFlux (q ∘ π) G = (((Equiv.Perm.sign π : ℤ) : ℝ) : 𝕜) * faceFlux q G := by
  simp only [faceFlux, simplexIntegral_comp_perm]
  push_cast
  ring

theorem faceFlux_congr (q : Fin (m + 1) → Fin (m + 1) → ℝ)
    {G G' : Fin (m + 1) → (Fin (m + 1) → ℝ) → 𝕜}
    (h : ∀ x ∈ convexHull ℝ (Set.range q),
      ∑ j, (faceNormal q j : 𝕜) * G j x = ∑ j, (faceNormal q j : 𝕜) * G' j x) :
    faceFlux q G = faceFlux q G' := by
  have hre : ∀ y ∈ refSimplex m, ∑ j, RCLike.re (G j (simplexMap q y)) * faceNormal q j =
      ∑ j, RCLike.re (G' j (simplexMap q y)) * faceNormal q j := fun y hy => by
    have := congrArg RCLike.re (h _ (simplexMap_mem_convexHull q hy))
    simpa [map_sum, RCLike.re_ofReal_mul, mul_comm] using this
  have him : ∀ y ∈ refSimplex m, ∑ j, RCLike.im (G j (simplexMap q y)) * faceNormal q j =
      ∑ j, RCLike.im (G' j (simplexMap q y)) * faceNormal q j := fun y hy => by
    have := congrArg RCLike.im (h _ (simplexMap_mem_convexHull q hy))
    simpa [map_sum, RCLike.im_ofReal_mul, mul_comm] using this
  simp only [faceFlux, simplexIntegral_fluxForm]
  rw [setIntegral_congr_fun (measurableSet_refSimplex m) hre,
    setIntegral_congr_fun (measurableSet_refSimplex m) him]

theorem faceFlux_zero (q : Fin (m + 1) → Fin (m + 1) → ℝ) :
    faceFlux q (0 : Fin (m + 1) → (Fin (m + 1) → ℝ) → 𝕜) = 0 := by
  simp [faceFlux, simplexIntegral_fluxForm]

theorem faceFlux_eq_zero (q : Fin (m + 1) → Fin (m + 1) → ℝ)
    {G : Fin (m + 1) → (Fin (m + 1) → ℝ) → 𝕜}
    (h : ∀ x ∈ convexHull ℝ (Set.range q), ∑ j, (faceNormal q j : 𝕜) * G j x = 0) :
    faceFlux q G = 0 := by
  rw [← faceFlux_zero q]
  exact faceFlux_congr q fun x hx => by simpa using h x hx

theorem simplexMap_eq_refMap {n : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    simplexMap T.points = T.refMap := by
  funext x i
  simp [simplexMap, affine_apply, Affine.Simplex.refMap_apply, Affine.Simplex.linearPart_apply,
    simplexMatrix, Finset.sum_apply, mul_comm]

theorem refSimplex_eq_closedInterior {n : ℕ} :
    refSimplex n = (Feec.Mesh.refSimplex n).closedInterior := by
  ext x
  rw [Feec.Mesh.mem_closedInterior_refSimplex, mem_refSimplex_iff]

theorem image_simplexMap_refSimplex {n : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    simplexMap T.points '' refSimplex n = T.closedInterior := by
  rw [simplexMap_eq_refMap, refSimplex_eq_closedInterior, ← T.closedInterior_eq_image_refMap]

theorem setIntegral_closedInterior_divergence (T : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1))
    {F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ} (hF : ∀ j, ContDiff ℝ 1 (F j)) :
    ∫ x in T.closedInterior, ∑ j, partialDeriv j (F j) x =
      (SignType.sign (edgeMatrix T.points).det : ℝ) * ∑ i : Fin (m + 2), (-1) ^ (i : ℕ) *
        simplexIntegral (T.points ∘ i.succAbove) (fluxForm F) := by
  have hdet : (edgeMatrix T.points).det ≠ 0 := (isUnit_det_edgeMatrix T).ne_zero
  have h := setIntegral_image_simplexMap_divergence T.points hdet isOpen_univ
    (Set.subset_univ _) fun j => (hF j).contDiffOn
  rw [image_simplexMap_refSimplex, ← self_mul_sign] at h
  exact mul_left_cancel₀ hdet (h.trans (mul_assoc _ _ _))

/-- **The divergence theorem on an `n`-simplex for `𝕜ⁿ`-valued fields**, any vertex order:
`∫_T div G = Σᵢ (-1)ⁱ sign(det B_T) ∫_{∂ᵢ T} ι_G vol`. -/
theorem setIntegral_closedInterior_divergence_rclike
    (T : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1))
    {G : Fin (m + 1) → (Fin (m + 1) → ℝ) → 𝕜} (hG : ∀ j, ContDiff ℝ 1 (G j)) :
    ∫ x in T.closedInterior, ∑ j, partialDeriv j (G j) x =
      ∑ i : Fin (m + 2), (((-1) ^ (i : ℕ) * SignType.sign (edgeMatrix T.points).det : ℝ) : 𝕜) *
        faceFlux (T.points ∘ i.succAbove) G := by
  have hre : ∀ j, ContDiff ℝ 1 fun x => RCLike.re (G j x) := fun j =>
    (RCLike.reCLM (K := 𝕜)).contDiff.comp (hG j)
  have him : ∀ j, ContDiff ℝ 1 fun x => RCLike.im (G j x) := fun j =>
    (RCLike.imCLM (K := 𝕜)).contDiff.comp (hG j)
  have hdre : ∀ j x, partialDeriv j (fun x => RCLike.re (G j x)) x =
      RCLike.re (partialDeriv j (G j) x) := fun j x =>
    (RCLike.reCLM (K := 𝕜)).partialDeriv_comp ((hG j).differentiable one_ne_zero x) j
  have hdim : ∀ j x, partialDeriv j (fun x => RCLike.im (G j x)) x =
      RCLike.im (partialDeriv j (G j) x) := fun j x =>
    (RCLike.imCLM (K := 𝕜)).partialDeriv_comp ((hG j).differentiable one_ne_zero x) j
  have hcont : Continuous fun x => ∑ j, partialDeriv j (G j) x :=
    continuous_finsetSum _ fun j _ => (hG j).continuous_partialDeriv j
  have hint : IntegrableOn (fun x => ∑ j, partialDeriv j (G j) x) T.closedInterior :=
    hcont.continuousOn.integrableOn_compact T.isCompact_closedInterior
  have e1 := setIntegral_closedInterior_divergence T hre
  have e2 := setIntegral_closedInterior_divergence T him
  simp only [hdre, hdim, ← map_sum] at e1 e2
  rw [integral_re hint] at e1
  rw [integral_im hint] at e2
  rw [← RCLike.re_add_im (∫ x in T.closedInterior, ∑ j, partialDeriv j (G j) x), e1, e2]
  simp only [faceFlux, mul_add, sum_add_distrib, Finset.mul_sum]
  push_cast
  congr 1
  · refine sum_congr rfl fun i _ => by ring
  · rw [Finset.sum_mul]; refine sum_congr rfl fun i _ => by ring

theorem det_edgeMatrix_comp_perm {n : ℕ} (p : Fin (n + 1) → Fin n → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (edgeMatrix (p ∘ σ)).det = ((Equiv.Perm.sign σ : ℤ) : ℝ) * (edgeMatrix p).det := by
  have hp : p ∘ σ = fun i => affine (simplexMatrix p) (p 0) ((refVertex n ∘ σ) i) := by
    funext i; exact (simplexMap_refVertex p (σ i)).symm
  have hM : edgeMatrix (p ∘ σ) = edgeMatrix p * Matrix.of (simplexMatrix (refVertex n ∘ σ)) := by
    rw [hp, edgeMatrix, simplexMatrix_comp_affine]; rfl
  rw [hM, Matrix.det_mul, ← permDet, permDet_eq_sign, mul_comm]

theorem comp_cycleRange_symm {α : Type*} (p : Fin (m + 2) → α) (i : Fin (m + 2)) :
    p ∘ i.cycleRange.symm = Fin.cons (p i) (p ∘ i.succAbove) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Fin.cycleRange_symm_zero]
  · simp [Fin.cycleRange_symm_succ]

theorem cons_comp_perm {α : Type*} (a : α) (q : Fin (m + 1) → α) (π : Equiv.Perm (Fin (m + 1))) :
    (Fin.cons a (q ∘ π) : Fin (m + 2) → α) =
      (Fin.cons a q : Fin (m + 2) → α) ∘ Equiv.Perm.decomposeFin.symm (0, π) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp

theorem exists_perm_comp_eq {α : Type*} {k : ℕ} {f g : Fin k → α} (hf : Function.Injective f)
    (hg : Function.Injective g) (h : Set.range f = Set.range g) :
    ∃ π : Equiv.Perm (Fin k), f = g ∘ π := by
  refine ⟨(Equiv.ofInjective f hf).trans ((Set.equivOfEq h).trans (Equiv.ofInjective g hg).symm),
    funext fun x => ?_⟩
  simp only [Function.comp_apply, Equiv.trans_apply]
  rw [Equiv.apply_ofInjective_symm hg]
  rfl

theorem sign_perm_mul_det_edgeMatrix_cons (p : Fin (m + 2) → Fin (m + 1) → ℝ) (i : Fin (m + 2))
    (q : Fin (m + 1) → Fin (m + 1) → ℝ) (π : Equiv.Perm (Fin (m + 1)))
    (h : p ∘ i.succAbove = q ∘ π) :
    ((Equiv.Perm.sign π : ℤ) : ℝ) * (edgeMatrix (Fin.cons (p i) q : Fin (m + 2) → _)).det =
      (-1) ^ (i : ℕ) * (edgeMatrix p).det := by
  have h1 := det_edgeMatrix_comp_perm p i.cycleRange.symm
  rw [comp_cycleRange_symm, h, cons_comp_perm, det_edgeMatrix_comp_perm] at h1
  rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign] at h1
  simpa using h1

theorem _root_.AffineMap.mul_neg_of_sOppSide {V P : Type*} [AddCommGroup V] [Module ℝ V]
    [AddTorsor V P] {s : AffineSubspace ℝ P} (f : P →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ s, f x = 0) {a b : P}
    (hab : s.SOppSide a b) (ha : f a ≠ 0) (hb : f b ≠ 0) : f a * f b < 0 := by
  obtain ⟨p, hp, t, ⟨ht0, ht1⟩, rfl⟩ := AffineSubspace.wOppSide_iff_exists_wbtw.1 hab.wOppSide
  have h0 := hf _ hp
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring'] at h0
  rcases ht0.eq_or_lt with rfl | htp
  · exact absurd (by linarith) ha
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
  · nlinarith [mul_neg_of_pos_of_neg htp hb', mul_nonneg (sub_nonneg.2 ht1) (neg_nonneg.2 ha'.le)]
  · nlinarith
  · nlinarith
  · nlinarith [mul_pos htp hb', mul_nonneg (sub_nonneg.2 ht1) ha'.le]

theorem sign_mul_of_eq_one_or {ε x : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (SignType.sign (ε * x) : ℝ) = ε * SignType.sign x := by
  rcases hε with rfl | rfl
  · simp
  · rw [neg_one_mul, Left.sign_neg]; simp

theorem intCast_units_eq_one_or (u : ℤˣ) : ((u : ℤ) : ℝ) = 1 ∨ ((u : ℤ) : ℝ) = -1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- A fixed enumeration `Fin k → Fin n → ℝ` of a finite point set (of cardinality `k`). -/
def faceEnum {n : ℕ} (F : Finset (Fin n → ℝ)) (k : ℕ) : Fin k → Fin n → ℝ := fun i =>
  if h : (i : ℕ) < F.card then (F.equivFin.symm ⟨i, h⟩ : Fin n → ℝ) else 0

theorem faceEnum_of_lt {n : ℕ} (F : Finset (Fin n → ℝ)) {k : ℕ} (i : Fin k) (h : (i : ℕ) < F.card) :
    faceEnum F k i = F.equivFin.symm ⟨i, h⟩ := by
  simp [faceEnum, h]

theorem injective_faceEnum {n : ℕ} {F : Finset (Fin n → ℝ)} {k : ℕ} (hF : F.card = k) :
    Function.Injective (faceEnum F k) := by
  intro i j hij
  rw [faceEnum_of_lt F i (hF ▸ i.2), faceEnum_of_lt F j (hF ▸ j.2)] at hij
  have := F.equivFin.symm.injective (Subtype.ext hij)
  exact Fin.ext (by simpa using congrArg Fin.val this)

theorem range_faceEnum {n : ℕ} {F : Finset (Fin n → ℝ)} {k : ℕ} (hF : F.card = k) :
    Set.range (faceEnum F k) = F := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rw [faceEnum_of_lt F i (hF ▸ i.2)]
    exact (F.equivFin.symm _).2
  · intro hx
    refine ⟨⟨F.equivFin ⟨x, hx⟩, hF ▸ (F.equivFin ⟨x, hx⟩).2⟩, ?_⟩
    simp [faceEnum, (F.equivFin ⟨x, hx⟩).2]

open Feec.Mesh in
/-- The apex of `T` opposite a facet `F`: a vertex of `T` not in `F`. -/
def apex {n : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n) (F : Finset (Fin n → ℝ)) : Fin n → ℝ := by
  classical exact if h : (vertexSet T \ F).Nonempty then h.choose else 0

open Feec.Mesh in
theorem apex_erase {n : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i : Fin (n + 1)) :
    apex T ((vertexSet T).erase (T.points i)) = T.points i := by
  classical
  have he : vertexSet T \ (vertexSet T).erase (T.points i) = {T.points i} := by
    ext x
    simp only [mem_sdiff, mem_erase, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; by_contra hx; exact h2 ⟨hx, h1⟩
    · rintro rfl; exact ⟨points_mem_vertexSet T i, fun h => h.1 rfl⟩
  have hne : (vertexSet T \ (vertexSet T).erase (T.points i)).Nonempty := he ▸ singleton_nonempty _
  unfold apex
  rw [dite_eq_left hne]
  have h := hne.choose_spec
  rw [mem_sdiff, mem_erase] at h
  by_contra hc
  exact h.2 ⟨hc, h.1⟩

open Feec.Mesh in
theorem range_comp_succAbove {n : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i : Fin (n + 1)) :
    Set.range (T.points ∘ i.succAbove) = ((vertexSet T).erase (T.points i) : Set _) := by
  ext x
  simp only [Set.mem_range, Function.comp_apply, coe_erase, Set.mem_sdiff, coe_vertexSet,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨_, rfl⟩, fun h => Fin.succAbove_ne i j (T.independent.injective h)⟩
  · rintro ⟨⟨j, rfl⟩, hj⟩
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq (fun h : j = i => hj (h ▸ rfl))
    exact ⟨j', rfl⟩

open Feec.Mesh in
theorem card_erase_vertexSet {n : ℕ} (T : Affine.Simplex ℝ (Fin n → ℝ) n) (i : Fin (n + 1)) :
    ((vertexSet T).erase (T.points i)).card = n := by
  rw [card_erase_of_mem (points_mem_vertexSet T i), card_vertexSet]; rfl

/-- The orientation that `T` induces on its facet `F`, relative to the enumeration `faceEnum F`. -/
def orient (T : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1)) (F : Finset (Fin (m + 1) → ℝ)) : ℝ :=
  SignType.sign (edgeMatrix (Fin.cons (apex T F) (faceEnum F (m + 1)) :
    Fin (m + 2) → Fin (m + 1) → ℝ)).det

theorem neg_one_pow_mul_faceFlux_eq_orient (T : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1))
    (i : Fin (m + 2)) (G : Fin (m + 1) → (Fin (m + 1) → ℝ) → 𝕜) :
    (((-1) ^ (i : ℕ) * SignType.sign (edgeMatrix T.points).det : ℝ) : 𝕜) *
        faceFlux (T.points ∘ i.succAbove) G =
      (orient T ((Feec.Mesh.vertexSet T).erase (T.points i)) : 𝕜) *
        faceFlux (faceEnum ((Feec.Mesh.vertexSet T).erase (T.points i)) (m + 1)) G := by
  set F := (Feec.Mesh.vertexSet T).erase (T.points i)
  have hF : F.card = m + 1 := card_erase_vertexSet T i
  obtain ⟨π, hπ⟩ := exists_perm_comp_eq (T.independent.injective.comp (Fin.succAbove_right_injective))
    (injective_faceEnum hF) (by rw [range_comp_succAbove, range_faceEnum hF])
  have key := sign_perm_mul_det_edgeMatrix_cons T.points i _ π hπ
  rw [hπ, faceFlux_comp_perm, orient, apex_erase]
  set D := (edgeMatrix (Fin.cons (T.points i) (faceEnum F (m + 1)) :
    Fin (m + 2) → Fin (m + 1) → ℝ)).det
  set ε : ℝ := ((Equiv.Perm.sign π : ℤ) : ℝ)
  have hε := intCast_units_eq_one_or (Equiv.Perm.sign π)
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> simp [ε, h]
  have hD : D = ε * ((-1) ^ (i : ℕ) * (edgeMatrix T.points).det) := by
    rw [← key, ← mul_assoc, hεε, one_mul]
  have hs : (SignType.sign D : ℝ) = ε * ((-1) ^ (i : ℕ) * SignType.sign (edgeMatrix T.points).det) := by
    rw [hD, sign_mul_of_eq_one_or hε, sign_mul_of_eq_one_or (neg_one_pow_eq_or ℝ _)]
  rw [hs]
  push_cast
  ring

open Feec.Mesh in
theorem exists_eq_erase_of_facet {n : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {F : Finset (Fin n → ℝ)} (hF : F ⊆ vertexSet T) (hc : F.card = n) :
    ∃ i, F = (vertexSet T).erase (T.points i) := by
  classical
  obtain ⟨i, hi, -⟩ := exists_apex hF hc
  refine ⟨i, Finset.eq_of_subset_of_card_le (fun x hx => mem_erase.2 ⟨fun h => hi (h ▸ hx), hF hx⟩)
    ?_⟩
  rw [card_erase_vertexSet, hc]

open Feec.Mesh in
theorem setIntegral_divergence_eq_sum_faces (T : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1))
    {G : Fin (m + 1) → (Fin (m + 1) → ℝ) → 𝕜} (hG : ∀ j, ContDiff ℝ 1 (G j)) :
    ∫ x in T.closedInterior, ∑ j, partialDeriv j (G j) x =
      ∑ F ∈ (vertexSet T).powersetCard (m + 1),
        (orient T F : 𝕜) * faceFlux (faceEnum F (m + 1)) G := by
  classical
  rw [setIntegral_closedInterior_divergence_rclike T hG]
  simp_rw [neg_one_pow_mul_faceFlux_eq_orient]
  refine Finset.sum_nbij (fun i => (vertexSet T).erase (T.points i)) ?_ ?_ ?_ fun _ _ => rfl
  · intro i _
    exact mem_powersetCard.2 ⟨erase_subset _ _, card_erase_vertexSet T i⟩
  · intro i _ j _ hij
    by_contra hne
    have : T.points i ∈ (vertexSet T).erase (T.points j) :=
      mem_erase.2 ⟨fun h => hne (T.independent.injective h), points_mem_vertexSet T i⟩
    have hij' : (vertexSet T).erase (T.points i) = (vertexSet T).erase (T.points j) := hij
    rw [← hij'] at this
    exact (notMem_erase _ _) this
  · intro F hF
    obtain ⟨i, rfl⟩ := exists_eq_erase_of_facet (mem_powersetCard.1 hF).1
      (mem_powersetCard.1 hF).2
    exact ⟨i, mem_coe.2 (mem_univ i), rfl⟩

open Feec.Mesh in
theorem det_cons_apex_ne_zero {T : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1)}
    {F : Finset (Fin (m + 1) → ℝ)} (hF : F ⊆ vertexSet T) (hc : F.card = m + 1) :
    (edgeMatrix (Fin.cons (apex T F) (faceEnum F (m + 1)) : Fin (m + 2) → Fin (m + 1) → ℝ)).det ≠
      0 := by
  obtain ⟨i, rfl⟩ := exists_eq_erase_of_facet hF hc
  obtain ⟨π, hπ⟩ := exists_perm_comp_eq (T.independent.injective.comp Fin.succAbove_right_injective)
    (injective_faceEnum hc) (by rw [range_comp_succAbove, range_faceEnum hc])
  have key := sign_perm_mul_det_edgeMatrix_cons T.points i _ π hπ
  rw [apex_erase]
  intro h0
  rw [h0, mul_zero] at key
  exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) (isUnit_det_edgeMatrix T).ne_zero) key.symm

open Feec.Mesh in
theorem apex_mem_sdiff {T : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1)}
    {F : Finset (Fin (m + 1) → ℝ)} (hF : F ⊆ vertexSet T) (hc : F.card = m + 1) :
    apex T F ∈ vertexSet T ∧ apex T F ∉ F := by
  obtain ⟨i, rfl⟩ := exists_eq_erase_of_facet hF hc
  rw [apex_erase]
  exact ⟨points_mem_vertexSet T i, notMem_erase _ _⟩

/-- The affine function `x ↦ N_q · (q₀ - x)`. -/
def faceAffine (q : Fin (m + 1) → Fin (m + 1) → ℝ) : (Fin (m + 1) → ℝ) →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ (Fin (m + 1) → ℝ) (∑ j, faceNormal q j * q 0 j) -
    (Fintype.linearCombination ℝ (fun j : Fin (m + 1) => faceNormal q j) :
      (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap

theorem faceAffine_apply (q : Fin (m + 1) → Fin (m + 1) → ℝ) (x : Fin (m + 1) → ℝ) :
    faceAffine q x = ∑ j, faceNormal q j * (q 0 j - x j) := by
  simp only [faceAffine, AffineMap.coe_sub, Pi.sub_apply, AffineMap.coe_const,
    Function.const_apply, LinearMap.coe_toAffineMap, Fintype.linearCombination_apply, smul_eq_mul,
    mul_sub, sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun j _ => mul_comm _ _

theorem faceAffine_eq_zero (q : Fin (m + 1) → Fin (m + 1) → ℝ) {x : Fin (m + 1) → ℝ}
    (hx : x ∈ affineSpan ℝ (Set.range q)) : faceAffine q x = 0 := by
  set S : AffineSubspace ℝ (Fin (m + 1) → ℝ) :=
    AffineSubspace.comap (faceAffine q) (AffineSubspace.mk' (0 : ℝ) ⊥)
  have hS : affineSpan ℝ (Set.range q) ≤ S := by
    rw [affineSpan_le]
    rintro _ ⟨l, rfl⟩
    simp only [S, AffineSubspace.coe_comap, Set.mem_preimage, SetLike.mem_coe,
      AffineSubspace.mem_mk', vsub_eq_sub, sub_zero, Submodule.mem_bot]
    rw [faceAffine_apply]
    have := faceNormal_dot_sub q l
    rw [← neg_eq_zero, ← this, ← sum_neg_distrib]
    exact sum_congr rfl fun j _ => by ring
  have := hS hx
  simpa [S, AffineSubspace.mem_mk'] using this

open Feec.Mesh in
/-- **Two `n`-simplices sharing an interior facet induce opposite orientations on it.** -/
theorem orient_eq_neg (M : SimplicialMesh (m + 1)) {F : Finset (Fin (m + 1) → ℝ)}
    (hF : M.IsInteriorFacet F) {T T' : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1)}
    (hT : T ∈ M.cofaces F) (hT' : T' ∈ M.cofaces F) (hne : T ≠ T') :
    orient T' F = -orient T F := by
  have hc : F.card = m + 1 := hF.1.1
  have hFT := (M.mem_cofaces.1 hT).2
  have hFT' := (M.mem_cofaces.1 hT').2
  set q := faceEnum F (m + 1)
  have hq : Set.range q = F := range_faceEnum hc
  obtain ⟨ha, haF⟩ := apex_mem_sdiff hFT hc
  obtain ⟨ha', haF'⟩ := apex_mem_sdiff hFT' hc
  have hopp := hF.2.2 T hT T' hT' hne _ ha haF _ ha' haF'
  have hD : ∀ a, (edgeMatrix (Fin.cons a q : Fin (m + 2) → Fin (m + 1) → ℝ)).det =
      faceAffine q a := fun a => by rw [det_edgeMatrix_cons, faceAffine_apply]
  have h0 := det_cons_apex_ne_zero hFT hc
  have h0' := det_cons_apex_ne_zero hFT' hc
  rw [hD] at h0 h0'
  have hneg := AffineMap.mul_neg_of_sOppSide (faceAffine q)
    (fun x hx => faceAffine_eq_zero q (by rwa [hq])) hopp h0 h0'
  show (SignType.sign (edgeMatrix (Fin.cons (apex T' F) q : Fin (m + 2) → _)).det : ℝ) =
    -(SignType.sign (edgeMatrix (Fin.cons (apex T F) q : Fin (m + 2) → _)).det : ℝ)
  rw [hD, hD]
  rcases lt_or_gt_of_ne h0 with h1 | h1
  · have h2 : 0 < faceAffine q (apex T' F) := by nlinarith
    rw [sign_neg h1, sign_pos h2]; simp
  · have h2 : faceAffine q (apex T' F) < 0 := by nlinarith
    rw [sign_neg h2, sign_pos h1]; simp

open Feec.Mesh in
/-- **The divergence theorem on a simplicial mesh**: `C¹` fields `G_T` whose normal components
agree across interior facets and vanish on boundary facets satisfy `Σ_T ∫_T div G_T = 0`. -/
theorem sum_setIntegral_divergence_eq_zero (M : SimplicialMesh (m + 1))
    (G : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1) → Fin (m + 1) → (Fin (m + 1) → ℝ) → 𝕜)
    (hG : ∀ T ∈ M.simplices, ∀ j, ContDiff ℝ 1 (G T j))
    (hint : ∀ F, M.IsInteriorFacet F → ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F, ∀ ν,
      IsFaceNormal F ν → ∀ x ∈ convexHull ℝ (F : Set (Fin (m + 1) → ℝ)),
        ∑ j, (ν j : 𝕜) * G T j x = ∑ j, (ν j : 𝕜) * G T' j x)
    (hbd : ∀ F, M.IsBoundaryFacet F → ∀ T ∈ M.cofaces F, ∀ ν,
      IsFaceNormal F ν → ∀ x ∈ convexHull ℝ (F : Set (Fin (m + 1) → ℝ)),
        ∑ j, (ν j : 𝕜) * G T j x = 0) :
    ∑ T ∈ M.simplices, ∫ x in T.closedInterior, ∑ j, partialDeriv j (G T j) x = 0 := by
  classical
  rw [sum_congr rfl fun T hT => setIntegral_divergence_eq_sum_faces T (hG T hT)]
  rw [Finset.sum_comm' (t' := M.simplices.biUnion fun T => (vertexSet T).powersetCard (m + 1))
    (s' := fun F => M.cofaces F) (fun T F => by
      simp only [mem_powersetCard, mem_biUnion, M.mem_cofaces]
      constructor
      · rintro ⟨hT, hF, hc⟩; exact ⟨⟨hT, hF⟩, T, hT, hF, hc⟩
      · rintro ⟨⟨hT, hF⟩, -, -, -, hc⟩; exact ⟨hT, hF, hc⟩)]
  refine sum_eq_zero fun F hF => ?_
  obtain ⟨T₀, hT₀, hF₀⟩ := mem_biUnion.1 hF
  have hc : F.card = m + 1 := (mem_powersetCard.1 hF₀).2
  have hfac : F ∈ M.facets := ⟨hc, T₀, hT₀, (mem_powersetCard.1 hF₀).1⟩
  set q := faceEnum F (m + 1)
  have hq : Set.range q = F := range_faceEnum hc
  have hN : IsFaceNormal F (faceNormal q) := isFaceNormal_faceNormal hq
  have hhull : convexHull ℝ (Set.range q) = convexHull ℝ (F : Set (Fin (m + 1) → ℝ)) := by
    rw [hq]
  rcases M.isInteriorFacet_or_isBoundaryFacet hfac with hI | hB
  · obtain ⟨T, T', hne, he⟩ := card_eq_two.1 hI.2.1
    have hT : T ∈ M.cofaces F := he ▸ mem_insert_self T {T'}
    have hT' : T' ∈ M.cofaces F := he ▸ mem_insert_of_mem (mem_singleton_self T')
    rw [he, sum_pair hne, orient_eq_neg M hI hT hT' hne,
      faceFlux_congr q (G := G T') (G' := G T) fun x hx =>
        (hint F hI T hT T' hT' _ hN x (hhull ▸ hx)).symm]
    push_cast
    ring
  · obtain ⟨T, he⟩ := card_eq_one.1 hB.2.1
    have hT : T ∈ M.cofaces F := he ▸ mem_singleton_self T
    rw [he, sum_singleton, faceFlux_eq_zero q fun x hx => hbd F hB T hT _ hN x (hhull ▸ hx),
      mul_zero]

end Feec.FiniteElement
