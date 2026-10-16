module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Feec.Ch4.Constraints

/-!
# Repair of thesis §4.10: the discretizations of (4.14) and of the reduced system (4.15)

**Thesis claim** ([QuennevilleBelair2015, §4.10, p. 66]). Discretizations `V_h⁰ × V_h¹ × V_h²`
of the matrix wave equation (4.14) are

* `P_{r+1}Λ⁰ ⊗ V × P_rΛ¹ ⊗ V × P_{r-1}Λ² ⊗ V`,
* `P_{r+1}Λ⁰ ⊗ V × P_rΛ¹ ⊗ V × P_r⁻Λ² ⊗ V`,
* `P_{r+1}Λ⁰ ⊗ V × P_r⁻Λ¹ ⊗ V × P_{r-1}Λ² ⊗ V`,
* `P_{r+1}Λ⁰ ⊗ V × P_r⁻Λ¹ ⊗ V × P_r⁻Λ² ⊗ V`,

and after Prop 4.18 (p. 68) discretizations `V_h¹ × V_h²` of the reduced system (4.15) are
`{P_rΛ¹ or P_r⁻Λ¹} ⊗ V × {P_{r-1}Λ² or P_r⁻Λ²} ⊗ V`. The discrete Hodge wave theory of §4.6
needs each choice to be a subcomplex: `d V_h^k ⊆ V_h^{k+1}`.

**Defect.** The last two (4.14) entries are not subcomplexes: `grad x₀^{r+1} ∉ P_r⁻Λ¹`
(`Feec.Constraints.pgrad_not_mem_PminusLambda1`; here `sec410_printed_fail`, for every `V_h²`).

**Repair** (proved here; the inclusions hold for every `r`, the thesis takes `r ≥ 1`, and at
`r = 0` the minus spaces are junk values; the negative results assume `1 ≤ r`):

* `sec410_corrected`: the corrected list
  `P_{r+1}Λ⁰ × P_rΛ¹ × {P_{r-1}Λ², P_r⁻Λ²}` and `P_rΛ⁰ × P_r⁻Λ¹ × {P_{r-1}Λ², P_r⁻Λ²}`
  (all `⊗ V`, row-wise) consists of four subcomplexes. This is the list the thesis itself
  prints for the vector wave equation in §4.9 (p. 63), whose scalar form is
  `sec49_vector_wave`.
* `sec410_alt`: the index-shifted alternative
  `P_{r+1}Λ⁰ × P_{r+1}⁻Λ¹ × {P_rΛ², P_{r+1}⁻Λ²}` (the same theorem at `r + 1`).
* Maximality: `pgrad_PLambda0_sub_PminusLambda1_iff` (`grad P_sΛ⁰ ⊆ P_r⁻Λ¹ ↔ s ≤ r`) and
  `pgrad_PLambda0_sub_PLambda1_iff` (`grad P_sΛ⁰ ⊆ P_rΛ¹ ↔ s ≤ r + 1`); so `P_rΛ⁰`, resp.
  `P_{r+1}Λ⁰`, is the largest full polynomial space of 0-forms pairing with `P_r⁻Λ¹`, resp.
  `P_rΛ¹`.
* `sec410_reduced`: the four reduced (4.15) discretizations after Prop 4.18 are correct as
  printed (no `Λ⁰` factor, so no grad step; only the curl inclusions are needed).
* `mcurl_mgrad`: `curl ∘ grad = 0`, so the subcomplexes are complexes.

**Model and scope.** Purely algebraic, at the level of polynomial shape functions on `ℝ³`, in
the vector-proxy model of `Feec.Ch4.Constraints`: 1-forms and 2-forms are
`Fin 3 → MvPolynomial (Fin 3) ℝ`, `P_r⁻Λ¹ = P_{r-1}³ ⊕ x × H_{r-1}³` (Nédélec first kind),
`P_r⁻Λ² = P_{r-1}³ ⊕ x H_{r-1}` (Raviart–Thomas), and `⊗ V` means matrix fields whose rows lie
in the given space, with `grad`/`curl` acting row-wise. Out of scope: global conformity of the
assembled finite element spaces on a mesh (`H̊¹`, `H̊(curl)`, `H(div)` conformity via degrees of
freedom) and bounded cochain projections; the thesis also only cites these from [AFW2006],
[AFW2010].
-/

@[expose] public noncomputable section

open MvPolynomial Feec.Constraints

namespace Feec.Repair.C410

/-! ## Polynomial curl, `P_rΛ¹`, `P_rΛ²`, `P_r⁻Λ²` -/

/-- Curl of a polynomial vector field (the exterior derivative `Λ¹ → Λ²` in vector proxies). -/
def pcurl (v : Fin 3 → Poly3) : Fin 3 → Poly3 :=
  ![pderiv 1 (v 2) - pderiv 2 (v 1), pderiv 2 (v 0) - pderiv 0 (v 2),
    pderiv 0 (v 1) - pderiv 1 (v 0)]

/-- `P_rΛ¹(ℝ³)`: polynomial vector fields of degree `≤ r`. -/
def PLambda1 (r : ℕ) : Set (Fin 3 → Poly3) := {v | ∀ i, (v i).totalDegree ≤ r}

/-- `P_rΛ²(ℝ³)` in vector proxies: polynomial vector fields of degree `≤ r`. -/
def PLambda2 (r : ℕ) : Set (Fin 3 → Poly3) := {v | ∀ i, (v i).totalDegree ≤ r}

/-- The position field `x`. -/
def xVec : Fin 3 → Poly3 := fun i => X i

/-- `P_r⁻Λ²(ℝ³) = P_{r-1}³ ⊕ x H_{r-1}` (Raviart–Thomas / Nédélec face elements of the first
kind; `x H_{r-1}` is the Koszul image of homogeneous 3-forms), for `r ≥ 1`. -/
def PminusLambda2 (r : ℕ) : Set (Fin 3 → Poly3) :=
  {w | ∃ p : Fin 3 → Poly3, ∃ s : Poly3, (∀ i, (p i).totalDegree ≤ r - 1) ∧
    s.IsHomogeneous (r - 1) ∧ w = p + s • xVec}

theorem pcurl_add (v w : Fin 3 → Poly3) : pcurl (v + w) = pcurl v + pcurl w := by
  ext i : 1
  fin_cases i <;> simp [pcurl] <;> ring

/-- Curl lowers the degree. -/
theorem pcurl_totalDegree_le {m : ℕ} {v : Fin 3 → Poly3} (hv : ∀ i, (v i).totalDegree ≤ m)
    (i : Fin 3) : (pcurl v i).totalDegree ≤ m - 1 := by
  have h : ∀ a b : Fin 3, (pderiv a (v b) : Poly3).totalDegree ≤ m - 1 := fun a b =>
    (totalDegree_pderiv_le a (v b)).trans (Nat.sub_le_sub_right (hv b) 1)
  fin_cases i <;> exact (totalDegree_sub _ _).trans (max_le (h _ _) (h _ _))

/-- Curl maps homogeneous fields of degree `m` to homogeneous fields of degree `m - 1`. -/
theorem pcurl_isHomogeneous {m : ℕ} {v : Fin 3 → Poly3} (hv : ∀ i, (v i).IsHomogeneous m)
    (i : Fin 3) : (pcurl v i).IsHomogeneous (m - 1) := by
  fin_cases i <;> exact (hv _).pderiv.sub (hv _).pderiv

/-- `x × q` is homogeneous of degree `n + 1` when `q` is homogeneous of degree `n`. -/
theorem xCross_isHomogeneous {n : ℕ} {q : Fin 3 → Poly3} (hq : ∀ i, (q i).IsHomogeneous n)
    (i : Fin 3) : (xCross q i).IsHomogeneous (1 + n) := by
  have h : ∀ a b : Fin 3, (X a * q b : Poly3).IsHomogeneous (1 + n) := fun a b =>
    (isHomogeneous_X ℝ a).mul (hq b)
  fin_cases i <;> exact (h _ _).sub (h _ _)

/-! ## The inclusions -/

/-- `grad P_{r+1}Λ⁰ ⊆ P_rΛ¹`. -/
theorem pgrad_mem_PLambda1 {r : ℕ} {f : Poly3} (hf : f ∈ PLambda0 (r + 1)) :
    pgrad f ∈ PLambda1 r := fun i =>
  (totalDegree_pderiv_le i f).trans (by have : f.totalDegree ≤ r + 1 := hf; omega)

/-- `P_{r-1}Λ² ⊆ P_r⁻Λ²`. -/
theorem PLambda2_sub_PminusLambda2 (r : ℕ) : PLambda2 (r - 1) ⊆ PminusLambda2 r :=
  fun w hw => ⟨w, 0, hw, isHomogeneous_zero _ _ _, by simp⟩

/-- `curl P_rΛ¹ ⊆ P_{r-1}Λ²`. -/
theorem pcurl_mem_PLambda2 {r : ℕ} {v : Fin 3 → Poly3} (hv : v ∈ PLambda1 r) :
    pcurl v ∈ PLambda2 (r - 1) :=
  pcurl_totalDegree_le hv

/-- `curl P_r⁻Λ¹ ⊆ P_{r-1}Λ²` (no hypothesis on `r`: at the junk value `r = 0` both sides are
read with `0 - 1 = 0`). The `x × H_{r-1}` part has homogeneous curl of degree `r - 1`. -/
theorem pcurl_PminusLambda1_mem_PLambda2 {r : ℕ} {v : Fin 3 → Poly3}
    (hv : v ∈ PminusLambda1 r) : pcurl v ∈ PLambda2 (r - 1) := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hv
  intro i
  rw [pcurl_add, Pi.add_apply]
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact (pcurl_totalDegree_le hp i).trans (Nat.sub_le _ _)
  · have := (pcurl_isHomogeneous (xCross_isHomogeneous hq) i).totalDegree_le
    simpa using this

/-- `curl P_rΛ¹ ⊆ P_r⁻Λ²`. -/
theorem pcurl_PLambda1_mem_PminusLambda2 {r : ℕ} {v : Fin 3 → Poly3} (hv : v ∈ PLambda1 r) :
    pcurl v ∈ PminusLambda2 r :=
  PLambda2_sub_PminusLambda2 r (pcurl_mem_PLambda2 hv)

/-- `curl P_r⁻Λ¹ ⊆ P_r⁻Λ²`. -/
theorem pcurl_PminusLambda1_mem_PminusLambda2 {r : ℕ} {v : Fin 3 → Poly3}
    (hv : v ∈ PminusLambda1 r) : pcurl v ∈ PminusLambda2 r :=
  PLambda2_sub_PminusLambda2 r (pcurl_PminusLambda1_mem_PLambda2 hv)

/-- `curl ∘ grad = 0` on polynomials. -/
theorem pcurl_pgrad (f : Poly3) : pcurl (pgrad f) = 0 := by
  ext i : 1
  fin_cases i <;> simp [pcurl, pgrad, pderiv_comm]

/-! ## Maximality of the 0-form spaces -/

/-- `grad x₀^s ∉ P_r⁻Λ¹` for every `s ≥ r + 1` (`r ≥ 1`); generalizes
`Feec.Constraints.pgrad_not_mem_PminusLambda1` (the case `s = r + 1`). -/
theorem pgrad_not_mem_PminusLambda1_of_le {r s : ℕ} (hr : 1 ≤ r) (hs : r + 1 ≤ s) :
    X 0 ^ s ∈ PLambda0 s ∧ pgrad (X 0 ^ s) ∉ PminusLambda1 r := by
  refine ⟨by simp [PLambda0, totalDegree_X_pow], ?_⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rintro ⟨p, q, hp, -, h⟩
  rw [pgrad_X0_pow] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.add_apply,
    xCross, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have key : C ((t : ℝ) + 1) * X 0 ^ (t + 1) = X 0 * p 0 + X 1 * p 1 + X 2 * p 2 := by
    linear_combination X 0 * h0 + X 1 * h1 + X 2 * h2
  have hdeg : (X 0 * p 0 + X 1 * p 1 + X 2 * p 2 : Poly3).totalDegree ≤ r := by
    have hm : ∀ i, (X i * p i : Poly3).totalDegree ≤ r := fun i =>
      (totalDegree_mul _ _).trans (by rw [totalDegree_X]; have := hp i; omega)
    exact (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
      (max_le (hm 0) (hm 1))) (hm 2))
  rw [← key, C_mul_X_pow_eq_monomial, totalDegree_monomial _ (by positivity)] at hdeg
  simp [Finsupp.sum_add_index'] at hdeg
  omega

/-- **Maximality of `P_rΛ⁰` for `P_r⁻Λ¹`** (`r ≥ 1`): `grad P_sΛ⁰ ⊆ P_r⁻Λ¹ ↔ s ≤ r`. -/
theorem pgrad_PLambda0_sub_PminusLambda1_iff {r s : ℕ} (hr : 1 ≤ r) :
    (∀ f ∈ PLambda0 s, pgrad f ∈ PminusLambda1 r) ↔ s ≤ r := by
  refine ⟨fun h => ?_, fun hs f hf => pgrad_mem_PminusLambda1 (le_trans hf hs)⟩
  by_contra hs
  obtain ⟨h1, h2⟩ := pgrad_not_mem_PminusLambda1_of_le hr (s := s) (by omega)
  exact h2 (h _ h1)

/-- **Maximality of `P_{r+1}Λ⁰` for `P_rΛ¹`**: `grad P_sΛ⁰ ⊆ P_rΛ¹ ↔ s ≤ r + 1`
(witness `x₀^s`, whose gradient has degree `s - 1`). -/
theorem pgrad_PLambda0_sub_PLambda1_iff {r s : ℕ} :
    (∀ f ∈ PLambda0 s, pgrad f ∈ PLambda1 r) ↔ s ≤ r + 1 := by
  refine ⟨fun h => ?_, fun hs f hf => pgrad_mem_PLambda1 (le_trans hf hs)⟩
  by_contra hs
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have h0 := h (X 0 ^ (t + 1)) (by simp [PLambda0, totalDegree_X_pow]) 0
  rw [pgrad_X0_pow] at h0
  simp only [Matrix.cons_val_zero] at h0
  rw [C_mul_X_pow_eq_monomial, totalDegree_monomial _ (by positivity)] at h0
  simp at h0
  omega

/-! ## Subcomplexes, scalar level and `⊗ V` (row-wise) -/

/-- `V0 × V1 × V2` is a subcomplex of the polynomial de Rham complex `grad`, `curl`. -/
structure IsSubcomplex (V0 : Set Poly3) (V1 V2 : Set (Fin 3 → Poly3)) : Prop where
  grad_mem : ∀ f ∈ V0, pgrad f ∈ V1
  curl_mem : ∀ v ∈ V1, pcurl v ∈ V2

/-- `S ⊗ V` for a space `S` of vector proxies: matrix fields with every row in `S`. -/
def tensV (S : Set (Fin 3 → Poly3)) : Set (Fin 3 → Fin 3 → Poly3) := {A | ∀ a, A a ∈ S}

/-- `S ⊗ V` for a space `S` of scalars: vector fields with every component in `S`. -/
def tensV0 (S : Set Poly3) : Set (Fin 3 → Poly3) := {u | ∀ a, u a ∈ S}

/-- Row-wise gradient (`grad` on `Λ⁰ ⊗ V`). -/
def mgrad (u : Fin 3 → Poly3) : Fin 3 → Fin 3 → Poly3 := fun a => pgrad (u a)

/-- Row-wise curl (`curl` on `Λ¹ ⊗ V`). -/
def mcurl (A : Fin 3 → Fin 3 → Poly3) : Fin 3 → Fin 3 → Poly3 := fun a => pcurl (A a)

theorem mcurl_mgrad (u : Fin 3 → Poly3) : mcurl (mgrad u) = 0 := by
  ext a : 1
  exact pcurl_pgrad (u a)

/-- `V0 ⊗ V × V1 ⊗ V × V2 ⊗ V` is a subcomplex for the row-wise `grad`, `curl`. -/
structure IsSubcomplex3 (V0 : Set (Fin 3 → Poly3)) (V1 V2 : Set (Fin 3 → Fin 3 → Poly3)) :
    Prop where
  grad_mem : ∀ u ∈ V0, mgrad u ∈ V1
  curl_mem : ∀ A ∈ V1, mcurl A ∈ V2

/-- A scalar subcomplex lifts row-wise to `⊗ V`. -/
theorem IsSubcomplex.tensV {V0 : Set Poly3} {V1 V2 : Set (Fin 3 → Poly3)}
    (h : IsSubcomplex V0 V1 V2) :
    IsSubcomplex3 (tensV0 V0) (C410.tensV V1) (C410.tensV V2) :=
  ⟨fun _ hu a => h.grad_mem _ (hu a), fun _ hA a => h.curl_mem _ (hA a)⟩

/-- **Thesis §4.9, p. 63** (vector wave equation (4.12)), scalar shape-function form: the four
listed discretizations `P_{r+1} × P_rΛ¹ × {P_{r-1}Λ², P_r⁻Λ²}` and
`P_r × P_r⁻Λ¹ × {P_{r-1}Λ², P_r⁻Λ²}` are subcomplexes. No hypothesis on `r` is needed for the
inclusions (for `r = 0` the minus spaces are junk values); the thesis has `r ≥ 1`. -/
theorem sec49_vector_wave (r : ℕ) :
    IsSubcomplex (PLambda0 (r + 1)) (PLambda1 r) (PLambda2 (r - 1)) ∧
    IsSubcomplex (PLambda0 (r + 1)) (PLambda1 r) (PminusLambda2 r) ∧
    IsSubcomplex (PLambda0 r) (PminusLambda1 r) (PLambda2 (r - 1)) ∧
    IsSubcomplex (PLambda0 r) (PminusLambda1 r) (PminusLambda2 r) :=
  ⟨⟨fun _ => pgrad_mem_PLambda1, fun _ => pcurl_mem_PLambda2⟩,
    ⟨fun _ => pgrad_mem_PLambda1, fun _ => pcurl_PLambda1_mem_PminusLambda2⟩,
    ⟨fun _ => pgrad_mem_PminusLambda1, fun _ => pcurl_PminusLambda1_mem_PLambda2⟩,
    ⟨fun _ => pgrad_mem_PminusLambda1, fun _ => pcurl_PminusLambda1_mem_PminusLambda2⟩⟩

/-- **Thesis §4.10, p. 66, corrected list of discretizations of (4.14).**

Original claim: the four spaces `P_{r+1}Λ⁰ ⊗ V × {P_rΛ¹, P_r⁻Λ¹} ⊗ V × {P_{r-1}Λ², P_r⁻Λ²} ⊗ V`
are discretizations, i.e. subcomplexes. Defect: the two with `P_r⁻Λ¹` are not
(`sec410_printed_fail`). Repair: replace `P_{r+1}Λ⁰` by `P_rΛ⁰` in the pairs with `P_r⁻Λ¹`
(the largest possible choice, `pgrad_PLambda0_sub_PminusLambda1_iff`); all four resulting
spaces are subcomplexes. Shape-function level only (see the module docstring for scope). -/
theorem sec410_corrected (r : ℕ) :
    IsSubcomplex3 (tensV0 (PLambda0 (r + 1))) (tensV (PLambda1 r)) (tensV (PLambda2 (r - 1))) ∧
    IsSubcomplex3 (tensV0 (PLambda0 (r + 1))) (tensV (PLambda1 r)) (tensV (PminusLambda2 r)) ∧
    IsSubcomplex3 (tensV0 (PLambda0 r)) (tensV (PminusLambda1 r)) (tensV (PLambda2 (r - 1))) ∧
    IsSubcomplex3 (tensV0 (PLambda0 r)) (tensV (PminusLambda1 r)) (tensV (PminusLambda2 r)) :=
  have h := sec49_vector_wave r
  ⟨h.1.tensV, h.2.1.tensV, h.2.2.1.tensV, h.2.2.2.tensV⟩

/-- **Thesis §4.10, the alternative repair**: keep `P_{r+1}Λ⁰` and raise the Nédélec index,
`P_{r+1}Λ⁰ × P_{r+1}⁻Λ¹ × {P_rΛ², P_{r+1}⁻Λ²}` (all `⊗ V`). This is `sec410_corrected` at
`r + 1`. -/
theorem sec410_alt (r : ℕ) :
    IsSubcomplex3 (tensV0 (PLambda0 (r + 1))) (tensV (PminusLambda1 (r + 1)))
      (tensV (PLambda2 r)) ∧
    IsSubcomplex3 (tensV0 (PLambda0 (r + 1))) (tensV (PminusLambda1 (r + 1)))
      (tensV (PminusLambda2 (r + 1))) :=
  ⟨(sec410_corrected (r + 1)).2.2.1, (sec410_corrected (r + 1)).2.2.2⟩

/-- **Thesis §4.10, p. 66, defect**: for `r ≥ 1` the printed pairs
`P_{r+1}Λ⁰ ⊗ V × P_r⁻Λ¹ ⊗ V × V_h²` are not subcomplexes, whatever `V_h²` is
(witness `u = (x₀^{r+1}, x₀^{r+1}, x₀^{r+1})`). -/
theorem sec410_printed_fail {r : ℕ} (hr : 1 ≤ r) (V2 : Set (Fin 3 → Fin 3 → Poly3)) :
    ¬ IsSubcomplex3 (tensV0 (PLambda0 (r + 1))) (tensV (PminusLambda1 r)) V2 := by
  intro h
  obtain ⟨h1, h2⟩ := pgrad_not_mem_PminusLambda1 hr
  exact h2 (h.grad_mem (fun _ => X 0 ^ (r + 1)) (fun _ => h1) 0)

/-- **Thesis §4.10, after Prop 4.18 (p. 68)**: the four discretizations
`{P_rΛ¹, P_r⁻Λ¹} ⊗ V × {P_{r-1}Λ², P_r⁻Λ²} ⊗ V` of the reduced system (4.15) are correct as
printed: `curl` maps each `V_h¹` into each `V_h²`. -/
theorem sec410_reduced (r : ℕ) :
    (∀ A ∈ tensV (PLambda1 r), mcurl A ∈ tensV (PLambda2 (r - 1))) ∧
    (∀ A ∈ tensV (PLambda1 r), mcurl A ∈ tensV (PminusLambda2 r)) ∧
    (∀ A ∈ tensV (PminusLambda1 r), mcurl A ∈ tensV (PLambda2 (r - 1))) ∧
    (∀ A ∈ tensV (PminusLambda1 r), mcurl A ∈ tensV (PminusLambda2 r)) :=
  have h := sec410_corrected r
  ⟨h.1.curl_mem, h.2.1.curl_mem, h.2.2.1.curl_mem, h.2.2.2.curl_mem⟩

end Feec.Repair.C410
