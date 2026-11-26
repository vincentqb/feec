module

public import Feec.Geometry.Bianchi
public import Feec.Physics.EinsteinBianchi.Fields

/-!
# The nonlinear Einstein–Bianchi system

The second Bianchi identity for the Weyl tensor `W = [[E, B], [B, -E]]` in an orthonormal frame
of a metric on `ℝ⁴` is a system of constraints and evolution equations for `E`, `B`, satisfied by
every vacuum metric; for a normal with symmetric extrinsic curvature it is the system of
[QuennevilleBelair2015], §3.4 (adapted), which follows [Friedrich1996].

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [H. Friedrich, *Hyperbolic reductions for Einstein's equations*][Friedrich1996]
* [R. M. Wald, *General Relativity*][Wald1984]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Matrix Finset Feec.MatrixSymbol Feec.DoubleForm Feec.CurvatureTensor

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi

variable (dE dB : Jet4)

theorem jet4_nrm {dX : Jet4} (hX : ∀ μ, (dX μ)ᵀ = dX μ) (μ : Fin 4) :
    dX μ 0 1 = dX μ 1 0 ∧ dX μ 0 2 = dX μ 2 0 ∧ dX μ 1 2 = dX μ 2 1 := by
  have s : ∀ i j, dX μ i j = dX μ j i := fun i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hX μ) j) i
  exact ⟨s 0 1, s 0 2, s 1 2⟩

theorem bianchi2_divB (hB : ∀ μ, (dB μ)ᵀ = dB μ) (j : Fin 3) :
    bianchi2 dE dB 1 2 3 (p (.inl j)) (q (.inl j)) = div (sp dB) j := by
  have sB := jet4_nrm hB
  fin_cases j <;>
    simp [bianchi2_eq, sgn, pidx, p, q, div, sp, Fin.sum_univ_three, sB]

theorem bianchi2_divE (hE : ∀ μ, (dE μ)ᵀ = dE μ) (j : Fin 3) :
    bianchi2 dE dB 1 2 3 (p (.inr j)) (q (.inr j)) = -div (sp dE) j := by
  have sE := jet4_nrm hE
  fin_cases j <;>
    simp [bianchi2_eq, sgn, pidx, p, q, div, sp, Fin.sum_univ_three, sE] <;> ring

theorem bianchi2_evolB (hE : ∀ μ, (dE μ)ᵀ = dE μ) (hB : ∀ μ, (dB μ)ᵀ = dB μ) (j m : Fin 3) :
    bianchi2 dE dB 0 (p (.inr m)) (q (.inr m)) (p (.inl j)) (q (.inl j)) =
      (dB 0 - curl (sp dE)) j m := by
  have sE := jet4_nrm hE
  have sB := jet4_nrm hB
  fin_cases j <;> fin_cases m <;>
    simp [bianchi2_eq, sgn, pidx, p, q, curl, sp, Fin.sum_univ_three, sE, sB,
      leviCivita3_apply] <;> ring

theorem bianchi2_evolE (hE : ∀ μ, (dE μ)ᵀ = dE μ) (hB : ∀ μ, (dB μ)ᵀ = dB μ) (j m : Fin 3) :
    bianchi2 dE dB 0 (p (.inr m)) (q (.inr m)) (p (.inr j)) (q (.inr j)) =
      -(dE 0 + curl (sp dB)) j m := by
  have sE := jet4_nrm hE
  have sB := jet4_nrm hB
  fin_cases j <;> fin_cases m <;>
    simp [bianchi2_eq, sgn, pidx, p, q, curl, sp, Fin.sum_univ_three, sE, sB,
      leviCivita3_apply] <;> ring

/-! ### The frame Bianchi identity for a Weyl field -/

/-- Frame connection coefficients `γ^λ_{κν}` (`∇_{e_κ} e_ν = γ^λ_{κν} e_λ`), `γ l κ ν`. -/
abbrev FrameConn := Fin 4 → Fin 4 → Fin 4 → ℝ

/-- The Weyl tensor `[[E, B], [B, -E]]` with electric and magnetic parts `E, B`. -/
def weylOf (E B : Matrix (Fin 3) (Fin 3) ℝ) : Tensor4 := ofBlocks E B B (-E)

/-- The connection part `γ^λ_{κμ} W_λνρσ + … ` of `∇_κ W_μνρσ`. -/
def connPart (γ : FrameConn) (W : Tensor4) (κ μ ν ρ σ : Fin 4) : ℝ :=
  ∑ l, (γ l κ μ * W l ν ρ σ + γ l κ ν * W μ l ρ σ + γ l κ ρ * W μ ν l σ + γ l κ σ * W μ ν ρ l)

/-- The lower-order part of the frame Bianchi identity: minus the cyclic sum of `connPart`. -/
def lowerOrder (γ : FrameConn) (W : Tensor4) (α β γ' δ θ : Fin 4) : ℝ :=
  -(connPart γ W α β γ' δ θ + connPart γ W β γ' α δ θ + connPart γ W γ' α β δ θ)

/-- The frame second Bianchi expression `∇_[α W_βγ']δθ` (times 3) for `W = [[E, B], [B, -E]]`. -/
def frameBianchi (γ : FrameConn) (E B : Matrix (Fin 3) (Fin 3) ℝ) (dE dB : Jet4)
    (α β γ' δ θ : Fin 4) : ℝ :=
  cov4 γ (weylOf E B) (dWeyl dE dB) α β γ' δ θ + cov4 γ (weylOf E B) (dWeyl dE dB) β γ' α δ θ
    + cov4 γ (weylOf E B) (dWeyl dE dB) γ' α β δ θ

theorem frameBianchi_eq (γ : FrameConn) (E B : Matrix (Fin 3) (Fin 3) ℝ) (dE dB : Jet4)
    (α β γ' δ θ : Fin 4) :
    frameBianchi γ E B dE dB α β γ' δ θ =
      bianchi2 dE dB α β γ' δ θ + lowerOrder γ (weylOf E B) α β γ' δ θ := by
  simp only [frameBianchi, cov4, bianchi2, lowerOrder, connPart]
  ring

/-- Lower-order terms of the evolution equation for `E`. -/
def lotE (γ : FrameConn) (W : Tensor4) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun j m => -lowerOrder γ W 0 (p (.inr m)) (q (.inr m)) (p (.inr j)) (q (.inr j))

/-- Lower-order terms of the evolution equation for `B`. -/
def lotB (γ : FrameConn) (W : Tensor4) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun j m => lowerOrder γ W 0 (p (.inr m)) (q (.inr m)) (p (.inl j)) (q (.inl j))

/-- Lower-order terms of the constraint for `E`. -/
def conE (γ : FrameConn) (W : Tensor4) : Fin 3 → ℝ :=
  fun j => -lowerOrder γ W 1 2 3 (p (.inr j)) (q (.inr j))

/-- Lower-order terms of the constraint for `B`. -/
def conB (γ : FrameConn) (W : Tensor4) : Fin 3 → ℝ :=
  fun j => lowerOrder γ W 1 2 3 (p (.inl j)) (q (.inl j))

/-- The nonlinear Einstein–Bianchi system in an orthonormal frame `(e_0 = n, e_1, e_2, e_3)`. -/
def NonlinearEB (γ : FrameConn) (E B : Matrix (Fin 3) (Fin 3) ℝ) (dE dB : Jet4) : Prop :=
  div (sp dE) + conE γ (weylOf E B) = 0 ∧ div (sp dB) + conB γ (weylOf E B) = 0 ∧
    dE 0 + curl (sp dB) + lotE γ (weylOf E B) = 0 ∧ dB 0 - curl (sp dE) + lotB γ (weylOf E B) = 0

theorem eq_zero_of_alt3 (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (h12 : ∀ a b c, G a b c = -G b a c)
    (h23 : ∀ a b c, G a b c = -G a c b) (r0 : G 1 2 3 = 0) (r1 : G 0 2 3 = 0) (r2 : G 0 3 1 = 0)
    (r3 : G 0 1 2 = 0) (a b c : Fin 4) : G a b c = 0 := by
  have := h12 a b c; have := h12 a c b; have := h12 b a c; have := h12 b c a
  have := h12 c a b; have := h12 c b a; have := h23 a b c; have := h23 a c b
  have := h23 b a c; have := h23 b c a; have := h23 c a b; have := h23 c b a
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at * <;> linarith

theorem pairSkew_dWeyl (dE dB : Jet4) (κ : Fin 4) : PairSkew (dWeyl dE dB κ) :=
  pairSkew_ofMat _

theorem frameBianchi_swap12 (γ : FrameConn) (E B : Matrix (Fin 3) (Fin 3) ℝ) (dE dB : Jet4)
    (α β γ' δ θ : Fin 4) :
    frameBianchi γ E B dE dB α β γ' δ θ = -frameBianchi γ E B dE dB β α γ' δ θ := by
  have hS := fun κ => cov4_pairSkew γ (pairSkew_ofMat (fromBlocks E B B (-E)))
    (pairSkew_dWeyl dE dB) κ
  simp only [frameBianchi, weylOf, ofBlocks] at hS ⊢
  rw [(hS α β γ' δ θ).1, (hS β γ' α δ θ).1, (hS γ' α β δ θ).1]
  ring

theorem frameBianchi_swap23 (γ : FrameConn) (E B : Matrix (Fin 3) (Fin 3) ℝ) (dE dB : Jet4)
    (α β γ' δ θ : Fin 4) :
    frameBianchi γ E B dE dB α β γ' δ θ = -frameBianchi γ E B dE dB α γ' β δ θ := by
  have hS := fun κ => cov4_pairSkew γ (pairSkew_ofMat (fromBlocks E B B (-E)))
    (pairSkew_dWeyl dE dB) κ
  simp only [frameBianchi, weylOf, ofBlocks] at hS ⊢
  rw [(hS α β γ' δ θ).1, (hS β γ' α δ θ).1, (hS γ' α β δ θ).1]
  ring

theorem frameBianchi_swap45 (γ : FrameConn) (E B : Matrix (Fin 3) (Fin 3) ℝ) (dE dB : Jet4)
    (α β γ' δ θ : Fin 4) :
    frameBianchi γ E B dE dB α β γ' δ θ = -frameBianchi γ E B dE dB α β γ' θ δ := by
  have hS := fun κ => cov4_pairSkew γ (pairSkew_ofMat (fromBlocks E B B (-E)))
    (pairSkew_dWeyl dE dB) κ
  simp only [frameBianchi, weylOf, ofBlocks] at hS ⊢
  rw [(hS α β γ' δ θ).2, (hS β γ' α δ θ).2, (hS γ' α β δ θ).2]
  ring

/-- For jets of symmetric `E`, `B`, the frame second Bianchi identity for `W = [[E, B], [B, -E]]`
holds iff the nonlinear Einstein–Bianchi system `NonlinearEB` holds. -/
theorem frameBianchi_iff (γ : FrameConn) (E B : Matrix (Fin 3) (Fin 3) ℝ) (dE dB : Jet4)
    (hE : ∀ μ, (dE μ)ᵀ = dE μ) (hB : ∀ μ, (dB μ)ᵀ = dB μ) :
    (∀ α β γ' δ θ, frameBianchi γ E B dE dB α β γ' δ θ = 0) ↔ NonlinearEB γ E B dE dB := by
  have c123 : ∀ J, frameBianchi γ E B dE dB 1 2 3 (p J) (q J) =
      bianchi2 dE dB 1 2 3 (p J) (q J) + lowerOrder γ (weylOf E B) 1 2 3 (p J) (q J) :=
    fun J => frameBianchi_eq _ _ _ _ _ _ _ _ _ _
  have c0 : ∀ m J, frameBianchi γ E B dE dB 0 (p (.inr m)) (q (.inr m)) (p J) (q J) =
      bianchi2 dE dB 0 (p (.inr m)) (q (.inr m)) (p J) (q J)
        + lowerOrder γ (weylOf E B) 0 (p (.inr m)) (q (.inr m)) (p J) (q J) :=
    fun m J => frameBianchi_eq _ _ _ _ _ _ _ _ _ _
  constructor
  · intro h
    refine ⟨funext fun j => ?_, funext fun j => ?_, Matrix.ext fun j m => ?_,
      Matrix.ext fun j m => ?_⟩
    · have := h 1 2 3 (p (.inr j)) (q (.inr j))
      rw [c123, bianchi2_divE dE dB hE] at this
      simp only [Pi.add_apply, conE, Pi.zero_apply]; linarith
    · have := h 1 2 3 (p (.inl j)) (q (.inl j))
      rw [c123, bianchi2_divB dE dB hB] at this
      simp only [Pi.add_apply, conB, Pi.zero_apply]; linarith
    · have := h 0 (p (.inr m)) (q (.inr m)) (p (.inr j)) (q (.inr j))
      rw [c0, bianchi2_evolE dE dB hE hB] at this
      simp only [Matrix.add_apply, lotE, Matrix.of_apply, Matrix.zero_apply] at this ⊢; linarith
    · have := h 0 (p (.inr m)) (q (.inr m)) (p (.inl j)) (q (.inl j))
      rw [c0, bianchi2_evolB dE dB hE hB] at this
      simp only [Matrix.add_apply, Matrix.sub_apply, lotB, Matrix.of_apply,
        Matrix.zero_apply] at this ⊢; linarith
  · rintro ⟨h1, h2, h3, h4⟩ α β γ' δ θ
    have hw := skew2_expand (fun δ θ => frameBianchi γ E B dE dB α β γ' δ θ)
      (fun δ θ => frameBianchi_swap45 γ E B dE dB α β γ' δ θ) δ θ
    rw [hw]
    suffices H : ∀ J, ∀ α β γ', frameBianchi γ E B dE dB α β γ' (p J) (q J) = 0 by
      rw [H, mul_zero]
    have hev : ∀ m J, frameBianchi γ E B dE dB 0 (p (.inr m)) (q (.inr m)) (p J) (q J) = 0 := by
      intro m J
      rcases J with j | j
      · rw [c0, bianchi2_evolB dE dB hE hB]
        have := congrFun (congrFun h4 j) m
        simp only [Matrix.add_apply, Matrix.sub_apply, lotB, Matrix.of_apply,
          Matrix.zero_apply] at this ⊢
        linarith
      · rw [c0, bianchi2_evolE dE dB hE hB]
        have := congrFun (congrFun h3 j) m
        simp only [Matrix.add_apply, lotE, Matrix.of_apply, Matrix.zero_apply] at this ⊢
        linarith
    intro J
    apply eq_zero_of_alt3 (fun α β γ' => frameBianchi γ E B dE dB α β γ' (p J) (q J))
      (fun a b c => frameBianchi_swap12 γ E B dE dB a b c _ _)
      (fun a b c => frameBianchi_swap23 γ E B dE dB a b c _ _)
    · rcases J with j | j
      · rw [c123, bianchi2_divB dE dB hB]
        have := congrFun h2 j; simp only [Pi.add_apply, conB, Pi.zero_apply] at this; linarith
      · rw [c123, bianchi2_divE dE dB hE]
        have := congrFun h1 j; simp only [Pi.add_apply, conE, Pi.zero_apply] at this; linarith
    · exact hev 0 J
    · exact hev 1 J
    · exact hev 2 J

/-! ### Linearization at Minkowski space -/

theorem weylOf_smul (ε : ℝ) (E B : Matrix (Fin 3) (Fin 3) ℝ) :
    weylOf (ε • E) (ε • B) = ε • weylOf E B := by
  funext a b c d
  simp only [weylOf, ofBlocks, ofMat_apply, Pi.smul_apply, smul_eq_mul]
  generalize pidx a b = I
  generalize pidx c d = J
  rcases I with i | i <;> rcases J with j | j <;> simp <;> ring

theorem hasDerivAt_weylOf {E B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {E' B' : Matrix (Fin 3) (Fin 3) ℝ}
    {t : ℝ} (hE : ∀ i j, HasDerivAt (fun ε => E ε i j) (E' i j) t)
    (hB : ∀ i j, HasDerivAt (fun ε => B ε i j) (B' i j) t) (a b c d : Fin 4) :
    HasDerivAt (fun ε => weylOf (E ε) (B ε) a b c d) (weylOf E' B' a b c d) t := by
  simp only [weylOf, ofBlocks, ofMat_apply]
  generalize pidx a b = I
  generalize pidx c d = J
  rcases I with i | i <;> rcases J with j | j <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.neg_apply]
  · exact (hE i j).const_mul _
  · exact (hB i j).const_mul _
  · exact (hB i j).const_mul _
  · exact (hE i j).neg.const_mul _

theorem hasDerivAt_lowerOrder {γ : ℝ → FrameConn} {W : ℝ → Tensor4} {γ' : FrameConn}
    {W' : Tensor4} (hγ : ∀ l κ ν, HasDerivAt (fun ε => γ ε l κ ν) (γ' l κ ν) 0)
    (hW : ∀ a b c d, HasDerivAt (fun ε => W ε a b c d) (W' a b c d) 0) (hγ0 : γ 0 = 0)
    (hW0 : W 0 = 0) (α β γ'' δ θ : Fin 4) :
    HasDerivAt (fun ε => lowerOrder (γ ε) (W ε) α β γ'' δ θ) 0 0 := by
  have key : ∀ l κ ν a b c d, HasDerivAt (fun ε => γ ε l κ ν * W ε a b c d) 0 0 := by
    intro l κ ν a b c d
    have := (hγ l κ ν).fun_mul (hW a b c d)
    simpa [hγ0, hW0] using this
  have hc : ∀ κ μ ν ρ σ, HasDerivAt (fun ε => connPart (γ ε) (W ε) κ μ ν ρ σ) 0 0 := by
    intro κ μ ν ρ σ
    have := HasDerivAt.fun_sum (u := univ) (A := fun l ε => γ ε l κ μ * W ε l ν ρ σ
      + γ ε l κ ν * W ε μ l ρ σ + γ ε l κ ρ * W ε μ ν l σ + γ ε l κ σ * W ε μ ν ρ l)
      (A' := fun _ => 0) (x := 0) fun l _ =>
        by simpa using (((key l κ μ l ν ρ σ).fun_add (key l κ ν μ l ρ σ)).add
          (key l κ ρ μ ν l σ)).fun_add (key l κ σ μ ν ρ l)
    simpa [connPart] using this
  simpa [lowerOrder] using
    (((hc α β γ'' δ θ).fun_add (hc β γ'' α δ θ)).fun_add (hc γ'' α β δ θ)).fun_neg

theorem hasDerivAt_div {dX : ℝ → Jet4} {dX' : Jet4} {t : ℝ}
    (h : ∀ μ i j, HasDerivAt (fun ε => dX ε μ i j) (dX' μ i j) t) (a : Fin 3) :
    HasDerivAt (fun ε => div (sp (dX ε)) a) (div (sp dX') a) t := by
  simp only [div, sp]
  exact HasDerivAt.fun_sum fun b _ => h _ _ _

theorem hasDerivAt_curl {dX : ℝ → Jet4} {dX' : Jet4} {t : ℝ}
    (h : ∀ μ i j, HasDerivAt (fun ε => dX ε μ i j) (dX' μ i j) t) (a b : Fin 3) :
    HasDerivAt (fun ε => curl (sp (dX ε)) a b) (curl (sp dX') a b) t := by
  simp only [curl, sp, Matrix.of_apply]
  exact HasDerivAt.fun_sum fun c _ => HasDerivAt.fun_sum fun d _ => (h _ _ _).const_mul _

/-- Along a family differentiable at `ε = 0` through `γ = 0`, `E = B = 0`, the derivatives at
`ε = 0` of the residuals of `NonlinearEB` are the residuals of `EBJet` of the derivative jets. -/
theorem linearization_nonlinearEB {γ : ℝ → FrameConn} {E B : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {dE dB : ℝ → Jet4} {γ' : FrameConn} {E' B' : Matrix (Fin 3) (Fin 3) ℝ} {dE' dB' : Jet4}
    (hγ : ∀ l κ ν, HasDerivAt (fun ε => γ ε l κ ν) (γ' l κ ν) 0)
    (hE : ∀ i j, HasDerivAt (fun ε => E ε i j) (E' i j) 0)
    (hB : ∀ i j, HasDerivAt (fun ε => B ε i j) (B' i j) 0)
    (hdE : ∀ μ i j, HasDerivAt (fun ε => dE ε μ i j) (dE' μ i j) 0)
    (hdB : ∀ μ i j, HasDerivAt (fun ε => dB ε μ i j) (dB' μ i j) 0)
    (hγ0 : γ 0 = 0) (hE0 : E 0 = 0) (hB0 : B 0 = 0) :
    (∀ a, HasDerivAt (fun ε => (div (sp (dE ε)) + conE (γ ε) (weylOf (E ε) (B ε))) a)
      (div (sp dE') a) 0) ∧
    (∀ a, HasDerivAt (fun ε => (div (sp (dB ε)) + conB (γ ε) (weylOf (E ε) (B ε))) a)
      (div (sp dB') a) 0) ∧
    (∀ a b, HasDerivAt (fun ε => (dE ε 0 + curl (sp (dB ε)) + lotE (γ ε) (weylOf (E ε) (B ε))) a b)
      ((dE' 0 + curl (sp dB')) a b) 0) ∧
    (∀ a b, HasDerivAt (fun ε => (dB ε 0 - curl (sp (dE ε)) + lotB (γ ε) (weylOf (E ε) (B ε))) a b)
      ((dB' 0 - curl (sp dE')) a b) 0) := by
  have hW0 : weylOf (E 0) (B 0) = 0 := by
    rw [hE0, hB0, show (0 : Matrix (Fin 3) (Fin 3) ℝ) = (0 : ℝ) • 0 by simp, weylOf_smul,
      zero_smul]
  have hL := hasDerivAt_lowerOrder (W := fun ε => weylOf (E ε) (B ε)) hγ
    (hasDerivAt_weylOf hE hB) hγ0 hW0
  refine ⟨fun a => ?_, fun a => ?_, fun a b => ?_, fun a b => ?_⟩
  · simpa [conE] using (hasDerivAt_div hdE a).fun_add (hL 1 2 3 _ _).fun_neg
  · simpa [conB] using (hasDerivAt_div hdB a).fun_add (hL 1 2 3 _ _)
  · simpa [lotE] using
      ((hdE 0 a b).fun_add (hasDerivAt_curl hdB a b)).fun_add (hL 0 _ _ _ _).fun_neg
  · simpa [lotB] using ((hdB 0 a b).fun_sub (hasDerivAt_curl hdE a b)).fun_add (hL 0 _ _ _ _)

theorem ebJet_of_nonlinearEB {γ : ℝ → FrameConn} {E B : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {dE dB : ℝ → Jet4} {γ' : FrameConn} {E' B' : Matrix (Fin 3) (Fin 3) ℝ} {dE' dB' : Jet4}
    (hγ : ∀ l κ ν, HasDerivAt (fun ε => γ ε l κ ν) (γ' l κ ν) 0)
    (hE : ∀ i j, HasDerivAt (fun ε => E ε i j) (E' i j) 0)
    (hB : ∀ i j, HasDerivAt (fun ε => B ε i j) (B' i j) 0)
    (hdE : ∀ μ i j, HasDerivAt (fun ε => dE ε μ i j) (dE' μ i j) 0)
    (hdB : ∀ μ i j, HasDerivAt (fun ε => dB ε μ i j) (dB' μ i j) 0)
    (hγ0 : γ 0 = 0) (hE0 : E 0 = 0) (hB0 : B 0 = 0)
    (hN : ∀ ε, NonlinearEB (γ ε) (E ε) (B ε) (dE ε) (dB ε)) : EBJet dE' dB' := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    linearization_nonlinearEB hγ hE hB hdE hdB hγ0 hE0 hB0
  have z : ∀ {f : ℝ → ℝ} {f' : ℝ}, HasDerivAt f f' 0 → (∀ ε, f ε = 0) → f' = 0 :=
    fun hf h0 => hf.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun ε => h0 ε))
  refine ⟨funext fun a => z (h1 a) fun ε => congrFun (hN ε).1 a,
    funext fun a => z (h2 a) fun ε => congrFun (hN ε).2.1 a,
    Matrix.ext fun a b => z (h3 a b) fun ε => congrFun (congrFun (hN ε).2.2.1 a) b,
    Matrix.ext fun a b => z (h4 a b) fun ε => congrFun (congrFun (hN ε).2.2.2 a) b⟩

/-! ### Every vacuum metric satisfies the nonlinear EB system -/

/-- The Minkowski matrix `η = diag(-1, 1, 1, 1)`. -/
def ηM : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal (Metric.minkowski4 ℝ)

/-- A differentiable orthonormal frame `e` of a metric `g`, with coframe `θ`: `eᵀ g e = η`. -/
structure IsOrthonormalFrame (g e θ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  differentiable : ∀ a μ, Differentiable ℝ fun y => e y a μ
  coframe : ∀ y, e y * θ y = 1
  orthonormal : ∀ y, (e y)ᵀ * g y * e y = ηM

theorem ηM_mul_self : ηM * ηM = 1 := by
  rw [ηM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; exact Metric.minkowski4_mul_self i

theorem frame_inv_metric {g e θ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (hF : IsOrthonormalFrame g e θ) (y : Fin 4 → ℝ) : (e y * ηM * (e y)ᵀ) * g y = 1 := by
  have h1 : (e y)ᵀ * g y = ηM * θ y := by
    calc (e y)ᵀ * g y = (e y)ᵀ * g y * (e y * θ y) := by rw [hF.coframe y, Matrix.mul_one]
      _ = ηM * θ y := by rw [← Matrix.mul_assoc, hF.orthonormal y]
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.mul_assoc (e y), ηM_mul_self,
    Matrix.mul_one, hF.coframe y]

theorem frameRiemField_isWeyl {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ} (h : IsLeviCivita g Γ)
    {e θ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} (hF : IsOrthonormalFrame g e θ)
    (hvac : ∀ y, ricField Γ y = 0) (y : Fin 4 → ℝ) : IsWeyl (frameRiemField g Γ e y) := by
  refine ⟨frame4_pairSkew _ (riemLowField_pairSkew h y),
    frame4_bianchi1 _ (riemLowField_bianchi1 h y), fun b c => ?_⟩
  have hric := ricci_riemLowField (Γ := Γ) (frame_inv_metric hF y)
  rw [hvac y] at hric
  simp only [mtr, frameRiemField]
  refine (frame4_trace13 (e y) (Metric.minkowski4 ℝ) _ b c).trans ?_
  refine sum_eq_zero fun b' _ => sum_eq_zero fun d _ => ?_
  have : ∑ a, ∑ c', (∑ μ, Metric.minkowski4 ℝ μ * e y a μ * e y c' μ) * riemLowField g Γ y a b' c' d
      = ricci (e y * ηM * (e y)ᵀ) (riemLowField g Γ y) b' d := by
    simp only [ricci, Matrix.of_apply, Matrix.mul_apply, ηM, Matrix.diagonal_apply,
      Matrix.transpose_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun c' _ => sum_congr rfl fun a _ => by
      congr 1; exact sum_congr rfl fun μ _ => by ring
  rw [this, hric]
  simp

/-- The electric part `E_ij = W(n, e_i, n, e_j)` (`n = e_0`) of the curvature in the frame. -/
def elecField (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ) (e : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (y : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := blkE (frameRiemField g Γ e y)

/-- The magnetic part `B` (block `W(n ∧ e_i, ⋆(n ∧ e_j))`) of the curvature in the frame. -/
def magField (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ) (e : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (y : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := blkB (frameRiemField g Γ e y)

/-- Frame-derivative jet `e_κ(A) = e^h_κ ∂_h A` of a matrix field. -/
def frameDeriv (e : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (A : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 4 → ℝ) : Jet4 :=
  fun κ => ∑ h, e x h κ • jet4 A x h

theorem frameRiemField_eq_weylOf {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ} (h : IsLeviCivita g Γ)
    {e θ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} (hF : IsOrthonormalFrame g e θ)
    (hvac : ∀ y, ricField Γ y = 0) (y : Fin 4 → ℝ) :
    frameRiemField g Γ e y = weylOf (elecField g Γ e y) (magField g Γ e y) ∧
      (elecField g Γ e y)ᵀ = elecField g Γ e y ∧ (elecField g Γ e y).trace = 0 ∧
      (magField g Γ e y)ᵀ = magField g Γ e y ∧ (magField g Γ e y).trace = 0 := by
  obtain ⟨E, B, hE, htrE, hB, htrB, hW⟩ :=
    (weyl_iff _).1 (frameRiemField_isWeyl h hF hvac y)
  have e1 : elecField g Γ e y = E := by rw [elecField, hW, blkE_ofBlocks]
  have e2 : magField g Γ e y = B := by rw [magField, hW, blkB_ofBlocks]
  rw [e1, e2]
  exact ⟨hW, hE, htrE, hB, htrB⟩

theorem sum_mul_dWeyl (w : Fin 4 → ℝ) (dE dB : Jet4) (a b c d : Fin 4) :
    ∑ h, w h * dWeyl dE dB h a b c d = weylOf (∑ h, w h • dE h) (∑ h, w h • dB h) a b c d := by
  simp only [dWeyl, weylOf, ofBlocks, ofMat_apply]
  generalize pidx a b = I
  generalize pidx c d = J
  rcases I with i | i <;> rcases J with j | j <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_sum,
      ← sum_neg_distrib] <;>
    exact sum_congr rfl fun _ _ => by ring

/-- Every vacuum metric satisfies the nonlinear Einstein–Bianchi system: in every orthonormal
frame, the electric and magnetic parts of its curvature satisfy `NonlinearEB` at every point. -/
theorem vacuum_nonlinearEB {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ} (h : IsLeviCivita g Γ)
    {e θ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} (hF : IsOrthonormalFrame g e θ)
    (hvac : ∀ y, ricField Γ y = 0) (x : Fin 4 → ℝ) :
    NonlinearEB (frameConnField Γ e θ x) (elecField g Γ e x) (magField g Γ e x)
      (frameDeriv e (elecField g Γ e) x) (frameDeriv e (magField g Γ e) x) := by
  have hg : ∀ a b, Differentiable ℝ fun y => g y a b := fun a b =>
    (h.contDiff_metric a b).differentiable (by norm_num)
  have hR := differentiable_riemField h.contDiff_chr
  have hR4 : ∀ a b c d, Differentiable ℝ fun y => riemLowField g Γ y a b c d := fun a b c d => by
    simp only [riemLowField, lower]; fun_prop
  have he := hF.differentiable
  have hW : ∀ a b c d, Differentiable ℝ fun y => frameRiemField g Γ e y a b c d :=
    differentiable_slot1 he (differentiable_slot2 he (differentiable_slot3 he
      (differentiable_slot4 he hR4)))
  have hEd : ∀ i j, DifferentiableAt ℝ (fun y => elecField g Γ e y i j) x := fun i j =>
    (hW _ _ _ _) x
  have hBd : ∀ i j, DifferentiableAt ℝ (fun y => magField g Γ e y i j) x := fun i j =>
    (hW _ _ _ _) x
  have hWE := fun y => frameRiemField_eq_weylOf h hF hvac y
  have hfun : frameRiemField g Γ e = fun y => weylOf (elecField g Γ e y) (magField g Γ e y) :=
    funext fun y => (hWE y).1
  have hjet : frameJet (e x) (pd4 (frameRiemField g Γ e) x) =
      dWeyl (frameDeriv e (elecField g Γ e) x) (frameDeriv e (magField g Γ e) x) := by
    funext κ a b c d
    simp only [frameJet, pd4]
    rw [hfun]
    simp only [weylOf, pd_weyl hEd hBd]
    rw [sum_mul_dWeyl]
    rfl
  have hsym : ∀ (A : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ), (∀ y, (A y)ᵀ = A y) →
      ∀ κ, (frameDeriv e A x κ)ᵀ = frameDeriv e A x κ := by
    intro A hA κ
    simp only [frameDeriv, Matrix.transpose_sum, Matrix.transpose_smul, jet4_symm hA x]
  refine (frameBianchi_iff _ _ _ _ _ (hsym _ fun y => (hWE y).2.1)
    (hsym _ fun y => (hWE y).2.2.2.1)).1 fun α β γ' δ θ' => ?_
  have := frameRiemField_cyclic h he hF.coframe x α β γ' δ θ'
  rw [hjet, (hWE x).1] at this
  exact this

/-- Metric compatibility of frame connection coefficients: `η_λ γ^λ_{κν} = -η_ν γ^ν_{κλ}`. -/
def IsMetricConn (γ : FrameConn) : Prop :=
  ∀ l κ ν, Metric.minkowski4 ℝ l * γ l κ ν = -(Metric.minkowski4 ℝ ν * γ ν κ l)

theorem isMetricConn_frameConnField {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ} (h : IsLeviCivita g Γ)
    {e θ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} (hF : IsOrthonormalFrame g e θ)
    (x : Fin 4 → ℝ) : IsMetricConn (frameConnField Γ e θ x) := by
  have hg : ∀ a b, Differentiable ℝ fun y => g y a b := fun a b =>
    (h.contDiff_metric a b).differentiable (by norm_num)
  have he := hF.differentiable
  have hrel := isFrameConn_field Γ hF.coframe x
  -- `V h ν = ∇_h e_ν` and `η_λ Γ'^λ_{hν} = g(e_λ, V h ν)`
  set Γ' := mixedConnField Γ e θ x
  let V : Fin 4 → Fin 4 → Fin 4 → ℝ := fun h ν b =>
    partialDeriv h (fun y => e y b ν) x + ∑ c, Γ x b h c * e x c ν
  have hV : ∀ h ν b, V h ν b = ∑ l, Γ' l h ν * e x b l := fun h ν b => (hrel h b ν).symm
  have hη : ∀ μ ν, ∑ a, ∑ b, e x a μ * g x a b * e x b ν = ηM μ ν := fun μ ν => by
    rw [← hF.orthonormal x]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, sum_mul]
    rw [Finset.sum_comm]
  have hlow : ∀ μ h ν, ∑ a, ∑ b, e x a μ * g x a b * V h ν b =
      Metric.minkowski4 ℝ μ * Γ' μ h ν := fun μ h ν => by
    simp only [hV, mul_sum]
    calc ∑ a, ∑ b, ∑ l, e x a μ * g x a b * (Γ' l h ν * e x b l)
        = ∑ l, ∑ a, ∑ b, Γ' l h ν * (e x a μ * g x a b * e x b l) :=
          sum3_congr_perm permCyc fun y => by simp only [permCyc, Equiv.coe_fn_mk]; ring
      _ = ∑ l, Γ' l h ν * ∑ a, ∑ b, e x a μ * g x a b * e x b l := by simp only [mul_sum]
      _ = Metric.minkowski4 ℝ μ * Γ' μ h ν := by
          simp only [hη, ηM, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq,
            Finset.mem_univ, ite_true]
          ring
  -- differentiate `eᵀ g e = η`
  have hd : ∀ k μ ν, Metric.minkowski4 ℝ ν * Γ' ν k μ + Metric.minkowski4 ℝ μ * Γ' μ k ν = 0 := by
    intro k μ ν
    have hc : (fun y => ∑ a, ∑ b, e y a μ * g y a b * e y b ν) = fun _ => ηM μ ν := by
      funext y
      rw [← hF.orthonormal y]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, sum_mul]
      rw [Finset.sum_comm]
    have h0 := congrArg (fun F => partialDeriv k F x) hc
    simp only [partialDeriv_const] at h0
    have hpd : partialDeriv k (fun y => ∑ a, ∑ b, e y a μ * g y a b * e y b ν) x =
        ∑ a, ∑ b, (partialDeriv k (fun y => e y a μ) x * g x a b * e x b ν
          + e x a μ * partialDeriv k (fun y => g y a b) x * e x b ν
          + e x a μ * g x a b * partialDeriv k (fun y => e y b ν) x) := by
      rw [partialDeriv_sum _ (fun a _ => by fun_prop)]
      refine sum_congr rfl fun a _ => ?_
      rw [partialDeriv_sum _ (fun b _ => by fun_prop)]
      refine sum_congr rfl fun b _ => ?_
      rw [partialDeriv_mul (by fun_prop) (by fun_prop),
        partialDeriv_mul (by fun_prop) (by fun_prop)]
      ring
    have hreg : ∑ a, ∑ b, e x a μ * partialDeriv k (fun y => g y a b) x * e x b ν =
        ∑ a, ∑ b, ((∑ c, Γ x a k c * e x c μ) * g x a b * e x b ν
          + e x a μ * g x a b * ∑ c, Γ x b k c * e x c ν) := by
      simp only [h.compat, mul_add, add_mul, sum_mul, mul_sum, sum_add_distrib]
      congr 1
      · exact sum3_congr_perm perm13 fun y => by simp only [perm13, Equiv.coe_fn_mk]; ring
      · exact sum3_congr_perm perm23 fun y => by simp only [perm23, Equiv.coe_fn_mk]; ring
    have hsum : ∑ a, ∑ b, (V k μ a * g x a b * e x b ν + e x a μ * g x a b * V k ν b) = 0 := by
      rw [← h0, hpd]
      simp only [sum_add_distrib] at hreg ⊢
      simp only [V, add_mul, mul_add, sum_add_distrib]
      linarith [hreg]
    rw [← hlow ν k μ, ← hlow μ k ν, ← hsum, ← sum_add_distrib]
    simp only [sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by
      rw [(h.symm x).apply a b]; ring
  intro l κ ν
  simp only [frameConnField, frameConn, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun h' _ => ?_
  have := hd h' ν l
  linear_combination e x h' κ * this

/-! ### The nonlinear system with extrinsic curvature -/

/-- The acceleration `a = ∇_n n` of the normal `n = e_0`: `a_i = γ^i_{00}`. -/
def accel (γ : FrameConn) : Fin 3 → ℝ := fun i => γ i.succ 0 0

/-- The extrinsic curvature `K_ij = g(∇_{e_i} n, e_j) = γ^0_{ij}`, with the sign of [Wald1984]. -/
def extrinsic (γ : FrameConn) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => γ 0 i.succ j.succ

/-- The spatial covariant-derivative jet `D_c A_ad` of a spatial tensor in the frame. -/
def covSp (γ : FrameConn) (A : Matrix (Fin 3) (Fin 3) ℝ) (dA : Jet4) : SpaceJet :=
  fun c => Matrix.of fun a d => dA c.succ a d
    - ∑ l, (γ l.succ c.succ a.succ * A l d + γ l.succ c.succ d.succ * A a l)

/-- The normal covariant derivative `∇_n A` of a spatial tensor in the frame. -/
def covTime (γ : FrameConn) (A : Matrix (Fin 3) (Fin 3) ℝ) (dA : Jet4) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a d => dA 0 a d - ∑ l, (γ l.succ 0 a.succ * A l d + γ l.succ 0 d.succ * A a l)

/-- The Lie derivative `L_n A = ∇_n A + K A + A Kᵀ` of a spatial `(0,2)` tensor along `n`. -/
def lieN (γ : FrameConn) (A : Matrix (Fin 3) (Fin 3) ℝ) (dA : Jet4) : Matrix (Fin 3) (Fin 3) ℝ :=
  covTime γ A dA + extrinsic γ * A + A * (extrinsic γ)ᵀ

/-- `(G ×· H)_j = ε_{klj} G_ik H_il` ([QuennevilleBelair2015], §3.4). -/
def crossDot (G H : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  fun j => ∑ i, ∑ k, ∑ l, leviCivita3 ℝ k l j * G i k * H i l

/-- `(G ×× H)_ij = ε_{ikl} G_km H_ln ε_{jmn}` ([QuennevilleBelair2015], §3.4). -/
def crossCross (G H : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => ∑ k, ∑ l, ∑ m, ∑ n,
    leviCivita3 ℝ i k l * leviCivita3 ℝ j m n * G k m * H l n

/-- `(v × A)_ij = ε_{jkl} v_k A_il`. -/
def crossVec (v : Fin 3 → ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => ∑ k, ∑ l, leviCivita3 ℝ j k l * v k * A i l

/-- The lower-order term `L¹ = -3 sym(K E) + E tr K - E ×× K + 2 sym(a × B)` for `E`. -/
def thesisL1 (γ : FrameConn) (E B : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (-3 : ℝ) • symPart (extrinsic γ * E) + (extrinsic γ).trace • E - crossCross E (extrinsic γ)
    + (2 : ℝ) • symPart (crossVec (accel γ) B)

/-- The lower-order term `L² = -3 sym(K B) + B tr K - B ×× K - 2 sym(a × E)` for `B`. -/
def thesisL2 (γ : FrameConn) (E B : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (-3 : ℝ) • symPart (extrinsic γ * B) + (extrinsic γ).trace • B - crossCross B (extrinsic γ)
    - (2 : ℝ) • symPart (crossVec (accel γ) E)

theorem conn_nf {γ : FrameConn} (hγ : IsMetricConn γ) (κ : Fin 4) :
    γ 0 κ 0 = 0 ∧ γ 1 κ 1 = 0 ∧ γ 2 κ 2 = 0 ∧ γ 3 κ 3 = 0 ∧ γ 1 κ 0 = γ 0 κ 1 ∧
      γ 2 κ 0 = γ 0 κ 2 ∧ γ 3 κ 0 = γ 0 κ 3 ∧ γ 2 κ 1 = -γ 1 κ 2 ∧ γ 3 κ 1 = -γ 1 κ 3 ∧
      γ 3 κ 2 = -γ 2 κ 3 := by
  have h00 := hγ 0 κ 0; have h11 := hγ 1 κ 1; have h22 := hγ 2 κ 2; have h33 := hγ 3 κ 3
  have h10 := hγ 1 κ 0; have h20 := hγ 2 κ 0; have h30 := hγ 3 κ 0; have h21 := hγ 2 κ 1
  have h31 := hγ 3 κ 1; have h32 := hγ 3 κ 2
  simp [Metric.minkowski4] at h00 h11 h22 h33 h10 h20 h30 h21 h31 h32
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem mat_nf {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = A) (htA : A.trace = 0) :
    A 1 0 = A 0 1 ∧ A 2 0 = A 0 2 ∧ A 2 1 = A 1 2 ∧ A 2 2 = -A 0 0 - A 1 1 := by
  refine ⟨congrFun (congrFun hA 0) 1, congrFun (congrFun hA 0) 2, congrFun (congrFun hA 1) 2, ?_⟩
  rw [Matrix.trace_fin_three] at htA; linarith

theorem extrinsic_nf {γ : FrameConn} (hK : (extrinsic γ)ᵀ = extrinsic γ) :
    γ 0 2 1 = γ 0 1 2 ∧ γ 0 3 1 = γ 0 1 3 ∧ γ 0 3 2 = γ 0 2 3 :=
  ⟨congrFun (congrFun hK 0) 1, congrFun (congrFun hK 0) 2, congrFun (congrFun hK 1) 2⟩

theorem conE_eq {γ : FrameConn} (hγ : IsMetricConn γ) (hK : (extrinsic γ)ᵀ = extrinsic γ)
    {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E) (htE : E.trace = 0) (hB : Bᵀ = B)
    (htB : B.trace = 0) (dE : Jet4) (j : Fin 3) :
    (div (sp dE) + conE γ (weylOf E B)) j = (div (covSp γ E dE) - crossDot B (extrinsic γ)) j := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 0
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 1
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 2
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 3
  obtain ⟨_, _, _⟩ := extrinsic_nf hK
  obtain ⟨_, _, _, _⟩ := mat_nf hE htE
  obtain ⟨_, _, _, _⟩ := mat_nf hB htB
  clear hγ hK hE htE hB htB
  fin_cases j <;>
    simp [conE, lowerOrder, connPart, weylOf, ofBlocks, ofMat_apply, sgn, pidx, p, q,
      Fin.sum_univ_four, Fin.sum_univ_three, div, sp, covSp, crossDot, extrinsic,
      leviCivita3_apply, *] <;> ring

theorem conB_eq {γ : FrameConn} (hγ : IsMetricConn γ) (hK : (extrinsic γ)ᵀ = extrinsic γ)
    {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E) (htE : E.trace = 0) (hB : Bᵀ = B)
    (htB : B.trace = 0) (dB : Jet4) (j : Fin 3) :
    (div (sp dB) + conB γ (weylOf E B)) j = (div (covSp γ B dB) + crossDot E (extrinsic γ)) j := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 0
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 1
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 2
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 3
  obtain ⟨_, _, _⟩ := extrinsic_nf hK
  obtain ⟨_, _, _, _⟩ := mat_nf hE htE
  obtain ⟨_, _, _, _⟩ := mat_nf hB htB
  clear hγ hK hE htE hB htB
  fin_cases j <;>
    simp [conB, lowerOrder, connPart, weylOf, ofBlocks, ofMat_apply, sgn, pidx, p, q,
      Fin.sum_univ_four, Fin.sum_univ_three, div, sp, covSp, crossDot, extrinsic,
      leviCivita3_apply, *] <;> ring

set_option maxHeartbeats 4000000 in
theorem evolE_eq {γ : FrameConn} (hγ : IsMetricConn γ) (hK : (extrinsic γ)ᵀ = extrinsic γ)
    {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E) (htE : E.trace = 0) (hB : Bᵀ = B)
    (htB : B.trace = 0) (dE dB : Jet4) (hdB : IsSymTF dB) (i j : Fin 3) :
    (dE 0 + curl (sp dB) + lotE γ (weylOf E B)) i j =
      (lieN γ E dE + symPart (curl (covSp γ B dB)) + thesisL1 γ E B) i j
        - (1 / 2) * ∑ k, leviCivita3 ℝ i j k
          * (div (covSp γ B dB) + crossDot E (extrinsic γ)) k := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 0
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 1
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 2
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 3
  obtain ⟨_, _, _⟩ := extrinsic_nf hK
  obtain ⟨_, _, _, _⟩ := mat_nf hE htE
  obtain ⟨_, _, _, _⟩ := mat_nf hB htB
  obtain ⟨_, _, _, _⟩ := mat_nf (hdB 1).1 (hdB 1).2
  obtain ⟨_, _, _, _⟩ := mat_nf (hdB 2).1 (hdB 2).2
  obtain ⟨_, _, _, _⟩ := mat_nf (hdB 3).1 (hdB 3).2
  clear hγ hK hE htE hB htB hdB
  fin_cases i <;> fin_cases j <;>
    simp [lotE, lowerOrder, connPart, weylOf, ofBlocks, ofMat_apply, sgn, pidx, p, q,
      Fin.sum_univ_four, Fin.sum_univ_three, div, sp, covSp, curl, crossDot, extrinsic,
      lieN, covTime, symPart, thesisL1, crossCross, crossVec, accel, Matrix.mul_apply,
      Matrix.trace_fin_three, leviCivita3_apply, *] <;> ring

set_option maxHeartbeats 4000000 in
theorem evolB_eq {γ : FrameConn} (hγ : IsMetricConn γ) (hK : (extrinsic γ)ᵀ = extrinsic γ)
    {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E) (htE : E.trace = 0) (hB : Bᵀ = B)
    (htB : B.trace = 0) (dE dB : Jet4) (hdE : IsSymTF dE) (i j : Fin 3) :
    (dB 0 - curl (sp dE) + lotB γ (weylOf E B)) i j =
      (lieN γ B dB - symPart (curl (covSp γ E dE)) + thesisL2 γ E B) i j
        + (1 / 2) * ∑ k, leviCivita3 ℝ i j k
          * (div (covSp γ E dE) - crossDot B (extrinsic γ)) k := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 0
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 1
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 2
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := conn_nf hγ 3
  obtain ⟨_, _, _⟩ := extrinsic_nf hK
  obtain ⟨_, _, _, _⟩ := mat_nf hE htE
  obtain ⟨_, _, _, _⟩ := mat_nf hB htB
  obtain ⟨_, _, _, _⟩ := mat_nf (hdE 1).1 (hdE 1).2
  obtain ⟨_, _, _, _⟩ := mat_nf (hdE 2).1 (hdE 2).2
  obtain ⟨_, _, _, _⟩ := mat_nf (hdE 3).1 (hdE 3).2
  clear hγ hK hE htE hB htB hdE
  fin_cases i <;> fin_cases j <;>
    simp [lotB, lowerOrder, connPart, weylOf, ofBlocks, ofMat_apply, sgn, pidx, p, q,
      Fin.sum_univ_four, Fin.sum_univ_three, div, sp, covSp, curl, crossDot, extrinsic,
      lieN, covTime, symPart, thesisL2, crossCross, crossVec, accel, Matrix.mul_apply,
      Matrix.trace_fin_three, leviCivita3_apply, *] <;> ring

/-- The nonlinear system with spatial covariant derivatives, `L_n`, the extrinsic curvature, `a`. -/
def ExtrinsicEB (γ : FrameConn) (E B : Matrix (Fin 3) (Fin 3) ℝ) (dE dB : Jet4) : Prop :=
  div (covSp γ E dE) - crossDot B (extrinsic γ) = 0 ∧
    div (covSp γ B dB) + crossDot E (extrinsic γ) = 0 ∧
    lieN γ E dE + symPart (curl (covSp γ B dB)) + thesisL1 γ E B = 0 ∧
    lieN γ B dB - symPart (curl (covSp γ E dE)) + thesisL2 γ E B = 0

/-- For metric-compatible frame connection coefficients with symmetric extrinsic curvature, and
symmetric trace-free `E`, `B` and jets, `NonlinearEB ↔ ExtrinsicEB`. -/
theorem nonlinearEB_iff_extrinsicEB {γ : FrameConn} (hγ : IsMetricConn γ)
    (hK : (extrinsic γ)ᵀ = extrinsic γ) {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E)
    (htE : E.trace = 0) (hB : Bᵀ = B) (htB : B.trace = 0) {dE dB : Jet4} (hdE : IsSymTF dE)
    (hdB : IsSymTF dB) : NonlinearEB γ E B dE dB ↔ ExtrinsicEB γ E B dE dB := by
  have r1 := conE_eq hγ hK hE htE hB htB dE
  have r2 := conB_eq hγ hK hE htE hB htB dB
  have r3 := evolE_eq hγ hK hE htE hB htB dE dB hdB
  have r4 := evolB_eq hγ hK hE htE hB htB dE dB hdE
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have c1 : div (covSp γ E dE) - crossDot B (extrinsic γ) = 0 :=
      funext fun j => by rw [← r1, h1]
    have c2 : div (covSp γ B dB) + crossDot E (extrinsic γ) = 0 :=
      funext fun j => by rw [← r2, h2]
    refine ⟨c1, c2, Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
    · have := r3 i j
      rw [h3, c2] at this
      simpa using this.symm
    · have := r4 i j
      rw [h4, c1] at this
      simpa using this.symm
  · rintro ⟨c1, c2, h3, h4⟩
    refine ⟨funext fun j => by rw [r1, c1], funext fun j => by rw [r2, c2],
      Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
    · rw [r3, h3, c2]; simp
    · rw [r4, h4, c1]; simp

theorem frameDeriv_isSymTF {e : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {A : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} (hs : ∀ y, (A y)ᵀ = A y)
    (ht : ∀ y, (A y).trace = 0) {x : Fin 4 → ℝ}
    (hd : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) :
    IsSymTF (frameDeriv e A x) := by
  intro κ
  refine ⟨by simp only [frameDeriv, Matrix.transpose_sum, Matrix.transpose_smul, jet4_symm hs x],
    ?_⟩
  have h0 : ∀ h, (jet4 A x h).trace = 0 := by
    intro h
    have h1 : (jet4 A x h).trace = partialDeriv h (fun y => ∑ i, A y i i) x := by
      rw [partialDeriv_fintype_sum (fun i => hd i i)]; rfl
    have h2 : (fun y => ∑ i, A y i i) = fun _ => 0 := funext ht
    rw [h1, h2]; simp
  simp only [frameDeriv, Matrix.trace_sum, Matrix.trace_smul, h0, smul_zero, sum_const_zero]

/-- Every vacuum metric satisfies `ExtrinsicEB` in an orthonormal frame whose normal `e_0` has
symmetric extrinsic curvature. [QuennevilleBelair2015], §3.4 (adapted) -/
theorem vacuum_extrinsicEB {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ} (h : IsLeviCivita g Γ)
    {e θ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} (hF : IsOrthonormalFrame g e θ)
    (hvac : ∀ y, ricField Γ y = 0) (x : Fin 4 → ℝ)
    (hK : (extrinsic (frameConnField Γ e θ x))ᵀ = extrinsic (frameConnField Γ e θ x)) :
    ExtrinsicEB (frameConnField Γ e θ x) (elecField g Γ e x) (magField g Γ e x)
      (frameDeriv e (elecField g Γ e) x) (frameDeriv e (magField g Γ e) x) := by
  have hR := differentiable_riemField h.contDiff_chr
  have hg : ∀ a b, Differentiable ℝ fun y => g y a b := fun a b =>
    (h.contDiff_metric a b).differentiable (by norm_num)
  have hR4 : ∀ a b c d, Differentiable ℝ fun y => riemLowField g Γ y a b c d := fun a b c d => by
    simp only [riemLowField, lower]; fun_prop
  have he := hF.differentiable
  have hW : ∀ a b c d, Differentiable ℝ fun y => frameRiemField g Γ e y a b c d :=
    differentiable_slot1 he (differentiable_slot2 he (differentiable_slot3 he
      (differentiable_slot4 he hR4)))
  have hWE := fun y => frameRiemField_eq_weylOf h hF hvac y
  obtain ⟨-, hE, htE, hB, htB⟩ := hWE x
  exact (nonlinearEB_iff_extrinsicEB (isMetricConn_frameConnField h hF x) hK hE htE hB htB
    (frameDeriv_isSymTF (fun y => (hWE y).2.1) (fun y => (hWE y).2.2.1)
      fun i j => (hW _ _ _ _) x)
    (frameDeriv_isSymTF (fun y => (hWE y).2.2.2.1) (fun y => (hWE y).2.2.2.2)
      fun i j => (hW _ _ _ _) x)).1 (vacuum_nonlinearEB h hF hvac x)

/-! ### Symmetry of `K` and hypersurface-orthogonality -/

/-- For a torsion-free connection, `K_ij = γ^0_{ij}` is symmetric iff the brackets `[e_i, e_j]` of
the spatial triad have no `e_0` component. [Wald1984], §B.3 -/
theorem extrinsic_symm_iff_bracket {Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hΓ : ∀ x a b c, Γ x a b c = Γ x a c b) (e θ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (x : Fin 4 → ℝ) :
    (extrinsic (frameConnField Γ e θ x))ᵀ = extrinsic (frameConnField Γ e θ x) ↔
      ∀ i j : Fin 3, frameBracket e θ x 0 i.succ j.succ = 0 := by
  constructor
  · intro hK i j
    have := congrFun (congrFun hK j) i
    simp only [extrinsic, Matrix.transpose_apply, Matrix.of_apply] at this
    rw [← frameConnField_sub_swap hΓ, this, sub_self]
  · intro hc
    ext i j
    simp only [extrinsic, Matrix.transpose_apply, Matrix.of_apply]
    have := frameConnField_sub_swap hΓ e θ x 0 j.succ i.succ
    rw [hc] at this
    linarith

/-! ### A model: Minkowski space in a Cartesian frame -/

theorem isLeviCivita_minkowski :
    IsLeviCivita (fun _ => ηM) (fun _ _ _ _ => (0 : ℝ)) where
  symm _ := by
    rw [Matrix.IsSymm, ηM, Matrix.diagonal_transpose]
  contDiff_metric _ _ := contDiff_const
  contDiff_chr _ _ _ := contDiff_const
  torsionFree _ _ _ _ := rfl
  compat _ _ _ _ := by simp

theorem isOrthonormalFrame_minkowski :
    IsOrthonormalFrame (fun _ => ηM) (fun _ => 1) (fun _ => 1) where
  differentiable _ _ := differentiable_const _
  coframe _ := Matrix.mul_one 1
  orthonormal _ := by simp

theorem ricField_minkowski (y : Fin 4 → ℝ) : ricField (fun _ _ _ _ => (0 : ℝ)) y = 0 := by
  funext b d
  simp [ricField, riemField, riemComp]

theorem frameConnField_minkowski (x : Fin 4 → ℝ) :
    frameConnField (fun _ _ _ _ => (0 : ℝ)) (fun _ => (1 : Matrix (Fin 4) (Fin 4) ℝ))
      (fun _ => 1) x = 0 := by
  funext l κ ν
  simp [frameConnField, frameConn, mixedConnField]

theorem minkowski_extrinsicEB (x : Fin 4 → ℝ) :
    ExtrinsicEB (frameConnField (fun _ _ _ _ => 0) (fun _ => 1) (fun _ => 1) x)
      (elecField (fun _ => ηM) (fun _ _ _ _ => 0) (fun _ => 1) x)
      (magField (fun _ => ηM) (fun _ _ _ _ => 0) (fun _ => 1) x)
      (frameDeriv (fun _ => 1) (elecField (fun _ => ηM) (fun _ _ _ _ => 0) (fun _ => 1)) x)
      (frameDeriv (fun _ => 1) (magField (fun _ => ηM) (fun _ _ _ _ => 0) (fun _ => 1)) x) :=
  vacuum_extrinsicEB isLeviCivita_minkowski isOrthonormalFrame_minkowski ricField_minkowski x
    (by rw [frameConnField_minkowski]; ext i j; simp [extrinsic])

end Feec.EinsteinBianchi
