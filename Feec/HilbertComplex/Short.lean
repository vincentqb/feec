module

public import Feec.HilbertComplex.Dirac

/-!
# Short Hilbert complexes `W₀ → W₁ → W₂`

Short Hilbert complexes `W₀ --d₀--> W₁ --d₁--> W₂` of closed densely defined operators, as Hilbert
complexes on `ComplexShape.fin3`, with their skew-adjoint wave operator.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

universe u

namespace Feec

/-- A short Hilbert complex `W₀ --d₀--> W₁ --d₁--> W₂` of closed densely defined operators.
[QuennevilleBelair2015], §4.4 -/
structure ShortHilbertComplex (𝕜 : Type*) [RCLike 𝕜] (W₀ W₁ W₂ : Type*)
    [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
    [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
    [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂] where
  d₀ : W₀ →ₗ.[𝕜] W₁
  d₁ : W₁ →ₗ.[𝕜] W₂
  dense₀ : Dense (d₀.domain : Set W₀)
  dense₁ : Dense (d₁.domain : Set W₁)
  closed₀ : d₀.IsClosed
  closed₁ : d₁.IsClosed
  mapsTo : ∀ x : d₀.domain, (d₀ x : W₁) ∈ d₁.domain
  comp : ∀ x : d₀.domain, d₁ ⟨d₀ x, mapsTo x⟩ = 0

namespace ShortHilbertComplex

variable (W₀ W₁ W₂ : Type u)

/-- The spaces of a short complex as a family on `Fin 3`. -/
def W3 : Fin 3 → Type u
  | 0 => W₀
  | 1 => W₁
  | 2 => W₂

variable {𝕜 : Type*} [RCLike 𝕜]
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]

instance instNormedAddCommGroupW3 : ∀ i, NormedAddCommGroup (W3 W₀ W₁ W₂ i)
  | 0 => inferInstanceAs (NormedAddCommGroup W₀)
  | 1 => inferInstanceAs (NormedAddCommGroup W₁)
  | 2 => inferInstanceAs (NormedAddCommGroup W₂)

instance instInnerProductSpaceW3 : ∀ i, InnerProductSpace 𝕜 (W3 W₀ W₁ W₂ i)
  | 0 => inferInstanceAs (InnerProductSpace 𝕜 W₀)
  | 1 => inferInstanceAs (InnerProductSpace 𝕜 W₁)
  | 2 => inferInstanceAs (InnerProductSpace 𝕜 W₂)

instance instCompleteSpaceW3 : ∀ i, CompleteSpace (W3 W₀ W₁ W₂ i)
  | 0 => inferInstanceAs (CompleteSpace W₀)
  | 1 => inferInstanceAs (CompleteSpace W₁)
  | 2 => inferInstanceAs (CompleteSpace W₂)

variable {W₀ W₁ W₂} (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂)

/-- The differentials of `toHilbertComplex`. -/
def d3 : ∀ i j : Fin 3, W3 W₀ W₁ W₂ i →ₗ.[𝕜] W3 W₀ W₁ W₂ j
  | 0, 1 => S.d₀
  | 1, 2 => S.d₁
  | _, _ => 0

/-- A short Hilbert complex as a Hilbert complex on `ComplexShape.fin3`. -/
def toHilbertComplex : HilbertComplex 𝕜 ComplexShape.fin3 (W3 W₀ W₁ W₂) where
  d := S.d3
  shape i j h := by
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd rfl h
  dense i j := by
    fin_cases i <;> fin_cases j <;> first | exact S.dense₀ | exact S.dense₁ | exact dense_univ
  closed i j := by
    fin_cases i <;> fin_cases j <;>
      first | exact S.closed₀ | exact S.closed₁ | exact LinearPMap.isClosed_zero
  mapsTo i j k x := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      first | exact S.mapsTo x | exact Submodule.mem_top |
        exact (apply_eq_zero_of_eq_zero rfl x).symm ▸ Submodule.zero_mem _
  d_comp_d i j k x := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      first | exact S.comp x | rfl |
        exact LinearPMap.apply_mk_eq_zero _ _ (apply_eq_zero_of_eq_zero rfl x)

/-- The Dirac operator `d + d†` of a short complex, on `PiLp 2 (W3 W₀ W₁ W₂)`. -/
abbrev dirac : PiLp 2 (W3 W₀ W₁ W₂) →ₗ.[𝕜] PiLp 2 (W3 W₀ W₁ W₂) := S.toHilbertComplex.dirac

/-- The wave operator `(x₀, x₁, x₂) ↦ (−d₀† x₁, d₀ x₀ − d₁† x₂, d₁ x₁)`.
[QuennevilleBelair2015], (4.5) -/
abbrev wave : PiLp 2 (W3 W₀ W₁ W₂) →ₗ.[𝕜] PiLp 2 (W3 W₀ W₁ W₂) := S.toHilbertComplex.wave

/-- The wave operator of a short complex is skew-adjoint. [QuennevilleBelair2015], Thm 4.6
(adapted) -/
theorem isSkewAdjoint_wave : S.wave.IsSkewAdjoint := S.toHilbertComplex.isSkewAdjoint_wave

end ShortHilbertComplex

namespace HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {W : Fin 3 → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-- A Hilbert complex on `ComplexShape.fin3` as a short complex. -/
def toShort (H : HilbertComplex 𝕜 ComplexShape.fin3 W) :
    ShortHilbertComplex 𝕜 (W 0) (W 1) (W 2) where
  d₀ := H.d 0 1
  d₁ := H.d 1 2
  dense₀ := H.dense 0 1
  dense₁ := H.dense 1 2
  closed₀ := H.closed 0 1
  closed₁ := H.closed 1 2
  mapsTo := H.mapsTo 0 1 2
  comp := H.d_comp_d 0 1 2

end HilbertComplex

namespace ShortHilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
  (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂)

theorem mem_wave_domain {x : PiLp 2 (W3 W₀ W₁ W₂)} : x ∈ S.wave.domain ↔
    (x 0 : W₀) ∈ S.d₀.domain ∧ (x 1 : W₁) ∈ S.d₁.domain ∧ (x 1 : W₁) ∈ S.d₀†.domain ∧
      (x 2 : W₂) ∈ S.d₁†.domain := by
  rw [HilbertComplex.mem_wave_domain]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1 0 1, h1 1 2, h2 0 1, h2 1 2⟩
  · rintro ⟨h0, h1, h1', h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> first | exact h0 | exact h1 | exact Submodule.mem_top
    · fin_cases i <;> fin_cases j <;>
        first | exact h1' | exact h2 |
          exact (show ((0 : W3 W₀ W₁ W₂ _ →ₗ.[𝕜] W3 W₀ W₁ W₂ _)†).domain = ⊤ by
            rw [adjoint_zero]; rfl) ▸ Submodule.mem_top

theorem wave_apply_zero (x : S.wave.domain) :
    ((S.wave x : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀) =
      -(S.d₀† ⟨(x : PiLp 2 (W3 W₀ W₁ W₂)) 1, x.2.2 1 0⟩) := by
  rw [HilbertComplex.wave_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 0 0 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 1 0 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 2 0 = 0 from rfl),
    adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 0 0 = 0 from rfl),
    adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 0 2 = 0 from rfl)]
  simp
  rfl

theorem wave_apply_one (x : S.wave.domain) :
    ((S.wave x : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁) =
      S.d₀ ⟨(x : PiLp 2 (W3 W₀ W₁ W₂)) 0, x.2.1 0 1⟩ -
        S.d₁† ⟨(x : PiLp 2 (W3 W₀ W₁ W₂)) 2, x.2.2 2 1⟩ := by
  rw [HilbertComplex.wave_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 1 1 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 2 1 = 0 from rfl),
    adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 1 0 = 0 from rfl),
    adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 1 1 = 0 from rfl)]
  simp
  rfl

theorem wave_apply_two (x : S.wave.domain) :
    ((S.wave x : PiLp 2 (W3 W₀ W₁ W₂)) 2 : W₂) =
      S.d₁ ⟨(x : PiLp 2 (W3 W₀ W₁ W₂)) 1, x.2.1 1 2⟩ := by
  rw [HilbertComplex.wave_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 0 2 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 2 2 = 0 from rfl),
    adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 2 0 = 0 from rfl),
    adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 2 1 = 0 from rfl),
    adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 2 2 = 0 from rfl)]
  simp
  rfl

end ShortHilbertComplex

namespace ShortHilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- One closed densely defined `T : E → F` as the short complex `E → F → 0`. -/
def ofOp (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) (hc : T.IsClosed) :
    ShortHilbertComplex 𝕜 E F PUnit where
  d₀ := T
  d₁ := 0
  dense₀ := hT
  dense₁ := by simp [zero_domain]
  closed₀ := hc
  closed₁ := LinearPMap.isClosed_zero
  mapsTo _ := Submodule.mem_top
  comp _ := rfl

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- A bounded complex `E --A--> F --B--> G` as a short Hilbert complex.
[QuennevilleBelair2015], §4.2 -/
def ofBounded (A : E →L[𝕜] F) (B : F →L[𝕜] G) (hBA : ∀ x, B (A x) = 0) :
    ShortHilbertComplex 𝕜 E F G where
  d₀ := (A : E →ₗ[𝕜] F).toPMap ⊤
  d₁ := (B : F →ₗ[𝕜] G).toPMap ⊤
  dense₀ := by simp [dense_univ]
  dense₁ := by simp [dense_univ]
  closed₀ := A.isClosed_toPMap_top
  closed₁ := B.isClosed_toPMap_top
  mapsTo _ := Submodule.mem_top
  comp x := hBA x

end ShortHilbertComplex

end Feec
