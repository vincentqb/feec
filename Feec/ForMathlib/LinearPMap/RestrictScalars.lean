module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Feec.ForMathlib.LinearPMap.Basic

/-!
# Complex partial linear maps viewed over `ℝ`

A complex partial linear map is a real one with the same domain, graph and values; when the real
inner products are the real parts of the complex ones, its real adjoint is the real restriction of
its complex adjoint.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate
open RCLike

namespace LinearPMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F]

/-- A complex partial linear map as a real one (same domain and values). -/
def restrictScalars (T : E →ₗ.[ℂ] F) : E →ₗ.[ℝ] F where
  domain := T.domain.restrictScalars ℝ
  toFun :=
    { toFun := fun x => T ⟨x.1, x.2⟩
      map_add' := fun x y => T.map_add ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
      map_smul' := fun r x => by
        have e : (⟨(r • x : T.domain.restrictScalars ℝ).1, (r • x).2⟩ : T.domain) =
            (r : ℂ) • ⟨x.1, x.2⟩ :=
          Subtype.ext (RCLike.real_smul_eq_coe_smul (K := ℂ) r (x : E))
        rw [e, T.map_smul, RingHom.id_apply]
        exact (RCLike.real_smul_eq_coe_smul (K := ℂ) r _).symm }

variable (T : E →ₗ.[ℂ] F)

@[simp] theorem mem_restrictScalars_domain {x : E} :
    x ∈ T.restrictScalars.domain ↔ x ∈ T.domain := Iff.rfl

theorem restrictScalars_apply (x : T.restrictScalars.domain) :
    T.restrictScalars x = T ⟨x.1, x.2⟩ := rfl

theorem mem_graph_restrictScalars {p : E × F} : p ∈ T.restrictScalars.graph ↔ p ∈ T.graph := by
  simp only [mem_graph_iff]
  exact ⟨fun ⟨y, h1, h2⟩ => ⟨⟨y.1, y.2⟩, h1, h2⟩, fun ⟨y, h1, h2⟩ => ⟨⟨y.1, y.2⟩, h1, h2⟩⟩

theorem isClosed_restrictScalars (hT : T.IsClosed) : T.restrictScalars.IsClosed := by
  have e : (T.restrictScalars.graph : Set (E × F)) = T.graph := by
    ext p; exact T.mem_graph_restrictScalars
  unfold LinearPMap.IsClosed
  rw [e]; exact hT

theorem dense_restrictScalars_domain (hd : Dense (T.domain : Set E)) :
    Dense (T.restrictScalars.domain : Set E) := hd

theorem restrictScalars_zero : (0 : E →ₗ.[ℂ] F).restrictScalars = 0 := by
  refine LinearPMap.ext rfl fun x y h => ?_
  rw [restrictScalars_apply]
  rfl

variable [CompleteSpace E]

theorem adjoint_restrictScalars (hE : ∀ x y : E, ⟪x, y⟫_ℝ = re ⟪x, y⟫_ℂ)
    (hF : ∀ x y : F, ⟪x, y⟫_ℝ = re ⟪x, y⟫_ℂ) (hd : Dense (T.domain : Set E)) :
    (T.restrictScalars)† = (T†).restrictScalars := by
  have hfa := adjoint_isFormalAdjoint hd
  have hle : (T†).restrictScalars ≤ (T.restrictScalars)† := by
    refine IsFormalAdjoint.le_adjoint (T.dense_restrictScalars_domain hd) fun x y => ?_
    rw [restrictScalars_apply, restrictScalars_apply, hF, hE]
    have := hfa ⟨y.1, y.2⟩ ⟨x.1, x.2⟩
    rw [← inner_conj_symm, ← this, inner_conj_symm]
  refine (LinearPMap.eq_of_le_of_domain_le hle fun y hy => ?_).symm
  change y ∈ (T†).domain
  set w := (T.restrictScalars)† ⟨y, hy⟩
  have hra := adjoint_isFormalAdjoint (T.dense_restrictScalars_domain hd)
  have key : ∀ x : T.domain, re ⟪w, (x : E)⟫_ℂ = re ⟪y, T x⟫_ℂ := fun x => by
    have := hra ⟨y, hy⟩ ⟨x.1, x.2⟩
    rw [hE, hF] at this
    exact this
  refine mem_adjoint_domain_of_exists _ ⟨w, fun x => Complex.ext (key x) ?_⟩
  have hI := key (Complex.I • x)
  rw [Submodule.coe_smul, inner_smul_right, LinearPMap.map_smul, inner_smul_right] at hI
  simpa using hI

end LinearPMap
