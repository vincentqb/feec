# The crowning theorem, stated in full

**1. 1. well-posedness (constrainedFEEC\_wellPosed)** (conclusion 1 of `approxFEEC`).

```lean4
theorem approxFEEC_wellPosed (Z : F.Core) :
    (∀ x ∈ H.wave.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 (fun t => H.waveGroup.S t x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      ∀ t, ‖H.waveGroup.S t x‖ = ‖x‖) :=
  (approxFEEC F Z).1
```

**2. 2. propagation iff reducing** (conclusion 2 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_propagates_iff`). $\mathrm {RCLike}\  \text {𝕜}\to {}$ $\mathrm {Fintype}\  \mathit {ι}\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {NormedAddCommGroup}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {InnerProductSpace}$ $\text {𝕜}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\mathit {inst}:\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {CompleteSpace}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {NormedSpace}$ $\mathbb {R}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\mathit {inst}:\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {IsScalarTower}$ $\mathbb {R}$ $\text {𝕜}$ $(\mathit {W}\  \mathit {i}))\to {}$ $\forall \mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ},$ $\mathit {F}.\mathrm {Core}\to {}$ $(\mathit {H}.\mathrm {wave}.\mathrm {IsReducing}\  \mathit {F}.\mathrm {K}\leftrightarrow {}$ $(\forall \mathit {t}:\mathbb {R},{}$ $\forall \mathit {x}:\mathrm {PiLp}\  \mathrm {2}\  \mathit {W},{}$ $\mathit {x}\in {}$ $\mathit {F}.\mathrm {K}\to {}$ $\mathrm {DFunLike.coe}\  (\mathit {H}.\mathrm {waveGroup}.\mathrm {S}\  \mathit {t})\  \mathit {x}\in {}$ $\mathit {F}.\mathrm {K}))$

**3. 3a. convergence on the core** (conclusion 3 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_converges_core`). $\mathrm {RCLike}\  \text {𝕜}\to {}$ $\mathrm {Fintype}\  \mathit {ι}\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {NormedAddCommGroup}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {InnerProductSpace}$ $\text {𝕜}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\mathit {inst}:\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {CompleteSpace}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {NormedSpace}$ $\mathbb {R}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\mathit {inst}:\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {IsScalarTower}$ $\mathbb {R}$ $\text {𝕜}$ $(\mathit {W}\  \mathit {i}))\to {}$ $\forall \mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ},$ $\forall \mathit {Z}:\mathit {F}.\mathrm {Core},$ $\forall \mathit {T}:\mathbb {R},$ $\forall \mathit {x}:\mathrm {PiLp}\  \mathrm {2}\  \mathit {W},$ $\mathit {x}\in {}$ $\mathit {Z}.\mathrm {Data}\to {}$ $\mathrm {TendstoUniformlyOn}$ $(\mathit {h}\mapsto \mathit {t}\mapsto \mathit {F}.\mathrm {sol}\  \mathit {h}\  ((\mathit {Z}.\mathrm {cmp}\  \mathit {T}).\mathrm {p}\  \mathit {x}\  \mathit {h}\  \mathrm {0})\  \mathit {t})$ $(\mathit {t}\mapsto \mathrm {DFunLike.coe}\  (\mathit {H}.\mathrm {waveGroup}.\mathrm {S}\  \mathit {t})\  \mathit {x})$ $\mathit {F}.\mathrm {l}$ $(\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T})$

**4. 3b. convergence on the closure of the core, every convergent initial family; one exists** (conclusion 4 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_converges`). $\mathrm {RCLike}\  \text {𝕜}\to {}$ $\mathrm {Fintype}\  \mathit {ι}\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {NormedAddCommGroup}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {InnerProductSpace}$ $\text {𝕜}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\mathit {inst}:\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {CompleteSpace}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {NormedSpace}$ $\mathbb {R}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\mathit {inst}:\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {IsScalarTower}$ $\mathbb {R}$ $\text {𝕜}$ $(\mathit {W}\  \mathit {i}))\to {}$ $\forall \mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ},$ $\forall \mathit {Z}:\mathit {F}.\mathrm {Core},$ $\forall \mathit {T}:\mathbb {R},$ $\forall \mathit {x}:\mathrm {PiLp}\  \mathrm {2}\  \mathit {W},$ $\mathit {x}\in {}$ $\mathit {Z}.\mathrm {Data}.\mathrm {topologicalClosure}\to {}$ $\mathrm {Filter.Tendsto}\  (\mathit {h}\mapsto \mathrm {DFunLike.coe}\  (\mathit {F}.\mathrm {incl}\  \mathit {h})\  (\mathrm {DFunLike.coe}\  (\mathit {F}.\mathrm {proj}\  \mathit {h})\  \mathit {x}))\  \mathit {F}.\mathrm {l}\  (\mathrm {nhds}\  \mathit {x})\land {}$ $(\forall \mathit {v}:(\forall \mathit {h}:\mathit {κ},\mathit {F}.\mathrm {X}\  \mathit {h}),{}$ $\mathrm {Filter.Tendsto}\  (\mathit {h}\mapsto \mathrm {DFunLike.coe}\  (\mathit {F}.\mathrm {incl}\  \mathit {h})\  (\mathit {v}\  \mathit {h}))\  \mathit {F}.\mathrm {l}\  (\mathrm {nhds}\  \mathit {x})\to {}$ $\mathrm {TendstoUniformlyOn}\  (\mathit {h}\mapsto \mathit {t}\mapsto \mathit {F}.\mathrm {sol}\  \mathit {h}\  (\mathit {v}\  \mathit {h})\  \mathit {t})\  (\mathit {t}\mapsto \mathrm {DFunLike.coe}\  (\mathit {H}.\mathrm {waveGroup}.\mathrm {S}\  \mathit {t})\  \mathit {x})\  \mathit {F}.\mathrm {l}\  (\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T}))$

**5. 3c. rates: best approximation + consistency (+ initial mismatch)** (conclusion 5 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_rate`). $\mathrm {RCLike}\  \text {𝕜}\to {}$ $\mathrm {Fintype}\  \mathit {ι}\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {NormedAddCommGroup}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {InnerProductSpace}$ $\text {𝕜}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\mathit {inst}:\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {CompleteSpace}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {NormedSpace}$ $\mathbb {R}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\mathit {inst}:\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {IsScalarTower}$ $\mathbb {R}$ $\text {𝕜}$ $(\mathit {W}\  \mathit {i}))\to {}$ $\forall \mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ},$ $\mathit {F}.\mathrm {Core}\to {}$ $\forall \mathit {T}:\mathbb {R},$ $\forall \mathit {R}:\mathit {F}.\mathrm {RateClass}\  \mathit {T},$ $\forall \mathit {x}:\mathrm {PiLp}\  \mathrm {2}\  \mathit {W},$ $\mathit {x}\in {}$ $\mathit {R}.\mathrm {toComparison}.\mathrm {Data}\to {}$ $\forall \mathit {h}:\mathit {κ},$ $\forall \mathit {v}:\mathit {F}.\mathrm {X}\  \mathit {h},$ $\forall \mathit {t}:\mathbb {R},$ $\mathit {t}\in {}$ $\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T}\to {}$ $\mathrm {Norm.norm}\  (\mathrm {DFunLike.coe}\  (\mathit {H}.\mathrm {waveGroup}.\mathrm {S}\  \mathit {t})\  \mathit {x}-\mathit {F}.\mathrm {sol}\  \mathit {h}\  \mathit {v}\  \mathit {t})\leq {}$ $(\mathit {R}.\mathrm {C}+{}$ $\mathrm {Norm.norm}\  (\mathit {F}.\mathrm {incl}\  \mathit {h})\cdot {}$ $\mathit {R}.\mathrm {C'}\cdot {}$ $\mathit {t})\cdot {}$ $((\mathit {R}.\mathrm {meshSize}\  \mathit {h})^{\mathit {R}.\mathrm {α}}\cdot {}$ $\mathit {R}.\mathrm {classNorm}\  \mathit {x})+{}$ $\mathrm {Norm.norm}\  (\mathit {F}.\mathrm {incl}\  \mathit {h})\cdot {}$ $\mathrm {Norm.norm}\  (\mathit {R}.\mathrm {toComparison}.\mathrm {p}\  \mathit {x}\  \mathit {h}\  \mathrm {0}-\mathit {v})$

**6. 4a. reducing constraint: residual through ιₕ bounded by the error, tends to 0** (conclusion 6 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_residual_reducing`). $\mathrm {RCLike}\  \text {𝕜}\to {}$ $\mathrm {Fintype}\  \mathit {ι}\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {NormedAddCommGroup}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {InnerProductSpace}$ $\text {𝕜}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\mathit {inst}:\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {CompleteSpace}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {NormedSpace}$ $\mathbb {R}$ $(\mathit {W}\  \mathit {i}))\to {}$ $(\mathit {inst}:\forall \mathit {i}:\mathit {ι},{}$ $\mathrm {IsScalarTower}$ $\mathbb {R}$ $\text {𝕜}$ $(\mathit {W}\  \mathit {i}))\to {}$ $\forall \mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ},$ $\forall \mathit {Z}:\mathit {F}.\mathrm {Core},$ $\mathit {H}.\mathrm {wave}.\mathrm {IsReducing}\  \mathit {F}.\mathrm {K}\to {}$ $\forall \mathit {x}:\mathrm {PiLp}\  \mathrm {2}\  \mathit {W},$ $\mathit {x}\in {}$ $\mathit {F}.\mathrm {K}\to {}$ $(\forall \mathit {h}:\mathit {κ},{}$ $\forall \mathit {v}:\mathit {F}.\mathrm {X}\  \mathit {h},{}$ $\forall \mathit {t}:\mathbb {R},{}$ $\mathrm {Metric.infDist}\  (\mathit {F}.\mathrm {sol}\  \mathit {h}\  \mathit {v}\  \mathit {t})\  (\mathrm {SetLike.coe}\  \mathit {F}.\mathrm {K})\leq {}$ $\mathrm {Norm.norm}\  (\mathrm {DFunLike.coe}\  (\mathit {H}.\mathrm {waveGroup}.\mathrm {S}\  \mathit {t})\  \mathit {x}-\mathit {F}.\mathrm {sol}\  \mathit {h}\  \mathit {v}\  \mathit {t}))\land {}$ $(\mathit {x}\in {}$ $\mathit {Z}.\mathrm {Data}.\mathrm {topologicalClosure}\to {}$ $(\forall \mathit {T}:\mathbb {R},{}$ $\forall \mathit {v}:(\forall \mathit {h}:\mathit {κ},\mathit {F}.\mathrm {X}\  \mathit {h}),{}$ $\mathrm {Filter.Tendsto}\  (\mathit {h}\mapsto \mathrm {DFunLike.coe}\  (\mathit {F}.\mathrm {incl}\  \mathit {h})\  (\mathit {v}\  \mathit {h}))\  \mathit {F}.\mathrm {l}\  (\mathrm {nhds}\  \mathit {x})\to {}$ $\mathrm {TendstoUniformlyOn}\  (\mathit {h}\mapsto \mathit {t}\mapsto \mathrm {Metric.infDist}\  (\mathit {F}.\mathrm {sol}\  \mathit {h}\  (\mathit {v}\  \mathit {h})\  \mathit {t})\  (\mathrm {SetLike.coe}\  \mathit {F}.\mathrm {K}))\  (\_\mapsto \mathrm {0})\  \mathit {F}.\mathrm {l}\  (\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T})))$

**7. 4b. per datum: a solution leaving Q has residual tending to dist(e^{tL}x, Q) > 0** (conclusion 7 of `approxFEEC`).

```lean4
theorem headline_residual_leaves (Z : F.Core) :
    (∀ Q : Set (PiLp 2 W), IsClosed Q → Q.Nonempty → ∀ x ∈ Z.Data.topologicalClosure,
      ∀ v : ∀ h, F.X h, Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) → ∀ t, 0 ≤ t →
      H.waveGroup.S t x ∉ Q → 0 < infDist (H.waveGroup.S t x) Q ∧
        Tendsto (fun h => infDist (F.sol h (v h) t) Q) F.l
          (𝓝 (infDist (H.waveGroup.S t x) Q))) :=
  (approxFEEC F Z).2.2.2.2.2.2.1
```

**8. 4b. a non-reducing constraint is left by data of K or Kᗮ; with a dense core, the residuals of every convergent discretization of that datum have a positive limit** (conclusion 8 of `approxFEEC`).

```lean4
theorem headline_residual_not_reducing (Z : F.Core) :
    (¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = F.K ∨ Q = F.Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
        H.waveGroup.S t x ∉ Q ∧ 0 < infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)) ∧
        (Dense (Z.Data : Set (PiLp 2 W)) → ∀ v : ∀ h, F.X h,
          Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
          Tendsto (fun h => infDist (F.sol h (v h) t) (Q : Set (PiLp 2 W))) F.l
            (𝓝 (infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)))))) :=
  (approxFEEC F Z).2.2.2.2.2.2.2.1
```

**9. 4c. with D(L) ∩ K dense in K: a datum of D(L) ∩ K leaves K for some t ∈ \[-T, T\]** (conclusion 9 of `approxFEEC`).

```lean4
theorem headline_residual_not_reducing_symm (Z : F.Core) :
    (¬ H.wave.IsReducing F.K →
      (∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) → ∀ T : ℝ, 0 < T →
      ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc (-T) T,
        H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W))) :=
  (approxFEEC F Z).2.2.2.2.2.2.2.2.1
```

**10. 4c. graded complex, R-invariant K, D(L) ∩ K dense in K: a datum of D(L) ∩ K leaves K forward in time, with residuals tending to a positive limit** (conclusion 10 of `approxFEEC`).

```lean4
theorem headline_residual_not_reducing_graded (Z : F.Core) :
    (∀ p : ι → Bool, (∀ i j, c.Rel i j → p j ≠ p i) → (∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K) →
      (∀ k ∈ F.K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) →
      ¬ H.wave.IsReducing F.K → ∀ T : ℝ, 0 < T →
      ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ F.K ∧ ∃ t ∈ Icc 0 T,
        H.waveGroup.S t x ∉ F.K ∧ 0 < infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) ∧
        ((x : PiLp 2 W) ∈ Z.Data.topologicalClosure → ∀ v : ∀ h, F.X h,
          Tendsto (fun h => F.incl h (v h)) F.l (𝓝 x) →
          Tendsto (fun h => infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W))) F.l
            (𝓝 (infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)))) ∧
          ∀ᶠ h in F.l, infDist (H.waveGroup.S t x) (F.K : Set (PiLp 2 W)) / 2 <
            infDist (F.sol h (v h) t) (F.K : Set (PiLp 2 W)))) :=
  (approxFEEC F Z).2.2.2.2.2.2.2.2.2
```
