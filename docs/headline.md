# The crowning theorem, stated in full

**Well-posedness.** Every datum of `D(L)` has a unique classical, strong and weak solution, which conserves the norm (conclusion 1 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_wellPosed`). For all $\mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ}$, $\mathit {Z}:\mathit {F}.\mathrm {Core}$, $\mathit {x}\in {}\mathit {H}.\mathrm {wave}.\mathrm {domain}$ and $\mathit {T}:\mathbb {R}$:

1. $\mathrm {Evolution.IsClassicalSolution}$ $\mathit {H}.\mathrm {wave}$ $(\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T})$ $\mathrm {0}$ $(\mathit {H}.\mathrm {exact}\  \mathit {x})$.
2. For every $\mathit {U}:(\mathbb {R}\to \mathrm {PiLp}\  \mathrm {2}\  \mathit {W})$, if $\mathit {U}\  \mathrm {0}={}$ $\mathit {x}$ and $\mathrm {Evolution.IsStrongSolution}$ $\mathit {H}.\mathrm {wave}$ $(\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T})$ $\mathrm {0}$ $\mathit {U}$, then $\mathrm {Set.EqOn}$ $\mathit {U}$ $(\mathit {H}.\mathrm {exact}\  \mathit {x})$ $(\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T})$.
3. For every $\mathit {U}:(\mathbb {R}\to \mathrm {PiLp}\  \mathrm {2}\  \mathit {W})$, if $\mathit {U}\  \mathrm {0}={}$ $\mathit {x}$ and $\mathrm {HodgeWave.IsWeakSolution}$ $\mathit {H}$ $(\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T})$ $\mathrm {0}$ $\mathit {U}$, then $\mathrm {Set.EqOn}$ $\mathit {U}$ $(\mathit {H}.\mathrm {exact}\  \mathit {x})$ $(\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T})$.
4. For every $\mathit {t}:\mathbb {R}$, $\mathrm {Norm.norm}\  (\mathit {H}.\mathrm {exact}\  \mathit {x}\  \mathit {t})={}$ $\mathrm {Norm.norm}\  \mathit {x}$.

**Propagation.** The flow preserves the constraint if and only if `K` reduces `L` (conclusion 2 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_propagates_iff`). For all $\mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ}$ and $\mathit {Z}:\mathit {F}.\mathrm {Core}$,\
  $\mathit {H}.\mathrm {wave}.\mathrm {IsReducing}$ $\mathit {F}.\mathrm {K}$ if and only if for all $\mathit {t}:\mathbb {R}$ and $\mathit {x}\in {}\mathit {F}.\mathrm {K}$, the state at time $\mathit {t}$ of the solution of $\mathit {H}$ from $\mathit {x}\in {}$ $\mathit {F}.\mathrm {K}$.

**Convergence on the core**, uniformly on `[0, T]` (conclusion 3 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_converges_core`). For all $\mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ}$, $\mathit {Z}:\mathit {F}.\mathrm {Core}$, $\mathit {T}:\mathbb {R}$ and $\mathit {x}\in {}\mathit {Z}.\mathrm {Data}$, $\mathrm {TendstoUniformlyOn}$ $(\mathit {h}\mapsto \mathit {t}\mapsto \mathit {F}.\mathrm {sol}\  \mathit {h}\  ((\mathit {Z}.\mathrm {cmp}\  \mathit {T}).\mathrm {p}\  \mathit {x}\  \mathit {h}\  \mathrm {0})\  \mathit {t})$ $(\mathit {H}.\mathrm {exact}\  \mathit {x})$ $\mathit {F}.\mathrm {l}$ $(\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T})$.

**Convergence on the closure of the core**, from every initial family converging to the datum; one exists (conclusion 4 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_converges`). For all $\mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ}$, $\mathit {Z}:\mathit {F}.\mathrm {Core}$, $\mathit {T}:\mathbb {R}$ and $\mathit {x}\in {}\mathit {Z}.\mathrm {Data}.\mathrm {topologicalClosure}$:

1. $\mathrm {Filter.Tendsto}$ $(\mathit {h}\mapsto \mathrm {DFunLike.coe}\  (\mathit {F}.\mathrm {incl}\  \mathit {h})\  (\mathrm {DFunLike.coe}\  (\mathit {F}.\mathrm {proj}\  \mathit {h})\  \mathit {x}))$ $\mathit {F}.\mathrm {l}$ $(\mathrm {nhds}\  \mathit {x})$.
2. For every $\mathit {v}:(\forall \mathit {h}:\mathit {κ},\mathit {F}.\mathrm {X}\  \mathit {h})$, if $\mathit {v}$ converges to $\mathit {x}$ through the reading maps of $\mathit {F}$, then $\mathrm {TendstoUniformlyOn}$ $(\mathit {h}\mapsto \mathit {t}\mapsto \mathit {F}.\mathrm {sol}\  \mathit {h}\  (\mathit {v}\  \mathit {h})\  \mathit {t})$ $(\mathit {H}.\mathrm {exact}\  \mathit {x})$ $\mathit {F}.\mathrm {l}$ $(\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T})$.

**Rate.** The error is bounded by best approximation, consistency and initial mismatch (conclusion 5 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_rate`). For all $\mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ}$, $\mathit {Z}:\mathit {F}.\mathrm {Core}$, $\mathit {T}:\mathbb {R}$, $\mathit {R}:\mathit {F}.\mathrm {RateClass}\  \mathit {T}$, $\mathit {x}\in {}\mathit {R}.\mathrm {toComparison}.\mathrm {Data}$, $\mathit {h}:\mathit {κ}$, $\mathit {v}:\mathit {F}.\mathrm {X}\  \mathit {h}$ and $\mathit {t}\in {}\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T}$, $\mathrm {Norm.norm}\  (\mathit {H}.\mathrm {exact}\  \mathit {x}\  \mathit {t}-\mathit {F}.\mathrm {sol}\  \mathit {h}\  \mathit {v}\  \mathit {t})\leq {}$ $(\mathit {R}.\mathrm {C}+{}$ $\mathrm {Norm.norm}\  (\mathit {F}.\mathrm {incl}\  \mathit {h})\cdot {}$ $\mathit {R}.\mathrm {C'}\cdot {}$ $\mathit {t})\cdot {}$ $((\mathit {R}.\mathrm {meshSize}\  \mathit {h})^{\mathit {R}.\mathrm {α}}\cdot {}$ $\mathit {R}.\mathrm {classNorm}\  \mathit {x})+{}$ $\mathrm {Norm.norm}\  (\mathit {F}.\mathrm {incl}\  \mathit {h})\cdot {}$ $\mathrm {Norm.norm}\  (\mathit {R}.\mathrm {toComparison}.\mathrm {p}\  \mathit {x}\  \mathit {h}\  \mathrm {0}-\mathit {v})$.

**Reducing constraint.** The residual is bounded by the error and tends to `0` (conclusion 6 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_residual_reducing`). For all $\mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ}$ and $\mathit {Z}:\mathit {F}.\mathrm {Core}$, if $\mathit {H}.\mathrm {wave}.\mathrm {IsReducing}$ $\mathit {F}.\mathrm {K}$, then for every $\mathit {x}\in {}\mathit {F}.\mathrm {K}$:

1. For all $\mathit {h}:\mathit {κ}$, $\mathit {v}:\mathit {F}.\mathrm {X}\  \mathit {h}$ and $\mathit {t}:\mathbb {R}$, the distance of $\mathit {F}.\mathrm {sol}$ $\mathit {h}$ $\mathit {v}$ $\mathit {t}$ to the constraint of $\mathit {F}\leq {}$ $\mathrm {Norm.norm}$ $(\mathit {H}.\mathrm {exact}\  \mathit {x}\  \mathit {t}-\mathit {F}.\mathrm {sol}\  \mathit {h}\  \mathit {v}\  \mathit {t})$.
2. If $\mathit {x}\in {}$ $\mathit {Z}.\mathrm {Data}.\mathrm {topologicalClosure}$, then for all $\mathit {T}:\mathbb {R}$ and $\mathit {v}:(\forall \mathit {h}:\mathit {κ},\mathit {F}.\mathrm {X}\  \mathit {h})$, if $\mathit {v}$ converges to $\mathit {x}$ through the reading maps of $\mathit {F}$, then $\mathrm {TendstoUniformlyOn}$ $(\mathit {h}\mapsto \mathit {t}\mapsto \mathit {F}.\mathrm {residual}\  (\mathit {F}.\mathrm {sol}\  \mathit {h}\  (\mathit {v}\  \mathit {h})\  \mathit {t}))$ $(\_\mapsto \mathrm {0})$ $\mathit {F}.\mathrm {l}$ $(\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T})$.

**A solution leaving a closed set.** The residuals tend to its positive distance (conclusion 7 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_residual_leaves`). For all $\mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ}$, $\mathit {Z}:\mathit {F}.\mathrm {Core}$ and $\mathit {Q}:\mathrm {Set}\  (\mathrm {PiLp}\  \mathrm {2}\  \mathit {W})$, if $\mathrm {IsClosed}$ $\mathit {Q}$ and $\mathit {Q}.\mathrm {Nonempty}$, then for all $\mathit {x}\in {}\mathit {Z}.\mathrm {Data}.\mathrm {topologicalClosure}$ and $\mathit {v}:(\forall \mathit {h}:\mathit {κ},\mathit {F}.\mathrm {X}\  \mathit {h})$, if $\mathit {v}$ converges to $\mathit {x}$ through the reading maps of $\mathit {F}$, then for every $\mathit {t}:\mathbb {R}$, if $\mathrm {0}\leq {}$ $\mathit {t}$ and it is not the case that the state at time $\mathit {t}$ of the solution of $\mathit {H}$ from $\mathit {x}\in {}$ $\mathit {Q}$, then $\mathrm {0}<{}$ $\mathrm {Metric.infDist}\  (\mathit {H}.\mathrm {exact}\  \mathit {x}\  \mathit {t})\  \mathit {Q}$ and $\mathrm {Filter.Tendsto}$ $(\mathit {h}\mapsto \mathrm {Metric.infDist}\  (\mathit {F}.\mathrm {sol}\  \mathit {h}\  (\mathit {v}\  \mathit {h})\  \mathit {t})\  \mathit {Q})$ $\mathit {F}.\mathrm {l}$ $(\mathrm {nhds}\  (\mathrm {Metric.infDist}\  (\mathit {H}.\mathrm {exact}\  \mathit {x}\  \mathit {t})\  \mathit {Q}))$.

**Non-reducing constraint.** A datum of `K` or `Kᗮ` leaves it, with residuals of positive limit when the core is dense (conclusion 8 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_residual_not_reducing`). For all $\mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ}$ and $\mathit {Z}:\mathit {F}.\mathrm {Core}$, if it is not the case that $\mathit {H}.\mathrm {wave}.\mathrm {IsReducing}$ $\mathit {F}.\mathrm {K}$, then for every $\mathit {T}:\mathbb {R}$, if $\mathrm {0}<{}$ $\mathit {T}$, then there is $\mathit {Q}:\mathrm {Submodule}\  \text {𝕜}\  (\mathrm {PiLp}\  \mathrm {2}\  \mathit {W})$ such that

1. Either $\mathit {Q}={}$ $\mathit {F}.\mathrm {K}$ or $\mathit {Q}={}$ $\mathit {F}.\mathrm {K}.\mathrm {orthogonal}$.
2. There are $\mathit {x}\in {}\mathit {Q}$ and $\mathit {t}\in {}\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T}$ such that
   1. It is not the case that the state at time $\mathit {t}$ of the solution of $\mathit {H}$ from $\mathit {x}\in {}$ $\mathit {Q}$.
   2. $\mathrm {0}<{}$ $\mathrm {Metric.infDist}\  (\mathit {H}.\mathrm {exact}\  \mathit {x}\  \mathit {t})\  (\mathrm {SetLike.coe}\  \mathit {Q})$.
   3. If $\mathrm {Dense}$ $(\mathrm {SetLike.coe}\  \mathit {Z}.\mathrm {Data})$, then for every $\mathit {v}:(\forall \mathit {h}:\mathit {κ},\mathit {F}.\mathrm {X}\  \mathit {h})$, if $\mathit {v}$ converges to $\mathit {x}$ through the reading maps of $\mathit {F}$, then $\mathrm {Filter.Tendsto}$ $(\mathit {h}\mapsto \mathrm {Metric.infDist}\  (\mathit {F}.\mathrm {sol}\  \mathit {h}\  (\mathit {v}\  \mathit {h})\  \mathit {t})\  (\mathrm {SetLike.coe}\  \mathit {Q}))$ $\mathit {F}.\mathrm {l}$ $(\mathrm {nhds}\  (\mathrm {Metric.infDist}\  (\mathit {H}.\mathrm {exact}\  \mathit {x}\  \mathit {t})\  (\mathrm {SetLike.coe}\  \mathit {Q})))$.

**Non-reducing constraint, smooth data.** A datum of `D(L) ∩ K` leaves `K` for some `t ∈ [-T, T]` (conclusion 9 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_residual_not_reducing_symm`). For all $\mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ}$ and $\mathit {Z}:\mathit {F}.\mathrm {Core}$, if\
  it is not the case that $\mathit {H}.\mathrm {wave}.\mathrm {IsReducing}$ $\mathit {F}.\mathrm {K}$\
and $\mathit {F}$ has its constraint in the closure of its smooth part, then for every $\mathit {T}:\mathbb {R}$, if $\mathrm {0}<{}$ $\mathit {T}$, then there is $\mathit {x}:\mathrm {Subtype}\  (\mathit {x}\mapsto \mathit {x}\in \mathit {H}.\mathrm {wave}.\mathrm {domain})$ such that

1. $\mathit {x}.\mathrm {val}\in {}$ $\mathit {F}.\mathrm {K}$.
2. There is $\mathit {t}\in {}\mathrm {Set.Icc}\  (-\mathit {T})\  \mathit {T}$ such that
   1. It is not the case that the state at time $\mathit {t}$ of the solution of $\mathit {H}$ from $\mathit {x}.\mathrm {val}\in {}$ $\mathit {F}.\mathrm {K}$.
   2. $\mathrm {0}<$ the distance of $\mathit {H}.\mathrm {exact}$ $\mathit {x}.\mathrm {val}$ $\mathit {t}$ to the constraint of $\mathit {F}$.

**Non-reducing constraint, graded complex.** A datum of `D(L) ∩ K` leaves `K` forward in time, with residuals of positive limit (conclusion 10 of `approxFEEC`).

**Theorem** (`Feec.HilbertComplex.headline_residual_not_reducing_graded`). For all $\mathit {F}:\mathit {H}.\mathrm {ApproxFEEC}\  \mathit {κ}$, $\mathit {Z}:\mathit {F}.\mathrm {Core}$ and $\mathit {p}:(\mathit {ι}\to \mathrm {Bool})$, if $\mathit {p}$ alternates along $\mathit {c}$ and $\mathit {F}$ has its constraint invariant under the reversal by $\mathit {p}$ and $\mathit {F}$ has its constraint in the closure of its smooth part and it is not the case that $\mathit {H}.\mathrm {wave}.\mathrm {IsReducing}$ $\mathit {F}.\mathrm {K}$, then for every $\mathit {T}:\mathbb {R}$, if $\mathrm {0}<{}$ $\mathit {T}$, then there is $\mathit {x}:\mathrm {Subtype}\  (\mathit {x}\mapsto \mathit {x}\in \mathit {H}.\mathrm {wave}.\mathrm {domain})$ such that

1. $\mathit {x}.\mathrm {val}\in {}$ $\mathit {F}.\mathrm {K}$.
2. There is $\mathit {t}\in {}\mathrm {Set.Icc}\  \mathrm {0}\  \mathit {T}$ such that
   1. It is not the case that the state at time $\mathit {t}$ of the solution of $\mathit {H}$ from $\mathit {x}.\mathrm {val}\in {}$ $\mathit {F}.\mathrm {K}$.
   2. $\mathrm {0}<$ the distance of $\mathit {H}.\mathrm {exact}$ $\mathit {x}.\mathrm {val}$ $\mathit {t}$ to the constraint of $\mathit {F}$.
   3. $\mathit {Z}$ detects the departure of $\mathit {x}.\mathrm {val}$ at time $\mathit {t}$.

where for all $\mathit {c}:\mathrm {ComplexShape}\  \mathit {ι}$ and $\mathit {p}:(\mathit {ι}\to \mathrm {Bool})$, $\mathit {p}$ alternates along $\mathit {c}$ means for all $\mathit {i},\mathit {j}:\mathit {ι}$, if $\mathit {c}.\mathrm {Rel}$ $\mathit {i}$ $\mathit {j}$, then $\mathit {p}\  \mathit {j}\neq {}$ $\mathit {p}\  \mathit {i}$.
