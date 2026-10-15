# Formalization map: `main.tex` → Lean

Every formal declaration carries a docstring naming the informal statement it comes from.
This file is the reverse index: for each numbered item of the article, the Lean name, the
file it lives in, and its current status.

The Lean development is in `RequestProject/`:

| file | contents |
| --- | --- |
| `Rigidity.lean` | placements, affine independence, genericity, self-stresses, the rigidity map, infinitesimal rigidity, continuous flexes, Maxwell's count |
| `Tableaux.lean` | tableaux, colours, semistandard tableaux, exchange rules, brackets, straightening to zero, red/blue balance, multidegrees |
| `Orientation.lean` | deserts and the non-desert graph, `d`-orientations, sources/streams/sinks, the `Γ`-oriented line graph, weights, path systems, balancing conditions, balanced / balanced at `p` / `d`-balanced |
| `Multidegree.lean` | multidegree bookkeeping for weights, paths and path systems |
| `Generic.lean` | generic placements are affinely independent |
| `OrientationExists.lean` | existence of `d`-orientations; existence of sinks |
| `Sylvester.lean` | determinants of families of columns, exchanges of entries between two families, and Sylvester's exchange identity |
| `GenericEvaluation.lean` | evaluation of bracket polynomials at a placement, and the two directions of the generic evaluation lemma |
| `DesertStress.lean` | self-stresses vanish on desert edges |
| `PathDecomposition.lean`, `StreamFormula.lean`, `StreamFormulaMain.lean` | paths of the line graph, the fractions `frac(𝔞)|_p`, and the stream formula |
| `CramerStep.lean`, `LineGraphCramer.lean`, `LineGraphAcyclic.lean`, `RowSelection.lean` | Cramer's rule along the arrows of the line graph, and its acyclicity |
| `StressConverse.lean` | the converse direction: a solution of the `p,Γ`-equations is a self-stress |
| `MinorRank.lean` | a matrix has a nonzero kernel vector exactly when all its maximal minors vanish |
| `SinkSystem.lean` | the `p,Γ`-equations as a homogeneous linear system in the sink coordinates, with coefficients the path sums `Q` |
| `PathSplice.lean` | splitting a directed path of the line graph at a node, node ranks, and splicing |
| `LGVInvolution.lean` | the sign-reversing involution: exchanging the tails of two crossing paths |
| `LGV.lean` | the Lindström–Gessel–Viennot lemma for the `Γ`-oriented line graph |
| `BalancingEval.lean` | evaluating a balancing condition at a placement |
| `RedBlue.lean` | the exchange rules preserve the bracket polynomial, the linear independence of the semistandard tableaux, and the equivalence between red/blue balance and straightening to zero |
| `Results.lean` | the numbered results of the article |

## Definitions

| article | Lean |
| --- | --- |
| tableau, colour, product of columns | `Tableau`, `Tableau.mul`, `Tableau.listProd` |
| semistandard tableau | `IsSemistandard` |
| exchange rules, reduction of a multiset of tableaux | `exchangeCols`, `exchangeResult`, `TabStep`, `MultisetStep`, `ReducesTo` |
| brackets, evaluation at a matrix | `bracketEval`, `tableauEval`, `multisetEval` |
| straightens to zero (lies in the Plücker ideal) | `StraightensToZero` |
| each semistandard tableau equally often red and blue | `RedBlueBalanced` |
| vertex multidegree, multi-homogeneous | `colDegree`, `tableauDegree`, `MultiHomogeneous` |
| desert edges, non-desert graph | `IsDeep`, `nonDesert`, `IsDesertEdge`, `isDeep_nonDesert` |
| the orientation `Γ` | `DOrientation` |
| source, stream, sink | `DOrientation.IsSource`, `IsStream`, `IsSink` |
| the `Γ`-oriented line graph `𝓛`, its arrows | `CoreEdge`, `DOrientation.LArrow` |
| up-weight `𝔲_𝔞`, down-weight `𝔡_𝔞` | `DOrientation.arrowUp`, `DOrientation.arrowDown` |
| paths, path systems, disjoint path systems | `DOrientation.IsLPath`, `PathSystemData`, `IsDisjointPathSystem`, `disjointSystems` |
| weight `wt(𝒫)` of a path system | `DOrientation.systemWeight` |
| balancing condition `{{wt(𝒫)}}` | `DOrientation.balancingCondition` |
| `Γ` balanced; `G` is `d`-balanced | `DOrientation.Balanced`, `IsDBalanced` |
| `Γ` balanced at `p`; `G` balanced at `p` | `DOrientation.BalancedAt`, `BalancedAtPlacement` |
| `frac(𝔞)`, `frac(𝒫)` evaluated at `p` | `DOrientation.fracEval`, `DOrientation.pathFracEval` |
| affinely independent placement | `AffinelyIndependentPlacement` |
| generic placement | `GenericPlacement` |
| edge vectors, vertex equations, self-stress `wA = 0` | `edgeVector`, `stressVal`, `IsSelfStress` |
| the coefficient matrix `A`; infinitesimal rigidity/flexibility | `rigidityMap`, `infFlexes`, `InfinitesimallyRigid`, `InfinitesimallyFlexible` |
| Maxwell's count `\|E\| = d\|V\| - binom (d+1) 2` | `MaxwellCount` |
| locally flexible, generically locally flexible, generically rigid | `IsFlex`, `LocallyFlexible`, `GenericallyLocallyFlexible`, `GenericallyRigid` |
| the matrix `M` with columns `(p_i, 1)`, evaluation `·\|_p` | `placementMatrix`, `evalAtPlacement` |

## Results

| article | Lean | status |
| --- | --- | --- |
| Lemma `lemma:semistandard-tableaux-span` | `lemma_semistandard_tableaux_span` | **proved** |
| Theorem `thm:main-Maxwell-locally-flexible` | `theorem_main_Maxwell_locally_flexible` | **proved** |
| Corollary `cor:characterization` | `corollary_characterization` | **proved** |
| Theorem `thm:balanced-equivalent-to-selfstress` | `theorem_balanced_equivalent_to_selfstress` | **proved** |
| Corollary `cor:affine-Maxwell-infinitesimally-flexible` | `corollary_affine_Maxwell_infinitesimally_flexible` | **proved** |
| Lemma `lemma:remove-common-factors` | `lemma_remove_common_factors` | **proved** (with the hypothesis `0 < n`, see below); the underlying statement `straightensToZero_iff_removeCommon` is **proved** |
| Lemma `lemma:stream-formula-new` | `DOrientation.lemma_stream_formula` | **proved** |
| Lemma `lemma:source-constraint-equations-new` | `DOrientation.lemma_source_constraint_equations` | **proved** |
| Lemma `lemma:stress-system-equivalent-Gamma-system` | `DOrientation.lemma_stress_system_equivalent_Gamma_system` | **proved** |
| Lemma `lemma:balanced-equivalent-nonzero-solution` | `DOrientation.lemma_balanced_equivalent_nonzero_solution` | **proved** (using the Lindström–Gessel–Viennot lemma below) |
| Lemma `lemma:Gamma-equivalent-to-Gamma'` | `lemma_Gamma_equivalent_to_Gamma'` | **proved** |
| Proposition `proposition:Sylvester-exchange` | `proposition_Sylvester_exchange` | **proved** (via `colDet_mul_colDet_eq_sum_exchTerm` of `Sylvester.lean`) |
| Lemma `lemma:red-blue-equiv-straighten-to-zero` | `lemma_red_blue_equiv_straighten_to_zero` | **proved** (in `RedBlue.lean`, with the hypothesis `0 < n`, see below) |
| Lemma `lemma:balancing-multihomogeneous-new` | `lemma_balancing_multihomogeneous` | **proved** |
| Lemma `lemma:generic-evaluation-straightening-new` | `lemma_generic_evaluation_straightening` | **proved** (both directions in `GenericEvaluation.lean`) |
| Lemma `lemma:generic-geometric-balancing` | `lemma_generic_geometric_balancing` | **proved** |
| Lemma `lemma:generic-orientation-independent` | `lemma_generic_orientation_independent` | **proved** |

## Additional results proved along the way

| statement | Lean | status |
| --- | --- | --- |
| under Maxwell's count, infinitesimal flexibility ⟺ a nonzero self-stress exists (the linear algebra inside `cor:affine-Maxwell-infinitesimally-flexible`) | `infinitesimallyFlexible_iff_exists_nonzero_selfStress` | **proved** |
| `w` is a self-stress ⟺ `w` annihilates the range of the rigidity map | `isSelfStress_iff` | **proved** |
| a generic placement is affinely independent | `affinelyIndependentPlacement_of_generic` | **proved** |
| every graph carries a `d`-orientation | `exists_dOrientation` | **proved** |
| whenever there are non-desert edges, there is at least one sink | `DOrientation.exists_isSink_of_hasNonDesertEdge` | **proved** |
| `deg 𝔲_𝔞 + deg ξ = deg 𝔡_𝔞 + deg η` for every arrow, and its telescoping along paths and path systems | `DOrientation.arrowDegree_telescope`, `pathDegree_telescope`, `systemDegree_telescope`, `systemWeightDegree_eq` | **proved** |
| the non-desert edges form a graph of minimum degree `d+1` | `isDeep_nonDesert` | **proved** |
| Sylvester's exchange identity for determinants of families of columns, over an arbitrary commutative ring | `colDet_mul_colDet_eq_sum_exchTerm` | **proved** |
| the exchange term does not depend on the chosen matching of the two sets of positions | `exchTerm_eq`, `exchTerm_eq_perm` | **proved** |
| a multi-homogeneous bracket polynomial vanishing at one generic placement vanishes at all placements, hence straightens to zero | `straightensToZero_of_evalAtPlacement_zero` | **proved** |
| the first step of the proof of the stream formula: for an affinely independent placement, a self-stress vanishes on every desert edge | `stressVal_eq_zero_of_isDesertEdge`, `selfStress_eq_zero_of_isDesertEdge` | **proved** |
| the edges carrying a nonzero stress form a `d`-deep edge relation | `isDeep_nonzeroStressEdges` | **proved** |
| the Lindström–Gessel–Viennot lemma quoted in the proof of `lemma:balanced-equivalent-nonzero-solution`: the determinant of the matrix of path sums is the signed sum of `frac(𝒫)|_p` over the disjoint path systems | `DOrientation.det_pathSum_eq_sum_disjointSystems` | **proved** |
| the expansion of that determinant over *all* path systems, disjoint or not | `DOrientation.det_pathSum_eq_sum_allSystems` | **proved** |
| the sign-reversing involution: the non-disjoint path systems cancel in pairs | `DOrientation.sum_sdiff_eq_zero`, `DOrientation.cross_cross`, `DOrientation.CrossData.sharedNodes_swapAt` | **proved** |
| the rank of a node of the line graph increases strictly along its arrows (acyclicity), and the splicing of two directed paths at a common node | `DOrientation.nodeRank_lt_of_lArrow`, `DOrientation.isChain_splice` | **proved** |
| a matrix has a nonzero kernel vector exactly when all its maximal minors vanish | `exists_nonzero_kernel_iff_forall_det_eq_zero` | **proved** |
| the `p,Γ`-equations have a nonzero solution exactly when the source constraint system in the sink coordinates does | `DOrientation.exists_nonzero_pGammaSolution_iff` | **proved** |
| a solution of the `p,Γ`-equations is a self-stress | `DOrientation.isSelfStress_of_streamFormulas` | **proved** |

## Additional results of `RedBlue.lean`

| statement | Lean | status |
| --- | --- | --- |
| the exchange rules, the permutation of a column and the vanishing of a tableau with a repeated entry do not change the bracket polynomial | `RedBlue.tabStep_eval`, `RedBlue.multisetStep_eval`, `RedBlue.reducesTo_eval` | **proved** |
| a multiset containing every product of columns equally often red and blue evaluates to zero at every matrix | `RedBlue.multisetEval_eq_zero_of_redBlueBalanced` | **proved** |
| the leading monomial of the bracket of a strictly increasing column, for the lexicographic order on the variables of the generic matrix, is the diagonal monomial, with coefficient one | `RedBlue.degree_bracketEval`, `RedBlue.degree_prod_bracketEval` | **proved** |
| a semistandard tableau is determined by the multiset of the entries of each of its rows, i.e. by the leading monomial of its product of brackets | `RedBlue.colsExp_injective` | **proved** |
| distinct semistandard tableaux are linearly independent: a multiset of semistandard tableaux whose bracket polynomial straightens to zero is red/blue balanced | `RedBlue.redBlueBalanced_of_straightensToZero` | **proved** |
| for tableaux of height `n = 0` the lemma `lemma:red-blue-equiv-straighten-to-zero` is false | `RedBlue.not_redBlue_equiv_straightensToZero_of_height_zero` | **proved** |

## Conventions and caveats

* The theorems of Asimow and Roth quoted in the introduction of the article (generic local
  rigidity is equivalent to infinitesimal rigidity) and the existence of generic
  placements are **not** assumed as axioms: they appear as explicit hypotheses `hAR` and
  `hgen` of the statements that use them.
* As in the article, the dimension `d` is a positive integer wherever this matters; this
  is recorded as an explicit hypothesis `0 < d`.
* Lemma `lemma:red-blue-equiv-straighten-to-zero` needs the hypothesis `0 < n` on the
  height of the tableaux, which the article leaves implicit (its tableaux have `n = d + 1`
  rows). Without it the statement is false: for `n = 0` every bracket is the determinant of
  the empty matrix, that is `1`, and one red tableau with no column together with one blue
  tableau with one column is reduced, semistandard, has bracket polynomial `1 - 1 = 0` and
  is not red/blue balanced. The counterexample is formalized as
  `RedBlue.not_redBlue_equiv_straightensToZero_of_height_zero`; the statement without the
  hypothesis is kept, commented out, in `Tableaux.lean`. The hypothesis is available at
  every place where the lemma is used, since there `n = d + 1`.
* "Straightens to zero" is formalized as the vanishing of the bracket polynomial on the
  generic matrix, which the article states to be equivalent to belonging to the Plücker
  ideal.
* Local flexibility is formalized as the existence of a continuous motion of the vertices
  starting at `p`, preserving the lengths of all bars, and changing at least one distance
  between two vertices.
* The worked examples of Section "Examples" of the article (planar envelope, octahedron,
  double banana, …) are illustrative computations and are not formalized here.
* In the `p,Γ`-equations (`IsPGammaSolution`) the stream formula is applied to the streams
  using all paths of the line graph leaving them, and to the sources using only the paths
  leaving them at their *positive* endpoint (`pathsFromPos`), exactly as the article
  prescribes. Using all paths for the sources as well would be inconsistent with the
  source constraint equations, since the arrows leaving a source at its negative endpoint
  carry a blue (negative) up-weight, so that the sum over all paths leaving a source is
  the difference of the two sums, which the source constraint equations set to zero.
