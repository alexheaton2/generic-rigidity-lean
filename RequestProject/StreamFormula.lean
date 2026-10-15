import RequestProject.LineGraphCramer

/-!
# Fractions along the arrows of the line graph, and the one-step stream formula

This file introduces the quantities used in Lemma `lemma:stream-formula-new` of the
source article (`main.tex`, Section "Proofs"), namely the fractions
`frac(𝔞) = 𝔲_𝔞 / 𝔡_𝔞` attached to the arrows of the `Γ`-oriented line graph, their
products along paths, and the finite sets of paths joining two nodes.

Its main result, `DOrientation.cramer_line_step_div`, is the *one-step* form of the
stream formula: for a node `ξ` which is not a source and is oriented into an endpoint
`a`,
`w_ξ = ∑_η frac(ξ → η)|_p · w_η`,
the sum being over the nodes `η` reached from `ξ` by an arrow using `a`. This is
equation `eqn:cramers-rule-new` of the source article written with the fractions
`frac(𝔞)`; the full stream formula follows from it by *"repeated substitution of
variables, using (\ref{eqn:cramers-rule-new}) at every node along paths starting at
`(i,j)` and ending at a sink"*.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace DOrientation

variable (Γ : DOrientation d G)

/-- The fraction `frac(𝔞) = 𝔲_𝔞 / 𝔡_𝔞` of an arrow of the line graph, evaluated at a
placement `p` (`main.tex`, Section "Examples": *"Let `frac(𝔞) = 𝔲_𝔞 / 𝔡_𝔞`"*). -/
noncomputable def fracEval (p : V → Fin d → ℝ) (xi eta : CoreEdge d G) : ℝ :=
  tableauEval (placementMatrix p) (Γ.arrowUp xi eta)
    / tableauEval (placementMatrix p) (Γ.arrowDown xi eta)

/-- The product `∏_{𝔞 ∈ 𝒫} frac(𝔞)|_p` of the fractions along a path of the line graph. -/
noncomputable def pathFracEval (p : V → Fin d → ℝ) (l : List (CoreEdge d G)) : ℝ :=
  ((l.zip l.tail).map (fun x => Γ.fracEval p x.1 x.2)).prod

/-- The finite set of all duplicate-free lists of nodes of the line graph. Since the
`Γ`-oriented line graph is acyclic, every directed path of `𝓛` occurs in it. -/
noncomputable def nodupLists (d : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (List (CoreEdge d G)) :=
  Finset.image Subtype.val (univ : Finset {L : List (CoreEdge d G) // L.Nodup})

theorem mem_nodupLists {L : List (CoreEdge d G)} : L ∈ nodupLists d G ↔ L.Nodup := by
  simp [nodupLists]

/-- The finite set of paths of the line graph from a node `ξ` to a node `ν`. Since the
`Γ`-oriented line graph is acyclic, every path repeats no node. -/
noncomputable def pathsFrom (xi nu : CoreEdge d G) : Finset (List (CoreEdge d G)) :=
  (nodupLists d G).filter (fun L => Γ.IsLPath xi nu L)

theorem mem_pathsFrom {xi nu : CoreEdge d G} {L : List (CoreEdge d G)} :
    L ∈ Γ.pathsFrom xi nu ↔ L.Nodup ∧ Γ.IsLPath xi nu L := by
  simp [pathsFrom, mem_nodupLists]

/-- The paths of the line graph from a node `μ` to a node `ν` which leave `μ` at its
**positive endpoint**, that is, whose first arrow uses the smaller of the two endpoints of
`μ`. For a source, the arrows leaving it at its negative endpoint are precisely those
whose up-weight carries a minus sign (`main.tex`, Subsection "Main Results" and Section
"Proofs": *"applying (\ref{eqn:stream-formula-new}) to streams and also to sources from
their positive endpoint"*). -/
noncomputable def pathsFromPos (mu nu : CoreEdge d G) : Finset (List (CoreEdge d G)) :=
  (nodupLists d G).filter (fun L => Γ.IsLPath mu nu L ∧
    ∀ eta ∈ L.tail.head?, sharedVertex mu eta = mu.1.1)

/-! ### The weights of an arrow evaluated at a placement -/

/-- The down-weight `𝔡_𝔞 = [j_1 … j_{d-1} b a]` of an arrow, evaluated at a placement. -/
theorem tableauEval_arrowDown (p : V → Fin d → ℝ) (xi eta : CoreEdge d G) :
    tableauEval (placementMatrix p) (Γ.arrowDown xi eta)
      = bracketEval (placementMatrix p)
          (Γ.weightColumn (sharedVertex xi eta) (otherEnd xi (sharedVertex xi eta))
            (otherEnd xi (sharedVertex xi eta)) (sharedVertex xi eta)) := by
  simp [arrowDown, tableauEval, Tableau.sign]

/-- The up-weight `𝔲_𝔞 = [j_1 … j_{d-1} a c]` of an arrow, evaluated at a placement. The
arrow is blue, i.e. carries a minus sign, exactly when it leaves a source from its
negative endpoint, the larger of the two (`main.tex`, Subsection "Main Results"). -/
theorem tableauEval_arrowUp (p : V → Fin d → ℝ) (xi eta : CoreEdge d G) :
    tableauEval (placementMatrix p) (Γ.arrowUp xi eta)
      = (if Γ.IsSource xi.1.1 xi.1.2 ∧ sharedVertex xi eta = xi.1.2 then (-1 : ℝ) else 1)
        * bracketEval (placementMatrix p)
          (Γ.weightColumn (sharedVertex xi eta) (otherEnd xi (sharedVertex xi eta))
            (sharedVertex xi eta) (otherEnd eta (sharedVertex xi eta))) := by
  by_cases h : Γ.IsSource xi.1.1 xi.1.2 ∧ sharedVertex xi eta = xi.1.2
  · simp [arrowUp, tableauEval, Tableau.sign, h.1, h.2]
  · simp [arrowUp, tableauEval, Tableau.sign, h]

/-- The up-weight of an arrow leaving a node which is not a source; such an arrow is red,
so no sign intervenes. -/
theorem tableauEval_arrowUp_of_not_isSource (p : V → Fin d → ℝ) (xi eta : CoreEdge d G)
    (h : ¬ Γ.IsSource xi.1.1 xi.1.2) :
    tableauEval (placementMatrix p) (Γ.arrowUp xi eta)
      = bracketEval (placementMatrix p)
          (Γ.weightColumn (sharedVertex xi eta) (otherEnd xi (sharedVertex xi eta))
            (sharedVertex xi eta) (otherEnd eta (sharedVertex xi eta))) := by
  rw [Γ.tableauEval_arrowUp p xi eta, if_neg (by tauto), one_mul]

/-- **The down-weight of an arrow never vanishes at an affinely independent placement**
(`main.tex`, Section "Proofs": Cramer's rule *"is valid by affine independence, no matter
the choice of `d` incoming edges"*). -/
theorem bracketEval_weightColumn_down_ne_zero (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) {a b : V} (hab : Γ.into a b) :
    bracketEval (placementMatrix p) (Γ.weightColumn a b b a) ≠ 0 := by
  rw [Γ.bracketEval_weightColumn_down p a b]
  refine differenceDet_ne_zero p hp a _ (Γ.incomingFamily_injective hab) ?_
  intro i
  have hinto := Γ.incomingFamily_into hab i
  exact ((isDeep_nonDesert d G).2.1 _ _ (Γ.into_nonDesert _ _ hinto)).ne'

/-- **The fraction form and the bracket form of the one-step relation are equivalent.**
For a node `ξ` of the line graph oriented into its endpoint `a`, the relation
`± w_ξ = ∑_η frac(ξ → η)|_p · w_η` of the source article (`main.tex`, Section "Proofs",
equation `eqn:cramers-rule-new` written with the fractions `frac(𝔞) = 𝔲_𝔞 / 𝔡_𝔞`) holds
if and only if the corresponding relation between the brackets themselves holds. No
self-stress hypothesis is needed: this is the mere clearing of denominators, valid
because the down-bracket does not vanish at an affinely independent placement. -/
theorem line_step_frac_iff_bracket (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (w : OrientedEdge G → ℝ)
    {xi : CoreEdge d G} {a : V} (ha : a = xi.1.1 ∨ a = xi.1.2)
    (hb : Γ.into a (otherEnd xi a)) :
    ((if Γ.IsSource xi.1.1 xi.1.2 ∧ a = xi.1.2 then (-1 : ℝ) else 1) * w (coreToEdge xi)
        = ∑ eta ∈ Γ.succAt a, Γ.fracEval p xi eta * w (coreToEdge eta))
      ↔ (w (coreToEdge xi) *
            bracketEval (placementMatrix p)
              (Γ.weightColumn a (otherEnd xi a) (otherEnd xi a) a)
          = ∑ eta ∈ Γ.succAt a, w (coreToEdge eta) *
              bracketEval (placementMatrix p)
                (Γ.weightColumn a (otherEnd xi a) a (otherEnd eta a))) := by
  classical
  set b := otherEnd xi a with hbdef
  set D := bracketEval (placementMatrix p) (Γ.weightColumn a b b a) with hD
  set s := (if Γ.IsSource xi.1.1 xi.1.2 ∧ a = xi.1.2 then (-1 : ℝ) else 1) with hs
  have hDne : D ≠ 0 := Γ.bracketEval_weightColumn_down_ne_zero hd p hp hb
  have hs2 : s * s = 1 := by rw [hs]; split <;> norm_num
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hs2
    exact zero_ne_one hs2
  have hfrac : ∀ eta ∈ Γ.succAt a, Γ.fracEval p xi eta * w (coreToEdge eta)
      = s * (w (coreToEdge eta) *
          bracketEval (placementMatrix p) (Γ.weightColumn a b a (otherEnd eta a))) / D := by
    intro eta hmem
    have hshared : sharedVertex xi eta = a :=
      ((Γ.mem_succAt_iff_lArrow ha hb).1 hmem).2
    rw [fracEval, Γ.tableauEval_arrowUp p xi eta, Γ.tableauEval_arrowDown p xi eta, hshared,
      ← hbdef, ← hD, ← hs]
    field_simp
  rw [Finset.sum_congr rfl hfrac, ← Finset.sum_div, ← Finset.mul_sum, eq_div_iff hDne]
  constructor
  · intro h
    refine mul_left_cancel₀ hsne ?_
    rw [← mul_assoc]
    exact h
  · intro h
    rw [mul_assoc, h]

/-- **The one-step stream formula, with the sign of the source article** (`main.tex`,
Section "Proofs", equation `eqn:cramers-rule-new` written with the fractions
`frac(𝔞) = 𝔲_𝔞 / 𝔡_𝔞`). For a node `ξ` of the line graph oriented into its endpoint `a`,
`± w_ξ = ∑_η frac(ξ → η)|_p · w_η`, the sum running over the nodes `η` reached from `ξ` by
an arrow using `a`; the sign is negative exactly when `ξ` is a source and `a` is its
negative (larger) endpoint, since the arrows leaving a source from its negative endpoint
are blue. -/
theorem cramer_line_step_div_signed (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w)
    {xi : CoreEdge d G} {a : V} (ha : a = xi.1.1 ∨ a = xi.1.2)
    (hb : Γ.into a (otherEnd xi a)) :
    (if Γ.IsSource xi.1.1 xi.1.2 ∧ a = xi.1.2 then (-1 : ℝ) else 1) * w (coreToEdge xi)
      = ∑ eta ∈ Γ.succAt a, Γ.fracEval p xi eta * w (coreToEdge eta) :=
  (Γ.line_step_frac_iff_bracket hd p hp w ha hb).2 (Γ.cramer_line_step hd p hp w hw ha hb)

/-- **The one-step stream formula** for a node which is not a source (`main.tex`,
Section "Proofs", equation `eqn:cramers-rule-new`): `w_ξ = ∑_η frac(ξ → η)|_p · w_η`. -/
theorem cramer_line_step_div (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w)
    {xi : CoreEdge d G} {a : V} (ha : a = xi.1.1 ∨ a = xi.1.2)
    (hb : Γ.into a (otherEnd xi a)) (hns : ¬ Γ.IsSource xi.1.1 xi.1.2) :
    w (coreToEdge xi) = ∑ eta ∈ Γ.succAt a, Γ.fracEval p xi eta * w (coreToEdge eta) := by
  have h := Γ.cramer_line_step_div_signed hd p hp w hw ha hb
  rwa [if_neg (by tauto), one_mul] at h

end DOrientation

end RigidityTableaux
