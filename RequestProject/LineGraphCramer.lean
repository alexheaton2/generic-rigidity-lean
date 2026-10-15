import RequestProject.CramerStep

/-!
# Cramer's rule read in the `Γ`-oriented line graph

This file translates equation `eqn:cramers-rule-new` of the source article (`main.tex`,
Section "Proofs", inside the proof of Lemma `lemma:stream-formula-new`) from a statement
about the vertices of `G` into a statement about the arrows of the `Γ`-oriented line
graph `𝓛`:

> Since every path in `𝓛` reaching `(a,b)_a` extends to a path using the arrow
> `(a,b)_a → (a,c_k)` for `k = 1,…,m` …

Concretely, `DOrientation.cramer_line_step` states, for a node `ξ` of `𝓛` oriented into
one of its endpoints `a`, the relation
`w_ξ · 𝔡_𝔞|_p = ∑_{η} w_η · 𝔲_𝔞|_p`,
the sum running over the nodes `η` reached from `ξ` by an arrow using `a`; here `𝔡` and
`𝔲` are the down- and up-weights of the corresponding arrows. The version
`DOrientation.cramer_line_step_div` divides by the (nonzero) down-weight and is the form
`w_ξ = ∑_η frac(𝔞)|_p · w_η` used in the source article.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A non-desert edge of `G`, viewed as an edge of `G`. -/
def coreToEdge (e : CoreEdge d G) : OrientedEdge G :=
  ⟨e.1, e.2.1, (isDeep_nonDesert d G).2.1 _ _ e.2.2⟩

/-- The stress coordinate of a node of the line graph is the stress coordinate of the
corresponding edge of `G`. -/
theorem stressVal_coreToEdge (w : OrientedEdge G → ℝ) (xi : CoreEdge d G) :
    stressVal w xi.1.1 xi.1.2 = w (coreToEdge xi) := by
  rw [stressVal, dif_pos ⟨xi.2.1, (isDeep_nonDesert d G).2.1 _ _ xi.2.2⟩]
  rfl

/-- The node of the line graph determined by a non-desert edge `{a,c}`. -/
noncomputable def mkNode {a c : V} (h : nonDesert d G a c) : CoreEdge d G :=
  if hlt : a < c then ⟨(a, c), hlt, h⟩
  else ⟨(c, a), lt_of_le_of_ne (not_lt.1 hlt)
    (((isDeep_nonDesert d G).2.1 a c h).ne.symm), (isDeep_nonDesert d G).1 a c h⟩

theorem mkNode_mem {a c : V} (h : nonDesert d G a c) :
    a = (mkNode h).1.1 ∨ a = (mkNode h).1.2 := by
  rw [mkNode]
  by_cases hlt : a < c
  · rw [dif_pos hlt]; exact Or.inl rfl
  · rw [dif_neg hlt]; exact Or.inr rfl

theorem otherEnd_mkNode {a c : V} (h : nonDesert d G a c) :
    DOrientation.otherEnd (mkNode h) a = c := by
  have hne : a ≠ c := ((isDeep_nonDesert d G).2.1 a c h).ne
  rw [mkNode, DOrientation.otherEnd]
  by_cases hlt : a < c
  · rw [dif_pos hlt]; simp
  · rw [dif_neg hlt]; simp [hne]

theorem mkNode_otherEnd {a : V} {eta : CoreEdge d G} (h : a = eta.1.1 ∨ a = eta.1.2)
    (hnd : nonDesert d G a (DOrientation.otherEnd eta a)) : mkNode hnd = eta := by
  have hlt := eta.2.1
  rcases h with h | h
  · have hoe : DOrientation.otherEnd eta a = eta.1.2 := by
      rw [DOrientation.otherEnd, if_pos h]
    have : a < eta.1.2 := h ▸ hlt
    apply Subtype.ext
    rw [mkNode]
    rw [dif_pos (by rw [hoe]; exact this)]
    show ((a, DOrientation.otherEnd eta a) : V × V) = (eta : V × V)
    rw [hoe]
    exact Prod.ext_iff.2 ⟨h, rfl⟩
  · have hne : a ≠ eta.1.1 := by rw [h]; exact (ne_of_gt hlt)
    have hoe : DOrientation.otherEnd eta a = eta.1.1 := by
      rw [DOrientation.otherEnd, if_neg hne]
    apply Subtype.ext
    rw [mkNode]
    rw [dif_neg (by rw [hoe, h]; exact not_lt.2 (le_of_lt hlt))]
    show ((DOrientation.otherEnd eta a, a) : V × V) = (eta : V × V)
    rw [hoe]
    exact Prod.ext_iff.2 ⟨rfl, h⟩

theorem stressVal_mkNode (w : OrientedEdge G → ℝ) {a c : V} (h : nonDesert d G a c) :
    stressVal w a c = w (coreToEdge (mkNode h)) := by
  have hadj : G.Adj a c := (isDeep_nonDesert d G).2.1 a c h
  rw [mkNode]
  by_cases hlt : a < c
  · rw [dif_pos hlt, stressVal, dif_pos ⟨hlt, hadj⟩]
    rfl
  · have hlt' : c < a := lt_of_le_of_ne (not_lt.1 hlt) hadj.ne.symm
    rw [dif_neg hlt, stressVal, dif_neg (by exact fun hc => absurd hc.1 hlt),
      dif_pos ⟨hlt', hadj.symm⟩]
    rfl

theorem stressVal_otherEnd (w : OrientedEdge G → ℝ) {a : V} {xi : CoreEdge d G}
    (ha : a = xi.1.1 ∨ a = xi.1.2) :
    stressVal w a (DOrientation.otherEnd xi a) = w (coreToEdge xi) := by
  rcases ha with h | h
  · rw [DOrientation.otherEnd, if_pos h, h, stressVal_coreToEdge]
  · have hne : a ≠ xi.1.1 := by rw [h]; exact (ne_of_gt xi.2.1)
    rw [DOrientation.otherEnd, if_neg hne, h, stressVal_symm, stressVal_coreToEdge]

namespace DOrientation

variable (Γ : DOrientation d G)

/-- The nodes of the line graph reached from a node oriented into `a` by an arrow using
`a`: those non-desert edges `η` at `a` which are oriented *out* of `a` (`main.tex`,
Subsection "Main Results": *"whose arrows point between adjacent edges `ξ → η` whenever
`ξ` is oriented into a vertex that `η` is oriented out of"*). -/
noncomputable def succAt (a : V) : Finset (CoreEdge d G) :=
  univ.filter (fun eta => (a = eta.1.1 ∨ a = eta.1.2) ∧ ¬ Γ.into a (otherEnd eta a))

theorem mem_succAt {a : V} {eta : CoreEdge d G} :
    eta ∈ Γ.succAt a ↔ (a = eta.1.1 ∨ a = eta.1.2) ∧ ¬ Γ.into a (otherEnd eta a) := by
  simp [succAt]

/-- The arrows of the line graph leaving `ξ` through the endpoint `a` at which `ξ` is
oriented into are exactly the nodes of `succAt a`. -/
theorem mem_succAt_iff_lArrow {a : V} {xi eta : CoreEdge d G}
    (ha : a = xi.1.1 ∨ a = xi.1.2) (hb : Γ.into a (otherEnd xi a)) :
    eta ∈ Γ.succAt a ↔ (Γ.LArrow xi eta ∧ sharedVertex xi eta = a) := by
  constructor
  · intro hmem
    rw [Γ.mem_succAt] at hmem
    obtain ⟨hend, hout⟩ := hmem
    have hshared : sharedVertex xi eta = a := by
      rcases ha with h | h
      · have hpos : xi.1.1 = eta.1.1 ∨ xi.1.1 = eta.1.2 := by
          rcases hend with h' | h'
          · exact Or.inl (h.symm.trans h')
          · exact Or.inr (h.symm.trans h')
        rw [sharedVertex, if_pos hpos]
        exact h.symm
      · have hnot : ¬ (xi.1.1 = eta.1.1 ∨ xi.1.1 = eta.1.2) := by
          intro hcon
          -- then `η` has both endpoints `a` and `xi.1.1`, so `otherEnd η a = xi.1.1`
          have hne : xi.1.1 ≠ a := by rw [h]; exact ne_of_lt xi.2.1
          have hoe : otherEnd eta a = xi.1.1 := by
            rcases hend with he | he
            · rw [otherEnd, if_pos he]
              rcases hcon with hc | hc
              · exact absurd (hc.trans he.symm) hne
              · exact hc.symm
            · have hne2 : a ≠ eta.1.1 := by
                rw [he]; exact (ne_of_gt eta.2.1)
              rw [otherEnd, if_neg hne2]
              rcases hcon with hc | hc
              · exact hc.symm
              · exact absurd (hc.trans he.symm) hne
          have hoexi : otherEnd xi a = xi.1.1 := by
            rw [otherEnd, if_neg (by rw [h]; exact (ne_of_gt xi.2.1))]
          rw [hoe] at hout
          rw [hoexi] at hb
          exact hout hb
        rw [sharedVertex, if_neg hnot]
        exact h.symm
    refine ⟨⟨?_, ?_⟩, hshared⟩
    · intro hcon
      rw [hcon] at hb
      exact hout hb
    · rw [hshared]
      exact ⟨hend, hb, hout⟩
  · rintro ⟨harr, hshared⟩
    have h2 : (sharedVertex xi eta = eta.1.1 ∨ sharedVertex xi eta = eta.1.2) ∧
        Γ.into (sharedVertex xi eta) (otherEnd xi (sharedVertex xi eta)) ∧
        ¬ Γ.into (sharedVertex xi eta) (otherEnd eta (sharedVertex xi eta)) := harr.2
    rw [hshared] at h2
    rw [Γ.mem_succAt]
    exact ⟨h2.1, h2.2.2⟩

/-- **The two ways of summing the up-brackets at a vertex agree.** The sum over the
vertices `c` such that `{a,c}` is not oriented into `a`, of the stress coordinate
`w_{ac}` against the up-bracket `[j_1 … j_{d-1} a c]|_p`, equals the sum of the same
quantities over the nodes `η` of the line graph reached from `a` by an arrow, as soon as
the stress vanishes on the desert edges at `a`. This is the passage between the vertex
equations and the line graph used in both directions of Lemma
`lemma:stress-system-equivalent-Gamma-system` of the source article. -/
theorem sum_filter_eq_sum_succAt (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ) {a : V}
    (hdes : ∀ c : V, IsDesertEdge d G a c → stressVal w a c = 0) (b : V) :
    ∑ c ∈ univ.filter (fun c => ¬ Γ.into a c),
        stressVal w a c * bracketEval (placementMatrix p) (Γ.weightColumn a b a c)
      = ∑ eta ∈ Γ.succAt a, w (coreToEdge eta) *
          bracketEval (placementMatrix p) (Γ.weightColumn a b a (otherEnd eta a)) := by
  classical
  -- restrict the sum to the non-desert edges at `a`
  have hsub : (univ.filter (fun c => ¬ Γ.into a c ∧ nonDesert d G a c))
      ⊆ univ.filter (fun c => ¬ Γ.into a c) := by
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    exact hc.1
  have hzero : ∀ c ∈ univ.filter (fun c => ¬ Γ.into a c),
      c ∉ univ.filter (fun c => ¬ Γ.into a c ∧ nonDesert d G a c) →
      stressVal w a c * bracketEval (placementMatrix p) (Γ.weightColumn a b a c) = 0 := by
    intro c hc hc'
    simp only [mem_filter, mem_univ, true_and] at hc hc'
    have hnd : ¬ nonDesert d G a c := fun h => hc' ⟨hc, h⟩
    have : stressVal w a c = 0 := by
      by_cases hadj : G.Adj a c
      · exact hdes c ⟨hadj, hnd⟩
      · exact stressVal_eq_zero_of_not_adj w hadj
    rw [this, zero_mul]
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_bij' (fun c hc => mkNode (by
      simp only [mem_filter, mem_univ, true_and] at hc; exact hc.2))
    (fun eta _ => otherEnd eta a) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    rw [Γ.mem_succAt]
    refine ⟨mkNode_mem _, ?_⟩
    rw [otherEnd_mkNode]
    exact hc.1
  · intro eta hmem
    rw [Γ.mem_succAt] at hmem
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨hmem.2, ?_⟩
    rcases hmem.1 with h | h
    · rw [otherEnd, if_pos h, h]; exact eta.2.2
    · have hne : a ≠ eta.1.1 := by rw [h]; exact (ne_of_gt eta.2.1)
      rw [otherEnd, if_neg hne, h]
      exact (isDeep_nonDesert d G).1 _ _ eta.2.2
  · intro c hc
    exact otherEnd_mkNode _
  · intro eta hmem
    rw [Γ.mem_succAt] at hmem
    exact mkNode_otherEnd hmem.1 _
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    rw [otherEnd_mkNode, ← stressVal_mkNode w hc.2]

/-- **Equation `eqn:cramers-rule-new` of the source article, read in the line graph**
(`main.tex`, Section "Proofs"). For a node `ξ` of the line graph oriented into one of its
endpoints `a`, the stress coordinate of `ξ` times the down-weight of the arrows leaving
`ξ` through `a` equals the sum, over the nodes `η` reached by such an arrow, of the stress
coordinate of `η` times the up-weight of the arrow `ξ → η`. -/
theorem cramer_line_step (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w)
    {xi : CoreEdge d G} {a : V} (ha : a = xi.1.1 ∨ a = xi.1.2)
    (hb : Γ.into a (otherEnd xi a)) :
    w (coreToEdge xi) *
        bracketEval (placementMatrix p) (Γ.weightColumn a (otherEnd xi a) (otherEnd xi a) a)
      = ∑ eta ∈ Γ.succAt a, w (coreToEdge eta) *
          bracketEval (placementMatrix p)
            (Γ.weightColumn a (otherEnd xi a) a (otherEnd eta a)) := by
  classical
  have hkey := Γ.cramer_bracket hd p w hw hb
  rw [stressVal_otherEnd w ha] at hkey
  rw [hkey]
  exact Γ.sum_filter_eq_sum_succAt p w
    (fun c hc => stressVal_eq_zero_of_isDesertEdge p hp w hw a c hc) _

end DOrientation

end RigidityTableaux
