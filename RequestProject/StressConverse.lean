import RequestProject.StreamFormulaMain

/-!
# From the `p,Γ`-equations back to the self-stress equations

This file proves the second half of Lemma `lemma:stress-system-equivalent-Gamma-system`
of the source article (`main.tex`, Section "Proofs"):

> Next suppose `w` satisfies the `p,Γ`-equations. Since Equation
> (\ref{eqn:source-constraint-equations-new}) is satisfied, we can apply Equation
> (\ref{eqn:stream-formula-new}) to source variables, using only paths from their positive
> endpoint, or only paths from their negative endpoint but ignoring the minus sign on the
> first arrow's weight, and both formulas will agree by Lemma
> \ref{lemma:source-constraint-equations-new}. Thus we have values `w_{ij}` for every
> `(i,j) ∈ E` which satisfy all vertex equations.

The argument is organised in three steps.

* `DOrientation.line_step_of_streamFormulas`: a solution of the `p,Γ`-equations satisfies
  the *one-step* relations `± w_ξ = ∑_η frac(ξ → η)|_p · w_η` at every node `ξ` of the
  line graph and every endpoint at which `ξ` enters; for a source read from its negative
  endpoint this is exactly where the source constraint equations are used.
* `DOrientation.cramer_bracket_of_line_step`: the one-step relations are the bracket form
  of Cramer's rule at a vertex.
* `eq_zero_of_colDet_update_eq_zero` and `DOrientation.isSelfStress_of_cramer`: Cramer's
  rule at a vertex, for all `d` edges oriented into it, forces the vertex equation, because
  the `d` incoming edge vectors form a basis at an affinely independent placement.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### A vector all of whose Cramer coordinates vanish is zero -/

/-- If a family `u` of `n` vectors of `ℝ^n` has nonzero determinant and all the
determinants obtained by replacing one of its members by `S` vanish, then `S = 0`. This is
the converse of Cramer's rule used in the proof of Lemma
`lemma:stress-system-equivalent-Gamma-system` of the source article. -/
theorem eq_zero_of_colDet_update_eq_zero {n : ℕ} (u : Fin n → Fin n → ℝ)
    (hu : colDet u ≠ 0) (S : Fin n → ℝ)
    (h : ∀ i, colDet (Function.update u i S) = 0) : S = 0 := by
  classical
  set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => u j i with hA
  have hdet : A.det = colDet u := rfl
  have hcr : A.cramer S = 0 := by
    funext i
    rw [Matrix.cramer_apply, ← colDet_update]
    exact h i
  have hmul := Matrix.mulVec_cramer A S
  rw [hcr] at hmul
  have h0 : A.det • S = 0 := by
    rw [← hmul]
    simp
  rcases smul_eq_zero.1 h0 with hz | hz
  · exact absurd (hdet ▸ hz) hu
  · exact hz

namespace DOrientation

variable (Γ : DOrientation d G)

/-! ### Two orderings of the incoming edges at a vertex -/

/-- The families `incomingFamily a b` and `incomingFamily a b'` of the `d` neighbours of
`a` joined to it by an edge oriented into `a` differ only by a permutation of the `d`
positions, and the permutation may be chosen to send the position of `b'` in the first
family to the last position, where the second family stores `b'`. -/
theorem exists_perm_incomingFamily (hd : 0 < d) {a b : V} (hb : Γ.into a b) (i : Fin d) :
    ∃ σ : Equiv.Perm (Fin d), ∀ c : V,
      Function.update (Γ.incomingFamily a b) i c
        = (Function.update (Γ.incomingFamily a (Γ.incomingFamily a b i)) (lastPos hd) c) ∘ σ := by
  classical
  set f := Γ.incomingFamily a b with hf
  have hfi : Γ.into a (f i) := Γ.incomingFamily_into hb i
  set g := Γ.incomingFamily a (f i) with hg
  have hfinj : Function.Injective f := Γ.incomingFamily_injective hb
  have hginj : Function.Injective g := Γ.incomingFamily_injective hfi
  have himg : ∀ j, ∃ k, g k = f j := by
    intro j
    have hmem : f j ∈ Finset.image g univ := by
      rw [hg, Γ.incomingFamily_image hfi]
      simp only [mem_filter, mem_univ, true_and]
      exact Γ.incomingFamily_into hb j
    simpa using hmem
  choose σ₀ hσ₀ using himg
  have hσ₀inj : Function.Injective σ₀ := by
    intro j j' hjj
    refine hfinj ?_
    rw [← hσ₀ j, ← hσ₀ j', hjj]
  refine ⟨Equiv.ofBijective σ₀ (Finite.injective_iff_bijective.1 hσ₀inj), ?_⟩
  set σ := Equiv.ofBijective σ₀ (Finite.injective_iff_bijective.1 hσ₀inj) with hσ
  have hgσ : ∀ j, g (σ j) = f j := hσ₀
  have hσi : σ i = lastPos (d := d) hd := by
    refine hginj ?_
    rw [hgσ i, hg, Γ.incomingFamily_lastPos hd a (f i)]
  intro c
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, Function.comp_apply, hσi, Function.update_self]
  · have hσj : σ j ≠ lastPos (d := d) hd := by
      rw [← hσi]
      exact fun hcon => hj (σ.injective hcon)
    rw [Function.update_of_ne hj, Function.comp_apply, Function.update_of_ne hσj, hgσ j]

/-- The vanishing of the alternating sum of `cramer_sum_split` at a vertex `a`, known for
the ordering of the incoming edges determined by every incoming edge `b`, gives its
vanishing for any single ordering with the replaced position arbitrary. -/
theorem sum_differenceDet_update_eq_zero (hd : 0 < d) (p : V → Fin d → ℝ)
    (w : OrientedEdge G → ℝ) {a b : V} (hb : Γ.into a b)
    (hcr : ∀ b' : V, Γ.into a b' →
      ∑ c : V, stressVal w a c *
        differenceDet p a (Function.update (Γ.incomingFamily a b') (lastPos hd) c) = 0)
    (i : Fin d) :
    ∑ c : V, stressVal w a c *
      differenceDet p a (Function.update (Γ.incomingFamily a b) i c) = 0 := by
  classical
  obtain ⟨σ, hσ⟩ := Γ.exists_perm_incomingFamily hd hb i
  have hterm : ∀ c : V,
      differenceDet p a (Function.update (Γ.incomingFamily a b) i c)
        = ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            differenceDet p a
              (Function.update (Γ.incomingFamily a (Γ.incomingFamily a b i)) (lastPos hd) c) := by
    intro c
    rw [differenceDet, differenceDet, hσ c]
    exact colDet_comp_perm
      (fun j => edgeVectorAt p a
        (Function.update (Γ.incomingFamily a (Γ.incomingFamily a b i)) (lastPos hd) c j)) σ
  calc ∑ c : V, stressVal w a c *
        differenceDet p a (Function.update (Γ.incomingFamily a b) i c)
      = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ c : V, stressVal w a c *
          differenceDet p a
            (Function.update (Γ.incomingFamily a (Γ.incomingFamily a b i)) (lastPos hd) c) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun c _ => by rw [hterm c]; ring)
    _ = 0 := by
        rw [hcr _ (Γ.incomingFamily_into hb i), mul_zero]

/-! ### Cramer's rule at every incoming edge forces the vertex equation -/

/-- **The converse of Cramer's rule at a vertex.** If a weight function vanishes on the
desert edges and satisfies, at every vertex `a` and every edge `{a,b}` oriented into `a`,
the bracket form `eqn:cramers-rule-new` of Cramer's rule, then it is a self-stress. This
is the linear algebra behind the second half of Lemma
`lemma:stress-system-equivalent-Gamma-system` of the source article. -/
theorem isSelfStress_of_cramer (p : V → Fin d → ℝ) (hp : AffinelyIndependentPlacement d p)
    (w : OrientedEdge G → ℝ)
    (hdes : ∀ i j : V, IsDesertEdge d G i j → stressVal w i j = 0)
    (hcr : ∀ a b : V, Γ.into a b →
      stressVal w a b * bracketEval (placementMatrix p) (Γ.weightColumn a b b a)
        = ∑ c ∈ univ.filter (fun c => ¬ Γ.into a c),
            stressVal w a c * bracketEval (placementMatrix p) (Γ.weightColumn a b a c)) :
    IsSelfStress p w := by
  classical
  intro a k0
  have hd : 0 < d := Fin.pos_iff_nonempty.2 ⟨k0⟩
  set S : Fin d → ℝ := fun k => ∑ c : V, stressVal w a c * edgeVector p a c k with hS
  have hSsum : S = ∑ c : V, stressVal w a c • edgeVectorAt p a c := by
    funext k
    rw [hS]
    simp [edgeVectorAt, Finset.sum_apply]
  have hSzero : S = 0 := by
    by_cases hex : ∃ b : V, Γ.into a b
    · obtain ⟨b, hb⟩ := hex
      -- the alternating sums of `cramer_sum_split` all vanish
      have hcr' : ∀ b' : V, Γ.into a b' →
          ∑ c : V, stressVal w a c *
            differenceDet p a (Function.update (Γ.incomingFamily a b') (lastPos hd) c) = 0 := by
        intro b' hb'
        rw [Γ.cramer_sum_split hd p w hb', hcr a b' hb']
        ring
      set u : Fin d → Fin d → ℝ := fun i => edgeVectorAt p a (Γ.incomingFamily a b i) with hu
      have hune : colDet u ≠ 0 := by
        refine differenceDet_ne_zero p hp a (Γ.incomingFamily a b)
          (Γ.incomingFamily_injective hb) ?_
        intro i
        have hinto := Γ.incomingFamily_into hb i
        exact ((isDeep_nonDesert d G).2.1 _ _ (Γ.into_nonDesert _ _ hinto)).ne'
      refine eq_zero_of_colDet_update_eq_zero u hune S ?_
      intro i
      rw [hSsum, colDet_update_sum]
      have hcong : ∀ c : V, colDet (Function.update u i (edgeVectorAt p a c))
          = differenceDet p a (Function.update (Γ.incomingFamily a b) i c) := by
        intro c
        rw [differenceDet]
        congr 1
        funext j
        by_cases hj : j = i
        · rw [hj, Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj, hu]
      rw [Finset.sum_congr rfl (fun c _ => by rw [hcong c])]
      exact Γ.sum_differenceDet_update_eq_zero hd p w hb hcr' i
    · -- no edge is oriented into `a`, so every edge at `a` is a desert edge
      push_neg at hex
      have hzero : ∀ c : V, stressVal w a c = 0 := by
        intro c
        by_cases hadj : G.Adj a c
        · refine hdes a c ⟨hadj, ?_⟩
          intro hnd
          have hcard := Γ.card_into a c hnd
          have : (univ.filter (fun c' => Γ.into a c')) = ∅ := by
            refine Finset.filter_eq_empty_iff.2 ?_
            intro c' _
            exact hex c'
          rw [this] at hcard
          simp only [Finset.card_empty] at hcard
          omega
        · exact stressVal_eq_zero_of_not_adj w hadj
      funext k
      rw [hS]
      simp [hzero]
  have := congrFun hSzero k0
  rw [hS] at this
  simpa using this

/-! ### The `p,Γ`-equations imply the one-step relations -/

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A non-desert edge which is neither a source nor a sink is a stream (`main.tex`,
Subsection "Main Results"). -/
theorem isStream_of_not_isSource_of_not_isSink {eta : CoreEdge d G}
    (hns : ¬ Γ.IsSource eta.1.1 eta.1.2) (hsink : ¬ Γ.IsSink eta.1.1 eta.1.2) :
    Γ.IsStream eta.1.1 eta.1.2 := by
  have hnd := eta.2.2
  rw [IsSource] at hns
  rw [IsSink] at hsink
  refine ⟨hnd, ?_⟩
  by_cases h1 : Γ.into eta.1.1 eta.1.2 <;> by_cases h2 : Γ.into eta.1.2 eta.1.1 <;> tauto

/-- **The one-step relations hold for every solution of the `p,Γ`-equations.** For a node
`ξ` of the line graph entering at a vertex `a`, the relation
`± w_ξ = ∑_η frac(ξ → η)|_p · w_η` holds. For a stream this is the stream formula, for a
source read at its positive endpoint it is the stream formula applied from that endpoint,
and for a source read at its negative endpoint it is the source constraint equation
(`main.tex`, Section "Proofs"). -/
theorem line_step_of_streamFormulas (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ)
    (hstream : ∀ xi : CoreEdge d G, Γ.IsStream xi.1.1 xi.1.2 →
      w (coreToEdge xi) = Γ.sinkSum p w xi)
    (hsrcpos : ∀ mu : CoreEdge d G, Γ.IsSource mu.1.1 mu.1.2 →
      w (coreToEdge mu) = Γ.sinkSumPos p w mu)
    (hsrc : ∀ mu : CoreEdge d G, Γ.IsSource mu.1.1 mu.1.2 → Γ.sinkSum p w mu = 0)
    {xi : CoreEdge d G} {a : V} (hxi : Γ.EntersAt xi a) :
    (if Γ.IsSource xi.1.1 xi.1.2 ∧ a = xi.1.2 then (-1 : ℝ) else 1) * w (coreToEdge xi)
      = ∑ eta ∈ Γ.succAt a, Γ.fracEval p xi eta * w (coreToEdge eta) := by
  classical
  -- every node reached by an arrow satisfies the stream formula
  have hsucc : ∀ {b : V}, Γ.EntersAt xi b → ∀ eta ∈ Γ.succAt b,
      w (coreToEdge eta) = Γ.sinkSum p w eta := by
    intro b hb eta hmem
    have harr : Γ.LArrow xi eta := ((Γ.mem_succAt_iff_lArrow hb.1 hb.2).1 hmem).1
    have hns : ¬ Γ.IsSource eta.1.1 eta.1.2 := Γ.not_isSource_of_lArrow harr
    by_cases hsink : Γ.IsSink eta.1.1 eta.1.2
    · exact (Γ.sinkSum_of_isSink p w hsink).symm
    · exact hstream eta (Γ.isStream_of_not_isSource_of_not_isSink hns hsink)
  by_cases hsrcxi : Γ.IsSource xi.1.1 xi.1.2
  · -- a source
    have h1 : Γ.EntersAt xi xi.1.1 := Γ.entersAt_fst_of_isSource hsrcxi
    have h2 : Γ.EntersAt xi xi.1.2 := Γ.entersAt_snd_of_isSource hsrcxi
    have hpos : w (coreToEdge xi)
        = ∑ eta ∈ Γ.succAt xi.1.1, Γ.fracEval p xi eta * w (coreToEdge eta) := by
      rw [hsrcpos xi hsrcxi, Γ.sinkSumPos_step p w hsrcxi]
      exact Finset.sum_congr rfl (fun eta hmem => by rw [hsucc h1 eta hmem])
    have hall : (∑ eta ∈ Γ.succAt xi.1.1, Γ.fracEval p xi eta * w (coreToEdge eta))
        + ∑ eta ∈ Γ.succAt xi.1.2, Γ.fracEval p xi eta * w (coreToEdge eta) = 0 := by
      have hnotsink : ¬ Γ.IsSink xi.1.1 xi.1.2 := Γ.not_isSink_of_entersAt h1
      have := hsrc xi hsrcxi
      rw [Γ.sinkSum_step p w hnotsink, Γ.allSucc_eq_union_of_isSource hsrcxi,
        Finset.sum_union (Γ.disjoint_succAt_of_isSource hsrcxi)] at this
      have hs1 : ∑ eta ∈ Γ.succAt xi.1.1, Γ.fracEval p xi eta * Γ.sinkSum p w eta
          = ∑ eta ∈ Γ.succAt xi.1.1, Γ.fracEval p xi eta * w (coreToEdge eta) :=
        Finset.sum_congr rfl (fun eta hmem => by rw [hsucc h1 eta hmem])
      have hs2 : ∑ eta ∈ Γ.succAt xi.1.2, Γ.fracEval p xi eta * Γ.sinkSum p w eta
          = ∑ eta ∈ Γ.succAt xi.1.2, Γ.fracEval p xi eta * w (coreToEdge eta) :=
        Finset.sum_congr rfl (fun eta hmem => by rw [hsucc h2 eta hmem])
      rw [hs1, hs2] at this
      exact this
    rcases hxi.1 with ha | ha
    · subst ha
      rw [if_neg (by rintro ⟨-, hc⟩; exact absurd hc (ne_of_lt xi.2.1)), one_mul]
      exact hpos
    · subst ha
      rw [if_pos ⟨hsrcxi, rfl⟩]
      linarith
  · -- a stream
    have hstreamxi : Γ.IsStream xi.1.1 xi.1.2 :=
      Γ.isStream_of_not_isSource_of_not_isSink hsrcxi (Γ.not_isSink_of_entersAt hxi)
    rw [if_neg (by tauto), one_mul, hstream xi hstreamxi,
      Γ.sinkSum_step p w (Γ.not_isSink_of_entersAt hxi), Γ.allSucc_eq_succAt hxi hsrcxi]
    exact Finset.sum_congr rfl (fun eta hmem => by rw [hsucc hxi eta hmem])

/-! ### The `p,Γ`-equations imply the self-stress equations -/

/-- **The second half of Lemma `lemma:stress-system-equivalent-Gamma-system` of the source
article** (`main.tex`, Section "Proofs"). A weight function which vanishes on the desert
edges, satisfies the stream formula at every stream, the stream formula at every source
read from its positive endpoint, and the source constraint equations, satisfies all the
vertex equations, i.e. it is a self-stress. -/
theorem isSelfStress_of_streamFormulas (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (w : OrientedEdge G → ℝ)
    (hdes : ∀ e : OrientedEdge G, IsDesertEdge d G e.1.1 e.1.2 → w e = 0)
    (hstream : ∀ xi : CoreEdge d G, Γ.IsStream xi.1.1 xi.1.2 →
      w (coreToEdge xi) = Γ.sinkSum p w xi)
    (hsrcpos : ∀ mu : CoreEdge d G, Γ.IsSource mu.1.1 mu.1.2 →
      w (coreToEdge mu) = Γ.sinkSumPos p w mu)
    (hsrc : ∀ mu : CoreEdge d G, Γ.IsSource mu.1.1 mu.1.2 → Γ.sinkSum p w mu = 0) :
    IsSelfStress p w := by
  classical
  -- the stress values vanish on the desert edges
  have hdes' : ∀ i j : V, IsDesertEdge d G i j → stressVal w i j = 0 := by
    intro i j hij
    by_cases hlt : i < j
    · have h := hdes ⟨(i, j), hlt, hij.1⟩ hij
      rw [stressVal, dif_pos ⟨hlt, hij.1⟩]
      exact h
    · have hlt' : j < i := lt_of_le_of_ne (not_lt.1 hlt) hij.1.ne'
      have hij' : IsDesertEdge d G j i :=
        ⟨hij.1.symm, fun hnd => hij.2 ((isDeep_nonDesert d G).1 _ _ hnd)⟩
      have h := hdes ⟨(j, i), hlt', hij'.1⟩ hij'
      rw [stressVal, dif_neg (by exact fun hc => absurd hc.1 hlt), dif_pos ⟨hlt', hij'.1⟩]
      exact h
  refine Γ.isSelfStress_of_cramer p hp w hdes' ?_
  intro a b hab
  have hd : 0 < d := Γ.pos_of_into hab
  have hnd : nonDesert d G a b := Γ.into_nonDesert a b hab
  set xi : CoreEdge d G := mkNode hnd with hxi
  have hmem : a = xi.1.1 ∨ a = xi.1.2 := mkNode_mem hnd
  have hoe : otherEnd xi a = b := otherEnd_mkNode hnd
  have hentersat : Γ.EntersAt xi a := ⟨hmem, by rw [hoe]; exact hab⟩
  have hline := Γ.line_step_of_streamFormulas p w hstream hsrcpos hsrc hentersat
  have hbr := (Γ.line_step_frac_iff_bracket hd p hp w hmem (by rw [hoe]; exact hab)).1 hline
  rw [hoe] at hbr
  have hsv : stressVal w a b = w (coreToEdge xi) := by
    rw [← hoe]
    exact stressVal_otherEnd w hmem
  rw [hsv, hbr]
  exact (Γ.sum_filter_eq_sum_succAt p w (fun c hc => hdes' a c hc) b).symm

end DOrientation

end RigidityTableaux
