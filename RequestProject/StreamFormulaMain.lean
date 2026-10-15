import RequestProject.PathDecomposition

/-!
# The stream formula

This file proves the main computation behind Lemma `lemma:stream-formula-new` of the
source article (`main.tex`, Section "Proofs"):

> Since every path in `𝓛` reaching `(a,b)_a` extends to a path using the arrow
> `(a,b)_a → (a,c_k)` for `k = 1,…,m`, the formula (\ref{eqn:stream-formula-new}) follows
> upon repeated substitution of variables, using (\ref{eqn:cramers-rule-new}) at every
> node along paths starting at `(i,j)` and ending at a sink.

The substitution is organised as an induction on the rank of the vertex at which a node
of the line graph enters, which increases strictly along the arrows of `𝓛`.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace DOrientation

variable (Γ : DOrientation d G)

/-- If some edge is oriented into a vertex then `d` is positive. -/
theorem pos_of_into {a b : V} (h : Γ.into a b) : 0 < d := by
  classical
  have hcard := Γ.card_into a b (Γ.into_nonDesert a b h)
  rw [← hcard]
  refine Finset.card_pos.2 ⟨b, ?_⟩
  simp only [mem_filter, mem_univ, true_and]
  exact h

/-- The right-hand side of the stream formula of the source article: the combination
`∑_ν (∑_{paths 𝒫 : ξ → ν} ∏_{𝔞 ∈ 𝒫} frac(𝔞)|_p) w_ν` of the sink coordinates
(`main.tex`, Section "Proofs", equation `eqn:stream-formula-new`). -/
noncomputable def sinkSum (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ)
    (xi : CoreEdge d G) : ℝ :=
  ∑ nu ∈ Γ.sinks, (∑ L ∈ Γ.pathsFrom xi nu, Γ.pathFracEval p L) * w (coreToEdge nu)

/-- At a sink the stream formula is trivially true: the only path leaving a sink is the
trivial one. -/
theorem sinkSum_of_isSink (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ)
    {nu0 : CoreEdge d G} (h : Γ.IsSink nu0.1.1 nu0.1.2) :
    Γ.sinkSum p w nu0 = w (coreToEdge nu0) := by
  classical
  rw [sinkSum, Finset.sum_eq_single nu0]
  · rw [Γ.sum_pathsFrom_of_isSink p h, if_pos rfl, one_mul]
  · intro nu _ hne
    rw [Γ.sum_pathsFrom_of_isSink p h, if_neg hne, zero_mul]
  · intro hmem
    exact absurd (by simp only [sinks, mem_filter, mem_univ, true_and]; exact h) hmem

/-- **The sink sums satisfy the same one-step relation as the stress coordinates.** For a
node `ξ` which is not a sink, `sinkSum ξ = ∑_η frac(ξ → η)|_p · sinkSum η`, the sum running
over the nodes `η` reached from `ξ` by an arrow. -/
theorem sinkSum_step (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ) {xi : CoreEdge d G}
    (hxi : ¬ Γ.IsSink xi.1.1 xi.1.2) :
    Γ.sinkSum p w xi = ∑ eta ∈ Γ.allSucc xi, Γ.fracEval p xi eta * Γ.sinkSum p w eta := by
  classical
  rw [sinkSum]
  have hcongr : ∀ nu ∈ Γ.sinks,
      (∑ L ∈ Γ.pathsFrom xi nu, Γ.pathFracEval p L) * w (coreToEdge nu)
        = ∑ eta ∈ Γ.allSucc xi, Γ.fracEval p xi eta *
            ((∑ L ∈ Γ.pathsFrom eta nu, Γ.pathFracEval p L) * w (coreToEdge nu)) := by
    intro nu hnu
    have hsink : Γ.IsSink nu.1.1 nu.1.2 := by
      simpa only [sinks, mem_filter, mem_univ, true_and] using hnu
    have hne : xi ≠ nu := fun hcon => hxi (by rw [hcon]; exact hsink)
    rw [Γ.sum_pathsFrom_cons p hne, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun eta _ => by ring)
  rw [Finset.sum_congr rfl hcongr, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun eta _ => ?_)
  rw [sinkSum, Finset.mul_sum]

/-- **Lemma `lemma:stream-formula-new` of the source article**, in the form covering both
streams and sources treated from one of their endpoints: for an affinely independent
placement `p` and a self-stress `w`, the stress coordinate of a node `ξ` of the line graph
which is not a source and enters at a vertex `a` is the combination
`∑_ν (∑_{paths 𝒫 : ξ → ν} ∏_{𝔞 ∈ 𝒫} frac(𝔞)|_p) w_ν` of the sink coordinates. -/
theorem selfStress_eq_sinkSum (p : V → Fin d → ℝ) (hp : AffinelyIndependentPlacement d p)
    (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w) {xi : CoreEdge d G} {a : V}
    (hxi : Γ.EntersAt xi a) (hns : ¬ Γ.IsSource xi.1.1 xi.1.2) :
    w (coreToEdge xi) = Γ.sinkSum p w xi := by
  classical
  set N := (univ.sup Γ.rank) + 1 with hN
  have hrank : ∀ v : V, Γ.rank v < N := by
    intro v
    exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ v))
  have key : ∀ m : ℕ, ∀ (xi : CoreEdge d G) (a : V), N - Γ.rank a ≤ m →
      Γ.EntersAt xi a → ¬ Γ.IsSource xi.1.1 xi.1.2 →
      w (coreToEdge xi) = Γ.sinkSum p w xi := by
    intro m
    induction m with
    | zero =>
      intro xi a hle _ _
      have := hrank a
      omega
    | succ m ih =>
      intro xi a hle hxi hns
      have hd : 0 < d := Γ.pos_of_into hxi.2
      have hstep := Γ.cramer_line_step_div hd p hp w hw hxi.1 hxi.2 hns
      rw [hstep, Γ.sinkSum_step p w (Γ.not_isSink_of_entersAt hxi),
        Γ.allSucc_eq_succAt hxi hns]
      refine Finset.sum_congr rfl (fun eta hmem => ?_)
      obtain ⟨harr, hsv⟩ := (Γ.mem_succAt_iff_lArrow hxi.1 hxi.2).1 hmem
      have hnseta : ¬ Γ.IsSource eta.1.1 eta.1.2 := Γ.not_isSource_of_lArrow harr
      by_cases hsink : Γ.IsSink eta.1.1 eta.1.2
      · rw [Γ.sinkSum_of_isSink p w hsink]
      · obtain ⟨a', ha'⟩ := Γ.exists_entersAt_of_not_isSink hsink
        have hlt : Γ.rank a < Γ.rank a' := by
          have := Γ.rank_lt_of_lArrow harr ha'
          rwa [hsv] at this
        have hle' : N - Γ.rank a' ≤ m := by omega
        rw [ih eta a' hle' ha' hnseta]
  exact key (N - Γ.rank a) xi a le_rfl hxi hns

/-- Every node reached from another node by an arrow of the line graph satisfies the
stream formula: it is either a sink or a stream. -/
theorem selfStress_eq_sinkSum_of_lArrow (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w)
    {xi eta : CoreEdge d G} (h : Γ.LArrow xi eta) :
    w (coreToEdge eta) = Γ.sinkSum p w eta := by
  have hns := Γ.not_isSource_of_lArrow h
  by_cases hsink : Γ.IsSink eta.1.1 eta.1.2
  · exact (Γ.sinkSum_of_isSink p w hsink).symm
  · obtain ⟨a', ha'⟩ := Γ.exists_entersAt_of_not_isSink hsink
    exact Γ.selfStress_eq_sinkSum p hp w hw ha' hns

/-- A source enters at its smaller (positive) endpoint. -/
theorem entersAt_fst_of_isSource {mu : CoreEdge d G} (h : Γ.IsSource mu.1.1 mu.1.2) :
    Γ.EntersAt mu mu.1.1 :=
  ⟨Or.inl rfl, by rw [otherEnd, if_pos rfl]; exact h.2.1⟩

/-- A source enters at its larger (negative) endpoint. -/
theorem entersAt_snd_of_isSource {mu : CoreEdge d G} (h : Γ.IsSource mu.1.1 mu.1.2) :
    Γ.EntersAt mu mu.1.2 :=
  ⟨Or.inr rfl, by rw [otherEnd, if_neg (ne_of_gt mu.2.1)]; exact h.2.2⟩

/-- The arrows leaving a source use one of its two endpoints. -/
theorem allSucc_eq_union_of_isSource {mu : CoreEdge d G} (h : Γ.IsSource mu.1.1 mu.1.2) :
    Γ.allSucc mu = Γ.succAt mu.1.1 ∪ Γ.succAt mu.1.2 := by
  classical
  have h1 := Γ.entersAt_fst_of_isSource h
  have h2 := Γ.entersAt_snd_of_isSource h
  ext eta
  rw [Γ.mem_allSucc, Finset.mem_union, Γ.mem_succAt_iff_lArrow h1.1 h1.2,
    Γ.mem_succAt_iff_lArrow h2.1 h2.2]
  constructor
  · intro harr
    rcases sharedVertex_mem mu eta with hs | hs
    · exact Or.inl ⟨harr, hs⟩
    · exact Or.inr ⟨harr, hs⟩
  · rintro (⟨harr, -⟩ | ⟨harr, -⟩) <;> exact harr

/-- No arrow leaves a source through both of its endpoints. -/
theorem disjoint_succAt_of_isSource {mu : CoreEdge d G} (h : Γ.IsSource mu.1.1 mu.1.2) :
    Disjoint (Γ.succAt mu.1.1) (Γ.succAt mu.1.2) := by
  classical
  rw [Finset.disjoint_left]
  intro eta he1 he2
  rw [Γ.mem_succAt] at he1 he2
  have hmu : eta = mu := by
    apply Subtype.ext
    rcases he1.1 with ha | ha <;> rcases he2.1 with hb | hb
    · exact absurd (ha.trans hb.symm) (ne_of_lt mu.2.1)
    · exact Prod.ext_iff.2 ⟨ha.symm, hb.symm⟩
    · exact absurd (lt_of_lt_of_eq (lt_of_eq_of_lt hb eta.2.1) ha.symm) (asymm mu.2.1)
    · exact absurd (ha.trans hb.symm) (ne_of_lt mu.2.1)
  subst hmu
  refine he1.2 ?_
  rw [otherEnd, if_pos rfl]
  exact h.2.1

/-- The right-hand side of the stream formula for a source, using only the paths leaving
it at its **positive endpoint** (`main.tex`, Section "Proofs": *"applying
(\ref{eqn:stream-formula-new}) to streams and also to sources from their positive
endpoint"*). -/
noncomputable def sinkSumPos (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ)
    (mu : CoreEdge d G) : ℝ :=
  ∑ nu ∈ Γ.sinks, (∑ L ∈ Γ.pathsFromPos mu nu, Γ.pathFracEval p L) * w (coreToEdge nu)

/-- The one-step relation for the sink sums of a source taken over the paths leaving it at
its positive endpoint. -/
theorem sinkSumPos_step (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ) {mu : CoreEdge d G}
    (hmu : Γ.IsSource mu.1.1 mu.1.2) :
    Γ.sinkSumPos p w mu
      = ∑ eta ∈ Γ.succAt mu.1.1, Γ.fracEval p mu eta * Γ.sinkSum p w eta := by
  classical
  have hnotsink : ¬ Γ.IsSink mu.1.1 mu.1.2 :=
    Γ.not_isSink_of_entersAt (Γ.entersAt_fst_of_isSource hmu)
  rw [sinkSumPos]
  have hcongr : ∀ nu ∈ Γ.sinks,
      (∑ L ∈ Γ.pathsFromPos mu nu, Γ.pathFracEval p L) * w (coreToEdge nu)
        = ∑ eta ∈ Γ.succAt mu.1.1, Γ.fracEval p mu eta *
            ((∑ L ∈ Γ.pathsFrom eta nu, Γ.pathFracEval p L) * w (coreToEdge nu)) := by
    intro nu hnu
    have hsink : Γ.IsSink nu.1.1 nu.1.2 := by
      simpa only [sinks, mem_filter, mem_univ, true_and] using hnu
    have hne : mu ≠ nu := fun hcon => hnotsink (by rw [hcon]; exact hsink)
    rw [Γ.sum_pathsFromPos_cons p hmu hne, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun eta _ => by ring)
  rw [Finset.sum_congr rfl hcongr, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun eta _ => ?_)
  rw [sinkSum, Finset.mul_sum]

/-- **The stream formula applied to a source from its positive endpoint** (`main.tex`,
Section "Proofs"). For an affinely independent placement and a self-stress, the stress
coordinate of a source is the combination of the sink coordinates given by the paths that
leave it at its smaller endpoint. -/
theorem selfStress_eq_sinkSumPos_of_isSource (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w)
    {mu : CoreEdge d G} (hmu : Γ.IsSource mu.1.1 mu.1.2) :
    w (coreToEdge mu) = Γ.sinkSumPos p w mu := by
  classical
  have hd : 0 < d := Γ.pos_of_into hmu.2.1
  have h1 := Γ.entersAt_fst_of_isSource hmu
  rw [Γ.sinkSumPos_step p w hmu]
  have hrepl : ∀ eta ∈ Γ.succAt mu.1.1,
      Γ.fracEval p mu eta * Γ.sinkSum p w eta
        = Γ.fracEval p mu eta * w (coreToEdge eta) := by
    intro eta hmem
    have harr : Γ.LArrow mu eta := ((Γ.mem_succAt_iff_lArrow h1.1 h1.2).1 hmem).1
    rw [← Γ.selfStress_eq_sinkSum_of_lArrow p hp w hw harr]
  rw [Finset.sum_congr rfl hrepl]
  have hpos := Γ.cramer_line_step_div_signed hd p hp w hw h1.1 h1.2
  rw [if_neg (by rintro ⟨-, hc⟩; exact absurd hc (ne_of_lt mu.2.1)), one_mul] at hpos
  exact hpos

/-- **Lemma `lemma:source-constraint-equations-new` of the source article.** For a source
`μ`, the stream formula applied at its positive endpoint and at its negative endpoint give
the same value up to sign, so the corresponding combination of the sink coordinates
vanishes. -/
theorem sinkSum_eq_zero_of_isSource (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w)
    {mu : CoreEdge d G} (hmu : Γ.IsSource mu.1.1 mu.1.2) :
    Γ.sinkSum p w mu = 0 := by
  classical
  have hd : 0 < d := Γ.pos_of_into hmu.2.1
  have h1 := Γ.entersAt_fst_of_isSource hmu
  have h2 := Γ.entersAt_snd_of_isSource hmu
  have hnotsink : ¬ Γ.IsSink mu.1.1 mu.1.2 := Γ.not_isSink_of_entersAt h1
  rw [Γ.sinkSum_step p w hnotsink, Γ.allSucc_eq_union_of_isSource hmu,
    Finset.sum_union (Γ.disjoint_succAt_of_isSource hmu)]
  have hrepl : ∀ (a : V), Γ.EntersAt mu a → ∀ eta ∈ Γ.succAt a,
      Γ.fracEval p mu eta * Γ.sinkSum p w eta
        = Γ.fracEval p mu eta * w (coreToEdge eta) := by
    intro a haa eta hmem
    have harr : Γ.LArrow mu eta := ((Γ.mem_succAt_iff_lArrow haa.1 haa.2).1 hmem).1
    rw [← Γ.selfStress_eq_sinkSum_of_lArrow p hp w hw harr]
  rw [Finset.sum_congr rfl (hrepl mu.1.1 h1), Finset.sum_congr rfl (hrepl mu.1.2 h2)]
  have hpos := Γ.cramer_line_step_div_signed hd p hp w hw h1.1 h1.2
  have hneg := Γ.cramer_line_step_div_signed hd p hp w hw h2.1 h2.2
  rw [if_neg (by rintro ⟨-, hc⟩; exact absurd hc (ne_of_lt mu.2.1)), one_mul] at hpos
  rw [if_pos ⟨hmu, rfl⟩] at hneg
  rw [← hpos, ← hneg]
  ring

/-- A stream enters at exactly one of its endpoints. -/
theorem exists_entersAt_of_isStream {xi : CoreEdge d G} (h : Γ.IsStream xi.1.1 xi.1.2) :
    ∃ a : V, Γ.EntersAt xi a := by
  rcases h.2 with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact ⟨xi.1.1, Or.inl rfl, by rw [otherEnd, if_pos rfl]; exact h1⟩
  · exact ⟨xi.1.2, Or.inr rfl, by rw [otherEnd, if_neg (ne_of_gt xi.2.1)]; exact h2⟩

/-- A stream is not a source. -/
theorem not_isSource_of_isStream {xi : CoreEdge d G} (h : Γ.IsStream xi.1.1 xi.1.2) :
    ¬ Γ.IsSource xi.1.1 xi.1.2 := by
  rintro ⟨-, hs1, hs2⟩
  rcases h.2 with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2 hs2
  · exact h1 hs1

end DOrientation

end RigidityTableaux
