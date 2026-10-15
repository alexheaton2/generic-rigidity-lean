import RequestProject.LineGraphAcyclic

/-!
# Decomposing the path sums of the line graph

This file carries out the *"repeated substitution of variables, using
(\ref{eqn:cramers-rule-new}) at every node along paths starting at `(i,j)` and ending at
a sink"* of the proof of Lemma `lemma:stream-formula-new` in the source article
(`main.tex`, Section "Proofs").

The two combinatorial ingredients are:

* `DOrientation.sum_pathsFrom_of_isSink`: at a sink the only path is the trivial one, so
  the path sum reduces to `1`;
* `DOrientation.sum_pathsFrom_cons`: every path leaving a non-source node `ξ` starts with
  an arrow `ξ → η`, and conversely; this yields
  `∑_{𝒫 : ξ → ν} ∏ frac = ∑_η frac(ξ → η) · ∑_{𝒫 : η → ν} ∏ frac`.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace DOrientation

variable (Γ : DOrientation d G)

/-- A node which is not a source enters at at most one vertex: a stream is oriented into
exactly one of its endpoints (`main.tex`, Subsection "Main Results"). -/
theorem entersAt_unique {xi : CoreEdge d G} (hns : ¬ Γ.IsSource xi.1.1 xi.1.2) {a a' : V}
    (h : Γ.EntersAt xi a) (h' : Γ.EntersAt xi a') : a = a' := by
  have hlt := xi.2.1
  rcases h.1 with ha | ha <;> rcases h'.1 with ha' | ha'
  · rw [ha, ha']
  · exfalso
    have h1 : Γ.into xi.1.1 xi.1.2 := by
      have h2 := h.2
      rw [otherEnd, if_pos ha] at h2
      rwa [ha] at h2
    have h2 : Γ.into xi.1.2 xi.1.1 := by
      have h3 := h'.2
      rw [otherEnd, if_neg (by rw [ha']; exact ne_of_gt hlt)] at h3
      rwa [ha'] at h3
    exact hns ⟨xi.2.2, h1, h2⟩
  · exfalso
    have h1 : Γ.into xi.1.1 xi.1.2 := by
      have h2 := h'.2
      rw [otherEnd, if_pos ha'] at h2
      rwa [ha'] at h2
    have h2 : Γ.into xi.1.2 xi.1.1 := by
      have h3 := h.2
      rw [otherEnd, if_neg (by rw [ha]; exact ne_of_gt hlt)] at h3
      rwa [ha] at h3
    exact hns ⟨xi.2.2, h1, h2⟩
  · rw [ha, ha']

/-- A node that enters somewhere is not a sink. -/
theorem not_isSink_of_entersAt {xi : CoreEdge d G} {a : V} (h : Γ.EntersAt xi a) :
    ¬ Γ.IsSink xi.1.1 xi.1.2 := by
  intro hsink
  rcases h.1 with ha | ha
  · refine hsink.2.1 ?_
    have h2 := h.2
    rw [otherEnd, if_pos ha] at h2
    rwa [ha] at h2
  · refine hsink.2.2 ?_
    have h2 := h.2
    rw [otherEnd, if_neg (by rw [ha]; exact ne_of_gt xi.2.1)] at h2
    rwa [ha] at h2

/-- A node that is not a sink enters at one of its endpoints. -/
theorem exists_entersAt_of_not_isSink {xi : CoreEdge d G} (h : ¬ Γ.IsSink xi.1.1 xi.1.2) :
    ∃ a : V, Γ.EntersAt xi a := by
  by_cases h1 : Γ.into xi.1.1 xi.1.2
  · exact ⟨xi.1.1, Or.inl rfl, by rw [otherEnd, if_pos rfl]; exact h1⟩
  · by_cases h2 : Γ.into xi.1.2 xi.1.1
    · refine ⟨xi.1.2, Or.inr rfl, ?_⟩
      rw [otherEnd, if_neg (ne_of_gt xi.2.1)]
      exact h2
    · exact absurd ⟨xi.2.2, h1, h2⟩ h

/-- A sink has no outgoing arrow in the line graph. -/
theorem not_lArrow_of_isSink {xi eta : CoreEdge d G} (h : Γ.IsSink xi.1.1 xi.1.2) :
    ¬ Γ.LArrow xi eta := fun harr =>
  Γ.not_isSink_of_entersAt (Γ.entersAt_sharedVertex_of_lArrow harr) h

/-- The only path of the line graph leaving a sink is the trivial one. -/
theorem isLPath_of_isSink {nu0 nu : CoreEdge d G} (h : Γ.IsSink nu0.1.1 nu0.1.2)
    {L : List (CoreEdge d G)} (hL : Γ.IsLPath nu0 nu L) : L = [nu0] ∧ nu = nu0 := by
  obtain ⟨hhead, hlast, hchain⟩ := hL
  cases L with
  | nil => exact absurd hhead (by simp)
  | cons hd tl =>
    have hhd : hd = nu0 := by simpa using hhead
    subst hhd
    cases tl with
    | nil => exact ⟨rfl, by simpa using hlast.symm⟩
    | cons hd' tl' =>
      exact absurd (List.isChain_cons_cons.1 hchain).1 (Γ.not_lArrow_of_isSink h)

/-- **The path sum at a sink**: the only path leaving a sink `ν₀` is the trivial path, so
the inner sum of the stream formula of the source article is `1` at `ν₀` and `0`
elsewhere. -/
theorem sum_pathsFrom_of_isSink (p : V → Fin d → ℝ) {nu0 nu : CoreEdge d G}
    (h : Γ.IsSink nu0.1.1 nu0.1.2) :
    (∑ L ∈ Γ.pathsFrom nu0 nu, Γ.pathFracEval p L) = if nu = nu0 then 1 else 0 := by
  classical
  by_cases hnu : nu = nu0
  · subst hnu
    rw [if_pos rfl]
    have hset : Γ.pathsFrom nu nu = {[nu]} := by
      ext L
      rw [Γ.mem_pathsFrom, Finset.mem_singleton]
      constructor
      · intro hL
        exact (Γ.isLPath_of_isSink h hL.2).1
      · intro hL
        subst hL
        exact ⟨List.nodup_singleton _, rfl, rfl, List.IsChain.singleton _⟩
    rw [hset, Finset.sum_singleton]
    simp [pathFracEval]
  · rw [if_neg hnu]
    have hset : Γ.pathsFrom nu0 nu = ∅ := by
      ext L
      rw [Γ.mem_pathsFrom]
      simp only [Finset.notMem_empty, iff_false, not_and]
      intro _ hL
      exact hnu (Γ.isLPath_of_isSink h hL).2
    rw [hset, Finset.sum_empty]

omit [DecidableRel G.Adj] in
/-- The fraction of a path splits off its first arrow. -/
theorem pathFracEval_cons (p : V → Fin d → ℝ) (xi eta : CoreEdge d G)
    (t : List (CoreEdge d G)) :
    Γ.pathFracEval p (xi :: eta :: t) = Γ.fracEval p xi eta * Γ.pathFracEval p (eta :: t) := by
  simp [pathFracEval]

/-- The set of all nodes reached from `ξ` by an arrow of the line graph. -/
noncomputable def allSucc (xi : CoreEdge d G) : Finset (CoreEdge d G) :=
  univ.filter (fun eta => Γ.LArrow xi eta)

theorem mem_allSucc {xi eta : CoreEdge d G} : eta ∈ Γ.allSucc xi ↔ Γ.LArrow xi eta := by
  simp [allSucc]

/-- For a node which is not a source, the arrows leaving it all use the single vertex at
which it enters. -/
theorem allSucc_eq_succAt {xi : CoreEdge d G} {a : V} (hxi : Γ.EntersAt xi a)
    (hns : ¬ Γ.IsSource xi.1.1 xi.1.2) : Γ.allSucc xi = Γ.succAt a := by
  ext eta
  rw [Γ.mem_allSucc, Γ.mem_succAt_iff_lArrow hxi.1 hxi.2]
  constructor
  · intro harr
    exact ⟨harr, Γ.entersAt_unique hns (Γ.entersAt_sharedVertex_of_lArrow harr) hxi⟩
  · exact fun h => h.1

/-- **Every path leaving a node starts with an arrow, and conversely.** For a node `ξ`
distinct from `ν`, the paths from `ξ` to `ν` are exactly the lists `ξ :: 𝒫` with `𝒫` a
path from a node `η` reached from `ξ` by an arrow to `ν`. -/
theorem pathsFrom_eq_biUnion {xi nu : CoreEdge d G} (hne : xi ≠ nu) :
    Γ.pathsFrom xi nu
      = (Γ.allSucc xi).biUnion (fun eta => (Γ.pathsFrom eta nu).image (fun L => xi :: L)) := by
  classical
  ext L
  rw [Γ.mem_pathsFrom, Finset.mem_biUnion]
  constructor
  · rintro ⟨hnd, hhead, hlast, hchain⟩
    cases L with
    | nil => exact absurd hhead (by simp)
    | cons hd tl =>
      have hhd : hd = xi := by simpa using hhead
      subst hhd
      cases tl with
      | nil => exact absurd (by simpa using hlast : hd = nu) hne
      | cons hd' tl' =>
        obtain ⟨harr, hchain'⟩ := List.isChain_cons_cons.1 hchain
        refine ⟨hd', Γ.mem_allSucc.2 harr, ?_⟩
        refine Finset.mem_image.2 ⟨hd' :: tl', ?_, rfl⟩
        refine Γ.mem_pathsFrom.2 ⟨(List.nodup_cons.1 hnd).2, rfl, ?_, hchain'⟩
        rw [List.getLast?_cons_cons] at hlast
        exact hlast
  · rintro ⟨eta, heta, hL⟩
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 hL
    obtain ⟨hnd', hhead', hlast', hchain'⟩ := Γ.mem_pathsFrom.1 hL'
    have harr : Γ.LArrow xi eta := Γ.mem_allSucc.1 heta
    cases L' with
    | nil => exact absurd hhead' (by simp)
    | cons hd t =>
      have hhd : hd = eta := by simpa using hhead'
      subst hhd
      have hchain : (xi :: hd :: t).IsChain Γ.LArrow :=
        List.isChain_cons_cons.2 ⟨harr, hchain'⟩
      refine ⟨Γ.nodup_of_isChain _ hchain, rfl, ?_, hchain⟩
      rw [List.getLast?_cons_cons]
      exact hlast'

/-- The computational heart of the decomposition of the path sums: summing the fractions
over all paths obtained by prefixing `ξ` to the paths leaving the nodes of a finite set
`S`. -/
theorem sum_biUnion_cons (p : V → Fin d → ℝ) (xi nu : CoreEdge d G)
    (S : Finset (CoreEdge d G)) :
    (∑ L ∈ S.biUnion (fun eta => (Γ.pathsFrom eta nu).image (fun L => xi :: L)),
        Γ.pathFracEval p L)
      = ∑ eta ∈ S, Γ.fracEval p xi eta *
          ∑ L ∈ Γ.pathsFrom eta nu, Γ.pathFracEval p L := by
  classical
  have hdisj : (↑S : Set (CoreEdge d G)).PairwiseDisjoint
      (fun eta => (Γ.pathsFrom eta nu).image (fun L => xi :: L)) := by
    intro e1 _ e2 _ hne2
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro L h1 h2
    obtain ⟨L1, hL1, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨L2, hL2, heq⟩ := Finset.mem_image.1 h2
    have hL12 : L2 = L1 := by simpa using heq
    subst hL12
    have hh1 := (Γ.mem_pathsFrom.1 hL1).2.1
    have hh2 := (Γ.mem_pathsFrom.1 hL2).2.1
    exact hne2 (by rw [hh1] at hh2; exact Option.some_inj.1 hh2)
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl (fun eta _ => ?_)
  rw [Finset.sum_image (fun x _ y _ h => by simpa using h), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun L hL => ?_)
  obtain ⟨-, hhead, -, -⟩ := Γ.mem_pathsFrom.1 hL
  cases L with
  | nil => exact absurd hhead (by simp)
  | cons hd t =>
    have hhd : hd = eta := by simpa using hhead
    subst hhd
    exact Γ.pathFracEval_cons p xi hd t

/-- **The one-step decomposition of the path sums** (`main.tex`, Section "Proofs"):
`∑_{𝒫 : ξ → ν} ∏_{𝔞 ∈ 𝒫} frac(𝔞)|_p = ∑_η frac(ξ → η)|_p · ∑_{𝒫 : η → ν} ∏ frac(𝔞)|_p`,
the outer sum running over the nodes `η` reached from `ξ` by an arrow. -/
theorem sum_pathsFrom_cons (p : V → Fin d → ℝ) {xi nu : CoreEdge d G} (hne : xi ≠ nu) :
    (∑ L ∈ Γ.pathsFrom xi nu, Γ.pathFracEval p L)
      = ∑ eta ∈ Γ.allSucc xi, Γ.fracEval p xi eta *
          ∑ L ∈ Γ.pathsFrom eta nu, Γ.pathFracEval p L := by
  rw [Γ.pathsFrom_eq_biUnion hne, Γ.sum_biUnion_cons p xi nu]

theorem mem_pathsFromPos {mu nu : CoreEdge d G} {L : List (CoreEdge d G)} :
    L ∈ Γ.pathsFromPos mu nu ↔ L.Nodup ∧ Γ.IsLPath mu nu L ∧
      ∀ eta ∈ L.tail.head?, sharedVertex mu eta = mu.1.1 := by
  simp [pathsFromPos, mem_nodupLists, and_assoc]

/-- **The paths leaving a source at its positive endpoint** are exactly the lists `μ :: 𝒫`
with `𝒫` a path leaving a node reached from `μ` by an arrow using the smaller endpoint of
`μ` (`main.tex`, Section "Proofs"). -/
theorem pathsFromPos_eq_biUnion {mu nu : CoreEdge d G}
    (hmu : Γ.IsSource mu.1.1 mu.1.2) (hne : mu ≠ nu) :
    Γ.pathsFromPos mu nu
      = (Γ.succAt mu.1.1).biUnion
          (fun eta => (Γ.pathsFrom eta nu).image (fun L => mu :: L)) := by
  classical
  have h1 : Γ.EntersAt mu mu.1.1 :=
    ⟨Or.inl rfl, by rw [otherEnd, if_pos rfl]; exact hmu.2.1⟩
  ext L
  rw [Γ.mem_pathsFromPos, Finset.mem_biUnion]
  constructor
  · rintro ⟨hnd, ⟨hhead, hlast, hchain⟩, hpos⟩
    cases L with
    | nil => exact absurd hhead (by simp)
    | cons hd tl =>
      have hhd : hd = mu := by simpa using hhead
      subst hhd
      cases tl with
      | nil => exact absurd (by simpa using hlast : hd = nu) hne
      | cons hd' tl' =>
        obtain ⟨harr, hchain'⟩ := List.isChain_cons_cons.1 hchain
        have hsv : sharedVertex hd hd' = hd.1.1 := hpos hd' rfl
        refine ⟨hd', (Γ.mem_succAt_iff_lArrow h1.1 h1.2).2 ⟨harr, hsv⟩, ?_⟩
        refine Finset.mem_image.2 ⟨hd' :: tl', ?_, rfl⟩
        refine Γ.mem_pathsFrom.2 ⟨(List.nodup_cons.1 hnd).2, rfl, ?_, hchain'⟩
        rw [List.getLast?_cons_cons] at hlast
        exact hlast
  · rintro ⟨eta, heta, hL⟩
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 hL
    obtain ⟨hnd', hhead', hlast', hchain'⟩ := Γ.mem_pathsFrom.1 hL'
    obtain ⟨harr, hsv⟩ := (Γ.mem_succAt_iff_lArrow h1.1 h1.2).1 heta
    cases L' with
    | nil => exact absurd hhead' (by simp)
    | cons hd t =>
      have hhd : hd = eta := by simpa using hhead'
      subst hhd
      have hchain : (mu :: hd :: t).IsChain Γ.LArrow :=
        List.isChain_cons_cons.2 ⟨harr, hchain'⟩
      refine ⟨Γ.nodup_of_isChain _ hchain, ⟨rfl, ?_, hchain⟩, ?_⟩
      · rw [List.getLast?_cons_cons]
        exact hlast'
      · intro zeta hzeta
        have hz : zeta = hd := by simpa using hzeta.symm
        subst hz
        exact hsv

/-- The decomposition of the path sums for a source, using only the paths leaving it at
its positive endpoint. -/
theorem sum_pathsFromPos_cons (p : V → Fin d → ℝ) {mu nu : CoreEdge d G}
    (hmu : Γ.IsSource mu.1.1 mu.1.2) (hne : mu ≠ nu) :
    (∑ L ∈ Γ.pathsFromPos mu nu, Γ.pathFracEval p L)
      = ∑ eta ∈ Γ.succAt mu.1.1, Γ.fracEval p mu eta *
          ∑ L ∈ Γ.pathsFrom eta nu, Γ.pathFracEval p L := by
  rw [Γ.pathsFromPos_eq_biUnion hmu hne, Γ.sum_biUnion_cons p mu nu]

end DOrientation

end RigidityTableaux
