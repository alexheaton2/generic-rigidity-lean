import RequestProject.StreamFormula

/-!
# The `Γ`-oriented line graph is acyclic

The source article asserts, and uses throughout, that the `Γ`-oriented line graph `𝓛` has
no directed cycles (`main.tex`, Section "Proofs": *"Since `𝓛` is finite and acyclic, every
maximal directed path beginning at a source or stream terminates at a sink"*). This file
derives that statement from the rank function carried by a `d`-orientation.

The key observation is `DOrientation.rank_lt_of_lArrow`: if `ξ → η` is an arrow using the
vertex `a`, and `η` is itself oriented into an endpoint `a'`, then `rank a < rank a'`.
Consequently the vertices used by the successive arrows of a directed path have strictly
increasing rank (`DOrientation.rank_lt_of_mem_of_lArrow`), so no directed path repeats a
node (`DOrientation.nodup_of_isChain`).
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace DOrientation

variable (Γ : DOrientation d G)

/-- A node `η` of the line graph **enters at** the vertex `a` when `a` is an endpoint of
`η` and the edge `η` is oriented into `a`. The arrows of `𝓛` leaving `η` are exactly those
using a vertex at which `η` enters. -/
def EntersAt (eta : CoreEdge d G) (a : V) : Prop :=
  (a = eta.1.1 ∨ a = eta.1.2) ∧ Γ.into a (otherEnd eta a)

/-- The shared vertex of an arrow is an endpoint of its source. -/
theorem sharedVertex_mem (xi eta : CoreEdge d G) :
    sharedVertex xi eta = xi.1.1 ∨ sharedVertex xi eta = xi.1.2 := by
  rw [sharedVertex]
  split <;> simp

/-- The endpoint of a node other than a given one, when both are endpoints. -/
theorem otherEnd_eq_of_ne {eta : CoreEdge d G} {a a' : V}
    (ha : a = eta.1.1 ∨ a = eta.1.2) (ha' : a' = eta.1.1 ∨ a' = eta.1.2) (hne : a ≠ a') :
    otherEnd eta a = a' := by
  have hlt := eta.2.1
  rcases ha with h | h
  · rw [otherEnd, if_pos h]
    rcases ha' with h' | h'
    · exact absurd (h.trans h'.symm) hne
    · exact h'.symm
  · have hna : a ≠ eta.1.1 := by rw [h]; exact ne_of_gt hlt
    rw [otherEnd, if_neg hna]
    rcases ha' with h' | h'
    · exact h'.symm
    · exact absurd (h.trans h'.symm) hne

/-- The source of an arrow enters at the vertex the arrow uses. -/
theorem entersAt_sharedVertex_of_lArrow {xi eta : CoreEdge d G} (h : Γ.LArrow xi eta) :
    Γ.EntersAt xi (sharedVertex xi eta) :=
  ⟨sharedVertex_mem xi eta, h.2.2.1⟩

/-- The target of an arrow is never a source: a source is oriented into both its
endpoints, whereas the target of an arrow is oriented out of the vertex the arrow uses
(`main.tex`, Subsection "Main Results"). -/
theorem not_isSource_of_lArrow {xi eta : CoreEdge d G} (h : Γ.LArrow xi eta) :
    ¬ Γ.IsSource eta.1.1 eta.1.2 := by
  intro hsrc
  have hend := h.2.1
  have hout := h.2.2.2
  rcases hend with he | he
  · rw [otherEnd, if_pos he] at hout
    exact hout (by rw [he]; exact hsrc.2.1)
  · have hne : sharedVertex xi eta ≠ eta.1.1 := by
      rw [he]; exact ne_of_gt eta.2.1
    rw [otherEnd, if_neg hne] at hout
    exact hout (by rw [he]; exact hsrc.2.2)

/-- **The rank increases along the arrows of the line graph.** If `ξ → η` is an arrow of
`𝓛` using the vertex `a` and `η` enters at `a'`, then `rank a < rank a'`. This is the
precise form of the acyclicity of `𝓛` asserted in the source article. -/
theorem rank_lt_of_lArrow {xi eta : CoreEdge d G} (h : Γ.LArrow xi eta) {a' : V}
    (h' : Γ.EntersAt eta a') : Γ.rank (sharedVertex xi eta) < Γ.rank a' := by
  set a := sharedVertex xi eta with hadef
  have hend : a = eta.1.1 ∨ a = eta.1.2 := h.2.1
  have hout : ¬ Γ.into a (otherEnd eta a) := h.2.2.2
  have hne : a ≠ a' := by
    intro hcon
    rw [hcon] at hout
    exact hout h'.2
  have h1 : otherEnd eta a = a' := otherEnd_eq_of_ne hend h'.1 hne
  have h2 : otherEnd eta a' = a := otherEnd_eq_of_ne h'.1 hend (Ne.symm hne)
  rw [h1] at hout
  have hin : Γ.into a' a := by rw [← h2]; exact h'.2
  have hnd : nonDesert d G a a' := by
    rcases hend with he | he
    · rcases h'.1 with he' | he'
      · exact absurd (he.trans he'.symm) hne
      · rw [he, he']; exact eta.2.2
    · rcases h'.1 with he' | he'
      · rw [he, he']; exact (isDeep_nonDesert d G).1 _ _ eta.2.2
      · exact absurd (he.trans he'.symm) hne
  exact Γ.rank_lt a a' hnd hin hout

/-- **The rank strictly increases along a directed path.** If `L` is a directed path whose
first node `h` is reached by an arrow from `ξ`, then every node of `L` enters only at
vertices of rank strictly larger than the vertex used by the arrow `ξ → h`. -/
theorem rank_lt_of_mem_of_lArrow :
    ∀ (L : List (CoreEdge d G)), L.IsChain Γ.LArrow →
      ∀ xi h : CoreEdge d G, L.head? = some h → Γ.LArrow xi h →
        ∀ zeta ∈ L, ∀ a' : V, Γ.EntersAt zeta a' →
          Γ.rank (sharedVertex xi h) < Γ.rank a' := by
  intro L
  induction L with
  | nil => intro _ _ _ hhead; exact absurd hhead (by simp)
  | cons hd tl ih =>
    intro hchain xi h hhead harr zeta hzeta a' hentry
    have hh : hd = h := by simpa using hhead
    subst hh
    rcases List.mem_cons.1 hzeta with hz | hz
    · subst hz
      exact Γ.rank_lt_of_lArrow harr hentry
    · cases tl with
      | nil => exact absurd hz (by simp)
      | cons hd' tl' =>
        obtain ⟨harr', hchain'⟩ := List.isChain_cons_cons.1 hchain
        have hfirst : Γ.rank (sharedVertex xi hd) < Γ.rank (sharedVertex hd hd') :=
          Γ.rank_lt_of_lArrow harr (Γ.entersAt_sharedVertex_of_lArrow harr')
        exact lt_trans hfirst
          (ih hchain' hd hd' rfl harr' zeta hz a' hentry)

/-- **The `Γ`-oriented line graph is acyclic**: no directed path of `𝓛` repeats a node
(`main.tex`, Section "Proofs": *"Since `𝓛` is finite and acyclic …"*). -/
theorem nodup_of_isChain : ∀ (L : List (CoreEdge d G)), L.IsChain Γ.LArrow → L.Nodup := by
  intro L
  induction L with
  | nil => intro _; exact List.nodup_nil
  | cons hd tl ih =>
    intro hchain
    have htl : tl.IsChain Γ.LArrow := by
      cases tl with
      | nil => exact List.IsChain.nil
      | cons hd' tl' => exact (List.isChain_cons_cons.1 hchain).2
    refine List.nodup_cons.2 ⟨?_, ih htl⟩
    intro hmem
    cases tl with
    | nil => exact absurd hmem (by simp)
    | cons hd' tl' =>
      obtain ⟨harr', -⟩ := List.isChain_cons_cons.1 hchain
      have := Γ.rank_lt_of_mem_of_lArrow (hd' :: tl') htl hd hd' rfl harr' hd hmem
        (sharedVertex hd hd') (Γ.entersAt_sharedVertex_of_lArrow harr')
      exact lt_irrefl _ this

/-- Every directed path of `𝓛` is a path in the sense of `IsLPath`: a list of nodes with
no repetitions. -/
theorem isLPath_nodup {mu nu : CoreEdge d G} {L : List (CoreEdge d G)}
    (h : Γ.IsLPath mu nu L) : L.Nodup :=
  Γ.nodup_of_isChain L h.2.2

end DOrientation

end RigidityTableaux
