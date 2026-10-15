import RequestProject.SinkSystem

/-!
# Splitting a path of the line graph at a node

This file prepares the exchange of tails used in the proof of the Lindström–Gessel–Viennot
lemma quoted by the source article (`main.tex`, Section "Proofs", proof of Lemma
`lemma:balanced-equivalent-nonzero-solution`).

It contains:

* the elementary list operations `List.before` and `List.after`, which split a list at the
  first occurrence of an element;
* the *rank* `nodeRank` of a node of the line graph, which strictly increases along the
  arrows of `𝓛`, so that a node occurring before another one on a directed path can never
  occur after it on a directed path (this is the acyclicity of `𝓛`);
* the splicing of two directed paths at a common node, and the behaviour of the products
  `∏ frac(𝔞)|_p` under splicing.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

/-! ### Splitting a list at the first occurrence of an element -/

namespace ListSplit

variable {α : Type*} [DecidableEq α]

/-- The elements of a list strictly before the first occurrence of `v`. -/
def before (v : α) : List α → List α
  | [] => []
  | a :: t => if a = v then [] else a :: before v t

/-- The elements of a list strictly after the first occurrence of `v`. -/
def after (v : α) : List α → List α
  | [] => []
  | a :: t => if a = v then t else after v t

@[simp] theorem before_nil (v : α) : before v ([] : List α) = [] := rfl

@[simp] theorem after_nil (v : α) : after v ([] : List α) = [] := rfl

theorem before_cons (v a : α) (t : List α) :
    before v (a :: t) = if a = v then [] else a :: before v t := rfl

theorem after_cons (v a : α) (t : List α) :
    after v (a :: t) = if a = v then t else after v t := rfl

theorem not_mem_before (v : α) (L : List α) : v ∉ before v L := by
  induction L with
  | nil => simp
  | cons a t ih =>
      rw [before_cons]
      by_cases h : a = v
      · simp [h]
      · simp only [if_neg h, List.mem_cons, not_or]
        exact ⟨fun hcon => h hcon.symm, ih⟩

theorem before_append_after {v : α} {L : List α} (h : v ∈ L) :
    before v L ++ v :: after v L = L := by
  induction L with
  | nil => simp at h
  | cons a t ih =>
      rw [before_cons, after_cons]
      by_cases hav : a = v
      · simp [hav]
      · rcases List.mem_cons.1 h with h1 | h1
        · exact absurd h1.symm hav
        · simp only [if_neg hav, List.cons_append]
          rw [ih h1]

theorem before_of_append_cons {v : α} {X Y : List α} (h : v ∉ X) :
    before v (X ++ v :: Y) = X := by
  induction X with
  | nil => simp [before_cons]
  | cons a t ih =>
      have ha : a ≠ v := fun hcon => h (by simp [hcon])
      have ht : v ∉ t := fun hcon => h (by simp [hcon])
      simp only [List.cons_append, before_cons, if_neg ha]
      rw [ih ht]

theorem after_of_append_cons {v : α} {X Y : List α} (h : v ∉ X) :
    after v (X ++ v :: Y) = Y := by
  induction X with
  | nil => simp [after_cons]
  | cons a t ih =>
      have ha : a ≠ v := fun hcon => h (by simp [hcon])
      have ht : v ∉ t := fun hcon => h (by simp [hcon])
      simp only [List.cons_append, after_cons, if_neg ha]
      rw [ih ht]

theorem mem_iff_of_mem {v x : α} {L : List α} (h : v ∈ L) :
    x ∈ L ↔ x ∈ before v L ∨ x = v ∨ x ∈ after v L := by
  conv_lhs => rw [← before_append_after h]
  simp [List.mem_append]

end ListSplit

open ListSplit

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace DOrientation

variable (Γ : DOrientation d G)

/-! ### The rank of a node of the line graph -/

/-- The finite set of candidate ranks of a node of the line graph: the ranks of the
vertices at which the node enters, together with a value larger than all vertex ranks. -/
noncomputable def rankCandidates (xi : CoreEdge d G) : Finset ℕ :=
  insert ((univ.sup Γ.rank) + 1) ((univ.filter (fun a => Γ.EntersAt xi a)).image Γ.rank)

omit [DecidableRel G.Adj] in
theorem rankCandidates_nonempty (xi : CoreEdge d G) : (Γ.rankCandidates xi).Nonempty :=
  ⟨_, Finset.mem_insert_self _ _⟩

/-- The **rank of a node** of the line graph: the smallest rank of a vertex at which the
node enters, and a value larger than all vertex ranks for a sink. It increases strictly
along the arrows of `𝓛`, which is the acyclicity of `𝓛` used in the source article. -/
noncomputable def nodeRank (xi : CoreEdge d G) : ℕ :=
  (Γ.rankCandidates xi).min' (Γ.rankCandidates_nonempty xi)

theorem nodeRank_le_of_entersAt {xi : CoreEdge d G} {a : V} (h : Γ.EntersAt xi a) :
    Γ.nodeRank xi ≤ Γ.rank a := by
  refine Finset.min'_le _ _ ?_
  rw [rankCandidates]
  refine Finset.mem_insert_of_mem ?_
  exact Finset.mem_image.2 ⟨a, by simp only [mem_filter, mem_univ, true_and]; exact h, rfl⟩

/-- **The rank of a node increases strictly along the arrows of the line graph.** -/
theorem nodeRank_lt_of_lArrow {xi eta : CoreEdge d G} (h : Γ.LArrow xi eta) :
    Γ.nodeRank xi < Γ.nodeRank eta := by
  refine lt_of_le_of_lt (Γ.nodeRank_le_of_entersAt (Γ.entersAt_sharedVertex_of_lArrow h)) ?_
  rw [nodeRank, Finset.lt_min'_iff]
  intro b hb
  rw [rankCandidates, Finset.mem_insert] at hb
  rcases hb with hb | hb
  · subst hb
    exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ _))
  · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hb
    simp only [mem_filter, mem_univ, true_and] at ha'
    exact Γ.rank_lt_of_lArrow h ha'

/-- Along a directed path the ranks of the nodes are strictly increasing. -/
theorem nodeRank_pairwise {L : List (CoreEdge d G)} (h : L.IsChain Γ.LArrow) :
    L.Pairwise (fun x y => Γ.nodeRank x < Γ.nodeRank y) := by
  haveI : Trans (fun x y : CoreEdge d G => Γ.nodeRank x < Γ.nodeRank y)
      (fun x y : CoreEdge d G => Γ.nodeRank x < Γ.nodeRank y)
      (fun x y : CoreEdge d G => Γ.nodeRank x < Γ.nodeRank y) :=
    ⟨fun h1 h2 => lt_trans h1 h2⟩
  exact List.IsChain.pairwise (h.imp (fun _ _ harr => Γ.nodeRank_lt_of_lArrow harr))

theorem nodeRank_lt_of_mem_before {L : List (CoreEdge d G)} (hchain : L.IsChain Γ.LArrow)
    {v x : CoreEdge d G} (hv : v ∈ L) (hx : x ∈ before v L) :
    Γ.nodeRank x < Γ.nodeRank v := by
  have hp := Γ.nodeRank_pairwise hchain
  rw [← before_append_after hv] at hp
  rw [List.pairwise_append] at hp
  exact hp.2.2 x hx v (by simp)

theorem nodeRank_lt_of_mem_after {L : List (CoreEdge d G)} (hchain : L.IsChain Γ.LArrow)
    {v x : CoreEdge d G} (hv : v ∈ L) (hx : x ∈ after v L) :
    Γ.nodeRank v < Γ.nodeRank x := by
  have hp := Γ.nodeRank_pairwise hchain
  rw [← before_append_after hv] at hp
  rw [List.pairwise_append] at hp
  have h2 := hp.2.1
  rw [List.pairwise_cons] at h2
  exact h2.1 x hx

/-! ### Splicing two directed paths at a common node -/

omit [DecidableRel G.Adj] in
theorem isChain_before {L : List (CoreEdge d G)} (hchain : L.IsChain Γ.LArrow)
    {v : CoreEdge d G} (hv : v ∈ L) : (before v L ++ [v]).IsChain Γ.LArrow := by
  have h : L = (before v L ++ [v]) ++ after v L := by
    rw [List.append_assoc]
    simpa using (before_append_after hv).symm
  rw [h, List.isChain_append] at hchain
  exact hchain.1

omit [DecidableRel G.Adj] in
theorem isChain_after {L : List (CoreEdge d G)} (hchain : L.IsChain Γ.LArrow)
    {v : CoreEdge d G} (hv : v ∈ L) : (v :: after v L).IsChain Γ.LArrow := by
  have h : L = before v L ++ (v :: after v L) := (before_append_after hv).symm
  rw [h, List.isChain_append] at hchain
  exact hchain.2.1

/-- Splicing the beginning of one directed path with the end of another at a common node
gives a directed path. -/
theorem isChain_splice {X Y : List (CoreEdge d G)} {v : CoreEdge d G}
    (hX : (X ++ [v]).IsChain Γ.LArrow) (hY : (v :: Y).IsChain Γ.LArrow) :
    (X ++ v :: Y).IsChain Γ.LArrow := by
  rw [List.isChain_append] at hX ⊢
  refine ⟨hX.1, hY, ?_⟩
  intro x hx z hz
  have hz' : z = v := by simpa using hz.symm
  subst hz'
  exact hX.2.2 x hx z (by simp)

/-! ### The fractions along a spliced path -/

omit [DecidableRel G.Adj] in
theorem pathFracEval_append_cons (p : V → Fin d → ℝ) (v : CoreEdge d G) :
    ∀ X Y : List (CoreEdge d G),
      Γ.pathFracEval p (X ++ v :: Y)
        = Γ.pathFracEval p (X ++ [v]) * Γ.pathFracEval p (v :: Y) := by
  intro X
  induction X with
  | nil => intro Y; simp [pathFracEval]
  | cons a X ih =>
      intro Y
      cases X with
      | nil =>
          simp only [List.nil_append, List.cons_append]
          rw [Γ.pathFracEval_cons p a v Y]
          have hav : Γ.pathFracEval p [a, v] = Γ.fracEval p a v := by
            simp [pathFracEval]
          rw [hav]
      | cons b X =>
          have ih' := ih Y
          simp only [List.cons_append] at ih' ⊢
          rw [Γ.pathFracEval_cons p a b (X ++ v :: Y), ih',
            Γ.pathFracEval_cons p a b (X ++ [v]), mul_assoc]

end DOrientation

end RigidityTableaux
