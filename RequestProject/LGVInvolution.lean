import RequestProject.PathSplice

/-!
# The sign-reversing involution of the Lindström–Gessel–Viennot lemma

The source article invokes the Lindström–Gessel–Viennot lemma in the proof of Lemma
`lemma:balanced-equivalent-nonzero-solution` (`main.tex`, Section "Proofs"):

> Let `𝒟` be the set of disjoint path systems for `μ_1, …, μ_ℓ`. By the
> Lindström–Gessel–Viennot lemma, `det Q_{ij}` is equal to `∑_{𝒫 ∈ 𝒟} frac(𝒫)|_p`.

Its proof is a cancellation: the path systems which are *not* disjoint come in pairs of
opposite sign. This file constructs the pairing. Given a path system whose paths are not
pairwise disjoint, one chooses a node `v` lying on at least two of the paths, the two
smallest indices `j₀ < j₁` of paths through `v`, and exchanges the two tails of these
paths after `v`. This changes the permutation of the system by the transposition
`(j₀ j₁)`, hence reverses its sign, while preserving the product of the fractions
`frac(𝔞)|_p`; and doing it twice returns the original system.

The exchange is well behaved because the `Γ`-oriented line graph is acyclic: a node lying
before `v` on one path can never lie after `v` on another path.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

open ListSplit

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Two elementary list lemmas -/

theorem head?_append_cons {α : Type*} (X : List α) (v : α) (Y : List α) :
    (X ++ v :: Y).head? = (X ++ [v]).head? := by
  cases X <;> simp

theorem min'_congr_finset {α : Type*} [LinearOrder α] {s t : Finset α} (hst : s = t)
    (hs : s.Nonempty) (ht : t.Nonempty) : s.min' hs = t.min' ht := by
  subst hst
  rfl

/-! ### Shared nodes of a path system -/

namespace DOrientation

/-- The nodes lying on at least two of the paths of a path system: the path system is
disjoint exactly when there are none. -/
noncomputable def sharedNodes {l : ℕ} (P : PathSystemData d G l) : Finset (CoreEdge d G) :=
  univ.filter (fun x => ∃ j j' : Fin l, j ≠ j' ∧ x ∈ (P.2 j).1 ∧ x ∈ (P.2 j').1)

theorem mem_sharedNodes {l : ℕ} {P : PathSystemData d G l} {x : CoreEdge d G} :
    x ∈ sharedNodes P ↔ ∃ j j' : Fin l, j ≠ j' ∧ x ∈ (P.2 j).1 ∧ x ∈ (P.2 j').1 := by
  simp [sharedNodes]

/-- The indices of the paths of a path system passing through a given node. -/
noncomputable def idxSet {l : ℕ} (P : PathSystemData d G l) (v : CoreEdge d G) :
    Finset (Fin l) :=
  univ.filter (fun j => v ∈ (P.2 j).1)

theorem mem_idxSet {l : ℕ} {P : PathSystemData d G l} {v : CoreEdge d G} {j : Fin l} :
    j ∈ idxSet P v ↔ v ∈ (P.2 j).1 := by
  simp [idxSet]

/-! ### Exchanging the tails of two paths at a common node -/

/-- Repackaging a list as a duplicate-free list, keeping a fallback value if it has
repetitions. -/
noncomputable def nodupPack (L : List (CoreEdge d G))
    (fallback : {L : List (CoreEdge d G) // L.Nodup}) : {L : List (CoreEdge d G) // L.Nodup} :=
  if h : L.Nodup then ⟨L, h⟩ else fallback

theorem nodupPack_of_nodup {L : List (CoreEdge d G)}
    {fallback : {L : List (CoreEdge d G) // L.Nodup}} (h : L.Nodup) :
    (nodupPack L fallback).1 = L := by
  rw [nodupPack, dif_pos h]

/-- **The exchange of tails**: the path system obtained by exchanging the parts of the
paths `j₀` and `j₁` lying after their common node `v`, and composing the permutation with
the transposition `(j₀ j₁)`. -/
noncomputable def swapAt {l : ℕ} (P : PathSystemData d G l) (v : CoreEdge d G) (j0 j1 : Fin l) :
    PathSystemData d G l :=
  (P.1 * Equiv.swap j0 j1,
    fun j =>
      if j = j0 then nodupPack (before v (P.2 j0).1 ++ v :: after v (P.2 j1).1) (P.2 j0)
      else if j = j1 then nodupPack (before v (P.2 j1).1 ++ v :: after v (P.2 j0).1) (P.2 j1)
      else P.2 j)

variable (Γ : DOrientation d G)

/-- The data of a path system together with a node lying on two of its paths, at which the
tails will be exchanged. -/
structure CrossData {l : ℕ} (mu nu : Fin l → CoreEdge d G) (P : PathSystemData d G l)
    (v : CoreEdge d G) (j0 j1 : Fin l) : Prop where
  /-- each path of the system is a directed path from its source to the matched sink -/
  isPath : ∀ j, Γ.IsLPath (mu j) (nu (P.1 j)) (P.2 j).1
  /-- the two exchanged indices are different -/
  ne : j0 ≠ j1
  /-- the node lies on the first path -/
  mem0 : v ∈ (P.2 j0).1
  /-- the node lies on the second path -/
  mem1 : v ∈ (P.2 j1).1

variable {l : ℕ} {mu nu : Fin l → CoreEdge d G} {P : PathSystemData d G l}
  {v : CoreEdge d G} {j0 j1 : Fin l}

theorem CrossData.chain0 (hc : Γ.CrossData mu nu P v j0 j1) :
    ((P.2 j0).1).IsChain Γ.LArrow := (hc.isPath j0).2.2

theorem CrossData.chain1 (hc : Γ.CrossData mu nu P v j0 j1) :
    ((P.2 j1).1).IsChain Γ.LArrow := (hc.isPath j1).2.2

theorem CrossData.nodup_new0 (hc : Γ.CrossData mu nu P v j0 j1) :
    (before v (P.2 j0).1 ++ v :: after v (P.2 j1).1).Nodup :=
  Γ.nodup_of_isChain _
    (Γ.isChain_splice (Γ.isChain_before hc.chain0 hc.mem0) (Γ.isChain_after hc.chain1 hc.mem1))

theorem CrossData.nodup_new1 (hc : Γ.CrossData mu nu P v j0 j1) :
    (before v (P.2 j1).1 ++ v :: after v (P.2 j0).1).Nodup :=
  Γ.nodup_of_isChain _
    (Γ.isChain_splice (Γ.isChain_before hc.chain1 hc.mem1) (Γ.isChain_after hc.chain0 hc.mem0))

theorem CrossData.swapAt_j0 (hc : Γ.CrossData mu nu P v j0 j1) :
    ((swapAt P v j0 j1).2 j0).1 = before v (P.2 j0).1 ++ v :: after v (P.2 j1).1 := by
  rw [swapAt]
  simp only [if_pos rfl]
  exact nodupPack_of_nodup hc.nodup_new0

theorem CrossData.swapAt_j1 (hc : Γ.CrossData mu nu P v j0 j1) :
    ((swapAt P v j0 j1).2 j1).1 = before v (P.2 j1).1 ++ v :: after v (P.2 j0).1 := by
  rw [swapAt]
  simp only [if_neg (Ne.symm hc.ne), if_pos rfl]
  exact nodupPack_of_nodup hc.nodup_new1

theorem swapAt_other {j : Fin l} (hj0 : j ≠ j0) (hj1 : j ≠ j1) :
    ((swapAt P v j0 j1).2 j) = P.2 j := by
  rw [swapAt]
  simp only [if_neg hj0, if_neg hj1]

theorem swapAt_perm (j : Fin l) : (swapAt P v j0 j1).1 j = P.1 (Equiv.swap j0 j1 j) := rfl

/-! ### The shared nodes and the indices through a node are unchanged -/

omit [DecidableRel G.Adj] in
/-- If two path systems agree away from two indices, and the union and the intersection of
the two exchanged paths are unchanged, then they have the same shared nodes. -/
theorem sharedNodes_subset_of_exchange {Q R : PathSystemData d G l} {a b : Fin l} (hab : a ≠ b)
    (hother : ∀ j, j ≠ a → j ≠ b → (Q.2 j).1 = (R.2 j).1)
    (hunion : ∀ x, (x ∈ (Q.2 a).1 ∨ x ∈ (Q.2 b).1) ↔ (x ∈ (R.2 a).1 ∨ x ∈ (R.2 b).1))
    (hinter : ∀ x, (x ∈ (Q.2 a).1 ∧ x ∈ (Q.2 b).1) ↔ (x ∈ (R.2 a).1 ∧ x ∈ (R.2 b).1)) :
    sharedNodes Q ⊆ sharedNodes R := by
  intro x hx
  rw [mem_sharedNodes] at hx ⊢
  obtain ⟨j, j', hjj', hxj, hxj'⟩ := hx
  by_cases hj : j = a ∨ j = b
  · by_cases hj' : j' = a ∨ j' = b
    · have hboth : x ∈ (Q.2 a).1 ∧ x ∈ (Q.2 b).1 := by
        rcases hj with h | h <;> rcases hj' with h' | h' <;> subst h <;> subst h' <;>
          first
            | exact absurd rfl hjj'
            | exact ⟨hxj, hxj'⟩
            | exact ⟨hxj', hxj⟩
      exact ⟨a, b, hab, ((hinter x).1 hboth).1, ((hinter x).1 hboth).2⟩
    · push_neg at hj'
      have hu : x ∈ (R.2 a).1 ∨ x ∈ (R.2 b).1 :=
        (hunion x).1 (by rcases hj with h | h <;> subst h <;> tauto)
      have hxR : x ∈ (R.2 j').1 := (hother j' hj'.1 hj'.2) ▸ hxj'
      rcases hu with h | h
      · exact ⟨a, j', fun hc => hj'.1 hc.symm, h, hxR⟩
      · exact ⟨b, j', fun hc => hj'.2 hc.symm, h, hxR⟩
  · push_neg at hj
    by_cases hj' : j' = a ∨ j' = b
    · have hu : x ∈ (R.2 a).1 ∨ x ∈ (R.2 b).1 :=
        (hunion x).1 (by rcases hj' with h | h <;> subst h <;> tauto)
      have hxR : x ∈ (R.2 j).1 := (hother j hj.1 hj.2) ▸ hxj
      rcases hu with h | h
      · exact ⟨j, a, hj.1, hxR, h⟩
      · exact ⟨j, b, hj.2, hxR, h⟩
    · push_neg at hj'
      exact ⟨j, j', hjj', (hother j hj.1 hj.2) ▸ hxj, (hother j' hj'.1 hj'.2) ▸ hxj'⟩

/-- The elements of a path of a path system before its common node have smaller rank than
the node, hence differ from all the elements after it. -/
theorem CrossData.memNew0 (hc : Γ.CrossData mu nu P v j0 j1) (x : CoreEdge d G) :
    x ∈ ((swapAt P v j0 j1).2 j0).1 ↔
      x ∈ before v (P.2 j0).1 ∨ x = v ∨ x ∈ after v (P.2 j1).1 := by
  rw [hc.swapAt_j0]
  simp [List.mem_append, List.mem_cons]

theorem CrossData.memNew1 (hc : Γ.CrossData mu nu P v j0 j1) (x : CoreEdge d G) :
    x ∈ ((swapAt P v j0 j1).2 j1).1 ↔
      x ∈ before v (P.2 j1).1 ∨ x = v ∨ x ∈ after v (P.2 j0).1 := by
  rw [hc.swapAt_j1]
  simp [List.mem_append, List.mem_cons]

theorem CrossData.memOld0 (hc : Γ.CrossData mu nu P v j0 j1) (x : CoreEdge d G) :
    x ∈ (P.2 j0).1 ↔ x ∈ before v (P.2 j0).1 ∨ x = v ∨ x ∈ after v (P.2 j0).1 :=
  mem_iff_of_mem hc.mem0

theorem CrossData.memOld1 (hc : Γ.CrossData mu nu P v j0 j1) (x : CoreEdge d G) :
    x ∈ (P.2 j1).1 ↔ x ∈ before v (P.2 j1).1 ∨ x = v ∨ x ∈ after v (P.2 j1).1 :=
  mem_iff_of_mem hc.mem1

/-- **The exchange of tails does not change the set of shared nodes.** This is where the
acyclicity of the `Γ`-oriented line graph enters: the beginning of one path and the end of
another can never meet. -/
theorem CrossData.sharedNodes_swapAt (hc : Γ.CrossData mu nu P v j0 j1) :
    sharedNodes (swapAt P v j0 j1) = sharedNodes P := by
  have hunion : ∀ x, (x ∈ ((swapAt P v j0 j1).2 j0).1 ∨ x ∈ ((swapAt P v j0 j1).2 j1).1) ↔
      (x ∈ (P.2 j0).1 ∨ x ∈ (P.2 j1).1) := by
    intro x
    rw [hc.memNew0, hc.memNew1, hc.memOld0, hc.memOld1]
    tauto
  have hinter : ∀ x, (x ∈ ((swapAt P v j0 j1).2 j0).1 ∧ x ∈ ((swapAt P v j0 j1).2 j1).1) ↔
      (x ∈ (P.2 j0).1 ∧ x ∈ (P.2 j1).1) := by
    intro x
    rw [hc.memNew0, hc.memNew1, hc.memOld0, hc.memOld1]
    by_cases hxv : x = v
    · subst hxv; tauto
    have h1 : x ∈ before v (P.2 j0).1 → x ∉ after v (P.2 j0).1 := by
      intro h h'
      exact lt_irrefl _ (lt_trans (Γ.nodeRank_lt_of_mem_before hc.chain0 hc.mem0 h)
        (Γ.nodeRank_lt_of_mem_after hc.chain0 hc.mem0 h'))
    have h2 : x ∈ before v (P.2 j0).1 → x ∉ after v (P.2 j1).1 := by
      intro h h'
      exact lt_irrefl _ (lt_trans (Γ.nodeRank_lt_of_mem_before hc.chain0 hc.mem0 h)
        (Γ.nodeRank_lt_of_mem_after hc.chain1 hc.mem1 h'))
    have h3 : x ∈ before v (P.2 j1).1 → x ∉ after v (P.2 j0).1 := by
      intro h h'
      exact lt_irrefl _ (lt_trans (Γ.nodeRank_lt_of_mem_before hc.chain1 hc.mem1 h)
        (Γ.nodeRank_lt_of_mem_after hc.chain0 hc.mem0 h'))
    have h4 : x ∈ before v (P.2 j1).1 → x ∉ after v (P.2 j1).1 := by
      intro h h'
      exact lt_irrefl _ (lt_trans (Γ.nodeRank_lt_of_mem_before hc.chain1 hc.mem1 h)
        (Γ.nodeRank_lt_of_mem_after hc.chain1 hc.mem1 h'))
    tauto
  have hother : ∀ j, j ≠ j0 → j ≠ j1 → ((swapAt P v j0 j1).2 j).1 = (P.2 j).1 := by
    intro j h0 h1
    rw [swapAt_other h0 h1]
  refine Finset.Subset.antisymm
    (sharedNodes_subset_of_exchange hc.ne hother hunion hinter)
    (sharedNodes_subset_of_exchange hc.ne (fun j h0 h1 => (hother j h0 h1).symm)
      (fun x => (hunion x).symm) (fun x => (hinter x).symm))

/-- The exchange of tails does not change the set of indices of the paths through the
common node. -/
theorem CrossData.idxSet_swapAt (hc : Γ.CrossData mu nu P v j0 j1) :
    idxSet (swapAt P v j0 j1) v = idxSet P v := by
  ext j
  simp only [mem_idxSet]
  by_cases h0 : j = j0
  · subst h0
    simp only [hc.memNew0, hc.mem0, iff_true]
    tauto
  · by_cases h1 : j = j1
    · subst h1
      simp only [hc.memNew1, hc.mem1, iff_true]
      tauto
    · rw [swapAt_other h0 h1]

/-! ### The exchange of tails is an involution reversing the sign -/

/-- The exchanged system is again a system of directed paths joining the same sources to
the sinks, matched by the permutation composed with the transposition `(j₀ j₁)`. -/
theorem CrossData.isPath_swapAt (hc : Γ.CrossData mu nu P v j0 j1) (j : Fin l) :
    Γ.IsLPath (mu j) (nu ((swapAt P v j0 j1).1 j)) ((swapAt P v j0 j1).2 j).1 := by
  by_cases h0 : j = j0
  · rw [h0, hc.swapAt_j0]
    refine ⟨?_, ?_, ?_⟩
    · rw [head?_append_cons, ← head?_append_cons (before v (P.2 j0).1) v (after v (P.2 j0).1),
        before_append_after hc.mem0]
      exact (hc.isPath j0).1
    · rw [swapAt_perm, Equiv.swap_apply_left, List.getLast?_append_cons,
        ← List.getLast?_append_cons (before v (P.2 j1).1) v (after v (P.2 j1).1),
        before_append_after hc.mem1]
      exact (hc.isPath j1).2.1
    · exact Γ.isChain_splice (Γ.isChain_before hc.chain0 hc.mem0)
        (Γ.isChain_after hc.chain1 hc.mem1)
  · by_cases h1 : j = j1
    · rw [h1, hc.swapAt_j1]
      refine ⟨?_, ?_, ?_⟩
      · rw [head?_append_cons, ← head?_append_cons (before v (P.2 j1).1) v (after v (P.2 j1).1),
          before_append_after hc.mem1]
        exact (hc.isPath j1).1
      · rw [swapAt_perm, Equiv.swap_apply_right, List.getLast?_append_cons,
          ← List.getLast?_append_cons (before v (P.2 j0).1) v (after v (P.2 j0).1),
          before_append_after hc.mem0]
        exact (hc.isPath j0).2.1
      · exact Γ.isChain_splice (Γ.isChain_before hc.chain1 hc.mem1)
          (Γ.isChain_after hc.chain0 hc.mem0)
    · rw [swapAt_other h0 h1, swapAt_perm, Equiv.swap_apply_of_ne_of_ne h0 h1]
      exact hc.isPath j

/-- The node and the two indices still exhibit a crossing in the exchanged system. -/
theorem CrossData.swap (hc : Γ.CrossData mu nu P v j0 j1) :
    Γ.CrossData mu nu (swapAt P v j0 j1) v j0 j1 where
  isPath := hc.isPath_swapAt
  ne := hc.ne
  mem0 := by rw [hc.swapAt_j0]; simp
  mem1 := by rw [hc.swapAt_j1]; simp

/-- **Exchanging the tails twice returns the original path system.** -/
theorem CrossData.swapAt_swapAt (hc : Γ.CrossData mu nu P v j0 j1) :
    swapAt (swapAt P v j0 j1) v j0 j1 = P := by
  have hc' := hc.swap
  refine Prod.ext ?_ (funext fun j => ?_)
  · show P.1 * Equiv.swap j0 j1 * Equiv.swap j0 j1 = P.1
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  · by_cases h0 : j = j0
    · rw [h0]
      refine Subtype.ext ?_
      rw [hc'.swapAt_j0, hc.swapAt_j0, hc.swapAt_j1,
        before_of_append_cons (not_mem_before v _), after_of_append_cons (not_mem_before v _),
        before_append_after hc.mem0]
    · by_cases h1 : j = j1
      · rw [h1]
        refine Subtype.ext ?_
        rw [hc'.swapAt_j1, hc.swapAt_j1, hc.swapAt_j0,
          before_of_append_cons (not_mem_before v _), after_of_append_cons (not_mem_before v _),
          before_append_after hc.mem1]
      · rw [swapAt_other h0 h1, swapAt_other h0 h1]

/-- The product `frac(𝒫)|_p` of the fractions along all the arrows of all the paths of a
path system (`main.tex`, Section "Proofs"). -/
noncomputable def systemFracEval (p : V → Fin d → ℝ) {l : ℕ} (P : PathSystemData d G l) : ℝ :=
  ∏ j, Γ.pathFracEval p (P.2 j).1

/-- **Exchanging the tails does not change the product of the fractions.** -/
theorem CrossData.systemFracEval_swapAt (hc : Γ.CrossData mu nu P v j0 j1)
    (p : V → Fin d → ℝ) :
    Γ.systemFracEval p (swapAt P v j0 j1) = Γ.systemFracEval p P := by
  have key : ∀ Q : PathSystemData d G l, ∏ j, Γ.pathFracEval p (Q.2 j).1
      = Γ.pathFracEval p (Q.2 j0).1 * (Γ.pathFracEval p (Q.2 j1).1 *
          ∏ j ∈ (univ.erase j0).erase j1, Γ.pathFracEval p (Q.2 j).1) := by
    intro Q
    rw [← Finset.mul_prod_erase univ (fun j => Γ.pathFracEval p (Q.2 j).1) (mem_univ j0),
      ← Finset.mul_prod_erase (univ.erase j0) (fun j => Γ.pathFracEval p (Q.2 j).1)
        (Finset.mem_erase.2 ⟨Ne.symm hc.ne, mem_univ j1⟩)]
  have hrest : ∏ j ∈ (univ.erase j0).erase j1, Γ.pathFracEval p ((swapAt P v j0 j1).2 j).1
      = ∏ j ∈ (univ.erase j0).erase j1, Γ.pathFracEval p (P.2 j).1 := by
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finset.mem_erase, Finset.mem_erase] at hj
    rw [swapAt_other hj.2.1 hj.1]
  have hL0 : Γ.pathFracEval p (P.2 j0).1
      = Γ.pathFracEval p (before v (P.2 j0).1 ++ v :: after v (P.2 j0).1) := by
    rw [before_append_after hc.mem0]
  have hL1 : Γ.pathFracEval p (P.2 j1).1
      = Γ.pathFracEval p (before v (P.2 j1).1 ++ v :: after v (P.2 j1).1) := by
    rw [before_append_after hc.mem1]
  simp only [systemFracEval]
  rw [key (swapAt P v j0 j1), key P, hc.swapAt_j0, hc.swapAt_j1, hrest, hL0, hL1]
  rw [Γ.pathFracEval_append_cons p v (before v (P.2 j0).1) (after v (P.2 j1).1),
    Γ.pathFracEval_append_cons p v (before v (P.2 j1).1) (after v (P.2 j0).1),
    Γ.pathFracEval_append_cons p v (before v (P.2 j0).1) (after v (P.2 j0).1),
    Γ.pathFracEval_append_cons p v (before v (P.2 j1).1) (after v (P.2 j1).1)]
  ring

omit [DecidableRel G.Adj] in
/-- **Exchanging the tails reverses the sign of the permutation of the path system.** -/
theorem CrossData.sign_swapAt (hc : Γ.CrossData mu nu P v j0 j1) :
    Equiv.Perm.sign (swapAt P v j0 j1).1 = - Equiv.Perm.sign P.1 := by
  show Equiv.Perm.sign (P.1 * Equiv.swap j0 j1) = _
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hc.ne, mul_neg_one]

omit [DecidableRel G.Adj] in
/-- The exchanged path system is different from the original one: its permutation is. -/
theorem CrossData.swapAt_ne (hc : Γ.CrossData mu nu P v j0 j1) :
    swapAt P v j0 j1 ≠ P := by
  intro hcon
  have h : Equiv.Perm.sign (swapAt P v j0 j1).1 = Equiv.Perm.sign P.1 := by rw [hcon]
  rw [hc.sign_swapAt] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign P.1) with hs | hs <;> rw [hs] at h <;> simp at h

/-! ### The canonical crossing and the sign-reversing involution -/

/-- A node lying on two paths of a path system is on at least two of them. -/
theorem one_lt_card_idxSet {Q : PathSystemData d G l} {x : CoreEdge d G}
    (h : x ∈ sharedNodes Q) : 1 < #(idxSet Q x) := by
  rw [mem_sharedNodes] at h
  obtain ⟨j, j', hne, hj, hj'⟩ := h
  exact Finset.one_lt_card.2 ⟨j, mem_idxSet.2 hj, j', mem_idxSet.2 hj', hne⟩

/-- The canonical node at which the tails of a non-disjoint path system are exchanged. -/
noncomputable def crossNode (Q : PathSystemData d G l) (h : (sharedNodes Q).Nonempty) :
    CoreEdge d G := h.choose

theorem crossNode_mem (Q : PathSystemData d G l) (h : (sharedNodes Q).Nonempty) :
    crossNode Q h ∈ sharedNodes Q := h.choose_spec

theorem idxSet_crossNode_nonempty (Q : PathSystemData d G l) (h : (sharedNodes Q).Nonempty) :
    (idxSet Q (crossNode Q h)).Nonempty :=
  Finset.card_pos.1 (lt_trans Nat.zero_lt_one (one_lt_card_idxSet (crossNode_mem Q h)))

/-- The smallest index of a path of the system through the canonical crossing node. -/
noncomputable def crossJ0 (Q : PathSystemData d G l) (h : (sharedNodes Q).Nonempty) : Fin l :=
  (idxSet Q (crossNode Q h)).min' (idxSet_crossNode_nonempty Q h)

theorem crossJ0_mem (Q : PathSystemData d G l) (h : (sharedNodes Q).Nonempty) :
    crossJ0 Q h ∈ idxSet Q (crossNode Q h) := Finset.min'_mem _ _

theorem erase_crossJ0_nonempty (Q : PathSystemData d G l) (h : (sharedNodes Q).Nonempty) :
    ((idxSet Q (crossNode Q h)).erase (crossJ0 Q h)).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem (crossJ0_mem Q h)]
  have := one_lt_card_idxSet (crossNode_mem Q h)
  omega

/-- The second smallest index of a path of the system through the canonical crossing
node. -/
noncomputable def crossJ1 (Q : PathSystemData d G l) (h : (sharedNodes Q).Nonempty) : Fin l :=
  ((idxSet Q (crossNode Q h)).erase (crossJ0 Q h)).min' (erase_crossJ0_nonempty Q h)

theorem crossJ1_mem (Q : PathSystemData d G l) (h : (sharedNodes Q).Nonempty) :
    crossJ1 Q h ∈ idxSet Q (crossNode Q h) :=
  Finset.mem_of_mem_erase (Finset.min'_mem _ _)

theorem crossJ0_ne_crossJ1 (Q : PathSystemData d G l) (h : (sharedNodes Q).Nonempty) :
    crossJ0 Q h ≠ crossJ1 Q h :=
  fun hcon => (Finset.ne_of_mem_erase (Finset.min'_mem _ _)) hcon.symm

/-- **The sign-reversing involution of the Lindström–Gessel–Viennot lemma**: exchange the
tails of the two smallest-indexed paths through the canonical crossing node. -/
noncomputable def cross (Q : PathSystemData d G l) : PathSystemData d G l :=
  if h : (sharedNodes Q).Nonempty then swapAt Q (crossNode Q h) (crossJ0 Q h) (crossJ1 Q h)
  else Q

theorem cross_eq_swapAt (Q : PathSystemData d G l) (h : (sharedNodes Q).Nonempty) :
    cross Q = swapAt Q (crossNode Q h) (crossJ0 Q h) (crossJ1 Q h) := by
  rw [cross, dif_pos h]

theorem crossData_of_isPath {Q : PathSystemData d G l}
    (hpath : ∀ j, Γ.IsLPath (mu j) (nu (Q.1 j)) (Q.2 j).1) (h : (sharedNodes Q).Nonempty) :
    Γ.CrossData mu nu Q (crossNode Q h) (crossJ0 Q h) (crossJ1 Q h) where
  isPath := hpath
  ne := crossJ0_ne_crossJ1 Q h
  mem0 := mem_idxSet.1 (crossJ0_mem Q h)
  mem1 := mem_idxSet.1 (crossJ1_mem Q h)

theorem crossNode_congr {Q R : PathSystemData d G l} (hQR : sharedNodes Q = sharedNodes R)
    (hQ : (sharedNodes Q).Nonempty) (hR : (sharedNodes R).Nonempty) :
    crossNode Q hQ = crossNode R hR := by
  have key : ∀ (s t : Finset (CoreEdge d G)) (hs : s.Nonempty) (ht : t.Nonempty),
      s = t → hs.choose = ht.choose := by
    rintro s t hs ht rfl
    rfl
  exact key _ _ hQ hR hQR

theorem crossJ0_congr {Q R : PathSystemData d G l}
    (hQ : (sharedNodes Q).Nonempty) (hR : (sharedNodes R).Nonempty)
    (hidx : idxSet Q (crossNode Q hQ) = idxSet R (crossNode R hR)) :
    crossJ0 Q hQ = crossJ0 R hR := min'_congr_finset hidx _ _

theorem crossJ1_congr {Q R : PathSystemData d G l}
    (hQ : (sharedNodes Q).Nonempty) (hR : (sharedNodes R).Nonempty)
    (hidx : idxSet Q (crossNode Q hQ) = idxSet R (crossNode R hR)) :
    crossJ1 Q hQ = crossJ1 R hR :=
  min'_congr_finset (by rw [hidx, crossJ0_congr hQ hR hidx]) _ _

/-- **The exchange of tails is an involution.** -/
theorem cross_cross {Q : PathSystemData d G l}
    (hpath : ∀ j, Γ.IsLPath (mu j) (nu (Q.1 j)) (Q.2 j).1) (h : (sharedNodes Q).Nonempty) :
    cross (cross Q) = Q := by
  have hc := Γ.crossData_of_isPath hpath h
  have hQ' : cross Q = swapAt Q (crossNode Q h) (crossJ0 Q h) (crossJ1 Q h) :=
    cross_eq_swapAt Q h
  have hshare : sharedNodes (cross Q) = sharedNodes Q := by
    rw [hQ']; exact hc.sharedNodes_swapAt
  have h' : (sharedNodes (cross Q)).Nonempty := by rw [hshare]; exact h
  have hv : crossNode (cross Q) h' = crossNode Q h := crossNode_congr hshare h' h
  have hidx : idxSet (cross Q) (crossNode (cross Q) h') = idxSet Q (crossNode Q h) := by
    rw [hv, hQ']; exact hc.idxSet_swapAt
  rw [cross_eq_swapAt (cross Q) h', hv, crossJ0_congr h' h hidx, crossJ1_congr h' h hidx, hQ']
  exact hc.swapAt_swapAt

/-! ### The cancellation of the non-disjoint path systems -/

/-- All candidate path systems joining the sources `μ` to the sinks `ν`, disjoint or
not. -/
noncomputable def allSystems {l : ℕ} (mu nu : Fin l → CoreEdge d G) :
    Finset (PathSystemData d G l) :=
  univ.filter (fun P => ∀ j, Γ.IsLPath (mu j) (nu (P.1 j)) (P.2 j).1)

theorem mem_allSystems {Q : PathSystemData d G l} :
    Q ∈ Γ.allSystems mu nu ↔ ∀ j, Γ.IsLPath (mu j) (nu (Q.1 j)) (Q.2 j).1 := by
  simp [allSystems]

theorem disjointSystems_subset_allSystems :
    Γ.disjointSystems mu nu ⊆ Γ.allSystems mu nu := by
  intro Q hQ
  rw [disjointSystems, mem_filter] at hQ
  exact Γ.mem_allSystems.2 hQ.2.1

theorem mem_disjointSystems_iff {Q : PathSystemData d G l} :
    Q ∈ Γ.disjointSystems mu nu ↔
      Q ∈ Γ.allSystems mu nu ∧ ¬ (sharedNodes Q).Nonempty := by
  constructor
  · intro hQ
    refine ⟨Γ.disjointSystems_subset_allSystems hQ, ?_⟩
    rw [disjointSystems, mem_filter] at hQ
    rintro ⟨x, hx⟩
    rw [mem_sharedNodes] at hx
    obtain ⟨j, j', hne, hj, hj'⟩ := hx
    exact hQ.2.2 j j' hne x hj hj'
  · rintro ⟨hall, hns⟩
    rw [disjointSystems, mem_filter]
    refine ⟨mem_univ _, Γ.mem_allSystems.1 hall, ?_⟩
    intro j j' hne x hx hx'
    exact hns ⟨x, mem_sharedNodes.2 ⟨j, j', hne, hx, hx'⟩⟩

theorem sharedNodes_nonempty_of_mem_sdiff {Q : PathSystemData d G l}
    (hQ : Q ∈ Γ.allSystems mu nu \ Γ.disjointSystems mu nu) : (sharedNodes Q).Nonempty := by
  rw [Finset.mem_sdiff] at hQ
  by_contra hcon
  exact hQ.2 (Γ.mem_disjointSystems_iff.2 ⟨hQ.1, hcon⟩)

/-- **The non-disjoint path systems cancel in pairs.** This is the combinatorial heart of
the Lindström–Gessel–Viennot lemma quoted in the source article (`main.tex`, Section
"Proofs"). -/
theorem sum_sdiff_eq_zero (p : V → Fin d → ℝ) {l : ℕ} (mu nu : Fin l → CoreEdge d G) :
    ∑ Q ∈ Γ.allSystems mu nu \ Γ.disjointSystems mu nu,
      ((Equiv.Perm.sign Q.1 : ℤ) : ℝ) * Γ.systemFracEval p Q = 0 := by
  refine Finset.sum_involution (fun Q _ => cross Q) ?_ ?_ ?_ ?_
  · intro Q hQ
    have hns := Γ.sharedNodes_nonempty_of_mem_sdiff hQ
    have hpath := Γ.mem_allSystems.1 (Finset.mem_sdiff.1 hQ).1
    have hc := Γ.crossData_of_isPath hpath hns
    show ((Equiv.Perm.sign Q.1 : ℤ) : ℝ) * Γ.systemFracEval p Q
        + ((Equiv.Perm.sign (cross Q).1 : ℤ) : ℝ) * Γ.systemFracEval p (cross Q) = 0
    rw [cross_eq_swapAt Q hns, hc.systemFracEval_swapAt, hc.sign_swapAt]
    push_cast
    ring
  · intro Q hQ _
    have hns := Γ.sharedNodes_nonempty_of_mem_sdiff hQ
    have hpath := Γ.mem_allSystems.1 (Finset.mem_sdiff.1 hQ).1
    have hc := Γ.crossData_of_isPath hpath hns
    show cross Q ≠ Q
    rw [cross_eq_swapAt Q hns]
    exact hc.swapAt_ne
  · intro Q hQ
    have hns := Γ.sharedNodes_nonempty_of_mem_sdiff hQ
    have hpath := Γ.mem_allSystems.1 (Finset.mem_sdiff.1 hQ).1
    have hc := Γ.crossData_of_isPath hpath hns
    have hall : cross Q ∈ Γ.allSystems mu nu := by
      rw [cross_eq_swapAt Q hns]
      exact Γ.mem_allSystems.2 hc.isPath_swapAt
    have hshare : sharedNodes (cross Q) = sharedNodes Q := by
      rw [cross_eq_swapAt Q hns]; exact hc.sharedNodes_swapAt
    show cross Q ∈ Γ.allSystems mu nu \ Γ.disjointSystems mu nu
    rw [Finset.mem_sdiff]
    refine ⟨hall, ?_⟩
    intro hcon
    exact (Γ.mem_disjointSystems_iff.1 hcon).2 (by rw [hshare]; exact hns)
  · intro Q hQ
    show cross (cross Q) = Q
    exact Γ.cross_cross (Γ.mem_allSystems.1 (Finset.mem_sdiff.1 hQ).1)
      (Γ.sharedNodes_nonempty_of_mem_sdiff hQ)

end DOrientation

end RigidityTableaux
