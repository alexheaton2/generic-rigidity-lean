import RequestProject.Orientation

/-!
# Self-stresses vanish on desert edges

This file proves the first step of the proof of Lemma `lemma:stream-formula-new` of the
source article (`main.tex`, Section "Proofs"): *"First note that `w_{ij} = 0` whenever
`(i,j)` is a desert edge, by affine independence of `p` applied repeatedly as we label
desert edges."*

Instead of following the desert-labelling process step by step, we observe that the
edges carrying a nonzero stress form a `d`-deep edge relation: at a vertex incident to an
edge with nonzero stress, the vertex equation together with the affine independence of
`p` forces at least `d+1` incident edges to carry a nonzero stress. Since the non-desert
edges are by definition the union of all `d`-deep relations, every edge with nonzero
stress is a non-desert edge, i.e. every desert edge carries zero stress.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The edges of `G` carrying a nonzero stress. -/
def nonzeroStressEdges (w : OrientedEdge G → ℝ) (i j : V) : Prop :=
  G.Adj i j ∧ stressVal w i j ≠ 0

/-- At a vertex incident to an edge with nonzero stress, at least `d+1` incident edges
carry a nonzero stress: this is the vertex equation of the self-stress together with the
affine independence of the placement. -/
theorem card_nonzeroStress_neighbors (p : V → Fin d → ℝ) (hp : AffinelyIndependentPlacement d p)
    (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w) (a b : V)
    (hab : nonzeroStressEdges w a b) :
    d + 1 ≤ #(univ.filter (fun c => nonzeroStressEdges w a c)) := by
  classical
  set N : Finset V := univ.filter (fun c => nonzeroStressEdges w a c) with hN
  by_contra hlt
  push_neg at hlt
  have hbN : b ∈ N := by
    rw [hN]
    simpa using hab
  have haN : a ∉ N := by
    rw [hN]
    simp only [mem_filter, mem_univ, true_and, nonzeroStressEdges]
    rintro ⟨hadj, -⟩
    exact G.ne_of_adj hadj rfl
  have hzero : ∀ c : V, c ∉ N → stressVal w a c = 0 := by
    intro c hc
    rw [hN] at hc
    simp only [mem_filter, mem_univ, true_and, nonzeroStressEdges, not_and, not_not] at hc
    by_cases hadj : G.Adj a c
    · exact hc hadj
    · exact stressVal_eq_zero_of_not_adj w hadj
  -- the vertex `a` together with the neighbours carrying nonzero stress
  have hcard : (insert a N).card ≤ d + 1 := by
    rw [Finset.card_insert_of_notMem haN]
    omega
  have hai := hp (insert a N) hcard
  rw [affineIndependent_iff_of_fintype] at hai
  -- the weights coming from the vertex equation at `a`
  set lam : V → ℝ :=
    fun c => if c = a then -(∑ c' ∈ N, stressVal w a c') else stressVal w a c with hlam
  have hlamN : ∀ c ∈ N, lam c = stressVal w a c := by
    intro c hc
    have hca : c ≠ a := fun h => haN (h ▸ hc)
    rw [hlam]
    simp [hca]
  have hlama : lam a = -(∑ c' ∈ N, stressVal w a c') := by
    rw [hlam]
    simp
  have hsumN : ∑ c ∈ insert a N, lam c = 0 := by
    rw [Finset.sum_insert haN, Finset.sum_congr rfl hlamN, hlama]
    ring
  have hsum : ∑ x : ((insert a N : Finset V) : Set V), lam (x : V) = 0 :=
    (Finset.sum_coe_sort (insert a N) lam).trans hsumN
  have hvsub : (Finset.univ.weightedVSub (fun x : ((insert a N : Finset V) : Set V) =>
      (p (x : V) : Fin d → ℝ))) (fun x => lam (x : V)) = 0 := by
    have h1 := Finset.weightedVSub_eq_linear_combination
      (s := (Finset.univ : Finset ((insert a N : Finset V) : Set V)))
      (w := fun x : ((insert a N : Finset V) : Set V) => lam (x : V))
      (p := fun x : ((insert a N : Finset V) : Set V) => (p (x : V) : Fin d → ℝ)) hsum
    have h2 : (∑ x : ((insert a N : Finset V) : Set V), lam (x : V) • (p (x : V) : Fin d → ℝ))
        = ∑ c ∈ insert a N, lam c • (p c : Fin d → ℝ) :=
      Finset.sum_coe_sort (insert a N) (fun c => lam c • (p c : Fin d → ℝ))
    rw [h1, h2]
    funext k
    have hpi : (∑ c ∈ insert a N, lam c • (p c : Fin d → ℝ)) k
        = ∑ c ∈ insert a N, lam c * p c k := by
      simp
    have hrestrict : ∑ c ∈ N, stressVal w a c * edgeVector p a c k = 0 := by
      have h0 : ∑ c ∈ N, stressVal w a c * edgeVector p a c k
          = ∑ c ∈ (univ : Finset V), stressVal w a c * edgeVector p a c k := by
        refine Finset.sum_subset (Finset.subset_univ N) ?_
        intro c _ hc
        rw [hzero c hc, zero_mul]
      rw [h0, hw a k]
    have hexp : ∑ c ∈ N, stressVal w a c * edgeVector p a c k
        = (∑ c ∈ N, stressVal w a c * p c k) - (∑ c ∈ N, stressVal w a c) * p a k := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [edgeVector]
      ring
    rw [hexp] at hrestrict
    rw [hpi, Finset.sum_insert haN,
      Finset.sum_congr rfl (fun c hc => by rw [hlamN c hc] : ∀ c ∈ N, lam c * p c k
        = stressVal w a c * p c k), hlama]
    simp only [Pi.zero_apply]
    linarith [hrestrict]
  have hbmem : b ∈ ((insert a N : Finset V) : Set V) := by
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
    exact Or.inr hbN
  have hb := hai (fun x => lam (x : V)) hsum hvsub ⟨b, hbmem⟩
  rw [hlamN b hbN] at hb
  exact hab.2 hb

/-- The edges carrying a nonzero stress form a `d`-deep edge relation. -/
theorem isDeep_nonzeroStressEdges (p : V → Fin d → ℝ) (hp : AffinelyIndependentPlacement d p)
    (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w) :
    IsDeep d G (nonzeroStressEdges w) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro i j ⟨hij, hne⟩
    exact ⟨hij.symm, by rwa [stressVal_symm]⟩
  · rintro i j ⟨hij, -⟩
    exact hij
  · intro i j hij
    exact card_nonzeroStress_neighbors p hp w hw i j hij

/-- **Desert edges carry no stress.** For an affinely independent placement `p`, every
self-stress vanishes on the desert edges of `G` (`main.tex`, first step of the proof of
Lemma `lemma:stream-formula-new`). -/
theorem stressVal_eq_zero_of_isDesertEdge (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w)
    (i j : V) (hij : IsDesertEdge d G i j) : stressVal w i j = 0 := by
  by_contra hne
  exact hij.2 ⟨nonzeroStressEdges w, isDeep_nonzeroStressEdges p hp w hw, ⟨hij.1, hne⟩⟩

/-- The version of `stressVal_eq_zero_of_isDesertEdge` for the coordinates of the stress
indexed by the oriented edges of `G`. -/
theorem selfStress_eq_zero_of_isDesertEdge (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w)
    (e : OrientedEdge G) (he : IsDesertEdge d G e.1.1 e.1.2) : w e = 0 := by
  have h := stressVal_eq_zero_of_isDesertEdge p hp w hw e.1.1 e.1.2 he
  rwa [stressVal, dif_pos ⟨e.2.1, e.2.2⟩] at h

end RigidityTableaux
