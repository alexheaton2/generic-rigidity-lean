import RequestProject.TrivialMotions

/-!
# Selecting an independent set of rows of the rigidity matrix

This file provides the linear-algebra step in the proof of Corollary
`cor:characterization` of the source article (`main.tex`): if a framework `(G,p)` is
infinitesimally rigid, then one may select `m = d|V| - binom (d+1) 2` of the rows of the
coefficient matrix `A` of the self-stress equations which are linearly independent. The
corresponding spanning subgraph `H ⊆ G` has exactly `m` edges, i.e. satisfies Maxwell's
count, and carries no nonzero self-stress.

The rows of `A` are recorded as the linear functionals `edgeRow p e` on the space of
velocity assignments, and the space they span is `rowSpace p`; the space of infinitesimal
flexes is exactly the subspace annihilated by `rowSpace p`.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The row of the coefficient matrix `A` of the self-stress equations of the source
article (`main.tex`, Section "Geometric results") corresponding to the edge `e`, viewed
as a linear functional on the space of velocity assignments. -/
noncomputable def edgeRow (p : V → Fin d → ℝ) (e : OrientedEdge G) :
    Module.Dual ℝ (V → Fin d → ℝ) :=
  (LinearMap.proj e : (OrientedEdge G → ℝ) →ₗ[ℝ] ℝ) ∘ₗ rigidityMap p

omit [Fintype V] [DecidableEq V] in
theorem edgeRow_apply (p : V → Fin d → ℝ) (e : OrientedEdge G) (q : V → Fin d → ℝ) :
    edgeRow p e q = rigidityMap p q e := rfl

/-- The row space of the matrix `A` of the source article. -/
noncomputable def rowSpace (p : V → Fin d → ℝ) :
    Submodule ℝ (Module.Dual ℝ (V → Fin d → ℝ)) :=
  Submodule.span ℝ (Set.range (edgeRow (G := G) p))

omit [Fintype V] [DecidableEq V] in
/-- The infinitesimal flexes are exactly the velocity assignments annihilated by every
row of `A`. -/
theorem infFlexes_eq_dualCoannihilator (p : V → Fin d → ℝ) :
    infFlexes (G := G) p = (rowSpace (G := G) p).dualCoannihilator := by
  ext q
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro hq φ hφ
    have hq' : rigidityMap (G := G) p q = 0 := hq
    have hsub : rowSpace (G := G) p ≤ LinearMap.ker (LinearMap.applyₗ (R := ℝ) q) := by
      rw [rowSpace, Submodule.span_le]
      rintro ψ ⟨e, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      show edgeRow p e q = 0
      rw [edgeRow_apply, hq']
      rfl
    exact hsub hφ
  · intro h
    show rigidityMap (G := G) p q = 0
    funext e
    have := h (edgeRow p e) (Submodule.subset_span ⟨e, rfl⟩)
    rw [edgeRow_apply] at this
    simpa using this

omit [DecidableEq V] in
/-- The rank-nullity relation for the matrix `A` of the source article: the rank of `A`
plus the dimension of the space of infinitesimal flexes is `d|V|`. -/
theorem finrank_rowSpace_add_finrank_infFlexes (p : V → Fin d → ℝ) :
    Module.finrank ℝ (rowSpace (G := G) p) + Module.finrank ℝ (infFlexes (G := G) p)
      = d * Fintype.card V := by
  rw [infFlexes_eq_dualCoannihilator,
    Subspace.finrank_add_finrank_dualCoannihilator_eq (rowSpace (G := G) p),
    Module.finrank_pi_fintype ℝ]
  simp [Module.finrank_fintype_fun_eq_card, mul_comm]

/-! ### The spanning subgraph on a chosen set of edges -/

/-- The spanning subgraph of `G` whose edges are those in a chosen set `S` of edges of
`G`. This is the subgraph selected in the proof of Corollary `cor:characterization` of
the source article. -/
def subgraphOfEdges (S : Set (OrientedEdge G)) : SimpleGraph V where
  Adj i j := ∃ e ∈ S, (e.1.1 = i ∧ e.1.2 = j) ∨ (e.1.1 = j ∧ e.1.2 = i)
  symm := by
    rintro i j ⟨e, he, h⟩
    exact ⟨e, he, h.symm⟩
  loopless := ⟨by
    rintro i ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;>
      exact absurd e.2.1 (by rw [h1, h2]; exact lt_irrefl i)⟩

omit [Fintype V] [DecidableEq V] in
theorem subgraphOfEdges_le (S : Set (OrientedEdge G)) : subgraphOfEdges S ≤ G := by
  rintro i j ⟨e, -, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · rw [← h1, ← h2]; exact e.2.2
  · rw [← h1, ← h2]; exact e.2.2.symm

/-- The edges of the chosen subgraph are exactly the chosen edges. -/
noncomputable def edgeIncl (S : Set (OrientedEdge G)) (e : S) :
    OrientedEdge (subgraphOfEdges S) :=
  ⟨e.1.1, e.1.2.1, ⟨e.1, e.2, Or.inl ⟨rfl, rfl⟩⟩⟩

omit [Fintype V] [DecidableEq V] in
theorem edgeIncl_bijective (S : Set (OrientedEdge G)) :
    Function.Bijective (edgeIncl S) := by
  constructor
  · intro e e' h
    have h1 : (edgeIncl S e).1 = (edgeIncl S e').1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h1)
  · rintro ⟨⟨i, j⟩, hlt, e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨⟨e, he⟩, Subtype.ext (Prod.ext h1 h2)⟩
    · exact absurd e.2.1 (by rw [h1, h2]; exact asymm hlt)

omit [Fintype V] [DecidableEq V] in
theorem rigidityMap_edgeIncl (S : Set (OrientedEdge G)) (p q : V → Fin d → ℝ) (e : S) :
    rigidityMap (G := subgraphOfEdges S) p q (edgeIncl S e) = edgeRow p e.1 q := rfl

omit [Fintype V] [DecidableEq V] in
/-- Every infinitesimal flex of a framework is an infinitesimal flex of each of its
spanning subframeworks. -/
theorem infFlexes_mono {H : SimpleGraph V} [DecidableRel H.Adj] (hHG : H ≤ G)
    (p : V → Fin d → ℝ) : infFlexes (G := G) p ≤ infFlexes (G := H) p := by
  intro q hq
  have hq' : rigidityMap (G := G) p q = 0 := hq
  show rigidityMap (G := H) p q = 0
  funext e
  have h : rigidityMap (G := G) p q ⟨e.1, e.2.1, hHG e.2.2⟩ = 0 := by rw [hq']; rfl
  exact h

/-! ### Selecting independent rows -/

/-- **The row selection step in the proof of Corollary `cor:characterization` of the
source article.** If the framework `(G,p)` is infinitesimally rigid, then `G` has a
spanning subgraph `H` satisfying Maxwell's count `|E| = d|V| - binom (d+1) 2` which
carries no nonzero self-stress at `p`. -/
theorem exists_maxwell_subgraph_no_selfstress (p : V → Fin d → ℝ)
    (hrig : InfinitesimallyRigid (G := G) p) :
    ∃ H : SimpleGraph V, H ≤ G ∧ MaxwellCount d H ∧
      ¬ ∃ w : OrientedEdge H → ℝ, w ≠ 0 ∧ IsSelfStress p w := by
  classical
  set f : OrientedEdge G → Module.Dual ℝ (V → Fin d → ℝ) := edgeRow p with hf
  set S : Set (OrientedEdge G) :=
    (linearIndepOn_empty ℝ f).extend (Set.empty_subset (Set.univ : Set (OrientedEdge G)))
    with hS
  have hli : LinearIndepOn ℝ f S :=
    (linearIndepOn_empty ℝ f).linearIndepOn_extend (Set.empty_subset _)
  have hspan : Submodule.span ℝ (f '' S) = rowSpace (G := G) p := by
    rw [hS, (linearIndepOn_empty ℝ f).span_image_extend_eq_span_image
      (Set.empty_subset (Set.univ : Set (OrientedEdge G))), Set.image_univ, rowSpace]
  have hcard : Fintype.card S = Module.finrank ℝ (rowSpace (G := G) p) := by
    have hr : Set.range (fun x : S => f x.1) = f '' S := (Set.image_eq_range f S).symm
    rw [← hspan, ← hr]
    exact (finrank_span_eq_card hli.linearIndependent).symm
  refine ⟨subgraphOfEdges S, subgraphOfEdges_le S, ?_, ?_⟩
  · -- Maxwell's count
    have h1 : #(subgraphOfEdges S).edgeFinset = Fintype.card S := by
      rw [← card_orientedEdge (subgraphOfEdges S)]
      exact (Fintype.card_of_bijective (edgeIncl_bijective S)).symm
    have h2 := finrank_rowSpace_add_finrank_infFlexes (G := G) p
    have h3 : Module.finrank ℝ (infFlexes (G := G) p) = Nat.choose (d + 1) 2 := hrig
    unfold MaxwellCount
    rw [h1, hcard]
    omega
  · rintro ⟨w, hw0, hw⟩
    have hbij := edgeIncl_bijective S
    have hsum : ∀ q : V → Fin d → ℝ,
        ∑ x : S, w (edgeIncl S x) * f x.1 q = 0 := by
      intro q
      have h := (isSelfStress_iff p w).1 hw q
      rw [← h]
      refine Fintype.sum_bijective (edgeIncl S) hbij
        (fun x => w (edgeIncl S x) * f x.1 q) (fun e => w e * rigidityMap p q e) ?_
      intro x
      show w (edgeIncl S x) * f x.1 q = w (edgeIncl S x) * rigidityMap p q (edgeIncl S x)
      rw [rigidityMap_edgeIncl S p q x]
    have hzero : ∑ x : S, w (edgeIncl S x) • f x.1 = 0 := by
      refine LinearMap.ext fun q => ?_
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
      exact hsum q
    have := (Fintype.linearIndependent_iff.mp hli.linearIndependent)
      (fun x => w (edgeIncl S x)) hzero
    apply hw0
    funext e'
    obtain ⟨x, rfl⟩ := hbij.2 e'
    exact this x

end RigidityTableaux
