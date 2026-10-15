import RequestProject.StressConverse

/-!
# The `p,Γ`-equations as a linear system in the sink coordinates

This file organises the `p,Γ`-equations of the source article (`main.tex`, Section
"Proofs") as a homogeneous linear system in the sink coordinates alone:

> Thus Lemma \ref{lemma:stream-formula-new} determines stream variables `w_{ij}` in terms
> of sink variables `w_ν`, while Lemma \ref{lemma:source-constraint-equations-new} gives
> constraints on the sink variables `w_ν` which, when satisfied, allow Lemma
> \ref{lemma:stream-formula-new} to determine the source variables `w_μ` in terms of the
> sink variables `w_ν`, by treating them as streams using the positive endpoint.

The coefficients of the system are the sums `Q_{μν}` of the source article: the sum, over
all paths of the line graph from `μ` to `ν`, of the product of `frac(𝔞)|_p` along the
path.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace DOrientation

variable (Γ : DOrientation d G)

/-- The coefficient `Q_{ξν}` of the source article (`main.tex`, Section "Proofs"): the sum
over all paths of the line graph from `ξ` to `ν` of the product of `frac(𝔞)|_p` along the
path. -/
noncomputable def pathSum (p : V → Fin d → ℝ) (xi nu : CoreEdge d G) : ℝ :=
  ∑ L ∈ Γ.pathsFrom xi nu, Γ.pathFracEval p L

/-- The variant of `pathSum` for a source, using only the paths leaving it at its positive
endpoint (`main.tex`, Section "Proofs"). -/
noncomputable def pathSumPos (p : V → Fin d → ℝ) (mu nu : CoreEdge d G) : ℝ :=
  ∑ L ∈ Γ.pathsFromPos mu nu, Γ.pathFracEval p L

theorem sinkSum_eq_pathSum (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ) (xi : CoreEdge d G) :
    Γ.sinkSum p w xi = ∑ nu ∈ Γ.sinks, Γ.pathSum p xi nu * w (coreToEdge nu) := rfl

theorem sinkSumPos_eq_pathSumPos (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ)
    (mu : CoreEdge d G) :
    Γ.sinkSumPos p w mu = ∑ nu ∈ Γ.sinks, Γ.pathSumPos p mu nu * w (coreToEdge nu) := rfl

/-- The enumeration `μ_1, …, μ_k` of the sources of `Γ`, used to write the source
constraint equations as a linear system. -/
noncomputable def sourceEnum : Fin (#Γ.sources) → CoreEdge d G := fun i =>
  ((Γ.sources.equivFin).symm i : CoreEdge d G)

theorem sinkEnum_mem (j : Fin (#Γ.sinks)) : Γ.sinkEnum j ∈ Γ.sinks :=
  ((Γ.sinks.equivFin).symm j).2

theorem sourceEnum_mem (i : Fin (#Γ.sources)) : Γ.sourceEnum i ∈ Γ.sources :=
  ((Γ.sources.equivFin).symm i).2

theorem sinkEnum_injective : Function.Injective Γ.sinkEnum := by
  intro i j hij
  have : ((Γ.sinks.equivFin).symm i) = ((Γ.sinks.equivFin).symm j) := Subtype.ext hij
  simpa using this

theorem sourceEnum_injective : Function.Injective Γ.sourceEnum := by
  intro i j hij
  have : ((Γ.sources.equivFin).symm i) = ((Γ.sources.equivFin).symm j) := Subtype.ext hij
  simpa using this

theorem exists_sinkEnum_eq {nu : CoreEdge d G} (h : nu ∈ Γ.sinks) :
    ∃ j, Γ.sinkEnum j = nu := by
  refine ⟨Γ.sinks.equivFin ⟨nu, h⟩, ?_⟩
  simp [sinkEnum]

theorem exists_sourceEnum_eq {mu : CoreEdge d G} (h : mu ∈ Γ.sources) :
    ∃ i, Γ.sourceEnum i = mu := by
  refine ⟨Γ.sources.equivFin ⟨mu, h⟩, ?_⟩
  simp [sourceEnum]

theorem sum_sinks (f : CoreEdge d G → ℝ) :
    ∑ nu ∈ Γ.sinks, f nu = ∑ j, f (Γ.sinkEnum j) := by
  classical
  rw [← Finset.sum_coe_sort Γ.sinks f]
  exact (Equiv.sum_comp (Γ.sinks.equivFin).symm (fun x : {x // x ∈ Γ.sinks} => f (x : _))).symm

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem sum_sources (f : CoreEdge d G → ℝ) :
    ∑ mu ∈ Γ.sources, f mu = ∑ i, f (Γ.sourceEnum i) := by
  classical
  rw [← Finset.sum_coe_sort Γ.sources f]
  exact (Equiv.sum_comp (Γ.sources.equivFin).symm
    (fun x : {x // x ∈ Γ.sources} => f (x : _))).symm

/-- The **`p,Γ`-equations** of the source article (`main.tex`, Section "Proofs"): the
desert coordinates vanish, the stream coordinates are given by the stream formula, the
source coordinates are given by the stream formula applied *from their positive
endpoint*, and the source constraint equations hold.

As the source article stresses, for a source the stream formula must be applied using
only the paths leaving it at its positive endpoint: the sum over *all* paths leaving a
source is the difference of the two sums (the arrows leaving a source at its negative
endpoint have a blue, i.e. negative, up-weight), and this difference is exactly what the
source constraint equations set to zero. -/
def IsPGammaSolution (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ) : Prop :=
  (∀ e : OrientedEdge G, IsDesertEdge d G e.1.1 e.1.2 → w e = 0) ∧
    (∀ xi : CoreEdge d G, Γ.IsStream xi.1.1 xi.1.2 →
      w (coreToEdge xi)
        = ∑ nu ∈ Γ.sinks, (∑ L ∈ Γ.pathsFrom xi nu, Γ.pathFracEval p L) * w (coreToEdge nu)) ∧
    (∀ mu : CoreEdge d G, Γ.IsSource mu.1.1 mu.1.2 →
      w (coreToEdge mu)
        = ∑ nu ∈ Γ.sinks,
            (∑ L ∈ Γ.pathsFromPos mu nu, Γ.pathFracEval p L) * w (coreToEdge nu)) ∧
    (∀ mu : CoreEdge d G, Γ.IsSource mu.1.1 mu.1.2 →
      ∑ nu ∈ Γ.sinks, (∑ L ∈ Γ.pathsFrom mu nu, Γ.pathFracEval p L) * w (coreToEdge nu) = 0)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Every node of the line graph is a source, a stream or a sink. -/
theorem coreEdge_trichotomy (xi : CoreEdge d G) :
    Γ.IsSource xi.1.1 xi.1.2 ∨ Γ.IsStream xi.1.1 xi.1.2 ∨ Γ.IsSink xi.1.1 xi.1.2 := by
  by_cases hsrc : Γ.IsSource xi.1.1 xi.1.2
  · exact Or.inl hsrc
  · by_cases hsink : Γ.IsSink xi.1.1 xi.1.2
    · exact Or.inr (Or.inr hsink)
    · exact Or.inr (Or.inl (Γ.isStream_of_not_isSource_of_not_isSink hsrc hsink))

omit [DecidableEq V] in
theorem coreToEdge_mk (e : OrientedEdge G) (hnd : nonDesert d G e.1.1 e.1.2) :
    coreToEdge (⟨e.1, e.2.1, hnd⟩ : CoreEdge d G) = e := rfl

/-- **A solution of the `p,Γ`-equations all of whose sink coordinates vanish is zero.**
Every coordinate is determined by the sink coordinates through the stream formula
(`main.tex`, Section "Proofs"). -/
theorem eq_zero_of_isPGammaSolution_of_sinks_eq_zero (p : V → Fin d → ℝ)
    (w : OrientedEdge G → ℝ) (hw : Γ.IsPGammaSolution p w)
    (hz : ∀ nu ∈ Γ.sinks, w (coreToEdge nu) = 0) : w = 0 := by
  classical
  obtain ⟨hdes, hstream, hsrcpos, -⟩ := hw
  funext e
  by_cases hnd : nonDesert d G e.1.1 e.1.2
  · set xi : CoreEdge d G := ⟨e.1, e.2.1, hnd⟩ with hxi
    have he : e = coreToEdge xi := (coreToEdge_mk e hnd).symm
    rcases Γ.coreEdge_trichotomy xi with hsrc | hstr | hsink
    · rw [he, hsrcpos xi hsrc]
      refine Finset.sum_eq_zero (fun nu hnu => ?_)
      rw [hz nu hnu, mul_zero]
    · rw [he, hstream xi hstr]
      refine Finset.sum_eq_zero (fun nu hnu => ?_)
      rw [hz nu hnu, mul_zero]
    · rw [he]
      exact hz xi (by simp only [DOrientation.sinks, mem_filter, mem_univ, true_and]; exact hsink)
  · exact hdes e ⟨e.2.2, hnd⟩

/-- The weight function reconstructed from a vector of sink coordinates: the desert
coordinates vanish, and every other coordinate is given by the stream formula, applied to
a source from its positive endpoint (`main.tex`, Section "Proofs"). -/
noncomputable def ofSinkVector (p : V → Fin d → ℝ) (x : Fin (#Γ.sinks) → ℝ) :
    OrientedEdge G → ℝ := fun e =>
  if hnd : nonDesert d G e.1.1 e.1.2 then
    (if Γ.IsSource e.1.1 e.1.2 then
        ∑ j, Γ.pathSumPos p (⟨e.1, e.2.1, hnd⟩ : CoreEdge d G) (Γ.sinkEnum j) * x j
      else ∑ j, Γ.pathSum p (⟨e.1, e.2.1, hnd⟩ : CoreEdge d G) (Γ.sinkEnum j) * x j)
  else 0

theorem ofSinkVector_coreToEdge (p : V → Fin d → ℝ) (x : Fin (#Γ.sinks) → ℝ)
    (xi : CoreEdge d G) :
    Γ.ofSinkVector p x (coreToEdge xi)
      = if Γ.IsSource xi.1.1 xi.1.2 then ∑ j, Γ.pathSumPos p xi (Γ.sinkEnum j) * x j
        else ∑ j, Γ.pathSum p xi (Γ.sinkEnum j) * x j := by
  rw [ofSinkVector,
    dif_pos (show nonDesert d G (coreToEdge xi).1.1 (coreToEdge xi).1.2 from xi.2.2)]
  rfl

theorem ofSinkVector_sinkEnum (p : V → Fin d → ℝ) (x : Fin (#Γ.sinks) → ℝ)
    (j0 : Fin (#Γ.sinks)) :
    Γ.ofSinkVector p x (coreToEdge (Γ.sinkEnum j0)) = x j0 := by
  classical
  have hsink : Γ.IsSink (Γ.sinkEnum j0).1.1 (Γ.sinkEnum j0).1.2 := by
    have := Γ.sinkEnum_mem j0
    simpa only [DOrientation.sinks, mem_filter, mem_univ, true_and] using this
  have hnsrc : ¬ Γ.IsSource (Γ.sinkEnum j0).1.1 (Γ.sinkEnum j0).1.2 := by
    rintro ⟨-, h1, -⟩
    exact hsink.2.1 h1
  rw [Γ.ofSinkVector_coreToEdge p x, if_neg hnsrc]
  rw [Finset.sum_eq_single j0]
  · rw [pathSum, Γ.sum_pathsFrom_of_isSink p hsink, if_pos rfl, one_mul]
  · intro j _ hj
    rw [pathSum, Γ.sum_pathsFrom_of_isSink p hsink,
      if_neg (fun hcon => hj (Γ.sinkEnum_injective hcon)), zero_mul]
  · intro h
    exact absurd (mem_univ j0) h

/-- **The `p,Γ`-equations have a nonzero solution exactly when the source constraint
equations have one** (`main.tex`, Section "Proofs", first sentences of the proof of Lemma
`lemma:balanced-equivalent-nonzero-solution`). The stream formula determines every
coordinate of a solution from its sink coordinates, so a solution is nonzero exactly when
its sink coordinates are, and the only remaining conditions on the sink coordinates are
the source constraint equations. -/
theorem exists_nonzero_pGammaSolution_iff (p : V → Fin d → ℝ) :
    (∃ w : OrientedEdge G → ℝ, w ≠ 0 ∧ Γ.IsPGammaSolution p w) ↔
      ∃ x : Fin (#Γ.sinks) → ℝ, x ≠ 0 ∧
        ∀ i : Fin (#Γ.sources), ∑ j, Γ.pathSum p (Γ.sourceEnum i) (Γ.sinkEnum j) * x j = 0 := by
  classical
  constructor
  · rintro ⟨w, hw0, hw⟩
    refine ⟨fun j => w (coreToEdge (Γ.sinkEnum j)), ?_, ?_⟩
    · intro hcon
      refine hw0 (Γ.eq_zero_of_isPGammaSolution_of_sinks_eq_zero p w hw ?_)
      intro nu hnu
      obtain ⟨j, rfl⟩ := Γ.exists_sinkEnum_eq hnu
      exact congrFun hcon j
    · intro i
      have hsrc : Γ.IsSource (Γ.sourceEnum i).1.1 (Γ.sourceEnum i).1.2 := by
        have := Γ.sourceEnum_mem i
        simpa only [DOrientation.sources, mem_filter, mem_univ, true_and] using this
      have h := hw.2.2.2 (Γ.sourceEnum i) hsrc
      rw [Γ.sum_sinks (fun nu => (∑ L ∈ Γ.pathsFrom (Γ.sourceEnum i) nu, Γ.pathFracEval p L)
        * w (coreToEdge nu))] at h
      exact h
  · rintro ⟨x, hx0, hx⟩
    obtain ⟨j0, hj0⟩ : ∃ j, x j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hx0 (funext hcon)
    refine ⟨Γ.ofSinkVector p x, ?_, ?_, ?_, ?_, ?_⟩
    · intro hcon
      refine hj0 ?_
      rw [← Γ.ofSinkVector_sinkEnum p x j0, hcon]
      rfl
    · intro e he
      rw [ofSinkVector, dif_neg he.2]
    · intro xi hxi
      have hnsrc : ¬ Γ.IsSource xi.1.1 xi.1.2 := Γ.not_isSource_of_isStream hxi
      rw [Γ.ofSinkVector_coreToEdge p x, if_neg hnsrc,
        Γ.sum_sinks (fun nu => (∑ L ∈ Γ.pathsFrom xi nu, Γ.pathFracEval p L)
          * Γ.ofSinkVector p x (coreToEdge nu))]
      exact Finset.sum_congr rfl (fun j _ => by rw [Γ.ofSinkVector_sinkEnum p x j]; rfl)
    · intro mu hmu
      rw [Γ.ofSinkVector_coreToEdge p x, if_pos hmu,
        Γ.sum_sinks (fun nu => (∑ L ∈ Γ.pathsFromPos mu nu, Γ.pathFracEval p L)
          * Γ.ofSinkVector p x (coreToEdge nu))]
      exact Finset.sum_congr rfl (fun j _ => by rw [Γ.ofSinkVector_sinkEnum p x j]; rfl)
    · intro mu hmu
      obtain ⟨i, rfl⟩ := Γ.exists_sourceEnum_eq
        (by simp only [DOrientation.sources, mem_filter, mem_univ, true_and]; exact hmu)
      rw [Γ.sum_sinks (fun nu => (∑ L ∈ Γ.pathsFrom (Γ.sourceEnum i) nu, Γ.pathFracEval p L)
        * Γ.ofSinkVector p x (coreToEdge nu))]
      rw [← hx i]
      exact Finset.sum_congr rfl (fun j _ => by rw [Γ.ofSinkVector_sinkEnum p x j]; rfl)

end DOrientation

end RigidityTableaux
