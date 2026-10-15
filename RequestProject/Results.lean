import RequestProject.Generic
import RequestProject.OrientationExists
import RequestProject.Multidegree
import RequestProject.RowSelection
import RequestProject.GenericEvaluation
import RequestProject.DesertStress
import RequestProject.StreamFormulaMain
import RequestProject.StressConverse
import RequestProject.SinkSystem
import RequestProject.MinorRank
import RequestProject.BalancingEval
import RequestProject.Straightening
import RequestProject.RedBlue

/-!
# The results of the source article

This file states (and, where possible, proves) the numbered results of the source
article `main.tex`:

* Lemma `lemma:remove-common-factors`;
* Lemma `lemma:stream-formula-new` and Lemma `lemma:source-constraint-equations-new`;
* Lemma `lemma:stress-system-equivalent-Gamma-system`,
  Lemma `lemma:balanced-equivalent-nonzero-solution`,
  Lemma `lemma:Gamma-equivalent-to-Gamma'`;
* Theorem `thm:balanced-equivalent-to-selfstress` and
  Corollary `cor:affine-Maxwell-infinitesimally-flexible`;
* Lemma `lemma:balancing-multihomogeneous-new`,
  Lemma `lemma:generic-evaluation-straightening-new`,
  Lemma `lemma:generic-geometric-balancing`,
  Lemma `lemma:generic-orientation-independent`;
* Theorem `thm:main-Maxwell-locally-flexible` and Corollary `cor:characterization`.

The two results quoted from the literature in the source article, namely the theorems of
Asimow and Roth (generic local rigidity is equivalent to infinitesimal rigidity) and the
existence of generic placements, are carried as explicit hypotheses where they are used,
rather than being assumed as axioms.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace DOrientation

variable (Γ : DOrientation d G)

/-- **Lemma `lemma:stream-formula-new` of the source article.** For an affinely
independent placement `p` and a self-stress `w`, the stress coordinate of a stream
`(i,j)` is determined by the sink coordinates:
`w_{ij} = ∑_ν (∑_{paths 𝒫 : ij → ν} ∏_{𝔞 ∈ 𝒫} frac(𝔞)|_p) w_ν`. -/
theorem lemma_stream_formula (p : V → Fin d → ℝ) (hp : AffinelyIndependentPlacement d p)
    (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w) (xi : CoreEdge d G)
    (hxi : Γ.IsStream xi.1.1 xi.1.2) :
    w (coreToEdge xi)
      = ∑ nu ∈ Γ.sinks, (∑ L ∈ Γ.pathsFrom xi nu, Γ.pathFracEval p L) * w (coreToEdge nu) := by
  obtain ⟨a, ha⟩ := Γ.exists_entersAt_of_isStream hxi
  exact Γ.selfStress_eq_sinkSum p hp w hw ha (Γ.not_isSource_of_isStream hxi)

/-- **Lemma `lemma:source-constraint-equations-new` of the source article.** For an
affinely independent placement `p` and a self-stress `w`, each source `μ` imposes the
constraint `∑_ν (∑_{paths 𝒫 : μ → ν} ∏_{𝔞 ∈ 𝒫} frac(𝔞)|_p) w_ν = 0` on the sink
coordinates. -/
theorem lemma_source_constraint_equations (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w)
    (mu : CoreEdge d G) (hmu : Γ.IsSource mu.1.1 mu.1.2) :
    ∑ nu ∈ Γ.sinks, (∑ L ∈ Γ.pathsFrom mu nu, Γ.pathFracEval p L) * w (coreToEdge nu) = 0 :=
  Γ.sinkSum_eq_zero_of_isSource p hp w hw hmu

/- The **`p,Γ`-equations** of the source article (`main.tex`, Section "Proofs") are
formalized as `DOrientation.IsPGammaSolution` in `RequestProject/SinkSystem.lean`, where
they are also organised as a linear system in the sink coordinates. -/

/-- **Lemma `lemma:stress-system-equivalent-Gamma-system` of the source article.** For an
affinely independent placement, the self-stress equations `wA = 0` are equivalent to the
`p,Γ`-equations. -/
theorem lemma_stress_system_equivalent_Gamma_system (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (w : OrientedEdge G → ℝ) :
    IsSelfStress p w ↔ Γ.IsPGammaSolution p w := by
  constructor
  · intro hw
    refine ⟨fun e he => selfStress_eq_zero_of_isDesertEdge p hp w hw e he,
      fun xi hxi => Γ.lemma_stream_formula p hp w hw xi hxi,
      fun mu hmu => Γ.selfStress_eq_sinkSumPos_of_isSource p hp w hw hmu,
      fun mu hmu => Γ.sinkSum_eq_zero_of_isSource p hp w hw hmu⟩
  · rintro ⟨hdes, hstream, hsrcpos, hsrc⟩
    exact Γ.isSelfStress_of_streamFormulas p hp w hdes hstream hsrcpos hsrc

/-- **Lemma `lemma:balanced-equivalent-nonzero-solution` of the source article.** For an
affinely independent placement, `Γ` is balanced at `p` if and only if the
`p,Γ`-equations have a nonzero solution. -/
theorem lemma_balanced_equivalent_nonzero_solution (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) :
    Γ.BalancedAt p ↔ ∃ w : OrientedEdge G → ℝ, w ≠ 0 ∧ Γ.IsPGammaSolution p w := by
  classical
  rw [Γ.exists_nonzero_pGammaSolution_iff p,
    exists_nonzero_kernel_iff_forall_det_eq_zero
      (fun i j => Γ.pathSum p (Γ.sourceEnum i) (Γ.sinkEnum j))]
  constructor
  · rintro ⟨-, hdisj⟩ r
    by_cases hinj : Function.Injective r
    · have hchoice : Γ.IsSourceChoice (fun i => Γ.sourceEnum (r i)) :=
        ⟨fun i i' hii => hinj (Γ.sourceEnum_injective hii), fun i => Γ.sourceEnum_mem _⟩
      have hle : #Γ.sinks ≤ #Γ.sources := by
        have := Fintype.card_le_of_injective r hinj
        simpa using this
      rcases hdisj with hlt | ⟨-, heval⟩
      · omega
      · have h0 := heval (fun i => Γ.sourceEnum (r i)) hchoice
        exact (Γ.evalAtPlacement_balancingCondition_eq_zero_iff hd p hp _ Γ.sinkEnum).1 h0
    · -- a repeated equation makes the minor vanish
      obtain ⟨i, i', hne, heq⟩ : ∃ i i', i ≠ i' ∧ r i = r i' := by
        by_contra hcon
        push_neg at hcon
        exact hinj (fun i i' h => by
          by_contra hne
          exact absurd h (hcon i i' hne))
      refine Matrix.det_zero_of_row_eq hne ?_
      funext j
      simp [heq]
  · intro hdet
    have hpos : 0 < #Γ.sinks := by
      rcases Nat.eq_zero_or_pos (#Γ.sinks) with hl | h
      · exfalso
        haveI hemp : IsEmpty (Fin (#Γ.sinks)) := by rw [hl]; infer_instance
        have h1 := hdet (fun j => (hemp.false j).elim)
        rw [Matrix.det_isEmpty] at h1
        exact one_ne_zero h1
      · exact h
    have hnd : HasNonDesertEdge (d := d) (G := G) := by
      obtain ⟨nu, hnu⟩ := Finset.card_pos.1 hpos
      have : Γ.IsSink nu.1.1 nu.1.2 := by
        simpa only [DOrientation.sinks, mem_filter, mem_univ, true_and] using hnu
      exact ⟨nu.1.1, nu.1.2, this.1⟩
    refine ⟨hnd, ?_⟩
    by_cases hlt : #Γ.sources < #Γ.sinks
    · exact Or.inl hlt
    · refine Or.inr ⟨by omega, ?_⟩
      intro mu hmu
      refine (Γ.evalAtPlacement_balancingCondition_eq_zero_iff hd p hp mu Γ.sinkEnum).2 ?_
      have hchoose : ∀ i, ∃ k, Γ.sourceEnum k = mu i := fun i =>
        Γ.exists_sourceEnum_eq (hmu.2 i)
      choose r hr using hchoose
      have := hdet r
      rw [show (Matrix.of fun i j => Γ.pathSum p (Γ.sourceEnum (r i)) (Γ.sinkEnum j))
          = (Matrix.of fun i j => Γ.pathSum p (mu i) (Γ.sinkEnum j)) by
        ext i j
        rw [Matrix.of_apply, Matrix.of_apply, hr i]] at this
      exact this

end DOrientation

/-- **Lemma `lemma:Gamma-equivalent-to-Gamma'` of the source article.** Being balanced at
an affinely independent placement `p` does not depend on the chosen `d`-orientation, so
`G` being balanced at `p` is well defined. -/
theorem lemma_Gamma_equivalent_to_Gamma' (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (Γ Γ' : DOrientation d G) :
    Γ.BalancedAt p ↔ Γ'.BalancedAt p := by
  have h : ∀ Γ₀ : DOrientation d G,
      Γ₀.BalancedAt p ↔ ∃ w : OrientedEdge G → ℝ, w ≠ 0 ∧ IsSelfStress p w := by
    intro Γ₀
    rw [Γ₀.lemma_balanced_equivalent_nonzero_solution hd p hp]
    constructor
    · rintro ⟨w, hw0, hw⟩
      exact ⟨w, hw0, (Γ₀.lemma_stress_system_equivalent_Gamma_system p hp w).2 hw⟩
    · rintro ⟨w, hw0, hw⟩
      exact ⟨w, hw0, (Γ₀.lemma_stress_system_equivalent_Gamma_system p hp w).1 hw⟩
  rw [h Γ, h Γ']

/-- **Theorem `thm:balanced-equivalent-to-selfstress` of the source article.** For an
affinely independent placement `p`, the graph `G` is balanced at `p` if and only if the
framework `(G,p)` has a nonzero self-stress. -/
theorem theorem_balanced_equivalent_to_selfstress (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) :
    BalancedAtPlacement d G p ↔ ∃ w : OrientedEdge G → ℝ, w ≠ 0 ∧ IsSelfStress p w := by
  have h : ∀ Γ₀ : DOrientation d G,
      Γ₀.BalancedAt p ↔ ∃ w : OrientedEdge G → ℝ, w ≠ 0 ∧ IsSelfStress p w := by
    intro Γ₀
    rw [Γ₀.lemma_balanced_equivalent_nonzero_solution hd p hp]
    constructor
    · rintro ⟨w, hw0, hw⟩
      exact ⟨w, hw0, (Γ₀.lemma_stress_system_equivalent_Gamma_system p hp w).2 hw⟩
    · rintro ⟨w, hw0, hw⟩
      exact ⟨w, hw0, (Γ₀.lemma_stress_system_equivalent_Gamma_system p hp w).1 hw⟩
  constructor
  · rintro ⟨Γ, hΓ⟩
    exact (h Γ).1 hΓ
  · intro hw
    obtain ⟨Γ⟩ := exists_dOrientation d G
    exact ⟨Γ, (h Γ).2 hw⟩

/-- **Corollary `cor:affine-Maxwell-infinitesimally-flexible` of the source article.** For
an affinely independent placement `p` of a graph with `|V| ≥ d` and
`|E| = d|V| - binom (d+1) 2`, the graph is balanced at `p` if and only if `(G,p)` is
infinitesimally flexible.

The hypothesis `|V| ≥ d` of the source article is kept for fidelity; the formal proof
turns out to use only the edge count, since the required lower bound on the dimension of
the space of infinitesimal flexes already follows from it. -/
theorem corollary_affine_Maxwell_infinitesimally_flexible (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) (hV : d ≤ Fintype.card V) (hM : MaxwellCount d G) :
    BalancedAtPlacement d G p ↔ InfinitesimallyFlexible (G := G) p := by
  rw [infinitesimallyFlexible_iff_exists_nonzero_selfStress hM p]
  exact theorem_balanced_equivalent_to_selfstress hd p hp

omit [Fintype V] [LinearOrder V] in
/-- Factoring a set of columns common to all tableaux of a multiset out of the
corresponding bracket polynomial. This is the computation behind Lemma
`lemma:remove-common-factors` of the source article (`main.tex`, Section "Proofs"). -/
theorem multisetEval_common_factor {n : ℕ} {R : Type*} [CommRing R] (M : Fin n → V → R)
    (m : Multiset (Tableau n V)) (common : Multiset (Column n V))
    (hcommon : ∀ T ∈ m, common ≤ T.cols) :
    multisetEval M m
      = (common.map (bracketEval M)).prod
        * multisetEval M (m.map (fun T => (⟨T.red, T.cols - common⟩ : Tableau n V))) := by
  unfold multisetEval
  rw [Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro T hT
  obtain ⟨X, hX⟩ : ∃ X, T.cols = common + X :=
    ⟨T.cols - common, (add_tsub_cancel_of_le (hcommon T hT)).symm⟩
  simp only [Function.comp_apply, tableauEval, hX, Multiset.map_add, Multiset.prod_add,
    Tableau.sign, add_tsub_cancel_left]
  ring

omit [Fintype V] [LinearOrder V] in
/-- The bracket of a column with pairwise distinct entries is a nonzero polynomial in the
entries of the generic matrix. This is why the common columns of Lemma
`lemma:remove-common-factors` of the source article may be cancelled. -/
theorem bracketEval_genericMatrix_ne_zero {n : ℕ} (c : Column n V)
    (hc : Function.Injective c) : bracketEval (genericMatrix n V) c ≠ 0 := by
  intro h
  have h2 := congrArg
    (MvPolynomial.eval (fun x : Fin n × V => if x.2 = c x.1 then (1 : ℚ) else 0)) h
  rw [bracketEval, RingHom.map_det] at h2
  have hone :
      (MvPolynomial.eval (fun x : Fin n × V => if x.2 = c x.1 then (1 : ℚ) else 0)).mapMatrix
        (Matrix.of fun i j : Fin n => genericMatrix n V i (c j)) = 1 := by
    ext i j
    simp [genericMatrix, Matrix.one_apply, hc.eq_iff, eq_comm]
  rw [hone] at h2
  simp at h2

omit [Fintype V] in
/-- Removing from every tableau of a multiset a common set of columns with pairwise
distinct entries does not change whether the bracket polynomial straightens to zero
(`main.tex`, Lemma `lemma:remove-common-factors`). -/
theorem straightensToZero_iff_removeCommon {n : ℕ} (m : Multiset (Tableau n V))
    (common : Multiset (Column n V)) (hstrict : ∀ c ∈ common, StrictMono c)
    (hcommon : ∀ T ∈ m, common ≤ T.cols) :
    StraightensToZero m ↔
      StraightensToZero (m.map (fun T => (⟨T.red, T.cols - common⟩ : Tableau n V))) := by
  unfold StraightensToZero
  rw [multisetEval_common_factor (genericMatrix n V) m common hcommon]
  have hne : (common.map (bracketEval (genericMatrix n V))).prod ≠ 0 := by
    refine Multiset.prod_ne_zero ?_
    intro hmem
    obtain ⟨c, hc, hc0⟩ := Multiset.mem_map.mp hmem
    exact bracketEval_genericMatrix_ne_zero c (hstrict c hc).injective hc0
  simp [mul_eq_zero, hne]

/-- **Lemma `lemma:remove-common-factors` of the source article.** If every tableau of a
balancing condition contains a common set of columns (already permuted into strictly
increasing order, with colours adjusted), then the balancing condition contains each
semistandard tableau in equal amounts red and blue if and only if the reduced multiset,
with the common columns removed, does. -/
theorem lemma_remove_common_factors {n : ℕ} (hn : 0 < n) (m : Multiset (Tableau n V))
    (common : Multiset (Column n V)) (hstrict : ∀ c ∈ common, StrictMono c)
    (hcommon : ∀ T ∈ m, common ≤ T.cols)
    (m' mred' : Multiset (Tableau n V))
    (hm' : ReducesTo m m') (hss' : ∀ T ∈ m', IsSemistandard T)
    (hred : ReducesTo (m.map (fun T => (⟨T.red, T.cols - common⟩ : Tableau n V))) mred')
    (hssred : ∀ T ∈ mred', IsSemistandard T) :
    RedBlueBalanced m' ↔ RedBlueBalanced mred' := by
  rw [lemma_red_blue_equiv_straighten_to_zero hn m m' hm' hss',
    lemma_red_blue_equiv_straighten_to_zero hn _ mred' hred hssred]
  exact straightensToZero_iff_removeCommon m common hstrict hcommon

omit [DecidableRel G.Adj] in
/-- **Lemma `lemma:balancing-multihomogeneous-new` of the source article.** Every
balancing condition is multi-homogeneous in the vertices of `G`. As in the source
article, the dimension `d` is a positive integer. The hypothesis that `μ` is a choice of
sources, which the source article includes in the statement, turns out not to be needed
for the multidegree computation; it is kept here to match the statement of the article. -/
theorem lemma_balancing_multihomogeneous (hd : 0 < d) (Γ : DOrientation d G)
    (mu : Fin (#Γ.sinks) → CoreEdge d G) (hmu : Γ.IsSourceChoice mu) :
    MultiHomogeneous (Γ.balancingCondition mu Γ.sinkEnum) := by
  classical
  intro T hT T' hT' v
  simp only [DOrientation.balancingCondition, Multiset.mem_map] at hT hT'
  obtain ⟨P, hP, rfl⟩ := hT
  obtain ⟨P', hP', rfl⟩ := hT'
  have h1 := Γ.systemWeightDegree_eq hd mu Γ.sinkEnum P (Finset.mem_val.mp hP) v
  have h2 := Γ.systemWeightDegree_eq hd mu Γ.sinkEnum P' (Finset.mem_val.mp hP') v
  omega

/-- **Lemma `lemma:generic-evaluation-straightening-new` of the source article.** A
bracket polynomial which is multi-homogeneous in the vertices of `G` evaluates to zero at
a generic placement if and only if it straightens to zero. -/
theorem lemma_generic_evaluation_straightening (m : Multiset (Tableau (d + 1) V))
    (hm : MultiHomogeneous m) (p : V → Fin d → ℝ) (hp : GenericPlacement d p) :
    evalAtPlacement p m = 0 ↔ StraightensToZero m :=
  ⟨straightensToZero_of_evalAtPlacement_zero m hm p hp,
    evalAtPlacement_eq_zero_of_straightensToZero p m⟩

omit [DecidableRel G.Adj] in
/-- **Lemma `lemma:generic-geometric-balancing` of the source article.** At a generic
placement `p`, a `d`-orientation `Γ` is balanced if and only if it is balanced at `p`. -/
theorem lemma_generic_geometric_balancing (hd : 0 < d) (Γ : DOrientation d G)
    (p : V → Fin d → ℝ) (hp : GenericPlacement d p) :
    Γ.Balanced ↔ Γ.BalancedAt p := by
  unfold DOrientation.Balanced DOrientation.BalancedAt
  constructor
  · rintro ⟨hnd, h | ⟨hle, h⟩⟩
    · exact ⟨hnd, Or.inl h⟩
    · refine ⟨hnd, Or.inr ⟨hle, ?_⟩⟩
      intro mu hmu
      obtain ⟨m', hred, hss, hrb⟩ := h mu hmu
      have hstr : StraightensToZero (Γ.balancingCondition mu Γ.sinkEnum) :=
        (lemma_red_blue_equiv_straighten_to_zero (Nat.succ_pos d) _ m' hred hss).1 hrb
      exact (lemma_generic_evaluation_straightening _
        (lemma_balancing_multihomogeneous hd Γ mu hmu) p hp).2 hstr
  · rintro ⟨hnd, h | ⟨hle, h⟩⟩
    · exact ⟨hnd, Or.inl h⟩
    · refine ⟨hnd, Or.inr ⟨hle, ?_⟩⟩
      intro mu hmu
      have hstr := (lemma_generic_evaluation_straightening _
        (lemma_balancing_multihomogeneous hd Γ mu hmu) p hp).1 (h mu hmu)
      obtain ⟨m', hred, hss⟩ :=
        lemma_semistandard_tableaux_span (Nat.succ_pos d) (Γ.balancingCondition mu Γ.sinkEnum)
      exact ⟨m', hred, hss, (lemma_red_blue_equiv_straighten_to_zero (Nat.succ_pos d) _ m' hred hss).2 hstr⟩

/-- **Lemma `lemma:generic-orientation-independent` of the source article.** Being
balanced does not depend on the chosen `d`-orientation, so `G` being `d`-balanced is well
defined. This uses the existence of a generic placement. -/
theorem lemma_generic_orientation_independent (hd : 0 < d)
    (hgen : ∃ p : V → Fin d → ℝ, GenericPlacement d p) (Γ Γ' : DOrientation d G) :
    Γ.Balanced ↔ Γ'.Balanced := by
  obtain ⟨p, hp⟩ := hgen
  rw [lemma_generic_geometric_balancing hd Γ p hp, lemma_generic_geometric_balancing hd Γ' p hp]
  exact lemma_Gamma_equivalent_to_Gamma' hd p (affinelyIndependentPlacement_of_generic p hp) Γ Γ'

/-- **Theorem `thm:main-Maxwell-locally-flexible` of the source article.** Let `G` have
`|V| ≥ d` and `|E| = d|V| - binom (d+1) 2`. Then `G` is `d`-balanced if and only if `G` is
generically locally flexible in `ℝ^d`.

The equivalence of generic local flexibility and infinitesimal flexibility, which the
source article quotes from Asimow and Roth, is carried here as the hypothesis `hAR`; the
existence of generic placements is the hypothesis `hgen`. -/
theorem theorem_main_Maxwell_locally_flexible
    (hAR : ∀ p : V → Fin d → ℝ, GenericPlacement d p →
      (LocallyFlexible G p ↔ InfinitesimallyFlexible (G := G) p))
    (hgen : ∃ p : V → Fin d → ℝ, GenericPlacement d p) (hd : 0 < d)
    (hV : d ≤ Fintype.card V) (hM : MaxwellCount d G) :
    IsDBalanced d G ↔ GenericallyLocallyFlexible d G := by
  have key : ∀ p : V → Fin d → ℝ, GenericPlacement d p →
      (IsDBalanced d G ↔ LocallyFlexible G p) := by
    intro p hp
    have hpa : AffinelyIndependentPlacement d p := affinelyIndependentPlacement_of_generic p hp
    have hbal : IsDBalanced d G ↔ BalancedAtPlacement d G p := by
      constructor
      · rintro ⟨Γ, hΓ⟩
        exact ⟨Γ, (lemma_generic_geometric_balancing hd Γ p hp).1 hΓ⟩
      · rintro ⟨Γ, hΓ⟩
        exact ⟨Γ, (lemma_generic_geometric_balancing hd Γ p hp).2 hΓ⟩
    rw [hbal, corollary_affine_Maxwell_infinitesimally_flexible hd p hpa hV hM, hAR p hp]
  constructor
  · intro hb p hp
    exact (key p hp).1 hb
  · intro hflex
    obtain ⟨p, hp⟩ := hgen
    exact (key p hp).2 (hflex p hp)

/-- **Corollary `cor:characterization` of the source article.** Let `G` have `|V| ≥ d` and
`m = d|V| - binom (d+1) 2`. Then `G` is generically rigid in `ℝ^d` if and only if `G`
contains a spanning `m`-edge subgraph that is not `d`-balanced. -/
theorem corollary_characterization
    (hAR : ∀ (H : SimpleGraph V) (p : V → Fin d → ℝ), GenericPlacement d p →
      (LocallyFlexible H p ↔ InfinitesimallyFlexible (G := H) p))
    (hgen : ∃ p : V → Fin d → ℝ, GenericPlacement d p) (hd : 0 < d)
    (hV : d ≤ Fintype.card V) :
    GenericallyRigid d G ↔
      ∃ H : SimpleGraph V, H ≤ G ∧ MaxwellCount d H ∧ ¬ IsDBalanced d H := by
  constructor
  · intro hrigid
    obtain ⟨p, hp⟩ := hgen
    have hpa : AffinelyIndependentPlacement d p := affinelyIndependentPlacement_of_generic p hp
    have hrig : InfinitesimallyRigid (G := G) p := by
      by_contra hflex
      exact hrigid p hp ((hAR G p hp).2 hflex)
    obtain ⟨H, hHG, hM, hns⟩ := exists_maxwell_subgraph_no_selfstress p hrig
    refine ⟨H, hHG, hM, ?_⟩
    rintro ⟨Γ, hΓ⟩
    exact hns ((theorem_balanced_equivalent_to_selfstress (G := H) hd p hpa).1
      ⟨Γ, (lemma_generic_geometric_balancing hd Γ p hp).1 hΓ⟩)
  · rintro ⟨H, hHG, hM, hnb⟩ p hp hflex
    have hpa : AffinelyIndependentPlacement d p := affinelyIndependentPlacement_of_generic p hp
    have hns : ¬ ∃ w : OrientedEdge H → ℝ, w ≠ 0 ∧ IsSelfStress p w := by
      intro hw
      obtain ⟨Γ, hΓ⟩ := (theorem_balanced_equivalent_to_selfstress (G := H) hd p hpa).2 hw
      exact hnb ⟨Γ, (lemma_generic_geometric_balancing hd Γ p hp).2 hΓ⟩
    have hHrig : InfinitesimallyRigid (G := H) p := by
      by_contra hf
      exact hns ((infinitesimallyFlexible_iff_exists_nonzero_selfStress hM p).1 hf)
    have hle : Module.finrank ℝ (infFlexes (G := G) p) ≤ Nat.choose (d + 1) 2 := by
      rw [← hHrig]
      exact Submodule.finrank_mono (infFlexes_mono hHG p)
    have hge := choose_two_le_finrank_infFlexes (G := G) p hd hpa hV
    exact ((hAR G p hp).1 hflex) (le_antisymm hle hge)

end RigidityTableaux
