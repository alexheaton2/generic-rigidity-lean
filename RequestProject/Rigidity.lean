import Mathlib

/-!
# Bar-joint frameworks: placements, self-stresses and infinitesimal rigidity

This file formalizes the geometric set-up of the source article
(`main.tex`, Section "Geometric results" and Section "Proofs"):

* placements `p : V → ℝ^d` of a finite simple graph `G = (V,E)`;
* **affinely independent** placements ("any set of at most `d+1` vertices are affinely
  independent");
* **generic** placements (coordinates algebraically independent over `ℚ`);
* the edge vectors `e_{ij} = p_j - p_i`, the **vertex equations**
  `∑_j w_{ij} e_{ij} = 0`, and hence the **self-stress equations** `wA = 0`;
* the coefficient matrix `A` of the self-stress equations, viewed as the linear
  **rigidity map**, and **infinitesimal rigidity / flexibility**
  (`dim right ker A = binom (d+1) 2`);
* continuous flexes, used to state generic local flexibility.

The main result proved here is the linear-algebra content of
Corollary `cor:affine-Maxwell-infinitesimally-flexible` of the source article:
under Maxwell's edge count `|E| = d|V| - binom (d+1) 2`, a framework is
infinitesimally flexible if and only if it carries a nonzero self-stress.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The set of edges of `G`, presented as ordered pairs `(i,j)` with `i < j`.

This is the index set used for the tuple `w = (w_{ij})` of stress coordinates in
the source article (`main.tex`, Section "Geometric results": *"Order the edges
forming a tuple `w = (w_{ij})`"*). -/
abbrev OrientedEdge (G : SimpleGraph V) [DecidableRel G.Adj] : Type _ :=
  {e : V × V // e.1 < e.2 ∧ G.Adj e.1 e.2}

omit [DecidableEq V] in
/-- The number of ordered representatives `(i,j)`, `i < j`, of edges of `G` is the
number `|E|` of edges of `G`. -/
theorem card_orientedEdge (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (OrientedEdge G) = #G.edgeFinset := by
  classical
  rw [show Fintype.card (OrientedEdge G)
        = Fintype.card {e : V × V // e.1 < e.2 ∧ G.Adj e.1 e.2} from rfl,
    Fintype.card_subtype]
  refine Finset.card_bij (fun e _ => s(e.1, e.2)) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    simpa using ha.2
  · intro a ha b hb hab
    simp only [mem_filter, mem_univ, true_and] at ha hb
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd (h1 ▸ h2 ▸ ha.1) (by simpa using asymm hb.1)
  · intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e with
    | _ i j =>
      have hadj : G.Adj i j := by simpa using he
      rcases lt_trichotomy i j with h | h | h
      · have hmem : (i, j) ∈ univ.filter (fun e : V × V => e.1 < e.2 ∧ G.Adj e.1 e.2) := by
          simp only [mem_filter, mem_univ, true_and]; exact ⟨h, hadj⟩
        exact ⟨(i, j), hmem, rfl⟩
      · exact absurd (h ▸ hadj) (SimpleGraph.irrefl G)
      · have hmem : (j, i) ∈ univ.filter (fun e : V × V => e.1 < e.2 ∧ G.Adj e.1 e.2) := by
          simp only [mem_filter, mem_univ, true_and]; exact ⟨h, hadj.symm⟩
        exact ⟨(j, i), hmem, Sym2.eq_swap⟩

variable {d : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The **edge vector** `e_{ij} = p_j - p_i` of the source article
(`main.tex`, Section "Geometric results"). -/
def edgeVector (p : V → Fin d → ℝ) (i j : V) : Fin d → ℝ := fun k => p j k - p i k

/-- A placement `p : V → ℝ^d` is **affinely independent** if any set of at most `d+1`
vertices is affinely independent (`main.tex`, Section "Geometric results" and
Section "Proofs"). -/
def AffinelyIndependentPlacement (d : ℕ) (p : V → Fin d → ℝ) : Prop :=
  ∀ s : Finset V, s.card ≤ d + 1 → AffineIndependent ℝ (fun i : (s : Set V) => (p i : Fin d → ℝ))

/-- A placement is **generic** when its coordinates are algebraically independent over `ℚ`
(`main.tex`, Introduction: local rigidity "is independent of the coordinates of the
vertices, provided they are algebraically independent over `ℚ`"). -/
def GenericPlacement (d : ℕ) (p : V → Fin d → ℝ) : Prop :=
  AlgebraicIndependent ℚ (fun ik : V × Fin d => p ik.1 ik.2)

/-- The symmetric extension `w_{ij} = w_{ji}` of a tuple of stress coordinates indexed by
the edges of `G`, extended by `0` on non-edges. This implements the convention
`w_{ij} = w_{ji}` of the source article (`main.tex`, Section "Geometric results"). -/
noncomputable def stressVal (w : OrientedEdge G → ℝ) (i j : V) : ℝ := by
  classical
  exact if h : i < j ∧ G.Adj i j then w ⟨(i, j), h⟩
    else if h' : j < i ∧ G.Adj j i then w ⟨(j, i), h'⟩ else 0

omit [Fintype V] [DecidableEq V] in
/-- The stress coordinates are symmetric: `w_{ij} = w_{ji}`. -/
theorem stressVal_symm (w : OrientedEdge G → ℝ) (i j : V) :
    stressVal w i j = stressVal w j i := by
  classical
  unfold stressVal
  by_cases h : i < j ∧ G.Adj i j
  · have h1 : ¬ (j < i ∧ G.Adj j i) := fun hc => absurd h.1 (asymm hc.1)
    rw [dif_pos h, dif_neg h1, dif_pos h]
  · by_cases h' : j < i ∧ G.Adj j i
    · rw [dif_neg h, dif_pos h', dif_pos h']
    · rw [dif_neg h, dif_neg h', dif_neg h', dif_neg h]

omit [Fintype V] [DecidableEq V] in
/-- `w_{ij} = 0` for non-adjacent `i, j`. -/
theorem stressVal_eq_zero_of_not_adj (w : OrientedEdge G → ℝ) {i j : V} (h : ¬ G.Adj i j) :
    stressVal w i j = 0 := by
  classical
  unfold stressVal
  have h' : ¬ G.Adj j i := fun hc => h hc.symm
  simp [h, h']

/-- A tuple `w = (w_{ij})` is a **self-stress** of the framework `(G, p)` if it satisfies
all vertex equations `∑_{j : (i,j) ∈ E} w_{ij} e_{ij} = 0`, i.e. the self-stress
equations `wA = 0` of the source article (`main.tex`, Section "Geometric results"
and Section "Proofs"). -/
def IsSelfStress (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ) : Prop :=
  ∀ i : V, ∀ k : Fin d, ∑ j : V, stressVal w i j * edgeVector p i j k = 0

/-- The **rigidity map** of the framework `(G,p)`: the linear map whose matrix is the
coefficient matrix `A` of the self-stress equations of the source article
(`main.tex`, Section "Geometric results"). It sends an assignment `q` of velocity
vectors to the vertices to the tuple of numbers `⟪q_i - q_j, p_i - p_j⟫` indexed by
the edges; `w A = 0` says exactly that `w` annihilates its range. -/
noncomputable def rigidityMap (p : V → Fin d → ℝ) :
    (V → Fin d → ℝ) →ₗ[ℝ] (OrientedEdge G → ℝ) where
  toFun q := fun e => ∑ k : Fin d, (q e.1.1 k - q e.1.2 k) * (p e.1.1 k - p e.1.2 k)
  map_add' q q' := by
    funext e; simp only [Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext k; ring
  map_smul' c q := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    congr 1; funext k; ring

/-- The space of **infinitesimal flexes** of `(G,p)`: the right kernel of the coefficient
matrix `A` of the source article. -/
noncomputable def infFlexes (p : V → Fin d → ℝ) : Submodule ℝ (V → Fin d → ℝ) :=
  LinearMap.ker (rigidityMap (G := G) p)

/-- The framework `(G,p)` is **infinitesimally rigid** when
`dim right ker A = binom (d+1) 2` (`main.tex`, Section "Geometric results"). -/
def InfinitesimallyRigid (p : V → Fin d → ℝ) : Prop :=
  Module.finrank ℝ (infFlexes (G := G) p) = Nat.choose (d + 1) 2

/-- The framework `(G,p)` is **infinitesimally flexible** when it is not infinitesimally
rigid (`main.tex`, Section "Geometric results"). -/
def InfinitesimallyFlexible (p : V → Fin d → ℝ) : Prop :=
  ¬ InfinitesimallyRigid (G := G) p

/-- **Maxwell's edge count** `|E| = d|V| - binom (d+1) 2` of the source article
(`main.tex`, Introduction and Theorem `thm:main-Maxwell-locally-flexible`),
stated without natural-number subtraction. -/
def MaxwellCount (d : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  #G.edgeFinset + Nat.choose (d + 1) 2 = d * Fintype.card V

/-- The squared Euclidean distance between two points of `ℝ^d`, used to express that a
continuous motion preserves the lengths of the bars. -/
def sqdist (x y : Fin d → ℝ) : ℝ := ∑ k : Fin d, (x k - y k) ^ 2

/-- A **continuous flex** of the framework `(G,p)`: a continuous motion of the vertices
starting at `p`, keeping the lengths of all bars constant, but changing some
distance between two vertices — i.e. a continuous deformation which is not a rigid
body motion (`main.tex`, Introduction: *"Such a framework is said to be locally rigid
if its only continuous deformations are rigid body motions, and locally flexible
otherwise."*). -/
def IsFlex (G : SimpleGraph V) (p : V → Fin d → ℝ) (q : ℝ → V → Fin d → ℝ) : Prop :=
  Continuous q ∧ q 0 = p ∧
    (∀ t : ℝ, ∀ i j : V, G.Adj i j → sqdist (q t i) (q t j) = sqdist (p i) (p j)) ∧
    (∃ (t : ℝ) (i j : V), sqdist (q t i) (q t j) ≠ sqdist (p i) (p j))

/-- The framework `(G,p)` is **locally flexible** if it admits a continuous flex
(`main.tex`, Introduction). -/
def LocallyFlexible (G : SimpleGraph V) (p : V → Fin d → ℝ) : Prop :=
  ∃ q : ℝ → V → Fin d → ℝ, IsFlex G p q

/-- The graph `G` is **generically locally flexible in `ℝ^d`** if every generic placement
gives a locally flexible framework (`main.tex`, Introduction and Theorem
`thm:main-Maxwell-locally-flexible`). By the results of Asimow and Roth quoted in the
introduction of the source article, generic local flexibility is a property of the
graph alone. -/
def GenericallyLocallyFlexible (d : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ p : V → Fin d → ℝ, GenericPlacement d p → LocallyFlexible G p

/-! ### The linear algebra behind Corollary `cor:affine-Maxwell-infinitesimally-flexible` -/

omit [DecidableEq V] in
/-- Summing a symmetric function that vanishes on non-edges over the edges of `G`
(each edge counted once, as the ordered pair `(i,j)` with `i < j`) is the same as
summing over all ordered pairs of vertices and halving. -/
theorem sum_orientedEdge_eq_half_sum (f : V → V → ℝ) (hsymm : ∀ i j, f i j = f j i)
    (hzero : ∀ i j, ¬ G.Adj i j → f i j = 0) :
    ∑ e : OrientedEdge G, f e.1.1 e.1.2 = (1 / 2) * ∑ i : V, ∑ j : V, f i j := by
  classical
  have hdiag : ∀ i : V, f i i = 0 := fun i => hzero i i (G.irrefl)
  -- the sum over edges is a sum over the pairs `i < j`
  have h1 : ∑ e : OrientedEdge G, f e.1.1 e.1.2
      = ∑ x ∈ univ.filter (fun x : V × V => x.1 < x.2), f x.1 x.2 := by
    rw [show (∑ e : OrientedEdge G, f e.1.1 e.1.2)
        = ∑ x ∈ univ.filter (fun x : V × V => x.1 < x.2 ∧ G.Adj x.1 x.2), f x.1 x.2 from
      (Finset.sum_subtype (p := fun x : V × V => x.1 < x.2 ∧ G.Adj x.1 x.2) _
        (by intro x; simp) (fun x => f x.1 x.2)).symm]
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact hx.1
    intro x hx hx'
    simp only [mem_filter, mem_univ, true_and] at hx hx'
    exact hzero _ _ fun hadj => hx' ⟨hx, hadj⟩
  -- the sum over all ordered pairs splits into `i < j` and `j < i`, with equal parts
  have h2 : ∑ i : V, ∑ j : V, f i j
      = 2 * ∑ x ∈ univ.filter (fun x : V × V => x.1 < x.2), f x.1 x.2 := by
    have hprod : ∑ i : V, ∑ j : V, f i j = ∑ x ∈ (univ : Finset (V × V)), f x.1 x.2 := by
      rw [show (univ : Finset (V × V)) = (univ : Finset V) ×ˢ (univ : Finset V) from
        Finset.univ_product_univ.symm, Finset.sum_product']
    rw [hprod, ← Finset.sum_filter_add_sum_filter_not univ (fun x : V × V => x.1 < x.2)]
    have hswap : ∑ x ∈ univ.filter (fun x : V × V => ¬ x.1 < x.2), f x.1 x.2
        = ∑ x ∈ univ.filter (fun x : V × V => x.1 < x.2), f x.1 x.2 := by
      have hsub : ∑ x ∈ univ.filter (fun x : V × V => ¬ x.1 < x.2), f x.1 x.2
          = ∑ x ∈ univ.filter (fun x : V × V => x.2 < x.1), f x.1 x.2 := by
        refine (Finset.sum_subset ?_ ?_).symm
        · intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx ⊢
          exact asymm hx
        · intro x hx hx'
          simp only [mem_filter, mem_univ, true_and] at hx hx'
          have : x.1 = x.2 := le_antisymm (not_lt.mp hx') (not_lt.mp hx)
          rw [this]; exact hdiag _
      rw [hsub]
      refine Finset.sum_nbij' (fun x : V × V => (x.2, x.1)) (fun x : V × V => (x.2, x.1))
        ?_ ?_ ?_ ?_ ?_
      · intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact hx
      · intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact hx
      · intro x _; rfl
      · intro x _; rfl
      · intro x _
        exact hsymm x.1 x.2
    rw [hswap]; ring
  rw [h1, h2]; ring

omit [DecidableEq V] in
/-- The pairing between a tuple `w = (w_{ij})` of stress coordinates and the rigidity
map: this is the identity showing that `w A = 0` (the self-stress equations of
`main.tex`, Section "Geometric results") holds exactly when `w` annihilates the range
of the rigidity map, i.e. exactly when all vertex equations
`∑_j w_{ij} e_{ij} = 0` hold. -/
theorem sum_mul_rigidityMap (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ)
    (q : V → Fin d → ℝ) :
    ∑ e : OrientedEdge G, w e * rigidityMap p q e
      = - ∑ i : V, ∑ k : Fin d, q i k * (∑ j : V, stressVal w i j * edgeVector p i j k) := by
  classical
  set f : V → V → ℝ := fun i j =>
    stressVal w i j * ∑ k : Fin d, (q i k - q j k) * (p i k - p j k) with hf
  have hsymm : ∀ i j, f i j = f j i := by
    intro i j
    rw [hf]
    simp only
    rw [stressVal_symm w i j]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hzero : ∀ i j, ¬ G.Adj i j → f i j = 0 := by
    intro i j h
    rw [hf]
    simp [stressVal_eq_zero_of_not_adj w h]
  have hE : ∑ e : OrientedEdge G, w e * rigidityMap p q e
      = ∑ e : OrientedEdge G, f e.1.1 e.1.2 := by
    refine Finset.sum_congr rfl fun e _ => ?_
    have hval : stressVal w e.1.1 e.1.2 = w e := by
      unfold stressVal
      rw [dif_pos e.2]
    simp only [hf, hval, rigidityMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hE, sum_orientedEdge_eq_half_sum f hsymm hzero]
  -- expand the double sum
  have hexp : ∑ i : V, ∑ j : V, f i j
      = 2 * (- ∑ i : V, ∑ k : Fin d, q i k * (∑ j : V, stressVal w i j * edgeVector p i j k)) := by
    have hsplit : ∀ i j : V, f i j
        = (∑ k : Fin d, q i k * (stressVal w i j * (p i k - p j k)))
          - (∑ k : Fin d, q j k * (stressVal w i j * (p i k - p j k))) := by
      intro i j
      rw [hf]
      simp only
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hA : ∑ i : V, ∑ j : V, (∑ k : Fin d, q i k * (stressVal w i j * (p i k - p j k)))
        = - ∑ i : V, ∑ k : Fin d, q i k * (∑ j : V, stressVal w i j * edgeVector p i j k) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [edgeVector]
      ring
    have hB : ∑ i : V, ∑ j : V, (∑ k : Fin d, q j k * (stressVal w i j * (p i k - p j k)))
        = ∑ i : V, ∑ k : Fin d, q i k * (∑ j : V, stressVal w i j * edgeVector p i j k) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [stressVal_symm w j i]
      simp only [edgeVector]
    calc ∑ i : V, ∑ j : V, f i j
        = ∑ i : V, ∑ j : V, ((∑ k : Fin d, q i k * (stressVal w i j * (p i k - p j k)))
            - (∑ k : Fin d, q j k * (stressVal w i j * (p i k - p j k)))) := by
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
      _ = (∑ i : V, ∑ j : V, (∑ k : Fin d, q i k * (stressVal w i j * (p i k - p j k))))
            - (∑ i : V, ∑ j : V, (∑ k : Fin d, q j k * (stressVal w i j * (p i k - p j k)))) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_sub_distrib _ _
      _ = 2 * (- ∑ i : V, ∑ k : Fin d, q i k
              * (∑ j : V, stressVal w i j * edgeVector p i j k)) := by
          rw [hA, hB]; ring
  rw [hexp]; ring

/-- A tuple `w` is a self-stress of `(G,p)` exactly when it annihilates the range of the
rigidity map; this is the statement `w A = 0` of the source article
(`main.tex`, Section "Geometric results"). -/
theorem isSelfStress_iff (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ) :
    IsSelfStress p w ↔ ∀ q : V → Fin d → ℝ, ∑ e : OrientedEdge G, w e * rigidityMap p q e = 0 := by
  classical
  constructor
  · intro hw q
    rw [sum_mul_rigidityMap]
    simp only [neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
    rw [hw i k, mul_zero]
  · intro h i k
    have := h (fun i' k' => if i' = i ∧ k' = k then 1 else 0)
    rw [sum_mul_rigidityMap] at this
    have hinner : ∀ i' : V, ∑ k' : Fin d,
        (if i' = i ∧ k' = k then (1 : ℝ) else 0)
          * (∑ j : V, stressVal w i' j * edgeVector p i' j k')
        = if i' = i then ∑ j : V, stressVal w i j * edgeVector p i j k else 0 := by
      intro i'
      by_cases hi : i' = i
      · subst hi
        rw [Finset.sum_eq_single k]
        · simp
        · intro b _ hb; simp [hb]
        · intro hb; exact absurd (mem_univ k) hb
      · simp [hi]
    rw [Finset.sum_congr rfl fun i' _ => hinner i'] at this
    simpa using this

/-- The framework `(G,p)` carries a nonzero self-stress exactly when the rigidity map is
not surjective, i.e. when the rows of the matrix `A` of the source article are linearly
dependent (`main.tex`, Section "Geometric results"). -/
theorem exists_nonzero_selfStress_iff_not_surjective (p : V → Fin d → ℝ) :
    (∃ w : OrientedEdge G → ℝ, w ≠ 0 ∧ IsSelfStress p w) ↔
      ¬ Function.Surjective (rigidityMap (G := G) p) := by
  classical
  constructor
  · rintro ⟨w, hw0, hw⟩ hsurj
    obtain ⟨q, hq⟩ := hsurj w
    have h0 : ∑ e : OrientedEdge G, w e * w e = 0 := by
      have h := (isSelfStress_iff p w).1 hw q
      rwa [hq] at h
    have hz : ∀ e : OrientedEdge G, w e = 0 := by
      intro e
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun e (_ : e ∈ (univ : Finset (OrientedEdge G))) => mul_self_nonneg (w e))).1 h0 e
        (mem_univ e)
      exact mul_self_eq_zero.mp h
    exact hw0 (funext fun e => hz e)
  · intro hns
    have hlt : LinearMap.range (rigidityMap (G := G) p) < ⊤ :=
      lt_top_iff_ne_top.mpr (fun h => hns (LinearMap.range_eq_top.mp h))
    obtain ⟨f, hf0, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    refine ⟨fun e => f (fun j => if e = j then 1 else 0), ?_, ?_⟩
    · intro hzero
      apply hf0
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.pi_apply_eq_sum_univ f x]
      simp only [LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun e _ => ?_
      have hfe : f (fun j => if e = j then (1 : ℝ) else 0) = 0 := congrFun hzero e
      rw [hfe, smul_zero]
    · rw [isSelfStress_iff]
      intro q
      have hmem : rigidityMap (G := G) p q ∈ LinearMap.range (rigidityMap (G := G) p) :=
        LinearMap.mem_range_self _ q
      have hzero : f (rigidityMap (G := G) p q) = 0 := by
        have : f (rigidityMap (G := G) p q) ∈
            (LinearMap.range (rigidityMap (G := G) p)).map f := Submodule.mem_map_of_mem hmem
        rw [hfmap] at this
        simpa using this
      have expand := LinearMap.pi_apply_eq_sum_univ f (rigidityMap (G := G) p q)
      calc ∑ e : OrientedEdge G, (f fun j => if e = j then (1 : ℝ) else 0)
              * rigidityMap (G := G) p q e
          = ∑ e : OrientedEdge G, rigidityMap (G := G) p q e
              • (f fun j => if e = j then (1 : ℝ) else 0) :=
            Finset.sum_congr rfl fun e _ => by rw [smul_eq_mul, mul_comm]
        _ = f (rigidityMap (G := G) p q) := expand.symm
        _ = 0 := hzero

/-- **Corollary `cor:affine-Maxwell-infinitesimally-flexible` of the source article, linear
algebra part.** For a graph satisfying Maxwell's count `|E| = d|V| - binom (d+1) 2`, the
framework `(G,p)` is infinitesimally flexible if and only if it carries a nonzero
self-stress `w ≠ 0` with `wA = 0`. (This is the step in the proof of the corollary in
`main.tex`, Section "Proofs": the rank of `A` is at most the number of its rows, hence
`G` is infinitesimally flexible exactly when there exists a nonzero self-stress.) -/
theorem infinitesimallyFlexible_iff_exists_nonzero_selfStress
    (hM : MaxwellCount d G) (p : V → Fin d → ℝ) :
    InfinitesimallyFlexible (G := G) p ↔
      ∃ w : OrientedEdge G → ℝ, w ≠ 0 ∧ IsSelfStress p w := by
  classical
  rw [exists_nonzero_selfStress_iff_not_surjective]
  unfold InfinitesimallyFlexible InfinitesimallyRigid infFlexes
  constructor
  · intro hflex hsurj
    apply hflex
    have hrange : LinearMap.range (rigidityMap (G := G) p) = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hrk : Module.finrank ℝ (LinearMap.range (rigidityMap (G := G) p))
        = Fintype.card (OrientedEdge G) := by
      rw [hrange, finrank_top]
      simp [Module.finrank_fintype_fun_eq_card]
    have hdom : Module.finrank ℝ (V → Fin d → ℝ) = d * Fintype.card V := by
      rw [Module.finrank_pi_fintype ℝ]
      simp [Module.finrank_fintype_fun_eq_card, mul_comm]
    have hsum := LinearMap.finrank_range_add_finrank_ker (rigidityMap (G := G) p)
    have hcard : Fintype.card (OrientedEdge G) = #G.edgeFinset := card_orientedEdge G
    rw [hrk, hcard, hdom] at hsum
    unfold MaxwellCount at hM
    omega
  · intro hns hrig
    apply hns
    have hdom : Module.finrank ℝ (V → Fin d → ℝ) = d * Fintype.card V := by
      rw [Module.finrank_pi_fintype ℝ]
      simp [Module.finrank_fintype_fun_eq_card, mul_comm]
    have hsum := LinearMap.finrank_range_add_finrank_ker (rigidityMap (G := G) p)
    rw [hrig, hdom] at hsum
    have hcard : Fintype.card (OrientedEdge G) = #G.edgeFinset := card_orientedEdge G
    have hrk : Module.finrank ℝ (LinearMap.range (rigidityMap (G := G) p))
        = Fintype.card (OrientedEdge G) := by
      unfold MaxwellCount at hM
      omega
    have : LinearMap.range (rigidityMap (G := G) p) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hrk]
      simp [Module.finrank_fintype_fun_eq_card]
    exact LinearMap.range_eq_top.mp this

/-- The graph `G` is **generically rigid in `ℝ^d`** if some (equivalently, every) generic
placement gives a framework which is not locally flexible (`main.tex`,
Corollary `cor:characterization`). -/
def GenericallyRigid (d : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ p : V → Fin d → ℝ, GenericPlacement d p → ¬ LocallyFlexible G p

end RigidityTableaux
