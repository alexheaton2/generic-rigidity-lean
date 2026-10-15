import RequestProject.Orientation

/-!
# Multidegrees of weights, paths and balancing conditions

This file develops the vertex multidegree bookkeeping used in the proof of Lemma
`lemma:balancing-multihomogeneous-new` of the source article (`main.tex`, Subsection
"From geometric to combinatorial balancing"), namely:

* the multidegree of a product of tableaux is the sum of the multidegrees;
* for an arrow `𝔞 : ξ → η` of the `Γ`-oriented line graph,
  `deg 𝔲_𝔞 + deg ξ = deg 𝔡_𝔞 + deg η` (in the source article: `deg frac(𝔞) = deg η − deg ξ`);
* the same identity telescopes along paths and along path systems.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V}

/-! ### Multidegrees of products of tableaux -/

omit [Fintype V] [LinearOrder V] in
@[simp] theorem tableauDegree_mul {n : ℕ} (T T' : Tableau n V) (v : V) :
    tableauDegree (Tableau.mul T T') v = tableauDegree T v + tableauDegree T' v := by
  simp [tableauDegree, Tableau.mul]

omit [Fintype V] [LinearOrder V] in
@[simp] theorem tableauDegree_one {n : ℕ} (v : V) :
    tableauDegree (Tableau.one n V) v = 0 := by
  simp [tableauDegree, Tableau.one]

omit [Fintype V] [LinearOrder V] in
@[simp] theorem tableauDegree_neg {n : ℕ} (T : Tableau n V) (v : V) :
    tableauDegree (Tableau.neg T) v = tableauDegree T v := by
  simp [tableauDegree, Tableau.neg]

omit [Fintype V] [LinearOrder V] in
@[simp] theorem tableauDegree_smulSign {n : ℕ} (s : ℤˣ) (T : Tableau n V) (v : V) :
    tableauDegree (Tableau.smulSign s T) v = tableauDegree T v := by
  unfold Tableau.smulSign
  split <;> simp

omit [Fintype V] [LinearOrder V] in
theorem tableauDegree_listProd {n : ℕ} (L : List (Tableau n V)) (v : V) :
    tableauDegree (Tableau.listProd L) v = (L.map (fun T => tableauDegree T v)).sum := by
  induction L with
  | nil => simp [Tableau.listProd]
  | cons T L ih =>
    rw [show Tableau.listProd (T :: L) = Tableau.mul T (Tableau.listProd L) from rfl,
      tableauDegree_mul, ih]
    simp

/-! ### The multidegree of an edge and of the weights of an arrow -/

/-- The multidegree `deg (a,b) = ε_a + ε_b` of an edge of `G`, evaluated at the vertex `v`
(`main.tex`, Subsection "From geometric to combinatorial balancing"). -/
def edgeDegree (e : CoreEdge d G) (v : V) : ℕ :=
  (if e.1.1 = v then 1 else 0) + (if e.1.2 = v then 1 else 0)

namespace DOrientation

variable (Γ : DOrientation d G)

/-- The contribution of the entries `j_1, …, j_{d-1}` to the multidegree of a weight
column. -/
noncomputable def jDegree (a b v : V) : ℕ :=
  #(univ.filter (fun i : Fin (d + 1) =>
      (i : ℕ) + 2 ≤ d ∧ (Γ.incomingOthersList a b).getD i a = v))

/-- The multidegree of a weight column `[j_1 … j_{d-1} x y]`: the entries `j_1, …, j_{d-1}`
contribute `jDegree`, and the last two boxes contribute `ε_x + ε_y`. -/
theorem colDegree_weightColumn (hd : 0 < d) (a b x y v : V) :
    colDegree (Γ.weightColumn a b x y) v
      = Γ.jDegree a b v + (if x = v then 1 else 0) + (if y = v then 1 else 0) := by
  classical
  -- split the index set `Fin (d+1)` into the first `d-1` boxes, the box `d-1` and the box `d`
  have hsplit : (univ.filter (fun i : Fin (d + 1) => Γ.weightColumn a b x y i = v))
      = (univ.filter (fun i : Fin (d + 1) =>
            (i : ℕ) + 2 ≤ d ∧ (Γ.incomingOthersList a b).getD i a = v))
        ∪ ((univ.filter (fun i : Fin (d + 1) => (i : ℕ) + 1 = d ∧ x = v))
        ∪ (univ.filter (fun i : Fin (d + 1) => ¬ ((i : ℕ) + 2 ≤ d) ∧ ¬ ((i : ℕ) + 1 = d)
              ∧ y = v))) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union, weightColumn]
    by_cases h1 : (i : ℕ) + 2 ≤ d
    · have h2 : ¬ ((i : ℕ) + 1 = d) := by omega
      simp [h1, h2]
    · by_cases h2 : (i : ℕ) + 1 = d
      · simp [h1, h2]
      · simp [h1, h2]
  have hdisj1 : Disjoint (univ.filter (fun i : Fin (d + 1) =>
            (i : ℕ) + 2 ≤ d ∧ (Γ.incomingOthersList a b).getD i a = v))
      ((univ.filter (fun i : Fin (d + 1) => (i : ℕ) + 1 = d ∧ x = v))
        ∪ (univ.filter (fun i : Fin (d + 1) => ¬ ((i : ℕ) + 2 ≤ d) ∧ ¬ ((i : ℕ) + 1 = d)
              ∧ y = v))) := by
    simp only [Finset.disjoint_left, mem_filter, mem_univ, true_and, mem_union]
    rintro i ⟨hi, -⟩ (⟨h, -⟩ | ⟨h, -⟩) <;> omega
  have hdisj2 : Disjoint (univ.filter (fun i : Fin (d + 1) => (i : ℕ) + 1 = d ∧ x = v))
      (univ.filter (fun i : Fin (d + 1) => ¬ ((i : ℕ) + 2 ≤ d) ∧ ¬ ((i : ℕ) + 1 = d)
              ∧ y = v)) := by
    simp only [Finset.disjoint_left, mem_filter, mem_univ, true_and]
    rintro i ⟨hi, -⟩ ⟨-, h, -⟩
    exact h hi
  have hx : #(univ.filter (fun i : Fin (d + 1) => (i : ℕ) + 1 = d ∧ x = v))
      = if x = v then 1 else 0 := by
    by_cases hxv : x = v
    · have hset : (univ.filter (fun i : Fin (d + 1) => (i : ℕ) + 1 = d ∧ x = v))
          = {(⟨d - 1, by omega⟩ : Fin (d + 1))} := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · rintro ⟨h1, -⟩
          apply Fin.ext
          simp only
          omega
        · rintro rfl
          exact ⟨by simp only; omega, hxv⟩
      rw [hset, if_pos hxv, Finset.card_singleton]
    · simp [hxv]
  have hy : #(univ.filter (fun i : Fin (d + 1) => ¬ ((i : ℕ) + 2 ≤ d) ∧ ¬ ((i : ℕ) + 1 = d)
              ∧ y = v)) = if y = v then 1 else 0 := by
    by_cases hyv : y = v
    · have hset : (univ.filter (fun i : Fin (d + 1) => ¬ ((i : ℕ) + 2 ≤ d) ∧ ¬ ((i : ℕ) + 1 = d)
            ∧ y = v)) = {(⟨d, by omega⟩ : Fin (d + 1))} := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · rintro ⟨h1, h2, -⟩
          apply Fin.ext
          simp only
          omega
        · rintro rfl
          refine ⟨by simp only; omega, by simp only; omega, hyv⟩
      rw [hset, if_pos hyv, Finset.card_singleton]
    · simp [hyv]
  unfold colDegree
  rw [hsplit, Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2,
    hx, hy, jDegree, ← add_assoc]

/-- The key degree identity for an arrow `𝔞 : ξ → η` of the line graph:
`deg 𝔲_𝔞 + deg ξ = deg 𝔡_𝔞 + deg η`, which is the statement `deg frac(𝔞) = deg η − deg ξ`
in the proof of Lemma `lemma:balancing-multihomogeneous-new` of the source article. -/
theorem arrowDegree_telescope (hd : 0 < d) {xi eta : CoreEdge d G} (h : Γ.LArrow xi eta)
    (v : V) :
    tableauDegree (Γ.arrowUp xi eta) v + edgeDegree xi v
      = tableauDegree (Γ.arrowDown xi eta) v + edgeDegree eta v := by
  classical
  set a := sharedVertex xi eta with ha
  set b := otherEnd xi a with hb
  set c := otherEnd eta a with hc
  have hup : tableauDegree (Γ.arrowUp xi eta) v = colDegree (Γ.weightColumn a b a c) v := by
    simp [arrowUp, tableauDegree, ← ha, ← hb, ← hc]
  have hdown : tableauDegree (Γ.arrowDown xi eta) v = colDegree (Γ.weightColumn a b b a) v := by
    simp [arrowDown, tableauDegree, ← ha, ← hb]
  -- the endpoints of `ξ` are `a` and `b`, those of `η` are `a` and `c`
  have hxi : edgeDegree xi v = (if a = v then 1 else 0) + (if b = v then 1 else 0) := by
    unfold edgeDegree
    by_cases h1 : a = xi.1.1
    · have : b = xi.1.2 := by simp [hb, otherEnd, h1]
      rw [h1, this]
    · have ha2 : a = xi.1.2 := by
        simp only [ha, sharedVertex] at h1 ⊢
        by_cases hcase : xi.1.1 = eta.1.1 ∨ xi.1.1 = eta.1.2
        · exact absurd (by simp [hcase]) h1
        · simp [hcase]
      have hb2 : b = xi.1.1 := by simp [hb, otherEnd, ha2, (ne_of_lt xi.2.1).symm]
      rw [ha2, hb2, add_comm]
  have heta : edgeDegree eta v = (if a = v then 1 else 0) + (if c = v then 1 else 0) := by
    unfold edgeDegree
    have hmem : a = eta.1.1 ∨ a = eta.1.2 := h.2.1
    rcases hmem with h1 | h1
    · have : c = eta.1.2 := by simp [hc, otherEnd, ← h1]
      rw [← h1, this]
    · have hne : a ≠ eta.1.1 := by
        rw [h1]; exact (ne_of_lt eta.2.1).symm
      have : c = eta.1.1 := by simp [hc, otherEnd, hne]
      rw [← h1, this, add_comm]
  rw [hup, hdown, hxi, heta, Γ.colDegree_weightColumn hd a b a c v,
    Γ.colDegree_weightColumn hd a b b a v]
  ring

/-- Telescoping the degree identity along a path of the line graph: for a path with first
node `a` and last node `z`, `deg u(𝒫) + deg a = deg d(𝒫) + deg z` (`main.tex`, proof of
Lemma `lemma:balancing-multihomogeneous-new`: *"degrees telescope along any directed
path"*). -/
theorem pathDegree_telescope (hd : 0 < d) :
    ∀ (a : CoreEdge d G) (t : List (CoreEdge d G)), (a :: t).IsChain Γ.LArrow → ∀ v : V,
      tableauDegree (Γ.pathUp (a :: t)) v + edgeDegree a v
        = tableauDegree (Γ.pathDown (a :: t)) v
            + edgeDegree ((a :: t).getLast (List.cons_ne_nil a t)) v := by
  intro a t
  induction t generalizing a with
  | nil =>
    intro _ v
    simp [pathUp, pathDown, Tableau.listProd]
  | cons b t ih =>
    intro hchain v
    rw [List.isChain_cons_cons] at hchain
    have harrow := Γ.arrowDegree_telescope hd hchain.1 v
    have hIH := ih b hchain.2 v
    have hup : Γ.pathUp (a :: b :: t) = Tableau.mul (Γ.arrowUp a b) (Γ.pathUp (b :: t)) := by
      simp [pathUp, Tableau.listProd]
    have hdown : Γ.pathDown (a :: b :: t)
        = Tableau.mul (Γ.arrowDown a b) (Γ.pathDown (b :: t)) := by
      simp [pathDown, Tableau.listProd]
    have hlast : (a :: b :: t).getLast (List.cons_ne_nil a _)
        = (b :: t).getLast (List.cons_ne_nil b t) := List.getLast_cons _
    rw [hup, hdown, hlast, tableauDegree_mul, tableauDegree_mul]
    omega

/-- Telescoping the degree identity over a whole path system: `deg u(𝒫) + ∑ deg μ_j =
deg d(𝒫) + ∑ deg ν_j`, independently of the paths and of the permutation matching sources
to sinks (`main.tex`, proof of Lemma `lemma:balancing-multihomogeneous-new`). -/
theorem systemDegree_telescope (hd : 0 < d) {l : ℕ} (mu nu : Fin l → CoreEdge d G)
    (P : PathSystemData d G l) (hP : Γ.IsDisjointPathSystem mu nu P) (v : V) :
    tableauDegree (Γ.systemUp P) v + ∑ j, edgeDegree (mu j) v
      = tableauDegree (Γ.systemDown P) v + ∑ j, edgeDegree (nu j) v := by
  classical
  have hperm : ∑ j, edgeDegree (nu (P.1 j)) v = ∑ j, edgeDegree (nu j) v :=
    Equiv.sum_comp P.1 (fun j => edgeDegree (nu j) v)
  have hsumUp : tableauDegree (Γ.systemUp P) v = ∑ j, tableauDegree (Γ.pathUp (P.2 j).1) v := by
    rw [systemUp, tableauDegree_listProd, List.map_map]
    exact (Fin.sum_univ_def _).symm
  have hsumDown : tableauDegree (Γ.systemDown P) v
      = ∑ j, tableauDegree (Γ.pathDown (P.2 j).1) v := by
    rw [systemDown, tableauDegree_listProd, List.map_map]
    exact (Fin.sum_univ_def _).symm
  have hj : ∀ j : Fin l, tableauDegree (Γ.pathUp (P.2 j).1) v + edgeDegree (mu j) v
      = tableauDegree (Γ.pathDown (P.2 j).1) v + edgeDegree (nu (P.1 j)) v := by
    intro j
    obtain ⟨hhead, hlast, hchain⟩ := hP.1 j
    match hL : (P.2 j).1 with
    | [] => rw [hL] at hhead; simp at hhead
    | a :: t =>
      have ha : a = mu j := by rw [hL] at hhead; simpa using hhead
      have hz : (a :: t).getLast (List.cons_ne_nil a t) = nu (P.1 j) := by
        rw [hL, List.getLast?_eq_some_getLast (List.cons_ne_nil a t)] at hlast
        simpa using hlast
      have hkey := Γ.pathDegree_telescope hd a t (by rw [hL] at hchain; exact hchain) v
      rw [← ha, ← hz]
      exact hkey
  rw [hsumUp, hsumDown, ← hperm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => hj j

/-- The multidegree of the weight `wt(𝒫)` of a disjoint path system, computed as in the
proof of Lemma `lemma:balancing-multihomogeneous-new` of the source article: the right
hand side does not depend on `𝒫`. -/
theorem systemWeightDegree_eq (hd : 0 < d) {l : ℕ} (mu nu : Fin l → CoreEdge d G)
    (P : PathSystemData d G l) (hP : P ∈ Γ.disjointSystems mu nu) (v : V) :
    tableauDegree (Γ.systemWeight mu nu P) v + ∑ j, edgeDegree (mu j) v
      = ∑ j, edgeDegree (nu j) v
        + ∑ Q ∈ Γ.disjointSystems mu nu, tableauDegree (Γ.systemDown Q) v := by
  classical
  have hPmem : Γ.IsDisjointPathSystem mu nu P := by
    simpa [disjointSystems] using hP
  have hprod : tableauDegree
      (Tableau.listProd (((Γ.disjointSystems mu nu).erase P).val.toList.map
        (fun Q => Γ.systemDown Q))) v
      = ∑ Q ∈ (Γ.disjointSystems mu nu).erase P, tableauDegree (Γ.systemDown Q) v := by
    rw [tableauDegree_listProd, List.map_map]
    have hcoe : (Multiset.map ((fun T => tableauDegree T v) ∘ (fun Q => Γ.systemDown Q))
          ((Γ.disjointSystems mu nu).erase P).val).sum
        = (((Γ.disjointSystems mu nu).erase P).val.toList.map
            ((fun T => tableauDegree T v) ∘ (fun Q => Γ.systemDown Q))).sum := by
      conv_lhs => rw [← Multiset.coe_toList ((Γ.disjointSystems mu nu).erase P).val]
      simp
    rw [← hcoe]
    rfl
  have hwt : tableauDegree (Γ.systemWeight mu nu P) v
      = tableauDegree (Γ.systemUp P) v
        + ∑ Q ∈ (Γ.disjointSystems mu nu).erase P, tableauDegree (Γ.systemDown Q) v := by
    rw [systemWeight, tableauDegree_smulSign, tableauDegree_mul, hprod]
  have hsum : ∑ Q ∈ (Γ.disjointSystems mu nu).erase P, tableauDegree (Γ.systemDown Q) v
      + tableauDegree (Γ.systemDown P) v
      = ∑ Q ∈ Γ.disjointSystems mu nu, tableauDegree (Γ.systemDown Q) v :=
    Finset.sum_erase_add _ _ hP
  have htel := Γ.systemDegree_telescope hd mu nu P hPmem v
  rw [hwt]
  omega

end DOrientation

end RigidityTableaux
