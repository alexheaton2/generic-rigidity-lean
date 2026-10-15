import RequestProject.LGV

/-!
# Evaluating a balancing condition at a placement

This file carries out the computation of the source article (`main.tex`, Section "Proofs",
proof of Lemma `lemma:balanced-equivalent-nonzero-solution`):

> Let `D` be the product of all down-weights of all path systems `𝒫 ∈ 𝒟`. Then
> `∑_{𝒫 ∈ 𝒟} wt(𝒫)|_p = D|_p · ∑_{𝒫 ∈ 𝒟} frac(𝒫)|_p = D|_p · det Q_{ij}`.
> Because `p` is affinely independent, `D|_p ≠ 0` and thus
> `∑ wt(𝒫)|_p = 0 ⟺ det Q_{ij} = 0`.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Evaluation is multiplicative on products of tableaux -/

section TableauEval

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The evaluation of a product of two tableaux is the product of their evaluations: the
colours multiply as signs and the columns are concatenated. -/
theorem tableauEval_mul (M : Fin n → V → R) (T T' : Tableau n V) :
    tableauEval M (T.mul T') = tableauEval M T * tableauEval M T' := by
  obtain ⟨r, c⟩ := T
  obtain ⟨r', c'⟩ := T'
  simp only [tableauEval, Tableau.mul, Tableau.sign, Multiset.map_add, Multiset.prod_add]
  cases r <;> cases r' <;> simp <;> ring

theorem tableauEval_one (M : Fin n → V → R) : tableauEval M (Tableau.one n V) = 1 := by
  simp [tableauEval, Tableau.one, Tableau.sign]

theorem tableauEval_listProd (M : Fin n → V → R) (L : List (Tableau n V)) :
    tableauEval M (Tableau.listProd L) = (L.map (tableauEval M)).prod := by
  induction L with
  | nil => simpa [Tableau.listProd] using tableauEval_one M
  | cons T L ih =>
      simp only [Tableau.listProd, List.foldr_cons, List.map_cons, List.prod_cons]
      rw [tableauEval_mul, ← ih]
      rfl

theorem tableauEval_smulSign (M : Fin n → V → R) (s : ℤˣ) (T : Tableau n V) :
    tableauEval M (Tableau.smulSign s T) = ((s : ℤ) : R) * tableauEval M T := by
  rcases Int.units_eq_one_or s with hs | hs <;>
    simp [Tableau.smulSign, Tableau.neg, tableauEval, Tableau.sign, hs] <;>
      cases hT : T.red <;> simp <;> ring

end TableauEval

namespace DOrientation

variable (Γ : DOrientation d G)

/-! ### The up- and down-weights of a path -/

omit [DecidableRel G.Adj] in
theorem tableauEval_pathUp_nil (p : V → Fin d → ℝ) (xi : CoreEdge d G) :
    tableauEval (placementMatrix p) (Γ.pathUp [xi]) = 1 := by
  simp [pathUp, Tableau.listProd, tableauEval_one]

omit [DecidableRel G.Adj] in
theorem tableauEval_pathDown_nil (p : V → Fin d → ℝ) (xi : CoreEdge d G) :
    tableauEval (placementMatrix p) (Γ.pathDown [xi]) = 1 := by
  simp [pathDown, Tableau.listProd, tableauEval_one]

omit [DecidableRel G.Adj] in
theorem pathUp_cons (xi eta : CoreEdge d G) (t : List (CoreEdge d G)) :
    Γ.pathUp (xi :: eta :: t) = Tableau.mul (Γ.arrowUp xi eta) (Γ.pathUp (eta :: t)) := by
  simp [pathUp, Tableau.listProd]

omit [DecidableRel G.Adj] in
theorem pathDown_cons (xi eta : CoreEdge d G) (t : List (CoreEdge d G)) :
    Γ.pathDown (xi :: eta :: t) = Tableau.mul (Γ.arrowDown xi eta) (Γ.pathDown (eta :: t)) := by
  simp [pathDown, Tableau.listProd]

/-- **The down-weight of a path does not vanish at an affinely independent placement**: it
is a product of down-brackets of arrows, each of which is a determinant of `d` edge vectors
at a vertex with `d` incoming edges. -/
theorem tableauEval_pathDown_ne_zero (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) :
    ∀ (xi : CoreEdge d G) (t : List (CoreEdge d G)), (xi :: t).IsChain Γ.LArrow →
      tableauEval (placementMatrix p) (Γ.pathDown (xi :: t)) ≠ 0 := by
  intro xi t
  induction t generalizing xi with
  | nil =>
      intro _
      rw [Γ.tableauEval_pathDown_nil p xi]
      exact one_ne_zero
  | cons eta t ih =>
      intro hchain
      rw [List.isChain_cons_cons] at hchain
      rw [Γ.pathDown_cons xi eta t, tableauEval_mul]
      refine mul_ne_zero ?_ (ih eta hchain.2)
      rw [Γ.tableauEval_arrowDown p xi eta]
      exact Γ.bracketEval_weightColumn_down_ne_zero hd p hp hchain.1.2.2.1

/-- **The product of the fractions along a path is the ratio of its up-weight and its
down-weight** (`main.tex`, Section "Examples" and Section "Proofs"). -/
theorem pathFracEval_eq_div (p : V → Fin d → ℝ) :
    ∀ (xi : CoreEdge d G) (t : List (CoreEdge d G)),
      Γ.pathFracEval p (xi :: t)
        = tableauEval (placementMatrix p) (Γ.pathUp (xi :: t))
          / tableauEval (placementMatrix p) (Γ.pathDown (xi :: t)) := by
  intro xi t
  induction t generalizing xi with
  | nil =>
      rw [Γ.tableauEval_pathUp_nil p xi, Γ.tableauEval_pathDown_nil p xi]
      simp [pathFracEval]
  | cons eta t ih =>
      rw [Γ.pathFracEval_cons p xi eta t, ih eta, Γ.pathUp_cons xi eta t,
        Γ.pathDown_cons xi eta t, tableauEval_mul, tableauEval_mul, fracEval]
      rw [div_mul_div_comm]

/-! ### The up- and down-weights of a path system -/

omit [DecidableRel G.Adj] in
theorem tableauEval_systemUp (p : V → Fin d → ℝ) {l : ℕ} (P : PathSystemData d G l) :
    tableauEval (placementMatrix p) (Γ.systemUp P)
      = ∏ j, tableauEval (placementMatrix p) (Γ.pathUp (P.2 j).1) := by
  rw [systemUp, tableauEval_listProd, List.map_map]
  exact (Fin.prod_univ_def _).symm

omit [DecidableRel G.Adj] in
theorem tableauEval_systemDown (p : V → Fin d → ℝ) {l : ℕ} (P : PathSystemData d G l) :
    tableauEval (placementMatrix p) (Γ.systemDown P)
      = ∏ j, tableauEval (placementMatrix p) (Γ.pathDown (P.2 j).1) := by
  rw [systemDown, tableauEval_listProd, List.map_map]
  exact (Fin.prod_univ_def _).symm

/-- The down-weight of a disjoint path system does not vanish at an affinely independent
placement. -/
theorem tableauEval_systemDown_ne_zero (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) {l : ℕ} {mu nu : Fin l → CoreEdge d G}
    {P : PathSystemData d G l} (hP : Γ.IsDisjointPathSystem mu nu P) :
    tableauEval (placementMatrix p) (Γ.systemDown P) ≠ 0 := by
  rw [Γ.tableauEval_systemDown p P]
  refine Finset.prod_ne_zero_iff.2 (fun j _ => ?_)
  obtain ⟨hhead, -, hchain⟩ := hP.1 j
  match hL : (P.2 j).1 with
  | [] =>
      rw [hL] at hhead
      simp at hhead
  | a :: t =>
      exact Γ.tableauEval_pathDown_ne_zero hd p hp a t (by rw [hL] at hchain; exact hchain)

/-- **The product `frac(𝒫)|_p` of a disjoint path system is the ratio of its up-weight and
its down-weight** (`main.tex`, Section "Proofs"). -/
theorem systemFracEval_eq_div (p : V → Fin d → ℝ) {l : ℕ} {mu nu : Fin l → CoreEdge d G}
    {P : PathSystemData d G l} (hP : Γ.IsDisjointPathSystem mu nu P) :
    Γ.systemFracEval p P
      = tableauEval (placementMatrix p) (Γ.systemUp P)
        / tableauEval (placementMatrix p) (Γ.systemDown P) := by
  rw [systemFracEval, Γ.tableauEval_systemUp p P, Γ.tableauEval_systemDown p P,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  obtain ⟨hhead, -, -⟩ := hP.1 j
  match hL : (P.2 j).1 with
  | [] =>
      rw [hL] at hhead
      simp at hhead
  | a :: t =>
      exact Γ.pathFracEval_eq_div p a t

/-! ### The evaluation of a balancing condition -/

/-- The evaluation of a balancing condition at a placement is the product `D|_p` of the
down-weights of all the disjoint path systems times the signed sum of the `frac(𝒫)|_p`
(`main.tex`, Section "Proofs"). -/
theorem evalAtPlacement_balancingCondition (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) {l : ℕ} (mu nu : Fin l → CoreEdge d G) :
    evalAtPlacement p (Γ.balancingCondition mu nu)
      = (∏ Q ∈ Γ.disjointSystems mu nu, tableauEval (placementMatrix p) (Γ.systemDown Q))
        * ∑ P ∈ Γ.disjointSystems mu nu,
            ((Equiv.Perm.sign P.1 : ℤ) : ℝ) * Γ.systemFracEval p P := by
  classical
  rw [evalAtPlacement, multisetEval, balancingCondition, Multiset.map_map, Finset.mul_sum]
  show ∑ P ∈ Γ.disjointSystems mu nu,
      tableauEval (placementMatrix p) (Γ.systemWeight mu nu P) = _
  refine Finset.sum_congr rfl (fun P hP => ?_)
  have hPd : Γ.IsDisjointPathSystem mu nu P := by
    simpa only [disjointSystems, mem_filter, mem_univ, true_and] using hP
  have hdown : tableauEval (placementMatrix p) (Γ.systemDown P) ≠ 0 :=
    Γ.tableauEval_systemDown_ne_zero hd p hp hPd
  have hprod : tableauEval (placementMatrix p)
      (Tableau.listProd (((Γ.disjointSystems mu nu).erase P).val.toList.map
        (fun Q => Γ.systemDown Q)))
      = ∏ Q ∈ (Γ.disjointSystems mu nu).erase P,
          tableauEval (placementMatrix p) (Γ.systemDown Q) := by
    rw [tableauEval_listProd, List.map_map]
    show (((Γ.disjointSystems mu nu).erase P).val.toList.map
        (fun Q => tableauEval (placementMatrix p) (Γ.systemDown Q))).prod = _
    conv_rhs => rw [Finset.prod_eq_multiset_prod,
      ← Multiset.coe_toList ((Γ.disjointSystems mu nu).erase P).val]
    simp
  have herase : (∏ Q ∈ (Γ.disjointSystems mu nu).erase P,
        tableauEval (placementMatrix p) (Γ.systemDown Q))
      * tableauEval (placementMatrix p) (Γ.systemDown P)
      = ∏ Q ∈ Γ.disjointSystems mu nu, tableauEval (placementMatrix p) (Γ.systemDown Q) :=
    Finset.prod_erase_mul _ _ hP
  rw [systemWeight, tableauEval_smulSign, tableauEval_mul, hprod,
    Γ.systemFracEval_eq_div p hPd, ← herase]
  field_simp

/-- **The product `D|_p` of the down-weights does not vanish at an affinely independent
placement** (`main.tex`, Section "Proofs"). -/
theorem prod_systemDown_ne_zero (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) {l : ℕ} (mu nu : Fin l → CoreEdge d G) :
    (∏ Q ∈ Γ.disjointSystems mu nu, tableauEval (placementMatrix p) (Γ.systemDown Q)) ≠ 0 := by
  classical
  refine Finset.prod_ne_zero_iff.2 (fun Q hQ => ?_)
  have hQd : Γ.IsDisjointPathSystem mu nu Q := by
    simpa only [disjointSystems, mem_filter, mem_univ, true_and] using hQ
  exact Γ.tableauEval_systemDown_ne_zero hd p hp hQd

/-- **A balancing condition vanishes at an affinely independent placement exactly when the
corresponding maximal minor of the matrix of path sums vanishes** (`main.tex`, Section
"Proofs", proof of Lemma `lemma:balanced-equivalent-nonzero-solution`). -/
theorem evalAtPlacement_balancingCondition_eq_zero_iff (hd : 0 < d) (p : V → Fin d → ℝ)
    (hp : AffinelyIndependentPlacement d p) {l : ℕ} (mu nu : Fin l → CoreEdge d G) :
    evalAtPlacement p (Γ.balancingCondition mu nu) = 0
      ↔ (Matrix.of fun i j => Γ.pathSum p (mu i) (nu j)).det = 0 := by
  rw [Γ.evalAtPlacement_balancingCondition hd p hp mu nu,
    Γ.det_pathSum_eq_sum_disjointSystems p mu nu,
    mul_eq_zero_iff_left (Γ.prod_systemDown_ne_zero hd p hp mu nu)]

end DOrientation

end RigidityTableaux
