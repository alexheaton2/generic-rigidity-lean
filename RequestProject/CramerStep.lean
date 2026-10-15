import RequestProject.DesertStress
import RequestProject.Sylvester

/-!
# Cramer's rule at a vertex

This file develops the linear algebra behind equation `eqn:cramers-rule-new` in the proof
of Lemma `lemma:stream-formula-new` of the source article (`main.tex`, Section "Proofs"):

> Move the last term to the right-side, and apply Cramer's rule to solve for `w_{ab}`,
> which is valid by affine independence, no matter the choice of `d` incoming edges.

Three ingredients are proved here.

* `bracketEval_placementMatrix`: the article's passage from `d × d` determinants of edge
  vectors to `(d+1) × (d+1)` brackets, *"by rewriting each `e_{ax} = p_x - p_a`, appending
  a column `(p_a, 1)^T` on the right while adding a zero to every other column in a new
  `(d+1)`st coordinate"*: the bracket `[v_1 … v_d a]|_p` equals the determinant of the
  edge vectors `p_{v_1} - p_a, …, p_{v_d} - p_a`.
* `cramer_sum_eq_zero`: applying the `d`-linear alternating form
  `det(e_{a v_1}, …, ·, …, e_{a v_d})` to the vertex equation at `a` kills all the terms
  indexed by the chosen incoming edges except one, which is Cramer's rule.
* `differenceDet_ne_zero`: at an affinely independent placement the denominator
  `det(e_{a v_1}, …, e_{a v_d})` of Cramer's rule is nonzero.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The edge vectors `e_{ax} = p_x - p_a` at a vertex `a`, as a family of vectors indexed
by the vertices. -/
def edgeVectorAt (p : V → Fin d → ℝ) (a : V) : V → Fin d → ℝ := fun x => edgeVector p a x

/-- The determinant `det(e_{a v_1}, …, e_{a v_d})` of the edge vectors at `a` given by a
family `v` of `d` vertices. -/
noncomputable def differenceDet (p : V → Fin d → ℝ) (a : V) (v : Fin d → V) : ℝ :=
  colDet (fun i => edgeVectorAt p a (v i))

theorem differenceDet_eq_det (p : V → Fin d → ℝ) (a : V) (v : Fin d → V) :
    differenceDet p a v = Matrix.det (Matrix.of fun k i : Fin d => p (v i) k - p a k) := rfl

/-! ### Brackets as determinants of edge vectors -/

/-- **The passage from edge vectors to brackets** of the source article: the bracket
`[v_1 … v_d a]|_p`, i.e. the maximal minor of the matrix `M` with columns `(p_i,1)` on the
columns `v_1, …, v_d, a`, is the determinant of the edge vectors
`p_{v_1} - p_a, …, p_{v_d} - p_a`. -/
theorem bracketEval_placementMatrix (p : V → Fin d → ℝ) (c : Column (d + 1) V) :
    bracketEval (placementMatrix p) c
      = differenceDet p (c (Fin.last d)) (fun i => c i.castSucc) := by
  classical
  set a := c (Fin.last d) with ha
  set A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    Matrix.of fun i j => placementMatrix p i (c j) with hA
  set B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    Matrix.of fun i j => if j = Fin.last d then A i j else A i j - A i (Fin.last d) with hB
  -- subtracting the last column from all the others does not change the determinant
  have hdet : B.det = A.det := by
    have h := Matrix.det_eq_of_forall_row_eq_smul_add_const (A := B.transpose) (B := A.transpose)
      (fun i => if i = Fin.last d then (0 : ℝ) else -1) (Fin.last d) (by simp) ?_
    · rw [← Matrix.det_transpose B, ← Matrix.det_transpose A]
      exact h
    · intro i j
      by_cases hi : i = Fin.last d
      · simp [hi, hB]
      · simp only [Matrix.transpose_apply, hB, Matrix.of_apply, if_neg hi]
        ring
  -- the last row of `B` is the last basis vector
  have hlastrow : ∀ j : Fin (d + 1), B (Fin.last d) j = if j = Fin.last d then 1 else 0 := by
    intro j
    have hval : ∀ x : V, placementMatrix p (Fin.last d) x = 1 := by
      intro x
      rw [placementMatrix, dif_neg (by simp)]
    by_cases hj : j = Fin.last d
    · simp [hB, hA, hj, hval]
    · simp [hB, hA, hj, hval]
  -- expanding along the last row
  have hexp := Matrix.det_succ_row B (Fin.last d)
  rw [Finset.sum_eq_single (Fin.last d)] at hexp
  · rw [hlastrow (Fin.last d), if_pos rfl] at hexp
    have hsign : ((-1 : ℝ)) ^ ((Fin.last d : ℕ) + (Fin.last d : ℕ)) = 1 := by
      rw [show ((Fin.last d : ℕ) + (Fin.last d : ℕ)) = 2 * d by simp [Fin.val_last]; ring]
      rw [pow_mul]
      norm_num
    rw [hsign] at hexp
    have hsub : (B.submatrix (Fin.last d).succAbove (Fin.last d).succAbove)
        = Matrix.of fun k i : Fin d => p (c i.castSucc) k - p a k := by
      ext k i
      have hk : ((k.castSucc : Fin (d + 1)) : ℕ) < d := by simpa using k.isLt
      simp only [Matrix.submatrix_apply, Fin.succAbove_last, Matrix.of_apply, hB, hA]
      rw [if_neg (by simp : ¬ (i.castSucc = Fin.last d))]
      rw [placementMatrix, placementMatrix, dif_pos hk, dif_pos hk]
      congr 2 <;> simp [Fin.ext_iff]
    rw [hsub] at hexp
    rw [bracketEval, differenceDet_eq_det, ← hA, ← hdet, hexp]
    ring
  · intro j _ hj
    rw [hlastrow j, if_neg hj]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Cramer's rule at a vertex -/

/-- Replacing one of the vertices of the family by a vertex already occurring in it makes
the determinant of the edge vectors vanish. -/
theorem differenceDet_update_eq_zero (p : V → Fin d → ℝ) (a : V) (v : Fin d → V)
    {i i₀ : Fin d} (hne : i ≠ i₀) :
    differenceDet p a (Function.update v i₀ (v i)) = 0 := by
  classical
  rw [differenceDet_eq_det, ← Matrix.det_transpose]
  refine Matrix.det_zero_of_row_eq hne ?_
  funext k
  simp [Function.update_of_ne hne, Function.update_self]

/-- **The denominator of Cramer's rule is nonzero.** At an affinely independent placement,
the determinant of the edge vectors `e_{a v_1}, …, e_{a v_d}` given by `d` distinct
vertices `v_1, …, v_d`, all different from `a`, does not vanish (`main.tex`, Section
"Proofs": *"apply Cramer's rule to solve for `w_{ab}`, which is valid by affine
independence, no matter the choice of `d` incoming edges"*). -/
theorem differenceDet_ne_zero (p : V → Fin d → ℝ) (hp : AffinelyIndependentPlacement d p)
    (a : V) (v : Fin d → V) (hv : Function.Injective v) (ha : ∀ i, v i ≠ a) :
    differenceDet p a v ≠ 0 := by
  classical
  intro h0
  have hdet : (Matrix.of fun k i : Fin d => p (v i) k - p a k).det = 0 := by
    rw [← differenceDet_eq_det]
    exact h0
  obtain ⟨x, hx, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  -- the vertices `a, v_1, …, v_d`
  set s : Finset V := insert a (Finset.image v univ) with hs
  have haim : a ∉ Finset.image v univ := by
    simp only [Finset.mem_image, not_exists]
    rintro i ⟨-, hi⟩
    exact ha i hi
  have hcard : s.card ≤ d + 1 := by
    rw [hs, Finset.card_insert_of_notMem haim, Finset.card_image_of_injective _ hv]
    simp
  have hai := hp s hcard
  rw [affineIndependent_iff_of_fintype] at hai
  set lam : V → ℝ :=
    fun y => if y = a then -(∑ i, x i) else ∑ i ∈ univ.filter (fun i => v i = y), x i with hlam
  have hlamv : ∀ i : Fin d, lam (v i) = x i := by
    intro i
    have hfil : (univ.filter (fun j => v j = v i)) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hv h, fun h => by rw [h]⟩
    rw [hlam]
    simp only [if_neg (ha i), hfil, Finset.sum_singleton]
  have hlama : lam a = -(∑ i, x i) := by rw [hlam]; simp
  have hsumS : ∑ y ∈ s, lam y = 0 := by
    rw [hs, Finset.sum_insert haim, hlama,
      Finset.sum_image (fun i _ j _ h => hv h)]
    rw [Finset.sum_congr rfl (fun i _ => hlamv i)]
    ring
  have hsum : ∑ y : ((s : Finset V) : Set V), lam (y : V) = 0 :=
    (Finset.sum_coe_sort s lam).trans hsumS
  have hvsub : (Finset.univ.weightedVSub (fun y : ((s : Finset V) : Set V) =>
      (p (y : V) : Fin d → ℝ))) (fun y => lam (y : V)) = 0 := by
    have h1 := Finset.weightedVSub_eq_linear_combination
      (s := (Finset.univ : Finset ((s : Finset V) : Set V)))
      (w := fun y : ((s : Finset V) : Set V) => lam (y : V))
      (p := fun y : ((s : Finset V) : Set V) => (p (y : V) : Fin d → ℝ)) hsum
    have h2 : (∑ y : ((s : Finset V) : Set V), lam (y : V) • (p (y : V) : Fin d → ℝ))
        = ∑ y ∈ s, lam y • (p y : Fin d → ℝ) :=
      Finset.sum_coe_sort s (fun y => lam y • (p y : Fin d → ℝ))
    rw [h1, h2, hs, Finset.sum_insert haim, hlama,
      Finset.sum_image (fun i _ j _ h => hv h)]
    funext k
    have hk := congrFun hmul k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at hk
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.zero_apply, hlamv]
    have hk' : ∑ i, (p (v i) k - p a k) * x i = 0 := hk
    have : ∑ i, x i * p (v i) k - (∑ i, x i) * p a k = 0 := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      rw [← hk']
      exact Finset.sum_congr rfl (fun i _ => by ring)
    linarith [this]
  have hi0 : ∀ i : Fin d, x i = 0 := by
    intro i
    have hmem : (v i) ∈ ((s : Finset V) : Set V) := by
      simp only [hs, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_image]
      exact Or.inr ⟨i, Finset.mem_univ i, rfl⟩
    have := hai (fun y => lam (y : V)) hsum hvsub ⟨v i, hmem⟩
    rwa [hlamv i] at this
  exact hx (funext hi0)

omit [DecidableEq V] in
/-- **Cramer's rule at the vertex `a`** (`main.tex`, equation `eqn:cramers-rule-new`).
Applying the alternating form `det(e_{a v_1}, …, ·, …, e_{a v_d})` to the vertex equation
of a self-stress at `a` gives a linear relation between the stress coordinate of the edge
`{a, v_{i₀}}` and the stress coordinates of the edges not among the chosen ones. -/
theorem cramer_sum_eq_zero (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ) (hw : IsSelfStress p w)
    (a : V) (v : Fin d → V) (i₀ : Fin d) :
    ∑ c : V, stressVal w a c * differenceDet p a (Function.update v i₀ c) = 0 := by
  classical
  have hvert : ∑ c : V, stressVal w a c • edgeVectorAt p a c = (0 : Fin d → ℝ) := by
    funext k
    have := hw a k
    simpa [edgeVectorAt, edgeVector, Finset.sum_apply] using this
  have hkey := colDet_update_sum (Finset.univ : Finset V)
    (fun i => edgeVectorAt p a (v i)) i₀ (fun c => stressVal w a c) (fun c => edgeVectorAt p a c)
  rw [hvert, colDet_update_zero] at hkey
  have hgoal : ∀ c : V, differenceDet p a (Function.update v i₀ c)
      = colDet (Function.update (fun i => edgeVectorAt p a (v i)) i₀ (edgeVectorAt p a c)) := by
    intro c
    rw [differenceDet]
    congr 1
    funext i
    by_cases hi : i = i₀
    · rw [hi, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  simp only [hgoal]
  exact hkey.symm

/-! ### The bracket form of Cramer's rule at a vertex -/

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
/-- Transposing two entries of a column changes the sign of its bracket. -/
theorem bracketEval_comp_swap {n : ℕ} {R : Type*} [CommRing R] (M : Fin n → V → R)
    (c : Column n V) {i j : Fin n} (hij : i ≠ j) :
    bracketEval M (c ∘ Equiv.swap i j) = - bracketEval M c := by
  classical
  have hsub : (Matrix.of fun k l : Fin n => M k ((c ∘ Equiv.swap i j) l))
      = (Matrix.of fun k l : Fin n => M k (c l)).submatrix id (Equiv.swap i j) := rfl
  rw [bracketEval, hsub, Matrix.det_permute', Equiv.Perm.sign_swap hij, bracketEval]
  simp

namespace DOrientation

variable (Γ : DOrientation d G)

/-- The family of the `d` vertices joined to `a` by an edge oriented into `a`, listed as
in the columns `[j_1 … j_{d-1} b a]` and `[j_1 … j_{d-1} a c]` of the source article: the
other incoming neighbours `j_1 < ⋯ < j_{d-1}` first, then `b`. -/
noncomputable def incomingFamily (a b : V) : Fin d → V :=
  fun i => if (i : ℕ) + 2 ≤ d then (Γ.incomingOthersList a b).getD i a else b

/-- The last position of the family `incomingFamily`, the one holding `b`. -/
def lastPos (hd : 0 < d) : Fin d := ⟨d - 1, by omega⟩

theorem weightColumn_castSucc (a b x y : V) (i : Fin d) :
    Γ.weightColumn a b x y i.castSucc
      = if (i : ℕ) + 2 ≤ d then (Γ.incomingOthersList a b).getD i a else x := by
  have hi : ((i.castSucc : Fin (d + 1)) : ℕ) = (i : ℕ) := rfl
  rw [weightColumn]
  by_cases h : (i : ℕ) + 2 ≤ d
  · rw [if_pos (by rw [hi]; exact h), if_pos h, hi]
  · have hlast : (i : ℕ) + 1 = d := by
      have := i.isLt
      omega
    rw [if_neg (by rw [hi]; exact h), if_pos (by rw [hi]; exact hlast), if_neg h]

theorem weightColumn_last (a b x y : V) :
    Γ.weightColumn a b x y (Fin.last d) = y := by
  have h1 : ((Fin.last d : Fin (d + 1)) : ℕ) = d := rfl
  rw [weightColumn, if_neg (by rw [h1]; omega), if_neg (by rw [h1]; omega)]

/-- The columns `[j_1 … j_{d-1} b a]` of the source article, read off as a family of `d`
vertices followed by `a`. -/
theorem weightColumn_down_castSucc (a b : V) :
    (fun i : Fin d => Γ.weightColumn a b b a i.castSucc) = Γ.incomingFamily a b := by
  funext i
  rw [Γ.weightColumn_castSucc a b b a i, incomingFamily]

theorem weightColumn_up_castSucc (hd : 0 < d) (a b c : V) :
    (fun i : Fin d => Γ.weightColumn a b c a i.castSucc)
      = Function.update (Γ.incomingFamily a b) (lastPos (d := d) hd) c := by
  funext i
  rw [Γ.weightColumn_castSucc a b c a i]
  by_cases h : (i : ℕ) + 2 ≤ d
  · have hne : i ≠ lastPos (d := d) hd := by
      intro hcon
      rw [hcon] at h
      simp only [lastPos] at h
      omega
    rw [if_pos h, Function.update_of_ne hne, incomingFamily, if_pos h]
  · have heq : i = lastPos (d := d) hd := by
      have := i.isLt
      apply Fin.ext
      simp only [lastPos]
      omega
    rw [if_neg h, heq, Function.update_self]

/-- The bracket `[j_1 … j_{d-1} b a]|_p` is the determinant of the edge vectors at `a`
given by the `d` incoming neighbours of `a`. -/
theorem bracketEval_weightColumn_down (p : V → Fin d → ℝ) (a b : V) :
    bracketEval (placementMatrix p) (Γ.weightColumn a b b a)
      = differenceDet p a (Γ.incomingFamily a b) := by
  rw [bracketEval_placementMatrix, Γ.weightColumn_last a b b a, Γ.weightColumn_down_castSucc a b]

/-- The bracket `[j_1 … j_{d-1} a c]|_p` is minus the determinant of the edge vectors at
`a` obtained by replacing the incoming neighbour `b` by `c`. -/
theorem bracketEval_weightColumn_up (hd : 0 < d) (p : V → Fin d → ℝ) (a b c : V) :
    bracketEval (placementMatrix p) (Γ.weightColumn a b a c)
      = - differenceDet p a (Function.update (Γ.incomingFamily a b) (lastPos (d := d) hd) c) := by
  classical
  have hswap : Γ.weightColumn a b a c
      = (Γ.weightColumn a b c a) ∘ Equiv.swap (⟨d - 1, by omega⟩ : Fin (d + 1)) (Fin.last d) := by
    funext i
    have hlast : ((Fin.last d : Fin (d + 1)) : ℕ) = d := rfl
    by_cases h1 : i = (⟨d - 1, by omega⟩ : Fin (d + 1))
    · rw [h1]
      simp only [Function.comp_apply, Equiv.swap_apply_left]
      rw [Γ.weightColumn_last a b c a, weightColumn]
      rw [if_neg (by simpa using (by omega : ¬ ((d - 1) + 2 ≤ d))),
        if_pos (by simpa using (by omega : (d - 1) + 1 = d))]
    · by_cases h2 : i = Fin.last d
      · rw [h2]
        simp only [Function.comp_apply, Equiv.swap_apply_right]
        rw [Γ.weightColumn_last a b a c, weightColumn]
        rw [if_neg (by simpa using (by omega : ¬ ((d - 1) + 2 ≤ d))),
          if_pos (by simpa using (by omega : (d - 1) + 1 = d))]
      · simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
        have hi : (i : ℕ) + 2 ≤ d := by
          have hlt := i.isLt
          have hne1 : (i : ℕ) ≠ d - 1 := fun h => h1 (Fin.ext h)
          have hne2 : (i : ℕ) ≠ d := fun h => h2 (Fin.ext (by rw [h, hlast]))
          omega
        rw [weightColumn, weightColumn, if_pos hi, if_pos hi]
  have hne : (⟨d - 1, by omega⟩ : Fin (d + 1)) ≠ Fin.last d := by
    intro hcon
    have := congrArg (fun x : Fin (d + 1) => (x : ℕ)) hcon
    simp only [Fin.val_last] at this
    omega
  rw [hswap, bracketEval_comp_swap _ _ hne, bracketEval_placementMatrix,
    Γ.weightColumn_last a b c a, Γ.weightColumn_up_castSucc hd a b c]

/-! ### The `d` incoming neighbours of a vertex -/

/-- There are exactly `d - 1` incoming neighbours of `a` besides `b`, when `{a,b}` is
itself oriented into `a` (`main.tex`, Subsection "Main Results": the vertices
`j_1 < ⋯ < j_{d-1}`). -/
theorem card_incomingOthers {a b : V} (hab : Γ.into a b) :
    #(Γ.incomingOthers a b) = d - 1 := by
  classical
  have hmem : b ∈ univ.filter (fun c => Γ.into a c) := by
    simp only [mem_filter, mem_univ, true_and]; exact hab
  rw [incomingOthers, Finset.card_erase_of_mem hmem,
    Γ.card_into a b (Γ.into_nonDesert a b hab)]

/-- The list `j_1 < ⋯ < j_{d-1}` has length `d - 1`. -/
theorem length_incomingOthersList {a b : V} (hab : Γ.into a b) :
    (Γ.incomingOthersList a b).length = d - 1 := by
  rw [incomingOthersList, Finset.length_sort, Γ.card_incomingOthers hab]

/-- The list `j_1 < ⋯ < j_{d-1}` has no repetitions. -/
theorem nodup_incomingOthersList (a b : V) : (Γ.incomingOthersList a b).Nodup := by
  rw [incomingOthersList]
  exact Finset.sort_nodup _ _

/-- The list `j_1 < ⋯ < j_{d-1}` enumerates the incoming neighbours of `a` besides `b`. -/
theorem mem_incomingOthersList {a b x : V} :
    x ∈ Γ.incomingOthersList a b ↔ x ∈ Γ.incomingOthers a b := by
  simp [incomingOthersList]

/-- Every member of the family `incomingFamily a b` is an incoming neighbour of `a`. -/
theorem incomingFamily_into {a b : V} (hab : Γ.into a b) (i : Fin d) :
    Γ.into a (Γ.incomingFamily a b i) := by
  classical
  rw [incomingFamily]
  by_cases h : (i : ℕ) + 2 ≤ d
  · rw [if_pos h]
    have hlt : (i : ℕ) < (Γ.incomingOthersList a b).length := by
      rw [Γ.length_incomingOthersList hab]; omega
    rw [List.getD_eq_getElem _ _ hlt]
    have hmem : (Γ.incomingOthersList a b)[(i : ℕ)] ∈ Γ.incomingOthers a b :=
      Γ.mem_incomingOthersList.1 (List.getElem_mem hlt)
    rw [incomingOthers, Finset.mem_erase, mem_filter] at hmem
    exact hmem.2.2
  · rw [if_neg h]; exact hab

/-- The family `incomingFamily a b` lists `d` distinct vertices. -/
theorem incomingFamily_injective {a b : V} (hab : Γ.into a b) :
    Function.Injective (Γ.incomingFamily a b) := by
  classical
  have hlen := Γ.length_incomingOthersList hab
  have hnodup : (Γ.incomingOthersList a b).Nodup := Γ.nodup_incomingOthersList a b
  have hnotb : ∀ i : Fin d, (i : ℕ) + 2 ≤ d →
      (Γ.incomingOthersList a b).getD (i : ℕ) a ≠ b := by
    intro i hi
    have hlt : (i : ℕ) < (Γ.incomingOthersList a b).length := by rw [hlen]; omega
    rw [List.getD_eq_getElem _ _ hlt]
    have hmem : (Γ.incomingOthersList a b)[(i : ℕ)] ∈ Γ.incomingOthers a b :=
      Γ.mem_incomingOthersList.1 (List.getElem_mem hlt)
    rw [incomingOthers, Finset.mem_erase] at hmem
    exact hmem.1
  intro i j hij
  simp only [incomingFamily] at hij
  by_cases hi : (i : ℕ) + 2 ≤ d <;> by_cases hj : (j : ℕ) + 2 ≤ d
  · rw [if_pos hi, if_pos hj] at hij
    have hli : (i : ℕ) < (Γ.incomingOthersList a b).length := by rw [hlen]; omega
    have hlj : (j : ℕ) < (Γ.incomingOthersList a b).length := by rw [hlen]; omega
    rw [List.getD_eq_getElem _ _ hli, List.getD_eq_getElem _ _ hlj] at hij
    exact Fin.ext (hnodup.getElem_inj_iff.1 hij)
  · rw [if_pos hi, if_neg hj] at hij
    exact absurd hij (hnotb i hi)
  · rw [if_neg hi, if_pos hj] at hij
    exact absurd hij.symm (hnotb j hj)
  · have hi' : (i : ℕ) + 1 = d := by have := i.isLt; omega
    have hj' : (j : ℕ) + 1 = d := by have := j.isLt; omega
    exact Fin.ext (by omega)

/-- The family `incomingFamily a b` enumerates exactly the `d` incoming neighbours of
`a`. -/
theorem incomingFamily_image {a b : V} (hab : Γ.into a b) :
    Finset.image (Γ.incomingFamily a b) univ = univ.filter (fun c => Γ.into a c) := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro c hc
    simp only [Finset.mem_image, mem_univ, true_and] at hc
    obtain ⟨i, hi⟩ := hc
    simp only [mem_filter, mem_univ, true_and, ← hi]
    exact Γ.incomingFamily_into hab i
  · rw [Finset.card_image_of_injective _ (Γ.incomingFamily_injective hab),
      Γ.card_into a b (Γ.into_nonDesert a b hab)]
    simp

/-- The vertex `b` sits at the last position of the family. -/
theorem incomingFamily_lastPos (hd : 0 < d) (a b : V) :
    Γ.incomingFamily a b (lastPos (d := d) hd) = b := by
  rw [incomingFamily, if_neg (by simp only [lastPos]; omega)]

/-! ### The bracket form of Cramer's rule -/

/-- **The bracket form of the alternating sum at a vertex.** Splitting the sum of
`cramer_sum_eq_zero` into its incoming and outgoing parts turns it into the two sides of
equation `eqn:cramers-rule-new` of the source article; no self-stress hypothesis is needed
for this purely determinantal identity. -/
theorem cramer_sum_split (hd : 0 < d) (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ)
    {a b : V} (hab : Γ.into a b) :
    ∑ c : V, stressVal w a c
        * differenceDet p a (Function.update (Γ.incomingFamily a b) (lastPos (d := d) hd) c)
      = stressVal w a b * bracketEval (placementMatrix p) (Γ.weightColumn a b b a)
        - ∑ c ∈ univ.filter (fun c => ¬ Γ.into a c),
            stressVal w a c * bracketEval (placementMatrix p) (Γ.weightColumn a b a c) := by
  classical
  -- split the sum over the incoming neighbours and the rest
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun c => Γ.into a c)
    (fun c => stressVal w a c *
      differenceDet p a (Function.update (Γ.incomingFamily a b) (lastPos (d := d) hd) c))]
  -- the incoming part reduces to the single term `c = b`
  have hin : ∑ c ∈ univ.filter (fun c => Γ.into a c),
      stressVal w a c
        * differenceDet p a (Function.update (Γ.incomingFamily a b) (lastPos (d := d) hd) c)
      = stressVal w a b * bracketEval (placementMatrix p) (Γ.weightColumn a b b a) := by
    rw [← Γ.incomingFamily_image hab, Finset.sum_image
      (fun i _ j _ h => Γ.incomingFamily_injective hab h)]
    rw [Finset.sum_eq_single (lastPos (d := d) hd)]
    · rw [Function.update_eq_self, Γ.incomingFamily_lastPos hd a b,
        Γ.bracketEval_weightColumn_down p a b]
    · intro i _ hi
      rw [differenceDet_update_eq_zero p a (Γ.incomingFamily a b) hi, mul_zero]
    · intro h; exact absurd (mem_univ _) h
  -- the outgoing part is the right-hand side, up to sign
  have hout : ∑ c ∈ univ.filter (fun c => ¬ Γ.into a c),
      stressVal w a c
        * differenceDet p a (Function.update (Γ.incomingFamily a b) (lastPos (d := d) hd) c)
      = - ∑ c ∈ univ.filter (fun c => ¬ Γ.into a c),
          stressVal w a c * bracketEval (placementMatrix p) (Γ.weightColumn a b a c) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Γ.bracketEval_weightColumn_up hd p a b c]
    ring
  rw [hin, hout]
  ring

/-- **Equation `eqn:cramers-rule-new` of the source article** in its bracket form
(`main.tex`, Section "Proofs"). At a vertex `a` with an edge `{a,b}` oriented into `a`,
Cramer's rule expresses the stress coordinate `w_{ab}` in terms of the coordinates of the
edges outgoing at `a`:
`w_{ab} · [j_1 … j_{d-1} b a]|_p = ∑_c w_{ac} · [j_1 … j_{d-1} a c]|_p`,
the sum running over the vertices `c` with `{a,c}` not oriented into `a`. -/
theorem cramer_bracket (hd : 0 < d) (p : V → Fin d → ℝ) (w : OrientedEdge G → ℝ)
    (hw : IsSelfStress p w) {a b : V} (hab : Γ.into a b) :
    stressVal w a b * bracketEval (placementMatrix p) (Γ.weightColumn a b b a)
      = ∑ c ∈ univ.filter (fun c => ¬ Γ.into a c),
          stressVal w a c * bracketEval (placementMatrix p) (Γ.weightColumn a b a c) := by
  have h := Γ.cramer_sum_split hd p w hab
  rw [cramer_sum_eq_zero p w hw a (Γ.incomingFamily a b) (lastPos (d := d) hd)] at h
  linarith

end DOrientation

end RigidityTableaux
