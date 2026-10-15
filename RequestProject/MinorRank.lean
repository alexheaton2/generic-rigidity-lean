import Mathlib

/-!
# Nonzero kernel vectors and the vanishing of the maximal minors

This file proves the piece of linear algebra used in the proof of Lemma
`lemma:balanced-equivalent-nonzero-solution` of the source article (`main.tex`, Section
"Proofs"):

> By their form, the `p,Γ`-equations have a nonzero solution exactly when the linear
> homogeneous equations (\ref{eqn:source-constraint-equations-new}) running over all
> sources have a nonzero solution. But this happens exactly when there are more sinks than
> sources, or else when all maximal minors of their coefficient matrix vanish.

Both cases of the article are covered by the single statement
`exists_nonzero_kernel_iff_forall_det_eq_zero`: a homogeneous system with `l` unknowns has
a nonzero solution if and only if the determinant of every `l × l` matrix formed by `l` of
its equations vanishes. (When there are fewer equations than unknowns, every such choice
repeats an equation and the determinants vanish automatically.)
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

/-- The cofactors of the last row of the square system built from `l` chosen equations:
the vector whose `j`-th entry is the signed minor obtained by deleting the last equation
and the `j`-th unknown. It is a nonzero solution of the system as soon as all the maximal
minors vanish and one of these minors is nonzero. -/
private noncomputable def cofactorVector {m l : ℕ} (M : Fin m → Fin (l + 1) → ℝ)
    (r : Fin l → Fin m) : Fin (l + 1) → ℝ := fun j =>
  (-1) ^ ((l : ℕ) + (j : ℕ)) *
    (Matrix.of fun i j' : Fin l => M (r i) (j.succAbove j')).det

private theorem cofactorVector_last {m l : ℕ} (M : Fin m → Fin (l + 1) → ℝ)
    (r : Fin l → Fin m) :
    cofactorVector M r (Fin.last l)
      = (Matrix.of fun i j' : Fin l => M (r i) j'.castSucc).det := by
  have hsign : ((-1 : ℝ)) ^ ((l : ℕ) + ((Fin.last l : Fin (l + 1)) : ℕ)) = 1 := by
    rw [show ((l : ℕ) + ((Fin.last l : Fin (l + 1)) : ℕ)) = 2 * l by simp [Fin.val_last]; ring,
      pow_mul]
    norm_num
  rw [cofactorVector, hsign, one_mul]
  congr 1
  ext i j'
  rw [Matrix.of_apply, Matrix.of_apply, Fin.succAbove_last]

/-- If all the maximal minors of a homogeneous linear system vanish, the system has a
nonzero solution. -/
private theorem exists_nonzero_kernel_of_forall_det_eq_zero :
    ∀ {l m : ℕ} (M : Fin m → Fin l → ℝ),
      (∀ r : Fin l → Fin m, (Matrix.of fun i j => M (r i) j).det = 0) →
      ∃ x : Fin l → ℝ, x ≠ 0 ∧ ∀ i, ∑ j, M i j * x j = 0 := by
  intro l
  induction l with
  | zero =>
      intro m M hdet
      exfalso
      have h := hdet (fun j => j.elim0)
      rw [Matrix.det_isEmpty] at h
      exact one_ne_zero h
  | succ l ih =>
      intro m M hdet
      by_cases hsmall : ∀ r : Fin l → Fin m,
          (Matrix.of fun i j : Fin l => M (r i) j.castSucc).det = 0
      · -- the first `l` unknowns already admit a nonzero solution
        obtain ⟨y, hy0, hy⟩ := ih (fun i j => M i j.castSucc) hsmall
        refine ⟨Fin.snoc y 0, ?_, ?_⟩
        · intro hcon
          refine hy0 ?_
          funext j
          have := congrFun hcon j.castSucc
          simpa using this
        · intro i
          rw [Fin.sum_univ_castSucc]
          simp [hy i]
      · -- some minor of the first `l` unknowns is nonzero: the cofactors of the last row
        -- of the enlarged systems give a nonzero solution
        push_neg at hsmall
        obtain ⟨r, hr⟩ := hsmall
        refine ⟨cofactorVector M r, ?_, ?_⟩
        · intro hcon
          refine hr ?_
          rw [← cofactorVector_last M r, hcon]
          rfl
        · intro s
          have hzero := hdet (Fin.snoc r s)
          rw [Matrix.det_succ_row _ (Fin.last l)] at hzero
          rw [← hzero]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have hrow : ∀ j : Fin (l + 1),
              (Matrix.of fun i j : Fin (l + 1) =>
                  M ((Fin.snoc r s : Fin (l + 1) → Fin m) i) j) (Fin.last l) j
                = M s j := by
            intro j
            rw [Matrix.of_apply, Fin.snoc_last]
          have hminor : ((Matrix.of fun i j : Fin (l + 1) =>
                  M ((Fin.snoc r s : Fin (l + 1) → Fin m) i) j).submatrix
                (Fin.last l).succAbove j.succAbove)
              = Matrix.of fun i j' : Fin l => M (r i) (j.succAbove j') := by
            ext i j'
            rw [Matrix.submatrix_apply, Matrix.of_apply, Matrix.of_apply, Fin.succAbove_last,
              Fin.snoc_castSucc]
          rw [hrow, hminor, cofactorVector, Fin.val_last]
          ring

/-- **A homogeneous linear system has a nonzero solution exactly when all its maximal
minors vanish** (`main.tex`, Section "Proofs", proof of Lemma
`lemma:balanced-equivalent-nonzero-solution`). Here the rows of `M` are the equations and
the columns are the unknowns; the maximal minors are the determinants of the `l × l`
matrices obtained by selecting `l` equations. -/
theorem exists_nonzero_kernel_iff_forall_det_eq_zero {m l : ℕ} (M : Fin m → Fin l → ℝ) :
    (∃ x : Fin l → ℝ, x ≠ 0 ∧ ∀ i, ∑ j, M i j * x j = 0) ↔
      ∀ r : Fin l → Fin m, (Matrix.of fun i j => M (r i) j).det = 0 := by
  constructor
  · rintro ⟨x, hx0, hx⟩ r
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx0, ?_⟩
    funext i
    simpa [Matrix.mulVec, dotProduct] using hx (r i)
  · exact exists_nonzero_kernel_of_forall_det_eq_zero M

end RigidityTableaux
