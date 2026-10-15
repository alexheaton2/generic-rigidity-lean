import RequestProject.Rigidity

/-!
# Generic placements are affinely independent

The source article uses repeatedly that a generic placement (one whose coordinates are
algebraically independent over `ℚ`) is affinely independent, i.e. that any at most `d+1`
of its points are affinely independent (`main.tex`, Subsection "Geometric results" and
proof of Lemma `lemma:generic-geometric-balancing`: *"A generic placement is affinely
independent"*).

This file proves that implication. The argument is the standard one: an affine dependence
among `k ≤ d+1` of the points makes a `k × k` determinant built from the coordinates and
a row of ones vanish, while the corresponding polynomial in the coordinates is not the
zero polynomial, so it cannot vanish on algebraically independent values.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The `k × k` matrix of indeterminates used to detect affine dependence of `k` points:
the first `k-1` rows carry the first `k-1` coordinates of the points, and the last row is
a row of ones. -/
noncomputable def genericAffineMatrix {k : ℕ} (hk : k ≤ d + 1) (e : Fin k → V) :
    Matrix (Fin k) (Fin k) (MvPolynomial (V × Fin d) ℚ) :=
  Matrix.of fun r i =>
    if h : (r : ℕ) + 1 < k then MvPolynomial.X (e i, ⟨r, by omega⟩) else 1

omit [Fintype V] in
/-- The determinant of the matrix of indeterminates above is not the zero polynomial: it
takes the value `1` at the points `e_1, …, e_{k-1}, 0`. -/
theorem genericAffineMatrix_det_ne_zero {k : ℕ} (hk : k ≤ d + 1) (e : Fin k → V)
    (he : Function.Injective e) : (genericAffineMatrix hk e).det ≠ 0 := by
  classical
  set g : V × Fin d → ℚ := fun x =>
    if ∃ i : Fin k, e i = x.1 ∧ (i : ℕ) = (x.2 : ℕ) then 1 else 0 with hg
  intro hzero
  have hmap : ((genericAffineMatrix hk e).map (MvPolynomial.eval g)).det = 0 := by
    have hd := RingHom.map_det (MvPolynomial.eval g) (genericAffineMatrix hk e)
    rw [show ((genericAffineMatrix hk e).map (MvPolynomial.eval g))
      = (MvPolynomial.eval g).mapMatrix (genericAffineMatrix hk e) from rfl, ← hd, hzero, map_zero]
  -- the evaluated matrix is lower triangular with `1` on the diagonal
  have hentry : ∀ r i : Fin k,
      ((genericAffineMatrix hk e).map (MvPolynomial.eval g)) r i
        = if (r : ℕ) + 1 < k then (if (i : ℕ) = (r : ℕ) then 1 else 0) else 1 := by
    intro r i
    by_cases h : (r : ℕ) + 1 < k
    · simp only [Matrix.map_apply, genericAffineMatrix, Matrix.of_apply, dif_pos h,
        MvPolynomial.eval_X, hg, if_pos h]
      by_cases hir : (i : ℕ) = (r : ℕ)
      · have : ∃ j : Fin k, e j = e i ∧ (j : ℕ) = (r : ℕ) := ⟨i, rfl, hir⟩
        simp [this, hir]
      · have hno : ¬ ∃ j : Fin k, e j = e i ∧ (j : ℕ) = (r : ℕ) := by
          rintro ⟨j, hj, hjr⟩
          exact hir (by rw [← he hj]; exact hjr)
        simp [hno, hir]
    · simp [Matrix.map_apply, genericAffineMatrix, Matrix.of_apply, h]
  have htri : ∀ r i : Fin k, r < i →
      ((genericAffineMatrix hk e).map (MvPolynomial.eval g)) r i = 0 := by
    intro r i hri
    rw [hentry]
    have hlt : (r : ℕ) < (i : ℕ) := hri
    have hrk : (r : ℕ) + 1 < k := lt_of_le_of_lt hlt i.2
    simp [hrk, Nat.ne_of_gt hlt]
  have hdiag : ∀ r : Fin k, ((genericAffineMatrix hk e).map (MvPolynomial.eval g)) r r = 1 := by
    intro r
    rw [hentry]
    by_cases h : (r : ℕ) + 1 < k <;> simp [h]
  have hone : ((genericAffineMatrix hk e).map (MvPolynomial.eval g)).det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => htri i j hij)]
    exact Finset.prod_eq_one fun r _ => hdiag r
  rw [hone] at hmap
  exact one_ne_zero hmap

omit [Fintype V] in
/-- The determinant criterion for affine independence of finitely many points of a generic
placement: any `k ≤ d+1` distinct vertices carry no affine dependence. -/
theorem generic_no_affine_dependence (p : V → Fin d → ℝ) (hp : GenericPlacement d p)
    {k : ℕ} (hk : k ≤ d + 1) (e : Fin k → V) (he : Function.Injective e)
    (w : Fin k → ℝ) (hw0 : ∑ i, w i = 0) (hws : ∀ r : Fin d, ∑ i, w i * p (e i) r = 0) :
    ∀ i, w i = 0 := by
  classical
  -- the real matrix obtained by evaluating the matrix of indeterminates at `p`
  set f : MvPolynomial (V × Fin d) ℚ →+* ℝ :=
    (MvPolynomial.aeval (fun x : V × Fin d => p x.1 x.2)).toRingHom with hf
  set N : Matrix (Fin k) (Fin k) ℝ := (genericAffineMatrix hk e).map f with hN
  have hNentry : ∀ r i : Fin k,
      N r i = if h : (r : ℕ) + 1 < k then p (e i) ⟨r, by omega⟩ else 1 := by
    intro r i
    by_cases h : (r : ℕ) + 1 < k
    · simp [hN, genericAffineMatrix, hf, h]
    · simp [hN, genericAffineMatrix, hf, h]
  have hdet : N.det ≠ 0 := by
    have hinj : Function.Injective (MvPolynomial.aeval (fun x : V × Fin d => p x.1 x.2)) := hp
    have : N.det = f (genericAffineMatrix hk e).det := (RingHom.map_det f _).symm
    rw [this]
    intro hzero
    have : (genericAffineMatrix hk e).det = 0 := by
      have h0 : f (genericAffineMatrix hk e).det = f 0 := by rw [hzero, map_zero]
      exact hinj h0
    exact genericAffineMatrix_det_ne_zero hk e he this
  -- an affine dependence would be a nonzero kernel vector of `N`
  by_contra hcon
  push_neg at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  have hker : Matrix.mulVec N w = 0 := by
    funext r
    have hexp : Matrix.mulVec N w r = ∑ i, N r i * w i := by
      simp [Matrix.mulVec, dotProduct]
    rw [hexp]
    show (∑ i, N r i * w i) = (0 : ℝ)
    by_cases h : (r : ℕ) + 1 < k
    · rw [Finset.sum_congr rfl fun i _ => by rw [hNentry r i, dif_pos h, mul_comm]]
      exact hws ⟨r, by omega⟩
    · rw [Finset.sum_congr rfl fun i _ => by rw [hNentry r i, dif_neg h, one_mul]]
      exact hw0
  have : N.det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨w, fun hw => hi₀ (congrFun hw i₀), hker⟩
  exact hdet this

omit [Fintype V] in
/-- **A generic placement is affinely independent** (`main.tex`, proof of Lemma
`lemma:generic-geometric-balancing`). -/
theorem affinelyIndependentPlacement_of_generic (p : V → Fin d → ℝ)
    (hp : GenericPlacement d p) : AffinelyIndependentPlacement d p := by
  classical
  intro s hs
  rw [affineIndependent_iff]
  intro t w hw0 hwsum i hi
  -- enumerate the vertices of `s`
  set E : ↑(s : Set V) ≃ Fin s.card :=
    (Equiv.subtypeEquivRight (by intro x; simp)).trans s.equivFin with hE
  set e : Fin s.card → V := fun j => ((E.symm j : ↑(s : Set V)) : V) with he
  have hinj : Function.Injective e := by
    intro a b hab
    exact E.symm.injective (Subtype.ext hab) |>.symm ▸ rfl
  -- extend the weights by zero
  set W : Fin s.card → ℝ := fun j => if E.symm j ∈ t then w (E.symm j) else 0 with hW
  have hWsum : ∑ j, W j = 0 := by
    rw [hW]
    rw [show (∑ j, (if E.symm j ∈ t then w (E.symm j) else 0))
        = ∑ x : ↑(s : Set V), (if x ∈ t then w x else 0) from
      Equiv.sum_comp E.symm (fun x => if x ∈ t then w x else 0)]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact hw0
  have hWcoord : ∀ r : Fin d, ∑ j, W j * p (e j) r = 0 := by
    intro r
    have hcoord : ∑ x ∈ t, w x * p (x : V) r = 0 := by
      have := congrFun hwsum r
      simpa [Finset.sum_apply] using this
    rw [hW, he]
    rw [show (∑ j, (if E.symm j ∈ t then w (E.symm j) else 0) * p ((E.symm j : ↑(s : Set V)) : V) r)
        = ∑ x : ↑(s : Set V), (if x ∈ t then w x else 0) * p (x : V) r from
      Equiv.sum_comp E.symm (fun x => (if x ∈ t then w x else 0) * p (x : V) r)]
    rw [show (∑ x : ↑(s : Set V), (if x ∈ t then w x else 0) * p (x : V) r)
        = ∑ x : ↑(s : Set V), (if x ∈ t then w x * p (x : V) r else 0) from
      Finset.sum_congr rfl fun x _ => by by_cases hx : x ∈ t <;> simp [hx]]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact hcoord
  have hcard : s.card ≤ d + 1 := hs
  have hall := generic_no_affine_dependence p hp hcard e hinj W hWsum hWcoord
  have := hall (E i)
  rw [hW] at this
  simpa [hi] using this

end RigidityTableaux
