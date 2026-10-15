import RequestProject.Orientation

/-!
# Evaluating bracket polynomials at a generic placement

This file develops the material behind Lemma `lemma:generic-evaluation-straightening-new`
of the source article (`main.tex`, Section "Proofs"): *a bracket polynomial which is
multi-homogeneous in the vertices evaluates to zero at a generic placement if and only if
it straightens to zero*.

The two directions are separated:

* `evalAtPlacement_eq_zero_of_straightensToZero`: a bracket polynomial which straightens
  to zero evaluates to zero at *every* placement (no genericity or multi-homogeneity is
  needed here);
* `straightensToZero_of_evalAtPlacement_zero`: conversely, if a multi-homogeneous bracket
  polynomial vanishes at one generic placement, then it straightens to zero. The proof
  uses that the coordinates of a generic placement are algebraically independent to see
  that the polynomial vanishes at *all* placements, and then the multi-homogeneity to
  pass from the affine chart `M = (p, 1)` used in the source article to an arbitrary
  matrix, by scaling the columns.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Transport of bracket evaluation along a ring homomorphism -/

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- The bracket of a column commutes with ring homomorphisms. -/
theorem bracketEval_map (φ : R →+* R') (M : Fin n → V → R) (c : Column n V) :
    φ (bracketEval M c) = bracketEval (fun i v => φ (M i v)) c := by
  rw [bracketEval, RingHom.map_det]
  rfl

/-- The evaluation of a tableau commutes with ring homomorphisms. -/
theorem tableauEval_map (φ : R →+* R') (M : Fin n → V → R) (T : Tableau n V) :
    φ (tableauEval M T) = tableauEval (fun i v => φ (M i v)) T := by
  unfold tableauEval
  rw [map_mul, map_intCast, map_multiset_prod, Multiset.map_map]
  congr 1
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro c _
  exact bracketEval_map φ M c

/-- The evaluation of a bracket polynomial commutes with ring homomorphisms. -/
theorem multisetEval_map (φ : R →+* R') (M : Fin n → V → R) (m : Multiset (Tableau n V)) :
    φ (multisetEval M m) = multisetEval (fun i v => φ (M i v)) m := by
  unfold multisetEval
  rw [map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro T _
  exact tableauEval_map φ M T

/-! ### Scaling the columns of the matrix -/

/-- Grouping the entries of a column by their value: the product over the boxes of a
column of a function of the entry is the product over the vertices of that function
raised to the multiplicity `deg_v` of the source article. -/
theorem prod_comp_colDegree (γ : V → R) (c : Column n V) :
    ∏ j : Fin n, γ (c j) = ∏ v : V, γ v ^ colDegree c v := by
  classical
  rw [Finset.prod_comp γ c]
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro v _ hv
  have hz : colDegree c v = 0 := by
    rw [colDegree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _ hj
    exact hv (Finset.mem_image.mpr ⟨j, mem_univ j, hj⟩)
  rw [colDegree] at hz
  rw [hz, pow_zero]

/-- Scaling the `v`-th column of the matrix by `γ v` multiplies the bracket of a column
by `∏_v γ_v^{deg_v}`. -/
theorem bracketEval_scale (γ : V → R) (M : Fin n → V → R) (c : Column n V) :
    bracketEval (fun i v => γ v * M i v) c
      = (∏ v : V, γ v ^ colDegree c v) * bracketEval M c := by
  rw [bracketEval, bracketEval, ← prod_comp_colDegree γ c]
  exact Matrix.det_mul_row (fun j => γ (c j)) (Matrix.of fun i j : Fin n => M i (c j))

/-- Scaling the `v`-th column of the matrix by `γ v` multiplies the evaluation of a
tableau by `∏_v γ_v^{deg_v}`, where `deg` is the vertex multi-degree of the tableau. -/
theorem tableauEval_scale (γ : V → R) (M : Fin n → V → R) (T : Tableau n V) :
    tableauEval (fun i v => γ v * M i v) T
      = (∏ v : V, γ v ^ tableauDegree T v) * tableauEval M T := by
  unfold tableauEval tableauDegree
  have key : ∀ s : Multiset (Column n V),
      (s.map (bracketEval fun i v => γ v * M i v)).prod
        = (∏ v : V, γ v ^ (s.map (fun c => colDegree c v)).sum)
          * (s.map (bracketEval M)).prod := by
    intro s
    induction s using Multiset.induction with
    | empty => simp
    | cons c s ih =>
        have hexp : (∏ v : V, γ v ^ (Multiset.map (fun c => colDegree c v) (c ::ₘ s)).sum)
            = (∏ v : V, γ v ^ colDegree c v)
              * ∏ v : V, γ v ^ (Multiset.map (fun c => colDegree c v) s).sum := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun v _ => ?_
          rw [Multiset.map_cons, Multiset.sum_cons, pow_add]
        rw [hexp, Multiset.map_cons, Multiset.prod_cons, bracketEval_scale, ih,
          Multiset.map_cons, Multiset.prod_cons]
        ring
  rw [key]
  ring

/-- Scaling the `v`-th column of the matrix by `γ v` multiplies a multi-homogeneous
bracket polynomial by `∏_v γ_v^{deg_v}`. This is the reason why the source article
requires multi-homogeneity in Lemma `lemma:generic-evaluation-straightening-new`. -/
theorem multisetEval_scale_of_multiHomogeneous (γ : V → R) (M : Fin n → V → R)
    {m : Multiset (Tableau n V)} (hm : MultiHomogeneous m) {T₀ : Tableau n V} (hT₀ : T₀ ∈ m) :
    multisetEval (fun i v => γ v * M i v) m
      = (∏ v : V, γ v ^ tableauDegree T₀ v) * multisetEval M m := by
  unfold multisetEval
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro T hT
  rw [tableauEval_scale]
  congr 1
  exact Finset.prod_congr rfl fun v _ => by rw [hm T hT T₀ hT₀ v]

/-! ### The affine chart used in the source article -/

variable {d : ℕ}

/-- The generic matrix of the affine chart `M = (p, 1)` of the source article: the
`(d+1) × |V|` matrix whose first `d` rows are independent indeterminates and whose last
row is constant `1`. -/
noncomputable def genericChartMatrix (d : ℕ) (V : Type*) :
    Fin (d + 1) → V → MvPolynomial (Fin d × V) ℚ :=
  fun i v => if h : (i : ℕ) < d then MvPolynomial.X (⟨i, h⟩, v) else 1

/-- Evaluating the generic chart matrix at a placement gives the matrix `M = (p,1)` of
the source article. -/
theorem aeval_genericChartMatrix (p : V → Fin d → ℝ) (i : Fin (d + 1)) (v : V) :
    (MvPolynomial.aeval (fun x : Fin d × V => p x.2 x.1) : MvPolynomial (Fin d × V) ℚ →ₐ[ℚ] ℝ)
        (genericChartMatrix d V i v) = placementMatrix p i v := by
  unfold genericChartMatrix placementMatrix
  by_cases h : (i : ℕ) < d
  · rw [dif_pos h, dif_pos h, MvPolynomial.aeval_X]
  · rw [dif_neg h, dif_neg h, map_one]

/-- The evaluation of a bracket polynomial at a placement `p` is the evaluation at `p` of
the polynomial obtained from the generic chart matrix. -/
theorem evalAtPlacement_eq_aeval (p : V → Fin d → ℝ) (m : Multiset (Tableau (d + 1) V)) :
    evalAtPlacement p m
      = (MvPolynomial.aeval (fun x : Fin d × V => p x.2 x.1) :
            MvPolynomial (Fin d × V) ℚ →ₐ[ℚ] ℝ)
          (multisetEval (genericChartMatrix d V) m) := by
  unfold evalAtPlacement
  refine Eq.trans ?_ (multisetEval_map
    ((MvPolynomial.aeval (fun x : Fin d × V => p x.2 x.1) :
      MvPolynomial (Fin d × V) ℚ →ₐ[ℚ] ℝ) : MvPolynomial (Fin d × V) ℚ →+* ℝ)
    (genericChartMatrix d V) m).symm
  congr 1
  funext i v
  exact (aeval_genericChartMatrix p i v).symm

/-! ### The two directions of Lemma `lemma:generic-evaluation-straightening-new` -/

/-- A bracket polynomial which straightens to zero evaluates to zero at every placement.
This is the easy direction of Lemma `lemma:generic-evaluation-straightening-new` of the
source article. -/
theorem evalAtPlacement_eq_zero_of_straightensToZero (p : V → Fin d → ℝ)
    (m : Multiset (Tableau (d + 1) V)) (hm : StraightensToZero m) :
    evalAtPlacement p m = 0 := by
  unfold evalAtPlacement
  have h := multisetEval_map
    ((MvPolynomial.aeval (fun x : Fin (d + 1) × V => placementMatrix p x.1 x.2) :
      MvPolynomial (Fin (d + 1) × V) ℚ →ₐ[ℚ] ℝ) : MvPolynomial (Fin (d + 1) × V) ℚ →+* ℝ)
    (genericMatrix (d + 1) V) m
  rw [hm] at h
  simpa [genericMatrix] using h.symm

/-- The bracket polynomial of the generic matrix, transported to real coefficients. -/
theorem multisetEval_genericMatrix_map (m : Multiset (Tableau n V)) :
    MvPolynomial.map (algebraMap ℚ ℝ) (multisetEval (genericMatrix n V) m)
      = multisetEval (fun (i : Fin n) (v : V) =>
          (MvPolynomial.X (i, v) : MvPolynomial (Fin n × V) ℝ)) m := by
  have h := multisetEval_map
    (MvPolynomial.map (algebraMap ℚ ℝ) : MvPolynomial (Fin n × V) ℚ →+* MvPolynomial (Fin n × V) ℝ)
    (genericMatrix n V) m
  simpa [genericMatrix] using h

/-- If a multi-homogeneous bracket polynomial vanishes at one generic placement, then it
straightens to zero. This is the substantial direction of Lemma
`lemma:generic-evaluation-straightening-new` of the source article. -/
theorem straightensToZero_of_evalAtPlacement_zero (m : Multiset (Tableau (d + 1) V))
    (hm : MultiHomogeneous m) (p : V → Fin d → ℝ) (hp : GenericPlacement d p)
    (h0 : evalAtPlacement p m = 0) : StraightensToZero m := by
  classical
  -- the polynomial in the affine chart vanishes identically
  have hchart : multisetEval (genericChartMatrix d V) m = 0 := by
    have hinj : Function.Injective
        (MvPolynomial.aeval (fun x : Fin d × V => p x.2 x.1) :
          MvPolynomial (Fin d × V) ℚ →ₐ[ℚ] ℝ) := by
      have hswap : AlgebraicIndependent ℚ
          ((fun ik : V × Fin d => p ik.1 ik.2) ∘ (fun x : Fin d × V => (x.2, x.1))) :=
        hp.comp _ (fun x y hxy => by
          have h1 : x.2 = y.2 := congrArg Prod.fst hxy
          have h2 : x.1 = y.1 := congrArg Prod.snd hxy
          exact Prod.ext h2 h1)
      exact hswap
    have := evalAtPlacement_eq_aeval p m
    rw [h0] at this
    exact hinj (by rw [← this, map_zero])
  -- hence the bracket polynomial vanishes at every placement
  have hall : ∀ q : V → Fin d → ℝ, evalAtPlacement q m = 0 := by
    intro q
    rw [evalAtPlacement_eq_aeval q m, hchart, map_zero]
  -- hence at every matrix whose last row has no zero entry
  have hA : ∀ A : Fin (d + 1) → V → ℝ, (∀ v : V, A (Fin.last d) v ≠ 0) →
      multisetEval A m = 0 := by
    intro A hlast
    rcases Multiset.empty_or_exists_mem m with rfl | ⟨T₀, hT₀⟩
    · simp [multisetEval]
    · set γ : V → ℝ := fun v => A (Fin.last d) v with hγ
      set q : V → Fin d → ℝ := fun v j => A j.castSucc v / γ v with hq
      have hB : ∀ (i : Fin (d + 1)) (v : V), A i v = γ v * placementMatrix q i v := by
        intro i v
        unfold placementMatrix
        by_cases h : (i : ℕ) < d
        · rw [dif_pos h]
          have hi : (⟨(i : ℕ), h⟩ : Fin d).castSucc = i := by
            apply Fin.ext; simp
          rw [hq]
          simp only [hi]
          have hγv : γ v ≠ 0 := hlast v
          field_simp
        · rw [dif_neg h, mul_one]
          have : i = Fin.last d := by
            apply Fin.ext
            have := i.2
            simp only [Fin.val_last]
            omega
          rw [this]
      have hAeq : A = fun i v => γ v * placementMatrix q i v := by
        funext i v; exact hB i v
      rw [hAeq, multisetEval_scale_of_multiHomogeneous γ (placementMatrix q) hm hT₀]
      have := hall q
      unfold evalAtPlacement at this
      rw [this, mul_zero]
  -- so the bracket polynomial is the zero polynomial
  have hpoly : multisetEval (fun (i : Fin (d + 1)) (v : V) =>
      (MvPolynomial.X (i, v) : MvPolynomial (Fin (d + 1) × V) ℝ)) m = 0 := by
    set F := multisetEval (fun (i : Fin (d + 1)) (v : V) =>
      (MvPolynomial.X (i, v) : MvPolynomial (Fin (d + 1) × V) ℝ)) m with hF
    set g : MvPolynomial (Fin (d + 1) × V) ℝ := ∏ v : V, MvPolynomial.X (Fin.last d, v) with hg
    have hgF : g * F = 0 := by
      refine MvPolynomial.funext ?_
      intro x
      rw [map_mul, map_zero]
      by_cases hz : ∃ v : V, x (Fin.last d, v) = 0
      · obtain ⟨v, hv⟩ := hz
        have : MvPolynomial.eval x g = 0 := by
          rw [hg, map_prod]
          refine Finset.prod_eq_zero (mem_univ v) ?_
          rw [MvPolynomial.eval_X, hv]
        rw [this, zero_mul]
      · push_neg at hz
        have hFx : MvPolynomial.eval x F = 0 := by
          have h := multisetEval_map (MvPolynomial.eval x)
            (fun (i : Fin (d + 1)) (v : V) => (MvPolynomial.X (i, v) :
              MvPolynomial (Fin (d + 1) × V) ℝ)) m
          rw [← hF] at h
          rw [h]
          simpa using hA (fun i v => x (i, v)) (fun v => hz v)
        rw [hFx, mul_zero]
    have hgne : g ≠ 0 := by
      rw [hg]
      refine Finset.prod_ne_zero_iff.mpr fun v _ => ?_
      exact MvPolynomial.X_ne_zero _
    rcases mul_eq_zero.mp hgF with h | h
    · exact absurd h hgne
    · exact h
  have := multisetEval_genericMatrix_map (n := d + 1) (V := V) m
  rw [hpoly] at this
  have hinj : Function.Injective
      (MvPolynomial.map (algebraMap ℚ ℝ) :
        MvPolynomial (Fin (d + 1) × V) ℚ → MvPolynomial (Fin (d + 1) × V) ℝ) :=
    MvPolynomial.map_injective _ (algebraMap ℚ ℝ).injective
  exact hinj (by rw [this, map_zero])

end RigidityTableaux
