import Mathlib
import RequestProject.GenericEvaluation

/-!
# Red-blue balance and straightening to zero

This file proves Lemma `lemma:red-blue-equiv-straighten-to-zero` of the source article
(`main.tex`, Subsection "Main Results"):

> A multiset of tableaux reduced to semistandard tableaux contains each semistandard
> tableau in equal amounts red and blue if and only if the original bracket polynomial
> straightens to zero.

The proof has two halves.

* The exchange rules do not change the value of a bracket polynomial (this is
  Proposition `proposition:Sylvester-exchange` of the article, together with the
  behaviour of a determinant under permutations of its columns and its vanishing when two
  columns coincide).  Hence the reduced multiset has the same bracket polynomial as the
  original one, and a multiset which contains every tableau equally often red and blue
  evaluates to zero.
* Conversely, distinct semistandard tableaux are linearly independent: this is the
  classical statement that standard monomials form a basis of the bracket ring.  It is
  proved here by the leading-monomial argument: for the lexicographic monomial order in
  which the variable `x_{i,v}` precedes `x_{j,w}` when `i < j`, or `i = j` and `v < w`,
  the leading monomial of the bracket of a strictly increasing column `c` is the diagonal
  monomial `∏ᵢ x_{i, c i}`, so that the leading monomial of a semistandard tableau
  records exactly the multiset of entries of each of its rows, from which the tableau can
  be read back.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

namespace RedBlue

variable {n : ℕ} {V : Type*}

/-! ### The exchange rules do not change the bracket polynomial -/

section Eval

variable {R : Type*} [CommRing R]

/-- Permuting the entries of a column multiplies its bracket by the sign of the
permutation. -/
theorem bracketEval_comp_perm (M : Fin n → V → R) (c : Column n V) (σ : Equiv.Perm (Fin n)) :
    bracketEval M (c ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : R) * bracketEval M c := by
  classical
  have : (Matrix.of fun i j : Fin n => M i (c (σ j)))
      = (Matrix.of fun i j : Fin n => M i (c j)).submatrix id σ := rfl
  simp only [bracketEval, Function.comp_apply, this, Matrix.det_permute']

/-- The bracket of a column with a repeated entry vanishes. -/
theorem bracketEval_eq_zero_of_not_injective (M : Fin n → V → R) (c : Column n V)
    (h : ¬ Function.Injective c) : bracketEval M c = 0 := by
  classical
  rw [Function.not_injective_iff] at h
  obtain ⟨i, j, hij, hne⟩ := h
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])

/-- A tableau one of whose columns has a repeated entry evaluates to zero. -/
theorem tableauEval_eq_zero_of_not_injective (M : Fin n → V → R) (T : Tableau n V)
    {c : Column n V} (hc : c ∈ T.cols) (h : ¬ Function.Injective c) :
    tableauEval M T = 0 := by
  classical
  have : bracketEval M c ∈ T.cols.map (bracketEval M) := Multiset.mem_map_of_mem _ hc
  rw [bracketEval_eq_zero_of_not_injective M c h] at this
  simp [tableauEval, Multiset.prod_eq_zero this]

/-- Each elementary step of the reduction procedure preserves the value of the
corresponding bracket polynomial. -/
theorem tabStep_eval [DecidableEq V] {T : Tableau n V} {r : Multiset (Tableau n V)}
    (h : TabStep T r) (M : Fin n → V → R) :
    tableauEval M T = multisetEval M r := by
  classical
  induction h with
  | permute red c rest σ =>
      simp only [multisetEval, Multiset.map_singleton, Multiset.sum_singleton, tableauEval,
        Multiset.map_cons, Multiset.prod_cons, bracketEval_comp_perm]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;> cases red <;>
        simp [hσ, Tableau.sign]
  | vanish T c hc hinj =>
      simp [multisetEval, tableauEval_eq_zero_of_not_injective M T hc hinj]
  | exchange red c₁ c₂ rest S =>
      set q : Tableau n V → Prop := fun T => ∀ c ∈ T.cols, Function.Injective c with hq
      set X : Multiset (Tableau n V) :=
        ((univ : Finset {T : Finset (Fin n) // T.card = S.card}).val).map
          (fun T =>
            let e := exchangeCols c₁ c₂ S T.1 T.2
            (⟨red, e.1 ::ₘ e.2 ::ₘ rest⟩ : Tableau n V)) with hX
      have hfilter : multisetEval M (X.filter q) = multisetEval M X := by
        conv_rhs => rw [← Multiset.filter_add_not q X]
        simp only [multisetEval, Multiset.map_add, Multiset.sum_add]
        have : ((X.filter (fun T => ¬ q T)).map (tableauEval M)).sum = 0 := by
          refine Multiset.sum_eq_zero ?_
          intro x hx
          obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp hx
          have hTn : ¬ q T := (Multiset.mem_filter.mp hT).2
          obtain ⟨c, hc, hcinj⟩ : ∃ c ∈ T.cols, ¬ Function.Injective c := by
            by_contra hcon
            push_neg at hcon
            exact hTn hcon
          exact tableauEval_eq_zero_of_not_injective M T hc hcinj
        rw [this, add_zero]
      have hXeval : multisetEval M X
          = ((⟨red, c₁ ::ₘ c₂ ::ₘ rest⟩ : Tableau n V).sign : R)
            * ((Multiset.map (bracketEval M) rest).prod
              * ∑ T : {T : Finset (Fin n) // T.card = S.card},
                  bracketEval M (exchangeCols c₁ c₂ S T.1 T.2).1
                    * bracketEval M (exchangeCols c₁ c₂ S T.1 T.2).2) := by
        simp only [hX, multisetEval, Multiset.map_map, Function.comp_apply, tableauEval,
          Multiset.map_cons, Multiset.prod_cons]
        rw [Finset.sum, ← Multiset.sum_map_mul_left, ← Multiset.sum_map_mul_left]
        refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
        intro x _
        simp only [Tableau.sign]
        ring
      rw [show multisetEval M (exchangeResult red c₁ c₂ rest S) = multisetEval M X from
          hfilter ▸ rfl, hXeval,
        ← proposition_Sylvester_exchange M c₁ c₂ S]
      simp [tableauEval, mul_comm, mul_assoc]

/-- One step of the reduction of a multiset of tableaux preserves the value of the
corresponding bracket polynomial. -/
theorem multisetStep_eval [DecidableEq V] {m m' : Multiset (Tableau n V)}
    (h : MultisetStep m m') (M : Fin n → V → R) :
    multisetEval M m = multisetEval M m' := by
  obtain ⟨T, m₀, r, rfl, hstep, rfl⟩ := h
  simp only [multisetEval, Multiset.map_cons, Multiset.sum_cons, Multiset.map_add,
    Multiset.sum_add]
  rw [tabStep_eval hstep M]
  simp [multisetEval, add_comm]

/-- Reduction by exchange rules preserves the value of the corresponding bracket
polynomial (`main.tex`, Subsection "Main Results"). -/
theorem reducesTo_eval [DecidableEq V] {m m' : Multiset (Tableau n V)}
    (h : ReducesTo m m') (M : Fin n → V → R) :
    multisetEval M m = multisetEval M m' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (multisetStep_eval hstep M)

end Eval

/-! ### Grouping the tableaux of a multiset according to their columns -/

section Group

variable {R : Type*} [CommRing R]

variable [DecidableEq V]

/-- The **signed count** of a product of columns in a multiset of tableaux: the number of
red copies minus the number of blue copies. A multiset is `RedBlueBalanced` exactly when
all its signed counts vanish. -/
def signedCount (m : Multiset (Tableau n V)) (c : Multiset (Column n V)) : ℤ :=
  (redCount m c : ℤ) - (blueCount m c : ℤ)

theorem signedCount_zero (c : Multiset (Column n V)) : signedCount (0 : Multiset (Tableau n V)) c = 0 := by
  simp [signedCount, redCount, blueCount]

theorem signedCount_cons (T : Tableau n V) (m : Multiset (Tableau n V))
    (c : Multiset (Column n V)) :
    signedCount (T ::ₘ m) c
      = signedCount m c + (if T.cols = c then (T.sign : ℤ) else 0) := by
  classical
  simp only [signedCount, redCount, blueCount, Multiset.filter_cons, Tableau.sign]
  by_cases hc : T.cols = c <;> by_cases hr : T.red = true <;>
    simp [hc, hr] <;> ring

theorem redBlueBalanced_iff_signedCount (m : Multiset (Tableau n V)) :
    RedBlueBalanced m ↔ ∀ c, signedCount m c = 0 := by
  constructor
  · intro h c
    simp [signedCount, h c]
  · intro h c
    have := h c
    simp only [signedCount, sub_eq_zero] at this
    exact_mod_cast this

/-- The value of a bracket polynomial, grouped according to the products of columns
occurring in it: each product of columns is weighted by its signed count. -/
theorem multisetEval_eq_sum_signedCount (M : Fin n → V → R) (m : Multiset (Tableau n V))
    (C : Finset (Multiset (Column n V))) (hC : ∀ T ∈ m, T.cols ∈ C) :
    multisetEval M m
      = ∑ c ∈ C, ((signedCount m c : ℤ) : R) * (c.map (bracketEval M)).prod := by
  classical
  induction m using Multiset.induction with
  | empty => simp [multisetEval, signedCount_zero]
  | cons T m ih =>
      have hmem : T.cols ∈ C := hC T (Multiset.mem_cons_self _ _)
      have ih' := ih (fun U hU => hC U (Multiset.mem_cons_of_mem hU))
      simp only [multisetEval, Multiset.map_cons, Multiset.sum_cons]
      rw [← multisetEval, ih']
      have : ∑ c ∈ C, ((signedCount (T ::ₘ m) c : ℤ) : R) * (c.map (bracketEval M)).prod
          = (∑ c ∈ C, ((signedCount m c : ℤ) : R) * (c.map (bracketEval M)).prod)
            + ∑ c ∈ C, ((if T.cols = c then (T.sign : ℤ) else 0 : ℤ) : R)
                * (c.map (bracketEval M)).prod := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [signedCount_cons]
        push_cast
        ring
      have h2 : ∑ c ∈ C, ((if T.cols = c then (T.sign : ℤ) else 0 : ℤ) : R)
            * (c.map (bracketEval M)).prod
          = ((T.sign : ℤ) : R) * (T.cols.map (bracketEval M)).prod := by
        refine (Finset.sum_eq_single_of_mem T.cols hmem (fun b _ hb => ?_)).trans ?_
        · simp [Ne.symm hb]
        · simp
      rw [this, h2]
      simp [tableauEval, add_comm]

/-- A multiset of tableaux containing every product of columns equally often red and blue
has zero bracket polynomial, for every matrix. -/
theorem multisetEval_eq_zero_of_redBlueBalanced (M : Fin n → V → R)
    (m : Multiset (Tableau n V)) (h : RedBlueBalanced m) :
    multisetEval M m = 0 := by
  classical
  rw [multisetEval_eq_sum_signedCount M m (m.map Tableau.cols).toFinset
    (fun T hT => Multiset.mem_toFinset.mpr (Multiset.mem_map_of_mem _ hT))]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  rw [(redBlueBalanced_iff_signedCount m).mp h c, Int.cast_zero, zero_mul]

end Group

/-! ### Distinct semistandard tableaux are linearly independent -/

section Independence

open scoped MonomialOrder

variable [DecidableEq V] [LinearOrder V] [Fintype V]

/-- The index of the variable of the generic matrix sitting in the row `i` and in the
column of the vertex `v`, as an element of the lexicographically ordered product
`Fin n ×ₗ V`: the variable `x_{i,v}` precedes `x_{j,w}` when `i < j`, or when `i = j` and
`v < w`. This is the ordering of the variables used to straighten bracket polynomials. -/
def lexIdx (i : Fin n) (v : V) : Fin n ×ₗ V := toLex (i, v)

omit [DecidableEq V] [LinearOrder V] [Fintype V] in
/-- Every variable index is the index of a variable in some row and some column. -/
theorem exists_lexIdx (x : Fin n ×ₗ V) : ∃ i v, x = lexIdx i v :=
  ⟨(ofLex x).1, (ofLex x).2, rfl⟩

omit [DecidableEq V] [LinearOrder V] [Fintype V] in
/-- Two variables coincide exactly when their rows and their vertices coincide. -/
theorem lexIdx_inj {i j : Fin n} {v w : V} : lexIdx i v = lexIdx j w ↔ i = j ∧ v = w := by
  constructor
  · intro h
    have h' : ((i, v) : Fin n × V) = (j, w) := toLex.injective h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  · rintro ⟨rfl, rfl⟩
    rfl

omit [DecidableEq V] [Fintype V] in
/-- The lexicographic order on the variables: `x_{i,v}` precedes `x_{j,w}` when `i < j`,
or when `i = j` and `v < w`. -/
theorem lexIdx_lt_iff {i j : Fin n} {v w : V} :
    lexIdx i v < lexIdx j w ↔ (i < j ∨ (i = j ∧ v < w)) := by
  rw [lexIdx, lexIdx, Prod.Lex.lt_iff]
  simp

/-- The generic matrix, with its variables indexed by the lexicographically ordered
product `Fin n ×ₗ V`. -/
noncomputable def lexMatrix (n : ℕ) (V : Type*) [LinearOrder V] :
    Fin n → V → MvPolynomial (Fin n ×ₗ V) ℚ :=
  fun i v => MvPolynomial.X (lexIdx i v)

/-- Relabelling the variables of the generic matrix by the lexicographically ordered
index set: a bracket polynomial which straightens to zero also vanishes on the relabelled
generic matrix. -/
theorem multisetEval_lexMatrix_eq_zero (m : Multiset (Tableau n V))
    (h : StraightensToZero m) : multisetEval (lexMatrix n V) m = 0 := by
  classical
  have h1 := multisetEval_map
    (MvPolynomial.rename (fun x : Fin n × V => (toLex x : Fin n ×ₗ V))).toRingHom
    (genericMatrix n V) m
  rw [StraightensToZero] at h
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h, map_zero] at h1
  have h2 : (fun (i : Fin n) (v : V) =>
      (MvPolynomial.rename fun x : Fin n × V => (toLex x : Fin n ×ₗ V))
        (genericMatrix n V i v)) = lexMatrix n V := by
    funext i v
    simp [genericMatrix, lexMatrix, lexIdx]
  rw [h2] at h1
  exact h1.symm

/-- The exponent vector of the diagonal monomial `∏ᵢ x_{i, c i}` of the bracket of a
column `c`. -/
noncomputable def diagExp (c : Column n V) : (Fin n ×ₗ V) →₀ ℕ :=
  ∑ i : Fin n, Finsupp.single (lexIdx i (c i)) 1

/-- The exponent vector of the monomial of the expansion of the determinant defining a
bracket which is associated with the permutation `σ`. -/
noncomputable def permExp (c : Column n V) (σ : Equiv.Perm (Fin n)) : (Fin n ×ₗ V) →₀ ℕ :=
  ∑ i : Fin n, Finsupp.single (lexIdx (σ i) (c i)) 1

omit [Fintype V] in
/-- The exponent vector of the monomial associated with a permutation, computed entry by
entry: it has a `1` in the row `j` at the entry `c (σ⁻¹ j)`. -/
theorem permExp_apply (c : Column n V) (σ : Equiv.Perm (Fin n)) (j : Fin n) (v : V) :
    permExp c σ (lexIdx j v) = if c (σ.symm j) = v then 1 else 0 := by
  classical
  rw [permExp, Finset.sum_apply', Finset.sum_eq_single (σ.symm j)]
  · simp [Finsupp.single_apply, lexIdx_inj]
  · intro b _ hb
    have hbj : σ b ≠ j := fun h => hb (by rw [← h, Equiv.symm_apply_apply])
    simp [lexIdx_inj, hbj]
  · simp

omit [DecidableEq V] [LinearOrder V] [Fintype V] in
/-- The diagonal exponent vector is the one of the identity permutation. -/
theorem diagExp_eq_permExp_one (c : Column n V) : diagExp c = permExp c 1 := by
  simp [diagExp, permExp]

omit [Fintype V] in
/-- The exponent vector of the diagonal monomial of the bracket of a column, computed
entry by entry. -/
theorem diagExp_apply (c : Column n V) (j : Fin n) (v : V) :
    diagExp c (lexIdx j v) = if c j = v then 1 else 0 := by
  rw [diagExp_eq_permExp_one, permExp_apply]
  simp

/-- For a strictly increasing column, the diagonal monomial of its bracket is strictly
larger, in the lexicographic monomial order, than the monomial associated with any other
permutation. -/
theorem permExp_lt_diagExp (c : Column n V) (hc : StrictMono c) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ≠ 1) : permExp c σ ≺[MonomialOrder.lex] diagExp c := by
  classical
  set τ : Equiv.Perm (Fin n) := σ.symm with hτ
  have hτne : τ ≠ 1 := fun h => hσ (by simpa using congrArg Equiv.symm h)
  set s : Finset (Fin n) := univ.filter (fun i => τ i ≠ i) with hs
  have hsne : s.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    refine hτne (Equiv.ext (fun i => ?_))
    by_contra hi
    have hmem : i ∈ s := by
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using hi
    simp [hemp] at hmem
  obtain ⟨i₀, hi₀s, hi₀min⟩ : ∃ i₀ ∈ s, ∀ i ∈ s, i₀ ≤ i :=
    ⟨s.min' hsne, s.min'_mem hsne, fun i hi => s.min'_le i hi⟩
  have hτi₀ : τ i₀ ≠ i₀ := by simpa [hs] using hi₀s
  have hsmall : ∀ i, i < i₀ → τ i = i := by
    intro i hi
    by_contra hne
    exact absurd (hi₀min i (by simp [hs, hne])) (not_le.mpr hi)
  have hgt : i₀ < τ i₀ := by
    rcases lt_trichotomy (τ i₀) i₀ with h | h | h
    · exact absurd (τ.injective (hsmall (τ i₀) h)) hτi₀
    · exact absurd h hτi₀
    · exact h
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  refine ⟨lexIdx i₀ (c i₀), ?_, ?_⟩
  · intro x hx
    obtain ⟨j, v, rfl⟩ := exists_lexIdx x
    rw [ofLex_toLex, ofLex_toLex, permExp_apply, diagExp_apply, ← hτ]
    rcases lexIdx_lt_iff.mp hx with hj | ⟨hj, hv⟩
    · rw [hsmall j hj]
    · subst hj
      have h1 : c (τ j) ≠ v := by
        intro h
        exact absurd (h ▸ hc hgt) (not_lt.mpr hv.le)
      have h2 : c j ≠ v := ne_of_gt hv
      simp [h1, h2]
  · rw [ofLex_toLex, ofLex_toLex, permExp_apply, diagExp_apply, ← hτ]
    have h1 : c (τ i₀) ≠ c i₀ := fun h => hτi₀ (hc.injective h)
    simp [h1]

omit [DecidableEq V] [LinearOrder V] [Fintype V] in
/-- A product of variables is the monomial with the corresponding exponent vector. -/
theorem prod_X_eq_monomial (a : Fin n → (Fin n ×ₗ V)) :
    (∏ i : Fin n, MvPolynomial.X (a i) : MvPolynomial (Fin n ×ₗ V) ℚ)
      = MvPolynomial.monomial (∑ i : Fin n, Finsupp.single (a i) 1) 1 := by
  classical
  have key : ∀ s : Finset (Fin n),
      (∏ i ∈ s, MvPolynomial.X (a i) : MvPolynomial (Fin n ×ₗ V) ℚ)
        = MvPolynomial.monomial (∑ i ∈ s, Finsupp.single (a i) 1) 1 := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert j s hj ih =>
        rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, MvPolynomial.X,
          MvPolynomial.monomial_mul, one_mul]
  exact key univ

omit [DecidableEq V] [Fintype V] in
/-- The expansion of a bracket as a sum of monomials, one for each permutation. -/
theorem bracketEval_lexMatrix_eq_sum (c : Column n V) :
    bracketEval (lexMatrix n V) c
      = ∑ σ : Equiv.Perm (Fin n),
          MvPolynomial.monomial (permExp c σ) (((Equiv.Perm.sign σ : ℤ) : ℚ)) := by
  classical
  rw [bracketEval, Matrix.det_apply']
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have hentry : ∀ i : Fin n, (Matrix.of fun i j : Fin n => lexMatrix n V i (c j)) (σ i) i
      = MvPolynomial.X (lexIdx (σ i) (c i)) := fun i => rfl
  rw [Finset.prod_congr rfl (fun i _ => hentry i), prod_X_eq_monomial, ← permExp,
    show ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n ×ₗ V) ℚ)
        = MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℚ)) by simp,
    MvPolynomial.C_mul_monomial, mul_one]

/-- The bracket of a strictly increasing column, as a polynomial in the entries of the
generic matrix, has the diagonal monomial as its leading monomial, with coefficient one. -/
theorem degree_bracketEval (hn : 0 < n) (c : Column n V) (hc : StrictMono c) :
    (MonomialOrder.lex (σ := Fin n ×ₗ V)).degree (bracketEval (lexMatrix n V) c) = diagExp c
      ∧ (MonomialOrder.lex (σ := Fin n ×ₗ V)).Monic (bracketEval (lexMatrix n V) c) := by
  classical
  set mo := MonomialOrder.lex (σ := Fin n ×ₗ V) with hmo
  set f : MvPolynomial (Fin n ×ₗ V) ℚ := MvPolynomial.monomial (diagExp c) 1 with hf
  set g : MvPolynomial (Fin n ×ₗ V) ℚ :=
    ∑ σ ∈ univ.erase (1 : Equiv.Perm (Fin n)),
      MvPolynomial.monomial (permExp c σ) (((Equiv.Perm.sign σ : ℤ) : ℚ)) with hg
  have hsplit : bracketEval (lexMatrix n V) c = f + g := by
    rw [bracketEval_lexMatrix_eq_sum, hf, hg,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
    simp [diagExp_eq_permExp_one]
  have hdegf : mo.degree f = diagExp c := by
    rw [hf, MonomialOrder.degree_monomial]
    simp
  have hdne : diagExp c ≠ 0 := by
    intro h0
    have hval := congrArg (fun e => e (lexIdx (⟨0, hn⟩ : Fin n) (c ⟨0, hn⟩))) h0
    simp [diagExp_apply] at hval
  have hne0 : (0 : mo.syn) < mo.toSyn (diagExp c) := by
    have := mo.toSyn_strictMono (lt_of_le_of_ne (zero_le (diagExp c)) (Ne.symm hdne))
    simpa using this
  have hdegg : mo.degree g ≺[mo] mo.degree f := by
    rw [hdegf, hg]
    refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
    rw [Finset.sup_lt_iff hne0]
    intro σ hσ
    have hσ1 : σ ≠ 1 := (Finset.mem_erase.mp hσ).1
    exact lt_of_le_of_lt (MonomialOrder.degree_monomial_le _) (permExp_lt_diagExp c hc hσ1)
  refine ⟨?_, ?_⟩
  · rw [hsplit, MonomialOrder.degree_add_of_lt hdegg, hdegf]
  · rw [MonomialOrder.Monic, hsplit, MonomialOrder.leadingCoeff_add_of_lt hdegg, hf,
      MonomialOrder.leadingCoeff_monomial]

/-- The exponent vector of the leading monomial of a product of brackets. -/
noncomputable def colsExp (S : Multiset (Column n V)) : (Fin n ×ₗ V) →₀ ℕ :=
  (S.map diagExp).sum

/-- The leading monomial of the product of the brackets of a multiset of strictly
increasing columns is the sum of the diagonal monomials, with coefficient one. -/
theorem degree_prod_bracketEval (hn : 0 < n) (S : Multiset (Column n V))
    (hS : ∀ c ∈ S, StrictMono c) :
    (MonomialOrder.lex (σ := Fin n ×ₗ V)).degree (S.map (bracketEval (lexMatrix n V))).prod
        = colsExp S
      ∧ (MonomialOrder.lex (σ := Fin n ×ₗ V)).Monic
          (S.map (bracketEval (lexMatrix n V))).prod := by
  classical
  induction S using Multiset.induction with
  | empty =>
      refine ⟨?_, ?_⟩
      · simp only [Multiset.map_zero, Multiset.prod_zero, colsExp, Multiset.sum_zero]
        rw [← MvPolynomial.C_1, MonomialOrder.degree_C]
      · rw [MonomialOrder.Monic]
        simp only [Multiset.map_zero, Multiset.prod_zero]
        rw [← MvPolynomial.C_1, MonomialOrder.leadingCoeff_C]
  | cons c S ih =>
      obtain ⟨ihdeg, ihmonic⟩ := ih (fun d hd => hS d (Multiset.mem_cons_of_mem hd))
      obtain ⟨hdeg, hmonic⟩ := degree_bracketEval hn c (hS c (Multiset.mem_cons_self _ _))
      have hprod : ((c ::ₘ S).map (bracketEval (lexMatrix n V))).prod
          = bracketEval (lexMatrix n V) c * (S.map (bracketEval (lexMatrix n V))).prod := by
        simp
      have hlc : (MonomialOrder.lex (σ := Fin n ×ₗ V)).leadingCoeff
            (bracketEval (lexMatrix n V) c)
          * (MonomialOrder.lex (σ := Fin n ×ₗ V)).leadingCoeff
            (S.map (bracketEval (lexMatrix n V))).prod ≠ 0 := by
        rw [hmonic, ihmonic]
        norm_num
      refine ⟨?_, ?_⟩
      · rw [hprod, MonomialOrder.degree_mul_of_mul_leadingCoeff_ne_zero hlc, hdeg, ihdeg]
        simp [colsExp]
      · rw [hprod]
        exact MonomialOrder.Monic.mul hmonic ihmonic

omit [Fintype V] in
/-- The leading monomial of a product of brackets records, for each row `i` and each
vertex `v`, the number of columns whose `i`-th entry is `v`. -/
theorem colsExp_apply (S : Multiset (Column n V)) (i : Fin n) (v : V) :
    colsExp S (lexIdx i v) = (S.map (fun c => c i)).count v := by
  classical
  induction S using Multiset.induction with
  | empty => simp [colsExp]
  | cons c S ih =>
      simp only [colsExp, Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply,
        Multiset.count_cons] at *
      rw [ih, diagExp_apply]
      by_cases h : c i = v
      · simp [h, add_comm]
      · simp [h, Ne.symm h, add_comm]

omit [Fintype V] in
/-- **Distinct semistandard tableaux have distinct leading monomials.** A semistandard
tableau can be read back from the multiset of the entries of each of its rows. -/
theorem colsExp_injective (hn : 0 < n) {S S' : Multiset (Column n V)}
    (h : IsSemistandard (⟨true, S⟩ : Tableau n V))
    (h' : IsSemistandard (⟨true, S'⟩ : Tableau n V))
    (he : colsExp S = colsExp S') : S = S' := by
  classical
  obtain ⟨L, hL, hLmono, hLchain⟩ := h
  obtain ⟨L', hL', hL'mono, hL'chain⟩ := h'
  have hLS : (↑L : Multiset (Column n V)) = S := hL
  have hLS' : (↑L' : Multiset (Column n V)) = S' := hL'
  haveI : Trans (fun c c' : Column n V => ∀ i, c i ≤ c' i)
      (fun c c' : Column n V => ∀ i, c i ≤ c' i)
      (fun c c' : Column n V => ∀ i, c i ≤ c' i) :=
    ⟨fun h1 h2 i => le_trans (h1 i) (h2 i)⟩
  have hLpair : L.Pairwise (fun c c' : Column n V => ∀ i, c i ≤ c' i) :=
    List.isChain_iff_pairwise.mp hLchain
  have hL'pair : L'.Pairwise (fun c c' : Column n V => ∀ i, c i ≤ c' i) :=
    List.isChain_iff_pairwise.mp hL'chain
  have hrow : ∀ i : Fin n, L.map (fun c => c i) = L'.map (fun c => c i) := by
    intro i
    have hcount : ∀ v : V, ((L.map (fun c => c i) : List V) : Multiset V).count v
        = ((L'.map (fun c => c i) : List V) : Multiset V).count v := by
      intro v
      have h1 := congrArg (fun e => e (lexIdx i v)) he
      simp only [colsExp_apply] at h1
      rw [← hLS, ← hLS'] at h1
      simpa using h1
    have hperm : (L.map (fun c => c i)).Perm (L'.map (fun c => c i)) := by
      rw [← Multiset.coe_eq_coe]
      exact Multiset.ext.mpr hcount
    exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba)
      (List.pairwise_map.mpr (hLpair.imp (fun hh => hh i)))
      (List.pairwise_map.mpr (hL'pair.imp (fun hh => hh i))) hperm
  have hlen : L.length = L'.length := by
    have hl := congrArg List.length (hrow ⟨0, hn⟩)
    simpa using hl
  have hLL' : L = L' := by
    refine List.ext_getElem hlen (fun k hk hk' => ?_)
    funext i
    have h2 := congrArg (fun l : List V => l[k]?) (hrow i)
    simp only [List.getElem?_map] at h2
    rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk'] at h2
    simpa using h2
  rw [← hLS, ← hLS', hLL']

/-- **Linear independence of the semistandard tableaux.** A multiset of semistandard
tableaux whose bracket polynomial straightens to zero contains each of them equally often
red and blue. -/
theorem redBlueBalanced_of_straightensToZero (hn : 0 < n) (m : Multiset (Tableau n V))
    (hss : ∀ T ∈ m, IsSemistandard T) (h0 : StraightensToZero m) :
    RedBlueBalanced m := by
  classical
  rw [redBlueBalanced_iff_signedCount]
  by_contra hcon
  push_neg at hcon
  obtain ⟨c₀, hc₀⟩ := hcon
  set C : Finset (Multiset (Column n V)) := (m.map Tableau.cols).toFinset with hC
  have hCmem : ∀ T ∈ m, T.cols ∈ C :=
    fun T hT => Multiset.mem_toFinset.mpr (Multiset.mem_map_of_mem _ hT)
  have hsub : ∀ c : Multiset (Column n V), signedCount m c ≠ 0 → c ∈ C := by
    intro c hne
    by_contra hnc
    refine hne ?_
    unfold signedCount redCount blueCount
    have hr : m.filter (fun T => T.red = true ∧ T.cols = c) = 0 := by
      refine Multiset.filter_eq_nil.mpr (fun T hT hTc => ?_)
      exact hnc (hTc.2 ▸ hCmem T hT)
    have hb : m.filter (fun T => T.red = false ∧ T.cols = c) = 0 := by
      refine Multiset.filter_eq_nil.mpr (fun T hT hTc => ?_)
      exact hnc (hTc.2 ▸ hCmem T hT)
    rw [hr, hb]
    simp
  set D : Finset (Multiset (Column n V)) := C.filter (fun c => signedCount m c ≠ 0) with hD
  have hDne : D.Nonempty := ⟨c₀, by simp [hD, hsub c₀ hc₀, hc₀]⟩
  obtain ⟨cmax, hmaxD, hmax⟩ :=
    D.exists_max_image (fun c => (MonomialOrder.lex (σ := Fin n ×ₗ V)).toSyn (colsExp c)) hDne
  have hmaxC : cmax ∈ C := (Finset.mem_filter.mp hmaxD).1
  have hmaxne : signedCount m cmax ≠ 0 := (Finset.mem_filter.mp hmaxD).2
  have hssC : ∀ c ∈ C, IsSemistandard (⟨true, c⟩ : Tableau n V) := by
    intro c hc
    obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hc)
    exact hss T hT
  have hstrict : ∀ c ∈ C, ∀ d ∈ c, StrictMono d := by
    intro c hc d hd
    obtain ⟨L, hL, hLmono, _⟩ := hssC c hc
    have hLc : (↑L : Multiset (Column n V)) = c := hL
    exact hLmono d (by rwa [← hLc] at hd)
  have heval : multisetEval (lexMatrix n V) m = 0 := multisetEval_lexMatrix_eq_zero m h0
  rw [multisetEval_eq_sum_signedCount (lexMatrix n V) m C hCmem] at heval
  have hcoeff := congrArg (MvPolynomial.coeff (colsExp cmax)) heval
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hcoeff
  have hterm : ∀ c ∈ C, c ≠ cmax →
      MvPolynomial.coeff (colsExp cmax)
        (((signedCount m c : ℤ) : MvPolynomial (Fin n ×ₗ V) ℚ)
          * (c.map (bracketEval (lexMatrix n V))).prod) = 0 := by
    intro c hc hcne
    by_cases hzero : signedCount m c = 0
    · simp [hzero]
    · have hcD : c ∈ D := Finset.mem_filter.mpr ⟨hc, hzero⟩
      obtain ⟨hdeg, -⟩ := degree_prod_bracketEval hn c (hstrict c hc)
      have hlt : (MonomialOrder.lex (σ := Fin n ×ₗ V)).degree
          (c.map (bracketEval (lexMatrix n V))).prod ≺[MonomialOrder.lex] colsExp cmax := by
        rw [hdeg]
        refine lt_of_le_of_ne (hmax c hcD) (fun heq => ?_)
        exact hcne (colsExp_injective hn (hssC c hc) (hssC cmax hmaxC)
          ((MonomialOrder.lex (σ := Fin n ×ₗ V)).toSyn.injective heq))
      rw [show ((signedCount m c : ℤ) : MvPolynomial (Fin n ×ₗ V) ℚ)
          = MvPolynomial.C ((signedCount m c : ℤ) : ℚ) by simp,
        MvPolynomial.coeff_C_mul, MonomialOrder.coeff_eq_zero_of_lt hlt, mul_zero]
  rw [Finset.sum_eq_single_of_mem cmax hmaxC hterm] at hcoeff
  obtain ⟨hdegmax, hmonicmax⟩ := degree_prod_bracketEval hn cmax (hstrict cmax hmaxC)
  rw [show ((signedCount m cmax : ℤ) : MvPolynomial (Fin n ×ₗ V) ℚ)
      = MvPolynomial.C ((signedCount m cmax : ℤ) : ℚ) by simp,
    MvPolynomial.coeff_C_mul,
    show MvPolynomial.coeff (colsExp cmax) (cmax.map (bracketEval (lexMatrix n V))).prod
      = (MonomialOrder.lex (σ := Fin n ×ₗ V)).leadingCoeff
          (cmax.map (bracketEval (lexMatrix n V))).prod from by
        rw [MonomialOrder.leadingCoeff, hdegmax],
    hmonicmax, mul_one] at hcoeff
  exact hmaxne (by exact_mod_cast hcoeff)

/-! ### The counterexample for tableaux of height zero -/

/-- The lemma `lemma:red-blue-equiv-straighten-to-zero` of the source article fails for
tableaux of height `n = 0`, which is why the hypothesis `0 < n` is added to its formal
statement: the multiset consisting of one red tableau with no column and one blue tableau
with one column is already reduced and semistandard, its bracket polynomial is `1 - 1 = 0`
and yet it is not red-blue balanced. -/
theorem not_redBlue_equiv_straightensToZero_of_height_zero :
    ¬ (∀ (m m' : Multiset (Tableau 0 (Fin 1))), ReducesTo m m' →
        (∀ T ∈ m', IsSemistandard T) → (RedBlueBalanced m' ↔ StraightensToZero m)) := by
  classical
  intro hall
  set c : Column 0 (Fin 1) := fun i => i.elim0 with hc
  set m : Multiset (Tableau 0 (Fin 1)) :=
    {(⟨true, 0⟩ : Tableau 0 (Fin 1)), (⟨false, {c}⟩ : Tableau 0 (Fin 1))} with hm
  have hss : ∀ T ∈ m, IsSemistandard T := by
    intro T hT
    have hT' : T = ⟨true, 0⟩ ∨ T = ⟨false, {c}⟩ := by
      simpa [hm] using hT
    rcases hT' with rfl | rfl
    · exact ⟨[], by simp, by simp, by simp⟩
    · refine ⟨[c], by simp, ?_, by simp⟩
      intro d hd i
      exact i.elim0
  have hstr : StraightensToZero m := by
    simp [StraightensToZero, multisetEval, hm, tableauEval, Tableau.sign, bracketEval]
  have hbal := (hall m m Relation.ReflTransGen.refl hss).2 hstr
  have h0 := hbal 0
  rw [redCount, blueCount] at h0
  have hcne : ({c} : Multiset (Column 0 (Fin 1))) ≠ 0 := by simp
  simp [hm, Multiset.filter_singleton, hcne] at h0

end Independence

end RedBlue

/-- **Lemma `lemma:red-blue-equiv-straighten-to-zero` of the source article** (`main.tex`,
Subsection "Main Results"): *"a multiset of tableaux reduced to semistandard tableaux
contains each semistandard tableau in equal amounts red and blue if and only if the
original bracket polynomial straightens to zero"*. In particular the condition does not
depend on the chosen reduction, so the conditions for an orientation to be balanced are
well defined.

The hypothesis `0 < n` on the height of the tableaux, which the source article leaves
implicit (its tableaux have `n = d + 1` rows), is necessary: see
`RigidityTableaux.RedBlue.not_redBlue_equiv_straightensToZero_of_height_zero` for the
counterexample with `n = 0`. -/
theorem lemma_red_blue_equiv_straighten_to_zero {V : Type*} [DecidableEq V] [LinearOrder V]
    [Fintype V] {n : ℕ} (hn : 0 < n) (m m' : Multiset (Tableau n V)) (hred : ReducesTo m m')
    (hss : ∀ T ∈ m', IsSemistandard T) :
    RedBlueBalanced m' ↔ StraightensToZero m := by
  constructor
  · intro h
    rw [StraightensToZero, RedBlue.reducesTo_eval hred (genericMatrix n V)]
    exact RedBlue.multisetEval_eq_zero_of_redBlueBalanced _ m' h
  · intro h
    refine RedBlue.redBlueBalanced_of_straightensToZero hn m' hss ?_
    rw [StraightensToZero, ← RedBlue.reducesTo_eval hred (genericMatrix n V)]
    exact h

end RigidityTableaux
