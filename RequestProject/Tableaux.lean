import Mathlib
import RequestProject.Sylvester

/-!
# Tableaux, exchange rules and the bracket ring

This file formalizes the combinatorial and algebraic notions of the source article
(`main.tex`, Subsection "Main Results" and Subsection "From geometric to combinatorial
balancing"):

* a **tableau** is a blue or red rectangular array of boxes filled with entries from an
  ordered set `V`, i.e. a colour together with a (commutative) product of columns;
* the **exchange rules** following Fulton;
* **semistandard** tableaux (strictly increasing down columns, weakly increasing along
  rows);
* the evaluation of tableaux as products of maximal minors (brackets) of a matrix, and
  the notion of a bracket polynomial **straightening to zero**, i.e. lying in the
  Plücker ideal;
* Proposition `proposition:Sylvester-exchange` (page 108 of Fulton, attributed to
  Sylvester), which is what makes the exchange rules valid relations between brackets;
* Lemma `lemma:semistandard-tableaux-span`, which says that every multiset of tableaux
  reduces, using exchange rules, to a multiset of semistandard tableaux;
* Lemma `lemma:red-blue-equiv-straighten-to-zero`: a reduced multiset contains each
  semistandard tableau in equal amounts red and blue if and only if the corresponding
  bracket polynomial straightens to zero.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

/-- A **column** of height `n` filled with entries from `V`, written `[i_1 … i_n]` in the
source article (`main.tex`, Subsection "Main Results"). -/
abbrev Column (n : ℕ) (V : Type*) := Fin n → V

/-- A **tableau**: a colour (`red = true` for a plus sign, `red = false` for blue, i.e. a
minus sign) together with the commutative product of its columns, recorded as a
multiset of columns. This is the notion of tableau of the source article
(`main.tex`, Subsection "Main Results"): *"By a tableau we mean a blue or red
rectangular array of boxes, filled with entries from an ordered set `V`"*. -/
structure Tableau (n : ℕ) (V : Type*) where
  /-- The colour of the tableau: `true` is red (a plus sign), `false` is blue. -/
  red : Bool
  /-- The columns of the tableau, as a commutative (multiset) product. -/
  cols : Multiset (Column n V)

namespace Tableau

variable {n : ℕ} {V : Type*}

/-- The sign of a tableau: `+1` if red, `-1` if blue (`main.tex`, Subsection
"Main Results": *"blue for a minus sign, red otherwise"*). -/
def sign (T : Tableau n V) : ℤ := if T.red then 1 else -1

end Tableau

/-! ### Semistandard tableaux -/

variable {n : ℕ} {V : Type*}

/-- A tableau is **semistandard** if its columns can be arranged so that entries strictly
increase down each column and weakly increase along each row (`main.tex`, Subsection
"Main Results": *"Tableaux that strictly increase down columns and weakly increase along
rows are called semistandard"*). -/
def IsSemistandard [LinearOrder V] (T : Tableau n V) : Prop :=
  ∃ L : List (Column n V), (L : Multiset (Column n V)) = T.cols ∧
    (∀ c ∈ L, StrictMono c) ∧ L.IsChain (fun c c' => ∀ i, c i ≤ c' i)

/-! ### Exchange rules -/

/-- The pair of columns obtained from `c₁` and `c₂` by interchanging the boxes of `c₁` in
the positions `S` with the boxes of `c₂` in the positions `T`, maintaining the vertical
order (`main.tex`, Subsection "Main Results": *"Given a tableau `T`, fix two columns and
`r` boxes in the first column. Replace `T` by all tableaux obtained by exchanging those
`r` boxes with every choice of `r` boxes in the second column, maintaining the vertical
order"*). -/
def exchangeCols (c₁ c₂ : Column n V) (S T : Finset (Fin n)) (h : T.card = S.card) :
    Column n V × Column n V :=
  ( fun i => if hi : i ∈ S then
      c₂ (T.orderIsoOfFin h ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩))
    else c₁ i,
    fun j => if hj : j ∈ T then
      c₁ (S.orderIsoOfFin rfl ((T.orderIsoOfFin h).symm ⟨j, hj⟩))
    else c₂ j )

/-- The multiset of tableaux replacing a tableau `T = ⟨red, c₁ ⬝ c₂ ⬝ rest⟩` under the
exchange rule which exchanges the boxes of `c₁` in positions `S` with all choices of
`#S` boxes of `c₂`. Tableaux with a repeated entry in a column vanish and are
discarded, as in the source article (`main.tex`, Subsection "Main Results": *"Each
resulting tableau inherits the same colour as `T`, and vanishes if an entry is repeated
within a column"*). -/
noncomputable def exchangeResult [DecidableEq V] (red : Bool) (c₁ c₂ : Column n V)
    (rest : Multiset (Column n V)) (S : Finset (Fin n)) : Multiset (Tableau n V) := by
  classical
  exact (((univ : Finset {T : Finset (Fin n) // T.card = S.card}).val).map
      (fun T =>
        let e := exchangeCols c₁ c₂ S T.1 T.2
        (⟨red, e.1 ::ₘ e.2 ::ₘ rest⟩ : Tableau n V))).filter
    (fun T => ∀ c ∈ T.cols, Function.Injective c)

/-- One elementary step of the reduction procedure on tableaux, as allowed in the source
article (`main.tex`, Subsection "Main Results", and the proof of Lemma
`lemma:semistandard-tableaux-span`): a column may be permuted, swapping the colour by
the sign of the permutation; a tableau with a repeated entry in a column vanishes; and
any exchange rule may be applied. -/
inductive TabStep [DecidableEq V] : Tableau n V → Multiset (Tableau n V) → Prop
  /-- Permuting the entries of one column, swapping the colour for odd permutations. -/
  | permute (red : Bool) (c : Column n V) (rest : Multiset (Column n V))
      (σ : Equiv.Perm (Fin n)) :
      TabStep ⟨red, c ::ₘ rest⟩
        {⟨if Equiv.Perm.sign σ = 1 then red else !red, (c ∘ σ) ::ₘ rest⟩}
  /-- A tableau with a repeated entry in a column vanishes. -/
  | vanish (T : Tableau n V) (c : Column n V) (hc : c ∈ T.cols) (h : ¬ Function.Injective c) :
      TabStep T 0
  /-- An exchange rule. -/
  | exchange (red : Bool) (c₁ c₂ : Column n V) (rest : Multiset (Column n V))
      (S : Finset (Fin n)) :
      TabStep ⟨red, c₁ ::ₘ c₂ ::ₘ rest⟩ (exchangeResult red c₁ c₂ rest S)

/-- One step of the reduction of a multiset of tableaux: replace one of its tableaux by
the multiset of tableaux prescribed by an allowed step (`main.tex`, Subsection
"Main Results": *"Any tableaux in a multiset may be exchanged as follows …"*). -/
def MultisetStep [DecidableEq V] (m m' : Multiset (Tableau n V)) : Prop :=
  ∃ (T : Tableau n V) (m₀ r : Multiset (Tableau n V)),
    m = T ::ₘ m₀ ∧ TabStep T r ∧ m' = m₀ + r

/-- Reduction of a multiset of tableaux by a finite sequence of allowed steps. -/
def ReducesTo [DecidableEq V] (m m' : Multiset (Tableau n V)) : Prop :=
  Relation.ReflTransGen MultisetStep m m'

/-
Lemma `lemma:semistandard-tableaux-span` of the source article is stated and proved as
`RigidityTableaux.lemma_semistandard_tableaux_span` in `RequestProject/Straightening.lean`,
which is where the straightening algorithm is developed. It cannot be stated here because
its proof needs the machinery built in that file, which in turn needs the definitions of
this one.
-/

/-! ### Brackets: evaluating tableaux as products of maximal minors -/

variable {R : Type*} [CommRing R]

/-- The **bracket** `[i_1 … i_n]` evaluated at a matrix `M` with `n` rows and columns
indexed by `V`: the maximal minor of `M` on the columns `i_1, …, i_n` (`main.tex`,
Subsection "Geometric results": *"we may evaluate `∑ wt(P)` at `p` by replacing each
column with the corresponding maximal minor of the matrix `M`"*). -/
def bracketEval (M : Fin n → V → R) (c : Column n V) : R :=
  Matrix.det (Matrix.of fun i j : Fin n => M i (c j))

/-- The evaluation of a tableau: the sign given by its colour times the product of the
brackets of its columns. -/
def tableauEval (M : Fin n → V → R) (T : Tableau n V) : R :=
  (T.sign : R) * (T.cols.map (bracketEval M)).prod

/-- The evaluation of a multiset of tableaux, i.e. of the corresponding bracket
polynomial, at a matrix `M`. -/
def multisetEval (M : Fin n → V → R) (m : Multiset (Tableau n V)) : R :=
  (m.map (tableauEval M)).sum

/-- The generic `n × |V|` matrix, whose entries are independent indeterminates. -/
noncomputable def genericMatrix (n : ℕ) (V : Type*) :
    Fin n → V → MvPolynomial (Fin n × V) ℚ :=
  fun i v => MvPolynomial.X (i, v)

/-- A multiset of tableaux **straightens to zero** when the corresponding bracket
polynomial vanishes identically on all matrices, i.e. lies in the Plücker ideal
(`main.tex`, Subsection "From geometric to combinatorial balancing": *"A bracket
polynomial straightens to zero exactly when it belongs to the Plücker ideal"*). -/
def StraightensToZero (m : Multiset (Tableau n V)) : Prop :=
  multisetEval (genericMatrix n V) m = 0

/-- **Proposition `proposition:Sylvester-exchange` of the source article** (page 108 of
Fulton, attributed to Sylvester), in bracket form: exchanging a fixed set `S` of boxes
of one column with all choices of equally many boxes of a second column, keeping the
vertical order, does not change the product of the two brackets. -/
theorem proposition_Sylvester_exchange [DecidableEq V] (M : Fin n → V → R)
    (c₁ c₂ : Column n V) (S : Finset (Fin n)) :
    bracketEval M c₁ * bracketEval M c₂
      = ∑ T : {T : Finset (Fin n) // T.card = S.card},
          bracketEval M (exchangeCols c₁ c₂ S T.1 T.2).1
            * bracketEval M (exchangeCols c₁ c₂ S T.1 T.2).2 := by
  classical
  have hbr : ∀ c : Column n V, bracketEval M c = colDet (fun j i => M i (c j)) := fun _ => rfl
  have hterm : ∀ (T : Finset (Fin n)) (hT : T.card = S.card),
      exchTerm (fun j i => M i (c₁ j)) (fun j i => M i (c₂ j)) S T
        = bracketEval M (exchangeCols c₁ c₂ S T hT).1
          * bracketEval M (exchangeCols c₁ c₂ S T hT).2 := by
    intro T hT
    rw [exchTerm_eq _ _ S T (matchEquiv S T hT), hbr, hbr]
    congr 1
    · congr 1
      funext j i
      simp only [swapFst, exchangeCols, matchEquiv]
      split <;> rfl
    · congr 1
      funext j i
      simp only [swapSnd, exchangeCols, matchEquiv]
      split <;> rfl
  rw [hbr c₁, hbr c₂,
    colDet_mul_colDet_eq_sum_exchTerm (fun j i => M i (c₁ j)) (fun j i => M i (c₂ j)) S,
    Finset.sum_subtype (p := fun T : Finset (Fin n) => T.card = S.card)
      (Finset.powersetCard S.card Finset.univ)
      (fun T => by simp [Finset.mem_powersetCard])
      (fun T => exchTerm (fun j i => M i (c₁ j)) (fun j i => M i (c₂ j)) S T)]
  exact Finset.sum_congr rfl (fun T _ => hterm T.1 T.2)

/-! ### Red-blue balance -/

/-- The number of red copies of a given product of columns inside a multiset of tableaux. -/
def redCount [DecidableEq V] (m : Multiset (Tableau n V)) (c : Multiset (Column n V)) : ℕ := by
  classical
  exact Multiset.card (m.filter (fun T => T.red = true ∧ T.cols = c))

/-- The number of blue copies of a given product of columns inside a multiset of tableaux. -/
def blueCount [DecidableEq V] (m : Multiset (Tableau n V)) (c : Multiset (Column n V)) : ℕ := by
  classical
  exact Multiset.card (m.filter (fun T => T.red = false ∧ T.cols = c))

/-- A multiset of tableaux **contains each tableau in equal amounts red and blue**
(`main.tex`, Subsection "Main Results", definition of a balanced orientation). -/
def RedBlueBalanced [DecidableEq V] (m : Multiset (Tableau n V)) : Prop :=
  ∀ c : Multiset (Column n V), redCount m c = blueCount m c

/-
**Lemma `lemma:red-blue-equiv-straighten-to-zero` of the source article** is stated and
proved as `RigidityTableaux.lemma_red_blue_equiv_straighten_to_zero` in
`RequestProject/RedBlue.lean`, which is where the linear independence of the semistandard
tableaux is established. It cannot be stated here because its proof needs the machinery
built in that file.

The statement as it stands below (without any hypothesis on the height `n` of the
tableaux) is **false** for `n = 0`, which is why it is commented out: for `n = 0` there is
exactly one column, every bracket equals the determinant of the empty matrix, that is `1`,
and every multiset of columns is semistandard, so that the multiset consisting of one red
tableau with no column and one blue tableau with one column is reduced, semistandard, has
bracket polynomial `1 - 1 = 0`, and yet is not red-blue balanced. This counterexample is
formalized as `RigidityTableaux.RedBlue.not_redBlue_equiv_straightensToZero_of_height_zero`
in `RequestProject/RedBlue.lean`. The version proved there carries the hypothesis `0 < n`,
which is satisfied everywhere the lemma is used (the tableaux of the source article have
height `n = d + 1`).

theorem lemma_red_blue_equiv_straighten_to_zero [DecidableEq V] [LinearOrder V] [Fintype V]
    (m m' : Multiset (Tableau n V)) (hred : ReducesTo m m')
    (hss : ∀ T ∈ m', IsSemistandard T) :
    RedBlueBalanced m' ↔ StraightensToZero m := by
  sorry
-/

/-! ### Multidegrees -/

/-- The **vertex multi-degree** of a column, `deg [i_1 … i_n] = ε_{i_1} + ⋯ + ε_{i_n}`
(`main.tex`, Subsection "From geometric to combinatorial balancing"). -/
def colDegree [DecidableEq V] (c : Column n V) (v : V) : ℕ :=
  (univ.filter (fun i : Fin n => c i = v)).card

/-- The vertex multi-degree of a tableau: the sum of the multi-degrees of its columns. -/
def tableauDegree [DecidableEq V] (T : Tableau n V) (v : V) : ℕ :=
  (T.cols.map (fun c => colDegree c v)).sum

/-- A multiset of tableaux is **multi-homogeneous in the vertices** when all of its
tableaux have the same vertex multi-degree (`main.tex`, Lemma
`lemma:balancing-multihomogeneous-new`). -/
def MultiHomogeneous [DecidableEq V] (m : Multiset (Tableau n V)) : Prop :=
  ∀ T ∈ m, ∀ T' ∈ m, ∀ v : V, tableauDegree T v = tableauDegree T' v

end RigidityTableaux
