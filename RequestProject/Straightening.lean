import RequestProject.Tableaux

/-!
# The straightening algorithm: semistandard tableaux span

This file proves Lemma `lemma:semistandard-tableaux-span` of the source article
(`main.tex`, Subsection "Main Results"):

> Every multiset of tableaux may be reduced to a multiset of semistandard tableaux using
> exchange rules.

The proof is the classical straightening algorithm. Columns are first sorted (a tableau
with a repeated entry in a column vanishes); a tableau all of whose columns are strictly
increasing is semistandard exactly when its columns are pairwise comparable for the
entrywise order; and two incomparable columns are replaced, by an exchange rule, with
tableaux that are strictly larger for an explicit weight.

The weight of a column is the position of its set of entries in the order which compares
the sorted entries lexicographically from the top. The weight of a tableau is the sum of
`2 ^ (weight of a column)`, and this is what strictly increases at each exchange.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

namespace Straightening

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {n : ℕ}

/-! ### A numerical weight for finite sets of vertices -/

/-- The position of a vertex counted from the *top*: the largest vertex has rank `0`. -/
noncomputable def revRank (v : V) : ℕ :=
  Fintype.card V - 1 - ((monoEquivOfFin V rfl).symm v : ℕ)

theorem revRank_lt (v : V) : revRank v < Fintype.card V := by
  have h : ((monoEquivOfFin V rfl).symm v : ℕ) < Fintype.card V := ((monoEquivOfFin V rfl).symm v).2
  unfold revRank
  omega

theorem revRank_lt_revRank_of_lt {u v : V} (h : v < u) : revRank u < revRank v := by
  have hlt : ((monoEquivOfFin V rfl).symm v : ℕ) < ((monoEquivOfFin V rfl).symm u : ℕ) := by
    exact_mod_cast (OrderIso.lt_iff_lt (monoEquivOfFin V rfl).symm).2 h
  have h1 : ((monoEquivOfFin V rfl).symm u : ℕ) < Fintype.card V :=
    ((monoEquivOfFin V rfl).symm u).2
  unfold revRank
  omega

theorem revRank_injective : Function.Injective (revRank : V → ℕ) := by
  intro u v huv
  rcases lt_trichotomy u v with h | h | h
  · exact absurd huv (Nat.ne_of_gt (revRank_lt_revRank_of_lt h))
  · exact h
  · exact absurd huv.symm (Nat.ne_of_gt (revRank_lt_revRank_of_lt h))

/-- The numerical code of a finite set of vertices: the binary number whose bits are the
elements of the set, the *smallest* vertex contributing the most significant bit. -/
noncomputable def setCode (S : Finset V) : ℕ := ∑ v ∈ S, 2 ^ revRank v

theorem sum_two_pow_lt_of_lt {N : ℕ} {S : Finset V} (h : ∀ v ∈ S, revRank v < N) :
    setCode S < 2 ^ N := by
  have himg : S.image revRank ⊆ Finset.range N := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi
    exact Finset.mem_range.2 (h v hv)
  have hsum : setCode S = ∑ i ∈ S.image revRank, 2 ^ i :=
    (Finset.sum_image (fun x _ y _ hxy => revRank_injective hxy)).symm
  have hle : ∑ i ∈ S.image revRank, 2 ^ i ≤ ∑ i ∈ Finset.range N, 2 ^ i :=
    Finset.sum_le_sum_of_subset (f := fun i => 2 ^ i) himg
  have hgeo : ∑ i ∈ Finset.range N, 2 ^ i = 2 ^ N - 1 := by
    simpa using Nat.geomSum_eq (le_refl 2) N
  have h2 : 0 < 2 ^ N := Nat.two_pow_pos N
  omega

theorem setCode_lt (S : Finset V) : setCode S < 2 ^ Fintype.card V :=
  sum_two_pow_lt_of_lt (fun v _ => revRank_lt v)

/-- **The comparison of codes.** If the smallest vertex at which two sets differ belongs
to the second one, then the second one has the larger code. -/
theorem setCode_lt_setCode {P Q : Finset V} {v : V} (hvQ : v ∈ Q) (hvP : v ∉ P)
    (hagree : ∀ u : V, u < v → (u ∈ P ↔ u ∈ Q)) : setCode P < setCode Q := by
  classical
  set C : Finset V := P.filter (fun u => u < v) with hC
  have hCQ : Q.filter (fun u => u < v) = C := by
    ext u
    simp only [hC, mem_filter]
    exact and_congr_left (fun hu => (hagree u hu).symm)
  have hPsplit : setCode P = setCode C + ∑ u ∈ P.filter (fun u => ¬ u < v), 2 ^ revRank u := by
    rw [setCode, setCode, hC, ← Finset.sum_filter_add_sum_filter_not P (fun u => u < v)]
  have hQsplit : setCode Q = setCode C + ∑ u ∈ Q.filter (fun u => ¬ u < v), 2 ^ revRank u := by
    rw [setCode, setCode, ← hCQ, ← Finset.sum_filter_add_sum_filter_not Q (fun u => u < v)]
  have hPbound : ∑ u ∈ P.filter (fun u => ¬ u < v), 2 ^ revRank u < 2 ^ revRank v := by
    have : ∀ u ∈ P.filter (fun u => ¬ u < v), revRank u < revRank v := by
      intro u hu
      rw [mem_filter, not_lt] at hu
      have hne : u ≠ v := fun h => hvP (h ▸ hu.1)
      exact revRank_lt_revRank_of_lt (lt_of_le_of_ne hu.2 (Ne.symm hne))
    have := sum_two_pow_lt_of_lt (N := revRank v) (S := P.filter (fun u => ¬ u < v)) this
    simpa [setCode] using this
  have hQbound : 2 ^ revRank v ≤ ∑ u ∈ Q.filter (fun u => ¬ u < v), 2 ^ revRank u := by
    refine Finset.single_le_sum (f := fun u => 2 ^ revRank u) (fun _ _ => Nat.zero_le _) ?_
    rw [mem_filter]
    exact ⟨hvQ, by simp⟩
  omega

/-- The weight of a finite set of vertices: sets whose sorted enumeration is larger in the
lexicographic order from the top get the larger weight. -/
noncomputable def setWeight (S : Finset V) : ℕ := 2 ^ Fintype.card V - setCode S

theorem setWeight_lt_setWeight {P Q : Finset V} {v : V} (hvQ : v ∈ Q) (hvP : v ∉ P)
    (hagree : ∀ u : V, u < v → (u ∈ P ↔ u ∈ Q)) : setWeight Q < setWeight P := by
  have h1 := setCode_lt_setCode hvQ hvP hagree
  have h2 := setCode_lt Q
  unfold setWeight
  omega

theorem setWeight_lt_of_exists_small {S S' : Finset V} {y : V}
    (hy : y ∈ S' \ S) (hlt : ∀ w ∈ S \ S', y < w) : setWeight S' < setWeight S := by
  classical
  set D : Finset V := (S \ S') ∪ (S' \ S) with hD
  have hyD : y ∈ D := Finset.mem_union_right _ hy
  have hDne : D.Nonempty := ⟨y, hyD⟩
  have hvD : D.min' hDne ∈ D := Finset.min'_mem _ _
  have hvy : D.min' hDne ≤ y := Finset.min'_le _ _ hyD
  have hvS' : D.min' hDne ∈ S' \ S := by
    rcases Finset.mem_union.1 hvD with h | h
    · exact absurd (lt_of_lt_of_le (hlt _ h) hvy) (lt_irrefl _)
    · exact h
  have hagree : ∀ u : V, u < D.min' hDne → (u ∈ S ↔ u ∈ S') := by
    intro u hu
    by_contra hcon
    have huD : u ∈ D := by
      rw [hD, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
      by_cases h1 : u ∈ S
      · exact Or.inl ⟨h1, fun h2 => hcon ⟨fun _ => h2, fun _ => h1⟩⟩
      · have h2 : u ∈ S' := by
          by_contra h3
          exact hcon ⟨fun h => absurd h h1, fun h => absurd h h3⟩
        exact Or.inr ⟨h2, h1⟩
    exact absurd (Finset.min'_le _ _ huD) (not_le.2 hu)
  exact setWeight_lt_setWeight (Finset.mem_sdiff.1 hvS').1 (Finset.mem_sdiff.1 hvS').2 hagree

theorem exists_min_symmDiff_mem {S S' : Finset V} (hne : S ≠ S')
    (hcount : ∀ t : V, #(S'.filter (fun u => u ≤ t)) ≤ #(S.filter (fun u => u ≤ t))) :
    ∃ y ∈ S \ S', ∀ w ∈ S' \ S, y < w := by
  classical
  set D : Finset V := (S \ S') ∪ (S' \ S) with hD
  have hDne : D.Nonempty := by
    rcases Finset.eq_empty_or_nonempty D with h | h
    · refine absurd ?_ hne
      ext u
      constructor
      · intro hu
        by_contra hu'
        have hmem : u ∈ D := Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hu, hu'⟩)
        rw [h] at hmem
        simp at hmem
      · intro hu
        by_contra hu'
        have hmem : u ∈ D := Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hu, hu'⟩)
        rw [h] at hmem
        simp at hmem
    · exact h
  have hyD : D.min' hDne ∈ D := Finset.min'_mem _ _
  have hagree : ∀ u : V, u < D.min' hDne → (u ∈ S ↔ u ∈ S') := by
    intro u hu
    by_contra hcon
    have huD : u ∈ D := by
      rw [hD, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
      by_cases h1 : u ∈ S
      · exact Or.inl ⟨h1, fun h2 => hcon ⟨fun _ => h2, fun _ => h1⟩⟩
      · have h2 : u ∈ S' := by
          by_contra h3
          exact hcon ⟨fun h => absurd h h1, fun h => absurd h h3⟩
        exact Or.inr ⟨h2, h1⟩
    exact absurd (Finset.min'_le _ _ huD) (not_le.2 hu)
  have hyS : D.min' hDne ∈ S \ S' := by
    rcases Finset.mem_union.1 hyD with h | h
    · exact h
    · exfalso
      obtain ⟨hyS', hyS⟩ := Finset.mem_sdiff.1 h
      have hins : S'.filter (fun u => u ≤ D.min' hDne)
          = insert (D.min' hDne) (S.filter (fun u => u ≤ D.min' hDne)) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hu, hle⟩
          rcases eq_or_lt_of_le hle with h1 | h1
          · exact Or.inl h1
          · exact Or.inr ⟨(hagree u h1).2 hu, hle⟩
        · rintro (rfl | ⟨hu, hle⟩)
          · exact ⟨hyS', le_refl _⟩
          · have hlt : u < D.min' hDne := lt_of_le_of_ne hle (fun hh => hyS (hh ▸ hu))
            exact ⟨(hagree u hlt).1 hu, hle⟩
      have hynot : D.min' hDne ∉ S.filter (fun u => u ≤ D.min' hDne) := fun hh =>
        hyS (Finset.mem_filter.1 hh).1
      have hc := hcount (D.min' hDne)
      rw [hins, Finset.card_insert_of_notMem hynot] at hc
      omega
  refine ⟨D.min' hDne, hyS, fun w hw => ?_⟩
  have hle : D.min' hDne ≤ w := Finset.min'_le _ _ (Finset.mem_union_right _ hw)
  rcases eq_or_lt_of_le hle with h | h
  · exact absurd (h ▸ (Finset.mem_sdiff.1 hw).1) (Finset.mem_sdiff.1 hyS).2
  · exact h

/-! ### The weight of a column -/

/-- The set of entries of a column. -/
def colSet (c : Column n V) : Finset V := Finset.image c univ

omit [Fintype V] [LinearOrder V] in
theorem mem_colSet {c : Column n V} {v : V} : v ∈ colSet c ↔ ∃ i, c i = v := by
  simp [colSet]

/-- The weight of a column: strictly increasing columns which are larger in the
lexicographic order from the top have the larger weight. -/
noncomputable def colWeight (c : Column n V) : ℕ := setWeight (colSet c)

theorem colSet_comp_perm (c : Column n V) (σ : Equiv.Perm (Fin n)) :
    colSet (c ∘ σ) = colSet c := by
  ext v
  simp only [mem_colSet]
  exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩, fun ⟨i, hi⟩ => ⟨σ.symm i, by simpa using hi⟩⟩

theorem colWeight_comp_perm (c : Column n V) (σ : Equiv.Perm (Fin n)) :
    colWeight (c ∘ σ) = colWeight c := by
  rw [colWeight, colWeight, colSet_comp_perm]

theorem card_filter_colSet {c : Column n V} (hc : Function.Injective c) (t : V) :
    #((colSet c).filter (fun u => u ≤ t)) = #(univ.filter (fun i => c i ≤ t)) := by
  classical
  have himg : (colSet c).filter (fun u => u ≤ t) = (univ.filter (fun i => c i ≤ t)).image c := by
    ext u
    simp only [Finset.mem_filter, mem_colSet, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, rfl⟩, hle⟩
      exact ⟨i, hle, rfl⟩
    · rintro ⟨i, hle, rfl⟩
      exact ⟨⟨i, rfl⟩, hle⟩
  rw [himg, Finset.card_image_of_injective _ hc]

/-- **A pointwise smaller strictly increasing column has a smaller weight.** -/
theorem colWeight_lt_colWeight {c c' : Column n V} (hc : StrictMono c) (hc' : StrictMono c')
    (hle : ∀ i, c i ≤ c' i) (hne : c ≠ c') : colWeight c < colWeight c' := by
  classical
  have hcount : ∀ t : V, #((colSet c').filter (fun u => u ≤ t))
      ≤ #((colSet c).filter (fun u => u ≤ t)) := by
    intro t
    rw [card_filter_colSet hc.injective t, card_filter_colSet hc'.injective t]
    refine Finset.card_le_card ?_
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_trans (hle i) hi
  obtain ⟨i, hi⟩ : ∃ i, c i < c' i := by
    by_contra hcc
    push_neg at hcc
    exact hne (funext (fun i => le_antisymm (hle i) (hcc i)))
  have hsub : univ.filter (fun j => c' j ≤ c i) ⊆ univ.filter (fun j => c j ≤ c i) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact le_trans (hle j) hj
  have hstrict : #((colSet c').filter (fun u => u ≤ c i))
      < #((colSet c).filter (fun u => u ≤ c i)) := by
    rw [card_filter_colSet hc.injective, card_filter_colSet hc'.injective]
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨i, ?_, ?_⟩)
    · simp
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact not_le.2 hi
  have hSne : colSet c ≠ colSet c' := by
    intro h
    rw [h] at hstrict
    omega
  obtain ⟨y, hy, hylt⟩ := exists_min_symmDiff_mem hSne hcount
  exact setWeight_lt_of_exists_small hy hylt

/-! ### Elementary properties of the reduction of multisets of tableaux -/

theorem reducesTo_of_tabStep {T : Tableau n V} {r : Multiset (Tableau n V)} (h : TabStep T r) :
    ReducesTo {T} r :=
  Relation.ReflTransGen.single ⟨T, 0, r, rfl, h, (zero_add r).symm⟩

theorem multisetStep_add {m m' k : Multiset (Tableau n V)} (h : MultisetStep m m') :
    MultisetStep (m + k) (m' + k) := by
  obtain ⟨T, m₀, r, rfl, hstep, rfl⟩ := h
  refine ⟨T, m₀ + k, r, by simp [Multiset.cons_add], hstep, ?_⟩
  rw [add_assoc, add_comm r k, ← add_assoc]

theorem reducesTo_add {m m' : Multiset (Tableau n V)} (k : Multiset (Tableau n V))
    (h : ReducesTo m m') : ReducesTo (m + k) (m' + k) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (multisetStep_add hstep)

/-- Reducing a multiset of tableaux one tableau at a time. -/
theorem exists_reducesTo_of_forall {P : Tableau n V → Prop} (m : Multiset (Tableau n V))
    (H : ∀ T ∈ m, ∃ m', ReducesTo {T} m' ∧ ∀ U ∈ m', P U) :
    ∃ m'', ReducesTo m m'' ∧ ∀ U ∈ m'', P U := by
  classical
  induction m using Multiset.induction_on with
  | empty => exact ⟨0, Relation.ReflTransGen.refl, by simp⟩
  | cons T m₀ ih =>
      obtain ⟨r, hr, hrP⟩ := H T (Multiset.mem_cons_self T m₀)
      obtain ⟨m'', hm'', hm''P⟩ := ih (fun U hU => H U (Multiset.mem_cons_of_mem hU))
      refine ⟨r + m'', ?_, ?_⟩
      · have h1 : ReducesTo ({T} + m₀) (r + m₀) := reducesTo_add m₀ hr
        have h2 : ReducesTo (m₀ + r) (m'' + r) := reducesTo_add r hm''
        have hstart : (T ::ₘ m₀) = {T} + m₀ := by simp
        rw [hstart]
        refine h1.trans ?_
        rw [add_comm r m₀, add_comm r m'']
        exact h2
      · intro U hU
        rcases Multiset.mem_add.1 hU with h | h
        · exact hrP U h
        · exact hm''P U h

/-! ### Sorting the columns of a tableau -/

theorem exists_strictMono_comp {c : Column n V} (hc : Function.Injective c) :
    ∃ σ : Equiv.Perm (Fin n), StrictMono (c ∘ σ) := by
  refine ⟨Tuple.sort c, ?_⟩
  exact (Tuple.monotone_sort c).strictMono_of_injective (hc.comp (Equiv.injective _))

/-- Sorting the columns of a tableau, one at a time. -/
theorem exists_sorted_aux (red : Bool) (A B : Multiset (Column n V))
    (hinj : ∀ c ∈ B, Function.Injective c) :
    ∃ (red' : Bool) (B' : Multiset (Column n V)),
      (∀ c ∈ B', StrictMono c) ∧ B'.map colWeight = B.map colWeight ∧
      ReducesTo {(⟨red, A + B⟩ : Tableau n V)} {(⟨red', A + B'⟩ : Tableau n V)} := by
  classical
  induction B using Multiset.induction_on generalizing A red with
  | empty => exact ⟨red, 0, by simp, rfl, Relation.ReflTransGen.refl⟩
  | cons c B₀ ih =>
      obtain ⟨σ, hσ⟩ := exists_strictMono_comp (hinj c (Multiset.mem_cons_self c B₀))
      set red₁ : Bool := if Equiv.Perm.sign σ = 1 then red else !red with hred₁
      have hstep : TabStep (⟨red, c ::ₘ (A + B₀)⟩ : Tableau n V)
          {(⟨red₁, (c ∘ σ) ::ₘ (A + B₀)⟩ : Tableau n V)} := TabStep.permute red c (A + B₀) σ
      have h1 : ReducesTo {(⟨red, A + (c ::ₘ B₀)⟩ : Tableau n V)}
          {(⟨red₁, ((c ∘ σ) ::ₘ A) + B₀⟩ : Tableau n V)} := by
        have e1 : A + (c ::ₘ B₀) = c ::ₘ (A + B₀) := by
          rw [Multiset.add_cons]
        have e2 : ((c ∘ σ) ::ₘ A) + B₀ = (c ∘ σ) ::ₘ (A + B₀) := by
          rw [Multiset.cons_add]
        rw [e1, e2]
        exact reducesTo_of_tabStep hstep
      obtain ⟨red', B₀', hmono', hmap', hred'⟩ := ih red₁ ((c ∘ σ) ::ₘ A)
        (fun x hx => hinj x (Multiset.mem_cons_of_mem hx))
      refine ⟨red', (c ∘ σ) ::ₘ B₀', ?_, ?_, ?_⟩
      · intro x hx
        rcases Multiset.mem_cons.1 hx with rfl | hx
        · exact hσ
        · exact hmono' x hx
      · rw [Multiset.map_cons, Multiset.map_cons, hmap', colWeight_comp_perm]
      · refine h1.trans ?_
        have e3 : A + ((c ∘ σ) ::ₘ B₀') = ((c ∘ σ) ::ₘ A) + B₀' := by
          rw [Multiset.add_cons, Multiset.cons_add]
        rw [e3]
        exact hred'

/-! ### Semistandard tableaux are those with pairwise comparable columns -/

theorem isSemistandard_of_pairwise (red : Bool) (cols : Multiset (Column n V))
    (hmono : ∀ c ∈ cols, StrictMono c)
    (hcomp : ∀ c ∈ cols, ∀ c' ∈ cols, (∀ i, c i ≤ c' i) ∨ (∀ i, c' i ≤ c i)) :
    IsSemistandard (⟨red, cols⟩ : Tableau n V) := by
  classical
  set le : Column n V → Column n V → Bool :=
    fun c c' => decide (colWeight c ≤ colWeight c') with hle
  set L := cols.toList.mergeSort le with hLdef
  have hperm : L.Perm cols.toList := List.mergeSort_perm _ _
  have hLcols : (L : Multiset (Column n V)) = cols := by
    rw [Multiset.coe_eq_coe.2 hperm, Multiset.coe_toList]
  have hmemL : ∀ c ∈ L, c ∈ cols := by
    intro c hc
    rw [← hLcols]
    exact Multiset.mem_coe.2 hc
  have hpair : L.Pairwise (fun a b => le a b = true) := by
    refine List.pairwise_mergeSort ?_ ?_ _
    · intro a b c hab hbc
      simp only [hle, decide_eq_true_eq] at hab hbc ⊢
      omega
    · intro a b
      simp only [hle, Bool.or_eq_true, decide_eq_true_eq]
      omega
  refine ⟨L, hLcols, fun c hc => hmono c (hmemL c hc), ?_⟩
  refine List.Pairwise.isChain (hpair.imp_of_mem ?_)
  intro a b ha hb hab
  have hw : colWeight a ≤ colWeight b := by simpa [hle] using hab
  rcases hcomp a (hmemL a ha) b (hmemL b hb) with h | h
  · exact h
  · by_cases hab2 : a = b
    · subst hab2
      exact fun i => le_refl _
    · exact absurd (colWeight_lt_colWeight (hmono b (hmemL b hb)) (hmono a (hmemL a ha)) h
        (Ne.symm hab2)) (not_lt.2 hw)

/-! ### The weight of a tableau -/

/-- The weight of a tableau: the sum of `2 ^ (weight of a column)` over its columns. It is
what strictly increases at each exchange used by the straightening algorithm. -/
noncomputable def tabWeight (T : Tableau n V) : ℕ := (T.cols.map (fun c => 2 ^ colWeight c)).sum

theorem colWeight_le (c : Column n V) : colWeight c ≤ 2 ^ Fintype.card V :=
  Nat.sub_le _ _

theorem tabWeight_le (T : Tableau n V) :
    tabWeight T ≤ Multiset.card T.cols * 2 ^ (2 ^ Fintype.card V) := by
  classical
  have h : ∀ x ∈ T.cols.map (fun c => 2 ^ colWeight c), x ≤ 2 ^ (2 ^ Fintype.card V) := by
    intro x hx
    obtain ⟨c, _, rfl⟩ := Multiset.mem_map.1 hx
    exact Nat.pow_le_pow_right (by norm_num) (colWeight_le c)
  have := Multiset.sum_le_card_nsmul _ _ h
  simpa [tabWeight, smul_eq_mul] using this

/-! ### The exchange step of the straightening algorithm -/

omit [Fintype V] [LinearOrder V] in
theorem colSet_exchangeCols_snd (c₁ c₂ : Column n V) (S T : Finset (Fin n)) (h : #T = #S) :
    colSet (exchangeCols c₁ c₂ S T h).2 = S.image c₁ ∪ (univ \ T).image c₂ := by
  classical
  ext v
  simp only [mem_colSet, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hj : j ∈ T
    · left
      refine ⟨((S.orderIsoOfFin rfl) ((T.orderIsoOfFin h).symm ⟨j, hj⟩) : Fin n),
        ((S.orderIsoOfFin rfl) ((T.orderIsoOfFin h).symm ⟨j, hj⟩)).2, ?_⟩
      simp only [exchangeCols, dif_pos hj]
    · right
      exact ⟨j, hj, by simp only [exchangeCols, dif_neg hj]⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨j, hj, rfl⟩)
    · refine ⟨(((T.orderIsoOfFin h) ((S.orderIsoOfFin rfl).symm ⟨s, hs⟩) : {x // x ∈ T}) : Fin n),
        ?_⟩
      have hjT : (((T.orderIsoOfFin h) ((S.orderIsoOfFin rfl).symm ⟨s, hs⟩) : {x // x ∈ T})
          : Fin n) ∈ T := ((T.orderIsoOfFin h) ((S.orderIsoOfFin rfl).symm ⟨s, hs⟩)).2
      simp only [exchangeCols, dif_pos hjT]
      congr 1
      have hsub : (⟨(((T.orderIsoOfFin h) ((S.orderIsoOfFin rfl).symm ⟨s, hs⟩) : {x // x ∈ T})
            : Fin n), hjT⟩ : {x // x ∈ T})
          = (T.orderIsoOfFin h) ((S.orderIsoOfFin rfl).symm ⟨s, hs⟩) := Subtype.ext rfl
      rw [hsub]
      simp
    · exact ⟨j, by simp only [exchangeCols, dif_neg hj]⟩

omit [Fintype V] [LinearOrder V] in
theorem mem_exchangeResult {red : Bool} {c₁ c₂ : Column n V} {rest : Multiset (Column n V)}
    {S : Finset (Fin n)} {U : Tableau n V} (hU : U ∈ exchangeResult red c₁ c₂ rest S) :
    ∃ (T : Finset (Fin n)) (hT : #T = #S),
      U = ⟨red, (exchangeCols c₁ c₂ S T hT).1 ::ₘ (exchangeCols c₁ c₂ S T hT).2 ::ₘ rest⟩ := by
  classical
  rw [exchangeResult] at hU
  obtain ⟨T, -, hT⟩ := Multiset.mem_map.1 (Multiset.mem_of_mem_filter hU)
  exact ⟨T.1, T.2, hT.symm⟩

/-- **The column of a strictly increasing column pair which is lexicographically smaller
from the top has the smaller weight.** -/
theorem colWeight_lt_of_lt_at_first_diff {X Y : Column n V} (hX : StrictMono X)
    (hY : StrictMono Y) {i0 : Fin n} (hlt : X i0 < Y i0) (hagree : ∀ j, j < i0 → X j = Y j) :
    colWeight X < colWeight Y := by
  classical
  refine setWeight_lt_of_exists_small (y := X i0) ?_ ?_
  · rw [Finset.mem_sdiff]
    refine ⟨mem_colSet.2 ⟨i0, rfl⟩, ?_⟩
    intro hmem
    obtain ⟨j, hj⟩ := mem_colSet.1 hmem
    rcases lt_trichotomy j i0 with h | h | h
    · rw [← hagree j h] at hj
      exact absurd hj (ne_of_lt (hX h))
    · subst h
      exact absurd hj.symm (ne_of_lt hlt)
    · exact absurd hj (ne_of_gt (lt_trans hlt (hY h)))
  · intro w hw
    rw [Finset.mem_sdiff] at hw
    obtain ⟨j, rfl⟩ := mem_colSet.1 hw.1
    rcases lt_or_ge j i0 with h | h
    · exact absurd (mem_colSet.2 ⟨j, hagree j h⟩) hw.2
    · exact lt_of_lt_of_le hlt (hY.monotone h)

/-- **The exchange step strictly increases the weight of the tableau.** Given two
incomparable strictly increasing columns `X` and `Y` with `X` the smaller one, and a row
`k` at which `Y k < X k`, exchanging the boxes of `X` in the rows `≥ k` with all choices
of equally many boxes of `Y` produces only tableaux of strictly larger weight. -/
theorem tabWeight_lt_of_mem_exchangeResult (red : Bool) {X Y : Column n V}
    (rest : Multiset (Column n V)) (hX : StrictMono X) (hY : StrictMono Y)
    (hXY : colWeight X < colWeight Y) {k : Fin n} (hk : Y k < X k)
    {U : Tableau n V} (hU : U ∈ exchangeResult red X Y rest (univ.filter (fun j => k ≤ j))) :
    tabWeight (⟨red, X ::ₘ Y ::ₘ rest⟩ : Tableau n V) < tabWeight U := by
  classical
  set S : Finset (Fin n) := univ.filter (fun j => k ≤ j) with hS
  have hkS : k ∈ S := by simp [hS]
  obtain ⟨T, hT, rfl⟩ := mem_exchangeResult hU
  obtain ⟨t, htT, htk⟩ : ∃ t ∈ T, t ≤ k := by
    by_contra hcon
    push_neg at hcon
    have hsub : T ⊆ S.erase k := by
      intro t ht
      rw [Finset.mem_erase]
      exact ⟨ne_of_gt (hcon t ht), by simp [hS]; exact le_of_lt (hcon t ht)⟩
    have h1 : #T ≤ #(S.erase k) := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hkS, hT] at h1
    have h2 : 0 < #S := Finset.card_pos.2 ⟨k, hkS⟩
    omega
  have hsetB : colSet (exchangeCols X Y S T hT).2 = S.image X ∪ (univ \ T).image Y :=
    colSet_exchangeCols_snd X Y S T hT
  have hbig : ∀ j ∈ S, Y t < X j := by
    intro j hj
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact lt_of_le_of_lt (hY.monotone htk) (lt_of_lt_of_le hk (hX.monotone hj))
  have hB : colWeight Y < colWeight (exchangeCols X Y S T hT).2 := by
    refine setWeight_lt_of_exists_small (y := Y t) ?_ ?_
    · rw [Finset.mem_sdiff, hsetB]
      refine ⟨mem_colSet.2 ⟨t, rfl⟩, ?_⟩
      intro hmem
      rcases Finset.mem_union.1 hmem with hmem | hmem
      · obtain ⟨j, hj, hjv⟩ := Finset.mem_image.1 hmem
        exact absurd hjv.symm (ne_of_lt (hbig j hj))
      · obtain ⟨j, hj, hjv⟩ := Finset.mem_image.1 hmem
        rw [Finset.mem_sdiff] at hj
        exact hj.2 (hY.injective hjv.symm ▸ htT)
    · intro w hw
      rw [Finset.mem_sdiff, hsetB] at hw
      rcases Finset.mem_union.1 hw.1 with hmem | hmem
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hmem
        exact hbig j hj
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hmem
        exact absurd (mem_colSet.2 ⟨j, rfl⟩) hw.2
  have h1 : (2 : ℕ) ^ colWeight X ≤ 2 ^ colWeight Y :=
    Nat.pow_le_pow_right (by norm_num) (le_of_lt hXY)
  have h2 : (2 : ℕ) ^ colWeight Y + 2 ^ colWeight Y
      ≤ 2 ^ colWeight (exchangeCols X Y S T hT).2 := by
    have hpow : (2 : ℕ) ^ (colWeight Y + 1) ≤ 2 ^ colWeight (exchangeCols X Y S T hT).2 :=
      Nat.pow_le_pow_right (by norm_num) hB
    rw [pow_succ, mul_two] at hpow
    exact hpow
  have h3 : 0 < (2 : ℕ) ^ colWeight (exchangeCols X Y S T hT).1 := Nat.two_pow_pos _
  simp only [tabWeight, Multiset.map_cons, Multiset.sum_cons]
  omega

/-! ### Ordering two incomparable columns -/

theorem exists_ordered_incomparable {c c' : Column n V} (hc : StrictMono c) (hc' : StrictMono c')
    (h1 : ∃ i, c' i < c i) (h2 : ∃ i, c i < c' i) :
    ∃ X Y : Column n V, ((X = c ∧ Y = c') ∨ (X = c' ∧ Y = c)) ∧
      colWeight X < colWeight Y ∧ ∃ k, Y k < X k := by
  classical
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  set D : Finset (Fin n) := univ.filter (fun i => c i ≠ c' i) with hD
  have hk1D : k1 ∈ D := by
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ne_of_gt hk1
  have hDne : D.Nonempty := ⟨k1, hk1D⟩
  have hi0 : c (D.min' hDne) ≠ c' (D.min' hDne) := by
    have := Finset.min'_mem D hDne
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  have hagree : ∀ j, j < D.min' hDne → c j = c' j := by
    intro j hj
    by_contra hcon
    exact absurd (Finset.min'_le D j (by
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hcon)) (not_le.2 hj)
  rcases lt_or_gt_of_ne hi0 with h | h
  · exact ⟨c, c', Or.inl ⟨rfl, rfl⟩, colWeight_lt_of_lt_at_first_diff hc hc' h hagree,
      ⟨k1, hk1⟩⟩
  · exact ⟨c', c, Or.inr ⟨rfl, rfl⟩,
      colWeight_lt_of_lt_at_first_diff hc' hc h (fun j hj => (hagree j hj).symm), ⟨k2, hk2⟩⟩

/-! ### The straightening algorithm -/

theorem tabWeight_mk (red : Bool) (cols : Multiset (Column n V)) :
    tabWeight (⟨red, cols⟩ : Tableau n V) = ((cols.map colWeight).map (fun w => 2 ^ w)).sum := by
  rw [tabWeight, Multiset.map_map]
  rfl

/-- **The straightening algorithm.** Every tableau reduces to a multiset of semistandard
tableaux. The induction is on the difference between an a priori bound and the weight of
the tableau, which the exchange step strictly increases. -/
theorem exists_reducesTo_semistandard_aux : ∀ (b : ℕ) (T : Tableau n V),
    Multiset.card T.cols * 2 ^ (2 ^ Fintype.card V) - tabWeight T ≤ b →
    ∃ m', ReducesTo {T} m' ∧ ∀ U ∈ m', IsSemistandard U := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro T hb
    classical
    by_cases hinj : ∀ c ∈ T.cols, Function.Injective c
    · obtain ⟨red', cols', hmono', hmap', hred'⟩ :=
        exists_sorted_aux T.red 0 T.cols hinj
      rw [zero_add, zero_add] at hred'
      have hTeq : (⟨T.red, T.cols⟩ : Tableau n V) = T := rfl
      rw [hTeq] at hred'
      have hcard : Multiset.card cols' = Multiset.card T.cols := by
        have := congrArg Multiset.card hmap'
        simpa using this
      have htw : tabWeight (⟨red', cols'⟩ : Tableau n V) = tabWeight T := by
        rw [tabWeight_mk, hmap']
        rw [show T = (⟨T.red, T.cols⟩ : Tableau n V) from rfl, tabWeight_mk]
      by_cases hcomp : ∀ c ∈ cols', ∀ c' ∈ cols', (∀ i, c i ≤ c' i) ∨ (∀ i, c' i ≤ c i)
      · exact ⟨{(⟨red', cols'⟩ : Tableau n V)}, hred', by
          intro U hU
          rw [Multiset.mem_singleton] at hU
          subst hU
          exact isSemistandard_of_pairwise red' cols' hmono' hcomp⟩
      · push_neg at hcomp
        obtain ⟨a, ha, a', ha', hna, hna'⟩ := hcomp
        obtain ⟨X, Y, hXY, hwXY, k, hk⟩ :=
          exists_ordered_incomparable (hmono' a ha) (hmono' a' ha') hna hna'
        have hXmem : X ∈ cols' := by rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
        have hYmem : Y ∈ cols' := by rcases hXY with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
        have hXneY : X ≠ Y := by
          intro hcon
          rw [hcon] at hwXY
          exact absurd hwXY (lt_irrefl _)
        have hYmem2 : Y ∈ cols'.erase X := (Multiset.mem_erase_of_ne (Ne.symm hXneY)).2 hYmem
        set rest : Multiset (Column n V) := (cols'.erase X).erase Y with hrest
        have hcols' : cols' = X ::ₘ Y ::ₘ rest := by
          rw [hrest, Multiset.cons_erase hYmem2, Multiset.cons_erase hXmem]
        set S : Finset (Fin n) := univ.filter (fun j => k ≤ j) with hS
        have hstep : TabStep (⟨red', X ::ₘ Y ::ₘ rest⟩ : Tableau n V)
            (exchangeResult red' X Y rest S) := TabStep.exchange red' X Y rest S
        have hred2 : ReducesTo {(⟨red', cols'⟩ : Tableau n V)} (exchangeResult red' X Y rest S) := by
          rw [hcols']
          exact reducesTo_of_tabStep hstep
        have hkey : ∀ U ∈ exchangeResult red' X Y rest S,
            ∃ m'', ReducesTo {U} m'' ∧ ∀ W ∈ m'', IsSemistandard W := by
          intro U hU
          have hgt : tabWeight (⟨red', X ::ₘ Y ::ₘ rest⟩ : Tableau n V) < tabWeight U :=
            tabWeight_lt_of_mem_exchangeResult red' rest (hmono' X hXmem) (hmono' Y hYmem)
              hwXY hk hU
          obtain ⟨T2, hT2, rfl⟩ := mem_exchangeResult hU
          have hcardU : Multiset.card
              ((exchangeCols X Y S T2 hT2).1 ::ₘ (exchangeCols X Y S T2 hT2).2 ::ₘ rest)
              = Multiset.card cols' := by
            rw [hcols']
            simp
          have hbnd := tabWeight_le
            (⟨red', (exchangeCols X Y S T2 hT2).1 ::ₘ (exchangeCols X Y S T2 hT2).2 ::ₘ rest⟩ :
              Tableau n V)
          have hb1 : Multiset.card cols' * 2 ^ (2 ^ Fintype.card V)
              - tabWeight (⟨red', cols'⟩ : Tableau n V) ≤ b := by
            rw [htw, hcard]
            exact hb
          have hlt : Multiset.card cols' * 2 ^ (2 ^ Fintype.card V)
              - tabWeight (⟨red', (exchangeCols X Y S T2 hT2).1 ::ₘ
                (exchangeCols X Y S T2 hT2).2 ::ₘ rest⟩ : Tableau n V) < b := by
            rw [hcardU] at hbnd
            have hw1 : tabWeight (⟨red', cols'⟩ : Tableau n V)
                = tabWeight (⟨red', X ::ₘ Y ::ₘ rest⟩ : Tableau n V) := by rw [hcols']
            omega
          refine ih _ hlt _ ?_
          rw [hcardU]
        obtain ⟨m'', hm'', hm''ss⟩ :=
          exists_reducesTo_of_forall (P := fun U => IsSemistandard U) _ hkey
        exact ⟨m'', (hred'.trans hred2).trans hm'', hm''ss⟩
    · push_neg at hinj
      obtain ⟨c, hc, hcinj⟩ := hinj
      exact ⟨0, reducesTo_of_tabStep (TabStep.vanish T c hc hcinj), by simp⟩

/-- **Lemma `lemma:semistandard-tableaux-span` of the source article** (`main.tex`,
Subsection "Main Results"): every multiset of tableaux may be reduced to a multiset of
semistandard tableaux using the exchange rules. -/
theorem exists_reducesTo_semistandard (m : Multiset (Tableau n V)) :
    ∃ m' : Multiset (Tableau n V), ReducesTo m m' ∧ ∀ T ∈ m', IsSemistandard T :=
  exists_reducesTo_of_forall (P := fun U => IsSemistandard U) m
    (fun T _ => exists_reducesTo_semistandard_aux _ T (le_refl _))

end Straightening

/-- **Lemma `lemma:semistandard-tableaux-span` of the source article** (`main.tex`,
Subsection "Main Results"): *"every multiset of tableaux may be reduced to a multiset of
semistandard tableaux using exchange rules"*. Every multiset of tableaux on a finite
ordered set `V` with fixed height `n` may be reduced to a multiset of semistandard
tableaux using the exchange rules.

The hypothesis `0 < n` of the source article is kept, although the straightening
algorithm formalized here does not need it. -/
theorem lemma_semistandard_tableaux_span {V : Type*} [DecidableEq V] [LinearOrder V]
    [Fintype V] {n : ℕ} (hn : 0 < n) (m : Multiset (Tableau n V)) :
    ∃ m' : Multiset (Tableau n V), ReducesTo m m' ∧ ∀ T ∈ m', IsSemistandard T :=
  Straightening.exists_reducesTo_semistandard m

end RigidityTableaux
