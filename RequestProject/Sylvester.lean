import Mathlib

/-!
# Sylvester's exchange identity for determinants

This file proves the determinant identity behind Proposition
`proposition:Sylvester-exchange` of the source article (`main.tex`, Subsection "From
geometric to combinatorial balancing", quoted from page 108 of Fulton and attributed to
Sylvester):

> For any `p × p` matrices `M` and `N` and `1 ≤ k ≤ p`,
> `det M ⬝ det N = ∑ det M' ⬝ det N'`, where the sum is over all pairs `(M',N')`
> obtained from `M` and `N` by interchanging a fixed set of `k` columns of `M` with any
> `k` columns of `N`, preserving the order of the columns.

The development is stated for families of columns:

* `colDet u` is the determinant of the matrix whose `j`-th column is `u j`;
* `swapFst c₁ c₂ S T e` and `swapSnd c₁ c₂ S T e` interchange the entries of `c₁` in the
  positions `S` with the entries of `c₂` in the positions `T`, along a bijection
  `e : S ≃ T`;
* `matchEquiv S T h` is the order-preserving bijection `S ≃ T`, which is the one used in
  the exchange rules for tableaux;
* `exchTerm u v S T` is the product of the two determinants after such an exchange (it
  does not depend on the chosen bijection, `exchTerm_eq`);
* `colDet_mul_colDet_eq_sum_exchTerm` is Sylvester's identity.

The proof is by induction on `#S`, using Cramer's rule for the case `#S = 1`
(`colDet_mul_colDet_eq_sum_update`). The induction divides by `#S`, so it is first run
over a `ℚ`-algebra and then transported to an arbitrary commutative ring by specializing
the identity for the generic matrices with integer coefficients.
-/

open scoped BigOperators
open Finset Matrix

namespace RigidityTableaux

variable {n : ℕ} {R : Type*} [CommRing R]

/-! ### Determinants of families of columns -/

/-- The determinant of the matrix whose `j`-th column is the vector `u j`. -/
def colDet (u : Fin n → Fin n → R) : R := Matrix.det (Matrix.of fun i j => u j i)

theorem colDet_eq_det (M : Matrix (Fin n) (Fin n) R) : colDet (fun j i => M i j) = M.det := rfl

/-- Permuting the columns of a family multiplies its determinant by the sign of the
permutation. -/
theorem colDet_comp_perm (u : Fin n → Fin n → R) (π : Equiv.Perm (Fin n)) :
    colDet (fun j => u (π j)) = (Equiv.Perm.sign π : ℤ) * colDet u := by
  have h : (Matrix.of fun i j => u (π j) i)
      = (Matrix.of fun i j => u j i).submatrix id π := rfl
  rw [colDet, h, Matrix.det_permute', colDet]

/-- Composing a family of columns with a map of the entries. -/
theorem colDet_map {R' : Type*} [CommRing R'] (φ : R →+* R') (u : Fin n → Fin n → R) :
    φ (colDet u) = colDet (fun j i => φ (u j i)) := by
  rw [colDet, RingHom.map_det, colDet]
  rfl

/-! ### Exchanging entries between two families -/

section Swap

variable {α : Type*}

/-- The first family after interchanging its entries in the positions `S` with the
entries of the second family in the positions `T`, along the bijection `e`. -/
def swapFst (c₁ c₂ : Fin n → α) (S T : Finset (Fin n))
    (e : {i // i ∈ S} ≃ {j // j ∈ T}) : Fin n → α :=
  fun i => if hi : i ∈ S then c₂ (e ⟨i, hi⟩) else c₁ i

/-- The second family after interchanging the entries of the first family in the
positions `S` with its own entries in the positions `T`, along the bijection `e`. -/
def swapSnd (c₁ c₂ : Fin n → α) (S T : Finset (Fin n))
    (e : {i // i ∈ S} ≃ {j // j ∈ T}) : Fin n → α :=
  fun j => if hj : j ∈ T then c₁ (e.symm ⟨j, hj⟩) else c₂ j

/-- The order-preserving bijection between two finite sets of the same cardinality; this
is the matching used by the exchange rules, which maintain the vertical order. -/
def matchEquiv (S T : Finset (Fin n)) (h : T.card = S.card) :
    {i // i ∈ S} ≃ {j // j ∈ T} :=
  ((S.orderIsoOfFin rfl).symm.trans (T.orderIsoOfFin h)).toEquiv

theorem swapFst_map {β : Type*} (f : α → β) (c₁ c₂ : Fin n → α) (S T : Finset (Fin n))
    (e : {i // i ∈ S} ≃ {j // j ∈ T}) :
    swapFst (f ∘ c₁) (f ∘ c₂) S T e = f ∘ swapFst c₁ c₂ S T e := by
  funext i
  simp only [swapFst, Function.comp_apply]
  split <;> rfl

theorem swapSnd_map {β : Type*} (f : α → β) (c₁ c₂ : Fin n → α) (S T : Finset (Fin n))
    (e : {i // i ∈ S} ≃ {j // j ∈ T}) :
    swapSnd (f ∘ c₁) (f ∘ c₂) S T e = f ∘ swapSnd c₁ c₂ S T e := by
  funext j
  simp only [swapSnd, Function.comp_apply]
  split <;> rfl

end Swap

/-! ### The exchange term and its independence of the chosen matching -/

/-- The product of the two determinants obtained by interchanging the entries of `u` in
the positions `S` with the entries of `v` in the positions `T` (zero if the two sets do
not have the same cardinality). By `exchTerm_eq` the value does not depend on the
bijection `S ≃ T` used to perform the interchange. -/
noncomputable def exchTerm (u v : Fin n → Fin n → R) (S T : Finset (Fin n)) : R :=
  if h : T.card = S.card then
    colDet (swapFst u v S T (matchEquiv S T h)) * colDet (swapSnd u v S T (matchEquiv S T h))
  else 0

/-- Interchanging entries along different bijections `S ≃ T` gives the same product of
determinants: the two determinants change by the sign of the same permutation. -/
theorem exchTerm_eq_of_equiv (u v : Fin n → Fin n → R) (S T : Finset (Fin n))
    (e e' : {i // i ∈ S} ≃ {j // j ∈ T}) :
    colDet (swapFst u v S T e) * colDet (swapSnd u v S T e)
      = colDet (swapFst u v S T e') * colDet (swapSnd u v S T e') := by
  classical
  set σ : Equiv.Perm {i // i ∈ S} := e'.trans e.symm with hσ
  set τ : Equiv.Perm {j // j ∈ T} := e'.symm.trans e with hτ
  set π : Equiv.Perm (Fin n) := σ.extendDomain (Equiv.refl {i // i ∈ S}) with hπ
  set ρ : Equiv.Perm (Fin n) := τ.extendDomain (Equiv.refl {j // j ∈ T}) with hρ
  have h1 : swapFst u v S T e' = fun i => swapFst u v S T e (π i) := by
    funext i
    by_cases hi : i ∈ S
    · have hπi : π i = ((σ ⟨i, hi⟩ : {i // i ∈ S}) : Fin n) := by
        rw [hπ, Equiv.Perm.extendDomain_apply_subtype σ (Equiv.refl _) hi]
        rfl
      have hmem : ((σ ⟨i, hi⟩ : {i // i ∈ S}) : Fin n) ∈ S := (σ ⟨i, hi⟩).2
      simp only [swapFst, dif_pos hi, hπi, dif_pos hmem]
      congr 1
      have : (⟨((σ ⟨i, hi⟩ : {i // i ∈ S}) : Fin n), hmem⟩ : {i // i ∈ S}) = σ ⟨i, hi⟩ := rfl
      rw [this, hσ]
      simp
    · have hπi : π i = i := by
        rw [hπ, Equiv.Perm.extendDomain_apply_not_subtype σ (Equiv.refl _) hi]
      simp only [swapFst, dif_neg hi, hπi]
  have h2 : swapSnd u v S T e' = fun j => swapSnd u v S T e (ρ j) := by
    funext j
    by_cases hj : j ∈ T
    · have hρj : ρ j = ((τ ⟨j, hj⟩ : {j // j ∈ T}) : Fin n) := by
        rw [hρ, Equiv.Perm.extendDomain_apply_subtype τ (Equiv.refl _) hj]
        rfl
      have hmem : ((τ ⟨j, hj⟩ : {j // j ∈ T}) : Fin n) ∈ T := (τ ⟨j, hj⟩).2
      simp only [swapSnd, dif_pos hj, hρj, dif_pos hmem]
      congr 1
      have : (⟨((τ ⟨j, hj⟩ : {j // j ∈ T}) : Fin n), hmem⟩ : {j // j ∈ T}) = τ ⟨j, hj⟩ := rfl
      rw [this, hτ]
      simp
    · have hρj : ρ j = j := by
        rw [hρ, Equiv.Perm.extendDomain_apply_not_subtype τ (Equiv.refl _) hj]
      simp only [swapSnd, dif_neg hj, hρj]
  have hsignπ : Equiv.Perm.sign π = Equiv.Perm.sign σ := by
    rw [hπ, Equiv.Perm.sign_extendDomain]
  have hsignρ : Equiv.Perm.sign ρ = Equiv.Perm.sign σ := by
    rw [hρ, Equiv.Perm.sign_extendDomain]
    have : τ = e.permCongr σ⁻¹ := by
      apply Equiv.ext
      intro x
      simp [hτ, hσ, Equiv.permCongr_apply]
    rw [this, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_inv]
  rw [h1, h2, colDet_comp_perm, colDet_comp_perm, hsignπ, hsignρ]
  have hs : ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign σ : ℤ) : R) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num
  rw [mul_mul_mul_comm, hs, one_mul]

theorem exchTerm_eq (u v : Fin n → Fin n → R) (S T : Finset (Fin n))
    (e : {i // i ∈ S} ≃ {j // j ∈ T}) :
    exchTerm u v S T = colDet (swapFst u v S T e) * colDet (swapSnd u v S T e) := by
  have hcard : T.card = S.card := by
    have := Fintype.card_congr e
    simpa [Fintype.card_coe] using this.symm
  rw [exchTerm, dif_pos hcard]
  exact exchTerm_eq_of_equiv u v S T _ e

/-! ### Cramer's rule: the case of a single exchanged position -/

/-- Replacing one column of a family corresponds to `Matrix.updateCol`. -/
theorem colDet_update (u : Fin n → Fin n → R) (s : Fin n) (w : Fin n → R) :
    colDet (Function.update u s w) = ((Matrix.of fun i j => u j i).updateCol s w).det := by
  rw [colDet]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Matrix.updateCol_apply, Function.update_apply]
  split <;> simp_all

theorem colDet_update_smul (u : Fin n → Fin n → R) (s : Fin n) (a : R) (w : Fin n → R) :
    colDet (Function.update u s (a • w)) = a * colDet (Function.update u s w) := by
  rw [colDet_update, colDet_update, Matrix.det_updateCol_smul]

theorem colDet_update_add (u : Fin n → Fin n → R) (s : Fin n) (w w' : Fin n → R) :
    colDet (Function.update u s (w + w'))
      = colDet (Function.update u s w) + colDet (Function.update u s w') := by
  rw [colDet_update, colDet_update, colDet_update, Matrix.det_updateCol_add]

theorem colDet_update_zero (u : Fin n → Fin n → R) (s : Fin n) :
    colDet (Function.update u s 0) = 0 := by
  rw [colDet_update]
  refine Matrix.det_eq_zero_of_column_eq_zero s ?_
  intro i
  simp

/-- Multilinearity of the determinant in the column that is replaced. -/
theorem colDet_update_sum {ι : Type*} (t : Finset ι) (u : Fin n → Fin n → R) (s : Fin n)
    (c : ι → R) (w : ι → Fin n → R) :
    colDet (Function.update u s (∑ j ∈ t, c j • w j))
      = ∑ j ∈ t, c j * colDet (Function.update u s (w j)) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using colDet_update_zero u s
  | insert j t hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, colDet_update_add, colDet_update_smul, ih]

/-- **Sylvester's exchange identity for a single position.** This is Cramer's rule: the
case `k = 1` of Proposition `proposition:Sylvester-exchange` of the source article. -/
theorem colDet_mul_colDet_eq_sum_update (u v : Fin n → Fin n → R) (s : Fin n) :
    colDet u * colDet v
      = ∑ j : Fin n,
          colDet (Function.update u s (v j)) * colDet (Function.update v j (u s)) := by
  classical
  set A : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => v j i with hA
  set c : Fin n → R := A.cramer (u s) with hc
  have hcj : ∀ j, c j = colDet (Function.update v j (u s)) := by
    intro j
    rw [hc, Matrix.cramer_apply, colDet_update]
  have hmul : ∑ j : Fin n, c j • v j = A.det • u s := by
    have h := Matrix.mulVec_cramer A (u s)
    funext i
    have hi := congrFun h i
    simp only [Matrix.mulVec, dotProduct, hA, Matrix.of_apply, Pi.smul_apply,
      smul_eq_mul] at hi
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using hi
  have hkey : colDet (Function.update u s (A.det • u s))
      = ∑ j : Fin n, c j * colDet (Function.update u s (v j)) := by
    rw [← hmul, colDet_update_sum]
  rw [colDet_update_smul, Function.update_eq_self] at hkey
  have hAdet : A.det = colDet v := rfl
  rw [hAdet] at hkey
  rw [mul_comm]
  rw [hkey]
  exact Finset.sum_congr rfl fun j _ => by rw [hcj j, mul_comm]

/-! ### Exchanging along a permutation -/

/-- The bijection `S ≃ T` induced by a permutation of all positions mapping `S` onto
`T`. -/
def permEquiv (S T : Finset (Fin n)) (π : Equiv.Perm (Fin n)) (h : S.image π = T) :
    {i // i ∈ S} ≃ {j // j ∈ T} where
  toFun i := ⟨π i, by rw [← h]; exact Finset.mem_image_of_mem π i.2⟩
  invFun j := ⟨π.symm j, by
    have hj : (j : Fin n) ∈ S.image π := by rw [h]; exact j.2
    obtain ⟨x, hx, hxj⟩ := Finset.mem_image.mp hj
    have : π.symm (j : Fin n) = x := by rw [← hxj]; simp
    rw [this]; exact hx⟩
  left_inv i := by ext; simp
  right_inv j := by ext; simp

theorem swapFst_permEquiv {α : Type*} (c₁ c₂ : Fin n → α) (S T : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) (h : S.image π = T) :
    swapFst c₁ c₂ S T (permEquiv S T π h) = fun i => if i ∈ S then c₂ (π i) else c₁ i := by
  funext i
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    simp only [swapFst, dif_pos hi, permEquiv, Equiv.coe_fn_mk]
  · rw [if_neg hi]
    simp only [swapFst, dif_neg hi]

theorem swapSnd_permEquiv {α : Type*} (c₁ c₂ : Fin n → α) (S T : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) (h : S.image π = T) :
    swapSnd c₁ c₂ S T (permEquiv S T π h) = fun j => if j ∈ T then c₁ (π.symm j) else c₂ j := by
  funext j
  by_cases hj : j ∈ T
  · rw [if_pos hj]
    simp only [swapSnd, dif_pos hj, permEquiv, Equiv.coe_fn_symm_mk]
  · rw [if_neg hj]
    simp only [swapSnd, dif_neg hj]

/-- The exchange term computed along any permutation carrying `S` onto `T`. -/
theorem exchTerm_eq_perm (u v : Fin n → Fin n → R) (S T : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) (h : S.image π = T) :
    exchTerm u v S T
      = colDet (fun i => if i ∈ S then v (π i) else u i)
        * colDet (fun j => if j ∈ T then u (π.symm j) else v j) := by
  rw [exchTerm_eq u v S T (permEquiv S T π h), swapFst_permEquiv, swapSnd_permEquiv]

/-- Two finite sets of positions of the same cardinality are carried onto one another by
a permutation of all positions. -/
theorem exists_perm_image_eq (S T : Finset (Fin n)) (h : S.card = T.card) :
    ∃ π : Equiv.Perm (Fin n), S.image π = T := by
  classical
  have e : {x // x ∈ S} ≃ {x // x ∈ T} :=
    (S.equivFin).trans ((Fintype.equivFinOfCardEq (by simp [h])).symm)
  refine ⟨e.extendSubtype, ?_⟩
  apply Finset.ext
  intro y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Equiv.extendSubtype_apply_of_mem _ _ hx]
    exact (e ⟨x, hx⟩).2
  · intro hy
    exact ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).2, by
      rw [Equiv.extendSubtype_apply_of_mem _ _ (e.symm ⟨y, hy⟩).2]; simp⟩

/-! ### The inductive step -/

/-- The inductive step in the proof of Sylvester's identity: exchanging the positions
`S.erase s` with a fixed set `T'` can be rewritten, by Cramer's rule at the position `s`,
as a sum of exchanges of the larger set `S` with the sets `insert j T'`, minus the
exchanges of the sets `S.erase s'` with `T'`. -/
theorem exchTerm_erase_step (u v : Fin n → Fin n → R) (S : Finset (Fin n)) {s : Fin n}
    (hs : s ∈ S) (T' : Finset (Fin n)) (hcard : T'.card = (S.erase s).card) :
    exchTerm u v (S.erase s) T'
      = (∑ j ∈ univ \ T', exchTerm u v S (insert j T'))
        - ∑ s' ∈ S.erase s, exchTerm u v (S.erase s') T' := by
  classical
  have hsS' : s ∉ S.erase s := Finset.notMem_erase s S
  have hSins : insert s (S.erase s) = S := Finset.insert_erase hs
  obtain ⟨π', hπ'⟩ := exists_perm_image_eq (S.erase s) T' hcard.symm
  set U : Fin n → Fin n → R := fun i => if i ∈ S.erase s then v (π' i) else u i with hUdef
  set W : Fin n → Fin n → R := fun j => if j ∈ T' then u (π'.symm j) else v j with hWdef
  have hUW : exchTerm u v (S.erase s) T' = colDet U * colDet W :=
    exchTerm_eq_perm u v (S.erase s) T' π' hπ'
  have hUs : U s = u s := by rw [hUdef]; simp [hsS']
  have hπ's : π' s ∉ T' := by
    rw [← hπ']
    intro hmem
    obtain ⟨x, hx, hxs⟩ := Finset.mem_image.mp hmem
    rw [π'.injective hxs] at hx
    exact hsS' hx
  -- Case 1: the position `j` is not yet used
  have hA : ∀ j ∈ univ \ T',
      colDet (Function.update U s (W j)) * colDet (Function.update W j (U s))
        = exchTerm u v S (insert j T') := by
    intro j hj
    have hjT : j ∉ T' := by simpa using hj
    have hπi : ∀ i ∈ S.erase s, (Equiv.swap (π' s) j * π') i = π' i := by
      intro i hi
      have h1 : π' i ≠ π' s := by
        intro h
        rw [π'.injective h] at hi
        exact hsS' hi
      have h2 : π' i ≠ j := by
        intro h
        exact hjT (h ▸ (hπ' ▸ Finset.mem_image_of_mem π' hi))
      show Equiv.swap (π' s) j (π' i) = π' i
      exact Equiv.swap_apply_of_ne_of_ne h1 h2
    have hπs : (Equiv.swap (π' s) j * π') s = j := by
      show Equiv.swap (π' s) j (π' s) = j
      exact Equiv.swap_apply_left _ _
    have hπsymm : ∀ t, (Equiv.swap (π' s) j * π').symm t = π'.symm (Equiv.swap (π' s) j t) := by
      intro t
      rw [Equiv.symm_apply_eq]
      simp [Equiv.Perm.mul_apply]
    have himg : S.image (Equiv.swap (π' s) j * π') = insert j T' := by
      rw [← hSins, Finset.image_insert, hπs]
      congr 1
      rw [← hπ']
      exact Finset.image_congr (fun x hx => hπi x hx)
    have h1 : Function.update U s (W j)
        = fun i => if i ∈ S then v ((Equiv.swap (π' s) j * π') i) else u i := by
      funext i
      by_cases hi : i = s
      · subst hi
        rw [Function.update_self, if_pos hs, hπs, hWdef]
        simp [hjT]
      · rw [Function.update_of_ne hi]
        by_cases hiS' : i ∈ S.erase s
        · have hiS : i ∈ S := Finset.mem_of_mem_erase hiS'
          rw [hUdef]
          simp only [if_pos hiS', if_pos hiS, hπi i hiS']
        · have hiS : i ∉ S := fun h => hiS' (Finset.mem_erase.2 ⟨hi, h⟩)
          rw [hUdef]
          simp only [if_neg hiS', if_neg hiS]
    have h2 : Function.update W j (U s)
        = fun t => if t ∈ insert j T' then u ((Equiv.swap (π' s) j * π').symm t) else v t := by
      funext t
      by_cases ht : t = j
      · subst ht
        rw [Function.update_self, if_pos (Finset.mem_insert_self _ _), hUs, hπsymm]
        simp
      · rw [Function.update_of_ne ht]
        by_cases htT : t ∈ T'
        · have h1' : t ≠ π' s := fun h => hπ's (h ▸ htT)
          rw [hWdef]
          simp only [if_pos htT, if_pos (Finset.mem_insert_of_mem htT), hπsymm,
            Equiv.swap_apply_of_ne_of_ne h1' ht]
        · have : t ∉ insert j T' := by
            simp only [Finset.mem_insert]
            tauto
          rw [hWdef]
          simp only [if_neg htT, if_neg this]
    rw [h1, h2, exchTerm_eq_perm u v S (insert j T') _ himg]
  -- Case 2: the position `j` is already used
  have hB : ∀ j ∈ T',
      colDet (Function.update U s (W j)) * colDet (Function.update W j (U s))
        = - exchTerm u v (S.erase (π'.symm j)) T' := by
    intro j hjT
    obtain ⟨s', hs'def⟩ : ∃ s', π'.symm j = s' := ⟨_, rfl⟩
    rw [hs'def]
    have hπs' : π' s' = j := by rw [← hs'def]; simp
    have hs'S' : s' ∈ S.erase s := by
      have hmem : j ∈ (S.erase s).image π' := by rw [hπ']; exact hjT
      obtain ⟨x, hx, hxj⟩ := Finset.mem_image.mp hmem
      have hxs' : x = s' := π'.injective (by rw [hxj, hπs'])
      rw [← hxs']; exact hx
    have hss' : s ≠ s' := fun h => hsS' (h ▸ hs'S')
    have hWj : W j = u s' := by rw [hWdef]; simp [hjT, hs'def]
    have hπi : ∀ i ∈ (S.erase s).erase s', (Equiv.swap (π' s) j * π') i = π' i := by
      intro i hi
      have hi' : i ∈ S.erase s := Finset.mem_of_mem_erase hi
      have hine : i ≠ s' := (Finset.mem_erase.mp hi).1
      have h1 : π' i ≠ π' s := by
        intro h
        rw [π'.injective h] at hi'
        exact hsS' hi'
      have h2 : π' i ≠ j := by
        intro h
        exact hine (π'.injective (by rw [h, hπs']))
      show Equiv.swap (π' s) j (π' i) = π' i
      exact Equiv.swap_apply_of_ne_of_ne h1 h2
    have hπs : (Equiv.swap (π' s) j * π') s = j := by
      show Equiv.swap (π' s) j (π' s) = j
      exact Equiv.swap_apply_left _ _
    have hπsymm : ∀ t, (Equiv.swap (π' s) j * π').symm t = π'.symm (Equiv.swap (π' s) j t) := by
      intro t
      rw [Equiv.symm_apply_eq]
      simp [Equiv.Perm.mul_apply]
    have hSerase : S.erase s' = insert s ((S.erase s).erase s') := by
      rw [Finset.erase_right_comm]
      exact (Finset.insert_erase (Finset.mem_erase.2 ⟨hss', hs⟩)).symm
    have himg : (S.erase s').image (Equiv.swap (π' s) j * π') = T' := by
      rw [hSerase, Finset.image_insert, hπs]
      have : ((S.erase s).erase s').image (Equiv.swap (π' s) j * π')
          = ((S.erase s).erase s').image π' := Finset.image_congr (fun x hx => hπi x hx)
      rw [this, Finset.image_erase π'.injective, hπ', hπs', Finset.insert_erase hjT]
    -- the second determinant
    have h2 : Function.update W j (U s)
        = fun t => if t ∈ T' then u ((Equiv.swap (π' s) j * π').symm t) else v t := by
      funext t
      by_cases ht : t = j
      · subst ht
        rw [Function.update_self, if_pos hjT, hUs, hπsymm]
        simp
      · rw [Function.update_of_ne ht]
        by_cases htT : t ∈ T'
        · have h1' : t ≠ π' s := fun h => hπ's (h ▸ htT)
          rw [hWdef]
          simp only [if_pos htT, hπsymm, Equiv.swap_apply_of_ne_of_ne h1' ht]
        · rw [hWdef]
          simp only [if_neg htT]
    -- the first determinant, after swapping the two positions `s` and `s'`
    obtain ⟨Y, hY⟩ : ∃ Y : Fin n → Fin n → R,
        Y = fun i => if i ∈ S.erase s' then v ((Equiv.swap (π' s) j * π') i) else u i := ⟨_, rfl⟩
    have h1 : Function.update U s (W j) = fun i => Y (Equiv.swap s s' i) := by
      funext i
      by_cases hi : i = s
      · rw [hi, Function.update_self, hWj, Equiv.swap_apply_left, hY]
        simp only
        rw [if_neg (fun h => (Finset.mem_erase.mp h).1 rfl)]
      · by_cases hi' : i = s'
        · rw [Function.update_of_ne hi, hi', Equiv.swap_apply_right, hUdef, hY]
          simp only
          rw [if_pos hs'S', if_pos (Finset.mem_erase.2 ⟨hss', hs⟩), hπs, hπs']
        · rw [Function.update_of_ne hi, Equiv.swap_apply_of_ne_of_ne hi hi', hUdef, hY]
          simp only
          by_cases hiS' : i ∈ S.erase s
          · have hiSe : i ∈ S.erase s' :=
              Finset.mem_erase.2 ⟨hi', Finset.mem_of_mem_erase hiS'⟩
            have hii : i ∈ (S.erase s).erase s' := Finset.mem_erase.2 ⟨hi', hiS'⟩
            rw [if_pos hiS', if_pos hiSe, hπi i hii]
          · have hiSe : i ∉ S.erase s' := by
              intro h
              exact hiS' (Finset.mem_erase.2 ⟨hi, Finset.mem_of_mem_erase h⟩)
            rw [if_neg hiS', if_neg hiSe]
    rw [h1, h2, colDet_comp_perm, Equiv.Perm.sign_swap hss',
      exchTerm_eq_perm u v (S.erase s') T' _ himg, ← hY]
    push_cast
    ring
  -- assembling the two cases
  rw [hUW, colDet_mul_colDet_eq_sum_update U W s,
    ← Finset.sum_sdiff (Finset.subset_univ T'), Finset.sum_congr rfl hA,
    Finset.sum_congr rfl hB]
  have himg2 : T'.image (π'.symm) = S.erase s := by
    rw [← hπ', Finset.image_image]
    simp
  rw [← himg2, Finset.sum_image (fun x _ y _ h => π'.symm.injective h)]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]

/-! ### Counting the ways of enlarging a set of positions -/

/-- Every set of `k+1` positions arises in exactly `k+1` ways by adding one position to a
set of `k` positions. -/
theorem sum_sdiff_insert_powersetCard (k : ℕ) (f : Finset (Fin n) → R) :
    ∑ T' ∈ powersetCard k univ, ∑ j ∈ univ \ T', f (insert j T')
      = ((k : R) + 1) * ∑ T ∈ powersetCard (k + 1) univ, f T := by
  classical
  have hbij : ∑ T' ∈ powersetCard k (univ : Finset (Fin n)), ∑ j ∈ univ \ T', f (insert j T')
      = ∑ T ∈ powersetCard (k + 1) (univ : Finset (Fin n)), ∑ _j ∈ T, f T := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (i := fun p => (⟨insert p.2 p.1, p.2⟩ : (_ : Finset (Fin n)) × Fin n))
      (j := fun p => (⟨p.1.erase p.2, p.2⟩ : (_ : Finset (Fin n)) × Fin n)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨T', j⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff, Finset.mem_univ,
        true_and] at hp ⊢
      obtain ⟨⟨-, hcard⟩, hj⟩ := hp
      exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem hj, hcard]⟩,
        Finset.mem_insert_self _ _⟩
    · rintro ⟨T, j⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff, Finset.mem_univ,
        true_and] at hp ⊢
      obtain ⟨⟨-, hcard⟩, hj⟩ := hp
      refine ⟨⟨Finset.subset_univ _, by rw [Finset.card_erase_of_mem hj, hcard]; rfl⟩, ?_⟩
      exact Finset.notMem_erase _ _
    · rintro ⟨T', j⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_sdiff, Finset.mem_univ, true_and] at hp
      simp [Finset.erase_insert hp.2]
    · rintro ⟨T, j⟩ hp
      simp only [Finset.mem_sigma] at hp
      simp [Finset.insert_erase hp.2]
    · rintro ⟨T', j⟩ _
      rfl
  rw [hbij, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro T hT
  rw [Finset.sum_const, (Finset.mem_powersetCard.mp hT).2]
  push_cast
  ring

/-! ### Sylvester's identity -/

section RatAlgebra

variable [Algebra ℚ R]

/-- **Sylvester's exchange identity** over a `ℚ`-algebra. The proof is by induction on the
number of exchanged positions, using Cramer's rule; the inductive step divides by the
number of exchanged positions, whence the assumption on the coefficients, which is
removed in `colDet_mul_colDet_eq_sum_exchTerm`. -/
theorem colDet_mul_colDet_eq_sum_exchTerm_ratAlg (u v : Fin n → Fin n → R) :
    ∀ (k : ℕ) (S : Finset (Fin n)), S.card = k →
      colDet u * colDet v = ∑ T ∈ powersetCard k univ, exchTerm u v S T := by
  intro k
  induction k with
  | zero =>
      intro S hS
      have hS0 : S = ∅ := Finset.card_eq_zero.mp hS
      subst hS0
      rw [Finset.powersetCard_zero, Finset.sum_singleton,
        exchTerm_eq_perm u v ∅ ∅ (Equiv.refl _) (by simp)]
      simp
  | succ k ih =>
      intro S hS
      obtain ⟨s0, hs0⟩ : ∃ x, x ∈ S := Finset.card_pos.mp (by omega)
      have hS'card : (S.erase s0).card = k := by
        rw [Finset.card_erase_of_mem hs0, hS]
        omega
      have hIH := ih (S.erase s0) hS'card
      have hstep : ∀ T' ∈ powersetCard k (univ : Finset (Fin n)),
          exchTerm u v (S.erase s0) T'
            = (∑ j ∈ univ \ T', exchTerm u v S (insert j T'))
              - ∑ s' ∈ S.erase s0, exchTerm u v (S.erase s') T' := by
        intro T' hT'
        exact exchTerm_erase_step u v S hs0 T'
          (by rw [hS'card, (Finset.mem_powersetCard.mp hT').2])
      rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib,
        sum_sdiff_insert_powersetCard] at hIH
      have hpart2 : ∑ T' ∈ powersetCard k (univ : Finset (Fin n)),
          ∑ s' ∈ S.erase s0, exchTerm u v (S.erase s') T'
          = (k : R) * (colDet u * colDet v) := by
        rw [Finset.sum_comm]
        have hin : ∀ s' ∈ S.erase s0,
            ∑ T' ∈ powersetCard k (univ : Finset (Fin n)), exchTerm u v (S.erase s') T'
              = colDet u * colDet v := by
          intro s' hs'
          exact (ih (S.erase s')
            (by rw [Finset.card_erase_of_mem (Finset.mem_of_mem_erase hs'), hS]; omega)).symm
        rw [Finset.sum_congr rfl hin, Finset.sum_const, Finset.card_erase_of_mem hs0, hS]
        simp [nsmul_eq_mul]
      rw [hpart2] at hIH
      have h2 : ((k : R) + 1) * (colDet u * colDet v)
          = ((k : R) + 1) * ∑ T ∈ powersetCard (k + 1) univ, exchTerm u v S T := by
        linear_combination hIH
      obtain ⟨c, hc⟩ : ∃ c : R, c * ((k : R) + 1) = 1 :=
        ⟨algebraMap ℚ R (1 / ((k : ℚ) + 1)), by
          rw [show ((k : R) + 1) = algebraMap ℚ R ((k : ℚ) + 1) by
            rw [map_add, map_natCast, map_one], ← map_mul]
          rw [show (1 / ((k : ℚ) + 1)) * ((k : ℚ) + 1) = 1 by
            field_simp]
          exact map_one _⟩
      calc colDet u * colDet v = (c * ((k : R) + 1)) * (colDet u * colDet v) := by
            rw [hc, one_mul]
        _ = c * (((k : R) + 1) * (colDet u * colDet v)) := by ring
        _ = c * (((k : R) + 1) * ∑ T ∈ powersetCard (k + 1) univ, exchTerm u v S T) := by rw [h2]
        _ = (c * ((k : R) + 1)) * ∑ T ∈ powersetCard (k + 1) univ, exchTerm u v S T := by ring
        _ = ∑ T ∈ powersetCard (k + 1) univ, exchTerm u v S T := by rw [hc, one_mul]

end RatAlgebra

/-- The exchange term commutes with ring homomorphisms. -/
theorem exchTerm_map {R' : Type*} [CommRing R'] (φ : R →+* R') (u v : Fin n → Fin n → R)
    (S T : Finset (Fin n)) :
    φ (exchTerm u v S T)
      = exchTerm (fun j i => φ (u j i)) (fun j i => φ (v j i)) S T := by
  unfold exchTerm
  split_ifs with h
  · rw [map_mul, colDet_map, colDet_map]
    have e1 : (fun j i => φ (swapFst u v S T (matchEquiv S T h) j i))
        = swapFst (fun j i => φ (u j i)) (fun j i => φ (v j i)) S T (matchEquiv S T h) := by
      funext j i
      simp only [swapFst]
      split <;> rfl
    have e2 : (fun j i => φ (swapSnd u v S T (matchEquiv S T h) j i))
        = swapSnd (fun j i => φ (u j i)) (fun j i => φ (v j i)) S T (matchEquiv S T h) := by
      funext j i
      simp only [swapSnd]
      split <;> rfl
    rw [e1, e2]
  · exact map_zero φ

/-- **Sylvester's exchange identity** over an arbitrary commutative ring: the product of
the determinants of two families of columns equals the sum, over all sets `T` of
positions with `#T = #S`, of the products of the determinants obtained by interchanging
the entries in the positions `S` of the first family with the entries in the positions
`T` of the second one, maintaining the order. This is Proposition
`proposition:Sylvester-exchange` of the source article. -/
theorem colDet_mul_colDet_eq_sum_exchTerm (u v : Fin n → Fin n → R) (S : Finset (Fin n)) :
    colDet u * colDet v = ∑ T ∈ powersetCard S.card univ, exchTerm u v S T := by
  classical
  -- the identity for the generic matrices with integer coefficients
  set ι := Bool × Fin n × Fin n with hι
  set gu : Fin n → Fin n → MvPolynomial ι ℤ := fun j i => MvPolynomial.X (true, j, i) with hgu
  set gv : Fin n → Fin n → MvPolynomial ι ℤ := fun j i => MvPolynomial.X (false, j, i) with hgv
  have hgen : colDet gu * colDet gv = ∑ T ∈ powersetCard S.card univ, exchTerm gu gv S T := by
    have hQ := colDet_mul_colDet_eq_sum_exchTerm_ratAlg
      (fun j i => (MvPolynomial.X (true, j, i) : MvPolynomial ι ℚ))
      (fun j i => (MvPolynomial.X (false, j, i) : MvPolynomial ι ℚ)) S.card S rfl
    have hinj : Function.Injective
        (MvPolynomial.map (Int.castRingHom ℚ) : MvPolynomial ι ℤ → MvPolynomial ι ℚ) :=
      MvPolynomial.map_injective _ Int.cast_injective
    apply hinj
    rw [map_mul, colDet_map, colDet_map, map_sum]
    simp only [hgu, hgv, MvPolynomial.map_X]
    rw [hQ]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [exchTerm_map]
    simp only [hgu, hgv, MvPolynomial.map_X]
  -- specializing the generic identity
  set φ : MvPolynomial ι ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R)
      (fun p : ι => if p.1 then u p.2.1 p.2.2 else v p.2.1 p.2.2) with hφ
  have hgu' : (fun (j : Fin n) (i : Fin n) => φ (gu j i)) = u := by
    funext j i
    rw [hφ, hgu]
    simp
  have hgv' : (fun (j : Fin n) (i : Fin n) => φ (gv j i)) = v := by
    funext j i
    rw [hφ, hgv]
    simp
  have := congrArg φ hgen
  rw [map_mul, colDet_map, colDet_map, map_sum, hgu', hgv'] at this
  rw [this]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [exchTerm_map, hgu', hgv']

end RigidityTableaux
