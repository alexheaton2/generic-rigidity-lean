import RequestProject.Rigidity

/-!
# Trivial infinitesimal motions

The source article (`main.tex`, Section "Geometric results") defines a framework `(G,p)`
in `ℝ^d` to be *infinitesimally rigid* when the right kernel of the coefficient matrix
`A` of the self-stress equations has dimension `binom (d+1) 2`, the number of degrees of
freedom of a rigid body motion of `ℝ^d`.

This file supplies the fact underlying that definition, and needed in the proof of
Corollary `cor:characterization` of the source article: for a placement with `|V| ≥ d`
in which any `d+1` vertices are affinely independent, the space of infinitesimal flexes
always has dimension at least `binom (d+1) 2`, because it contains the *trivial*
infinitesimal motions `q_i = A p_i + b` with `A` skew-symmetric, and these form a space
of dimension `binom d 2 + d = binom (d+1) 2`.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

/-! ### Skew-symmetric matrices, coordinatised by the pairs `k < l` -/

variable {d : ℕ}

/-- The index set `{(k,l) : k < l}` of the entries above the diagonal of a `d × d`
matrix; it parametrises the skew-symmetric `d × d` matrices, i.e. the infinitesimal
rotations of `ℝ^d`. -/
abbrev SkewIdx (d : ℕ) := {x : Fin d × Fin d // x.1 < x.2}

/-- The number of entries strictly above the diagonal of a `d × d` matrix is
`binom d 2`; equivalently, the space of infinitesimal rotations of `ℝ^d` has dimension
`binom d 2`. -/
theorem card_skewIdx (d : ℕ) : Fintype.card (SkewIdx d) = d.choose 2 := by
  classical
  have hsum : ∀ n : ℕ, ∑ i ∈ range n, i = n.choose 2 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]; simp [Nat.add_comm]
  rw [Fintype.card_subtype, Finset.card_filter, ← Finset.univ_product_univ,
    Finset.sum_product_right]
  have h : ∀ j : Fin d, ∑ i : Fin d, (if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    rw [← Fin.card_Iio j]
    congr 1
    ext i
    simp
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i), hsum]

/-- The skew-symmetric matrix with prescribed entries above the diagonal: an
infinitesimal rotation of `ℝ^d`. -/
def skewMat (a : SkewIdx d → ℝ) (k l : Fin d) : ℝ :=
  if h : k < l then a ⟨(k, l), h⟩ else if h' : l < k then -a ⟨(l, k), h'⟩ else 0

/-- `skewMat a` is skew-symmetric. -/
theorem skewMat_antisymm (a : SkewIdx d → ℝ) (k l : Fin d) :
    skewMat a k l = -skewMat a l k := by
  unfold skewMat
  rcases lt_trichotomy k l with h | h | h
  · rw [dif_pos h, dif_neg (asymm h), dif_pos h, neg_neg]
  · subst h; simp
  · rw [dif_neg (asymm h), dif_pos h, dif_pos h]

/-- The entries of `skewMat a` above the diagonal are the coordinates of `a`. -/
theorem skewMat_apply_of_lt (a : SkewIdx d → ℝ) (x : SkewIdx d) :
    skewMat a x.1.1 x.1.2 = a x := by
  unfold skewMat
  rw [dif_pos x.2]

/-- Additivity of `a ↦ skewMat a`. -/
theorem skewMat_add (a a' : SkewIdx d → ℝ) (k l : Fin d) :
    skewMat (a + a') k l = skewMat a k l + skewMat a' k l := by
  unfold skewMat
  split_ifs <;> simp [Pi.add_apply]
  ring

/-- Homogeneity of `a ↦ skewMat a`. -/
theorem skewMat_smul (c : ℝ) (a : SkewIdx d → ℝ) (k l : Fin d) :
    skewMat (c • a) k l = c * skewMat a k l := by
  unfold skewMat
  split_ifs <;> simp [Pi.smul_apply]

/-- The infinitesimal rotation `w ↦ A w` attached to `a`, as a linear map. -/
noncomputable def skewApply (a : SkewIdx d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun w := fun k => ∑ l, skewMat a k l * w l
  map_add' w w' := by
    funext k
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  map_smul' c w := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

theorem skewApply_apply (a : SkewIdx d → ℝ) (w : Fin d → ℝ) (k : Fin d) :
    skewApply a w k = ∑ l, skewMat a k l * w l := rfl

/-- An infinitesimal rotation is orthogonal to the vector it is applied to:
`⟪A u, u⟫ = 0` for skew-symmetric `A`. This is why a trivial infinitesimal motion
preserves all bar lengths to first order. -/
theorem skewApply_dot_self (a : SkewIdx d → ℝ) (u : Fin d → ℝ) :
    ∑ k, skewApply a u k * u k = 0 := by
  have h : ∑ k, skewApply a u k * u k = -∑ k, skewApply a u k * u k := by
    calc ∑ k, skewApply a u k * u k
        = ∑ k, ∑ l, skewMat a k l * u l * u k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [skewApply_apply, Finset.sum_mul]
      _ = ∑ l, ∑ k, skewMat a k l * u l * u k := Finset.sum_comm
      _ = -∑ k, ∑ l, skewMat a k l * u l * u k := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [skewMat_antisymm a l k]
          ring
      _ = -∑ k, skewApply a u k * u k := by
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [skewApply_apply, Finset.sum_mul]
  linarith

/-- A skew-symmetric matrix whose kernel has codimension at most one is zero: an
infinitesimal rotation fixing a hyperplane of `ℝ^d` pointwise is trivial. -/
theorem skewMat_eq_zero_of_codim_le_one (a : SkewIdx d → ℝ) (K : Submodule ℝ (Fin d → ℝ))
    (hK : K ≤ LinearMap.ker (skewApply a)) (hdim : d ≤ Module.finrank ℝ K + 1) :
    ∀ k l, skewMat a k l = 0 := by
  classical
  set B : (Fin d → ℝ) → (Fin d → ℝ) → ℝ := fun y z => ∑ k, y k * skewApply a z k with hB
  have hBanti : ∀ y z, B y z = -B z y := by
    intro y z
    have h1 : B y z = ∑ k, ∑ l, y k * (skewMat a k l * z l) := by
      simp only [hB, skewApply_apply, Finset.mul_sum]
    have h2 : B z y = ∑ k, ∑ l, z k * (skewMat a k l * y l) := by
      simp only [hB, skewApply_apply, Finset.mul_sum]
    rw [h1, h2, Finset.sum_comm (γ := Fin d)]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [skewMat_antisymm a l k]
    ring
  have hBright : ∀ y z, z ∈ K → B y z = 0 := by
    intro y z hz
    have : skewApply a z = 0 := hK hz
    simp [hB, this]
  have hBleft : ∀ y z, y ∈ K → B y z = 0 := by
    intro y z hy
    rw [hBanti, hBright z y hy, neg_zero]
  have hBself : ∀ y, B y y = 0 := by
    intro y
    have := hBanti y y
    linarith
  -- any two vectors are linearly dependent modulo `K`
  have hdep : ∀ y z : Fin d → ℝ, ∃ s t : ℝ, ¬(s = 0 ∧ t = 0) ∧ s • y + t • z ∈ K := by
    intro y z
    have hq : Module.finrank ℝ ((Fin d → ℝ) ⧸ K) ≤ 1 := by
      have h := Submodule.finrank_quotient_add_finrank K
      have hd : Module.finrank ℝ (Fin d → ℝ) = d := by
        simp [Module.finrank_fintype_fun_eq_card]
      omega
    have hni : ¬ LinearIndependent ℝ ![K.mkQ y, K.mkQ z] := by
      intro hli
      have := hli.fintype_card_le_finrank
      simp only [Fintype.card_fin] at this
      omega
    rw [LinearIndependent.pair_iff] at hni
    push_neg at hni
    obtain ⟨s, t, hst, hne⟩ := hni
    refine ⟨s, t, ?_, ?_⟩
    · rintro ⟨rfl, rfl⟩
      exact hne rfl rfl
    · have h3 : K.mkQ (s • y + t • z) = 0 := by
        rw [map_add, map_smul, map_smul]
        exact hst
      rw [Submodule.mkQ_apply] at h3
      exact (Submodule.Quotient.mk_eq_zero K).1 h3
  have hBzero : ∀ y z, B y z = 0 := by
    intro y z
    obtain ⟨s, t, hst, hmem⟩ := hdep y z
    have h1 : B y (s • y + t • z) = 0 := hBright y _ hmem
    have h2 : B z (s • y + t • z) = 0 := hBright z _ hmem
    have e1 : B y (s • y + t • z) = s * B y y + t * B y z := by
      simp only [hB, map_add, map_smul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have e2 : B z (s • y + t • z) = s * B z y + t * B z z := by
      simp only [hB, map_add, map_smul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, hBself y, mul_zero, zero_add] at h1
    rw [e2, hBself z, mul_zero, add_zero] at h2
    rcases eq_or_ne t 0 with ht | ht
    · have hs : s ≠ 0 := fun hs => hst ⟨hs, ht⟩
      have : B z y = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h hs
        · exact h
      rw [hBanti, this, neg_zero]
    · rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h ht
      · exact h
  intro k l
  have h := hBzero (fun m => if m = k then 1 else 0) (fun m => if m = l then 1 else 0)
  simp only [hB, skewApply_apply] at h
  rw [Finset.sum_eq_single k] at h
  · simpa using h
  · intro b _ hb; simp [hb]
  · intro hk; exact absurd (mem_univ k) hk

/-! ### The trivial infinitesimal motions of a placement -/

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The **trivial infinitesimal motions** `q_i = A p_i + b` of a placement `p`, with `A`
skew-symmetric (an infinitesimal rotation) and `b` a translation velocity. These are the
`binom (d+1) 2` degrees of freedom of a rigid body motion of `ℝ^d` referred to in the
definition of infinitesimal rigidity in the source article (`main.tex`, Section
"Geometric results"). -/
noncomputable def trivialMotion (p : V → Fin d → ℝ) :
    ((SkewIdx d → ℝ) × (Fin d → ℝ)) →ₗ[ℝ] (V → Fin d → ℝ) where
  toFun ab := fun i k => skewApply ab.1 (p i) k + ab.2 k
  map_add' ab ab' := by
    funext i k
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, skewApply_apply]
    have hl : ∀ l, skewMat (ab.1 + ab'.1) k l * p i l
        = skewMat ab.1 k l * p i l + skewMat ab'.1 k l * p i l := by
      intro l; rw [skewMat_add]; ring
    rw [Finset.sum_congr rfl fun l _ => hl l, Finset.sum_add_distrib]
    ring
  map_smul' c ab := by
    funext i k
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      skewApply_apply]
    have hl : ∀ l, skewMat (c • ab.1) k l * p i l = c * (skewMat ab.1 k l * p i l) := by
      intro l; rw [skewMat_smul]; ring
    rw [Finset.sum_congr rfl fun l _ => hl l, ← Finset.mul_sum]
    ring

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
theorem trivialMotion_apply (p : V → Fin d → ℝ) (ab : (SkewIdx d → ℝ) × (Fin d → ℝ))
    (i : V) (k : Fin d) : trivialMotion p ab i k = skewApply ab.1 (p i) k + ab.2 k := rfl

omit [Fintype V] [DecidableEq V] in
/-- A trivial infinitesimal motion is an infinitesimal flex of every framework on the
placement `p`: it lies in the right kernel of the matrix `A` of the source article
(`main.tex`, Section "Geometric results"). -/
theorem trivialMotion_mem_infFlexes (p : V → Fin d → ℝ)
    (ab : (SkewIdx d → ℝ) × (Fin d → ℝ)) :
    trivialMotion p ab ∈ infFlexes (G := G) p := by
  show rigidityMap (G := G) p (trivialMotion p ab) = 0
  funext e
  show ∑ k : Fin d, (trivialMotion p ab e.1.1 k - trivialMotion p ab e.1.2 k)
      * (p e.1.1 k - p e.1.2 k) = 0
  have hdiff : ∀ k : Fin d, trivialMotion p ab e.1.1 k - trivialMotion p ab e.1.2 k
      = skewApply ab.1 (p e.1.1 - p e.1.2) k := by
    intro k
    rw [trivialMotion_apply, trivialMotion_apply, skewApply_apply, skewApply_apply,
      skewApply_apply]
    have hl : ∀ l, skewMat ab.1 k l * (p e.1.1 - p e.1.2) l
        = skewMat ab.1 k l * p e.1.1 l - skewMat ab.1 k l * p e.1.2 l := by
      intro l; simp only [Pi.sub_apply]; ring
    rw [Finset.sum_congr rfl fun l _ => hl l, Finset.sum_sub_distrib]
    ring
  rw [Finset.sum_congr rfl fun k _ => by
    rw [hdiff k, show p e.1.1 k - p e.1.2 k = (p e.1.1 - p e.1.2) k from rfl]]
  exact skewApply_dot_self ab.1 (p e.1.1 - p e.1.2)

omit [LinearOrder V] in
/-- The trivial infinitesimal motions of an affinely independent placement of at least
`d` vertices are pairwise distinct: an infinitesimal rotation together with a translation
which fixes all the vertices to first order is zero. -/
theorem trivialMotion_injective (p : V → Fin d → ℝ) (hd : 0 < d)
    (hp : AffinelyIndependentPlacement d p) (hV : d ≤ Fintype.card V) :
    Function.Injective (trivialMotion (V := V) p) := by
  classical
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  rintro ab hab
  have h0 : ∀ (i : V) (k : Fin d), skewApply ab.1 (p i) k + ab.2 k = 0 := by
    intro i k
    have : trivialMotion p ab = 0 := hab
    have := congrFun (congrFun this i) k
    simpa [trivialMotion_apply] using this
  -- choose `d` vertices; their difference vectors span a hyperplane
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (univ : Finset V)) (n := d)
    (by simpa using hV)
  have hne : s.Nonempty := by
    rw [← Finset.card_pos, hs]; exact hd
  obtain ⟨i0, hi0⟩ := hne
  have hai : AffineIndependent ℝ (fun i : (s : Set V) => (p i : Fin d → ℝ)) :=
    hp s (by omega)
  have hli : LinearIndependent ℝ
      (fun i : {x : ((s : Set V)) // x ≠ ⟨i0, hi0⟩} => (p i : Fin d → ℝ) - p i0) := by
    have := (affineIndependent_iff_linearIndependent_vsub ℝ
      (fun i : (s : Set V) => (p i : Fin d → ℝ)) ⟨i0, hi0⟩).1 hai
    simpa [vsub_eq_sub] using this
  set W : Submodule ℝ (Fin d → ℝ) :=
    Submodule.span ℝ (Set.range
      (fun i : {x : ((s : Set V)) // x ≠ ⟨i0, hi0⟩} => (p i : Fin d → ℝ) - p i0)) with hW
  have hcardidx : Fintype.card {x : ((s : Set V)) // x ≠ (⟨i0, hi0⟩ : (s : Set V))} = d - 1 := by
    rw [Fintype.card_subtype_compl]
    simp [hs]
  have hWrank : Module.finrank ℝ W = d - 1 := by
    rw [hW, finrank_span_eq_card hli, hcardidx]
  have hWker : W ≤ LinearMap.ker (skewApply ab.1) := by
    rw [hW, Submodule.span_le]
    rintro v ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    funext k
    have hi := h0 (i : V) k
    have hi0' := h0 i0 k
    have : skewApply ab.1 ((p i : Fin d → ℝ) - p i0) k
        = skewApply ab.1 (p i) k - skewApply ab.1 (p i0) k := by
      rw [show ((p (i : V) : Fin d → ℝ) - p i0) = p i - p i0 from rfl]
      rw [map_sub]
      rfl
    rw [this]
    simp only [Pi.zero_apply]
    linarith
  have hzero := skewMat_eq_zero_of_codim_le_one ab.1 W hWker (by omega)
  have ha : ab.1 = 0 := by
    funext x
    rw [← skewMat_apply_of_lt ab.1 x, hzero]
    rfl
  have hb : ab.2 = 0 := by
    have hVpos : 0 < Fintype.card V := lt_of_lt_of_le hd hV
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp hVpos
    funext k
    have := h0 i k
    rw [ha] at this
    simp only [skewApply_apply, skewMat] at this
    simp only [Pi.zero_apply] at this ⊢
    simpa using this
  exact Prod.ext ha hb

/-- The space of infinitesimal flexes of an affinely independent placement of at least
`d` vertices has dimension at least `binom (d+1) 2`, since it contains the trivial
infinitesimal motions. This is the lower bound implicit in the definition of
infinitesimal rigidity of the source article (`main.tex`, Section "Geometric results":
*"`dim right ker A = binom (d+1) 2`"*). -/
theorem choose_two_le_finrank_infFlexes (p : V → Fin d → ℝ) (hd : 0 < d)
    (hp : AffinelyIndependentPlacement d p) (hV : d ≤ Fintype.card V) :
    Nat.choose (d + 1) 2 ≤ Module.finrank ℝ (infFlexes (G := G) p) := by
  classical
  have hinj : Function.Injective
      (LinearMap.codRestrict (infFlexes (G := G) p) (trivialMotion p)
        (trivialMotion_mem_infFlexes (G := G) p)) := by
    intro x y hxy
    exact trivialMotion_injective p hd hp hV (congrArg Subtype.val hxy)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hdom : Module.finrank ℝ ((SkewIdx d → ℝ) × (Fin d → ℝ)) = Nat.choose (d + 1) 2 := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, card_skewIdx, Fintype.card_fin,
      Nat.choose_succ_succ d 1]
    simp [Nat.add_comm]
  omega

end RigidityTableaux
