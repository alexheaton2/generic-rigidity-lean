import RequestProject.Orientation

/-!
# Existence of `d`-orientations

The source article constructs a `d`-orientation `Γ` on any graph by choosing, at every
vertex of the non-desert graph, `d` of its incident edges as incoming, and then removing
the cycles of the resulting stream digraph (`main.tex`, Subsection "Main Results", *"The
orientation `Γ`"*).

Here we show that such an orientation always exists, by making the canonical choice:
at each vertex `a`, the `d` incoming edges are those joining `a` to its `d` smallest
non-desert neighbours. With this choice the stream digraph is automatically acyclic: the
function `rank a = pos(g(a)) + pos(a)`, where `g(a)` is the largest of the `d` chosen
neighbours of `a` and `pos` counts the vertices below a given one, strictly increases
along every stream arrow.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}

/-- The position of a vertex in the fixed order on `V`: the number of vertices below it. -/
def posOf (x : V) : ℕ := #(univ.filter (fun u : V => u < x))

omit [DecidableEq V] in
theorem posOf_lt_posOf {x y : V} (h : x < y) : posOf x < posOf y := by
  classical
  apply Finset.card_lt_card
  constructor
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    exact hu.trans h
  · intro hsub
    have := hsub (by simp [h] : x ∈ univ.filter (fun u : V => u < y))
    simp only [mem_filter, mem_univ, true_and] at this
    exact lt_irrefl x this

omit [DecidableEq V] in
theorem posOf_le_posOf {x y : V} (h : x ≤ y) : posOf x ≤ posOf y := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact (posOf_lt_posOf h).le

omit [Fintype V] in
/-- Counting lemma: inside a finite set `S`, exactly `k` elements have fewer than `k`
elements of `S` below them, provided `k ≤ #S`. In other words, the `k` smallest elements
of `S` are exactly those of rank `< k`. -/
theorem card_filter_rank_lt (S : Finset V) (k : ℕ) (hk : k ≤ #S) :
    #(S.filter (fun b => #(S.filter (fun c => c < b)) < k)) = k := by
  classical
  set iso := S.orderIsoOfFin (rfl : #S = #S) with hiso
  have hinj : Function.Injective (fun j : Fin #S => (iso j : V)) := by
    intro a b hab
    exact iso.injective (Subtype.ext hab)
  have hrank : ∀ j : Fin #S, #(S.filter (fun c => c < (iso j : V))) = (j : ℕ) := by
    intro j
    have himg : S.filter (fun c => c < (iso j : V))
        = (univ.filter (fun i : Fin #S => i < j)).image (fun i => (iso i : V)) := by
      ext x
      simp only [mem_filter, mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨hxS, hlt⟩
        refine ⟨iso.symm ⟨x, hxS⟩, ?_, by simp⟩
        by_contra hcon
        push_neg at hcon
        have := iso.monotone hcon
        simp only [OrderIso.apply_symm_apply] at this
        exact absurd hlt (not_lt.mpr (by simpa using this))
      · rintro ⟨i, hi, rfl⟩
        exact ⟨(iso i).2, iso.strictMono hi⟩
    rw [himg, Finset.card_image_of_injective _ hinj]
    have : (univ.filter (fun i : Fin #S => i < j)) = Finset.Iio j := by ext i; simp
    rw [this, Fin.card_Iio]
  have hset : S.filter (fun b => #(S.filter (fun c => c < b)) < k)
      = (univ.filter (fun j : Fin #S => (j : ℕ) < k)).image (fun j => (iso j : V)) := by
    ext x
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hxS, hlt⟩
      refine ⟨iso.symm ⟨x, hxS⟩, ?_, by simp⟩
      have := hrank (iso.symm ⟨x, hxS⟩)
      simp only [OrderIso.apply_symm_apply] at this
      rw [← this]
      exact hlt
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(iso j).2, by rw [hrank j]; exact hj⟩
  rw [hset, Finset.card_image_of_injective _ hinj]
  have h : (univ.filter (fun j : Fin #S => (j : ℕ) < k)) = univ.map (Fin.castLEEmb hk) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_map, Fin.castLEEmb,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hj
      refine ⟨⟨j, hj⟩, ?_⟩
      ext; simp
    · rintro ⟨i, hi⟩
      have : (j : ℕ) = (i : ℕ) := by rw [← hi]; simp
      rw [this]; exact i.2
  rw [h]
  simp

variable (d) (G : SimpleGraph V)

/-- The non-desert neighbours of a vertex. -/
noncomputable def coreNeighbors (a : V) : Finset V := by
  classical exact univ.filter (fun c => nonDesert d G a c)

/-- The canonical choice of incoming edges: the edge `{a,b}` is incoming at `a` when `b`
is one of the `d` smallest non-desert neighbours of `a`. -/
def stdInto (a b : V) : Prop :=
  nonDesert d G a b ∧ #((coreNeighbors d G a).filter (fun c => c < b)) < d

/-- The set of neighbours joined to `a` by an edge incoming at `a`, for the canonical
choice. -/
noncomputable def stdIncoming (a : V) : Finset V := by
  classical exact univ.filter (fun c => stdInto d G a c)

variable {d G}

omit [DecidableEq V] [LinearOrder V] in
theorem card_coreNeighbors {a b : V} (h : nonDesert d G a b) :
    d + 1 ≤ #(coreNeighbors d G a) :=
  (isDeep_nonDesert d G).2.2 a b h

/-- The canonical choice makes exactly `d` edges incoming at every vertex of the
non-desert graph. -/
theorem card_stdIncoming {a b : V} (h : nonDesert d G a b) : #(stdIncoming d G a) = d := by
  classical
  have hsub : stdIncoming d G a
      = (coreNeighbors d G a).filter
          (fun b => #((coreNeighbors d G a).filter (fun c => c < b)) < d) := by
    ext x
    simp only [stdIncoming, coreNeighbors, mem_filter, mem_univ, true_and, stdInto]
  rw [hsub]
  exact card_filter_rank_lt _ d (le_trans (Nat.le_succ d) (card_coreNeighbors h))

omit [DecidableEq V] in
/-- The chosen incoming neighbours are exactly the smallest ones: any chosen neighbour is
smaller than any non-chosen non-desert neighbour. -/
theorem stdInto_lt_of_not_stdInto {a y b : V} (hy : stdInto d G a y)
    (hb : nonDesert d G a b) (hnb : ¬ stdInto d G a b) : y < b := by
  classical
  by_contra hcon
  push_neg at hcon
  have hmono : (coreNeighbors d G a).filter (fun c => c < b)
      ⊆ (coreNeighbors d G a).filter (fun c => c < y) := by
    intro c hc
    simp only [mem_filter] at hc ⊢
    exact ⟨hc.1, lt_of_lt_of_le hc.2 hcon⟩
  have h1 : d ≤ #((coreNeighbors d G a).filter (fun c => c < b)) := by
    by_contra hlt
    push_neg at hlt
    exact hnb ⟨hb, hlt⟩
  have h2 := Finset.card_le_card hmono
  exact absurd hy.2 (not_lt.mpr (le_trans h1 h2))

/-- The largest chosen incoming neighbour of `a` (or `a` itself if there is none). -/
noncomputable def gOf (a : V) : V :=
  if h : (stdIncoming d G a).Nonempty then (stdIncoming d G a).max' h else a

/-- **Every graph carries a `d`-orientation.** This is the construction of the source
article (`main.tex`, Subsection "Main Results"): `d` incoming edges are chosen at every
vertex of the non-desert graph, and the stream digraph is acyclic. -/
theorem exists_dOrientation (d : ℕ) (G : SimpleGraph V) : Nonempty (DOrientation d G) := by
  classical
  refine ⟨{ into := stdInto d G
            into_nonDesert := fun a b h => h.1
            card_into := ?_
            rank := fun a => posOf (gOf (d := d) (G := G) a) + posOf a
            rank_lt := ?_ }⟩
  · intro a b h
    have := card_stdIncoming (d := d) (G := G) h
    simpa [stdIncoming] using this
  · intro a b hab hba hnab
    -- `a` is a chosen incoming neighbour of `b`, so `a ≤ g(b)`
    have hbne : (stdIncoming d G b).Nonempty := ⟨a, by simpa [stdIncoming] using hba⟩
    have hale : a ≤ gOf (d := d) (G := G) b := by
      rw [gOf, dif_pos hbne]
      exact Finset.le_max' _ a (by simpa [stdIncoming] using hba)
    -- `g(a)` is a chosen incoming neighbour of `a`, hence smaller than `b`
    have hd1 : 1 ≤ d := by
      have hcard := card_stdIncoming (d := d) (G := G) (a := b) (b := a) hba.1
      have : 0 < #(stdIncoming d G b) := Finset.card_pos.mpr hbne
      omega
    have hane : (stdIncoming d G a).Nonempty := by
      rw [← Finset.card_pos, card_stdIncoming (d := d) (G := G) hab]
      omega
    have hga : stdInto d G a (gOf (d := d) (G := G) a) := by
      have hmem : gOf (d := d) (G := G) a ∈ stdIncoming d G a := by
        rw [gOf, dif_pos hane]
        exact Finset.max'_mem _ _
      simpa [stdIncoming] using hmem
    have hlt : gOf (d := d) (G := G) a < b := stdInto_lt_of_not_stdInto hga hab hnab
    have h1 : posOf (gOf (d := d) (G := G) a) < posOf b := posOf_lt_posOf hlt
    have h2 : posOf a ≤ posOf (gOf (d := d) (G := G) b) := posOf_le_posOf hale
    omega

/-! ### Existence of sinks -/

namespace DOrientation

variable {G : SimpleGraph V} (Γ : DOrientation d G)

omit [DecidableEq V] [LinearOrder V] in
/-- **Whenever there are non-desert edges, there is at least one sink** (`main.tex`,
Section "Proofs": *"Hence, whenever there are non-desert edges, there is at least one
sink"*). The proof follows the same idea as the acyclicity of the line graph: a vertex of
maximal rank incident to a non-desert edge must be an endpoint of a sink. -/
theorem exists_isSink_of_hasNonDesertEdge (h : HasNonDesertEdge (d := d) (G := G)) :
    ∃ i j : V, Γ.IsSink i j := by
  classical
  obtain ⟨i0, j0, hij0⟩ := h
  set S : Finset V := univ.filter (fun a => ∃ b, nonDesert d G a b) with hS
  have hi0 : i0 ∈ S := by simp only [hS, mem_filter, mem_univ, true_and]; exact ⟨j0, hij0⟩
  obtain ⟨a, haS, hmax⟩ := S.exists_max_image Γ.rank ⟨i0, hi0⟩
  simp only [hS, mem_filter, mem_univ, true_and] at haS
  obtain ⟨b, hab⟩ := haS
  -- `a` has more than `d` non-desert neighbours, but only `d` incoming edges
  have hsub : (univ.filter (fun c => Γ.into a c)) ⊆ (univ.filter (fun c => nonDesert d G a c)) := by
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    exact Γ.into_nonDesert a c hc
  have hcard1 : #(univ.filter (fun c => Γ.into a c)) = d := Γ.card_into a b hab
  have hcard2 : d + 1 ≤ #(univ.filter (fun c => nonDesert d G a c)) :=
    (isDeep_nonDesert d G).2.2 a b hab
  have hssub : (univ.filter (fun c => Γ.into a c)) ⊂ (univ.filter (fun c => nonDesert d G a c)) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
      intro hEq
      rw [hEq] at hcard1
      omega⟩
  obtain ⟨c, hcmem, hcnot⟩ := Finset.exists_of_ssubset hssub
  simp only [mem_filter, mem_univ, true_and] at hcmem hcnot
  by_cases hca : Γ.into c a
  · -- the edge `{a,c}` is a stream from `a` to `c`, so `c` has larger rank: impossible
    exfalso
    have hlt : Γ.rank a < Γ.rank c := Γ.rank_lt a c hcmem hca hcnot
    have hcS : c ∈ S := by
      simp only [hS, mem_filter, mem_univ, true_and]
      exact ⟨a, (isDeep_nonDesert d G).1 a c hcmem⟩
    exact absurd (hmax c hcS) (not_le.mpr hlt)
  · exact ⟨a, c, hcmem, hcnot, hca⟩

end DOrientation

end RigidityTableaux
