import RequestProject.LGVInvolution

/-!
# The Lindström–Gessel–Viennot lemma for the `Γ`-oriented line graph

This file proves the combinatorial identity quoted in the proof of Lemma
`lemma:balanced-equivalent-nonzero-solution` of the source article (`main.tex`, Section
"Proofs"):

> Let `𝒟` be the set of disjoint path systems for `μ_1, …, μ_ℓ`. By the
> Lindström–Gessel–Viennot lemma, `det Q_{ij}` is equal to `∑_{𝒫 ∈ 𝒟} frac(𝒫)|_p`, where
> `frac(𝒫)|_p` is the sign of the permutation times the product of
> `𝔲_𝔞|_p / 𝔡_𝔞|_p` over all arrows in all paths in the path system `𝒫`.

Here `Q_{ij}` is the matrix `pathSum` of sums over all paths of the line graph from `μ_i`
to `ν_j`.

The proof has two halves. Expanding the determinant and each of its entries writes it as
the signed sum of `frac(𝒫)|_p` over *all* path systems, disjoint or not; and the
non-disjoint ones cancel in pairs under the sign-reversing involution constructed in
`RequestProject.LGVInvolution`.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace DOrientation

variable (Γ : DOrientation d G)

/-- The sum `Q_{ξν}` of the source article, read as a sum over duplicate-free lists of
nodes rather than over the finite set `pathsFrom`. -/
theorem sum_nodup_filter_eq_pathSum (p : V → Fin d → ℝ) (xi nu : CoreEdge d G) :
    ∑ L ∈ univ.filter (fun L : {L : List (CoreEdge d G) // L.Nodup} => Γ.IsLPath xi nu L.1),
      Γ.pathFracEval p L.1 = Γ.pathSum p xi nu := by
  rw [pathSum]
  have himg : Γ.pathsFrom xi nu = Finset.image Subtype.val
      (univ.filter (fun L : {L : List (CoreEdge d G) // L.Nodup} => Γ.IsLPath xi nu L.1)) := by
    ext L
    simp only [Γ.mem_pathsFrom, Finset.mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hnd, hp⟩
      exact ⟨⟨L, hnd⟩, hp, rfl⟩
    · rintro ⟨M, hp, rfl⟩
      exact ⟨M.2, hp⟩
  rw [himg, Finset.sum_image (fun x _ y _ h => Subtype.ext h)]

/-- **Expanding the determinant of the matrix of path sums.** Each term of the Leibniz
expansion is, after expanding the entries themselves, the signed sum of `frac(𝒫)|_p` over
all path systems — disjoint or not — realising the corresponding permutation. -/
theorem det_pathSum_eq_sum_allSystems (p : V → Fin d → ℝ) {l : ℕ}
    (mu nu : Fin l → CoreEdge d G) :
    (Matrix.of fun i j => Γ.pathSum p (mu i) (nu j)).det
      = ∑ P ∈ Γ.allSystems mu nu,
          ((Equiv.Perm.sign P.1 : ℤ) : ℝ) * Γ.systemFracEval p P := by
  have hdet : (Matrix.of fun i j => Γ.pathSum p (mu i) (nu j)).det
      = ∑ σ : Equiv.Perm (Fin l),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, Γ.pathSum p (mu j) (nu (σ j)) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    exact Finset.sum_congr rfl (fun sigma _ => rfl)
  have hpi : ∀ σ : Equiv.Perm (Fin l),
      ∑ Q : Fin l → {L : List (CoreEdge d G) // L.Nodup},
        (if (∀ j, Γ.IsLPath (mu j) (nu (σ j)) (Q j).1) then
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, Γ.pathFracEval p (Q j).1 else 0)
        = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, Γ.pathSum p (mu j) (nu (σ j)) := by
    intro sigma
    rw [← Finset.sum_filter]
    have hfilter : (univ.filter (fun Q : Fin l → {L : List (CoreEdge d G) // L.Nodup} =>
        ∀ j, Γ.IsLPath (mu j) (nu (sigma j)) (Q j).1))
        = Fintype.piFinset (fun j => univ.filter
            (fun L : {L : List (CoreEdge d G) // L.Nodup} =>
              Γ.IsLPath (mu j) (nu (sigma j)) L.1)) := by
      ext Q
      simp [Fintype.mem_piFinset]
    have hps : ∏ j, Γ.pathSum p (mu j) (nu (sigma j))
        = ∏ j, ∑ L ∈ univ.filter (fun L : {L : List (CoreEdge d G) // L.Nodup} =>
            Γ.IsLPath (mu j) (nu (sigma j)) L.1), Γ.pathFracEval p L.1 := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Γ.sum_nodup_filter_eq_pathSum]
    rw [hfilter, ← Finset.mul_sum, hps,
      Finset.prod_univ_sum (fun j => univ.filter
        (fun L : {L : List (CoreEdge d G) // L.Nodup} => Γ.IsLPath (mu j) (nu (sigma j)) L.1))
        (fun j L => Γ.pathFracEval p L.1)]
  rw [hdet, allSystems, Finset.sum_filter, Fintype.sum_prod_type]
  exact (Finset.sum_congr rfl (fun sigma _ => hpi sigma)).symm

/-- **The Lindström–Gessel–Viennot lemma** in the form used by the source article
(`main.tex`, Section "Proofs", proof of Lemma
`lemma:balanced-equivalent-nonzero-solution`): the determinant of the matrix of path sums
from the chosen sources to the sinks is the signed sum of `frac(𝒫)|_p` over the disjoint
path systems joining them. -/
theorem det_pathSum_eq_sum_disjointSystems (p : V → Fin d → ℝ) {l : ℕ}
    (mu nu : Fin l → CoreEdge d G) :
    (Matrix.of fun i j => Γ.pathSum p (mu i) (nu j)).det
      = ∑ P ∈ Γ.disjointSystems mu nu,
          ((Equiv.Perm.sign P.1 : ℤ) : ℝ) * Γ.systemFracEval p P := by
  rw [Γ.det_pathSum_eq_sum_allSystems p mu nu,
    ← Finset.sum_sdiff (Γ.disjointSystems_subset_allSystems (mu := mu) (nu := nu)),
    Γ.sum_sdiff_eq_zero p mu nu, zero_add]

end DOrientation

end RigidityTableaux
