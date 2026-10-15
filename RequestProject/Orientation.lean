import RequestProject.Rigidity
import RequestProject.Tableaux

/-!
# `d`-orientations, the `Γ`-oriented line graph, and balancing conditions

This file formalizes the combinatorial machinery of the source article
(`main.tex`, Subsection "Main Results", Subsection "Geometric results" and
Section "Proofs"):

* the desert edges and the non-desert graph (the largest subgraph of minimum degree
  `d+1`);
* a **`d`-orientation** `Γ`: a choice of `d` incoming edges at every non-desert vertex,
  with acyclic stream digraph;
* **sources**, **streams**, **sinks** and **deserts**;
* the **`Γ`-oriented line graph** `𝓛`, its arrows, and their **up-weights** and
  **down-weights** (single-column tableaux);
* paths, **path systems**, disjoint path systems, and the **weight** `wt(𝒫)`;
* the **balancing conditions** `{{wt(𝒫)}}`, the notions of `Γ` being **balanced** and
  **balanced at `p`**, and of `G` being **`d`-balanced**;
* the statements of Theorem `thm:balanced-equivalent-to-selfstress`, Corollary
  `cor:affine-Maxwell-infinitesimally-flexible`, Theorem
  `thm:main-Maxwell-locally-flexible`, Corollary `cor:characterization`, and of the
  lemmas of Section "Proofs" of the source article.
-/

open scoped BigOperators
open Finset

namespace RigidityTableaux

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {d : ℕ}

/-! ### Deserts and the non-desert graph -/

/-- An edge relation `s` inside `G` is **`d`-deep** if it is symmetric and every vertex
incident to an `s`-edge has at least `d+1` incident `s`-edges, i.e. `s` has minimum
degree `d+1` on its support. This is the property the non-desert edges are required to
have in the source article (`main.tex`, Subsection "Main Results": *"Repeat this
process, assigning edges as deserts if they are incident to any vertex with `d` or less
non-desert edges, until any remaining non-desert edges form a graph with minimum degree
`d+1`"*). -/
def IsDeep (d : ℕ) (G : SimpleGraph V) (s : V → V → Prop) : Prop :=
  (∀ i j, s i j → s j i) ∧ (∀ i j, s i j → G.Adj i j) ∧
    ∀ i j, s i j → d + 1 ≤ #(univ.filter (fun c => s i c))

/-- The **non-desert** edges of `G`: the union of all `d`-deep edge relations, i.e. the
edges surviving the desert-removal process of the source article (`main.tex`,
Subsection "Main Results"). Its complement inside the edge set consists of the
**desert** edges. -/
def nonDesert (d : ℕ) (G : SimpleGraph V) (i j : V) : Prop :=
  ∃ s : V → V → Prop, IsDeep d G s ∧ s i j

omit [DecidableEq V] [LinearOrder V] in
/-- The non-desert edges themselves form a `d`-deep edge relation: the desert-removal
process of the source article terminates in a graph of minimum degree `d+1`. -/
theorem isDeep_nonDesert (d : ℕ) (G : SimpleGraph V) : IsDeep d G (nonDesert d G) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro i j ⟨s, hs, hij⟩
    exact ⟨s, hs, hs.1 i j hij⟩
  · rintro i j ⟨s, hs, hij⟩
    exact hs.2.1 i j hij
  · rintro i j ⟨s, hs, hij⟩
    refine le_trans (hs.2.2 i j hij) (Finset.card_le_card ?_)
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    exact ⟨s, hs, hc⟩

/-- A **desert** edge of `G`: an edge which does not survive the desert-removal process
(`main.tex`, Subsection "Main Results"). -/
def IsDesertEdge (d : ℕ) (G : SimpleGraph V) (i j : V) : Prop :=
  G.Adj i j ∧ ¬ nonDesert d G i j

/-! ### `d`-orientations -/

/-- A **`d`-orientation `Γ`** on `G` (`main.tex`, Subsection "Main Results", *"The
orientation `Γ`"*). The predicate `into a b` records that the non-desert edge `{a,b}` is
*incoming at `a`*. At every vertex of the non-desert graph exactly `d` incident edges are
chosen incoming, and the stream digraph (an arrow `a → b` for every edge incoming at `b`
and outgoing at `a`) is required to have no directed cycles; the latter is expressed by
the existence of a strictly increasing rank function, which for a finite digraph is
equivalent to acyclicity. -/
structure DOrientation (d : ℕ) (G : SimpleGraph V) where
  /-- `into a b` means that the non-desert edge `{a,b}` is oriented *into* `a`. -/
  into : V → V → Prop
  /-- Only non-desert edges are oriented. -/
  into_nonDesert : ∀ a b, into a b → nonDesert d G a b
  /-- Exactly `d` edges are incoming at each vertex of the non-desert graph. -/
  card_into : ∀ a b, nonDesert d G a b → #(univ.filter (fun c => into a c)) = d
  /-- A rank function witnessing that the stream digraph has no directed cycles. -/
  rank : V → ℕ
  /-- The rank increases along every stream arrow `a → b` (an edge incoming at `b` and
  outgoing at `a`). -/
  rank_lt : ∀ a b, nonDesert d G a b → into b a → ¬ into a b → rank a < rank b

namespace DOrientation

variable {G : SimpleGraph V} (Γ : DOrientation d G)

/-- An edge is a **source** if it is incoming at both endpoints (`main.tex`, Subsection
"Main Results": *"An edge `(i,j)` incoming at both endpoints … is a source"*). -/
def IsSource (i j : V) : Prop := nonDesert d G i j ∧ Γ.into i j ∧ Γ.into j i

/-- An edge is a **stream** if it is incoming at exactly one endpoint (`main.tex`,
Subsection "Main Results"). -/
def IsStream (i j : V) : Prop :=
  nonDesert d G i j ∧ ((Γ.into i j ∧ ¬ Γ.into j i) ∨ (¬ Γ.into i j ∧ Γ.into j i))

/-- An edge is a **sink** if it is outgoing at both endpoints (`main.tex`, Subsection
"Main Results": *"An edge outgoing at both endpoints … is a sink"*). -/
def IsSink (i j : V) : Prop := nonDesert d G i j ∧ ¬ Γ.into i j ∧ ¬ Γ.into j i

end DOrientation

/-- The nodes of the `Γ`-oriented line graph: the non-desert edges of `G`, presented as
ordered pairs `(i,j)` with `i < j` (`main.tex`, Subsection "Main Results": *"Let `𝓛` be
the directed graph whose nodes are edges of `G`"*). -/
abbrev CoreEdge (d : ℕ) (G : SimpleGraph V) : Type _ :=
  {e : V × V // e.1 < e.2 ∧ nonDesert d G e.1 e.2}

namespace DOrientation

variable {G : SimpleGraph V} (Γ : DOrientation d G)

/-- The **sources** of `Γ`, as a finite set of nodes of the line graph. -/
noncomputable def sources : Finset (CoreEdge d G) :=
  univ.filter (fun e => Γ.IsSource e.1.1 e.1.2)

/-- The **sinks** of `Γ`, as a finite set of nodes of the line graph. -/
noncomputable def sinks : Finset (CoreEdge d G) :=
  univ.filter (fun e => Γ.IsSink e.1.1 e.1.2)

/-- The shared vertex of two adjacent line graph nodes: the vertex `a` used by an arrow
`ξ → η` (`main.tex`, Subsection "Main Results": *"we say the arrow `ξ → η` uses `a`"*). -/
def sharedVertex (xi eta : CoreEdge d G) : V :=
  if xi.1.1 = eta.1.1 ∨ xi.1.1 = eta.1.2 then xi.1.1 else xi.1.2

/-- The endpoint of `ξ` other than the given vertex `a`. -/
def otherEnd (xi : CoreEdge d G) (a : V) : V := if a = xi.1.1 then xi.1.2 else xi.1.1

/-- The arrows of the **`Γ`-oriented line graph** `𝓛`: `ξ → η` whenever `ξ` is oriented
into a vertex `a` that `η` is oriented out of (`main.tex`, Subsection "Main Results":
*"whose arrows point between adjacent edges `ξ → η` whenever `ξ` is oriented into a
vertex that `η` is oriented out of"*). -/
def LArrow (xi eta : CoreEdge d G) : Prop :=
  xi ≠ eta ∧
    (let a := sharedVertex xi eta
     (a = eta.1.1 ∨ a = eta.1.2) ∧ Γ.into a (otherEnd xi a) ∧ ¬ Γ.into a (otherEnd eta a))

/-- The other vertices `j_1 < ⋯ < j_{d-1}` with edges oriented into `a`, besides `b`
(`main.tex`, Subsection "Main Results"). -/
noncomputable def incomingOthers (a b : V) : Finset V :=
  (univ.filter (fun c => Γ.into a c)).erase b

/-- The list `j_1 < ⋯ < j_{d-1}` of the other vertices with edges oriented into `a`. -/
noncomputable def incomingOthersList (a b : V) : List V :=
  (Γ.incomingOthers a b).sort (· ≤ ·)

/-- The column `[j_1 j_2 … j_{d-1} x y]` of height `d+1` built from the other incoming
neighbours of `a` besides `b`, followed by two further entries; this is the shape of both
the up-weights and the down-weights of the source article (`main.tex`, Subsection
"Main Results"). -/
noncomputable def weightColumn (a b x y : V) : Column (d + 1) V := fun i =>
  if (i : ℕ) + 2 ≤ d then (Γ.incomingOthersList a b).getD i a
  else if (i : ℕ) + 1 = d then x else y

/-- The **up-weight** `𝔲_𝔞 = [j_1 … j_{d-1} a c]` of an arrow `𝔞 : ξ → η` using the vertex
`a`, with a minus sign (blue colour) when `𝔞` leaves a source from its negative endpoint,
that is, from the larger of the two endpoints (`main.tex`, Subsection "Main Results"). -/
noncomputable def arrowUp (xi eta : CoreEdge d G) : Tableau (d + 1) V :=
  let a := sharedVertex xi eta
  let b := otherEnd xi a
  let c := otherEnd eta a
  { red := ¬ (Γ.IsSource xi.1.1 xi.1.2 ∧ a = xi.1.2)
    cols := {Γ.weightColumn a b a c} }

/-- The **down-weight** `𝔡_𝔞 = [j_1 … j_{d-1} b a]` of an arrow `𝔞 : ξ → η` using the
vertex `a` (`main.tex`, Subsection "Main Results"). -/
noncomputable def arrowDown (xi eta : CoreEdge d G) : Tableau (d + 1) V :=
  let a := sharedVertex xi eta
  let b := otherEnd xi a
  { red := true
    cols := {Γ.weightColumn a b b a} }

end DOrientation

/-! ### Products of tableaux -/

/-- The product of two tableaux: colours multiply (red is `+`, blue is `−`) and the
columns are concatenated (`main.tex`, Subsection "Main Results": *"with commutative
product the concatenation of columns"*). -/
def Tableau.mul {n : ℕ} (T T' : Tableau n V) : Tableau n V :=
  { red := (T.red = T'.red), cols := T.cols + T'.cols }

/-- The empty product of tableaux: the red tableau with no columns, i.e. `+1`. -/
def Tableau.one (n : ℕ) (V : Type*) : Tableau n V := { red := true, cols := 0 }

/-- The product of a list of tableaux. -/
def Tableau.listProd {n : ℕ} (L : List (Tableau n V)) : Tableau n V :=
  L.foldr Tableau.mul (Tableau.one n V)

/-- Flipping the colour of a tableau, i.e. multiplying it by `-1`. -/
def Tableau.neg {n : ℕ} (T : Tableau n V) : Tableau n V := { T with red := !T.red }

/-- Multiplying a tableau by a sign. -/
def Tableau.smulSign {n : ℕ} (s : ℤˣ) (T : Tableau n V) : Tableau n V :=
  if s = 1 then T else Tableau.neg T

namespace DOrientation

variable {G : SimpleGraph V} (Γ : DOrientation d G)

/-! ### Paths and path systems in the line graph -/

/-- A list of nodes of the line graph is a **path** from `μ` to `ν` when it starts at `μ`,
ends at `ν`, and consecutive nodes are joined by arrows of `𝓛` (`main.tex`, Subsection
"Main Results"). -/
def IsLPath (mu nu : CoreEdge d G) (l : List (CoreEdge d G)) : Prop :=
  l.head? = some mu ∧ l.getLast? = some nu ∧ l.IsChain (fun x y => Γ.LArrow x y)

/-- The **up-weight of a path**: the product of the up-weights of its arrows
(`main.tex`, Subsection "Main Results": *"The up-weight of a path in `𝓛` is the product
of the up-weights of its arrows"*). -/
noncomputable def pathUp (l : List (CoreEdge d G)) : Tableau (d + 1) V :=
  Tableau.listProd ((l.zip l.tail).map (fun x => Γ.arrowUp x.1 x.2))

/-- The **down-weight of a path**: the product of the down-weights of its arrows. -/
noncomputable def pathDown (l : List (CoreEdge d G)) : Tableau (d + 1) V :=
  Tableau.listProd ((l.zip l.tail).map (fun x => Γ.arrowDown x.1 x.2))

/-- The data of a candidate path system: a permutation together with a family of
duplicate-free lists of nodes (`main.tex`, Subsection "Main Results": *"a path system
`𝒫 = (π, 𝒫_1, …, 𝒫_ℓ)` is a permutation `π ∈ S_ℓ` and paths from the sources to the
permuted sinks"*). -/
abbrev PathSystemData (d : ℕ) (G : SimpleGraph V) (l : ℕ) : Type _ :=
  Equiv.Perm (Fin l) × (Fin l → {L : List (CoreEdge d G) // L.Nodup})

/-- A candidate is a **disjoint path system** from the sources `μ` to the sinks `ν` when
each `𝒫_j` is a path from `μ_j` to `ν_{π j}` and no two of the paths share a node
(`main.tex`, Subsection "Main Results": *"A path system is disjoint if none of the paths
share a node"*). -/
def IsDisjointPathSystem {l : ℕ} (mu nu : Fin l → CoreEdge d G)
    (P : PathSystemData d G l) : Prop :=
  (∀ j, Γ.IsLPath (mu j) (nu (P.1 j)) (P.2 j).1) ∧
    ∀ j j', j ≠ j' → ∀ x ∈ (P.2 j).1, x ∉ (P.2 j').1

/-- The finite set `𝒟` of all disjoint path systems joining the chosen sources to the
sinks. -/
noncomputable def disjointSystems {l : ℕ} (mu nu : Fin l → CoreEdge d G) :
    Finset (PathSystemData d G l) :=
  univ.filter (fun P => Γ.IsDisjointPathSystem mu nu P)

/-- The **up-weight of a path system**: the product of the up-weights of its paths. -/
noncomputable def systemUp {l : ℕ} (P : PathSystemData d G l) : Tableau (d + 1) V :=
  Tableau.listProd ((List.finRange l).map (fun j => Γ.pathUp (P.2 j).1))

/-- The **down-weight of a path system**: the product of the down-weights of its paths. -/
noncomputable def systemDown {l : ℕ} (P : PathSystemData d G l) : Tableau (d + 1) V :=
  Tableau.listProd ((List.finRange l).map (fun j => Γ.pathDown (P.2 j).1))

/-- The **weight `wt(𝒫)` of a disjoint path system**: the sign of its permutation times
its up-weight times the down-weights of *all other* disjoint path systems joining the
same sources to the sinks (`main.tex`, Subsection "Main Results": *"The weight `wt(𝒫)` of
a path system is the product of its up-weight with the down-weights of all other disjoint
path systems connecting the chosen sources to the `ℓ` sinks, times the sign of its
permutation"*). -/
noncomputable def systemWeight {l : ℕ} (mu nu : Fin l → CoreEdge d G)
    (P : PathSystemData d G l) : Tableau (d + 1) V :=
  Tableau.smulSign (Equiv.Perm.sign P.1)
    (Tableau.mul (Γ.systemUp P)
      (Tableau.listProd
        (((Γ.disjointSystems mu nu).erase P).val.toList.map (fun Q => Γ.systemDown Q))))

/-- The **balancing condition** `{{wt(𝒫)}}` associated with a choice of sources: the
multiset with one element `wt(𝒫)` for each disjoint path system `𝒫` joining the chosen
sources `μ_1, …, μ_ℓ` to the sinks `ν_1, …, ν_ℓ` (`main.tex`, Subsection "Main Results",
equation `eqn:LGV-balancing-condition`). -/
noncomputable def balancingCondition {l : ℕ} (mu nu : Fin l → CoreEdge d G) :
    Multiset (Tableau (d + 1) V) :=
  (Γ.disjointSystems mu nu).val.map (fun P => Γ.systemWeight mu nu P)

/-- The enumeration `ν_1, …, ν_ℓ` of the sinks of `Γ` used to form balancing conditions. -/
noncomputable def sinkEnum : Fin (#Γ.sinks) → CoreEdge d G := fun j =>
  ((Γ.sinks.equivFin).symm j : CoreEdge d G)

/-- A family `μ_1, …, μ_ℓ` of `ℓ = |sinks|` distinct sources of `Γ`. -/
def IsSourceChoice (mu : Fin (#Γ.sinks) → CoreEdge d G) : Prop :=
  Function.Injective mu ∧ ∀ j, mu j ∈ Γ.sources

/-- There is at least one non-desert edge, i.e. `Γ` is not the all-desert orientation
(`main.tex`, Subsection "Main Results": *"An all-desert orientation is not balanced"*). -/
def HasNonDesertEdge : Prop := ∃ i j : V, nonDesert d G i j

/-- `Γ` is **balanced** (`main.tex`, Subsection "Main Results"): there are non-desert
edges, and either there are more sinks than sources, or `|sources| ≥ |sinks| = ℓ` and for
every choice of `ℓ` sources the balancing condition reduces, by exchange rules, to a
multiset of semistandard tableaux containing each semistandard tableau in equal amounts
red and blue. -/
def Balanced : Prop :=
  HasNonDesertEdge (d := d) (G := G) ∧
    ((#Γ.sources < #Γ.sinks) ∨
      (#Γ.sinks ≤ #Γ.sources ∧
        ∀ mu : Fin (#Γ.sinks) → CoreEdge d G, Γ.IsSourceChoice mu →
          ∃ m' : Multiset (Tableau (d + 1) V),
            ReducesTo (Γ.balancingCondition mu Γ.sinkEnum) m' ∧
              (∀ T ∈ m', IsSemistandard T) ∧ RedBlueBalanced m'))

end DOrientation

/-- The matrix `M` whose `i`-th column is `(p_i, 1)`, used to evaluate tableaux at a
placement (`main.tex`, Subsection "Geometric results" and Subsection "From geometric to
combinatorial balancing"). -/
def placementMatrix (p : V → Fin d → ℝ) : Fin (d + 1) → V → ℝ :=
  fun i v => if h : (i : ℕ) < d then p v ⟨i, h⟩ else 1

/-- The evaluation `∑ wt(𝒫)|_p` of a bracket polynomial at a placement `p`, obtained by
replacing each column by the corresponding maximal minor of `M` (`main.tex`, Subsection
"Geometric results"). -/
noncomputable def evalAtPlacement (p : V → Fin d → ℝ)
    (m : Multiset (Tableau (d + 1) V)) : ℝ :=
  multisetEval (placementMatrix p) m

namespace DOrientation

variable {G : SimpleGraph V} (Γ : DOrientation d G)

/-- `Γ` is **balanced at `p`** (`main.tex`, Subsection "Geometric results"): there are
non-desert edges, and either there are more sinks than sources, or `|sources| ≥ |sinks|`
and every balancing condition evaluates to zero at `p`. -/
def BalancedAt (p : V → Fin d → ℝ) : Prop :=
  HasNonDesertEdge (d := d) (G := G) ∧
    ((#Γ.sources < #Γ.sinks) ∨
      (#Γ.sinks ≤ #Γ.sources ∧
        ∀ mu : Fin (#Γ.sinks) → CoreEdge d G, Γ.IsSourceChoice mu →
          evalAtPlacement p (Γ.balancingCondition mu Γ.sinkEnum) = 0))

end DOrientation

/-- The graph `G` is **balanced at `p`** when one (equivalently, by Lemma
`lemma:Gamma-equivalent-to-Gamma'`, every) `d`-orientation `Γ` is balanced at `p`
(`main.tex`, Subsection "Geometric results"). -/
def BalancedAtPlacement (d : ℕ) (G : SimpleGraph V) (p : V → Fin d → ℝ) : Prop :=
  ∃ Γ : DOrientation d G, Γ.BalancedAt p

/-- The graph `G` is **`d`-balanced** when one (equivalently, by Lemma
`lemma:generic-orientation-independent`, every) `d`-orientation `Γ` is balanced
(`main.tex`, Subsection "Main Results"). -/
def IsDBalanced (d : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ Γ : DOrientation d G, Γ.Balanced

end RigidityTableaux
