/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Junction

/-!
# Phonological transformations as correspondence-graph relations

[jardine-2016-diss] (Ch. 7) models a phonological *process* not as a function but as a
**relation** between input and output, presented by a set of **correspondence graphs**
and carved out of GEN by **banned-subgraph constraints** (markedness + faithfulness) —
which is what makes the relation *local*.

A string correspondence graph is exactly a bipartite `Graph S T` reinterpreted: the
upper tier is the input string, the lower tier the output string, and the association
links are the input↔output **correspondence arcs**. (Precedence is carried by the tier
order; Jardine's separate precedence/correspondence arc-labeling `ℓ_A` is here the
structural split between tier-order and links.) The banned-subgraph grammar is
`Graph.Free` ([jardine-2016-diss] Ch. 5's `L^NL_G`).

This is the *process* layer of the substrate's three-layer spec (objects `AR`,
precedence-morphisms `PrecAR`, processes here). The autosegmental case — correspondence
between multi-tier APGs — extends it over `MultiGraph`.

## Scope note

`SubgraphEmbeds` matches contiguous blocks of *both* tiers plus links, so it expresses
**correspondence** (input↔output) banned subgraphs directly. Jardine's *output-only*
markedness constraints (e.g. forbid an output `apa` regardless of input) need the
arc-labelled-subgraph refinement he flags in Ch. 7 fn. 7; that is deferred.

## Main definitions

* `Correspondence.input`/`output` — the two strings a correspondence graph relates.
* `Correspondence.rel` — `R(CG)`, the string relation of a set of correspondence graphs
  ([jardine-2016-diss] Def. 25).
* `Correspondence.specifiedBy` — `CG(φ)`, a process presented by a banned-subgraph grammar.
* `Correspondence.IsLocal` — a relation presented by a finite banned-subgraph grammar.
-/

namespace Autosegmental
namespace Correspondence

variable {S T : Type*}

/-! ### Correspondence on the graph foundation

The same layer over two-tier representations: input over `true`, output over
`false`, correspondence arcs the links, banned subgraphs `AR.Free`. -/

section Coordinate

universe u
variable {S T : Type u}

/-- A finite two-tier correspondence representation. -/
abbrev Rep (S T : Type u) :=
  {G : AR.{u, 0, u} (Sigma.fst : ((b : Bool) × TwoTier S T b) → Bool) //
    Finite G.obj.V}

/-- The **input** string: the `true`-tier word. -/
noncomputable def Rep.input (G : Rep S T) : List S :=
  haveI := G.property
  G.val.tierWord true

/-- The **output** string: the `false`-tier word. -/
noncomputable def Rep.output (G : Rep S T) : List T :=
  haveI := G.property
  G.val.tierWord false

/-- **R(CG)** ([jardine-2016-diss] Def. 25) on the foundation: the string
    relation realized by a set of correspondence representations. -/
def relRep (CG : Rep S T → Prop) (w : List S) (v : List T) : Prop :=
  ∃ G, CG G ∧ G.input = w ∧ G.output = v

/-- `R` is monotone: more correspondence graphs realize a larger relation. -/
theorem relRep_mono {CG CG' : Rep S T → Prop} (h : ∀ G, CG G → CG' G) {w v} :
    relRep CG w v → relRep CG' w v := by
  rintro ⟨G, hG, hi, ho⟩
  exact ⟨G, h G hG, hi, ho⟩

/-- A process **specified by banned subgraphs** `φ` (Jardine's `CG(φ)`): the
    representations free of every forbidden pattern. -/
def specifiedByRep (φ : List (Rep S T)) (G : Rep S T) : Prop :=
  haveI := G.property
  G.val.Free φ

/-- A string relation is **local** when presented by a finite banned-subgraph
    grammar over correspondence representations. -/
def IsLocalRep (R : List S → List T → Prop) : Prop :=
  ∃ φ : List (Rep S T), R = relRep (specifiedByRep φ)

/-- Banned-subgraph grammars **compose by union**: the `L^NL_G` conjunction of
    two local constraint sets. -/
theorem specifiedByRep_append (φ ψ : List (Rep S T)) (G : Rep S T) :
    specifiedByRep (φ ++ ψ) G ↔ specifiedByRep φ G ∧ specifiedByRep ψ G := by
  unfold specifiedByRep AR.Free
  rw [List.forall_mem_append]

/-- The empty grammar specifies all of GEN. -/
@[simp] theorem specifiedByRep_nil (G : Rep S T) : specifiedByRep [] G ↔ True := by
  unfold specifiedByRep AR.Free
  simp

end Coordinate

end Correspondence
end Autosegmental
