/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Embedding

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

/-- The **input** string of a correspondence graph: its upper tier. -/
def input (G : Graph S T) : List S := G.upper.toList

/-- The **output** string of a correspondence graph: its lower tier. -/
def output (G : Graph S T) : List T := G.lower.toList

/-- **R(CG)** ([jardine-2016-diss] Def. 25): the string relation realized by a set `CG` of
    correspondence graphs — the input/output pairs of its members. -/
def rel (CG : Graph S T → Prop) (w : List S) (v : List T) : Prop :=
  ∃ G, CG G ∧ input G = w ∧ output G = v

/-- `R` is monotone: more correspondence graphs realize a larger relation. -/
theorem rel_mono {CG CG' : Graph S T → Prop} (h : ∀ G, CG G → CG' G) {w v} :
    rel CG w v → rel CG' w v := by
  rintro ⟨G, hG, hi, ho⟩; exact ⟨G, h G hG, hi, ho⟩

/-- A process **specified by banned subgraphs** `φ`: the correspondence graphs free of
    every forbidden pattern (Jardine's `CG(φ)`; reuses `Graph.Free`, the `L^NL_G`
    banned-subgraph grammar — markedness and faithfulness as forbidden correspondence
    substructures). -/
def specifiedBy (φ : List (Graph S T)) (G : Graph S T) : Prop := G.Free φ

instance [DecidableEq S] [DecidableEq T] (φ : List (Graph S T)) (G : Graph S T) :
    Decidable (specifiedBy φ G) := inferInstanceAs (Decidable (G.Free φ))

/-- A string relation is **local** when presented by a finite banned-subgraph grammar
    over correspondence graphs — the locality of phonological processes [jardine-2016-diss]. -/
def IsLocal (R : List S → List T → Prop) : Prop :=
  ∃ φ : List (Graph S T), R = rel (specifiedBy φ)

/-- Banned-subgraph grammars **compose by union**: `CG(φ ++ ψ) = CG(φ) ∩ CG(ψ)` — the
    `L^NL_G` conjunction of two local constraint sets. -/
theorem specifiedBy_append (φ ψ : List (Graph S T)) (G : Graph S T) :
    specifiedBy (φ ++ ψ) G ↔ specifiedBy φ G ∧ specifiedBy ψ G := by
  simp only [specifiedBy, Graph.Free, List.forall_mem_append]

/-- The empty grammar specifies all of GEN. -/
@[simp] theorem specifiedBy_nil (G : Graph S T) : specifiedBy [] G ↔ True := by
  simp [specifiedBy, Graph.Free]

end Correspondence
end Autosegmental
