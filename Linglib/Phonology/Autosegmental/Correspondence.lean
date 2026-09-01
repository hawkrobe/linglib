/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Junction

/-!
# Phonological transformations as correspondence-graph relations

[jardine-2016b] (Ch. 7) models a phonological *process* not as a function but as a
**relation** between input and output, presented by a set of **correspondence graphs**
and carved out of GEN by **banned-subgraph constraints** (markedness + faithfulness) —
which is what makes the relation *local*.

A string correspondence graph is exactly a bipartite `Graph S T` reinterpreted: the
upper tier is the input string, the lower tier the output string, and the association
links are the input↔output **correspondence arcs**. (Precedence is carried by the tier
order; Jardine's separate precedence/correspondence arc-labeling `ℓ_A` is here the
structural split between tier-order and links.) The banned-subgraph grammar is
`Graph.Free` ([jardine-2016b] Ch. 5's `L^NL_G`).

This is the *process* layer of the substrate's three-layer spec (objects `AR`,
precedence-morphisms `PrecAR`, processes here). The autosegmental case — correspondence
between multi-tier APGs — extends it over `MultiGraph`.

A banned subgraph is a factor (`AR.FactorEmbeds`): contiguous windows of both tiers plus
links. Jardine's arc-label distinction (Ch. 7 fn. 7) is the tier/link split itself, so
his constraint types are all factors — a correspondence constraint carries links, an
*output-only* markedness constraint (forbid a surface `apa` whatever the input) is a factor
with an empty input tier and no links.

## Main definitions

* `Rep`, `Rep.input`/`Rep.output` — a finite correspondence representation and the two
  strings it relates.
* `relRep` — `R(CG)`, the string relation of a set of correspondence graphs
  ([jardine-2016b] Def. 25).
* `specifiedByRep` — `CG(φ)`, a process presented by a banned-subgraph grammar;
  `IsLocalRep`, a relation presented by a finite one.
* `Rep.ofWords` — the correspondence graph of an input word, an output word and a
  correspondence relation on their positions; banned-subgraph tests between such graphs
  decide.
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

/-- A finite two-tier correspondence representation: input over `true`, output over
`false`, on a vertex type in `Type` — where `AR.ofData` builds. -/
abbrev Rep (S T : Type u) :=
  {G : AR.{u, 0, 0} (Sigma.fst : ((b : Bool) × TwoTier S T b) → Bool) // Finite G.obj.V}

/-- The **input** string: the `true`-tier word. -/
noncomputable def Rep.input (G : Rep S T) : List S :=
  haveI := G.property
  G.val.tierWord true

/-- The **output** string: the `false`-tier word. -/
noncomputable def Rep.output (G : Rep S T) : List T :=
  haveI := G.property
  G.val.tierWord false

/-- **R(CG)** ([jardine-2016b] Def. 25) on the foundation: the string
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

instance (G : Rep S T) : Finite G.val.obj.V := G.property

/-- A grammar tests its banned subgraphs one by one. -/
theorem specifiedByRep_cons (F : Rep S T) (φ : List (Rep S T)) (G : Rep S T) :
    specifiedByRep (F :: φ) G ↔ ¬ F.val.FactorEmbeds G.val ∧ specifiedByRep φ G := by
  unfold specifiedByRep AR.Free
  exact List.forall_mem_cons

/-! ### Correspondence graphs from words

The graph of an input word, an output word, and a correspondence relation on their
positions. Banned-subgraph tests between such graphs are computed on the words
(`AR.factorEmbeds_ofData_iff`), so grammars over concrete strings decide. -/

/-- The tier words of an input word and an output word: input over `true`, output over
`false`. -/
def words (w : List S) (v : List T) : ∀ b : Bool, List (TwoTier S T b)
  | true => (w : List (TwoTier S T true))
  | false => (v : List (TwoTier S T false))

/-- Correspondence arcs from the input tier to the output tier, under a correspondence
relation on positions. -/
def links (C : ℕ → ℕ → Prop) (i j : Bool) (p q : ℕ) : Prop := i = true ∧ j = false ∧ C p q

instance (C : ℕ → ℕ → Prop) [DecidableRel C] (i j : Bool) (p q : ℕ) :
    Decidable (links C i j p q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The correspondence graph of the input word `w` and the output word `v` under the
correspondence relation `C` on their positions. -/
def Rep.ofWords (w : List S) (v : List T) (C : ℕ → ℕ → Prop) : Rep S T :=
  ⟨AR.ofData (words w v) (links C), inferInstance⟩

@[simp] theorem Rep.input_ofWords (w : List S) (v : List T) (C : ℕ → ℕ → Prop) :
    (Rep.ofWords w v C).input = w :=
  AR.tierWord_ofData true

@[simp] theorem Rep.output_ofWords (w : List S) (v : List T) (C : ℕ → ℕ → Prop) :
    (Rep.ofWords w v C).output = v :=
  AR.tierWord_ofData false

/-- Embedding between graphs of words is the data-level check, hence decidable. -/
instance [DecidableEq S] [DecidableEq T] (w w' : List S) (v v' : List T)
    (C C' : ℕ → ℕ → Prop) [DecidableRel C] [DecidableRel C'] :
    Decidable ((Rep.ofWords w v C).val.FactorEmbeds (Rep.ofWords w' v' C').val) :=
  decidable_of_iff (dataEmbeds (words w v) (words w' v') (links C) (links C'))
    (AR.factorEmbeds_ofData_iff (wsF := words w v) (wsX := words w' v') (LF := links C)
      (LX := links C')).symm

end Coordinate

end Correspondence
end Autosegmental
