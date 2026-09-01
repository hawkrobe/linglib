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
* `Strings` — a correspondence graph given by its data (input word, output word,
  correspondence relation), whose banned-subgraph test `Strings.SpecifiedBy` decides.
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

/-! ### Correspondence graphs from data

A correspondence graph presented by its data — the two strings and the correspondence
relation on their positions. Its banned-subgraph test is computed on the data
(`AR.factorEmbeds_ofData_iff`), so grammars over concrete strings decide. -/

/-- A string correspondence: an input word, an output word, and the correspondence
relation between their positions. -/
structure Strings (S T : Type u) where
  /-- The input string. -/
  input : List S
  /-- The output string. -/
  output : List T
  /-- Input position `p` corresponds to output position `q`. -/
  Corr : ℕ → ℕ → Prop
  [decCorr : DecidableRel Corr]

namespace Strings

attribute [instance] decCorr

/-- The tier words: input over `true`, output over `false`. -/
def words (D : Strings S T) : ∀ b : Bool, List (TwoTier S T b)
  | true => (D.input : List (TwoTier S T true))
  | false => (D.output : List (TwoTier S T false))

/-- The links: correspondence arcs from the input tier to the output tier. -/
def links (D : Strings S T) (i j : Bool) (p q : ℕ) : Prop := i = true ∧ j = false ∧ D.Corr p q

instance (D : Strings S T) (i j : Bool) (p q : ℕ) : Decidable (D.links i j p q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The correspondence representation presented by the data. -/
def toRep (D : Strings S T) : Rep S T := ⟨AR.ofData D.words D.links, inferInstance⟩

@[simp] theorem input_toRep (D : Strings S T) : D.toRep.input = D.input :=
  AR.tierWord_ofData true

@[simp] theorem output_toRep (D : Strings S T) : D.toRep.output = D.output :=
  AR.tierWord_ofData false

/-- `F` occurs in `G`, computed on the data. -/
def Embeds (F G : Strings S T) : Prop := dataEmbeds F.words G.words F.links G.links

instance [DecidableEq S] [DecidableEq T] (F G : Strings S T) : Decidable (F.Embeds G) :=
  inferInstanceAs (Decidable (dataEmbeds _ _ _ _))

theorem factorEmbeds_toRep_iff (F G : Strings S T) :
    F.toRep.val.FactorEmbeds G.toRep.val ↔ F.Embeds G :=
  AR.factorEmbeds_ofData_iff

/-- A correspondence free of every banned subgraph of a grammar, on the data. -/
def SpecifiedBy (φ : List (Strings S T)) (G : Strings S T) : Prop := ∀ F ∈ φ, ¬ F.Embeds G

instance [DecidableEq S] [DecidableEq T] (φ : List (Strings S T)) (G : Strings S T) :
    Decidable (SpecifiedBy φ G) :=
  List.decidableBAll _ _

/-- The data-level grammar test is the representation-level one. -/
theorem specifiedByRep_map_toRep (φ : List (Strings S T)) (G : Strings S T) :
    specifiedByRep (φ.map toRep) G.toRep ↔ SpecifiedBy φ G := by
  simp only [specifiedByRep, AR.Free, List.forall_mem_map, factorEmbeds_toRep_iff, SpecifiedBy]

end Strings

end Coordinate

end Correspondence
end Autosegmental
