/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.TwoTier

/-!
# Phonological transformations as correspondence relations

[jardine-2016b] (Ch. 7) models a phonological process as a relation between input and output
strings, presented by a set of correspondence graphs and carved out by banned-subgraph
constraints, which is what makes the relation local. A correspondence graph is a two-tier
representation with the input over `true`, the output over `false`, and the correspondence arcs
as its links; precedence is the order on each tier. A banned subgraph is a factor
(`AR.FactorEmbeds`), so an output-only markedness constraint is a factor with an empty input
tier and no links.

## Main definitions

* `Rep`, `Rep.input`, `Rep.output`: a finite correspondence representation and the two strings
  it relates.
* `relRep`: the string relation of a set of correspondence graphs ([jardine-2016b] Def. 25).
* `specifiedByRep`, `IsLocalRep`: a process presented by a banned-subgraph grammar, and a
  relation presented by a finite one.
* `Rep.ofWords`: the correspondence graph of an input word, an output word and a
  correspondence relation on their positions.

## References

* [jardine-2016b]
-/

@[expose] public section

namespace Autosegmental
namespace Correspondence

section Coordinate

universe u
variable {S T : Type u}

/-- A correspondence representation is a finite two-tier representation, the input over
`true` and the output over `false`, on a vertex type in `Type`, where `AR.ofData` builds. -/
abbrev Rep (S T : Type u) :=
  {G : AR.{u, 0, 0} (Sigma.fst : ((b : Bool) × TwoTier S T b) → Bool) // Finite G.obj.V}

/-- The input string is the `true`-tier word. -/
noncomputable def Rep.input (G : Rep S T) : List S :=
  haveI := G.property
  G.val.tierWord true

/-- The output string is the `false`-tier word. -/
noncomputable def Rep.output (G : Rep S T) : List T :=
  haveI := G.property
  G.val.tierWord false

/-- **R(CG)** ([jardine-2016b] Def. 25) on the foundation: the string
    relation realized by a set of correspondence representations. -/
def relRep (CG : Rep S T → Prop) (w : List S) (v : List T) : Prop :=
  ∃ G, CG G ∧ G.input = w ∧ G.output = v

/-- More correspondence graphs realize a larger relation. -/
theorem relRep_mono {CG CG' : Rep S T → Prop} (h : ∀ G, CG G → CG' G) {w v} :
    relRep CG w v → relRep CG' w v := by
  rintro ⟨G, hG, hi, ho⟩
  exact ⟨G, h G hG, hi, ho⟩

/-- The process specified by banned subgraphs `φ` (Jardine's `CG(φ)`) holds of the
representations free of every forbidden pattern. -/
def specifiedByRep (φ : List (Rep S T)) (G : Rep S T) : Prop :=
  haveI := G.property
  G.val.Free φ

/-- A string relation is **local** when presented by a finite banned-subgraph
    grammar over correspondence representations. -/
def IsLocalRep (R : List S → List T → Prop) : Prop :=
  ∃ φ : List (Rep S T), R = relRep (specifiedByRep φ)

/-- Banned-subgraph grammars compose by union, the `L^NL_G` conjunction of two local
constraint sets. -/
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

/-! ### Correspondence graphs from words -/

/-- The correspondence graph of the input word `w` and the output word `v` under the
correspondence relation `C` on their positions. -/
def Rep.ofWords (w : List S) (v : List T) (C : ℕ → ℕ → Prop) : Rep S T :=
  ⟨AR.ofWords w v C, inferInstance⟩

@[simp] theorem Rep.input_ofWords (w : List S) (v : List T) (C : ℕ → ℕ → Prop) :
    (Rep.ofWords w v C).input = w :=
  AR.tierWord_ofWords_true

@[simp] theorem Rep.output_ofWords (w : List S) (v : List T) (C : ℕ → ℕ → Prop) :
    (Rep.ofWords w v C).output = v :=
  AR.tierWord_ofWords_false

instance [DecidableEq S] [DecidableEq T] (w w' : List S) (v v' : List T)
    (C C' : ℕ → ℕ → Prop) [DecidableRel C] [DecidableRel C'] :
    Decidable ((Rep.ofWords w v C).val.FactorEmbeds (Rep.ofWords w' v' C').val) :=
  inferInstanceAs (Decidable ((AR.ofWords w v C).FactorEmbeds (AR.ofWords w' v' C')))

end Coordinate

end Correspondence
end Autosegmental
