module

public import Linglib.Morphology.DistributedMorphology.Fusion
public import Linglib.Morphology.DistributedMorphology.Impoverishment

/-!
# The spell-out pipeline

The PF branch of the Y-model at the domain level: a spell-out domain is
the sequence of terminals the syntax hands over, the postsyntactic modules
transform it, and Vocabulary Insertion realizes what survives, each
position in its neighborhood; the module inventory and its ordering follow
the Basque morphotactics. The focus-level rule types
(`ImpoverishmentRule` and kin) rewrite one terminal inside
its `Neighborhood`; the operations here move, remove, and merge the
terminals themselves, which no focus-level rule can express. Each is a
rewrite of the domain at the first of its neighborhoods (`Neighborhood.along`)
that satisfies the rule's condition.

Each operation carries its position-count law, so terminal/exponent
misalignment is arithmetic: terminal metathesis preserves the count,
obliteration and fusion never increase it, and
`Spellout.length_pf` says insertion positions equal terminals after the
modules — Fission multiplies exponents within a position (`scansion`),
not positions. `winner?_retreat` (`VocabularyInsertion/Basic.lean`) supplies the
insertion-side ordering law.

Consumers: `Studies/Middleton2026.lean` (Basque whole-terminal rules and
the Ondarru ordering witness), `Studies/HalleMarantz1993.lean` (Tns+Agr
fusion feeding one insertion).

## Main definitions

* `SpelloutDomain`, `rewriteFirst`: the domain, and rewriting it at its first neighborhood
  satisfying a condition.
* `ObliterationRule`, `TerminalMetathesisRule`: whole-terminal deletion and adjacent-terminal
  swap, each a decidable condition on a neighborhood.
* `FusionRule.applyFirstAdjacent`: the domain lift of Fusion.
* `Spellout`, `Spellout.run`, `Spellout.pf`: the module sequence, then insertion in context.

## Main results

* `length_rewriteFirst_le`, `length_rewriteFirst`: the count laws, which hold because each
  neighborhood reassembles to the domain (`Neighborhood.toList_of_mem_along`).
* `Spellout.length_pf`: insertion positions equal terminals after the modules.

## TODO

* The LF branch: an `Interpreted` extension whose interpretation reads
  the input domain (the Y-model separation by type), seeded by the
  domain-level allosemy licensing of `Studies/Benz2025.lean`.
* Stratifying the module list by linearization — Lowering before,
  Local Dislocation after.

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
* [K. Arregi and A. Nevins, *Morphotactics*][arregi-nevins-2012]
* [D. Embick and R. Noyer, *Movement operations after syntax*][embick-noyer-2001]
-/

@[expose] public section

namespace DistributedMorphology

/-- A spell-out domain is the linear sequence of terminals the syntax hands over at
spell-out. -/
abbrev SpelloutDomain (Bundle : Type*) := List Bundle

variable {Bundle : Type*}

open Neighborhood (along toList_of_mem_along)

/-! ### Rewriting at the first neighborhood -/

/-- `rewriteFirst p f d` replaces the domain `d` by `f n` for its first neighborhood `n`
satisfying `p`, scanning left to right, and leaves it unchanged if there is none. Obliteration,
terminal metathesis, and the domain lift of Fusion are its instances. -/
def rewriteFirst (p : Neighborhood Bundle → Prop) [DecidablePred p]
    (f : Neighborhood Bundle → SpelloutDomain Bundle) (d : SpelloutDomain Bundle) :
    SpelloutDomain Bundle :=
  ((along d).find? fun n ↦ decide (p n)).elim d f

section RewriteFirst

variable {p : Neighborhood Bundle → Prop} [DecidablePred p]
  {f : Neighborhood Bundle → SpelloutDomain Bundle}

/-- A rewrite that never lengthens a neighborhood's string never lengthens the
domain. -/
theorem length_rewriteFirst_le (hf : ∀ n, (f n).length ≤ n.toList.length)
    (d : SpelloutDomain Bundle) : (rewriteFirst p f d).length ≤ d.length := by
  unfold rewriteFirst
  cases h : (along d).find? fun n ↦ decide (p n) with
  | none => exact le_rfl
  | some n => simpa [toList_of_mem_along d (List.mem_of_find?_eq_some h)] using hf n

/-- A rewrite that preserves the length of each neighborhood's string preserves
the number of terminals. -/
theorem length_rewriteFirst (hf : ∀ n, (f n).length = n.toList.length)
    (d : SpelloutDomain Bundle) : (rewriteFirst p f d).length = d.length := by
  unfold rewriteFirst
  cases h : (along d).find? fun n ↦ decide (p n) with
  | none => rfl
  | some n => simpa [toList_of_mem_along d (List.mem_of_find?_eq_some h)] using hf n

end RewriteFirst

/-- A whole-terminal deletion rule — [arregi-nevins-2012]'s Obliteration:
the terminal whose neighborhood satisfies `condition` is removed
outright. The focus-level `ImpoverishmentRule` deletes a feature inside a
terminal; this rule deletes the terminal. -/
structure ObliterationRule (Bundle : Type*) where
  /-- The neighborhoods whose focus is removed. -/
  condition : Neighborhood Bundle → Prop
  [decCond : DecidablePred condition]

namespace ObliterationRule

instance (rule : ObliterationRule Bundle) : DecidablePred rule.condition := rule.decCond

/-- Applying the rule drops the first terminal whose neighborhood satisfies its condition, and
otherwise leaves the domain unchanged. -/
def apply (rule : ObliterationRule Bundle) : SpelloutDomain Bundle → SpelloutDomain Bundle :=
  rewriteFirst rule.condition fun n ↦ n.leftCtx.reverse ++ n.rightCtx

/-- Obliteration never increases the number of terminals. -/
theorem length_apply_le (rule : ObliterationRule Bundle)
    (d : SpelloutDomain Bundle) : (rule.apply d).length ≤ d.length :=
  length_rewriteFirst_le (fun n ↦ by simp [Neighborhood.toList]) d

end ObliterationRule

/-- An adjacent-terminal swap rule — the terminal-order metathesis of
[arregi-nevins-2012]'s Metathesis module (the feature metathesis of the Taos
prefix in `Studies/Middleton2026.lean`): where `condition` holds of a
neighborhood, its focus swaps with the terminal to its right. Ergative
Metathesis, which fronts a clitic across intervening terminals, is a
`rewriteFirst` of its own there. -/
structure TerminalMetathesisRule (Bundle : Type*) where
  /-- The neighborhoods whose focus swaps with the terminal to its right. -/
  condition : Neighborhood Bundle → Prop
  [decCond : DecidablePred condition]

namespace TerminalMetathesisRule

instance (rule : TerminalMetathesisRule Bundle) : DecidablePred rule.condition := rule.decCond

/-- Applying the rule swaps the first focus that has a terminal to its right and whose
neighborhood satisfies its condition with that terminal, and otherwise leaves the domain
unchanged. -/
def apply (rule : TerminalMetathesisRule Bundle) :
    SpelloutDomain Bundle → SpelloutDomain Bundle :=
  rewriteFirst (fun n ↦ n.rightCtx ≠ [] ∧ rule.condition n) fun
    | ⟨t₁, l, t₂ :: r⟩ => l.reverse ++ t₂ :: t₁ :: r
    | n => n.toList

/-- Terminal metathesis preserves the number of terminals. -/
@[simp] theorem length_apply (rule : TerminalMetathesisRule Bundle)
    (d : SpelloutDomain Bundle) : (rule.apply d).length = d.length :=
  length_rewriteFirst (fun | ⟨_, _, _ :: _⟩ => by simp [Neighborhood.toList]
                           | ⟨_, _, []⟩ => rfl) d

end TerminalMetathesisRule

namespace FusionRule

variable {F : Type*}

/-- The domain lift of Fusion fuses the first terminal that fuses with the terminal to its right,
and otherwise leaves the domain unchanged. -/
def applyFirstAdjacent (rule : FusionRule F) : SpelloutDomain (List F) → SpelloutDomain (List F) :=
  rewriteFirst (fun n ↦ ∃ q ∈ n.rightCtx.head?, rule.condition n.focus q) fun
    | ⟨p, l, q :: r⟩ => l.reverse ++ (p ++ q) :: r
    | n => n.toList

/-- Fusion never increases the number of terminals. -/
theorem length_applyFirstAdjacent_le (rule : FusionRule F) (d : SpelloutDomain (List F)) :
    (rule.applyFirstAdjacent d).length ≤ d.length :=
  length_rewriteFirst_le (fun | ⟨_, _, _ :: _⟩ => by simp [Neighborhood.toList]
                              | ⟨_, _, []⟩ => le_rfl) d

end FusionRule

/-- Run an ordered module sequence over a domain. The order of the list
is the theory's architectural claim ([arregi-nevins-2012]'s strict
sequence; the Basque ordering witness in `Studies/Middleton2026.lean`
shows reordering it has empirical content). -/
def runModules (modules : List (SpelloutDomain Bundle → SpelloutDomain Bundle))
    (d : SpelloutDomain Bundle) : SpelloutDomain Bundle :=
  modules.foldl (fun d m => m d) d

/-- Module sequences compose by concatenation. -/
theorem runModules_append
    (m₁ m₂ : List (SpelloutDomain Bundle → SpelloutDomain Bundle))
    (d : SpelloutDomain Bundle) :
    runModules (m₁ ++ m₂) d = runModules m₂ (runModules m₁ d) := by
  simp [runModules, List.foldl_append]

@[simp] theorem runModules_nil (d : SpelloutDomain Bundle) :
    runModules ([] : List (SpelloutDomain Bundle → SpelloutDomain Bundle)) d
      = d := rfl

/-- A PF-branch pipeline runs the ordered postsyntactic modules over a spell-out domain, then
Vocabulary Insertion at each surviving position in its neighborhood. -/
structure Spellout (Bundle F : Type*) where
  /-- The ordered postsyntactic module sequence. -/
  modules : List (SpelloutDomain Bundle → SpelloutDomain Bundle)
  /-- The exponents inserted at a position, seeing its neighbors: one,
  several under Fission (`scansion`), none at a non-licensed position. -/
  insert : Neighborhood Bundle → List F

namespace Spellout

variable {F : Type*}

/-- The domain after the module sequence. -/
def run (s : Spellout Bundle F) (d : SpelloutDomain Bundle) :
    SpelloutDomain Bundle :=
  runModules s.modules d

/-- The PF output has one insertion slot per surviving position. -/
def pf (s : Spellout Bundle F) (d : SpelloutDomain Bundle) :
    List (List F) :=
  (along (s.run d)).map s.insert

/-- Exponent slots equal terminals after the modules, so the exponent count diverges from the
syntactic terminal count only through the modules. -/
@[simp] theorem length_pf (s : Spellout Bundle F) (d : SpelloutDomain Bundle) :
    (s.pf d).length = (s.run d).length := by
  simp [pf]

end Spellout

end DistributedMorphology
