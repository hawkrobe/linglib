/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Word

/-!
# Phrase-level prosodic structure

The φ and ι layers sit above the prosodic word, with Strict-Layer well-formedness one level up
(Selkirk 1996; overview in Ishihara and Kalivoda 2022). A phrase is a φ-node over well-formed
ω-trees, and an utterance an ι-node over phrases. `HeadUnique` is the culminativity of
prominence, at most one head child per node, the structural hook that Büring's (2015) metrical
weak–strong calculus reads (Büring 2016). The φ-constituents of an utterance are its maximal
φ-projections (`maximalProjections`); φ-edges are what demarcative focus reflexes
(`Reflex.boundary`) realize.

## References

* [selkirk-1996]
* [ishihara-kalivoda-2022]
* [buring-2015]
* [buring-2016]
-/

@[expose] public section

namespace Prosody

open RoseTree

/-- A well-formed phonological phrase is a licensed tree rooted in a φ-node, so a φ-node over
well-formed prosodic words, the Strict Layer at the phrase level. -/
abbrev IsPhrase : Tree → Prop := IsConstituent Constituent.isPh

/-- A well-formed intonational phrase, or utterance, is a licensed tree rooted in an ι-node, so
an ι-node over well-formed phrases. -/
abbrev IsUtterance : Tree → Prop := IsConstituent Constituent.isIota

/-- Prominence is culminative when at most one child heads its parent. -/
def HeadUnique (t : Tree) : Prop :=
  (t.children.filter (fun c => c.value.isHead)).length ≤ 1

instance (t : Tree) : Decidable (HeadUnique t) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Every child of a well-formed phrase is a well-formed word. -/
theorem IsPhrase.children_isWord {t : Tree} (h : IsPhrase t) :
    ∀ c ∈ t.children, IsWord c := by
  rcases t with ⟨a, cs⟩
  obtain ⟨hph, hl⟩ := h
  obtain ⟨b, rfl⟩ : ∃ b, a = .ph b := by cases a <;> simp_all [Constituent.isPh]
  exact fun c hc ↦ ⟨(licensed_node_iff.mp hl).1 c.value (List.mem_map_of_mem hc), hl.of_mem hc⟩

/-- Every child of a well-formed utterance is a well-formed phrase. -/
theorem IsUtterance.children_isPhrase {t : Tree} (h : IsUtterance t) :
    ∀ c ∈ t.children, IsPhrase c := by
  rcases t with ⟨a, cs⟩
  obtain ⟨hι, hl⟩ := h
  obtain rfl : a = .iota := by cases a <;> simp_all [Constituent.isIota]
  exact fun c hc ↦ ⟨(licensed_node_iff.mp hl).1 c.value (List.mem_map_of_mem hc), hl.of_mem hc⟩

end Prosody
