/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Prosody.Word

/-!
# Phrase-level prosodic structure

The φ and ι layers above the prosodic word: Strict-Layer
well-formedness one level up ([selkirk-1996]; overview
[ishihara-kalivoda-2022]). A phrase is a φ-node over well-formed
ω-trees; an utterance is an ι-node over phrases. `HeadUnique` is the
culminativity of prominence — at most one head child per node — the
structural hook the metrical weak–strong calculus of [buring-2015]
reads ([buring-2016]). `phrases` reads the φ-constituents off an
utterance; φ-edges are what demarcative focus reflexes
(`Semantics.Focus.Reflex.boundary`) realize.
-/

namespace Prosody

open RoseTree

/-- A φ-node over well-formed prosodic words: the Strict Layer at the
phrase level. -/
def isPhraseTree (t : Tree) : Bool :=
  t.value.isPh && t.children.all isWordTree

/-- Well-formed phonological phrase. -/
def IsPhrase (t : Tree) : Prop := isPhraseTree t

instance (t : Tree) : Decidable (IsPhrase t) :=
  inferInstanceAs (Decidable (_ = true))

/-- An ι-node over well-formed phrases: the utterance level. -/
def isUtteranceTree (t : Tree) : Bool :=
  t.value.isIota && t.children.all isPhraseTree

/-- Well-formed intonational phrase (utterance). -/
def IsUtterance (t : Tree) : Prop := isUtteranceTree t

instance (t : Tree) : Decidable (IsUtterance t) :=
  inferInstanceAs (Decidable (_ = true))

/-- Culminativity of prominence: at most one child heads its parent. -/
def HeadUnique (t : Tree) : Prop :=
  (t.children.filter (fun c => c.value.isHead)).length ≤ 1

instance (t : Tree) : Decidable (HeadUnique t) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The φ-constituents of a tree, outermost-first. -/
def phrases (t : Tree) : List Tree :=
  maximalProjections Constituent.isPh t

/-- Every child of a well-formed phrase is a well-formed word. -/
theorem IsPhrase.children_isWord {t : Tree} (h : IsPhrase t) :
    ∀ c ∈ t.children, IsWord c := by
  have := (Bool.and_eq_true _ _).mp h
  exact fun c hc => (List.all_eq_true.mp this.2) c hc

/-- Every child of a well-formed utterance is a well-formed phrase. -/
theorem IsUtterance.children_isPhrase {t : Tree} (h : IsUtterance t) :
    ∀ c ∈ t.children, IsPhrase c := by
  have := (Bool.and_eq_true _ _).mp h
  exact fun c hc => (List.all_eq_true.mp this.2) c hc

end Prosody
