/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Word.Basic

open Morphology (Word)


/-!
# Auxiliary

The auxiliary word class: closed-class function words of verbal predication,
carrying tense-aspect-modality or voice meaning while a lexical verb carries
the semantic content ([anderson-2006]; UD `AUX`). Unlike `Particle`, whose
entries are uniform enough for one concrete structure, auxiliary entries vary
irreducibly per language — agreement and negation morphology in English,
force-flavor meaning in German modals, register and predicate distribution in
Indonesian — so the category is an interface over per-language entry types:
`Auxiliary α` holds when every member of `α` projects to a UD `AUX` word.

Aux-related content elsewhere: AVC inflection-locus typology in
`Syntax/Category/Auxiliary/Constructions.lean`; BE/HAVE selection in
`Semantics/ArgumentStructure/AuxiliarySelection.lean`; per-language entry
types in `Fragments/`.
-/

set_option autoImplicit false

/-- An entry type of auxiliaries: every member projects to a UD `AUX` word. -/
class Auxiliary (α : Type*) where
  toWord : α → Word
  cat_aux : ∀ a, (toWord a).cat = .AUX

attribute [simp] Auxiliary.cat_aux
