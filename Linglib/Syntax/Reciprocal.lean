/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Insert
import Linglib.Syntax.Voice.Alternation
import Linglib.Data.WALS.Features.F106A

/-!
# Reciprocal constructions: morphosyntactic typology

Cross-linguistic vocabulary for reciprocal constructions: the marking strategy
([nordlinger-2023]'s synthesis of [konig-kokutani-2006], [nedjalkov-2007a], and
[evans-2008]), the site it codes and the valency it derives, the formation locus
of reciprocal verbs ([siloni-2008], [siloni-2012]), and the marker inventories
from which the WALS reciprocal–reflexive value ([maslova-nedjalkov-2013]) is
computed.

## Main definitions

* `Strategy`, `CodingSite`, `Strategy.codingSite`, `Strategy.IsNominal` — the
  strategy and the site it marks.
* `Strategy.alternation`, `Strategy.defaultValency` — the coding-frame operation
  a predicate-marking strategy realizes ([creissels-2024]'s
  `Voice.reciprocalization`) and the valency it therefore derives.
* `Formation` — lexical vs syntactic formation of reciprocal verbs.
* `Reading`, `Marker`, `ofInventory` — a reciprocal exponent with its polysemy,
  and the WALS Ch 106 value of an inventory.

## Implementation notes

The strategy fixes the coding site, and the default valency follows from the
site: argument strategies leave the base verb's frame intact, while predicate
and multipredicate strategies realize the denucleativizing reciprocalization
alternation, whose derived construction is intransitive. Languages may override
the default (Tonga, Malagasy: [maslova-2008], [hurst-2012]), so the observed
valency is data in the study that records it. A bound reciprocal pronoun
(Wambaya *-ngg-*) fills an argument slot and is an argument strategy; the clitic
of a syntactically formed reciprocal verb (French *se*) is not an object
([siloni-2012]) and marks the predicate.

## References

* [nordlinger-2023]
* [konig-kokutani-2006]
* [nedjalkov-2007a]
* [nedjalkov-2007b]
* [evans-2008]
* [maslova-nedjalkov-2013]
* [siloni-2008]
* [siloni-2012]
* [reinhart-siloni-2005]
* [creissels-2024]
* [maslova-2008]
* [hurst-2012]
-/

namespace Reciprocal

/-- Morphosyntactic strategy for encoding reciprocity ([nordlinger-2023]'s
compression of [konig-kokutani-2006], [nedjalkov-2007a], and [evans-2008]). -/
inductive Strategy where
  /-- Bipartite quantifier NP (English *each other*, Icelandic *hvort annað*). -/
  | bipartiteNP
  /-- Free reciprocal pronoun (Hausa *jūnan-mù*, German *einander*). -/
  | recipPronoun
  /-- Bound reciprocal pronoun in the object slot of the pronominal complex
      (Wambaya *-ngg-*, Warlpiri *-nyanu*; [evans-2008]). -/
  | boundPronoun
  /-- Clitic of a syntactically formed reciprocal verb (French *se*, Czech *se*;
      [siloni-2012]). -/
  | recipClitic
  /-- Verbal affix (Swahili *-an-*, Hungarian *-óz-*). -/
  | verbalAffix
  /-- Reciprocal auxiliary (Warrwa *wanji-* 'exchange', [evans-2008]). -/
  | verbalAuxiliary
  /-- Inherently reciprocal predicate (English *quarrel*, *meet*). -/
  | lexical
  /-- Compound verb (Mandarin *dǎ-lái-dǎ-qù*, [konig-kokutani-2006]). -/
  | compoundVerb
  deriving DecidableEq, Repr

/-- Where a strategy codes reciprocity: [evans-2008]'s three-way split. -/
inductive CodingSite where
  /-- A nonsubject argument position, as an NP or a bound pronominal. -/
  | argument
  /-- The predicate: an affix, auxiliary, or clitic, or the lexical entry itself. -/
  | predicate
  /-- A fused multipredicate structure. -/
  | multiclausal
  deriving DecidableEq, Repr

/-- Coding site of each strategy. -/
def Strategy.codingSite : Strategy → CodingSite
  | .bipartiteNP | .recipPronoun | .boundPronoun => .argument
  | .recipClitic | .verbalAffix | .verbalAuxiliary | .lexical => .predicate
  | .compoundVerb => .multiclausal

/-- A nominal strategy marks a nonsubject argument position
([konig-kokutani-2006]). -/
def Strategy.IsNominal (s : Strategy) : Prop := s.codingSite = .argument

instance : DecidablePred Strategy.IsNominal :=
  fun s ↦ inferInstanceAs (Decidable (s.codingSite = .argument))

/-- Valency of a reciprocal construction ([nordlinger-2023]). -/
inductive Valency where
  /-- Two overt syntactic argument slots preserved. -/
  | bivalent
  /-- The reciprocants form a single subject NP. -/
  | monovalent
  deriving DecidableEq, Repr

open Voice in
/-- The coding-frame operation a strategy realizes: every strategy marking the
predicate or a multipredicate structure applies [creissels-2024]'s
denucleativizing `reciprocalization`; argument strategies leave the frame intact. -/
def Strategy.alternation (s : Strategy) : Option ValencyAlternation :=
  if s.IsNominal then none else some reciprocalization

/-- Default valency, derived from the realized alternation's `derivedTransitive`
field; a tendency that languages may override ([maslova-2008], [hurst-2012]). -/
def Strategy.defaultValency (s : Strategy) : Valency :=
  match s.alternation with
  | some a => if a.derivedTransitive = some false then .monovalent else .bivalent
  | none => .bivalent

/-- Nominal strategies preserve valency by default. -/
theorem Strategy.defaultValency_eq_bivalent_iff (s : Strategy) :
    s.defaultValency = .bivalent ↔ s.IsNominal := by
  cases s <;> decide

/-- Predicate-marking strategies reduce valency by default. -/
theorem Strategy.defaultValency_eq_monovalent_iff (s : Strategy) :
    s.defaultValency = .monovalent ↔ ¬ s.IsNominal := by
  cases s <;> decide

/-- Formation locus of reciprocal verbs: lexical θ-role bundling vs syntactic
derivation ([siloni-2008], [siloni-2012]; [reinhart-siloni-2005]'s lex-syn
parameter). -/
inductive Formation where
  | lexical
  | syntactic
  deriving DecidableEq, Repr

/-! ### Marker inventories -/

/-- Readings a reciprocal marker can carry ([nordlinger-2023] after
[nedjalkov-2007b]). -/
inductive Reading where
  | reciprocal
  | reflexive
  | collective
  | sociative
  | iterative
  deriving DecidableEq, Repr

/-- A reciprocal exponent: form, strategy, and the readings it covers. -/
structure Marker where
  /-- Surface form (romanization or orthographic). -/
  form : String
  /-- Native-script form, when `form` is a romanization. -/
  script : Option String := none
  /-- Morphosyntactic strategy of the exponent. -/
  strategy : Strategy
  /-- Readings the marker covers. -/
  readings : Finset Reading := {.reciprocal}
  deriving DecidableEq

open Data.WALS.F106A in
/-- The WALS Ch 106 value of a marker inventory ([maslova-nedjalkov-2013]): no
reciprocal-capable marker, every such marker also reflexive, none reflexive, or
both kinds. -/
def ofInventory (inv : List Marker) : ReciprocalType :=
  let recips := inv.filter fun m ↦ Reading.reciprocal ∈ m.readings
  if recips.isEmpty then .noReciprocalConstruction
  else if recips.all (fun m ↦ Reading.reflexive ∈ m.readings) then .identicalToReflexive
  else if recips.all (fun m ↦ Reading.reflexive ∉ m.readings) then .distinctFromReflexive
  else .mixed

end Reciprocal
