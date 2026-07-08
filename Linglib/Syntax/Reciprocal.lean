/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Voice.Alternation

/-!
# Reciprocal constructions: morphosyntactic typology

Cross-linguistic vocabulary for reciprocal constructions: the
reciprocal-reflexive formal relation (WALS Ch 106, [maslova-nedjalkov-2013]),
the marking strategy ([nordlinger-2023]'s synthesis of [konig-kokutani-2006],
[nedjalkov-2007a], and [evans-2008]), the valency effect, and the formation
locus of reciprocal verbs ([siloni-2008], [siloni-2012]).

The exponence primitive is the marker (`Marker`): form, strategy, and polysemy
readings. The WALS Ch 106 value is computed from a language's marker inventory
(`ofInventory`), `isNominal` projects from the coding site, and the default
valency effect derives from the coding-frame operation a strategy realizes
(`Voice.reciprocalization`).

## Main definitions

* `ReflexiveRelation` — reciprocal/reflexive formal relation (WALS Ch 106).
* `Strategy` + `codingSite`/`isNominal` — the morphosyntactic locus.
* `Strategy.alternation` / `defaultValency` — the realized coding-frame
  operation and the valency effect it derives.
* `Valency`, `Formation` + `Formation.allowsDiscontinuous`.
* `Reading`, `Marker`, `ofInventory` — marker inventories and the derived
  WALS Ch 106 value.
* `LexicalVerb` — verbs with inherently reciprocal entries (the lexical
  strategy marks predicates, not forms).

Per-language inventories live in `Fragments/{Lang}/Reciprocals.lean`;
WALS-data grounding lives with the studies that use it (e.g.
`Studies/Nordlinger2023.lean`), not here.
-/

namespace Reciprocal

/-- WALS Ch 106 relation between reciprocal and reflexive marking
([maslova-nedjalkov-2013]). -/
inductive ReflexiveRelation where
  /-- "There are no non-iconic reciprocal constructions." -/
  | noDedicated
  /-- "All reciprocal constructions are formally distinct from reflexive
      constructions" (English *each other* vs *themselves*). -/
  | distinctFromReflexive
  /-- "There are both reflexive and non-reflexive reciprocal constructions"
      (German *sich* + *einander*). -/
  | mixed
  /-- "The reciprocal and reflexive constructions are formally identical"
      (Imbabura Quechua *-ri-*). -/
  | identicalToReflexive
  deriving DecidableEq, Repr

/-- Morphosyntactic strategy for encoding reciprocity ([nordlinger-2023]
§3.1's compression of [konig-kokutani-2006], [nedjalkov-2007a], and
[evans-2008]). -/
inductive Strategy where
  /-- Bipartite quantifier NP (English *each other*, Icelandic *hvort annað*). -/
  | bipartiteNP
  /-- Reciprocal pronoun (Hausa *jūnan-mù*). -/
  | recipPronoun
  /-- Reciprocal clitic (French *se*, Wambaya *-ngg-*). -/
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

/-- Valency effect of the reciprocal construction ([nordlinger-2023] §3.2). -/
inductive Valency where
  /-- Two overt syntactic argument slots preserved. -/
  | bivalent
  /-- The reciprocants form a single subject NP. -/
  | monovalent
  deriving DecidableEq, Repr

/-- Coding site of reciprocal marking: argument position, predicate, or
fused multipredicate structure. -/
inductive CodingSite where
  | argument
  | predicate
  | multiclausal
  deriving DecidableEq, Repr

/-- Coding site of each strategy. Clitics sit on the predicate side,
following [siloni-2012] rather than [konig-kokutani-2006]'s nominal
grouping. -/
def Strategy.codingSite : Strategy → CodingSite
  | .bipartiteNP | .recipPronoun => .argument
  | .recipClitic | .verbalAffix | .verbalAuxiliary | .lexical => .predicate
  | .compoundVerb => .multiclausal

/-- Whether the strategy marks a (nonsubject) argument position
([nordlinger-2023] §3.2). -/
def Strategy.isNominal (s : Strategy) : Bool :=
  s.codingSite == .argument

open Voice in
/-- The coding-frame operation a strategy realizes: grammatical verb-marking
strategies apply [creissels-2025]'s denucleativizing `reciprocalization`. -/
def Strategy.alternation : Strategy → Option ValencyAlternation
  | .recipClitic | .verbalAffix | .verbalAuxiliary | .compoundVerb =>
      some reciprocalization
  | .bipartiteNP | .recipPronoun | .lexical => none

/-- Default valency effect, derived from the realized alternation's
`derivedTransitive` field; a tendency that languages may override
(Wambaya, Tonga, Malagasy — [maslova-2008], [hurst-2012]). -/
def Strategy.defaultValency (s : Strategy) : Valency :=
  match s.alternation with
  | some a => if a.derivedTransitive = some false then .monovalent else .bivalent
  | none   => .bivalent

/-- Formation locus of reciprocal verbs: lexical θ-role bundling vs
syntactic derivation ([siloni-2008], [siloni-2012];
[reinhart-siloni-2005]'s lex-syn parameter). -/
inductive Formation where
  | lexical
  | syntactic
  deriving DecidableEq, Repr

/-- Whether the formation licenses the discontinuous reciprocal
construction — lexical only ([siloni-2012] §7; verb-level exceptions
exist, fn. 32). -/
def Formation.allowsDiscontinuous : Formation → Bool
  | .lexical   => true
  | .syntactic => false

/-! ### Marker inventories -/

/-- Readings a reciprocal marker can carry ([nordlinger-2023] §4.2,
[nedjalkov-2007b]). -/
inductive Reading where
  | reciprocal
  | reflexive
  | collective
  | sociative
  | iterative
  deriving DecidableEq, Repr

/-- A verb with an inherently reciprocal (lexical) entry. -/
structure LexicalVerb where
  /-- Citation form of the reciprocal entry. -/
  form : String
  /-- Gloss of the reciprocal entry. -/
  gloss : String
  /-- Form of the binary (transitive) alternate: homophonous in Romance,
      morphologically distinct in Bantu (Swahili *acha* > *achana*),
      `none` when no alternate exists. -/
  transitiveAlternate : Option String := none
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
  readings : List Reading := [.reciprocal]
  deriving DecidableEq, Repr

/-- WALS Ch 106 value computed from a marker inventory: no
reciprocal-capable marker → `noDedicated`; all also reflexive →
`identicalToReflexive`; none reflexive → `distinctFromReflexive`;
both kinds → `mixed`. -/
def ofInventory (inv : List Marker) : ReflexiveRelation :=
  let recips := inv.filter (·.readings.contains .reciprocal)
  if recips.isEmpty then .noDedicated
  else if recips.all (·.readings.contains .reflexive) then .identicalToReflexive
  else if recips.all (fun m => !m.readings.contains .reflexive) then
    .distinctFromReflexive
  else .mixed

end Reciprocal
