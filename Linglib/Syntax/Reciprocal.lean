/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.WALS.Features.F106A

/-!
# Reciprocal constructions: morphosyntactic typology

Cross-linguistic vocabulary for reciprocal constructions: the
reciprocal-reflexive formal relation (WALS Ch 106, [maslova-nedjalkov-2013]),
the morphosyntactic locus of reciprocal marking ([nordlinger-2023]'s synthesis
of [konig-kokutani-2006], [nedjalkov-2007a], and [evans-2008]), the valency
effect, and the formation locus of reciprocal verbs ([siloni-2008],
[siloni-2012]). Valency-reducing reciprocalization as an operation on coding
frames is `Syntax.ArgumentStructure.Alternation.reciprocalization`.

## Main definitions

* `ReciprocalType` — reciprocal/reflexive formal relation (WALS Ch 106).
* `RecipStrategy` + `RecipStrategy.isNominal` — the morphosyntactic locus.
* `RecipValency` — valency effect (bivalent vs monovalent).
* `RecipFormation` + `RecipFormation.allowsDiscontinuous` — lexical vs syntactic.
* `ofWALS106A` — WALS Ch 106 converter.
-/

namespace Reciprocal

/-- WALS Ch 106: how reciprocal situations are encoded relative to reflexives.
The four values follow [maslova-nedjalkov-2013]'s classification. -/
inductive ReciprocalType where
  /-- "There are no non-iconic reciprocal constructions" — the language lacks
      a dedicated grammatical reciprocal marker. -/
  | noDedicated
  /-- "All reciprocal constructions are formally distinct from reflexive
      constructions" (e.g. English *each other* vs *themselves*). -/
  | distinctFromReflexive
  /-- "There are both reflexive and non-reflexive reciprocal constructions" —
      a reflexive-identical strategy coexists with a formally distinct one
      (e.g. German *sich* + *einander*). Common in Europe. -/
  | mixed
  /-- "The reciprocal and reflexive constructions are formally identical"
      (e.g. Imbabura Quechua *-ri-*). -/
  | identicalToReflexive
  deriving DecidableEq, Repr

/-- Morphosyntactic strategy for encoding reciprocity, following the strategy
inventory of [nordlinger-2023] §3.1, which compresses the structural
typologies of [konig-kokutani-2006], [nedjalkov-2007a], and [evans-2008]
(Evans's full typology is finer, splitting NP-marking into five subtypes and
treating verb compounding as multiclausal). -/
inductive RecipStrategy where
  /-- Bipartite quantifier NP — English *each other*, Russian *drug druga*,
      Icelandic *hvort annað* (parts independently inflected,
      [hurst-nordlinger-2021]). -/
  | bipartiteNP
  /-- Reciprocal pronoun — Hausa *jūnan-mù*. Free or bound pronominal form in
      argument position. -/
  | recipPronoun
  /-- Reciprocal clitic — French/Czech *se*, Wambaya *-ngg-* (RR morpheme in
      the auxiliary, [nordlinger-1998]). Intermediate between pronoun and
      affix. -/
  | recipClitic
  /-- Morphological marking on the verb — Swahili *-an-*, Hungarian *-óz-*,
      Chicheŵa *-an-*. Typically derives a monovalent verb from a transitive
      base. -/
  | verbalAffix
  /-- Reciprocal auxiliary — Warrwa *wanji-* 'exchange' replaces the regular
      transitive auxiliary ([evans-2008]). -/
  | verbalAuxiliary
  /-- Inherently reciprocal predicate — English *quarrel*, *meet*. The
      symmetric meaning is part of the verb's lexical semantics. -/
  | lexical
  /-- Compound verb — Mandarin *dǎ-lái-dǎ-qù* (beat-come-beat-go = 'beat each
      other', [konig-kokutani-2006]). -/
  | compoundVerb
  deriving DecidableEq, Repr

/-- Whether the strategy marks a (nonsubject) argument position, in the sense
of [nordlinger-2023] §3.2's NP/argument vs verb-marked split (after
[konig-kokutani-2006]'s nominal/verbal distinction).

Deviation from [konig-kokutani-2006]: they group clitics with the nominal
strategies, but this classifier places `recipClitic` on the verbal side
because Romance/Slavic *se* is not an anaphoric object — it marks a
valency-reducing operation on the verb ([siloni-2012]). Wambaya *-ngg-* is
the documented exception: a bound clitic whose clause stays bivalent
([evans-et-al-2007]). -/
def RecipStrategy.isNominal : RecipStrategy → Bool
  | .bipartiteNP     => true
  | .recipPronoun    => true
  | .recipClitic     => false
  | .verbalAffix     => false
  | .verbalAuxiliary => false
  | .lexical         => false
  | .compoundVerb    => false

/-- Valency effect of the reciprocal construction ([nordlinger-2023] §3.2):
syntactically bivalent constructions keep two overt argument slots, while
monovalent ones express all reciprocants in the subject. NP/argument
strategies tend to preserve valency and verb-marked strategies to reduce it
([nedjalkov-2007a]), but the correlation is a tendency, not absolute:
Malagasy verb-marked reciprocals retain full valency at f-structure
([hurst-2006], [hurst-2012]), and Tonga combines verbal marking with two
argument NPs ([maslova-2008]). [maslova-2008]'s unary/binary distinction
cross-cuts this one: English *each other* is bivalent yet unary (the object
slot is filled by a fixed expression). -/
inductive RecipValency where
  /-- Two overt syntactic argument slots preserved. -/
  | bivalent
  /-- The verb becomes intransitive; reciprocants form a single subject NP. -/
  | monovalent
  deriving DecidableEq, Repr

/-- Where reciprocal verbs are formed, per [siloni-2008] and [siloni-2012]
(the lex-syn parameter of [reinhart-siloni-2005]):

- `lexical`: formed in the lexicon through "bundling" — two thematic roles
  (agent, patient) merge into a single complex role, yielding symmetric verbs
  whose reciprocity is a singular atomic event.
- `syntactic`: formed in the course of the syntactic derivation (Romance and
  some Slavic *se* verbs); reciprocity accumulates from sub-events.

Siloni's discontinuity generalization: discontinuous reciprocal constructions
(reciprocants split across subject and comitative argument) occur only with
lexically formed reciprocal verbs. -/
inductive RecipFormation where
  | lexical
  | syntactic
  deriving DecidableEq, Repr

/-- Whether the formation type licenses the discontinuous reciprocal
construction ("John kissed with Mary") — available only for lexically formed
reciprocal verbs ([siloni-2012] §7; [nordlinger-2023] §3.3). A language-level
availability claim: individual lexical reciprocals may still resist it, e.g.
English *kiss*/*hug* ([siloni-2012], fn. 32). -/
def RecipFormation.allowsDiscontinuous : RecipFormation → Bool
  | .lexical   => true
  | .syntactic => false

/-! ### WALS converter -/

/-- Convert a WALS 106A value to `ReciprocalType`. -/
def ofWALS106A : Data.WALS.F106A.ReciprocalType → ReciprocalType
  | .noReciprocalConstruction => .noDedicated
  | .distinctFromReflexive    => .distinctFromReflexive
  | .mixed                    => .mixed
  | .identicalToReflexive     => .identicalToReflexive

end Reciprocal
