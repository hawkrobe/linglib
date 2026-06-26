/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.WALS.Features.F106A

/-!
# Reciprocal constructions: morphosyntactic typology

[nordlinger-2023]

The reciprocal-construction typology (WALS Ch 106 + [nordlinger-2023]'s
synthesis of König & Kokutani 2006, Nedjalkov 2007a, Evans 2008, and Siloni
2008/2012): how a language encodes reciprocity relative to reflexives, the
morphosyntactic locus of the marking, its valency effect, and where reciprocal
verbs are formed. Graduated from the dissolved `Typology/ArgumentStructure`
drawer (whose unconsumed passive/antipassive/applicative/causative/ditransitive
apparatus was dropped); consumed by [nordlinger-2023] and Siloni 2012.

## Main definitions

* `ReciprocalType` — reciprocal/reflexive formal relation (WALS Ch 106).
* `RecipStrategy` + `RecipStrategy.isNominal` — the morphosyntactic locus.
* `RecipValency` — valency effect (bivalent vs monovalent).
* `RecipFormation` + `RecipFormation.allowsDiscontinuous` — lexical vs syntactic.
* `fromWALS106A` — WALS Ch 106 converter.
-/

namespace Reciprocal

/-- WALS Ch 106: How reciprocal situations are encoded relative to reflexives.

    The four values follow [maslova-nedjalkov-2013]'s classification:

    - `noDedicated`: "There are no non-iconic reciprocal constructions" --
      the language lacks a dedicated grammatical reciprocal marker.
    - `distinctFromReflexive`: "All reciprocal constructions are formally
      distinct from reflexive constructions" (e.g. English "each other" vs
      "themselves").
    - `mixed`: "There are both reflexive and non-reflexive reciprocal
      constructions" -- the language has both a reflexive-identical strategy
      and a formally distinct one (e.g. German "sich" + "einander").
      Common in Europe.
    - `identicalToReflexive`: "The reciprocal and reflexive constructions
      are formally identical" (e.g. Imbabura Quechua "-ri",
      West Greenlandic "-ssin-"). -/
inductive ReciprocalType where
  | noDedicated
  | distinctFromReflexive
  | mixed
  | identicalToReflexive
  deriving DecidableEq, Repr

instance : Inhabited ReciprocalType := ⟨.noDedicated⟩

/-- Morphosyntactic strategy for encoding reciprocity.

    [nordlinger-2023] summarizes the structural typologies of
    König & Kokutani (2006), Nedjalkov (2007a), and Evans (2008), which
    classify reciprocal constructions by the morphosyntactic locus
    of the reciprocal marking:

    - `bipartiteNP`: Bipartite quantifier NP -- English "each other",
      Icelandic "hvor...annad" (two independently inflected parts).
    - `recipPronoun`: Reciprocal pronoun -- Russian "drug druga",
      Hausa "jùnan-mù". Free-standing pronominal form in object position.
    - `recipClitic`: Reciprocal clitic -- French/Czech "se",
      Wambaya "-ngg-" (RR morpheme in auxiliary). Intermediate between
      pronoun and affix; functionally verbal (valence-reducing in most
      cases, though Wambaya retains bivalent syntax via ergative case).
    - `verbalAffix`: Morphological marking on the verb -- Swahili "-ana",
      Hungarian "-oz-", Chicheŵa "-an-". Derives an intransitive
      (monovalent) verb from a transitive base.
    - `verbalAuxiliary`: Reciprocal auxiliary -- Warrwa "wanji-" replaces
      the regular transitive auxiliary.
    - `lexical`: Inherently reciprocal predicate -- English "quarrel",
      "meet". The symmetric meaning is part of the verb's lexical semantics.
    - `compoundVerb`: Compound verb -- Mandarin "dǎ-lái-dǎ-qù"
      (beat-come-beat-go = 'beat each other'). -/
inductive RecipStrategy where
  | bipartiteNP
  | recipPronoun
  | recipClitic
  | verbalAffix
  | verbalAuxiliary
  | lexical
  | compoundVerb
  deriving DecidableEq, Repr

/-- Whether the strategy marks the NP/argument position (nominal strategy)
    or the verb/predicate (verbal strategy).
    König & Kokutani (2006)'s primary typological distinction.

    Clitics are classified as non-nominal: Evans (2008) treats them as
    intermediate, but their valence behavior is typically verbal --
    French/Czech "se" reduces valence (monovalent), and even Wambaya
    "-ngg-" is morphologically bound to the auxiliary. -/
def RecipStrategy.isNominal : RecipStrategy → Bool
  | .bipartiteNP     => true
  | .recipPronoun    => true
  | .recipClitic     => false
  | .verbalAffix     => false
  | .verbalAuxiliary => false
  | .lexical         => false
  | .compoundVerb    => false

/-- Valency effect of reciprocal construction on the base predicate.

    Maslova (2008) distinguishes "unary" and "binary" reciprocals;
    [nordlinger-2023] discusses how NP/argument strategies tend to
    preserve valency while verb-marked strategies tend to reduce it. The
    correlation is a tendency, not absolute -- Malagasy verb-marked
    reciprocals retain full valency at f-structure (Hurst 2006, 2012). -/
inductive RecipValency where
  | bivalent    -- two syntactic arguments preserved
  | monovalent  -- verb becomes intransitive (single subject NP)
  deriving DecidableEq, Repr

/-- Where reciprocal verbs are formed, per Siloni (2008, 2012).

    [nordlinger-2023] discusses Siloni's distinction:
    - `lexical`: formed in the lexicon through "bundling" -- two thematic
      roles (agent, patient) merge into a single complex role. Produces
      verbs with inherently symmetric semantics. Can license discontinuous
      reciprocal constructions (subject + comitative argument).
    - `syntactic`: formed in the syntax via an operation that creates
      the symmetric reading. Cannot license discontinuous reciprocals.

    Key empirical prediction: discontinuous reciprocals ("John kissed
    with Mary") are possible only with lexically-formed reciprocal verbs. -/
inductive RecipFormation where
  | lexical
  | syntactic
  deriving DecidableEq, Repr

/-- Can the reciprocal construction appear in discontinuous form
    (reciprocants split across subject and comitative argument)?
    [nordlinger-2023] §3.3. -/
def RecipFormation.allowsDiscontinuous : RecipFormation → Bool
  | .lexical   => true
  | .syntactic => false

/-! ### WALS converter -/

/-- Convert WALS 106A value to `ReciprocalType`. -/
def fromWALS106A : Data.WALS.F106A.ReciprocalType → ReciprocalType
  | .noReciprocalConstruction => .noDedicated
  | .distinctFromReflexive    => .distinctFromReflexive
  | .mixed                    => .mixed
  | .identicalToReflexive     => .identicalToReflexive


end Reciprocal
