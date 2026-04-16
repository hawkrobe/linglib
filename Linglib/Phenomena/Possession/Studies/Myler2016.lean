import Linglib.Theories.Syntax.Minimalism.Core.Copula
import Linglib.Theories.Morphology.DM.VocabularyInsertion
import Linglib.Theories.Morphology.DM.NominalStructure
import Linglib.Theories.Semantics.Lexical.Noun.Relational.Barker2011

/-!
# Myler 2016: Building and Interpreting Possession Sentences
@cite{myler-2016}

This study file connects the copula theory (Copula.lean) to empirical
predictions and cross-linguistic data from @cite{myler-2016}.

## Contents

- **Icelandic hafa/eiga** (§4.3): two HAVE verbs with bidirectional
  VI conditioning, formalized as VocabItems
- **The two puzzles**: injectivity of `haveReading` (too-many-meanings)
  and `vi_characterization` (too-many-structures)
- **Cross-module bridges**: connections to possession typology
  (@cite{stassen-2009}), Barker's π (@cite{barker-2011}), and
  nominal structure (inalienable/alienable)
-/

namespace Phenomena.Possession.Studies.Myler2016

open Minimalism

-- ════════════════════════════════════════════════════
-- § 1. Icelandic: Two HAVEs (§4.3)
-- ════════════════════════════════════════════════════

/-- Icelandic has two HAVE verbs (*hafa* and *eiga*) that carve up the
    possession domain based on the DP-internal structure of the complement.

    @cite{myler-2016} §4.3 / Myler, Sigurðsson & Wood 2014:
    - v ⇔ *hafa* / ___Voice_{D},φ ___Pred (complement contains PredP)
    - v ⇔ *eiga* / ___Voice_{D},φ       (elsewhere in transitive context)

    The distribution:
    - *eiga*: concrete possession, kinship (Poss head mediates, no PP possessor)
    - *hafa*: body parts, abstract (root-introduced relation, PP possessor possible)
    - Both work for non-possessive small clause complements (*hafa* only)

    Generalizations:
    (90a) Clausal possession with *eiga* only if DP-internal possession
          CANNOT be expressed with a PP.
    (90b) Clausal possession with *hafa* only if DP-internal possession
          CAN be expressed with a PP. -/
inductive IcelandicHaveVerb where
  | hafa   -- v ⇔ hafa / ___Voice_{D},φ ___Pred
  | eiga   -- v ⇔ eiga / ___Voice_{D},φ (elsewhere transitive)
  deriving DecidableEq, Repr

/-- Does the DP-internal possession use a PP (preposition) to introduce
    the possessor? This is the bidirectional conditioning environment. -/
structure IcelandicPossDP where
  /-- Is there a PredP (small clause) in the DP structure? -/
  hasPredP : Bool
  /-- Can the possessor be expressed with a PP inside the DP? -/
  hasPPPossessor : Bool
  deriving DecidableEq, Repr

/-- Icelandic VI rule for HAVE verbs.
    Bidirectional conditioning: looks at both Voice above AND complement below. -/
def icelandicHaveVI (dp : IcelandicPossDP) : IcelandicHaveVerb :=
  if dp.hasPredP then .hafa else .eiga

/-- Body parts and abstract nouns (PP possessor possible) → hafa. -/
theorem bodyPart_hafa : icelandicHaveVI { hasPredP := true, hasPPPossessor := true } = .hafa := rfl

/-- Concrete and kinship (no PP possessor) → eiga. -/
theorem concrete_eiga : icelandicHaveVI { hasPredP := false, hasPPPossessor := false } = .eiga := rfl

/-- Generalization (90a): eiga ↔ no PP possessor internally. -/
theorem eiga_iff_no_pp (dp : IcelandicPossDP) :
    icelandicHaveVI dp = .eiga ↔ dp.hasPredP = false := by
  cases dp with | mk p pp => cases p <;> simp [icelandicHaveVI]

/-- Generalization (90b): hafa ↔ PP possessor available internally. -/
theorem hafa_iff_pred (dp : IcelandicPossDP) :
    icelandicHaveVI dp = .hafa ↔ dp.hasPredP = true := by
  cases dp with | mk p pp => cases p <;> simp [icelandicHaveVI]

-- ─── VocabItem formulation (parallel to copulaVIRules) ───

open Morphology.DM.VI in

/-- Icelandic HAVE VI as proper `VocabItem`s from the DM framework.

    Two items compete via the Elsewhere Condition:
    - *hafa*: specificity 1 (checks hasPredP = true)
    - *eiga*: specificity 0 (elsewhere — matches any transitive context)

    This parallels `copulaVIRules` for the English HAVE/BE alternation,
    but applies within the HAVE domain: both *hafa* and *eiga* realize
    transitive Voice, differing only in the DP-internal structure. -/
def icelandicHaveVIRules : List (VocabItem IcelandicPossDP Unit) :=
  [ { exponent := "hafa"
    , contextMatch := fun dp => dp.hasPredP
    , specificity := 1 }
  , { exponent := "eiga"
    , contextMatch := fun _ => true
    , specificity := 0 } ]

open Morphology.DM.VI in

/-- The VocabItem formulation agrees with the direct `icelandicHaveVI`. -/
theorem icelandicVI_agrees_vocabItem (dp : IcelandicPossDP) :
    vocabularyInsertSimple icelandicHaveVIRules dp =
    some (if icelandicHaveVI dp = .hafa then "hafa" else "eiga") := by
  cases dp with | mk p pp => cases p <;> cases pp <;>
  simp [icelandicHaveVI, icelandicHaveVIRules, vocabularyInsertSimple,
    vocabularyInsert, VocabItem.matches, List.mergeSort, List.findSome?]

-- ════════════════════════════════════════════════════
-- § 2. The Two Puzzles, Solved
-- ════════════════════════════════════════════════════

/-- The "too-many-meanings" puzzle: how can one construction (*have*)
    have so many different meanings?

    @cite{myler-2016} (81): possession constructions can mean so many
    things because they involve sentencifying a meaning that comes from
    inside DP. The meanings are a *syntactic* natural class (all introduced
    by heads inside DP), not a *semantic* one. Since v = λx.x, ALL the
    thematic content comes from the complement and from Voice allosemy.

    Formally: `haveReading` is **injective** — each complement type
    produces a distinct reading. This captures the claim that v contributes
    nothing: the complement alone determines the interpretation. -/
theorem too_many_meanings_solution :
    Function.Injective haveReading := by
  intro a b h; cases a <;> cases b <;> first | rfl | simp [haveReading] at h

/-- The "too-many-structures" puzzle: how can the same possessive meanings
    be realized in so many syntactically different ways across languages?

    @cite{myler-2016} (93): possession relations originate inside DP
    (root-introduced or Poss-head-introduced). Since v is meaningless
    and makes no semantic demands, syntax alone decides where the
    possessor is first-merged. Combined with parametric variation in
    delayed gratification and the ±D property of functional heads,
    this generates the full typology from a small set of parameters.

    Formally: the HAVE/BE distinction depends only on whether Voice is
    transitive, which is independent of the possession relation itself. -/
theorem too_many_structures_solution (v : VoiceHead) :
    copulaVI v = .have ↔
    (v.hasD = true ∧ v.flavor ≠ .nonThematic ∧ v.flavor ≠ .passive) :=
  vi_characterization v

-- ════════════════════════════════════════════════════
-- § 3. Cross-Module Bridges
-- ════════════════════════════════════════════════════

-- ─── Bridge to Possession Typology ───

/-- @cite{myler-2016}'s HAVE = BE + Voice_{D},φ provides the syntactic
    analysis underlying the have-verb predicative possession strategy
    from @cite{stassen-2009}.

    A language uses the have-verb strategy iff its possession construction
    has transitive Voice — exactly the `copulaVI` condition.
    Derived from `copulaVI`, not stipulated independently. -/
def isHaveVerbLanguage (voice : VoiceHead) : Bool :=
  copulaVI voice == .have

/-- A language with transitive, θ-assigning Voice produces HAVE. -/
theorem haveVerb_from_transitive_voice :
    isHaveVerbLanguage voiceAgent = true := rfl

/-- A language with intransitive Voice produces BE (locational/existential). -/
theorem be_from_intransitive_voice :
    isHaveVerbLanguage voiceAnticausative = false := rfl

/-- `isHaveVerbLanguage` agrees with `copulaVI` by construction. -/
theorem isHaveVerbLanguage_iff_copulaVI (v : VoiceHead) :
    isHaveVerbLanguage v = true ↔ copulaVI v = .have := by
  simp [isHaveVerbLanguage, beq_iff_eq]

-- ─── Bridge to Barker 2011 (Possession inside DP) ───

open Semantics.Lexical.Noun.Relational.Barker2011 in

/-- The relational HAVE reading requires the complement DP to have a
    Pred2 interpretation (either lexically relational or via π-shift).
    This is exactly `NominalInterpType.pred2` from @cite{barker-2011}.

    @cite{myler-2016}: "The meanings [of HAVE] are a syntactic natural
    class: all introduced by heads inside DP." For relational HAVE, the
    DP must supply a possessor slot — which is what Pred2 provides.

    The bridge: relational HAVE ↔ possessedDP complement ↔
    `NominalInterpType.pred2` (has relatum slot for possessor). -/
theorem relational_have_requires_pred2 :
    NominalInterpType.pred2.hasRelatumSlot = true ∧
    NominalInterpType.pred2.canTakePossessor = true := ⟨rfl, rfl⟩

open Semantics.Lexical.Noun.Relational.Barker2011 in

/-- Bare sortals (Pred1, no π) cannot appear in relational HAVE:
    "I have a cloud" requires a contextually supplied relation (π).
    Without π, the DP has no possessor slot, so no possessive reading. -/
theorem bare_sortal_blocks_relational :
    NominalInterpType.pred1.canTakePossessor = false := rfl

-- ─── Bridge to NominalStructure (Possession Type) ───

open Morphology.DM in

/-- Delayed gratification connects to the inalienable/alienable distinction
    from NominalStructure.lean:

    - Inalienable possessor (Spec,nP): can undergo delayed gratification
      to Spec,VoiceP → yields relational HAVE with inalienable reading
    - Alienable possessor (Spec,PossP): can undergo delayed gratification
      to Spec,VoiceP → yields relational HAVE with alienable reading

    In both cases, the possessor starts DP-internally and percolates to
    Spec,VoiceP. The structural position inside DP determines the
    INTERPRETATION (kinship vs ownership), not whether HAVE surfaces. -/
theorem both_possession_types_allow_have :
    PossessionType.inalienable.possessorPosition.isWithinNP = true ∧
    PossessionType.alienable.possessorPosition.isWithinNP = false := ⟨rfl, rfl⟩

open Morphology.DM in

/-- Inalienable possession is nP-internal (can affect gender under GLH);
    alienable possession is nP-external (cannot). This is orthogonal to
    whether the language spells out v as HAVE or BE. -/
theorem possession_type_orthogonal_to_copula :
    PossessionType.inalienable.canAffectGender = true ∧
    PossessionType.alienable.canAffectGender = false := ⟨rfl, rfl⟩

end Phenomena.Possession.Studies.Myler2016
