import Linglib.Features.Complementation

/-!
# Adyghe Clausal Embedding Inventory

[caponigro-polinsky-2011]

Adyghe (Northwest Caucasian, ISO 639-3 `ady`) inventory of
complement-taking predicates. [caponigro-polinsky-2011]'s central
descriptive result: Adyghe has no embedded declaratives or embedded
polar interrogatives — every *tensed* notional complement is a relative
construction inside a DP ((96) vs (98)), while a smaller class of
volitional and aspectual predicates takes infinitival/converbal TPs
(their §8). The construction imposes no presuppositional restriction
(their §6.5) — pace the relative *fact*-clause characterization they
cite from Gerasimov & Lander.

Factivity values are textbook consensus for the predicate concepts —
[caponigro-polinsky-2011] run no per-predicate projection tests; their
only factivity-relevant claim is the construction-level one above.
Forms follow the paper's transliteration (ʷ marks labialization, ʼ
ejectives, ə schwa).
-/

namespace Adyghe.Clause

/-! ### Predicate schema -/

/-- Status of the high applicative *re-* on a predicate's
    notional-complement verb ([caponigro-polinsky-2011] §6.3): *re-* is
    the only applicative confined to relative constructions, occurs
    outermost in the applicative field, and — always adjacent to the
    relativizer *ze-* — distinguishes proposition-denoting embeddings
    from ordinary relatives. -/
inductive HighApplicative where
  /-- Every attested notional complement carries *ze-re-*. -/
  | required
  /-- Attested with and without *re-*, tracking the polar-question vs
      constituent-question reading ((99) vs (69)), not free variation. -/
  | readingConditioned
  /-- The predicate takes an infinitival/converbal TP, not a relative
      clause — the volitional/aspectual class of their §8. -/
  | notApplicable
  deriving DecidableEq, Repr

/-- Case suffix on the complement DP's right edge: absolutive *-r* vs
    oblique *-m*, "which depends on the different case assigning
    properties of the respective main predicate" ((98) vs (99)).
    Caveat ([caponigro-polinsky-2011] §2.2.3): Adyghe has an extensive
    middle class taking absolutive subject + oblique object, so this
    split may reduce to matrix valence. -/
inductive ComplementCase where
  | abs
  | obl
  deriving DecidableEq, Repr

/-- An Adyghe complement-taking predicate.

    - `ctpClass`: [noonan-2007] category; `none` where unclear.
    - `factive`: textbook consensus for the predicate concept (see
      module docstring — not a [caponigro-polinsky-2011] claim).
    - `highApplicative`, `complementCase`: the morphological
      observables. -/
structure AdygheEmbedder where
  form : String
  gloss : String
  ctpClass : Option CTPClass
  factive : Option Bool
  highApplicative : HighApplicative
  complementCase : Option ComplementCase
  deriving DecidableEq, Repr

/-! ### Relative-strategy predicates

Tensed notional complements: a DP-wrapped relative clause whose verb
carries *ze-re-*. -/

/-- *gʷəpšəsa* 'think'. The bare finite complement is ungrammatical
    ((96)); the relative-construction complement is fine ((98)); plain
    DP objects attested ((102)). [caponigro-polinsky-2011] §6.2. -/
def gwepshesa : AdygheEmbedder where
  form := "gʷəpšəsa"; gloss := "think"
  ctpClass := some .propAttitude
  factive := some false
  highApplicative := .required
  complementCase := some .abs

/-- *qəč'ewəpč'a* 'ask'. Constituent-question complements carry the
    relativizer without *re-* ((69)); polar complements carry *ze-re-*
    ((99)); direct embedding of a matrix interrogative is out ((97)).
    Plain DP objects attested ((103)). [caponigro-polinsky-2011] §§5,
    6.2. -/
def chewepcha : AdygheEmbedder where
  form := "qəč'ewəpč'a"; gloss := "ask"
  ctpClass := some .utterance
  factive := some false
  highApplicative := .readingConditioned
  complementCase := some .obl

/-- *ŝe* (also *jeŝe*) 'know'. One *ze-re-* complement is ambiguous
    between declarative and interrogative readings ((101)); the
    complement is a strong island ((104)–(106)).
    [caponigro-polinsky-2011] §6.2. -/
def she : AdygheEmbedder where
  form := "ŝe"; gloss := "know"
  ctpClass := some .knowledge
  factive := some true
  highApplicative := .required
  complementCase := some .abs

/-- *gʷərəʔʷe* 'understand'. Its *ze-re-* complement is
    truth-conditionally equivalent with and without an overt nominal
    head — *qeba* 'news', *ŝəpqə* 'verity' ((108)–(110)) — the paper's
    argument for a silent N in the shell. [caponigro-polinsky-2011]
    §6.3. -/
def gwereqwe : AdygheEmbedder where
  form := "gʷərəʔʷe"; gloss := "understand"
  ctpClass := some .knowledge
  factive := some true
  highApplicative := .required
  complementCase := some .abs

/-- *ʔʷa* 'say', with a *ze-re-* complement in §3.1's footnote example
    (ii). [caponigro-polinsky-2011]. -/
def qwa : AdygheEmbedder where
  form := "ʔʷa"; gloss := "say"
  ctpClass := some .utterance
  factive := some false
  highApplicative := .required
  complementCase := some .abs

/-! ### Infinitival-strategy predicates

The volitional and aspectual class takes infinitival/converbal TPs, not
relative clauses ([caponigro-polinsky-2011] §8, citing Polinsky &
Potsdam). -/

-- UNVERIFIED: transliteration of the form in (54) not yet checked
-- against the typeset article.
/-- *raʔežʼa* 'begin' — aspectual, infinitival TP complement
    (*-new* infinitive, (54); the star on (54) targets the possessive
    marker, not the complement). [caponigro-polinsky-2011] §2.3, §8. -/
def raqezha : AdygheEmbedder where
  form := "raʔežʼa"; gloss := "begin"
  ctpClass := some .phasal
  factive := none
  highApplicative := .notApplicable
  complementCase := none

/-! ### Inventories -/

/-- The complement-taking predicates with quotable per-predicate data
    in [caponigro-polinsky-2011]. -/
def allEmbedders : List AdygheEmbedder :=
  [gwepshesa, chewepcha, she, gwereqwe, qwa, raqezha]

/-- The predicates whose tensed complements use the relative strategy. -/
def relativeTakers : List AdygheEmbedder :=
  allEmbedders.filter (·.highApplicative != .notApplicable)

/-- Drift sentry: the relative-strategy predicates are exactly the five
    tensed-complement-takers. -/
theorem relativeTakers_membership :
    relativeTakers = [gwepshesa, chewepcha, she, gwereqwe, qwa] := by
  decide

/-- The relative strategy is factivity-blind: it is required both for
    consensus-factive 'know'/'understand' and consensus-non-factive
    'think'/'say' ([caponigro-polinsky-2011] §6.5: the construction has
    no presuppositional restriction). -/
theorem relative_strategy_factivity_blind :
    (∃ v ∈ relativeTakers, v.factive = some true) ∧
    (∃ v ∈ relativeTakers, v.factive = some false) := by
  refine ⟨?_, ?_⟩ <;> decide

end Adyghe.Clause
