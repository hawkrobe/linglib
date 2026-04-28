import Mathlib.Tactic.DeriveFintype

/-!
# Bybee 1985 Ch 5: Dynamic Network Model of Lexical Representation
@cite{bybee-1985}

This file formalizes the substrate of Bybee 1985 Ch 5 ("Two Principles in
a Dynamic Model of Lexical Representation," pp. 111-135). It is a peer-
framework directory alongside `Theories/Morphology/{DM, PFM, WP,
Nanosyntax, FragmentGrammars}/` — Bybee's network model is *the*
usage-based competitor to the realisational and generative camps, and the
audit (4-agent, 0.230.453) flagged its absence as the most important
architectural gap in linglib's morphology layer.

## The Two Principles

Bybee abandons the structuralist/generative "is it in the lexicon or
not?" binary (p. 116) and proposes two gradient + dynamic notions:

1. **Lexical strength** (§4 p. 117): each item entered in the lexicon
   has a strength that grows with each token of use ("etching it with
   deeper and darker lines each time"). Strength can also decline with
   disuse. Strength accounts for autonomy effects (Ch 3): high-strength
   items can be processed unanalyzed, retain irregularity, undergo
   inflectional split, develop fused/contracted forms.

2. **Lexical connection** (§5 pp. 118-119): each item bears multiple
   typed connections to other items. Three closeness factors:
   (a) *number/nature of shared semantic features*; (b) *phonological
   similarity*; (c) *word frequency* (high-frequency items form *more
   distant* connections — they're processed unanalyzed and don't lean
   on related items). The strongest non-identity relation is the
   **morphological relation** = parallel semantic + phonological
   connections. Identity (§7 p. 124) is the strongest possible relation:
   non-autonomous items map onto an existing representation rather than
   getting their own.

## Five empirical phenomena lexical strength accounts for (§6)

(p. 119-122): (i) maintenance of irregularity in high-frequency forms;
(ii) high-frequency synthesis/fusion (English *says/has/does*; Spanish
*dar*); (iii) lexical and inflectional split (*wend/went* split, *supposed*
→ *spowsta*); (iv) local markedness (Tiersma 1982 — a "derived" form
becomes the basic one when more frequent); (v) development of contracted
forms (*don't*, *won't* — Zwicky-Pullum 1983).

## What this file does NOT cover

- Ch 5 §10 morphological classes as emergent from network connection
  density — deferred to a future `SchemaInduction.lean` sibling
- Ch 5 §11 productivity from class size + variance — deferred
- Cross-framework refutation theorem against DM (the bridge the
  cross-framework reconciler proposed: a paradigm where DM's
  `subsetPrinciple` predicts identical output but Bybee's strength
  predicts divergent retention) — deferred to a study file

## Architectural commitments encoded here

This substrate **commits** Bybee's central architectural claim:
representations + connections form a *graph* where rules emerge from
connection density, NOT a lexicon-rule binary. This is incompatible
with DM's late-insertion-only architecture (HM 1993) and with PFM's
realization-rule-only architecture (Stump 2001). Consumers that mix
this substrate with DM/PFM should use bridge theorems in study files,
not silently coexist.

-/

namespace Theories.Morphology.UsageBased

-- ============================================================================
-- §1: Lexical Entries (Bybee Ch 5 §4 — "lexical strength")
-- ============================================================================

/-- A stored lexical item in Bybee's dynamic network.

`tokenFreq` is the empirical token count — Bybee Ch 5 §4 p. 117 grounds
strength in repeated processing ("each time a word is heard and produced
it leaves a slight trace on the lexicon, it increases in lexical
strength"). The strength projection below is a monotonically-increasing
function of this count.

The meaning type `α` is polymorphic to admit Bool/PMF/structured
semantic backends — Bybee herself is agnostic about meaning
representation; the network model concerns *organization*, not the
representation primitive. -/
structure LexicalEntry (α : Type) where
  /-- Phonological form. -/
  form : String
  /-- Meaning. -/
  meaning : α
  /-- Empirical token frequency. Bybee §4: strength accumulates with
      each token of use; with disuse, strength declines. We model the
      synchronic snapshot as `tokenFreq` and decline as a monotonic
      decreasing function of time-since-last-use (not modeled here). -/
  tokenFreq : Nat
  deriving Repr

/-- Lexical strength as a function of token frequency. The exact shape
    is unspecified by Bybee Ch 5 §4 ("each time… etching it with deeper
    and darker lines"); we use the identity to keep `decide`
    tractable, but consumers may quotient by any monotonic function. -/
def LexicalEntry.strength {α : Type} (e : LexicalEntry α) : Nat :=
  e.tokenFreq

/-- Strength is monotonic in token frequency. -/
theorem LexicalEntry.strength_monotonic {α : Type} (e₁ e₂ : LexicalEntry α)
    (h : e₁.tokenFreq ≤ e₂.tokenFreq) : e₁.strength ≤ e₂.strength := h

-- ============================================================================
-- §2: Connection Types (Bybee Ch 5 §5 — "lexical connection")
-- ============================================================================

/-- The kind of connection between two lexical entries (Ch 5 §5).

Bybee distinguishes:

- **Semantic** — shared semantic features (*table* and *chair* both in
  the supercategory *furniture*; *deep* and *shallow* opposite ends of
  one dimension; *doctor*/*nurse*/*hospital*/*operate* in the same scene)
- **Phonological** — shared phonological skeleton without shared
  meaning (the two senses of *crane*; homophonous forms — Bybee notes
  these connections "usually go unnoticed")
- **Morphological** — *parallel* semantic + phonological connections;
  Bybee Ch 5 §5 p. 118: "if two words are related by both semantic
  and phonological connections, then a morphological relation exists"
- **Identity** — Ch 5 §7 p. 124: "the strongest relations are
  relations of identity. Relations of identity lead to non-autonomous
  representations, the mapping of one word onto an existing
  representation, strengthening it." -/
inductive ConnectionKind where
  | semantic
  | phonological
  | morphological
  | identity
  deriving DecidableEq, Repr, Fintype

/-- The relative strength of connection kinds (Ch 5 §7 p. 124: identity
    strongest; §5 p. 118: morphological is the strongest non-identity
    relation). The numerical embedding is convenience; the substantive
    content is the order. Ties between `.semantic` and `.phonological`
    reflect Bybee's claim that the *combination* (`.morphological`) is
    what's strong, not either component alone. -/
def ConnectionKind.relativeStrength : ConnectionKind → Nat
  | .semantic       => 1
  | .phonological   => 1
  | .morphological  => 2
  | .identity       => 3

/-- Identity is strictly the strongest connection kind. -/
theorem ConnectionKind.identity_strongest (k : ConnectionKind) (h : k ≠ .identity) :
    k.relativeStrength < ConnectionKind.identity.relativeStrength := by
  cases k <;> simp_all [relativeStrength]

/-- Among non-identity kinds, morphological is the strongest. -/
theorem ConnectionKind.morphological_strongest_non_identity
    (k : ConnectionKind) (h₁ : k ≠ .identity) (h₂ : k ≠ .morphological) :
    k.relativeStrength < ConnectionKind.morphological.relativeStrength := by
  cases k <;> simp_all [relativeStrength]

-- ============================================================================
-- §3: Connections (typed edges in the network)
-- ============================================================================

/-- A directed typed edge in the lexical network. We use `String`-keyed
    endpoints so that connections are independent of which copy of an
    entry one is referring to (useful when networks are constructed
    from multiple sources). -/
structure Connection where
  src : String
  dst : String
  kind : ConnectionKind
  deriving DecidableEq, Repr

-- ============================================================================
-- §4: Network (Ch 5 §8 "representation of a complex paradigm")
-- ============================================================================

/-- A lexical network: a finite set of entries plus a finite set of
    typed connections among them (Ch 5 §8 p. 124 representation of
    Spanish *dormir* shows three stem allomorphs `dwerm`/`dorm`/`durmy`
    connected by morphological relations across persons/numbers/tenses).

    The network is intentionally finite + decide-friendly so that
    cross-linguistic + diachronic claims (Ch 5 §6) can be checked
    structurally. -/
structure Network (α : Type) where
  entries : List (LexicalEntry α)
  connections : List Connection
  deriving Repr

/-- Membership in the network's entry list. -/
def Network.contains {α : Type} [DecidableEq α] (N : Network α) (form : String) : Bool :=
  N.entries.any (·.form == form)

/-- Lookup an entry by form. -/
def Network.lookup {α : Type} (N : Network α) (form : String) :
    Option (LexicalEntry α) :=
  N.entries.find? (·.form == form)

-- ============================================================================
-- §5: Connection Predicates and Morphological Relation
-- ============================================================================

/-- `N.IsRelatedBy a b k` holds when there is a connection of kind `k`
    from form `a` to form `b` in network `N`. The Prop form (rather
    than Bool) is the canonical mathlib pattern for relations one
    wants to *reason about*; `Decidable` is derived for finite networks. -/
def Network.IsRelatedBy {α : Type} (N : Network α)
    (a b : String) (k : ConnectionKind) : Prop :=
  ∃ c ∈ N.connections, c.src = a ∧ c.dst = b ∧ c.kind = k

instance {α : Type} (N : Network α) (a b : String) (k : ConnectionKind) :
    Decidable (N.IsRelatedBy a b k) :=
  inferInstanceAs (Decidable (∃ _ ∈ N.connections, _))

/-- Bybee Ch 5 §5 p. 118: a morphological relation between two forms
    holds **iff** there is both a semantic and a phonological connection.

    This is the substantive compositional claim — morphological
    relatedness is *not* a primitive connection kind, it is *derived*
    from the existence of two parallel connections (semantic and
    phonological). The `ConnectionKind.morphological` constructor is a
    convenience label for edges users have already classified; the
    network-level relation is the conjunction defined here.

    Per the CLAUDE.md "derive don't duplicate" pattern, this is the
    canonical morphological-relation predicate; users should not
    define their own. -/
def Network.HasMorphologicalRelation {α : Type} (N : Network α)
    (a b : String) : Prop :=
  N.IsRelatedBy a b .semantic ∧ N.IsRelatedBy a b .phonological

instance {α : Type} (N : Network α) (a b : String) :
    Decidable (N.HasMorphologicalRelation a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================================
-- §6: Empirical Anchor — English Strong-Verb Frequencies
--     (Bybee Ch 5 §6 p. 120, Sweet's Anglo Saxon Primer Class I/II/VII)
-- ============================================================================

/-! Bybee's central diachronic claim (§6 pp. 119-120): high-frequency
strong verbs maintain their irregularity; low-frequency strong verbs
regularize. The data comes from comparing modern descendants of Old
English Strong Verbs in classes I, II, and VII against their Francis &
Kučera 1982 token-frequency counts.

We model each verb as a `LexicalEntry Unit` (we don't formalize meaning
here — the substantive claim is about strength, not denotation), with
`tokenFreq` set to Bybee's reported count. The theorem
`strong_verbs_higher_frequency_than_regularized` then becomes a decidable
property of the dataset.

Verified against Bybee 1985 p. 120 — frequencies are all-forms counts
from Francis & Kučera 1982, except `slit*` and `beat*` which now take
the zero-allomorph (Bybee's footnote). -/

private def mkEntry (form : String) (freq : Nat) : LexicalEntry Unit :=
  ⟨form, (), freq⟩

/-- Bybee's "Strong verbs that have stayed Strong" from p. 120 (classes
    I, II, VII). Verified token frequencies. -/
def strongStillStrong : List (LexicalEntry Unit) := [
  -- Class I (mean freq 223)
  mkEntry "drive" 203, mkEntry "rise" 199, mkEntry "ride" 126,
  mkEntry "write" 561, mkEntry "bite" 26,
  -- Class II (mean freq 140)
  mkEntry "choose" 177, mkEntry "fly" 92, mkEntry "shoot" 117,
  mkEntry "lose" 274, mkEntry "flee" 40,
  -- Class VII (mean freq 515)
  mkEntry "fall" 239, mkEntry "hold" 509, mkEntry "know" 1473,
  mkEntry "grow" 300, mkEntry "blow" 52
]

/-- Bybee's "Strong verbs that have regularized or become Weak" from
    p. 120 (classes I, II, VII). Verified token frequencies. -/
def strongRegularized : List (LexicalEntry Unit) := [
  -- Class I (mean freq 5)
  mkEntry "bide" 1, mkEntry "reap" 5, mkEntry "slit" 3, mkEntry "sneak" 11,
  -- Class II (mean freq 22)
  mkEntry "rue" 0, mkEntry "seethe" 0, mkEntry "smoke" 26,
  mkEntry "float" 23, mkEntry "shove" 16,
  -- Class VII (mean freq 21)
  mkEntry "wax" 6, mkEntry "weep" 28, mkEntry "beat" 66, mkEntry "hew" 1,
  mkEntry "leap" 33, mkEntry "mow" 1, mkEntry "sow" 6, mkEntry "flow" 40,
  mkEntry "row" 5
]

/-- The mean token frequency of Strong-verbs-that-stayed-Strong is
    *strictly greater* than the mean of Strong-verbs-that-regularized.

    This is Bybee's central diachronic claim — irregularity correlates
    with high frequency; low-frequency irregulars regularize. The means
    Bybee reports per class are 223/5 (Class I), 140/22 (Class II),
    515/21 (Class VII). Aggregating across classes:

      stayed-Strong: (203+199+126+561+26 + 177+92+117+274+40 +
                      239+509+1473+300+52) / 15 = 4388/15 ≈ 292
      regularized:   (1+5+3+11 + 0+0+26+23+16 + 6+28+66+1+33+1+6+40+5)
                     / 18 = 271/18 ≈ 15

    We compare sums (avoiding rational arithmetic): if mean₁ > mean₂
    and the populations differ in size, then sum₁ × |pop₂| >
    sum₂ × |pop₁|. -/
theorem strong_verbs_higher_frequency_than_regularized :
    (strongStillStrong.map (·.tokenFreq)).sum * strongRegularized.length
    > (strongRegularized.map (·.tokenFreq)).sum * strongStillStrong.length := by
  decide

/-- Equivalent reformulation: the average-bound version. The product
    inequality above is logically equivalent to mean₁ > mean₂ when
    both populations are non-empty (we avoid Rat to keep `decide`
    cheap). -/
theorem strongStillStrong_nonempty : strongStillStrong.length > 0 := by decide

theorem strongRegularized_nonempty : strongRegularized.length > 0 := by decide

end Theories.Morphology.UsageBased
