import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Topic — Aboutness and Contrastive Topics
[reinhart-1981] [buring-2003] [krifka-2008]

Substrate type for the **Topic** axis of information structure, one
of the four IS notions Krifka 2008 enumerates (focus, givenness,
topic, delimitation; see `Features/Givenness.lean` for the broader
discussion of how at-issueness sits orthogonally to Krifka's four).
[fery-ishihara-2016] (Oxford Handbook of Information Structure)
follows Krifka in treating topic as a primitive notion, defined per
[krifka-2008]:

> The topic constituent identifies the entity or set of entities
> under which the information expressed in the comment constituent
> should be stored in the CommonGround content.

Following [reinhart-1981]'s file-card metaphor: the CommonGround is
organized like a subject-oriented library catalogue indexed by
topics; each new proposition is filed under the topic it is about.

## What's here

- `TopicMark` — binary aboutness marking. Whether a constituent is
  the (Reinhart) aboutness topic or not. Substrate hook for studies
  that need to annotate constituents as topical.
- `ContrastiveTopic α` — placeholder structure for Büring-style
  contrastive topic, mirroring `Features.InformationStructure.Focus`
  shape (a marked element with a list of alternatives). Not enough
  yet to formalize Büring 2003's full [T,F]-marking calculus, but
  enough to type lexical entries that bear contrastive-topic
  marking.

## What's not here

This file deliberately does NOT formalize:

- Büring 2003's full [T,F]-marking + question hierarchy / D-tree
  semantics. That belongs in a future
  `Semantics/Focus/Buring2003.lean` study or similar.
- Krifka 2008's frame-setting topics (§5.1.4) and delimitation
  topics — distinct concepts to add when consumers demand them.
- [fery-ishihara-2016] Ch 4 (Büring) argues for *eliminating*
  non-contrastive topics as a coherent linguistic category; this
  remains a live debate. The substrate keeps both `TopicMark`
  (aboutness) and `ContrastiveTopic` available rather than picking
  a side.

## Layer position

`Features/`. Sibling of `Features/Givenness.lean`,
`Features/Accessibility.lean`, and `Features/InformationStructure.lean`.
Importable from any consumer that needs to type a constituent as
topical or contrastive-topic. Currently `Phenomena/Generics/BarePlurals.lean`
has a local `TopicFocusDatum` that could migrate here in a follow-up.
-/

set_option autoImplicit false

namespace Features

/-- [reinhart-1981] aboutness topic: whether a constituent is
    the entity under which the proposition is filed in the CommonGround.
    Binary by design — degree-of-topicality theories belong in their
    own files. -/
inductive TopicMark where
  /-- Aboutness topic: the constituent the proposition is *about*. -/
  | aboutness
  /-- Non-topical constituent. -/
  | nonTopic
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- [buring-2003] contrastive topic: a topic constituent paired
    with a set of alternative topics that could have been chosen.
    Mirrors `Features.InformationStructure.Focus` shape — both
    Roothian-flavored alternative-set primitives.

    The placeholder structure carries the topic and its alternatives;
    Büring's full [T,F]-marking calculus (where the alternatives index
    a discourse-tree of subquestions) belongs in a later study file. -/
structure ContrastiveTopic (α : Type) where
  /-- The topical element. -/
  topic : α
  /-- Alternative topics that could have been picked instead. -/
  alternatives : List α
  deriving Repr

end Features
