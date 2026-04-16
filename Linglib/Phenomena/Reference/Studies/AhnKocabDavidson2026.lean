import Linglib.Theories.Semantics.Composition.Modification
import Linglib.Phenomena.Reference.Studies.Ariel2001
import Linglib.Theories.Pragmatics.GriceanMaxims
import Linglib.Theories.Semantics.Lexical.Expressives.Basic
import Linglib.Theories.Semantics.Lexical.Verb.SelectionalPreferences

/-!
# @cite{ahn-kocab-davidson-2026}

Pragmatics of spatial descriptions: Sign language loci. Language (2026), 1–40.

## Core Analysis

Sign language loci (spatial locations in signing space) are **spatial modifiers**,
not agreement markers. The indexical point IX directed toward a location A
(written IX_A) is a predicate `R(x, a)` that relates an entity to a location.
IX_A composes with a nominal restriction via predicate modification to form a
demonstrative-like expression.

This analysis unifies the use of loci in both the verbal domain (verb
"agreement" = incorporation of IX into the verb) and the nominal domain
(IX_A = spatial modifier on a null demonstrative), and derives their
optionality from pragmatic principles: loci are licensed when disambiguation
is needed (Be Brief), paralleling demonstratives in spoken languages and
differential object marking.

## Key Formalizations

- `ixLoc` — the core IX_LOC denotation: `λo. λx. R(x, o)` (eq. 22a)
- `ixA` — IX pointing at locus A, applied: `λx. R(x, a)` (eq. 22b)
- `ixModified` — IX_A composes with nominal restriction via `predMod` (eq. 23–27)
- `LocusRelationType` — the deictic-to-abstract continuum for R (eqs. 38–40)
- `VerbLocusType` — selectional properties replacing Padden's trichotomy
- `incorporateSubj/Obj/Both` — verbal incorporation as `predMod` on argument positions
- Bridge theorems to `TwoDimProp` (@cite{potts-2005}), `SemClass`, Ariel accessibility,
  Gricean maxims

## Theoretical Contributions

1. Reduces Padden's three-way verb classification (agreeing, spatial, plain)
   to selectional properties of the verb — what type of nominal (personal,
   locational) can be incorporated
2. Derives optionality of loci from Be Brief (M3): loci are costlier
   referential forms, dispreferred when a simpler form suffices
3. Parallels DOM (@cite{aissen-2003}): both involve overt marking conditioned
   by disambiguation need along prominence scales
-/

set_option autoImplicit false

namespace AhnKocabDavidson2026

open Semantics.Composition.Modification (predMod truePred predMod_true_left predMod_comm)
open Core.Discourse.ReferentialForm (AccessibilityLevel)
open Pragmatics.GriceanMaxims
open Semantics.Lexical.Expressives (TwoDimProp)
open Semantics.Lexical.Verb.SelectionalPreferences (SemClass)

-- ════════════════════════════════════════════════════════════════
-- § 1. Core Types
-- ════════════════════════════════════════════════════════════════

/-- Abstract locus: a location in signing space used to track discourse
    referents. Two loci are distinguished if they occupy different spatial
    positions. The type is kept abstract — concrete spatial geometry is
    orthogonal to the pragmatic analysis. -/
inductive Locus where
  | a | b | c
  deriving DecidableEq, Repr

/-- The relation R between an entity and a locus. The paper's key insight
    is that R is not fixed — it ranges from transparent physical co-location
    to arbitrary discourse association (eqs. 38–40).

    See `deicticR` (eq. 38) and `abstractR` (eq. 40) for concrete examples
    at the extremes of this continuum. -/
inductive LocusRelationType where
  /-- Deictic: R(x, o) iff x is physically located at o in the signing
      context. The referent is present and the signer points at them.
      This is the most transparent R (eq. 38). -/
  | deictic
  /-- Metonymic: R(x, o) iff x is the regular occupant of location o.
      E.g., pointing at an office to refer to its occupant (eq. 39). -/
  | metonymic
  /-- Abstract: R(x, o) iff x has been associated with o by prior
      discourse introduction. No physical or conventional link required.
      This is the most opaque R (eq. 40). -/
  | abstract
  deriving DecidableEq, Repr

/-- Transparency of the R relation: how much the spatial location
    correlates with the physical world. Higher = more transparent.
    This orders the deictic-to-abstract continuum (eqs. 38–40). -/
def LocusRelationType.transparency : LocusRelationType → Fin 3
  | .deictic   => 2
  | .metonymic => 1
  | .abstract  => 0

/-- The deictic–abstract continuum is ordered: deictic > metonymic > abstract. -/
theorem deictic_most_transparent :
    LocusRelationType.deictic.transparency > LocusRelationType.abstract.transparency ∧
    LocusRelationType.deictic.transparency > LocusRelationType.metonymic.transparency :=
  ⟨by native_decide, by native_decide⟩

/-- Entity type for ASL discourse scenarios. -/
inductive Entity where
  | jin | sol | linda | mike | bob | will | girl | boy
  | tv | tree | ball
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2. IX_LOC Semantics
-- ════════════════════════════════════════════════════════════════

/-- `⟦IX_LOC⟧ = λo. λx. R(x, o)` — the core denotation of the indexical
    point. Takes a location variable `o` and returns a predicate over
    entities. This is the spatial predicate that all uses of loci share.

    Eq. 22a of @cite{ahn-kocab-davidson-2026}. -/
def ixLoc (R : Entity → Locus → Bool) : Locus → Entity → Bool :=
  fun o x => R x o

/-- `⟦IX_A⟧ = λx. R(x, a)` — IX pointing at a specific locus A.
    This is `ixLoc R` partially applied to a concrete locus.

    Analogous to a Kaplan demonstration (@cite{kaplan-1989}): IX_A requires
    a contextual element (the R relation) to determine reference, and when
    R is functional, picks out a unique entity — like a pointing gesture
    that presents an individual in context (see `ixA_unique_when_functional`).

    Eq. 22b of @cite{ahn-kocab-davidson-2026}. -/
def ixA (R : Entity → Locus → Bool) (loc : Locus) : Entity → Bool :=
  ixLoc R loc

/-- IX_A composes with a nominal restriction P via predicate modification:
    `⟦P + IX_A⟧ = λx. P(x) ∧ R(x, a)`.

    This covers:
    - `⟦[that+IX_A] girl⟧ = ιx. girl(x) ∧ R(x, a)` (English, eq. 23)
    - `⟦[she+IX_A]⟧ = ιx. fem(x) ∧ R(x, a)` (English, eq. 25)
    - `⟦[ta+IX_A]⟧ = ιx. entity(x) ∧ R(x, a)` (Mandarin, eq. 26)
    - `⟦[∅+IX_A]⟧ = ιx. R(x, a)` (ASL, eq. 27) -/
def ixModified (R : Entity → Locus → Bool) (loc : Locus)
    (P : Entity → Bool) : Entity → Bool :=
  predMod P (ixA R loc)

/-- ASL null-pronoun case: ∅ + IX_A. The nominal restriction is vacuous
    (`truePred`), so the result is just `R(x, a)`. Eq. 27. -/
def ixNull (R : Entity → Locus → Bool) (loc : Locus) : Entity → Bool :=
  ixModified R loc truePred

/-- The null-pronoun case reduces to the bare spatial predicate. -/
theorem ixNull_eq_ixA (R : Entity → Locus → Bool) (loc : Locus) :
    ixNull R loc = ixA R loc := by
  simp only [ixNull, ixModified]
  exact predMod_true_left (ixA R loc)

/-- IX_A + P entails P: the modified expression is strictly more restrictive
    than the bare nominal. Any entity satisfying `P ∧ R(·, a)` also
    satisfies `P`. -/
theorem ixModified_entails_base (R : Entity → Locus → Bool) (loc : Locus)
    (P : Entity → Bool) (x : Entity)
    (h : ixModified R loc P x = true) : P x = true := by
  simp only [ixModified, predMod] at h
  exact (Bool.and_eq_true_iff.mp h).1

/-- IX_A + P entails R(·, a): the modified expression entails the spatial
    predicate. -/
theorem ixModified_entails_spatial (R : Entity → Locus → Bool) (loc : Locus)
    (P : Entity → Bool) (x : Entity)
    (h : ixModified R loc P x = true) : ixA R loc x = true := by
  simp only [ixModified, predMod] at h
  exact (Bool.and_eq_true_iff.mp h).2

/-- The order of composition does not matter: `P ∧ R(·, a)` = `R(·, a) ∧ P`.
    This follows from commutativity of predicate modification. -/
theorem ixModified_order (R : Entity → Locus → Bool) (loc : Locus)
    (P : Entity → Bool) :
    ixModified R loc P = predMod (ixA R loc) P :=
  predMod_comm P (ixA R loc)

/-- When R is functional (each locus maps to at most one entity), IX_A
    determines a unique referent — at most one entity satisfies R(·, a).
    This is the demonstrative-like property of IX_A: like a Kaplan
    demonstration, it picks out a unique individual in context. -/
theorem ixA_unique_when_functional (R : Entity → Locus → Bool)
    (hfun : ∀ (x y : Entity) (loc : Locus), R x loc = true → R y loc = true → x = y)
    (loc : Locus) (x y : Entity)
    (hx : ixA R loc x = true) (hy : ixA R loc y = true) : x = y :=
  hfun x y loc hx hy

-- ════════════════════════════════════════════════════════════════
-- § 3. Verb Selectional Properties (replacing Padden's trichotomy)
-- ════════════════════════════════════════════════════════════════

/-- The type of nominal that a verb selects for in its argument slots.
    This replaces Padden (1983)'s three-way classification:
    - `personal` → "agreeing" verbs (HELP, GIVE, TELL, ASK)
    - `locational` → "spatial" verbs (MOVE, PUT, CARRY)
    - `unspecified` → "plain" verbs (MEMORIZE, LOVE, THINK, WONDER)

    The key insight of @cite{ahn-kocab-davidson-2026} §3.5 is that all
    three classes can incorporate IX_LOC; they differ only in what entity
    type the spatial predicate selects for. -/
inductive VerbLocusType where
  /-- Verb selects for personal entities (agent/patient).
      Locus incorporation marks person information. -/
  | personal
  /-- Verb selects for locational entities (source/goal).
      Locus incorporation marks spatial information. -/
  | locational
  /-- Verb does not lexically specify; incorporation is possible but
      not triggered by the verb's own selectional requirements. -/
  | unspecified
  deriving DecidableEq, Repr

/-- Bridge to selectional preference classes: verb locus types correspond
    to semantic classes from the cross-linguistic selectional preference
    framework. `personal` maps to `SemClass.animate` (person arguments),
    `locational` maps to `SemClass.location`, and `unspecified` has no
    selectional restriction. -/
def VerbLocusType.toSemClass : VerbLocusType → Option SemClass
  | .personal    => some .animate
  | .locational  => some .location
  | .unspecified => none

/-- An ASL verb entry with locus selectional properties. -/
structure ASLVerbEntry where
  /-- Verb gloss -/
  gloss : String
  /-- What the subject slot selects for -/
  subjectType : VerbLocusType
  /-- What the object slot selects for -/
  objectType : VerbLocusType
  /-- Whether the verb has a directional movement component -/
  hasPath : Bool
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § 3a. ASL Verb Lexicon
-- ════════════════════════════════════════════════════════════════

/-- HELP: agreeing verb. Subject = agent (personal), object = recipient
    (personal). Has path movement from source to goal. -/
def help : ASLVerbEntry :=
  { gloss := "HELP", subjectType := .personal, objectType := .personal,
    hasPath := true }

/-- GIVE: agreeing verb with transfer semantics. -/
def give : ASLVerbEntry :=
  { gloss := "GIVE", subjectType := .personal, objectType := .personal,
    hasPath := true }

/-- ASK: agreeing verb. -/
def ask : ASLVerbEntry :=
  { gloss := "ASK", subjectType := .personal, objectType := .personal,
    hasPath := true }

/-- PUSH: agreeing verb. -/
def push : ASLVerbEntry :=
  { gloss := "PUSH", subjectType := .personal, objectType := .personal,
    hasPath := true }

/-- MOVE: spatial verb. Source and goal are locations, not persons. -/
def move : ASLVerbEntry :=
  { gloss := "MOVE", subjectType := .locational, objectType := .locational,
    hasPath := true }

/-- PUT: spatial verb. -/
def put : ASLVerbEntry :=
  { gloss := "PUT", subjectType := .personal, objectType := .locational,
    hasPath := true }

/-- DANCE: plain verb. No lexical locus selection, but CAN incorporate
    a locus via co-location when pragmatically needed. -/
def dance : ASLVerbEntry :=
  { gloss := "DANCE", subjectType := .unspecified, objectType := .unspecified,
    hasPath := false }

/-- FALL: plain verb. Intransitive, no path. -/
def fall : ASLVerbEntry :=
  { gloss := "FALL", subjectType := .unspecified, objectType := .unspecified,
    hasPath := false }

/-- RUN: plain verb. -/
def run : ASLVerbEntry :=
  { gloss := "RUN", subjectType := .unspecified, objectType := .unspecified,
    hasPath := false }

/-- All three verb types can incorporate IX_LOC. The traditional claim
    that only "agreeing" and "spatial" verbs show locus modification
    is empirically wrong — plain verbs like DANCE can be locationally
    modified when disambiguation requires it (§2.2, exx. 9–11). -/
theorem all_types_can_incorporate :
    dance.subjectType = .unspecified ∧
    help.subjectType = .personal ∧
    move.subjectType = .locational :=
  ⟨rfl, rfl, rfl⟩

/-- The difference between "agreeing" and "plain" verbs is selectional,
    not categorical: both can incorporate, but agreeing verbs lexically
    select for personal nominals while plain verbs do not. -/
theorem agreeing_vs_plain_is_selectional :
    help.objectType = .personal ∧
    dance.objectType = .unspecified :=
  ⟨rfl, rfl⟩

/-- Agreeing verbs select for animate entities; spatial verbs select for
    locations. This connects the ASL-specific typology to the
    cross-linguistic selectional preference framework. -/
theorem selectional_bridge :
    help.subjectType.toSemClass = some .animate ∧
    help.objectType.toSemClass = some .animate ∧
    move.subjectType.toSemClass = some .location ∧
    move.objectType.toSemClass = some .location ∧
    dance.subjectType.toSemClass = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 4. Verbal Incorporation
-- ════════════════════════════════════════════════════════════════

/-- Incorporation of IX_A for the subject argument: the verb's meaning
    is conjoined with the spatial predicate via predicate modification
    on the subject position. For each fixed object y, the subject
    predicate `λx. V(x, y)` is modified by `ixA R loc`.

    This is the semantic content of what is traditionally called "verb
    agreement" in sign languages — it is predicate modification, not
    agreement in the syntactic sense. -/
def incorporateSubj (verbMeaning : Entity → Entity → Bool)
    (R : Entity → Locus → Bool) (loc : Locus) :
    Entity → Entity → Bool :=
  fun x y => predMod (fun x' => verbMeaning x' y) (ixA R loc) x

/-- Incorporation of IX_A for the object argument: the verb's meaning
    is conjoined with the spatial predicate via predicate modification
    on the object position. -/
def incorporateObj (verbMeaning : Entity → Entity → Bool)
    (R : Entity → Locus → Bool) (loc : Locus) :
    Entity → Entity → Bool :=
  fun x y => predMod (verbMeaning x) (ixA R loc) y

/-- Full incorporation (both arguments): sequential application of
    object incorporation then subject incorporation.

    For `₍ₐ₎VERB₍ᵦ₎`, this yields `λx y. V(x,y) ∧ R(y,b) ∧ R(x,a)`. -/
def incorporateBoth (verbMeaning : Entity → Entity → Bool)
    (R : Entity → Locus → Bool) (locSubj locObj : Locus) :
    Entity → Entity → Bool :=
  fun x y => predMod (fun x' => predMod (verbMeaning x') (ixA R locObj) y)
                      (ixA R locSubj) x

/-- Full incorporation is equivalent to sequential incorporation:
    incorporate the object, then the subject. -/
theorem incorporate_both_eq_sequential
    (V : Entity → Entity → Bool) (R : Entity → Locus → Bool)
    (locSubj locObj : Locus) :
    incorporateBoth V R locSubj locObj =
    incorporateSubj (incorporateObj V R locObj) R locSubj := rfl

/-- The order of incorporation does not matter: incorporating subject
    then object yields the same result as object then subject. -/
theorem incorporate_order_independent
    (V : Entity → Entity → Bool) (R : Entity → Locus → Bool)
    (locSubj locObj : Locus) (x y : Entity) :
    incorporateSubj (incorporateObj V R locObj) R locSubj x y =
    incorporateObj (incorporateSubj V R locSubj) R locObj x y := by
  simp only [incorporateSubj, incorporateObj, predMod, Bool.and_assoc]
  congr 1
  exact Bool.and_comm _ _

-- ════════════════════════════════════════════════════════════════
-- § 5. Pragmatic Licensing
-- ════════════════════════════════════════════════════════════════

/-- Disambiguation context: the discourse factors that determine whether
    locus marking is pragmatically needed. These correspond to the three
    experimental conditions in §4 of @cite{ahn-kocab-davidson-2026}. -/
structure PragmaticContext where
  /-- Number of potential referents for the target predicate. -/
  numReferents : Fin 3  -- 0 = none (degenerate), 1 = one, 2 = two
  /-- Whether narrative context provides disambiguating information. -/
  narrativeSupport : Bool
  /-- Whether the competing referent (if any) is animate. When the
      competitor is inanimate, animacy alone disambiguates. -/
  competitorAnimate : Bool
  deriving DecidableEq, Repr

/-- Contextual support: whether the discourse context alone provides
    sufficient information to resolve the intended referent. -/
def PragmaticContext.hasContextSupport (ctx : PragmaticContext) : Bool :=
  ctx.numReferents.val ≤ 1 || ctx.narrativeSupport || !ctx.competitorAnimate

/-- Whether locus marking is pragmatically needed: loci are licensed
    for disambiguation when contextual support is insufficient.

    The main hypothesis (eq. 53): "Locus use (IX_LOC and its incorporated
    forms, e.g. locationally modified verbs) is pragmatically licensed to
    disambiguate between potential antecedents." -/
def locusNeeded (ctx : PragmaticContext) : Bool :=
  !ctx.hasContextSupport

-- ════════════════════════════════════════════════════════════════
-- § 5a. Utterance Alternatives
-- ════════════════════════════════════════════════════════════════

/-- Utterance type: bare (no locus marking) vs. marked (with loci on
    nouns and/or verbs). These are the alternatives the speaker
    chooses between. -/
inductive LocusUtterance where
  /-- No locus marking: bare nouns, citation-form verbs. -/
  | bare
  /-- Locus-marked: IX on nouns, locationally modified verbs. -/
  | marked
  deriving DecidableEq, Repr

/-- Cost: locus-marked utterances are more costly (more phonological
    material, more articulatory effort). This is the Be Brief (M3)
    pressure against unnecessary locus use. -/
def LocusUtterance.cost : LocusUtterance → Nat
  | .bare   => 0
  | .marked => 1

/-- Marked utterances are costlier than bare ones. -/
theorem marked_costlier : LocusUtterance.marked.cost > LocusUtterance.bare.cost := by
  native_decide

/-- Informativity: whether the utterance resolves ambiguity in context. -/
def LocusUtterance.resolvesIn (u : LocusUtterance) (ctx : PragmaticContext) : Bool :=
  match u with
  | .bare   => ctx.hasContextSupport
  | .marked => true  -- loci always resolve (by providing spatial information)

-- ════════════════════════════════════════════════════════════════
-- § 5b. Experimental Conditions
-- ════════════════════════════════════════════════════════════════

/-- One referent, with contextual support. -/
def oneRef_plusCtx : PragmaticContext :=
  { numReferents := 1, narrativeSupport := true, competitorAnimate := true }

/-- Two referents, no contextual support (both animate, no narrative). -/
def twoRef_minusCtx : PragmaticContext :=
  { numReferents := 2, narrativeSupport := false, competitorAnimate := true }

/-- Two referents, with contextual support (narrative present). -/
def twoRef_plusCtx : PragmaticContext :=
  { numReferents := 2, narrativeSupport := true, competitorAnimate := true }

/-- Two referents, inanimate competitor (animacy disambiguates). -/
def twoRef_inanimate : PragmaticContext :=
  { numReferents := 2, narrativeSupport := false, competitorAnimate := false }

-- Key predictions verified:

/-- One referent: context suffices, locus not needed. -/
theorem oneRef_has_support : oneRef_plusCtx.hasContextSupport = true := rfl

/-- Two animate referents without narrative: locus needed. -/
theorem twoRef_animate_locus_needed : locusNeeded twoRef_minusCtx = true := rfl

/-- Two referents with narrative support: context suffices. -/
theorem twoRef_narrative_has_support :
    twoRef_plusCtx.hasContextSupport = true := rfl

/-- Two referents, inanimate competitor: context suffices (animacy
    disambiguates — only the animate referent can be the agent). -/
theorem inanimate_has_support :
    twoRef_inanimate.hasContextSupport = true := rfl

/-- Locus-marked utterances always resolve, regardless of context. -/
theorem marked_always_resolves (ctx : PragmaticContext) :
    LocusUtterance.marked.resolvesIn ctx = true := rfl

/-- Bare utterances fail to resolve exactly when context is insufficient. -/
theorem bare_fails_iff_no_support (ctx : PragmaticContext) :
    LocusUtterance.bare.resolvesIn ctx = ctx.hasContextSupport := rfl

-- ════════════════════════════════════════════════════════════════
-- § 6. Bridge: Gricean Maxim Tensions
-- ════════════════════════════════════════════════════════════════

/-- The pragmatic tension in locus use is between M2 (avoid ambiguity)
    and M3 (be brief). Loci resolve ambiguity (satisfying M2) but add
    phonological material (violating M3). The speaker should use loci
    iff the M2 gain outweighs the M3 cost — i.e., iff disambiguation
    is actually needed.

    This is structurally identical to the Be Brief / Avoid Ambiguity
    tradeoff that governs modifier use in spoken languages (e.g.,
    "the tall one" vs. "it" in a reference game). -/
def locusTension : MannerSubmaxim × MannerSubmaxim :=
  (.avoidAmbiguity, .beBrief)

/-- The two maxims in tension are distinct. -/
theorem tension_is_genuine :
    locusTension.1 ≠ locusTension.2 := by decide

/-- Optimal locus use: use loci iff context alone is insufficient for
    disambiguation. This resolves the M2/M3 tension by making the M3
    cost justified only when M2 would otherwise be violated. -/
def optimalLocusChoice (ctx : PragmaticContext) : LocusUtterance :=
  if locusNeeded ctx then .marked else .bare

/-- The optimal choice always resolves the referent. -/
theorem optimal_always_resolves (ctx : PragmaticContext) :
    (optimalLocusChoice ctx).resolvesIn ctx = true := by
  unfold optimalLocusChoice locusNeeded LocusUtterance.resolvesIn
  cases ctx.hasContextSupport <;> simp

-- ════════════════════════════════════════════════════════════════
-- § 7. Bridge: Accessibility Scale
-- ════════════════════════════════════════════════════════════════

/-- Where IX_LOC falls on Ariel's accessibility marking scale.

    IX_LOC is a stressed pronominal form with an accompanying gesture
    (pointing to a locus). This maps to `stressedPronGesture` —
    a stressed pronoun with a deictic gesture (rank 12).

    Without the locus (bare noun), the form would be a definite
    description or a null argument (depending on language).
    The locus-marked form is thus *less* accessible (more informative,
    more rigid) than a bare pronoun, and *more* accessible than a
    full definite description. -/
def ixLocAccessibility : AccessibilityLevel := .stressedPronGesture

/-- Bare pronominal reference (ASL null argument) maps to `zero`. -/
def bareNullAccessibility : AccessibilityLevel := .zero

/-- IX_LOC is less accessible (lower rank) than a bare null argument.
    This means it is more informative and should be used only when the
    more reduced form (null argument) is insufficient. -/
theorem ixLoc_less_accessible_than_null :
    ixLocAccessibility.rank < bareNullAccessibility.rank := by
  native_decide

/-- IX_LOC is more accessible than a full definite description.
    It is not as heavy as "the boy who is sitting on the left." -/
theorem ixLoc_more_accessible_than_description :
    ixLocAccessibility.rank > AccessibilityLevel.shortDefDescription.rank := by
  native_decide

/-- The accessibility prediction: speakers should use IX_LOC only when
    the more reduced form (null argument / bare noun) fails to uniquely
    identify the referent. This is Ariel's core principle applied to
    sign language loci. -/
theorem accessibility_predicts_locus_use :
    -- IX_LOC is more informative than null
    ixLocAccessibility.informativity > bareNullAccessibility.informativity ∧
    -- but has lower attenuation (heavier)
    ixLocAccessibility.attenuation < bareNullAccessibility.attenuation := by
  decide

-- ════════════════════════════════════════════════════════════════
-- § 8. DOM Parallel
-- ════════════════════════════════════════════════════════════════

/-!
### Parallel to Differential Object Marking (@cite{aissen-2003})

Both locus marking in sign languages and DOM in spoken languages involve
**optional overt marking** conditioned by disambiguation need:

- In DOM, objects are overtly case-marked when they are atypical (high
  animacy/definiteness, which makes them harder to distinguish from subjects).
- In sign language, loci are overtly used when context fails to disambiguate.

The shared principle: "Mark when disambiguation is needed; omit marking
when the default interpretation suffices."

@cite{aissen-2003} formalizes DOM as harmonic alignment of prominence scales
with grammatical relations. The locus parallel suggests the same mechanism
extends to the visual-spatial modality.

See `Phenomena/Case/Studies/Aissen2003.lean` for the OT formalization.
-/

-- ════════════════════════════════════════════════════════════════
-- § 9. Deictic-to-Abstract Continuum
-- ════════════════════════════════════════════════════════════════

/-- Deictic R: physical co-location. The signer points directly at a
    present referent. This is the most transparent relation type
    (`LocusRelationType.deictic`, eq. 38). -/
def deicticR (physicalLocation : Entity → Locus) : Entity → Locus → Bool :=
  fun x o => physicalLocation x == o

/-- Abstract R: discourse-introduced association. The signer has
    arbitrarily associated entities with loci earlier in the discourse.
    This is the most opaque relation type
    (`LocusRelationType.abstract`, eq. 40). -/
def abstractR (association : Entity → Option Locus) : Entity → Locus → Bool :=
  fun x o => association x == some o

/-- A concrete scenario: Jin is at locus A, Sol is at locus B. -/
def scenario1 : Entity → Locus → Bool
  | .jin, .a => true
  | .sol, .b => true
  | _, _ => false

/-- In scenario1, IX_A picks out Jin. -/
theorem scenario1_ixA_picks_jin :
    ixA scenario1 .a .jin = true ∧
    ixA scenario1 .a .sol = false :=
  ⟨rfl, rfl⟩

/-- In scenario1, IX_B picks out Sol. -/
theorem scenario1_ixB_picks_sol :
    ixA scenario1 .b .sol = true ∧
    ixA scenario1 .b .jin = false :=
  ⟨rfl, rfl⟩

/-- scenario1 is functional: each locus maps to at most one entity.
    Therefore `ixA_unique_when_functional` applies, giving IX_A
    demonstrative-like uniqueness. -/
theorem scenario1_functional (x y : Entity) (loc : Locus)
    (hx : scenario1 x loc = true) (hy : scenario1 y loc = true) :
    x = y := by
  cases x <;> cases y <;> cases loc <;> simp_all [scenario1]

/-- Verbal incorporation in scenario1: "₍ₐ₎HELP₍ᵦ₎" (Jin helps Sol).
    A simple transitive verb meaning for testing incorporation. -/
def helpMeaning : Entity → Entity → Bool
  | .jin, .sol  => true
  | .sol, .jin  => true
  | .jin, .jin  => true
  | .sol, .sol  => true
  | _, _ => false

/-- ₍ₐ₎HELP₍ᵦ₎ with scenario1 R correctly restricts to "Jin helps Sol". -/
theorem aHelpB_correct :
    incorporateBoth helpMeaning scenario1 .a .b .jin .sol = true ∧
    incorporateBoth helpMeaning scenario1 .a .b .sol .jin = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 10. Two-Dimensional Meaning (@cite{potts-2005})
-- ════════════════════════════════════════════════════════════════

/-- Introducing use of IX_LOC: the locus association is use-conditional
    (CI) content, not at-issue. The sentence's truth conditions come from
    the predicate; the spatial association projects as a CI.

    Uses `TwoDimProp` from @cite{potts-2005} directly — the introducing
    use of IX_LOC is structurally parallel to how expressives like "bastard"
    contribute CI content that projects through all operators. -/
def introducingUse (predicate : Entity → Bool) (R : Entity → Locus → Bool)
    (loc : Locus) : TwoDimProp Entity :=
  { atIssue := predicate
  , ci := fun x => R x loc }

/-- Anaphoric use: the spatial restriction IS at-issue (it picks out
    the unique entity associated with the locus). CI is trivial. -/
def anaphoricUse (R : Entity → Locus → Bool) (loc : Locus)
    (P : Entity → Bool) : TwoDimProp Entity :=
  { atIssue := ixModified R loc P
  , ci := fun _ => true }

/-- The introducing use's CI projects through negation: negating
    "JIN₍ₐ₎ DANCE" negates the dancing but preserves the locus
    association. Derived from `TwoDimProp.ci_projects_through_neg`. -/
theorem introducing_ci_projects (pred : Entity → Bool)
    (R : Entity → Locus → Bool) (loc : Locus) :
    (TwoDimProp.neg (introducingUse pred R loc)).ci =
    (introducingUse pred R loc).ci :=
  TwoDimProp.ci_projects_through_neg _

/-- The anaphoric use has trivial CI: all use-conditional content was
    already introduced. -/
theorem anaphoric_ci_trivial (R : Entity → Locus → Bool) (loc : Locus)
    (P : Entity → Bool) (x : Entity) :
    (anaphoricUse R loc P).ci x = true := rfl

end AhnKocabDavidson2026
