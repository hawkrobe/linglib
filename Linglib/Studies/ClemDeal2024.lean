/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Fragments.Kawapanan.Shawi.Basic
import Linglib.Studies.Deal2024
import Linglib.Syntax.Case.Dependent

/-!
# Dependent Case by Agree: Ergative in Shawi [clem-deal-2024]

[clem-deal-2024] argue that ergative case in Shawi (Kawapanan; Peru)
arises when v Agrees with the *subject after the object*: the subject
serves as the **second goal** for the v probe, receiving a goal-flag
bundle that includes the object's φ-features. The ergative suffix `-ri`
spells out the φ-root of that bundle, and the optional "object agreement
on subject" (OAgr-on-S) morpheme spells out the inner φ-features of the
same bundle.

The distribution of `-ri` in Shawi is a **strictly descending** /
ultrastrong PCC pattern (1>2>3). [clem-deal-2024]'s final generalization
(their (10), p. 274) is: ergative appears when the subject is at least as
high as the object on the person hierarchy 1>2>3 *and both arguments are
in the same syntactic domain*. The hierarchy half is exactly [deal-2024]'s
`strictlyDescending` grammar (`SAT:[SPKR]`, `DynINT:[PART]↑`), already
formalized in `Deal2024.lean`; the same-domain half is the object's
visibility to the v probe (`objectVisible`).

`predictsErgative` realizes both factors. Note it follows the [deal-2024]
mechanism the paper adopts, not the loose prose of (10): a 1st-person
object satisfies `SAT:[SPKR]` and halts the probe, so `predictsErgative`
predicts *no* ergative at the reflexive 1→1 cell, even though "at least as
high as" (1 ≥ 1) would admit it. Shawi data do not document the reflexive
1→1/2→2 cells — Table 4 (p. 285) has no such rows — so this is a prediction
of the mechanism, not a tested fact.

This study file does five things:

1. **Map** the Shawi clause to the Deal-2024 PCC framing: the lower goal
   (DO) is the object, the higher / second goal (IO) is the subject.
2. **Predict** the distribution of `-ri` over the cells of
   [clem-deal-2024] Table 4 (p. 285) from the existing `strictlyDescending`
   grammar plus the high/low ambiguity for 3rd-person objects (the source
   of "(✓)" optionality).
3. **Ground** the predictions in the privative person geometry shared
   with [deal-2024]'s `dpBears` (and via that, with
   [pancheva-zubizarreta-2018]'s `satisfiesProminence` and
   [bejar-rezac-2009]'s `personSpec`).
4. **Bridge** to the existing person-rank order via
   `Deal2024.sd_off_diagonal_iff_outranks` — the Shawi pattern's
   1>2>3 hierarchy is exactly the one that fell out of Deal-2024.
5. **Counterexample** the configurational case rules [clem-deal-2024]
   discusses (§1 (1), after [baker-2015]; §4.1 (37), a
   [barany-sheehan-2024]-style rule) by running linglib's *own* formalized
   dependent-case algorithm (`Syntax.Case.assignCases`) on Shawi cells,
   rather than a local strawman.

Genuinely new machinery — bidirectional Agree (goal flagging),
Distributed-Morphology Vocabulary Insertion, Kinyalolo's Constraint —
is *not* introduced here. The study file derives Shawi's empirical
table from infrastructure linglib already has, and flags the new
machinery as a separate follow-up.
-/

namespace ClemDeal2024

open Minimalist (decomposePerson)

open Deal2024 (DealGrammar isLicit strictlyDescending dpBears
  sd_off_diagonal_iff_outranks)
open Kawapanan.Shawi (ObjectPosition ObjectSyntax Phi mustBeHigh
  ergativeMarker oagrOnSMarker objectSyntaxLicit)
open Syntax.Case (NPInDomain assignCases getCaseOf)

-- ============================================================================
-- § 1: Mapping Shawi to Deal-2024
-- ============================================================================

/-- The v probe in Shawi sits between the object (lower) and the subject
    (higher). Cyclic Agree (Béjar & Rezac 2009) makes the object the
    first goal (G1 ≡ DO in Deal-2024 terms) and the subject the second
    goal (G2 ≡ IO). [clem-deal-2024] (13) (cyclic expansion), (15)–(19). -/
def shawiGrammar : DealGrammar := strictlyDescending

/-- Shawi's surface 1>2>3 pattern is what Deal-2024 calls strictly
    descending. This is a definitional alignment (a drift guard), not a
    discovery — hence an anonymous `example`. -/
example : shawiGrammar = strictlyDescending := rfl

-- ============================================================================
-- § 2: The two factors of the ergative prediction
-- ============================================================================

/-- Whether v can interact with the object as G1. 3rd-person *low*
    objects sit inside the inner v_cat phase and are invisible to the
    v probe ([clem-deal-2024] §3.2, (24), (30)). Every other object —
    local-person (1/2, including the clusivity cells) and high-positioned
    3rd-person — is visible.

    Two notes on the wildcard. (i) `objectVisible .first .low` and
    `objectVisible .second .low` return `true` vacuously: local-person
    objects never occupy the low position (`mustBeHigh` is `true` for
    them), so the case is structurally inaccessible. (ii) The impersonal
    `.zero` and the clusivity cells `.firstInclusive`/`.firstExclusive`
    fall through to `true`; only the bare `.third` low cell is invisible,
    matching the paper's treatment of 3rd-person objects as the persons
    that show no overt object agreement and may stay low. -/
def objectVisible : Person → ObjectPosition → Bool
  | .third, .low => false
  | _, _         => true

/-- Predict whether `-ri` surfaces on the subject of a transitive clause
    with the given subject person, object person, and object position.

    Two factors must coincide:
    1. The object must be visible to v (`objectVisible`).
    2. The probe must successfully Agree with the subject as a
       *second* goal — exactly Deal-2024's `isLicit` for the strictly
       descending grammar. -/
def predictsErgative (subj obj : Person) (pos : ObjectPosition) : Bool :=
  objectVisible obj pos && isLicit shawiGrammar subj obj

-- ============================================================================
-- § 3: Feature-geometry-grounded characterizations
-- ============================================================================

/-- 1P object always satisfies SAT:[SPKR], halting the probe before it
    reaches the subject — ergative is impossible regardless of the
    subject's features or the object's position. [clem-deal-2024]
    (7a–b), (14a–b), §3 derivation in (15). -/
theorem erg_with_1p_obj_blocked (subj : Person) (pos : ObjectPosition) :
    predictsErgative subj .first pos = false := by
  cases subj <;> cases pos <;> rfl

/-- 2P high object: lacks [SPKR] (no SAT halt) but bears [PART],
    triggering dynamic narrowing. The subject is then visible as G2
    only if it bears [PART] — i.e., is itself local-person.
    [clem-deal-2024] §3.2, (16). -/
theorem erg_with_2p_obj_iff_subj_part (subj : Person) :
    predictsErgative subj .second .high = dpBears subj .part := by
  cases subj <;> rfl

/-- 3P high object: lacks [SPKR] *and* lacks [PART], so the probe
    neither halts nor narrows. The subject is visible as G2 regardless
    of its features. [clem-deal-2024] (8), (22). -/
theorem erg_with_3p_obj_high_always (subj : Person) :
    predictsErgative subj .third .high = true := by
  cases subj <;> rfl

/-- 3P low object: invisible to v. The probe finds only the subject as
    G1; no goal-flag bundle reaches the subject. [clem-deal-2024]
    (24). -/
theorem erg_with_3p_obj_low_blocked (subj : Person) :
    predictsErgative subj .third .low = false := by
  cases subj <;> rfl

-- ============================================================================
-- § 4: Hierarchy-rank bridge — inheriting Deal-2024's characterization
-- ============================================================================

/-- For non-diagonal (subject ≠ object) configurations with a visible
    object, ergative on the subject coincides with the subject
    *outranking* the object on the 1>2>3 person hierarchy.
    Inherits [deal-2024]'s `sd_off_diagonal_iff_outranks` —
    Shawi's hierarchy effect is exactly the one that fell out of
    Deal-2024 on independent grounds. -/
theorem erg_off_diagonal_iff_subj_outranks_obj
    (subj obj : Person)
    (h_neq : decomposePerson subj ≠ decomposePerson obj) :
    predictsErgative subj obj .high = true ↔
      subj.prominence > obj.prominence := by
  have h_vis : objectVisible obj .high = true := by cases obj <;> rfl
  unfold predictsErgative
  rw [h_vis, Bool.true_and]
  exact sd_off_diagonal_iff_outranks subj obj h_neq

-- ============================================================================
-- § 5: Cell-by-cell verification of Table 4
-- ============================================================================

/-- [clem-deal-2024] Table 4 (p. 285) — the full ergative distribution by
    person of subject and object, here with the high/low split of the
    3rd-person-object rows giving 10 cells. Each reduces by `rfl` from
    `predictsErgative`. Table 4 lists 7 (subject, object) person pairs; it
    has no reflexive 1→1 or 2→2 rows (see the header note on the 1→1
    mechanism prediction). -/
theorem table4 :
    predictsErgative .first  .second .high = true  ∧  -- a   1→2      obligatory
    predictsErgative .first  .third  .high = true  ∧  -- b   1→3 high present
    predictsErgative .first  .third  .low  = false ∧  -- b   1→3 low  absent
    predictsErgative .second .first  .high = false ∧  -- c   2→1      impossible
    predictsErgative .second .third  .high = true  ∧  -- d   2→3 high present
    predictsErgative .second .third  .low  = false ∧  -- d   2→3 low  absent
    predictsErgative .third  .first  .high = false ∧  -- e   3→1      impossible
    predictsErgative .third  .second .high = false ∧  -- f   3→2      impossible
    predictsErgative .third  .third  .high = true  ∧  -- g   3→3 high present
    predictsErgative .third  .third  .low  = false :=  -- g   3→3 low  absent
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Optionality is exactly the `(✓)` cells: 1→3, 2→3, 3→3. -/
theorem optionality_only_with_3p_object (subj obj : Person) :
    (predictsErgative subj obj .high ≠ predictsErgative subj obj .low) →
    obj = .third := by
  cases obj <;> cases subj <;> decide

-- ============================================================================
-- § 6: Local-person objects: position is forced
-- ============================================================================

/-- For any local-person object, the position parameter is irrelevant
    to the prediction: ergative depends only on `isLicit shawiGrammar`.
    Reason: `objectVisible` is `true` for any non-3P object regardless
    of position. -/
theorem local_object_position_irrelevant
    (subj obj : Person) (h : obj.IsSAP) (pos : ObjectPosition) :
    predictsErgative subj obj pos = isLicit shawiGrammar subj obj := by
  cases obj <;> first | rfl | exact h.elim

/-- Bookkeeping: for any local-person object, the Fragment-level
    `mustBeHigh` constraint forces the high position, which is exactly
    what the probe-visibility analysis presupposes. -/
theorem local_object_must_be_high (p : Person) (h : p.IsSAP) :
    mustBeHigh p = true := by
  cases p <;> first | rfl | exact h.elim

-- ============================================================================
-- § 7: Configurational case as a foil (paper §1, §4.1)
-- ============================================================================

/-- A Shawi monotransitive mapped to a dependent-case Spell-Out domain:
    the subject c-commands the object (earlier = structurally higher), and
    neither bears lexical case. Person-blind, exactly as a configurational
    case rule is. -/
def shawiDomain (_subj _obj : Person) : List NPInDomain :=
  [⟨"subj", none⟩, ⟨"obj", none⟩]

/-- Baker's configurational rule for ergative ([baker-2015]; [clem-deal-2024]
    (1)): "if there are two distinct NPs in the same spell-out domain such
    that NP1 c-commands NP2, then value the case feature of NP1 as ergative
    unless NP2 has already been marked for case." Rather than restate this
    as a local strawman, we *run* linglib's own dependent-case algorithm —
    `Syntax.Case.assignCases .ergative`, which values the higher of two
    caseless NPs ergative — over the Shawi domain. -/
def configErg (subj obj : Person) : Bool :=
  getCaseOf "subj" (assignCases .ergative (shawiDomain subj obj)) == some .erg

/-- The configurational rule is person-blind: `assignCases .ergative` values
    *every* transitive subject ergative, regardless of person. -/
theorem configErg_person_blind (subj obj : Person) :
    configErg subj obj = true := by cases subj <;> cases obj <;> decide

/-- It therefore overgenerates exactly where Shawi bans `-ri` because the
    object outranks the subject. 2→1: [clem-deal-2024] (7a). This is the
    paper's own argument against rule (1). -/
theorem configurational_rule_overgenerates_2_to_1 :
    configErg .second .first = true ∧
    predictsErgative .second .first .high = false := by decide

/-- And 3→1: [clem-deal-2024] (7b). -/
theorem configurational_rule_overgenerates_3_to_1 :
    configErg .third .first = true ∧
    predictsErgative .third .first .high = false := by decide

/-- The augmented configurational rule [clem-deal-2024] (37) writes the
    person hierarchy into rule (1) itself: NP1 gets ergative when it
    c-commands a caseless NP2 *and* "NP1 is at least as high as NP2 on the
    person hierarchy 1>2>3" — note `≥` (the paper's "at least as high as"),
    so it fires on the person diagonal too. This is [clem-deal-2024]'s
    rendering of an option explored by [barany-sheehan-2024]; linglib has no
    formalized person-augmented configurational rule, consistent with the
    paper's third concern (§4.1) that such rules face no principled limit on
    the hierarchies they may stipulate. -/
def augmentedConfigErg (subj obj : Person) : Bool :=
  decide (subj.prominence ≥ obj.prominence)

/-- [clem-deal-2024] do *not* refute (37) empirically — they grant it "is
    simple to state" (§4.1), and it is descriptively adequate: on every
    documented (high-object) cell of Table 4 it predicts exactly the
    Agree analysis. -/
theorem augmented_config_matches_on_documented_cells :
    (augmentedConfigErg .first  .second = predictsErgative .first  .second .high) ∧
    (augmentedConfigErg .first  .third  = predictsErgative .first  .third  .high) ∧
    (augmentedConfigErg .second .first  = predictsErgative .second .first  .high) ∧
    (augmentedConfigErg .second .third  = predictsErgative .second .third  .high) ∧
    (augmentedConfigErg .third  .first  = predictsErgative .third  .first  .high) ∧
    (augmentedConfigErg .third  .second = predictsErgative .third  .second .high) ∧
    (augmentedConfigErg .third  .third  = predictsErgative .third  .third  .high) := by
  decide

/-- The paper's objections to (37) are architectural, not empirical (§4.1):
    a person-augmented configurational rule (i) severs the case↔agreement
    (OAgr-on-S) connection, (ii) cannot unify the case-split person hierarchy
    with the identical hierarchy seen in agreement (e.g. Spanish
    ditransitives), and (iii) places no principled limit on which hierarchies
    a case rule may stipulate. linglib's internal counterpart is *expressive*:
    being a rule over person alone, (37) is blind to object position, so it
    cannot produce the position-conditioned optionality of 3rd-person objects
    (Table 4 rows b, d, g; (8), (23)). It predicts ergative for 3→3 (3 ≥ 3) —
    the high-object reading, (22) — but has no way to derive the low-object,
    no-ergative reading, (24), that the Agree analysis gets from object
    visibility. -/
theorem augmented_config_blind_to_object_position :
    augmentedConfigErg .third .third = true ∧
    predictsErgative .third .third .high = true ∧
    predictsErgative .third .third .low = false := by decide

-- ============================================================================
-- § 8: Object syntax — overt-postverbal blocked under ergative
-- ============================================================================

/-- [clem-deal-2024] (9), (21): when the subject bears `-ri`,
    the object cannot remain overt-postverbal. This combines the
    Fragment-level `objectSyntaxLicit` with the predictedness of
    ergative — a high-object subject that outranks the object forces
    the object out of postverbal position (to OSV or *pro*-drop). -/
theorem outranking_subj_blocks_postverbal_obj
    (subj obj : Person)
    (h_neq : decomposePerson subj ≠ decomposePerson obj)
    (h_rank : subj.prominence > obj.prominence) :
    objectSyntaxLicit (predictsErgative subj obj .high) .overtPostverbal = false := by
  have h_erg : predictsErgative subj obj .high = true :=
    (erg_off_diagonal_iff_subj_outranks_obj subj obj h_neq).mpr h_rank
  rw [h_erg]
  rfl

/-- The fronted (OSV) and *pro*-drop options remain licit regardless
    of whether the subject bears `-ri`. -/
theorem fronted_and_prodropped_always_licit
    (subj obj : Person) (pos : ObjectPosition) :
    objectSyntaxLicit (predictsErgative subj obj pos) .overtFronted = true ∧
    objectSyntaxLicit (predictsErgative subj obj pos) .proDropped = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 9: OAgr-on-S correlation ([clem-deal-2024] §2, §3.3, fn. 7)
-- ============================================================================

/-! "Object agreement on subject" (OAgr-on-S) can spell out the inner
φ-features of the goal-flag bundle that `-ri` exposes; if no such bundle is
present (i.e. no ergative), there is nothing for the OAgr-on-S morpheme to
attach to. [clem-deal-2024]'s empirical generalization (§2, p. 274, with
footnote 7, elaborated in §3.3) is that OAgr-on-S obtains *only if* the
subject is ergative — an *only if*, not an *iff*: an ergative subject may
appear with or without OAgr-on-S.

We deliberately do **not** ship a separate `oagrOnSAvailable` predicate.
Its availability coincides with `predictsErgative` only *by construction*
here, so a definition `oagrOnSAvailable := predictsErgative` plus a "bridge"
theorem would merely rename `predictsErgative` and re-export its theorems.
The substantive content — the only-if/not-iff asymmetry — is not derivable
without the goal-flagging machinery flagged in §11; until then it is an
empirical generalization *about* `predictsErgative`, not a separate object. -/

-- ============================================================================
-- § 10: Bridges — Shawi inherits Deal-2024 cell counts
-- ============================================================================

/-- Across the 9 (subject, object) cells, the strictly-descending
    grammar licenses 5 — exactly the 5 cells where ergative is licit
    in Shawi (rows a, b, d, g of Table 4, with row b/d/g being the
    high-object subcases). Derived from `Deal2024.sd_licit_count`. -/
theorem shawi_licit_count :
    Deal2024.licitCount shawiGrammar = 5 :=
  Deal2024.sd_licit_count

/-- Among the high-object cells, predicted ergative coincides with
    `isLicit` on the strictly-descending grammar — Shawi inherits the
    Deal-2024 typology wholesale once we condition on "object visible
    to v". -/
theorem high_object_matches_deal2024 (subj obj : Person) :
    predictsErgative subj obj .high = isLicit shawiGrammar subj obj := by
  cases obj <;> rfl

-- ============================================================================
-- § 11: What is *not* yet formalized
-- ============================================================================

/-! ## Follow-ups

`[clem-deal-2024]`'s analysis crucially depends on three pieces of
machinery that linglib does not yet have:

1. **Bidirectional Agree (goal flagging)** — the probe-to-goal direction
   of feature transfer. Without this, the claim that `-ri` *is* the
   object's φ-features (rather than a primitive [ERG]) cannot be stated
   structurally. `Syntax/Minimalism/Agree.lean` currently
   models only valuation (goal→probe).
2. **Distributed Morphology / Vocabulary Insertion** — for the VI rule
   `ri ↔ φ / ___ [φ,D]` ([clem-deal-2024] (34)) and Kinyalolo's
   Constraint impoverishment ((35)). The `Core/Lexical/MorphRule.lean`
   skeleton is Bybee-flavored and does not yet capture context-sensitive
   realization.
3. **Feature provenance** — distinguishing "native" features on a goal
   from features deposited there by Agree ([clem-deal-2024] fn. 23).
   Required to state the ergative VI without overgenerating.

Once (1)–(3) are in place, the OAgr-on-S generalization noted in §9 —
currently an empirical *only if* *about* `predictsErgative` — can be
derived as a theorem, including the only-if/not-iff asymmetry.
-/

end ClemDeal2024
