import Linglib.Phenomena.Agreement.Studies.Deal2024
import Linglib.Fragments.Kawapanan.Shawi.Basic

/-!
# Dependent Case by Agree: Ergative in Shawi @cite{clem-deal-2024}

@cite{clem-deal-2024} argue that ergative case in Shawi (Kawapanan; Peru)
arises when v Agrees with the *subject after the object*: the subject
serves as the **second goal** for the v probe, receiving a goal-flag
bundle that includes the object's φ-features. The ergative suffix `-ri`
spells out the φ-root of that bundle, and the optional "object agreement
on subject" (OAgr-on-S) morpheme spells out the inner φ-features of the
same bundle.

The distribution of `-ri` in Shawi is a **strictly descending** /
ultrastrong PCC pattern (1>2>3): ergative appears iff the subject is at
least as high as the object on the person hierarchy. This is exactly
@cite{deal-2024}'s `strictlyDescending` grammar (`SAT:[SPKR]`,
`DynINT:[PART]↑`), already formalized in `Deal2024.lean`.

This study file does five things:

1. **Map** the Shawi clause to the Deal-2024 PCC framing: the lower goal
   (DO) is the object, the higher / second goal (IO) is the subject.
2. **Predict** the distribution of `-ri` over the 7 (subject, object,
   3rd-person-object-position) cells of @cite{clem-deal-2024} Table 4
   from the existing `strictlyDescending` grammar plus the high/low
   ambiguity for 3rd-person objects (the source of "(✓)" optionality).
3. **Ground** the predictions in the privative person geometry shared
   with @cite{deal-2024}'s `dpBears` (and via that, with
   @cite{pancheva-zubizarreta-2018}'s `satisfiesProminence` and
   @cite{bejar-rezac-2009}'s `personSpec`).
4. **Bridge** to the existing person-rank order via
   `Deal2024.sd_off_diagonal_iff_outranks` — the Shawi pattern's
   1>2>3 hierarchy is exactly the one that fell out of Deal-2024.
5. **Counterexample** the simple and augmented configurational case
   rules (paper §4.1, equations (1) and (37)) on Shawi cells.

Genuinely new machinery — bidirectional Agree (goal flagging),
Distributed-Morphology Vocabulary Insertion, Kinyalolo's Constraint —
is *not* introduced here. The study file derives Shawi's empirical
table from infrastructure linglib already has, and flags the new
machinery as a separate follow-up.
-/

namespace Phenomena.Agreement.Studies.ClemDeal2024

open Core.Prominence (PersonLevel)
open Deal2024 (DealGrammar isLicit strictlyDescending dpBears
  sd_off_diagonal_iff_outranks)
open Fragments.Kawapanan.Shawi (ObjectPosition ObjectSyntax Phi mustBeHigh
  ergativeMarker oagrOnSMarker objectSyntaxLicit)

-- ============================================================================
-- § 1: Mapping Shawi to Deal-2024
-- ============================================================================

/-- The v probe in Shawi sits between the object (lower) and the subject
    (higher). Cyclic Agree (Béjar & Rezac 2009) makes the object the
    first goal (G1 ≡ DO in Deal-2024 terms) and the subject the second
    goal (G2 ≡ IO). @cite{clem-deal-2024} (3), (15)–(19). -/
def shawiGrammar : DealGrammar := strictlyDescending

/-- Shawi's surface 1>2>3 pattern is what Deal-2024 calls strictly
    descending. This is a definitional alignment, not a discovery. -/
theorem shawi_is_strictly_descending :
    shawiGrammar = strictlyDescending := rfl

-- ============================================================================
-- § 2: The two factors of the ergative prediction
-- ============================================================================

/-- Whether v can interact with the object as G1. 3rd-person *low*
    objects sit inside the inner v_cat phase and are invisible to the
    v probe (@cite{clem-deal-2024} §3.2, (24)). Local-person and
    high-positioned 3rd-person objects are visible.

    Note: `objectVisible .first .low` and `objectVisible .second .low`
    return `true` vacuously — local-person objects never occupy the
    low position (`mustBeHigh` is `true` for them), so this case is
    structurally inaccessible. -/
def objectVisible : PersonLevel → ObjectPosition → Bool
  | .third, .low => false
  | _, _         => true

/-- Predict whether `-ri` surfaces on the subject of a transitive clause
    with the given subject person, object person, and object position.

    Two factors must coincide:
    1. The object must be visible to v (`objectVisible`).
    2. The probe must successfully Agree with the subject as a
       *second* goal — exactly Deal-2024's `isLicit` for the strictly
       descending grammar. -/
def predictsErgative (subj obj : PersonLevel) (pos : ObjectPosition) : Bool :=
  objectVisible obj pos && isLicit shawiGrammar subj obj

-- ============================================================================
-- § 3: Feature-geometry-grounded characterizations
-- ============================================================================

/-- 1P object always satisfies SAT:[SPKR], halting the probe before it
    reaches the subject — ergative is impossible regardless of the
    subject's features or the object's position. @cite{clem-deal-2024}
    (7a–b), (14a–b), §3 derivation in (15). -/
theorem erg_with_1p_obj_blocked (subj : PersonLevel) (pos : ObjectPosition) :
    predictsErgative subj .first pos = false := by
  cases subj <;> cases pos <;> rfl

/-- 2P high object: lacks [SPKR] (no SAT halt) but bears [PART],
    triggering dynamic narrowing. The subject is then visible as G2
    only if it bears [PART] — i.e., is itself local-person.
    @cite{clem-deal-2024} §3.2, (16). -/
theorem erg_with_2p_obj_iff_subj_part (subj : PersonLevel) :
    predictsErgative subj .second .high = dpBears subj .part := by
  cases subj <;> rfl

/-- 3P high object: lacks [SPKR] *and* lacks [PART], so the probe
    neither halts nor narrows. The subject is visible as G2 regardless
    of its features. @cite{clem-deal-2024} (8), (19). -/
theorem erg_with_3p_obj_high_always (subj : PersonLevel) :
    predictsErgative subj .third .high = true := by
  cases subj <;> rfl

/-- 3P low object: invisible to v. The probe finds only the subject as
    G1; no goal-flag bundle reaches the subject. @cite{clem-deal-2024}
    (24). -/
theorem erg_with_3p_obj_low_blocked (subj : PersonLevel) :
    predictsErgative subj .third .low = false := by
  cases subj <;> rfl

-- ============================================================================
-- § 4: Hierarchy-rank bridge — inheriting Deal-2024's characterization
-- ============================================================================

/-- For non-diagonal (subject ≠ object) configurations with a visible
    object, ergative on the subject coincides with the subject
    *outranking* the object on the 1>2>3 person hierarchy.
    Inherits @cite{deal-2024}'s `sd_off_diagonal_iff_outranks` —
    Shawi's hierarchy effect is exactly the one that fell out of
    Deal-2024 on independent grounds. -/
theorem erg_off_diagonal_iff_subj_outranks_obj
    (subj obj : PersonLevel) (h_neq : subj ≠ obj) :
    predictsErgative subj obj .high = true ↔ subj.rank > obj.rank := by
  have h_vis : objectVisible obj .high = true := by cases obj <;> rfl
  unfold predictsErgative
  rw [h_vis, Bool.true_and]
  exact sd_off_diagonal_iff_outranks subj obj h_neq

-- ============================================================================
-- § 5: Cell-by-cell verification of Table 4
-- ============================================================================

/-- @cite{clem-deal-2024} Table 4 (p. 19) — full ergative distribution
    over the 7 (subject, object) combinations × object position.
    All 10 cells reduce by `rfl` from `predictsErgative`. -/
example : -- row a (1→2): obligatory
    predictsErgative .first .second .high = true := rfl
example : -- row b high (1→3 high): present
    predictsErgative .first .third .high = true := rfl
example : -- row b low (1→3 low): absent
    predictsErgative .first .third .low = false := rfl
example : -- row c (2→1): impossible
    predictsErgative .second .first .high = false := rfl
example : -- row d high (2→3 high): present
    predictsErgative .second .third .high = true := rfl
example : -- row d low (2→3 low): absent
    predictsErgative .second .third .low = false := rfl
example : -- row e (3→1): impossible
    predictsErgative .third .first .high = false := rfl
example : -- row f (3→2): impossible
    predictsErgative .third .second .high = false := rfl
example : -- row g high (3→3 high): present
    predictsErgative .third .third .high = true := rfl
example : -- row g low (3→3 low): absent
    predictsErgative .third .third .low = false := rfl

/-- Optionality is exactly the `(✓)` cells: 1→3, 2→3, 3→3. -/
theorem optionality_only_with_3p_object (subj obj : PersonLevel) :
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
    (subj obj : PersonLevel) (h : obj ≠ .third) (pos : ObjectPosition) :
    predictsErgative subj obj pos = isLicit shawiGrammar subj obj := by
  cases obj
  · rfl
  · rfl
  · exact absurd rfl h

/-- Bookkeeping: for any local-person object, the Fragment-level
    `mustBeHigh` constraint forces the high position, which is exactly
    what the probe-visibility analysis presupposes. -/
theorem local_object_must_be_high (p : PersonLevel) (h : p ≠ .third) :
    mustBeHigh p = true := by
  cases p
  · rfl
  · rfl
  · exact absurd rfl h

-- ============================================================================
-- § 7: Counterexamples to configurational case (paper §4.1)
-- ============================================================================

/-- The simple configurational rule for ergative assignment from
    @cite{baker-2015}, paper (1): "if there are two distinct NPs in
    the same spell-out domain such that NP1 c-commands NP2, then
    value the case feature of NP1 as ergative unless NP2 has already
    been marked for case." Predicts ergative for *every* transitive
    subject. -/
def configurationalRulePredictsErg (_subj _obj : PersonLevel) : Bool := true

/-- The simple rule overgenerates 2→1: it predicts `-ri` on a 2P
    subject with a 1P object, but Shawi disallows it
    (@cite{clem-deal-2024} (4a), (7a)). -/
theorem configurational_rule_overgenerates_2_to_1 :
    configurationalRulePredictsErg .second .first = true ∧
    predictsErgative .second .first .high = false := ⟨rfl, rfl⟩

/-- And 3→1: same pattern (@cite{clem-deal-2024} (7b)). -/
theorem configurational_rule_overgenerates_3_to_1 :
    configurationalRulePredictsErg .third .first = true ∧
    predictsErgative .third .first .high = false := ⟨rfl, rfl⟩

/-- The augmented configurational rule from Bárány & Sheehan 2024,
    paper (37): "NP1 outranks NP2 on the person hierarchy 1>2>3"
    written into the configurational rule itself. Still overgenerates
    on 3→3 with low object: the rule fires (3 ≥ 3) but Shawi shows
    no `-ri` (@cite{clem-deal-2024} (23c), (24)). The Agree-based
    analysis predicts the absence because a low 3P object is invisible
    to the probe, so the subject is G1 rather than G2 — no goal
    flagging, no ergative. -/
def augmentedConfigRulePredictsErg (subj obj : PersonLevel) : Bool :=
  decide (subj.rank ≥ obj.rank)

theorem augmented_config_rule_overgenerates_3_3_low :
    augmentedConfigRulePredictsErg .third .third = true ∧
    predictsErgative .third .third .low = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 8: Object syntax — overt-postverbal blocked under ergative
-- ============================================================================

/-- @cite{clem-deal-2024} (9), (21): when the subject bears `-ri`,
    the object cannot remain overt-postverbal. This combines the
    Fragment-level `objectSyntaxLicit` with the predictedness of
    ergative — a high-object subject that outranks the object forces
    the object out of postverbal position (to OSV or *pro*-drop). -/
theorem outranking_subj_blocks_postverbal_obj
    (subj obj : PersonLevel) (h_neq : subj ≠ obj) (h_rank : subj.rank > obj.rank) :
    objectSyntaxLicit (predictsErgative subj obj .high) .overtPostverbal = false := by
  have h_erg : predictsErgative subj obj .high = true :=
    (erg_off_diagonal_iff_subj_outranks_obj subj obj h_neq).mpr h_rank
  rw [h_erg]
  rfl

/-- The fronted (OSV) and *pro*-drop options remain licit regardless
    of whether the subject bears `-ri`. -/
theorem fronted_and_prodropped_always_licit
    (subj obj : PersonLevel) (pos : ObjectPosition) :
    objectSyntaxLicit (predictsErgative subj obj pos) .overtFronted = true ∧
    objectSyntaxLicit (predictsErgative subj obj pos) .proDropped = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 9: OAgr-on-S correlation (@cite{clem-deal-2024} §4.3, fn. 7)
-- ============================================================================

/-- "Object agreement on subject" can spell out the inner φ-features of
    the goal-flag bundle that `-ri` exposes; if no such bundle is
    present (i.e., no ergative), there is nothing for the OAgr-on-S
    morpheme to attach to.

    We define availability by reusing `predictsErgative` directly,
    matching @cite{clem-deal-2024} §4.3's empirical generalization that
    OAgr-on-S obtains *only if* the subject is ergative. The non-trivial
    asymmetry (ergative *without* OAgr-on-S is grammatical; OAgr-on-S
    *without* ergative is not) is structurally true here only by
    construction; deriving it requires the goal-flagging machinery
    flagged in "Follow-ups". -/
def oagrOnSAvailable : PersonLevel → PersonLevel → ObjectPosition → Bool :=
  predictsErgative

/-- Inheriting the hierarchy bridge: OAgr-on-S is available off the
    diagonal iff the subject outranks the object — same pattern as
    `-ri` itself. -/
theorem oagrOnS_off_diagonal_iff_subj_outranks_obj
    (subj obj : PersonLevel) (h_neq : subj ≠ obj) :
    oagrOnSAvailable subj obj .high = true ↔ subj.rank > obj.rank :=
  erg_off_diagonal_iff_subj_outranks_obj subj obj h_neq

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
theorem high_object_matches_deal2024 (subj obj : PersonLevel) :
    predictsErgative subj obj .high = isLicit shawiGrammar subj obj := by
  cases obj <;> rfl

-- ============================================================================
-- § 11: What is *not* yet formalized
-- ============================================================================

/-! ## Follow-ups

`@cite{clem-deal-2024}`'s analysis crucially depends on three pieces of
machinery that linglib does not yet have:

1. **Bidirectional Agree (goal flagging)** — the probe-to-goal direction
   of feature transfer. Without this, the claim that `-ri` *is* the
   object's φ-features (rather than a primitive [ERG]) cannot be stated
   structurally. `Theories/Syntax/Minimalism/Core/Agree.lean` currently
   models only valuation (goal→probe).
2. **Distributed Morphology / Vocabulary Insertion** — for the VI rule
   `ri ↔ φ / ___ [φ,D]` (@cite{clem-deal-2024} (34)) and Kinyalolo's
   Constraint impoverishment ((35)). The `Core/Lexical/MorphRule.lean`
   skeleton is Bybee-flavored and does not yet capture context-sensitive
   realization.
3. **Feature provenance** — distinguishing "native" features on a goal
   from features deposited there by Agree (@cite{clem-deal-2024} fn. 23).
   Required to state the ergative VI without overgenerating.

Once (1)–(3) are in place, the OAgr-on-S correlation here can be
strengthened from a definitional implication to a derived theorem.
-/

end Phenomena.Agreement.Studies.ClemDeal2024
