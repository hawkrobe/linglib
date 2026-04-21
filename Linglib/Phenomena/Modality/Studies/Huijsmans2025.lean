import Linglib.Theories.Semantics.Tense.Evidential
import Linglib.Core.Modality.ModalTypes

/-!
# Huijsmans (2025) @cite{huijsmans-2025}

*Timing of evidence and epistemic modal claims.* Natural Language Semantics
33: 207–254.

The future morphemes *səm* (ʔayʔaǰuθəm; Central Salish) and *will* (English)
pattern with strong epistemic modals like *ćε* (ʔayʔaǰuθəm inferential) and
*must*, but their distributions diverge in inferences about non-future
eventualities. Huijsmans argues the difference is **temporal**, not modal
strength: *səm/will* presuppose the modal base is established **prior** to
the earliest moment the prejacent is claimed to hold, while *ćε* requires
at least one modal-base proposition to hold **at or following** that moment.

## Structural claim

The temporal-presupposition partition is structurally identical to the
EP-condition partition in `Theories/Semantics/Tense/Evidential.lean`,
but indexed on **MBT** (modal-base time) rather than **EAT** (evidence
acquisition time). `EPCondition` is reused under the slot reinterpretation
`MBT ↦ acquisitionTime`, `PrejT ↦ eventTime`. The bridge is
`MBTProfile.licenses_iff_EP`.

## Empirical wedge

Most of Huijsmans's stimuli (cooking, Daniel-home, poison) satisfy
`MBT < PrejT ∧ EAT < ET` — both analyses agree. The Felipe-rain stimulus
(ex. 46-49) and clam-digging stimulus (ex. 48-49) have `MBT < PrejT` but
`ET < EAT` — Huijsmans's MBT analysis correctly licenses *will/must*; an
EAT analysis (with the same partition reinterpreted) does not.
`MBT_vs_EAT_diverge_on_felipe` is the load-bearing theorem.

## At-issue content

The at-issue content is Kratzer strong necessity over the modal base,
shared across all four lexical entries (modulo modal-base type). It is
not formalized in this file; consumers wanting full denotations should
combine `Modal.flavor` with `Theories.Semantics.Modality.Kratzer.necessity`.
-/

namespace Phenomena.Modality.Studies.Huijsmans2025

open Semantics.Tense.Evidential (EPCondition EvidentialFrame)

-- ════════════════════════════════════════════════════
-- § 1. Stimulus: temporal anchors testable by both analyses
-- ════════════════════════════════════════════════════

/-- A stimulus context, supplying the four temporal anchors needed to
    state both Huijsmans's MBT predictions and the EAT predictions she
    is contrasted against. The MBT/EAT split lives in *which* pair of
    anchors a profile reads. -/
structure Stimulus (Time : Type) where
  /-- ⌜MBT⌝ — the maximum over `q ∈ MB` of `EARLIEST(SHIFT q)`, i.e.
      the latest "earliest moment" required by the modal base. -/
  earliestMBT   : Time
  /-- ⌜PrejT⌝ — `EARLIEST(p)` for the prejacent `p`. -/
  earliestPrejT : Time
  /-- The (Cumming/Hirayama-Matthewson) evidence-acquisition time. -/
  eat           : Time
  /-- The event time of the prejacent. -/
  et            : Time
  deriving Repr

-- ════════════════════════════════════════════════════
-- § 2. MBT-presupposition profiles
-- ════════════════════════════════════════════════════

/-- The three MBT-presupposition profiles Huijsmans's four lexical items
    instantiate. A domain-flavored selector over the abstract
    `Core.Time.Relation` partition (cf. `EPCondition` in
    `Tense/Evidential.lean`, which selects from the same partition for
    the EAT/ET slot pair). Only three of the five abstract relations
    name a Huijsmans modal; the others are unused here. -/
inductive MBTProfile where
  /-- `MBT < PrejT`. Modal base established strictly before the prejacent's
      earliest moment. *səm*, *will*. Eq. (35). -/
  | strictPrior
  /-- `PrejT ≤ MBT`. At least one MB proposition becomes true at or after the
      prejacent's earliest moment. *ćε*. Eq. (36). -/
  | nonProspective
  /-- No temporal restriction. *must*. -/
  | unrestricted
  deriving DecidableEq, Repr

/-- Underlying point-relation: the slot pair is `(earliestMBT, earliestPrejT)`,
    and each profile picks one shape from `Relation`. Mirrors
    `EPCondition.toRelation` in `Tense/Evidential.lean`. -/
def MBTProfile.toRelation : MBTProfile → Core.Time.Relation
  | .strictPrior    => .before
  | .nonProspective => .notBefore        -- PrejT ≤ MBT, i.e. MBT ≥ PrejT
  | .unrestricted   => .unrestricted

/-- The MBT-licensing predicate, derived from the abstract partition. -/
def MBTProfile.licenses {Time : Type} [LinearOrder Time]
    (c : MBTProfile) (s : Stimulus Time) : Prop :=
  c.toRelation.eval s.earliestMBT s.earliestPrejT

instance {Time : Type} [LinearOrder Time] [DecidableEq Time] (c : MBTProfile)
    (s : Stimulus Time) : Decidable (c.licenses s) := by
  unfold MBTProfile.licenses; infer_instance

-- ════════════════════════════════════════════════════
-- § 3. Lexical entries
-- ════════════════════════════════════════════════════

/-- A modal in the Huijsmans typology: a label, a (possibly underspecified)
    modal-flavor, and an MBT-presupposition profile. All four entries in
    this paper are necessity modals; force is omitted. -/
structure Modal where
  label   : String
  /-- Modal flavor, or `none` for underspecified (Huijsmans p. 218). -/
  flavor  : Option Core.Modality.ModalFlavor
  profile : MBTProfile
  deriving Repr

/-- ʔayʔaǰuθəm future clitic *səm*. Underspecified for modal base
    (epistemic and circumstantial uses; Huijsmans §2.3). -/
def sem  : Modal := ⟨"səm",  none,            .strictPrior⟩

/-- English future auxiliary *will*. Underspecified for modal base
    (epistemic in non-future-eventuality uses, circumstantial in
    future-eventuality uses; Huijsmans §2.4). -/
def will : Modal := ⟨"will", none,            .strictPrior⟩

/-- ʔayʔaǰuθəm inferential clitic *ćε*. Epistemic only. -/
def che  : Modal := ⟨"ćε",   some .epistemic, .nonProspective⟩

/-- English necessity modal *must*. Underspecified for modal base; this
    paper only treats epistemic uses. -/
def must : Modal := ⟨"must", none,            .unrestricted⟩

-- ════════════════════════════════════════════════════
-- § 4. Empirical contrasts (one Stimulus per Huijsmans table row)
-- ════════════════════════════════════════════════════

/-- (40) Cooking. The fish-cooking stimulus: MB props (fish in oven,
    typical cook time) hold prior to PrejT (it is cooked).
    Both MBT and EAT analyses predict *səm/will/must* ✓, *ćε* ✗. -/
def cooking : Stimulus Int :=
  { earliestMBT := 0, earliestPrejT := 2, eat := 0, et := 2 }

theorem cooking_table :
    will.profile.licenses cooking ∧
    sem.profile.licenses  cooking ∧
    must.profile.licenses cooking ∧
    ¬ che.profile.licenses cooking := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- (46) Felipe-rain. The wedge case. MB props (it is raining, Felipe has
    no rain jacket) become true earlier than PrejT (Felipe is wet), but
    the speaker only acquires the evidence later (sees the rain at 6pm,
    after Felipe has already gotten wet at 5pm). So `MBT < PrejT` but
    `ET < EAT`. Huijsmans correctly licenses *will/must*; an EAT analysis
    incorrectly rejects *will*. -/
def felipeRain : Stimulus Int :=
  { earliestMBT := 0, earliestPrejT := 1, eat := 3, et := 1 }

theorem felipe_table :
    will.profile.licenses felipeRain ∧
    must.profile.licenses felipeRain ∧
    ¬ che.profile.licenses felipeRain := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- (50) Smell-of-fish. The smell coincides with PrejT: at least one MB
    proposition (the fish smells cooked) holds at the moment the prejacent
    holds. *ćε/must* ✓, *səm/will* ✗. -/
def smellOfFish : Stimulus Int :=
  { earliestMBT := 1, earliestPrejT := 1, eat := 1, et := 1 }

theorem smell_table :
    che.profile.licenses  smellOfFish ∧
    must.profile.licenses smellOfFish ∧
    ¬ will.profile.licenses smellOfFish ∧
    ¬ sem.profile.licenses  smellOfFish := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════
-- § 5. The MBT-vs-EAT divergence theorem
-- ════════════════════════════════════════════════════

/-- The EAT-indexed analogue of `MBTProfile.licenses` — applies the same
    partition shape to `(eat, et)` instead of `(earliestMBT, earliestPrejT)`.
    Defined inline rather than imported from a (not-yet-existent)
    Hirayama-Matthewson study file. -/
def MBTProfile.eatLicenses {Time : Type} [LinearOrder Time] :
    MBTProfile → Stimulus Time → Prop
  | .strictPrior,    s => s.eat < s.et
  | .nonProspective, s => s.et ≤ s.eat
  | .unrestricted,   _ => True

instance {Time : Type} [LinearOrder Time] [DecidableEq Time] (c : MBTProfile)
    (s : Stimulus Time) : Decidable (c.eatLicenses s) := by
  cases c <;> simp [MBTProfile.eatLicenses] <;> infer_instance

/-- **The empirical wedge** (Huijsmans (46)–(49)).

    On the Felipe-rain stimulus the MBT and EAT analyses disagree on
    *will*: the MBT-analysis licenses it (matching the judgment), the
    EAT-analysis rejects it (mispredicting). This is the entire empirical
    content of Huijsmans's argument compressed to a single `decide`. -/
theorem MBT_vs_EAT_diverge_on_felipe :
      will.profile.licenses    felipeRain
    ∧ ¬ will.profile.eatLicenses felipeRain := by
  refine ⟨?_, ?_⟩ <;> decide

end Phenomena.Modality.Studies.Huijsmans2025
