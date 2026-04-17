import Linglib.Phenomena.Agreement.Studies.Deal2024

/-!
# Sakha Accusative as Dependent Case via Agree @cite{baker-vinokurova-2010}

@cite{clem-deal-2024} §5.1 reanalyzes the Sakha (Turkic) accusative
pattern of @cite{baker-vinokurova-2010} as the **mirror image** of
Shawi ergative under the same Agree-based framework:

- A T probe with `[INT:φ, SAT:-]` (insatiable, no dynamic interaction)
  Agrees first with the subject (G1, since T is structurally above v),
  then with the object (G2). @cite{clem-deal-2024} (40)–(41).
- Object accusative is dependent case: the spell-out on G2 of features
  transferred from G1.
- Sakha shows DOM conditioned by definiteness/specificity and by word
  order: high (= scrambled out of vP) objects participate in Agree
  with T and receive `-y` (or `-ny`) ACC; low objects do not.
  @cite{baker-vinokurova-2010}, paper (42), (44).

This file states the *Directionality Correlation*
(@cite{clem-deal-2024} §5.1): the location of the probe (low = on v
vs. high = on T) determines whether dependent case spells out on the
subject (ergative; cf. `ClemDeal2024.lean`) or on the object
(accusative; this file). The grammar parameters (SAT/INT) determine
the hierarchy effect; the probe location determines which argument
bears the spell-out.

The `noPCC` Deal grammar (= insatiable, no dynamic interaction)
already lives in `Phenomena/Agreement/Studies/Deal2024.lean`. The
Sakha analysis reuses it; the only Sakha-specific machinery is
flipping the G1/G2 assignments (probe is high, so G1 = subject) and
adding object visibility (high vs low objects).

Note: this is a typology stub. The full Sakha case system (genitive
on raised possessors, dative, partitive) and the
definiteness/specificity conditioning of object scrambling are not
formalized here; the goal is to expose the structural parallel to
Shawi via shared Deal-2024 infrastructure.
-/

namespace Phenomena.Agreement.Studies.BakerVinokurova2010

open Core.Prominence (PersonLevel)
open Deal2024 (DealGrammar isLicit noPCC nopcc_all_licit nopcc_licit_count)

-- ============================================================================
-- § 1: Probe specification
-- ============================================================================

/-- The Sakha T probe is insatiable (`SAT:-`) and has no dynamic
    interaction. @cite{clem-deal-2024} §5.1, paper (40)–(41). -/
def sakhaGrammar : DealGrammar := noPCC

/-- Sakha's grammar is the same as the "no PCC" / Double-Weakness
    profile that Deal-2024 uses for Nez Perce ergative
    (@cite{deal-2010}) and Amahuaca (@cite{clem-2019}). -/
theorem sakha_is_noPCC : sakhaGrammar = noPCC := rfl

-- ============================================================================
-- § 2: Object position and visibility
-- ============================================================================

/-- Position of the object relative to the T probe's effective domain
    after subject-Agree. @cite{baker-vinokurova-2010}, paper (42):
    object position correlates with VP-adverbs and with the placement
    of indirect objects. -/
inductive ObjectPosition where
  | low    -- inside vP, below the relevant boundary
  | high   -- scrambled to a position visible to T as G2
  deriving DecidableEq, Repr

/-- Object visibility to T after subject Agree as G1. Only high
    (= scrambled) objects participate. -/
def objectVisible : ObjectPosition → Bool
  | .low  => false
  | .high => true

-- ============================================================================
-- § 3: Predicted accusative
-- ============================================================================

/-- Predict whether the object bears the accusative suffix. Two factors:
    1. The object must be visible to T (`objectVisible`).
    2. T must be able to Agree with both args — `isLicit` for the
       insatiable `noPCC` grammar is *true* for every (subj, obj)
       pair, so this conjunct contributes nothing in Sakha. The
       conjunction is preserved here for parallelism with Shawi's
       `predictsErgative` and to stay open to future grammars where
       the second conjunct does constrain the prediction. -/
def predictsAccusative
    (subj obj : PersonLevel) (pos : ObjectPosition) : Bool :=
  objectVisible pos && isLicit sakhaGrammar subj obj

-- ============================================================================
-- § 4: Verification
-- ============================================================================

/-- High (= scrambled) object always receives ACC, regardless of person
    of either argument — Sakha has no person-hierarchy effect on
    accusative because the probe is insatiable and never narrows.
    @cite{baker-vinokurova-2010}, paper (42a). -/
theorem acc_high_obj_always (subj obj : PersonLevel) :
    predictsAccusative subj obj .high = true := by
  unfold predictsAccusative objectVisible
  rw [Bool.true_and]
  exact nopcc_all_licit subj obj

/-- Low object never receives ACC: it is invisible to T, so the only
    Agree relation is between T and the subject. @cite{baker-vinokurova-2010},
    paper (42b). -/
theorem acc_low_obj_blocked (subj obj : PersonLevel) :
    predictsAccusative subj obj .low = false := by
  cases subj <;> cases obj <;> rfl

-- ============================================================================
-- § 5: Directionality Correlation (paper §5.1)
-- ============================================================================

/-! @cite{clem-deal-2024} §5.1 (paper (43)): the Sakha ACC vocabulary
item `y ↔ φ / ___ [φ,D]` is *identical* to the Shawi ERG VI (paper
(34)) modulo phonological form. Both spell out the φ-bundle of a
*previous* Agree partner on a current goal — the difference between
ergative and accusative is purely the location of the probe (v vs T)
and hence which argument is G1 vs G2.

This is the **Directionality Correlation**: forward hierarchy patterns
+ low probe ⇒ ergative on subject; forward hierarchy patterns + high
probe ⇒ accusative on object; analogous "reverse" patterns are
attested cross-linguistically (cf. Yurok, Shapsug Adyghe).

The full directionality typology (Shiwilu strong PCC, Yurok reverse
strong PCC, Kolyma Yukaghir weak PCC) requires per-language stubs
that are out of scope here — they would each instantiate a different
Deal-2024 grammar with a different probe location and reuse the
G1/G2-flipping machinery introduced above.
-/

end Phenomena.Agreement.Studies.BakerVinokurova2010
