import Linglib.Theories.Syntax.Minimalism.Selection
import Linglib.Theories.Syntax.Minimalism.FromFragments

/-!
# Adger 2003: C-Selection and Subcategorization @cite{adger-2003}

Replicates Adger's c-selection account of subcategorization
(*Core Syntax* ch. 3 §3.5–§3.6) on linglib's Minimalism substrate via the
`Derivation.WellFormed` predicate from
`Theories/Syntax/Minimalism/Selection.lean`.

## Adger's apparatus (recap)

Each lexical head bears interpretable categorial features [F] (e.g. [V] for
verbs) and uninterpretable c-selectional features [uG] (e.g. [uN] for
transitive verbs). Adger's checking system:

- (104) **Full Interpretation**: structure at the semantic interface
  contains no uninterpretable features
- (105) **Checking Requirement**: uninterpretable [uF] must be checked, and
  once checked deletes
- (106) **Checking under Sisterhood**: [uF] on Y is checked when Y is
  sister to Z bearing matching [F]
- (110) `kiss [V, uN]`: V interpretable, uN uninterpretable
- (114) `*Anson demonized` is bad because *demonize*'s [uN] is unchecked

## Substrate mapping

| Adger                  | linglib                                       |
|------------------------|-----------------------------------------------|
| interpretable [F]      | `SimpleLI.cat : Cat`                          |
| uninterpretable [uG]   | `SimpleLI.sel : SelStack` (a `List Cat`)      |
| Full Interpretation    | `Derivation.WellFormed` (Selection.lean)      |
| first Merge / complement | `Step.emR` (consumes one `pending` feature) |
| second Merge / specifier | `Step.emL` (no consumption)                 |

`verbToSelStack` (in `Theories/Syntax/Minimalism/Derivations.lean`) derives
the SelStack from `VerbEntry.complementType`:

| complementType | SelStack    | English class |
|----------------|-------------|---------------|
| `.none`        | `[]`        | intransitive  |
| `.np`          | `[.D]`      | transitive    |
| `.np_np`       | `[.D, .D]`  | ditransitive  |

## Sections

- §1 grammatical proper-noun derivations are well-formed
- §2 ungrammatical c-selection violations fail well-formedness
- §3 `subcategorization_data_match` agrees with
  `Phenomena.ArgumentStructure.Subcategorization.data`
- §4 substrate finding: bare common nouns expose a known limitation in
  the canonical `Derivations.lean` derivations
- §5 resolution: Adger ch. 7's null-D wrapper (`nullDWrap` in
  `Selection.lean`) projects bare common nouns as DPs that satisfy verbs'
  [uD] c-selection
-/

namespace Adger2003

open Minimalism Minimalism.FromFragments

/-! ## §0: Lexicon — Fragment-grounded SO building blocks

Migrated from the deleted `Theories/Syntax/Minimalism/Derivations.lean`;
instances belong in Phenomena per the architecture audit. Each SO is a
leaf with `Cat` and `SelStack` derived from its Fragment lexical entry.

### LIToken id allocation (one-derivation scope)

Every leaf carries a `Nat` id used by `Step.im`/movement to identify
chains. The scheme below partitions ids into ranges so that ids are
distinct across SOs that may co-occur in a derivation:

| Range       | Use                                  |
|-------------|--------------------------------------|
| 1–9         | Pronouns                             |
| 10–19       | Proper-noun DPs                      |
| 20–29       | Common-noun bare Ns                  |
| 30–39       | Verb leaves                          |
| 40–49       | Determiners                          |
| 100–199     | §2 ungrammatical-derivation seeds    |
| 200–299     | §5 null-D-wrapped derivation seeds   |
| 9000+       | Silent / null-D heads (`nullDWrap`)  |
-/

-- Pronouns
def heSO : SyntacticObject := pronounToSO Fragments.English.Pronouns.he 1
def herSO : SyntacticObject := pronounToSO Fragments.English.Pronouns.her 2
def theySO : SyntacticObject := pronounToSO Fragments.English.Pronouns.they 3

-- Proper nouns (project as DPs per Longobardi 1994 / @cite{adger-2003} ch. 7)
def johnSO : SyntacticObject := nounToSO Fragments.English.Nouns.john 10
def marySO : SyntacticObject := nounToSO Fragments.English.Nouns.mary 11

-- Common nouns (bare N — see §4 / §5 for the null-D wrapping treatment)
def catSO : SyntacticObject := nounToSO Fragments.English.Nouns.cat 20
def pizzaSO : SyntacticObject := nounToSO Fragments.English.Nouns.pizza 21
def bookSO : SyntacticObject := nounToSO Fragments.English.Nouns.book 22

-- Verbs
def sleepsSO : SyntacticObject :=
  verbToSO Fragments.English.Predicates.Verbal.sleep 30
def seesSO : SyntacticObject :=
  verbToSO Fragments.English.Predicates.Verbal.see 31
def eatsSO : SyntacticObject :=
  verbToSO Fragments.English.Predicates.Verbal.eat 32
def arrivesSO : SyntacticObject :=
  verbToSO Fragments.English.Predicates.Verbal.arrive 33
def devoursSO : SyntacticObject :=
  verbToSO Fragments.English.Predicates.Verbal.devour 34
def givesSO : SyntacticObject :=
  verbToSO Fragments.English.Predicates.Verbal.give 35

-- Determiner
def theSO : SyntacticObject := mkLeafPhon .D [.N] "the" 40

-- ============================================================================
-- §0.5: Canonical English Derivations
-- (The 9 derivations migrated from the deleted Derivations.lean. Reference
-- by all subsequent sections; each derivation builds a tree via `Step.apply`
-- without c-selection checking — `WellFormed` (§1) layers checking on top.)
-- ============================================================================

/-- "John sleeps": `[S John sleeps]` — intransitive. -/
def john_sleeps : Derivation :=
  { initial := sleepsSO, steps := [.emL johnSO] }

/-- "Mary arrives": `[S Mary arrives]` — intransitive. -/
def mary_arrives : Derivation :=
  { initial := arrivesSO, steps := [.emL marySO] }

/-- "John sees Mary": `[S John [VP sees Mary]]` — transitive. -/
def john_sees_mary : Derivation :=
  { initial := seesSO, steps := [.emR marySO, .emL johnSO] }

/-- "Mary sees John" — transitive variant. -/
def mary_sees_john : Derivation :=
  { initial := seesSO, steps := [.emR johnSO, .emL marySO] }

/-- "He sees her": pronouns project D directly. -/
def he_sees_her : Derivation :=
  { initial := seesSO, steps := [.emR herSO, .emL heSO] }

/-- "Mary eats pizza": transitive with bare common-noun complement. -/
def mary_eats_pizza : Derivation :=
  { initial := eatsSO, steps := [.emR pizzaSO, .emL marySO] }

/-- "The cat eats pizza": determiner+N subject, bare common-noun object. -/
def the_cat_eats_pizza : Derivation :=
  { initial := eatsSO, steps := [.emR pizzaSO, .emL (merge theSO catSO)] }

/-- "John devours pizza": transitive with bare common-noun complement. -/
def john_devours_pizza : Derivation :=
  { initial := devoursSO, steps := [.emR pizzaSO, .emL johnSO] }

/-- "John gives Mary book": ditransitive. (Word order is *gives book Mary*
    in linearization — see substantive note in the audit; the Larson 1988
    shell would put goal *Mary* as inner complement and theme *the book*
    as outer.) -/
def john_gives_mary_book : Derivation :=
  { initial := givesSO
    steps := [.emR bookSO, .emR marySO, .emL johnSO] }

-- ============================================================================
-- §1: Grammatical Derivations Are Well-Formed
-- (Restricted to proper-noun and pronominal complements, which project D
-- and so satisfy verbs' [.D] c-selection.)
-- ============================================================================

/-- "John sleeps" — intransitive: empty `pending` stack consumed trivially. -/
theorem john_sleeps_wellFormed : john_sleeps.WellFormed := by decide

/-- "Mary arrives" — intransitive variant. -/
theorem mary_arrives_wellFormed : mary_arrives.WellFormed := by decide

/-- "John sees Mary" — transitive: *see*'s [.D] is checked by *Mary*'s D. -/
theorem john_sees_mary_wellFormed : john_sees_mary.WellFormed := by decide

/-- "Mary sees John" — symmetric variant. -/
theorem mary_sees_john_wellFormed : mary_sees_john.WellFormed := by decide

/-- "He sees her" — pronouns also project D, so this checks too. -/
theorem he_sees_her_wellFormed : he_sees_her.WellFormed := by decide

-- ============================================================================
-- §2: Ungrammatical Derivations Fail Well-Formedness
-- (@cite{adger-2003} eq. 114: unchecked [uF] violates Full Interpretation.)
-- ============================================================================

/-- "*Mary arrives John" — intransitive with spurious complement.
    *arrive*'s `pending = []` so the `emR john` step has nothing to check
    against and `applyChecked` returns `none`. -/
def mary_arrives_john_bad : Derivation :=
  { initial := verbToSO Fragments.English.Predicates.Verbal.arrive 100
    steps   := [.emR (nounToSO Fragments.English.Nouns.john 101),
                .emL (nounToSO Fragments.English.Nouns.mary 102)] }

/-- "*John sees" — transitive missing required complement.
    *see*'s [.D] is never checked, so the final `pending = [.D]` ≠ `[]`. -/
def john_sees_bad : Derivation :=
  { initial := verbToSO Fragments.English.Predicates.Verbal.see 110
    steps   := [.emL (nounToSO Fragments.English.Nouns.john 111)] }

theorem mary_arrives_john_not_wellFormed :
    ¬ mary_arrives_john_bad.WellFormed := by decide

theorem john_sees_not_wellFormed :
    ¬ john_sees_bad.WellFormed := by decide

-- ============================================================================
-- §3: Bridge to Subcategorization Data
-- ============================================================================

/-- Adger's c-selection predictions agree with
    `Phenomena.ArgumentStructure.Subcategorization.data` on the
    proper-noun fragment of the contrast set:

    | Frame         | Grammatical    | Ungrammatical          |
    |---------------|----------------|------------------------|
    | intransitive  | "John sleeps"  | "*Mary arrives John"   |
    | transitive    | "John sees Mary" | "*John sees"         |

    The full data file's bare-common-noun examples are addressed in §4. -/
theorem subcategorization_data_match :
    john_sleeps.WellFormed
    ∧ ¬ mary_arrives_john_bad.WellFormed
    ∧ john_sees_mary.WellFormed
    ∧ ¬ john_sees_bad.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- §4: Substrate Finding — Bare Common Nouns
-- ============================================================================

/-! ### Bare common nouns under strict c-selection

The existing `*_pizza` / `*_book` derivations in
`Theories/Syntax/Minimalism/Derivations.lean` use bare common nouns
(`cat = .N` per `nounToSO` for non-proper entries) as direct objects of
verbs that c-select [.D]. Per Adger ch. 7 *Functional Categories II — the
DP*, bare common nouns require null-D wrapping to project as DPs and check
verbs' [uD]. linglib's substrate currently encodes common nouns as N
without this wrapping, so strict c-selection flags these derivations as
ill-formed even though their *intended* English glosses are grammatical.

This is a substrate-encoding artifact, not a pedagogical ill-formedness.
Resolving it requires one of:
  (a) introducing a null-D wrapper for bare common nouns (Adger ch. 7);
  (b) allowing verbs to alternately c-select N (counter to standard
      Minimalism);
  (c) treating bare common nouns as having an implicit kind-denoting D
      feature.

Out of scope for this study; the well-formedness predicate's strictness
makes the gap visible (rather than silently passing), which is what
linglib aims for. The three `example`s below pin the current behaviour. -/

/-- "John devours pizza" with bare *pizza* (.N) fails *devour*'s [uD]. -/
theorem john_devours_pizza_not_wellFormed_bare :
    ¬ john_devours_pizza.WellFormed := by decide

/-- "Mary eats pizza" — same pattern with *eat*. -/
theorem mary_eats_pizza_not_wellFormed_bare :
    ¬ mary_eats_pizza.WellFormed := by decide

/-- "John gives Mary book" — *book* (.N) is the inner complement and
    fails *give*'s first [uD]. -/
theorem john_gives_mary_book_not_wellFormed_bare :
    ¬ john_gives_mary_book.WellFormed := by decide

-- ============================================================================
-- §5: Resolution via Adger ch. 7 — null-D wrapping
-- ============================================================================

/-! ### Null-D-wrapped DPs are well-formed

@cite{adger-2003} ch. 7 (Functional Categories II — the DP) treats bare
common nouns as DPs headed by a phonologically silent D. `Selection.lean`
provides `nullDWrap : SyntacticObject → Nat → SyntacticObject`, which
constructs `(∅ᴅ, n)`: the silent D's [uN] feature is checked internally
against the noun's .N, yielding a saturated DP with `outerCat = .D` and
`checkedSel = some []`.

The parallel `*_DP` derivations below mirror the canonical sentences from
`Derivations.lean` but route the common-noun complement through `nullDWrap`,
producing well-formed structures. The phonYield is unchanged because
`nullD` has an empty `phonForm`. -/

/-- Bare *pizza* (cat = .N) wrapped under null D, projecting a saturated DP. -/
def pizzaDP : SyntacticObject :=
  nullDWrap (nounToSO Fragments.English.Nouns.pizza 200) 9200

/-- Bare *book* under null D. -/
def bookDP : SyntacticObject :=
  nullDWrap (nounToSO Fragments.English.Nouns.book 201) 9201

/-- "John devours pizza" with null-D-wrapped DP complement.
    *devour*'s [uD] is checked by the wrapped DP's outer .D. -/
def john_devours_pizza_DP : Derivation :=
  { initial := verbToSO Fragments.English.Predicates.Verbal.devour 210
    steps   := [.emR pizzaDP,
                .emL (nounToSO Fragments.English.Nouns.john 220)] }

/-- "Mary eats pizza" — same pattern with *eat*. -/
def mary_eats_pizza_DP : Derivation :=
  { initial := verbToSO Fragments.English.Predicates.Verbal.eat 211
    steps   := [.emR pizzaDP,
                .emL (nounToSO Fragments.English.Nouns.mary 221)] }

/-- "John gives Mary book": ditransitive with *book* as inner complement
    (direct object) wrapped under null D, *Mary* as proper-noun outer
    complement (indirect object). Both [uD] features on *give* are checked. -/
def john_gives_mary_book_DP : Derivation :=
  { initial := verbToSO Fragments.English.Predicates.Verbal.give 212
    steps   := [.emR bookDP,
                .emR (nounToSO Fragments.English.Nouns.mary 222),
                .emL (nounToSO Fragments.English.Nouns.john 223)] }

theorem john_devours_pizza_DP_wellFormed :
    john_devours_pizza_DP.WellFormed := by decide

theorem mary_eats_pizza_DP_wellFormed :
    mary_eats_pizza_DP.WellFormed := by decide

theorem john_gives_mary_book_DP_wellFormed :
    john_gives_mary_book_DP.WellFormed := by decide

/-! ### Surface form

By construction, `nullD`'s `phonForm` is empty, so the null-D-wrapped
derivations linearize to the same surface strings as the canonical bare-
noun derivations — only the internal structure differs. PhonYield equality
theorems analogous to `Derivations.lean`'s `*_phon` are deferred: the
`foldl`-over-steps + nested `phonYield` append exceeds `decide`'s
reduction budget and is not closeable by `rfl`, and the existing
`Derivations.lean` precedent (`native_decide`) is non-mathlib-compatible
per CLAUDE.md. A structured proof via explicit unfolding lemmas is the
right next step but out of scope here. -/

/-- Combined: the §4 ill-formed bare-noun derivations and the §5
    null-D-wrapped DP derivations form a minimal pair that operationalises
    Adger ch. 7's claim that argumental nominals are DPs. -/
theorem nullD_resolves_substrate_finding :
    ¬ john_devours_pizza.WellFormed ∧ john_devours_pizza_DP.WellFormed
    ∧ ¬ mary_eats_pizza.WellFormed ∧ mary_eats_pizza_DP.WellFormed
    ∧ ¬ john_gives_mary_book.WellFormed ∧ john_gives_mary_book_DP.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Adger2003
