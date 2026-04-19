import Linglib.Core.Logic.OT
import Linglib.Theories.Phonology.OptimalityTheory.Constraints
import Linglib.Core.Morphology.MorphProfile

/-!
# Doubling Theory: Identity vs. Reduplication

The theoretical framework for the double identity of doubling: the same
surface form XX is structurally ambiguous between phonological identity
(two independent identical segments, banned by OCP) and morphological
reduplication (RED + base, preferred when the morphological context
licenses it).

## Key types

- `DoublingFunction`: what morphological category doubling expresses
  (plurality, diminutive, etc.)
- `DoublingGrammar`: parameterizes the model by a speaker's L1 —
  which functions the L1 marks morphologically, and which it marks
  *by reduplication specifically*
- `DoublingParse`: the structural parse of a doubled form
- `realizeMorphAvailable`: derives whether REALIZE-MORPH is active for
  a given function from the L1's `DoublingGrammar`

## Positive and negative transfer

Following @cite{berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016}:

- **Positive transfer**: if the L1 expresses function *f* morphologically,
  speakers can interpret XX as morphological reduplication for *f*
- **Negative transfer**: if the L1 uses reduplication for *other* functions
  but specifically NOT for *f*, that blocks the reduplication
  interpretation for *f*

The `realizeMorphAvailable` predicate encodes both transfer directions:
REALIZE-MORPH is active for function *f* when (i) the L1 marks *f*
morphologically AND (ii) the L1 has no negative evidence (does not use
reduplication for other functions while excluding *f*).

@cite{berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016}
@cite{berent-2026}
-/

namespace Phonology.Doubling

open Core.OT
open Phonology.Constraints

-- ============================================================================
-- § 1: Doubling Functions
-- ============================================================================

/-- Morphological function that doubling can express.

    Different languages use reduplication for different morphological
    categories. The availability of the reduplication parse for a given
    semantic context depends on the speaker's L1 morphology. -/
inductive DoublingFunction where
  | plurality     -- e.g., Indonesian rumah-rumah 'houses'
  | diminutive    -- e.g., Hebrew seleg -> slaglag 'puppy'
  deriving DecidableEq, Repr

/-- Complete enumeration of `DoublingFunction` constructors.
    Used by `hasAnyRedup` so that adding a constructor automatically
    updates the check (compile will fail on `all_complete` if the
    list is not updated). -/
def DoublingFunction.all : List DoublingFunction := [.plurality, .diminutive]

theorem DoublingFunction.all_complete :
    ∀ f : DoublingFunction, f ∈ DoublingFunction.all := by
  intro f; cases f <;> simp [DoublingFunction.all]

-- ============================================================================
-- § 2: Doubling Grammar (L1 parameterization)
-- ============================================================================

/-- A speaker's L1 morphological knowledge relevant to interpreting
    doubled forms.

    Two dimensions determine whether a speaker interprets XX as
    morphological reduplication for function *f*:

    1. `morphFor f`: does the L1 express *f* by any morphological means?
       (Necessary for morphological interpretation of XX-as-f.)
    2. `redupFor f`: does the L1 express *f* specifically by reduplication?
       (Determines positive vs. negative transfer.) -/
structure DoublingGrammar where
  /-- Does the L1 express function *f* by any morphological means?
      E.g., English marks plurality (dog-s) but not diminutives productively. -/
  morphFor : DoublingFunction → Bool
  /-- Does the L1 express function *f* specifically by reduplication?
      E.g., Hebrew uses reduplication for diminutives but not plurality. -/
  redupFor : DoublingFunction → Bool

/-- Does the L1 use reduplication for any morphological function?

    Defined via `DoublingFunction.all` rather than manual disjunction.
    Adding a new constructor to `DoublingFunction` will cause
    `all_complete` to fail unless `all` is updated, which automatically
    extends this check. -/
def DoublingGrammar.hasAnyRedup (g : DoublingGrammar) : Bool :=
  DoublingFunction.all.any g.redupFor

/-- Is REALIZE-MORPH available for function *f* given the speaker's L1?

    REALIZE-MORPH is active when:
    (i) the L1 expresses *f* morphologically (`morphFor f`), AND
    (ii) there is no negative transfer — if the L1 uses reduplication
         at all, it must include *f* among the functions expressed by
         reduplication.

    Negative transfer (@cite{berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016}):
    when a speaker's L1 uses reduplication for function A but not B,
    the speaker has positive evidence that reduplication != B. This
    blocks the reduplication parse for B even if B is morphologically
    marked by other means. -/
def realizeMorphAvailable (g : DoublingGrammar) (f : DoublingFunction) : Bool :=
  g.morphFor f && (!g.hasAnyRedup || g.redupFor f)

-- ============================================================================
-- § 2b: Structural properties of transfer
-- ============================================================================

/-- No morphology → no REALIZE-MORPH, regardless of reduplication status.

    This is the prerequisite: the L1 must express *f* morphologically
    at all before the reduplication parse is even considered. -/
theorem no_morph_no_realizeMorph (g : DoublingGrammar) (f : DoublingFunction)
    (h : g.morphFor f = false) :
    realizeMorphAvailable g f = false := by
  simp [realizeMorphAvailable, h]

/-- Without productive reduplication, there is no negative transfer:
    REALIZE-MORPH availability reduces to whether the L1 marks *f*
    morphologically.

    This is why English-type grammars (no productive reduplication)
    have no negative transfer — without reduplication in the L1,
    there is no evidence against any particular function. -/
theorem no_redup_no_negative_transfer (g : DoublingGrammar) (f : DoublingFunction)
    (h : g.hasAnyRedup = false) :
    realizeMorphAvailable g f = g.morphFor f := by
  simp only [realizeMorphAvailable, h, Bool.not_false, Bool.true_or,
    Bool.and_true]

/-- When the L1 uses reduplication for *f* AND marks *f* morphologically,
    REALIZE-MORPH is available (positive transfer).

    This is why Hebrew diminutives get positive transfer: Hebrew uses
    reduplication specifically for diminutives. -/
theorem redup_positive_transfer (g : DoublingGrammar) (f : DoublingFunction)
    (hm : g.morphFor f = true) (hr : g.redupFor f = true) :
    realizeMorphAvailable g f = true := by
  simp only [realizeMorphAvailable, hm, hr, Bool.true_and,
    DoublingGrammar.hasAnyRedup, DoublingFunction.all, List.any]
  cases f <;> simp_all

/-- When the L1 uses reduplication for some function but NOT for *f*,
    negative transfer blocks REALIZE-MORPH for *f* even if *f* is
    morphologically marked.

    This is why Hebrew speakers disprefer XX for plurality: Hebrew
    uses reduplication for diminutives but not plurality, providing
    evidence that reduplication != plurality. -/
theorem redup_negative_transfer (g : DoublingGrammar) (f : DoublingFunction)
    (hany : g.hasAnyRedup = true) (hnot : g.redupFor f = false) :
    realizeMorphAvailable g f = false := by
  simp only [realizeMorphAvailable, hany, Bool.not_true, Bool.false_or,
    hnot, Bool.and_false]

/-- Complete characterization of `realizeMorphAvailable`: the four
    transfer theorems above exhaust all cases. Every combination of
    `morphFor f`, `hasAnyRedup`, and `redupFor f` is covered.

    This is the mathlib-style exhaustive case analysis: any function
    satisfying these four properties agrees with `realizeMorphAvailable`
    on all inputs. -/
theorem realizeMorphAvailable_complete (g : DoublingGrammar) (f : DoublingFunction) :
    (g.morphFor f = false → realizeMorphAvailable g f = false) ∧
    (g.morphFor f = true → g.hasAnyRedup = false →
      realizeMorphAvailable g f = true) ∧
    (g.morphFor f = true → g.redupFor f = true →
      realizeMorphAvailable g f = true) ∧
    (g.hasAnyRedup = true → g.redupFor f = false →
      realizeMorphAvailable g f = false) :=
  ⟨no_morph_no_realizeMorph g f,
   fun hm h => by rw [no_redup_no_negative_transfer g f h, hm],
   redup_positive_transfer g f,
   redup_negative_transfer g f⟩

-- ============================================================================
-- § 2c: Monotonicity
-- ============================================================================

/-- `redupFor` is NOT monotone: adding reduplication for another function
    can block REALIZE-MORPH for *f* (negative transfer).

    Witness: g₁ has no reduplication and marks plurality morphologically,
    so REALIZE-MORPH is available. g₂ adds reduplication for diminutives
    only. Now REALIZE-MORPH for plurality is blocked — the speaker has
    evidence that reduplication ≠ plurality. -/
theorem redupFor_not_monotone :
    ∃ (g₁ g₂ : DoublingGrammar) (f : DoublingFunction),
      g₁.morphFor = g₂.morphFor ∧
      (∀ x, g₁.redupFor x = true → g₂.redupFor x = true) ∧
      realizeMorphAvailable g₁ f = true ∧
      realizeMorphAvailable g₂ f = false := by
  refine ⟨
    ⟨fun | .plurality => true | .diminutive => true,
     fun | .plurality => false | .diminutive => false⟩,
    ⟨fun | .plurality => true | .diminutive => true,
     fun | .plurality => false | .diminutive => true⟩,
    .plurality, rfl, ?_, ?_, ?_⟩
  · intro x; cases x <;> simp
  · decide
  · decide

-- ============================================================================
-- § 2d: Bridge to MorphProfile
-- ============================================================================

open Core.Morphology (Reduplication)

/-- Languages without productive reduplication (WALS Ch 27) have no
    reduplication for any `DoublingFunction`.

    This connects the `DoublingGrammar` framework to the coarse-grained
    `MorphProfile.Reduplication` typology: if `Reduplication = .noProductive`,
    then `redupFor f = false` for all *f*, which means `hasAnyRedup = false`
    and negative transfer is impossible (by `no_redup_no_negative_transfer`). -/
def noRedupGrammar (morphFor : DoublingFunction → Bool) : DoublingGrammar :=
  { morphFor := morphFor
    redupFor := fun _ => false }

theorem noRedupGrammar_no_redup (morphFor : DoublingFunction → Bool) :
    (noRedupGrammar morphFor).hasAnyRedup = false := by
  simp [noRedupGrammar, DoublingGrammar.hasAnyRedup, DoublingFunction.all, List.any]

/-- For languages without productive reduplication, REALIZE-MORPH
    availability equals `morphFor f` — no negative transfer is possible.
    Connects `MorphProfile.reduplication = .noProductive` to the
    doubling predictions. -/
theorem noRedup_realizeMorph (morphFor : DoublingFunction → Bool)
    (f : DoublingFunction) :
    realizeMorphAvailable (noRedupGrammar morphFor) f = morphFor f :=
  no_redup_no_negative_transfer _ f (noRedupGrammar_no_redup morphFor)

-- ============================================================================
-- § 3: Doubling Parses
-- ============================================================================

/-- Parse of a doubled form XX.

    The same surface form XX is structurally ambiguous between two parses:

    - **Identity** (phonological): two independent identical segments.
      Banned by OCP — the phonological grammar disprefers it.

    - **Reduplication** (morphological): a RED morpheme copies the base.
      Preferred when the morphological context licenses it.

    - **Nonidentical**: XY control (no doubling). -/
inductive DoublingParse where
  | identity       -- phonological: two independent identical units
  | reduplication   -- morphological: RED + base
  | nonidentical    -- XY control: no doubling
  deriving DecidableEq, Repr

-- ============================================================================
-- § 4: OT Constraints on Doubling
-- ============================================================================

/-- OCP-XX: penalizes phonological identity.
    Violated by the identity parse, not by reduplication or XY.

    Conceptually related to the general `mkOCP` constraint in
    `Constraints.lean` (both penalize adjacent identity), but operates
    at a different level of abstraction: `mkOCP` counts adjacent
    identical pairs on a feature tier, while `ocpXX` classifies the
    *parse* of a doubled form as phonological identity vs. morphological
    reduplication. -/
def ocpXX : NamedConstraint DoublingParse :=
  mkMark "OCP-XX" (· == .identity)

/-- *RED: general markedness against reduplication.
    Violated by the reduplicative parse (morphological cost of RED). -/
def starRED : NamedConstraint DoublingParse :=
  mkMark "*RED" (· == .reduplication)

/-- REALIZE-MORPH: faithfulness to the morphological specification.
    When the input specifies a morphological operation (e.g., plurality
    expressed via reduplication), the output must realize it.

    Violated by the nonidentical parse (XY doesn't express the
    morphological specification). Active only when the speaker's L1
    makes the reduplication interpretation available for the relevant
    morphological function (see `realizeMorphAvailable`). -/
def realizeMorph : NamedConstraint DoublingParse :=
  mkMax "REALIZE-MORPH" (· == .nonidentical)

-- ============================================================================
-- § 5: Rankings and Candidate Sets
-- ============================================================================

/-- Phonological ranking: only OCP-XX and *RED are active.
    REALIZE-MORPH is absent (no morphological specification). -/
def phonRanking : List (NamedConstraint DoublingParse) :=
  [ocpXX, starRED]

/-- Morphological ranking: OCP-XX >> REALIZE-MORPH >> *RED.
    Active when the morphological context licenses reduplication
    AND the speaker's L1 makes it available. -/
def morphRanking : List (NamedConstraint DoublingParse) :=
  [ocpXX, realizeMorph, starRED]

/-- Candidates in a phonological context or when reduplication is
    unavailable: identity or nonidentical. Reduplication is not
    a candidate (no morphological trigger or no L1 support). -/
def phonCandidates : List DoublingParse := [.identity, .nonidentical]

/-- Candidates in a morphological context where reduplication is
    available: all three parses compete. -/
def morphCandidates : List DoublingParse :=
  [.identity, .reduplication, .nonidentical]

-- ============================================================================
-- § 6: L1-Parameterized Model
-- ============================================================================

/-- Candidate set for a given L1 and morphological function.
    Reduplication is a candidate only when the L1 makes it available
    for the relevant function. -/
def l1CandidatesFor (g : DoublingGrammar) (f : DoublingFunction) :
    List DoublingParse :=
  if realizeMorphAvailable g f then morphCandidates else phonCandidates

/-- Constraint ranking for a given L1 and morphological function.
    REALIZE-MORPH is in the ranking only when the L1 makes it
    available for the relevant function. -/
def l1RankingFor (g : DoublingGrammar) (f : DoublingFunction) :
    List (NamedConstraint DoublingParse) :=
  if realizeMorphAvailable g f then morphRanking else phonRanking

theorem l1CandidatesFor_ne (g : DoublingGrammar) (f : DoublingFunction) :
    l1CandidatesFor g f ≠ [] := by
  simp only [l1CandidatesFor]
  split <;> simp [morphCandidates, phonCandidates]

-- ============================================================================
-- § 7: Core OT Predictions
-- ============================================================================

/-- In phonological contexts (no morphological trigger), XY wins.
    OCP-XX bans identity; *RED is irrelevant since reduplication
    is not a candidate. -/
theorem phon_prefers_XY :
    (mkTableau phonCandidates phonRanking).optimal
    = {.nonidentical} := by decide

/-- In morphological contexts where reduplication is available,
    reduplication wins. OCP-XX bans identity; REALIZE-MORPH bans
    nonidentical; reduplication violates only low-ranked *RED. -/
theorem morph_prefers_reduplication :
    (mkTableau morphCandidates morphRanking).optimal
    = {.reduplication} := by decide

/-- The phonology--morphology reversal: context determines which
    constraints are active, producing opposite surface preferences
    from the same underlying OCP-XX. -/
theorem doubling_reversal :
    (mkTableau phonCandidates phonRanking).optimal
      = {.nonidentical} ∧
    (mkTableau morphCandidates morphRanking).optimal
      = {.reduplication} := by
  exact ⟨phon_prefers_XY, morph_prefers_reduplication⟩

end Phonology.Doubling
