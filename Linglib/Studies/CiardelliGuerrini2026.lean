import Linglib.Semantics.Modality.ModalTypes
import Linglib.Fragments.English.Auxiliaries
import Linglib.Semantics.Exhaustification.FreeChoice
import Mathlib.Data.Set.Basic

/-!
# Against wide scope free choice ([ciardelli-guerrini-2026])

The free-choice reading of "you may A or you may B" does not arise from the
wide-scope LF `◇A ∨ ◇B`, but from the narrow-scope LF `◇(A ∨ B)`. For
disjunction the two LFs are truth-conditionally equivalent
(`scope_equivalence`), so the scope distinction is invisible to truth
conditions; it matters only compositionally, because only `◇(A ∨ B)` feeds the
exhaustification that derives `◇A ∧ ◇B`. The wide-scope LF instead yields an
*ignorance* reading and does not, on its own, entail free choice
(`wideScope_underdetermines_fc`). (For conjunction the two LFs are *not*
equivalent; see §8.)

The narrow-scope LF is derived by modal concord [zeijlstra-2007]: modal
auxiliaries carry uninterpretable features `[u∃/∀-MOD]`; a single silent
interpretable operator c-commanding the coordination checks both, so only it is
interpreted, yielding `Δ(A ∘ B)` rather than `ΔA ∘ ΔB`.

`MOD A COORD MOD B` is scope-ambiguous across the board:

| surface form     | wide-scope LF | narrow-scope LF |
|------------------|---------------|-----------------|
| may A or may B   | `◇A ∨ ◇B`     | `◇(A ∨ B)`      |
| must A or must B | `□A ∨ □B`     | `□(A ∨ B)`      |
| may A and may B  | `◇A ∧ ◇B`     | `◇(A ∧ B)`      |

The modal operators `diamond`/`box` are `Core.Logic.Modal.poss`/`nec` (the flat
S5 modals shared with the whole free-choice stack), so the scope theorems consume
the substrate's distribution lemmas directly.

## Main declarations

* `scope_equivalence` — the two disjunction LFs are truth-conditionally equal.
* `disjunctive_obligation_narrow_weaker` / `_not_wide` — must-or-must: under
  necessity the narrow LF `□(A ∪ B)` is strictly *weaker* than the wide `□A ∨ □B`.
* `ConcordDerivation` — two `[u-MOD]` auxiliaries checked by one silent operator.
* `narrowScope_yields_fc` / `wideScope_underdetermines_fc` — free choice from the
  narrow LF; non-entailment of free choice from the wide LF.
* `reductionist_thesis` — the two packaged together.
* `negation_concord_pattern` — cross-negation concord succeeds iff forces are duals.
-/

namespace CiardelliGuerrini2026

open Semantics.Modality
open Exhaustification.FreeChoice (diamond box diamond_distributes_iff FCAltSet free_choice_forward)
open English.Auxiliaries

/-! ### Truth-conditional equivalence

For disjunction the two LFs collapse: `◇(A ∨ B) ↔ ◇A ∨ ◇B` in standard modal
logic. This is *the point* of [ciardelli-guerrini-2026] — the scope distinction
is invisible to truth conditions, and matters only for compositional derivation
and pragmatic enrichment. (For conjunction the LFs are *not* equivalent; see §8.)
-/

/-- The two disjunction LFs are truth-conditionally equivalent: `◇(A ∨ B) ↔ ◇A ∨ ◇B`.
A thin alias for `Exhaustification.FreeChoice.diamond_distributes_iff`, recording its
role as the central observation of [ciardelli-guerrini-2026]. -/
theorem scope_equivalence {World : Type*} (A B : Set World) :
    diamond (A ∪ B) ↔ diamond A ∨ diamond B :=
  diamond_distributes_iff A B

/-! ### Must-or-must: disjunctive obligation (§2)

Under *necessity*, the scope distinction is **not** truth-conditionally vacuous.
`diamond`/`box` here are `Core.Logic.Modal.poss`/`nec`, so these theorems consume
the substrate's flat distribution directly. For disjunction the narrow LF
`□(A ∪ B)` is strictly *weaker* than the wide LF `□A ∨ □B` — exactly C&G's
must-or-must contrast: "(either) you must A or you must B" on its salient reading
is a single disjunctive obligation `□(A ∨ B)`, not two obligations. -/

/-- Wide ⟹ narrow: `□A ∨ □B → □(A ∪ B)`. The narrow disjunctive-obligation LF is
the weaker reading (monotonicity of `Core.Logic.Modal.nec`). -/
theorem disjunctive_obligation_narrow_weaker {World : Type*} (A B : Set World) :
    box A ∨ box B → box (A ∪ B) := by
  rintro (h | h)
  · exact Core.Logic.Modal.nec_mono (fun _ ha => Or.inl ha) h
  · exact Core.Logic.Modal.nec_mono (fun _ hb => Or.inr hb) h

/-- …but **not** conversely: `□(A ∪ B)` does not entail `□A ∨ □B`. A disjunctive
obligation leaves which disjunct is met open, so neither `□A` nor `□B` follows.
This is why must-or-must has a genuine narrow reading the wide LF lacks. -/
theorem disjunctive_obligation_not_wide :
    ∃ (A B : Set Bool), box (A ∪ B) ∧ ¬ (box A ∨ box B) := by
  refine ⟨{true}, {false}, ?_, ?_⟩
  · intro w; cases w
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (h | h)
    · exact absurd (show false = true from h false) (by decide)
    · exact absurd (show true = false from h true) (by decide)

/-! ### Scope-ambiguity data (§2)

`MOD A COORD MOD B` sentences are scope-ambiguous. The illustrative sentences
record the modal force, which §10 cross-checks against the Fragment; narrow-scope
*availability* is witnessed structurally by the concord derivations of §3
(`mayMayConcord`, `mustMustConcord`), whose mere existence as well-typed terms is
the proof that the two auxiliaries can undergo concord. -/

/-- An illustrative "MOD A COORD MOD B" sentence. -/
structure ScopeAmbiguityDatum where
  sentence : String
  /-- The coordinator: "or" or "and". -/
  coord : String
  modalForce : ModalForce
  /-- The reading dominant in the discussed context. -/
  dominantReading : String
  deriving Repr

/-- (2) "You may do A or you may do B" — free choice from the narrow-scope LF. -/
def mayOrMay : ScopeAmbiguityDatum :=
  { sentence := "You may do A or you may do B"
  , coord := "or", modalForce := .possibility
  , dominantReading := "narrow-scope (free choice)" }

/-- (5) "You must write an essay or you must give a presentation." -/
def mustOrMust : ScopeAmbiguityDatum :=
  { sentence := "You must write an essay or you must give a presentation"
  , coord := "or", modalForce := .necessity
  , dominantReading := "narrow-scope (disjunctive obligation)" }

/-- (7) "You may go to Bob's party and you may go to Charlie's party." -/
def mayAndMay : ScopeAmbiguityDatum :=
  { sentence := "You may go to Bob's party and you may go to Charlie's party"
  , coord := "and", modalForce := .possibility
  , dominantReading := "narrow-scope (conjunctive permission)" }

def scopeData : List ScopeAmbiguityDatum := [mayOrMay, mustOrMust, mayAndMay]

/-! ### Modal concord derivation (§3)

[zeijlstra-2007]'s feature system explains how the narrow-scope LF `◇(A ∨ B)`
arises compositionally for "may A or may B":

1. each "may" carries `[u∃-MOD]` (uninterpretable existential feature);
2. a silent `◇` operator `[i∃-MOD]` is projected above the coordination;
3. the silent operator checks both `[u∃-MOD]` features in the conjuncts;
4. only the silent operator is semantically interpreted, giving `◇(A ∨ B)`.
-/

/-- The modal feature carried by English "may" — derived from the Fragment entry's
force and interpretability. -/
def mayFeature : ModalFeature := may.toModalFeature.get!

/-- The modal feature carried by English "must" — derived from the Fragment. -/
def mustFeature : ModalFeature := must.toModalFeature.get!

/-- "May" carries `[u∃-MOD]`: possibility force, uninterpretable. -/
theorem may_feature_eq :
    may.toModalFeature = some ⟨.possibility, .uninterpretable⟩ := rfl

/-- "Must" carries `[u∀-MOD]`: necessity force, uninterpretable. -/
theorem must_feature_eq :
    must.toModalFeature = some ⟨.necessity, .uninterpretable⟩ := rfl

/-- The silent operator that checks a given u-feature: same force, but
interpretable. This is the operator [ciardelli-guerrini-2026] posit above the
coordination. -/
def silentChecker (f : ModalFeature) : ModalFeature := ⟨f.force, .interpretable⟩

/-- **Core derivation**: the matching silent operator checks any u-feature. This is
the general form of the concord mechanism — not just "may" or "must", but *any*
auxiliary carrying a u-feature. -/
theorem silent_checker_works (f : ModalFeature) (h : f.interp = .uninterpretable) :
    (silentChecker f).checks f = true := by
  simp only [silentChecker, ModalFeature.checks, h]
  cases f.force <;> decide

/-- A silent `[i-MOD]` with force `g₁` checks any `[u-MOD]` of matching concord class. -/
private theorem silent_checks_matching (g₁ g₂ : ModalFeature)
    (hI : g₂.interp = .uninterpretable)
    (hF : ConcordType.fromModalForce g₁.force = ConcordType.fromModalForce g₂.force) :
    (silentChecker g₁).checks g₂ = true := by
  have hforce : (silentChecker g₁).checks g₂ = (silentChecker g₂).checks g₂ := by
    simp only [silentChecker, ModalFeature.checks, hF]
  rw [hforce]
  exact silent_checker_works g₂ hI

/-! #### ConcordDerivation: packaging the full derivation chain -/

/-- A concord derivation witnesses that two modal features can be checked by a
single silent operator. This is the formal content of [ciardelli-guerrini-2026]'s
compositional mechanism.

A `ConcordDerivation` exists iff both features are uninterpretable (u-MOD) and
belong to the same concord class (both ∃-type or both ∀-type). The silent
operator, the checking proofs, and the resulting narrow-scope interpretation are
all derived from these two conditions. -/
structure ConcordDerivation where
  /-- The feature of the first modal auxiliary. -/
  f₁ : ModalFeature
  /-- The feature of the second modal auxiliary. -/
  f₂ : ModalFeature
  /-- Both are uninterpretable. -/
  uInterp₁ : f₁.interp = .uninterpretable
  uInterp₂ : f₂.interp = .uninterpretable
  /-- Same concord class. -/
  sameClass : ConcordType.fromModalForce f₁.force = ConcordType.fromModalForce f₂.force

namespace ConcordDerivation

/-- The silent interpretable operator — derived, not stipulated. -/
def checker (cd : ConcordDerivation) : ModalFeature :=
  silentChecker cd.f₁

/-- The checker is interpretable (semantically active). -/
theorem checker_interpretable (cd : ConcordDerivation) :
    cd.checker.interp = .interpretable := rfl

/-- The checker checks the first feature. -/
theorem checks_first (cd : ConcordDerivation) :
    cd.checker.checks cd.f₁ = true :=
  silent_checker_works cd.f₁ cd.uInterp₁

/-- The checker checks the second feature. -/
theorem checks_second (cd : ConcordDerivation) :
    cd.checker.checks cd.f₂ = true :=
  silent_checks_matching cd.f₁ cd.f₂ cd.uInterp₂ cd.sameClass

end ConcordDerivation

/-- Construct a `ConcordDerivation` from two `AuxEntry`s. The derivation is built
entirely from Fragment data — no stipulation. -/
def ConcordDerivation.fromAux (a₁ a₂ : AuxEntry)
    {f₁ f₂ : ModalFeature}
    (_h₁ : a₁.toModalFeature = some f₁) (_h₂ : a₂.toModalFeature = some f₂)
    (hI₁ : f₁.interp = .uninterpretable) (hI₂ : f₂.interp = .uninterpretable)
    (hF : ConcordType.fromModalForce f₁.force = ConcordType.fromModalForce f₂.force) :
    ConcordDerivation :=
  ⟨f₁, f₂, hI₁, hI₂, hF⟩

/-! #### Universal modal properties -/

/-- The modal auxiliaries that participate in concord: Fragment entries with
uninterpretable features. -/
def modalAuxiliaries : List AuxEntry :=
  allAuxiliaries.filter (λ a => a.interpretability == some .uninterpretable)

/-- Exactly 13 English modal auxiliaries carry u-features. -/
theorem modal_aux_count : modalAuxiliaries.length = 13 := by decide

/-- Modal auxiliaries with modal meaning (those that can form `ConcordDerivation`s).
Excludes `dare`, which has u-features but no modal-meaning specification. -/
def concordCapableModals : List AuxEntry :=
  modalAuxiliaries.filter (λ a => a.toModalFeature.isSome)

/-- 12 of 13 modal auxiliaries have derivable modal features. -/
theorem concord_capable_count : concordCapableModals.length = 12 := by decide

/-- Every concord-capable modal's feature is uninterpretable. -/
theorem concord_capable_all_uninterpretable :
    concordCapableModals.all (λ a =>
      decide (a.interpretability == some .uninterpretable)) = true := by
  decide

/-- Non-modal auxiliaries have no modal feature — they cannot participate in
concord at all. -/
theorem do_no_feature : do_.toModalFeature = none := rfl
theorem be_no_feature : am.toModalFeature = none := rfl
theorem have_no_feature : have_.toModalFeature = none := rfl

/-! #### Instantiations -/

/-- "May A or may B" concord derivation — fully derived from the Fragment. -/
def mayMayConcord : ConcordDerivation :=
  .fromAux may may may_feature_eq may_feature_eq rfl rfl rfl

/-- "Must A or must B" concord derivation — fully derived from the Fragment. -/
def mustMustConcord : ConcordDerivation :=
  .fromAux must must must_feature_eq must_feature_eq rfl rfl rfl

/-- Cross-force checking fails: a silent `□` cannot check "may" `[u∃]`. -/
theorem cross_force_blocked :
    (silentChecker mustFeature).checks mayFeature = false := by decide

/-! ### The FC pipeline: concord → narrow scope → free choice (§3)

The pipeline has three stages:

1. **feature matching** → `ConcordDerivation` (above);
2. **narrow scope** → a single modal operator over the coordination;
3. **exhaustification** → the free-choice inference.

The key point: the narrow/wide scope distinction is truth-conditionally vacuous
*for disjunction* (`scope_equivalence`) but pragmatically active. Only the
narrow-scope LF, exhaustified, yields free choice; the wide-scope LF
underdetermines it (and yields an ignorance reading instead). -/

/-- The **free-choice pipeline**: the narrow-scope `◇(A ∨ B)`, doubly exhaustified,
yields free choice `◇A ∧ ◇B`. This is the reductionist thesis in action — FC
arises from the narrow-scope LF (derived via concord) fed to the standard
exhaustification mechanism (`free_choice_forward`). -/
theorem narrowScope_yields_fc {World : Type*} (A B : Set World)
    (hExh : (FCAltSet.mk A B).exh2) : diamond A ∧ diamond B :=
  free_choice_forward ⟨A, B⟩ hExh

/-- The wide-scope LF `◇A ∨ ◇B` does **not** entail free choice `◇A ∧ ◇B`: a
disjunction of possibilities holds even when only one disjunct is possible. This
is why [ciardelli-guerrini-2026] locate the free-choice reading exclusively in the
narrow-scope LF — the wide-scope LF yields the *ignorance* reading (the speaker is
unsure which disjunct holds), not free choice. -/
theorem wideScope_underdetermines_fc :
    ∃ (A B : Set Unit), (diamond A ∨ diamond B) ∧ ¬ (diamond A ∧ diamond B) := by
  refine ⟨Set.univ, ∅, Or.inl ⟨(), trivial⟩, ?_⟩
  rintro ⟨-, w, hw⟩
  exact Set.notMem_empty w hw

/-- **The reductionist thesis** ([ciardelli-guerrini-2026], formalized).

Despite truth-conditional equivalence (`scope_equivalence`), the FC reading arises
only from the narrow-scope LF: (1) the two disjunction LFs are equivalent, and
(2) the narrow-scope LF, exhaustified, yields free choice. The wide-scope LF does
not (`wideScope_underdetermines_fc`), so there is no separate problem of
"wide-scope free choice". -/
theorem reductionist_thesis {World : Type*} (A B : Set World) :
    (diamond (A ∪ B) ↔ diamond A ∨ diamond B) ∧
    ((FCAltSet.mk A B).exh2 → diamond A ∧ diamond B) :=
  ⟨scope_equivalence A B, narrowScope_yields_fc A B⟩

/-! ### Auxiliary vs non-auxiliary modals (§4.1)

[meyer-sauerland-2017] observed that (19a-b) lack FC readings:

  (19a) It's ok for John to sing or it's ok for John to dance.  (*FC)
  (19b) John is allowed to sing or he is allowed to dance.      (*FC)

[ciardelli-guerrini-2026] explain this: "it's ok" and "be allowed" carry
**interpretable** features, so they are already interpreted and cannot be checked
by a higher silent operator — no narrow-scope LF, no FC. Modal auxiliaries ("may",
"must", "can") carry **uninterpretable** features and *can* be checked → FC
available. The auxiliary status of "may", "must", "can", "need" is derived from
`English.FunctionWords` — they are all `.modal` entries.

Caveat: in §4.3 the authors flag (31) "it is possible that A or it is possible
that B", a *non-auxiliary* modal that nevertheless seems to allow FC, as an
outstanding problem. The prediction below is therefore about the concord
*mechanism* (interpreted features cannot be checked), not an exceptionless surface
generalization. -/

/-- Fragment-derived: the English modals used by [ciardelli-guerrini-2026] are
modal auxiliaries. -/
theorem may_is_modal : may.auxType = .modal := rfl
theorem must_is_modal : must.auxType = .modal := rfl
theorem can_is_modal : can.auxType = .modal := rfl
theorem need_is_modal : need.auxType = .modal := rfl

/-- All these modals carry uninterpretable features in the Fragment. -/
theorem may_uninterpretable : may.interpretability = some .uninterpretable := rfl
theorem must_uninterpretable : must.interpretability = some .uninterpretable := rfl
theorem can_uninterpretable : can.interpretability = some .uninterpretable := rfl
theorem need_uninterpretable : need.interpretability = some .uninterpretable := rfl

/-- **The mechanism behind the auxiliary/non-auxiliary contrast**: an *interpreted*
feature can never be checked. Non-auxiliary modal constructions ("it's ok that",
"be allowed/required to") carry interpretable features, so no silent operator can
check them — hence no narrow-scope LF and no FC in coordination. This is derived
from `ModalFeature.checks` (which requires the checked feature to be
uninterpretable), not stipulated. -/
theorem interpreted_unchecked (checker f : ModalFeature)
    (h : f.interp = .interpretable) : checker.checks f = false := by
  have hb : (f.interp == .uninterpretable) = false := by rw [h]; decide
  simp only [ModalFeature.checks, hb, Bool.and_false, Bool.false_and]

/-- Corollary: an interpreted feature cannot be the checked conjunct of a
`ConcordDerivation` — that would contradict `uInterp₂`. -/
theorem interpreted_not_concord_checked (cd : ConcordDerivation) :
    cd.f₂.interp ≠ .interpretable := by
  rw [cd.uInterp₂]; decide

/-! ### Against ATB movement (§1, ex. 3)

[simons-2005] proposed that the narrow-scope LF `◇(A ∨ B)` arises from
across-the-board (ATB) movement of the modal at LF. [ciardelli-guerrini-2026] note
evidence *against* this: ATB movement is independently blocked for nominal
quantifiers.

  (3a) Everyone sang or everyone danced.
  (3b) Everyone sang or danced.

(3a) cannot be interpreted as (3b). If ATB movement of "everyone" were possible at
LF, (3a) should receive the (3b) reading — but it does not. This undermines ATB as
the mechanism for deriving narrow-scope modal LFs. The modal concord account avoids
the problem: the narrow-scope LF is derived by feature checking (specific to
modals), not movement (which would overgeneralize to quantifiers).

Formalizing the contrast faithfully needs a movement/quantifier substrate this
study does not import, so the argument is recorded here as prose. -/

/-! ### Concord across negation (§4.2)

Modal concord across negation requires **opposite** forces. The checking uses
`ModalForce.dual` — negation over a modal operator yields its dual:

  (24) ALLOW[i∃](¬NEED[u∀]) ✓  — dual(∀) = ∃, matches the checker
  (26) *DEMAND[i∀](¬NEED[u∀]) ✗  — dual(∀) = ∃ ≠ ∀
  (25) DEMAND[i∀](¬MAY[u∃]) ✓  — dual(∃) = ∀, matches the checker
  (27) *ALLOW[i∃](¬MAY[u∃]) ✗  — dual(∃) = ∀ ≠ ∃

The pattern: checking across negation succeeds iff the checker's force equals the
dual of the checked item's force. This follows from
`ModalFeature.checksAcrossNegation`, which uses `ModalForce.dual`. The
generalization is from [grosz-2010] and [anand-brasoveanu-2010]. -/

/-- (24) ALLOW[i∃] checks ¬NEED[u∀]: well-formed (dual(∀) = ∃). -/
theorem allow_neg_need_ok :
    (ModalFeature.checksAcrossNegation
      ⟨.possibility, .interpretable⟩
      ⟨.necessity, .uninterpretable⟩)
    = true := by decide

/-- (26) *DEMAND[i∀] checks ¬NEED[u∀]: ill-formed (dual(∀) = ∃ ≠ ∀). -/
theorem demand_neg_need_bad :
    (ModalFeature.checksAcrossNegation
      ⟨.necessity, .interpretable⟩
      ⟨.necessity, .uninterpretable⟩)
    = false := by decide

/-- (25) DEMAND[i∀] checks ¬MAY[u∃]: well-formed (dual(∃) = ∀). -/
theorem demand_neg_may_ok :
    (ModalFeature.checksAcrossNegation
      ⟨.necessity, .interpretable⟩
      ⟨.possibility, .uninterpretable⟩)
    = true := by decide

/-- (27) *ALLOW[i∃] checks ¬MAY[u∃]: ill-formed (dual(∃) = ∀ ≠ ∃). -/
theorem allow_neg_may_bad :
    (ModalFeature.checksAcrossNegation
      ⟨.possibility, .interpretable⟩
      ⟨.possibility, .uninterpretable⟩)
    = false := by decide

/-- General pattern: cross-negation concord succeeds iff the forces are duals.
This is the content of the negation-concord generalization from [grosz-2010] and
[anand-brasoveanu-2010], formalized as a consequence of `checksAcrossNegation`
using `ModalForce.dual`. -/
theorem negation_concord_pattern (checkerForce checkedForce : ModalForce)
    (hNec : checkerForce = .necessity ∨ checkerForce = .possibility)
    (hChk : checkedForce = .necessity ∨ checkedForce = .possibility) :
    ModalFeature.checksAcrossNegation
      ⟨checkerForce, .interpretable⟩
      ⟨checkedForce, .uninterpretable⟩ = true
    ↔ checkerForce = checkedForce.dual := by
  rcases hNec with rfl | rfl <;> rcases hChk with rfl | rfl <;> decide

/-! ### "I need not cook and I need not clean" (§4.2, ex. 28-29)

"I need not cook and I need not clean" can convey `◇(¬Cook ∧ ¬Clean)` —
permission to do neither — but not `□(¬Cook ∧ ¬Clean)` — obligation to do neither.
This follows from the concord-across-negation generalization; the "need" u-feature
force (necessity) comes from the Fragment. -/

/-- "Need" carries `[u∀-MOD]` in the Fragment. -/
theorem need_feature_eq :
    need.toModalFeature = some ⟨.necessity, .uninterpretable⟩ := rfl

/-- The existential reading is available: `◇[i∃]` checks `¬NEED[u∀]`. -/
theorem need_not_existential_ok :
    ModalFeature.checksAcrossNegation
      ⟨.possibility, .interpretable⟩
      need.toModalFeature.get!
    = true := by decide

/-- The universal reading is blocked: `□[i∀]` cannot check `¬NEED[u∀]`. -/
theorem need_not_universal_blocked :
    ModalFeature.checksAcrossNegation
      ⟨.necessity, .interpretable⟩
      need.toModalFeature.get!
    = false := by decide

/-! ### Conjunctive permission, may-and-may (§2, ex. 7-8)

"You may go to Bob's party and you may go to Charlie's party" has a reading where
Alice is allowed to go to both parties: `◇(Bob ∧ Charlie)`. Unlike disjunction,
`◇(A ∧ B)` is strictly *stronger* than `◇A ∧ ◇B`, so for conjunction the scope
distinction has truth-conditional consequences. -/

/-- For conjunction, narrow scope is strictly stronger than wide scope:
`◇(A ∧ B) → ◇A ∧ ◇B` (but not conversely). -/
theorem conjunctive_narrow_stronger {World : Type*}
    (p q : Set World)
    (h : diamond (p ∩ q)) : diamond p ∧ diamond q := by
  obtain ⟨w, hp, hq⟩ := h
  exact ⟨⟨w, hp⟩, ⟨w, hq⟩⟩

/-! ### Same-feature concord in the fragment

[ciardelli-guerrini-2026]'s mechanism for the narrow-scope LF is that two
auxiliaries carrying the same modal feature are checked by a single silent
operator (the coordination structure for "you must A or you must B" → □(A ∨ B)),
leaving one semantic operator. The fragment exhibits the precondition: `must` and
`have to` both carry `[u∀-MOD]`, so a single `[i∀]` operator checks both. -/

/-- `must` and `have to` carry the same modal feature (both `[u∀-MOD]`) — a
same-force concord configuration. -/
theorem must_haveTo_same_feature :
    must.toModalFeature = haveTo.toModalFeature := rfl

/-- `have to` carries `[u∀-MOD]`: necessity force, uninterpretable. -/
theorem haveTo_feature_eq :
    haveTo.toModalFeature = some ⟨.necessity, .uninterpretable⟩ := rfl

/-- The `must`/`have to` concord as a `ConcordDerivation`, derived from the
Fragment: two `[u∀]` auxiliaries checked by one operator. -/
def mustHaveToConcord : ConcordDerivation :=
  .fromAux must haveTo must_feature_eq haveTo_feature_eq rfl rfl rfl

/-- Cross-force concord fails: "must" `[u∀]` cannot be checked by a silent `[i∃-MOD]`
operator. This predicts no concord between necessity and possibility modals. -/
theorem must_may_no_concord :
    (ModalFeature.checks
      ⟨may.toModalFeature.get!.force, .interpretable⟩
      must.toModalFeature.get!)
    = false := by decide

/-! ### Scope-data verification against the Fragment

The `modalForce` field in each `ScopeAmbiguityDatum` is independently verifiable
against the Fragment's modal-meaning entries. -/

/-- The force in `mayOrMay` matches the Fragment entry for "may". -/
theorem mayOrMay_force_verified :
    mayOrMay.modalForce = may.toModalFeature.get!.force := rfl

/-- The force in `mustOrMust` matches the Fragment entry for "must". -/
theorem mustOrMust_force_verified :
    mustOrMust.modalForce = must.toModalFeature.get!.force := rfl

/-- The force in `mayAndMay` matches the Fragment entry for "may". -/
theorem mayAndMay_force_verified :
    mayAndMay.modalForce = may.toModalFeature.get!.force := rfl

end CiardelliGuerrini2026
