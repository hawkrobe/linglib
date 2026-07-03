import Linglib.Discourse.Commitment.Space
import Linglib.Studies.Krifka2015

/-!
# Imperatives as Preferential Commitment
[condoravdi-lauer-2012] [lauer-2013]

Worked examples exercising the substrate's `force = .preferential` axis,
which had no consumer prior to this file. Anchored on
[condoravdi-lauer-2012] ("Imperatives: meaning and illocutionary
force", *Empirical Issues in Syntax and Semantics 9*, pp. 37–58).

## Paper's central distinction (§§3.2–3.3)

[condoravdi-lauer-2012] argue that declarative and imperative
utterances create commitments of *different attitudinal types*:

- **Declarative utterance** (e.g., "It's raining"): adds
  `PB_w(Sp, ⟦φ⟧)` — public commitment to ACT AS THOUGH BELIEVING φ.
- **Imperative utterance** (e.g., "Sit down!"): adds
  `PEP_w(Sp, ⟦φ⟧)` — public commitment to ACT AS THOUGH PREFERRING φ
  to be a maximal element of the speaker's effective preference structure.

Both kinds are *commitments to act* (paper §3.2). They differ in the
attitude the speaker is committed to act under: doxastic vs preferential.
This is the substrate's `CommitmentForce` axis.

## Coverage

- §1 — World fixture and propositions
- §2 — Declarative-as-doxastic baseline (Krifka 2015 default)
- §3 — Imperative-as-preferential (the paper's central claim)
- §4 — Doxastic vs preferential CommonGround divergence (the two projections
       see different things)
- §5 — vs Krifka 2015: same substrate, different force; Krifka's
       framework was purely doxastic

## Out of scope

- The paper's "four challenges" (§2: contextual inconsistency, speaker
  endorsement, automatic sincerity, interlocutors' role) — these are
  arguments that any imperative theory must meet; Condoravdi-Lauer's
  apparatus passes them via PEP/PB closure properties (Lauer 2013
  Ch. 5). The substrate doesn't yet model time-indexed PB/PEP closure
  (per `CommitmentSpace.lean` substrate scope note); these challenges
  are deferred.
- The paper's typology of imperative uses (§1: directives, wishes,
  permissions, disinterested advice, four groups) — formalized via
  varying the contextual conditions on the SAME PEP commitment;
  worked examples for each group would multiply the file. Single-case
  worked example here.
- Comparison with [kaufmann-2012] and [portner-2007] (paper
  §6) — separate study files would cover these; the [roberts-2023]
  study at sibling `Studies/Roberts2023.lean` already engages the
  Kaufmann-Portner debate.

-/

namespace CondoravdiLauer2012

open Discourse.Krifka
open Discourse (DiscourseRole)
open Discourse.Commitment (IndexedCommitment IndexedWeightedCommitment CommitmentForce)

-- ════════════════════════════════════════════════════
-- § 1. Setup
-- ════════════════════════════════════════════════════

/-- A 2-world model: addressee sits / doesn't sit. -/
inductive AddrPosture where | sitting | standing
  deriving DecidableEq, Repr

/-- Proposition: the addressee is sitting. -/
def isSitting : AddrPosture → Prop
  | .sitting => True
  | .standing => False

-- ════════════════════════════════════════════════════
-- § 2. Declarative baseline (Krifka 2015, doxastic)
-- ════════════════════════════════════════════════════

/-- Speaker utters the declarative "The addressee is sitting".
    Creates a doxastic commitment (Krifka 2015 default; [condoravdi-lauer-2012]
    paper §3.3 Convention applied to assertions). -/
def declarativeState : KrifkaState AddrPosture :=
  KrifkaState.empty.assert isSitting .speaker

/-- The declarative state has speaker doxastically committed to `isSitting`. -/
theorem declarative_root_eq :
    declarativeState.space.root =
      [IndexedCommitment.commit .speaker isSitting] := rfl

/-- Therefore the doxastic context set narrows to sitting-worlds. -/
theorem declarative_doxastic_narrows (w : AddrPosture) :
    declarativeState.space.toDoxasticContextSet w ↔ isSitting w := by
  constructor
  · intro h
    exact h _ (List.mem_cons_self) rfl
  · intro hSit ic hic hf
    rcases List.mem_singleton.mp hic with rfl
    exact hSit

/-- The preferential context set is unaffected by the declarative
    (no preferential commitments in root). -/
theorem declarative_preferential_unchanged (w : AddrPosture) :
    declarativeState.space.toPreferentialContextSet w := by
  intro ic hic hf
  rcases List.mem_singleton.mp hic with rfl
  -- ic is .commit speaker .doxastic isSitting; hf : .doxastic = .preferential is False
  exact absurd hf (by decide)

-- ════════════════════════════════════════════════════
-- § 3. Imperative as preferential commitment (paper §3.3)
-- ════════════════════════════════════════════════════

/-- Speaker utters the imperative "Sit down!". The substrate's `assert`
    operator with `force := .preferential` models the paper's
    `PEP_w(Sp, ⟦sit_down⟧)` commitment.

    Per [condoravdi-lauer-2012] §3.3: the convention for imperatives
    parallels the convention for declaratives, but commits the speaker
    to a PREFERENCE rather than a BELIEF. -/
def imperativeState : KrifkaState AddrPosture :=
  KrifkaState.empty.assert isSitting .speaker .preferential

/-- The imperative state has speaker preferentially committed to
    `isSitting`. Same `IndexedCommitment.commit` constructor as the
    declarative — only the `force` field differs. -/
theorem imperative_root_eq :
    imperativeState.space.root =
      [IndexedWeightedCommitment.commit .speaker .preferential isSitting] := rfl

/-- The doxastic context set is unaffected by the imperative — the
    speaker has not committed to BELIEVE the addressee is sitting,
    only to prefer it. -/
theorem imperative_doxastic_unchanged (w : AddrPosture) :
    imperativeState.space.toDoxasticContextSet w := by
  intro ic hic hf
  rcases List.mem_singleton.mp hic with rfl
  exact absurd hf (by decide)

/-- The preferential context set narrows to sitting-worlds — the
    speaker IS committed to act as though preferring `isSitting`. -/
theorem imperative_preferential_narrows (w : AddrPosture) :
    imperativeState.space.toPreferentialContextSet w ↔ isSitting w := by
  constructor
  · intro h
    exact h _ (List.mem_cons_self) rfl
  · intro hSit ic hic hf
    rcases List.mem_singleton.mp hic with rfl
    exact hSit

-- ════════════════════════════════════════════════════
-- § 4. Doxastic vs Preferential divergence
-- ════════════════════════════════════════════════════

/-! ## The two projections see different things

Paper §3.2: `PB` and `PEP` are independent attitudinal commitments. A
declarative engages only PB; an imperative engages only PEP. The
substrate's `toDoxasticContextSet` / `toPreferentialContextSet`
projections make this independence Lean-checkable. -/

/-- Headline: declarative narrows doxastic but not preferential;
    imperative narrows preferential but not doxastic. -/
theorem dox_pref_dual (w : AddrPosture) :
    -- Declarative: doxastic narrows iff isSitting; preferential trivial
    (declarativeState.space.toDoxasticContextSet w ↔ isSitting w) ∧
    declarativeState.space.toPreferentialContextSet w ∧
    -- Imperative: preferential narrows iff isSitting; doxastic trivial
    imperativeState.space.toDoxasticContextSet w ∧
    (imperativeState.space.toPreferentialContextSet w ↔ isSitting w) :=
  ⟨declarative_doxastic_narrows w,
   declarative_preferential_unchanged w,
   imperative_doxastic_unchanged w,
   imperative_preferential_narrows w⟩

/-- The conflated `toContextSet` is the conjunction of both projections
    (substrate-level theorem `toContextSet_eq_doxastic_and_preferential`).
    Specialised to `imperativeState`: the conflated CommonGround narrows to
    sitting-worlds even though only the preferential-CommonGround component is
    really committed. The conflated view loses information. -/
theorem imperative_conflated_loses_distinction (w : AddrPosture) :
    imperativeState.space.toContextSet w ↔ isSitting w := by
  rw [Discourse.Krifka.CommitmentSpace.toContextSet_eq_doxastic_and_preferential]
  constructor
  · rintro ⟨_, hp⟩
    exact (imperative_preferential_narrows w).mp hp
  · intro hSit
    exact ⟨imperative_doxastic_unchanged w,
           (imperative_preferential_narrows w).mpr hSit⟩

-- ════════════════════════════════════════════════════
-- § 5. vs Krifka 2015 — same substrate, different force
-- ════════════════════════════════════════════════════

/-! ## Krifka 2015 was purely doxastic; CL2012 adds preferential

Per the chronological-dependency rule, this 2012 paper PRECEDES
Krifka 2015 — but Krifka 2015's framework, as formalised in
`Studies/Krifka2015.lean`, only exercises
`force = .doxastic` (the substrate's default). Condoravdi-Lauer 2012
provides the missing imperative case via `force = .preferential`,
exercising the same substrate machinery on the same `IndexedCommitment`
constructor.

The interesting cross-framework observation: both Krifka 2015's
declarative-assertion and Condoravdi-Lauer 2012's imperative-assertion
produce a single-element root. They differ ONLY in the `force` field. -/

/-- Both Krifka 2015's declarative and CL2012's imperative produce a
    single-element root with the SAME `IndexedCommitment.commit`
    constructor and the SAME content (`isSitting`). They differ only
    in the `force` field. -/
theorem declarative_imperative_share_content_differ_in_force :
    declarativeState.space.root =
      [IndexedWeightedCommitment.commit .speaker .doxastic isSitting] ∧
    imperativeState.space.root =
      [IndexedWeightedCommitment.commit .speaker .preferential isSitting] ∧
    -- Different force on the head commitment
    (declarativeState.space.root.head?.map (·.force)) ≠
    (imperativeState.space.root.head?.map (·.force)) := by
  refine ⟨rfl, rfl, ?_⟩
  decide

end CondoravdiLauer2012
