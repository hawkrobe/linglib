import Linglib.Core.Case.Basic
import Linglib.Theories.Syntax.Case.Dependent
import Linglib.Theories.Syntax.Minimalism.Core.CaseFilter

/-!
# Hybrid Licensing
@cite{kalin-2018} @cite{coon-keine-2021} @cite{marantz-1991} @cite{baker-2015}

A theory of nominal licensing that decouples *which* nominals need
licensing from *where* the licensers live. Following @cite{kalin-2018}'s
analysis of differential object marking (DOM) in the Neo-Aramaic
language Senaya, every clause carries

1. an **obligatory primary licenser** (always merged), plus
2. zero or more **secondary licensers** that merge only when their
   inactivity would cause some nominal to remain unlicensed —
   essentially a global last-resort economy condition on functional
   structure.

Independently, languages parameterize *which* nominals need licensing in
the first place. Some make every nominal need licensing (no DOM);
others restrict the licensing requirement to nominals carrying certain
structural/featural components (e.g., [+specific], [+definite],
[+animate]) — yielding DOM as the visible signature of secondary
licensers being activated.

## Feature-Theoretic Implementation

@cite{kalin-2018} cashes "needs licensing" as carrying an
*uninterpretable, unvalued* [Case] feature in the
@cite{pesetsky-torrego-2007} framework: licensing is feature
*valuation* via Agree with an active licenser. Nominals without the
unvalued feature are not active for licensing — they are interpretable
in situ. The `needsLicensing` flag on `LicensedNP` is the Boolean
abstraction of this feature; the `caseFeature` accessor returns the
NP's licensing-relevant case state (valued by lexical case, valued by
a licenser, or unvalued).

## Why "Hybrid"

The architecture is hybrid in two senses:

- **Licensers**: primary (obligatory) + secondary (last-resort) coexist
  in the same clause. This contrasts with Agree-based theories
  (@cite{marantz-1991} as a foil; classical Minimalism) in which case is
  assigned by a fixed set of functional heads, and with dependent case
  (`Dependent.lean`, @cite{baker-2015}) in which configuration alone
  determines case without a head-based licensing requirement.
- **Marked vs. unmarked objects**: under hybrid licensing, marked
  objects are not structurally distinguished from unmarked ones in the
  usual sense (they don't necessarily occupy a high position or escape
  pseudo-incorporation); the difference is that they triggered
  activation of a secondary licenser.

## Two Parameters

A language's licensing system is determined by:

- `needsLicensing : NPFeatures → Bool` — which nominals require licensing
- the inventory of `Licenser`s, of which exactly one is `primary` and
  the rest are `secondary`

DOM patterns fall out from the interaction. A nominal is *unmarked* if
the primary licenser suffices; *marked* if convergence required
activating a secondary licenser. Non-DOM languages either (a) license
every nominal via the primary head (no secondary licenser ever
activates) or (b) make every nominal need licensing so that secondary
licensers always activate uniformly.

## Relation to Other Case Theories

- **Dependent case** (`Dependent.lean`, @cite{baker-2015}): configural,
  no head-based licensing requirement. Hybrid licensing is largely
  orthogonal — the two can in principle coexist in a single language,
  with dependent case assigning the morphological exponent and licensing
  determining whether a secondary licenser had to merge to host a given
  nominal.
- **Voice-based case** (`Phenomena/Case/Studies/Scott2023.lean`): case
  is keyed to argument position via Voice. Both frameworks use
  designated functional heads as case assigners; whether secondary
  licensers in a particular language are best identified with Voice
  flavors is a language-specific question this file does not adjudicate.
- **Feature gluttony** (@cite{coon-keine-2021}): an alternative to
  licensing-based accounts of hierarchy effects (PCC, dative-nominative
  configurations). @cite{coon-keine-2021} argue that hierarchy effects
  are *not* due to failures of nominal licensing but to a probe
  participating in too many Agree dependencies. Hybrid licensing
  applies to DOM patterns that feature gluttony does not target;
  the two are adjacent debates rather than competing analyses of the
  same data.

## Bridge to the Case Filter

§ 7 connects this module's `LicensingOutcome` to the Chomskyan Case
Filter formalized in `Theories/Syntax/Minimalism/Core/CaseFilter.lean`:
an outcome that values Case (any of `.byPrimary`, `.bySecondary`, or
`.byLexical`) satisfies the Case Filter, while `.unlicensed` does not.
Kalin's framework thus *derives* the Case Filter as the convergence
condition on hybrid licensing rather than stipulating it.

-/

namespace Syntax.Case.Licensing

-- We qualify `Core.Case` everywhere because `Core/Lexical/Word.lean`
-- aliases a *different* `Case` (UD.Case) at root scope.
open Minimalism (DPFeatures satisfiesCaseFilter)

-- ============================================================================
-- § 1: Primary vs. Secondary Licensers
-- ============================================================================

/-- A licenser merges either obligatorily (primary) or as a last-resort
    response to convergence requirements (secondary). Following
    @cite{kalin-2018}: every clause has exactly one primary licenser
    (e.g., T) and any number of secondary licensers (e.g., dedicated
    AGRO heads, prepositional case-assigners hosting DOM markers). -/
inductive LicenserKind where
  | primary
  | secondary
  deriving DecidableEq, Repr

/-- A nominal licenser, identified by its host head and merge kind.
    The `head` field is opaque — concrete languages instantiate it with
    e.g. "T", "AGRO", "P-DOM". The case actually realized on the
    licensed NP is `assignedCase`. -/
structure Licenser where
  kind : LicenserKind
  head : String
  assignedCase : Core.Case
  deriving DecidableEq, Repr

/-- Is this licenser primary (obligatorily merged in every clause)? -/
@[simp] def Licenser.isPrimary (ℓ : Licenser) : Bool :=
  ℓ.kind == .primary

-- ============================================================================
-- § 2: Nominals and Their Licensing Need
-- ============================================================================

/-- A nominal as seen by the licensing system. Extends `NPInDomain`
    (the configural type from `Dependent.lean`) with the
    licensing-requirement flag.

    `needsLicensing = true` is the Boolean abstraction of carrying an
    *uninterpretable, unvalued* [Case] feature in the
    @cite{pesetsky-torrego-2007} sense: the NP cannot be interpreted
    without being valued by an active licenser. `needsLicensing = false`
    means the NP lacks this feature (the [-specific] / [-definite] /
    [-animate] cell of a DOM language) and is interpretable in situ.

    `lexicalCase` (inherited from `NPInDomain`) records pre-assigned
    lexical case from a P or V head; lexical case independently values
    [Case] and so satisfies the licensing requirement on its own. -/
structure LicensedNP extends Syntax.Case.NPInDomain where
  needsLicensing : Bool
  deriving DecidableEq, Repr

/-- An NP's effective case state: `none` if it carries unvalued [Case]
    and has no lexical case; `some c` if either it has lexical case `c`
    or its [Case] feature is interpretable (no licensing needed). The
    accessor exposes the Pesetsky-Torrego abstraction underlying
    `needsLicensing` + `lexicalCase`. -/
def LicensedNP.caseFeature (np : LicensedNP) : Option Core.Case :=
  match np.lexicalCase, np.needsLicensing with
  | some c, _      => some c
  | none,   false  => some .nom  -- interpretable in situ; nominative is
                                  -- the default exponent for an inactive
                                  -- nominal (see Kalin §3 on Senaya
                                  -- non-specific objects)
  | none,   true   => none       -- needs licensing

/-- An NP is *active for licensing* iff it carries unvalued [Case] and
    has no lexical case independently satisfying the requirement. -/
@[simp] def LicensedNP.isActive (np : LicensedNP) : Bool :=
  np.needsLicensing && np.lexicalCase.isNone

theorem LicensedNP.caseFeature_none_iff_active (np : LicensedNP) :
    np.caseFeature = none ↔ np.isActive = true := by
  unfold caseFeature isActive
  cases np.lexicalCase <;> cases np.needsLicensing <;> simp

-- ============================================================================
-- § 3: A Clause's Licensing Inventory
-- ============================================================================

/-- A clause's licensing potential: its primary licenser plus the
    secondary licensers available for last-resort activation.
    @cite{kalin-2018}: every clause has exactly one primary licenser;
    secondaries are language-specific and may be empty. -/
structure ClauseLicensers where
  primary : Licenser
  secondaries : List Licenser
  primary_is_primary : primary.kind = .primary := by rfl

/-- All licensers in the clause, primary first. -/
def ClauseLicensers.all (cl : ClauseLicensers) : List Licenser :=
  cl.primary :: cl.secondaries

theorem ClauseLicensers.primary_isPrimary (cl : ClauseLicensers) :
    cl.primary.isPrimary = true := by
  simp [Licenser.isPrimary, cl.primary_is_primary]

-- ============================================================================
-- § 4: The Licensing Algorithm
-- ============================================================================

/-- Outcome of licensing a nominal. Each constructor records *which*
    licenser valued the NP's [Case] feature and *what* case was
    assigned, so two clauses with different primary heads (T vs. Infl)
    or different secondary assigners produce distinguishable results. -/
inductive LicensingOutcome where
  /-- Licensed by the obligatory primary head; records the head's name
      and the case it assigned. -/
  | byPrimary (head : String) (c : Core.Case)
  /-- Licensed by a last-resort secondary licenser. -/
  | bySecondary (head : String) (c : Core.Case)
  /-- Pre-licensed by P or V via lexical case (bleeds the Agree
      requirement). -/
  | byLexical (c : Core.Case)
  /-- Crash: no licenser available to value [Case]. -/
  | unlicensed
  deriving DecidableEq, Repr

/-- Has this NP's [Case] feature been valued? `true` for any of the
    three valuation outcomes; `false` only for `.unlicensed`. -/
@[simp] def LicensingOutcome.isLicensed : LicensingOutcome → Bool
  | .unlicensed => false
  | _ => true

/-- The case value an outcome assigns, if any. -/
def LicensingOutcome.assignedCase : LicensingOutcome → Option Core.Case
  | .byPrimary _ c    => some c
  | .bySecondary _ c  => some c
  | .byLexical c      => some c
  | .unlicensed       => none

/-- The result of licensing a single NP. -/
structure LicensedResult where
  label : String
  outcome : LicensingOutcome
  deriving DecidableEq, Repr

/-- License a queue of secondary licensers against a list of active NPs.
    Each NP consumes one secondary; an NP with no secondary remaining
    crashes as `.unlicensed`. Hoisted out of `licenseActive` as a
    private top-level def (rather than a `where` clause) so callers can
    reason about it directly in proofs. -/
private def licenseSecondaries :
    List Licenser → List LicensedNP → List LicensedResult
  | _, [] => []
  | [], np :: rest =>
      { label := np.label, outcome := .unlicensed } ::
        licenseSecondaries [] rest
  | s :: ss, np :: rest =>
      { label := np.label, outcome := .bySecondary s.head s.assignedCase } ::
        licenseSecondaries ss rest

/-- License a list of active (need-licensing, no lexical-case) NPs given
    a primary licenser and a queue of secondary licensers. The primary
    licenser handles the first NP; subsequent NPs draw from the
    secondary queue in order.

    @cite{kalin-2018}'s economy condition on secondary licensers — that
    a secondary is "active" iff its inactivity would leave some nominal
    unlicensed — is implemented here by greedily consuming secondaries
    only when active NPs remain. -/
def licenseActive (primary : Licenser) (secondaries : List Licenser)
    (active : List LicensedNP) : List LicensedResult :=
  match active with
  | [] => []
  | np :: rest =>
      { label := np.label,
        outcome := .byPrimary primary.head primary.assignedCase } ::
        licenseSecondaries secondaries rest

/-- License a list of NPs by mapping each to its outcome via three
    disjoint branches:
    - lexical case present → `.byLexical`,
    - no lexical case and not active → primary licenses trivially,
    - active → look up the label in the result of `licenseActive` on
      the active sublist.

    Mapping (rather than concatenating filtered partitions) makes the
    output the same length as the input by construction, and preserves
    the input's label order. NPs are assumed to have distinct labels;
    this is a representational invariant (a Spell-Out domain doesn't
    contain two NPs with the same opaque label). -/
def licenseNPs (cl : ClauseLicensers) (nps : List LicensedNP) :
    List LicensedResult :=
  let active := nps.filter LicensedNP.isActive
  let assignments := licenseActive cl.primary cl.secondaries active
  nps.map λ np =>
    { label := np.label,
      outcome :=
        match np.lexicalCase with
        | some c => .byLexical c
        | none =>
          if np.needsLicensing then
            ((assignments.find? (·.label == np.label)).map (·.outcome)).getD
              .unlicensed
          else
            .byPrimary cl.primary.head cl.primary.assignedCase }

/-- Look up the licensing outcome for an NP by label. -/
def getOutcomeOf (label : String) (results : List LicensedResult) :
    Option LicensingOutcome :=
  (results.find? (·.label == label)).map (·.outcome)

-- ============================================================================
-- § 5: DOM as Hybrid-Licensing Signature
-- ============================================================================

/-- A nominal is *DOM-marked* iff licensing required activating a
    secondary licenser. The unmarked/marked split in DOM languages is
    thus derivative of the licensing algorithm rather than a primitive
    of the case system. -/
@[simp] def isDOMMarked : LicensingOutcome → Prop
  | .bySecondary _ _ => True
  | _ => False

instance : DecidablePred isDOMMarked := fun o => by
  cases o <;> unfold isDOMMarked <;> infer_instance

/-- The set of DOM-marked NP labels in a result list. -/
def domMarkedNPs (results : List LicensedResult) : List String :=
  (results.filter λ r => decide (isDOMMarked r.outcome)).map (·.label)

-- ============================================================================
-- § 6: Structural Properties
-- ============================================================================

/-! These hold for arbitrary inputs and lock down the algorithm's
shape: the secondary queue is consumed left-to-right, and an NP is
licensed iff the algorithm could supply it with some licenser. -/

theorem licenseSecondaries_length (avail : List Licenser)
    (active : List LicensedNP) :
    (licenseSecondaries avail active).length = active.length := by
  induction active generalizing avail with
  | nil => rfl
  | cons _ rest ih =>
    cases avail with
    | nil =>
      unfold licenseSecondaries
      simp only [List.length_cons]
      exact congrArg (· + 1) (ih [])
    | cons s ss =>
      unfold licenseSecondaries
      simp only [List.length_cons]
      exact congrArg (· + 1) (ih ss)

theorem licenseActive_length (primary : Licenser) (secondaries : List Licenser)
    (active : List LicensedNP) :
    (licenseActive primary secondaries active).length = active.length := by
  cases active with
  | nil => rfl
  | cons _ rest =>
    unfold licenseActive
    simp only [List.length_cons]
    exact congrArg (· + 1) (licenseSecondaries_length secondaries rest)

/-- **Totality of the licensing algorithm.** Every input NP yields
    exactly one output result, in the same order. The algorithm
    preserves the NP inventory of the input. -/
theorem licenseNPs_length (cl : ClauseLicensers) (nps : List LicensedNP) :
    (licenseNPs cl nps).length = nps.length := by
  unfold licenseNPs; rw [List.length_map]

/-- The output preserves input labels in order — by construction, since
    every constructor in the body of `licenseNPs` sets `label := np.label`. -/
theorem licenseNPs_labels (cl : ClauseLicensers) (nps : List LicensedNP) :
    (licenseNPs cl nps).map (·.label) = nps.map (·.label) := by
  unfold licenseNPs
  rw [List.map_map]
  rfl

/-- The first active NP (in c-command order) is always licensed by the
    primary head — this is the structural content of "every clause
    carries an obligatory primary licenser." -/
theorem first_active_byPrimary (primary : Licenser)
    (secondaries : List Licenser) (np : LicensedNP) (rest : List LicensedNP) :
    (licenseActive primary secondaries (np :: rest))[0]? =
      some { label := np.label,
             outcome := .byPrimary primary.head primary.assignedCase } := by
  rfl

/-- **Kalin Thesis 1 (some NPs need licensing).** A non-needing NP
    receives `.byPrimary` regardless of its position — no secondary is
    consumed on its behalf. Captured here as: an NP with
    `needsLicensing = false` and no lexical case is filtered out of
    `active` and so gets the primary outcome via `licenseNPs`. -/
theorem nonNeeding_isLicensed_byPrimary (cl : ClauseLicensers)
    (np : LicensedNP) (h_lex : np.lexicalCase = none)
    (h_need : np.needsLicensing = false) :
    LicensedResult.outcome <$>
        (licenseNPs cl [np]).head?
      = some (.byPrimary cl.primary.head cl.primary.assignedCase) := by
  unfold licenseNPs
  simp [h_lex, h_need]

/-- A helper: if there are at least as many secondaries as NPs to
    license, no NP escapes `licenseSecondaries` with `.unlicensed`. -/
private theorem licenseSecondaries_no_unlicensed (avail : List Licenser)
    (active : List LicensedNP) (h : active.length ≤ avail.length)
    (r : LicensedResult) (hr : r ∈ licenseSecondaries avail active) :
    r.outcome ≠ .unlicensed := by
  induction active generalizing avail with
  | nil => cases hr
  | cons _ rest ih =>
    cases avail with
    | nil => simp at h
    | cons _ ss =>
      unfold licenseSecondaries at hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · intro heq; cases heq
      · exact ih ss (by simp at h; omega) hr'

/-- **Kalin Thesis 2 (all NPs CAN be licensed).** Given enough
    secondaries (one fewer than the active-NP count, since the primary
    handles the first), every active NP is licensed: no `.unlicensed`
    outcome arises in `licenseActive`. -/
theorem licenseActive_no_crash_when_enough_secondaries
    (primary : Licenser) (secondaries : List Licenser)
    (active : List LicensedNP)
    (h : active.length ≤ secondaries.length + 1) :
    ∀ r ∈ licenseActive primary secondaries active, r.outcome ≠ .unlicensed := by
  intro r hr
  cases active with
  | nil => cases hr
  | cons _ rest =>
    unfold licenseActive at hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · intro heq; cases heq
    · exact licenseSecondaries_no_unlicensed secondaries rest
        (by simp at h; omega) r hr'

/-- **Kalin Thesis 3 (primary obligatory + secondary last-resort).** If
    no NP needs licensing (and none has lexical case), every NP gets
    `.byPrimary` — secondaries never activate. -/
theorem no_need_means_no_secondaries_used (cl : ClauseLicensers)
    (nps : List LicensedNP)
    (h : ∀ np ∈ nps, np.needsLicensing = false ∧ np.lexicalCase = none) :
    ∀ r ∈ licenseNPs cl nps,
      r.outcome = .byPrimary cl.primary.head cl.primary.assignedCase := by
  intro r hr
  unfold licenseNPs at hr
  rw [List.mem_map] at hr
  obtain ⟨np, hnp_mem, hr_eq⟩ := hr
  obtain ⟨h_need, h_lex⟩ := h np hnp_mem
  rw [← hr_eq]
  simp [h_lex, h_need]

-- ============================================================================
-- § 7: Bridge to the Case Filter
-- ============================================================================

/-! Connects `LicensingOutcome` to the Chomskyan Case Filter
formalized in `Minimalism/Core/CaseFilter.lean`: an outcome valued by
*any* mechanism (primary, secondary, or lexical) satisfies the Case
Filter; only `.unlicensed` violates it. Kalin's framework thus
*derives* the Case Filter as the convergence condition on hybrid
licensing — not a separate stipulation. -/

/-- Translate a licensing outcome into the DP feature bundle that
    `Minimalism.satisfiesCaseFilter` consumes. Any valued outcome
    becomes a DP with valued [Case]; `.unlicensed` becomes a DP with
    unvalued [Case]. -/
def LicensingOutcome.toDPFeatures : LicensingOutcome → DPFeatures
  | .byPrimary _ c   => DPFeatures.withCase [] c
  | .bySecondary _ c => DPFeatures.withCase [] c
  | .byLexical c     => DPFeatures.withCase [] c
  | .unlicensed      => DPFeatures.withUnvaluedCase []

/-- **Bridge: licensing convergence ⟺ Case Filter satisfied.** A
    nominal's [Case] is valued by some hybrid-licensing mechanism iff
    it satisfies the Chomskyan Case Filter. The two convergence
    conditions are extensionally equivalent — making the Case Filter a
    theorem of hybrid licensing rather than an independent axiom. -/
theorem isLicensed_iff_satisfiesCaseFilter (o : LicensingOutcome) :
    o.isLicensed = satisfiesCaseFilter o.toDPFeatures := by
  cases o <;> rfl

/-- A list of licensing results converges (no `.unlicensed`) iff every
    induced DP satisfies the Case Filter. -/
theorem all_isLicensed_iff_caseFilterHolds (results : List LicensedResult) :
    results.all (·.outcome.isLicensed) =
      Minimalism.caseFilterHolds (results.map λ r => r.outcome.toDPFeatures) := by
  induction results with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.all_cons, List.map_cons, Minimalism.caseFilterHolds,
               List.all_cons]
    rw [isLicensed_iff_satisfiesCaseFilter]
    unfold Minimalism.caseFilterHolds at ih
    rw [ih]

-- ============================================================================
-- § 8: Worked Examples
-- ============================================================================

/-! These illustrate the algorithm on a Turkish-style DOM clause and on
the degenerate no-secondary configuration. They are not the empirical
core of the framework — that lives in `Phenomena/Case/Studies/` — but
they exercise the algorithm end-to-end and would catch breakage from
any refactor of the licensing pipeline. -/

private def primaryT : Licenser :=
  { kind := .primary, head := "T", assignedCase := .nom }

private def secondaryAgrO : Licenser :=
  { kind := .secondary, head := "AGRO", assignedCase := .acc }

private def turkishLikeClause : ClauseLicensers :=
  { primary := primaryT, secondaries := [secondaryAgrO] }

/-- A canonical transitive: subject + specific object. The subject is
    licensed by primary T; the object needs licensing and is handled by
    the secondary AGRO — yielding DOM marking on the object. -/
private def transitive_specific : List LicensedNP :=
  [ { label := "subj", lexicalCase := none, needsLicensing := true }
  , { label := "obj-specific", lexicalCase := none, needsLicensing := true } ]

/-- A nonspecific object that lacks the licensing requirement remains
    unmarked — the secondary licenser need not activate. -/
private def transitive_nonspecific : List LicensedNP :=
  [ { label := "subj", lexicalCase := none, needsLicensing := true }
  , { label := "obj-nonspecific", lexicalCase := none, needsLicensing := false } ]

theorem specific_object_is_dom_marked :
    getOutcomeOf "obj-specific"
      (licenseNPs turkishLikeClause transitive_specific) =
    some (.bySecondary "AGRO" .acc) := by decide

theorem nonspecific_object_unmarked :
    getOutcomeOf "obj-nonspecific"
      (licenseNPs turkishLikeClause transitive_nonspecific) =
    some (.byPrimary "T" .nom) := by decide

theorem subject_always_primary :
    getOutcomeOf "subj"
      (licenseNPs turkishLikeClause transitive_specific) =
        some (.byPrimary "T" .nom) ∧
    getOutcomeOf "subj"
      (licenseNPs turkishLikeClause transitive_nonspecific) =
        some (.byPrimary "T" .nom) := ⟨by decide, by decide⟩

/-- DOM signature: only the specific object is marked in the specific
    transitive; nothing is marked in the nonspecific transitive. -/
theorem dom_signature :
    domMarkedNPs (licenseNPs turkishLikeClause transitive_specific) =
      ["obj-specific"] ∧
    domMarkedNPs (licenseNPs turkishLikeClause transitive_nonspecific) = [] :=
  ⟨by decide, by decide⟩

/-- A clause with no secondary licenser cannot host a second active
    nominal — modeling languages where the primary licenser is the only
    one available. -/
private def noSecondaryClause : ClauseLicensers :=
  { primary := primaryT, secondaries := [] }

theorem no_secondary_means_crash :
    getOutcomeOf "obj-specific"
      (licenseNPs noSecondaryClause transitive_specific) =
        some .unlicensed := by decide

/-- **Primary head identity is load-bearing.** Two clauses with
    different primary licensers produce distinguishable outcomes — the
    algorithm honors the primary's identity rather than collapsing it
    to an opaque `.byPrimary` token. -/
private def inflPrimaryClause : ClauseLicensers :=
  { primary := { kind := .primary, head := "Infl", assignedCase := .nom },
    secondaries := [secondaryAgrO] }

theorem primary_head_distinguishes :
    getOutcomeOf "subj"
      (licenseNPs turkishLikeClause transitive_specific) ≠
    getOutcomeOf "subj"
      (licenseNPs inflPrimaryClause transitive_specific) := by decide

end Syntax.Case.Licensing
