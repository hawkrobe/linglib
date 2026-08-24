import Linglib.Features.Case.Basic
import Linglib.Features.Case.Source
import Linglib.Syntax.Case.Dependent

/-!
# Hybrid licensing

This file formalizes the theory of nominal licensing of [kalin-2018], which
decouples *which* nominals need licensing from *where* the licensers live.
Every clause carries one obligatory primary licenser plus zero or more
secondary licensers that merge only when their inactivity would leave some
nominal unlicensed — a last-resort economy condition on functional structure.
Independently, a language fixes which nominals need licensing at all: making
every nominal need it yields no differential object marking, while restricting
the requirement to nominals carrying a structural or featural component
([+specific], [+definite], [+animate]) yields DOM as the visible signature of
a secondary licenser having been activated.

"Needs licensing" is an uninterpretable, unvalued [Case] feature in the sense
of [pesetsky-torrego-2007], and licensing is its valuation under Agree;
`LicensedNP.needsLicensing` is that feature's Boolean abstraction. A nominal
is *unmarked* when the primary licenser suffices and *marked* when convergence
required a secondary, so the marked/unmarked split is derived rather than
primitive.

## Main definitions

* `Licenser`, `ClauseLicensers`: a licenser and a clause's inventory of them,
  exactly one of which is primary.
* `LicensedNP`: a nominal together with its licensing requirement.
* `LicensingOutcome`: which licenser valued a nominal, or the crash;
  `LicensingOutcome.toNeutral` projects it onto the account-neutral
  `Case.Source`.
* `licenseNPs`: the licensing algorithm over a clause.
* `isDOMMarked`: a nominal is DOM-marked exactly when a secondary licensed it.

## Main results

* `licenseNPs_length`, `licenseNPs_labels`: licensing is total and
  order-preserving.
* `licenseActive_no_crash_when_enough_secondaries`,
  `no_need_means_no_secondaries_used`: with enough secondaries nothing
  crashes, and with nothing needing licensing no secondary activates.

## References

* [kalin-2018]
* [pesetsky-torrego-2007]
-/
namespace Syntax.Case.Licensing

-- `Case` is qualified throughout: a different `Case` (UD.Case) is aliased at
-- root scope.

/-! ### Licensers -/

/-- A licenser merges either obligatorily (primary) or as a last-resort
    response to convergence requirements (secondary). Following
    [kalin-2018]: every clause has exactly one primary licenser
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
  assignedCase : Case
  deriving DecidableEq, Repr

/-! ### Nominals and their licensing requirement -/

/-- A nominal as seen by the licensing system. Extends `NPInDomain`
    (the configural type from `Dependent.lean`) with the
    licensing-requirement flag.

    `needsLicensing = true` is the Boolean abstraction of carrying an
    *uninterpretable, unvalued* [Case] feature in the
    [pesetsky-torrego-2007] sense: the NP cannot be interpreted
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
def LicensedNP.caseFeature (np : LicensedNP) : Option Case :=
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

/-! ### The licensing inventory of a clause -/

/-- A clause's licensing potential: its primary licenser plus the
    secondary licensers available for last-resort activation.
    [kalin-2018]: every clause has exactly one primary licenser;
    secondaries are language-specific and may be empty. -/
structure ClauseLicensers where
  primary : Licenser
  secondaries : List Licenser
  primary_is_primary : primary.kind = .primary := by rfl

/-- All licensers in the clause, primary first. -/
def ClauseLicensers.all (cl : ClauseLicensers) : List Licenser :=
  cl.primary :: cl.secondaries

/-! ### The licensing algorithm -/

/-- Outcome of licensing a nominal. Each constructor records *which*
    licenser valued the NP's [Case] feature and *what* case was
    assigned, so two clauses with different primary heads (T vs. Infl)
    or different secondary assigners produce distinguishable results. -/
inductive LicensingOutcome where
  /-- Licensed by the obligatory primary head; records the head's name
      and the case it assigned. -/
  | byPrimary (head : String) (c : Case)
  /-- Licensed by a last-resort secondary licenser. -/
  | bySecondary (head : String) (c : Case)
  /-- Pre-licensed by P or V via lexical case (bleeds the Agree
      requirement). -/
  | byLexical (c : Case)
  /-- Crash: no licenser available to value [Case]. -/
  | unlicensed
  deriving DecidableEq, Repr

/-- The nominal's [Case] feature was valued, by any of the three mechanisms. -/
@[simp] def LicensingOutcome.IsLicensed : LicensingOutcome → Prop
  | .unlicensed => False
  | _ => True

instance : DecidablePred LicensingOutcome.IsLicensed := fun o => by
  cases o <;> unfold LicensingOutcome.IsLicensed <;> infer_instance

/-- The case value an outcome assigns, if any. -/
def LicensingOutcome.assignedCase : LicensingOutcome → Option Case
  | .byPrimary _ c    => some c
  | .bySecondary _ c  => some c
  | .byLexical c      => some c
  | .unlicensed       => none

/-- The neutral provenance (`Case.Source`) of a licensing outcome: primary
    and secondary licensing are `structural` (Agree-valued), lexical
    pre-licensing is `inherent`, and the crash `unlicensed` is `uncased` —
    the only account in the library that produces it. -/
def LicensingOutcome.toNeutral : LicensingOutcome → _root_.Case.Source
  | .byPrimary _ _   => .structural
  | .bySecondary _ _ => .structural
  | .byLexical _     => .inherent
  | .unlicensed      => .uncased

/-- The neutral source faithfully records licensing **failure**: an outcome
    is `uncased` iff it is unlicensed. With `CaseSource.toNeutral_ne_uncased`
    (dependent case is total), this is the foundational provenance-level
    contrast between the two rival accounts — one can crash, the other
    cannot. -/
theorem LicensingOutcome.toNeutral_uncased_iff (o : LicensingOutcome) :
    o.toNeutral = _root_.Case.Source.uncased ↔ ¬ o.IsLicensed := by
  cases o <;> simp [LicensingOutcome.toNeutral]

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

    [kalin-2018]'s economy condition on secondary licensers — that
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

/-! ### Differential object marking -/

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

/-! ### Structural properties -/

/-! These hold for arbitrary inputs and lock down the algorithm's
shape: the secondary queue is consumed left-to-right, and an NP is
licensed iff the algorithm could supply it with some licenser. -/

theorem licenseSecondaries_length (avail : List Licenser)
    (active : List LicensedNP) :
    (licenseSecondaries avail active).length = active.length := by
  induction active generalizing avail with
  | nil => rfl
  | cons _ _ ih => cases avail <;> simp [licenseSecondaries, ih]

theorem licenseActive_length (primary : Licenser) (secondaries : List Licenser)
    (active : List LicensedNP) :
    (licenseActive primary secondaries active).length = active.length := by
  cases active <;> simp [licenseActive, licenseSecondaries_length]

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

/-! ### Differential marking requires an available secondary -/

private theorem licenseSecondaries_nil (active : List LicensedNP) :
    ∀ r ∈ licenseSecondaries [] active, r.outcome = .unlicensed := by
  induction active with
  | nil => simp [licenseSecondaries]
  | cons _ _ ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr' <;> [rfl; exact ih r hr']

private theorem licenseActive_nil_not_dom (primary : Licenser)
    (active : List LicensedNP) :
    ∀ r ∈ licenseActive primary [] active, ¬ isDOMMarked r.outcome := by
  intro r hr
  cases active with
  | nil => cases hr
  | cons _ tl =>
    rcases List.mem_cons.mp hr with rfl | hr'
    · simp
    · simp [licenseSecondaries_nil tl r hr']

/-- With no secondary licenser available, nothing is DOM-marked: the
    marked/unmarked split exists only where a secondary can activate. -/
theorem no_dom_without_secondaries (cl : ClauseLicensers) (nps : List LicensedNP)
    (h : cl.secondaries = []) :
    ∀ r ∈ licenseNPs cl nps, ¬ isDOMMarked r.outcome := by
  intro r hr
  simp only [licenseNPs, List.mem_map] at hr
  obtain ⟨np, _, rfl⟩ := hr
  cases hlex : np.lexicalCase with
  | some c => simp
  | none =>
    by_cases hneed : np.needsLicensing
    · simp only [hneed, if_pos]
      rcases hfind : List.find? (·.label == np.label)
        (licenseActive cl.primary cl.secondaries
          (nps.filter LicensedNP.isActive)) with _ | q
      · rw [hfind]; simp
      · rw [hfind]
        simpa using licenseActive_nil_not_dom cl.primary _ q
          (h ▸ List.mem_of_find?_eq_some hfind)
    · simp [hneed]

/-- Every DOM-marked label in a result list was licensed by a secondary. -/
theorem mem_domMarkedNPs (results : List LicensedResult) (lbl : String)
    (h : lbl ∈ domMarkedNPs results) :
    ∃ r ∈ results, r.label = lbl ∧ isDOMMarked r.outcome := by
  simp only [domMarkedNPs, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
  obtain ⟨r, ⟨hmem, hdom⟩, rfl⟩ := h
  exact ⟨r, hmem, rfl, hdom⟩

end Syntax.Case.Licensing
