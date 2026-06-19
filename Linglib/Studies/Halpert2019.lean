import Linglib.Syntax.Minimalist.Probe.Basic

/-!
# [halpert-2019]: Raising, unphased

Halpert derives cross-linguistic variation in raising-to-subject
**without the Phase Impenetrability Condition**. Two clause-and-language
properties do the work:

1. whether a clausal complement is a **φ-goal** matrix T interacts with;
2. whether that clause can **satisfy the EPP** (move to Spec,TP);

plus whether T has an EPP at all. The engine is the canonical `Probe`
(`Probe/Basic.lean`): Deal's ([deal-2015a-nels]) *interaction* is `Probe.vis`
(the search halts on a φ-bearing clause — an A-over-A intervener) and
*satisfaction* is `Probe.act` (the goal can occupy Spec,TP). When the
closest clause interacts but cannot satisfy the EPP it absorbs the probe
(`Probe.agree_eq_none_of_inactive`); T then probes a second time
([rackowski-richards-2005]), reaching the embedded subject —
hyper-raising — when it genuinely Agreed with the clause, and stalling
(defective intervention) when it did not.

This **relativizes phasehood to φ-probes** rather than positing a fixed
PIC (`phaseImpenetrable`, `Syntax/Minimalist/Phase.lean`): finite CPs and
nonfinite TPs of the *same size* get opposite raising outcomes across
languages, so the split cannot be size/phase-driven
(`finite_cp_outcome_not_size_driven`, `nonfinite_tp_outcome_not_size_driven`).

## Main declarations

- `Clause` — a complement by its three probe-relevant properties.
- `eppProbe` / `raisingOutcome` — the matrix-T EPP probe and the
  derivation it drives, run through `Probe.agree`.
- `english_profile`, `zulu_profile`, `uyghur_profile`,
  `makhuwa_no_raising` — the attested profiles, derived from the engine.
-/

namespace Halpert2019

open Minimalist

/-- A clausal complement, classified by the three probe-relevant
    properties Halpert's account turns on. -/
structure Clause where
  /-- T's φ-probe halts on it: a φ-goal, or a defective nominal
      intervener (the English `that`-CP). Transparent clauses (English
      nonfinite TP, small clauses) are not interveners. -/
  interacts : Bool
  /-- T can Agree with it (copy φ) — a genuine φ-goal. The English
      `that`-CP interacts but has no φ to copy ([moulton-2009]). -/
  canAgree : Bool
  /-- It can satisfy the EPP by moving to Spec,TP (Zulu infinitival TP,
      Uyghur DP-nominalization), vs. clauses barred from Spec,TP (Zulu
      finite CP, Uyghur NP-nominalization). -/
  canSatisfyEPP : Bool
  deriving DecidableEq, Repr

/-- A goal the matrix-T EPP probe ranges over, in c-command order: the
    clausal complement (closest) then the embedded subject. -/
inductive Goal
  | clause (c : Clause)
  | subject
  deriving DecidableEq, Repr

/-- The matrix-T EPP probe: [deal-2015a-nels]'s *interaction* is `Probe.vis`
    (the search halts on an intervening clause), *satisfaction* is
    `Probe.act` (the goal can occupy Spec,TP). The embedded subject is a
    movable φ-goal — visible and EPP-satisfying. -/
def eppProbe : Probe Goal where
  vis := fun g => match g with | .clause c => c.interacts | .subject => true
  act := fun g => match g with | .clause c => c.canSatisfyEPP | .subject => true

/-- The clause c-commands the embedded subject. -/
def goals (c : Clause) : List Goal := [.clause c, .subject]

/-- The five raising outcomes Halpert's typology distinguishes. -/
inductive RaisingOutcome
  /-- No EPP: T Agrees with the clause in situ, nothing moves (Makhuwa,
      Matengo). -/
  | noRaising
  /-- Ordinary raising: the embedded subject moves to matrix Spec,TP
      (English nonfinite TP). -/
  | subjectRaises
  /-- The whole clause satisfies the EPP and moves (Zulu infinitival TP,
      Uyghur DP-nominalization). -/
  | clauseRaises
  /-- A second Agree reaches the embedded subject (Zulu finite CP,
      Uyghur NP-nominalization). -/
  | hyperRaises
  /-- A defective intervener stalls the probe (English finite CP). -/
  | blocked
  deriving DecidableEq, Repr

/-- The derivation, run through the canonical `Probe` engine. With no EPP
    nothing moves. With an EPP, matrix T runs `eppProbe.agree` over
    `[clause, subject]`: a transparent clause is skipped and the subject
    raises; a clause that satisfies the EPP is Agreed-with and raises
    whole; an interacting clause that cannot satisfy the EPP absorbs the
    probe (`Probe.agree_eq_none_of_inactive`), and the licensed second
    probe reaches the embedded subject (`hyperRaises`) iff T genuinely
    Agreed with the clause, else stalls (`blocked`). -/
def raisingOutcome (c : Clause) (hasEPP : Bool) : RaisingOutcome :=
  if hasEPP then
    match eppProbe.agree (goals c) with
    | some .subject => .subjectRaises
    | some (.clause _) => .clauseRaises
    | none => if c.canAgree then .hyperRaises else .blocked
  else .noRaising

/-! ### The derivation, from the `Probe` engine -/

private theorem search_clause {c : Clause} (h : c.interacts = true) :
    eppProbe.search (goals c) = some (.clause c) := by
  simp only [Probe.search, goals, eppProbe, List.find?_cons_of_pos, h]

private theorem search_subject {c : Clause} (h : c.interacts = false) :
    eppProbe.search (goals c) = some .subject := by
  simp only [Probe.search, goals, eppProbe, List.find?_cons_of_neg, h,
    List.find?_cons_of_pos, Bool.false_eq_true, not_false_eq_true]

/-- No EPP ⇒ no raising, whatever the clause. -/
theorem raisingOutcome_eq_noRaising (c : Clause) :
    raisingOutcome c false = .noRaising := rfl

/-- A transparent clause (not an intervener) lets T reach the embedded
    subject: ordinary raising. -/
theorem raisingOutcome_eq_subjectRaises {c : Clause} (h : c.interacts = false) :
    raisingOutcome c true = .subjectRaises := by
  have : eppProbe.agree (goals c) = some .subject :=
    Probe.agree_eq_some_iff.mpr ⟨search_subject h, rfl⟩
  simp only [raisingOutcome, this, if_true]

/-- A φ-goal that satisfies the EPP raises as a whole clause; the
    embedded subject does not move. -/
theorem raisingOutcome_eq_clauseRaises {c : Clause} (hi : c.interacts = true)
    (he : c.canSatisfyEPP = true) : raisingOutcome c true = .clauseRaises := by
  have : eppProbe.agree (goals c) = some (.clause c) :=
    Probe.agree_eq_some_iff.mpr ⟨search_clause hi, he⟩
  simp only [raisingOutcome, this, if_true]

/-- A φ-goal that interacts but cannot satisfy the EPP absorbs the first
    Agree; the licensed second probe reaches the embedded subject. -/
theorem raisingOutcome_eq_hyperRaises {c : Clause} (hi : c.interacts = true)
    (ha : c.canAgree = true) (he : c.canSatisfyEPP = false) :
    raisingOutcome c true = .hyperRaises := by
  have : eppProbe.agree (goals c) = none :=
    Probe.agree_eq_none_of_inactive (search_clause hi) he
  simp only [raisingOutcome, this, ha, if_true]

/-- A defective intervener (interacts, but T cannot Agree with it) stalls
    the probe: no second Agree, no raising. -/
theorem raisingOutcome_eq_blocked {c : Clause} (hi : c.interacts = true)
    (ha : c.canAgree = false) (he : c.canSatisfyEPP = false) :
    raisingOutcome c true = .blocked := by
  have : eppProbe.agree (goals c) = none :=
    Probe.agree_eq_none_of_inactive (search_clause hi) he
  simp only [raisingOutcome, this, ha, if_true, if_false, Bool.false_eq_true]

/-! ### Cross-linguistic raising profiles -/

/-- English nonfinite TP: transparent, not an intervener. -/
def englishNonfiniteTP : Clause := ⟨false, false, false⟩
/-- English finite `that`-CP: a defective intervener — visible, no φ to
    Agree, cannot move ([moulton-2009]). -/
def englishFiniteCP : Clause := ⟨true, false, false⟩
/-- Zulu small clause: transparent. -/
def zuluSmallClause : Clause := ⟨false, false, false⟩
/-- Zulu infinitival TP: a φ-goal that satisfies the EPP. -/
def zuluInfinitiveTP : Clause := ⟨true, true, true⟩
/-- Zulu finite `ukuthi`-CP: a φ-goal that cannot satisfy the EPP. -/
def zuluFiniteCP : Clause := ⟨true, true, false⟩
/-- Uyghur DP-nominalization (non-modal adjective): φ-goal, satisfies the
    EPP ([asarina-2011]). -/
def uyghurDP : Clause := ⟨true, true, true⟩
/-- Uyghur NP-nominalization (modal adjective): φ-goal, cannot satisfy
    the EPP. -/
def uyghurNP : Clause := ⟨true, true, false⟩

/-- English raising profile ([halpert-2019]): raising is *required* out of
    a nonfinite TP and *blocked* out of a finite CP. (Models the
    `seem`/`be likely` predicates; the `tend`/`happen`/`keep` selection
    matrix and the AP/NP-vs-VP small-clause split are not modelled.) -/
theorem english_profile :
    raisingOutcome englishNonfiniteTP true = .subjectRaises ∧
    raisingOutcome englishFiniteCP true = .blocked :=
  ⟨raisingOutcome_eq_subjectRaises rfl, raisingOutcome_eq_blocked rfl rfl rfl⟩

/-- Zulu raising profile ([halpert-2019], building on [ura-1994]'s
    hyper-raising): hyper-raising out of a finite CP, the whole clause
    raises out of a nonfinite TP (so the subject does not), and the
    subject raises out of a small clause. The finite-CP case is in fact
    *optional* — an expletive `ku-` non-raising variant coexists with
    hyper-raising, and the `ku-`/`u-` morphology spells out first- vs.
    second-Agree — an optionality this deterministic `RaisingOutcome`
    abstracts over. -/
theorem zulu_profile :
    raisingOutcome zuluFiniteCP true = .hyperRaises ∧
    raisingOutcome zuluInfinitiveTP true = .clauseRaises ∧
    raisingOutcome zuluSmallClause true = .subjectRaises :=
  ⟨raisingOutcome_eq_hyperRaises rfl rfl rfl, raisingOutcome_eq_clauseRaises rfl rfl,
   raisingOutcome_eq_subjectRaises rfl⟩

/-- Uyghur raising profile ([asarina-2011], [halpert-2019]): a
    DP-nominalization raises whole; an NP-nominalization hyper-raises the
    embedded subject. -/
theorem uyghur_profile :
    raisingOutcome uyghurDP true = .clauseRaises ∧
    raisingOutcome uyghurNP true = .hyperRaises :=
  ⟨raisingOutcome_eq_clauseRaises rfl rfl, raisingOutcome_eq_hyperRaises rfl rfl rfl⟩

/-- Makhuwa/Matengo: removing just the EPP from the Zulu setting kills
    raising entirely — even out of a finite-CP φ-goal. -/
theorem makhuwa_no_raising (c : Clause) : raisingOutcome c false = .noRaising :=
  raisingOutcome_eq_noRaising c

/-! ### Raising is unphased -/

/-- The thesis: a finite CP yields hyper-raising in Zulu but is blocked in
    English — same clause "size", opposite outcomes — because the split is
    φ-goal status (`canAgree`), not a size-driven phase boundary. -/
theorem finite_cp_outcome_not_size_driven :
    raisingOutcome zuluFiniteCP true ≠ raisingOutcome englishFiniteCP true := by
  decide

/-- Likewise a nonfinite TP: the whole clause raises in Zulu but the
    subject raises in English — the split is EPP-satisfaction
    (`canSatisfyEPP`), not clause size. -/
theorem nonfinite_tp_outcome_not_size_driven :
    raisingOutcome zuluInfinitiveTP true ≠ raisingOutcome englishNonfiniteTP true := by
  decide

end Halpert2019
