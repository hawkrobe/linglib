module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English ditransitive verbs

This file defines the English ditransitive verbs of Bruening's study of implicit arguments,
*charge*, *cost*, *fine*, *tip*, *pay*, *forgive*, *deny*, *permit*, *teach*, *feed*, *show*,
*award*, *grant*, *offer*, *lend* and the rest, with the frames in which each argument may be
implicit.

## References

* [bruening-2021]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree
open English.Inflection

/-! ### Ditransitive verbs and implicit arguments ([bruening-2021]) -/

/-! Ditransitive verbs classified by their implicit argument behavior,
    following [bruening-2021] Table (56). The classification is
    theory-neutral: it records surface optionality and interpretation
    without committing to a specific structural analysis. -/

-- DOC-only verbs (no PP frame alternant)

/-- "charge" — DOC-only. Implicit second obj indef, implicit goal def (addressee). -/
def charge : Verb := .mkRegular {
  form := "charge"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill, .equip, .run} }

/-- "cost" — DOC-only. Implicit second obj indef, implicit goal def. -/
def cost : Verb := .mkRegular {
  form := "cost"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .state
  levinClasses := {LevinClass.cost} }

/-- "fine" — DOC-only. Implicit second obj indef, implicit goal def. -/
def fine : Verb := .mkRegular {
  form := "fine"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill, .judgment} }

/-- "tip" — DOC-only. Implicit second obj indef, implicit goal def (unique). -/
def tip : Verb where
  form := "tip"
  form3sg := "tips"
  formPast := "tipped"
  formPastPart := "tipped"
  formPresPart := "tipping"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill, .throw}

/-- "pay" — DOC-only. Implicit second obj indef, implicit goal def. -/
def pay : Verb where
  form := "pay"
  form3sg := "pays"
  formPast := "paid"
  formPastPart := "paid"
  formPresPart := "paying"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩, ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

/-- "strike" — DOC-only. Implicit second obj indef, implicit goal def (familiar). -/
def strike_ : Verb where
  form := "strike"
  form3sg := "strikes"
  formPast := "struck"
  formPastPart := "struck"
  formPresPart := "striking"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .achievement
  senseTag := .default
  levinClasses := {LevinClass.amuse, .hit, .soundEmission}

/-- "forgive" — DOC-only. Implicit second obj def, implicit goal def (addressee). -/
def forgive : Verb where
  form := "forgive"
  form3sg := "forgives"
  formPast := "forgave"
  formPastPart := "forgiven"
  formPresPart := "forgiving"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .def)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.judgment}

/-- "spare" — DOC-only. Implicit second obj def, no implicit goal. -/
def spare : Verb := .mkRegular {
  form := "spare"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill} }

/-- "deny" — DOC-only. Implicit goal def; second object obligatory
    ([bruening-2021] Table 56 row 3 col 1, ex. (32d) p. 1032). -/
def deny : Verb where
  form := "deny"
  form3sg := "denies"
  formPast := "denied"
  formPastPart := "denied"
  formPresPart := "denying"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conjecture}

/-- "permit" — DOC-only. Implicit goal def (addressee); second object
    obligatory ([bruening-2021] Table 56 row 3 col 1, ex. (32e) p. 1032). -/
def permit : Verb where
  form := "permit"
  form3sg := "permits"
  formPast := "permitted"
  formPastPart := "permitted"
  formPresPart := "permitting"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .accomplishment

/-- "assign" — alternating (DOC + PP). Implicit goal definite; the second
    object is obligatory, Pesetsky's observation as [bruening-2021] report it. -/
def assign : Verb := .mkRegular {
  form := "assign"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp, ArgumentFrame.np_pp (some Adpositions.to_),
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.futureHaving} }

-- DOC-only verbs with no implicit arguments

/-- "begrudge" — DOC-only. Neither object implicit. -/
def begrudge : Verb := .mkRegular {
  form := "begrudge"
  frames := [ArgumentFrame.np_np]
  vendlerClass := some .state }

/-- "bet" — DOC-only. Neither object implicit. -/
def bet : Verb where
  form := "bet"
  form3sg := "bets"
  formPast := "bet"
  formPastPart := "bet"
  formPresPart := "betting"
  frames := [ArgumentFrame.np_np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill}

-- Alternating verbs (both DOC and PP frame)

/-- "serve" — alternates DOC/PP. Implicit second obj indef (DOC).
    Implicit goal def (PP). -/
def serve : Verb := .mkRegular {
  form := "serve"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.implicit (some .indef), .adpositional]⟩,
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.fit, .fulfilling, .give, .masquerade} }

/-- "teach" — alternates DOC/PP. Implicit goal indef (PP).
    When both implicit, both are indefinite. -/
def teach : Verb where
  form := "teach"
  form3sg := "teaches"
  formPast := "taught"
  formPastPart := "taught"
  formPresPart := "teaching"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.implicit (some .indef), .adpositional]⟩,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩]
  vendlerClass := some .activity
  levinClasses := {LevinClass.transferOfMessage}

/-- "feed" — alternates DOC/PP. Implicit second obj indef (DOC).
    No implicit goal. -/
def feed : Verb where
  form := "feed"
  form3sg := "feeds"
  formPast := "fed"
  formPastPart := "fed"
  formPresPart := "feeding"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩]
  vendlerClass := some .activity
  levinClasses := {LevinClass.feed, .fit, .give, .gorge}

/-- "show" — alternates DOC/PP. Implicit second obj def. No implicit goal. -/
def show_ : Verb where
  form := "show"
  form3sg := "shows"
  formPast := "showed"
  formPastPart := "shown"
  formPresPart := "showing"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conjecture, .crane, .reflexiveAppearance, .transferOfMessage}

/-- "award" — alternates DOC/PP. Implicit goal def (PP). -/
def award : Verb := .mkRegular {
  form := "award"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp, ArgumentFrame.np_pp (some Adpositions.to_),
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.futureHaving} }

/-- "forward" — alternates DOC/PP. Implicit goal def (PP). -/
def forward_ : Verb := .mkRegular {
  form := "forward"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp, ArgumentFrame.np_pp (some Adpositions.to_),
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.send} }

/-- "grant" — alternates DOC/PP. Implicit goal def (PP). -/
def grant : Verb := .mkRegular {
  form := "grant"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conjecture, .futureHaving} }

/-- "offer" — alternates DOC/PP. Implicit goal def (PP). -/
def offer : Verb := .mkRegular {
  form := "offer"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.characterize, .futureHaving, .reflexiveAppearance} }

/-- "reserve" — alternates DOC/PP. Implicit goal def (PP). -/
def reserve : Verb := .mkRegular {
  form := "reserve"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp, ArgumentFrame.np_pp (some Adpositions.for_),
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.get} }

/-- "pass" — alternates DOC/PP. Implicit DO def in PP frame only. -/
def pass : Verb := .mkRegular {
  form := "pass"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.implicit (some .def), .adpositional]⟩,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ArgumentFrame.np_pp (some Adpositions.to_), ArgumentFrame.np_np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give, .marry, .send, .throw} }

-- Alternating verbs with no implicit arguments

/-- "hand" — Levin 11.1 Send verbs; alternates DOC/PP, neither argument
    implicit. -/
def hand : Verb := .mkRegular {
  form := "hand"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp, ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.send} }

/-- "lend" — alternates DOC/PP. Neither argument implicit. -/
def lend : Verb where
  form := "lend"
  form3sg := "lends"
  formPast := "lent"
  formPastPart := "lent"
  formPresPart := "lending"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp, ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

end English.Verbs
