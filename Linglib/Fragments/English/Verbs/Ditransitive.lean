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
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 1, 2]),
     (⟨some .nominal, [.implicit (some .def), .nominal]⟩, [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill, .equip, .run} }

/-- "cost" — DOC-only. Implicit second obj indef, implicit goal def. -/
def cost : Verb := .mkRegular {
  form := "cost"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 1, 2]),
     (⟨some .nominal, [.implicit (some .def), .nominal]⟩, [0, 1, 2])]
  vendlerClass := some .state
  levinClasses := {LevinClass.cost} }

/-- "fine" — DOC-only. Implicit second obj indef, implicit goal def. -/
def fine : Verb := .mkRegular {
  form := "fine"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill, .judgment} }

/-- "tip" — DOC-only. Implicit second obj indef, implicit goal def (unique). -/
def tip : Verb where
  form := "tip"
  form3sg := "tips"
  formPast := "tipped"
  formPastPart := "tipped"
  formPresPart := "tipping"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 1, 2]),
     (⟨some .nominal, [.implicit (some .def), .nominal]⟩, [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill, .throw}

/-- "pay" — DOC-only. Implicit second obj indef, implicit goal def. -/
def pay : Verb where
  form := "pay"
  form3sg := "pays"
  formPast := "paid"
  formPastPart := "paid"
  formPresPart := "paying"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 1, 2]),
     (⟨some .nominal, [.implicit (some .def), .nominal]⟩, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

/-- "strike" — DOC-only. Implicit second obj indef, implicit goal def (familiar). -/
def strike_ : Verb where
  form := "strike"
  form3sg := "strikes"
  formPast := "struck"
  formPastPart := "struck"
  formPresPart := "striking"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 1, 2]),
     (⟨some .nominal, [.implicit (some .def), .nominal]⟩, [0, 1, 2])]
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
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .def)]⟩, [0, 1, 2]),
     (⟨some .nominal, [.implicit (some .def), .nominal]⟩, [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.judgment}

/-- "spare" — DOC-only. Implicit second obj def, no implicit goal. -/
def spare : Verb := .mkRegular {
  form := "spare"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .def)]⟩, [0, 1, 2])]
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
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (⟨some .nominal, [.implicit (some .def), .nominal]⟩, [0, 1, 2])]
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
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (⟨some .nominal, [.implicit (some .def), .nominal]⟩, [0, 1, 2])]
  vendlerClass := some .accomplishment

/-- "assign" — alternating (DOC + PP). Implicit goal definite; the second
    object is obligatory, Pesetsky's observation as [bruening-2021] report it. -/
def assign : Verb := .mkRegular {
  form := "assign"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1]),
     (⟨some .nominal, [.implicit (some .def), .nominal]⟩, [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.futureHaving} }

-- DOC-only verbs with no implicit arguments

/-- "begrudge" — DOC-only. Neither object implicit. -/
def begrudge : Verb := .mkRegular {
  form := "begrudge"
  valency := .ofFrame ArgumentFrame.np_np
  vendlerClass := some .state }

/-- "bet" — DOC-only. Neither object implicit. -/
def bet : Verb where
  form := "bet"
  form3sg := "bets"
  formPast := "bet"
  formPastPart := "bet"
  formPresPart := "betting"
  valency := .ofFrame ArgumentFrame.np_np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill}

-- Alternating verbs (both DOC and PP frame)

/-- "serve" — alternates DOC/PP. Implicit second obj indef (DOC).
    Implicit goal def (PP). -/
def serve : Verb := .mkRegular {
  form := "serve"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (⟨some .nominal, [.implicit (some .indef), .adpositional]⟩, [0, 2, 1]),
     (⟨some .nominal, [.nominal, .implicit (some .def)]⟩, [0, 2, 1])]
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
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (⟨some .nominal, [.implicit (some .indef), .adpositional]⟩, [0, 2, 1]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 2, 1])]
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
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 1, 2])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.feed, .fit, .give, .gorge}

/-- "show" — alternates DOC/PP. Implicit second obj def. No implicit goal. -/
def show_ : Verb where
  form := "show"
  form3sg := "shows"
  formPast := "showed"
  formPastPart := "shown"
  formPresPart := "showing"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (⟨some .nominal, [.nominal, .implicit (some .def)]⟩, [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conjecture, .crane, .reflexiveAppearance, .transferOfMessage}

/-- "award" — alternates DOC/PP. Implicit goal def (PP). -/
def award : Verb := .mkRegular {
  form := "award"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1]),
     (⟨some .nominal, [.nominal, .implicit (some .def)]⟩, [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.futureHaving} }

/-- "forward" — alternates DOC/PP. Implicit goal def (PP). -/
def forward_ : Verb := .mkRegular {
  form := "forward"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1]),
     (⟨some .nominal, [.nominal, .implicit (some .def)]⟩, [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.send} }

/-- "grant" — alternates DOC/PP. Implicit goal def (PP). -/
def grant : Verb := .mkRegular {
  form := "grant"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (⟨some .nominal, [.nominal, .implicit (some .def)]⟩, [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conjecture, .futureHaving} }

/-- "offer" — alternates DOC/PP. Implicit goal def (PP). -/
def offer : Verb := .mkRegular {
  form := "offer"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (⟨some .nominal, [.nominal, .implicit (some .def)]⟩, [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.characterize, .futureHaving, .reflexiveAppearance} }

/-- "reserve" — alternates DOC/PP. Implicit goal def (PP). -/
def reserve : Verb := .mkRegular {
  form := "reserve"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_), [0, 2, 1]),
     (⟨some .nominal, [.nominal, .implicit (some .def)]⟩, [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.get} }

/-- "pass" — alternates DOC/PP. Implicit DO def in PP frame only. -/
def pass : Verb := .mkRegular {
  form := "pass"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp, [0, 1, 2]),
     (⟨some .nominal, [.implicit (some .def), .adpositional]⟩, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give, .marry, .send, .throw} }

-- Alternating verbs with no implicit arguments

/-- "hand" — Levin 11.1 Send verbs; alternates DOC/PP, neither argument
    implicit. -/
def hand : Verb := .mkRegular {
  form := "hand"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.send} }

/-- "mail" — transitive, ditransitive, or with a *to*-phrase (*Paul mailed a letter*). -/
def mail : Verb := .mkRegular {
  form := "mail"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2])]
  levinClasses := {LevinClass.send} }

/-- "lend" — alternates DOC/PP. Neither argument implicit. -/
def lend : Verb where
  form := "lend"
  form3sg := "lends"
  formPast := "lent"
  formPastPart := "lent"
  formPresPart := "lending"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

end English.Verbs
