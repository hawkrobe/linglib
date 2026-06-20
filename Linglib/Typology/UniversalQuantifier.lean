import Mathlib.Data.List.Basic

/-!
# DP-internal universal-quantifier typology

[haslinger-etal-2025-nllt]

Per-language substrate for the cross-linguistic survey of DP-internal
universal quantifiers (UQs) in [haslinger-etal-2025-nllt]. The paper's central
typological split is between

* **1-form languages** — a single UQ lexeme whose interpretation is fixed by
  the *number* of its complement: distributive ([+dist]) with a singular count
  complement, non-distributive ([−dist]) with a plural complement (Table 2:
  Dagara, Moore, Gourmantchema, Wolof, Syrian Arabic); and
* **2-form languages** — distinct [+dist] and [−dist] UQ lexemes (Table 1:
  English, German, Hindi, Russian, Imbabura Quichua, Turkish, Basque, Telugu,
  Hausa, Logoori).

This file gives the Fragment-importable record (`UQProfile`) that each language
instantiates in `Fragments/{Language}/UniversalQuantifier.lean`. Cross-linguistic
theorems over the assembled sample live in the paper's study file
(`Studies/HaslingerHienEtAl2025.lean`), not here — `Typology/` never imports
`Fragments/`.

The forms are the surface UQ exponents the survey reports; the `source` field
records the data provenance the survey attributes them to (its Table 1 "source"
column and elicitation footnotes).
-/

namespace Typology.UniversalQuantifier

/-- Whether a language lexicalizes one universal quantifier whose reading is
fixed by complement number (`oneForm`), or two distinct [+dist]/[−dist] forms
(`twoForm`). [haslinger-etal-2025-nllt] -/
inductive SystemType where
  /-- Single UQ lexeme; reading determined by complement number. -/
  | oneForm
  /-- Distinct [+dist] and [−dist] UQ lexemes. -/
  | twoForm
  deriving DecidableEq, Repr

/-- A language's DP-internal universal-quantifier inventory, as compiled in
[haslinger-etal-2025-nllt] (Table 1 for 2-form languages, Table 2 for 1-form
languages). -/
structure UQProfile where
  /-- Language name. -/
  language : String
  /-- Genealogical family (the survey's label). -/
  family : String
  /-- 1-form vs 2-form classification. -/
  systemType : SystemType
  /-- The [+dist] exponent; in 1-form languages, the sole UQ exponent. -/
  distForm : String
  /-- The [−dist] exponent; empty in 1-form languages, where the same lexeme
      yields [−dist] under a plural complement. -/
  nonDistForm : String := ""
  /-- Data provenance the survey attributes the row to. -/
  source : String := ""
  deriving Repr, DecidableEq

namespace UQProfile

/-- A 1-form language: one UQ lexeme, reading fixed by complement number. -/
def isOneForm (p : UQProfile) : Prop := p.systemType = .oneForm

/-- A 2-form language: distinct [+dist]/[−dist] UQ lexemes. -/
def isTwoForm (p : UQProfile) : Prop := p.systemType = .twoForm

instance (p : UQProfile) : Decidable p.isOneForm := by
  unfold isOneForm; infer_instance

instance (p : UQProfile) : Decidable p.isTwoForm := by
  unfold isTwoForm; infer_instance

end UQProfile

end Typology.UniversalQuantifier
