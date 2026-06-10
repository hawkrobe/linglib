import Mathlib.Tactic.DeriveFintype

/-!
# Root Arity

[coon-2019]: the central division of labor in Mayan root typology is
that **roots determine internal arguments** while **functional heads
(v/Voice⁰) determine external arguments**. Root arity — whether a root
obligatorily projects a theme — is orthogonal to change entailment and
to the B&K-G feature signature, and is the dimension behind the Mayan
"root transitive" class: [coon-2019]'s √TV for Chuj, [lucy-1994]'s
agent-patient salient (`=∅`) class for Yucatec ("these roots require
two arguments and refer to events involving the action of one entity
on another").

Arity captures complement *projection*, not semantic type: an
unaccusative's sole argument is semantically theme-like, but the root
does not project it as a complement.

## Main declarations

* `Root.Arity` — `selectsTheme` (√TV) vs `noTheme`
-/

/-- Root-level argument selection ([coon-2019]): does the root
    obligatorily take an internal (theme) argument? `selectsTheme` is
    Coon's √TV — the Mayan root-transitive class; `noTheme` covers
    √ITV, √NOM, √POS. -/
inductive Root.Arity where
  | selectsTheme
  | noTheme
  deriving DecidableEq, Fintype, Repr

/-- Does this root arity entail an obligatory internal argument? -/
def Root.Arity.hasInternalArg : Root.Arity → Bool
  | .selectsTheme => true
  | .noTheme => false
