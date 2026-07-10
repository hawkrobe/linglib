import Linglib.Fragments.Greek.StandardModern.Complementizers
import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Polarity.Licensing
import Linglib.Semantics.Presupposition.Basic
import Linglib.Semantics.Composition.Tree
import Linglib.Studies.Chierchia1984

/-!
# Roussou 2010: Selecting complementizers
[roussou-2010]

Modern Greek complementizers in their dual capacity of being selected
and of selecting. *oti*, *pu*, and *an* are nominal elements merging
OUTSIDE the embedded clause (under N, as the matrix verb's internal
argument); *na* merges INSIDE the lower C domain and re-opens the EPP
position. The paper's informal semantic glosses are formalized here on
their classical anchors, each denotation carrying its distribution:

- *pu* is definite ([christidis-1986]; the factive-definite lineage of
  [kiparsky-kiparsky-1970]): `puClause` presupposes the proposition it
  locates, so factivity IS the definite's existence presupposition —
  projecting through negation (ex. 15b) where the presupposition-free
  `otiClause` is freely deniable (ex. 16).
- *an* denotes the Hamblin polar set {p, ¬p} (the paper adopts
  [adger-quer-2001]'s (6b), after [hamblin-1973b]): `anClause` is the
  inquisitive polar question — informationally inert, so some operator
  must close the open set. That polarity requirement is `anItem`, an
  NPI over the propositional domain whose licensing routes through the
  substrate's [zwarts-1998] / [van-rooy-2003-npi] table: matrix
  negation (ex. 11), question — supplied lexically by rogatives
  (ex. 10) or structurally (ex. 2c) — and incorporated-negation
  predicates ('doubt', 'forget', ex. 14). True/False predicates
  ([adger-quer-2001]; *ipothéto* 'assume', ex. 7) are veridical
  embedders: no row of the table corresponds to them, and none could —
  that absence is the account's rendering of their blocking effect.
- *na*-clauses denote properties, [chierchia-1984]'s control-complement
  layer, despite finite morphology (MG lacks infinitives): control
  (ex. 25–26) is the matrix argument saturating the open slot, and the
  outside mergers cannot embed a na-clause because they consume
  propositions — a type-level application failure.

Selection is thus not one-to-one (ex. 1–3): epistemic *pistévo* takes
*na* only with present-tense matrix inflection (ex. 23) and focus
licenses otherwise unselected *pu* (ex. 22) — both left as prose.

## Main declarations

- `PropQuant`, `MergeSite`, `CProfile`, `profile` — the lexical
  specification table (§3–4)
- `otiClause`, `puClause`, `anClause` — the three denotations;
  `puClause_factive`, `pu_projects_through_negation`,
  `puClause_strongEntails_oti`, `anClause_not_informative`
- `anItem` — *an* as `Polarity.Item`; `anItem_licensed` routes its
  distribution through `LicensingContext.licenses`
- `naLayer`, `na_layer_diverges_from_coding`, `comp_over_na_type_clash`
  — the property-layer analysis of *na*
- `factive_iff_definite` — the fragment's `factive` flag coincides
  with definite propositional quantification
-/

namespace Roussou2010

open Greek.StandardModern.Complementizers
open Semantics.Presupposition
open Semantics.Composition.Tree
open Semantics.Composition.TypeShifting

/-! ### The lexical specification (§3–4) -/

/-- Propositional quantification contributed by an outside-merging
complementizer: definite (binds a single proposition, locating it to a
reference point) vs indefinite (ranges over a set of propositions). -/
inductive PropQuant where
  | definite
  | indefinite
  deriving DecidableEq, Repr

/-- Merge site of a clause-typing element: outside the embedded clause
(under N, as the matrix verb's internal argument — *oti*, *pu*, *an*)
or inside its lower C domain (*na*, ex. 28). -/
inductive MergeSite where
  | outside
  | inside
  deriving DecidableEq, Repr

/-- The lexical specification §4 attributes to a clause-typer: merge
site, propositional quantification (`none` for inside-mergers, which
bind no propositional variable), and polarity sensitivity. -/
structure CProfile where
  site : MergeSite
  quant : Option PropQuant
  polar : Bool := false
  deriving DecidableEq, Repr

/-- The MG assignment (§3.1, §4): *oti* indefinite, *an* polar
indefinite, *pu* definite — all outside — and *na* inside with no
propositional quantification. -/
def profile (c : Complementizer) : Option CProfile :=
  if c = oti then some { site := .outside, quant := some .indefinite }
  else if c = an then
    some { site := .outside, quant := some .indefinite, polar := true }
  else if c = pu then some { site := .outside, quant := some .definite }
  else if c = na then some { site := .inside, quant := none }
  else none

/-- Definiteness is what the fragment's lexical `factive` flag records
([christidis-1986]: *pu* as the definite article of the propositional
domain). One way only: the factive doxastics (*kséro*, *katalavéno*)
take indefinite *oti* (ex. 19), with weak, deniable, verb-derived
factivity (ex. 15). -/
theorem factive_iff_definite :
    ∀ c ∈ [oti, pu, an, na],
      (c.factive = some true ↔ (profile c).bind (·.quant) = some .definite) := by
  decide

/-! ### The denotations -/

variable {W : Type*}

/-- The oti-clause: a plain indefinite over propositions —
presupposition-free assertion of its content. Any factive flavor is
verb-derived and deniable (ex. 15–16). -/
def otiClause (p : Set W) : PartialProp W :=
  { presup := fun _ => True, assertion := (· ∈ p) }

/-- The pu-clause: a definite over propositions ([christidis-1986];
[kiparsky-kiparsky-1970]'s factive-definite) — it presupposes the
proposition it locates to the reference point. -/
def puClause (p : Set W) : PartialProp W :=
  { presup := (· ∈ p), assertion := (· ∈ p) }

/-- The an-clause: the Hamblin polar set {p, ¬p} (the paper's (6b),
after [adger-quer-2001] and [hamblin-1973b]), as the inquisitive polar
question. -/
def anClause (p : Set W) : Question W := Question.polar p

/-- Factivity IS the definite's existence presupposition: the
pu-clause is defined at a world exactly when its content holds
there. -/
theorem puClause_factive (p : Set W) (w : W) :
    (puClause p).defined w ↔ w ∈ p := Iff.rfl

/-- ex. 15b: the definite's presupposition projects through internal
negation — denying a pu-clause still commits to its content — while
the oti-clause stays defined everywhere, so denial carries no factive
residue (ex. 16). -/
theorem pu_projects_through_negation (p : Set W) (w : W) :
    ((PartialProp.neg (puClause p)).defined w ↔ w ∈ p) ∧
      (PartialProp.neg (otiClause p)).defined w := by
  constructor
  · exact Iff.rfl
  · exact trivial

/-- ex. 17 (*thimáme oti/pu*): the pu-reading strong-entails the
oti-reading — Terrell's strong vs weak presupposition as
`strongEntails`. -/
theorem puClause_strongEntails_oti (p : Set W) :
    (puClause p).strongEntails (otiClause p) :=
  fun _ _ ha => ⟨trivial, ha⟩

/-- The an-clause is informationally inert: it asserts nothing, only
raising the {p, ¬p} issue. The polarity requirement is the demand that
some operator close this open set. -/
theorem anClause_not_informative (p : Set W) :
    ¬ (anClause p).isInformative :=
  Question.not_isInformative_polar p

/-! ### *an* as a polarity item (§2) -/

/-- *an* as an NPI over the propositional domain: weak licensor
requirement, with the paper's binder inventory mapped onto the
substrate's licensing rows — matrix negation (ex. 11), question,
whether supplied lexically by a rogative (ex. 10) or structurally
(ex. 2c), and incorporated-negation predicates (*amfivállo* 'doubt',
*ksexnó* 'forget', ex. 14). True/False predicates (ex. 7) are
veridical embedders: no licensing row corresponds to them, which is
the account's rendering of their blocking effect. -/
def anItem : Semantics.Polarity.Item where
  form := "an"
  baseForce := .existential
  licensor := some .weak
  licensingContexts := [.negation, .question, .doubtVerb]

/-- *an*'s polarity is a bona fide licensor requirement. -/
theorem anItem_isNPI : anItem.isNPI := by decide

/-- Each context of the inventory in fact licenses *an* under the
substrate's keystone ([zwarts-1998] strength on the signature rows,
[van-rooy-2003-npi] entropy on questions). -/
theorem anItem_licensed :
    ∀ c ∈ anItem.licensingContexts, c.licenses anItem := by
  decide

/-! ### *na* and the property layer (§3.2, §4) -/

/-- *na* re-opens the EPP position, so the na-clause denotes a
property — [chierchia-1984]'s control-complement layer — despite
finite morphology. -/
def naLayer : ComplSemLayer := .property

/-- MG detaches the property layer from nonfinite coding: the
coding-based mapping sends finite clauses to the propositional layer
(`Chierchia1984.complSemLayer`), but the finite na-clause is a
property. Control (ex. 25–26) is the matrix argument saturating the
open slot. -/
theorem na_layer_diverges_from_coding :
    naLayer = .property ∧
    Chierchia1984.complSemLayer .finiteClause = some .proposition := by
  exact ⟨rfl, rfl⟩

/-- The merge-site split cashed out at type level (p. 597): an outside
merger consumes a proposition (`.t`), while the na-clause — its EPP
re-opened — is a property, `.fn .e .t`; application is undefined
whatever the merger returns. Relative *pu* + *na* (ex. 31) escapes
because relative *pu* binds an individual variable instead. -/
theorem comp_over_na_type_clash (b : Intensional.Ty) :
    canApply (.fn .t b) (.fn .e .t) = none := rfl

end Roussou2010
