/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Basic
public import Linglib.Semantics.Polarity.Item
public import Linglib.Semantics.Quantification.Indefinite

/-!
# Polarity licensing

The licensing theory of `PolarityItem`. Each `LicensingContext` imposes an entailment signature
on the position of a polarity item, read modulo presuppositions (`LicensingContext.signature`),
and so carries a strength of negation (`LicensingContext.strength`, `⊥` where the context is not
downward entailing). Five contexts carry their strength only modulo their presupposition, von
Fintel's focus *only*, temporal *since*, adversatives, conditional antecedents and superlatives;
they are `LicensingContext.IsStrawsonOnly`.

Following Ladusaw and von Fintel, a context licenses a weak negative polarity item when it is
downward entailing modulo presuppositions. Following Zwarts and Gajewski, a stronger item needs
its strength of negation outright, which the Strawson-only contexts lack although all five are
Strawson anti-additive. A context blocks a positive polarity item when its strength outright
reaches the item's anti-licensor, as van der Wouden and Szabolcsi describe. The generic contexts
license free choice items, after Kadmon and Landman and Dayal, and questions license the weak
negative polarity items, after van Rooy. `LicensingContext.Admits` puts the routes together into
the distribution the theory predicts, which each fragment checks against the contexts its entries
are attested and excluded in.

## Main declarations

* `PolarityItem.LicensingContext.signature`, `LicensingContext.strength`,
  `LicensingContext.IsStrawsonOnly`, `LicensingContext.mechanism`: the theory of each context.
* `LicensingContext.Licenses`, `LicensingContext.AntiLicenses`, `LicensingContext.Admits`.

## Main results

* `LicensingContext.strength_eq_antiMorphic_iff`: clausal negation is the only anti-morphic
  context, so an item needing anti-morphic strength is licensed by it alone
  (`LicensingContext.licenses_iff_eq_negation`).
* `LicensingContext.not_licenses_of_isStrawsonOnly`: a Strawson-only context licenses no item
  stronger than weak ([gajewski-2011]).
* `LicensingContext.antiLicenses_negation`: clausal negation blocks every positive polarity item,
  [vanderwouden-1997]'s (169).
* `LicensingContext.antiLicenses_iff_licenses`: a context blocks the positive polarity items of a
  class exactly where it licenses the negative polarity items of that class, the mirror image of
  [vanderwouden-1997]'s (181).
* `LicensingContext.Licenses.of_licensor_le`: a context licensing an item licenses every item with
  a weaker licensor.

## Implementation notes

The signature of each context is the canonical one of the Ladusaw–Zwarts tradition, one row per
context whatever the item; [israel-2001]'s scalar model rejects this framing (see
`Studies/Israel2001.lean`). `Semantics/Polarity/Witnesses.lean` realizes the rows by model
operators. The phrasal comparative is monotone and licenses nothing ([hoeksema-1983]); a surface
*than NP* hosting a polarity item reduces to a clausal source and is listed under the clausal
comparative ([bhatt-pancheva-2004], [heim-2006]). The anti-additive signature of the restrictor of
a universal is standard, but its attribution is unsettled. Gajewski's condition on strong items
concerns the meaning enriched with presupposition and implicature; the licensing relation reads
the presupposition half, as the Strawson-only contexts, and the *few* and *at most* rows fall short
of anti-additivity outright.

## References

* [ladusaw-1979]
* [kadmon-landman-1993]
* [zwarts-1998]
* [vanderwouden-1997]
* [von-fintel-1999]
* [gajewski-2011]
* [szabolcsi-2004]
* [van-rooy-2003-npi]
* [dayal-1996]
* [hoeksema-1983]
* [bhatt-pancheva-2004]
* [heim-2006]
* [israel-2001]
* [haspelmath-1997]
-/

@[expose] public section

namespace PolarityItem

open NaturalLogic

/-- A context licenses polarity items by strengthening, the downward-entailing route of
[kadmon-landman-1993], as a generic context, which licenses free choice items
([kadmon-landman-1993], [dayal-1996]), or by the entropy of a question ([van-rooy-2003-npi]). -/
inductive LicensingMechanism where
  | strengthening
  | genericIndefinite
  | entropy
  deriving DecidableEq, Repr

namespace LicensingContext

/-- The entailment signature a context imposes on the position of a polarity item, read modulo
presuppositions ([von-fintel-1999]). Clausal negation is anti-morphic; the negative quantifiers,
*without*, *deny*, the restrictor of a universal and the clausal comparative are anti-additive
([ladusaw-1979], [zwarts-1998]), and so, modulo presuppositions, are focus *only*, adversatives,
conditional antecedents, superlatives ([gajewski-2011]) and temporal *since*
(`NaturalLogic.isStrawsonAntiAdditive_since`); *few*, *at most*, *before*, *too … to* and *doubt*
are antitone; the phrasal comparative, questions and the generic contexts are monotone. -/
def signature : LicensingContext → Signature
  | .negation => .antiAddMult
  | .nobody | .withoutClause | .denyVerb | .universalRestrictor | .clausalComparative
  | .onlyFocus | .adversative | .conditionalAntecedent | .superlative | .sinceTemporal => .antiAdd
  | .few | .atMost | .beforeClause | .tooTo | .doubtVerb => .anti
  | .phrasalComparative | .question | .modalPossibility | .modalNecessity | .imperative
  | .generic | .freeRelative => .mono

/-- The strength of negation of a context modulo presuppositions, `⊥` when it is not downward
entailing. -/
def strength (c : LicensingContext) : WithBot DEStrength := c.signature.toDEStrength

/-- A context is **Strawson-only** when its strength holds only modulo its presupposition, as for
focus *only*, temporal *since*, adversatives, conditional antecedents and superlatives
([von-fintel-1999]). -/
def IsStrawsonOnly : LicensingContext → Prop
  | .onlyFocus | .sinceTemporal | .adversative | .conditionalAntecedent | .superlative => True
  | .negation | .nobody | .few | .atMost | .beforeClause | .withoutClause | .question
  | .phrasalComparative | .clausalComparative | .tooTo | .modalPossibility | .modalNecessity
  | .imperative | .generic | .freeRelative | .universalRestrictor | .doubtVerb | .denyVerb => False

instance : DecidablePred IsStrawsonOnly
  | .onlyFocus | .sinceTemporal | .adversative | .conditionalAntecedent | .superlative =>
      isTrue trivial
  | .negation | .nobody | .few | .atMost | .beforeClause | .withoutClause | .question
  | .phrasalComparative | .clausalComparative | .tooTo | .modalPossibility | .modalNecessity
  | .imperative | .generic | .freeRelative | .universalRestrictor | .doubtVerb | .denyVerb =>
      isFalse id

/-- The route by which a context licenses polarity items. -/
def mechanism : LicensingContext → LicensingMechanism
  | .modalPossibility | .modalNecessity | .imperative | .generic | .freeRelative =>
      .genericIndefinite
  | .question => .entropy
  | _ => .strengthening

/-- A context **licenses** an item by strengthening when its strength reaches the item's licensor
and, for an item stronger than weak, holds outright; as a generic context when the item is a free
choice item; or as a question when the item is a weak negative polarity item. -/
def Licenses (c : LicensingContext) (e : PolarityItem) : Prop :=
  (c.mechanism = .strengthening ∧
      ∃ r ∈ e.licensor, (r : WithBot DEStrength) ≤ c.strength ∧ (r = .weak ∨ ¬ c.IsStrawsonOnly)) ∨
    (c.mechanism = .genericIndefinite ∧ e.IsFCI) ∨
    (c.mechanism = .entropy ∧ e.licensor = some .weak)

instance (c : LicensingContext) (e : PolarityItem) : Decidable (c.Licenses e) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- A context **anti-licenses** an item when its strength holds outright and reaches the item's
anti-licensor. -/
def AntiLicenses (c : LicensingContext) (e : PolarityItem) : Prop :=
  ∃ r ∈ e.antiLicensor, (r : WithBot DEStrength) ≤ c.strength ∧ ¬ c.IsStrawsonOnly

instance (c : LicensingContext) (e : PolarityItem) : Decidable (c.AntiLicenses e) :=
  inferInstanceAs (Decidable (∃ r ∈ e.antiLicensor, _))

/-- A context **admits** an item when it licenses the item, if the item needs licensing, and
does not anti-license it. -/
def Admits (c : LicensingContext) (e : PolarityItem) : Prop :=
  (e.IsNPI ∨ e.IsFCI → c.Licenses e) ∧ ¬ c.AntiLicenses e

instance (c : LicensingContext) (e : PolarityItem) : Decidable (c.Admits e) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {c : LicensingContext} {e e' : PolarityItem}

theorem admits_iff_licenses (h : e.antiLicensor = none) (he : e.IsNPI ∨ e.IsFCI) :
    c.Admits e ↔ c.Licenses e := by
  simp [Admits, AntiLicenses, h, he]

theorem admits_iff_not_antiLicenses (hn : ¬ e.IsNPI) (hf : ¬ e.IsFCI) :
    c.Admits e ↔ ¬ c.AntiLicenses e := by
  simp [Admits, hn, hf]

/-- Clausal negation is the only anti-morphic context. -/
theorem strength_eq_antiMorphic_iff (c : LicensingContext) :
    c.strength = DEStrength.antiMorphic ↔ c = .negation := by
  cases c <;> decide

/-- An item that needs anti-morphic strength and is not a free choice item is licensed by clausal
negation alone. -/
theorem licenses_iff_eq_negation (h : e.licensor = some .antiMorphic) (hf : ¬ e.IsFCI)
    (c : LicensingContext) : c.Licenses e ↔ c = .negation := by
  cases c <;> simp [Licenses, mechanism, h, hf] <;> decide

/-- A Strawson-only context licenses no item stronger than weak that is not a free choice item.
*Only*, adversatives and conditional antecedents are Strawson anti-additive, yet license no strong
negative polarity item ([gajewski-2011]). -/
theorem not_licenses_of_isStrawsonOnly (hc : c.IsStrawsonOnly) (h : ∀ r ∈ e.licensor, r ≠ .weak) :
    ¬ c.Licenses e := by
  rintro (⟨-, r, hr, -, hw | hs⟩ | ⟨hm, -⟩ | ⟨hm, -⟩)
  · exact h r hr hw
  · exact hs hc
  all_goals cases c <;> first | exact absurd hc id | exact absurd hm (by decide)

/-- Clausal negation blocks every positive polarity item, since its strength is the top of the
chain ([vanderwouden-1997]'s (169)). -/
theorem antiLicenses_negation (h : e.IsPPI) : LicensingContext.negation.AntiLicenses e := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
  exact ⟨r, hr, WithBot.coe_le_coe.mpr (by cases r <;> decide), id⟩

/-- A context that licenses by strengthening outright blocks the positive polarity items of a
class exactly where it licenses the negative polarity items of that class ([vanderwouden-1997]'s
(181)). -/
theorem antiLicenses_iff_licenses (h : e.antiLicensor = e'.licensor)
    (hc : c.mechanism = .strengthening) (hs : ¬ c.IsStrawsonOnly) :
    c.AntiLicenses e ↔ c.Licenses e' := by
  simp [AntiLicenses, Licenses, hc, hs, h]

/-- A context licensing an item licenses every item with a weaker licensor that is a free choice
item if the first is. -/
theorem Licenses.of_licensor_le {r r' : DEStrength} (he : e.licensor = some r)
    (he' : e'.licensor = some r') (hr : r' ≤ r) (hf : e.IsFCI → e'.IsFCI) (hl : c.Licenses e) :
    c.Licenses e' := by
  have hweak : ∀ s : DEStrength, s ≤ .weak → s = .weak := by decide
  rcases hl with ⟨hc, s, hs, hle, hsw⟩ | ⟨hc, hfc⟩ | ⟨hc, hw⟩
  · rw [he, Option.mem_some_iff] at hs
    subst hs
    refine .inl ⟨hc, r', he', (WithBot.coe_le_coe.mpr hr).trans hle, hsw.imp (fun h ↦ ?_) id⟩
    subst h
    exact hweak r' hr
  · exact .inr (.inl ⟨hc, hf hfc⟩)
  · rw [he, Option.some_inj] at hw
    subst hw
    exact .inr (.inr ⟨hc, by rw [he', hweak r' hr]⟩)

end LicensingContext

/-! ### The implicational map meets the licensing table

`LicensingContext.haspelmathFunction` (`Semantics/Quantification/Indefinite.lean`) classifies
each context by the function of [haspelmath-1997]'s map it realizes. -/

/-- The free-choice function of the map is exactly the generic mechanism. -/
theorem haspelmathFunction_eq_freeChoice_iff (c : LicensingContext) :
    c.haspelmathFunction = some .freeChoice ↔ c.mechanism = .genericIndefinite := by
  cases c <;> decide

/-- Every context realizing a function of the map's negative-polarity region, question through
direct negation, is downward entailing or a question, so the region is licensable by weak
negative polarity items, though not uniformly downward entailing ([van-rooy-2003-npi]). -/
theorem haspelmathFunction_npi_region (c : LicensingContext) {f : Indefinite.HaspelmathFunction}
    (hf : c.haspelmathFunction = some f) (hr : f ∈ Indefinite.npiRegion) :
    c.strength ≠ ⊥ ∨ c.mechanism = .entropy := by
  revert hf hr; cases c <;> cases f <;> decide

end PolarityItem
