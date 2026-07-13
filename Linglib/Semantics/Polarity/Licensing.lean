/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Entailment.NaturalLogic
import Linglib.Features.LicensingContext
import Linglib.Features.Indefinite
import Linglib.Semantics.Polarity.Item

/-!
# Polarity licensing
[ladusaw-1979] [kadmon-landman-1993] [zwarts-1998] [von-fintel-1999]
[van-rooy-2003-npi] [hoeksema-1983] [bhatt-pancheva-2004] [heim-2006]
[iatridou-2000] [dayal-1996] [horn-1996] [vanderwouden-1997]

The monotonicity-based licensing theory for `Polarity.Item`:
`contextProperties` assigns every `LicensingContext` its Strawson and
classical entailment signatures, its [kadmon-landman-1993] licensing
mechanism, and its citation lineage; `StrengthScale` is the polymorphic
item↔context strength pattern with `zwartsScale` as its canonical
instance; and the keystone `LicensingContext.licenses` dispatches on the
row's mechanism — Zwarts strength on signature rows, free choice on
generic-indefinite rows ([dayal-1996]), entropy on questions
([van-rooy-2003-npi]). Per-paper classifiers (`Ladusaw1979`,
`KadmonLandman1993`) project from `contextProperties` rather than
parallel-stipulating; the grounded grade — deriving the signatures from
the model witnesses of `Witnesses.lean` via the Kadmon–Landman
strengthening chain — is the planned next step.

## Main declarations

* `LicensingMechanism`, `ContextProperties`, `contextProperties` — the
  per-context theory table.
* `StrengthScale`, `zwartsScale` — polymorphic strength licensing.
* `LicensingContext.licenses` — the item↔context licensing keystone.
* `IsStrawsonOnly` and the Haspelmath-map grounding theorems.

## Implementation notes

The table's signatures are Ladusaw/Zwarts/von-Fintel canonical — one row
per context regardless of item; [israel-2001]'s scalar model rejects
exactly this framing (predictions in `Semantics/Polarity/Israel.lean`).
The NP-comparative row licenses nothing ([hoeksema-1983]); surface NPIs
in "than NP" route through the clausal row ([bhatt-pancheva-2004],
[heim-2006]). The every-restrictor-as-LAA signature is standard but of
contested attribution (Zwarts 1981 / van Benthem 1986 / Sánchez Valencia
1991; none in `references.bib`).
-/

namespace Semantics.Polarity.Licensing

open Features (LicensingContext)

/-! ### Licensing Mechanism (refined 5-way) -/

/-- The mechanism by which a context licenses NPIs.

    [kadmon-landman-1993] unify NPI licensing under domain widening +
    strengthening. The substrate refines K&L's original 3-way classification
    into 5 substantively distinct cases.

    - `byStrengthening` — DE contexts where widening strengthens the assertion.
      Covers [ladusaw-1979]'s monotonicity-based licensing.
    - `byGenericIndefinite` — Non-DE contexts (modals, generics, free relatives)
      where *any* surfaces as the generic indefinite (FC any).
    - `byStrawsonDE` — Strawson-DE licensing (superlatives per
      Herdan & Sharvit's superlative-NPI work [UNVERIFIED — bib entry
      missing] and [von-fintel-1999]).
    - `byEntropy` — Entropy-based licensing (questions per [van-rooy-2003-npi]).
    - `strengtheningFails` — contexts that *don't* license despite surface
      appearance (e.g., NP-comparatives that lack covert clausal structure).
      Used by study files (e.g., `KadmonLandman1993.lean`) for ungrammatical
      examples, replacing the earlier `byOtherMechanism` constructor. -/
inductive LicensingMechanism where
  | byStrengthening
  | byGenericIndefinite
  | byStrawsonDE
  | byEntropy
  | strengtheningFails
  deriving DecidableEq, Repr

/-! ### Context Properties (single source of truth) -/

/-- The bundle of theory-relevant facts about a licensing context.

    Every classification of `LicensingContext` (DE strength, K&L mechanism,
    canonical example, citation lineage) projects out of this single record.
    Per-paper classifiers (`Ladusaw1979.licensingStrength`,
    `KadmonLandman1993.klExplanation`) are derivations from `contextProperties`,
    not parallel stipulations. -/
structure ContextProperties where
  /-- Icard signature modulo presuppositions ([von-fintel-1999]'s
      Strawson reading): the row a Strawson-relativized soundness
      statement (`EntailmentSig.StrawsonSoundFor`) realizes. Coincides
      with the classical row for presupposition-free contexts. -/
  strawsonSignature : NaturalLogic.EntailmentSig
  /-- K&L mechanism: how this context licenses NPIs. -/
  mechanism : LicensingMechanism
  /-- A canonical English example. -/
  prototype : String
  /-- BibTeX keys for the works that established this classification. -/
  citations : List String
  /-- Classical (presupposition-free) signature row, when one holds.
      `none` for the contexts [von-fintel-1999] showed to be only
      Strawson-DE — only-focus, adversatives, temporal *since*,
      superlatives: no `EntailmentSig` row is classically sound for
      them. Defaults to the Strawson row (the presupposition-free
      case). -/
  classicalSignature : Option NaturalLogic.EntailmentSig :=
    some strawsonSignature
  deriving Repr

/-- Canonical map from licensing contexts to their theoretical properties.

    UNVERIFIED: The "every-restrictor is LAA" result is variously
    attributed to Zwarts 1981 / van Benthem 1986 / Sánchez Valencia 1991;
    none currently in `references.bib`. The substrate uses the standard
    `.antiAdd` signature for `.universalRestrictor` without committing
    to a specific source. -/
def contextProperties : LicensingContext → ContextProperties
  | .negation =>
      { strawsonSignature := .antiAddMult, mechanism := .byStrengthening
      , prototype := "Mary didn't see anyone."
      , citations := ["ladusaw-1979", "kadmon-landman-1993", "zwarts-1998"] }
  | .nobody =>
      { strawsonSignature := .antiAdd, mechanism := .byStrengthening
      , prototype := "Nobody saw anyone."
      , citations := ["ladusaw-1979", "zwarts-1998"] }
  | .withoutClause =>
      { strawsonSignature := .antiAdd, mechanism := .byStrengthening
      , prototype := "She left without saying anything."
      , citations := ["ladusaw-1979", "zwarts-1998"] }
  | .denyVerb =>
      { strawsonSignature := .antiAdd, mechanism := .byStrengthening
      , prototype := "She denied seeing anyone."
      , citations := ["zwarts-1998"] }
  | .universalRestrictor =>
      { strawsonSignature := .antiAdd, mechanism := .byStrengthening
      , prototype := "Everyone who saw anyone was questioned."
      , citations := ["ladusaw-1979", "UNVERIFIED-bib-missing:partee-westerstaahl"] }
  | .few =>
      { strawsonSignature := .anti, mechanism := .byStrengthening
      , prototype := "Few students saw anyone."
      , citations := ["ladusaw-1979"] }
  | .atMost =>
      { strawsonSignature := .anti, mechanism := .byStrengthening
      , prototype := "At most three students saw anyone."
      , citations := ["ladusaw-1979"] }
  | .conditionalAntecedent =>
      { strawsonSignature := .anti, mechanism := .byStrengthening
      , prototype := "If anyone calls, take a message."
      , citations := ["ladusaw-1979", "kadmon-landman-1993"] }
  | .beforeClause =>
      { strawsonSignature := .anti, mechanism := .byStrengthening
      , prototype := "She left before anyone arrived."
      , citations := ["ladusaw-1979"] }
  | .onlyFocus =>
      { strawsonSignature := .anti, mechanism := .byStrengthening
      , prototype := "Only Mary saw anyone."
      , citations := ["horn-1996", "von-fintel-1999"]
      , classicalSignature := none }
  | .tooTo =>
      { strawsonSignature := .anti, mechanism := .byStrengthening
      , prototype := "He was too tired to say anything."
      , citations := ["ladusaw-1979"] }
  | .comparativeNP =>
      -- [hoeksema-1983]: the NP-comparative is a Boolean
      -- homomorphism `Set (Set U) → Set U`, hence monotone increasing — it
      -- does *not* license NPIs. Modern interval-semantic accounts
      -- ([bhatt-pancheva-2004], [heim-2006]) reduce surface
      -- "than NP" with NPI to a covert clausal source — those NPIs are
      -- licensed by `.comparativeS`, not by this slot.
      { strawsonSignature := .mono, mechanism := .strengtheningFails
      , prototype := "Surface NP-comparative; no NPI licensing under genuine NP reading."
      , citations := ["hoeksema-1983", "bhatt-pancheva-2004", "heim-2006"] }
  | .comparativeS =>
      { strawsonSignature := .antiAdd, mechanism := .byStrengthening
      , prototype := "Mary is taller than anyone is."
      , citations := ["ladusaw-1979", "hoeksema-1983", "bhatt-pancheva-2004"] }
  | .adversative =>
      { strawsonSignature := .anti, mechanism := .byStrengthening
      , prototype := "I'm sorry I said anything."
      , citations := ["kadmon-landman-1993", "von-fintel-1999"]
      , classicalSignature := none }
  | .sinceTemporal =>
      { strawsonSignature := .anti, mechanism := .byStrengthening
      , prototype := "It's been five years since anyone visited."
      , citations := ["iatridou-2000", "von-fintel-1999"]
      , classicalSignature := none }
  | .doubtVerb =>
      { strawsonSignature := .anti, mechanism := .byStrengthening
      , prototype := "I doubt anyone came."
      , citations := ["zwarts-1998"] }
  | .modalPossibility =>
      { strawsonSignature := .mono, mechanism := .byGenericIndefinite
      , prototype := "You may take any cookie."
      , citations := ["kadmon-landman-1993", "dayal-1996"] }
  | .modalNecessity =>
      { strawsonSignature := .mono, mechanism := .byGenericIndefinite
      , prototype := "Anyone can solve this."
      , citations := ["dayal-1996"] }
  | .imperative =>
      { strawsonSignature := .mono, mechanism := .byGenericIndefinite
      , prototype := "Pick any card."
      , citations := ["kadmon-landman-1993"] }
  | .generic =>
      { strawsonSignature := .mono, mechanism := .byGenericIndefinite
      , prototype := "Any owl hunts mice."
      , citations := ["kadmon-landman-1993", "dayal-1996"] }
  | .freeRelative =>
      { strawsonSignature := .mono, mechanism := .byGenericIndefinite
      , prototype := "Pick whichever you like."
      , citations := ["dayal-1996"] }
  | .question =>
      { strawsonSignature := .mono, mechanism := .byEntropy
      , prototype := "Did anyone call?"
      , citations := ["van-rooy-2003-npi"] }
  | .superlative =>
      -- Strawson row `.anti` per [von-fintel-1999]
      -- (`superlative_isStrawsonDE`); previously a `.mono` placeholder.
      { strawsonSignature := .anti, mechanism := .byStrawsonDE
      , prototype := "The tallest student who saw anyone..."
      , citations := ["UNVERIFIED-bib-missing:herdan-sharvit", "von-fintel-1999"]
      , classicalSignature := none }

/-! ### Strength scales

A theory of NPI strength is an *ordered carrier* `S` plus how items and
contexts project onto it, with licensing = `≤` on `S`. Different theories of
strength (Gajewski plain-vs-exhaustified, Giannakidou veridicality, gradient)
instantiate different carriers. -/

/-- A **strength scale** for NPI licensing: how items and contexts project onto
an ordered strength carrier `S`. `none` on either side = "no strength here" (the
item licenses via another mechanism, or the context supplies none). -/
structure StrengthScale (Item Context S : Type*) [Preorder S] where
  /-- The strength an item requires (`none` = not strength-licensed). -/
  required : Item → Option S
  /-- The strength a context supplies (`none` = supplies no strength). -/
  supplied : Context → Option S

/-- Licensing on a scale: the context supplies at least the strength the item
requires (both sides present). -/
def StrengthScale.licenses {Item Context S : Type*} [Preorder S]
    (L : StrengthScale Item Context S) (i : Item) (c : Context) : Prop :=
  ∃ r ∈ L.required i, ∃ s ∈ L.supplied c, r ≤ s

instance {Item Context S : Type*} [Preorder S]
    [DecidableRel (α := S) (· ≤ ·)] (L : StrengthScale Item Context S)
    (i : Item) (c : Context) : Decidable (L.licenses i c) := by
  unfold StrengthScale.licenses; infer_instance

/-- The canonical Zwarts scale ([ladusaw-1979], [zwarts-1998],
[gajewski-2011]): carrier `DEStrength`, item strength from `Item.licensor`,
context strength from the row's Strawson signature. -/
def zwartsScale :
    StrengthScale Semantics.Polarity.Item LicensingContext
      NaturalLogic.DEStrength where
  required e := e.licensor
  supplied c := (contextProperties c).strawsonSignature.toDEStrength

/-! ### The licensing keystone -/

/-- The item↔context licensing relation (stipulated grade), read
context-side: `c.licenses e` says environment `c` licenses item `e`.
Dispatched on the row's `LicensingMechanism`:

- signature rows (`byStrengthening`, `byStrawsonDE`): Zwarts-strength
  licensing — the row's Strawson signature supplies at least `e.licensor`
  (n-words require anti-morphic strength, so clausal negation is the only
  qualifying row);
- `byGenericIndefinite` rows license free choice items;
- `byEntropy` rows (questions, [van-rooy-2003-npi]) license weak NPIs;
- `strengtheningFails` rows license nothing.

The grounded grade — deriving the signature side from the context
witnesses of `Witnesses.lean` via the Kadmon–Landman strengthening
chain — is planned (N1 of the NPI-API sweep). -/
def _root_.Features.LicensingContext.licenses (c : LicensingContext)
    (e : Semantics.Polarity.Item) : Prop :=
  match (contextProperties c).mechanism with
  | .byStrengthening | .byStrawsonDE => zwartsScale.licenses e c
  | .byGenericIndefinite => e.isFCI
  | .byEntropy => e.licensor = some .weak
  | .strengtheningFails => False

instance (c : LicensingContext) (e : Semantics.Polarity.Item) :
    Decidable (c.licenses e) := by
  unfold Features.LicensingContext.licenses; split <;> infer_instance

/-! ### The Haspelmath map meets the licensing table

`Features.LicensingContext.haspelmathFunction` (in `Features/Indefinite.lean`)
classifies each licensing environment by the [haspelmath-1997] map function it
realizes. The theorems here ground the map's stipulated polarity-side
classifiers (`HaspelmathFunction.isDE`/`isFC`) in `contextProperties`. -/

/-- [haspelmath-1997]'s free-choice region coincides exactly with the
[kadmon-landman-1993] generic-indefinite mechanism class: a context realizes
the `freeChoice` function iff its licensing mechanism is
`byGenericIndefinite`. -/
theorem haspelmathFunction_freeChoice_iff_genericIndefinite
    (c : LicensingContext) :
    c.haspelmathFunction = some .freeChoice ↔
      (contextProperties c).mechanism = .byGenericIndefinite := by
  cases c <;> decide

/-- Every context realizing an NPI-region function (`HaspelmathFunction.isDE`:
question through direct negation) either supplies Zwarts strength or is the
entropy row — the map's classical NPI region is weak-NPI-licensable, though
not uniformly DE (questions license by entropy, [van-rooy-2003-npi]). -/
theorem haspelmathFunction_npi_region_licensable (c : LicensingContext)
    (f : Indefinite.HaspelmathFunction) (hf : c.haspelmathFunction = some f)
    (hDE : f.isDE = true) :
    (contextProperties c).strawsonSignature.toDEStrength.isSome ∨
      (contextProperties c).mechanism = .byEntropy := by
  revert hf hDE; cases c <;> cases f <;> decide

/-- A context is **Strawson-only** when no classical signature row holds
([von-fintel-1999]): only-focus, adversatives, temporal *since*,
superlatives. -/
def IsStrawsonOnly (c : LicensingContext) : Prop :=
  (contextProperties c).classicalSignature = none

/-- When a classical row exists it coincides with the Strawson row:
presupposition-free contexts carry a single signature. -/
theorem classicalSignature_eq_strawson (c : LicensingContext) :
    (contextProperties c).classicalSignature = none ∨
    (contextProperties c).classicalSignature =
      some (contextProperties c).strawsonSignature := by
  cases c <;> decide

end Semantics.Polarity.Licensing
