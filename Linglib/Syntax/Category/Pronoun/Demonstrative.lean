import Linglib.Features.Deixis
import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Category.Pronoun.Capabilities

/-!
# Demonstrative pronouns — the genuinely deictic carrier
[patel-grosz-grosz-2017] [moroney-2021]

The *deictic* demonstrative pronoun (*this*/*that*, German *dieser*, Japanese *kore/sore/are*):
`DemonstrativePronoun` `extends` the general `Pronoun` with a `Features.Deixis.Feature` — the
spatial contrast (proximal/medial/distal) that makes it a demonstrative. One carrier of the
word-class-neutral `Demonstrative` capability; an adnominal demonstrative determiner (*this* book)
or pro-adverb (*here*) would be sibling carriers.

The membership criterion is the **deictic feature, not the morphological label**. This is the point
of [patel-grosz-grosz-2017]: German *der/die/das*, traditionally called "demonstrative pronouns",
are strong-article *personal* pronouns with no deixis (their footnote 1) — they are
`PersonalPronoun`s, not `DemonstrativePronoun`s (see `Studies/PatelGroszGrosz2017.lean`). The
genuine German demonstrative is *dieser*. So the PER/DEM(German) distinction is article strength
(a `Schwarz` semantic axis), *orthogonal* to demonstrativehood (a deictic axis); the type
assignment keeps them apart by construction.

## Main declarations

* `DemonstrativePronoun` — the deictic demonstrative pronoun (`extends Pronoun` + `deixis`).
* `instance : Demonstrative DemonstrativePronoun` — its deictic-contrast capability.
* `Proform` / `Bound` instances routing it through the Pronoun API.
-/

set_option autoImplicit false

/-- A deictic demonstrative pronoun: the general `Pronoun` (form + φ) plus the
    `Features.Deixis.Feature` it encodes — its proximal/medial/distal contrast (or `unspecified`
    for a distance-neutral demonstrative like German *dieser*). Carries no separate denotation here;
    its meaning is the deictic `Semantics.Definiteness.Description.demonstrative` over its restrictor. -/
structure DemonstrativePronoun extends Pronoun where
  /-- Demonstratives are UD `PronType=Dem`; the *type* fixes the morphology. -/
  pronType := some UD.PronType.Dem
  /-- The deictic feature (proximal/medial/distal, or `unspecified`). -/
  deixis : Features.Deixis.Feature
  deriving Repr, DecidableEq

/-- A demonstrative pronoun is a `Proform` (form + φ via its `Pronoun` core). -/
instance : Proform DemonstrativePronoun :=
  ⟨fun d => d.toPronoun.form, fun d => d.toPronoun.toWord.phi⟩

/-- Its binding class is the `Pronoun` core's, defaulting an undeclared shell to `.pronoun`. -/
instance : Bound DemonstrativePronoun :=
  ⟨fun d => d.toPronoun.bindingClass.getD .pronoun⟩

/-- The demonstrative pronoun is a carrier of the `Demonstrative` (deictic-contrast) capability. -/
instance : Demonstrative DemonstrativePronoun := ⟨DemonstrativePronoun.deixis⟩
