import Linglib.Features.LicensingContext
import Linglib.Features.NegativeConcord
import Linglib.Semantics.NaturalLogic

/-!
# Polarity items: NPI/PPI typology
[lahiri-1998] [haspelmath-1997]
[chierchia-2006] [israel-1996] [israel-2001]
[israel-2011] [schwab-2022]

(Lee & Horn 1994 MS *any* as indefinite + EVEN cited in §6 below;
not currently in `references.bib`.)

Per-language typological substrate for polarity-sensitive items: the
PolarityItemEntry record schema used by Fragment files, the **Israel
scalar model** machinery (ScalarValue × ScalarDirection × Canonicity ×
LikelihoodEffect), morphological-composition typology, and the
canonicity-prediction function `predictCanonicity`.

## Provenance

Split from `Core/Lexical/PolarityItem.lean` in the cleanup that
dissolved `Core/Lexical/`. The companion file
`Semantics/Polarity/Licensing.lean` holds the
monotonicity-based licensing infrastructure (LicensingContext,
LicensingMechanism, ContextProperties, contextProperties — the
Ladusaw/Zwarts/K&L/von Fintel synthesis).

## Cross-framework gap (Israel ↔ Ladusaw)

This file enshrines two distinct theoretical lineages without making
the choice between them explicit at the type level:

- **Israel scalar model** (`ScalarValue` × `ScalarDirection` ×
  `LikelihoodEffect` × `Canonicity`): the apparatus of
  [israel-1996], [israel-2001], [israel-2011].
  Treats polarity-sensitivity as a scalar-rhetorical phenomenon
  (high/low + strengthening/attenuating) orthogonal to monotonicity.

- **Monotonicity-based licensing** (in companion file
  `Semantics/Polarity/Licensing.lean`): the
  [ladusaw-1979] / [kadmon-landman-1993] / [zwarts-1998]
  / [chierchia-2006] lineage. Treats polarity-sensitivity as a
  monotonicity-licensing phenomenon with widening + strengthening as
  the unifying mechanism.

These two lineages give *different predictions* for cases like FCIs in
modal contexts, NPIs in superlatives, and the "rescued" NPIs of
[chierchia-2006]. The cross-file gap is acknowledged but NOT
closed by this restructure: the `contextProperties.signature` field
in the companion file is Ladusaw/Zwarts/P&W canonical (Israel cannot
project per-context signatures without scale/role parameters from the
item itself).

The Israel↔Ladusaw refutation theorem — showing a context where the
scalar model and the monotonicity model disagree — is **planned** for
`Studies/Israel2001.lean`. The natural witness is
Israel's **pecuniary paradox** ([israel-2001]): *a red cent* (NPI,
resource = impeding role) and *for peanuts* (PPI, reward = facilitating
role) inhabit the same monetary semantic domain — pure-monotonicity
accounts treat them uniformly, while Israel's role-likelihood mapping
correctly predicts the polarity contrast. (NOTE: `Israel2001.lean §8`
currently formalizes Israel↔Ladusaw *agreement* via a `ScaleDirection`
bridge enum — that's the wrong direction. The refutation work is
genuinely deferred.)

## Alternative scalar-tradition frameworks (not formalized in linglib)

The Israel scalar model is one of several scalar-tradition accounts:
- [lahiri-1998]: even-based scalar analysis grounding *bhii* /
  *koii bhii* in cardinality vs contextually-salient property
  alternatives. Israel positions himself against this.
- [chierchia-2006]: exhaustification + D-alternatives subsume
  Israel's mechanism via implicit EXH; differs from Israel on FCI
  rescue (*any* in non-DE contexts).
- Krifka 1995 (STA — "Sumarizing the alternatives"): different
  alternative structure from Israel's high/low scalar dimension.
  (Not currently in `references.bib`.)

The substrate's enums (ScalarValue, ScalarDirection, Canonicity,
LikelihoodEffect) implement the Israel framework specifically;
formalising these alternatives would need parallel substrate types.

## The Scalar Model of Polarity

Polarity items are characterized by two orthogonal scalar features
([israel-1996], [israel-2001]):
- **ScalarValue** (high/low): where the item sits on its scale
- **ScalarDirection** (strengthening/attenuating): rhetorical force

These interact with **LikelihoodEffect** — whether the item's referent
facilitates or impedes the event — to predict **Canonicity**
(canonical vs inverted). See `Studies/Israel2001.lean`.
-/

namespace Semantics.Polarity

open Features (LicensingContext)

-- ════════════════════════════════════════════════════
-- § 1. Scalar Value ([israel-2001])
-- ════════════════════════════════════════════════════

/-- Where the polarity item sits on its scale, relative to the scalar norm.

    [israel-2001]: polarity items conventionally encode a fixed position
    on a scalar ordering. Emphatic NPIs typically denote LOW values
    (*a wink*, *an inch*), while emphatic PPIs typically denote HIGH values
    (*tons*, *utterly*). Inverted items reverse this pattern. -/
inductive ScalarValue where
  | high     -- denotes high scalar value (tons, utterly, wild horses)
  | low      -- denotes low scalar value (a wink, an inch, a pittance)
  | unknown  -- not yet classified
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Scalar Direction ([israel-1996], [schwab-2022])
-- ════════════════════════════════════════════════════

/-- Rhetorical force: does this item strengthen or attenuate the assertion?
    Orthogonal to both PolarityType and ScalarValue.

    - **Strengthening** items (ever, any, jemals) make the assertion stronger
      than its scalar alternatives ([israel-2001]'s "emphatic" items).
    - **Attenuating** items (all that, so recht, long) make the assertion weaker
      than its scalar alternatives ([israel-2001]'s "understating" items).
    - **NonScalar** items: editorial slot for items genuinely lacking
      scalar structure. NOTE: *lift a finger* is sometimes used as the
      canonical example, but Israel actually classifies it as scalar
      (extreme low effort = a minimizer). True non-scalar polarity items
      are theoretically contested; if uncertain, prefer `unknown`.

    [israel-1996]. Polarity sensitivity as lexical semantics. L&P 19(6).
    [israel-2011]. The Grammar of Polarity. CUP.
    [schwab-2022]. Lexical variation in NPI illusions. -/
inductive ScalarDirection where
  | strengthening  -- ever, any, jemals: assertion stronger than alternatives
  | attenuating    -- all that, so recht, long: assertion weaker than alternatives
  | nonScalar      -- editorial slot; Israel actually treats most "minimizers"
                   -- (incl. *lift a finger*) as scalar — see docstring caveat
  | unknown        -- not yet verified for this item
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Canonicity ([israel-2001])
-- ════════════════════════════════════════════════════

/-- Whether a polarity item is canonical or inverted.

    **Canonical** items have the expected correlation between scalar value
    and polarity type:
    - Canonical emphatic NPIs denote LOW values (*a wink*, *an inch*)
    - Canonical emphatic PPIs denote HIGH values (*tons*, *utterly*)

    **Inverted** items reverse this:
    - Inverted emphatic NPIs denote HIGH values (*wild horses*, *all the tea in China*)
    - Inverted emphatic PPIs denote LOW values (*at the drop of a hat*, *for a pittance*)

    [israel-2001] shows inversion tracks propositional role:
    canonical items fill impeding roles (patient/theme); inverted items
    fill facilitating roles (stimulus/instrument/reward). -/
inductive Canonicity where
  | canonical  -- scalar value tracks polarity type in the default way
  | inverted   -- scalar value is opposite to what polarity type predicts
  | unknown    -- not yet classified
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 4. Likelihood Effect ([israel-2001])
-- ════════════════════════════════════════════════════

/-- How increasing the scalar value of an item's referent affects the
    likelihood of the proposition being true.

    This is the key to [israel-2001]'s resolution of the
    maximizer/minimizer puzzle:

    - **Facilitating** roles (agent, stimulus, instrument, reward):
      bigger/more → event more likely → scale is inverted
      (e.g., *wild horses* — more powerful force → more likely to move you)

    - **Impeding** roles (patient, theme, increment, resource/expense):
      bigger/more → event less likely → scale is canonical
      (e.g., *lift a finger* — more effort required → less likely to act)

    The pecuniary paradox dissolves: *a red cent* (NPI, resource = impeding)
    vs *for peanuts* (PPI, reward = facilitating) — same monetary domain,
    different propositional roles. -/
inductive LikelihoodEffect where
  | facilitating  -- bigger → event more likely (agent, stimulus, reward)
  | impeding      -- bigger → event less likely (patient, theme, expense)
  | unknown       -- not yet classified
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 5. Polarity Item Types
-- ════════════════════════════════════════════════════

/-- Type of polarity sensitivity. -/
inductive PolarityType where
  | npiWeak      -- Weak NPI: licensed by DE contexts
  | npiStrong    -- Strong NPI: requires anti-additive
  | fci          -- Free Choice Item: modal/generic/imperative
  | npiFci      -- Dual use: NPI in DE, FCI under modals (= "any")
  | ppi          -- Positive Polarity Item: blocked in DE
  deriving DecidableEq, Repr

/-- Base quantificational force (when interpretable). -/
inductive BaseForce where
  | existential   -- ∃ (any, some)
  | universal     -- ∀ (every)
  | degree        -- Degree/extent (at all, in the least)
  | temporal      -- Time reference (ever, yet)
  | manner        -- Manner/way (whatsoever)
  | additive      -- Additive particle (either, also, too)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 6. Morphological Composition ([lahiri-1998], Lee & Horn 1994 MS (UNVERIFIED — bib entry missing))
-- ════════════════════════════════════════════════════

/-- Morphological composition of a polarity-sensitive item.
    [lahiri-1998] shows Hindi NPIs are transparently `indefinite + even`.
    Lee & Horn 1994 MS *any* as indef + EVEN documents this pattern
    cross-linguistically (UNVERIFIED — bib entry missing).

    NOTE on `indefPlusNeg`: covers items genuinely composed as
    indefinite + negation morphology (some Slavic n-words, Romanian *nimic*).
    Italian n-words (*nessuno*, *niente*, *mai*) are conventionally analyzed
    as negative-concord items rather than indef+neg morphology
    (Zanuttini, Penka, Déprez, Giannakidou); they should be classified
    via the negative-concord framework (planned), not via this morphology
    field. -/
inductive NPIMorphology where
  | indefPlusEven  -- indefinite + 'even'/'also' particle (Hindi bhii,
                   -- Japanese -mo, Korean -to; [haspelmath-1997] A.38.2, A.39.2)
  | indefPlusNeg   -- indefinite + negation (Romanian nimic; some Slavic n-words)
  | plain          -- morphologically simple (English 'any', 'ever')
  | idiomatic      -- frozen idiom ('lift a finger')
  deriving DecidableEq, Repr

/-- Type of alternatives introduced by the focused element.
    [lahiri-1998]: *ek bhii* introduces cardinality alternatives,
    *koii bhii* introduces contextually salient property alternatives.
    [chierchia-2006]: subdomain (D-)alternatives for domain widening. -/
inductive AlternativeType where
  | cardinality        -- {one, two, three, ...}: entailment-ordered
  | contextualProperty -- {P₁, P₂, ...}: contextually determined
  | domain             -- subdomain alternatives (Chierchia 2006 D-alternatives)
  | unspecified         -- not yet analyzed
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 7. Polarity Item Entry
-- ════════════════════════════════════════════════════

/-- A lexical entry for a polarity-sensitive item.

    Theory-neutral: captures distributional facts without committing
    to a particular analysis (exhaustification, domain widening, etc.). -/
structure PolarityItemEntry where
  /-- Surface form -/
  form : String
  /-- Type of polarity sensitivity -/
  polarityType : PolarityType
  /-- Base quantificational/semantic force -/
  baseForce : BaseForce
  /-- Contexts where licensed (empty = needs positive). Refers to
      `LicensingContext` from the companion file
      `Semantics/Polarity/Licensing.lean`. -/
  licensingContexts : List LicensingContext
  /-- Scalar direction: strengthening, attenuating, or non-scalar -/
  scalarDirection : ScalarDirection := .unknown
  /-- Scalar value: high or low on the relevant scale ([israel-2001]) -/
  scalarValue : ScalarValue := .unknown
  /-- Canonical or inverted ([israel-2001]) -/
  canonicity : Canonicity := .unknown
  /-- Propositional role's likelihood effect ([israel-2001]) -/
  likelihoodEffect : LikelihoodEffect := .unknown
  /-- Morphological composition ([lahiri-1998]) -/
  morphology : NPIMorphology := .plain
  /-- Type of alternatives introduced -/
  alternativeType : AlternativeType := .unspecified
  /-- Negative-concord / n-word status ([giannakidou-2000],
      [van-der-auwera-van-alsenoy-2016]). `none` for items outside the
      negative-concord system; strict-NC n-words set `some .nWord` here rather than
      leaning on a strong-NPI `polarityType`. -/
  nWordStatus : Option Features.NegativeConcord.NWordStatus := none
  /-- Notes -/
  notes : String := ""
  deriving Repr

-- ════════════════════════════════════════════════════
-- § 8. Predicates
-- ════════════════════════════════════════════════════

/-- The [zwarts-1998] strength class an item requires of its licensor.
    N-words (`nWordStatus = some .nWord`) require an anti-morphic licensor —
    extensionally, clausal negation: the strict-negative-concord distribution
    ([giannakidou-2000], [watanabe-2004]) read at the context-enum grain
    (concord locality lives in `nWordStatus`, not in this projection). Other
    items derive from `polarityType`: weak NPIs (and the NPI face of dual
    NPI/FCIs) need weak DE, strong NPIs anti-additivity; FCIs and PPIs are
    not strength-keyed. A genuine superstrong NPI (*a tad bit*) would still
    extend `PolarityType` when one lands. -/
def PolarityItemEntry.strength (e : PolarityItemEntry) :
    Option NaturalLogic.DEStrength :=
  if e.nWordStatus = some .nWord then some .antiMorphic else
  match e.polarityType with
  | .npiWeak => some .weak
  | .npiFci => some .weak
  | .npiStrong => some .antiAdditive
  | .fci => none
  | .ppi => none

/-- Check if a context licenses a polarity item.

    An item is licensed if the context is explicitly listed in `licensingContexts`. -/
abbrev isLicensedIn (item : PolarityItemEntry) (ctx : LicensingContext) : Prop :=
  ctx ∈ item.licensingContexts

/-- Check if an item is an NPI (weak or strong). -/
abbrev PolarityItemEntry.isNPI (p : PolarityItemEntry) : Prop :=
  p.polarityType = .npiWeak ∨ p.polarityType = .npiStrong ∨ p.polarityType = .npiFci

/-- Check if an item is an FCI. -/
abbrev PolarityItemEntry.isFCI (p : PolarityItemEntry) : Prop :=
  p.polarityType = .fci ∨ p.polarityType = .npiFci

/-- Check if an item is a PPI. -/
abbrev PolarityItemEntry.isPPI (p : PolarityItemEntry) : Prop :=
  p.polarityType = .ppi

/-! ### Israel's prediction functions live in Theories

Israel's main empirical claim — `predictCanonicity` (impeding role →
canonical / facilitating role → inverted) and the
`PolarityItemEntry.canonicityConsistent` validation predicate that
checks whether stated canonicity matches the prediction — were moved
to `Semantics/Polarity/Israel.lean` (sibling of
`Semantics/Polarity/Licensing.lean`). This file holds only
the substrate enums Fragments populate, not Israel's predictions about
how those enum-valued fields relate. -/

end Semantics.Polarity

-- Re-export `LicensingContext` from `Features/` into `Semantics.Polarity`
-- so consumers doing `open Semantics.Polarity` see it in scope without
-- a separate `open Features`. (35 PolarityItem consumers reference
-- LicensingContext via constructors like `.negation`, `.modalPossibility`
-- in `PolarityItemEntry.licensingContexts` field initialization.)
namespace Semantics.Polarity
export Features (LicensingContext)
end Semantics.Polarity
