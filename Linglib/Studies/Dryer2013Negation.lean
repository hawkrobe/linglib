import Linglib.Syntax.Negation
import Linglib.Fragments.English.Negation
import Linglib.Fragments.German.Negation
import Linglib.Fragments.Romance.French.Negation
import Linglib.Fragments.Slavic.Russian.Negation
import Linglib.Fragments.Finnish.Negation
import Linglib.Fragments.Japanese.Negation
import Linglib.Fragments.Mandarin.Negation
import Linglib.Fragments.Turkish.Negation
import Linglib.Fragments.Slavic.Czech.Negation
import Linglib.Fragments.Spanish.Negation
import Linglib.Fragments.Italian.Negation
import Linglib.Fragments.Burmese.Negation
import Linglib.Fragments.Maori.Negation
import Linglib.Fragments.Hixkaryana.Negation
import Linglib.Fragments.Quechua.Negation

/-!
# Dryer (2013): WALS chapters on negation morpheme + word-order (112A, 143A, 144A)
[dryer-2013-wals] [wals-2013]

WALS chapters by Matthew S. Dryer covering negation typology:

- Ch 112A: Negative Morphemes
- Ch 143A: Order of Negative Morpheme and Verb
- Ch 144A: Position of Negative Word with Respect to Subject, Object, Verb

This study file holds **cross-linguistic generalisations** over a
15-language Fragment sample. Each language contributes its Fragment-side
`negationSystem` joint, whose WALS Ch 112A/143A/144A datapoints and ISO key
are populated from `Data.WALS` by `NegationSystem.ofISO`; the Ch 113-115
values are read off the `Data.WALS` rows via the `Syntax.Negation` per-ISO
accessors. No WALS value is hand-encoded here.

Ch 113-115 (Miestamo's symmetric/asymmetric chapters) are grounded in
`Studies/Miestamo2005.lean`.
-/

set_option autoImplicit false

namespace Dryer2013Negation

open Syntax.Negation

/-- The 15-language sample: the Fragment-side `negationSystem` joints.
    Sample shrunk from the dissolved file's 19 (dropped Izi, KolymaYukaghir,
    Rama, Nelemwa — none of which had Fragment files in the project).
    Czech is absent from the WALS Ch 113A-115A samples, so Ch 113-115
    claims hold vacuously for it. -/
def sample : List NegationSystem :=
  [ English.Negation.negationSystem
  , German.Negation.negationSystem
  , French.Negation.negationSystem
  , Russian.Negation.negationSystem
  , Finnish.Negation.negationSystem
  , Japanese.Negation.negationSystem
  , Mandarin.Negation.negationSystem
  , Turkish.Negation.negationSystem
  , Czech.Negation.negationSystem
  , Spanish.Negation.negationSystem
  , Italian.Negation.negationSystem
  , Burmese.Negation.negationSystem
  , Maori.Negation.negationSystem
  , Hixkaryana.Negation.negationSystem
  , Quechua.Negation.negationSystem ]

/-- WALS Ch 113A codes the language as having asymmetric negation
    (`asymmetric` or `both`). -/
def walsHasAsymmetric (iso : String) : Bool :=
  (symmetryOfISO iso).any (fun v => v == .asymmetric || v == .both)

/-! ### Cross-linguistic generalisations -/

set_option maxRecDepth 8192 in
/-- In the sample, every language with bipartite ("double") negation
    morphemes (Ch 112A) has asymmetric negation (Ch 113A). If negation
    requires two markers whose placement changes the clause structure, the
    negative clause structurally differs from the affirmative.
    (Scoped `maxRecDepth`: kernel evaluation recurses through the
    1157-row Ch 112A table.) -/
theorem bipartite_implies_asymmetric :
    sample.all (fun s =>
      s.wals112A != some .doubleNegation || walsHasAsymmetric s.iso) = true := by
  decide

/-- In the sample, every language classified as symmetric-only (Ch 113A)
    has a non-assignable asymmetry subtype (Ch 114A). -/
theorem symmetric_implies_nonassignable :
    sample.all (fun s =>
      symmetryOfISO s.iso != some .symmetric ||
      asymmetrySubtypeOfISO s.iso == some .nonAssignable) = true := by
  decide

/-- In the sample, no language classified as asymmetric or both (Ch 113A)
    has a non-assignable subtype (Ch 114A). -/
theorem asymmetric_implies_assignable :
    sample.all (fun s =>
      !walsHasAsymmetric s.iso ||
      (asymmetrySubtypeOfISO s.iso).any (· != .nonAssignable)) = true := by
  decide

set_option maxRecDepth 8192 in
/-- Negative auxiliary verbs (Ch 112A) are always associated with asymmetric
    negation of subtype A/Fin (Ch 114A): the auxiliary becomes the finite
    element, and the lexical verb is deficitized. Finnish illustrates this
    perfectly. (Scoped `maxRecDepth` as in `bipartite_implies_asymmetric`.) -/
theorem aux_verb_implies_afin :
    sample.all (fun s =>
      s.wals112A != some .negativeAuxiliaryVerb ||
      asymmetrySubtypeOfISO s.iso == some .finiteness) = true := by
  decide

/-- Russian shows negative concord (Ch 115A: negative indefinites co-occur
    with predicate negation). Czech, the sample's other Slavic language, is
    not in the Ch 115A sample; its obligatory concord is illustrated by
    `Czech.Negation.allConcordExamples`. -/
theorem russian_neg_concord :
    negIndefiniteOfISO Russian.Negation.negationSystem.iso = some .cooccur := by
  decide

end Dryer2013Negation
