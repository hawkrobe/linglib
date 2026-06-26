/-!
# Negative concord: n-word + concord typology
[giannakidou-2000] [van-der-auwera-van-alsenoy-2016]

Lightweight, Fragment-importable types for negative concord: the item-level n-word
status, the NC subtype, and the clausal-position parameter the strict/non-strict
contrast turns on.

Kept separate from `Typology/Negation.lean` (the WALS-based negation survey) so that
`Typology/PolarityItem.lean` and Fragment lexicons can import the n-word classification
without pulling in the WALS datapoint files. `Negation.lean` imports *this* file to
bridge the item-level status to its language-level WALS 115A `NegIndefiniteStrategy`
(`NegIndefiniteStrategy.hasNegativeConcord` / `.admits`).

## Main declarations

* `NWordStatus` — n-word / negative-quantifier / NPI (item-level).
* `NegConcordSubtype` — strict / non-strict / negative-spread.
* `NWordPosition` + `NegConcordSubtype.nmRequired` — the strict/non-strict contrast,
  derived from the type.
-/

namespace Features.NegativeConcord

/-- Item-level status of a negation-sensitive indefinite: the n-word vs
    negative-quantifier vs NPI trichotomy. [giannakidou-2000] gives the minimal,
    deliberately theory-neutral definition — n-words "occur in NC structures and can be
    associated with negative meaning" — and stresses their heterogeneity. The *internal*
    semantics is contested (negative existential vs polarity-sensitive universal vs an
    NPI licensed by a null negation); this enum records only the distributional class,
    which [van-der-auwera-van-alsenoy-2016] take as the basis of the NC typology.
    Lets a strict-NC n-word (Russian никто, Italian *nessuno*) be classified honestly
    rather than borrowing a strong-NPI slot in `Typology.PolarityItem`. -/
inductive NWordStatus where
  /-- N-word: occurs in negative-concord structures (Romance *nessuno*, Slavic никто,
      Greek *típota*, Hungarian *semmi*); licenses a negative fragment answer ("Nothing.")
      yet typically co-occurs with a clausal negation marker. -/
  | nWord
  /-- Inherently negative quantifier: negates on its own with no concord; two stack to
      double negation. English *nobody*, German *niemand*. -/
  | negQuantifier
  /-- Negative-polarity item: non-negative, licensed by (not contributing) negation,
      occurs across a wider range of contexts (questions, conditionals, comparatives).
      English *anybody*. -/
  | npi
  deriving DecidableEq, BEq, Repr

/-- Subtype of negative concord ([van-der-auwera-van-alsenoy-2016];
    [giannakidou-2000]). `strict` keeps the clausal negation marker regardless of
    n-word position (Greek, Hungarian, Slavic); `nonStrict` drops it when the n-word is
    preverbal but requires it postverbally (Italian, Spanish, Portuguese);
    `negativeSpread` has several n-words share one negation with no clausal marker at all
    (French *personne n'a rien dit*). [van-der-auwera-van-alsenoy-2016] find
    `strict` far more frequent than `nonStrict`, and `nonStrict` itself heterogeneous —
    not cleanly a single category. -/
inductive NegConcordSubtype where
  | strict
  | nonStrict
  | negativeSpread
  deriving DecidableEq, BEq, Repr

/-- Position of an n-word relative to the finite verb — the parameter the strict vs
    non-strict contrast turns on. -/
inductive NWordPosition where
  | preverbal
  | postverbal
  deriving DecidableEq, BEq, Repr

/-- Whether a clausal negation marker is required, given the NC subtype and the n-word's
    position ([giannakidou-2000]: strict NC keeps the marker regardless of position;
    non-strict drops it for a preverbal n-word but requires it postverbally; negative
    spread has no clausal marker). The strict/non-strict contrast falls out of the type. -/
def NegConcordSubtype.nmRequired : NegConcordSubtype → NWordPosition → Bool
  | .strict, _ => true
  | .nonStrict, .preverbal => false
  | .nonStrict, .postverbal => true
  | .negativeSpread, _ => false

/-- The strict vs non-strict contrast: both require the marker postverbally, but only
    strict requires it preverbally ([giannakidou-2000]). -/
theorem strict_nonstrict_contrast :
    NegConcordSubtype.strict.nmRequired .preverbal = true ∧
    NegConcordSubtype.nonStrict.nmRequired .preverbal = false ∧
    NegConcordSubtype.nonStrict.nmRequired .postverbal = true := by decide

end Features.NegativeConcord
