import Linglib.Typology.Numerals

/-!
# Modern Standard Arabic Numeral Profile (WALS Chs 53–56, 131)
@cite{wals-2013} @cite{ryding-2005}

WALS-style typological summary for MSA cardinal and ordinal numerals
per Ryding ch 15 (pp. 329–365).

## What's encoded vs documented

The substrate `Typology.NumeralProfile` records a small set of
typological dimensions (ordinal-formation strategy, distributive
marking, classifier presence, conjunction–quantifier identity, plural
marking, base). The arithmetically richer phenomena MSA is famous for
— the **polarity rule** (3–10 numerals take the opposite gender of
the counted noun), the **dual** numeral category, and the
diptote/triptote case alternation on *ʾaḥad ʿashar* through *tisʿat
ʿashar* (11–19) — are paradigm-internal facts not exposed by the
WALS-aligned schema. They are noted here for orientation but not
encoded as data: a richer Fragment for cardinal-numeral morphology
would belong in a separate file (or a future Studies engagement).

## Forms (Ryding §15.1 cardinals; §15.2 ordinals)

- 1 *waaḥid* (root w-ḥ-d) ↔ ordinal *ʾawwal* (root ʾ-w-l) — fully
  suppletive (different consonantal roots).
- 2 *ithnaani* ↔ ordinal *thaanin* — same root th-n-y but the ordinal
  uses the active-participle template *faaʿil*; treated as suppletive
  in the Greenberg-style typology (cf. Ryding §15.2).
- 3+ : ordinal *thaalith* / *raabiʿ* / *xaamis* / … regular *faaʿil*
  pattern from the cardinal root.
-/

namespace Fragments.Arabic.ModernStandard

/-- MSA: "first" *ʾawwal* fully suppletive (unrelated root); "second"
    *thaanin* on a distinct stem from the cardinal *ithnaani*; "third"
    onward derived regularly via the *faaʿil* template from cardinal
    roots. Distributive numerals are not marked by a dedicated
    morphological strategy in MSA — repetition (*waaḥid waaḥid* 'one by
    one') is the productive option, captured here as `markedByReduplication`.
    No numeral classifiers. *wa-* 'and' and *kull* 'all/every' are
    morphologically distinct. Dual + plural marking on counted nouns is
    obligatory. Decimal base (Ryding §15.1). -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Arabic (Modern Standard)"
  , iso := "arb"
  , ordinal := .firstSecondSuppletion
  , distributive := .markedByReduplication
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .westAsia
  , pluralMarking := .obligatory
  , numeralBase := some .decimal }

end Fragments.Arabic.ModernStandard
