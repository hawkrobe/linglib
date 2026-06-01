import Linglib.Typology.Numeral.WALS

/-!
# Modern Standard Arabic Numeral Profile (WALS Chs 53–56, 131)
@cite{wals-2013} @cite{ryding-2005}

WALS-style typological summary for MSA cardinal and ordinal numerals
per Ryding ch 15 (pp. 329–365).

## What's encoded vs documented

The substrate `Numeral.Profile` records a small set of
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
- 2 *ithnaani* ↔ ordinal *thaanin* — regular *faaʿil* template applied
  to the cardinal's own root th-n-y. Greenberg's WALS Ch 53A typology
  cares about formal distinctness from the cardinal (template-only
  reformation counts as regular), so MSA falls under "first suppletive,
  second-onward regular" rather than "first-and-second suppletive".
- 3+ : ordinal *thaalith* / *raabiʿ* / *xaamis* / … same regular
  *faaʿil* pattern from the cardinal root.
-/

namespace Arabic.ModernStandard

/-- MSA: "first" *ʾawwal* fully suppletive (unrelated root w-ḥ-d vs ʾ-w-l);
    "second" *thaanin* and onward are regular *faaʿil*-pattern derivations
    from the cardinal root, so the WALS Ch 53A category is `firstSuppletion`
    (only "first" suppletive). Distributive numerals are not marked by
    dedicated morphology in MSA — repetition (*waaḥid waaḥid* 'one by one')
    is general intensifying reduplication rather than a productive
    distributive construction in the Gil/WALS-Ch-54 sense. No numeral
    classifiers. *wa-* 'and' and *kull* 'all/every' are morphologically
    distinct. Dual + plural marking on counted nouns is obligatory.
    Decimal base (Ryding §15.1). -/
def numeralProfile : Numeral.Profile :=
  -- MSA (iso `arb`) is absent from WALS Chs 53/131; curated values kept for
  -- those. Ch 54 defaults to `noDistributive`, matching the docstring (the
  -- reduplication is intensifying, not a productive distributive).
  { Numeral.Profile.fromWALS "Arabic (Modern Standard)" "arb"
      (region := .westAsia) (pluralMarking := .obligatory) with
    ordinal := .firstSuppletion
    numeralBase := some .decimal }

end Arabic.ModernStandard
