import Linglib.Typology.Pronoun.Basic

/-!
# Modern Standard Arabic Pronoun Profile (WALS Chs 39, 40, 44–48; Chs 136–137)
@cite{wals-2013} @cite{ryding-2005}

WALS-style typological summary of MSA's personal pronoun system. Ryding
ch 12 (pp. 298–314) gives the full paradigm; this file records the
typological-feature dimensions only (which are also the dimensions on
which MSA and Egyptian Arabic largely agree).

## Forms (for reference, not encoded as data here)

Independent personal pronouns (Ryding §12.1 Table p. 298; the *Damaaʾir
munfaSila* الضمائر المنفصلة):
- 1SG *ʾanaa* (gender-invariant); 1PL *naḥnu*
- 2SG.M *ʾanta* / 2SG.F *ʾanti* / 2DU *ʾantumaa* / 2PL.M *ʾantum* / 2PL.F *ʾantunna*
- 3SG.M *huwa* / 3SG.F *hiya* / 3DU *humaa* / 3PL.M *hum* / 3PL.F *hunna*

The dual category (MSA-distinctive — Egyptian Arabic has lost it) is
the most visible MSA-vs-Egyptian contrast. Suffix pronouns (the
*Damaaʾir muttaSila* الضمائر المتصلة, Ryding §12.2 p. 301) are
phonologically reduced clitics on nouns / verbs / prepositions
(*kitaab-i-hi* 'his book', *bi-haa* 'with her', *qaal-uu-hu* 'they
said it').
-/

namespace Fragments.Arabic.ModernStandard

/-- Modern Standard Arabic (Afro-Asiatic, Semitic, ISO `arb`). MSA
    matches Egyptian on every WALS dimension surveyed here except for the
    presence of the dual: MSA marks 2DU (*ʾantumaa*) and 3DU (*humaa*),
    which Egyptian has lost. Per Ryding §12.1 (p. 298). -/
def pronounProfile : Pronoun.Profile :=
  { language := "Arabic (Modern Standard)"
  , family := "Afro-Asiatic"
  , iso := "arb"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .in3rdAndOtherPersons
  , politeness := some .none
  , indefiniteType := some .genericNounBased
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .pronounsOnly }

/-- MSA pronoun phonological shape (WALS Chs 136–137 per
    @cite{nichols-peterson-2013}): no M-T pattern (1SG *ʾanaa* lacks /m/;
    2SG *ʾanta* has /t/, not /m/), no N-M pattern (2SG has /t/, not /m/).
    1SG *ʾanaa* contains /n/ but the diagnostic requires the
    /n/ ~ /m/ pair, which is not present. -/
def pronounShapeProfile : Pronoun.ShapeProfile :=
  { language := "Arabic (Modern Standard)"
  , iso := "arb"
  , mtPronouns := some .absent
  , mIn1sg := some .absent
  , nmPronouns := some .absent
  , mIn2sg := some .absent }

end Fragments.Arabic.ModernStandard
