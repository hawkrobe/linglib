import Linglib.Features.Possession

/-!
# Smyrna Greek possession profile
[stassen-2009] [nichols-1986] [heine-1997]
[liosis-2016] [kampanarou-alexiadou-2026]

`PossessionProfile` bundle for Smyrna Greek (Aegean), the
*genitive-over-extension* endpoint within the Modern Greek dialect
continuum — the opposite direction from Grevena Greek.

## What makes Smyrna different from SMG

Smyrna Greek **tolerates inflectional genitive forms that SMG rejects** as
paradigm gaps. [liosis-2016] (cited in [kampanarou-alexiadou-2026]
fn 7 p. 11) lists *tu luluðakju* 'little flower-DIM.SG.GEN' and
*ton naftakjo(n)* 'little sailor-DIM.PL.GEN' as acceptable in Smyrna —
both starred in SMG, where the *-aki* diminutive class systematically
lacks inflectional genitive forms ([kampanarou-alexiadou-2026] §3
exx 14a–b).

This matters for the cross-dialectal argument: the Modern Greek dialect
continuum is **bidirectional**, not unidirectional toward genitive loss.
SMG sits between Smyrna's permissive paradigm and Grevena's complete
loss. Without a Smyrna profile in the typology, the SMG → GG trajectory
would look monotonic; Smyrna shows that the synchronic distribution is a
genuine intermediate state in a two-sided space.

## Cross-dialectal contrast

Sibling profiles: `Fragments/Greek/Possession.lean` (SMG, transitional)
and `Fragments/Greek/Grevena/Possession.lean` (GG, genitive lost).
-/

set_option autoImplicit false

namespace Greek.Smyrna.Possession

open _root_.Possession

/-- Heine notions expressible by Smyrna inflectional genitive. Same
    coverage as SMG — the Smyrna difference is in the *paradigm* (no gaps
    on `-aki` diminutives), not in the *notional range*. -/
def genNotions : List Notion :=
  [.physical, .temporary, .permanent, .inalienable, .abstract,
   .inanimateInalienable, .inanimateAlienable]

/-- Heine notions expressible by Smyrna `apo`-PPs. Smyrna is more
    permissive on the genitive side, so the `apo`-PP variant is less
    pressed into service; the `apo`-PP coverage parallels SMG (restricted
    to inanimate part-whole/source). -/
def apoNotions : List Notion :=
  [.inanimateInalienable, .inanimateAlienable]

/-- Smyrna Greek possession profile.

    Surface profile (`adnominalStrategy = .dependentMarking`) matches SMG;
    the difference is *paradigm completeness*, not strategy choice — the
    `-aki` diminutive class permits the genitive forms that SMG rejects
    as paradigm gaps. -/
def possession : PossessionProfile :=
  { language := "Smyrna Greek"
  , family := "Indo-European"
  , iso := "ell"  -- shares macro-language code with SMG
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .haveVerb
  , adnominalStrategy := .dependentMarking
  , affixPosition := some .none
  , examples :=
      [ "tu luluðakju"          -- 'little flower-DIM.SG.GEN' (SMG: *)
      , "ton naftakjo(n)"       -- 'little sailor-DIM.PL.GEN' (SMG: *)
      ]
  , notes := "Same surface adnominal strategy as SMG (dependent-marking inflectional genitive),\
 but with a more permissive paradigm: -aki diminutive nouns license inflectional genitive forms\
 that SMG rejects as paradigm gaps (per Liosis 2016, cited in Kampanarou & Alexiadou 2026 fn 7).\
 Establishes the bidirectionality of the Modern Greek dialect continuum: SMG sits between Smyrna's\
 over-extension and Grevena's complete loss." }

end Greek.Smyrna.Possession
