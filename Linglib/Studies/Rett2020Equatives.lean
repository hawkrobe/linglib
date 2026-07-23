import Linglib.Semantics.Degree.Basic

/-!
# Rett 2020: Separate but Equal — A Typology of Equative Constructions

[rett-2020-equatives] replicates the descriptive and theoretical typologies of
comparatives for equatives. Descriptively (§3, after Henkelmann 2006 and
Haspelmath & Buchholz 1998), languages mark equatives by relative strategies
(a degree-relativizer standard marker, with or without a parameter marker),
predicate strategies (a main predicate 'equal' or an adverbial 'equally'),
conjoined clauses, case-marked standards, or dedicated morphemes.
Theoretically (Figure 3), predicative equatives lack weak "at least" readings;
non-predicative equatives split into explicit (parameter-marked) and implicit
(unmarked, evaluative) — and explicit equatives split again (§4.3) into
sufficientive parameter markers (English *as*, degree quantifiers, modifiable
by *twice*) and degree-demonstrative parameter markers (Italian *tanto*,
unmodifiable).

Only the sufficientive strategy involves degree quantification (§5); its
set-based ⟦as⟧ ((5-b)) relates degree sets by inclusion, which at extent sets
is exactly the point-standard equative (`setBasedAs_iff_equativeSem`).
-/

namespace Rett2020Equatives

/-! ### Descriptive strategies (§3) -/

/-- An equative-marking strategy: the descriptive classes of §3, with
parameter-marked relatives split per §4.3 and the Appendix. -/
inductive Strategy where
  /-- Relativizer standard marker only ("Jane is tall like Bill";
  Italian *come*, Serbo-Croatian *kao*). -/
  | relativeSMOnly
  /-- Degree-demonstrative parameter marker plus relativizer standard marker
  (Italian *tanto...quanto*, Spanish *tan...como*). -/
  | relativeDemonstrative
  /-- Sufficientive parameter marker plus relativizer standard marker
  (English *as...as*, German *so...wie*). -/
  | relativeSufficientive
  /-- Main predicate meaning 'equal' (Nkore-Kiga *-ingana*). -/
  | predicateMain
  /-- Adverbial meaning 'equally, to the same extent' (Mandarin *yíyàng*). -/
  | predicateAdverbial
  /-- Conjoined parallel clauses, often with an additive particle
  (Mangarayi). -/
  | conjoined
  /-- Case marker or preposition as standard marker (Japanese, Greenlandic). -/
  | caseMarkedStandard
  /-- Construction-specific markers with no transparent etymology (Welsh). -/
  | dedicated
  deriving DecidableEq, Repr

/-- Theoretical classes (Figure 3). -/
inductive TheoreticalClass where
  | predicative
  | explicitSufficientive
  | explicitDemonstrative
  | implicit
  deriving DecidableEq, Repr

/-- Figure 3's classification. Predicate subtypes pattern together (fn. 11);
SM-only relatives and conjoined equatives are implicit by the §4.1
diagnostics; case-marked and dedicated strategies are left for future
research (§5). -/
def Strategy.theoretical : Strategy → Option TheoreticalClass
  | .relativeSMOnly => some .implicit
  | .relativeDemonstrative => some .explicitDemonstrative
  | .relativeSufficientive => some .explicitSufficientive
  | .predicateMain => some .predicative
  | .predicateAdverbial => some .predicative
  | .conjoined => some .implicit
  | .caseMarkedStandard => none
  | .dedicated => none

/-- A language's equative strategy with the paper's example form and
location. -/
structure TypologyDatum where
  language : String
  strategy : Strategy
  form : String
  /-- Example number or Appendix row. -/
  source : String
  deriving Repr

/-- Per-language strategies; a language may use several (English (50)). -/
def typology : List TypologyDatum :=
  [ { language := "English", strategy := .relativeSufficientive
    , form := "as ... as", source := "(50-a), Appendix" }
  , { language := "English", strategy := .relativeSMOnly
    , form := "tall like Bill", source := "(50-b)" }
  , { language := "English", strategy := .predicateMain
    , form := "equals Bill in height", source := "(50-d)" }
  , { language := "German", strategy := .relativeSufficientive
    , form := "so ... wie", source := "Appendix" }
  , { language := "French", strategy := .relativeSufficientive
    , form := "aussi ... que", source := "Appendix" }
  , { language := "Dutch", strategy := .relativeSufficientive
    , form := "zo ... als", source := "(63)" }
  , { language := "Swedish", strategy := .relativeSufficientive
    , form := "så ... som", source := "(67)" }
  , { language := "Italian", strategy := .relativeSMOnly
    , form := "come", source := "(61)" }
  , { language := "Italian", strategy := .relativeDemonstrative
    , form := "tanto ... quanto", source := "(70)" }
  , { language := "Spanish", strategy := .relativeDemonstrative
    , form := "tan ... como", source := "(73)" }
  , { language := "Croatian", strategy := .relativeSMOnly
    , form := "kao", source := "(58)" }
  , { language := "Mandarin", strategy := .predicateAdverbial
    , form := "gēn ... yíyàng gāo", source := "(37)" }
  , { language := "Japanese", strategy := .caseMarkedStandard
    , form := "", source := "§3.4 language list" }
  , { language := "Nkore-Kiga", strategy := .predicateMain
    , form := "-ingana ... oburaingwa", source := "(33)" }
  , { language := "Mangarayi", strategy := .conjoined
    , form := "ŋa-balayi ... wadij ña-balayi", source := "(42)" }
  , { language := "Welsh", strategy := .dedicated
    , form := "cyn ... â", source := "(47)" }
  ]

/-! ### Diagnostics for explicit equatives (Figure 2) -/

/-- A row of Figure 2: a parameter-marked relative equative with its subtype
and diagnostic values. `none` records the paper's uncertain cells. -/
structure ExplicitDiagnostics where
  language : String
  pm : String
  subtype : Strategy
  modifiable : Option Bool
  evaluative : Option Bool
  weakReading : Option Bool
  deriving Repr

/-- Figure 2's table. Slovenian's uncertain cells and Spanish's uncertain
modifiability (the consultants' "unnatural" vs Italian's ungrammatical, fn. 15
and surrounding text) are `none`. -/
def figure2 : List ExplicitDiagnostics :=
  [ { language := "English", pm := "as", subtype := .relativeSufficientive
    , modifiable := some true, evaluative := some false, weakReading := some true }
  , { language := "Dutch", pm := "zo", subtype := .relativeSufficientive
    , modifiable := some true, evaluative := some false, weakReading := some true }
  , { language := "German", pm := "so", subtype := .relativeSufficientive
    , modifiable := some true, evaluative := some false, weakReading := some true }
  , { language := "Korean", pm := "mankhum", subtype := .relativeSufficientive
    , modifiable := some true, evaluative := some false, weakReading := some true }
  , { language := "Swedish", pm := "så", subtype := .relativeSufficientive
    , modifiable := some true, evaluative := some false, weakReading := some true }
  , { language := "Catalan", pm := "tan", subtype := .relativeDemonstrative
    , modifiable := some false, evaluative := some false, weakReading := some true }
  , { language := "Italian", pm := "tanto", subtype := .relativeDemonstrative
    , modifiable := some false, evaluative := some false, weakReading := some true }
  , { language := "Romanian", pm := "tot", subtype := .relativeDemonstrative
    , modifiable := some false, evaluative := some false, weakReading := some true }
  , { language := "Slovenian", pm := "tako", subtype := .relativeDemonstrative
    , modifiable := some false, evaluative := none, weakReading := none }
  , { language := "Spanish", pm := "tan", subtype := .relativeDemonstrative
    , modifiable := none, evaluative := some false, weakReading := some true }
  ]

/-- Figure 2's generalization: among explicit equatives, factor-modifiability
holds exactly of the sufficientive parameter markers — the diagnostic that
splits explicit equatives into two subtypes. -/
theorem sufficientive_iff_modifiable :
    ∀ r ∈ figure2, r.modifiable = some true ↔ r.subtype = .relativeSufficientive := by
  decide

/-- Explicit equatives of both subtypes are non-evaluative wherever Figure 2
records a value. -/
theorem explicit_not_evaluative :
    ∀ r ∈ figure2, r.evaluative = some true → False := by
  decide

/-! ### The sufficientive equative as a degree quantifier -/

/-- The set-based sufficientive ⟦as⟧ ((5-b)): the standard's degree set is
included in the target's. -/
def setBasedAs {D : Type*} (std tgt : Set D) : Prop := std ⊆ tgt

/-- At extent sets, the set-based ⟦as⟧ is the point-standard equative: the
degree-quantificational sufficientive strategy coincides with
`Degree.equativeSem` over a measure function. -/
theorem setBasedAs_iff_equativeSem {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    setBasedAs (Set.Iic (μ b)) (Set.Iic (μ a)) ↔ Degree.equativeSem μ a b .positive :=
  (Degree.equativeSem_iff_Iic_subset μ a b).symm

end Rett2020Equatives
