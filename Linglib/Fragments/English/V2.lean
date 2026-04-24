import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic

/-!
# English V2 Profiles
@cite{westergaard-2009}

V2 micro-parameter profiles for English varieties (Table 3.1).
-/

namespace Fragments.English

open Minimalism (ForceHead V2Profile)

/-- Standard English: V-to-C only in matrix wh-questions and
    yes/no-questions (subject-auxiliary inversion). -/
abbrev stdEnglish : V2Profile :=
  {.Int, .Pol}

/-- Belfast English: like Standard English plus V-to-C in embedded
    questions (@cite{henry-1995}'s "I wonder could he come").
    -- UNVERIFIED: the `.Imp` setting (matrix imperative V-to-C
    -- distinct from Standard English) reflects the previous V2Data
    -- transcription but has not been independently confirmed against
    -- @cite{westergaard-2009} Table 3.1 or @cite{henry-1995}; Henry's
    -- monograph documents singular concord and embedded inversion in
    -- Belfast but does not (to our knowledge) treat matrix imperatives
    -- as a Belfast-specific micro-parameter — Standard English
    -- imperatives are already V1, making +Imp° on Belfast alone
    -- empirically odd. -/
abbrev belfastEnglish : V2Profile :=
  {.Int, .Pol, .Imp, .Wh}

end Fragments.English
