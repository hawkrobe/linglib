/-
Shared nominal classification and phi-feature agreement for DG coreference theories.

Used by d-command (Coreference.lean) binding analyses.
-/

import Linglib.Core.Word
import Linglib.Features.CoreferenceStatus
import Linglib.Fragments.English.NominalClassification
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal

namespace DepGrammar.Nominal

-- ============================================================================
-- Nominal Classification (shared helper)
-- ============================================================================

-- Nominal classification and φ-agreement are the shared, lexicon-driven
-- `Fragments.English.NominalClassification` definitions, re-exported here so
-- the d-command binding analyses (`Coreference.lean`) keep referring to them
-- through `DepGrammar.Nominal`.
export Features (NominalType)
export Fragments.English.NominalClassification (isNominalCat classifyNominal phiAgree)

-- ============================================================================
-- Shared Test Words (from Fragments, used by Coreference.lean)
-- ============================================================================

abbrev john := Fragments.English.Nouns.john.toWordSg
abbrev mary := Fragments.English.Nouns.mary.toWordSg
abbrev they := Fragments.English.Pronouns.they.toWord
abbrev sees := Fragments.English.Predicates.Verbal.see.toWord3sg
abbrev see := Fragments.English.Predicates.Verbal.see.toWordPl
abbrev himself := Fragments.English.Pronouns.himself.toWord
abbrev herself := Fragments.English.Pronouns.herself.toWord
abbrev themselves := Fragments.English.Pronouns.themselves.toWord
abbrev him := Fragments.English.Pronouns.him.toWord
abbrev her := Fragments.English.Pronouns.her.toWord
abbrev them := Fragments.English.Pronouns.them.toWord
abbrev eachOther := Fragments.English.Pronouns.eachOther.toWord

end DepGrammar.Nominal
