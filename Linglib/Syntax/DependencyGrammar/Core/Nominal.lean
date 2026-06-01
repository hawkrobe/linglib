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
-- `English.NominalClassification` definitions, re-exported here so
-- the d-command binding analyses (`Coreference.lean`) keep referring to them
-- through `DepGrammar.Nominal`.
export Features (NominalType)
export English.NominalClassification (isNominalCat classifyNominal phiAgree)

-- ============================================================================
-- Shared Test Words (from Fragments, used by Coreference.lean)
-- ============================================================================

abbrev john := English.Nouns.john.toWordSg
abbrev mary := English.Nouns.mary.toWordSg
abbrev they := English.Pronouns.they.toWord
abbrev sees := English.Predicates.Verbal.see.toWord3sg
abbrev see := English.Predicates.Verbal.see.toWordPl
abbrev himself := English.Pronouns.himself.toWord
abbrev herself := English.Pronouns.herself.toWord
abbrev themselves := English.Pronouns.themselves.toWord
abbrev him := English.Pronouns.him.toWord
abbrev her := English.Pronouns.her.toWord
abbrev them := English.Pronouns.them.toWord
abbrev eachOther := English.Pronouns.eachOther.toWord

end DepGrammar.Nominal
