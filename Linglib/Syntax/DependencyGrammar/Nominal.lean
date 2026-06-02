import Linglib.Core.Word
import Linglib.Features.CoreferenceStatus
import Linglib.Fragments.English.NominalClassification
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Shared nominal classification for DG coreference theories

Re-exports lexicon-driven nominal classification and φ-feature agreement
from `Fragments.English.NominalClassification` under the
`DepGrammar.Nominal` namespace, plus a small bundle of English test words
consumed by paper-anchored Studies (`Studies/Hudson1990.lean`).

The Fragments → Theory edge here is a known layer-discipline shortcut:
the binding-substrate API is lexicon-dependent and only English has a
lexicon implementation so far. A future refactor should hoist the
classification API to `Features/Binding` (theory-neutral) with per-language
Fragments providing instances; the test-word lexemes should move to
`Studies/Hudson1990.lean`.

## Main declarations

* `BindingClass`, `isNominalCat`, `classifyNominal` — re-exported. φ-agreement
  is `Word.Agree` (Core), not re-exported here.
* `john`, `mary`, `they`, `sees`, `see`, `himself`, `herself`,
  `themselves`, `him`, `her`, `them`, `eachOther` — English test words.
-/

namespace DepGrammar.Nominal

export Features (BindingClass)
export English.NominalClassification (isNominalCat classifyNominal)

/-! ### Shared English test words

Consumed by `Studies/Hudson1990.lean`. Slated for relocation to that file
in a follow-up cleanup (auditor finding 2026-06-01). -/

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
