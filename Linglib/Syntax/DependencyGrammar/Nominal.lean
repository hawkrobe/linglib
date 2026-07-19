import Linglib.Data.UD.Basic
import Linglib.Features.CoreferenceStatus
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# Shared English test words for DG coreference theories

A small bundle of English test words consumed by paper-anchored Studies
(`Studies/Hudson1990.lean`), plus a `BindingClass` re-export. Binding-class
classification is no longer re-exported here: a word's Principle A/B/C class is read
off its own UD morphology by the framework- and language-neutral `Binding.bindingClassOf`,
so no per-language lexicon classifier is needed.

## Main declarations

* `BindingClass` — re-exported. φ-agreement is `Word.Agree` (Core).
* `john`, `mary`, `they`, `sees`, `see`, `himself`, `herself`,
  `themselves`, `him`, `her`, `them`, `eachOther` — English test words.
  Slated for relocation to `Studies/Hudson1990.lean` (auditor finding 2026-06-01).
-/

namespace DepGrammar.Nominal


export Features (BindingClass)

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
