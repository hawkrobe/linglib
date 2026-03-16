/-!
# Japanese Passive Types
@cite{jo-seo-2023} @cite{ozaki-2026}

Japanese has two structurally distinct passive constructions that look
superficially similar (both use *-(r)are-*):

- **Direct passive** (*-niyotte* agent): valency-reducing, requires thematic
  Voice. Only available for verbs that project an external argument.
- **Indirect (adversative) passive** (*-ni* agent): introduces a malefactive
  argument. Available for ALL verbs, including unaccusatives and intransitives.

The *niyotte* substitution test distinguishes them: direct passives allow the
dative agent marker *ni* to be replaced with *niyotte*; indirect passives
do not (@cite{jo-seo-2023}).
-/

namespace Fragments.Japanese.Passive

/-- Types of passive in Japanese. -/
inductive PassiveType where
  | direct    -- *-niyotte* agent, requires thematic Voice
  | indirect  -- *-rare-* adversative, available for all verbs
  deriving DecidableEq, BEq, Repr

/-- Direct passive requires thematic Voice (an agentive external argument). -/
def PassiveType.requiresThematicVoice : PassiveType → Bool
  | .direct => true
  | .indirect => false

end Fragments.Japanese.Passive
