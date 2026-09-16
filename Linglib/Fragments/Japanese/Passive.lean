/-!
# Japanese passives

Japanese has two passives in *-(r)are-*. The direct passive reduces valency and needs a verb
with a thematic Voice, one that projects an external argument; its agent may be marked with
*niyotte*. The indirect or adversative passive adds an affected argument and is available for
every verb, unaccusatives included; its agent takes *ni* only, the substitution of *niyotte*
being Jo and Seo's test for the two.

## References

* [jo-seo-2023]
* [ozaki-2026]
-/

namespace Japanese.Passive

/-- The two passives. -/
inductive PassiveType where
  /-- The direct passive, with a *niyotte* agent. -/
  | direct
  /-- The indirect, adversative passive, with a *ni* agent. -/
  | indirect
  deriving DecidableEq, Repr

/-- The direct passive needs a verb with thematic Voice. -/
def PassiveType.RequiresThematicVoice : PassiveType → Prop
  | .direct => True
  | .indirect => False

instance : DecidablePred PassiveType.RequiresThematicVoice := fun t ↦ by
  cases t <;> unfold PassiveType.RequiresThematicVoice <;> infer_instance

end Japanese.Passive
