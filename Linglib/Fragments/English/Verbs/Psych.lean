module

public import Linglib.Fragments.English.Verbs.Attitude

/-!
# English psychological verbs

This file defines the English psychological and agent–patient verbs of Solstad and Bott's
study: the agent-experiencer verbs *enjoy*, *like*, *love*, *hate* and their kin, the
stimulus-experiencer verbs *frighten*, *amuse*, *fascinate* and the rest, and the agent-patient
verbs of contact and motion, *chase*, *hit*, *push*, *pull* and their kin.

## References

* [levin-1993]
* [levin-2026]
* [solstad-bott-2024]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree
open English.Inflection

/-! ### Agent-experiencer verbs ([solstad-bott-2024]) -/

/-! [levin-1993] class 31.2 (admire). Subject = experiencer, object = stimulus.
    NP1 (subject) IC bias. -/

/-- "enjoy" — AgExp verb (experiencer-subject) -/
def enjoy : Verb := .mkRegular {
  form := "enjoy"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "like" — AgExp verb (experiencer-subject) -/
def like : Verb := .mkRegular {
  form := "like"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "love" — AgExp verb (experiencer-subject) -/
def love : Verb := .mkRegular {
  form := "love"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "hate" — AgExp verb (experiencer-subject) -/
def hate : Verb := .mkRegular {
  form := "hate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "admire" — AgExp verb (experiencer-subject) -/
def admire : Verb := .mkRegular {
  form := "admire"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "envy" — AgExp verb (experiencer-subject).
    DOC-only ditransitive ("He envies me the car"). Implicit goal is
    definite (familiar). Implicit second obj is indefinite. -/
def envy : Verb := .mkRegular {
  form := "envy"
  frames := [ArgumentFrame.np, ArgumentFrame.np_np,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "respect" — AgExp verb (experiencer-subject) -/
def respect : Verb := .mkRegular {
  form := "respect"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "value" — AgExp verb (experiencer-subject) -/
def value : Verb := .mkRegular {
  form := "value"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire, .characterize, .price} }

/-- "fear" (NP complement) — Class I psych verb (B&R *temere*).
    "John fears snakes." Experiencer subject, stimulus object.
    Note: `fear` (attitude verb, clausal complement) is defined separately. -/
def fear_np : Verb := .mkRegular {
  form := "fear"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire, .marvel} }

/-- "dread" (NP complement) — Class I psych verb.
    "John dreads exams." Note: `dread` (attitude, clausal) defined separately. -/
def dread_np : Verb := .mkRegular {
  form := "dread"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-! ### Stimulus-experiencer verbs ([solstad-bott-2024]) -/

/-! [levin-1993] class 31.1 (amuse). Subject = stimulus, object = experiencer.
    NP2 (object) IC bias. -/

/-- "frighten" — StimExp verb (stimulus subject). -/
def frighten : Verb := .mkRegular {
  form := "frighten"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "amuse" — StimExp verb (stimulus subject). -/
def amuse : Verb := .mkRegular {
  form := "amuse"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "fascinate" — StimExp verb (stimulus subject). -/
def fascinate : Verb := .mkRegular {
  form := "fascinate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "irritate" — StimExp verb (stimulus subject). -/
def irritate : Verb := .mkRegular {
  form := "irritate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "annoy" — StimExp verb (stimulus subject). -/
def annoy : Verb := .mkRegular {
  form := "annoy"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "bore" — StimExp verb (stimulus subject). -/
def bore : Verb := .mkRegular {
  form := "bore"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse, .carve, .rummage} }

/-- "charm" — StimExp verb (stimulus subject). -/
def charm : Verb := .mkRegular {
  form := "charm"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "impress" — StimExp verb (stimulus subject). -/
def impress : Verb := .mkRegular {
  form := "impress"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "concern" — stative Class II psych verb. -/
def concern : Verb := .mkRegular {
  form := "concern"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.amuse} }

/-- "interest" — stative Class II psych verb. -/
def interest : Verb := .mkRegular {
  form := "interest"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.amuse} }

/-- "surprise" — eventive Class II (Levin 31.1). "The news surprised John." -/
def surprise : Verb := .mkRegular {
  form := "surprise"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "scare" — eventive Class II (Levin 31.1). "The noise scared John." -/
def scare : Verb := .mkRegular {
  form := "scare"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "delight" — eventive Class II (Levin 31.1). "The gift delighted Mary." -/
def delight : Verb := .mkRegular {
  form := "delight"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse, .marvel} }

/-- "embarrass" — eventive Class II (Levin 31.1). "The remark embarrassed John." -/
def embarrass : Verb := .mkRegular {
  form := "embarrass"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "upset" — eventive Class II (Levin 31.1). "The news upset Mary." -/
def upset_psych : Verb := .mkRegular {
  form := "upset"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "disgust" — eventive Class II (Levin 31.1). "The smell disgusted John." -/
def disgust : Verb := .mkRegular {
  form := "disgust"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "shock" — eventive Class II (Levin 31.1). "The revelation shocked everyone." -/
def shock : Verb := .mkRegular {
  form := "shock"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "confuse" — eventive Class II (Levin 31.1). "The instructions confused John." -/
def confuse : Verb := .mkRegular {
  form := "confuse"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amalgamate, .amuse} }

/-- "disappoint" — eventive Class II (Levin 31.1). "The result disappointed Mary." -/
def disappoint : Verb := .mkRegular {
  form := "disappoint"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "worry" (eventive) — Class II. "The noise worried John."
    Note: `worry` (attitude, clausal) defined separately. -/
def worry_eventive : Verb := .mkRegular {
  form := "worry"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "worry" (stative) — Class II. "The situation worries John." -/
def worry_stative : Verb := .mkRegular {
  form := "worry"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.amuse} }

/-- "please" — stative Class II. "The idea pleases John." Related to B&R Class III It.
    *piacere*. -/
def please_psych : Verb := .mkRegular {
  form := "please"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.amuse} }

/-- "trouble" — stative Class II. "The thought troubles John." -/
def trouble : Verb := .mkRegular {
  form := "trouble"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.amuse} }

/-- "puzzle" — stative Class II. "The problem puzzles John." -/
def puzzle : Verb := .mkRegular {
  form := "puzzle"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.amuse, .marvel} }

/-! ### Agent-patient verbs ([solstad-bott-2024]) -/

/-! Agent-patient verbs with full agentive subjects. NP1 IC bias (default).
    "kick" already defined above. -/

/-- "chase" — AgPat verb (Levin 51.6) -/
def chase : Verb := .mkRegular {
  form := "chase"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.chase} }

/-- "hit" — AgPat verb (Levin 18.1) -/
def hit : Verb where
  form := "hit"
  form3sg := "hits"
  formPast := "hit"
  formPastPart := "hit"
  formPresPart := "hitting"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.contiguousLocation, .hit, .nonAgentiveImpact, .throw}

/-- "push" — AgPat verb (Levin 12) -/
def push : Verb := .mkRegular {
  form := "push"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.carry, .funnel, .pushPull, .split} }

/-- "pull" — AgPat verb (Levin 12) -/
def pull : Verb := .mkRegular {
  form := "pull"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.carry, .get, .hurt, .pushPull, .split} }

/-- "shove" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def shove : Verb := .mkRegular {
  form := "shove"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.carry, .pushPull, .split, .throw} }

/-- "tug" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def tug : Verb where
  form := "tug"
  form3sg := "tugs"
  formPast := "tugged"
  formPastPart := "tugged"
  formPresPart := "tugging"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.carry, .pushPull, .split}

/-- "yank" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def yank : Verb := .mkRegular {
  form := "yank"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.pushPull, .split} }

/-- "jerk" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def jerk : Verb := .mkRegular {
  form := "jerk"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.pushPull} }

/-- "wrench" — verb of exerting force for [levin-2026] (31); not among the
    members of Levin's §12. -/
def wrench : Verb := .mkRegular {
  form := "wrench"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClasses := {LevinClass.remove} }


/-- "fling" — Levin 17.1 Throw verbs; a verb of exerting force for
    [levin-2026] (31). Irregular past. -/
def fling : Verb where
  form := "fling"
  form3sg := "flings"
  formPast := "flung"
  formPastPart := "flung"
  formPresPart := "flinging"
  frames := [ArgumentFrame.np, ArgumentFrame.np_np, ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.throw}

/-- "slam" — Levin 17.1 Throw verbs; a hitting verb for [levin-2026] (32a).
    Irregular doubling. -/
def slam : Verb where
  form := "slam"
  form3sg := "slams"
  formPast := "slammed"
  formPastPart := "slammed"
  formPresPart := "slamming"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.to_), ArgumentFrame.np_np]
  vendlerClass := some .activity
  levinClasses := {LevinClass.nonAgentiveImpact, .throw}

/-- "punch" — Levin 18.2 Swat verbs; a hitting verb for [levin-2026] (32a). -/
def punch : Verb := .mkRegular {
  form := "punch"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.carve, .swat} }

/-- "smack" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def smack : Verb := .mkRegular {
  form := "smack"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.crane, .hit} }

/-- "thump" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def thump : Verb := .mkRegular {
  form := "thump"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.hit, .soundEmission} }

/-- "bang" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def bang : Verb := .mkRegular {
  form := "bang"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.funnel, .hit, .nonAgentiveImpact, .soundEmission} }

/-- "thrash" — Levin 18.3 Spank verbs; a hitting verb for [levin-2026] (32a). -/
def thrash : Verb := .mkRegular {
  form := "thrash"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.on)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.spank} }

/-- "hammer" — Levin 18.1 Hit verbs. -/
def hammer : Verb := .mkRegular {
  form := "hammer"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.build, .funnel, .hit} }

/-- "scrape" — verb of surface contact, wiping (Levin 10.4,
    [levin-2026] (32b)). In intr-push-open, enters through
    surface-contact sense, not removing sense. -/
def scrape : Verb := .mkRegular {
  form := "scrape"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.objectDrop (some .indef),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.cut, .funnel, .wipeManner} }

/-- "wipe" — Levin 10.4 Wipe verbs, manner subclass. -/
def wipe : Verb := .mkRegular {
  form := "wipe"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.objectDrop (some .indef),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.funnel, .wipeManner} }

/-- "carry" — AgPat verb (Levin 11.4) -/
def carry : Verb where
  form := "carry"
  form3sg := "carries"
  formPast := "carried"
  formPastPart := "carried"
  formPresPart := "carrying"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.to_), ArgumentFrame.np_np]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.carry, .cost, .fit}

/-- "drag" — AgPat verb (Levin 11.4/12) -/
def drag : Verb where
  form := "drag"
  form3sg := "drags"
  formPast := "dragged"
  formPastPart := "dragged"
  formPresPart := "dragging"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.to_), ArgumentFrame.np_np]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.carry, .search}

/-- "call" — AgPat verb (communication + agent-patient frame) -/
def call : Verb := .mkRegular {
  form := "call"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .dub, .get, .mannerOfSpeaking} }

end English.Verbs
