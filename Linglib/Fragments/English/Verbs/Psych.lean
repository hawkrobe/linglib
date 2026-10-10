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
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "like" — AgExp verb (experiencer-subject) -/
def like : Verb := .mkRegular {
  form := "like"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "love" — AgExp verb (experiencer-subject) -/
def love : Verb := .mkRegular {
  form := "love"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "hate" — AgExp verb (experiencer-subject) -/
def hate : Verb := .mkRegular {
  form := "hate"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "admire" — AgExp verb (experiencer-subject) -/
def admire : Verb := .mkRegular {
  form := "admire"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "envy" — AgExp verb (experiencer-subject).
    DOC-only ditransitive ("He envies me the car"). Implicit goal is
    definite (familiar). Implicit second obj is indefinite. -/
def envy : Verb := .mkRegular {
  form := "envy"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_np, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 1, 2]),
     (⟨some .nominal, [.implicit (some .def), .nominal]⟩, [0, 1, 2])]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "respect" — AgExp verb (experiencer-subject) -/
def respect : Verb := .mkRegular {
  form := "respect"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "value" — AgExp verb (experiencer-subject) -/
def value : Verb := .mkRegular {
  form := "value"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.admire, .characterize, .price} }

/-- "fear" (NP complement) — Class I psych verb (B&R *temere*).
    "John fears snakes." Experiencer subject, stimulus object.
    Note: `fear` (attitude verb, clausal complement) is defined separately. -/
def fear_np : Verb := .mkRegular {
  form := "fear"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.admire, .marvel} }

/-- "dread" (NP complement) — Class I psych verb.
    "John dreads exams." Note: `dread` (attitude, clausal) defined separately. -/
def dread_np : Verb := .mkRegular {
  form := "dread"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-! ### Stimulus-experiencer verbs ([solstad-bott-2024]) -/

/-! [levin-1993] class 31.1 (amuse). Subject = stimulus, object = experiencer.
    NP2 (object) IC bias. -/

/-- "frighten" — StimExp verb (stimulus subject). -/
def frighten : Verb := .mkRegular {
  form := "frighten"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "amuse" — StimExp verb (stimulus subject). -/
def amuse : Verb := .mkRegular {
  form := "amuse"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "fascinate" — StimExp verb (stimulus subject). -/
def fascinate : Verb := .mkRegular {
  form := "fascinate"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "irritate" — StimExp verb (stimulus subject). -/
def irritate : Verb := .mkRegular {
  form := "irritate"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "annoy" — StimExp verb (stimulus subject). -/
def annoy : Verb := .mkRegular {
  form := "annoy"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "bore" — StimExp verb (stimulus subject). -/
def bore : Verb := .mkRegular {
  form := "bore"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse, .carve, .rummage} }

/-- "charm" — StimExp verb (stimulus subject). -/
def charm : Verb := .mkRegular {
  form := "charm"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "impress" — StimExp verb (stimulus subject). -/
def impress : Verb := .mkRegular {
  form := "impress"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "concern" — stative Class II psych verb. -/
def concern : Verb := .mkRegular {
  form := "concern"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.amuse} }

/-- "interest" — stative Class II psych verb. -/
def interest : Verb := .mkRegular {
  form := "interest"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.amuse} }

/-- "surprise" — eventive Class II (Levin 31.1). "The news surprised John." -/
def surprise : Verb := .mkRegular {
  form := "surprise"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "scare" — eventive Class II (Levin 31.1). "The noise scared John." -/
def scare : Verb := .mkRegular {
  form := "scare"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "delight" — eventive Class II (Levin 31.1). "The gift delighted Mary." -/
def delight : Verb := .mkRegular {
  form := "delight"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse, .marvel} }

/-- "embarrass" — eventive Class II (Levin 31.1). "The remark embarrassed John." -/
def embarrass : Verb := .mkRegular {
  form := "embarrass"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "upset" — eventive Class II (Levin 31.1). "The news upset Mary." -/
def upset_psych : Verb := .mkRegular {
  form := "upset"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "disgust" — eventive Class II (Levin 31.1). "The smell disgusted John." -/
def disgust : Verb := .mkRegular {
  form := "disgust"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "shock" — eventive Class II (Levin 31.1). "The revelation shocked everyone." -/
def shock : Verb := .mkRegular {
  form := "shock"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "confuse" — eventive Class II (Levin 31.1). "The instructions confused John." -/
def confuse : Verb := .mkRegular {
  form := "confuse"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amalgamate, .amuse} }

/-- "disappoint" — eventive Class II (Levin 31.1). "The result disappointed Mary." -/
def disappoint : Verb := .mkRegular {
  form := "disappoint"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse} }

/-- "worry" (eventive) — Class II. "The noise worried John."
    Note: `worry` (attitude, clausal) defined separately. -/
def worry_eventive : Verb := .mkRegular {
  form := "worry"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse}
  levinExcluded := {LevinClass.marvel} }

/-- "worry" (stative) — Class II. "The situation worries John." -/
def worry_stative : Verb := .mkRegular {
  form := "worry"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.amuse}
  levinExcluded := {LevinClass.marvel} }

/-- "please" — stative Class II. "The idea pleases John." Related to B&R Class III It.
    *piacere*. -/
def please_psych : Verb := .mkRegular {
  form := "please"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.amuse} }

/-- "trouble" — stative Class II. "The thought troubles John." -/
def trouble : Verb := .mkRegular {
  form := "trouble"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.amuse} }

/-- "puzzle" — stative Class II. "The problem puzzles John." -/
def puzzle : Verb := .mkRegular {
  form := "puzzle"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.amuse, .marvel} }

/-! ### Agent-patient verbs ([solstad-bott-2024]) -/

/-! Agent-patient verbs with full agentive subjects. NP1 IC bias (default).
    "kick" already defined above. -/

/-- "chase" — AgPat verb (Levin 51.6) -/
def chase : Verb := .mkRegular {
  form := "chase"
  valency := .ofFrame ArgumentFrame.np
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
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.contiguousLocation, .hit, .nonAgentiveImpact, .throw}

/-- "push" — AgPat verb (Levin 12) -/
def push : Verb := .mkRegular {
  form := "push"
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.pp (some Adpositions.at_), [0, 1])]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.carry, .funnel, .pushPull, .split} }

/-- "pull" — AgPat verb (Levin 12) -/
def pull : Verb := .mkRegular {
  form := "pull"
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.pp (some Adpositions.at_), [0, 1])]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.carry, .get, .hurt, .pushPull, .split} }

/-- "shove" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def shove : Verb := .mkRegular {
  form := "shove"
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.pp (some Adpositions.at_), [0, 1])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.carry, .pushPull, .split, .throw} }

/-- "tug" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def tug : Verb where
  form := "tug"
  form3sg := "tugs"
  formPast := "tugged"
  formPastPart := "tugged"
  formPresPart := "tugging"
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.pp (some Adpositions.at_), [0, 1])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.carry, .pushPull, .split}

/-- "yank" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def yank : Verb := .mkRegular {
  form := "yank"
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.pp (some Adpositions.at_), [0, 1])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.pushPull, .split} }

/-- "jerk" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def jerk : Verb := .mkRegular {
  form := "jerk"
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.pp (some Adpositions.at_), [0, 1])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.pushPull} }

/-- "wrench" — verb of exerting force for [levin-2026] (31); not among the
    members of Levin's §12. -/
def wrench : Verb := .mkRegular {
  form := "wrench"
  valency := .ofFrame ArgumentFrame.np
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
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2])]
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
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.nonAgentiveImpact, .throw}

/-- "punch" — Levin 18.2 Swat verbs; a hitting verb for [levin-2026] (32a). -/
def punch : Verb := .mkRegular {
  form := "punch"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 1, 2])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.carve, .swat} }

/-- "smack" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def smack : Verb := .mkRegular {
  form := "smack"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.crane, .hit} }

/-- "thump" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def thump : Verb := .mkRegular {
  form := "thump"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.hit, .soundEmission} }

/-- "bang" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def bang : Verb := .mkRegular {
  form := "bang"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.funnel, .hit, .nonAgentiveImpact, .soundEmission} }

/-- "thrash" — Levin 18.3 Spank verbs; a hitting verb for [levin-2026] (32a). -/
def thrash : Verb := .mkRegular {
  form := "thrash"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 1, 2])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.spank} }

/-- "hammer" — Levin 18.1 Hit verbs. -/
def hammer : Verb := .mkRegular {
  form := "hammer"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.build, .funnel, .hit} }

/-- "scrape" — verb of surface contact, wiping (Levin 10.4,
    [levin-2026] (32b)). In intr-push-open, enters through
    surface-contact sense, not removing sense. -/
def scrape : Verb := .mkRegular {
  form := "scrape"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.cut, .funnel, .wipeManner} }

/-- "wipe" — Levin 10.4 Wipe verbs, manner subclass. -/
def wipe : Verb := .mkRegular {
  form := "wipe"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.funnel, .wipeManner} }

/-- "carry" — AgPat verb (Levin 11.4) -/
def carry : Verb where
  form := "carry"
  form3sg := "carries"
  formPast := "carried"
  formPastPart := "carried"
  formPresPart := "carrying"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
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
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.carry, .search}

/-- "call" — AgPat verb (communication + agent-patient frame) -/
def call : Verb := .mkRegular {
  form := "call"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .dub, .get, .mannerOfSpeaking} }

end English.Verbs
