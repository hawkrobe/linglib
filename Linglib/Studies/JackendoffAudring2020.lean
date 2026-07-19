/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Construction.Sister
import Linglib.Morphology.Construction.SameExcept
import Linglib.Morphology.Construction.Inheritance
import Linglib.Morphology.Paradigm.Linkage
import Linglib.Morphology.Paradigm.Morphome
import Linglib.Core.Order.Flat

/-!
# Relational Morphology: the sister-schema engine and its divergences
[jackendoff-audring-2020]

[jackendoff-audring-2020]'s Relational Morphology explicates morphological
motivation as *shared structure* recorded by nondirectional relational links,
rather than by directed inheritance. This file instantiates the
`Morphology/Construction/` substrate as that engine and states its three
divergences from rival accounts, each verified against the book.

The linked-variable coindices `α` (phonology) and `β` (semantics) of the
`[X-ism]`/`[X-ist]` sister schemas are rendered as a shared coindex space; the
English and German verb paradigms use the syncretism (`Setoid.ker`) and ablaut
(`SameExcept`) substrate. The **Same Verb** flagship lifts
`Linkage.realize_eq_of_corr_eq_lexeme`: two lexemes sharing a morphosyntactic-form
correspondent inflect alike, evading the lexical-index accounts of
[spencer-2013]. The **cycle** flagship instantiates `Hierarchy.parent_asymm`:
Objection 10's `assassin`/`assassinate`, whose form and meaning planes demand
opposite parent orientations, cannot both be edges of one acyclic hierarchy,
while a symmetric sister link carries both by construction.

## Main results

* `behaviorism_pairs`, `trumpism_pairs` — the `[X-ism]`/`[X-ist]` sister schema
  and its open-endedness, as `Sister.Pairs` on linked coindices
* `walk_syncretisms`, `spricht_morphome` — English and German verb syncretisms /
  the morphomic 2/3-sg-present pattern via `syncretismClass`
* `singSang_contrast`, `stringStrung_contrast`, `ablaut_generality` — ablaut
  classes as `SameExcept` contrasts at the nucleus, under the general schema
* `draw_same_verb`, `ring_wring_distinct` — the Same Verb flagship and its
  homophony negative control
* `assassin_cycle`, `assassin_sister_pairs` — the cycle flagship: inheritance
  forces a 2-cycle where a sister link does not
-/

namespace JackendoffAudring2020

open Morphology Morphology.Construction

/-- The linked-variable coindices of [jackendoff-audring-2020]'s sister schemas:
`alpha` the phonological link, `beta` the semantic link. -/
inductive Coindex | alpha | beta
  deriving DecidableEq, Fintype

/-! ### Sister schemas: `[X-ism]` and `[X-ist]`

[jackendoff-audring-2020] §4.8.2, formalizing the second-order schema
[booij-2010] observed: a noun in `-ism` denoting an ideology is paired with a
noun in `-ist` denoting an adherent, correlated on the shared phonological base
(coindex `α`) and the shared ideology (coindex `β`). The relation is stated once
between the schemas and holds of every attested pair, and is open-ended — a new
ideology (`Trumpism`) has its adherents (`Trumpists`) without hesitation. -/

/-- Phonological bases and ideology values the `-ism`/`-ist` schemas range over. -/
inductive Sym | behavior | commun | trump | behaviorismSem | communismSem | trumpismSem
  deriving DecidableEq, Fintype

/-- The two variables of the `-ism` schema: a phonological base and an ideology. -/
inductive IsmVar | base | ideology
  deriving DecidableEq, Fintype

/-- The two variables of the `-ist` schema. -/
inductive IstVar | base | ideology
  deriving DecidableEq, Fintype

def ismCoindex : IsmVar → Coindex
  | .base => .alpha
  | .ideology => .beta

def istCoindex : IstVar → Coindex
  | .base => .alpha
  | .ideology => .beta

def ismSchema : Schema IsmVar (Flat Sym) := ⟨fun _ => ⊥, Set.univ⟩

def istSchema : Schema IstVar (Flat Sym) := ⟨fun _ => ⊥, Set.univ⟩

/-- The `[X-ism]`/`[X-ist]` sister schema: variables sharing a coindex are linked. -/
def ismistSister : Sister IsmVar IstVar (Flat Sym) where
  fst := ismSchema
  snd := istSchema
  link v₁ v₂ := ismCoindex v₁ = istCoindex v₂

def behaviorismW : IsmVar → Flat Sym
  | .base => ↑Sym.behavior
  | .ideology => ↑Sym.behaviorismSem

def behavioristW : IstVar → Flat Sym
  | .base => ↑Sym.behavior
  | .ideology => ↑Sym.behaviorismSem

def trumpismW : IsmVar → Flat Sym
  | .base => ↑Sym.trump
  | .ideology => ↑Sym.trumpismSem

def trumpistW : IstVar → Flat Sym
  | .base => ↑Sym.trump
  | .ideology => ↑Sym.trumpismSem

/-- `behaviorism`/`behaviorist` is a paired instantiation of the sister schema:
both share the base phonology (`α`) and the ideology (`β`) — the attested pair
`(44a)`. -/
theorem behaviorism_pairs : ismistSister.Pairs behaviorismW behavioristW := by
  refine ⟨fun _ => bot_le, fun _ => bot_le, ?_⟩
  intro v₁ v₂ hlink
  cases v₁ <;> cases v₂ <;>
    simp_all [ismistSister, ismCoindex, istCoindex, behaviorismW, behavioristW]

/-- The relation is open-ended: `Trumpism`/`Trumpist` pairs by the same schema
with no listed precedent (§4.8.2). -/
theorem trumpism_pairs : ismistSister.Pairs trumpismW trumpistW := by
  refine ⟨fun _ => bot_le, fun _ => bot_le, ?_⟩
  intro v₁ v₂ hlink
  cases v₁ <;> cases v₂ <;>
    simp_all [ismistSister, ismCoindex, istCoindex, trumpismW, trumpistW]

/-! ### English and German verb syncretisms

The English verb repertoire `(16)` is six cells. For `walk`, present equals
infinitive (bare stem) and past equals past participle (`-ed`): these are
*syncretisms* ([jackendoff-audring-2020]: "We would like the grammar to express
these syncretisms"), coincidences in the realization map read off `syncretismClass`
(`Setoid.ker`). The German present-tense `2/3-sg` stem ablaut (`spricht`) is a
*morphome* ([aronoff-1994]): the cells it groups do not form a natural class. -/

/-- The six English finite/nonfinite verb cells `(16)`. -/
inductive VCell | pres | pres3sg | past | inf | prespt | ptcp
  deriving DecidableEq, Fintype

/-- The phonological reflex of `walk` in each cell: bare stem, `-s`, `-ed`, `-ing`. -/
inductive VForm | bare | s | ed | ing
  deriving DecidableEq

/-- `walk`'s realization `(19)`: present and infinitive are bare, past and past
participle both `-ed`. -/
def walkForm : VCell → VForm
  | .pres => .bare
  | .inf => .bare
  | .pres3sg => .s
  | .past => .ed
  | .ptcp => .ed
  | .prespt => .ing

/-- `walk`'s two syncretisms: present with infinitive, past with past participle;
present and past are not syncretic. -/
theorem walk_syncretisms :
    VCell.inf ∈ syncretismClass walkForm .pres ∧
    VCell.ptcp ∈ syncretismClass walkForm .past ∧
    VCell.past ∉ syncretismClass walkForm .pres :=
  ⟨rfl, rfl, fun h => absurd h (show walkForm .past ≠ walkForm .pres by decide)⟩

/-- The six present-tense person/number cells of a German strong verb. -/
inductive GCell | s1 | s2 | s3 | p1 | p2 | p3
  deriving DecidableEq, Fintype

/-- The present-tense stem vowel of `sprechen`: the special ablauted `/ɪ/` in
`2/3-sg`, the default `/ɛ/` elsewhere `(43)`, `(45)`. -/
inductive GVowel | eLax | iLax
  deriving DecidableEq

def sprechenStemVowel : GCell → GVowel
  | .s2 => .iLax
  | .s3 => .iLax
  | _ => .eLax

/-- The morphomic `2/3-sg`-present pattern: `2-sg` and `3-sg` share the special
stem vowel, and `1-sg` does not — the cells group as a class with no natural
(feature-conjunction) characterization ([aronoff-1994]). -/
theorem spricht_morphome :
    GCell.s3 ∈ syncretismClass sprechenStemVowel .s2 ∧
    GCell.s1 ∉ syncretismClass sprechenStemVowel .s2 :=
  ⟨rfl, fun h => absurd h (show sprechenStemVowel .s1 ≠ sprechenStemVowel .s2 by decide)⟩

/-! ### Ablaut as same-except contrast

Table 5.1's ablaut classes are `SameExcept` contrasts at the syllabic nucleus: a
stem and its past tense are phonologically identical except for the nucleus
vowel. Over the vowel tier (only the nucleus bears a vowel), the `sing`/`sang`
pattern (ten verbs) and the `string`/`strung` pattern (thirteen) are contrasts;
the German `singen`/`sang`/`gesungen` three-sister (eighteen members) is a pair
of nucleus contrasts. The general ablaut schema `(25)` leaves the nucleus an open
variable, and the `sing`/`sang` subschema `(26)` instantiates it. -/

/-- The nucleus vowels the ablaut classes use: `sing` `/ɪ/`, `sang` `/æ/`,
`sung`/`strung` `/ʌ/`, German past `/a/`. -/
inductive Vowel | iLax | ae | uh | ah
  deriving DecidableEq, Fintype

/-- Syllable positions: only the nucleus carries a vowel on this tier. -/
inductive Pos | onset | nucleus | coda
  deriving DecidableEq, Fintype

/-- The vowel melody of a monosyllable: the vowel at the nucleus, `⊥` elsewhere. -/
def melody (v : Vowel) : Pos → Flat Vowel
  | .nucleus => ↑v
  | _ => ⊥

/-- Two melodies differing only in their nucleus vowel are a nucleus contrast. -/
theorem melody_contrast {v w : Vowel} (h : v ≠ w) :
    Contrast (melody v) (melody w) {Pos.nucleus} := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hp
    cases p <;> simp_all [melody]
  · simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨by simp [melody], by simp [melody], fun hh => h (Flat.coe_injective hh)⟩

/-- `sing`/`sang`: identical except at the nucleus (`/ɪ/` vs `/æ/`) — a contrast. -/
theorem singSang_contrast : Contrast (melody .iLax) (melody .ae) {Pos.nucleus} :=
  melody_contrast (by decide)

/-- `string`/`strung`: identical except at the nucleus (`/ɪ/` vs `/ʌ/`). -/
theorem stringStrung_contrast : Contrast (melody .iLax) (melody .uh) {Pos.nucleus} :=
  melody_contrast (by decide)

/-- German `singen`/`sang`/`gesungen`: the three sisters differ pairwise only at
the nucleus (`/ɪ/`, `/a/`, the back-vowel `/ʌ/`). -/
theorem singen_three_sister :
    Contrast (melody .iLax) (melody .ah) {Pos.nucleus} ∧
    Contrast (melody .ah) (melody .uh) {Pos.nucleus} :=
  ⟨melody_contrast (by decide), melody_contrast (by decide)⟩

/-- The general ablaut schema `(25)`: the nucleus is an open variable, all
positions otherwise unconstrained. -/
def ablautSchema : Schema Pos (Flat Vowel) where
  body := fun _ => ⊥
  opens := {Pos.nucleus}

/-- The `sing`/`sang` subschema `(26)` instantiates the general ablaut schema
`(25)`: the general schema's open nucleus is filled by `/ɪ/`. -/
theorem ablaut_generality : ablautSchema.Instantiates (melody .iLax) := by
  intro _; exact bot_le

/-! ### The Same Verb flagship

[jackendoff-audring-2020] §5.6: many verbs share an irregular paradigm across
distinct meanings — `draw` a picture and `draw` praise both have past `drew` —
where lexical-index accounts ([spencer-2013]) individuate every item. RM shares a
single morphosyntactic-form correspondent (the pivot; phonology is derived
through the shared morphosyntax↔phonology link), and one lift covers both the
containment case (`take`/`took part`) and the sister case (the two `draw`s
differing only in semantics). J&A flag "three (perhaps minor) issues" with the
index account (idioms, profligacy, mentalistic construal), not a knockdown
objection. The negative control is homophony without shared paradigm:
`ring`/`wring`/`ringed` are distinct verbs whose correspondents differ. -/

/-- The `draw` readings and the homophonous `ring`/`wring`. -/
inductive DrawLex | drawPicture | drawElicit | ring | wring
  deriving DecidableEq, Fintype

/-- The form correspondents: the two `draw`s share one, `ring` and `wring` differ. -/
inductive DrawStem | drawZ | ringZ | wringZ
  deriving DecidableEq, Fintype

inductive Tense | pres | past
  deriving DecidableEq, Fintype

/-- The paradigm linkage: both `draw` readings select the same stem, so they share
every correspondent; `ring` and `wring` select distinct stems. -/
def drawLinkage : Linkage DrawLex DrawStem Tense where
  stem
    | .drawPicture, _ => some .drawZ
    | .drawElicit, _ => some .drawZ
    | .ring, _ => some .ringZ
    | .wring, _ => some .wringZ
  pm := fun _ σ => σ

/-- **Same Verb**: the two `draw` readings, sharing a form correspondent, realize
identically at every cell — `drew` is forced, whatever their distinct semantics.
Instantiates `Linkage.realize_eq_of_corr_eq_lexeme`. -/
theorem draw_same_verb {W : Type*} (rf : DrawStem → Tense → W) (σ : Tense) :
    drawLinkage.realize rf .drawPicture σ = drawLinkage.realize rf .drawElicit σ :=
  drawLinkage.realize_eq_of_corr_eq_lexeme rf rfl

/-- The negative control: `ring` and `wring` are homophonous but have distinct
correspondents, so nothing forces a shared past — `rang` vs `wrung`. -/
theorem ring_wring_distinct :
    drawLinkage.corr .ring .past ≠ drawLinkage.corr .wring .past := by decide

/-! ### The cycle flagship: inheritance vs relational linking

[jackendoff-audring-2020]'s Objection 10 (§3.4.4): in pairs like
`assassin`/`assassinate`, the form plane builds the second on the first
(`assassinate` from `assassin`), while the meaning plane builds the first on the
second (an assassin is one who assassinates). "`assassin` is both 'above' and
'below' `assassinate`." Demanding a single directed inheritance relation realize
both orientations forces a 2-cycle, refuted by `Hierarchy.parent_asymm` (the
well-foundedness rendering is ours; the above-and-below paradox is J&A's). The
symmetric sister link carries both plane-links by construction, nondirectionally
— the divergence runs the other way from the default-override win of
[booij-2010]'s `werkbaar`. -/

/-- The mixed-direction pair. -/
inductive AsPair | assassin | assassinate
  deriving DecidableEq, Fintype

/-- **Cycle**: no acyclic hierarchy realizes both orientation demands. The form
plane demands `assassinate`'s parent be `assassin`; the meaning plane demands
`assassin`'s parent be `assassinate`; together they are a 2-cycle. -/
theorem assassin_cycle (h : Hierarchy AsPair)
    (hform : h.parent .assassinate = some .assassin)
    (hmean : h.parent .assassin = some .assassinate) : False :=
  h.parent_asymm hform hmean

/-- The two variables of a lexical entry that a sister link relates: phonological
base (`α`) and semantics (`β`). -/
inductive AsVar | phon | sem
  deriving DecidableEq, Fintype

def asCoindex : AsVar → Coindex
  | .phon => .alpha
  | .sem => .beta

/-- The shared material of the `assassin`/`assassinate` entries `(41)`. -/
inductive AsAtom | asasin | murderSem
  deriving DecidableEq, Fintype

def asSchema : Schema AsVar (Flat AsAtom) := ⟨fun _ => ⊥, Set.univ⟩

/-- The symmetric sister link between `assassin` and `assassinate`: they share the
phonological base (`α`) and part of the semantics (`β`), neither derived from the
other. -/
def assassinSister : Sister AsVar AsVar (Flat AsAtom) where
  fst := asSchema
  snd := asSchema
  link v₁ v₂ := asCoindex v₁ = asCoindex v₂

def assassinW : AsVar → Flat AsAtom
  | .phon => ↑AsAtom.asasin
  | .sem => ↑AsAtom.murderSem

def assassinateW : AsVar → Flat AsAtom
  | .phon => ↑AsAtom.asasin
  | .sem => ↑AsAtom.murderSem

/-- The sister link satisfies both plane-demands at once — the shared base and
shared semantics — where the directed hierarchy could not. -/
theorem assassin_sister_pairs : assassinSister.Pairs assassinW assassinateW := by
  refine ⟨fun _ => bot_le, fun _ => bot_le, ?_⟩
  intro v₁ v₂ hlink
  cases v₁ <;> cases v₂ <;>
    simp_all [assassinSister, asCoindex, assassinW, assassinateW]

/-- Nondirectionality: the sister relation reads the same transposed, so neither
member is "the base". -/
theorem assassin_sister_symm : assassinSister.swap.Pairs assassinateW assassinW :=
  Sister.pairs_swap.mpr assassin_sister_pairs

/-! ### Storage versus computation, and scope (prose)

**Storage vs computation.** [jackendoff-audring-2020] treat a paradigm as stored
schemas that operate nondirectionally, so no form is uniformly "derived" — a
lexical-strength gradient plays the role a rule/computation weight plays in
probabilistic grammars ([odonnell-2015]). No Lean content follows without a
concrete measure, so this stays prose.

**Scope.** The rival-framings above are [jackendoff-audring-2020]'s own claims,
stated as theirs: that inheritance cannot state horizontal links is contested in
the DATR literature. `Word.Term`'s ordered constructors and RM's order-free
morphosyntax (§4.7) are latent rivals — a documented stance difference, changing
nothing. RM independently vindicates the no-zero-morphs analysis (§4.3
double-coindexation): the past tense and infinitive of `walk` add no phonological
content, coindexed to the base rather than to a zero affix — a convergence noted
here, not in `Morph.lean`. -/

end JackendoffAudring2020
