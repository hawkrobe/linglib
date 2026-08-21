import Linglib.Morphology.Realization
import Linglib.Morphology.Morphotactics.CVTemplate
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Fragments.Hebrew.ConsonantalRoots
import Linglib.Data.Examples.Arad2005
import Mathlib.Data.List.Destutter
import Mathlib.Tactic.DeriveFintype

/-!
# Arad 2005: binyanim as the spell-out of v and Voice, and the locality of
root interpretation
[arad-2005]

The seven verbal patterns are five CV templates with vowel slots but no
vowels (her (24b)) — CVCVC, nVCCVC, CVCCVC, hVCCVC, hitCVCCVC — inserted
under v and associated with the root by the book's subscripts
(C₁iC₂C₂eC₃, her (3)); the vowels are the exponent of Voice, a
morphosyntactic feature that must be spelled out, by the rule (25) whose
context is the binyan v received — contextual allomorphy on the exponent of
the next head in. Nominal patterns carry their vowels (her (24a)), which is
her noun–verb asymmetry: a verb needs the template for Voice to have slots
to fill. §2.5 is formalized below as `Binyan`, `voiceSpellout`, and
`verb`, reproducing the seven forms of (3).

The √sgr family (her (5) in Ch. 7): one root, six listed formations across
verbal and nominal patterns — *sagar* 'close', *hisgir* 'extradite',
*histager* 'cocoon oneself', *seger* 'closure', *sograyim* 'parentheses',
*misgeret* 'frame'. Multiple Contextualized Meaning is allosemy of the root
across patterns (`sgr_mcm`); the √qlt nominal table (her (28) in Ch. 3) is
the second witness (`qlt_mcm`).

The lexeme grain and the root grain are related by arrows, not identity: no
strict hom merges any two of the lexemes into any target — their contextwise
interpretations clash (`no_strict_merger`) — but the six root-derived
lexemes lax-merge into the root's Encyclopedia entry
(`direct_lax_merger`): family, not identity.

**The denominal verb *misger*** 'to frame' (her (6)) is derived from the
noun *misgeret*, not from the root: no lax hom carries the full lexicon into
the root's entry, because *misger* is not among the root's own realizations
in any pattern (`misger_blocked`) — her interference argument. Its meaning
is instead the compositional image of the noun's (`misger_locality`), while
the root-derived lexemes' meanings are unanalyzable atoms
(`root_derived_atomic`) — her locality constraint (8) in Ch. 7: roots are
assigned an interpretation at the first category-assigning head, and the
interpretation is carried along thereafter.

## Main results

* `table3_derived` — the forms of (3) from v's binyan and Voice's vowels by
  (25).
* `voice_obligatory`, `active_many_to_one` — every binyan has an active
  vocalism, the passive ones only CVCCVC and hVCCVC; one feature, five
  exponents.
* `binyanim_vowel_slots`, `mishqalim_no_vowel_slots` — the asymmetry (24).
* `sgr_mcm`, `qlt_mcm` — Multiple Contextualized Meaning as root allosemy.
* `no_strict_merger` — no two sgr-lexemes strict-merge into any target.
* `direct_lax_merger` — the root-derived lexemes lax-merge into the root.
* `misger_blocked` — the denominal verb blocks a lax merger of the full
  lexicon: it is not a realization of the root.
* `misger_locality`, `root_derived_atomic` — word-derived meaning is the
  compositional image of the base noun's; root-derived meanings are atoms.
-/

namespace Arad2005

open Morphology Morphology.Realization DistributedMorphology Data.Examples

/-! ### Binyanim as the spell-out of v and Voice (§2.5) -/

/-- A position of a pattern skeleton in the book's subscripted notation: a
root radical by index, an open vowel slot, or a fixed segment. -/
inductive Skel where
  | radical (i : ℕ)
  | vowel
  | fixed (s : String) (slot : CVSlot)
  deriving DecidableEq, Repr

/-- A fixed vowel of a pattern. -/
def Skel.isFixedVowel : Skel → Bool
  | .fixed _ .V => true
  | _ => false

/-- The template slot a skeleton position occupies. -/
def Skel.slot : Skel → CVSlot
  | .radical _ => .C
  | .vowel => .V
  | .fixed _ c => c

/-- The five binyan templates ((24b)): vowel slots without vowels, the
prefixes *n-*, *h-*, *hit-*, and in CVCCVC the geminate slot of the middle
radical. -/
inductive Binyan where
  | cvcvc
  | nvccvc
  | cvccvc
  | hvccvc
  | hitcvccvc
  deriving DecidableEq, Repr, Fintype

/-- The skeletons of (3) and (24b). -/
def Binyan.skeleton : Binyan → List Skel
  | .cvcvc => [.radical 0, .vowel, .radical 1, .vowel, .radical 2]
  | .nvccvc => [.fixed "n" .C, .vowel, .radical 0, .radical 1, .vowel, .radical 2]
  | .cvccvc => [.radical 0, .vowel, .radical 1, .radical 1, .vowel, .radical 2]
  | .hvccvc => [.fixed "h" .C, .vowel, .radical 0, .radical 1, .vowel, .radical 2]
  | .hitcvccvc =>
    [.fixed "h" .C, .fixed "i" .V, .fixed "t" .C, .radical 0, .vowel, .radical 1, .radical 1,
      .vowel, .radical 2]

/-- Nominal patterns carry their vowels ((24a)). -/
def mishqalim : List (List Skel) :=
  [[.fixed "m" .C, .fixed "i" .V, .radical 0, .radical 1, .fixed "a" .V, .radical 2],
    [.fixed "m" .C, .fixed "i" .V, .radical 0, .radical 1, .fixed "o" .V, .radical 2],
    [.fixed "m" .C, .fixed "a" .V, .radical 0, .radical 1, .fixed "e" .V, .radical 2],
    [.fixed "t" .C, .fixed "a" .V, .radical 0, .radical 1, .fixed "i" .V, .radical 2],
    [.radical 0, .radical 1, .fixed "a" .V, .radical 2],
    [.radical 0, .fixed "a" .V, .radical 1, .fixed "i" .V, .radical 2]]

/-- The association lines a skeleton dictates: radicals and fixed segments at
their positions, vowels left to right into the vowel slots. -/
def Skel.associations : List Skel → ℕ → ℕ → ℕ → List Association
  | [], _, _, _ => []
  | .radical k :: rest, i, nv, nf => ⟨.root, k, i⟩ :: associations rest (i + 1) nv nf
  | .vowel :: rest, i, nv, nf => ⟨.vocalism, nv, i⟩ :: associations rest (i + 1) (nv + 1) nf
  | .fixed _ _ :: rest, i, nv, nf => ⟨.affix, nf, i⟩ :: associations rest (i + 1) nv (nf + 1)

/-- Fill a skeleton with a root and a vocalism: association by the subscripts. -/
def fill (sk : List Skel) (r : ConsonantalRoot String) (voc : List String) :
    TemplateMatch String where
  root := r
  vocalism := voc
  affix := sk.filterMap fun | .fixed s _ => some s | _ => none
  template := ⟨sk.map Skel.slot⟩
  associations := Skel.associations sk 0 0 0

/-- The features of Voice and of the v exponent it sees. -/
inductive VoiceFeature where
  | active
  | passive
  | binyan (b : Binyan)
  deriving DecidableEq, Repr

/-- The Voice spell-out (25): a vocalism in the context of the binyan inserted
under v. -/
def voiceSpellout : List (VocabularyItem VoiceFeature (List String)) :=
  [⟨⟨[.active], [[.binyan .cvcvc]], []⟩, ["a", "a"]⟩,
    ⟨⟨[.active], [[.binyan .nvccvc]], []⟩, ["i", "a"]⟩,
    ⟨⟨[.active], [[.binyan .cvccvc]], []⟩, ["i", "e"]⟩,
    ⟨⟨[.active], [[.binyan .hvccvc]], []⟩, ["i", "i"]⟩,
    ⟨⟨[.active], [[.binyan .hitcvccvc]], []⟩, ["a", "e"]⟩,
    ⟨⟨[.passive], [[.binyan .cvccvc]], []⟩, ["u", "a"]⟩,
    ⟨⟨[.passive], [[.binyan .hvccvc]], []⟩, ["u", "a"]⟩]

/-- The Voice node once v has been realized: its feature, with the binyan as
the inner neighbor. -/
def voiceNode (b : Binyan) (active : Bool) : Neighborhood (List VoiceFeature) :=
  ⟨[if active then .active else .passive], [[.binyan b]], []⟩

/-- The surface string, with Modern Hebrew degemination. -/
def surface (m : TemplateMatch String) : String := String.join (m.spellout.destutter (· ≠ ·))

/-- A verb: the binyan under v, Voice's vowels by (25) in its context, the
root associated by the skeleton. `none` where Voice has no exponent. -/
def verb (r : ConsonantalRoot String) (b : Binyan) (active : Bool) : Option String :=
  (subsetPrinciple voiceSpellout (voiceNode b active)).map fun voc =>
    surface (fill b.skeleton r voc)

def Binyan.ofLabel : String → Option Binyan
  | "cvcvc" => some .cvcvc
  | "nvccvc" => some .nvccvc
  | "cvccvc" => some .cvccvc
  | "hvccvc" => some .hvccvc
  | "hitcvccvc" => some .hitcvccvc
  | _ => none

def rootOfLabel : String → Option (ConsonantalRoot String)
  | "lmd" => some Hebrew.lmd
  | "spr" => some Hebrew.spr
  | "qlt" => some Hebrew.qlt
  | "pll" => some Hebrew.pll
  | _ => none

/-- The seven forms of (3): root, binyan, Voice value, and form. -/
def table3 : List (ConsonantalRoot String × Binyan × Bool × String) :=
  Examples.all.filterMap fun ex => do
    let r ← ex.feature? "root" >>= rootOfLabel
    let b ← ex.feature? "binyan" >>= Binyan.ofLabel
    let v ← ex.feature? "voice"
    pure (r, b, v = "active", ex.primaryText)

theorem table3_length : table3.length = 7 := by decide

/-- The forms of (3) are derived: the binyan under v, Voice's vowels in the
binyan's context, degemination at the surface. -/
theorem table3_derived : ∀ t ∈ table3, verb t.1 t.2.1 t.2.2.1 = some t.2.2.2 := by decide

/-- Voice must be spelled out ((22a)): every binyan has an active vocalism,
and a passive one exactly in CVCCVC and hVCCVC. -/
theorem voice_obligatory :
    (∀ b : Binyan, (subsetPrinciple voiceSpellout (voiceNode b true)).isSome) ∧
      ∀ b : Binyan, (subsetPrinciple voiceSpellout (voiceNode b false)).isSome ↔
        (b = .cvccvc ∨ b = .hvccvc) := by
  decide

/-- One feature, five exponents: [+active] is realized five ways, the choice
fixed by the binyan ((25)). -/
theorem active_many_to_one :
    ((voiceSpellout.filter (·.site.focus = [.active])).map (·.exponent)).Nodup ∧
      (voiceSpellout.filter (·.site.focus = [.active])).length = 5 := by
  decide

/-- Every binyan has two vowel slots and no vowels of its own; the prefix of
hitCVCCVC is its only fixed vowel ((24b)). -/
theorem binyanim_vowel_slots :
    ∀ b : Binyan, b.skeleton.count .vowel = 2 ∧
      ∀ p ∈ b.skeleton, p.isFixedVowel → b = .hitcvccvc := by
  decide

/-- Nominal patterns have no vowel slots: their vowels are their own ((24a)). -/
theorem mishqalim_no_vowel_slots : ∀ p ∈ mishqalim, p.count .vowel = 0 := by decide

/-! ### The √sgr family -/

/-- The patterns of the √sgr family ((5)), plus the denominal verb pattern
CiCCeC of (6). -/
inductive Pattern
  | caCaC | hiCCiC | hitCaCCeC | ceCeC | coCCayim | miCCeCet | ciCCeC
  deriving DecidableEq, Fintype, Repr

/-- Meanings: the root-derived listed atoms of (5), plus the compositional
layer `vOf m` — 'to do something with an m' — for word-derived verbs. -/
inductive Meaning
  | close | extradite | cocoonOneself | closure | parentheses | frame
  | vOf (m : Meaning)
  deriving DecidableEq, Repr

/-- The seven lexemes: the six root-derived formations of (5) and the
noun-derived *misger* of (6). -/
inductive SgrLex
  | sagar | hisgir | histager | seger | sograyim | misgeret | misger
  deriving DecidableEq, Fintype, Repr

/-- The single root. -/
inductive Sqrt | sgr
  deriving DecidableEq, Fintype, Repr

/-- Each lexeme's home pattern. -/
def SgrLex.pattern : SgrLex → Pattern
  | .sagar => .caCaC | .hisgir => .hiCCiC | .histager => .hitCaCCeC
  | .seger => .ceCeC | .sograyim => .coCCayim | .misgeret => .miCCeCet
  | .misger => .ciCCeC

/-- Each lexeme's form. -/
def SgrLex.form : SgrLex → String
  | .sagar => "sagar" | .hisgir => "hisgir" | .histager => "histager"
  | .seger => "seger" | .sograyim => "sograyim" | .misgeret => "misgeret"
  | .misger => "misger"

/-- Each lexeme's meaning: listed atoms for the root-derived six, the
compositional 'to frame' for the noun-derived verb. -/
def SgrLex.meaning : SgrLex → Meaning
  | .sagar => .close | .hisgir => .extradite | .histager => .cocoonOneself
  | .seger => .closure | .sograyim => .parentheses | .misgeret => .frame
  | .misger => .vOf .frame

/-- The lexeme-grain system: each lexeme licensed in its home pattern
only. -/
def sgrLexemes : Realization.Interpreted SgrLex Pattern String Meaning where
  realize := fun l c => if c = l.pattern then {l.form} else ∅
  interp := fun l c => if c = l.pattern then {l.meaning} else ∅

/-- The root-grain system: √sgr's own Encyclopedia entry ((5)) — the six
direct cells. The denominal pattern CiCCeC is empty: the root has no
root-derived formation there. -/
def sgrRoot : Realization.Interpreted Sqrt Pattern String Meaning where
  realize := fun _ c =>
    match c with
    | .caCaC => {"sagar"} | .hiCCiC => {"hisgir"}
    | .hitCaCCeC => {"histager"} | .ceCeC => {"seger"}
    | .coCCayim => {"sograyim"} | .miCCeCet => {"misgeret"}
    | .ciCCeC => ∅
  interp := fun _ c =>
    match c with
    | .caCaC => {.close} | .hiCCiC => {.extradite}
    | .hitCaCCeC => {.cocoonOneself} | .ceCeC => {.closure}
    | .coCCayim => {.parentheses} | .miCCeCet => {.frame}
    | .ciCCeC => ∅

/-- Multiple Contextualized Meaning is root allosemy: √sgr's interpretation
varies across patterns. -/
theorem sgr_mcm : sgrRoot.IsAllosemous .sgr := by decide

/-! ### Grain arrows -/

private theorem interp_clash :
    ∀ l l' : SgrLex, l ≠ l' →
      sgrLexemes.interp l l.pattern ≠ sgrLexemes.interp l' l.pattern := by
  decide

/-- No strict hom into any target merges two distinct sgr-lexemes: their
contextwise interpretations clash at the home cell
(`Interpreted.Hom.interp_eq_of_onRoot_eq`). At the lexeme grain, all seven
are genuinely distinct indices. -/
theorem no_strict_merger {R₂ C₂ : Type*}
    {T : Realization.Interpreted R₂ C₂ String Meaning}
    (φ : Realization.Interpreted.Hom sgrLexemes T) {l l' : SgrLex}
    (h : l ≠ l') : φ.onRoot l ≠ φ.onRoot l' :=
  fun he => interp_clash l l' h (φ.interp_eq_of_onRoot_eq he l.pattern)

/-- The root-derived sublexicon of (5). -/
inductive Direct | sagar | hisgir | histager | seger | sograyim | misgeret
  deriving DecidableEq, Fintype, Repr

/-- The inclusion into the full lexicon. -/
def Direct.toSgr : Direct → SgrLex
  | .sagar => .sagar | .hisgir => .hisgir | .histager => .histager
  | .seger => .seger | .sograyim => .sograyim | .misgeret => .misgeret

/-- The lexeme grain restricted to the root-derived six. -/
def sgrDirect : Realization.Interpreted Direct Pattern String Meaning where
  realize := fun l c => sgrLexemes.realize l.toSgr c
  interp := fun l c => sgrLexemes.interp l.toSgr c

/-- The six root-derived lexemes lax-merge into the root's Encyclopedia
entry: each one's form and meaning are among the root's, at its own pattern.
Family membership without identity — the lexeme→√ coarsening arrow. -/
theorem direct_lax_merger :
    Nonempty (Realization.Interpreted.LaxHom sgrDirect sgrRoot) :=
  ⟨⟨fun _ => .sgr, id, by decide, by decide⟩⟩

/-- **The denominal verb blocks the merger** (her interference argument): no
lax hom carries the full lexicon into the root's entry, because *misger* is
not among √sgr's realizations in any pattern — it enters the family only
through the noun *misgeret*. -/
theorem misger_blocked
    (φ : Realization.Interpreted.LaxHom sgrLexemes sgrRoot) : False := by
  have h := φ.realize_sub .misger .ciCCeC
  cases hr : φ.onRoot .misger
  cases hc : φ.onCtx .ciCCeC <;> rw [hr, hc] at h <;>
    revert h <;> decide

/-! ### Locality ((8)): assigned at first categorization, carried along -/

/-- *misger*'s meaning is the compositional image of *misgeret*'s — 'to X'
applied to the noun's fixed interpretation, per the locality constraint: the
interpretation assigned at the noun's categorization is carried along into
the denominal verb. -/
theorem misger_locality :
    sgrLexemes.interp .misger Pattern.ciCCeC
      = (sgrLexemes.interp .misgeret Pattern.miCCeCet).image Meaning.vOf := by
  decide

private def Meaning.isDerived : Meaning → Bool
  | .vOf _ => true
  | _ => false

/-- Root-derived meanings are unanalyzable atoms: none is the compositional
image of another formation's meaning — they are listed against the root,
fixed at first categorization. -/
theorem root_derived_atomic :
    ∀ l : SgrLex, l ≠ .misger → ∀ c,
      ∀ m ∈ sgrLexemes.interp l c, m.isDerived = false := by
  decide

/-! ### The √qlt witness ((28), (61b)) -/

/-- √qlt's nominal patterns ((28)) and its two verbal patterns ((61b)). -/
inductive QPattern
  | ceCeC | maCCeC | miCCaC | taCCiC | caCeCet | p1 | p5
  deriving DecidableEq, Fintype, Repr

/-- √qlt's listed meanings: *qelet* 'input', *maqlet* 'receiver', *miqlat*
'shelter, asylum', *taqlit* '(vinyl) record', *qaletet* 'cassette', *qalat*
'absorb', *hiqlit* 'record'. -/
inductive QMeaning
  | input | receiver | shelter | vinylRecord | cassette | absorb | recordV
  deriving DecidableEq, Fintype, Repr

/-- The single root. -/
inductive QSqrt | qlt
  deriving DecidableEq, Fintype, Repr

/-- √qlt's Encyclopedia entry across its seven attested patterns. -/
def qltRoot : Realization.Interpreted QSqrt QPattern String QMeaning where
  realize := fun _ c =>
    match c with
    | .ceCeC => {"qelet"} | .maCCeC => {"maqlet"} | .miCCaC => {"miqlat"}
    | .taCCiC => {"taqlit"} | .caCeCet => {"qaletet"}
    | .p1 => {"qalat"} | .p5 => {"hiqlit"}
  interp := fun _ c =>
    match c with
    | .ceCeC => {.input} | .maCCeC => {.receiver} | .miCCaC => {.shelter}
    | .taCCiC => {.vinylRecord} | .caCeCet => {.cassette}
    | .p1 => {.absorb} | .p5 => {.recordV}

/-- The √qlt table is a second MCM witness: seven patterns, seven listed
meanings — root allosemy at scale. -/
theorem qlt_mcm : qltRoot.IsAllosemous .qlt := by decide

end Arad2005
