import Linglib.Theories.HPSG.Basic

/-!
# Lexical Rules in HPSG

Formalization of valence-changing lexical rules in HPSG.

Müller (2013, §1) argues that valence-changing operations (passive,
resultative, causative) are best analyzed as *lexical rules* — operations
that transform a sign's valence (subj/comps lists) while preserving its
head features. This is the HPSG tradition from Pollard & Sag (1987, 1994).

## Key types

- `LexicalRule` — a transformation on a sign's valence
- `passiveRule` — promotes object to subject, optionally adds `by`-PP
- `resultativeRule` — adds a result-predicate argument

## Key theorems

- `passive_preserves_head`: passive doesn't change head features
- `passive_changes_valence`: passive modifies the argument structure

## References

- Pollard, C. & Sag, I. (1987). Information-Based Syntax and Semantics. Vol. 1.
- Pollard, C. & Sag, I. (1994). Head-Driven Phrase Structure Grammar.
- Müller, S. (2013). Unifying Everything. Language 89(4):920–950.
-/

namespace HPSG

/-! ## Lexical Rule infrastructure -/

/-- A lexical rule transforms a sign's valence while preserving head features.

Lexical rules operate on the *lexical entry* before it enters the syntax.
They capture generalizations about argument structure alternations
(passive, dative shift, resultative, etc.). -/
structure LexicalRule where
  /-- Name of the rule -/
  name : String
  /-- Transform the valence (subj + comps) -/
  transformVal : Valence → Valence
  /-- Lexical rules preserve head features (Müller's key claim) -/
  preservesHead : Bool := true

/-- Apply a lexical rule to a sign, producing a new sign with
transformed valence and preserved head features. -/
def applyLexRule (rule : LexicalRule) : Sign → Sign
  | .word w ss =>
    .word w { ss with val := rule.transformVal ss.val }
  | .phrase children ss =>
    .phrase children { ss with val := rule.transformVal ss.val }

/-! ## Specific lexical rules -/

/-- Passive lexical rule (Pollard & Sag 1987, 1994).

Passive promotes the first complement (direct object) to subject position
and optionally adds a `by`-PP to the complement list.

Input:  `SUBJ ⟨NP⟩, COMPS ⟨NP, ...⟩`
Output: `SUBJ ⟨NP⟩, COMPS ⟨(PP_by), ...⟩` -/
def passiveRule : LexicalRule :=
  { name := "passive"
  , transformVal := λ val =>
      match val.comps with
      | obj :: rest =>
        { subj := [obj]           -- promote object to subject
        , comps := rest }         -- remaining complements
      | [] => val                 -- intransitives: no change
  , preservesHead := true }

/-- Resultative lexical rule.

Adds a result predicate argument (AP or PP) to the complement list.

Input:  `SUBJ ⟨NP⟩, COMPS ⟨NP⟩`  (e.g., "hammer the metal")
Output: `SUBJ ⟨NP⟩, COMPS ⟨NP, AP⟩` (e.g., "hammer the metal flat") -/
def resultativeRule : LexicalRule :=
  { name := "resultative"
  , transformVal := λ val =>
      { val with comps := val.comps ++ [Cat.Adj] }  -- add result predicate slot
  , preservesHead := true }

/-- Dative shift lexical rule.

Transforms prepositional dative to double object construction.

Input:  `SUBJ ⟨NP⟩, COMPS ⟨NP, PP_to⟩` (e.g., "give a book to Mary")
Output: `SUBJ ⟨NP⟩, COMPS ⟨NP, NP⟩`   (e.g., "give Mary a book") -/
def dativeShiftRule : LexicalRule :=
  { name := "dative-shift"
  , transformVal := λ val =>
      match val.comps with
      | [theme, _] => { val with comps := [theme, Cat.N] }  -- replace PP with NP goal
      | _ => val
  , preservesHead := true }

/-! ## Key theorems -/

/-- Passive preserves head features (Müller's argument for lexical rules).

The passive operation changes argument structure but not the category
or head features of the verb. This is why Müller argues passive is
lexical rather than phrasal: it doesn't change what projects. -/
theorem passive_preserves_head (s : Sign) :
    (applyLexRule passiveRule s).synsem.head = s.synsem.head := by
  cases s with
  | word w ss => simp [applyLexRule, Sign.synsem]
  | phrase children ss => simp [applyLexRule, Sign.synsem]

/-- Passive changes the valence (specifically, the subject list).

For a transitive verb, passive promotes the object to subject position. -/
theorem passive_changes_valence_transitive (w : Word) (head : HeadFeatures)
    (subjCat objCat : Cat) (rest : List Cat) :
    let ss : Synsem := { cat := Cat.V, head := head, val := { subj := [subjCat], comps := objCat :: rest } }
    let s := Sign.word w ss
    (applyLexRule passiveRule s).synsem.val.subj = [objCat] := by
  simp [applyLexRule, Sign.synsem, passiveRule]

/-- Head features are preserved by all standard lexical rules. -/
theorem resultative_preserves_head (s : Sign) :
    (applyLexRule resultativeRule s).synsem.head = s.synsem.head := by
  cases s with
  | word w ss => simp [applyLexRule, Sign.synsem]
  | phrase children ss => simp [applyLexRule, Sign.synsem]

/-- Two signs derived from the same base by the same rule share a category.

This supports Müller's coordination argument: passivized verbs can
coordinate because they share a category (both are V). -/
theorem same_rule_same_cat (rule : LexicalRule) (s1 s2 : Sign)
    (h : s1.synsem.cat = s2.synsem.cat) :
    (applyLexRule rule s1).synsem.cat = (applyLexRule rule s2).synsem.cat := by
  cases s1 with
  | word w1 ss1 =>
    cases s2 with
    | word w2 ss2 => simp [applyLexRule, Sign.synsem] at h ⊢; exact h
    | phrase ch2 ss2 => simp [applyLexRule, Sign.synsem] at h ⊢; exact h
  | phrase ch1 ss1 =>
    cases s2 with
    | word w2 ss2 => simp [applyLexRule, Sign.synsem] at h ⊢; exact h
    | phrase ch2 ss2 => simp [applyLexRule, Sign.synsem] at h ⊢; exact h

end HPSG
