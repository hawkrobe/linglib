import Linglib.Data.Examples.Schema

/-!
# `CondoravdiLauer2016` — typed example data

Auto-generated from `Linglib/Data/Examples/CondoravdiLauer2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace CondoravdiLauer2016.Examples`.
-/

namespace CondoravdiLauer2016.Examples

open Data.Examples

def cl2016_2_intend : LinguisticExample :=
  { id := "cl2016_2_intend"
    source := ⟨"condoravdi-lauer-2016", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you intend to go to Harlem, you should / have to take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you intend to go to Harlem, you should / have to take the A train."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "harlemBase"), ("desirePredicate", "intend")]
    comment := "Intend-variant of (1); supports the paper's argument that the antecedent need not be want — any intention-related predicate works."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_3_plan : LinguisticExample :=
  { id := "cl2016_3_plan"
    source := ⟨"condoravdi-lauer-2016", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you are planning to go to Harlem, you should / have to take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you are planning to go to Harlem, you should / have to take the A train."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "harlemBase"), ("desirePredicate", "plan")]
    comment := "Plan-variant of (1)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_4_goal : LinguisticExample :=
  { id := "cl2016_4_goal"
    source := ⟨"condoravdi-lauer-2016", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If your goal is to go to Harlem, you should / have to take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If your goal is to go to Harlem, you should / have to take the A train."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "harlemBase"), ("desirePredicate", "goal")]
    comment := "Goal-variant of (1). Together with (2)-(3), shows the antecedent desire-predicate is not lexically privileged."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_5_chocolate : LinguisticExample :=
  { id := "cl2016_5_chocolate"
    source := ⟨"condoravdi-lauer-2016", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to eat chocolate, you should try thinking about something else."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to eat chocolate, you should try thinking about something else."
    context := "Advice to avoid eating chocolate."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nonAnankasticAntecedent"), ("reading", "mere-desire")]
    comment := "Non-anankastic if-want conditional. Same surface form as (1) but conveys NOT 'thinking-about-something-else is necessary for chocolate' — it's advice to avoid. Shows surface form does not determine anankasticity; want gets a mere-desire construal here (paper § 7.2.1, formalized as cl2016_5_chocolate in the chocolate-LF contrast)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_19_chess : LinguisticExample :=
  { id := "cl2016_19_chess"
    source := ⟨"condoravdi-lauer-2016", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(In view of what he wants,) John should resign the game. / (In view of what he wants,) John should not resign the game."
    discourseSegments := ["(In view of what he wants,) John should resign the game.", "(In view of what he wants,) John should not resign the game."]
    glossedTokens := []
    translation := "Both readings of 'in view of what he wants, John should/should not resign' are simultaneously felicitous."
    context := "John is far superior chess player, but Bill is good enough to draw out the game; John hates resigning to inferior players but it is 3am and he needs to sleep. The only way to end quickly is to resign; the only way to win is to keep playing."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "interactingPreferences"), ("modalForce", "unconditionalNec")]
    comment := "Interacting-preferences scenario: unconditional necessity statements (a)/(b) are jointly inconsistent, but the corresponding conditionals (20) can be jointly true. Shows preferences must be resolved differently in conditional vs unconditional cases."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_20_chess_conditional : LinguisticExample :=
  { id := "cl2016_20_chess_conditional"
    source := ⟨"condoravdi-lauer-2016", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John wants to go to bed, he should resign. / If John wants to win the game, he should not resign."
    discourseSegments := ["If John wants to go to bed, he should resign.", "If John wants to win the game, he should not resign."]
    glossedTokens := []
    translation := "Both conditionals true simultaneously."
    context := "Same chess scenario as (19)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "interactingPreferences"), ("modalForce", "conditionalNec")]
    comment := "Conditionalized version of (19); both conditionals can be true even though their unconditional counterparts cannot. Tests interacting-preferences resolution."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_28_invite : LinguisticExample :=
  { id := "cl2016_28_invite"
    source := ⟨"condoravdi-lauer-2016", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to invite everyone to the dinner, your table has to seat at least 20 people."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to invite everyone to the dinner, your table has to seat at least 20 people."
    context := "There are at least 20 people to be invited."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("relationType", "precondition")]
    comment := "Near-anankastic: conveys precondition (seating 20+ is necessary FOR being able to seat everyone) rather than means-of. Used to argue the analysis must generalize beyond means-of."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_29a_vaccine_safe : LinguisticExample :=
  { id := "cl2016_29a_vaccine_safe"
    source := ⟨"condoravdi-lauer-2016", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to travel to that place, you should / must get a vaccine to be safe."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to travel to that place, you should / must get a vaccine to be safe."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("relationType", "strengthened-goal")]
    comment := "Near-anankastic with overt purpose clause 'to be safe'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_29b_vaccine : LinguisticExample :=
  { id := "cl2016_29b_vaccine"
    source := ⟨"condoravdi-lauer-2016", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to travel to that place, you should / must get a vaccine."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to travel to that place, you should / must get a vaccire."
    context := "Getting a vaccine is a precondition for safe travel, not for travel per se."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("relationType", "implicit-strengthened-goal")]
    comment := "Near-anankastic without overt purpose clause; the strengthened goal (safe travel) must be supplied by context. Paper argues Huitink's strong-antecedent analysis predicts this false on its strongest reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_31_disneyworld : LinguisticExample :=
  { id := "cl2016_31_disneyworld"
    source := ⟨"condoravdi-lauer-2016", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to Disneyworld, you must / should spend at least five days there."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to go to Disneyworld, you must / should spend at least five days there."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("relationType", "teleological-consequence")]
    comment := "Near-anankastic about teleological CONSEQUENCES: spending five days is a consequence of (optimally) going to Disneyworld, not a precondition. Raises the same compositionality problem as canonical anankastics."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_38_exemption : LinguisticExample :=
  { id := "cl2016_38_exemption"
    source := ⟨"condoravdi-lauer-2016", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to use the exemption now, you must / will have to pay more taxes next year."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to use the exemption now, you must / will have to pay more taxes next year."
    context := "Tax law: using the exemption now triggers higher liability later."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("modalType", "deontic")]
    comment := "Near-anankastic with DEONTIC inner modal (rather than teleological). Conveys: actually taking the exemption forces higher taxes — not that wanting it does. The vacuity-of-want is contingent on the actualization assumption (paper § 7.2.2)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_39a_disaster : LinguisticExample :=
  { id := "cl2016_39a_disaster"
    source := ⟨"condoravdi-lauer-2016", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to the disaster area, you should go there quickly."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to go to the disaster area, you should go there quickly."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("relationType", "what-kind-of")]
    comment := "'What-kind-of' near-anankastic: the prejacent ENTAILS the antecedent goal (going-quickly entails going). Tests against purpose-clause analyses that can't paraphrase such conditionals."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_40a_dress : LinguisticExample :=
  { id := "cl2016_40a_dress"
    source := ⟨"condoravdi-lauer-2016", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to buy a fancy dress, you should buy a well-made one."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to buy a fancy dress, you should buy a well-made one."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("relationType", "what-kind-of")]
    comment := "'What-kind-of' near-anankastic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_46_neg_letter_grade : LinguisticExample :=
  { id := "cl2016_46_neg_letter_grade"
    source := ⟨"condoravdi-lauer-2016", "(46) (Penka p.c.)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you don't want to get a letter grade for the course, you don't have to take the exam."
    discourseSegments := []
    glossedTokens := []
    translation := "If you don't want to get a letter grade for the course, you don't have to take the exam."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("scope", "negation-over-want")]
    comment := "Negation in the antecedent: scopes over want (= 'absence of preference'), not over the complement. Tests that want interacts with embedding operators normally. Defeats 'vacuous want' analyses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_52_picnic_hiking : LinguisticExample :=
  { id := "cl2016_52_picnic_hiking"
    source := ⟨"condoravdi-lauer-2016", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I want it to rain tomorrow so the picnic gets canceled, but I (also) want it to be sunny tomorrow so I can go hiking."
    discourseSegments := []
    glossedTokens := []
    translation := "I want it to rain tomorrow so the picnic gets canceled, but I (also) want it to be sunny tomorrow so I can go hiking."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "conjunctionIntroduction"), ("reading", "mere-desire")]
    comment := "Levinson-style example: two incompatible wants coherently asserted. Argues mere-desire reading of want (not effective-preference) does not validate Conjunction Introduction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_55_chess_incompat : LinguisticExample :=
  { id := "cl2016_55_chess_incompat"
    source := ⟨"condoravdi-lauer-2016", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John intends to move in with his girlfriend, but he also intends to keep living alone."
    discourseSegments := []
    glossedTokens := []
    translation := "John intends to move in with his girlfriend, but he also intends to keep living alone."
    context := ""
    judgment := .questionable
    alternatives := [("John would like to move in with his girlfriend, but he would also like to keep living alone. He can't make up his mind.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "conjunctionIntroduction"), ("reading", "effective-preference")]
    comment := "Intend-variant of (53). The intend-version sounds contradictory / attributes irrationality; the would-like-to variant (alternative) is coherent. Argues intend = effective preference is subject to a consistency constraint that mere desires lack."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_61_concorde : LinguisticExample :=
  { id := "cl2016_61_concorde"
    source := ⟨"asher-1987", "p. 225"⟩
    reportedIn := some ⟨"condoravdi-lauer-2016", "(62) / via Levinson 2003"⟩
    language := "stan1293"
    primaryText := "Nicholas wants to take a free trip on the Concorde. / Nicholas wants to take a trip on the Concorde."
    discourseSegments := ["Nicholas wants to take a free trip on the Concorde.", "Nicholas wants to take a trip on the Concorde."]
    glossedTokens := []
    translation := "First sentence true (free trip would be great), second false (paying would be financial ruin)."
    context := "Paying for a Concorde trip would mean financial ruin for Nicholas; a free trip would be very welcome."
    judgment := .acceptable
    alternatives := []
    readings := [("upward-entailment-fails", .acceptable)]
    paperFeatures := [("puzzle", "upwardEntailment"), ("reading", "effective-preference")]
    comment := "Tests Upward Entailment for want. Asher/Levinson claim (a) true but (b) false despite the entailment; C&L argue (b) can be true on a sub-property reading (Condoravdi et al. 2001, Zimmermann 2006 — quantification over sub-concepts)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_63_poodle_dog : LinguisticExample :=
  { id := "cl2016_63_poodle_dog"
    source := ⟨"condoravdi-lauer-2016", "(63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wants to get a poodle, so he wants to get a dog."
    discourseSegments := []
    glossedTokens := []
    translation := "John wants to get a poodle, so he wants to get a dog."
    context := ""
    judgment := .acceptable
    alternatives := [("John wants to get a dog. So he would be happy to get a poodle.", .questionable)]
    readings := []
    paperFeatures := [("puzzle", "upwardEntailment")]
    comment := "Upward Entailment for want: poodle-getting entails dog-getting; the inference goes through. Pair with the alternative (which goes the wrong direction) to show want is UE not DE."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_82a_dog_tax : LinguisticExample :=
  { id := "cl2016_82a_dog_tax"
    source := ⟨"condoravdi-lauer-2016", "(82a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John gets a dog, he will have to pay more taxes."
    discourseSegments := []
    glossedTokens := []
    translation := "If John gets a dog, he will have to pay more taxes."
    context := "Dog owners pay a special tax; service dogs for the blind are exempt; John's eyesight is currently perfect and he has no dog."
    judgment := .acceptable
    alternatives := [("But if John loses his eyesight and gets a dog, he will not have to pay more taxes.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "defeasibleObligation"), ("modalType", "deontic")]
    comment := "Defeasible obligation pair. Both true on the double-modal analysis (outer NEC restricts to typical worlds where John keeps his eyesight; inner MUST quantifies over best worlds in those). Argues for stereotypical outer ordering source on overt deontic modals."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_92_vladivostok : LinguisticExample :=
  { id := "cl2016_92_vladivostok"
    source := ⟨"vonstechow-krasikova-penka-2006", "p. 168"⟩
    reportedIn := some ⟨"condoravdi-lauer-2016", "(92)"⟩
    language := "stan1293"
    primaryText := "If you want to go to Vladivostok, you have to take the Chinese train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to go to Vladivostok, you have to take the Chinese train."
    context := "Two trains go to Vladivostok, one Russian and one Chinese; the Chinese is much more comfortable. Addressee has a salient preference for comfort."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "compatibleSecondaryPreference")]
    comment := "Conditional anankastic with a COMPATIBLE secondary preference (comfort) that influences the prediction. Truth depends on whether comfort is taken to be an effective preference; vF&I 2005 report judgment variability — C&L attribute to contextual variability of effective-preference set, not grammatical variability."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_91a_virus_no : LinguisticExample :=
  { id := "cl2016_91a_virus_no"
    source := ⟨"condoravdi-lauer-2016", "(91a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I know John wants to go to Hoboken today, not to Harlem. #But if he wants to go to Harlem today, he has to take the A train."
    discourseSegments := ["I know John wants to go to Hoboken today, not to Harlem.", "But if he wants to go to Harlem today, he has to take the A train."]
    glossedTokens := []
    translation := "Continuation infelicitous when speaker known incompatible preference."
    context := ""
    judgment := .unacceptable
    alternatives := [("But if he wanted to go to Harlem today, he would have to take the A train.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "informationalAsymmetry"), ("mood", "indicative-vs-subjunctive")]
    comment := "Indicative anankastic infelicitous when speaker knows the hypothetical EP is incompatible with actual; subjunctive variant is fine. The paper's evidence that the indicative imposes 'antecedent is epistemically possible' — same constraint as ordinary indicative conditionals."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_112a_inclined_harlem : LinguisticExample :=
  { id := "cl2016_112a_inclined_harlem"
    source := ⟨"vonfintel-iatridou-2005", "(via Weatherson)"⟩
    reportedIn := some ⟨"condoravdi-lauer-2016", "(112c)"⟩
    language := "stan1293"
    primaryText := "If you're inclined to go to Harlem, you have to take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you're inclined to go to Harlem, you have to take the A train."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "weakAntecedent")]
    comment := "Weak antecedent (inclined, would-like-to, etc.). Generally not ananakastic — predicates that can only express mere desires can't target effective preferences. Becomes anankastic only in contexts where the mere desire would be acted on. Originally due to Weatherson (p.c.) via vF&I 2006 slides; here cited from the vF&I 2005 ms-companion."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [cl2016_2_intend, cl2016_3_plan, cl2016_4_goal, cl2016_5_chocolate, cl2016_19_chess, cl2016_20_chess_conditional, cl2016_28_invite, cl2016_29a_vaccine_safe, cl2016_29b_vaccine, cl2016_31_disneyworld, cl2016_38_exemption, cl2016_39a_disaster, cl2016_40a_dress, cl2016_46_neg_letter_grade, cl2016_52_picnic_hiking, cl2016_55_chess_incompat, cl2016_61_concorde, cl2016_63_poodle_dog, cl2016_82a_dog_tax, cl2016_92_vladivostok, cl2016_91a_virus_no, cl2016_112a_inclined_harlem]

end CondoravdiLauer2016.Examples
