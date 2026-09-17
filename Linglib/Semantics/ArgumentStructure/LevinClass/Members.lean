import Linglib.Semantics.ArgumentStructure.LevinClass

/-!
# The member lists of the Levin classes

The `Class Members` list of every class page of [levin-1993] Part II, by citation form, and
the classes that list a form (`LevinClass.classesOf`), which is how an English verb entry's
Levin classes are read.

## Implementation notes

The lists are transcribed mechanically from the pages, dropping Levin's question marks on
doubtful members and her parenthetical glosses; a form she lists under several classes is a
member of each.

## References

* [levin-1993]
-/

namespace ArgumentStructure.LevinClass

/-- The class page's member list. -/
def members : LevinClass → List String
  | .put => ["arrange", "immerse", "install", "lodge", "mount", "place", "position", "put", "set",
      "situate", "sling", "stash", "stow"]
  | .putInSpatialConfiguration => ["dangle", "hang", "lay", "lean", "perch", "rest", "sit",
      "stand", "suspend"]
  | .funnel => ["bang", "channel", "dip", "dump", "funnel", "hammer", "ladle", "pound", "push",
      "rake", "ram", "scoop", "scrape", "shake", "shovel", "siphon", "spoon", "squash", "squeeze",
      "squish", "sweep", "tuck", "wad", "wedge", "wipe", "wring"]
  | .putDirection => ["drop", "hoist", "lift", "lower", "raise"]
  | .pour => ["dribble", "drip", "pour", "slop", "slosh", "spew", "spill", "spurt"]
  | .coil => ["coil", "curl", "loop", "roll", "spin", "twirl", "twist", "whirl", "wind"]
  | .sprayLoad => ["brush", "cram", "crowd", "cultivate", "dab", "daub", "drape", "drizzle",
      "dust", "hang", "heap", "inject", "jam", "load", "mound", "pack", "pile", "plant", "plaster",
      "prick", "pump", "rub", "scatter", "seed", "settle", "sew", "shower", "slather", "smear",
      "smudge", "sow", "spatter", "splash", "splatter", "spray", "spread", "sprinkle", "spritz",
      "squirt", "stack", "stick", "stock", "strew", "string", "stuff", "swab", "vest", "wash",
      "wrap"]
  | .fill => ["adorn", "anoint", "bandage", "bathe", "bestrew", "bind", "blanket", "block", "blot",
      "bombard", "carpet", "choke", "cloak", "clog", "clutter", "coat", "contaminate", "cover",
      "dam", "dapple", "deck", "decorate", "deluge", "dirty", "dot", "douse", "drench", "edge",
      "embellish", "emblazon", "encircle", "encrust", "endow", "enrich", "entangle", "face",
      "festoon", "fill", "fleck", "flood", "frame", "garland", "garnish", "imbue", "impregnate",
      "infect", "inlay", "interlace", "interlard", "interleave", "intersperse", "interweave",
      "inundate", "lard", "lash", "line", "litter", "mask", "mottle", "ornament", "pad", "pave",
      "plate", "plug", "pollute", "replenish", "repopulate", "riddle", "ring", "ripple", "robe",
      "saturate", "season", "shroud", "smother", "soak", "soil", "speckle", "splotch", "spot",
      "staff", "stain", "stipple", "stud", "suffuse", "surround", "swaddle", "swathe", "taint",
      "tile", "trim", "veil", "vein", "wreathe"]
  | .butter => ["asphalt", "bait", "blanket", "blindfold", "board", "bread", "brick", "bridle",
      "bronze", "butter", "buttonhole", "cap", "carpet", "caulk", "chrome", "cloak", "cork",
      "crown", "diaper", "drug", "feather", "fence", "flour", "forest", "frame", "fuel", "gag",
      "garland", "glove", "graffiti", "gravel", "grease", "groove", "halter", "harness", "heel",
      "ink", "label", "leash", "leaven", "lipstick", "mantle", "mulch", "muzzle", "nickel", "oil",
      "ornament", "panel", "paper", "parquet", "patch", "pepper", "perfume", "pitch", "plank",
      "plaster", "poison", "polish", "pomade", "poster", "postmark", "powder", "putty", "robe",
      "roof", "rosin", "rouge", "rut", "saddle", "salt", "salve", "sand", "seed", "sequin",
      "shawl", "shingle", "shoe", "shutter", "silver", "slate", "slipcover", "sod", "sole",
      "spice", "stain", "starch", "stopper", "stress", "string", "stucco", "sugar", "sulphur",
      "tag", "tar", "tarmac", "tassel", "thatch", "ticket", "tile", "turf", "veil", "veneer",
      "wallpaper", "water", "wax", "whitewash", "wreathe", "yoke", "zipcode"]
  | .pocket => ["archive", "bag", "bank", "beach", "bed", "bench", "berth", "billet", "bin",
      "bottle", "box", "cage", "can", "case", "cellar", "cloister", "coop", "corral", "crate",
      "dock", "drydock", "file", "fork", "garage", "ground", "hangar", "house", "jail", "jar",
      "jug", "kennel", "land", "lodge", "pasture", "pen", "pillory", "pocket", "pot", "sheathe",
      "shelter", "shelve", "shoulder", "skewer", "snare", "spindle", "spit", "spool", "stable",
      "string", "tin", "trap", "tree", "warehouse"]
  | .remove => ["abstract", "cull", "delete", "discharge", "disengage", "disgorge", "dislodge",
      "dismiss", "draw", "eject", "eliminate", "eradicate", "evict", "excise", "excommunicate",
      "expel", "extirpate", "extract", "extrude", "lop", "omit", "ostracize", "oust", "partition",
      "pry", "reap", "remove", "separate", "sever", "shoo", "subtract", "uproot", "winkle",
      "withdraw", "wrench"]
  | .banish => ["banish", "deport", "evacuate", "expel", "extradite", "recall", "remove"]
  | .clear => ["clean", "clear", "drain", "empty"]
  | .wipeManner => ["bail", "buff", "dab", "distill", "dust", "erase", "expunge", "flush", "leach",
      "lick", "pluck", "polish", "prune", "purge", "rinse", "rub", "scour", "scrape", "scratch",
      "scrub", "shave", "skim", "smooth", "soak", "squeeze", "strain", "strip", "suck", "suction",
      "swab", "sweep", "trim", "wash", "wear", "weed", "whisk", "winnow", "wipe", "wring"]
  | .wipeInstrument => ["brush", "comb", "file", "filter", "hoover", "hose", "iron", "mop", "plow",
      "rake", "sandpaper", "shear", "shovel", "siphon", "sponge", "towel", "vacuum"]
  | .steal => ["abduct", "cadge", "capture", "confiscate", "cop", "emancipate", "embezzle",
      "exorcise", "extort", "extract", "filch", "flog", "grab", "impound", "kidnap", "liberate",
      "lift", "nab", "pilfer", "pinch", "pirate", "plagiarize", "purloin", "reclaim", "recover",
      "redeem", "regain", "repossess", "rescue", "retrieve", "rustle", "seize", "smuggle",
      "snatch", "sneak", "sponge", "steal", "swipe", "take", "thieve", "wangle", "weasel",
      "winkle", "withdraw", "wrest"]
  | .cheat => ["absolve", "acquit", "balk", "bereave", "bilk", "bleed", "break", "burgle", "cheat",
      "cleanse", "con", "cull", "cure", "defraud", "denude", "deplete", "depopulate", "deprive",
      "despoil", "disabuse", "disarm", "disencumber", "dispossess", "divest", "drain", "ease",
      "exonerate", "fleece", "free", "gull", "milk", "mulct", "pardon", "plunder", "purge",
      "purify", "ransack", "relieve", "render", "rid", "rifle", "rob", "sap", "strip", "swindle",
      "unburden", "void", "wean"]
  | .pit => ["bark", "beard", "bone", "burl", "core", "gill", "gut", "head", "hull", "husk",
      "lint", "louse", "milk", "peel", "pinion", "pip", "pit", "pith", "pod", "poll", "pulp",
      "rind", "scale", "scalp", "seed", "shell", "shuck", "skin", "snail", "stalk", "stem",
      "stone", "string", "tail", "tassel", "top", "vein", "weed", "wind", "worm", "zest"]
  | .debone => ["deaccent", "debark", "debone", "debowel", "debug", "debur", "declaw", "defang",
      "defat", "defeather", "deflea", "deflesh", "defoam", "defog", "deforest", "defrost",
      "defuzz", "degas", "degerm", "deglaze", "degrease", "degrit", "degum", "degut", "dehair",
      "dehead", "dehorn", "dehull", "dehusk", "deice", "deink", "delint", "delouse", "deluster",
      "demast", "derat", "derib", "derind", "desalt", "descale", "desex", "desprout", "destarch",
      "destress", "detassel", "detusk", "devein", "dewater", "dewax", "deworm"]
  | .mine => ["mine", "quarry"]
  | .send => ["airmail", "convey", "deliver", "dispatch", "express", "fedex", "forward", "hand",
      "mail", "pass", "port", "post", "return", "send", "shift", "ship", "shunt", "slip",
      "smuggle", "sneak", "transfer", "transport", "ups"]
  | .slide => ["bounce", "float", "move", "roll", "slide"]
  | .bringTake => ["bring", "take"]
  | .carry => ["carry", "drag", "haul", "heave", "heft", "hoist", "kick", "lug", "pull", "push",
      "schlep", "shove", "tote", "tow", "tug"]
  | .drive => ["barge", "bus", "cart", "drive", "ferry", "fly", "row", "shuttle", "truck", "wheel",
      "wire"]
  | .pushPull => ["draw", "heave", "jerk", "press", "pull", "push", "shove", "thrust", "tug",
      "yank"]
  | .give => ["feed", "give", "lease", "lend", "loan", "pass", "pay", "peddle", "refund", "render",
      "rent", "repay", "sell", "serve", "trade"]
  | .contribute => ["administer", "contribute", "disburse", "distribute", "donate", "extend",
      "forfeit", "proffer", "refer", "reimburse", "relinquish", "remit", "restore", "return",
      "sacrifice", "submit", "surrender", "transfer"]
  | .futureHaving => ["advance", "allocate", "allot", "assign", "award", "bequeath", "cede",
      "concede", "extend", "grant", "guarantee", "issue", "leave", "offer", "owe", "promise",
      "vote", "will", "yield"]
  | .fulfilling => ["credit", "entrust", "furnish", "issue", "leave", "present", "provide",
      "serve", "supply", "trust"]
  | .equip => ["arm", "burden", "charge", "compensate", "equip", "invest", "ply", "regale",
      "reward", "saddle"]
  | .get => ["book", "buy", "call", "cash", "catch", "charter", "choose", "earn", "fetch", "find",
      "gain", "gather", "get", "hire", "keep", "lease", "leave", "order", "phone", "pluck",
      "procure", "pull", "reach", "rent", "reserve", "save", "secure", "shoot", "slaughter",
      "steal", "vote", "win"]
  | .obtain => ["accept", "accumulate", "acquire", "appropriate", "borrow", "cadge", "collect",
      "exact", "grab", "inherit", "obtain", "purchase", "receive", "recover", "regain", "retrieve",
      "seize", "select", "snatch"]
  | .exchange => ["barter", "change", "exchange", "substitute", "swap", "trade"]
  | .berry => ["antique", "berry", "birdnest", "blackberry", "clam", "crab", "fish", "fowl",
      "grouse", "hay", "log", "mushroom", "nest", "nut", "oyster", "pearl", "prawn", "rabbit",
      "seal", "shark", "shrimp", "snail", "snipe", "sponge", "whale", "whelk"]
  | .learn => ["acquire", "cram", "glean", "learn", "memorize", "read", "study"]
  | .hold => ["clasp", "clutch", "grasp", "grip", "handle", "hold", "wield"]
  | .keep => ["hoard", "keep", "leave", "store"]
  | .conceal => ["block", "cloister", "conceal", "curtain", "hide", "isolate", "quarantine",
      "screen", "seclude", "sequester", "shelter"]
  | .throw => ["bash", "bat", "bunt", "cast", "catapult", "chuck", "fire", "flick", "fling",
      "flip", "hit", "hurl", "kick", "knock", "lob", "loft", "nudge", "pass", "pitch", "punt",
      "shoot", "shove", "slam", "slap", "sling", "smash", "tap", "throw", "tip", "toss"]
  | .pelt => ["bombard", "buffet", "pelt", "shower", "stone"]
  | .hit => ["bang", "bash", "batter", "beat", "bump", "butt", "dash", "drum", "hammer", "hit",
      "kick", "knock", "lash", "pound", "rap", "slap", "smack", "smash", "strike", "tamp", "tap",
      "thump", "thwack", "whack"]
  | .swat => ["bite", "claw", "paw", "peck", "punch", "scratch", "shoot", "slug", "stab", "swat",
      "swipe"]
  | .spank => ["belt", "birch", "bludgeon", "bonk", "brain", "cane", "clobber", "club", "conk",
      "cosh", "cudgel", "cuff", "flog", "knife", "paddle", "paddywhack", "pummel", "sock", "spank",
      "strap", "thrash", "truncheon", "wallop", "whip", "whisk"]
  | .nonAgentiveImpact => ["bang", "brush", "bump", "crash", "hit", "knock", "ram", "slam",
      "smash", "thud"]
  | .poke => ["dig", "jab", "pierce", "poke", "prick", "stick"]
  | .touch => ["caress", "graze", "kiss", "lick", "nudge", "pat", "peck", "pinch", "prod", "sting",
      "stroke", "tickle", "touch"]
  | .cut => ["chip", "clip", "cut", "hack", "hew", "saw", "scrape", "scratch", "slash", "snip"]
  | .carve => ["bore", "bruise", "carve", "chip", "chop", "crop", "crush", "cube", "dent", "dice",
      "drill", "file", "fillet", "gash", "gouge", "grate", "grind", "mangle", "mash", "mince",
      "mow", "nick", "notch", "perforate", "prune", "pulverize", "punch", "shred", "slice", "slit",
      "spear", "squash", "squish"]
  | .mix => ["combine", "commingle", "concatenate", "connect", "cream", "fuse", "join", "link",
      "merge", "mingle", "mix", "network"]
  | .amalgamate => ["alternate", "amalgamate", "associate", "coalesce", "coincide", "compare",
      "confederate", "confuse", "conjoin", "consolidate", "contrast", "correlate", "criss-cross",
      "entangle", "entwine", "harmonize", "incorporate", "integrate", "interchange",
      "interconnect", "interlace", "interlink", "interlock", "intermingle", "interrelate",
      "intersperse", "intertwine", "interweave", "introduce", "marry", "mate", "muddle", "oppose",
      "pair", "rhyme", "team", "total", "unify", "wed"]
  | .shake => ["attach", "baste", "beat", "bind", "bond", "bundle", "cluster", "collate",
      "collect", "fasten", "fuse", "gather", "glom", "graft", "group", "herd", "jumble", "lump",
      "mass", "moor", "package", "pair", "roll", "scramble", "sew", "shake", "shuffle", "splice",
      "stick", "stir", "swirl", "weld", "whip"]
  | .tape => ["anchor", "band", "belt", "bolt", "bracket", "buckle", "button", "cement", "chain",
      "clamp", "clasp", "clip", "epoxy", "fetter", "glue", "gum", "handcuff", "harness", "hinge",
      "hitch", "hook", "knot", "lace", "lash", "lasso", "latch", "leash", "link", "lock", "loop",
      "manacle", "moor", "muzzle", "nail", "padlock", "paste", "peg", "pin", "plaster", "rivet",
      "rope", "screw", "seal", "shackle", "skewer", "solder", "staple", "stitch", "strap",
      "string", "tack", "tape", "tether", "thumbtack", "tie", "trammel", "wire", "yoke", "zip"]
  | .cling => ["adhere", "cleave", "cling"]
  | .separate => ["decouple", "differentiate", "disconnect", "disentangle", "dissociate",
      "distinguish", "divide", "divorce", "part", "segregate", "separate", "sever"]
  | .split => ["break", "cut", "draw", "hack", "hew", "kick", "knock", "pry", "pull", "push",
      "rip", "roll", "saw", "shove", "slip", "split", "tear", "tug", "yank"]
  | .disassemble => ["detach", "disassemble", "disconnect", "partition", "sift", "sunder",
      "unbolt", "unbuckle", "unbutton", "unchain", "unclamp", "unclasp", "unclip", "unfasten",
      "unglue", "unhinge", "unhitch", "unhook", "unlace", "unlatch", "unleash", "unlock", "unpeg",
      "unpin", "unscrew", "unshackle", "unstaple", "unstitch", "untie", "unzip"]
  | .differ => ["differ", "diverge"]
  | .color => ["color", "distemper", "dye", "enamel", "glaze", "japan", "lacquer", "paint",
      "shellac", "spraypaint", "stain", "tint", "varnish"]
  | .imageImpression => ["emboss", "embroider", "engrave", "etch", "imprint", "incise", "inscribe",
      "mark", "paint", "set", "sign", "stamp", "tattoo"]
  | .scribble => ["carve", "chalk", "charcoal", "copy", "crayon", "doodle", "draw", "forge", "ink",
      "paint", "pencil", "plot", "print", "scratch", "scrawl", "scribble", "sketch", "spraypaint",
      "stencil", "trace", "type", "write"]
  | .illustrate => ["address", "adorn", "autograph", "brand", "date", "decorate", "embellish",
      "endorse", "illuminate", "illustrate", "initial", "label", "letter", "monogram", "ornament",
      "tag"]
  | .transcribe => ["copy", "film", "forge", "microfilm", "photocopy", "photograph", "record",
      "tape", "televise", "transcribe", "type"]
  | .build => ["arrange", "assemble", "bake", "build", "carve", "cast", "chisel", "churn",
      "compile", "cook", "crochet", "cut", "develop", "embroider", "fashion", "fold", "forge",
      "grind", "grow", "hack", "hammer", "hatch", "knit", "make", "mold", "pound", "roll",
      "sculpt", "sew", "shape", "spin", "stitch", "weave", "whittle"]
  | .grow => ["develop", "evolve", "grow", "hatch", "mature"]
  | .prepare => ["bake", "blend", "brew", "clean", "clear", "cook", "fix", "fry", "grill",
      "hardboil", "iron", "light", "mix", "poach", "pour", "prepare", "roast", "roll", "run",
      "scramble", "set", "softboil", "toast", "toss", "wash"]
  | .create => ["coin", "compose", "compute", "concoct", "construct", "create", "derive", "design",
      "dig", "fabricate", "form", "invent", "manufacture", "mint", "model", "organize", "produce",
      "recreate", "style", "synthesize"]
  | .knead => ["beat", "bend", "coil", "collect", "compress", "fold", "freeze", "knead", "melt",
      "shake", "squash", "squeeze", "squish", "twirl", "twist", "wad", "whip", "wind", "work"]
  | .turn => ["alter", "change", "convert", "metamorphose", "transform", "transmute", "turn"]
  | .performance => ["chant", "choreograph", "compose", "dance", "draw", "hum", "intone", "paint",
      "perform", "produce", "recite", "silkscreen", "sing", "spin", "take", "whistle", "write"]
  | .engender => ["beget", "cause", "create", "engender", "generate", "shape", "spawn"]
  | .calve => ["calve", "cub", "fawn", "foal", "kitten", "lamb", "litter", "pup", "spawn", "whelp"]
  | .appoint => ["acknowledge", "adopt", "appoint", "consider", "crown", "deem", "designate",
      "elect", "esteem", "imagine", "mark", "nominate", "ordain", "proclaim", "rate", "reckon",
      "report", "want"]
  | .characterize => ["accept", "address", "appreciate", "bill", "cast", "certify", "characterize",
      "choose", "cite", "class", "classify", "confirm", "count", "define", "describe", "diagnose",
      "disguise", "employ", "engage", "enlist", "enroll", "enter", "envisage", "establish",
      "esteem", "hail", "herald", "hire", "honor", "identify", "imagine", "incorporate", "induct",
      "intend", "lampoon", "offer", "oppose", "paint", "portray", "praise", "qualify", "rank",
      "recollect", "recommend", "regard", "reinstate", "reject", "remember", "represent",
      "repudiate", "reveal", "salute", "see", "select", "stigmatize", "take", "train", "treat",
      "use", "value", "view", "visualize"]
  | .dub => ["anoint", "baptize", "brand", "call", "christen", "consecrate", "crown", "decree",
      "dub", "label", "make", "name", "nickname", "pronounce", "rule", "stamp", "style", "term",
      "vote"]
  | .declare => ["adjudge", "adjudicate", "assume", "avow", "believe", "confess", "declare",
      "fancy", "find", "judge", "presume", "profess", "prove", "suppose", "think", "warrant"]
  | .conjecture => ["admit", "allow", "assert", "conjecture", "deny", "discover", "feel", "figure",
      "grant", "guarantee", "guess", "hold", "know", "maintain", "mean", "observe", "recognize",
      "repute", "show", "suspect"]
  | .masquerade => ["act", "behave", "camouflage", "count", "masquerade", "officiate", "qualify",
      "rank", "rate", "serve"]
  | .orphan => ["apprentice", "canonize", "cripple", "cuckold", "knight", "martyr", "orphan",
      "outlaw", "pauper", "recruit", "widow"]
  | .captain => ["boss", "bully", "butcher", "butler", "caddy", "captain", "champion", "chaperone",
      "chauffeur", "clerk", "coach", "cox", "crew", "doctor", "emcee", "escort", "guard", "host",
      "model", "mother", "nurse", "partner", "pilot", "pioneer", "police", "referee", "shepherd",
      "skipper", "sponsor", "star", "tailor", "tutor", "umpire", "understudy", "usher", "valet",
      "volunteer", "witness"]
  | .see => ["detect", "discern", "feel", "hear", "notice", "see", "sense", "smell", "taste"]
  | .sight => ["descry", "discover", "espy", "examine", "eye", "glimpse", "inspect", "investigate",
      "note", "observe", "overhear", "perceive", "recognize", "regard", "savor", "scan", "scent",
      "scrutinize", "sight", "spot", "spy", "study", "survey", "view", "watch", "witness"]
  | .peer => ["check", "gape", "gawk", "gaze", "glance", "glare", "goggle", "leer", "listen",
      "look", "ogle", "peek", "peep", "peer", "sniff", "snoop", "squint", "stare"]
  | .stimulusSubjectPerception => ["feel", "look", "smell", "sound", "taste"]
  | .amuse => ["abash", "affect", "afflict", "affront", "aggravate", "agitate", "agonize", "alarm",
      "alienate", "amaze", "amuse", "anger", "annoy", "antagonize", "appall", "appease", "arouse",
      "asperate", "assuage", "astonish", "astound", "awe", "baffle", "beguile", "bewilder",
      "bewitch", "boggle", "bore", "bother", "bug", "calm", "captivate", "chagrin", "charm",
      "cheer", "chill", "comfort", "concern", "confound", "confuse", "console", "content",
      "convince", "cow", "crush", "cut", "daunt", "daze", "dazzle", "deject", "delight",
      "demolish", "demoralize", "depress", "devastate", "disappoint", "disarm", "discombobulate",
      "discomfit", "discompose", "disconcert", "discourage", "disgrace", "disgruntle", "disgust",
      "dishearten", "disillusion", "dismay", "dispirit", "disquiet", "dissatisfy", "distract",
      "distress", "disturb", "dumbfound", "elate", "elecdisplease", "embarrass", "embolden",
      "enchant", "encourage", "engage", "engross", "enlighten", "enrage", "enrapture", "entertain",
      "enthrall", "enthuse", "entice", "entrance", "excite", "exenliven", "exhaust", "exhilarate",
      "fascinate", "faze", "flabbergast", "flatter", "floor", "fluster", "frighten", "frustrate",
      "gall", "galvanize", "gladden", "gratify", "grieve", "harass", "haunt", "hearten", "horrify",
      "humble", "humiliate", "hurt", "hypnotize", "impress", "incense", "infuriate", "inspire",
      "insult", "interest", "intimidate", "intoxicate", "intrigue", "invigorate", "irk",
      "irritate", "ize", "jar", "jollify", "jolt", "lull", "madden", "mesmerize", "miff",
      "mollify", "mortify", "move", "muddle", "mystify", "nauseate", "nettle", "numb", "obsess",
      "offend", "outrage", "overawe", "overwhelm", "pacify", "pain", "peeve", "perplex", "perturb",
      "pique", "placate", "plague", "please", "preoccupy", "puzzle", "rankle", "reassure",
      "refresh", "relax", "relieve", "repel", "repulse", "revitalprovoke", "revolt", "rile",
      "ruffle", "sadden", "satisfy", "scandalize", "scare", "shake", "shame", "shock", "sicken",
      "sober", "solace", "soothe", "spellbind", "spook", "stagger", "startle", "stimulate",
      "sting", "stir", "strike", "stump", "stun", "stupefy", "surprise", "tantalize", "tease",
      "tempt", "terrify", "terrorize", "threaten", "thrill", "throw", "tickle", "tire",
      "titillate", "torment", "touch", "transport", "trify", "trouble", "try", "unnerve",
      "unsettle", "uplift", "upset", "vex", "weary", "worry", "wound", "wow"]
  | .admire => ["abhor", "admire", "adore", "appreciate", "cherish", "deplore", "despise",
      "detest", "disdain", "dislike", "distrust", "dread", "enjoy", "envy", "esteem", "exalt",
      "execrate", "fancy", "favor", "fear", "hate", "idolize", "lament", "like", "loathe", "love",
      "miss", "mourn", "pity", "prize", "regret", "relish", "resent", "respect", "revere", "rue",
      "savor", "stand", "support", "tolerate", "treasure", "trust", "value", "venerate", "worship"]
  | .marvel => ["anguish", "beware", "care", "cringe", "cry", "delight", "despair", "disapprove",
      "enthuse", "exult", "fear", "feel", "fret", "fume", "gladden", "gloat", "glory", "grieve",
      "gush", "hunger", "hurt", "luxuriate", "madden", "marvel", "mind", "moon", "mope", "mourn",
      "obsess", "puzzle", "rage", "rave", "rejoice", "revel", "rhapsodize", "sadden", "salivate",
      "seethe", "sicken", "sorrow", "swoon", "tage", "thrill", "tire", "wonder"]
  | .appeal => ["matter"]
  | .want => ["covet", "crave", "desire", "fancy", "need", "want"]
  | .long => ["crave", "fall", "hanker", "hope", "hunger", "itch", "long", "lust", "pine", "pray",
      "thirst", "wish", "yearn"]
  | .judgment => ["abuse", "acclaim", "applaud", "backbite", "bless", "calumniate", "castigate",
      "celebrate", "censure", "chasten", "chastise", "chide", "commend", "compensate",
      "compliment", "condemn", "congratulate", "criticize", "decry", "defame", "denigrate",
      "denounce", "deprecate", "deride", "disparage", "eulogize", "excuse", "extol", "fault",
      "felicitate", "fine", "forgive", "greet", "hail", "honor", "impeach", "insult", "lambaste",
      "laud", "malign", "mock", "pardon", "penalize", "persecute", "praise", "prosecute", "punish",
      "rebuke", "recompense", "remunerate", "repay", "reprimand", "reproach", "reprove", "revile",
      "reward", "ridicule", "salute", "scold", "scorn", "shame", "snub", "thank", "toast",
      "upbraid", "victimize", "vilify", "welcome"]
  | .assessment => ["analyze", "assess", "audit", "evaluate", "review", "scrutinize", "study"]
  | .hunt => ["dig", "feel", "fish", "hunt", "mine", "poach", "scrounge"]
  | .search => ["advertise", "check", "comb", "dive", "drag", "dredge", "excavate", "patrol",
      "plumb", "probe", "prospect", "prowl", "quarry", "rake", "rifle", "scavenge", "scour",
      "scout", "search", "shop", "sift", "trawl", "troll", "watch"]
  | .stalk => ["smell", "stalk", "taste", "track"]
  | .investigate => ["canvass", "examine", "explore", "frisk", "inspect", "investigate", "observe",
      "quiz", "raid", "ransack", "riffle", "scan", "scrutinize", "survey", "tap"]
  | .rummage => ["bore", "burrow", "delve", "forage", "fumble", "grope", "leaf", "listen", "look",
      "page", "paw", "poke", "rifle", "root", "rummage", "scrabble", "scratch", "snoop", "thumb",
      "tunnel"]
  | .ferret => ["ferret", "nose", "seek", "tease"]
  | .correspond => ["agree", "argue", "banter", "bargain", "bicker", "brawl", "clash", "coexist",
      "collaborate", "collide", "combat", "commiserate", "communicate", "compete", "concur",
      "confabulate", "conflict", "consort", "cooperate", "correspond", "dicker", "differ",
      "disagree", "dispute", "dissent", "duel", "elope", "feud", "flirt", "haggle", "hobnob",
      "jest", "joke", "joust", "mate", "mingle", "mix", "neck", "negotiate", "pair", "plot",
      "quarrel", "quibble", "rendezvous", "scuffle", "skirmish", "spar", "spat", "spoon",
      "squabble", "struggle", "tilt", "tussle", "vie", "war", "wrangle", "wrestle"]
  | .marry => ["court", "cuddle", "date", "divorce", "embrace", "hug", "kiss", "marry", "nuzzle",
      "pass", "pet"]
  | .meet => ["battle", "box", "consult", "debate", "fight", "meet", "play", "visit"]
  | .transferOfMessage => ["ask", "cite", "demonstrate", "dictate", "explain", "explicate",
      "narrate", "pose", "preach", "quote", "read", "recite", "relay", "show", "teach", "tell",
      "write"]
  | .tell => ["tell"]
  | .mannerOfSpeaking => ["babble", "bark", "bawl", "bellow", "bleat", "boom", "bray", "burble",
      "cackle", "call", "carol", "chant", "chatter", "chirp", "cluck", "coo", "croak", "croon",
      "crow", "cry", "drawl", "drone", "gabble", "gibber", "groan", "growl", "grumble", "grunt",
      "hiss", "holler", "hoot", "howl", "jabber", "lilt", "lisp", "moan", "mumble", "murmur",
      "mutter", "purr", "rage", "rasp", "roar", "rumble", "scream", "screech", "shout", "shriek",
      "sing", "snap", "snarl", "snuffle", "splutter", "squall", "squawk", "squeak", "squeal",
      "stammer", "stutter", "thunder", "tisk", "trill", "trumpet", "twitter", "wail", "warble",
      "wheeze", "whimper", "whine", "whisper", "whistle", "whoop", "yammer", "yap", "yell", "yelp",
      "yodel"]
  | .instrumentOfCommunication => ["cable", "e-mail", "fax", "modem", "netmail", "phone", "radio",
      "relay", "satellite", "semaphore", "sign", "signal", "telecast", "telegraph", "telephone",
      "telex", "wire", "wireless"]
  | .talk => ["speak", "talk"]
  | .chitchat => ["argue", "chat", "chatter", "chitchat", "confer", "converse", "gab", "gossip",
      "rap", "schmooze", "yak"]
  | .say => ["announce", "articulate", "blab", "blurt", "claim", "confess", "confide", "convey",
      "declare", "mention", "note", "observe", "proclaim", "propose", "recount", "reiterate",
      "relate", "remark", "repeat", "report", "reveal", "say", "state", "suggest"]
  | .complain => ["boast", "brag", "complain", "crab", "gripe", "grouch", "grouse", "grumble",
      "kvetch", "object"]
  | .advise => ["admonish", "advise", "alert", "caution", "counsel", "instruct", "warn"]
  | .animalSound => ["baa", "bark", "bay", "bellow", "blat", "bleat", "bray", "buzz", "cackle",
      "call", "caw", "chatter", "cheep", "chirp", "chirrup", "chitter", "cluck", "coo", "croak",
      "crow", "cuckoo", "drone", "gobble", "growl", "grunt", "hee-haw", "hiss", "honk", "hoot",
      "howl", "low", "meow", "mew", "moo", "neigh", "oink", "peep", "pipe", "purr", "quack",
      "roar", "scrawk", "scream", "screech", "sing", "snap", "snarl", "snort", "snuffle", "squawk",
      "squeak", "squeal", "stridulate", "trill", "tweet", "twitter", "wail", "warble", "whimper",
      "whinny", "whistle", "woof", "yap", "yell", "yelp", "yip", "yowl"]
  | .eat => ["drink", "eat"]
  | .chew => ["chew", "chomp", "crunch", "gnaw", "lick", "munch", "nibble", "peck", "pick", "sip",
      "slurp", "suck"]
  | .gobble => ["bolt", "gobble", "gulp", "guzzle", "quaff", "swallow", "swig", "wolf"]
  | .devour => ["consume", "devour", "imbibe", "ingest", "swill"]
  | .dine => ["banquet", "breakfast", "luncheon", "nosh", "picnic", "snack", "sup"]
  | .gorge => ["exist", "feed", "flourish", "gorge", "live", "prosper", "survive", "thrive"]
  | .feed => ["bottlefeed", "breastfeed", "feed", "forcefeed", "handfeed", "spoonfeed"]
  | .hiccup => ["belch", "blush", "burp", "flush", "hiccup", "pant", "sneeze", "sniffle", "snore",
      "snuffle", "swallow", "wheeze", "yawn"]
  | .breathe => ["bleed", "breathe", "cough", "cry", "dribble", "drool", "puke", "spit", "sweat",
      "vomit", "weep"]
  | .exhale => ["exhale", "inhale", "perspire"]
  | .nonverbalExpression => ["beam", "cackle", "chortle", "chuckle", "cough", "cry", "frown",
      "gape", "gasp", "gawk", "giggle", "glare", "glower", "goggle", "grimace", "grin", "groan",
      "growl", "guffaw", "howl", "jeer", "laugh", "moan", "pout", "scowl", "sigh", "simper",
      "smile", "smirk", "sneeze", "snicker", "sniff", "snigger", "snivel", "snore", "snort", "sob",
      "titter", "weep", "whistle", "yawn"]
  | .wink => ["blink", "clap", "nod", "point", "shrug", "squint", "wag", "wave", "wink"]
  | .crane => ["bare", "bat", "beat", "blow", "clench", "close", "cock", "crane", "crook", "drum",
      "eyes", "fist", "flap", "flash", "flex", "flick", "flutter", "fold", "gnash", "grind",
      "hang", "hips", "hunch", "kick", "knit", "open", "pucker", "purse", "roll", "rub", "show",
      "shuffle", "smack", "snap", "stamp", "stretch", "toss", "turn", "twiddle", "waggle", "wring"]
  | .curtsey => ["bob", "bow", "curtsey", "genuflect", "kneel", "salaam", "salute"]
  | .snooze => ["catnap", "doze", "drowse", "nap", "sleep", "slumber", "snooze"]
  | .flinch => ["balk", "cower", "cringe", "flinch", "recoil", "shrink", "wince"]
  | .bodyInternalStateOfExistence => ["convulse", "cower", "quake", "quiver", "shake", "shiver",
      "shudder", "tremble", "writhe"]
  | .suffocate => ["asphyxiate", "choke", "drown", "stifle", "suffocate"]
  | .pain => ["ache", "bother", "hurt", "itch", "pain"]
  | .tingle => ["burn", "hum", "prickle", "pucker", "reel", "smart", "spin", "split", "sting",
      "swim", "throb", "tickle", "tingle"]
  | .hurt => ["back", "bark", "bite", "break", "bruise", "bump", "burn", "chip", "cut", "fracture",
      "her", "hurt", "injure", "knee", "prick", "pull", "rupture", "scald", "scratch", "skin",
      "split", "strain", "stub", "turn"]
  | .changeOfBodilyState => ["blanch", "faint", "sicken", "swoon"]
  | .dress => ["bathe", "change", "disrobe", "dress", "exercise", "preen", "primp", "shave",
      "shower", "strip", "undress", "wash"]
  | .groom => ["curry", "groom"]
  | .floss => ["brush", "floss"]
  | .braid => ["bob", "braid", "brush", "clip", "coldcream", "comb", "condition", "crimp", "crop",
      "curl", "cut", "dye", "file", "henna", "manicure", "part", "perm", "plait", "pluck", "set",
      "shampoo", "talc", "tease", "wave"]
  | .simpleDressing => ["doff", "don", "wear"]
  | .dressingWell => ["doll", "dress", "spruce", "tog"]
  | .beingDressed => ["attire", "clad", "garb", "robe"]
  | .murder => ["assassinate", "butcher", "dispatch", "eliminate", "execute", "immolate", "kill",
      "liquidate", "massacre", "murder", "slaughter", "slay"]
  | .poison => ["asphyxiate", "crucify", "drown", "electrocute", "garrotte", "hang", "knife",
      "poison", "shoot", "smother", "stab", "strangle", "suffocate"]
  | .lightEmission => ["beam", "blaze", "blink", "burn", "flame", "flare", "flash", "flicker",
      "glare", "gleam", "glimmer", "glint", "glisten", "glitter", "glow", "incandesce",
      "scintillate", "shimmer", "shine", "sparkle", "twinkle"]
  | .soundEmission => ["babble", "bang", "beat", "beep", "bellow", "blare", "blast", "blat",
      "boom", "bubble", "burble", "burr", "buzz", "chatter", "chime", "chink", "chir", "chitter",
      "chug", "clack", "clang", "clank", "clap", "clash", "clatter", "click", "cling", "clink",
      "clomp", "clump", "clunk", "crack", "crackle", "crash", "creak", "crepitate", "crunch",
      "cry", "ding", "dong", "explode", "fizz", "fizzle", "groan", "growl", "gurgle", "hiss",
      "hoot", "howl", "hum", "jangle", "jingle", "knell", "knock", "lilt", "moan", "murmur",
      "patter", "peal", "ping", "pink", "pipe", "plink", "plonk", "plop", "plunk", "pop", "purr",
      "putter", "rap", "rasp", "rattle", "ring", "roar", "roll", "rumble", "rustle", "scream",
      "screech", "shriek", "shrill", "sing", "sizzle", "snap", "splash", "splutter", "sputter",
      "squawk", "squeak", "squeal", "squelch", "strike", "swish", "swoosh", "thrum", "thud",
      "thump", "thunder", "thunk", "tick", "ting", "tinkle", "toll", "toot", "tootle", "trill",
      "trumpet", "twang", "ululate", "vroom", "wail", "wheeze", "whine", "whir", "whish",
      "whistle", "whoosh", "whump", "zing"]
  | .smellEmission => ["reek", "smell", "stink"]
  | .substanceEmission => ["belch", "bleed", "bubble", "dribble", "drip", "drool", "emanate",
      "exude", "foam", "gush", "leak", "ooze", "pour", "puff", "radiate", "seep", "shed", "slop",
      "spew", "spill", "spout", "sprout", "spurt", "squirt", "steam", "stream", "sweat"]
  | .destroy => ["annihilate", "blitz", "decimate", "demolish", "destroy", "devastate",
      "exterminate", "extirpate", "obliterate", "ravage", "raze", "ruin", "waste", "wreck"]
  | .break_ => ["break", "chip", "crack", "crash", "crush", "fracture", "rip", "shatter", "smash",
      "snap", "splinter", "split", "tear"]
  | .bend => ["bend", "crease", "crinkle", "crumple", "fold", "rumple", "wrinkle"]
  | .cooking => ["bake", "barbecue", "blanch", "boil", "braise", "broil", "brown", "charbroil",
      "charcoal-broil", "coddle", "cook", "crisp", "deep-fry", "fry", "grill", "hardboil", "heat",
      "microwave", "oven-fry", "oven-poach", "overcook", "pan-broil", "pan-fry", "parboil",
      "parch", "percolate", "perk", "plank", "poach", "pot-roast", "rissole", "roast", "scald",
      "scallop", "shirr", "simmer", "softboil", "steam", "steam-bake", "stew", "stir-fry", "toast"]
  | .otherChangeOfState => ["abate", "accelerate", "acetify", "acidify", "advance", "age",
      "agglomerate", "air", "alkalify", "alter", "ameliorate", "americanize", "atrophy",
      "attenuate", "awake", "awaken", "balance", "blacken", "blast", "blunt", "blur", "brighten",
      "broaden", "brown", "burn", "burst", "calcify", "capsize", "caramelize", "carbonify",
      "carbonize", "change", "char", "cheapen", "chill", "clean", "clear", "clog", "close",
      "coagulate", "coarsen", "collapse", "collect", "compress", "condense", "contract", "cool",
      "corrode", "crimson", "crisp", "crumble", "crystallize", "dampen", "darken", "de-escalate",
      "decelerate", "decentralize", "decompose", "decrease", "deepen", "deflate", "defrost",
      "degenerate", "degrade", "dehumidify", "demagnetize", "democratize", "depressurize",
      "desiccate", "destabilize", "deteriorate", "detonate", "dim", "diminish", "dirty",
      "disintegrate", "dissipate", "dissolve", "distend", "divide", "double", "drain", "dry",
      "dull", "ease", "empty", "emulsify", "energize", "enlarge", "equalize", "evaporate", "even",
      "expand", "explode", "fade", "fatten", "federate", "fill", "firm", "flatten", "flood",
      "fossilize", "fray", "freeze", "freshen", "frost", "fructify", "fuse", "gasify",
      "gelatinize", "gladden", "glutenize", "granulate", "gray", "green", "grow", "halt", "harden",
      "harmonize", "hasten", "heal", "heat", "heighten", "humidify", "hush", "hybridize", "ignite",
      "improve", "increase", "incubate", "inflate", "intensify", "iodize", "ionize", "kindle",
      "lengthen", "lessen", "level", "levitate", "light", "lighten", "lignify", "liquefy", "loop",
      "loose", "loosen", "macerate", "magnetize", "magnify", "mature", "mellow", "melt", "moisten",
      "muddy", "multiply", "narrow", "neaten", "neutralize", "nitrify", "open", "operate",
      "ossify", "overturn", "oxidize", "pale", "petrify", "polarize", "pop", "proliferate",
      "propagate", "pulverize", "purify", "purple", "putrefy", "quadruple", "quicken", "quiet",
      "quieten", "redden", "regularize", "rekindle", "reopen", "reproduce", "ripen", "roughen",
      "round", "rupture", "scorch", "sear", "sharpen", "short", "shortcircuit", "shorten",
      "shrink", "shrivel", "shut", "sicken", "silicify", "silver", "singe", "sink", "slack",
      "slacken", "slim", "slow", "smarten", "smooth", "soak", "sober", "soften", "solidify",
      "sour", "splay", "sprout", "stabilize", "steady", "steep", "steepen", "stiffen",
      "straighten", "stratify", "strengthen", "stretch", "submerge", "subside", "sweeten", "tame",
      "tan", "taper", "tauten", "tense", "thaw", "thicken", "thin", "tighten", "tilt", "tire",
      "topple", "toughen", "triple", "ulcerate", "unfold", "unionize", "vaporize", "vary",
      "vibrate", "volatilize", "waken", "warm", "warp", "weaken", "whiten", "widen"]
  | .entitySpecificChangeOfState => ["blister", "bloom", "blossom", "burn", "corrode", "decay",
      "deteriorate", "erode", "ferment", "flower", "germinate", "molder", "molt", "rot", "rust",
      "sprout", "stagnate", "swell", "tarnish", "wilt", "wither"]
  | .calibratableChangeOfState => ["appreciate", "balloon", "climb", "decline", "decrease",
      "depreciate", "differ", "diminish", "drop", "fall", "fluctuate", "gain", "grow", "increase",
      "jump", "mushroom", "plummet", "plunge", "rise", "rocket", "skyrocket", "soar", "surge",
      "tumble", "vary"]
  | .lodge => ["bivouac", "board", "camp", "dwell", "live", "lodge", "reside", "settle", "shelter",
      "stay", "stop"]
  | .exist => ["coexist", "correspond", "depend", "dwell", "endure", "exist", "extend", "flourish",
      "languish", "linger", "live", "loom", "lurk", "overspread", "persist", "predominate",
      "prosper", "remain", "reside", "shelter", "stay", "survive", "thrive", "tower"]
  | .entitySpecificModeOfBeing => ["billow", "bloom", "blossom", "blow", "breathe", "bristle",
      "bulge", "burn", "cascade", "corrode", "decay", "decompose", "effervesce", "erode",
      "ferment", "fester", "fizz", "flow", "flower", "foam", "froth", "germinate", "grow", "molt",
      "propagate", "rage", "ripple", "roil", "rot", "rust", "seethe", "smoke", "smolder", "spread",
      "sprout", "stagnate", "stream", "sweep", "tarnish", "trickle", "wilt", "wither"]
  | .modeOfBeingInvolvingMotion => ["bob", "bow", "creep", "dance", "drift", "eddy", "flap",
      "float", "flutter", "hover", "jiggle", "joggle", "oscillate", "pulsate", "quake", "quiver",
      "revolve", "rock", "rotate", "shake", "stir", "sway", "swirl", "teeter", "throb", "totter",
      "tremble", "undulate", "vibrate", "waft", "wave", "waver", "wiggle", "wobble", "writhe"]
  | .soundExistence => ["din", "echo", "resonate", "resound", "reverberate", "sound"]
  | .swarm => ["abound", "bustle", "crawl", "creep", "hop", "run", "swarm", "swim", "teem",
      "throng"]
  | .herd => ["accumulate", "aggregate", "amass", "assemble", "cluster", "collect", "congregate",
      "convene", "flock", "gather", "group", "herd", "huddle", "mass"]
  | .bulge => ["bristle", "bulge", "seethe"]
  | .spatialConfiguration => ["bend", "bow", "crouch", "dangle", "flop", "fly", "hang", "hover",
      "jut", "kneel", "lean", "lie", "loll", "loom", "lounge", "nestle", "open", "perch", "plop",
      "project", "protrude", "recline", "rest", "rise", "roost", "sag", "sit", "slope", "slouch",
      "slump", "sprawl", "squat", "stand", "stoop", "straddle", "swing", "tilt", "tower"]
  | .meander => ["cascade", "climb", "crawl", "cut", "drop", "go", "meander", "plunge", "run",
      "straggle", "stretch", "sweep", "tumble", "turn", "twist", "wander", "weave", "wind"]
  | .contiguousLocation => ["abut", "adjoin", "blanket", "border", "bound", "bracket", "bridge",
      "cap", "contain", "cover", "cross", "dominate", "edge", "encircle", "enclose", "fence",
      "fill", "flank", "follow", "frame", "head", "hit", "hug", "intersect", "line", "meet",
      "miss", "overhang", "precede", "rim", "ring", "skirt", "span", "straddle", "support",
      "surmount", "surround", "top", "touch", "underlie"]
  | .appear => ["appear", "arise", "awake", "awaken", "break", "burst", "come", "dawn", "derive",
      "develop", "emanate", "emerge", "erupt", "evolve", "exude", "flow", "form", "grow", "gush",
      "issue", "materialize", "open", "plop", "result", "rise", "spill", "spread", "steal", "stem",
      "stream", "supervene", "surge", "wax"]
  | .reflexiveAppearance => ["assert", "declare", "define", "express", "form", "intrude",
      "manifest", "offer", "pose", "present", "proffer", "recommend", "shape", "show", "suggest"]
  | .disappearance => ["die", "disappear", "expire", "lapse", "perish", "vanish"]
  | .occurrence => ["ensue", "eventuate", "happen", "occur", "recur", "transpire"]
  | .bodyInternalMotion => ["buck", "fidget", "flap", "gyrate", "kick", "rock", "squirm", "sway",
      "teeter", "totter", "twitch", "waggle", "wiggle", "wobble", "wriggle"]
  | .assumePosition => ["bend", "bow", "crouch", "flop", "hang", "kneel", "lean", "lie", "perch",
      "plop", "rise", "sit", "slouch", "slump", "sprawl", "squat", "stand", "stoop", "straddle"]
  | .inherentlyDirectedMotion => ["advance", "arrive", "ascend", "climb", "come", "cross",
      "depart", "descend", "enter", "escape", "exit", "fall", "flee", "go", "leave", "plunge",
      "recede", "return", "rise", "tumble"]
  | .leave => ["abandon", "desert", "leave"]
  | .roll => ["bounce", "coil", "drift", "drop", "float", "glide", "move", "revolve", "roll",
      "rotate", "slide", "spin", "swing", "turn", "twirl", "twist", "whirl", "wind"]
  | .run => ["amble", "backpack", "bolt", "bounce", "bound", "bowl", "canter", "carom", "cavort",
      "charge", "clamber", "climb", "clump", "coast", "crawl", "creep", "dart", "dash", "dodder",
      "drift", "file", "flit", "float", "fly", "frolic", "gallop", "gambol", "glide", "goosestep",
      "hasten", "hike", "hobble", "hop", "hurry", "hurtle", "inch", "jog", "journey", "jump",
      "leap", "limp", "lollop", "lope", "lumber", "lurch", "march", "meander", "mince", "mosey",
      "nip", "pad", "parade", "plod", "prance", "promenade", "prowl", "race", "ramble", "roam",
      "roll", "romp", "rove", "run", "rush", "sashay", "saunter", "scamper", "scoot", "scram",
      "scramble", "scud", "scurry", "scutter", "scuttle", "shamble", "shuffle", "sidle",
      "skedaddle", "skip", "skitter", "skulk", "sleepwalk", "slide", "slink", "slither", "slog",
      "slouch", "sneak", "somersault", "speed", "stagger", "stomp", "stray", "streak", "stride",
      "stroll", "strut", "stumble", "stump", "swagger", "sweep", "swim", "tack", "tear", "tiptoe",
      "toddle", "totter", "traipse", "tramp", "travel", "trek", "troop", "trot", "trudge",
      "trundle", "vault", "waddle", "wade", "walk", "wander", "whiz", "zigzag", "zoom"]
  | .vehicleName => ["balloon", "bicycle", "bike", "boat", "bobsled", "bus", "cab", "canoe",
      "chariot", "coach", "cycle", "dogsled", "ferry", "gondola", "helicopter", "jeep", "jet",
      "kayak", "moped", "motor", "motorbike", "motorcycle", "parachute", "punt", "raft",
      "rickshaw", "rocket", "skate", "skateboard", "ski", "sled", "sledge", "sleigh", "taxi",
      "toboggan", "tram", "trolley", "van", "yacht"]
  | .nonVehicleName => ["cruise", "drive", "fly", "oar", "paddle", "pedal", "ride", "row", "sail",
      "tack"]
  | .waltz => ["boogie", "bop", "cancan", "clog", "conga", "dance", "foxtrot", "jig", "jitterbug",
      "jive", "pirouette", "polka", "quickstep", "rumba", "samba", "shuffle", "squaredance",
      "tango", "tapdance", "waltz"]
  | .chase => ["chase", "follow", "pursue", "shadow", "tail", "track", "trail"]
  | .accompany => ["accompany", "conduct", "escort", "guide", "lead", "shepherd"]
  | .avoid => ["avoid", "boycott", "dodge", "duck", "elude", "evade", "shun", "sidestep"]
  | .linger => ["dally", "dawdle", "delay", "dither", "hesitate", "linger", "loiter", "tarry"]
  | .rush => ["hasten", "hurry", "rush"]
  | .register => ["measure", "read", "register", "total", "weigh"]
  | .cost => ["carry", "cost", "last", "take"]
  | .fit => ["carry", "contain", "feed", "fit", "hold", "house", "seat", "serve", "sleep", "store",
      "take"]
  | .price => ["appraise", "assess", "estimate", "fix", "peg", "price", "rate", "value"]
  | .bill => ["bet", "bill", "charge", "fine", "mulct", "overcharge", "save", "spare", "tax",
      "tip", "undercharge", "wager"]
  | .begin => ["begin", "cease", "commence", "continue", "end", "finish", "halt", "keep",
      "proceed", "repeat", "resume", "start", "stop", "terminate"]
  | .complete => ["complete", "discontinue", "initiate", "quit"]
  | .weekend => ["summer", "vacation", "weekend", "winter"]
  | .weather => ["blow", "clear", "drizzle", "fog", "freeze", "gust", "hail", "howl", "lightning",
      "mist", "mizzle", "pelt", "pour", "precipitate", "rain", "roar", "shower", "sleet", "snow",
      "spit", "spot", "sprinkle", "storm", "swelter", "teem", "thaw", "thunder"]

/-- The classes whose member lists carry the form. -/
def classesOf (form : String) : Finset LevinClass := Finset.univ.filter (form ∈ members ·)

@[simp] theorem mem_classesOf {form : String} {c : LevinClass} :
    c ∈ classesOf form ↔ form ∈ c.members := by simp [classesOf]

end ArgumentStructure.LevinClass
