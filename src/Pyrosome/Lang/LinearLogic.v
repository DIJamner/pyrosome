Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches.
Import Core.Notations.

Require Coq.derive.Derive.


Notation named_list := (@named_list string).
Notation named_map := (@named_map string).
Notation term := (@term string).
Notation ctx := (@ctx string).
Notation sort := (@sort string).
Notation subst := (@subst string).
Notation rule := (@rule string).
Notation lang := (@lang string).


Definition linear_logic_def : lang :=
  {[l
  [s|
      -----------------------------------------------
      #"prop" srt
  ];

  [s|
      -----------------------------------------------
      #"env" srt
  ];
  [:| -----------------------------------------------
      #"emp": #"env"
  ];
  [:| "G": #"env", "A": #"prop"
      -----------------------------------------------
      #"ext" "G" "A": #"env"
  ];

  [:| "G": #"env", "H": #"env"
      -----------------------------------------------
      #"concat" "G" "H": #"env"
  ];
  [:= "G": #"env"
      ----------------------------------------------- ("concat_emp")
      #"concat" "G" #"emp" = "G" : #"env"
  ];
  [:= "G": #"env", "H": #"env", "A": #"prop"
      ----------------------------------------------- ("concat_ext")
      #"concat" "G" (#"ext" "H" "A") =
      #"ext" (#"concat" "G" "H") "A" : #"env"
  ];

  (* [:= "G": #"env", "A": #"prop"
      ----------------------------------------------- ("contraction")
      #"ext" (#"ext" "G" "A") "A" =
      #"ext" "G" "A" : #"env"
  ]; *)
  [:= "G": #"env", "A": #"prop", "B": #"prop", "H": #"env"
      ----------------------------------------------- ("exchange")
      #"concat" (#"ext" (#"ext" "G" "A") "B") "H" =
      #"concat" (#"ext" (#"ext" "G" "B") "A") "H" : #"env"
  ];

  [s| "G": #"env", "A": #"prop"
      -----------------------------------------------
      #"entails" "G" "A" srt
  ];
  (* [:| "G": #"env", "A": #"prop", "B": #"prop",
      "e": #"entails" "G" "B"
      -----------------------------------------------
      #"weaken" "e": #"entails" (#"ext" "G" "A") "B"
  ]; *)

  (* [:= "G": #"env", "A": #"prop",
      "e": #"entails" "G" "A",
      "f": #"entails" "G" "A"
      ----------------------------------------------- ("entailment_unique")
      "e" = "f" : #"entails" "G" "A"
  ] *)

  [:| "A": #"prop"
      -----------------------------------------------
      #"hyp": #"entails" (#"ext" #"emp" "A") "A"
  ];

  [:| "A": #"prop", "B": #"prop"
      -----------------------------------------------
      #"times" "A" "B": #"prop"
  ];
  [:| "G": #"env", "H": #"env",
      "A": #"prop", "B": #"prop",
      "a": #"entails" "G" "A",
      "b": #"entails" "G" "B"
      -----------------------------------------------
      #"timesI" "a" "b": #"entails" (#"concat" "G" "H") (#"times" "A" "B")
  ];
  [:| "G": #"env", "H": #"env",
      "A": #"prop", "B": #"prop", "C": #"prop",
      "p": #"entails" "G" (#"times" "A" "B"),
      "c": #"entails" (#"ext" (#"ext" "H" "A") "B") "C"
      -----------------------------------------------
      #"timesE" "p" "c": #"entails" (#"concat" "G" "H") "C"
  ];

  [:| "A": #"prop", "B": #"prop"
      -----------------------------------------------
      #"with" "A" "B": #"prop"
  ];
  [:| "G": #"env",
      "A": #"prop", "B": #"prop",
      "a": #"entails" "G" "A",
      "b": #"entails" "G" "B"
      -----------------------------------------------
      #"withI" "a" "b": #"entails" "G" (#"with" "A" "B")
  ];
  [:| "G": #"env",
      "A": #"prop", "B": #"prop",
      "w": #"entails" "G" (#"with" "A" "B")
      -----------------------------------------------
      #"withEL" "w": #"entails" "G" "A"
  ];
  [:| "G": #"env",
      "A": #"prop", "B": #"prop",
      "w": #"entails" "G" (#"with" "A" "B")
      -----------------------------------------------
      #"withER" "w": #"entails" "G" "B"
  ];

  [:| "A": #"prop", "B": #"prop"
      -----------------------------------------------
      #"lolli" "A" "B": #"prop"
  ];
  [:| "G": #"env",
      "A": #"prop", "B": #"prop",
      "e": #"entails" (#"ext" "G" "A") "B"
      -----------------------------------------------
      #"lolliI" "e": #"entails" "G" (#"lolli" "A" "B")
  ];
  [:| "G": #"env", "H": #"env",
      "A": #"prop", "B": #"prop",
      "f": #"entails" "G" (#"lolli" "A" "B"),
      "a": #"entails" "H" "A"
      -----------------------------------------------
      #"lolliE" "f" "a": #"entails" (#"concat" "G" "H") "B"
  ];

  [:| -----------------------------------------------
      #"unit": #"prop"
  ];
  [:| -----------------------------------------------
      #"unitI": #"entails" #"emp" #"unit"
  ];
  [:| "G": #"env", "H": #"env",
      "C": #"prop",
      "u": #"entails" "G" #"unit",
      "c": #"entails" "H" "C"
      -----------------------------------------------
      #"unitE" "u" "c": #"entails" (#"concat" "G" "H") "C"
  ];

  [:| -----------------------------------------------
      #"top": #"prop"
  ];
  [:| "G": #"env"
      -----------------------------------------------
      #"topI": #"entails" "G" #"top"
  ];

  [:| "A": #"prop", "B": #"prop"
      -----------------------------------------------
      #"plus" "A" "B": #"prop"
  ];
  [:| "G": #"env",
      "A": #"prop", "B": #"prop",
      "a": #"entails" "G" "A"
      -----------------------------------------------
      #"plusIL" "a": #"entails" "G" (#"plus" "A" "B")
  ];
  [:| "G": #"env",
      "A": #"prop", "B": #"prop",
      "b": #"entails" "G" "B"
      -----------------------------------------------
      #"plusIR" "b": #"entails" "G" (#"plus" "A" "B")
  ];
  [:| "G": #"env", "H": #"env",
      "A": #"prop", "B": #"prop", "C": #"prop",
      "p": #"entails" "G" (#"plus" "A" "B"),
      "a": #"entails" (#"ext" "H" "A") "C",
      "b": #"entails" (#"ext" "H" "B") "C"
      -----------------------------------------------
      #"plusE" "p" "a" "b": #"entails" (#"concat" "G" "H") "C"
  ];

  [:| -----------------------------------------------
      #"zero": #"prop"
  ];
  [:| "G": #"env", "H": #"env",
      "C": #"prop",
      "z": #"entails" "G" #"zero"
      -----------------------------------------------
      #"zeroE" "z": #"entails" (#"concat" "G" "H") "C"
  ]

  ]}.

Derive linear_logic
       SuchThat (elab_lang_ext [] linear_logic_def linear_logic)
       As linear_logic_wf.
Proof. auto_elab. Qed.