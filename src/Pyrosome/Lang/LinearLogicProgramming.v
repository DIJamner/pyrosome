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


Definition llp_def : lang :=
  {[l
  [s|
      -----------------------------------------------
      #"env" srt
  ];

  [s| "G": #"env"
      -----------------------------------------------
      #"ty" "G" srt
  ];

  [s| "G": #"env", "A": #"ty" "G"
      -----------------------------------------------
      #"exp" "A" srt
  ];

  [:| -----------------------------------------------
      #"emp": #"env"
  ];
  [:| "G": #"env", "A": #"ty" "G", "e": #"exp" "A"
      -----------------------------------------------
      #"ext" "G" "e": #"env"
  ];

  [:| "G": #"env", "H": #"env"
      -----------------------------------------------
      #"concat" "G" "H": #"env"
  ];
  [:= "G": #"env"
      ----------------------------------------------- ("concat_emp")
      #"concat" "G" #"emp" = "G" : #"env"
  ];
  [:= "G": #"env", "H": #"env",
      "A": #"ty" "G", "e": #"exp" "A"
      ----------------------------------------------- ("concat_ext")
      #"concat" "G" (#"ext" "H" "e") =
      #"ext" (#"concat" "G" "H") "A" : #"env"
  ];

  (* [:= "G": #"env", "A": #"prop"
      ----------------------------------------------- ("contraction")
      #"ext" (#"ext" "G" "A") "A" =
      #"ext" "G" "A" : #"env"
  ]; *)
  [:= "G": #"env", "A": #"prop", "B": #"prop"
      ----------------------------------------------- ("exchange")
      #"ext" (#"ext" "G" "A") "B" =
      #"ext" (#"ext" "G" "B") "A" : #"env"
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

  (* [:| "A": #"prop"
      -----------------------------------------------
      #"hyp": #"entails" (#"ext" #"emp" "A") "A"
  ]; *)

  (* [:| "A": #"prop"
      -----------------------------------------------
      #"dual" "A": #"prop"
  ];
  [:= "A": #"prop"
      ----------------------------------------------- ("dual_dual")
      #"dual" (#"dual" "A") = "A": #"prop"
  ]; *)

  [:| "G": #"env", "H": #"env",
      "A": #"ty" "G", "B": #"ty" "H"
      -----------------------------------------------
      #"times" "A" "B": #"ty" (#"concat" "G" "H")
  ];
  [:| "G": #"env", "H": #"env",
      "A": #"ty" "G", "B": #"ty" "H",
      "a": #"exp" "A",
      "b": #"exp" "B"
      -----------------------------------------------
      #"timesI" "a" "b": #"exp" (#"times" "A" "B")
  ];
  [:| "G1": #"env", "G2": #"env", "H": #"env",
      "A": #"ty" "G1", "B": #"ty" "G2",
      "C": #"ty" (#"ext" (#"ext" "H" "A") "B"),
      "p": #"exp" (#"times" "A" "B"),
      "c": #"exp" "C"
      -----------------------------------------------
      #"timesE" "p" "c": #"entails" (#"concat" "G" "H") "C"
  ];

  [:| "G": #"env", "A": #"ty" "G", "B": #"ty" "G"
      -----------------------------------------------
      #"with" "A" "B": #"ty" "G"
  ];
  [:| "G": #"env",
      "A": #"ty" "G", "B": #"ty" "G",
      "a": #"exp" "A",
      "b": #"exp" "B"
      -----------------------------------------------
      #"withI" "a" "b": #"exp" (#"with" "A" "B")
  ];
  [:| "G": #"env",
      "A": #"ty" "G", "B": #"ty" "G",
      "w": #"exp" (#"with" "A" "B")
      -----------------------------------------------
      #"withEL" "w": #"exp" "A"
  ];
  [:| "G": #"env",
      "A": #"ty" "G", "B": #"ty" "G",
      "w": #"exp" (#"with" "A" "B")
      -----------------------------------------------
      #"withEL" "w": #"exp" "B"
  ];

  [:| "G": #"env",
      "A": #"ty" "G",
      "B": #"ty" (#"ext" "G" "A")
      -----------------------------------------------
      #"lolli" "A" "B": #"ty" "G"
  ];
  [:| "G": #"env",
      "A": #"ty" "G",
      "B": #"ty" (#"ext" "G" "A"),
      "b": #"exp" "B"
      -----------------------------------------------
      #"lolliI" "b": #"exp" (#"lolli" "A" "B")
  ];
  [:| "G": #"env",
      "A": #"ty" "G",
      "B": #"ty" (#"ext" "G" "A"),
      "f": #"exp" (#"lolli" "A" "B"),
      "a": #"exp" "A"
      -----------------------------------------------
      #"lolliE" "f" "a": #"exp" "B"
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
      #"null": #"prop"
  ];
  [:| "G": #"env", "H": #"env",
      "C": #"prop",
      "z": #"entails" "G" #"null"
      -----------------------------------------------
      #"nullE" "z": #"entails" (#"concat" "G" "H") "C"
  ]
(*
  [:= "A": #"prop", "B": #"prop"
      ----------------------------------------------- ("times_dual")
      #"dual" (#"times" "A" "B") = #"par" (#"dual" "A") (#"dual" "B")
      : #"prop"
  ];
  [:= "A": #"prop", "B": #"prop"
      ----------------------------------------------- ("par_dual")
      #"dual" (#"par" "A" "B") = #"times" (#"dual" "A") (#"dual" "B")
      : #"prop"
  ];
  [:= "A": #"prop", "B": #"prop"
      ----------------------------------------------- ("with_dual")
      #"dual" (#"with" "A" "B") = #"plus" (#"dual" "A") (#"dual" "B")
      : #"prop"
  ];
  [:= "A": #"prop", "B": #"prop"
      ----------------------------------------------- ("plus_dual")
      #"dual" (#"plus" "A" "B") = #"with" (#"dual" "A") (#"dual" "B")
      : #"prop"
  ];

  [:= ----------------------------------------------- ("unit_dual")
      #"dual" #"unit" = #"bot": #"prop"
  ];
  [:= ----------------------------------------------- ("bot_dual")
      #"dual" #"bot" = #"unit": #"prop"
  ];
  [:= ----------------------------------------------- ("top_dual")
      #"dual" #"top" = #"null": #"prop"
  ];
  [:= ----------------------------------------------- ("null_dual")
      #"dual" #"null" = #"top": #"prop"
  ]

  [:= "A": #"prop"
      ----------------------------------------------- ("!_dual")
      #"dual" (#"!" "A") = #"?" (#"dual" "A"): #"prop"
  ];
  [:= "A": #"prop"
      ----------------------------------------------- ("?_dual")
      #"dual" (#"?" "A") = #"!" (#"dual" "A"): #"prop"
  ] *)

  ]}.

Derive linear_logic
       SuchThat (elab_lang_ext [] linear_logic_def linear_logic)
       As linear_logic_wf.
Proof. auto_elab. Qed.

