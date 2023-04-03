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
      #"ty" srt
  ];

  [s|
      -----------------------------------------------
      #"env" srt
  ];
  [:| -----------------------------------------------
      #"emp": #"env"
  ];
  [:| "G": #"env", "A": #"ty"
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
  [:= "G": #"env", "H": #"env", "A": #"ty"
      ----------------------------------------------- ("concat_ext")
      #"concat" "G" (#"ext" "H" "A") =
      #"ext" (#"concat" "G" "H") "A" : #"env"
  ];

  (* [:= "G": #"env", "A": #"ty"
      ----------------------------------------------- ("contraction")
      #"ext" (#"ext" "G" "A") "A" =
      #"ext" "G" "A" : #"env"
  ]; *)
  [:| "G": #"env", "H": #"env",
      "A": #"ty", "B": #"ty", "C": #"ty",
      "c": #"exp" (#"concat" (#"ext" (#"ext" "G" "A") "B") "H") "C"
      -----------------------------------------------
      #"exch" "c": #"exp" (#"concat" (#"ext" (#"ext" "G" "B") "A") "H") "C"
  ];

  [s| "G": #"env", "A": #"ty"
      -----------------------------------------------
      #"exp" "G" "A" srt
  ];
  (* [:| "G": #"env", "A": #"ty", "B": #"ty",
      "e": #"exp" "G" "B"
      -----------------------------------------------
      #"weaken" "e": #"exp" (#"ext" "G" "A") "B"
  ]; *)

  (* [:= "G": #"env", "A": #"ty",
      "e": #"exp" "G" "A",
      "f": #"exp" "G" "A"
      ----------------------------------------------- ("entailment_unique")
      "e" = "f" : #"exp" "G" "A"
  ] *)

  [:| "A": #"ty"
      -----------------------------------------------
      #"hd": #"exp" (#"ext" #"emp" "A") "A"
  ];

  (* [:| "A": #"ty"
      -----------------------------------------------
      #"dual" "A": #"ty"
  ];
  [:= "A": #"ty"
      ----------------------------------------------- ("dual_dual")
      #"dual" (#"dual" "A") = "A": #"ty"
  ]; *)

  [:| "A": #"ty", "B": #"ty"
      -----------------------------------------------
      #"times" "A" "B": #"ty"
  ];
  [:| "G": #"env", "H": #"env",
      "A": #"ty", "B": #"ty",
      "a": #"exp" "G" "A",
      "b": #"exp" "H" "B"
      -----------------------------------------------
      #"timesI" "a" "b": #"exp" (#"concat" "G" "H") (#"times" "A" "B")
  ];
  [:| "G": #"env", "H": #"env",
      "A": #"ty", "B": #"ty", "C": #"ty",
      "p": #"exp" "G" (#"times" "A" "B"),
      "c": #"exp" (#"ext" (#"ext" "H" "A") "B") "C"
      -----------------------------------------------
      #"timesE" "p" "c": #"exp" (#"concat" "G" "H") "C"
  ];

  [:| "A": #"ty", "B": #"ty"
      -----------------------------------------------
      #"with" "A" "B": #"ty"
  ];
  [:| "G": #"env",
      "A": #"ty", "B": #"ty",
      "a": #"exp" "G" "A",
      "b": #"exp" "G" "B"
      -----------------------------------------------
      #"withI" "a" "b": #"exp" "G" (#"with" "A" "B")
  ];
  [:| "G": #"env",
      "A": #"ty", "B": #"ty",
      "w": #"exp" "G" (#"with" "A" "B")
      -----------------------------------------------
      #"withEL" "w": #"exp" "G" "A"
  ];
  [:| "G": #"env",
      "A": #"ty", "B": #"ty",
      "w": #"exp" "G" (#"with" "A" "B")
      -----------------------------------------------
      #"withER" "w": #"exp" "G" "B"
  ];

  [:| "A": #"ty", "B": #"ty"
      -----------------------------------------------
      #"lolli" "A" "B": #"ty"
  ];
  [:| "G": #"env",
      "A": #"ty", "B": #"ty",
      "e": #"exp" (#"ext" "G" "A") "B"
      -----------------------------------------------
      #"lolliI" "e": #"exp" "G" (#"lolli" "A" "B")
  ];
  [:| "G": #"env", "H": #"env",
      "A": #"ty", "B": #"ty",
      "f": #"exp" "G" (#"lolli" "A" "B"),
      "a": #"exp" "H" "A"
      -----------------------------------------------
      #"lolliE" "f" "a": #"exp" (#"concat" "G" "H") "B"
  ];

  [:| -----------------------------------------------
      #"unit": #"ty"
  ];
  [:| -----------------------------------------------
      #"unitI": #"exp" #"emp" #"unit"
  ];
  [:| "G": #"env", "H": #"env",
      "C": #"ty",
      "u": #"exp" "G" #"unit",
      "c": #"exp" "H" "C"
      -----------------------------------------------
      #"unitE" "u" "c": #"exp" (#"concat" "G" "H") "C"
  ];

  [:| -----------------------------------------------
      #"top": #"ty"
  ];
  [:| "G": #"env"
      -----------------------------------------------
      #"topI": #"exp" "G" #"top"
  ];

  [:| "A": #"ty", "B": #"ty"
      -----------------------------------------------
      #"plus" "A" "B": #"ty"
  ];
  [:| "G": #"env",
      "A": #"ty", "B": #"ty",
      "a": #"exp" "G" "A"
      -----------------------------------------------
      #"plusIL" "a": #"exp" "G" (#"plus" "A" "B")
  ];
  [:| "G": #"env",
      "A": #"ty", "B": #"ty",
      "b": #"exp" "G" "B"
      -----------------------------------------------
      #"plusIR" "b": #"exp" "G" (#"plus" "A" "B")
  ];
  [:| "G": #"env", "H": #"env",
      "A": #"ty", "B": #"ty", "C": #"ty",
      "p": #"exp" "G" (#"plus" "A" "B"),
      "a": #"exp" (#"ext" "H" "A") "C",
      "b": #"exp" (#"ext" "H" "B") "C"
      -----------------------------------------------
      #"plusE" "p" "a" "b": #"exp" (#"concat" "G" "H") "C"
  ];

  [:| -----------------------------------------------
      #"null": #"ty"
  ];
  [:| "G": #"env", "H": #"env",
      "C": #"ty",
      "z": #"exp" "G" #"null"
      -----------------------------------------------
      #"nullE" "z": #"exp" (#"concat" "G" "H") "C"
  ]
(*
  [:= "A": #"ty", "B": #"ty"
      ----------------------------------------------- ("times_dual")
      #"dual" (#"times" "A" "B") = #"par" (#"dual" "A") (#"dual" "B")
      : #"ty"
  ];
  [:= "A": #"ty", "B": #"ty"
      ----------------------------------------------- ("par_dual")
      #"dual" (#"par" "A" "B") = #"times" (#"dual" "A") (#"dual" "B")
      : #"ty"
  ];
  [:= "A": #"ty", "B": #"ty"
      ----------------------------------------------- ("with_dual")
      #"dual" (#"with" "A" "B") = #"plus" (#"dual" "A") (#"dual" "B")
      : #"ty"
  ];
  [:= "A": #"ty", "B": #"ty"
      ----------------------------------------------- ("plus_dual")
      #"dual" (#"plus" "A" "B") = #"with" (#"dual" "A") (#"dual" "B")
      : #"ty"
  ];

  [:= ----------------------------------------------- ("unit_dual")
      #"dual" #"unit" = #"bot": #"ty"
  ];
  [:= ----------------------------------------------- ("bot_dual")
      #"dual" #"bot" = #"unit": #"ty"
  ];
  [:= ----------------------------------------------- ("top_dual")
      #"dual" #"top" = #"null": #"ty"
  ];
  [:= ----------------------------------------------- ("null_dual")
      #"dual" #"null" = #"top": #"ty"
  ]

  [:= "A": #"ty"
      ----------------------------------------------- ("!_dual")
      #"dual" (#"!" "A") = #"?" (#"dual" "A"): #"ty"
  ];
  [:= "A": #"ty"
      ----------------------------------------------- ("?_dual")
      #"dual" (#"?" "A") = #"!" (#"dual" "A"): #"ty"
  ] *)

  ]}.

Derive linear_logic
       SuchThat (elab_lang_ext [] linear_logic_def linear_logic)
       As linear_logic_wf.
Proof. auto_elab. Qed.
