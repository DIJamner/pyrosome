
  
(*TODO: put in hoisting file*)
Definition hoist_lang_def : lang :=
  [[l
      [s| "A" : #"ty"
          -----------------------------------------------
          #"program" "A" srt
      ];
   [:| "ht" : #"heapty",
       "H" : #"heap" "HT",
       "A" : #"ty",
       "e" : #"blk" "HT" "A"             
       -----------------------------------------------
       #"prog" "H" "e" : #"program" "A"
      ];
      [:| "A" : #"ty"
          -----------------------------------------------
          #"neg" "A" : #"ty"
      ];
   
  [:| "G" : #"ty",
      "A" : #"ty",
      "B" : #"ty",
      "l" : #"val" "G" (#"label" (#"prod" "A" "B")),
      "v" : #"val" "G" "A"
      -----------------------------------------------
      #"closure" "A" "l" "v" : #"val" "G" (#"neg" "B")
   ];
   [:| "G" : #"env",
       "A" : #"ty",
       "v1" : #"val" "G" (#"neg" "A"),
       "v2" : #"val" "G" "A"
      -----------------------------------------------
      #"jmp" "v1" "v2" : #"blk" "G"
   ];
  [:= "G" : #"env",
      "A" : #"ty",
      "B" : #"ty",
      "e" : #"blk" (#"prod" "A" "B"),
      "v" : #"val" "G" "A",
      "v'" : #"val" "G" "B"
      ----------------------------------------------- ("jmp_beta")
      #"jmp" (#"closure" "A" "e" "v") "v'"
      = #"blk_subst" (#"pair" "v" "v'") "e"
      : #"blk" "G"
  ];
  [:= "G" : #"ty", "A" : #"ty",
      "v1" : #"val" "G" (#"neg" "A"),
      "v2" : #"val" "G" "A",
      "G'" : #"ty",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("jmp_subst")
      #"blk_subst" "g" (#"jmp" "v1" "v2")
      = #"jmp" (#"val_subst" "g" "v1") (#"val_subst" "g" "v2")
      : #"blk" "G'"
  ];  
  [:= "G" : #"ty", "A" : #"ty", "B" : #"ty",
      "e" : #"blk" (#"prod" "A" "B"),
      "v" : #"val" (#"ext" "G" "A"),
      "G'" : #"ty",
      "g" : #"sub" "G'" "G"
      ----------------------------------------------- ("clo_subst")
      #"val_subst" "g" (#"closure" "B" "e" "v")
      = #"closure" "B" "e" (#"val_subst" "g" "e")
      : #"val" "G'" (#"neg" "B")
  ]
  ]].
