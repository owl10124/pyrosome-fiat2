Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.

Compute value_subst_def.

Definition nat_lang_def : lang :=
  {[l
  [s|
      -----------------------------------------------
      #"natural" srt
  ];
  [:|  
       -----------------------------------------------
       #"0" : #"natural"
  ];
  [:|  "n": #"natural"
       -----------------------------------------------
       #"1+" "n" : #"natural"
  ];
  [s|  "n": #"natural", "m": #"natural"
       -----------------------------------------------
       #"neq" "n" "m" srt
  ];
  [:|  "n": #"natural"
       -----------------------------------------------
       #"neq_0_l" : #"neq" #"0" (#"1+" "n")
  ];
  [:|  "n": #"natural"
       -----------------------------------------------
       #"neq_0_r" : #"neq" (#"1+" "n") #"0"
  ];
  [:|  "n": #"natural", "m": #"natural",
       "p" : #"neq" "n" "m"
       -----------------------------------------------
       #"neq_1+" "p" : #"neq" (#"1+" "n") (#"1+" "m")
  ]
  ]}.


Derive nat_lang
       SuchThat (elab_lang_ext [] nat_lang_def nat_lang)
       As nat_lang_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve nat_lang_wf : elab_pfs.

Definition stlc_def : lang :=
  {[l/subst [exp_subst++value_subst]
  (* types *)
  [s| 
      -----------------------------------------------
      #"word" srt
  ];
  [s| 
      -----------------------------------------------
      #"int" srt
  ];
  [s| 
      -----------------------------------------------
      #"bool" srt
  ];
  [:|
      -----------------------------------------------
      #"true": #"bool"
  ];
  [:|
      -----------------------------------------------
      #"false": #"bool"
  ];

  [:|
      "A": #"ty"
      -----------------------------------------------
      #"list" "A": #"ty"
  ];

  [:|
      "G": #"env",
      "A": #"ty" 
      -----------------------------------------------
      #"lempty": #"val" "G" (#"list" "A")
  ];

  
  (* unops *)
  [:|
      "x": #"word"
      -----------------------------------------------
      #"w-" "x": #"word"
  ];
  [:| 
      "x": #"int"
      -----------------------------------------------
      #"-" "x": #"int"
  ];
  [:|
      "x": #"bool"
      -----------------------------------------------
      #"notb" "x": #"bool"
  ];
  [:=
      ----------------------------------------------- ("not_true")
      #"notb" #"true" = #"false": #"bool"
  ];
  [:=
      ----------------------------------------------- ("not_false")
      #"notb" #"false" = #"true": #"bool"
  ];
  (* todo *)
  (* binops *)
  [:| 
      "a": #"word",
      "b": #"word"
      -----------------------------------------------
      #"w+" "a" "b": #"word"
  ];
  [:|
      "a": #"int",
      "b": #"int"
      -----------------------------------------------
      #"+" "a" "b": #"int"
  ];
  [:|
      "a": #"bool",
      "b": #"bool"
      -----------------------------------------------
      #"andb" "a" "b": #"bool"
  ];
  [:|
      "G": #"env",
      "A": #"ty",
      "x": #"val" "G" "A",
      "l": #"val" "G" (#"list" "A")
      -----------------------------------------------
      #"cons" "x" "l": #"val" "G" (#"list" "A")
  ];
  [:| 
      "G": #"env",
      "A": #"ty",
      "l": #"val" "G" (#"list" "A"),
      "n": #"int"
      -----------------------------------------------
      #"repeat" "l" "n": #"val" "G" (#"list" "A")
  ];
  (* expr *)
  [:=
      ----------------------------------------------- ("and_true")
      #"andb" #"true" #"true" = #"true": #"bool"
  ];
  [:=
      "b": #"bool"
      ----------------------------------------------- ("and_false_l")
      #"andb" #"false" "b" = #"false": #"bool"
  ];
  [:=
      "b": #"bool"
      ----------------------------------------------- ("and_false_r")
      #"andb" "b" #"false" = #"false": #"bool"
  ];
  [:| 
      "G": #"env",
      "cond": #"bool",
      "A": #"ty",
      "true_expr": #"exp" "G" "A",
      "false_expr": #"exp" "G" "A"
      ----------------------------------------------- 
      #"if" "cond" "true_expr" "false_expr": #"exp" "G" "A"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "true_expr": #"exp" "G" "A",
      "false_expr": #"exp" "G" "A"
      ----------------------------------------------- ("if_true")
      #"if" #"true" "true_expr" "false_expr"
      = "true_expr"
      : #"exp" "G" "A"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "true_expr": #"exp" "G" "A",
      "false_expr": #"exp" "G" "A"
      ----------------------------------------------- ("if_false")
      #"if" #"false" "true_expr" "false_expr"
      = "false_expr"
      : #"exp" "G" "A"
  ];
  [:|
      "G": #"env",
      "A": #"ty",
      "l": #"val" "G" (#"list" "A")
      ----------------------------------------------- 
      #"length" "l": #"natural"
  ]
  (*
  [:=
      "G": #"env"
      -----------------------------------------------  ("length_nil")
      #"length" #"lempty" = #"0" : #"natural"
  ]
  [:=
      "G": #"env",
      "A": #"ty",
      "l": #"exp" "G" (#"list" "A"),
      "x": #"exp" "G" "A"
      -----------------------------------------------  ("length_induct")
       #"length" (#"cons" "x" "l") = #"1+" (#"length" "l") : #"natural"
  ]
   *)
  
  ]}.

Derive stlc
  SuchThat (elab_lang_ext (exp_subst++value_subst++nat_lang) stlc_def stlc)
       As stlc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve stlc_wf : elab_pfs.


