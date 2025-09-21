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
      ----------------------------------------------- ("not_falsej")
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
      "A": #"ty",
      "l": #"val" "G" (#"list" "A"),
      "n": #"int"
      -----------------------------------------------
      #"repeat" "l" "n": #"val" "G" (#"list" "A")
  ];
  (* expr *)
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
  ]
  ]}.

Derive stlc
       SuchThat (elab_lang_ext (exp_subst++value_subst) stlc_def stlc)
       As stlc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve stlc_wf : elab_pfs.


