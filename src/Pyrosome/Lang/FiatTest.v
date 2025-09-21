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
  (*[:| 
      "l": #"list",
      "n": #"int"
      -----------------------------------------------
      #"repeat" "l" "n": #"list"
     ];*)
  (* expr *)
  [:| 
      "G": #"env",
      "cond": #"bool",
      "A": #"ty",
      "true_expr": #"exp" "G" "A",
      "false_expr": #"exp" "G" "A"
      -----------------------------------------------
      #"if" "cond" "true_expr" "false_expr": #"exp" "G" "A"
  ]
  ]}.

Derive stlc
       SuchThat (elab_lang_ext (exp_subst++value_subst) stlc_def stlc)
       As stlc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve stlc_wf : elab_pfs.


