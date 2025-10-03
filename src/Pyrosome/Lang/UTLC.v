Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst.
Import Core.Notations.

Require Coq.derive.Derive.

(* Locate "#".
Locate "ext". 
Locate "snoc". 
Locate exp_subst. 
(* Unset Printing Notations.  *)
Compute exp_subst. 
Compute exp_subst_def. 
Compute value_subst. 
Compute value_subst_def.  *)


Definition utlc_def : lang :=
  {[l/subst [exp_subst++value_subst]
  [:| 
      -----------------------------------------------
      #"*" : #"ty"
  ];
  [:| "G" : #"env",
       "e" : #"exp" (#"ext" "G" #"*") #"*"
       -----------------------------------------------
       (* #"lambda" #"*" "e" : #"val" "G" (#"*") *) (* doesn't work *)
       #"lambda" "e" : #"val" "G" (#"*")
  ];
  [:| "G" : #"env",
       "e" : #"exp" "G" #"*",
       "e'" : #"exp" "G" #"*"
       -----------------------------------------------
       #"app" "e" "e'" : #"exp" "G" #"*"
  ];
  [:= "G" : #"env",
      "e" : #"exp" (#"ext" "G" #"*") #"*",
      "v" : #"val" "G" #"*"
      ----------------------------------------------- ("UTLC-beta")
      #"app" (#"ret" (#"lambda" "e")) (#"ret" "v")
      (* #"app" (#"ret" (#"lambda" #"*" "e")) (#"ret" "v") *) (* doesn't work*)
      = #"exp_subst" (#"snoc" #"id" "v") "e"
      : #"exp" "G" #"*"
  ]
  ]}.

  Compute utlc_def.

Derive utlc
       SuchThat (elab_lang_ext (exp_subst++value_subst) utlc_def utlc)
       As utlc_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve utlc_wf : elab_pfs.


