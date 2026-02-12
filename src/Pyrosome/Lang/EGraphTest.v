Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst Tools.EGraph.Automation Tools.EGraph.Defs.
Import Core.Notations.

Require Coq.derive.Derive.

Compute value_subst_def.


Definition egraph_test_def : lang :=
  {[l/subst [exp_subst++value_subst]
    (* change everything to val *)
     (* put nat into its own module *)
  [:|
     "t": #"ty"
      ----------------------------------------------- 
      #"a" "t" : #"ty"
  ];
  [:|
      ----------------------------------------------- 
      #"b" : #"ty"
  ];
  [:|
      
      ----------------------------------------------- 
      #"c" : #"ty"
  ];
  [:=
     "G": #"env"
      ----------------------------------------------- ("abc")
      #"a" #"b" = #"c" : #"ty"
  ]
  ]}.

Compute egraph_test_def.

(* filter to term_eq rules
   bundle into a rule_set
   call egraph_simpl *)


Derive egraph_test
  SuchThat (elab_lang_ext (exp_subst++value_subst) egraph_test_def egraph_test)
       As egraph_test_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve egraph_test_wf : elab_pfs.

Compute egraph_test.

Definition to_named_list {A : Type} (n : string) (x : option A) : named_list A :=
  match x with
  | Some x' => [(n, x')]
  | None => []
  end.


Compute PositiveInstantiation.egraph_simpl' egraph_test 100 100 2000 [] {{e#"a" #"b"}}.

(* next step: slightly larger program *)
