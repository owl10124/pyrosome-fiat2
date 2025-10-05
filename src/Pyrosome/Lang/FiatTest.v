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


Definition fiat_def : lang :=
  {[l/subst [exp_subst++value_subst]
    (* change everything to val *)
  [:|
      -----------------------------------------------
      #"nat": #"ty"
  ];
  [:|  
      "G": #"env"
       -----------------------------------------------
       #"0" : #"exp" "G" #"nat"
  ];
  [:|  
       "G": #"env",
       "n": #"exp" "G" #"nat"
       -----------------------------------------------
       #"1+" "n" : #"exp" "G" #"nat"
  ];
  [s|  "G": #"env",
       "n": #"exp" "G" #"nat", "m": #"exp" "G" #"nat"
       -----------------------------------------------
       #"neq" "n" "m" srt
  ];
  [:|  "G": #"env",
       "n": #"exp" "G" #"nat"
       -----------------------------------------------
       #"neq_0_l" : #"neq" #"0" (#"1+" "n")
  ];
  [:|  "G": #"env", "n": #"exp" "G" #"nat"
       -----------------------------------------------
       #"neq_0_r" : #"neq" (#"1+" "n") #"0"
  ];
  [:|  "G": #"env", "n": #"exp" "G" #"nat", "m": #"exp" "G" #"nat",
       "p" : #"neq" "n" "m"
       -----------------------------------------------
       #"neq_1+" "p" : #"neq" (#"1+" "n") (#"1+" "m")
  ];

  (* types *)
  [:| 
      -----------------------------------------------
      #"bool": #"ty"
  ];
  [:|
      "G": #"env"
      -----------------------------------------------
      #"true": #"exp" "G" #"bool"
  ];
  [:|
      "G": #"env"
      -----------------------------------------------
      #"false": #"exp" "G" #"bool"
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
      #"lempty" "A": #"exp" "G" (#"list" "A")
  ];

  (* unop definitions *)
  (*
  [:| 
      "G": #"env",
      "x": #"exp" "G" #"int"
      -----------------------------------------------
      #"-" "x": #"exp" "G" #"int"
     ];*)
  [:|
      "G": #"env",
      "x": #"exp" "G" #"bool"
      -----------------------------------------------
      #"notb" "x": #"exp" "G" #"bool"
  ];
  [:=
      "G": #"env"
      ----------------------------------------------- ("not_true")
      #"notb" #"true" = #"false": #"exp" "G" #"bool"
  ];
  [:=
      "G": #"env"
      ----------------------------------------------- ("not_false")
      #"notb" #"false" = #"true": #"exp" "G" #"bool"
  ];
  (* todo *)
  (* binop definitions *)
  [:|
      "G": #"env",
      "a": #"exp" "G" #"nat", "b": #"exp" "G" #"nat"
      -----------------------------------------------
      #"+" "a" "b": #"exp" "G" #"nat"
  ];
  [:=
      "G": #"env",
      "a": #"exp" "G" #"nat"
      ----------------------------------------------- ("add_0_r")
      #"+" "a" #"0" = "a": #"exp" "G" #"nat"
  ];
  [:=
      "G": #"env",
      "a": #"exp" "G" #"nat", "b": #"exp" "G" #"nat"
      ----------------------------------------------- ("add_n_Sm")
      #"+" "a" (#"1+" "b") = #"1+" (#"+" "a" "b")
      : #"exp" "G" #"nat"
  ];
  [:=
      "G": #"env",
      "a": #"exp" "G" #"nat", "b": #"exp" "G" #"nat"
      ----------------------------------------------- ("add_0_l")
      #"+" #"0" "a" = "a": #"exp" "G" #"nat"
  ];
  [:=
      "G": #"env",
      "a": #"exp" "G" #"nat", "b": #"exp" "G" #"nat"
      ----------------------------------------------- ("add_Sn_m")
      #"+" (#"1+" "a") "b"  = #"1+" (#"+" "a" "b")
      : #"exp" "G" #"nat"
  ];
  [:|
      "G": #"env",
      "a": #"exp" "G" #"bool", "b": #"exp" "G" #"bool"
      -----------------------------------------------
      #"andb" "a" "b": #"exp" "G" #"bool"
  ];
  [:|
      "G": #"env",
      "a": #"exp" "G" #"bool", "b": #"exp" "G" #"bool"
      -----------------------------------------------
      #"orb" "a" "b": #"exp" "G" #"bool"
  ];
  [:|
      "G": #"env",
      "A": #"ty",
      "x": #"exp" "G" "A",
      "l": #"exp" "G" (#"list" "A")
      -----------------------------------------------
      #"cons" "x" "l": #"exp" "G" (#"list" "A")
  ];
  [:|  (* can flesh out if i wanted to. but not important? it isn't in fiat2.. *)
      "G": #"env",
      "A": #"ty",
      "l": #"exp" "G" (#"list" "A")
      -----------------------------------------------
      #"car" "l": #"exp" "G" (#"list" "A")
  ];
  [:|
      "G": #"env",
      "A": #"ty",
      "l1": #"exp" "G" (#"list" "A"),
      "l2": #"exp" "G" (#"list" "A")
      -----------------------------------------------
      #"append" "l1" "l2": #"exp" "G" (#"list" "A")
  ];
  [:| 
      "G": #"env",
      "A": #"ty",
      "l": #"exp" "G" (#"list" "A"),
      "n": #"exp" "G" #"nat"
      -----------------------------------------------
      #"repeat" "l" "n": #"exp" "G" (#"list" "A")
  ];
  (* expr *)
  [:=
      "G": #"env"
      ----------------------------------------------- ("and_true")
      #"andb" #"true" #"true" = #"true": #"exp" "G" #"bool"
  ];
  [:=
      "G": #"env", "b": #"exp" "G" #"bool"
      ----------------------------------------------- ("and_false_l")
      #"andb" #"false" "b" = #"false": #"exp" "G" #"bool"
  ];
  [:=
      "G": #"env", "b": #"exp" "G" #"bool"
      ----------------------------------------------- ("and_false_r")
      #"andb" "b" #"false" = #"false": #"exp" "G" #"bool"
  ];
  [:=
      "G": #"env"
      ----------------------------------------------- ("or_false")
      #"orb" #"false" #"false" = #"false": #"exp" "G" #"bool"
  ];
  [:=
      "G": #"env", "b": #"exp" "G" #"bool"
      ----------------------------------------------- ("or_true_l")
      #"orb" #"true" "b" = #"true": #"exp" "G" #"bool"
  ];
  [:=
      "G": #"env", "b": #"exp" "G" #"bool"
      ----------------------------------------------- ("or_true_r")
      #"orb" "b" #"true" = #"true": #"exp" "G" #"bool"
  ];
  [:| 
      "G": #"env",
      "cond": #"exp" "G" #"bool",
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
  [:=
      "G": #"env",
      "A": #"ty",
      "l": #"exp" "G" (#"list" "A")
      -----------------------------------------------  ("append_empty")
      #"append" (#"lempty" "A") "l" = "l": #"exp" "G" (#"list" "A")
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "l1": #"exp" "G" (#"list" "A"),
      "l2": #"exp" "G" (#"list" "A"),
      "x": #"exp" "G" "A"
      -----------------------------------------------  ("append_nonempty")
      #"append" (#"cons" "x" "l1") "l2" = #"cons" "x" (#"append" "l1" "l2"): #"exp" "G" (#"list" "A")
  ];
  [:|
      "G": #"env",
      "A": #"ty",
      "l": #"exp" "G" (#"list" "A")
      ----------------------------------------------- 
      #"length" "l": #"exp" "G" #"nat"
  ];
  [:=
      "G": #"env",
      "A": #"ty"
      -----------------------------------------------  ("length_nil")
      #"length" (#"lempty" "A") = #"0" : #"exp" "G" #"nat"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "l": #"exp" "G" (#"list" "A"),
      "x": #"exp" "G" "A"
      -----------------------------------------------  ("length_induct")
       #"length" (#"cons" "x" "l") = #"1+" (#"length" "l") : #"exp" "G" #"nat"
  ];
  (* comparison *)
  (* we probably want to stick to values here, though...? *)
  [:| 
      -----------------------------------------------
      #"comparison": #"ty" (* analog: rocq corelib comparison *)
  ]; 
  (*
  [:| 
      "A": #"ty"
      -----------------------------------------------
      #"comparator" "A": #"ty" (* analog: A -> A -> comparison *)
  ]; 
  [:|
      "G": #"env",
      "A": #"ty",
      "cmp": #"comparator" "A",
      "x1": #"exp" "G" "A",
      "x2": #"exp" "G" "A"
      -----------------------------------------------
      "cmp" "x1" "x2" : #"exp" "G" #"comparison"
  ];
     later: attempt taking in higher-order comparator, for record and dict comparison
   *) 
  [:|
      "G": #"env"
      -----------------------------------------------
      #"Gt": #"exp" "G" #"comparison"
  ];
  [:|
      "G": #"env"
      -----------------------------------------------
      #"Lt": #"exp" "G" #"comparison"
  ];
  [:|
      "G": #"env"
      -----------------------------------------------
      #"Eq": #"exp" "G" #"comparison"
  ];
  [:|
      "G": #"env",
      "A": #"ty",
      "x1": #"exp" "G" "A",
      "x2": #"exp" "G" "A"
      -----------------------------------------------
      #"compare" "x1" "x2" : #"exp" "G" #"comparison"
  ];
  (* should this be an axiom?
  [:|
      "G": #"env",
      "A": #"ty",
      "x": #"exp" "G" "A",
      -----------------------------------------------
      #"compare" "x" "x" : #"exp" "G" #"comparison"
  ];
   *)
  (* comparison: bool *)
  [:=
      "G": #"env",
      "x1": #"exp" "G" #"bool"
      ----------------------------------------------- ("bool_eq")
      #"compare" "x1" "x1" = #"Eq": #"exp" "G" #"comparison"
  ];

  [:=
      "G": #"env"
      ----------------------------------------------- ("bool_lt")
      #"compare" #"false" #"true" = #"Lt": #"exp" "G" #"comparison"
  ];

  [:=
      "G": #"env"
      ----------------------------------------------- ("bool_gt")
      #"compare" #"true" #"false" = #"Gt": #"exp" "G" #"comparison"
  ];

  (* comparison: nat *)
  [:=
      "G": #"env",
      "x": #"exp" "G" #"nat"
      ----------------------------------------------- ("nat_eq")
      #"compare" "x" "x" = #"Eq": #"exp" "G" #"comparison"
  ];

  [:=
      "G": #"env",
      "x": #"exp" "G" #"nat"
      ----------------------------------------------- ("nat_lt")
      #"compare" #"0" (#"1+" "x") = #"Lt": #"exp" "G" #"comparison"
  ];

  [:=
      "G": #"env",
      "x": #"exp" "G" #"nat"
      ----------------------------------------------- ("nat_gt")
      #"compare" (#"1+" "x") #"0" = #"Gt": #"exp" "G" #"comparison"
  ];

  [:=
      "G": #"env",
      "x1": #"exp" "G" #"nat",
      "x2": #"exp" "G" #"nat"
      ----------------------------------------------- ("nat_induct")
      #"compare" (#"1+" "x1") (#"1+" "x2") = #"compare" "x1" "x2" : #"exp" "G" #"comparison"
  ];

  (* comparison: list (TODO) *)
  [:|
      "G": #"env",
      "A": #"ty",
      "l1": #"exp" "G" (#"list" "A"),
      "l2": #"exp" "G" (#"list" "A")
      -----------------------------------------------
      #"list_compare" "l1" "l2" : #"exp" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "l1": #"exp" "G" (#"list" "A"),
      "l2": #"exp" "G" (#"list" "A")
      ----------------------------------------------- ("list_compare_defn")
      #"compare" "l1" "l2" = #"list_compare" "l1" "l2" : #"exp" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "A": #"ty"
      ----------------------------------------------- ("list_empty_both")
      #"list_compare" (#"lempty" "A") (#"lempty" "A") = #"Eq" : #"exp" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "x": #"exp" "G" "A",
      "l": #"exp" "G" (#"list" "A")
      ----------------------------------------------- ("list_empty_l")
      #"list_compare" (#"lempty" "A") (#"cons" "x" "l") = #"Lt" : #"exp" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "x": #"exp" "G" "A",
      "l": #"exp" "G" (#"list" "A")
      ----------------------------------------------- ("list_empty_r")
      #"list_compare" (#"cons" "x" "l") (#"lempty" "A") = #"Gt" : #"exp" "G" #"comparison"
  ];
  [:|
      "G": #"env",
      "c1": #"exp" "G" #"comparison",
      "c2": #"exp" "G" #"comparison"
      -----------------------------------------------
      #"list_compare_base" "c1" "c2" : #"exp" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "c": #"exp" "G" #"comparison"
      ----------------------------------------------- ("list_compare_base_lt")
      #"list_compare_base" #"Lt" "c" = #"Lt" : #"exp" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "c": #"exp" "G" #"comparison"
      ----------------------------------------------- ("list_compare_base_gt")
      #"list_compare_base" #"Gt" "c" = #"Gt" : #"exp" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "c": #"exp" "G" #"comparison"
      ----------------------------------------------- ("list_compare_base_eq")
      #"list_compare_base" #"Eq" "c" = "c" : #"exp" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "x1": #"exp" "G" "A",
      "l1": #"exp" "G" (#"list" "A"),
      "x2": #"exp" "G" "A",
      "l2": #"exp" "G" (#"list" "A")
      ----------------------------------------------- ("list_induct")
      #"list_compare" (#"cons" "x1" "l1") (#"cons" "x2" "l2")
      = #"list_compare_base" (#"compare" "x1" "x2") (#"list_compare" "l1" "l2")
      : #"exp" "G" #"comparison"
  ]

    (* tenv            [already done? in RelTransfEx.v] *)
    (* expr            [already done? in Language.v] *)
    (* list A          [already done? in Language.v] *)
    (* string          [built-in] *)
    (* TRecord         [in Language.v] *)
    (* locals          [in RelTransfEx.v] *)
    (* (string * type) [need to define pairs of types, i think we already have it though] *)
    (* type_wf         [in TypeSystem.v BUT NOT NECESSARY FOR NOW] *)
    (* tenv_wf         [in TypeSound.v] *)
    (* type_of         [built-in?]  *)
    (* locals_wf       [in TypeSound.v] *)
    (* EFilter         [in Language.v] *)
    (* interp_expr     [in Interpret.v] *)
    (* free_immut_in   [in Utils.v] *)

    (* some notes:
       our environments, tenv, are maps from strings to types.

       tenv_wf checks that an environment is well-formed, i.e. that all defined variables are well-formed.
       it basically runs type_wf on all definitions in the env.

       type_of i can't find, seems to be in https://rocq-prover.org/doc/v8.19/api/coq-core/Typing/index.html ?? but
       my intuition is that it's defined somewhere though...

       (map.put Genv x (TRecord f1)) creates a new map, [idk what it actually does yet wait]
     *)

   (* Theorem efilter_efilter: forall (store env: locals) (Gstore Genv: tenv) (tb p p2: expr) (x y: string) (f1: list (string*type)),
        tenv_wf Gstore -> tenv_wf Genv -> locals_wf Gstore store -> locals_wf Genv env ->
        type_of Gstore (map.put Genv x (TRecord f1)) p TBool ->
        type_of Gstore (map.put Genv y (TRecord f1)) p2 TBool ->
        type_of Gstore Genv tb (TList (TRecord f1)) ->
        free_immut_in x p2 = false ->
        let pnew := EBinop OAnd p (ELet (EVar x) y p2) in
        interp_expr store env (EFilter (EFilter tb y p2) x p) =
        interp_expr store env (EFilter tb x pnew). *)


  ]}.

Derive fiat
  SuchThat (elab_lang_ext (exp_subst++value_subst) fiat_def fiat)
       As fiat_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve fiat_wf : elab_pfs.
