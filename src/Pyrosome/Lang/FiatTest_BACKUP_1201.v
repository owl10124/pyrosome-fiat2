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


Definition fiat_def : lang :=
  {[l/subst [exp_subst++value_subst]
    (* change everything to val *)
     (* put nat into its own module *)
  [:|
      -----------------------------------------------
      #"nat": #"ty"
  ];
  [:|  
      "G": #"env"
       -----------------------------------------------
       #"0" : #"val" "G" #"nat"
  ];
  [:|  
       "G": #"env",
       "n": #"val" "G" #"nat"
       -----------------------------------------------
       #"1+" "n" : #"val" "G" #"nat"
  ];
  [s|  "G": #"env",
       "n": #"val" "G" #"nat", "m": #"val" "G" #"nat"
       -----------------------------------------------
       #"neq" "n" "m" srt
  ];
  [:|  "G": #"env",
       "n": #"val" "G" #"nat"
       -----------------------------------------------
       #"neq_0_l" : #"neq" #"0" (#"1+" "n")
  ];
  [:|  "G": #"env", "n": #"val" "G" #"nat"
       -----------------------------------------------
       #"neq_0_r" : #"neq" (#"1+" "n") #"0"
  ];
  [:|  "G": #"env", "n": #"val" "G" #"nat", "m": #"val" "G" #"nat",
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
      #"true": #"val" "G" #"bool"
  ];
  [:|
      "G": #"env"
      -----------------------------------------------
      #"false": #"val" "G" #"bool"
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
      #"lempty" "A": #"val" "G" (#"list" "A")
  ];

  (* unop definitions *)
  (*
  [:| 
      "G": #"env",
      "x": #"val" "G" #"int"
      -----------------------------------------------
      #"-" "x": #"val" "G" #"int"
     ];*)
  [:|
      "G": #"env",
      "x": #"val" "G" #"bool"
      -----------------------------------------------
      #"notb" "x": #"val" "G" #"bool"
  ];
  [:=
      "G": #"env"
      ----------------------------------------------- ("not_true")
      #"notb" #"true" = #"false": #"val" "G" #"bool"
  ];
  [:=
      "G": #"env"
      ----------------------------------------------- ("not_false")
      #"notb" #"false" = #"true": #"val" "G" #"bool"
  ];
  [:|
      "G": #"env",
      "a": #"val" "G" #"bool", "b": #"val" "G" #"bool"
      -----------------------------------------------
      #"andb" "a" "b": #"val" "G" #"bool"
  ];
  [:|
      "G": #"env",
      "a": #"val" "G" #"bool", "b": #"val" "G" #"bool"
      -----------------------------------------------
      #"orb" "a" "b": #"val" "G" #"bool"
  ];
  [:=
      "G": #"env"
      ----------------------------------------------- ("and_true")
      #"andb" #"true" #"true" = #"true": #"val" "G" #"bool"
  ];
  [:=
      "G": #"env", "b": #"val" "G" #"bool"
      ----------------------------------------------- ("and_false_l")
      #"andb" #"false" "b" = #"false": #"val" "G" #"bool"
  ];
  [:=
      "G": #"env", "b": #"val" "G" #"bool"
      ----------------------------------------------- ("and_false_r")
      #"andb" "b" #"false" = #"false": #"val" "G" #"bool"
  ];
  [:=
      "G": #"env", "b": #"val" "G" #"bool"
      ----------------------------------------------- ("and_true_l")
      #"andb" #"true" "b" = "b": #"val" "G" #"bool"
  ];
  [:=
      "G": #"env", "b": #"val" "G" #"bool"
      ----------------------------------------------- ("and_true_r")
      #"andb" "b" #"true" = "b": #"val" "G" #"bool"
  ];
  [:=
      "G": #"env", "b": #"val" "G" #"bool"
      ----------------------------------------------- ("non_cont_l")
      #"andb" (#"notb" "b") "b" = #"false": #"val" "G" #"bool"
  ];
  [:=
      "G": #"env", "b": #"val" "G" #"bool"
      ----------------------------------------------- ("non_cont_r")
      #"andb" "b" (#"notb" "b") = #"false": #"val" "G" #"bool"
  ];

  (* todo *)
  (* binop definitions *)
    (*
  [:|
      "G": #"env",
      "a": #"val" "G" #"nat", "b": #"val" "G" #"nat"
      -----------------------------------------------
      #"+" "a" "b": #"val" "G" #"nat"
  ];
  [:=
      "G": #"env",
      "a": #"val" "G" #"nat"
      ----------------------------------------------- ("add_0_r")
      #"+" "a" #"0" = "a": #"val" "G" #"nat"
  ];
  [:=
      "G": #"env",
      "a": #"val" "G" #"nat", "b": #"val" "G" #"nat"
      ----------------------------------------------- ("add_n_Sm")
      #"+" "a" (#"1+" "b") = #"1+" (#"+" "a" "b")
      : #"val" "G" #"nat"
  ];
  [:=
      "G": #"env",
      "a": #"val" "G" #"nat", "b": #"val" "G" #"nat"
      ----------------------------------------------- ("add_0_l")
      #"+" #"0" "a" = "a": #"val" "G" #"nat"
  ];
  [:=
      "G": #"env",
      "a": #"val" "G" #"nat", "b": #"val" "G" #"nat"
      ----------------------------------------------- ("add_Sn_m")
      #"+" (#"1+" "a") "b"  = #"1+" (#"+" "a" "b")
      : #"val" "G" #"nat"
  ];
*)
  [:=
      "G": #"env"
      ----------------------------------------------- ("or_false")
      #"orb" #"false" #"false" = #"false": #"val" "G" #"bool"
  ];
  [:=
      "G": #"env", "b": #"val" "G" #"bool"
      ----------------------------------------------- ("or_true_l")
      #"orb" #"true" "b" = #"true": #"val" "G" #"bool"
  ];
  [:=
      "G": #"env", "b": #"val" "G" #"bool"
      ----------------------------------------------- ("or_true_r")
      #"orb" "b" #"true" = #"true": #"val" "G" #"bool"
  ];
  [:| 
      "G": #"env",
      "cond": #"val" "G" #"bool",
      "A": #"ty",
      "true_expr": #"val" "G" "A",
      "false_expr": #"val" "G" "A"
      ----------------------------------------------- 
      #"if" "cond" "true_expr" "false_expr": #"val" "G" "A"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "true_expr": #"val" "G" "A",
      "false_expr": #"val" "G" "A"
      ----------------------------------------------- ("if_true")
      #"if" #"true" "true_expr" "false_expr"
      = "true_expr"
      : #"val" "G" "A"
      ];
  [:=
      "G": #"env",
      "A": #"ty",
      "true_expr": #"val" "G" "A",
      "false_expr": #"val" "G" "A"
      ----------------------------------------------- ("if_false")
      #"if" #"false" "true_expr" "false_expr"
      = "false_expr"
      : #"val" "G" "A"
  ];
  [:|
      "G": #"env",
      "A": #"ty",
      "x": #"val" "G" "A",
      "l": #"val" "G" (#"list" "A")
      -----------------------------------------------
      #"cons" "x" "l": #"val" "G" (#"list" "A")
  ];
  [:|  (* can flesh out if i wanted to. but not important? it isn't in fiat2.. *)
      "G": #"env",
      "A": #"ty",
      "l": #"val" "G" (#"list" "A")
      -----------------------------------------------
      #"car" "l": #"val" "G" (#"list" "A")
  ];
  [:|
      "G": #"env",
      "A": #"ty",
      "l1": #"val" "G" (#"list" "A"),
      "l2": #"val" "G" (#"list" "A")
      -----------------------------------------------
      #"append" "l1" "l2": #"val" "G" (#"list" "A")
  ];
  [:| 
      "G": #"env",
      "A": #"ty",
      "l": #"val" "G" (#"list" "A"),
      "n": #"val" "G" #"nat"
      -----------------------------------------------
      #"repeat" "l" "n": #"val" "G" (#"list" "A")
  ];
  (* expr *)
  [:=
      "G": #"env",
      "A": #"ty",
      "l": #"val" "G" (#"list" "A")
      -----------------------------------------------  ("append_empty")
      #"append" (#"lempty" "A") "l" = "l": #"val" "G" (#"list" "A")
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "l1": #"val" "G" (#"list" "A"),
      "l2": #"val" "G" (#"list" "A"),
      "x": #"val" "G" "A"
      -----------------------------------------------  ("append_nonempty")
      #"append" (#"cons" "x" "l1") "l2" = #"cons" "x" (#"append" "l1" "l2"): #"val" "G" (#"list" "A")
  ];
  [:|
      "G": #"env",
      "A": #"ty",
      "l": #"val" "G" (#"list" "A")
      ----------------------------------------------- 
      #"length" "l": #"val" "G" #"nat"
  ];
  [:=
      "G": #"env",
      "A": #"ty"
      -----------------------------------------------  ("length_nil")
      #"length" (#"lempty" "A") = #"0" : #"val" "G" #"nat"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "l": #"val" "G" (#"list" "A"),
      "x": #"val" "G" "A"
      -----------------------------------------------  ("length_induct")
       #"length" (#"cons" "x" "l") = #"1+" (#"length" "l") : #"val" "G" #"nat"
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
      "x1": #"val" "G" "A",
      "x2": #"val" "G" "A"
      -----------------------------------------------
      "cmp" "x1" "x2" : #"val" "G" #"comparison"
  ];
     later: attempt taking in higher-order comparator, for record and dict comparison
   *) 
    (*
  [:|
      "G": #"env"
      -----------------------------------------------
      #"Gt": #"val" "G" #"comparison"
  ];
  [:|
      "G": #"env"
      -----------------------------------------------
      #"Lt": #"val" "G" #"comparison"
  ];
  [:|
      "G": #"env"
      -----------------------------------------------
      #"Eq": #"val" "G" #"comparison"
  ];
  [:|
      "G": #"env",
      "A": #"ty",
      "x1": #"val" "G" "A",
      "x2": #"val" "G" "A"
      -----------------------------------------------
      #"compare" "x1" "x2" : #"val" "G" #"comparison"
  ];
  (* should this be an axiom?
  [:|
      "G": #"env",
      "A": #"ty",
      "x": #"val" "G" "A",
      -----------------------------------------------
      #"compare" "x" "x" : #"val" "G" #"comparison"
  ];
   *)
  (* comparison: bool *)
  [:=
      "G": #"env",
      "x1": #"val" "G" #"bool"
      ----------------------------------------------- ("bool_eq")
      #"compare" "x1" "x1" = #"Eq": #"val" "G" #"comparison"
  ];

  [:=
      "G": #"env"
      ----------------------------------------------- ("bool_lt")
      #"compare" #"false" #"true" = #"Lt": #"val" "G" #"comparison"
  ];

  [:=
      "G": #"env"
      ----------------------------------------------- ("bool_gt")
      #"compare" #"true" #"false" = #"Gt": #"val" "G" #"comparison"
  ];

  (* comparison: nat *)
  [:=
      "G": #"env",
      "x": #"val" "G" #"nat"
      ----------------------------------------------- ("nat_eq")
      #"compare" "x" "x" = #"Eq": #"val" "G" #"comparison"
  ];

  [:=
      "G": #"env",
      "x": #"val" "G" #"nat"
      ----------------------------------------------- ("nat_lt")
      #"compare" #"0" (#"1+" "x") = #"Lt": #"val" "G" #"comparison"
  ];

  [:=
      "G": #"env",
      "x": #"val" "G" #"nat"
      ----------------------------------------------- ("nat_gt")
      #"compare" (#"1+" "x") #"0" = #"Gt": #"val" "G" #"comparison"
  ];

  [:=
      "G": #"env",
      "x1": #"val" "G" #"nat",
      "x2": #"val" "G" #"nat"
      ----------------------------------------------- ("nat_induct")
      #"compare" (#"1+" "x1") (#"1+" "x2") = #"compare" "x1" "x2" : #"val" "G" #"comparison"
  ];

  (* comparison: list (TODO) *)
  [:|
      "G": #"env",
      "A": #"ty",
      "l1": #"val" "G" (#"list" "A"),
      "l2": #"val" "G" (#"list" "A")
      -----------------------------------------------
      #"list_compare" "l1" "l2" : #"val" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "l1": #"val" "G" (#"list" "A"),
      "l2": #"val" "G" (#"list" "A")
      ----------------------------------------------- ("list_compare_defn")
      #"compare" "l1" "l2" = #"list_compare" "l1" "l2" : #"val" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "A": #"ty"
      ----------------------------------------------- ("list_empty_both")
      #"list_compare" (#"lempty" "A") (#"lempty" "A") = #"Eq" : #"val" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "x": #"val" "G" "A",
      "l": #"val" "G" (#"list" "A")
      ----------------------------------------------- ("list_empty_l")
      #"list_compare" (#"lempty" "A") (#"cons" "x" "l") = #"Lt" : #"val" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "x": #"val" "G" "A",
      "l": #"val" "G" (#"list" "A")
      ----------------------------------------------- ("list_empty_r")
      #"list_compare" (#"cons" "x" "l") (#"lempty" "A") = #"Gt" : #"val" "G" #"comparison"
  ];
  [:|
      "G": #"env",
      "c1": #"val" "G" #"comparison",
      "c2": #"val" "G" #"comparison"
      -----------------------------------------------
      #"list_compare_base" "c1" "c2" : #"val" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "c": #"val" "G" #"comparison"
      ----------------------------------------------- ("list_compare_base_lt")
      #"list_compare_base" #"Lt" "c" = #"Lt" : #"val" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "c": #"val" "G" #"comparison"
      ----------------------------------------------- ("list_compare_base_gt")
      #"list_compare_base" #"Gt" "c" = #"Gt" : #"val" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "c": #"val" "G" #"comparison"
      ----------------------------------------------- ("list_compare_base_eq")
      #"list_compare_base" #"Eq" "c" = "c" : #"val" "G" #"comparison"
  ];
  [:=
      "G": #"env",
      "A": #"ty",
      "x1": #"val" "G" "A",
      "l1": #"val" "G" (#"list" "A"),
      "x2": #"val" "G" "A",
      "l2": #"val" "G" (#"list" "A")
      ----------------------------------------------- ("list_induct")
      #"list_compare" (#"cons" "x1" "l1") (#"cons" "x2" "l2")
      = #"list_compare_base" (#"compare" "x1" "x2") (#"list_compare" "l1" "l2")
      : #"val" "G" #"comparison"
  ];
*)
  (* maps, placeholder for now *)
  (* Class map {key value} := mk {
    rep : Type;

    (* fundamental operation, all others are axiomatized in terms of this one *)
    get: rep -> key -> option value;

    empty : rep;
    put : rep -> key -> value -> rep;
    remove : rep -> key -> rep;
    fold{R: Type}: (R -> key -> value -> R) -> R -> rep -> R;
  }. *)

    (* OLD ONE DON'T USE I GUESS
  [:|
      "G": #"env",
      "l" : #"list_ty"
      ----------------------------------------------- 
      #"rempty" : #"val" "G" #"record"
  ];
    
  [:|
     "G": #"env",
     "R": #"val" "G" #"rec_type",
     "A": #"ty"
      ----------------------------------------------- 
      #"cons_record" "R" "A" : #"val" "G" #"rec_type"
  ]
*)

    
    (*
  [:|
      ----------------------------------------------- 
      #"map" : #"ty"
  ];
  [:|
      "G" : #"env"
      ----------------------------------------------- 
      #"mempty" : #"val" "G" #"map"
  ];
  [:|
      "G" : #"env",
      "m" : #"val" "G" #"map",
      "A" : #"ty",
      "v1" : #"val" "G" "A",
      "B" : #"ty",
      "v2" : #"val" "G" "B"
      ----------------------------------------------- 
      #"put" "m" "v1" "v2" : #"val" "G" #"map"
  ];

  [:|
      "G" : #"env"
      ----------------------------------------------- 
      #"get" : #"ty"
  ];
*)

  (* strings and record types, placeholder *)
    
    (*
  [:|
      ----------------------------------------------- 
      #"string" : #"ty"
  ];
  [:|
      "A": #"ty",
      "B": #"ty"
      ----------------------------------------------- 
      #"pair" "A" "B" : #"ty"
  ];
*)
  [s|
      ----------------------------------------------- 
      #"list_ty" srt
  ];
  [:|
      ----------------------------------------------- 
      #"empty_list_ty" : #"list_ty"
  ];
  [:|
      "A": #"ty",
      "l": #"list_ty"
      ----------------------------------------------- 
      #"cons_list_ty" "A" "l" : #"list_ty"
  ];

    (* wait nvm, i can use ext and ty_ext here? *)
  [:|
     "l" : #"list_ty"
      ----------------------------------------------- 
      #"Trecord" "l" : #"ty"
  ];

  [:|
      "G": #"env"
      ----------------------------------------------- 
      #"empty_record" : #"val" "G" (#"Trecord" #"empty_list_ty")
  ];

  [:|
      "G": #"env",
      "A": #"ty",
      "l": #"list_ty",
      "v": #"val" "G" "A",
      "record_val" : #"val" "G" (#"Trecord" "l")
      ----------------------------------------------- 
      #"cons_record" "v" "record_val" : #"val" "G" (#"Trecord" (#"cons_list_ty" "A" "l"))
  ];

    (* look at filter optimizations, read fiat2/database textbooks *)
    (* combine w/ e.g. join_into_filter_right *)
  [:|
      "G": #"env",
      "t": #"ty",
      "tb": #"val" "G" (#"list" "t"),
      "p": #"val" (#"ext" "G" "t") #"bool"
      ----------------------------------------------- 
      #"filter" "tb" "p": #"val" "G" (#"list" "t")
  ];

  (* If the predicate is false, then there is nothing in the table *)
  [:=
      "G": #"env",
      "t": #"ty",
      "tb": #"val" "G" (#"list" "t")
      ----------------------------------------------- ("filter_empty")
      #"filter" "tb" (#"false") = #"lempty" "t": #"val" "G" (#"list" "t")
  ];

  [:|
      "G": #"env",
      "t": #"ty",
      "tb": #"val" "G" (#"list" "t")
      -----------------------------------------------
      #"exclude" "tb" : #"val" "G" #"bool"
  ];

  [:=
      "G": #"env",
      "t": #"ty",
      "tb": #"val" "G" (#"list" "t")
      ----------------------------------------------- ("filter_exclude")
      #"filter" "tb" (#"val_subst" #"wkn" (#"exclude" "tb")) = #"lempty" "t": #"val" "G" (#"list" "t")
  ];
    
    
    (*
      Theorem efilter_efilter: forall (store env: locals) (Gstore Genv: tenv) (tb p p2: expr) (x y: string) (f1: list (string*type)),
        tenv_wf Gstore -> tenv_wf Genv -> locals_wf Gstore store -> locals_wf Genv env ->
        type_of Gstore (map.put Genv x (TRecord f1)) p TBool ->
        type_of Gstore (map.put Genv y (TRecord f1)) p2 TBool ->
        type_of Gstore Genv tb (TList (TRecord f1)) ->
        free_immut_in x p2 = false ->
        let pnew := EBinop OAnd p (ELet (EVar x) y p2) in
        interp_expr store env (EFilter (EFilter tb y p2) x p) =
        interp_expr store env (EFilter tb x pnew). *)
  [:=
      "G": #"env",
      "f1": #"list_ty",
      "tb": #"val" "G" (#"list" (#"Trecord" "f1")),
      "p": #"val" (#"ext" "G" (#"Trecord" "f1")) #"bool",
      "p2": #"val" (#"ext" "G" (#"Trecord" "f1")) #"bool"
      ----------------------------------------------- ("filter_filter_list_ty")
      #"filter" (#"filter" "tb" "p") "p2" 
      = #"filter" "tb" (#"andb" "p" "p2")
      : #"val" "G" (#"list" (#"Trecord" "f1")) (* same columns, right? *)
   ];
    (*
  [:=
      "G": #"env",
      "rec_type" : #"ty",
      "tb": #"val" "G" (#"list" "rec_type"),
      "p": #"val" (#"ext" "G" "rec_type") #"bool",
      "p2": #"val" (#"ext" "G" "rec_type") #"bool"
      ----------------------------------------------- ("filter_filter_generic")
      #"filter" (#"filter" "tb" "p") "p2" 
      = #"filter" "tb" (#"andb" "p" "p2")
      : #"val" "G" (#"list" "rec_type")
   ];
*)
    
    (* proj
  | TyEProj e t1 x r t2 : type_of Gstore Genv e (TList t1) ->
                          type_of Gstore (map.put Genv x t1) r t2 ->
                          type_of Gstore Genv (EProj e x r) (TList t2).
     *)

  [:|
      "G": #"env",
      "t1": #"ty",
      "t2": #"ty",
      "e": #"val" "G" (#"list" "t1"), (* can be any tpye *)
      "r": #"val" (#"ext" "G" "t1") "t2"
      -----------------------------------------------  
      #"proj" "e" "r": #"val" "G" (#"list" "t2") (* probably want a subset of it... *)
  ];

    (* join
  | TyEJoin e1 t1 e2 t2 x y p r t3 : type_of Gstore Genv e1 (TList t1) ->
                                     type_of Gstore Genv e2 (TList t2) ->
                                     type_of Gstore (map.put (map.put Genv x t1) y t2) p TBool ->
                                     type_of Gstore (map.put (map.put Genv x t1) y t2) r t3 ->
                                     type_of Gstore Genv (EJoin e1 e2 x y p r) (TList t3)
       *)
  [:|
     "G":  #"env",
     "t1": #"ty",
     "t2": #"ty",
     "t3": #"ty",
     "e1": #"val" "G" (#"list" "t1"),
     "e2": #"val" "G" (#"list" "t2"),
     "p":  #"val" (#"ext" (#"ext" "G" "t1") "t2") #"bool",
     "r":  #"val" (#"ext" (#"ext" "G" "t1") "t2") "t3"
      -----------------------------------------------  
     #"join" "e1" "e2" "p" "r": #"val" "G" (#"list" "t3")
  ];

  (* If the predicate is false, then we there is nothing in the table *)
  [:=
     "G":  #"env",
     "t1": #"ty",
     "t2": #"ty",
     "t3": #"ty",
     "e1": #"val" "G" (#"list" "t1"),
     "e2": #"val" "G" (#"list" "t2"),
     "r":  #"val" (#"ext" (#"ext" "G" "t1") "t2") "t3"
      -----------------------------------------------  ("join_empty")
     #"join" "e1" "e2" (#"false") "r" = #"lempty" "t3": #"val" "G" (#"list" "t3")
  ];

(*
    Theorem proj_proj: forall (store env: locals) (Gstore Genv: tenv) (tb r r2: expr) (x x2: string) (r2cols rcols: list string),
        free_immut_in x2 r = false ->
        let rnew := ELet r2 x r in
        interp_expr store env (EProj (EProj tb x2 r2) x r) =
        interp_expr store env (EProj tb x2 rnew).
*)
    [:=
      "G": #"env",
      "t1": #"ty",
      "t2": #"ty",
      "t3": #"ty",
      "tb": #"val" "G" (#"list" "t1"), 
      "r": #"val" (#"ext" "G" "t2") "t3",
      "r2": #"val" (#"ext" "G" "t1") "t2"
      ----------------------------------------------- ("proj_proj")
      #"proj" (#"proj" "tb" "r2") "r" = #"proj" "tb" (#"val_subst" (#"snoc" #"wkn" "r2") "r"): #"val" "G" (#"list" "t3")
                                                        (* #"sub" (#"ext" "G" "t1") (#"ext" "G" "t2") *)
    ];
    (* TODO filter_pushdown_head *)
    (* TODO look at examples where the filter can be simplified further *)
    (* TODO look at join[filter[join]] *)
    (*
    Theorem filter_into_join_left: forall (store env: locals) (Gstore Genv: tenv) (tb1 tb2 p r pf: expr) (x y xf: string) (f1 f2: list (string * type)),
        tenv_wf Gstore -> tenv_wf Genv -> locals_wf Gstore store -> locals_wf Genv env ->
        type_of Gstore (map.put (map.put Genv x (TRecord f1)) y (TRecord f2)) p TBool ->
        type_of Gstore (map.put Genv xf (TRecord f1)) pf TBool ->
        type_of Gstore Genv tb1 (TList (TRecord f1)) ->
        type_of Gstore Genv tb2 (TList (TRecord f2)) ->
        free_immut_in x pf = false ->
        free_immut_in y pf = false ->
        x <> y ->
        let pnew := EBinop OAnd p (ELet (EVar x) xf pf) in
        interp_expr store env (EJoin (EFilter tb1 xf pf) tb2 x y p r)
        = interp_expr store env (EJoin tb1 tb2 x y pnew r). *)
    [:=
       "G":   #"env",
       "f1":  #"list_ty",
       "f2":  #"list_ty",
       "t":   #"ty",
       "p":   #"val" (#"ext" (#"ext" "G" (#"Trecord" "f1")) (#"Trecord" "f2")) #"bool",
       "r":   #"val" (#"ext" (#"ext" "G" (#"Trecord" "f1")) (#"Trecord" "f2")) "t", (* arbitrary type *)
       "pf":  #"val" (#"ext" "G" (#"Trecord" "f1")) #"bool",
       "tb1": #"val" "G" (#"list" (#"Trecord" "f1")),
       "tb2": #"val" "G" (#"list" (#"Trecord" "f2"))
      ----------------------------------------------- ("filter_into_join_left")
      #"join" (#"filter" "tb1" "pf") "tb2" "p" "r" = #"join" "tb1" "tb2"
                                                       (#"andb" "p"
                                                                (#"val_subst" #"wkn" "pf"))
                                                       "r" : #"val" "G" (#"list" "t")
    ];
      (*
    Theorem filter_into_join_right: forall(store env: locals) (Gstore Genv: tenv) (tb1 tb2 p r pf: expr) (x y yf: string) (f1 f2: list (string * type)),
        tenv_wf Gstore -> tenv_wf Genv -> locals_wf Gstore store -> locals_wf Genv env ->
        type_of Gstore (map.put (map.put Genv x (TRecord f1)) y (TRecord f2)) p TBool ->
        type_of Gstore (map.put Genv yf (TRecord f2)) pf TBool ->
        type_of Gstore Genv tb1 (TList (TRecord f1)) ->
        type_of Gstore Genv tb2 (TList (TRecord f2)) ->
        free_immut_in x pf = false ->
        free_immut_in y pf = false ->
        x <> y ->
        let pnew := EBinop OAnd p (ELet (EVar y) yf pf) in
        interp_expr store env (EJoin tb1 (EFilter tb2 yf pf) x y p r)
        = interp_expr store env (EJoin tb1 tb2 x y pnew r). *)
    [:=
       "G":   #"env",
       "f1":  #"list_ty",
       "f2":  #"list_ty",
       "t":   #"ty",
       "p":   #"val" (#"ext" (#"ext" "G" (#"Trecord" "f1")) (#"Trecord" "f2")) #"bool",
       "r":   #"val" (#"ext" (#"ext" "G" (#"Trecord" "f1")) (#"Trecord" "f2")) "t", (* arbitrary type *)
       "pf":  #"val" (#"ext" "G" (#"Trecord" "f2")) #"bool",
       "tb1": #"val" "G" (#"list" (#"Trecord" "f1")),
       "tb2": #"val" "G" (#"list" (#"Trecord" "f2"))
      ----------------------------------------------- ("filter_into_join_right")
      #"join" "tb1" (#"filter" "tb2" "pf") "p" "r" = #"join" "tb1" "tb2"
                                                       (#"andb" "p"
                                                          (#"val_subst"
                                                             (#"snoc" (#"cmp" #"wkn" #"wkn") #"hd")
                                                             "pf"))
                                                       "r" : #"val" "G" (#"list" "t")
    ];

      (*
    Theorem proj_into_join: forall (store env: locals) (Gstore Genv: tenv) (t1 t2 p r rp: expr) (x y xp: string),
       x <> y ->
       xp <> x ->
       xp <> y ->
       free_immut_in x rp = false ->
       free_immut_in y rp = false ->
       let rnew := ELet r xp rp in
       interp_expr store env (EProj (EJoin t1 t2 x y p r) xp rp) =
       interp_expr store env (EJoin t1 t2 x y p rnew). *)
    [:=
       "G":   #"env",
       "ty1": #"ty",
       "ty2": #"ty",
       "ty3": #"ty",
       "ty4": #"ty",
       "t1":  #"val" "G" (#"list" "ty1"),
       "t2":  #"val" "G" (#"list" "ty2"),
       "p":   #"val" (#"ext" (#"ext" "G" "ty1") "ty2") #"bool",
       "r":   #"val" (#"ext" (#"ext" "G" "ty1") "ty2") "ty3",
       "rp":  #"val" (#"ext" "G" "ty3") "ty4"
      ----------------------------------------------- ("proj_into_join")
      #"proj" (#"join" "t1" "t2" "p" "r") "rp" = #"join" "t1" "t2" "p"
                                                   (#"val_subst"
                                                      (#"snoc" (#"cmp" #"wkn" #"wkn") "r")
                                                      "rp") :
                                                   #"val" "G" (#"list" "ty4")
    ]

      (*
  [:|
      "G": #"env",
      "f1": #"list_ty",
      "tbl": #"val" "G" (#"list" (#"Trecord" "f1")),
      "p": #"val" (#"ext" "G" (#"Trecord" "f1")) #"bool",
      "r": #"val" (#"ext" "G" (#"Trecord" "f1")) #"bool"
      ----------------------------------------------- 
      #"proj" (#"filter" "tbl" "p") "r" =
      #"proj" (#"filter" (#"proj" "tbl" : #"val" "G" (#"list" (#"Trecord" "l"))
  ]
*)

    (*     Theorem proj_pushdown_filter: forall (store env: locals) (Gstore Genv: tenv) (tbl p r:expr) (x xi xp:string)
      (pcols rcols: list string) (f1: list (string * type)) (t: type),
      tenv_wf Gstore -> tenv_wf Genv ->
      locals_wf Gstore store -> locals_wf Genv env ->
      type_of Gstore (map.put Genv x (TRecord f1)) p TBool ->
      type_of Gstore (map.put Genv xp (TRecord f1)) r t ->
      type_of Gstore Genv tbl (TList (TRecord f1)) ->
      cols x p = Some pcols ->
      cols xp r = Some rcols ->
      let columns := dedup String.eqb (pcols ++ rcols) in
      let ri := make_record xi columns in
      interp_expr store env (EProj (EFilter tbl x p) xp r) =
      interp_expr store env (EProj (EFilter (EProj tbl xi ri) x p) xp r). *)

  (*
  [:|
      "store": #"env",
      "env": #"env",
      "Genv": #"env",
      "G": #"env",
      "A": #"ty",
      "f1" : #"val" "G" (#"list" (#"pair" #"string" "A")),
      "tb" : #"exp" "G" #"map",
      "p" : #"val" (#"ext" "Genv" (#"record" "f1")) #"bool", (* type_of p, TODO get x *)
      "p2" : #"val" (#"ext" "Genv" (#"record" "f1")) #"bool" (* type_of p2, TODO get y *)
      (* free_immut_in *)
      (* interp_expr *)
      ----------------------------------------------- 
      #"test": #"env"
     ]*)
    (* does it make sense to say? instances of tenv and locals can both be
       instances of #"env", tenv has only types, while locals has the assignments *)
    (* resolved: tenv exists, mutable variables (e.g. locals) do not *)

    (* store vs env? ELoc vs EVar? how to unify local and env variables? *)
    (* resolved: don't care bout store for now *)

    (* how to create "forall" propositions? e.g. tenv_wf. *)

    (* tenv            [already done? in RelTransfEx.v] *)
    (* expr            [already done? in Language.v] *)
    (* list A          [already done? in Language.v] *)
    (* string          [built-in] *)
    (* TRecord         [in Language.v] *)
    (* locals          [in RelTransfEx.v] *)
    (* (string * type) [need to define pairs of types, i think we already have it though] *)
    (* type_wf         [in TypeSystem.v BUT NOT NECESSARY FOR NOW] *)
    (* tenv_wf         [in TypeSound.v] *)
    (* type_of         [in TypeSystem.v]  *)
    (* locals_wf       [in TypeSound.v] *)
    (* EFilter         [in Language.v] *)
    (* interp_expr     [in Interpret.v] *)
    (* free_immut_in   [in Utils.v] *)

    (* some notes:
       our environments, tenv, are maps from strings to types.

       tenv_wf checks that an environment is well-formed, i.e. that all defined variables are well-formed.
       it basically runs type_wf on all definitions in the env.

       (map.put Genv x (TRecord f1)) creates a new map, and says that x is a row of f1s
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

Compute fiat_def.

(* filter to term_eq rules
   bundle into a rule_set
   call egraph_simpl *)


Derive fiat
  SuchThat (elab_lang_ext (exp_subst++value_subst) fiat_def fiat)
       As fiat_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve fiat_wf : elab_pfs.

From Pyrosome Require Import Tools.UnElab.

Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 1 1 20 []
  {{e#"andb" #"emp" (#"true" #"emp") (#"true" #"emp")}}.
Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 1 1 20 []
  {{e#"andb" #"emp" (#"true" #"emp") (#"false" #"emp")}}.
Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 1 1 20 []
  {{e#"andb" #"emp" (#"false" #"emp") (#"false" #"emp")}}.
Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 1 1 20 []
  {{e#"andb" #"emp" (#"false" #"emp") (#"true" #"emp")}}.

Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 1 1 20 []
  {{e#"notb" #"emp" (#"false" #"emp")}}.
Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 1 1 20 []
  {{e#"notb" #"emp" (#"true" #"emp")}}.

Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 10 10 200 []
  {{e#"andb" #"emp" (#"notb" #"emp" (#"true" #"emp")) (#"notb" #"emp" (#"true" #"emp"))}}.
Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 10 10 200 []
  {{e#"andb" #"emp" (#"notb" #"emp" (#"true" #"emp")) (#"notb" #"emp" (#"false" #"emp"))}}.
Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 10 10 200 []
  {{e#"andb" #"emp" (#"notb" #"emp" (#"false" #"emp")) (#"notb" #"emp" (#"true" #"emp"))}}.
Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 10 10 200 []
  {{e#"andb" #"emp" (#"notb" #"emp" (#"false" #"emp")) (#"notb" #"emp" (#"false" #"emp"))}}.

Compute fiat.
Compute value_subst.

Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 1 1 20 [("x", {{s#"val" #"emp" #"bool"}})]
  {{e#"andb" #"emp" "x" (#"false" #"emp")}}.

(* next step: slightly larger program *)

(*
  [:=
      "G": #"env",
      "f1": #"list_ty",
      "tb": #"val" "G" (#"list" (#"Trecord" "f1")),
      "p": #"val" (#"ext" "G" (#"Trecord" "f1")) #"bool",
      "p2": #"val" (#"ext" "G" (#"Trecord" "f1")) #"bool"
      ----------------------------------------------- ("filter_filter_list_ty")
      #"filter" (#"filter" "tb" "p") "p2" 
      = #"filter" "tb" (#"andb" "p" "p2")
      : #"val" "G" (#"list" (#"Trecord" "f1")) (* same columns, right? *)
   ];
 *)

(* Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 100 100 2000 []
  {{e#"filter" #"emp" #"empty_list_ty" (#"filter" #"emp" #"empty_list_ty" (#"lempty" #"emp" (#"Trecord" #"empty_list_ty")) (#"true" #"emp")) (#"false" #"emp") }}. *)

Compute fiat.

Definition tr := {{e#"join"
                     (#"cons" #"empty_record" (#"lempty" (#"Trecord" #"empty_list_ty")))
                     (#"filter" 
                        (#"cons" (#"cons_record" #"true" #"empty_record")
                           (#"lempty" (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))))
                        #"false")
                     #"true"
                     #"0"
                }}.

Definition tr2 := {{e#"true"}}.

Axiom (todo : forall a, a).

Derive tr_derived
  SuchThat (elab_term (fiat++value_subst) [] tr tr_derived {{s#"val" #"emp" (#"list" #"nat")}})
  As tr_wf.
Proof.
  unfold tr, tr_derived.
  unshelve (repeat t); apply todo.
Qed.

Print tr_derived.

Compute hide_term_implicits (fiat++value_subst) (PositiveInstantiation.egraph_simpl' (fiat++value_subst) 10 10 10 [] tr_derived).

Compute hide_term_implicits (fiat++value_subst) (PositiveInstantiation.egraph_simpl' (fiat++value_subst) 10 10 10 [("arbitrary_type", {{s#"bool"}})]
                     {{e#"join" #"emp"
                         (#"Trecord" (#"empty_list_ty"))
                         (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))
                         #"nat"
                         (#"cons" #"emp"
                            (#"Trecord" (#"empty_list_ty"))
                            (#"empty_record" #"emp")
                            (#"lempty" #"emp" (#"Trecord" (#"empty_list_ty"))))
                         (#"filter" #"emp"
                            (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))
                            (#"cons" #"emp"
                               (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))
                               (#"cons_record" #"emp"
                                  #"bool"
                                  #"empty_list_ty"
                                  (#"true" #"emp")
                                  (#"empty_record" #"emp"))
                               (#"lempty" #"emp" (#"Trecord"
                                             (#"cons_list_ty" #"bool" #"empty_list_ty"))))
                            (#"false" (#"ext" #"emp" (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty")))))
                         (#"true" (#"ext" (#"ext" #"emp" (#"Trecord" (#"empty_list_ty"))) (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))))
                         (#"0" (#"ext" (#"ext" #"emp" (#"Trecord" (#"empty_list_ty"))) (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))))}}).
                         (* (#"1+" (#"ext" (#"ext" #"emp" (#"Trecord" (#"empty_list_ty"))) (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))) (#"0" (#"ext" (#"ext" #"emp" (#"Trecord" (#"empty_list_ty"))) (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty")))))}}). *)

Definition exclude := {{e#"val_subst"
                               (#"ext" #"emp" (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty")))
                               #"emp"
                               (#"wkn" #"emp" (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty")))
                               #"bool"
                               (#"exclude" #"emp"
                                  (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))
                                  (#"cons" #"emp"
                                     (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))
                                     (#"cons_record" #"emp"
                                        #"bool"
                                        #"empty_list_ty"
                                        (#"true" #"emp")
                                        (#"empty_record" #"emp"))
                                     (#"lempty" #"emp" (#"Trecord"
                                                          (#"cons_list_ty" #"bool" #"empty_list_ty")))))}}.

Compute fiat.

Compute hide_term_implicits (fiat++value_subst) (PositiveInstantiation.egraph_simpl' (fiat++value_subst) 3 3 4 [("tb", {{s#"cons" #"true" (#"lempty" #"bool")}})]

Compute PositiveInstantiation.egraph_simpl' (fiat++value_subst) 1 1 1 [("tb", {{s#"cons" #"true" (#"lempty" #"bool")}})]
  {{e#"proj" #"emp" #"bool" #"bool" (#"proj" #"emp" #"bool" #"bool" (#"lempty" #"emp" #"bool") (#"notb" (#"ext" #"emp" #"bool") (#"true" (#"ext" #"emp" #"bool")))) (#"notb" (#"ext" #"emp" #"bool")  (#"false" (#"ext" #"emp" #"bool")))}}.

Compute hide_term_implicits (fiat++value_subst) (PositiveInstantiation.egraph_simpl' (fiat++value_subst) 3 3 4 [("tb", {{s#"cons" #"true" (#"lempty" #"bool")}})]
  {{e#"proj" #"emp" #"bool" #"bool" (#"proj" #"emp" #"bool" #"bool" (#"lempty" #"emp" #"bool") (#"notb" (#"ext" #"emp" #"bool") (#"true" (#"ext" #"emp" #"bool")))) (#"notb" (#"ext" #"emp" #"bool")  (#"true" (#"ext" #"emp" #"bool")))}}).

Compute hide_term_implicits (fiat++value_subst) {{e#"proj" #"emp" #"bool" #"bool" (#"proj" #"emp" #"bool" #"bool" (#"lempty" #"emp" #"bool") (#"notb" (#"ext" #"emp" #"bool") (#"true" (#"ext" #"emp" #"bool")))) (#"notb" (#"ext" #"emp" #"bool")  (#"true" (#"ext" #"emp" #"bool")))}}.

hide_implicits.

(* CURSED BEYOND THIS POINT
Compute fiat.

Compute hide_term_implicits (fiat++value_subst) (PositiveInstantiation.egraph_simpl' (fiat++value_subst) 100 100 100 [("arbitrary_type", {{s#"bool"}})]
                     {{e#"join" #"emp"
                         (#"Trecord" (#"empty_list_ty"))
                         (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))
                         #"nat"
                         (#"cons" #"emp"
                            (#"Trecord" (#"empty_list_ty"))
                            (#"empty_record" #"emp")
                            (#"lempty" #"emp" (#"Trecord" (#"empty_list_ty"))))
                         (#"filter" #"emp"
                            (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))
                            (#"cons" #"emp"
                               (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))
                               (#"cons_record" #"emp"
                                  #"bool"
                                  #"empty_list_ty"
                                  (#"true" #"emp")
                                  (#"empty_record" #"emp"))
                               (#"lempty" #"emp" (#"Trecord"
                                             (#"cons_list_ty" #"bool" #"empty_list_ty"))))
                            (*
                            (#"false" (#"ext" #"emp" (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))))
*)
                            (#"val_subst"
                               (#"ext" #"emp" (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty")))
                               #"emp"
                               (#"wkn" #"emp" (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty")))
                               #"bool"
                               (#"exclude" #"emp"
                                  (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))
                                  (#"cons" #"emp"
                                     (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))
                                     (#"cons_record" #"emp"
                                        #"bool"
                                        #"empty_list_ty"
                                        (#"true" #"emp")
                                        (#"empty_record" #"emp"))
                                     (#"lempty" #"emp" (#"Trecord"
                                                          (#"cons_list_ty" #"bool" #"empty_list_ty"))))))
                            
                         )
                         (* (#"true" (#"ext" (#"ext" #"emp" (#"Trecord" (#"empty_list_ty"))) (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty")))) *)

                         (#"notb" (#"ext" (#"ext" #"emp" (#"Trecord" (#"empty_list_ty"))) #"Trecord" #"cons_list_ty" #"bool" #"empty_list_ty")
                               (#"val_subst" (#"ext" (#"ext" #"emp" (#"Trecord" (#"empty_list_ty"))) (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))) (
                                            #"ext" #"emp" (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))) (#"snoc" 
                                                                           (#"ext" 
                                                                            (
                                                                            #"ext" #"emp" (#"Trecord" (#"empty_list_ty"))) (
                                                                            #"Trecord" 
                                                                            (#"cons_list_ty" #"bool" #"empty_list_ty"))) #"emp" (
                                                                           #"cmp" 
                                                                           (#"ext" 
                                                                            (
                                                                            #"ext" #"emp" (#"Trecord" (#"empty_list_ty"))) (
                                                                            #"Trecord" 
                                                                            (#"cons_list_ty" #"bool" #"empty_list_ty"))) (
                                                                           #"ext" 
                                                                           #"emp" (#"Trecord" (#"empty_list_ty"))) #"emp" (
                                                                           #"wkn" 
                                                                           (#"ext" #"emp" (#"Trecord" (#"empty_list_ty"))) (
                                                                           #"Trecord" 
                                                                           (#"cons_list_ty" #"bool" #"empty_list_ty"))) (
                                                                           #"wkn" 
                                                                           #"emp" (#"Trecord" (#"empty_list_ty")))) (
                                                                           #"Trecord" 
                                                                           (#"cons_list_ty" #"bool" #"empty_list_ty")) (
                                                                           #"hd" 
                                                                           (#"ext" #"emp" (#"Trecord" (#"empty_list_ty"))) (
                                                                           #"Trecord" 
                                                                            (#"cons_list_ty" #"bool" #"empty_list_ty")))) #"bool"

                               (#"exclude" #"emp"
                                  (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))
                                  (#"cons" #"emp"
                                     (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))
                                     (#"cons_record" #"emp"
                                        #"bool"
                                        #"empty_list_ty"
                                        (#"true" #"emp")
                                        (#"empty_record" #"emp"))
                                     (#"lempty" #"emp" (#"Trecord"
                                                          (#"cons_list_ty" #"bool" #"empty_list_ty")))))))
                            
                         (#"0" (#"ext" (#"ext" #"emp" (#"Trecord" (#"empty_list_ty"))) (#"Trecord" (#"cons_list_ty" #"bool" #"empty_list_ty"))))}}).
*)

