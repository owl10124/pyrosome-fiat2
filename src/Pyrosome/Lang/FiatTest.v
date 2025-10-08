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
  (* todo *)
  (* binop definitions *)
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

    (* wait nvm, i can use ext and ty_ext here? *)
  [:|
      ----------------------------------------------- 
      #"rec_type" : #"ty"
  ];

  [:|
      "G": #"env"
      ----------------------------------------------- 
      #"rempty" : #"val" "G" #"rec_type"
  ];
    
  [:|
     "G": #"env",
     "R": #"val" "G" #"rec_type",
     "A": #"ty"
      ----------------------------------------------- 
      #"cons_record" "R" "A" : #"val" "G" #"rec_type"
  ];

    
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

  (* strings and record types, placeholder *)
    
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
    
  (* switch to tuples?  *)
  [:|
     "G" : #"env",
     "A" : #"ty",
     "l" : #"val" "G" (#"list" (#"pair" #"string" "A"))
      ----------------------------------------------- 
      #"record" "l" : #"ty"
  ];

    (*
  [:|
      "store": #"env",
      "env": #"env",
      "expr": #"exp"
      ----------------------------------------------- 
      #"interp_expr" "store" "env" "expr" : #"exp"
  ];
    *)
  [:|
      "store": #"env",
      "env": #"env",       (* this is well-formed by definition. *)
   (* "Gstore": #"env",  <-- not able to write rules for mutables *)
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
  ]
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

Derive fiat
  SuchThat (elab_lang_ext (exp_subst++value_subst) fiat_def fiat)
       As fiat_wf.
Proof. auto_elab. Qed.
#[export] Hint Resolve fiat_wf : elab_pfs.
