Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Logic.

Import ListNotations.

Require Import Omega. (* for omega tactic *)

Open Scope Z_scope. (* we must use integer Z, rather than natural number, this declaration is madetory *)

(* Syntax of Clock-based Dynamic Logic *)

(* Syntax of SEP_exp (Synchonous Event Program) *)


(* ========================= Syntax of CPM_exp ========================*)

(* =============== Syntax of Expressions ===================*)

(* variable name*)
Inductive Var := var : Z -> Var.

Definition x : Var := (var 1).
Definition y : Var := (var 2).
Definition z : Var := (var 3).
Definition k : Var := (var 4).


(* clock name *)
Inductive CName := clk : Z -> CName.

Definition c : CName := (clk 11).
Definition d : CName := (clk 12).
Definition c1 : CName  := (clk 13).
Definition c2 : CName  := (clk 14).
Definition c3 : CName  := (clk 15).
Definition c4 : CName  := (clk 16).

(* function h*)
Inductive h_f := hC : CName -> h_f.

(* function eta (we use y to express `eta')*)
Inductive y_f := yC : CName -> y_f.

(* guard g*)
Inductive g_exp := 
  gltC : h_f -> h_f -> Z -> g_exp |
  gleC : h_f -> h_f -> Z -> g_exp |
  ggtC : h_f -> h_f -> Z -> g_exp |
  ggeC : h_f -> h_f -> Z -> g_exp |
  geqC : h_f -> h_f -> Z -> g_exp
.

Print g_exp.

(* 33 - 41 *)
Notation "D( c1 , c2 ) < k" := (gltC (hC c1) (hC c2) k) (at level 35).
Notation "D( c1 , c2 ) <= k" := (gleC (hC c1) (hC c2) k) (at level 35).
Notation "D( c1 , c2 ) > k" := (ggtC (hC c1) (hC c2) k) (at level 35).
Notation "D( c1 , c2 ) >= k" := (ggeC (hC c1) (hC c2) k) (at level 35).
Notation "D( c1 , c2 ) == k" := (geqC (hC c1) (hC c2) k) (at level 35).

Check D(c, d) < 5.
Check D(c,d) >= -5.
Check D(c, d) == 5.

(* clock event *)
Definition ClkEvt := list CName.

Check ClkEvt.
Check c :: d :: nil.

(* Syntax of CPM *)
Inductive CPM_exp : Type := 
  evtC : ClkEvt -> CPM_exp | (* clock event *)
  gevtC : g_exp -> ClkEvt -> CPM_exp | (* guarded clock event *)
  eps : CPM_exp | (* empty program *)
  halt : CPM_exp | (* halting program *)
  seqC : CPM_exp -> CPM_exp -> CPM_exp | (* sequence *)
  choC : CPM_exp -> CPM_exp -> CPM_exp | (* choice *)
  starC : CPM_exp -> CPM_exp |(* finite loop *)
  omegaC : CPM_exp -> CPM_exp (* infinite loop *)
.

Coercion evtC : ClkEvt >-> CPM_exp. (* it does not work here *)
Notation "{ a1 | .. | an }" := (cons a1 .. (cons an nil) .. ) (at level 45). 
Check { c | d }.
Notation "@ a" := (evtC a) (at level 46).
Definition idle : ClkEvt := nil.
Check idle.
Notation "g ? a" := (gevtC g a) (at level 48).
Notation "P1 ; P2" := (seqC P1 P2) (at level 49, right associativity).
Notation "P1 'U' P2" := (choC P1 P2) (at level 51, right associativity).
Notation "P ^*" := (starC P) (at level 47, left associativity).
Notation "P ^w" := (starC P) (at level 47, left associativity).

Locate "^*".
Locate "^w".
Check c :: d :: nil.
Check evtC (c :: c1 :: nil).
Check { c | d }.
Check idle.
Check @ { c } ; ((D(c, d)<2) ? { d })^w.
Check @ { c } U ((D(c, d)<2) ? { d })^w.
Check @ {c} ; ((D(c, d)<2) ? { d })^w. 
(*Check @ { c } ; ((h(hC c, hC d)<2) ? { d })^w.*)

(* ========================================= Syntax of cDL Formula ===============================================*)

(* expression e *)
Inductive e_exp :=
  varC : Var -> e_exp | (* variable *)
  hfuncC : h_f -> e_exp | (* h function *)
  yfuncC : y_f -> e_exp | (* eta function *)
  numC : Z -> e_exp | (* constant *)
  plusC : e_exp -> e_exp -> e_exp | (* plus *)
  mulC : e_exp -> e_exp -> e_exp | (* multiply *)
  (* unecessary expression *)
  minusC : e_exp -> e_exp -> e_exp | (* minus *)
  divC : e_exp -> e_exp -> e_exp (* division *)
.
Print e_exp. 

Coercion varC : Var >-> e_exp.
Notation "h( c )" := (hfuncC (hC c)) (at level 52).
Notation "y( c )" := (yfuncC (yC c)) (at level 52).
Coercion numC : Z >-> e_exp.
Notation "e1 +' e2" := (plusC e1 e2) (at level 55, right associativity).
Notation "e1 *' e2" := (mulC e1 e2) (at level 53, right associativity).
Notation "e1 -' e2" := (minusC e1 e2) (at level 55, right associativity).
Notation "e1 /' e2" := (divC e1 e2) (at level 53, right associativity).

Check 5 +' 3.
Check 5 *' (3 +' 5).
Check h( c1 ) *' 4.
Compute y(c) *' 4.

(* dynamic formula *)
(* DEL
Inductive dyF_exp (A : Type) := 
  diaC : CPM_exp -> A -> A -> dyF_exp A |
  dnegC : dyF_exp A -> dyF_exp A |
  (*DEL diadC : CPM_exp -> dyF_exp A -> dyF_exp A | *)
  (* unnecessary expressions *)
  boxC : CPM_exp -> A -> A -> dyF_exp A
.
*)
(* DEL
Arguments diaC {A} _ _ _.
Arguments boxC {A} _ _ _.

Notation "<< p >> ( phi , psi )" := (diaC p phi psi) (at level 63). 
Notation "[[ p ]] ( phi , psi )" := (boxC p phi psi) (at level 63). 
Notation "'~ phi" := (dnegC phi) (at level 64).
*)

(* syntax of cDL formula *)
(* in this version, we define a language which is a bit more expressive than the one we give in ths paper, in
order to make the syntax of the langauge easier to define. *)
Inductive cDL_exp := 
  cdlTrueC : cDL_exp |
  cdlLEC : e_exp -> e_exp -> cDL_exp |
  cdlNegC : cDL_exp -> cDL_exp |
  cdlAndC : cDL_exp -> cDL_exp -> cDL_exp |
  cdlForallC : Var -> cDL_exp -> cDL_exp |
  cdlDiaC : CPM_exp -> cDL_exp -> cDL_exp -> cDL_exp |
  (* unnecessary expressions *)
  cdlFalseC : cDL_exp |
  cdlLTC : e_exp -> e_exp -> cDL_exp |
  cdlGTC : e_exp -> e_exp -> cDL_exp |
  cdlGEC : e_exp -> e_exp -> cDL_exp |
  cdlEQC : e_exp -> e_exp -> cDL_exp |
  cdlOrC : cDL_exp -> cDL_exp -> cDL_exp |
  cdlImpC : cDL_exp -> cDL_exp -> cDL_exp |
  cdlExistsC : Var -> cDL_exp -> cDL_exp |
  cdlBoxC : CPM_exp -> cDL_exp -> cDL_exp -> cDL_exp
.


(*DEL Coercion cdlDYFC : dyF_exp >-> cDL_exp. (* it does not work here *)*)

(*test 
Inductive A (X: Type) :=
  n1 : nat -> X -> (A X)
.

Arguments n1 {X} _ _. 

Inductive B :=
  m1 : (A nat) -> B |
  m2 : B -> B -> B
.

Coercion m1 : A >-> B.


Check m2 (m1 (n1 1 2)) (m1 (n1 2 2)).
Check m2 (n1 1 2) (n1 2 2).
*)


Notation "'tt''" := cdlTrueC (at level 9). (* previous setting is 65, but I don't why it does not work sometimes *)
Notation "e1 <=' e2" := (cdlLEC e1 e2) (at level 61).
(*DEL Notation "# d " := (cdlDYFC d) (at level 62).*)
Notation "~' e" := (cdlNegC e) (at level 67).
Notation "e1 /\' e2" := (cdlAndC e1 e2) (at level 69, right associativity).
Notation "'all' x , e" := (cdlForallC x e) (at level 68, x at level 67).
Notation "<< p >> ( phi , psi )" := (cdlDiaC p phi psi) (at level 63). 
(* unnecessary expressions *)
Notation "'ff''" := cdlFalseC (at level 9).
Notation "e1 <' e2" := (cdlLTC e1 e2) (at level 61).
Notation "e1 >' e2" := (cdlGTC e1 e2) (at level 61).
Notation "e1 >=' e2" := (cdlGEC e1 e2) (at level 61).
Notation "e1 =' e2" := (cdlEQC e1 e2) (at level 61).
(*DEL
Notation "<< p >>' r" := (cdl_dia1C p r) (at level 63, p at level 51, r at level 51). 
(* must be higher than the precedence of <<, which is 52 *)
Notation "<< p >> e" := (cdl_dia2C p e) (at level 63, p at level 51, e at level 51).
*)
Notation "e1 \/' e2" := (cdlOrC e1 e2) (at level 71, right associativity).
Notation "e1 ->' e2" := (cdlImpC e1 e2) (at level 72, right associativity).
Notation "'ext' x , e" := (cdlExistsC x e) (at level 68, x at level 67).
Notation "[[ p ]] ( phi , psi )" := (cdlBoxC p phi psi) (at level 63). 

Check tt'.
Check ff'.
Check (5 -' 3) <' 2.
Check (cdlDiaC eps tt' (5 =' 5)). 
Check << eps >> (tt' , 5 =' 5).
(*DEL Check (cdlDYFC (<< eps >> (tt' , 5 =' 5))) /\' x >' 5.*)
Check (<< eps >> (tt' , 5 =' 5)) /\' x >' 5.
Check (<< eps >> (tt' , 5 =' 5)) \/' x >' 5.
Check all x , 4 =' 5.
Check ext x , 4 =' 5.

Check h( c ) =' 2.

(*************************** Some   Auxiliary Functions ***************************)

(* compare the id of two variables *)
Definition eqv (x : Var) (y: Var) : bool :=
  match x, y with
  | var n, var m => if n =? m then true else false
  end.

Definition eqc (c1 : CName) (c2: CName) : bool :=
  match c1, c2 with
  | clk n, clk m => if n =? m then true else false
  end.

Compute 4=?4.

(* romove all elements x from a Var list *)
Fixpoint rmv (V : list Var) (x : Var) : list Var :=
  match V with
  | nil => nil
  | e :: V' => if eqv e x then rmv V' x else e :: (rmv V' x)
  end
.

Fixpoint rmvc (V : list CName) (x : CName) : list CName :=
  match V with
  | nil => nil
  | e :: V' => if eqc e x then rmvc V' x else e :: (rmvc V' x)
  end
.

(* generate a new variable id *)
Fixpoint MaxId (VSet : list Var) : Z :=
  match VSet with
  | nil => 0 (* when there is no variables in the current environment VSet, just start from the number 0 *)
  | v :: VSet' => let n := MaxId VSet' in (
                      match v with | var m => 
                        if n <=? m then m else (MaxId VSet') (* le_lt_dec : <= *)
                      end
                      )
  end
.

Compute 4 <=? 5.
Compute 5 <=? 5.
Compute 6 <=? 5.
Compute -6 <=? -5.
(* -------------------------------------- generate new variable in the context ----------------------- *)
Compute MaxId (var 1 :: var 3 :: var 5 :: var 6 :: nil).

Definition NewId (VSet : list Var) : Z := (MaxId VSet)+1. 

Compute NewId (var 7 :: var 1 :: var 3 :: var 3 :: var 5 :: var 6 :: nil).
Compute NewId nil.

(* --------------------------substitution--------------------------- *)

(*variable type*)
Inductive VarType := 
  tVarC : Var -> VarType |
  thC : CName -> VarType |
  tyC : CName -> VarType
.

Notation "& x" := (tVarC x) (at level 52).
Notation "&h( c )" := (thC c) (at level 52).
Notation "&y( c )" := (tyC c) (at level 52).

Locate "&".

(*substitution*)

(*sustitution for e_exp*)
Fixpoint e_exp_subsE (e : e_exp) (E : e_exp) (u : VarType) : e_exp := 
  match e with
  | varC v => match u with 
                | tVarC x => if (eqv v x) then E else varC v
                | thC c => varC v
                | tyC c => varC v
               end
  | hfuncC hf => match hf with 
                  | hC c => 
                    match u with 
                    | tVarC x => hfuncC hf
                    | thC c' => if (eqc c' c) then E else hfuncC hf
                    | tyC c' => hfuncC hf
                    end
                 end
  | yfuncC yf => match yf with
                  | yC c =>
                    match u with 
                      | tVarC x => yfuncC yf
                      | thC c' => yfuncC yf
                      | tyC c' => if (eqc c' c) then E else yfuncC yf
                    end
                 end
  | numC n => numC n
  | plusC e1 e2 => plusC (e_exp_subsE e1 E u) (e_exp_subsE e2 E u)
  | mulC e1 e2 => mulC (e_exp_subsE e1 E u) (e_exp_subsE e2 E u)
  | minusC e1 e2 => minusC (e_exp_subsE e1 E u) (e_exp_subsE e2 E u)
  | divC e1 e2 => divC (e_exp_subsE e1 E u) (e_exp_subsE e2 E u)
  end
.

Compute e_exp_subsE (x +' y) (y +' 1) (&x).
Compute e_exp_subsE (x *' z) (y *' 5) (&h(c)).
Compute e_exp_subsE (h(c) *' z) (y *' 5) (&h(c)).

Notation "e [ E 'subs-E' u ]" := (e_exp_subsE e E u) (at level 9).

Compute (x +' y) [(y +' 1) subs-E &x]. 

(*sustitution for dyF_exp*)
Definition subs_type := cDL_exp -> e_exp -> VarType -> cDL_exp.

(* currently we don't need it
Fixpoint dyF_subsE (e : dyF_exp cDL_exp) (E : e_exp) (u : VarType) (cdl_subsE : subs_type) : dyF_exp cDL_exp:=
  match e with
  | diaC p phi psi => diaC p (cdl_subsE phi E u) (cdl_subsE psi E u) 
  | dnegC e' => dnegC (dyF_subsE e' E u)
  | diadC p e' => diadC (CPM_exp_subsE p E u) (dyF_subssE e' E u)
  end 
.
*)

(*sustitution for cDL_exp*)
Fixpoint cdl_subsE (e : cDL_exp) (E : e_exp) (u : VarType) : cDL_exp := (* e[E // x] *)
    match e with
    | cdlTrueC => cdlTrueC
    | cdlLEC e1 e2 => cdlLEC (e_exp_subsE e1 E u) (e_exp_subsE e2 E u)
    | cdlNegC e' => cdlNegC (cdl_subsE e' E u)
    | cdlAndC e1 e2 => cdlAndC (cdl_subsE e1 E u) (cdl_subsE e2 E u)
    | cdlForallC x1 e' => match u with 
                             | tVarC x => if (eqv x1 x) then 
                                            cdlForallC x1 e' else 
                                              cdlForallC x1 (cdl_subsE e' E u)
                             | thC c => cdlForallC x1 (cdl_subsE e' E u)
                             | tyC c => cdlForallC x1 (cdl_subsE e' E u)
                           end
    | cdlDiaC p phi psi => cdlDiaC p (cdl_subsE phi E u) (cdl_subsE psi E u) 
(*we temporally do not need to consider the substitution of $p$ since 
we assume that our sequent is single-targeted and there is no case that we substitute a clock variable 
in a dyanmic formula. *)
    | cdlFalseC => cdlFalseC
    | cdlLTC e1 e2 => cdlLTC (e_exp_subsE e1 E u) (e_exp_subsE e2 E u)
    | cdlGTC e1 e2 => cdlGTC (e_exp_subsE e1 E u) (e_exp_subsE e2 E u)
    | cdlGEC e1 e2 => cdlGEC (e_exp_subsE e1 E u) (e_exp_subsE e2 E u)
    | cdlEQC e1 e2 => cdlEQC (e_exp_subsE e1 E u) (e_exp_subsE e2 E u)
    | cdlOrC e1 e2 => cdlOrC (cdl_subsE e1 E u) (cdl_subsE e2 E u)
    | cdlImpC e1 e2 => cdlImpC (cdl_subsE e1 E u) (cdl_subsE e2 E u)
    | cdlExistsC x1 e' => match u with 
                             | tVarC x => if (eqv x1 x) then 
                                            cdlExistsC x1 e' else 
                                              cdlExistsC x1 (cdl_subsE e' E u)
                             | thC c => cdlExistsC x1 (cdl_subsE e' E u)
                             | tyC c => cdlExistsC x1 (cdl_subsE e' E u)
                           end
    | cdlBoxC p phi psi => cdlBoxC p (cdl_subsE phi E u) (cdl_subsE psi E u) 
  end.

Notation "e [ E 'subs' u ]" := (cdl_subsE e E u) (at level 9).
(* Check << skip ]]' c1 << c2 .*)
Locate "/".
Locate "//".

Compute (x +' y) =' 1 /\' (h(c) *' z <=' 5) [(x +' 1) subs &h(c)].

(* substitution for a list *)
Fixpoint cdl_subsE_l (T : list cDL_exp) (E : e_exp) (u : VarType) : list cDL_exp := (* T [x' // x] *)
  match T with
  | nil => nil
  | e :: T' => (cdl_subsE e E u) :: (cdl_subsE_l T' E u)
  end.

Notation "T [ E 'subs-l' u ]" := (cdl_subsE_l T E u) (at level 9).

(* ------------------------------------------------------------------ *)

(* add an element at the nail of a exp list *)
Fixpoint addNail (l : list cDL_exp) (e : cDL_exp) : list cDL_exp :=
  match l with 
    | nil => e :: nil
    | a :: l' => a :: (addNail l' e)
  end.

(* Guard to cdl expression *)
Definition G_2_cdl (g : g_exp) : cDL_exp :=
  match g with
  | gltC h1 h2 k => cdlLTC (minusC (hfuncC h1) (hfuncC h2)) k
  | gleC h1 h2 k => cdlLEC (minusC (hfuncC h1) (hfuncC h2)) k
  | ggtC h1 h2 k => cdlGTC (minusC (hfuncC h1) (hfuncC h2)) k
  | ggeC h1 h2 k => cdlGEC (minusC (hfuncC h1) (hfuncC h2)) k
  | geqC h1 h2 k => cdlEQC (minusC (hfuncC h1) (hfuncC h2)) k
  end
.

Compute G_2_cdl (D(c1 , c2) <= 1).
Compute G_2_cdl (D(c1 , c2) > 5).

(* -------------------------------computation of variables in cdl formula----------------------------------------*)
(* this function check whether a variable (i.e. a string) belongs to a list of variables (list of string) *)
Fixpoint NotIn_bool (s : Var) (vec : list Var) : bool :=
  match vec with
  | nil => true
  | v :: vec' => if (eqv s v) then false else NotIn_bool s vec'
  end.

Compute NotIn_bool x (x :: y :: z :: nil).
Compute NotIn_bool z (x :: y :: z :: nil).

Fixpoint e_exp_V (e : e_exp) (V : list Var) : list Var := (*bv : list of computed variables at current time *)
  match e with
  | varC v => if (NotIn_bool v V) then v :: nil else nil
  | hfuncC h => nil
  | yfuncC y => nil
  | numC n => nil
  | plusC e1 e2 => (e_exp_V e1 V) ++ (e_exp_V e2 (V ++ (e_exp_V e1 V)))
  | mulC e1 e2 => (e_exp_V e1 V) ++ (e_exp_V e2 (V ++ (e_exp_V e1 V)))
  | minusC e1 e2 => (e_exp_V e1 V) ++ (e_exp_V e2 (V ++ (e_exp_V e1 V)))
  | divC e1 e2 => (e_exp_V e1 V) ++ (e_exp_V e2 (V ++ (e_exp_V e1 V)))
  end
.

Fixpoint cdl_V (e : cDL_exp) (V : list Var) : list Var := (*V : list of computed variables at current time *)
  match e with
  | cdlTrueC => nil
  | cdlLEC e1 e2 => let l := (e_exp_V e1 V) in (l ++ (e_exp_V e2 (V ++ l)))
  | cdlNegC e' => cdl_V e' V
  | cdlAndC e1 e2 => let l := (cdl_V e1 V) in (l ++ (cdl_V e2 (V ++ l)))
  | cdlForallC x1 e' => if NotIn_bool x1 V then x1 :: (cdl_V e' (x1 :: V)) else cdl_V e' V
  | cdlDiaC p phi psi => let l := (cdl_V phi V) in (l ++ (cdl_V psi (V ++ l)))
  (* in cDL there is no variables in a CPM *)
  | cdlFalseC => nil
  | cdlLTC e1 e2 => let l := (e_exp_V e1 V) in (l ++ (e_exp_V e2 (V ++ l)))
  | cdlGTC e1 e2 => let l := (e_exp_V e1 V) in (l ++ (e_exp_V e2 (V ++ l)))
  | cdlGEC e1 e2 => let l := (e_exp_V e1 V) in (l ++ (e_exp_V e2 (V ++ l)))
  | cdlEQC e1 e2 => let l := (e_exp_V e1 V) in (l ++ (e_exp_V e2 (V ++ l)))
  | cdlOrC e1 e2 => let l := (cdl_V e1 V) in (l ++ (cdl_V e2 (V ++ l)))
  | cdlImpC e1 e2 => let l := (cdl_V e1 V) in (l ++ (cdl_V e2 (V ++ l)))
  | cdlExistsC x1 e' => if NotIn_bool x1 V then x1 :: (cdl_V e' (x1 :: V)) else cdl_V e' V
  | cdlBoxC p phi psi => let l := (cdl_V phi V) in (l ++ (cdl_V psi (V ++ l)))
  (* in cDL there is no variables in a CPM *)
  end
.

(* compute V for a function *)
(* here we do a trick. We pass to phi a variable with a variable id that we will never use in the context 
(i.e., the var 0), and we add this variable to the bounded variable list bv, so that the final V set of 
phi will definitely not contain var 0. 
Note that var 0 must not be used anywhere, or it would be dangerous since it is possible var 0 
has already existed in the formul phi *)


Definition cdl_V_f (phi : e_exp -> cDL_exp) (V : list Var) : list Var :=
  cdl_V (phi (var 0)) ((var 0) :: V).

(*------------------------------------ transform a CDL exp to a FOLF formula ------------------------------*)
(* build a type for distinguishing pure FOL (i.e. Prop) or non-pure FOL *)
Inductive FOLF := 
  pureC : Prop -> FOLF |
  noPureC : FOLF
.

(* Evaluation *)
Definition state (A : Type) := A -> nat.
Arguments state {A}.  

(* transform an e_exp to a FOL exp under a given state st. *)
(* here the functionality of st is to link the concept of `variable' in CDL we define to 
the `nat' domain in Coq *)

Fixpoint Eexp_2_exp (e : e_exp) (st : Var -> Z) (fn : CName -> Z) (gn : CName -> Z) : Z :=
  match e with
  | varC v => (st v)
  | hfuncC h => match h with 
                 | hC c => (fn c)
                end
  | yfuncC y => match y with 
                 | yC c => (gn c)
                end
  | numC n => n
  | plusC e1 e2 => (Eexp_2_exp e1 st fn gn) + (Eexp_2_exp e2 st fn gn)
  | mulC e1 e2 => (Eexp_2_exp e1 st fn gn) * (Eexp_2_exp e2 st fn gn)
  | minusC e1 e2 => (Eexp_2_exp e1 st fn gn) - (Eexp_2_exp e2 st fn gn)
  | divC e1 e2 => (Eexp_2_exp e1 st fn gn) / (Eexp_2_exp e2 st fn gn)
  end
.


(* transform a CDL exp to a FOLF formula *)
Fixpoint CDLexp_2_FOLF (e : cDL_exp) (st : Var -> Z) (fn : CName -> Z) (gn : CName -> Z) : FOLF :=
  match e with
  | cdlTrueC => pureC True
  | cdlLEC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) <= (Eexp_2_exp e2 st fn gn))
  | cdlNegC e' => match (CDLexp_2_FOLF e' st fn gn) with 
                    | noPureC => noPureC
                    | pureC f => pureC (~ f) 
                   end
  | cdlAndC e1 e2 => match (CDLexp_2_FOLF e1 st fn gn), (CDLexp_2_FOLF e2 st fn gn) with 
                        | noPureC , _ => noPureC
                        | _ , noPureC => noPureC
                        | (pureC f1) , (pureC f2) => pureC (f1 /\ f2)
                      end
  | cdlForallC x e' => match (CDLexp_2_FOLF e' st fn gn) with
                          | noPureC => noPureC
                          | pureC f => pureC (forall (x : nat), f)
                        end
  | cdlDiaC p phi psi => noPureC (*once met dynamic operators, it is not a pure FOL formula *)
  | cdlFalseC => pureC False
  | cdlLTC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) < (Eexp_2_exp e2 st fn gn)) 
  | cdlGTC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) > (Eexp_2_exp e2 st fn gn)) 
  | cdlGEC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) >= (Eexp_2_exp e2 st fn gn)) 
  | cdlEQC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) = (Eexp_2_exp e2 st fn gn)) 
  | cdlOrC e1 e2 => match (CDLexp_2_FOLF e1 st fn gn), (CDLexp_2_FOLF e2 st fn gn) with 
                        | noPureC , _ => noPureC
                        | _ , noPureC => noPureC
                        | (pureC f1) , (pureC f2) => pureC (f1 \/ f2)
                     end
  | cdlImpC e1 e2 => match (CDLexp_2_FOLF e1 st fn gn), (CDLexp_2_FOLF e2 st fn gn) with 
                        | noPureC , _ => noPureC
                        | _ , noPureC => noPureC
                        | (pureC f1) , (pureC f2) => pureC (f1 -> f2)
                      end
  | cdlExistsC x e' => match (CDLexp_2_FOLF e' st fn gn) with
                          | noPureC => noPureC
                          | pureC f => pureC (exists (x : nat), f)
                        end
  | cdlBoxC p phi psi => noPureC (*once met dynamic operators, it is not a pure FOL formula *)
  end.

Fixpoint CDLexp_2_FOLF_Arith (e : cDL_exp) (st : Var -> Z) (fn : CName -> Z) (gn : CName -> Z) : FOLF :=
  match e with
  | cdlTrueC => pureC (0 = 0)
  | cdlLEC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) <= (Eexp_2_exp e2 st fn gn))
  | cdlNegC e' => match (CDLexp_2_FOLF_Arith e' st fn gn) with 
                    | noPureC => noPureC
                    | pureC f => pureC (~ f) 
                   end
  | cdlAndC e1 e2 => match (CDLexp_2_FOLF_Arith e1 st fn gn), (CDLexp_2_FOLF_Arith e2 st fn gn) with 
                        | noPureC , _ => noPureC
                        | _ , noPureC => noPureC
                        | (pureC f1) , (pureC f2) => pureC (f1 /\ f2)
                      end
  | cdlForallC x e' => match (CDLexp_2_FOLF_Arith e' st fn gn) with
                          | noPureC => noPureC
                          | pureC f => pureC (forall (x : nat), f)
                        end
  | cdlDiaC p phi psi => noPureC (*once met dynamic operators, it is not a pure FOL formula *)
  | cdlFalseC => pureC (0 > 0)
  | cdlLTC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) < (Eexp_2_exp e2 st fn gn)) 
  | cdlGTC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) > (Eexp_2_exp e2 st fn gn)) 
  | cdlGEC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) >= (Eexp_2_exp e2 st fn gn)) 
  | cdlEQC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) = (Eexp_2_exp e2 st fn gn)) 
  | cdlOrC e1 e2 => match (CDLexp_2_FOLF_Arith e1 st fn gn), (CDLexp_2_FOLF_Arith e2 st fn gn) with 
                        | noPureC , _ => noPureC
                        | _ , noPureC => noPureC
                        | (pureC f1) , (pureC f2) => pureC (f1 \/ f2)
                     end
  | cdlImpC e1 e2 => match (CDLexp_2_FOLF_Arith e1 st fn gn), (CDLexp_2_FOLF_Arith e2 st fn gn) with 
                        | noPureC , _ => noPureC
                        | _ , noPureC => noPureC
                        | (pureC f1) , (pureC f2) => pureC (f1 -> f2)
                      end
  | cdlExistsC x e' => match (CDLexp_2_FOLF_Arith e' st fn gn) with
                          | noPureC => noPureC
                          | pureC f => pureC (exists (x : nat), f)
                        end
  | cdlBoxC p phi psi => noPureC (*once met dynamic operators, it is not a pure FOL formula *)
  end.


Variable st0 : Var -> Z. 
Variable fn0 : CName -> Z.
Variable gn0 : CName -> Z.
Compute (CDLexp_2_FOLF tt' st0 fn0 gn0).
Compute (CDLexp_2_FOLF (tt' /\' x >=' 5) st0 fn0 gn0).
Compute (CDLexp_2_FOLF (tt' /\' (x >=' 5 ->' << eps >> (x >' 5, tt'))) st0 fn0 gn0).
Compute (CDLexp_2_FOLF (tt' /\' (x >=' 5 ->' h(c) >' 5 )) st0 fn0 gn0).
Compute (CDLexp_2_FOLF_Arith (tt' /\' (x >=' 5 ->' h(c) >' 5 )) st0 fn0 gn0).


(* transform a CDL_exp to Prop formula, if CDL_exp is not pure, simply return False, otherwise, 
return the Prop formula corresponding to it. *)

Definition CDLexp_2_Prop (e : cDL_exp) (st : Var -> nat) (fn : CName -> nat) (gn : CName -> nat) : Prop :=
  match (CDLexp_2_FOLF e st fn gn) with
    | noPureC => False
    | pureC f => f
  end.

(* this function only differs from CDLexp_2_Prop in that it replaces every `False' and `True' Prop with an arithmetic
expression which is `False' or `True'. *)
Definition CDLexp_2_Arith (e : cDL_exp) (st : Var -> nat) (fn : CName -> nat) (gn : CName -> nat) : Prop :=
  match (CDLexp_2_FOLF_Arith e st fn gn) with
    | noPureC => (0 > 0)
    | pureC f => f
  end.

Compute CDLexp_2_Prop (tt' /\' (x >=' 5 ->' << eps >> (x >' 5, tt'))) st0 fn0 gn0.
Compute CDLexp_2_Prop (tt' /\' (x >=' 5 ->' y(c) >' 5 )) st0 fn0 gn0.
Compute CDLexp_2_Arith (tt' /\' (x >=' 5 ->' y(c) >' 5 )) st0 fn0 gn0.

(* ----------------------------------- check if a substitution is admissible --------------------------------- *)
(* when checking if a substitution is admissible, we consider clock names c1 c2 c3 instead of clock-related 
variables h(c1) h(c2) h(c3) y(c1) y(c2) y(c3) .... This is simpler to be dealt with in Coq. And this is 
not like when we consider the substitution, there we must consider the clock-related variables *)
(* 
Currently we can assume that there is no clock variables in the substituting expression so we only take care of 
general variables. 
*)

Fixpoint commonEle (v1 : list Var) (v2 : list Var) : bool :=
  match v1 with
  | nil => false
  | e :: v1' => if (NotIn_bool e v2) then commonEle v1' v2 else true
  end.

Compute commonEle (x :: y :: nil) (z :: nil).
Compute commonEle (x :: y :: nil) (z :: y :: nil).

Fixpoint e_exp_chk (e : e_exp) (ev : list Var) (u : VarType) (bv : list Var) : Prop := 
  (* ev --> variables in expression, bv --> bounded variables currently *)
  match e with
  | varC v => match u with 
                | tVarC x => if andb (eqv v x) (commonEle ev bv) then False else True
                | thC c => True
                | tyC c => True
               end
  | hfuncC h => match h with 
                  hC c => match u with 
                            | tVarC x => True
                            | thC c' => if andb (eqc c c') (commonEle ev bv) then False else True
                            | tyC c' => True
                          end
                end

  | yfuncC y => match y with 
                  | yC c =>match u with 
                              | tVarC x => True
                              | thC c' => True
                              | tyC c' => if andb (eqc c c') (commonEle ev bv) then False else True
                            end
                end
  | numC n => True
  | plusC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  | mulC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  | minusC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  | divC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  end
.

Fixpoint cdl_chk (e : cDL_exp) (ev : list Var) (u : VarType) (bv : list Var) : Prop := 
  (* e --> the expression to be substituted, ev --> the set of variables of the substituting expression, 
     u --> the variable type to be substituted, bv --> the set of bounded variables at current time *)
(*currently we only consider variables and not clock variables, 
this is correct since we assume only general variables 
are contained in the substituting expression*)
    match e with
    | cdlTrueC => True
    | cdlLEC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
    | cdlNegC e' => cdl_chk e' ev u bv
    | cdlAndC e1 e2 => (cdl_chk e1 ev u bv) /\ (cdl_chk e2 ev u bv)
    | cdlForallC x1 e' => cdl_chk e' ev u (x1 :: bv)
    | cdlDiaC p phi psi => (cdl_chk phi ev u bv) /\ (cdl_chk psi ev u bv)
(*currently we can safely skip the CPM p cause no substituion happen in ps*)
    | cdlFalseC => True
    | cdlLTC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
    | cdlGTC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
    | cdlGEC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
    | cdlEQC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
    | cdlOrC e1 e2 => (cdl_chk e1 ev u bv) /\ (cdl_chk e2 ev u bv)
    | cdlImpC e1 e2 => (cdl_chk e1 ev u bv) /\ (cdl_chk e2 ev u bv)
    | cdlExistsC x1 e' => cdl_chk e' ev u (x1 :: bv)
    | cdlBoxC p phi psi => (cdl_chk phi ev u bv) /\ (cdl_chk psi ev u bv)
    end.

(* =========================================== construction of the proof system ================================================= *)

Reserved Notation "<| T , p1  ==> p2 , D // V , C , ntC |> " (at level 75).

Locate "==>". (* check that we could use this notation without any problems *)

(* definition of sequent *)
(* currently we do not consider the other direction of the rules and rules for the dual operator of `[[p]]'. *)
(* Gamma, Delta *)
Definition Gamma := list cDL_exp.
Definition Delta := list cDL_exp.

(* target place *)
Inductive place := 
  exp : cDL_exp -> place |
  empty : place
.

(* --------- transform a sequent to a CDL exp, which we will need to implement Rule (o) below ---------*)
Fixpoint Gamma_2_CDLexp (T : Gamma) : cDL_exp :=
  match T with 
  | nil => tt'
  | e :: T' => e /\' (Gamma_2_CDLexp T')
  end.

Fixpoint Delta_2_CDLexp (D : Gamma) : cDL_exp :=
  match D with 
  | nil => ff'
  | e :: D' => e \/' (Delta_2_CDLexp D')
  end.

Definition place_2_CDLexp_L (p : place) : cDL_exp :=
  match p with
  | empty => tt'
  | exp e => e
  end.

Definition place_2_CDLexp_R (p : place) : cDL_exp :=
  match p with
  | empty => ff'
  | exp e => e
  end.

Definition Seq_2_CDLexp (T : Gamma) (p1 : place) (p2 : place) (D : Delta) : cDL_exp :=
  ((Gamma_2_CDLexp T) /\' (place_2_CDLexp_L p1)) 
  ->'
  ((place_2_CDLexp_R p2) \/' (Delta_2_CDLexp D))
.




Inductive Seq : Gamma -> place -> place -> Delta -> (list Var) -> (list CName) -> (list CName) -> Prop :=

  (* ****************************** rules special for the sequent defined in Coq ********************* *)
(* these rules are special in Coq, they are not defined in the original proof system of cDL in the paper. We need them because
  the structure of the sequent in Coq is slightly different from that in the paper. We need special rules to deal with 
  `place' in the sequent *)

(* 
   V: all variables appearing in the current sequent 
   C: all clocks appearing in the current sequent
   ntC: all clocks that does not tick at current instant. 
*)

  r_placeR_rmv : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                        (phi : cDL_exp),
          (
            Seq T pls1 empty (addNail D phi) V C ntC (* put phi at the nail of D *)
          )
          ->
          (
            Seq T pls1 (exp phi) D V C ntC
          )
|
  r_placeR_add : forall (T : Gamma) (pls1 : place) (D' : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                        (phi : cDL_exp),
          (
            Seq T pls1 (exp phi) D' V C ntC (* add a new phi from the head of D = phi :: D' *)
          )
          ->
          (
            Seq T pls1 empty (phi :: D') V C ntC
          )
|
  r_placeL_rmv : forall (T : Gamma) (pls2 : place) (D : Delta)  (V : list Var) (C : list CName) (ntC : list CName)
                        (phi : cDL_exp),
          (
            Seq (addNail T phi) empty pls2 D V C ntC (* put phi at the nail of T *)
          )
          ->
          (
            Seq T (exp phi) pls2 D V C ntC
          )
|
  r_placeL_add : forall (T' : Gamma) (pls2 : place) (D : Delta)  (V : list Var) (C : list CName) (ntC : list CName)
                        (phi : cDL_exp),
          (
            Seq T' (exp phi) pls2 D V C ntC (* add a new phi from the head of T = phi :: T' *)
          )
          ->
          (
            Seq (phi :: T') empty pls2 D V C ntC
          )
|
(* ****************************** rules for combinational events *********************** *)
(* Rule (\alpha) *)
  r_Alpha_c : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                    (c : CName) (a : ClkEvt) (phi : cDL_exp) (psi : cDL_exp), 
          let n := NewId V in 
          let m := S n in
          (
            Seq (
                  (h(c) =' (var n) +' 1) :: (y(c) =' 1) :: 
                  (
                    (T [ (var n) subs-l &h(c) ]) [ (var m) subs-l &y(c) ]
                  )
                )
                      pls1
                        (exp (<< @ a >> (phi, psi))) 
                          (
                            (D [ (var n) subs-l &h(c) ]) [ (var m) subs-l &y(c)]
                          )
                            (var m :: var n :: V) 
                              C 
                                (rmvc ntC c) (*c ticks so it should be removed from ntC *)
          )
          ->
          (
            Seq T pls1 (exp (<< @ (c :: a) >> (phi, psi) )) D V C ntC
          )
|
  r_Alpha_idle1 : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName)
                    (phi : cDL_exp) (psi : cDL_exp), 
          (
            Seq T pls1 (exp (phi /\' psi)) D V C C (* when ntC = nil, reset it to C *) 
          )
          ->
          (
            Seq T pls1 (exp (<< @ idle >> (phi, psi))) D V C nil
          )
|
  r_Alpha_idle2 : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (c : CName) (ntC' : list CName)
                    (phi : cDL_exp) (psi : cDL_exp), (* dealing with all clocks that do not tick *)
          (
            let n := NewId V in 
            (
              Seq (
                    (y(c) =' 0) :: (T [(var n) subs-l &y(c)])
                  )
                    pls1
                      (exp (<< @ idle >> (phi, psi)))
                        (D [(var n) subs-l &y(c)])
                          ((var n) :: V)
                            C 
                              ntC'
            )
          )
          ->
          (
            Seq T pls1 (exp (<< @ idle >> (phi, psi))) D V C (c :: ntC')
          )
|

(* Rule epsilon *)
  r_Eps : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                  (phi : cDL_exp) (psi : cDL_exp), 
          (
            Seq T pls1 ( exp phi ) D V C ntC
          )
          ->
          (
            Seq T pls1 (exp (<< eps >> (phi, psi))) D V C ntC
          )
|

(* Rule g? *)
  r_Guard : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                          (g : g_exp) (a : ClkEvt) (phi : cDL_exp) (psi : cDL_exp), 
          (
            Seq T pls1 (exp ((G_2_cdl g) /\' << a >> (phi, psi))) D V C ntC
          )
          ->
          (
            Seq T pls1 (exp (<< g ? a >> (phi, psi))) D V C ntC
          )
|

(* Rule halt *)
  r_Halt : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                          (phi : cDL_exp) (psi : cDL_exp), 
          (
            Seq T pls1 (exp ff') D V C ntC
          )
          ->
          (
            Seq T pls1 (exp (<< halt >> (phi, psi))) D V C ntC
          )
|

(* Rule << omega >> *)
  r_Omega_dia : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                  (p : CPM_exp) (phi : cDL_exp) (psi : cDL_exp), 
          (
            exists (inv : cDL_exp), (* invariant has to be manually provided *)
              (
                Seq T pls1 
                        (exp inv)
                            D
                              (V ++ (cdl_V inv V))
                                  C 
                                   ntC
              )
              /\
              (
                Seq nil pls1 
                          (exp (
                                  inv ->' << p >> (inv, psi)
                               )
                          )
                            nil
                              (cdl_V (inv ->' << p >> (inv, psi)) nil)
                                  C 
                                    ntC

              )
          )
          ->
          (
            Seq T pls1 
                    (exp (<< p^w >> (phi, psi))) D V C ntC
          )
|

(* --------------------------------- rules inherited from FODL and dTL^2 -------------------------------- *)
(* Rule choice *)
  r_Choice : forall (T: Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                      (p : CPM_exp) (q : CPM_exp) (phi : cDL_exp) (psi : cDL_exp),
          (
            Seq T pls1
                    (exp (<< p >> (phi, psi) \/' << q >> (phi,psi)))
                      D V C ntC
          )
          ->
          (
            Seq T pls1 (exp (<< p U q >> (phi, psi))) D V C ntC
          )
|

(* Rule sequence *)
  r_Seq : forall (T: Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                      (p : CPM_exp) (q : CPM_exp) (phi : cDL_exp) (psi : cDL_exp),
          (
            Seq T pls1
                    (
                      exp (<< p >> (<< q >> (phi, psi), psi))
                    )
                      D V C ntC
          )
          ->
          (
            Seq T pls1 (exp (<< p;q >> (phi, psi))) D V C ntC
          )
|

(* Rule star n *)
  r_Star_n : forall (T: Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                      (p : CPM_exp) (phi : cDL_exp) (psi : cDL_exp),
          (
            Seq T pls1
                    (
                      exp (phi \/' << p ; p^* >> (phi, psi) )
                    )
                      D V C ntC
          )
          ->
          (
            Seq T pls1 (exp (<< p^* >> (phi, psi))) D V C ntC
          )
|
(* Rule << star >> *)
  r_Star_dia : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                  (p : CPM_exp) (phi : cDL_exp) (psi : cDL_exp), 
          (
            exists (inv : e_exp -> cDL_exp), (* invariant has to be manually provided *)
              (
                let X := var (NewId (V ++ (cdl_V_f inv V))) in 
                (
                Seq T pls1 
                        (exp (ext X , (X >=' 0 /\' (inv X))))
                            D 
                              (V ++ (cdl_V (ext X , (X >=' 0 /\' (inv X))) V))
                                  C
                                    ntC
                )
              )
              /\
              (
                let X := var (NewId 
                                (
                                  cdl_V ((inv (var 0)) ->' << p >> (inv ((var 0) -' 1), psi)) nil)
                                ) in
                (
                Seq nil pls1 
                          (exp (
                                  all X, (X >' 0 ->' ((inv X) ->' << p >> (inv (X -' 1), psi)))
                               )
                          )
                            nil
                              (cdl_V (
                                        all X, (X >' 0 ->' ((inv X) ->' << p >> (inv (X -' 1), psi)))
                                     ) nil)
                                  C 
                                    ntC
                )
              )
              /\
              (
                let X := var (NewId (cdl_V_f inv nil)) in
                (
                Seq nil pls1
                          (exp (
                                  (ext X, X <=' 0 /\' (inv X)) ->' phi
                               )
                          )
                            nil
                              (cdl_V ((ext X, X <=' 0 /\' (inv X)) ->' phi) nil)
                                  C 
                                    ntC
                )
              )
          )
          ->
          (
            Seq T pls1 
                    (exp (<< p^* >> (phi, psi))) D V C ntC
          )
|

(* ****************************** rules of FOL *********************** *)
(* Rule (o) *)
  r_o : forall (T : Gamma) (pls1 : place) (pls2 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName),
        (
          let fof := (Seq_2_CDLexp T pls1 pls2 D) in 
          (
            forall (st : Var -> nat) (fn : CName -> nat) (gn : CName -> nat) , (CDLexp_2_Arith fof st fn gn)
            (* the Prop formula corresponding to the sequent: `Seq T empty empty D V' *)
          )
        )
        ->
        (
          Seq T pls1 pls2 D V C ntC
        )
|

(* Rule (ax) *)
  r_ax : forall (T : Gamma) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName) 
                      (phi : cDL_exp), 
        (
          True
        )
        ->
        (
          Seq T (exp phi) (exp phi) D V C ntC
        )
|

(* Rule (cut) *)
  r_cut : forall (T : Gamma) (pls1 : place) (pls2 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName), 
        (
          forall (phi : cDL_exp),
            (
              Seq T pls1 pls2 (phi :: D) (V ++ (cdl_V phi V)) C ntC
            )
            /\
            (
              Seq (phi :: T) pls1 pls2 D (V ++ (cdl_V phi V)) C ntC
            )
        )
        ->
        (
          Seq T pls1 pls2 D V C ntC
        )
|

(* Rule (~ r) *)
  r_negR : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                (phi : cDL_exp),
        (
          Seq ((~' phi):: T) pls1 empty D V C ntC
        )
        ->
        (
          Seq T pls1 (exp phi) D V C ntC
        )
|

(* Rule (~ l) *)
  r_negL : forall (T : Gamma) (pls2 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                (phi : cDL_exp),
        (
          Seq T empty pls2 ((~' phi)::D) V C ntC
        )
        ->
        (
          Seq T (exp phi) pls2 D V C ntC
        )
|

(* Rule (/\ r) *)
  r_andR : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                (phi1 : cDL_exp) (phi2 : cDL_exp),
        (
          (
            Seq T pls1 (exp phi1) D V C ntC
          )
          /\
          (
            Seq T pls1 (exp phi2) D V C ntC
          )
        )
        ->
        (
          Seq T pls1 (exp (phi1 /\' phi2)) D V C ntC
        )
|

(* Rule (/\ l 1) *)
  r_andL_1 : forall (T : Gamma) (pls2 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                (phi1 : cDL_exp) (phi2 : cDL_exp),
        (
          Seq T 
                (exp phi1) pls2 D V C ntC
        )
        ->
        (
          Seq T (exp (phi1 /\' phi2)) pls2 D V C ntC
        )
|

(* Rule (/\ l 2) *)
  r_andL_2 : forall (T : Gamma) (pls2 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                (phi1 : cDL_exp) (phi2 : cDL_exp),
        (
          Seq T 
                (exp phi2) pls2 D V C ntC
        )
        ->
        (
          Seq T (exp (phi1 /\' phi2)) pls2 D V C ntC
        )
|

(* Rule (all r) *)
  r_allR : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                (phi : cDL_exp) (x : Var),
        (
          let n := NewId V in
          (
            Seq T pls1 
                    (
                      exp (phi [(var n) subs &x])
                    )
                        D 
                          ((var n) :: V) 
                              C ntC
          )
        )
        ->
        (
          Seq T pls1 (exp (all x , phi)) D V C ntC
        )
|

(* Rule (all l) *)

  r_allL : forall (T : Gamma) (pls2 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                (phi : cDL_exp) (x : Var),
        (
          exists (E : e_exp),
          (
            (cdl_chk phi (e_exp_V E nil) (&x) nil) (* make sure that the substitution phi[E / x] is admissible *)
            /\
            (
              Seq ((all x , phi) :: T) 
                      ( 
                        exp (phi [E subs &x])
                      )
                        pls2
                          D
                            (V ++ (e_exp_V E V)) C ntC
            )
          )
        )
        ->
        (
          Seq T (exp (all x , phi)) pls2 D V C ntC
        )
|

(* Rule (\/ r 1) *)
  r_orR_1 : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName) 
                 (phi1 : cDL_exp) (phi2 : cDL_exp),
        (
          Seq T pls1 (exp phi1) D V C ntC
        )
        ->
        (
          Seq T pls1 (exp (phi1 \/' phi2)) D V C ntC
        )
|

(* Rule (\/ r 2) *)
  r_orR_2 : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName) 
                 (phi1 : cDL_exp) (phi2 : cDL_exp),
        (
          Seq T pls1 (exp phi2) D V C ntC
        )
        ->
        (
          Seq T pls1 (exp (phi1 \/' phi2)) D V C ntC
        )
|

(* Rule (\/ l) *)
  r_orL : forall (T : Gamma) (pls2 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName) 
                (phi1 : cDL_exp) (phi2 : cDL_exp),
        (
          (
            Seq T (exp phi1) pls2 D V C ntC
          )
          /\
          (
            Seq T (exp phi2) pls2 D V C ntC
          )
        )
        ->
        (
          Seq T (exp (phi1 \/' phi2)) pls2 D V C ntC
        )
|

(* Rule (-> r) *)
  r_impR : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                  (phi1 : cDL_exp) (phi2 : cDL_exp),
        (
          Seq (phi1 :: T) pls1 (exp phi2) D V C ntC
        )
        ->
        (
          Seq T pls1 (exp (phi1 ->' phi2)) D V C ntC
        )
|

(* Rule (-> l) *)
  r_impL : forall (T : Gamma) (pls2 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                  (phi1 : cDL_exp) (phi2 : cDL_exp),
        (
          (
            Seq T empty pls2 (phi1 :: D) V C ntC
          )
          /\
          (
            Seq T (exp phi2) pls2 D V C ntC
          )
        )
        ->
        (
          Seq T (exp (phi1 ->' phi2)) pls2 D V C ntC
        )
|

(* Rule (ext r) *)
  r_extR : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName) 
                  (phi : cDL_exp) (x : Var),
        (
          exists (E : e_exp),
            (cdl_chk phi (e_exp_V E nil) (&x) nil) (* make sure that the substitution phi[E / x] is admissible *)
            /\
            (
              Seq T pls1 
                      (exp (phi [ E subs &x ])) 
                        D 
                          (V ++ (e_exp_V E V)) C ntC
            )
        )
        ->
        (
          Seq T pls1 (exp (ext x , phi)) D V C ntC
        )
|

(* Rule (ext l) *)
  r_extL : forall (T : Gamma) (pls2 : place) (D : Delta) (V : list Var) (C : list CName) (ntC : list CName)
                (phi : cDL_exp) (x : Var),
        (
          let n := NewId V in
          (
            Seq ((ext x, phi) :: T) 
                    (
                      exp (phi [(var n) subs &x])
                    )
                      pls2
                        D 
                          ((var n) :: V) C ntC
          )
        )
        ->
        (
          Seq T (exp (ext x , phi)) pls2 D V C ntC
        )
(* define the notation at the end *)  
where "<| T , p1  ==>  p2 , D  //  V , C , ntC |>" := (Seq T p1 p2 D V C ntC)
.

Locate "//".

Theorem tst1 : <| nil, (exp tt')  ==>  (exp tt') , nil  //  nil , nil , nil |>.
Proof.
apply r_ax.
auto.
Qed.

Theorem tst4 : forall (a b c : nat), 
(a = b + 1 /\ b = 0) -> (False \/ a >= 1).
Proof. 
intros.
omega.
Qed.

Theorem tstsb : Eexp_2_exp (4 -' (var 2)) st0 fn0 gn0 = 0.
Proof. 
  compute [Eexp_2_exp]. cbv.

(*
Theorem tst5 : True.
Proof.

Qed.

Theorem tst3 : forall (a b c : nat), 
(a = b + 1 /\ b = 0) -> (False \/ (a >= 1 /\ True)).
Proof. 
intros a b c.
intros. 
omega.
Qed.
*)

(*
Theorem tst2 : forall (st : Var -> nat) (fn gn : CName -> nat), 
(fn (clk 1) = st (var 1) + 1 /\ st (var 1) = 0) -> False \/ fn(clk 1) >= 0 /\ True.
Proof. 
intros. auto. 
omega.
Qed.
*)

Theorem tst6 : (True /\ True) /\ (True /\ True).
Proof.
  auto.
Qed.

Theorem tst9 : forall (st : Var -> nat) (fn gn : CName -> nat), 
(
     (st (var 3) - fn (clk 2)) + st (var 2) = 4 /\ 
     fn (clk 1) = st (var 3) + 1
) -> (
(fn (clk 1) - fn (clk 2)) + (st (var 2) - 1) = 4
).
Proof. 
  intros. omega.


Theorem tst8 : forall (st : Var -> nat) (fn gn : CName -> nat), 
(
(gn (clk 3) = 0 /\
     gn (clk 2) = 0 /\
     fn (clk 1) = st (var 3) + 1 /\
     gn (clk 1) = 1 /\
     ((st (var 3) - fn (clk 2)) + st (var 2) = 4 /\ st (var 3) - fn (clk 3) >= 0 /\ fn (clk 3) - fn (clk 2) >= 0) /\
     st (var 2) > 0 /\ 0 = 0) /\ 0 = 0
) -> (
((fn (clk 1) - fn (clk 2)) + (st (var 2) - 1) = 4 /\ fn (clk 1) - fn (clk 3) >= 0 /\ fn (clk 3) - fn (clk 2) >= 0) /\
((fn (clk 1) > fn (clk 3) \/ fn (clk 1) = fn (clk 3) /\ gn (clk 3) = 0) /\ fn (clk 3) >= fn (clk 2)) /\
(gn (clk 1) = 1 \/ gn (clk 2) = 1 \/ gn (clk 3) = 1) \/ 0 > 0
).

Proof. 
  intros. simpl. omega.
Qed.


(*
Theorem tst7 : forall (st : Var -> nat) (fn : CName -> nat), 
((fn (clk 1) - fn (clk 2) = match st (var 2) with
                              |0 => 4
                              |1 => 3
                              |2 => 2
                              |3 => 1
                              |S (S (S (S _))) => 0
                            end
/\ fn(clk 1) - fn (clk 3) >=0 /\ fn (clk 3) - fn (clk 2) >= 0 /\ 
st (var 2) > 0 /\ 0 = 0) /\ 0 = 0) -> 
(fn (clk 1) - fn (clk 2) < 4 \/ 0 > 0).
Proof. 
  intros. simpl. cbn. omega.
Qed.
*)

Theorem tstThm0 : <| ((h(c) =' 0 /\' y(c) =' 0):: nil) , empty  ==>  exp (<< @ {c} >> (h(c) >=' 1, tt')) , nil  //
                 nil , c :: nil , c:: nil |>.
Proof. 
apply r_Alpha_c. cbv.
apply r_Alpha_idle1. cbv.
apply r_placeR_rmv. 
apply r_o. cbn.
intros. 
omega.

Theorem tstThm1 : <| ((h(c) =' 0 /\' y(c) =' 0):: nil) , empty  ==>  exp (<< @ {c | c} >> (h(c) >=' 2, tt')) , nil  //
                 nil , c :: nil , c:: nil |>.
Proof. 
apply r_Alpha_c. cbv.
apply r_Alpha_c. cbv.
apply r_Alpha_idle1. cbv.
apply r_placeR_rmv. apply r_o. cbn.
intros.
omega.
Qed.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* the example in the paper*)
(* clocks v1, u1 and v3*)
Definition v1 : CName := (clk 1).
Definition u1 : CName := (clk 2).
Definition v3 : CName := (clk 3). 

(* program p *)
(* g1, g2*)
Definition g1 : g_exp := D(v1, u1) < 4.
Definition g2 : g_exp := D(v1, u1) == 4.
Print g1. 
Print g2.
(* p2, p3, p4*)
Definition p2 : CPM_exp := @ nil U g1?{v1} U  g1?{v1|v3}.
Print p2. 
Definition p3 : CPM_exp := @ nil U g2?{v1} U g2?{v1|v3}.
Print p3. 
Definition p4 : CPM_exp := @ nil U @ {v1|u1} U @ {v1|u1|v3}.
Print p4. 
(* p *)
Definition p : CPM_exp := p2^w U (p2^* ; p3 ; p4^w).
Print p.

(* initial condition I *)
Definition I : cDL_exp := (h(v1) =' 0 /\' y(v1) =' 0) /\'
                          (h(u1) =' 0 /\' y(u1) =' 0) /\'
                          (h(v3) =' 0 /\' y(v3) =' 0).
Print I. 
(* formula psi *)
(* formula expressing the specification *)
Definition psi_sp1 := (h(v1) >' h(v3) \/' (h(v1) =' h(v3) /\' y(v3) =' 0)) /\' h(v3) >=' h(u1).
(* formula for expressing `at least one clock ticks at each instant of a schedule' *)
Definition psi_es := y(v1) =' 1 \/' y(u1) =' 1 \/' y(v3) =' 1.
(* psi *)
Definition Psi := psi_sp1 /\' psi_es. 
Compute Psi. 

(* Other components in the sequent *)
Definition Gamma0 : Gamma := nil.
Definition Delta0 : Delta := nil.
Definition V0 : list Var := nil. 
Definition C0 : list CName := v1 :: u1 :: v3 :: nil.
Definition ntC0 : list CName := C0. 

Theorem Example : <| Gamma0 , empty ==> exp ( I ->' << p >> (tt' , Psi) ), Delta0 // 
                     V0, C0, ntC0 |>.

Definition inv1 (k : e_exp) : cDL_exp := (h(v1) -' h(u1)) +' k =' 4 /\' 
                                         h(v1) -' h(v3) >=' 0 /\'
                                         h(v3) -' h(u1) >=' 0.

Proof.
  apply r_impR. (* rule -> r *) 
  apply r_Choice. (* rule choice *)
  apply r_orR_2. (* rule \/ r 2 *)
  apply r_Seq. (* rule sequence *)
  apply r_Star_dia; exists inv1; split; [|split]. (* rule << star >> *) 
  - apply r_extR. exists 4. simpl. split. (* rule ext r *)
    + intuition.
    + apply r_o. cbn. intros. omega. (* rule o *)
  - apply r_allR. apply r_impR; apply r_impR. cbn. (* rule all r, rule -> r *)
    apply r_Choice. apply r_orR_2. apply r_Choice. apply r_orR_1. (* rule cho, \/ r 2, cho, \/ r 2 *)
    apply r_Guard. apply r_andR; split. 
    + cbv. apply r_o;cbn. intros. omega. (* rule o *)
    + cbv. apply r_Alpha_c. apply r_Alpha_idle2; apply r_Alpha_idle2; apply r_Alpha_idle1; cbv. (* rule alpha *)
      apply r_o. cbn. intros. omega.

(* program p2 *)
Definition P1 : P_exp := (x '= 2) '/\ (f '= 0).
Definition P2 : P_exp := (x '< 2) '/\ (f '= 0).

Definition a2 : Evt := { p ! 0 | f :=' 1 }.
Definition a3 : Evt := { p ! 0 | x :=' x '+ 1 }.
Print a3.

Definition p2 : SEP_exp := P1 ? a2 U P2 ? a3.
Print p2.


(* Gamma2 *)
Definition Gamma2 : Gamma := (Y >=' n(o)) :: (n(r) =' Y +' 1) :: (s(r) =' 1) :: (x =' 1) :: 
                             (f =' 0) :: (s(e) =' 0) :: (s(p) =' 0) :: (s(o) =' 0) :: nil. 
Print Gamma2.

Theorem example : <| Gamma2 , empty ==> (exp ([[ p2 ]]' r << o)) , nil //
                     (x :: f :: Y :: e :: p :: r :: o :: nil), 
                     (e :: p :: r :: o :: nil), 
                     (e :: p :: r :: o :: nil)
                  |>.

Proof.
  apply r_PiCho_all_int. 
  apply r_andR_int. split.
  Focus 2.
  - apply r_Test_all_rel_int.
    apply r_impR_int. 
    apply r_placeL_rmv_int. 
    apply r_Pi_all_int2; cbv.
    apply r_Pi_all_int1; cbv.
    apply r_Pi_all_int_idle2;apply r_Pi_all_int_idle2;apply r_Pi_all_int_idle2; cbv.
    apply r_Pi_all_int_idle1; cbv.
    apply r_placeR_rmv_int.
    apply r_o_int. cbn.
    intros H1 H2 H3. 
    omega.
  Admitted.
