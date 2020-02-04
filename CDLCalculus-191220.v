Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.

Import ListNotations.


(* Syntax of Clock-based Dynamic Logic *)

(* Syntax of SEP_exp (Synchonous Event Program) *)


(* ========================= Syntax of SEP_exp ========================*)

(* =============== Syntax of Expressions ===================*)

(* Arith Expression `e'*)

Inductive Var := var : nat -> Var.
(* in this version, I try to understand variables as identifications numbered by natural numbers, 
which we believe is more convenient than considering them as strings in practical derivations*)

Inductive e_exp := 
  enumC : nat -> e_exp | 
  evarC : Var -> e_exp | 
  eplusC : e_exp -> e_exp -> e_exp |
  (*non-necessary expression*)
  eminusC : e_exp -> e_exp -> e_exp |
  emulC : e_exp -> e_exp -> e_exp |
  edivC : e_exp -> e_exp -> e_exp
.
Print e_exp.


Notation "e1 '+ e2" := (eplusC e1 e2) (at level 31, right associativity).
Locate "'+".
Notation "e1 '- e2" := (eminusC e1 e2) (at level 31, right associativity).

Notation "e1 '* e2" := (emulC e1 e2) (at level 21, right associativity).

(*** Open Scope e_exp_scope. ***)

Locate "*".
Check (enumC 4) '* (enumC 5 '+ enumC 6).
Coercion evarC : Var >-> e_exp.
Notation "e1 '/ e2" := (edivC e1 e2) (at level 21, right associativity).
Check (enumC 4) '/ (enumC 4).

Coercion enumC : nat >-> e_exp.
Definition x : Var := (var 1).
Definition y : Var := (var 2).
Definition z : Var := (var 3).
Definition k : Var := (var 4).

Check 4 '* (5 '+ 2).
Check (5 '+ 4) '* 8.
Check x '- 3.
Compute x '- 3.
Check 5 '+ 4 '* 5.






(* Boolean Expression `P'*)
Inductive P_exp := 
  PtrueC : P_exp |
  PlteC : e_exp -> e_exp -> P_exp |
  PnegC : P_exp -> P_exp |
  PandC : P_exp -> P_exp -> P_exp |
  (*non-necesarry expression*)
  PfalseC : P_exp |
  PltC : e_exp -> e_exp -> P_exp |
  PgtC : e_exp -> e_exp -> P_exp |
  PgteC : e_exp -> e_exp -> P_exp |
  PeqC : e_exp -> e_exp -> P_exp |
  PorC : P_exp -> P_exp -> P_exp |
  PimpC : P_exp -> P_exp -> P_exp
.
Print P_exp.

(* 33 - 41 *)
Notation "''tt'" := PtrueC (at level 35).
Notation "e1 '<= e2" := (PlteC e1 e2) (at level 33).
Notation "'~ P" := (PnegC P) (at level 36).
Notation "P1 '/\ P2" := (PandC P1 P2) (at level 37, right associativity).
Notation "''ff'" := PfalseC (at level 35).
Notation "e1 '< e2" := (PltC e1 e2) (at level 33).
Notation "e1 '> e2" := (PgtC e1 e2) (at level 33).
Notation "e1 '>= e2" := (PgteC e1 e2) (at level 33).
Notation "e1 '= e2" := (PeqC e1 e2) (at level 33).
Notation "P1 '\/ P2" := (PorC P1 P2) (at level 37, right associativity).
Notation "P1 '-> P2" := (PimpC P1 P2) (at level 38, right associativity).

Locate "'/\".
Check 'tt '-> 'ff.
Check 5 '+ x '>= 5 '-> 3 '> 7.
Compute 5 '+ x '>= 5 '-> 3 '> 7.


(* Evaluation *)
Definition state := Var -> nat. 

(***
  Definging the evaluation for expressions is for checking the validation of FOL formulas after 
  transformation. 
***)

Fixpoint eval_e_exp (e : e_exp) (st : state) : nat :=  
(* st maps each var name to a value --- it is a state *)
  match e with
  | enumC n => n
  | evarC s => st s
  | eplusC e1 e2 => (eval_e_exp e1 st) + (eval_e_exp e2 st)
  | eminusC e1 e2 => (eval_e_exp e1 st) - (eval_e_exp e2 st)
  | emulC e1 e2 => (eval_e_exp e1 st) * (eval_e_exp e2 st)
  | edivC e1 e2 => (eval_e_exp e1 st) / (eval_e_exp e2 st)
  end.


Fixpoint eval_P_exp (P : P_exp) (st : state) : Prop :=
  match P with
  | PtrueC => True
  | PlteC e1 e2 => (eval_e_exp e1 st) <= (eval_e_exp e2 st)
  | PnegC P' => ~ (eval_P_exp P' st)
  | PandC P1 P2 => (eval_P_exp P1 st) /\ (eval_P_exp P1 st)
  | PfalseC => False
  | PltC e1 e2 => (eval_e_exp e1 st) < (eval_e_exp e2 st)
  | PgtC e1 e2 => (eval_e_exp e1 st) > (eval_e_exp e2 st)
  | PgteC e1 e2 => (eval_e_exp e1 st) >= (eval_e_exp e2 st)
  | PeqC e1 e2 => (eval_e_exp e1 st) = (eval_e_exp e2 st)
  | PorC P1 P2 => (eval_P_exp P1 st) \/ (eval_P_exp P1 st)
  | PimpC P1 P2 => (eval_P_exp P1 st) -> (eval_P_exp P1 st)
  end.

(* =============== Syntax of Event ===================*)


(* Event *)
Inductive EvtElement := 
  sigC : Var -> e_exp -> EvtElement | (* Signal *)
  assC : Var -> e_exp -> EvtElement  (* Assignment *)
.
Check EvtElement. 

Notation "s ! e" := (sigC s e) (at level 45).
Notation "x :=' e" := (assC x e) (at level 45).

(* currently we do not make distinguish between variable and clock names, both are strings*)
Definition c : Var := (var 5).
Definition d : Var := (var 6).
Definition c1 : Var  := (var 7).
Definition c2 : Var  := (var 8).
Definition c3 : Var  := (var 9).
Definition c4 : Var  := (var 10).

Check x :=' 4.
Compute x :=' 4.
Check c ! (x '+ 4).

Definition Evt := list EvtElement.

Check Evt.
Check (x :=' 4) :: (c!(x '+ 4)) :: nil.

(* ========================= Syntax of program ========================*)
Inductive SEP_exp : Type := 
  skip : SEP_exp | (* skip program $\varepsilon$ *)
  evtC : Evt -> SEP_exp | (* Event *)
  tstC : P_exp -> Evt -> SEP_exp | (* Test *)
  seqC : SEP_exp -> SEP_exp -> SEP_exp | (* sequence *)
  choC : SEP_exp -> SEP_exp -> SEP_exp | (* choice *)
  loopC : SEP_exp -> SEP_exp (* loop *)
.

Coercion evtC : Evt >-> SEP_exp.
Notation "{ a1 | .. | an }" := (cons a1 .. (cons an nil) .. ) (at level 45). 
Notation "@ a" := (evtC a) (at level 46).
Definition idle : Evt := nil.
Notation "P ? a" := (tstC P a) (at level 48).
Notation "P1 ; P2" := (seqC P1 P2) (at level 49, left associativity).
Notation "P1 'U' P2" := (choC P1 P2) (at level 51, left associativity).
Notation "P **" := (loopC P) (at level 47, left associativity).

Locate "**".
Check x :=' 4 :: nil.
Check evtC (x :=' 4 :: nil).
Check { x :=' 4 }.
Check { x :=' 4 | c1 ! 5}.
Check @ { x :=' 4 | c1 ! 5 }.
Check idle.
Check x '> 0 ? {c!4}.

(* ========================================= Syntax of CDL Formula ===============================================*)

(* ================== CCSL ======================== *)
(* clock relation *)
(***
  Currently, we model clocks as `strings', becuase now we don't need to give its semantics. 
  It won't work anymore if we consider its semantics later.
***)

Inductive CRel := 
  crSubClC : Var -> Var -> CRel |
  crExclC : Var -> Var -> CRel |
  crPrecC : Var -> Var -> CRel |
  crCausC : Var -> Var -> CRel
.
Check CRel.

Notation "c1 'sub' c2" := (crSubClC c1 c2) (at level 52).
Notation "c1 # c2" := (crExclC c1 c2) (at level 52).
Notation "c1 << c2" := (crPrecC c1 c2) (at level 52).
Notation "c1 <<= c2" := (crCausC c1 c2) (at level 52).

Check c1 << c2.
Check c1 # c2.
Check c1 sub c2.
Compute c1 << c2.

(* ================== CDL Formula ======================== *)
(* Clock relation in formula *)
Inductive rel := 
  rRelC : CRel -> rel |
  rConjC : list CRel -> rel
.
Print rel.

Coercion rRelC : CRel >-> rel.
Check c1 << c2.

Notation "/\{ c1 , .. , cn }" := (rConjC (cons c1 .. (cons cn nil) ..)).
Check /\{ c1 << c2 , c2 sub c3 , c1 <<= c3}.


(* Arith Expression `E' *)
(*DEL
(* define a map that maps each clock/signal to a variable that records the number it has ticked in history. *)
Definition CntClk := string -> string. 

(* define a map that maps each clock/signal to a variable that records the current state of this clock. *)
Definition StClk := string -> string. 
DEL*)

Inductive E_exp :=
  EvarC : Var -> E_exp |
  ECntClkC : Var -> E_exp | (* define a map that maps each clock/signal to a variable that records the number it has ticked in history. *)
  EStClkC : Var -> E_exp | (* define a map that maps each clock/signal to a variable that records the current state of this clock. *)
  EnumC : nat -> E_exp |
  EplusC : E_exp -> E_exp -> E_exp |
  (* unecessary expression *)
  EmulC : E_exp -> E_exp -> E_exp |
  EminusC : E_exp -> E_exp -> E_exp |
  EdivC : E_exp -> E_exp -> E_exp
.
Print E_exp. 

Coercion EvarC : Var >-> E_exp.
Notation "n( c )" := (ECntClkC c) (at level 52). (* the only DIFFERENCE between e_exp and E_exp *)
Notation "s( c )" := (EStClkC c) (at level 52).
Coercion EnumC : nat >-> E_exp.
Notation "e1 +' e2" := (EplusC e1 e2) (at level 55, right associativity).
Notation "e1 *' e2" := (EmulC e1 e2) (at level 53, right associativity).
Notation "e1 -' e2" := (EminusC e1 e2) (at level 55, right associativity).
Notation "e1 /' e2" := (EdivC e1 e2) (at level 53, right associativity).

Check 5 +' 3.
Check 5 '+ 3.
Check 5 *' (3 +' 5).
Check n(c) *' 4.
Compute n(c) *' 4.





(* CDL Formula *)
Inductive CDL_exp := 
  cdl_trueC : CDL_exp |
  cdl_ltC : E_exp -> E_exp -> CDL_exp |
  cdl_box1C : SEP_exp -> rel -> CDL_exp |
  cdl_box2C : SEP_exp -> CDL_exp -> CDL_exp |
  cdl_negC : CDL_exp -> CDL_exp |
  cdl_andC : CDL_exp -> CDL_exp -> CDL_exp |
  cdl_forallC : Var -> CDL_exp -> CDL_exp |
  (* unnecessary expressions *)
  cdl_falseC : CDL_exp |
  cdl_lteC : E_exp -> E_exp -> CDL_exp |
  cdl_gtC : E_exp -> E_exp -> CDL_exp |
  cdl_gteC : E_exp -> E_exp -> CDL_exp |
  cdl_eqC : E_exp -> E_exp -> CDL_exp |
  cdl_dia1C : SEP_exp -> rel -> CDL_exp |
  cdl_dia2C : SEP_exp -> CDL_exp -> CDL_exp |
  cdl_orC : CDL_exp -> CDL_exp -> CDL_exp |
  cdl_impC : CDL_exp -> CDL_exp -> CDL_exp
.

Notation "'tt''" := cdl_trueC (at level 65).
Notation "e1 <' e2" := (cdl_ltC e1 e2) (at level 61).
Notation "[ p ]' r" := (cdl_box1C p r) (at level 63, p at level 62, r at level 62).
Notation "[ p ] e" := (cdl_box2C p e) (at level 63, p at level 62, e at level 62).
Notation "~' e" := (cdl_negC e) (at level 67).
Notation "e1 /\' e2" := (cdl_andC e1 e2) (at level 69, right associativity).
Notation "'all' x , e" := (cdl_forallC x e) (at level 68, x at level 67).
(* unnecessary expressions *)
Notation "'ff''" := cdl_falseC (at level 65).
Notation "e1 <=' e2" := (cdl_lteC e1 e2) (at level 61).
Notation "e1 >' e2" := (cdl_gtC e1 e2) (at level 61).
Notation "e1 >=' e2" := (cdl_gteC e1 e2) (at level 61).
Notation "e1 =' e2" := (cdl_eqC e1 e2) (at level 61).
Notation "< p >' r" := (cdl_dia1C p r) (at level 63).
Notation "< p > e" := (cdl_dia2C p e) (at level 63).
Notation "e1 \/' e2" := (cdl_orC e1 e2) (at level 71, right associativity).
Notation "e1 ->' e2" := (cdl_impC e1 e2) (at level 72, right associativity).

Check tt'.
Check ff'.
Check (5 -' 3) <' 2.
Check ([ skip ]' c1 << c2) /\' 2 >' 5 /\' tt'.
Check [ @ {x :=' 4 | c1 ! 5} ; (x '> 0) ? {c2!4} ; @ idle; skip] n(c) >' 0.
Check [(@ {x :=' 4 | c1 ! 5} ; (x '> 0) ? {c2!4} ; @ idle; skip)** ]' c1<<c2.
Check [ skip ]' c1 << c2 .
Check all x , 4 =' 5.





(* ===================================================== CDL Calculus ======================================*)


(*************************** Auxiliary Functions ***************************)
(*check if a dynamic formula is a pure FOL formula *)

Fixpoint CheckPureFOL (e : CDL_exp) : Prop :=
  match e with
  | cdl_trueC => True
  | cdl_ltC e1 e2 => True
  | cdl_box1C p r => False
  | cdl_box2C p e' => False
  | cdl_negC e' => CheckPureFOL e'
  | cdl_andC e1 e2 => (CheckPureFOL e1) /\ (CheckPureFOL e2)
  | cdl_forallC x e' => (CheckPureFOL e')
  | cdl_falseC => True
  | cdl_lteC e1 e2 => True
  | cdl_gtC e1 e2 => True
  | cdl_gteC e1 e2 => True
  | cdl_eqC e1 e2 => True
  | cdl_dia1C p r => False
  | cdl_dia2C p e' => False
  | cdl_orC e1 e2 => (CheckPureFOL e1) /\ (CheckPureFOL e2)
  | cdl_impC e1 e2 => (CheckPureFOL e1) /\ (CheckPureFOL e2)
  end.


(* a structure of (true, false, `undefined') *)
Inductive Bool :=
  bBoolC : Prop -> Bool |
  bUndefC : Bool
.

(*
Notation "[ b ]" := (bBoolC b) (at level 74).
Notation "_|_" := bUndefC (at level 74).
*)

(* evaluate a pure FOL formula in CDL formula *)


(* during the derivation we need to translate expression e to expression E. In the semantics of dynamic logic, their 
corresponding arithmetical opertors have the same meanings *)

Fixpoint e_2_E (e : e_exp) : E_exp :=
  match e with
  | enumC n => EnumC n
  | evarC s => EvarC s
  | eplusC e1 e2 => EplusC (e_2_E e1) (e_2_E e2)
  | eminusC e1 e2 => EminusC (e_2_E e1) (e_2_E e2)
  | emulC e1 e2 => EmulC (e_2_E e1) (e_2_E e2)
  | edivC e1 e2 => EdivC (e_2_E e1) (e_2_E e2)
  end.





(* -------------------------------computation of free variables in cdl formula----------------------------------------*)
(***
Note that actually here we compute all occurrences of free variables in a cdl formula, not really all free variables, because
here we use `list' as the structure to `store' each appearance of free variables. 
It is enough for us to check whether a variable is a free variable or not in a formula checking if it does not equal to 
each occurrence of variables. 
***)

(* compare the id of two variables *)
Definition eqv (x : Var) (y: Var) : bool :=
  match x, y with
  | var n, var m => if n =? m then true else false
  end.

(* this function check whether a variable (i.e. a string) belongs to a list of variables (list of string) *)
Fixpoint NotIn_bool (s : Var) (vec : list Var) : bool :=
  match vec with
  | nil => true
  | v :: vec' => if (eqv s v) then false else NotIn_bool s vec'
  end.

Compute NotIn_bool x (x :: y :: z :: nil).
Compute NotIn_bool c (x :: y :: z :: nil).

(* this is another version for Prop type, just in case we need it in building the proof system*)
Fixpoint NotIn (s : Var) (vec : list Var) : Prop :=
  match vec with
  | nil => True
  | v :: vec' => if (eqv s v) then False else NotIn s vec'
  end.

Compute NotIn x (x :: y :: z :: nil).
Compute NotIn c (x :: y :: z :: nil).

Fixpoint In (s : Var) (vec : list Var) : Prop :=
  match vec with
  | nil => False
  | v :: vec' => if (eqv s v) then True else In s vec'
  end.

Fixpoint E_exp_FV (e : E_exp) (bv : list Var) : list Var := (*bv : list of bounded variables at current time *)
  match e with
  | EvarC v => if (NotIn_bool v bv) then (v :: nil) else nil
  | ECntClkC c => nil
  | EStClkC c => nil
  | EnumC n => nil
  | EplusC e1 e2 => (E_exp_FV e1 bv) ++ (E_exp_FV e2 bv)
  | EmulC e1 e2 => (E_exp_FV e1 bv) ++ (E_exp_FV e2 bv)
  | EminusC e1 e2 => (E_exp_FV e1 bv) ++ (E_exp_FV e2 bv)
  | EdivC e1 e2 => (E_exp_FV e1 bv) ++ (E_exp_FV e2 bv)
  end
.

Compute E_exp_FV (x +' 3 *' n(c)) nil.
Compute E_exp_FV (x +' 3 *' z) nil.
Compute E_exp_FV (x +' 3 *' z) (x :: nil).


Fixpoint e_exp_FV (e : e_exp) (bv : list Var) : list Var :=
  match e with 
  | enumC n => nil
  | evarC s => if (NotIn_bool s bv) then (s :: nil) else nil
  | eplusC e1 e2 => (e_exp_FV e1 bv) ++ (e_exp_FV e2 bv)
  | eminusC e1 e2 => (e_exp_FV e1 bv) ++ (e_exp_FV e2 bv)
  | emulC e1 e2 => (e_exp_FV e1 bv) ++ (e_exp_FV e2 bv)
  | edivC e1 e2 => (e_exp_FV e1 bv) ++ (e_exp_FV e2 bv)
  end
.

Compute e_exp_FV (x '+ 3 '* 5) nil.
Compute e_exp_FV (x '+ 3 '* z) nil.
Compute e_exp_FV (x '+ 3 '/ z) (x :: nil).

Fixpoint P_exp_FV (P : P_exp) (bv : list Var) : list Var :=
  match P with
  | PtrueC => nil
  | PlteC e1 e2 => (e_exp_FV e1 bv) ++ (e_exp_FV e2 bv)
  | PnegC P' => P_exp_FV P' bv
  | PandC P1 P2 => (P_exp_FV P1 bv) ++ (P_exp_FV P2 bv)
  | PfalseC => nil
  | PltC e1 e2 => (e_exp_FV e1 bv) ++ (e_exp_FV e2 bv)
  | PgtC e1 e2 => (e_exp_FV e1 bv) ++ (e_exp_FV e2 bv)
  | PgteC e1 e2 => (e_exp_FV e1 bv) ++ (e_exp_FV e2 bv)
  | PeqC e1 e2 => (e_exp_FV e1 bv) ++ (e_exp_FV e2 bv)
  | PorC P1 P2 => (P_exp_FV P1 bv) ++ (P_exp_FV P2 bv)
  | PimpC P1 P2 => (P_exp_FV P1 bv) ++ (P_exp_FV P2 bv)
  end
.

Compute P_exp_FV ('tt '/\ (3 '= 5 '* x)) nil.
Compute P_exp_FV ('tt '/\ (3 '= 5 '* x)) (x :: nil).
Compute P_exp_FV (y '<= 5 '/\ (3 '= 5 '* x)) (z :: nil).

Fixpoint EvtE_FV (e : EvtElement) (bv : list Var) : list Var :=
  match e with 
  | sigC s e' => e_exp_FV e' bv
  | assC s e' => e_exp_FV e' bv
  end
.

Fixpoint Evt_FV (evt : Evt) (bv : list Var) : list Var :=
  match evt with 
  | nil => nil
  | e :: evt' => (EvtE_FV e bv) ++ (Evt_FV evt' bv)
  end
.

Compute Evt_FV ({ x:='y '+ 2 | c ! (z '* 38)}) nil.
Compute Evt_FV ({ x:='y '+ 2 | c ! (z '* 38)}) (y :: nil).

Fixpoint SEP_exp_FV (e : SEP_exp) (bv : list Var) : list Var :=
  match e with 
  | skip => nil
  | evtC evt => (Evt_FV evt bv)
  | tstC P evt => (P_exp_FV P bv) ++ (Evt_FV evt bv)
  | seqC e1 e2 => (SEP_exp_FV e1 bv) ++ (SEP_exp_FV e2 bv)
  | choC e1 e2 => (SEP_exp_FV e1 bv) ++ (SEP_exp_FV e2 bv)
  | loopC e' => (SEP_exp_FV e' bv)
  end
.

Check x '> 2 ? { y :=' y '- z}.
Compute SEP_exp_FV ((@ { x :=' 5}; x '> 2 ? { y :=' y '- z} U skip) **) nil.

Fixpoint cdl_FV (e : CDL_exp) (bv : list Var) : list Var := (*bv : list of bounded variables at current time *)
  match e with
  | cdl_trueC => nil
  | cdl_ltC e1 e2 => (E_exp_FV e1 bv) ++ (E_exp_FV e2 bv)
  | cdl_box1C p r => SEP_exp_FV p bv
  | cdl_box2C p e' => (SEP_exp_FV p bv) ++ (cdl_FV e' bv)
  | cdl_negC e' => cdl_FV e' bv
  | cdl_andC e1 e2 => (cdl_FV e1 bv) ++ (cdl_FV e2 bv)
  | cdl_forallC x1 e' => cdl_FV e' (x1 :: bv) (* x1 is a bounded variable *)
  | cdl_falseC => nil
  | cdl_lteC e1 e2 => (E_exp_FV e1 bv) ++ (E_exp_FV e2 bv)
  | cdl_gtC e1 e2 => (E_exp_FV e1 bv) ++ (E_exp_FV e2 bv)
  | cdl_gteC e1 e2 => (E_exp_FV e1 bv) ++ (E_exp_FV e2 bv)
  | cdl_eqC e1 e2 => (E_exp_FV e1 bv) ++ (E_exp_FV e2 bv)
  | cdl_dia1C p r => SEP_exp_FV p bv
  | cdl_dia2C p e' => (SEP_exp_FV p bv) ++ (cdl_FV e' bv)
  | cdl_orC e1 e2 => (cdl_FV e1 bv) ++ (cdl_FV e2 bv)
  | cdl_impC e1 e2 => (cdl_FV e1 bv) ++ (cdl_FV e2 bv)
  end
.

Check ( all y , y =' 7 ) .
Compute cdl_FV ([ (@ { x :=' 5}; x '> 2 ? { y :=' y '- z} U skip) ] x >' 0 /\' ( all y , y =' 7 ) ) nil.
Compute cdl_FV ([ (@ { x :=' 5}; x '> 2 ? { y :=' y '- z} U skip) ] x >' 0 /\' ( all y , y =' 7 ) ) (y :: nil).


(* for list *)
Fixpoint cdl_FV_l (T : list CDL_exp) (bv : list Var) : list Var :=
  match T with 
  | nil => nil
  | e :: T' => (cdl_FV e bv) ++ (cdl_FV_l T' bv)
  end.

(* -------------------------------substitution for single variable----------------------------------------*)
Fixpoint E_exp_subs (e : E_exp) (x' : Var) (x : Var) : E_exp := 
  match e with
  | EvarC v => if (eqv v x) then EvarC x' else EvarC v
  | ECntClkC c => ECntClkC c (* do not consider replacing a clock-related variable *)
  | EStClkC c => EStClkC c
  | EnumC n => EnumC n
  | EplusC e1 e2 => EplusC (E_exp_subs e1 x' x) (E_exp_subs e2 x' x)
  | EmulC e1 e2 => EmulC (E_exp_subs e1 x' x) (E_exp_subs e2 x' x)
  | EminusC e1 e2 => EminusC (E_exp_subs e1 x' x) (E_exp_subs e2 x' x)
  | EdivC e1 e2 => EdivC (E_exp_subs e1 x' x) (E_exp_subs e2 x' x)
  end
.

Compute E_exp_subs (x +' y) y x.
Compute E_exp_subs (x *' z) y c.
Compute E_exp_subs (n(c) *' z) y z.

Notation "e [ x' 'subs-E' x ]" := (E_exp_subs e x' x) (at level 9).

Fixpoint e_exp_subs (e : e_exp) (x' : Var) (x : Var) : e_exp :=
  match e with
  | enumC n => enumC n
  | evarC s => if (eqv s x) then evarC x' else evarC s
  | eplusC e1 e2 => eplusC (e_exp_subs e1 x' x) (e_exp_subs e2 x' x)
  | eminusC e1 e2 => eminusC (e_exp_subs e1 x' x) (e_exp_subs e2 x' x)
  | emulC e1 e2 => emulC (e_exp_subs e1 x' x) (e_exp_subs e2 x' x)
  | edivC e1 e2 => edivC (e_exp_subs e1 x' x) (e_exp_subs e2 x' x)
  end
.

Compute (z '- 5) '* x '+ z.
Compute e_exp_subs ((z '- 5) '* x '+ z) y z.

Fixpoint P_exp_subs (P : P_exp) (x' : Var) (x : Var) : P_exp :=
  match P with
  | PtrueC => PtrueC 
  | PlteC e1 e2 => PlteC (e_exp_subs e1 x' x) (e_exp_subs e2 x' x)
  | PnegC P' => PnegC (P_exp_subs P' x' x)
  | PandC P1 P2 => PandC (P_exp_subs P1 x' x) (P_exp_subs P2 x' x)
  | PfalseC => PfalseC
  | PltC e1 e2 => PltC (e_exp_subs e1 x' x) (e_exp_subs e2 x' x)
  | PgtC e1 e2 => PgtC (e_exp_subs e1 x' x) (e_exp_subs e2 x' x)
  | PgteC e1 e2 => PgteC (e_exp_subs e1 x' x) (e_exp_subs e2 x' x)
  | PeqC e1 e2 => PeqC (e_exp_subs e1 x' x) (e_exp_subs e2 x' x)
  | PorC P1 P2 => PorC (P_exp_subs P1 x' x) (P_exp_subs P2 x' x)
  | PimpC P1 P2 => PimpC (P_exp_subs P1 x' x) (P_exp_subs P2 x' x)
  end
.

Compute 'tt '/\ '~ (x '< 5).
Compute P_exp_subs ('tt '/\ '~ (x '< 5)) z x.

Fixpoint EvtE_subs (e : EvtElement) (x' : Var) (x : Var) : EvtElement :=
  match e with 
  | sigC s e' => sigC s (e_exp_subs e' x' x)
  | assC s e' => assC s (e_exp_subs e' x' x)
  end
.

Compute EvtE_subs (c ! x '+ 5) y x.
Compute EvtE_subs (x :=' (5 '* x '+ 3 '/ y)) z x. 

Fixpoint Evt_subs (evt : Evt) (x' : Var) (x : Var) : Evt :=
  match evt with 
  | nil => nil
  | e :: evt' => (EvtE_subs e x' x) :: (Evt_subs evt' x' x)
  end
.

Compute { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }.
Compute Evt_subs ( { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }) z x. 


Fixpoint SEP_exp_subs (e : SEP_exp) (x' : Var) (x : Var) : SEP_exp :=
  match e with 
  | skip => skip
  | evtC evt => evtC (Evt_subs evt x' x)
  | tstC P evt => tstC (P_exp_subs P x' x) (Evt_subs evt x' x) 
  | seqC e1 e2 => seqC (SEP_exp_subs e1 x' x) (SEP_exp_subs e2 x' x)
  | choC e1 e2 => choC (SEP_exp_subs e1 x' x) (SEP_exp_subs e2 x' x)
  | loopC e' => loopC (SEP_exp_subs e' x' x)
  end
.

Compute @ { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }.
Compute SEP_exp_subs ( @ { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }) z x. 

Fixpoint cdl_subs (e : CDL_exp) (x' : Var) (x : Var) : CDL_exp := (* e[x' // x] *)
  match e with
  | cdl_trueC => cdl_trueC
  | cdl_ltC e1 e2 => cdl_ltC (E_exp_subs e1 x' x) (E_exp_subs e2 x' x)
  | cdl_box1C p r => cdl_box1C (SEP_exp_subs p x' x) r (* do not consider replacing a clock-related variable *)
  | cdl_box2C p e' => cdl_box2C (SEP_exp_subs p x' x) (cdl_subs e' x' x)
  | cdl_negC e' => cdl_negC (cdl_subs e' x' x)
  | cdl_andC e1 e2 => cdl_andC (cdl_subs e1 x' x) (cdl_subs e2 x' x)
  | cdl_forallC x1 e' => if (eqv x1 x) then cdl_forallC x1 e' else (cdl_subs e' x' x) 
  | cdl_falseC => cdl_falseC
  | cdl_lteC e1 e2 => cdl_lteC (E_exp_subs e1 x' x) (E_exp_subs e2 x' x)
  | cdl_gtC e1 e2 => cdl_gtC (E_exp_subs e1 x' x) (E_exp_subs e2 x' x)
  | cdl_gteC e1 e2 => cdl_gteC (E_exp_subs e1 x' x) (E_exp_subs e2 x' x)
  | cdl_eqC e1 e2 => cdl_eqC (E_exp_subs e1 x' x) (E_exp_subs e2 x' x)
  | cdl_dia1C p r => cdl_dia1C (SEP_exp_subs p x' x) r (* do not consider replacing a clock-related variable *)
  | cdl_dia2C p e' => cdl_dia2C (SEP_exp_subs p x' x) (cdl_subs e' x' x)
  | cdl_orC e1 e2 => cdl_orC (cdl_subs e1 x' x) (cdl_subs e2 x' x)
  | cdl_impC e1 e2 => cdl_impC (cdl_subs e1 x' x) (cdl_subs e2 x' x)
  end.

Notation "e [ x' 'subs' x ]" := (cdl_subs e x' x) (at level 9).
Check [ skip ]' c1 << c2 .
Locate "/".
Locate "//".

Compute [ y '> 1 ? { x :=' x '+ 1 }; skip ; @ { x :=' x '+ 1 }]' c1 << c2.
Compute ([ y '> 1 ? { x :=' x '+ 1 }; skip ; @ { x :=' x '+ 1 }]' c1 << c2) [ y subs x ] .


(* substitution for list *)
Fixpoint cdl_subs_l (T : list CDL_exp) (x' : Var) (x : Var) : list CDL_exp := (* T [x' // x] *)
  match T with
  | nil => nil
  | e :: T' => (cdl_subs e x' x) :: (cdl_subs_l T' x' x)
  end.

Notation "T [ x' 'subs-l' x ]" := (cdl_subs_l T x' x) (at level 9).


(* ====================================================== CDL Rules =============================================*)

Definition Gamma := list CDL_exp.
Definition Delta := list CDL_exp.

(***DEL Definition SequentL : Gamma -> CDL_exp -> Delta -> Prop.*)


(* we arrange a place special for the dynamic formula we want to verify in the sequent, other formulas in Gamma
and Delta are pure FOL formulas. 

We define two types of sequent: sequentL and sequentR, where L and R indicate the verifiying formula is on the left
or right side of the sequent. 
*)

Inductive place := 
  exp : CDL_exp -> place |
  empty : place
.


(*
Notation "'<<' e '>>'" := (exp e) (at level 74, e at level 72).
Notation "<< >>" := empty (at level 74).
Check << x <=' y >> .
Check << >>.
Locate "<< >>".
*)


Reserved Notation "{ T , p1 ==> p2 , D }" (at level 75).
(*Reserved Notation "T ==> p , D" (at level 75).*)

Locate "==>".

(*&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&& a simple test &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&*)

(*** as a test, we firstly implement a simple rule here, to check if everything in my mind would work well, 
we first realize the rule: 
    T[x'/x],x = e[x'/x] => E, D[x'/x]
    ---------------------------------
    T => [x := e] E, D

It is equavalent to realize the rule:
    forall x'. (x' not free in T, e, D) -> (T[x'/x],x = e[x'/x] => E, D[x'/x]) -> (T => [x := e] E, D)
***)

(* To be simple, we firstly define a sequent as a triple (\Gamma, formula, \Delta), where \Gamma and \Delta are the context of 
the formula that we are going to transform. *)

(**DEL
Inductive tstSeq : Gamma -> place -> place -> Delta -> Type :=
  tst1 : forall (T : Gamma) (D : Delta) (e : e_exp) (phi : CDL_exp) (x : string), 
          (
          forall (z : string), 
          (tstSeq ((x =' (e_2_E e) [z subs-E x]) :: (T [ z subs-l x ])) 
                   empty 
                  (exp phi) 
                  (D [ z subs-l x ]) )
        ) -> 
    (tstSeq T empty (exp ([ @ {x :=' e} ] phi)) D)
where "{ T , p1 ==> p2 , D }" := (tstSeq T p1 p2 D)
.

(* Theorem thm1 : (x =' 1) :: nil , empty ==> [ @ {x :=' x '+ 1}] x >' 2 , nil .*)

Theorem thm1 : tstSeq ((y =' 1) :: nil) empty (exp ([ @ {y :=' y '+ z}] y >' 2)) nil .
Proof. 
apply tst1.
intros. simpl. 
Abort.

Theorem thm2 : { ((y =' 1):: nil) , empty ==> exp ([ @ {y :=' y '+ z}] y >' 2) , nil }.
DEL**)

Inductive tstSeq2 : Gamma -> place -> place -> Delta -> Type :=
  tst2 : forall (T : Gamma) (D : Delta) (e : e_exp) (phi : CDL_exp) (x : string) (A : Evt), 
          (
          forall (z : string), 
          (forall (n : string), (In n ((cdl_FV_l T nil) ++ (cdl_FV_l D nil) ++ (e_exp_FV e nil) ++ (Evt_FV A nil) ++ (cdl_FV phi nil)))
                                  -> (n <> z)
          ) ->
          (tstSeq2 ((x =' (e_2_E e) [z subs-E x]) :: (T [ z subs-l x ])) 
                   empty 
                  (exp ([ @ A ] phi)) 
                  (D [ z subs-l x ]) )
        ) -> 
    (tstSeq2 T empty (exp ([ @ ((x :=' e) :: A) ] phi)) D) 
  |
  tst3 : forall (T : Gamma) (D : Delta) (phi : CDL_exp), 
          (
          tstSeq2 T 
                   empty 
                  (exp phi) 
                  D
        ) -> 
    (tstSeq2 T empty (exp ([ @ idle ] phi)) D)
where "{ T , p1 ==> p2 , D }" := (tstSeq2 T p1 p2 D)
.

Locate "<>".

Compute x = y.

Theorem thm2 : { ((y =' 1):: nil) , empty ==> exp ([ @ {y :=' y '+ z | y :=' y '+ 1}] y >' 2) , nil }.
Proof. 
apply tst2.
intros. simpl.
apply tst2.
intros. simpl.
apply tst3. simpl.
simpl H.
Abort.

(*DEL
Inductive E_expt :=
  tvarC : Type -> E_expt |
  tCntClkC : Type -> E_expt | 
  tStClkC : Type -> E_expt |
  tnumC : nat -> E_expt |
  tplusC : E_expt -> E_expt -> E_expt |
  (* unecessary expression *)
  tmulC : E_expt -> E_expt -> E_expt |
  tminusC : E_expt -> E_expt -> E_expt |
  tdivC : E_expt -> E_expt -> E_expt
.
Print E_expt.

Variable X : Type. 
Variable Y : Type. 

Fixpoint E_expt_subs (e : E_expt) (x' : Type) (x : Type) : E_expt := 
  match e with
  | tvarC x => tvarC x
  | tCntClkC c => tCntClkC c (* do not consider replacing a clock-related variable *)
  | tStClkC c => tStClkC c
  | tnumC n => tnumC n
  | tplusC e1 e2 => tplusC (E_expt_subs e1 x' x) (E_expt_subs e2 x' x)
  | tmulC e1 e2 => tmulC (E_expt_subs e1 x' x) (E_expt_subs e2 x' x)
  | tminusC e1 e2 => tminusC (E_expt_subs e1 x' x) (E_expt_subs e2 x' x)
  | tdivC e1 e2 => tdivC (E_expt_subs e1 x' x) (E_expt_subs e2 x' x)
  end
.
Print E_expt_subs.
***DEL*)

(*** exploring how the `apply' works and how the pattern matching works in Coq ***)
Inductive ev : nat -> Prop :=
  ev_0 : ev 0 |
  ev_SS : forall (n : nat), ev n -> ev ( S (S n))
.

Theorem ev_4 : ev 4.
Proof. 
apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Inductive month : Set :=
  Jan | Feb | Mar
.
 

(*&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&  end of test &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&*)
Inductive validSeq : sequent -> Type :=
  tst : forall (T : Gamma) (p : CDL_exp) (D : Delta), (CheckPureFOL p) -> validSeq ( T ==> p , D ).

