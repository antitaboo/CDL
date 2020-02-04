Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.

(* Syntax of Clock-based Dynamic Logic *)

(* Syntax of SEP_exp (Synchonous Event Program) *)


(* ========================= Syntax of SEP_exp ========================*)

(* =============== Syntax of Expressions ===================*)

(* Arith Expression `e'*)
Inductive e_exp := 
  enumC : nat -> e_exp | 
  evarC : string -> e_exp | 
  eplusC : e_exp -> e_exp -> e_exp |
  (*non-necessary expression*)
  eminusC : e_exp -> e_exp -> e_exp |
  emulLC : nat -> e_exp -> e_exp |
  emulRC : e_exp -> nat -> e_exp |
  edivC : e_exp -> nat -> e_exp
.
Print e_exp.

Notation "e1 '+ e2" := (eplusC e1 e2) (at level 31, right associativity).
Locate "'+".
Notation "e1 '- e2" := (eminusC e1 e2) (at level 31, right associativity).

Notation "n '*l' e" := (emulLC n e) (at level 21, right associativity).
Notation "e '*r' n" := (emulRC e n) (at level 21, right associativity).
Locate "*".
Check 4 *l (enumC 5 '+ enumC 6).

Notation "e1 '/ n" := (edivC e1 n) (at level 21, right associativity).
Check (enumC 4)'/4.

Coercion enumC : nat >-> e_exp.
Coercion evarC : string >-> e_exp.
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition k : string := "k".

Check 4 *l (5 '+ 2).
Check (5 '+ 4) *r 8.
Check x '- 3.
Check 5 '+ 4 *r 5.



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


(* Evaluation *)
(***
  Definging the evaluation for expressions is for checking the validation of FOL formulas after 
  transformation. 
***)

Fixpoint eval_e_exp (e : e_exp) (st : string -> nat) : nat :=  
(* st maps each var name to a value --- it is a state *)
  match e with
  | enumC n => n
  | evarC s => st s
  | eplusC e1 e2 => (eval_e_exp e1 st) + (eval_e_exp e2 st)
  | eminusC e1 e2 => (eval_e_exp e1 st) - (eval_e_exp e2 st)
  | emulLC n e' => n * (eval_e_exp e' st)
  | emulRC e' n => (eval_e_exp e' st) * n
  | edivC e' n => (eval_e_exp e' st) / n
  end.


Fixpoint eval_P_exp (P : P_exp) (st : string -> nat) : Prop :=
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
  sigC : string -> e_exp -> EvtElement | (* Signal *)
  assC : string -> e_exp -> EvtElement  (* Assignment *)
.
Check EvtElement. 

Notation "s ! e" := (sigC s e) (at level 45).
Notation "x ':= e" := (assC x e) (at level 45).

(* currently we do not make distinguish between variable and clock names, both are strings*)
Definition c : string := "c".
Definition d : string := "d".
Definition c1 : string := "c1".
Definition c2 : string := "c2".
Definition c3 : string := "c3".
Definition c4 : string := "c4".

Check x ':= 4.
Check c ! (x '+ 4).

Definition Evt := list EvtElement.

Check Evt.
Check (x ':= 4) :: (c!(x '+ 4)) :: nil.

Definition idle : Evt := nil.
Check idle.

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
Notation "{ a1 .. an }" := (evtC a1 :: .. :: an :: nil).
Notation "P ? a" := (tstC P a) (at level 47).
Notation "P1 ; P2" := (seqC P1 P2) (at level 48).
Notation "P1 'U' P2" := (choC P1 P2) (at level 49).
Notation "P **" := (loopC P) (at level 46).

Locate "**".
Check x ':= 4 :: nil.
Check evtC (x ':= 4 :: nil).

(* ========================================= Syntax of CDL Formula ===============================================*)

(* ================== CCSL ======================== *)
(* clock relation *)
(***
  Currently, we model clocks as `strings', becuase now we don't need to give its semantics. 
  It won't work anymore if we consider its semantics later.
***)

Inductive CRel := 
  crSubClC : string -> string -> CRel |
  crExclC : string -> string -> CRel |
  crPrecC : string -> string -> CRel |
  crCausC : string -> string -> CRel
.
Check CRel.


(* ================== CDL Formula ======================== *)
(* Clock relation in formula *)
Inductive rel := 
  rRelC : CRel -> rel |
  rConjC : list CRel -> rel
.
Print rel.

(* Arith Expression `E' *)
(*DEL
(* define a map that maps each clock/signal to a variable that records the number it has ticked in history. *)
Definition CntClk := string -> string. 

(* define a map that maps each clock/signal to a variable that records the current state of this clock. *)
Definition StClk := string -> string. 
DEL*)

Inductive E_exp :=
  EvarC : string -> E_exp |
  ECntClkC : string -> E_exp | (* define a map that maps each clock/signal to a variable that records the number it has ticked in history. *)
  EStClkC : string -> E_exp | (* define a map that maps each clock/signal to a variable that records the current state of this clock. *)
  EnumC : nat -> E_exp |
  EplusC : E_exp -> E_exp -> E_exp |
  EmulC : E_exp -> E_exp -> E_exp |
  (* unecessary expression *)
  EminusC : E_exp -> E_exp -> E_exp
.
Print E_exp. 


(* CDL Formula *)
Inductive CDL_exp := 
  cdl_trueC : CDL_exp |
  cdl_ltC : E_exp -> E_exp -> CDL_exp |
  cdl_box1C : SEP_exp -> rel -> CDL_exp |
  cdl_box2C : SEP_exp -> CDL_exp -> CDL_exp |
  cdl_negC : CDL_exp -> CDL_exp |
  cdl_andC : CDL_exp -> CDL_exp -> CDL_exp |
  cdl_forallC : string -> CDL_exp -> CDL_exp |
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





(* ====================================================== Definition of Sequent =========================== *)
(* To be simple, we firstly define a sequent as a triple (\Gamma, formula, \Delta), where \Gamma and \Delta are the context of 
the formula that we are going to transform. *)

Definition Gamma := list CDL_exp.
Definition Delta := list CDL_exp.

Definition SequentL := Gamma -> CDL_exp -> Delta. 
Definition SequentR := Gamma -> CDL_exp -> Delta.

(* we arrange a place special for the dynamic formula we want to verify in the sequent, other formulas in Gamma
and Delta are pure FOL formulas. 

We define two types of sequent: sequentL and sequentR, where L and R indicate the verifiying formula is on the left
or right side of the sequent. 
*)




(* ===================================================== CDL Calculus ======================================*)

