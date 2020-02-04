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
  emulC : e_exp -> e_exp -> e_exp |
  edivC : e_exp -> nat -> e_exp
.
Print e_exp.

Notation "e1 '+ e2" := (eplusC e1 e2) (at level 31, right associativity).
Locate "'+".
Notation "e1 '- e2" := (eminusC e1 e2) (at level 31, right associativity).

Notation "e1 '* e2" := (emulC e1 e2) (at level 21, right associativity).

(*** Open Scope e_exp_scope. ***)

Locate "*".
Check (enumC 4) '* (enumC 5 '+ enumC 6).

Notation "e1 '/ n" := (edivC e1 n) (at level 21, right associativity).
Check (enumC 4)'/4.

Coercion enumC : nat >-> e_exp.
Coercion evarC : string >-> e_exp.
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition k : string := "k".

Check 4 '* (5 '+ 2).
Check (5 '+ 4) '* 8.
Check x '- 3.
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


(* Evaluation *)
Definition state := string -> nat.

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
  | edivC e' n => (eval_e_exp e' st) / n
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
  sigC : string -> e_exp -> EvtElement | (* Signal *)
  assC : string -> e_exp -> EvtElement  (* Assignment *)
.
Check EvtElement. 

Notation "s ! e" := (sigC s e) (at level 45).
Notation "x :=' e" := (assC x e) (at level 45).

(* currently we do not make distinguish between variable and clock names, both are strings*)
Definition c : string := "c".
Definition d : string := "d".
Definition c1 : string := "c1".
Definition c2 : string := "c2".
Definition c3 : string := "c3".
Definition c4 : string := "c4".

Check x :=' 4.
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
  crSubClC : string -> string -> CRel |
  crExclC : string -> string -> CRel |
  crPrecC : string -> string -> CRel |
  crCausC : string -> string -> CRel
.
Check CRel.

Notation "c1 'sub' c2" := (crSubClC c1 c2) (at level 52).
Notation "c1 # c2" := (crExclC c1 c2) (at level 52).
Notation "c1 << c2" := (crPrecC c1 c2) (at level 52).
Notation "c1 <<= c2" := (crCausC c1 c2) (at level 52).

Check c1 << c2.
Check c1 # c2.
Check c1 sub c2.

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
  EvarC : string -> E_exp |
  ECntClkC : string -> E_exp | (* define a map that maps each clock/signal to a variable that records the number it has ticked in history. *)
  EStClkC : string -> E_exp | (* define a map that maps each clock/signal to a variable that records the current state of this clock. *)
  EnumC : nat -> E_exp |
  EplusC : E_exp -> E_exp -> E_exp |
  (* unecessary expression *)
  EmulC : E_exp -> E_exp -> E_exp |
  EminusC : E_exp -> E_exp -> E_exp |
  EdivC : E_exp -> nat -> E_exp
.
Print E_exp. 

Coercion EvarC : string >-> E_exp.
Notation "n( c )" := (ECntClkC c) (at level 52). (* the only DIFFERENCE between e_exp and E_exp *)
Notation "s( c )" := (EStClkC c) (at level 52).
Coercion EnumC : nat >-> E_exp.
Notation "e1 +' e2" := (EplusC e1 e2) (at level 55, right associativity).
Notation "e1 *' e2" := (EmulC e1 e2) (at level 53, right associativity).
Notation "e1 -' e2" := (EminusC e1 e2) (at level 55, right associativity).
Notation "e /' n" := (EdivC e n) (at level 53, right associativity).

Check 5 +' 3.
Check 5 '+ 3.
Check 5 *' (3 +' 5).
Check n(c) *' 4.





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

Notation "'tt''" := cdl_trueC (at level 65).
Notation "e1 <' e2" := (cdl_ltC e1 e2) (at level 61).
Notation "[ p ]' r" := (cdl_box1C p r) (at level 63).
Notation "[ p ] e" := (cdl_box2C p e) (at level 63).
Notation "~' e" := (cdl_negC e) (at level 67).
Notation "e1 /\' e2" := (cdl_andC e1 e2) (at level 69, right associativity).
Notation "'all' x , e" := (cdl_forallC x e) (at level 68).
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
Check ([skip]' c1 << c2) /\' 2 >' 5 /\' tt'.
Check [@ {x :=' 4 | c1 ! 5} ; (x '> 0) ? {c2!4} ; @ idle; skip] n(c) >' 0.
Check [(@ {x :=' 4 | c1 ! 5} ; (x '> 0) ? {c2!4} ; @ idle; skip)**]' c1<<c2.
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

Notation "[ b ]" := (bBoolC b) (at level 74).
Notation "_|_" := bUndefC (at level 74).


(* evaluate a pure FOL formula in CDL formula *)




(*************************** Rules for FOL **********************************)
(* To be simple, we firstly define a sequent as a triple (\Gamma, formula, \Delta), where \Gamma and \Delta are the context of 
the formula that we are going to transform. *)

Definition Gamma := list CDL_exp.
Definition Delta := list CDL_exp.

(***DEL Definition SequentL : Gamma -> CDL_exp -> Delta -> Prop.*)


(* we arrange a place special for the dynamic formula we want to verify in the sequent, other formulas in Gamma
and Delta are pure FOL formulas. 

We define two types of sequent: sequentL and sequentR, where L and R indicate the verifiying formula is on the left
or right side of the sequent. 
*)

Reserved Notation "T , p ==> D" (at level 75).
Reserved Notation "T ==> p , D" (at level 75).

Locate "==>".

Inductive validSeq : sequent -> Type :=
  tst : forall (T : Gamma) (p : CDL_exp) (D : Delta), (CheckPureFOL p) -> validSeq ( T ==> p , D ).

