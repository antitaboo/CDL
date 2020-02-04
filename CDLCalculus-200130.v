Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Logic.

Import ListNotations.

Require Import Omega. (* for omega tactic *)

(* Syntax of Clock-based Dynamic Logic *)

(* Syntax of SEP_exp (Synchonous Event Program) *)


(* ========================= Syntax of SEP_exp ========================*)

(* =============== Syntax of Expressions ===================*)

(* Arith Expression `e'*)
(* variable name*)
Inductive Var := var : nat -> Var.
(* in this version, I try to understand variables as identifications numbered by natural numbers, 
which we believe is more convenient than considering them as strings in practical derivations*)

(* expression e *)
Inductive e_exp := 
  enumC : nat -> e_exp | 
  evarC : Var -> e_exp | 
  eplusC : e_exp -> e_exp -> e_exp |
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






(* condition P*)
Inductive P_exp := 
  PtrueC : P_exp |
  PlteC : e_exp -> e_exp -> P_exp |
  PnegC : P_exp -> P_exp |
  PandC : P_exp -> P_exp -> P_exp |
  (*unnecesarry expression*)
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


(* event element*)
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

(* event *)
Definition Evt := list EvtElement.

Check Evt.
Check (x :=' 4) :: (c!(x '+ 4)) :: nil.

(* ========================= Syntax of program ========================*)
(* syntax of SEP *)
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
Notation "P   **" := (loopC P) (at level 47, left associativity).

Locate "**".
Check x :=' 4 :: nil.
Check evtC (x :=' 4 :: nil).
Check { x :=' 4 }.
Check { x :=' 4 | c1 ! 5}.
Check @ { x :=' 4 | c1 ! 5 }.
Check @ {x :=' 4}.
Check idle.
Check x '> 0 ? {c!4}.

(* ========================================= Syntax of CDL Formula ===============================================*)

(* ================== CCSL ======================== *)
(* clock relation *)
(***
  Currently, we model clocks as `strings', becuase now we don't need to give its semantics. 
  It won't work anymore if we consider its semantics later.
***)

(* CCSL clock relation *)
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
(* clock-relation term in CDL formulae *)
Inductive rel := 
  rRelC : CRel -> rel |
  rConjC : list CRel -> rel
.
Print rel.

Coercion rRelC : CRel >-> rel.
Check c1 << c2.

Notation "/\{ c1 , .. , cn }" := (rConjC (cons c1 .. (cons cn nil) ..)). (*(at level 46). a bit higher than notation {a1 | ... | an} *)
Check /\{ c1 << c2 , c2 sub c3 , c1 <<= c3 }.
Check { x :=' 4 | c1 ! 5}.

(* Arith Expression `E' *)
(*DEL
(* define a map that maps each clock/signal to a variable that records the number it has ticked in history. *)
Definition CntClk := string -> string. 

(* define a map that maps each clock/signal to a variable that records the current state of this clock. *)
Definition StClk := string -> string. 
DEL*)

(* expression E *)
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

(* define two functions at the interpretation level for ECntClkC and EStClkC. *)
(* Variable fn : nat -> nat.
   Variable gn : nat -> nat. *)

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



(* syntax of CDL formula *)
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
  cdl_impC : CDL_exp -> CDL_exp -> CDL_exp |
  cdl_existsC : Var -> CDL_exp -> CDL_exp
.

Notation "'tt''" := cdl_trueC (at level 9). (* previous setting is 65, but I don't why it does not work sometimes *)
Notation "e1 <' e2" := (cdl_ltC e1 e2) (at level 61).
Notation "[[ p ]]' r" := (cdl_box1C p r) (at level 63).
Notation "[[ p ]] e" := (cdl_box2C p e) (at level 63).
Notation "~' e" := (cdl_negC e) (at level 67).
Notation "e1 /\' e2" := (cdl_andC e1 e2) (at level 69, right associativity).
Notation "'all' x , e" := (cdl_forallC x e) (at level 68, x at level 67).
(* unnecessary expressions *)
Notation "'ff''" := cdl_falseC (at level 9).
Notation "e1 <=' e2" := (cdl_lteC e1 e2) (at level 61).
Notation "e1 >' e2" := (cdl_gtC e1 e2) (at level 61).
Notation "e1 >=' e2" := (cdl_gteC e1 e2) (at level 61).
Notation "e1 =' e2" := (cdl_eqC e1 e2) (at level 61).
Notation "<< p >>' r" := (cdl_dia1C p r) (at level 63, p at level 51, r at level 51). 
(* must be higher than the precedence of <<, which is 52 *)
Notation "<< p >> e" := (cdl_dia2C p e) (at level 63, p at level 51, e at level 51).
Notation "e1 \/' e2" := (cdl_orC e1 e2) (at level 71, right associativity).
Notation "e1 ->' e2" := (cdl_impC e1 e2) (at level 72, right associativity).
Notation "'ext' x , e" := (cdl_existsC x e) (at level 68, x at level 67).


Check tt'.
Check ff'.
Check (5 -' 3) <' 2.
Check ([[ skip ]]' c1 << c2) /\' 2 >' 5 /\' tt'.
Check [[ @ {x :=' 4 | c1 ! 5} ; (x '> 0) ? {c2!4} ; @ idle; skip ]] n(c) >' 0.
Check [[ (@ {x :=' 4 | c1 ! 5} ; (x '> 0) ? {c2!4} ; @ idle; skip)** ]]' c1<<c2.
Check [[ skip ]]' c1 << c2 .
Check all x , 4 =' 5.
Check ext x , 4 =' 5.





(* ===================================================== CDL Calculus ======================================*)


(*************************** Some   Auxiliary Functions ***************************)
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
  | cdl_existsC x e' => (CheckPureFOL e')
  end.

(* build a type for distinguishing pure FOL (i.e. Prop) or non-pure FOL *)
Inductive FOLF := 
  pureC : Prop -> FOLF |
  noPureC : FOLF
.

(* transform an E_exp to a FOL exp under a given state st. *)
(* here the functionality of st is to link the concept of `variable' in CDL we define to 
the `nat' domain in Coq *)

Fixpoint Eexp_2_exp (e : E_exp) (st : state) (fn : state) (gn : state) : nat :=
  match e with
  | EvarC v => st v
  | ECntClkC c => fn c
  | EStClkC c => gn c
  | EnumC n => n
  | EplusC e1 e2 => (Eexp_2_exp e1 st fn gn) + (Eexp_2_exp e2 st fn gn)
  | EmulC e1 e2 => (Eexp_2_exp e1 st fn gn) * (Eexp_2_exp e2 st fn gn)
  | EminusC e1 e2 => (Eexp_2_exp e1 st fn gn) - (Eexp_2_exp e2 st fn gn)
  | EdivC e1 e2 => (Eexp_2_exp e1 st fn gn) / (Eexp_2_exp e2 st fn gn)
  end
.

(* transform a CDL exp to a FOLF formula *)
Fixpoint CDLexp_2_FOLF (e : CDL_exp) (st : state) (fn : state) (gn : state) : FOLF :=
  match e with
  | cdl_trueC => pureC True
  | cdl_ltC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) < (Eexp_2_exp e2 st fn gn))
  | cdl_box1C p r => noPureC (*once met dynamic operators, it is not a pure FOL formula *)
  | cdl_box2C p e' => noPureC
  | cdl_negC e' => match (CDLexp_2_FOLF e' st fn gn) with 
                    | noPureC => noPureC
                    | pureC f => pureC (~ f) 
                   end
  | cdl_andC e1 e2 => match (CDLexp_2_FOLF e1 st fn gn), (CDLexp_2_FOLF e2 st fn gn) with 
                        | noPureC , _ => noPureC
                        | _ , noPureC => noPureC
                        | (pureC f1) , (pureC f2) => pureC (f1 /\ f2)
                      end
  | cdl_forallC x e' => match (CDLexp_2_FOLF e' st fn gn) with
                          | noPureC => noPureC
                          | pureC f => pureC (forall (x : nat), f)
                        end
  | cdl_falseC => pureC False
  | cdl_lteC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) <= (Eexp_2_exp e2 st fn gn)) 
  | cdl_gtC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) > (Eexp_2_exp e2 st fn gn)) 
  | cdl_gteC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) >= (Eexp_2_exp e2 st fn gn)) 
  | cdl_eqC e1 e2 => pureC ((Eexp_2_exp e1 st fn gn) = (Eexp_2_exp e2 st fn gn)) 
  | cdl_dia1C p r => noPureC (*once met dynamic operators, it is not a pure FOL formula *)
  | cdl_dia2C p e' => noPureC
  | cdl_orC e1 e2 => match (CDLexp_2_FOLF e1 st fn gn), (CDLexp_2_FOLF e2 st fn gn) with 
                        | noPureC , _ => noPureC
                        | _ , noPureC => noPureC
                        | (pureC f1) , (pureC f2) => pureC (f1 \/ f2)
                     end
  | cdl_impC e1 e2 => match (CDLexp_2_FOLF e1 st fn gn), (CDLexp_2_FOLF e2 st fn gn) with 
                        | noPureC , _ => noPureC
                        | _ , noPureC => noPureC
                        | (pureC f1) , (pureC f2) => pureC (f1 -> f2)
                      end
  | cdl_existsC x e' => match (CDLexp_2_FOLF e' st fn gn) with
                          | noPureC => noPureC
                          | pureC f => pureC (exists (x : nat), f)
                        end
  end.


Variable st0 : state. 
Variable fn0 : state.
Variable gn0 : state.
Compute (CDLexp_2_FOLF tt' st0 fn0 gn0).
Compute (CDLexp_2_FOLF (tt' /\' x >=' 5) st0 fn0 gn0).
Compute (CDLexp_2_FOLF (tt' /\' (x >=' 5 ->' [[ skip ]] x >' 5 )) st0 fn0 gn0).
Compute (CDLexp_2_FOLF (tt' /\' (x >=' 5 ->' n(c) >' 5 )) st0 fn0 gn0).


(* transform a CDL_exp to Prop formula, if CDL_exp is not pure, simply return False, otherwise, 
return the Prop formula corresponding to it. *)

Definition CDLexp_2_Prop (e : CDL_exp) (st : state) (fn : state) (gn : state) : Prop :=
  match (CDLexp_2_FOLF e st fn gn) with
    | noPureC => False
    | pureC f => f
  end.

Compute CDLexp_2_Prop (tt' /\' (x >=' 5 ->' [[ skip ]] x >' 5 )) st0 fn0 gn0.
Compute CDLexp_2_Prop (tt' /\' (x >=' 5 ->' n(c) >' 5 )) st0 fn0 gn0.


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


(* during the derivation we need to translate expression e to expression E, or expression P_exp 
to expression CDL_exp, in the semantics of dynamic logic, their 
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

Fixpoint Pexp_2_CDLexp (P : P_exp) : CDL_exp :=
  match P with
  | PtrueC => cdl_trueC
  | PlteC e1 e2 => cdl_lteC (e_2_E e1) (e_2_E e2)
  | PnegC P' => cdl_negC (Pexp_2_CDLexp P')
  | PandC P1 P2 => cdl_andC (Pexp_2_CDLexp P1) (Pexp_2_CDLexp P2)
  | PfalseC => cdl_falseC
  | PltC e1 e2 => cdl_ltC (e_2_E e1) (e_2_E e2)
  | PgtC e1 e2 => cdl_gtC (e_2_E e1) (e_2_E e2)
  | PgteC e1 e2 => cdl_gteC (e_2_E e1) (e_2_E e2)
  | PeqC e1 e2 => cdl_eqC (e_2_E e1) (e_2_E e2)
  | PorC P1 P2 => cdl_orC (Pexp_2_CDLexp P1) (Pexp_2_CDLexp P2)
  | PimpC P1 P2 => cdl_impC (Pexp_2_CDLexp P1) (Pexp_2_CDLexp P2)
  end.

(* compare the id of two variables *)
Definition eqv (x : Var) (y: Var) : bool :=
  match x, y with
  | var n, var m => if n =? m then true else false
  end.

(* romove an element from a Var list *)
Fixpoint rmv (V : list Var) (x : Var) : list Var :=
  match V with
  | nil => nil
  | e :: V' => if eqv e x then rmv V' x else e :: (rmv V' x)
  end
.

(* add an element at the nail of a exp list *)
Fixpoint addNail (l : list CDL_exp) (e : CDL_exp) : list CDL_exp :=
  match l with 
    | nil => e :: nil
    | a :: l' => a :: (addNail l' e)
  end.

(* -------------------------------computation of variables in cdl formula----------------------------------------*)

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


Fixpoint E_exp_V (e : E_exp) (V : list Var) : list Var := (*bv : list of computed variables at current time *)
  match e with
  | EvarC v => if (NotIn_bool v V) then v :: nil else nil
  | ECntClkC c => if (NotIn_bool c V) then c :: nil else nil
  | EStClkC c => if (NotIn_bool c V) then c :: nil else nil
  | EnumC n => nil
  | EplusC e1 e2 => (E_exp_V e1 V) ++ (E_exp_V e2 (V ++ (E_exp_V e1 V)))
  | EmulC e1 e2 => (E_exp_V e1 V) ++ (E_exp_V e2 (V ++ (E_exp_V e1 V)))
  | EminusC e1 e2 => (E_exp_V e1 V) ++ (E_exp_V e2 (V ++ (E_exp_V e1 V)))
  | EdivC e1 e2 => (E_exp_V e1 V) ++ (E_exp_V e2 (V ++ (E_exp_V e1 V)))
  end
.

Compute E_exp_V (x +' 3 *' n(c)) nil.
Compute E_exp_V (x +' 3 *' z) nil.
Compute E_exp_V (x +' 3 *' x +' y) nil.

Fixpoint e_exp_V (e : e_exp) (V : list Var): list Var :=
  match e with 
  | enumC n => nil
  | evarC s => if (NotIn_bool s V)  then s :: nil else nil
  | eplusC e1 e2 => (e_exp_V e1 V) ++ (e_exp_V e2 (V ++ (e_exp_V e1 V)))
  | eminusC e1 e2 => (e_exp_V e1 V) ++ (e_exp_V e2 (V ++ (e_exp_V e1 V)))
  | emulC e1 e2 => (e_exp_V e1 V) ++ (e_exp_V e2 (V ++ (e_exp_V e1 V)))
  | edivC e1 e2 => (e_exp_V e1 V) ++ (e_exp_V e2 (V ++ (e_exp_V e1 V)))
  end
.

Compute e_exp_V (x '+ 3 '* 5) nil.
Compute e_exp_V (x '+ 3 '* z) nil.
Compute e_exp_V (x '+ 3 '/ z '+ y '* z) nil.

Fixpoint P_exp_V (P : P_exp) (V : list Var) : list Var :=
  match P with
  | PtrueC => nil
  | PlteC e1 e2 => let l := (e_exp_V e1 V) in (l ++ (e_exp_V e2 (V ++ l)))
  | PnegC P' => P_exp_V P' V
  | PandC P1 P2 => let l := (P_exp_V P1 V) in (l ++ (P_exp_V P2 (V ++ l)))
  | PfalseC => nil
  | PltC e1 e2 => let l := (e_exp_V e1 V) in (l ++ (e_exp_V e2 (V ++ l)))
  | PgtC e1 e2 => let l := (e_exp_V e1 V) in (l ++ (e_exp_V e2 (V ++ l)))
  | PgteC e1 e2 => let l := (e_exp_V e1 V) in (l ++ (e_exp_V e2 (V ++ l)))
  | PeqC e1 e2 => let l := (e_exp_V e1 V) in (l ++ (e_exp_V e2 (V ++ l)))
  | PorC P1 P2 => let l := (P_exp_V P1 V) in (l ++ (P_exp_V P2 (V ++ l)))
  | PimpC P1 P2 => let l := (P_exp_V P1 V) in (l ++ (P_exp_V P2 (V ++ l)))
  end
.


Compute P_exp_V ('tt '/\ (3 '= 5 '* x)) nil.
Compute P_exp_V ('tt '/\ (3 '= 5 '* x)) (x :: nil).
Compute P_exp_V (y '<= 5 '/\ (3 '= 5 '* x)) (z :: nil).
Compute P_exp_V (y '<= 5 '/\ (3 '= 5 '* x) '\/ x '< 1) nil.

Fixpoint EvtE_V (e : EvtElement) (V : list Var): list Var :=
  match e with 
  | sigC s e' => if NotIn_bool s V then s :: (e_exp_V e' (s :: V)) else e_exp_V e' V
  | assC s e' => if NotIn_bool s V then s :: (e_exp_V e' (s :: V)) else e_exp_V e' V
  end
.

Fixpoint Evt_V (evt : Evt) (V : list Var) : list Var :=
  match evt with 
  | nil => nil
  | e :: evt' => let l := (EvtE_V e V) in (l ++ (Evt_V evt' (V ++ l)))
  end
.

Compute Evt_V ({ x:='y '+ 2 | c ! (z '* 38)}) nil.
Compute Evt_V ({ x:='y '+ 2 | c ! (z '* 38) | c ! x}) nil.

Fixpoint SEP_exp_V (e : SEP_exp) (V : list Var) : list Var :=
  match e with 
  | skip => nil
  | evtC evt => (Evt_V evt V)
  | tstC P evt => let l := (P_exp_V P V) in (l ++ (Evt_V evt (V ++ l)))
  | seqC e1 e2 => let l := (SEP_exp_V e1 V) in (l ++ (SEP_exp_V e2 (V ++ l)))
  | choC e1 e2 => let l := (SEP_exp_V e1 V) in (l ++ (SEP_exp_V e2 (V ++ l)))
  | loopC e' => (SEP_exp_V e' V)
  end
.

Check x '> 2 ? { y :=' y '- z}.
Compute SEP_exp_V ((@ { x :=' 5}; x '> 2 ? { y :=' y '- z} U skip) **) nil.

Definition CRel_V (R : CRel) (V : list Var) : list Var :=
  match R with
  | crSubClC c1 c2 => if NotIn_bool c1 V then 
                         c1 :: (if NotIn_bool c2 (c1 :: V) then 
                                   c2 :: nil else
                                      nil
                               ) else
                         if NotIn_bool c2 V then 
                              c2 :: nil else
                                nil
  | crExclC c1 c2 => if NotIn_bool c1 V then 
                         c1 :: (if NotIn_bool c2 (c1 :: V) then 
                                   c2 :: nil else
                                      nil
                               ) else
                         if NotIn_bool c2 V then 
                              c2 :: nil else
                                nil
  | crPrecC c1 c2 => if NotIn_bool c1 V then 
                         c1 :: (if NotIn_bool c2 (c1 :: V) then 
                                   c2 :: nil else
                                      nil
                               ) else
                         if NotIn_bool c2 V then 
                              c2 :: nil else
                                nil
  | crCausC c1 c2 => if NotIn_bool c1 V then 
                         c1 :: (if NotIn_bool c2 (c1 :: V) then 
                                   c2 :: nil else
                                      nil
                               ) else
                         if NotIn_bool c2 V then 
                              c2 :: nil else
                                nil
  end.

Compute CRel_V (c1 << c2) nil.
Compute CRel_V (c1 << c1) nil.
Compute CRel_V (c1 << c2) (c1 :: nil).
Compute CRel_V (c1 << c2) (c1 :: c2 :: nil).

Fixpoint CRel_V_l (lr : list CRel) (V : list Var) : list Var :=
  match lr with
  | nil => nil
  | r :: lr' => let l := (CRel_V r V) in (l ++ CRel_V_l lr' (V ++ l))
  end.

Compute CRel_V_l ((c1 << c2) :: (c1 sub c3) :: (c3 # c4) :: nil) nil.

Definition rel_V (r : rel) (V : list Var) : list Var :=
  match r with
  | rRelC R => CRel_V R V
  | rConjC lr => CRel_V_l lr V
  end.

Compute rel_V (/\{ c1 << c2 , c2 sub c3 , c1 <<= c3}) nil.
Compute rel_V (c1 << c2) nil. 

Fixpoint cdl_V (e : CDL_exp) (V : list Var) : list Var := (*V : list of computed variables at current time *)
  match e with
  | cdl_trueC => nil
  | cdl_ltC e1 e2 => let l := (E_exp_V e1 V) in (l ++ (E_exp_V e2 (V ++ l)))
  | cdl_box1C p r => let l := (SEP_exp_V p V) in (l ++ (rel_V r (V ++ l)))
  | cdl_box2C p e' => let l := (SEP_exp_V p V) in (l ++ (cdl_V e' (V ++ l)))
  | cdl_negC e' => cdl_V e' V
  | cdl_andC e1 e2 => let l := (cdl_V e1 V) in (l ++ (cdl_V e2 (V ++ l)))
  | cdl_forallC x1 e' => if NotIn_bool x1 V then x1 :: (cdl_V e' (x1 :: V)) else cdl_V e' V
  | cdl_falseC => nil
  | cdl_lteC e1 e2 => let l := (E_exp_V e1 V) in (l ++ (E_exp_V e2 (V ++ l)))
  | cdl_gtC e1 e2 => let l := (E_exp_V e1 V) in (l ++ (E_exp_V e2 (V ++ l)))
  | cdl_gteC e1 e2 => let l := (E_exp_V e1 V) in (l ++ (E_exp_V e2 (V ++ l)))
  | cdl_eqC e1 e2 => let l := (E_exp_V e1 V) in (l ++ (E_exp_V e2 (V ++ l)))
  | cdl_dia1C p r => let l := (SEP_exp_V p V) in (l ++ (rel_V r (V ++ l)))
  | cdl_dia2C p e' => let l := (SEP_exp_V p V) in (l ++ (cdl_V e' (V ++ l)))
  | cdl_orC e1 e2 => let l := (cdl_V e1 V) in (l ++ (cdl_V e2 (V ++ l)))
  | cdl_impC e1 e2 => let l := (cdl_V e1 V) in (l ++ (cdl_V e2 (V ++ l)))
  | cdl_existsC x1 e' => if NotIn_bool x1 V then x1 :: (cdl_V e' (x1 :: V)) else cdl_V e' V
  end
.

Check ( all y , y =' 7 ) .
Compute cdl_V ([[ (@ { x :=' 5}; x '> 2 ? { y :=' y '- z} U skip) ]] x >' 0 /\' ( all y , y =' 7 ) ) nil.
Compute cdl_V ([[ (@ { x :=' 5}; x '> 2 ? { y :=' y '- z} U skip) ]] x >' 0 /\' ( all y , y =' 7 ) ) (y :: nil).
Compute cdl_V ([[ (@ { x :=' 5}; x '> 2 ? { y :=' y '- z} U skip) ]] x >' 0 /\' ( ext y , y =' 7 ) ) (y :: nil).
Compute cdl_V ([[ (@ { c1 ! 5 }; x '> 2 ? { y :=' y '- z} U skip) ]] x >' 0 /\' ( ext y , y =' 7 ) ) (y :: nil).

(* for list *)
Fixpoint cdl_V_l (T : list CDL_exp) (V : list Var) : list Var :=
  match T with 
  | nil => nil
  | e :: T' => let l := (cdl_V e V) in (l ++ (cdl_V_l T' (V ++ l)))
  end.



(* compute V for a function *)
(* here we do a trick. We pass to phi a variable with a variable id that we will never use in the context 
(i.e., the var 0), and we add this variable to the bounded variable list bv, so that the final V set of 
phi will definitely not contain var 0. 
Note that var 0 must not be used anywhere, or it would be dangerous since it is possible var 0 
has already existed in the formul phi *)


Definition cdl_V_f (phi : E_exp -> CDL_exp) (V : list Var) : list Var :=
  cdl_V (phi (var 0)) ((var 0) :: V).

(* generate a new variable id *)
Fixpoint MaxId (VSet : list Var) : nat :=
  match VSet with
  | nil => 0 (* when there is no variables in the current environment VSet, just start from the number 0 *)
  | v :: VSet' => let n := MaxId VSet' in (
                      match v with | var m => 
                        if le_lt_dec n m then m else (MaxId VSet') (* le_lt_dec : <= *)
                      end
                      )
  end
.

(* ------------------------------ Compute the set of bounded variables for a formula -------------- *)

Fixpoint EvtE_BV (e : EvtElement) (V : list Var) : list Var := (* V --> the set of computed variables currently *)
  match e with 
  | sigC s e' => if NotIn_bool s V then s :: nil else nil (* no need to compute the BV in e' because it is 
impossible to have any BV in an e_exp. *)
  | assC s e' => if NotIn_bool s V then s :: nil else nil
  end
.

Fixpoint Evt_BV (evt : Evt) (V : list Var) : list Var :=
  match evt with
  | nil => nil
  | e :: evt' => let l := (EvtE_BV e V) in (Evt_BV evt' (V ++ l))
  end.

Fixpoint SEP_exp_BV (p : SEP_exp) (V : list Var) : list Var :=
  match p with 
  | skip => nil
  | evtC evt => Evt_BV evt V 
  | tstC P evt => Evt_BV evt V (* it is impossible for a bounded variable appears in P *)
  | seqC p1 p2 => let l := (SEP_exp_BV p1 V) in (l ++ (SEP_exp_BV p2 (V ++ l)))
  | choC p1 p2 => let l := (SEP_exp_BV p1 V) in (l ++ (SEP_exp_BV p2 (V ++ l)))
  | loopC p' => SEP_exp_BV p' V
  end
.

(* -------------------------------------- generate new variable in the context ----------------------- *)
Compute MaxId (var 1 :: var 3 :: var 5 :: var 6 :: nil).

Definition NewId (VSet : list Var) : nat := (S (MaxId VSet)). 

Compute NewId (var 7 :: var 1 :: var 3 :: var 3 :: var 5 :: var 6 :: nil).
Compute NewId nil.

(* --------------------------------------- hbar function -------------------------------------------- *)
(* hbar Function : translate a relation to a FOL formula*)
Definition hbar_Rel (r : CRel) : CDL_exp :=
  match r with 
  | crSubClC c1 c2 => (s(c1) =' 1 ->' s(c2) =' 1)
  | crExclC c1 c2 => (s(c1) =' 0 \/' s(c2) =' 1)
  | crPrecC c1 c2 => (n(c1) >' n(c2) \/' (n(c1) =' n(c2) ->' s(c1) =' 0))
  | crCausC c1 c2 => (n(c1) >=' n(c2))
  end.

Fixpoint hbar_l_conj (l : list CRel) : CDL_exp :=
  match l with
  | nil => tt'
  | r :: l' => (hbar_Rel r) /\' (hbar_l_conj l')
  end.

Definition hbar (r : rel) : CDL_exp :=
  match r with 
  | rRelC R => hbar_Rel R
  | rConjC l => hbar_l_conj l
  end.

(* --------------------------------- transform E_exp to e_exp -------------------------------*)
(* a structure tht distinguish E_exp and e_exp *)
Inductive e_exp_type :=
  compC : e_exp -> e_exp_type |
  noCompC : e_exp_type
.

Fixpoint E_2_e (E : E_exp)  : e_exp_type :=
  match E with
  | EvarC x => compC (evarC x)
  | ECntClkC c => noCompC (* it does not compat with e_exp *)
  | EStClkC c => noCompC
  | EnumC n => compC (enumC n) 
  | EplusC E1 E2 => match (E_2_e E1) , (E_2_e E2) with 
                  | noCompC , _  => noCompC
                  | _ , noCompC => noCompC
                  | (compC e1) , (compC e2) => compC (eplusC e1 e2)
                  end
  | EmulC E1 E2 => match (E_2_e E1) , (E_2_e E2) with 
                  | noCompC , _  => noCompC
                  | _ , noCompC => noCompC
                  | (compC e1) , (compC e2) => compC (emulC e1 e2)
                  end
  | EminusC E1 E2 => match (E_2_e E1) , (E_2_e E2) with 
                    | noCompC , _  => noCompC
                    | _ , noCompC => noCompC
                    | (compC e1) , (compC e2) => compC (eminusC e1 e2)
                   end
  | EdivC E1 E2 => match (E_2_e E1) , (E_2_e E2) with 
                    | noCompC , _  => noCompC
                    | _ , noCompC => noCompC
                    | (compC e1) , (compC e2) => compC (edivC e1 e2)
                   end
  end.

Compute (E_2_e ((x +' 5) -' (z *' (y +' 1 )))).
Compute (E_2_e ((x +' 5) -' (n(c) *' (y +' 1 )))).

(* ---------------------------------------- subsititution for an E_exp ----------------------------------- *)
(* the substitution defined here dose not garrentee the admissibility. *)
(* this type is used in substitution *)

Inductive VarType := 
  tVarC : Var -> VarType |
  tCntC : Var -> VarType |
  tStC : Var -> VarType
.

(*DEL
Coercion tVarC : Var >-> VarType.
Coercion tCntC : Var >-> VarType.
Coercion tStC : Var >-> VarType.
*)

Notation "& x" := (tVarC x) (at level 52).
Notation "&n( c )" := (tCntC c) (at level 52).
Notation "&s( c )" := (tStC c) (at level 52).

Locate "&".

Fixpoint E_exp_subsE (e : E_exp) (E : E_exp) (u : VarType) : E_exp := 
  match e with
  | EvarC v => match u with 
                | tVarC x => if (eqv v x) then E else EvarC v
                | tCntC c => EvarC v
                | tStC c => EvarC v
               end
  | ECntClkC c => match u with 
                    | tVarC x => ECntClkC c
                    | tCntC c' => if (eqv c' c) then E else ECntClkC c
                    | tStC c' => ECntClkC c
                  end
  | EStClkC c => match u with 
                    | tVarC x => EStClkC c
                    | tCntC c' => EStClkC c
                    | tStC c' => if (eqv c' c) then E else EStClkC c
                  end
  | EnumC n => EnumC n
  | EplusC e1 e2 => EplusC (E_exp_subsE e1 E u) (E_exp_subsE e2 E u)
  | EmulC e1 e2 => EmulC (E_exp_subsE e1 E u) (E_exp_subsE e2 E u)
  | EminusC e1 e2 => EminusC (E_exp_subsE e1 E u) (E_exp_subsE e2 E u)
  | EdivC e1 e2 => EdivC (E_exp_subsE e1 E u) (E_exp_subsE e2 E u)
  end
.

Compute E_exp_subsE (x +' y) (y +' 1) (&x).
Compute E_exp_subsE (x *' z) (y *' 5) (&n(c)).
Compute E_exp_subsE (n(c) *' z) (y *' 5) (&n(c)).

Notation "e [ E 'subs-E' u ]" := (E_exp_subsE e E u) (at level 9).

Fixpoint e_exp_subse (e : e_exp) (exp : e_exp) (u : VarType) : e_exp :=
  match e with
  | enumC n => enumC n
  | evarC s => match u with 
                 | tVarC x => if (eqv s x) then exp else evarC s
                 | tCntC c => evarC s
                 | tStC c => evarC s
               end
  | eplusC e1 e2 => eplusC (e_exp_subse e1 exp u) (e_exp_subse e2 exp u)
  | eminusC e1 e2 => eminusC (e_exp_subse e1 exp u) (e_exp_subse e2 exp u)
  | emulC e1 e2 => emulC (e_exp_subse e1 exp u) (e_exp_subse e2 exp u)
  | edivC e1 e2 => edivC (e_exp_subse e1 exp u) (e_exp_subse e2 exp u)
  end
.

Compute (z '- 5) '* x '+ z.
Compute e_exp_subse ((z '- 5) '* x '+ z) y (&z).
Compute e_exp_subse ((z '- 5) '* x '+ z) (y '- 2) (&z).

Fixpoint P_exp_subse (P : P_exp) (exp : e_exp) (u : VarType) : P_exp :=
  match P with
  | PtrueC => PtrueC 
  | PlteC e1 e2 => PlteC (e_exp_subse e1 exp u) (e_exp_subse e2 exp u)
  | PnegC P' => PnegC (P_exp_subse P' exp u)
  | PandC P1 P2 => PandC (P_exp_subse P1 exp u) (P_exp_subse P2 exp u)
  | PfalseC => PfalseC
  | PltC e1 e2 => PltC (e_exp_subse e1 exp u) (e_exp_subse e2 exp u)
  | PgtC e1 e2 => PgtC (e_exp_subse e1 exp u) (e_exp_subse e2 exp u)
  | PgteC e1 e2 => PgteC (e_exp_subse e1 exp u) (e_exp_subse e2 exp u)
  | PeqC e1 e2 => PeqC (e_exp_subse e1 exp u) (e_exp_subse e2 exp u)
  | PorC P1 P2 => PorC (P_exp_subse P1 exp u) (P_exp_subse P2 exp u)
  | PimpC P1 P2 => PimpC (P_exp_subse P1 exp u) (P_exp_subse P2 exp u)
  end
.

Compute 'tt '/\ '~ (x '< 5).
Compute P_exp_subse ('tt '/\ '~ (x '< 5)) z (&x).
Compute P_exp_subse ('tt '/\ '~ (x '< 5)) (z '* 2) (&x).

Fixpoint EvtE_subse (e : EvtElement) (exp : e_exp) (u : VarType) : EvtElement :=
  match e with 
  | sigC s e' => sigC s (e_exp_subse e' exp u)
  | assC s e' => assC s (e_exp_subse e' exp u)
  end
.

Compute EvtE_subse (c ! x '+ 5) y (&x).
Compute EvtE_subse (x :=' (5 '* x '+ 3 '/ y)) (z '/ 5) (&x). 

Fixpoint Evt_subse (evt : Evt) (exp : e_exp) (u : VarType) : Evt :=
  match evt with 
  | nil => nil
  | e :: evt' => (EvtE_subse e exp u) :: (Evt_subse evt' exp u)
  end
.

Compute { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }.
Compute Evt_subse ( { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }) z (&x). 
Compute Evt_subse ( { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }) (z '+ 1) (&x). 

Fixpoint SEP_exp_subse (e : SEP_exp) (exp : e_exp) (u : VarType) : SEP_exp :=
  match e with 
  | skip => skip
  | evtC evt => evtC (Evt_subse evt exp u)
  | tstC P evt => tstC (P_exp_subse P exp u) (Evt_subse evt exp u) 
  | seqC e1 e2 => seqC (SEP_exp_subse e1 exp u) (SEP_exp_subse e2 exp u)
  | choC e1 e2 => choC (SEP_exp_subse e1 exp u) (SEP_exp_subse e2 exp u)
  | loopC e' => loopC (SEP_exp_subse e' exp u)
  end
.

Compute @ { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }.
Compute SEP_exp_subse ( @ { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }) z (&x). 
Compute SEP_exp_subse ( @ { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }) (z '- 2) (&x). 

Fixpoint cdl_subsE (e : CDL_exp) (E : E_exp) (u : VarType) : CDL_exp := (* e[E // x] *)
    match e with
    | cdl_trueC => cdl_trueC
    | cdl_ltC e1 e2 => cdl_ltC (E_exp_subsE e1 E u) (E_exp_subsE e2 E u)
    | cdl_box1C p r => match (E_2_e E) with 
                        | compC exp => cdl_box1C (SEP_exp_subse p exp u) r
                        | noCompC => cdl_box1C p r
                       end
    | cdl_box2C p e' => match (E_2_e E) with 
                          | compC exp => cdl_box2C (SEP_exp_subse p exp u) (cdl_subsE e' E u)
                          | noCompC => cdl_box2C p e'
                        end
    | cdl_negC e' => cdl_negC (cdl_subsE e' E u)
    | cdl_andC e1 e2 => cdl_andC (cdl_subsE e1 E u) (cdl_subsE e2 E u)
    | cdl_forallC x1 e' => match u with 
                             | tVarC x => if (eqv x1 x) then 
                                            cdl_forallC x1 e' else 
                                              cdl_forallC x1 (cdl_subsE e' E u)
                             | tCntC c => cdl_forallC x1 (cdl_subsE e' E u)
                             | tStC c => cdl_forallC x1 (cdl_subsE e' E u)
                           end
    | cdl_falseC => cdl_falseC
    | cdl_lteC e1 e2 => cdl_lteC (E_exp_subsE e1 E u) (E_exp_subsE e2 E u)
    | cdl_gtC e1 e2 => cdl_gtC (E_exp_subsE e1 E u) (E_exp_subsE e2 E u)
    | cdl_gteC e1 e2 => cdl_gteC (E_exp_subsE e1 E u) (E_exp_subsE e2 E u)
    | cdl_eqC e1 e2 => cdl_eqC (E_exp_subsE e1 E u) (E_exp_subsE e2 E u)
    | cdl_dia1C p r => match (E_2_e E) with 
                        | compC exp => cdl_dia1C (SEP_exp_subse p exp u) r
                        | noCompC => cdl_dia1C p r
                       end
    | cdl_dia2C p e' => match (E_2_e E) with 
                          | compC exp => cdl_dia2C (SEP_exp_subse p exp u) (cdl_subsE e' E u)
                          | noCompC => cdl_dia2C p e'
                        end
    | cdl_orC e1 e2 => cdl_orC (cdl_subsE e1 E u) (cdl_subsE e2 E u)
    | cdl_impC e1 e2 => cdl_impC (cdl_subsE e1 E u) (cdl_subsE e2 E u)
    | cdl_existsC x1 e' => match u with 
                             | tVarC x => if (eqv x1 x) then 
                                            cdl_existsC x1 e' else 
                                              cdl_existsC x1 (cdl_subsE e' E u)
                             | tCntC c => cdl_existsC x1 (cdl_subsE e' E u)
                             | tStC c => cdl_existsC x1 (cdl_subsE e' E u)
                           end
  end.

Notation "e [ E 'subs' u ]" := (cdl_subsE e E u) (at level 9).
Check [[ skip ]]' c1 << c2 .
Locate "/".
Locate "//".

Compute [[ y '> 1 ? { x :=' x '+ 1 }; skip ; @ { x :=' x '+ 1 } ]]' c1 << c2.
Compute ([[ y '> 1 ? { x :=' x '+ 1 }; skip ; @ { x :=' x '+ 1 } ]]' c1 << c2) [ y subs &x ] .
Compute ([[ y '> 1 ? { x :=' x '+ 1 }; skip ; @ { x :=' x '+ 1 } ]]' c1 << c2) [ (y +' 1) subs &x ] .
Compute ([[ x '> 1 ? { x :=' x '+ 1 }; skip ; @ { x :=' x '+ 1 } ]] x =' y +' 2) [ (y +' 2) subs &x ] .
Compute ([[ x '> 1 ? { x :=' x '+ 1 }; skip ; @ { x :=' x '+ 1 } ]] n(c) =' y +' 2) [ (y +' 2) subs &n(c) ] .

(* substitution for list *)
Fixpoint cdl_subsE_l (T : list CDL_exp) (E : E_exp) (u : VarType) : list CDL_exp := (* T [x' // x] *)
  match T with
  | nil => nil
  | e :: T' => (cdl_subsE e E u) :: (cdl_subsE_l T' E u)
  end.

Notation "T [ E 'subs-l' u ]" := (cdl_subsE_l T E u) (at level 9).


(* ----------------------------------- check if a substitution is admissible --------------------------------- *)
(* when checking if a substitution is admissible, we consider clock names c1 c2 c3 instead of clock-related 
variables n(c1) n(c2) n(c3) s(c1) s(c2) s(c3) .... This is simpler to be dealt with in Coq. And this is 
not like when we consider the substitution, there we must consider the clock-related variables *)

Fixpoint commonEle (v1 : list Var) (v2 : list Var) : bool :=
  match v1 with
  | nil => false
  | e :: v1' => if (NotIn_bool e v2) then commonEle v1' v2 else true
  end.

Compute commonEle (x :: y :: nil) (z :: nil).
Compute commonEle (x :: y :: nil) (z :: y :: nil).

Fixpoint E_exp_chk (e : E_exp) (ev : list Var) (u : VarType) (bv : list Var) : Prop := 
  (* ev --> variables in expression, bv --> bounded variables currently *)
  match e with
  | EvarC v => match u with 
                | tVarC x => if andb (eqv v x) (commonEle ev bv) then False else True
                | tCntC c => True
                | tStC c => True
               end
  | ECntClkC c => match u with 
                    | tVarC x => True
                    | tCntC c' => if andb (eqv c c') (commonEle ev bv) then False else True
                    | tStC c' => True
                  end
  | EStClkC c => match u with 
                    | tVarC x => True
                    | tCntC c' => True
                    | tStC c' => if andb (eqv c c') (commonEle ev bv) then False else True
                  end
  | EnumC n => True
  | EplusC e1 e2 => (E_exp_chk e1 ev u bv) /\ (E_exp_chk e2 ev u bv)
  | EmulC e1 e2 => (E_exp_chk e1 ev u bv) /\ (E_exp_chk e2 ev u bv)
  | EminusC e1 e2 => (E_exp_chk e1 ev u bv) /\ (E_exp_chk e2 ev u bv)
  | EdivC e1 e2 => (E_exp_chk e1 ev u bv) /\ (E_exp_chk e2 ev u bv)
  end
.


Fixpoint e_exp_chk (e : e_exp) (ev : list Var) (u : VarType) (bv : list Var) : Prop :=
  match e with
  | enumC n => True
  | evarC s => match u with 
                | tVarC x => if andb (eqv s x) (commonEle ev bv) then False else True
                | tCntC c => True
                | tStC c => True
               end
  | eplusC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  | eminusC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  | emulC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  | edivC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  end
.



Fixpoint EvtE_chk (e : EvtElement) (ev : list Var) (u : VarType) (bv : list Var) : Prop :=
  match e with 
  | sigC s e' => e_exp_chk e' ev u bv (* here s does not affect the substitution in e' *)
  | assC s e' => e_exp_chk e' ev u bv
  end
.


Fixpoint Evt_chk (evt : Evt) (ev : list Var) (u : VarType) (bv : list Var) : Prop :=
  match evt with 
  | nil => True
  | e :: evt' => (EvtE_chk e ev u bv) /\ (Evt_chk evt' ev u (bv ++ (EvtE_BV e bv)))
  end
.


Fixpoint P_exp_chk (P : P_exp) (ev : list Var) (u : VarType) (bv : list Var) : Prop :=
  match P with
  | PtrueC => True
  | PlteC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  | PnegC P' => P_exp_chk P' ev u bv
  | PandC P1 P2 => (P_exp_chk P1 ev u bv) /\ (P_exp_chk P2 ev u bv)
  | PfalseC => True
  | PltC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  | PgtC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  | PgteC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  | PeqC e1 e2 => (e_exp_chk e1 ev u bv) /\ (e_exp_chk e2 ev u bv)
  | PorC P1 P2 => (P_exp_chk P1 ev u bv) /\ (P_exp_chk P2 ev u bv)
  | PimpC P1 P2 => (P_exp_chk P1 ev u bv) /\ (P_exp_chk P2 ev u bv)
  end
.



Fixpoint SEP_exp_chk (p : SEP_exp) (ev : list Var) (u : VarType) (bv : list Var) : Prop :=
  match p with 
  | skip => True
  | evtC evt => Evt_chk evt ev u bv
  | tstC P evt => (P_exp_chk P ev u bv) /\ (Evt_chk evt ev u bv) (* it is impossible to have any 
    new bounded variables in P, so here bv is kept the same *)
  | seqC e1 e2 => (SEP_exp_chk e1 ev u bv) /\ (SEP_exp_chk e2 ev u (bv ++ (SEP_exp_BV e1 bv)))
  | choC e1 e2 => (SEP_exp_chk e1 ev u bv) /\ (SEP_exp_chk e2 ev u bv)
  | loopC e' => SEP_exp_chk e' ev u bv
  end
.

Fixpoint cdl_chk (e : CDL_exp) (ev : list Var) (u : VarType) (bv : list Var) : Prop := 
  (* e --> the expression to be substituted, ev --> the set of variables of the substituting expression, 
     u --> the variable type to be substituted, bv --> the set of bounded variables at current time *)
    match e with
    | cdl_trueC => True
    | cdl_ltC e1 e2 => (E_exp_chk e1 ev u bv) /\ (E_exp_chk e2 ev u bv)
    | cdl_box1C p r => SEP_exp_chk p ev u bv
    | cdl_box2C p e' => (SEP_exp_chk p ev u bv) /\ (cdl_chk e' ev u (bv ++ (SEP_exp_BV p bv)))
    | cdl_negC e' => cdl_chk e' ev u bv
    | cdl_andC e1 e2 => (cdl_chk e1 ev u bv) /\ (cdl_chk e2 ev u bv)
    | cdl_forallC x1 e' => cdl_chk e' ev u (x1 :: bv)
    | cdl_falseC => True
    | cdl_lteC e1 e2 => (E_exp_chk e1 ev u bv) /\ (E_exp_chk e2 ev u bv)
    | cdl_gtC e1 e2 => (E_exp_chk e1 ev u bv) /\ (E_exp_chk e2 ev u bv)
    | cdl_gteC e1 e2 => (E_exp_chk e1 ev u bv) /\ (E_exp_chk e2 ev u bv)
    | cdl_eqC e1 e2 => (E_exp_chk e1 ev u bv) /\ (E_exp_chk e2 ev u bv)
    | cdl_dia1C p r => SEP_exp_chk p ev u bv
    | cdl_dia2C p e' => (SEP_exp_chk p ev u bv) /\ (cdl_chk e' ev u (bv ++ (SEP_exp_BV p bv)))
    | cdl_orC e1 e2 => (cdl_chk e1 ev u bv) /\ (cdl_chk e2 ev u bv)
    | cdl_impC e1 e2 => (cdl_chk e1 ev u bv) /\ (cdl_chk e2 ev u bv)
    | cdl_existsC x1 e' => cdl_chk e' ev u (x1 :: bv)
    end.

(* ====================================================== CDL proof system =============================================*)

(* Gamma, Delta *)
Definition Gamma := list CDL_exp.
Definition Delta := list CDL_exp.

(***DEL Definition SequentL : Gamma -> CDL_exp -> Delta -> Prop.*)


(* we arrange a target place special for the dynamic formula we want to verify in the sequent, other formulas in Gamma
and Delta are pure FOL formulas. 

We define two types of sequent: sequentL and sequentR, where L and R indicate the verifiying formula is on the left
or right side of the sequent. 
*)

(* target place *)
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

(*DEL
Inductive tstSeq2 : Gamma -> place -> place -> Delta -> (list Var) -> Prop :=
  tst2 : forall (T : Gamma) (D : Delta) (e : e_exp) (phi : CDL_exp) (FV : list Var) (x : Var) (A : Evt), 
          ( let n := NewId FV in 
          (tstSeq2 ((x =' (e_2_E e) [(var n) subs-E x]) :: (T [ (var n) subs-l x ])) 
                   empty 
                  (exp ([ @ A ] phi)) 
                  (D [ (var n) subs-l x ]) 
                  (var n :: FV) )
        ) -> 
    (tstSeq2 T empty (exp ([ @ ((x :=' e) :: A) ] phi)) D FV) 
  |
  tst3 : forall (T : Gamma) (D : Delta) (phi : CDL_exp) (FV : list Var), 
          (
          tstSeq2 T 
                   empty 
                  (exp phi) 
                  D
                  FV
        ) -> 
    (tstSeq2 T empty (exp ([ @ idle ] phi)) D FV)
where " { T , p1 } ==> { p2 , D } & { FV }" := (tstSeq2 T p1 p2 D FV)
.

Theorem thm2 : { ((y =' 1):: nil) , empty ==> exp ([ @ {y :=' y '+ z | y :=' y '+ 1}] y >' 2) , nil & 
                (y :: z :: nil) }.
Proof. 
apply tst2. cbv.
apply tst2. cbv.
apply tst3. cbv.
Abort.
*)

Compute (1 :: 2 :: 3 :: nil) ++ (4 :: 5 :: 6 :: nil).
Compute (4 :: 5 :: 6 :: nil) ++ (1 :: 2 :: 3 :: nil).

(*&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&  end of test &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&*)


(* =========================================== some auxiliary funcions ================= *)
(* transform a sequent to a CDL exp, which we will need to implement Rule (o) below *)
Fixpoint Gamma_2_CDLexp (T : Gamma) : CDL_exp :=
  match T with 
  | nil => tt'
  | e :: T' => e /\' (Gamma_2_CDLexp T')
  end.

Fixpoint Delta_2_CDLexp (D : Gamma) : CDL_exp :=
  match D with 
  | nil => ff'
  | e :: D' => e \/' (Delta_2_CDLexp D')
  end.

Definition place_2_CDLexp_L (p : place) : CDL_exp :=
  match p with
  | empty => tt'
  | exp e => e
  end.

Definition place_2_CDLexp_R (p : place) : CDL_exp :=
  match p with
  | empty => ff'
  | exp e => e
  end.

Definition Seq_2_CDLexp (T : Gamma) (p1 : place) (p2 : place) (D : Delta) : CDL_exp :=
  ((Gamma_2_CDLexp T) /\' (place_2_CDLexp_L p1)) 
  ->'
  ((place_2_CDLexp_R p2) \/' (Delta_2_CDLexp D))
.

Compute Seq_2_CDLexp ((x =' 1) :: (y >' 1) :: nil) empty (exp (z =' 3)) nil.

(* =========================================== construction of the proof system ================================================= *)

Reserved Notation "<| T , p1  ==> p2 , D // V , C , ntC |> " (at level 75).
(*Reserved Notation "T ==> p , D" (at level 75).*)

Locate "==>".

(* definition of sequent *)
(* currently we do not consider the other direction of the rules and rules for the dual operator of `[p]'. *)
Inductive Seq : Gamma -> place -> place -> Delta -> (list Var) -> (list Var) -> (list Var) -> Prop :=

  (* ****************************** rules special for the sequent defined in Coq ********************* *)
(* these rules are special in Coq, they are not defined in the original proof system of CDL in the paper. We need them because
  the structure of the sequent in Coq is slightly different from that in the paper. We need special rules to deal with 
  `place' in the sequent *)

(* 
   V: all variables appearing in the current sequent 
   C: all clocks appearing in the current sequent
   ntC: all clocks that does not tick at current instant. 
*)

  r_placeR_rmv_int : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                        (phi : CDL_exp),
          (
            Seq T pls1 empty (addNail D phi) V C ntC (* put phi at the nail of D *)
          )
          ->
          (
            Seq T pls1 (exp phi) D V C ntC
          )
|
  r_placeR_add_int : forall (T : Gamma) (pls1 : place) (D' : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                        (phi : CDL_exp),
          (
            Seq T pls1 (exp phi) D' V C ntC (* add a new phi from the head of D = phi :: D' *)
          )
          ->
          (
            Seq T pls1 empty (phi :: D') V C ntC
          )
|
  r_placeL_rmv_int : forall (T : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                        (phi : CDL_exp),
          (
            Seq (addNail T phi) empty pls1 D V C ntC (* put phi at the nail of T *)
          )
          ->
          (
            Seq T (exp phi) pls1 D V C ntC
          )
|
  r_placeL_add_int : forall (T' : Gamma) (pls1 : place) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                        (phi : CDL_exp),
          (
            Seq T' (exp phi) pls1 D V C ntC (* add a new phi from the head of T = phi :: T' *)
          )
          ->
          (
            Seq (phi :: T') empty pls1 D V C ntC
          )
|

  (* ****************************** rules for combinational events and formulae [p]rel *********************** *)
(* Rule (\phi[]) *)
  r_Phi_all_int1 : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                    (x : Var) (e : e_exp) (A : Evt) (phi : CDL_exp), 
          let n := NewId V in 
          (
            Seq ((x =' (e_2_E e) [(var n) subs-E &x]) :: (T [ (var n) subs-l &x ])) 
                      empty 
                        (exp ([[ @ A ]] phi)) 
                          (D [ (var n) subs-l &x ]) 
                            (var n :: V) C ntC
          )
          ->
          (
            Seq T empty (exp ([[ @ ((x :=' e) :: A) ]] phi)) D V C ntC
          )
|
  r_Phi_all_int2 : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var) 
                      (c : Var) (e : e_exp) (A : Evt) (phi : CDL_exp), 
          let n := NewId V in 
          let m := S n in
          (
            Seq (
                  (n(c) =' (var n) +' 1) :: 
                    (s(c) =' 1) ::
                      (
                        (T [ (var n) subs-l &n(c) ]) [ (var m) subs-l &s(c) ]
                      )
                ) 
                      empty 
                        (exp ([[ @ A ]] phi)) 
                          (
                            (D [ (var n) subs-l &n(c) ]) [ (var m) subs-l &s(c) ]
                          ) 
                            (var m :: var n :: V)
                              C
                                (rmv ntC c) (* remove c from the set ntC *)
          )
          ->
          (
            Seq T empty (exp ([[ @ ((c ! e) :: A) ]] phi)) D V C ntC
          )
|
  r_Phi_all_int_idle1 : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var)
                    (phi : CDL_exp), 
          (
            Seq T empty (exp phi) D V C C (* when ntC = nil, reset it to C *) 
          ) 
          ->
          (
            Seq T empty (exp ([[ @ idle ]] phi)) D V C nil
          )
|
  r_Phi_all_int_idle2 : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (c : Var) (ntC' : list Var)
                    (phi : CDL_exp), 
          (
            let n := NewId V in 
            (
              Seq (
                    (s(c) =' 0) :: (T [(var n) subs-l &s(c)])
                  )
                    empty
                      (exp ([[ @ idle ]] phi))
                        (D [(var n) subs-l &s(c)])
                          ((var n) :: V)
                            C 
                              ntC'
            )
          ) 
          ->
          (
            Seq T empty (exp ([[ @ idle ]] phi)) D V C (c :: ntC')
          )
|

(* Rule (\pi[]) *)
  r_Pi_all_int1 : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                    (x : Var) (e : e_exp) (A : Evt) (r : rel), 
          let n := NewId V in 
          (
            Seq ((x =' (e_2_E e) [(var n) subs-E &x]) :: (T [ (var n) subs-l &x ])) 
                      empty 
                        (exp ([[ @ A ]]' r)) 
                          (D [ (var n) subs-l &x ]) 
                            (var n :: V) C ntC
          )
          ->
          (
            Seq T empty (exp ([[ @ ((x :=' e) :: A) ]]' r)) D V C ntC
          )
|
  r_Pi_all_int2 : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                    (c : Var) (e : e_exp) (A : Evt) (r : rel), 
          let n := NewId V in 
          let m := S n in
          (
            Seq (
                  (n(c) =' (var n) +' 1) :: 
                    (s(c) =' 1) ::
                      (
                        (T [ (var n) subs-l &n(c) ]) [ (var m) subs-l &s(c) ]
                      )
                )
                      empty 
                        (exp ([[ @ A ]]' r)) 
                          (
                            (D [ (var n) subs-l &n(c) ]) [ (var m) subs-l &s(c) ]
                          ) 
                            (var m :: var n :: V) 
                              C 
                                (rmv ntC c) (* remove c from the set ntC *)
          )
          ->
          (
            Seq T empty (exp ([[ @ ((c ! e) :: A) ]]' r)) D V C ntC
          )
|
  r_Pi_all_int_idle1 : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var)
                    (r : rel), 
          (
            Seq T empty (exp (hbar r)) D V C C (* when ntC = nil, reset it to C *) 
          )
          ->
          (
            Seq T empty (exp ([[ @ idle ]]' r)) D V C nil
          )
|
r_Pi_all_int_idle2 : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (c : Var) (ntC' : list Var)
                    (r : rel), 
          (
            let n := NewId V in 
            (
              Seq (
                    (s(c) =' 0) :: (T [(var n) subs-l &s(c)])
                  )
                    empty
                      (exp ([[ @ idle ]]' r))
                        (D [(var n) subs-l &s(c)])
                          ((var n) :: V)
                            C 
                              ntC'
            )
          ) 
          ->
          (
            Seq T empty (exp ([[ @ idle ]]' r)) D V C (c :: ntC')
          )
|

(* Rule P? *)
  r_Test_all_phi_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                          (P : P_exp) (A : Evt) (phi : CDL_exp), 
          (
            Seq T empty (exp ((Pexp_2_CDLexp P) ->' [[ @ A ]] phi )) D V C ntC
          )
          ->
          (
            Seq T empty (exp ([[ P ? A ]] phi)) D V C ntC
          )
|
  r_Test_all_rel_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                        (P : P_exp) (A : Evt) (r : rel), 
          (
            Seq T empty (exp ((Pexp_2_CDLexp P) ->' [[ @ A ]]' r )) D V C ntC
          )
          ->
          (
            Seq T empty (exp ([[ P ? A ]]' r)) D V C ntC
          )
|

(* Rule \pi\epsilon *)
  r_PiEp_all_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                    (r : rel), 
          (
            Seq T empty ( exp (tt') ) D V C ntC
          )
          ->
          (
            Seq T empty (exp ([[ skip ]]' r)) D V C ntC
          )
|

(* Rule \epsilon *)
  r_Ep_all_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                  (phi : CDL_exp), 
          (
            Seq T empty ( exp phi ) D V C ntC
          )
          ->
          (
            Seq T empty (exp ([[ skip ]] phi)) D V C ntC
          )
|

(* Rule \pi[;] *)
  r_PiSeq_all_int : forall (T: Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                      (p : SEP_exp) (q : SEP_exp) (r : rel),
          (
            Seq T empty
                    (exp ([[ p ]]' r /\' [[ p ]] ([[ q ]]' r)))
                      D V C ntC
          )
          ->
          (
            Seq T empty (exp ([[ p;q ]]' r)) D V C ntC
          )
|

(* Rule \pi[\cup] *)
  r_PiCho_all_int : forall (T: Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                      (p : SEP_exp) (q : SEP_exp) (r : rel),
          (
            Seq T empty
                    (exp ([[ p ]]' r /\' [[ q ]]' r))
                      D V C ntC
          )
          ->
          (
            Seq T empty (exp ([[ p U q ]]' r)) D V C ntC
          )
|

(* Rule \pi[*]u *)
  r_PiLoopU_all_int : forall (T: Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                        (p : SEP_exp) (r : rel),
          (
            Seq T empty
                    (exp ([[ p ; p ** ]]' r))
                      D V C ntC
          )
          ->
          (
            Seq T empty (exp ([[ p ** ]]' r)) D V C ntC
          )
|

(* Rule \pi[*]i *)
  r_PiLoopI_all_int : forall (T: Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                        (p : SEP_exp) (r : rel),
          (
            Seq T empty
                    (exp ([[ p ** ]] ([[ p ]]' r)))
                      D V C ntC
          )
          ->
          (
            Seq T empty (exp ([[ p ** ]]' r)) D V C ntC
          )
|

(* ****************************** rules for formula [p]\phi inherited from FODL *********************** *)
(* Rule [;] *)
  r_Seq_all_int : forall (T: Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                    (p : SEP_exp) (q : SEP_exp) (phi : CDL_exp),
          (
            Seq T empty
                    (exp ([[ p ]] ([[ q ]] phi)))
                      D V C ntC
          )
          ->
          (
            Seq T empty (exp ([[ p ; q ]] phi)) D V C ntC
          )
|

(* Rule [U] *)
  r_Cho_all_int : forall (T: Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                    (p : SEP_exp) (q : SEP_exp) (phi : CDL_exp),
          (
            Seq T empty
                    (exp ([[ p ]] phi /\' [[ q ]] phi))
                      D V C ntC
          )
          ->
          (
            Seq T empty (exp ([[ p U q ]] phi)) D V C ntC
          )
|

(* Rule [*]u *)
  r_LoopU_all_Int : forall (T: Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                    (p : SEP_exp) (phi : CDL_exp),
          (
            Seq T empty
                    (exp (phi /\' [[ p ; p ** ]] phi))
                      D V C ntC
          )
          ->
          (
            Seq T empty (exp ([[ p ** ]] phi)) D V C ntC
          )
|

(*** here we also omit the rules ([]gen), (<>gen), ([*]ind), (<*>con) temporally since we actually do NOT 
need them for derivatiion, they are just necessary for the relative completeness of the proof system. ***)

(* Rule [*]i *)
  r_LoopI_all : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                  (p : SEP_exp) (phi : CDL_exp), 
          (
            exists (inv : CDL_exp), (* invariant has to be manually provided *)
              (
                Seq T empty (exp inv) D (V ++ (cdl_V inv V)) C ntC
              )
              /\
              (
                Seq nil empty 
                          (exp (inv ->' [[ p ]] inv))
                            nil
                              (cdl_V (inv ->' [[ p ]] inv) nil) C ntC
              )
              /\
              (
                Seq nil empty 
                          (exp (inv ->' phi))
                            nil
                              (cdl_V (inv ->' phi) nil) C ntC
              )
          )
          ->
          (
            Seq T empty 
                    (exp ([[ p ** ]] phi)) D V C ntC
          )
|

(* Rule <*>i *)
  r_LoopI_dia : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                  (p : SEP_exp) (phi : CDL_exp), 
          (
            exists (inv : E_exp -> CDL_exp), (* invariant has to be manually provided *)
              (
                let X := var (NewId (V ++ (cdl_V_f inv V))) in 
                (
                Seq T empty 
                        (exp (ext X , (X >=' 0 /\' (inv X))))
                            D 
                              (V ++ (cdl_V (ext X , (X >=' 0 /\' (inv X))) V))
                                  C ntC
                )
              )
              /\
              (
                let X := var (NewId (cdl_V_f inv nil)) in
                (
                Seq nil empty 
                          (exp (
                                  all X, X >' 0 ->' ((inv X) ->' << p >> (inv (X -' 1)))
                               )
                          )
                            nil
                              (cdl_V (all X, X >' 0 ->' ((inv X) ->' << p >> (inv (X -' 1)))) nil)
                                  C ntC
                )
              )
              /\
              (
                let X := var (NewId (cdl_V_f inv nil)) in
                (
                Seq nil empty
                          (exp (
                                  ext X, X <=' 0 /\' ((inv X) ->' phi)
                               )
                          )
                            nil
                              (cdl_V (ext X, X <=' 0 /\' ((inv X) ->' phi)) nil)
                                  C ntC
                )
              )
          )
          ->
          (
            Seq T empty 
                    (exp (<< p ** >> phi)) D V C ntC
          )
|

(* ****************************** rules of FOL *********************** *)
(* Rule (o) *)
  r_o_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var),
        (
          let fof := (Seq_2_CDLexp T empty empty D) in 
          (
            forall (st : Var -> nat) (fn : Var -> nat) (gn : Var -> nat) , (CDLexp_2_Prop fof st fn gn)
            (* the Prop formula corresponding to the sequent: `Seq T empty empty D V' *)
          )
        )
        ->
        (
          Seq T empty empty D V C ntC
        )
|

(* Rule (ax) *)
  r_ax_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var) 
                      (phi : CDL_exp), 
        (
          True
        )
        ->
        (
          Seq T (exp phi) (exp phi) D V C ntC
        )
|

(* Rule (cut) *)
  r_cut_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var), 
        (
          forall (phi : CDL_exp),
            (
              Seq T empty (exp phi) D (V ++ (cdl_V phi V)) C ntC
            )
            /\
            (
              Seq T (exp phi) empty D (V ++ (cdl_V phi V)) C ntC
            )
        )
        ->
        (
          Seq T empty empty D V C ntC
        )
|

(* Rule (~ r) *)
  r_negR_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                (phi : CDL_exp),
        (
          Seq T (exp (~' phi)) empty D V C ntC
        )
        ->
        (
          Seq T empty (exp phi) D V C ntC
        )
|

(* Rule (~ l) *)
  r_negL_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                (phi : CDL_exp),
        (
          Seq T empty (exp (~' phi)) D V C ntC
        )
        ->
        (
          Seq T (exp phi) empty D V C ntC
        )
|

(* Rule (/\ r) *)
  r_andR_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                (phi1 : CDL_exp) (phi2 : CDL_exp),
        (
          (
            Seq T empty (exp phi1) D V C ntC
          )
          /\
          (
            Seq T empty (exp phi2) D V C ntC
          )
        )
        ->
        (
          Seq T empty (exp (phi1 /\' phi2)) D V C ntC
        )
|

(* Rule (/\ l) *)
  r_andL_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                (phi1 : CDL_exp) (phi2 : CDL_exp),
        (
          Seq (phi2 :: T) 
                (exp phi1) empty D V C ntC
        )
        ->
        (
          Seq T (exp (phi1 /\' phi2)) empty D V C ntC
        )
|

(* Rule (all r) *)
  r_allR_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                (phi : CDL_exp) (x : Var),
        (
          let n := NewId V in
          (
            Seq T empty 
                    (
                      exp (phi [(var n) subs &x])
                    )
                        D 
                          ((var n) :: V) C ntC
          )
        )
        ->
        (
          Seq T empty (exp (all x , phi)) D V C ntC
        )
|

(* Rule (all l) *)

  r_allL_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                (phi : CDL_exp) (x : Var),
        (
          exists (E : E_exp),
          (
            (cdl_chk phi (E_exp_V E nil) (&x) nil) (* make sure that the substitution phi[E / x] is admissible *)
            /\
            (
              Seq ((all x , phi) :: T) 
                      ( 
                        exp (phi [E subs &x])
                      )
                        empty
                          D
                            (V ++ (E_exp_V E V)) C ntC
            )
          )
        )
        ->
        (
          Seq T (exp (all x , phi)) empty D V C ntC
        )
|

(* Rule (\/ r) *)
  r_orR_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var) 
                 (phi1 : CDL_exp) (phi2 : CDL_exp),
        (
          Seq T empty (exp phi1) ((phi2) :: D) V C ntC
        )
        ->
        (
          Seq T empty (exp (phi1 \/' phi2)) D V C ntC
        )
|

(* Rule (\/ l) *)
  r_orL_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var) 
                (phi1 : CDL_exp) (phi2 : CDL_exp),
        (
          (
            Seq T (exp phi1) empty D V C ntC
          )
          /\
          (
            Seq T (exp phi2) empty D V C ntC
          )
        )
        ->
        (
          Seq T (exp (phi1 \/' phi2)) empty D V C ntC
        )
|

(* Rule (-> r) *)
  r_impR_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                  (phi1 : CDL_exp) (phi2 : CDL_exp),
        (
          Seq T (exp phi1) (exp phi2) D V C ntC
        )
        ->
        (
          Seq T empty (exp (phi1 ->' phi2)) D V C ntC
        )
|

(* Rule (-> l) *)
  r_impL_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                  (phi1 : CDL_exp) (phi2 : CDL_exp),
        (
          (
            Seq T empty (exp phi1) D V C ntC
          )
          /\
          (
            Seq T (exp phi2) empty D V C ntC
          )
        )
        ->
        (
          Seq T (exp (phi1 ->' phi2)) empty D V C ntC
        )
|

(* Rule (ext r) *)
  r_extR_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var) 
                  (phi : CDL_exp) (x : Var),
        (
          exists (E : E_exp),
            (cdl_chk phi (E_exp_V E nil) (&x) nil) (* make sure that the substitution phi[E / x] is admissible *)
            /\
            (
              Seq T empty 
                      (exp (phi [ E subs &x ])) 
                        D 
                          (V ++ (E_exp_V E V)) C ntC
            )
        )
        ->
        (
          Seq T empty (exp (ext x , phi)) D V C ntC
        )
|

(* Rule (ext l) *)
  r_extL_int : forall (T : Gamma) (D : Delta) (V : list Var) (C : list Var) (ntC : list Var)
                (phi : CDL_exp) (x : Var),
        (
          let n := NewId V in
          (
            Seq ((ext x, phi) :: T) 
                    (
                      exp (phi [(var n) subs &x])
                    )
                      empty
                        D 
                          ((var n) :: V) C ntC
          )
        )
        ->
        (
          Seq T (exp (ext x , phi)) empty D V C ntC
        )

(* define the notation at the end *)
where "<| T , p1  ==>  p2 , D  //  V , C , ntC |>" := (Seq T p1 p2 D V C ntC)
.

Locate "//".

Theorem tst1 : <| nil, (exp tt')  ==>  (exp tt') , nil  //  nil , nil , nil |>.
Proof.
apply r_ax_int.
auto.
Qed.

Theorem tstThm1 : <| ((y =' 1):: nil) , empty  ==>  exp ([[ @ {y :=' y '+ z | y :=' y '+ 1} ]] y >' 2) , nil  //
                 (y :: z :: nil) , nil , nil |>.
Proof. 
apply r_Phi_all_int1. cbv.
apply r_Phi_all_int1. cbv.
apply r_Phi_all_int_idle1. cbv.
Abort.

Theorem tstThm2 : <| ((x =' 1) :: (y =' 1):: nil) , empty  ==>  exp ([[ @ {c ! 0 | y :=' y '+ 1} ]]' c1 << c2) , nil  //
                 (y :: z :: nil) , nil , nil |>.
Proof. 
apply r_Pi_all_int2.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* a small example *)
(* general variables x, f*)
Definition f : Var := (var 11).
Definition Y : Var := (var 12).

(* clock *)
Definition e : Var := (var 13).
Definition p : Var := (var 14).
Definition r : Var := (var 15).
Definition o : Var := (var 16).

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
