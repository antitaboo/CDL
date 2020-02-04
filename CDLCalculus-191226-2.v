Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.

Import ListNotations.

Require Import Omega. (* for omega tactic *)

(* Syntax of Clock-based Dynamic Logic *)

(* Syntax of SEP_exp (Synchonous Event Program) *)


(* ========================= Syntax of SEP_exp ========================*)

(* =============== Syntax of Expressions ===================*)

(* Arith Expression `e'*)

Inductive Var := 
  var : nat -> Var |
  cnt : nat -> Var |
  sta : nat -> Var
.

(* in this version, I try to understand variables as identifications numbered by natural numbers, 
which we believe is more convenient than considering them as strings in practical derivations*)

(* In CDL we build here in Coq, we only build the `E' expression  and take `e' expression as a sub-expression of it *)
Inductive E_exp := 
  EnumC : nat -> E_exp | 
  EvarC : Var -> E_exp | 
  EplusC : E_exp -> E_exp -> E_exp |
  (*non-necessary expression*)
  EminusC : E_exp -> E_exp -> E_exp |
  EmulC : E_exp -> E_exp -> E_exp |
  EdivC : E_exp -> E_exp -> E_exp
.
Print E_exp.


Notation "e1 '+ e2" := (EplusC e1 e2) (at level 31, right associativity).
Locate "'+".
Notation "e1 '- e2" := (EminusC e1 e2) (at level 31, right associativity).

Notation "e1 '* e2" := (EmulC e1 e2) (at level 21, right associativity).

(*** Open Scope e_exp_scope. ***)

Locate "*".
Check (EnumC 4) '* (EnumC 5 '+ EnumC 6).
Coercion EvarC : Var >-> E_exp.
Notation "e1 '/ e2" := (EdivC e1 e2) (at level 21, right associativity).
Check (EnumC 4) '/ (EnumC 4).

Coercion EnumC : nat >-> E_exp.
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

(* define two functions at the interpretation level for ECntClkC and EStClkC. *)
Variable fn : nat -> nat.
Variable gn : nat -> nat.

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
  cdl_impC : CDL_exp -> CDL_exp -> CDL_exp |
  cdl_existsC : Var -> CDL_exp -> CDL_exp
.

Notation "'tt''" := cdl_trueC (at level 9). (* previous setting is 65, but I don't why it does not work sometimes *)
Notation "e1 <' e2" := (cdl_ltC e1 e2) (at level 61).
Notation "[ p ]' r" := (cdl_box1C p r) (at level 63, p at level 62, r at level 62).
Notation "[ p ] e" := (cdl_box2C p e) (at level 63, p at level 62, e at level 62).
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
Check ([ skip ]' c1 << c2) /\' 2 >' 5 /\' tt'.
Check [ @ {x :=' 4 | c1 ! 5} ; (x '> 0) ? {c2!4} ; @ idle; skip] n(c) >' 0.
Check [(@ {x :=' 4 | c1 ! 5} ; (x '> 0) ? {c2!4} ; @ idle; skip)** ]' c1<<c2.
Check [ skip ]' c1 << c2 .
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

Fixpoint Eexp_2_exp (e : E_exp) (st : state) : nat :=
  match e with
  | EvarC v => st v
  | ECntClkC c => fn (st c)
  | EStClkC c => gn (st c)
  | EnumC n => n
  | EplusC e1 e2 => (Eexp_2_exp e1 st) + (Eexp_2_exp e2 st)
  | EmulC e1 e2 => (Eexp_2_exp e1 st) * (Eexp_2_exp e2 st)
  | EminusC e1 e2 => (Eexp_2_exp e1 st) - (Eexp_2_exp e2 st)
  | EdivC e1 e2 => (Eexp_2_exp e1 st) / (Eexp_2_exp e2 st)
  end
.

(* transform a CDL exp to a FOLF formula *)
Fixpoint CDLexp_2_FOLF (e : CDL_exp) (st : state) : FOLF :=
  match e with
  | cdl_trueC => pureC True
  | cdl_ltC e1 e2 => pureC ((Eexp_2_exp e1 st) < (Eexp_2_exp e2 st))
  | cdl_box1C p r => noPureC (*once met dynamic operators, it is not a pure FOL formula *)
  | cdl_box2C p e' => noPureC
  | cdl_negC e' => match (CDLexp_2_FOLF e' st) with 
                    | noPureC => noPureC
                    | pureC f => pureC (~ f) 
                   end
  | cdl_andC e1 e2 => match (CDLexp_2_FOLF e1 st), (CDLexp_2_FOLF e2 st) with 
                        | noPureC , _ => noPureC
                        | _ , noPureC => noPureC
                        | (pureC f1) , (pureC f2) => pureC (f1 /\ f2)
                      end
  | cdl_forallC x e' => match (CDLexp_2_FOLF e' st) with
                          | noPureC => noPureC
                          | pureC f => pureC (forall (x : nat), f)
                        end
  | cdl_falseC => pureC False
  | cdl_lteC e1 e2 => pureC ((Eexp_2_exp e1 st) <= (Eexp_2_exp e2 st)) 
  | cdl_gtC e1 e2 => pureC ((Eexp_2_exp e1 st) > (Eexp_2_exp e2 st)) 
  | cdl_gteC e1 e2 => pureC ((Eexp_2_exp e1 st) >= (Eexp_2_exp e2 st)) 
  | cdl_eqC e1 e2 => pureC ((Eexp_2_exp e1 st) = (Eexp_2_exp e2 st)) 
  | cdl_dia1C p r => noPureC (*once met dynamic operators, it is not a pure FOL formula *)
  | cdl_dia2C p e' => noPureC
  | cdl_orC e1 e2 => match (CDLexp_2_FOLF e1 st), (CDLexp_2_FOLF e2 st) with 
                        | noPureC , _ => noPureC
                        | _ , noPureC => noPureC
                        | (pureC f1) , (pureC f2) => pureC (f1 \/ f2)
                     end
  | cdl_impC e1 e2 => match (CDLexp_2_FOLF e1 st), (CDLexp_2_FOLF e2 st) with 
                        | noPureC , _ => noPureC
                        | _ , noPureC => noPureC
                        | (pureC f1) , (pureC f2) => pureC (f1 -> f2)
                      end
  | cdl_existsC x e' => match (CDLexp_2_FOLF e' st) with
                          | noPureC => noPureC
                          | pureC f => pureC (exists (x : nat), f)
                        end
  end.


Variable st0 : state. 
Compute (CDLexp_2_FOLF tt' st0).
Compute (CDLexp_2_FOLF (tt' /\' x >=' 5) st0).
Compute (CDLexp_2_FOLF (tt' /\' (x >=' 5 ->' [ skip ] x >' 5 )) st0).
Compute (CDLexp_2_FOLF (tt' /\' (x >=' 5 ->' n(c) >' 5 )) st0).


(* transform a CDL_exp to Prop formula, if CDL_exp is not pure, simply return False, otherwise, 
return the Prop formula corresponding to it. *)

Definition CDLexp_2_Prop (e : CDL_exp) (st : state) : Prop :=
  match (CDLexp_2_FOLF e st) with
    | noPureC => False
    | pureC f => f
  end.

Compute CDLexp_2_Prop (tt' /\' (x >=' 5 ->' [ skip ] x >' 5 )) st0.
Compute CDLexp_2_Prop (tt' /\' (x >=' 5 ->' n(c) >' 5 )) st0.


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
  | cdl_existsC x1 e' => cdl_FV e' (x1 :: bv) (* x1 is a bounded variable *)
  end
.

Check ( all y , y =' 7 ) .
Compute cdl_FV ([ (@ { x :=' 5}; x '> 2 ? { y :=' y '- z} U skip) ] x >' 0 /\' ( all y , y =' 7 ) ) nil.
Compute cdl_FV ([ (@ { x :=' 5}; x '> 2 ? { y :=' y '- z} U skip) ] x >' 0 /\' ( all y , y =' 7 ) ) (y :: nil).
Compute cdl_FV ([ (@ { x :=' 5}; x '> 2 ? { y :=' y '- z} U skip) ] x >' 0 /\' ( ext y , y =' 7 ) ) (y :: nil).

(* for list *)
Fixpoint cdl_FV_l (T : list CDL_exp) (bv : list Var) : list Var :=
  match T with 
  | nil => nil
  | e :: T' => (cdl_FV e bv) ++ (cdl_FV_l T' bv)
  end.

Check nat.


(* ------------------------------------- compute FV for a function ----------------------------------*)
(* here we do a trick. We pass to phi a variable with a variable id that we will never use in the context 
(i.e., the var 0), and we add this variable to the bounded variable list bv, so that the final FV set of 
phi will definitely not contain var 0. 
Note that var 0 must not be used anywhere, or it would be dangerous since it is possible var 0 
has already existed in the formul phi *)


Definition cdl_FV_f (phi : E_exp -> CDL_exp) (bv : list Var) : list Var :=
  cdl_FV (phi (var 0)) ((var 0) :: bv).

(* generate a new variable id *)
Fixpoint MaxId (FVSet : list Var) : nat :=
  match FVSet with
  | nil => 0 (* when there is no variables in the current environment FVSet, just start from the number 0 *)
  | v :: FVSet' => let n := MaxId FVSet' in (
                      match v with | var m => 
                        if le_lt_dec n m then m else (MaxId FVSet') (* le_lt_dec : <= *)
                      end
                      )
  end
.

Compute MaxId (var 1 :: var 3 :: var 5 :: var 6 :: nil).

Definition NewId (FVSet : list Var) : nat := (S (MaxId FVSet)). 

Compute NewId (var 7 :: var 1 :: var 3 :: var 3 :: var 5 :: var 6 :: nil).
Compute NewId nil.

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

(* transform E_exp to e_exp *)
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

Fixpoint E_exp_subsE (e : E_exp) (E : E_exp) (x : Var) : E_exp := 
  match e with
  | EvarC v => if (eqv v x) then E else EvarC v
  | ECntClkC c => ECntClkC c (* do not consider replacing a clock-related variable *)
  | EStClkC c => EStClkC c
  | EnumC n => EnumC n
  | EplusC e1 e2 => EplusC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
  | EmulC e1 e2 => EmulC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
  | EminusC e1 e2 => EminusC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
  | EdivC e1 e2 => EdivC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
  end
.

Compute E_exp_subsE (x +' y) (y +' 1) x.
Compute E_exp_subsE (x *' z) (y *' 5) c.
Compute E_exp_subsE (n(c) *' z) (y *' 5) z.

Notation "e [ E 'subs-E' x ]" := (E_exp_subsE e E x) (at level 9).

Fixpoint e_exp_subse (e : e_exp) (exp : e_exp) (x : Var) : e_exp :=
  match e with
  | enumC n => enumC n
  | evarC s => if (eqv s x) then exp else evarC s
  | eplusC e1 e2 => eplusC (e_exp_subse e1 exp x) (e_exp_subse e2 exp x)
  | eminusC e1 e2 => eminusC (e_exp_subse e1 exp x) (e_exp_subse e2 exp x)
  | emulC e1 e2 => emulC (e_exp_subse e1 exp x) (e_exp_subse e2 exp x)
  | edivC e1 e2 => edivC (e_exp_subse e1 exp x) (e_exp_subse e2 exp x)
  end
.

Compute (z '- 5) '* x '+ z.
Compute e_exp_subse ((z '- 5) '* x '+ z) y z.
Compute e_exp_subse ((z '- 5) '* x '+ z) (y '- 2) z.

Fixpoint P_exp_subse (P : P_exp) (exp : e_exp) (x : Var) : P_exp :=
  match P with
  | PtrueC => PtrueC 
  | PlteC e1 e2 => PlteC (e_exp_subse e1 exp x) (e_exp_subse e2 exp x)
  | PnegC P' => PnegC (P_exp_subse P' exp x)
  | PandC P1 P2 => PandC (P_exp_subse P1 exp x) (P_exp_subse P2 exp x)
  | PfalseC => PfalseC
  | PltC e1 e2 => PltC (e_exp_subse e1 exp x) (e_exp_subse e2 exp x)
  | PgtC e1 e2 => PgtC (e_exp_subse e1 exp x) (e_exp_subse e2 exp x)
  | PgteC e1 e2 => PgteC (e_exp_subse e1 exp x) (e_exp_subse e2 exp x)
  | PeqC e1 e2 => PeqC (e_exp_subse e1 exp x) (e_exp_subse e2 exp x)
  | PorC P1 P2 => PorC (P_exp_subse P1 exp x) (P_exp_subse P2 exp x)
  | PimpC P1 P2 => PimpC (P_exp_subse P1 exp x) (P_exp_subse P2 exp x)
  end
.

Compute 'tt '/\ '~ (x '< 5).
Compute P_exp_subse ('tt '/\ '~ (x '< 5)) z x.
Compute P_exp_subse ('tt '/\ '~ (x '< 5)) (z '* 2) x.

Fixpoint EvtE_subse (e : EvtElement) (exp : e_exp) (x : Var) : EvtElement :=
  match e with 
  | sigC s e' => sigC s (e_exp_subse e' exp x)
  | assC s e' => assC s (e_exp_subse e' exp x)
  end
.

Compute EvtE_subse (c ! x '+ 5) y x.
Compute EvtE_subse (x :=' (5 '* x '+ 3 '/ y)) (z '/ 5) x. 

Fixpoint Evt_subse (evt : Evt) (exp : e_exp) (x : Var) : Evt :=
  match evt with 
  | nil => nil
  | e :: evt' => (EvtE_subse e exp x) :: (Evt_subse evt' exp x)
  end
.

Compute { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }.
Compute Evt_subse ( { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }) z x. 
Compute Evt_subse ( { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }) (z '+ 1) x. 

Fixpoint SEP_exp_subse (e : SEP_exp) (exp : e_exp) (x : Var) : SEP_exp :=
  match e with 
  | skip => skip
  | evtC evt => evtC (Evt_subse evt exp x)
  | tstC P evt => tstC (P_exp_subse P exp x) (Evt_subse evt exp x) 
  | seqC e1 e2 => seqC (SEP_exp_subse e1 exp x) (SEP_exp_subse e2 exp x)
  | choC e1 e2 => choC (SEP_exp_subse e1 exp x) (SEP_exp_subse e2 exp x)
  | loopC e' => loopC (SEP_exp_subse e' exp x)
  end
.

Compute @ { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }.
Compute SEP_exp_subse ( @ { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }) z x. 
Compute SEP_exp_subse ( @ { c ! x '+ 5 | x :=' 5 '* x '+ 3 '/ y }) (z '- 2) x. 

Fixpoint cdl_subsE (e : CDL_exp) (E : E_exp) (x : Var) : CDL_exp := (* e[E // x] *)
    match e with
    | cdl_trueC => cdl_trueC
    | cdl_ltC e1 e2 => cdl_ltC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
    | cdl_box1C p r => match (E_2_e E) with 
                        | compC exp => cdl_box1C (SEP_exp_subse p exp x) r
                        | noCompC => cdl_box1C p r
                       end
    | cdl_box2C p e' => match (E_2_e E) with 
                          | compC exp => cdl_box2C (SEP_exp_subse p exp x) (cdl_subsE e' E x)
                          | noCompC => cdl_box2C p e'
                        end
    | cdl_negC e' => cdl_negC (cdl_subsE e' E x)
    | cdl_andC e1 e2 => cdl_andC (cdl_subsE e1 E x) (cdl_subsE e2 E x)
    | cdl_forallC x1 e' => if (eqv x1 x) then cdl_forallC x1 e' else cdl_forallC x1 (cdl_subsE e' E x) 
    | cdl_falseC => cdl_falseC
    | cdl_lteC e1 e2 => cdl_lteC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
    | cdl_gtC e1 e2 => cdl_gtC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
    | cdl_gteC e1 e2 => cdl_gteC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
    | cdl_eqC e1 e2 => cdl_eqC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
    | cdl_dia1C p r => match (E_2_e E) with 
                        | compC exp => cdl_dia1C (SEP_exp_subse p exp x) r
                        | noCompC => cdl_dia1C p r
                       end
    | cdl_dia2C p e' => match (E_2_e E) with 
                          | compC exp => cdl_dia2C (SEP_exp_subse p exp x) (cdl_subsE e' E x)
                          | noCompC => cdl_dia2C p e'
                        end
    | cdl_orC e1 e2 => cdl_orC (cdl_subsE e1 E x) (cdl_subsE e2 E x)
    | cdl_impC e1 e2 => cdl_impC (cdl_subsE e1 E x) (cdl_subsE e2 E x)
    | cdl_existsC x1 e' => if (eqv x1 x) then cdl_existsC x1 e' else cdl_existsC x1 (cdl_subsE e' E x) 
  end.

Notation "e [ E 'subs' x ]" := (cdl_subsE e E x) (at level 9).
Check [ skip ]' c1 << c2 .
Locate "/".
Locate "//".

Compute [ y '> 1 ? { x :=' x '+ 1 }; skip ; @ { x :=' x '+ 1 }]' c1 << c2.
Compute ([ y '> 1 ? { x :=' x '+ 1 }; skip ; @ { x :=' x '+ 1 }]' c1 << c2) [ y subs x ] .
Compute ([ y '> 1 ? { x :=' x '+ 1 }; skip ; @ { x :=' x '+ 1 }]' c1 << c2) [ (y +' 1) subs x ] .
Compute ([ x '> 1 ? { x :=' x '+ 1 }; skip ; @ { x :=' x '+ 1 }] x =' y +' 2) [ (y +' 2) subs x ] .


(* substitution for list *)
Fixpoint cdl_subsE_l (T : list CDL_exp) (E : E_exp) (x : Var) : list CDL_exp := (* T [x' // x] *)
  match T with
  | nil => nil
  | e :: T' => (cdl_subsE e E x) :: (cdl_subsE_l T' E x)
  end.

Notation "T [ E 'subs-l' x ]" := (cdl_subsE_l T E x) (at level 9).


(* ----------------------------------- check if a substitution is admissible --------------------------------- *)
(*** DEL
Fixpoint commonEle (v1 : list Var) (v2 : list Var) : bool :=
  match v1 with
  | nil => false
  | e :: v1' => if (NotIn_bool e v2) then commonEle v1' v2 else true
  end.

Compute commonEle (x :: y :: nil) (z :: nil).
Compute commonEle (x :: y :: nil) (z :: y :: nil).

Fixpoint E_exp_chk (e : E_exp) (ev : list Var) (x : Var) (bv : list Var) : Prop := 
  match e with
  | EvarC v => if (eqv v x) and (commonEle ev bv) then false else true
  | ECntClkC c => true
  | EStClkC c => true
  | EnumC n => EnumC n
  | EplusC e1 e2 => EplusC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
  | EmulC e1 e2 => EmulC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
  | EminusC e1 e2 => EminusC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
  | EdivC e1 e2 => EdivC (E_exp_subsE e1 E x) (E_exp_subsE e2 E x)
  end
.

Fixpoint SEP_chk (p : SEP_exp) (ev : list Var) (x : Var) (bv : list Var) : Prop :=
  match p with 
  | skip => True
  | evtC evt => evtC (Evt_chk evt exp x)
  | tstC P evt => tstC (P_exp_subse P exp x) (Evt_subse evt exp x) 
  | seqC e1 e2 => seqC (SEP_exp_subse e1 exp x) (SEP_exp_subse e2 exp x)
  | choC e1 e2 => choC (SEP_exp_subse e1 exp x) (SEP_exp_subse e2 exp x)
  | loopC e' => loopC (SEP_exp_subse e' exp x)
  end
.

Fixpoint cdl_chk (e : CDL_exp) (ev : list Var) (x : Var) (bv : list Var) : Prop := 
    match e with
    | cdl_trueC => True
    | cdl_ltC e1 e2 => (E_exp_chk e1 ev x bv) /\ (E_exp_chk e2 ev x bv)
    | cdl_box1C p r => SEP_chk p ev x bv
    | cdl_box2C p e' => (SEP_chk p ev x bv) /\ (cdl_chk e' ev x (bv ++ (SEP_BV p nil)))
    | cdl_negC e' => cdl_chk e' ev x bv
    | cdl_andC e1 e2 => (cdl_chk e1 ev x bv) /\ (cdl_chk e2 ev x bv)
    | cdl_forallC x1 e' => cdl_chk e' ev x (x1 :: bv)
    | cdl_falseC => True
    | cdl_lteC e1 e2 => (E_exp_chk e1 ev x bv) /\ (E_exp_chk e2 ev x bv)
    | cdl_gtC e1 e2 => (E_exp_chk e1 ev x bv) /\ (E_exp_chk e2 ev x bv)
    | cdl_gteC e1 e2 => (E_exp_chk e1 ev x bv) /\ (E_exp_chk e2 ev x bv)
    | cdl_eqC e1 e2 => (E_exp_chk e1 ev x bv) /\ (E_exp_chk e2 ev x bv)
    | cdl_dia1C p r => SEP_chk p ev x bv
    | cdl_dia2C p e' => (SEP_chk p ev x bv) /\ (cdl_chk e' ev x (bv ++ (SEP_BV p nil)))
    | cdl_orC e1 e2 => (cdl_chk e1 ev x bv) /\ (cdl_chk e2 ev x bv)
    | cdl_impC e1 e2 => (cdl_chk e1 ev x bv) /\ (cdl_chk e2 ev x bv)
    | cdl_existsC x1 e' => cdl_chk e' ev x (x1 :: bv)
    end.
***)
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


Reserved Notation "{ T , p1 ==> p2 , D & FV }" (at level 75).
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
where "{ T , p1 ==> p2 , D & FV }" := (tstSeq2 T p1 p2 D FV)
.

Theorem thm2 : { ((y =' 1):: nil) , empty ==> exp ([ @ {y :=' y '+ z | y :=' y '+ 1}] y >' 2) , nil & 
                (y :: z :: nil) }.
Proof. 
apply tst2. cbv.
apply tst2. cbv.
apply tst3. cbv.
Abort.
*)



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

(* currently we do not consider the other direction of the rules and rules for the dual operator of `[p]'. *)
Inductive Seq : Gamma -> place -> place -> Delta -> (list Var) -> Prop :=
  (* ****************************** rules for atomic events and formula [p]rel *********************** *)
(* Rule (Phi) *)
  r_Phi_all_int1 : forall (T : Gamma) (D : Delta) (FV : list Var) (x : Var) (e : e_exp) (A : Evt) (phi : CDL_exp), 
          let n := NewId FV in 
          (
            Seq ((x =' (e_2_E e) [(var n) subs-E x]) :: (T [ (var n) subs-l x ])) 
                      empty 
                        (exp ([ @ A ] phi)) 
                          (D [ (var n) subs-l x ]) 
                            (var n :: FV)
          )
          ->
          (
            Seq T empty (exp ([ @ ((x :=' e) :: A) ] phi)) D FV
          )
|

  r_Phi_all_int2 : forall (T : Gamma) (D : Delta) (FV : list Var) (phi : CDL_exp), 
          (
            Seq T empty (exp phi) D FV
          ) 
          -> 
          (
            Seq T empty (exp ([ @ idle ] phi)) D FV
          )
|

(* Rule (Pi) *)
  r_Pi_all_int1 : forall (T : Gamma) (D : Delta) (FV : list Var) (x : Var) (e : e_exp) (A : Evt) (r : rel), 
          let n := NewId FV in 
          (
            Seq ((x =' (e_2_E e) [(var n) subs-E x]) :: (T [ (var n) subs-l x ])) 
                      empty 
                        (exp ([ @ A ]' r)) 
                          (D [ (var n) subs-l x ]) 
                            (var n :: FV)
          )
          ->
          (
            Seq T empty (exp ([ @ ((x :=' e) :: A) ]' r)) D FV
          )
|
  r_Pi_all_int2 : forall (T : Gamma) (D : Delta) (FV : list Var) (r : rel), 
          (
            Seq T empty (exp (hbar r)) D FV
          ) 
          -> 
          (
            Seq T empty (exp ([ @ idle ]' r)) D FV
          )
|

(* Rule P? *)
  r_Test_all_phi_int : forall (T : Gamma) (D : Delta) (FV : list Var) (P : P_exp) (A : Evt) (phi : CDL_exp), 
          (
            Seq T empty (exp ((Pexp_2_CDLexp P) ->' [ @ A ] phi )) D FV
          )
          ->
          (
            Seq T empty (exp ([ P ? A ] phi)) D FV
          )
|
  r_Test_all_rel_int : forall (T : Gamma) (D : Delta) (FV : list Var) (P : P_exp) (A : Evt) (r : rel), 
          (
            Seq T empty (exp ((Pexp_2_CDLexp P) ->' [ @ A ]' r )) D FV
          )
          ->
          (
            Seq T empty (exp ([ P ? A ]' r)) D FV
          )
|

(* Rule \pi\epsilon *)
  r_PiEp_all_int : forall (T : Gamma) (D : Delta) (FV : list Var) (r : rel), 
          (
            Seq T empty ( exp (tt') ) D FV
          )
          ->
          (
            Seq T empty (exp ([ skip ]' r)) D FV
          )
|

(* Rule \epsilon *)
  r_Ep_all_int : forall (T : Gamma) (D : Delta) (FV : list Var) (phi : CDL_exp), 
          (
            Seq T empty ( exp phi ) D FV
          )
          ->
          (
            Seq T empty (exp ([ skip ] phi)) D FV
          )
|

(* Rule \pi[;] *)
  r_PiSeq_all_int : forall (T: Gamma) (D : Delta) (FV : list Var) (p : SEP_exp) (q : SEP_exp) (r : rel),
          (
            Seq T empty
                    (exp ([ p ]' r /\' [ p ] ([ q ]' r)))
                      D FV
          )
          ->
          (
            Seq T empty (exp ([ p;q ]' r)) D FV
          )
|

(* Rule \pi[\cup] *)
  r_PiCho_all_int : forall (T: Gamma) (D : Delta) (FV : list Var) (p : SEP_exp) (q : SEP_exp) (r : rel),
          (
            Seq T empty
                    (exp ([ p ]' r /\' [ q ]' r))
                      D FV
          )
          ->
          (
            Seq T empty (exp ([ p U q ]' r)) D FV
          )
|

(* Rule \pi[*]u *)
  r_PiLoopU_all_int : forall (T: Gamma) (D : Delta) (FV : list Var) (p : SEP_exp) (r : rel),
          (
            Seq T empty
                    (exp ([ p ; p ** ]' r))
                      D FV
          )
          ->
          (
            Seq T empty (exp ([ p ** ]' r)) D FV
          )
|

(* Rule \pi[*]i *)
  r_PiLoopI_all_int : forall (T: Gamma) (D : Delta) (FV : list Var) (p : SEP_exp) (r : rel),
          (
            Seq T empty
                    (exp ([ p ** ] ([ p ]' r)))
                      D FV
          )
          ->
          (
            Seq T empty (exp ([ p ** ]' r)) D FV
          )
|

(* ****************************** rules for formula [p]\phi inherited from FODL *********************** *)
(* Rule [;] *)
  r_Seq_all_int : forall (T: Gamma) (D : Delta) (FV : list Var) (p : SEP_exp) (q : SEP_exp) (phi : CDL_exp),
          (
            Seq T empty
                    (exp ([ p ] ([ q ] phi)))
                      D FV
          )
          ->
          (
            Seq T empty (exp ([ p ; q ] phi)) D FV
          )
|

(* Rule [U] *)
  r_Cho_all_int : forall (T: Gamma) (D : Delta) (FV : list Var) (p : SEP_exp) (q : SEP_exp) (phi : CDL_exp),
          (
            Seq T empty
                    (exp ([ p ] phi /\' [ q ] phi))
                      D FV
          )
          ->
          (
            Seq T empty (exp ([ p U q ] phi)) D FV
          )
|

(* Rule [*]u *)
  r_LoopU_all_Int : forall (T: Gamma) (D : Delta) (FV : list Var) (p : SEP_exp) (phi : CDL_exp),
          (
            Seq T empty
                    (exp (phi /\' [ p ; p ** ] phi))
                      D FV
          )
          ->
          (
            Seq T empty (exp ([ p ** ] phi)) D FV
          )
|

(*** here we also omit the rules ([]gen), (<>gen), ([*]ind), (<*>con) temporally since we actually do NOT 
need them for derivatiion, they are just necessary for the relative completeness of the proof system. ***)

(* Rule [*]i *)
  r_LoopI_all : forall (T : Gamma) (D : Delta) (FV : list Var) (p : SEP_exp) (phi : CDL_exp), 
          (
            exists (inv : CDL_exp), (* invariant has to be manually provided *)
              (
                Seq T empty (exp inv) D (FV ++ (cdl_FV inv nil))
              )
              /\
              (
                Seq nil empty 
                          (exp (inv ->' [ p ] inv))
                            nil
                              (cdl_FV (inv ->' [ p ] inv) nil)
              )
              /\
              (
                Seq nil empty 
                          (exp (inv ->' phi))
                            nil
                              (cdl_FV (inv ->' phi) nil)
              )
          )
          ->
          (
            Seq T empty 
                    (exp ([ p ** ] phi)) D FV
          )
|

(* Rule <*>i *)
  r_LoopI_dia : forall (T : Gamma) (D : Delta) (FV : list Var) (p : SEP_exp) (phi : CDL_exp), 
          (
            exists (inv : E_exp -> CDL_exp), (* invariant has to be manually provided *)
              (
                let X := var (NewId (FV ++ (cdl_FV_f inv nil))) in 
                (
                Seq T empty 
                        (exp (ext X , (X >=' 0 /\' (inv X))))
                            D 
                              (FV ++ (cdl_FV (ext X , (X >=' 0 /\' (inv X))) nil))
                )
              )
              /\
              (
                let X := var (NewId (cdl_FV_f inv nil)) in
                (
                Seq nil empty 
                          (exp (
                                  all X, X >' 0 ->' ((inv X) ->' << p >> (inv (X -' 1)))
                               )
                          )
                            nil
                              (cdl_FV (all X, X >' 0 ->' ((inv X) ->' << p >> (inv (X -' 1)))) nil)
                )
              )
              /\
              (
                let X := var (NewId (cdl_FV_f inv nil)) in
                (
                Seq nil empty
                          (exp (
                                  ext X, X <=' 0 /\' ((inv X) ->' phi)
                               )
                          )
                            nil
                              (cdl_FV (ext X, X <=' 0 /\' ((inv X) ->' phi)) nil)
                )
              )
          )
          ->
          (
            Seq T empty 
                    (exp (<< p ** >> phi)) D FV
          )
|

(* ****************************** rules of FOL *********************** *)
(* Rule (o) *)
  r_o_int : forall (T : Gamma) (D : Delta) (FV : list Var),
        (
          let fof := (Seq_2_CDLexp T empty empty D) in 
          (
            forall (st : state), (CDLexp_2_Prop fof st)
            (* the Prop formula corresponding to the sequent: `Seq T empty empty D FV' *)
          )
        )
        ->
        (
          Seq T empty empty D FV
        )
|

(* Rule (ax) *)
  r_ax_int : forall (T : Gamma) (D : Delta) (FV : list Var) (phi : CDL_exp), 
        (
          True
        )
        ->
        (
          Seq T (exp phi) (exp phi) D FV
        )
|

(* Rule (cut) *)
  r_cut_int : forall (T : Gamma) (D : Delta) (FV : list Var), 
        (
          forall (phi : CDL_exp),
            (
              Seq T empty (exp phi) D (FV ++ (cdl_FV phi nil))
            )
            /\
            (
              Seq T (exp phi) empty D (FV ++ (cdl_FV phi nil))
            )
        )
        ->
        (
          Seq T empty empty D FV
        )
|

(* Rule (~ r) *)
  r_negR_int : forall (T : Gamma) (D : Delta) (FV : list Var) (phi : CDL_exp),
        (
          Seq T (exp (~' phi)) empty D FV
        )
        ->
        (
          Seq T empty (exp phi) D FV
        )
|

(* Rule (~ l) *)
  r_negL_int : forall (T : Gamma) (D : Delta) (FV : list Var) (phi : CDL_exp),
        (
          Seq T empty (exp (~' phi)) D FV
        )
        ->
        (
          Seq T (exp phi) empty D FV
        )
|

(* Rule (/\ r) *)
  r_andR_int : forall (T : Gamma) (D : Delta) (FV : list Var) (phi1 : CDL_exp) (phi2 : CDL_exp),
        (
          (
            Seq T empty (exp phi1) D FV
          )
          /\
          (
            Seq T empty (exp phi2) D FV
          )
        )
        ->
        (
          Seq T empty (exp (phi1 /\' phi2)) D FV
        )
|

(* Rule (/\ l) *)
  r_andL_int : forall (T : Gamma) (D : Delta) (FV : list Var) (phi1 : CDL_exp) (phi2 : CDL_exp),
        (
          Seq (phi2 :: T) 
                (exp phi1) empty D FV
        )
        ->
        (
          Seq T (exp (phi1 /\' phi2)) empty D FV
        )
|

(* Rule (all r) *)
  r_allR_int : forall (T : Gamma) (D : Delta) (FV : list Var) (phi : CDL_exp) (x : Var),
        (
          let n := NewId FV in
          (
            Seq T empty 
                    (
                      exp (phi [(var n) subs x])
                    )
                        D 
                          ((var n) :: FV)
          )
        )
        ->
        (
          Seq T empty (exp (all x , phi)) D FV
        )
|

(* Rule (all l) *)

  r_allL_int : forall (T : Gamma) (D : Delta) (FV : list Var) (phi : CDL_exp) (x : Var),
        (
          exists (E : E_exp),
          (
            Seq (all x , phi) :: T 
                    (
                      exp (phi [E subs x])
                    )
                      empty
                        D
                          (FV ++ (cdl_FV phi nil))
          )
        )
        ->
        (
          Seq T (exp (all x , phi)) empty D FV
        )

(* define the notation at the end *)
where "{ T , p1 ==> p2 , D & FV }" := (Seq T p1 p2 D FV)
.


Theorem tst1 : { nil, (exp tt') ==> (exp tt') , nil & nil }.
Proof.
apply r_ax_int.
auto.
Qed.

Theorem tstThm1 : { ((y =' 1):: nil) , empty ==> exp ([ @ {y :=' y '+ z | y :=' y '+ 1}] y >' 2) , nil & 
                (y :: z :: nil) }.
Proof. 
apply r_Phi_all_int1. cbv.
apply r_Phi_all_int1. cbv.
apply r_Phi_all_int2. cbv.
Abort.



