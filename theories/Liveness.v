Require Import SsrExport.
Require Import Trace.
Require Import Language. 
Require Import Assert. 
Require Import Semax.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Variable x: id.
Variable tt: expr.
Axiom tt_true: forall st, is_true (tt st) = true.

(*
x := 0; while true (x := x + 1)
*) 

Definition a0: expr := (fun st => st x + 1).
Axiom update_x_a0: forall st, (st x) + 1 = update x (a0 st) st x. 


Inductive n_at_x n: assertS :=
| n_at_x_intro: forall st, (st x) = n -> n_at_x n st.  

Inductive n_at_x_eventually (n: nat): trace -> Prop :=
| n_at_x_nil: forall st, st x = n -> n_at_x_eventually n (Tnil st)
| n_at_x_cons: forall st tr, st x = n -> n_at_x_eventually n (Tcons st tr)
| n_at_x_delay: forall st tr, 
  n_at_x_eventually n tr -> n_at_x_eventually n (Tcons st tr).

Lemma n_at_x_eventually_setoid: forall n tr,
n_at_x_eventually n tr -> forall tr0, bisim tr tr0 ->
n_at_x_eventually n tr0. 
Proof. 
induction 1. 
- move => tr0 h0. foo h0. apply n_at_x_nil => //. 
- move => tr0 h0. foo h0. apply n_at_x_cons => //.
- move => tr0 h0. foo h0. apply n_at_x_delay. 
  have := IHn_at_x_eventually _ H3. done. 
Qed. 

Definition Eventually (n:nat): assertT. 
exists (n_at_x_eventually n). 
move => tr0 h0 tr1 h1. have := n_at_x_eventually_setoid h0 h1. by apply. 
Defined.   
 
(*
Definition p1: assertT :=
(exT (fun n0:nat => fun tr: trace => { st0: state & { st1: state & 
 prod (bisim tr (Tcons st0 (Tnil st1))) (prod (st0 x = n0)
         (st1 x = n0 + 1))}})). 

Definition u1: assertS := (exS (fun n0 => n_at_x n0)).
*)

(* Proposition 5.2 *)
Lemma prg_spec: forall (n:nat), 
semax ttS (x <- (fun _ => 0) ;; Swhile tt (x <- a0)) (Eventually n). 
Proof. 
move => n. 
have hs0: semax ttS (x <- (fun _ => 0)) 
(Updt ttS x (fun _ => 0) *** [| n_at_x 0 |]).
* have := semax_conseq_R _ (semax_assign _ _ _). apply. 
  move => tr. simpl. move => h0. exists tr. split => //. 
  foo h0. destruct H as [_ h0]. foo h0. foo H1.
  apply follows_delay. apply follows_nil => //. 
  exists (update x 0 x0). split => //. rewrite /update.
  have h: Zeq_bool x x = true. by rewrite -Zeq_is_eq_bool.
  apply n_at_x_intro. by rewrite h. by apply bisim_reflexive.     
have hs1: semax (n_at_x 0) (Swhile tt (x <- a0)) (Eventually n).
have h0 := semax_assign ttS x a0.
have h1 : (ttS andS eval_true tt) ->> ttS; first done.   
have h2 : (Updt ttS x a0) =>> (Updt ttS x a0) *** [| ttS |]. 
* clear h0 h1. move => tr0 h0. exists tr0. split => //. clear h0. 
  move: tr0. cofix hcoind. case. move => st0. apply follows_nil => //. 
  have := mk_singleton_nil. apply. done. move => st0 tr0. 
  have := follows_delay _ (hcoind tr0). apply. 
have h3 := semax_conseq h1 h2 h0 => {h0 h1 h2}.
have h0: (n_at_x 0) ->> ttS; first done. 
have h1 := semax_while h0 h3 => {h0 h3}.
have h0:((<< n_at_x 0 >>) ***
Iter (Updt ttS x a0 *** (<< ttS >>)) *** ([|eval_false tt|])) =>>
(Eventually n).
* clear h1. move => tr0 h0. move: h0 => [tr1 [h0 h1]]. move: h0 => [st0 [h0 h2]]. 
  foo h2. foo H1. foo h1. foo H2. simpl.  
  have h1: forall n tr,           
  append (iter (append (updt ttS x a0) (dup ttS)))
       (singleton (eval_false tt)) tr ->
  n_at_x_eventually (hd tr x + n) tr.
  * clear H1 h0 n tr'. move => n. induction n. 
    - case. move => st0 _. apply n_at_x_nil. simpl. by lia. 
      move => st0 tr0 _. apply n_at_x_cons. simpl. by lia.
    - move => tr0 h0. move: h0 => [tr1 [h0 h1]]. foo h0.
      foo h1. move: H1 => [st0 [h0 _]]. rewrite /eval_false in h0.
      rewrite tt_true in h0. foo h0. move: H => [tr2 [h0 h2]]. 
      move: h0 => [st0 [_ h0]]. foo h0. foo H2. foo h2. 
      foo H0. foo H3. move: H1 => [st1 [_ h2]]. foo h2. simpl in H0. 
      foo H2. foo h1. foo H4. foo H3. foo H2. simpl. apply n_at_x_delay.
      have h0 := follows_singleton H5.
      have h1: append (iter (append (updt ttS x a0) (dup ttS)))
      (singleton (eval_false tt)) tr'1. exists tr'1. 
      split; first done. 
      have := follows_setoid_R (@singleton_setoid _) H5 (bisim_symmetric h0).
      by apply. have h2 := IHn _ h1 => {h1 H5}.
      have h1: st0 x + S n = hd tr'1 x + n. 
      rewrite H0. rewrite -(update_x_a0 st0). lia. 
      rewrite h1 => {h1}. apply n_at_x_delay. 
      have := n_at_x_eventually_setoid h2 h0. by apply. 
  apply n_at_x_delay. have h2 := h1 _ _ H1 => {h1 H1}. 
  foo h0. have h0: n = hd tr' x + n by rewrite H; lia. rewrite h0 => {h0}.
  by apply h2. 
have := semax_conseq_R h0 h1. by apply. 
have := semax_seq hs0 hs1 => {hs0 hs1}. move => hs. 
have := semax_conseq_R _ hs => {hs}. apply. move => tr0. simpl. 
move => [tr1 [h0 h1]]. destruct h0 as [st0 [h0 h2]]. foo h2. foo H1. 
foo h1. foo H2. apply n_at_x_delay. done. 
Qed.
