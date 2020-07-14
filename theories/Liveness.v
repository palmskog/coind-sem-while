Require Import SsrExport.
Require Import Trace.
Require Import Language. 
Require Import Assert. 
Require Import Semax.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Variable x : id.
Variable tt : expr.
Axiom tt_true : forall st, is_true (tt st) = true.

Definition incr_x : expr := fun st => st x + 1.

Lemma update_x_incr_x : forall st,
 update x (incr_x st) st x = st x + 1.
Proof. by rewrite /update Nat.eqb_refl. Qed.

Inductive eventually_x_is_n (n: nat) : trace -> Prop :=
| x_is_n_nil: forall st, st x = n -> eventually_x_is_n n (Tnil st)
| x_is_n_cons: forall st tr, st x = n -> eventually_x_is_n n (Tcons st tr)
| x_is_n_delay: forall st tr, 
  eventually_x_is_n n tr -> eventually_x_is_n n (Tcons st tr).

Lemma eventually_x_is_n_setoid: forall n tr,
 eventually_x_is_n n tr -> forall tr0, bisim tr tr0 ->
 eventually_x_is_n n tr0.
Proof. 
induction 1. 
- move => tr0 h0. foo h0. apply x_is_n_nil => //. 
- move => tr0 h0. foo h0. apply x_is_n_cons => //.
- move => tr0 h0. foo h0. apply x_is_n_delay. 
  have := IHeventually_x_is_n _ H3. done. 
Qed.

Definition Eventually_x_is_n (n:nat): assertT. 
exists (eventually_x_is_n n). 
move => tr0 h0 tr1 h1. exact: (eventually_x_is_n_setoid h0 h1).
Defined.

Definition x_is_zero : assertS := fun st => st x = 0.

(*
x := 0; while true (x := x + 1)
*)

Definition s : stmt := x <- (fun _ => 0);; Swhile tt (x <- incr_x).

(* Proposition 5.2 *)
Lemma prg_spec: forall (n:nat), semax ttS s (Eventually_x_is_n n).
Proof. 
move => n.
have hs0: semax ttS (x <- (fun _ => 0))
(Updt ttS x (fun _ => 0) *** [| x_is_zero |]).
* have := semax_conseq_R _ (semax_assign _ _ _). apply.
  move => tr. simpl. move => h0. exists tr. split => //.
  foo h0. destruct H as [_ h0]. foo h0. foo H1.
  apply follows_delay. apply follows_nil => //. 
  exists (update x 0 x0). split => //. rewrite /update.
  have h: x =? x = true by apply Nat.eqb_refl.
  by rewrite /x_is_zero h. by apply bisim_reflexive.
have hs1 : semax x_is_zero (Swhile tt (x <- incr_x)) (Eventually_x_is_n n).
have h0 := semax_assign ttS x incr_x.
have h1 : (ttS andS eval_true tt) ->> ttS; first done.
have h2 : (Updt ttS x incr_x) =>> (Updt ttS x incr_x) *** [| ttS |]. 
* clear h0 h1. move => tr0 h0. exists tr0. split => //. clear h0. 
  move: tr0. cofix hcoind. case. move => st0. apply follows_nil => //. 
  have := mk_singleton_nil. apply. done. move => st0 tr0. 
  have := follows_delay _ (hcoind tr0). apply. 
have h3 := semax_conseq h1 h2 h0 => {h0 h1 h2}.
have h0 : x_is_zero ->> ttS by [].
have h1 := semax_while h0 h3 => {h0 h3}.
have h0 : ((<< x_is_zero >>) ***
 Iter (Updt ttS x incr_x *** (<< ttS >>)) *** ([|eval_false tt|])) =>>
 (Eventually_x_is_n n).
* clear h1. move => tr0 h0. move: h0 => [tr1 [h0 h1]]. move: h0 => [st0 [h0 h2]]. 
  foo h2. foo H1. foo h1. foo H2. simpl.
  have h1: forall n tr,
   append (iter (append (updt ttS x incr_x) (dup ttS)))
       (singleton (eval_false tt)) tr ->
   eventually_x_is_n (hd tr x + n) tr.
  * clear H1 h0 n tr'. move => n. induction n. 
    - case. move => st0 _. apply x_is_n_nil. simpl. by lia. 
      move => st0 tr0 _. apply x_is_n_cons. simpl. by lia.
    - move => tr0 h0. move: h0 => [tr1 [h0 h1]]. foo h0.
      foo h1. move: H1 => [st0 [h0 _]]. rewrite /eval_false in h0.
      rewrite tt_true in h0. foo h0. move: H => [tr2 [h0 h2]]. 
      move: h0 => [st0 [_ h0]]. foo h0. foo H2. foo h2. 
      foo H0. foo H3. move: H1 => [st1 [_ h2]]. foo h2. simpl in H0. 
      foo H2. foo h1. foo H4. foo H3. foo H2. simpl. apply x_is_n_delay.
      have h0 := follows_singleton H5.
      have h1: append (iter (append (updt ttS x incr_x) (dup ttS)))
       (singleton (eval_false tt)) tr'1.
      exists tr'1; split; first done.
      have := follows_setoid_R (@singleton_setoid _) H5 (bisim_symmetric h0).
      by apply. have h2 := IHn _ h1 => {h1 H5}.
      have h1: st0 x + S n = hd tr'1 x + n. 
      rewrite H0. rewrite (update_x_incr_x st0). lia. 
      rewrite h1 => {h1}. apply x_is_n_delay. 
      have := eventually_x_is_n_setoid h2 h0. by apply. 
  apply x_is_n_delay. have h2 := h1 _ _ H1 => {h1 H1}. 
  foo h0. have h0: n = hd tr' x + n by rewrite H0; lia. rewrite h0 => {h0}.
  by apply h2. 
have := semax_conseq_R h0 h1. by apply. 
have := semax_seq hs0 hs1 => {hs0 hs1}. move => hs. 
have := semax_conseq_R _ hs => {hs}. apply. move => tr0. simpl.
move => [tr1 [h0 h1]]. destruct h0 as [st0 [h0 h2]]. foo h2. foo H1.
foo h1. foo H2. by apply x_is_n_delay.
Qed.
