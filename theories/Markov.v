Require Import SsrExport.
Require Import Trace.
Require Import Language. 
Require Import Assert. 
Require Import Semax.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma imp_andT: forall p q0 q1,
p =>> q0 -> p =>> q1 -> p =>> (q0 andT q1).
Proof. 
move => [p hp] [q0 hq0] [q1 hq1] h0 h1 tr0 h2.
simpl in h2. simpl. split. 
apply h0. done. apply h1. done. 
Qed.

Variable B: nat -> Prop. 
Axiom B_noncontradictory: (forall n, B n -> False) -> False.
Variable x: id.

CoInductive cofinally: nat -> trace -> Prop :=
| cofinally_nil: forall n st,
  st x = n -> B n -> cofinally n (Tcons st (Tnil st))
| cofinally_delay: forall n st tr,
  cofinally (S n) tr ->
  st x = n -> (B n -> False) -> cofinally n (Tcons st (Tcons st tr)).

Lemma cofinally_setoid: forall n tr0, cofinally n tr0 ->
forall tr1, bisim tr0 tr1 -> cofinally n tr1. 
Proof. 
cofix COINDHYP. move => n tr0 h0 tr1 h1. foo h0. 
- foo h1. foo H3. have := cofinally_nil (refl_equal (st x)) H0; apply. 
- foo h1. foo H4. 
  have := cofinally_delay (COINDHYP _ _ H _ H5) (refl_equal (st x)) H1. 
  apply. 
Qed. 

Definition Cofinally (n: nat): assertT. 
exists (fun tr => cofinally n tr).
move => tr0 h0 tr1 h1. simpl. simpl in h0. 
have := cofinally_setoid h0 h1. apply. 
Defined.

(* Lemma 5.2 *)
Lemma Cofinally_correct: 
Cofinally 0 =>> (ttT *** [| fun st => B (st x) |]).
Proof. 
move => tr0 h0. simpl in h0. simpl. exists tr0. split; first done. 
have: forall n tr, cofinally n tr -> 
follows (singleton (fun st => B (st x))) tr tr. 
* clear h0. cofix hcoind. move => n tr h0. foo h0. 
  - apply follows_delay. apply follows_nil => //. exists st. 
    by split; [done | apply bisim_reflexive].
  - have := follows_delay _ (follows_delay _ (hcoind _ _ H)).
    by apply. 
apply. apply h0. 
Qed.

(* Lemma 5.1: cofinally 0 is stronger than nondivergent. *)
Lemma Cofinally_negInfinite: Cofinally 0 =>>  negT Infinite.
Proof.
move => tr0 h0 h1. simpl in h0. 
have h2: forall n, exists tr : trace, (cofinally n tr) /\ (infinite tr).
* move => n. induction n. 
  - exists tr0. by split. 
  - move: IHn => [tr1 [h2 h3]].  foo h2. foo h3. foo H1. 
    foo h3. foo H2. exists tr. by split. 
apply B_noncontradictory. move => n. induction n. 
- move => h3. foo h0. foo h1. by foo H2.
  have := H1 h3. by apply. 
- move => h3. have [tr1 [h4 h5]] := h2 (S n). foo h4. foo h5. 
  foo H2. have := H1 h3. apply. 
Qed.


Variable cond: expr.
Axiom cond_true: forall st, eval_true cond st -> (B (st x) -> False).
Axiom cond_false: forall st, eval_false cond st -> (B (st x)). 

Lemma plus_S: forall n,
n + 1 = S n. 
Proof. 
move => n; by lia. 
Qed. 

(* Proposition 5.1 *)
Lemma Markov_search:
semax ttS (x <- (fun _ => 0) ;; Swhile cond (x <- (fun st => (st x) + 1))) 
((ttT *** [|fun st => B (st x)|]) andT negT Infinite).
Proof.
have hs0: semax ttS (x <- (fun _ => 0)) 
((Updt ttS x (fun _ => 0)) *** [| fun st => st x = 0 |]).
* have := semax_conseq_R _ (semax_assign _ _ _). apply. 
  move => tr. simpl. move => h0. exists tr. split => //. 
  foo h0. destruct H as [_ h0]. foo h0. foo H1.
  apply follows_delay. apply follows_nil => //. 
  exists (update x 0 x0). split => //. rewrite /update.
  have h: Zeq_bool x x = true. by rewrite -Zeq_is_eq_bool.
  by rewrite h. by apply bisim_reflexive.     
have hs1: semax (fun st => st x = 0)  (Swhile cond (x <- (fun st => (st x) + 1))) 
((ttT *** [|fun st => B (st x)|]) andT negT Infinite).
set u0 := fun st => st x = 0. 
set a0 := (fun st => (st x) + 1).
pose u1 := ttS andS eval_true cond. 
have h0 := semax_assign u1 x a0.
have h1 : (Updt u1 x a0) =>> ((Updt u1 x a0)  *** [|ttS|]).
* clear h0. move => tr0 h0. exists tr0. split; first done. 
  clear h0. move: tr0. cofix hcoind. case. 
  - move => st0. apply follows_nil => //. 
    have := mk_singleton_nil; apply. done. 
  - move => st0 tr0; have := follows_delay _ (hcoind _); by apply. 
have h2 := semax_conseq_R h1 h0 => {h0 h1}.
have h0: u0 ->> ttS; first done. 
have h1 := semax_while h0 h2 => {h0 h2}.
have h0: ((<< u0 >>) ***
        Iter (Updt u1 x a0 *** (<< ttS >>)) *** ([|eval_false cond|]))
=>> Cofinally 0. 
* clear h1. move => tr0 [tr1 [h0 h1]]. simpl. move: h0 => [st0 [h0 h2]]. 
  foo h2. foo H1. foo h1. foo H2. 
  have h1: forall n st tr, hd tr x = n ->
  hd tr = st -> 
  append (iter (append (updt u1 x a0) (dup ttS)))
  (singleton (eval_false cond)) tr ->
  cofinally n (Tcons st tr). 
  * cofix hcoind. clear H1 h0. move => n st0 tr0 h h0 [tr1 [h1 h2]]. foo h1. 
    - foo h2. move: H1 => [st0 [h0 h1]]. foo h1. simpl. 
      apply cofinally_nil. done. have := cond_false h0; apply. 
    - move: H => [tr2 [h0 h1]]. move: h0 => [st0 [h0 h3]].
      foo h3. foo H2. foo h1. foo H3. foo H0. foo h2. 
      move: H2 => [st1 [h1 h2]]. foo h2. foo H2. simpl in H1.
      simpl. foo H5. foo H3. clear h1. foo H4.
      have h1: hd tr'1 = (update x (a0 st0) st0).
      * rewrite -H0. symmetry. by have := follows_hd H5; apply.  
      have h2: hd tr'1 x = S (st0 x).
      * rewrite h1. rewrite /update.
        have h2: Zeq_bool x x = true. rewrite -Zeq_is_eq_bool.
        done. rewrite h2 => {h2}. rewrite /a0. by apply plus_S.
      have h3: (append (iter (append (updt u1 x a0) (dup ttS)))
      (singleton (eval_false cond))) tr'1.
      * exists tr'0. by split.       
      have := cofinally_delay (hcoind _ _ _ h2 h1 h3) => {h1 h2 h3}.
      apply. done. move: h0 => [_ h0]. have := cond_true h0. apply.
      have := h1 _ _ _ _ _ H1 => {h1 H1}. apply.
      rewrite /u0 in h0. done. done. 
have h2 := semax_conseq_R h0 h1 => {h0 h1}.
have h0 := imp_andT Cofinally_correct Cofinally_negInfinite. 
have := semax_conseq_R h0 h2 => {h2 h0}. apply.
have := semax_seq hs0 hs1 => {hs0 hs1}. move => hs. 
have := semax_conseq_R _ hs. apply.
move => tr0. simpl. move => [tr1 [h0 h1]]. destruct h0 as [st0 [h0 h2]]. 
foo h2. foo H1. clear h0. foo h1. foo H2. destruct H1 as [h0 h1]. split. 
destruct h0 as [tr0 [_ h2]]. exists (Tcons st0 tr'). split => //. 
apply follows_delay. have h0 := follows_singleton h2. 
have := follows_setoid (@singleton_setoid _) h2 h0 (bisim_reflexive _).
done. move => h2. foo h2. have := h1 H1. done. 
Qed.
