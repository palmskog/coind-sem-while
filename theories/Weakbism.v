Require Import SsrExport.
Require Import Trace.
Require Import Language. 
Require Import Semax.
Require Import Assert.
Require Import AssertClassical.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma Append_ttS: forall p,
p =>> (p *** [| ttS |]). 
Proof.
move => [f hp] tr0 h0. simpl in h0. simpl. exists tr0. 
split; first done. clear h0 hp. move: tr0. cofix hcoind. 
case. move => st0. apply follows_nil => //.
by apply mk_singleton_nil. move => st0 tr0. 
have := follows_delay _ (hcoind _). by apply. 
Qed.

Variable x: id. 

Inductive red: trace -> trace -> Prop :=
| red_stop: forall st tr tr',
  st x <> hd tr x -> 
  bisim tr tr' -> 
  red (Tcons st tr) tr'
| red_tau: forall st tr tr',
  st x = hd tr x -> 
  red tr tr' -> 
  red (Tcons st tr) tr'.

Lemma red_deterministic: forall tr0 tr1, red tr0 tr1 ->
forall tr2, red tr0 tr2 -> bisim tr1 tr2. 
Proof. 
induction 1.
- move => tr0 h0. foo h0. 
  - have := bisim_transitive (bisim_symmetric H0) H5. by apply. 
  - done. 
- move => tr0 h0. foo h0. 
  - done. 
  - have := IHred _ H5. by apply. 
Qed. 

Lemma red_setoid: forall tr0 tr1, red tr0 tr1 ->
forall tr2, bisim tr0 tr2 -> forall tr3, bisim tr1 tr3 -> red tr2 tr3. 
Proof. 
induction 1. 
- move => tr0 h0 tr1 h2. foo h0. have h0 := bisim_hd H4. 
  rewrite h0 in H => {h0}.
  have := red_stop H (bisim_transitive (bisim_transitive (bisim_symmetric H4) H0) h2).
  by apply.
- move => tr0 h0 tr1 h1. foo h0. have h2 := bisim_hd H4. 
  rewrite h2 in H => {h2}. 
  have := red_tau H. apply. have := IHred _ H4 _ h1. by apply. 
Qed.
 
CoInductive up: nat -> trace -> Prop :=
| up_intro: forall st n tr0 tr1,
  st x = n ->
  red (Tcons st tr0) tr1 -> up (S n) tr1 ->
  up n (Tcons st tr0). 

Lemma up_setoid: forall n tr0, up n tr0 ->
forall tr1, bisim tr0 tr1 -> up n tr1.
Proof.
move => n tr0 h0 tr1 h1. foo h0. 
foo h1. 
have h1 := red_setoid H0 (bisim_cons st H4) (bisim_reflexive tr3).
have := up_intro (refl_equal (st x)) h1 H1.
by apply. 
Qed.

Definition Up (n:nat): assertT. 
exists (fun tr => up n tr). 
move => tr0 h0 tr1 h1.
have := up_setoid h0 h1. by apply. 
Defined.  

Inductive skips: trace -> Prop :=
| skips_nil: forall st, skips (Tnil st)
| skips_delay: forall st tr,
  skips tr -> hd tr x = st x -> skips (Tcons st tr). 

Lemma skips_setoid: forall tr0, skips tr0 -> forall tr1, bisim tr0 tr1 ->
skips tr1. 
Proof.
induction 1. 
- move => st0 h0. foo h0. by apply skips_nil.
- move => tr0 h0. foo h0. apply skips_delay. 
  have := IHskips _ H4. by apply. have h0 := bisim_hd H4.
  rewrite -h0. done. 
Qed. 

Definition Skips: assertT.
exists (fun tr => skips tr). 
move => tr0 h0 tr1 h1. simpl. 
have := skips_setoid h0 h1. by apply. 
Defined.  
 
  
Variable y: id. 
Axiom xy: Zeq_bool x y = false.   
Axiom yx: Zeq_bool y x = false.   
Variable cond: expr. (* y <> 0 *)
Axiom cond_tt: forall st, eval_true cond st -> (st y = 0 -> False).   
Axiom cond_ff: forall st, eval_false cond st -> st y = 0.  
Variable tt: expr. 
Axiom tt_true: forall st, is_true (tt st) = true. 

Definition s := 
Swhile tt 
(y <- (fun st => st x);; 
 Swhile cond (y <- (fun st => st y - 1));;
 x <- (fun st => (st x) + 1)). 

Definition u0: assertS := fun st => st x = 0.

Lemma Sn_1: forall n, S n - 1 = n. 
Proof. 
move => n. by lia.
Qed.  

Lemma Sn: forall n, n + 1 = S n. 
Proof. 
move => n. by lia.
Qed.

Require Import ClassicalEpsilon.

(* Proposition 5.3 *)
Lemma spec: semax u0 s (Up 0).
Proof. 
rewrite /s. 
pose a_t := eval_true cond.
pose a_f := eval_false cond. 
pose u_xy := fun st: state => st x = st y.      
have h0 := semax_assign (ttS andS a_t) y (fun st => st y - 1).
have h1 := semax_conseq_R (@Append_ttS _) h0 => {h0}.  
have h0: ttS ->> ttS; first done.
have h2 := semax_while h0 h1 => {h0 h1}. 
have h0: ((<< ttS >>) ***
Iter (Updt (ttS andS a_t) y (fun st : state => st y - 1) *** (<< ttS >>)) ***
[|eval_false cond|]) =>> Skips. 
* clear h2. move => tr0 h0. simpl. simpl in h0. move h1: (hd tr0 y) => n. 
  move: tr0 h1 h0. induction n. 
  - move => tr0 h0 [tr1 [h1 h2]]. move: h1 => [st0 [_ h1]]. foo h1. foo H1. 
    foo h2. simpl in h0. foo H2. move: H1 => [tr0 [h1 h2]]. foo h1. 
    - foo h2. move: H1 => [st0 [_ h1]]. foo h1. simpl. apply skips_delay. 
      by apply skips_nil. by simpl. 
    - move: H => [tr1 [h1 h3]]. move: h1 => [st0 [[_ h1] h4]].
      foo h4. foo h3. foo H0. foo h2. simpl in h0. absurd False.
      done. have := cond_tt h1 h0. by apply. 
  - move => tr0 h0 [tr1 [h1 h2]]. move: h1 => [st0 [_ h3]]. foo h3. foo H1.
    foo h2. simpl in h0. foo H2. apply skips_delay; last done. 
    move: H1 => [tr0 [h1 h2]]. foo h1. 
    - foo h2. move: H1 => [st0 [h1 h2]]. foo h2. apply skips_nil. 
    - move: H => [tr1 [h1 h3]]. move: h1 => [st0 [h1 h4]]. foo h4. foo H2. 
      foo h3. foo H0. foo H3. foo h2. simpl in h0. 
      have h2: skips tr'1. apply IHn => {IHn}. have h2 := follows_hd H4. 
      rewrite -h2 => {h2}. rewrite H0 => {H0}. rewrite h0 => {h0}. 
      rewrite /update. have h0: Zeq_bool y y = true. by rewrite -Zeq_is_eq_bool.
      rewrite h0 => {h0}. by apply Sn_1. exists tr'0. split; first done. 
      move: H1 => [st1 [_ h2]]. foo h2. simpl in H0. foo H2. foo H4.
      apply follows_delay. foo H2. foo H5. apply follows_nil => //. 
      exists tr'. split; first done. have h2 := follows_singleton H4. 
      have := follows_setoid_R (@singleton_setoid _) H4 (bisim_symmetric h2).
      by apply. apply skips_delay. have h3 := follows_singleton H5. 
      have := skips_setoid h2 h3. by apply. have h3 := follows_hd H5. 
      rewrite -h3 => {h3}. clear h2 h0 H1 H5. have h0 := follows_hd H4 => {H4}.
      rewrite -h0 => {h0}. rewrite H0 => {H0}. rewrite /update.    
      rewrite yx. done. 
have h1 := semax_conseq_R h0 h2 => {h0 h2}. 
have h0 := semax_assign ttS x (fun st => st x + 1). 
have h2 := semax_conseq_R (@Append_ttS _) h1 => {h1}.
have h1 := semax_seq h2 h0 =>  {h2 h0}.
have h0 := semax_conseq_R (@Append_ttS _) (semax_assign ttS y (fun st => st x)).
have h2 := semax_seq h0 h1 => {h0 h1}.  
have h0 := semax_conseq_R (@Append_assoc_R _ _ _) h2 => {h2}.
have h1: (Updt ttS y (fun st => st x) *** Skips) =>> Skips.
* clear h0. move => tr0 [tr1 [h0 h1]]. simpl. move: h0 => [st0 [_ h0]]. 
  foo h0. foo H1. foo h1. foo H2. apply skips_delay => //. rewrite H0. 
  rewrite /update. rewrite yx. done. 
have h2 := semax_conseq_R (Append_monotone_L h1) h0 => {h0 h1}.
have h0: u0 ->> ttS; first done. 
have h1: (ttS andS eval_true tt) ->> ttS; first done.
have h3 := semax_conseq h1 (@Append_ttS _) h2 => {h2 h1}.  
have h1 := semax_while h0 h3 => {h0 h3}.       
have h0: (<<u0>> *** Iter ((Skips *** Updt ttS x (fun st => st x + 1))
*** <<ttS>>) *** [| eval_false tt |]) =>> (Up 0). 
* clear h1. move => tr0 h0. simpl. simpl in h0. 
  move: h0 => [tr1 [h0 h1]]. move: h0 => [st0 [h0 h2]]. rewrite /u0 in h0.
  foo h2. foo H1. foo h1. foo H2. move: H1 => [tr0 [h1 h2]].  
  have: forall n tr0 tr1, hd tr1 x = n -> 
  iter (append (append (fun tr => skips tr)
  (updt ttS x (fun st => st x + 1))) (dup ttS)) tr0 -> 
  follows (singleton (eval_false tt)) tr0 tr1 -> up n (Tcons (hd tr1) tr1).
  * clear tr' h0 tr0 h1 h2. cofix hcoind. move => n tr0 tr1 h0 h1 h2. foo h1. 
    - foo h2. move: H1 => [st0 [h0 h1]]. rewrite /eval_false in h0. clear h1. 
      rewrite tt_true in h0. foo h0. 
    - move: H => [tr2 [h0 h1]]. move: h0 => [tr3 [h0 h3]].
      have h4: forall tr3, skips tr3 -> 
      forall tr2, follows (updt ttS x (fun st => st x + 1)) tr3 tr2 ->
      forall tr, follows (dup ttS) tr2 tr ->
      forall tr0, follows (iter
          (append (append (fun tr : trace => skips tr)
           (updt ttS x (fun st : state => st x + 1))) (dup ttS))) tr tr0 ->
      forall tr1, follows (singleton (eval_false tt)) tr0 tr1 ->   
      exists tr4 : trace,
      ((red (Tcons (hd tr1) tr1) (Tcons (hd tr4) tr4)) /\
        (hd tr4 x = S (hd tr1 x)) /\
        (iter (append
         (append (fun tr : trace => skips tr)
         (updt ttS x (fun st : state => (st x + 1)%nat))) (dup ttS)) tr4) /\
         (follows (singleton (eval_false tt)) tr4 tr4)).
       * clear hcoind tr0 tr1 h2 tr H0 tr2 h1 tr3 h0 h3. induction 1. 
          - move => tr0 h0 tr1 h1 tr2 h2 tr3 h3. foo h0. 
            move: H1 => [st0 [h0 h4]]. foo h4. foo h1. foo H1. clear h0. 
            foo H3. foo h2. move: H1 => [st1 [h0 h1]]. foo h1. foo H2. 
            simpl in H0. foo H4. clear h0. foo H3. foo h3. foo H4. exists tr'.
            have h0 := follows_hd H5. 
            have h1 := follows_singleton H5. 
            split. apply red_tau. by simpl.
            apply red_stop.
            simpl. rewrite /update. 
            have h: Zeq_bool x x = true; first by rewrite -Zeq_is_eq_bool.
            rewrite h => {h}. lia. rewrite H0. 
            apply bisim_cons. have := bisim_symmetric h1. by apply.
            simpl. rewrite H0. rewrite /update. have h: Zeq_bool x x = true;
            first by rewrite -Zeq_is_eq_bool. rewrite h => {h}.  split. by apply Sn. split.
            by apply H1. have := follows_setoid _ H5 _ (bisim_symmetric h1). apply.
            move => tr0 h2 tr1 h3. move: h2 => [st1 [h2 h4]]. foo h4.
            exists st1. split => //. have := bisim_symmetric h3. by apply. 
            by apply bisim_reflexive. 
          - move => tr0 h0 tr1 h1 tr2 h2 tr3 h3. foo h0. 
            have h0 := IHskips _ H4 => {IHskips}. foo h1. 
            have h1 := h0 _ H5 => {h0}. foo h2. 
            have h2 := h1 _ H6 => {h1}. foo h3. 
            have h3 := h2 _ H7 => {h2}. move: h3 => [tr0 [h3 [h0 [h1 h2]]]].
            simpl. rewrite -H0.  
            have h4 := follows_hd H4; rewrite h4 => {H4}.
            have h5 := follows_hd H5; rewrite h5  => {H5}.
            have h6 := follows_hd H6; rewrite h6  => {H6}. 
            have h7 := follows_hd H7; rewrite h7 => {H7}. 
            rewrite -h0. 
            exists tr0. split => //. clear h1 h2. 
            apply red_tau. simpl. reflexivity. foo h3. 
            absurd False. done. apply H3. reflexivity. apply red_tau. 
            rewrite -H0; rewrite h4. rewrite h5; rewrite h6; rewrite h7. 
            reflexivity. by apply H5.
     have h := h4 _ h0 _ h3 _ h1 _ H0 _ h2 => {h4 h0 h3 h1 H0 h2}. 
     move: h => [tr4 [h4 [h7 [h5 h6]]]].
     have := up_intro _ h4. apply. reflexivity. 
     have := hcoind _ _ _ _ _ h6. apply. by apply h7. apply h5. 
     move => h3. have := h3 _ _ _ h0 h1 h2. by apply. 
  have := semax_conseq_R h0 h1. by apply. 
Qed.
