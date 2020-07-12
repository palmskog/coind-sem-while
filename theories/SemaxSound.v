Require Import SsrExport. 
Require Import Trace.
Require Import Language. 
Require Import BigRel.
Require Import BigFunct.
Require Import Assert.
Require Import Semax.
 
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Proposition 3.3: Soundness *)
Lemma semax_sound: forall u s p,
semax u s p -> forall st tr, exec s st tr -> u st -> satisfy p tr.
Proof.
induction 1 => st0 tr0 hexec hu. 
- exists st0. foo hexec. by split; [done | reflexivity].  
- foo hexec. exists st0. by split; [done | reflexivity]. 
- foo hexec. have h1 := IHsemax1 _ _ H3 hu.
  destruct p1 as [f1 hf1]. destruct p2 as [f2 hf2]. clear H H0. simpl in IHsemax1. 
  simpl in IHsemax2. simpl in h1. simpl. exists tr. split.
  * have := (@append_singleton f1 hf1 v _ h1). apply.  
  * clear st0 hu H3. move: h1 => [tr1[_ h1]]. 
     have h0 := follows_singleton h1. 
     have h2 := follows_setoid_L h1 h0 => {h0 h1}. 
     clear IHsemax1 tr1. move: tr tr0 h2 H6. cofix COINDHYP. 
     move => tr0 tr1 h0 h1. foo h1. 
     - inversion h0. clear H3 H1 H0. move: H2 => [st1 [h1 h2]].
        foo h2. have h2 := exec_hd H. 
       apply follows_nil => //. have := IHsemax2 _ _ H h1. apply. 
     - foo h0. have := follows_delay e (COINDHYP _ _ H1 H). apply.   
- destruct p as [f hf]. exists (Tcons st0 (Tnil st0)). foo hexec.
 * foo H7. foo H5. split. 
  * exists st0. by split; [done | reflexivity].  
  * apply: follows_delay. have h0 := exec_hd H3. apply follows_nil => //.  
  * have h1: (u andS eval_true a) st0; first by split.   
    have := IHsemax1 _ _ H3 h1; by apply.
 * foo H7.  foo H5. split. 
   * exists st0. by split; [done | reflexivity].  
   * apply: follows_delay. have h0 := exec_hd H3. apply follows_nil => //.  
  * have h1: (u andS eval_false a) st0; first by split.   
    have := IHsemax2 _ _ H3 h1; by apply.
- clear H0. destruct p as [p hp]. simpl in IHsemax. simpl.   
  have h0: forall st, u st -> forall tr, exec (Swhile a s) st (Tcons st tr) ->
  (iter (append p (dup u))) tr.  
  cofix COINDHYP0.
  have h: forall tr0 tr1, follows (singleton u) tr0 tr0 -> execseq (Swhile a s) tr0 tr1 ->
  follows (iter (append p (dup u))) (lastdup tr0) tr1.
  cofix COINDHYP1. clear H st0 tr0 hexec hu.
  * move => tr0 tr1 h0 h1. foo h1. 
    - inversion h0. clear h0 H1 H0 H3. move: H2 => [st1 [h1 h2]]. foo h2. 
      rewrite [lastdup _]trace_destr. simpl. foo H.
      - apply follows_delay. apply follows_nil. by simpl. apply iter_stop. 
      - inversion H3; subst. inversion H5; subst. inversion H6; subst. 
        apply follows_delay. apply follows_nil. 
        rewrite -(exec_hd H1). have := execseq_hd H8. apply.
        have h0 := exec_while_loop H2 H3 H6. 
        have := COINDHYP0 _ h1 _ h0; apply. 
    - rewrite [lastdup _]trace_destr. simpl. foo h0. 
      have := follows_delay e (COINDHYP1 _ _ H1 H). apply. 
  * clear H st0 tr0 hexec hu. move => st0 h0 tr0 h1. foo h1. 
    - simpl. apply iter_stop.
    - foo H2. foo H6. foo H5. have h1: (u andS eval_true a) st0; first by split; simpl. 
      have h2 := IHsemax _ _ H2 h1 => {H2 h1 h0}. simpl.
      apply (@iter_loop _ (lastdup tr')). exists tr'. split. 
      have :=  (@append_singleton p hp u _ h2). apply. 
      move: h2 => [tr1 [h2 h3]]. have h0 := follows_singleton h3. 
      have h1 := follows_setoid_L h3 h0 => {h3 h0}.
      have := follows_dup h1. apply. move: h2 => [tr1 [h2 h0]]. 
      have h3 := follows_singleton h0. have h4 := follows_setoid_L h0 h3 => {h0 h3}.
      have := h _ _ h4 H3; apply.
  have h1: forall st tr, exec (Swhile a s) st tr -> follows (singleton (eval_false a)) tr tr.
  * clear st0 tr0 hexec hu h0. 
    have h1: forall tr0 tr1, execseq (Swhile a s) tr0 tr1 ->
    follows (singleton(eval_false a)) tr1 tr1.
   * cofix COINDHYP. move => tr0 tr1 h1. foo h1. foo H0. 
     apply follows_delay. apply follows_nil. simpl. reflexivity. exists st. 
     split. apply H5. reflexivity. foo H4. foo H6. foo H7. 
     have := follows_delay st (COINDHYP _ _ H6). apply.
     have := follows_delay e (COINDHYP _ _ H0). apply. 
    move => st0 tr0 h0. foo h0. apply follows_delay. apply follows_nil. 
    simpl. reflexivity. exists st0. split. apply H4. reflexivity.
    have := h1 _ _ H6; apply.
  inversion hexec; subst.
  - exists (Tcons st0 (Tnil st0)). split. exists st0. split. apply hu. reflexivity. 
    apply follows_delay. apply follows_nil => //. exists (Tnil st0). split. 
    apply: iter_stop. apply follows_nil => //. exists st0. split. apply H4. 
    reflexivity. 
  - inversion H3; subst. inversion H7; subst. inversion H6; subst. 
    exists (Tcons st0 (Tnil st0)). split. exists st0. split. apply hu. reflexivity. 
    apply follows_delay. apply follows_nil => //.  rewrite -(exec_hd H4). 
    have := execseq_hd H9. apply. exists tr'0. split. 
    have := h0 _ (H _ hu) _ hexec. apply. 
    have h2 := h1 _ _ hexec. foo h2. apply H1.    
- have := H0 _ (IHsemax _ _ hexec (H _ hu)). apply. 
- move: hu => [x h0]. exists x.
  have := H0 _ _ _ hexec h0. apply. 
Qed.       

(* Corollary 3.1 *)
Lemma semax_total: forall S U P, 
semax U S P -> forall s, U s -> exists tr,  hd tr = s /\ satisfy P tr. 
Proof.
move => S U P hsemax s hU. 
exists (Exec S s). split.
- by apply Exec_hd.
- apply (semax_sound hsemax (Exec_correct_exec _ _) hU). 
Qed.
