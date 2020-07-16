From CoindSemWhile Require Import SsrExport Trace Language BigRel Assert Semax. 
 
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Lemma 3.3 *)
Lemma conv_follows: forall (u:assertS) tr,
 (forall st, fin tr st -> u st) ->
 follows (singleton u) tr tr.
Proof. 
move => u. cofix COINDHYP. case. 
- move => st0 h0. have h1 := h0 st0 (fin_nil st0) => {h0}.
  apply follows_nil. by simpl. simpl. exists st0. 
  by split; [done | reflexivity].
- move => st0 tr0 h0. 
  have h1: forall st, fin tr0 st -> u st. 
  * move => st1 h1. have := h0 st1 (fin_delay st0 h1) => {h0 h1}. apply. 
  have := follows_delay st0 (COINDHYP _ h1); apply. 
Qed. 

Lemma last_adequate: forall (p: trace -> Prop) tr, p tr ->
 (append p (singleton (last p))) tr.
Proof. 
move => p tr0 h1. simpl in h1. simpl. exists tr0. 
split => //. apply conv_follows. 
move => st0 h2. exists tr0.  simpl. by split. 
Qed.

Lemma Last_adequate: forall (p: assertT),
 p =>> (p *** [| Last p |]).
Proof. 
move => p tr0 h0. destruct p as [f hf].  simpl. simpl in h0. 
have := last_adequate h0. apply. 
Qed.

Inductive loopinv (a: expr) (sp: assertS -> trace -> Prop) (u:assertS) : assertS :=
| loopinv_here: forall  st, 
  u st -> 
  loopinv a sp u st
| loopinv_next: forall st tr st' (v: assertS),
  loopinv a sp u st ->
  is_true (a st) = true -> 
  hd tr = st ->
  (forall st, v st -> loopinv a sp u st) -> 
  sp v tr ->
  fin tr st' ->
  loopinv a sp u st'.

Fixpoint sp (s: stmt) (u: assertS) {struct s} : trace -> Prop :=
match s with
| Sskip => (singleton u)
| Sassign x a => (updt u x a)  
| Sseq s1 s2 =>
   append (sp s1 u) (sp s2 (last (sp s1 u))) 
| Sifthenelse a s1 s2 =>
  append (dup u)
  (fun tr => sp s1 (u andS eval_true a) tr \/ sp s2 (u andS eval_false a) tr) 
|Swhile a s =>  
  let I := loopinv a (sp s) u in 
  append (dup u) 
  (append 
   (iter (append (sp s (I andS eval_true a)) (dup I))) 
   (singleton (eval_false a)))
end.

Lemma loopinv_init: forall u e sp, u ->> loopinv e sp u.
Proof. 
move => u a sp0 st h1. by apply: loopinv_here h1. 
Qed.   

(* Lemma 3.8 *)
Lemma sp_hd: forall s u tr, sp s u tr -> u (hd tr).
Proof. 
move => s; induction s; simpl => u tr.
- move => [st [h1 h2]]. subst. foo h2. simpl. by apply h1. 
- move => [st0 [h1 h2]]. foo h2. foo H1. simpl. by apply h1. 
- move => [tr0 [h1 h2]]. 
   have h3 := IHs1 _ _ h1. 
   rewrite (follows_hd h2) in h3; by apply h3. 
- move => [tr0 [h1 h2]]. move: h1 => [st1 [h1 h3]]. foo h3.   
  foo H1. foo h2. by simpl. 
- move => [tr0 [h1 h2]]. move: h1 => [st1 [h1 h3]]. foo h3. foo H1.   
  foo h2. by simpl. 
Qed. 

Lemma loopinv_cont: forall e (sp: assertS -> trace -> Prop),
(forall u u', u ->> u' -> forall tr, sp u tr -> sp u' tr) ->
forall u u',  u ->> u' -> loopinv e sp u ->> loopinv e sp u'. 
Proof.
move => e sp0 hsp0. rewrite /assertS_imp in hsp0 *. 
move => u u' h1 . induction 1. 
- apply: loopinv_here. have := h1 _ H; apply.
- apply: loopinv_next. apply IHloopinv. apply H0. apply H1. 
  apply H3. apply H4. apply H5. 
Qed.   
 
(* Lemma 3.7: sp is monotone. *)
Lemma sp_cont: forall s u u',
 u ->> u' -> forall tr, sp s u tr -> sp s u' tr.
Proof.
move => s; induction s; simpl  => u0 u1 h1 tr0 h2; simpl.
- move: h2 => [st1 [h2 h3]]. foo h3. exists st1. split. 
  have := h1 _ h2; apply. reflexivity.  
- move: h2 => [st0 [h3 h2]]. foo h2. foo H1. exists st0. split.  
  by have := h1 _ h3; apply. reflexivity. 
- move: h2 => [tr1 [h3 h4]]. exists tr1. split. 
  * have := IHs1 _ _ h1 _ h3; apply. 
  * clear h3. move: tr1 tr0 h4. cofix COINDHYP. move => tr0 tr1 h2. 
    foo h2. 
    - apply: follows_nil; first done.       
      apply: IHs2 _ _ _ _ H0. have := (last_cont (IHs1 _ _ h1)). apply.  
    - apply: follows_delay. apply: COINDHYP. by apply: H. 
- move: h2 => [tr1 [h2 h3]]. move: h2 => [st0 [h2 h4]]. foo h4. 
  foo h3. foo H1. foo H3. exists (Tcons (hd tr') (Tnil (hd tr'))). split. 
  * exists (hd tr'). split. 
    * have := h1 _ h2; apply. 
    * reflexivity.   
  * apply: follows_delay. apply: follows_nil. 
    * done. 
    * move: H1 => [h6 | h6]. 
      - left. apply: IHs1 h6. move => st0 [h6 h7].
      split; last done; by apply: h1 h6.
    - right. apply: IHs2 h6. move => st0 [h6 h7]. 
      split; last done; by apply: h1 h6. 
- move: h2 => [tr1 [h2 h3]]. move: h2 => [st0 [h2 h4]]. foo h4.  
  foo h3. foo H1. foo H3. exists (Tcons (hd tr') (Tnil (hd tr'))). split. 
  * exists (hd tr'). split. 
    * have := h1 _ h2; apply. 
    * reflexivity.   
  * apply follows_delay. apply follows_nil. 
    * done. 
    * have h3 := loopinv_cont IHs h1. have h4 := h3 e => {h3}. 
       have h5 := dup_cont h4. 
      have h3: (loopinv e (sp s) u0 andS eval_true e) ->>
      (loopinv e (sp s) u1 andS eval_true e).
      * move => st0 [h0 h3]. split => //. have := h4 _ h0; apply.    
      have h6 := IHs _ _ h3 => {h4 h3}.
      have h3 := append_cont h6 h5 => {h6 h5}. 
      have h4 := iter_cont h3 => {h3}.
      have := append_cont_L h4 H1. apply.  
Qed.    

(* Lemma 3.11: any trace satisfying sp(s,U) is produced by a run of s. *)
Lemma sp_then_exec: forall s u tr,
sp s u  tr -> 
exec s (hd tr) tr.
Proof.
move => s; induction s; simpl. 
- move => u tr [st [h1 h2]]. foo h2. simpl. by apply: exec_skip. 
- move => u tr [st [h1 h2]]. foo h2. foo H1. simpl. apply: exec_assign. 
- move => u tr [tr0 [h1 h2]]. 
  have h3:= IHs1 _ _ h1. have h4 := follows_hd h2. 
  rewrite h4 in h3. have := exec_seq h3; apply.
  move => {h1 h4 h3}. move: tr0 tr h2. cofix COINDHYP. 
  move => tr0 tr1 h1. foo h1. 
  - apply: execseq_nil. 
    have := IHs2 _ _ H0. simpl; apply. 
  - apply: execseq_cons. by have := COINDHYP _  _ H; apply. 
- move => u tr h1. move: h1 => [tr0 [h1 h2]]. move: h1 => [st0 [h1 h3]]. 
  foo h3. foo h2. foo H1. foo H3. simpl. move: H1 => [h4 | h4].   
  - have h5 := sp_hd h4. move: h5 => [h5 h6]. 
    have := exec_ifthenelse_true _ h6; apply.
    apply: execseq_cons. apply: execseq_nil.
    have := IHs1 _ _ h4; apply.
  - have h5 := sp_hd h4. move: h5 => [h5 h6]. 
    have := exec_ifthenelse_false _ h6; apply.
    apply: execseq_cons. apply: execseq_nil.
    have := IHs2 _ _ h4; apply.
- move => u tr0 h1. move: h1 => [tr1 [h1 h2]]. move: h1 => [st0 [h1 h3]]. 
  foo h3. foo H1. foo h2. foo H2.  simpl. move => {h1}.
  move: H1 => [tr0 [h0 h1]]. move: tr' tr0 h0 h1. cofix COINDHYP.
  have h: forall tr2 tr tr1 tr0: trace, follows (dup (loopinv e (sp s) u)) tr2 tr ->
  follows
  (iter (append (sp s (loopinv e (sp s) u andS eval_true e))
          (dup (loopinv e (sp s) u)))) tr tr1 ->
  follows (singleton (eval_false e)) tr1 tr0 -> execseq (Swhile e s) tr2 tr0. 
  * cofix COINDHYP0. move => tr0 tr1 tr2 tr3 h0 h2 h3. 
    foo h0. move: H0 => [st0 [_ h1]]. foo h1. foo H1. foo h2. 
    foo H2. foo h3. simpl. rewrite (follows_hd H3). apply execseq_nil. 
    have := COINDHYP _ _ H1 H3. apply.
    foo h2. foo h3. 
    have := execseq_cons st (COINDHYP0 _ _ _ _ H H3 H4). apply.     
  * move => tr0 tr1 h0 h1.  foo h0. 
    - foo h1. move: H1 => [st0 [h0 h1]]. foo h1. simpl. 
      foo h0. have :=  exec_while_false _ H0. apply. 
    - move: H => [tr2 [h0 h2]].
      have [_ h4]:= sp_hd h0.  have h3 := IHs _ _ h0 => {IHs h0}. 
      rewrite -(follows_hd h1). rewrite -(follows_hd H0).
      rewrite -(follows_hd h2). 
      have h5: execseq s (Tcons (hd tr2) (Tnil (hd tr2))) (Tcons (hd tr2) tr2). 
      * apply execseq_cons. apply execseq_nil => //.  
      apply: (exec_while_loop h4 h5) => {h4 h5 h3}.
      have := execseq_cons (hd tr2) (h _ _ _ _ h2 H0 h1). apply. 
Qed. 

(* Lemma 3.6: sp is setoid. *)
Lemma sp_setoid: forall s u tr tr',
sp s u tr -> bisim tr tr' -> sp s u tr'.
Proof. 
move => s; induction s; simpl; move => u tr0 tr1. 
- move => [st0 [h1 h2]] h3. foo h2. foo h3.   
  exists st0. split. apply h1. reflexivity.  
- move => [st0 [h1 h2]] h3. foo h2. foo H1. foo h3. foo H2.  
  exists st0. split. apply h1. reflexivity.
- move => [tr2 [h1 h2]] h3. exists tr2. split. 
  * have := IHs1 _ _ _ h1; apply. reflexivity.  
  * move => {h1}. move: tr0 tr1 tr2 h3 h2. cofix COINDHYP.
     move => tr0 tr1 tr2 h3 h2. foo h2. 
    - apply: follows_nil. 
      * symmetry. have := bisim_hd h3. apply.  
      *  have := IHs2 _ _ _ H0; apply. by apply: h3.
    - foo h3. have := follows_delay st (COINDHYP _ _ _ H3 H); apply. 
- move => [tr2 [h1 h2]] h3. move: h1 => [st0 [h1 h4]].  foo h4.
  foo H1. foo h2. foo h3. foo H2. have h2 := bisim_hd H3. 
  exists (Tcons (hd tr') (Tnil (hd tr'))). split. exists (hd tr').
  by split; [apply h1 | reflexivity]. apply follows_delay. symmetry in h2.  
  have := follows_nil h2. apply. clear h1 h2. move: H1 => [h1 | h1]. 
  - left. have := IHs1 _ _ _ h1 H3. apply. 
  - right. have := IHs2 _ _ _ h1 H3. apply. 
- move => h0 h1. move: h0 => [tr2 [h0 h2]]. exists tr2.
  split; first by apply h0. move: h0 => [st0 [h0 h3]]. foo h3. foo H1.
  foo h2. foo H2. foo h1. apply follows_delay. have h1 := bisim_hd H3.
  symmetry in h1. have := follows_nil h1 => {h1}. apply. clear h0.
  have := append_setoid _ H1 H3. apply. by apply singleton_setoid. 
Qed. 

(* Lemma 3.9: => *)
Lemma loopinv_adequate: forall a s u tr,
sp s (loopinv a (sp s) u andS eval_true a) tr ->
append (sp s (loopinv a (sp s) u andS eval_true a)) 
             (singleton (loopinv a (sp s) u)) tr.
Proof. 
move => a s u tr h0. exists tr. split; first by apply h0. 
apply conv_follows. move => st0 h1. 
have h2 := sp_hd h0. move: h2 => [h2 h3]. foo h3.
have h3 := @andS_left (loopinv a (sp s) u) (eval_true a).
have h4 := sp_cont h3 h0 => {h3 h0}.   
have := loopinv_next h2 H0 _ _ h4 => {h2 H0 h4}. 
apply => //.
Qed.    

(* Lemma 3.9: <= *)
Lemma loopinv_adequate_aux: forall a s u tr,
append (sp s (loopinv a (sp s) u andS eval_true a)) 
             (singleton (loopinv a (sp s) u)) tr ->
sp s (loopinv a (sp s) u andS eval_true a) tr.
Proof. move => a s u tr0 [tr1 [h0 h1]].
have := follows_singleton h1 => {h1}. move => h1. 
have := sp_setoid h0 h1. done. Qed.   

Definition Sp (s: stmt) (u: assertS): assertT. 
exists (sp s u). 
move => tr0 h0 tr1 h1. have := sp_setoid h0 h1. apply. 
Defined.

(* Lemma 3.10: sp is a postcondition w.r.t. the Hoare logic. *)
Lemma sp_deducible: forall s u, semax u s (Sp s u).
Proof. 
move => s; induction s => u.     
- have h0: ([|u|]) =>> (Sp Sskip u).
  * move => tr0 h0. move: h0 => [st0 [h0 h1]]. foo h1. exists st0. 
     split; [apply h0 | reflexivity]. 
  have := semax_conseq_R h0 (semax_skip _). apply.  
- have h0: (Updt u i e) =>> Sp (i <- e) u. 
  * move => tr0 h0. move: h0 => [st0 [h0 h1]]. foo h1. foo H1. 
     exists st0. split; [apply h0 | reflexivity]. 
  have := semax_conseq_R h0 (semax_assign _ _ _). apply.  
- have h0 := IHs1 u => {IHs1}. 
  have h1 := (@Last_adequate (Sp s1 u)). 
  have h2 := semax_conseq_R h1 h0 => {h0 h1}.  
  have h0 := IHs2 (Last (Sp s1 u)) => {IHs2}.
  have h3 := semax_seq h2 h0 => {h2 h0}. 
  have h0: (Sp s1 u *** Sp s2 (Last (Sp s1 u))) =>> (Sp (s1;; s2) u). 
  * clear h3. move => tr0 h0. move: h0 => [tr1 [h0 h1]]. simpl. 
     exists tr1. split; first by apply h0. simpl in h1. apply h1. 
  have := semax_conseq_R h0 h3. apply. 
- have h1 := IHs1 (u andS eval_true e) => {IHs1}.
  have h2 := IHs2 (u andS eval_false e) => {IHs2}.
  have h3 := semax_conseq_R (@orT_left (Sp s1 (u andS eval_true e)) (Sp s2 (u andS eval_false e)))  h1 => {h1}.
  have h4 := semax_conseq_R (@orT_right (Sp s1 (u andS eval_true e)) (Sp s2 (u andS eval_false e)))  h2 => {h2}.
  have h0 := semax_ifthenelse h3 h4 => {h3 h4}. 
  have h1: (<< u>> *** Sp s1 (u andS eval_true e) orT Sp s2 (u andS eval_false e)) =>>
                 (Sp (Sifthenelse e s1 s2) u).
  * clear h0. move => tr0 h0. simpl. simpl in h0. move: h0 => [tr1 [h0 h1]]. 
     exists tr1. split; first by apply h0. move: h0 => [st0 [h0 h2]]. foo h2. foo H1. 
     foo h1. foo H2. clear h0. apply follows_delay. apply follows_nil => //. 
  have := semax_conseq_R h1 h0. apply. 
- have h0 := IHs (loopinv e (sp s) u andS eval_true e) => {IHs}. 
  have h1 := @loopinv_init u e (sp s).
  have h2: (Sp s (loopinv e (sp s) u andS eval_true e)) =>>
  (Sp s (loopinv e (sp s) u andS eval_true e) *** [| loopinv e (sp s) u |]). 
  * clear h0 h1. move => tr0 h0. simpl in h0. simpl. apply loopinv_adequate. 
     apply h0. 
  have h3 := semax_conseq_R h2 h0 => {h2 h0}.
  have h0 := semax_while h1 h3 => {h1 h3}. 
  have h1: (<<u>> *** Iter (Sp s (loopinv e (sp s) u andS eval_true e) ***
  << loopinv e (sp s) u>>) *** [| eval_false e|]) =>>
   (Sp (Swhile e s) u).
  * clear h0. move => tr0 h0. simpl. apply h0. 
  have := semax_conseq_R h1 h0. apply. 
Qed. 

(* Corollary 3.2 *)
Lemma sp_correct: forall s (u: assertS) (p: assertT),
(forall st tr, exec s st tr -> u st -> satisfy p tr) ->
forall tr, sp s u tr -> satisfy p tr.
Proof. 
move => s u p h1 tr h2. 
have h3 := sp_then_exec h2. have h4 := sp_hd h2. 
have := h1 _ _ h3 h4; apply. 
Qed. 

(* Proposition 3.4: Completeness *)
Lemma sp_complete: forall s (u: assertS) (p: assertT),
 (forall st tr, exec s st tr -> u st -> satisfy p tr) ->
 semax u s p.
Proof.
move => s u p h1. 
have h2 := sp_deducible s u. have h3 := sp_correct h1. 
have := semax_conseq_R _ h2; apply.
* move => tr0 h0. simpl in h0. have := h3 _ h0; apply.  
Qed.
