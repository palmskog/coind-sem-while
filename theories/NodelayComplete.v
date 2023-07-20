Require Import SsrExport.
Require Export ZArith.
Require Export List.
Require Import Language. 
Require Import resumption. 
Require Import BigStep.
Require Import BigStepNodelay.
Require Import Coq.Program.Equality. 

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma Norm_irrelevance: forall r0 r1 (h: Bism r0 r1) 
(h0: Resp r0) (h1: Resp r1),
Bismd (Norm h0) (Norm h1). 
Proof. 
cofix hcoind. move => r0 r1 h0 h1. dependent inversion h1.
- clear r H. rewrite [Norm _]resd_destr; simpl. 
  move => h2; dependent inversion h2.
  - clear r H. have [h4 h3] := Redn_deterministic r2 r3 h0. foo h3. 
    rewrite [Norm _]resd_destr; simpl. by apply Bismd_refl. 
  - clear r H. have [_ h3] := Redn_deterministic r2 r3 h0. foo h3. 
  - clear r3 H. have [_ h3] := Redn_deterministic r2 r h0. foo h3.
- clear r H. rewrite [Norm _]resd_destr; simpl. 
  move => h2; dependent inversion h2.
  - clear r H. have [h4 h3] := Redn_deterministic r2 r4 h0. foo h3. 
  - clear r H. have [_ h3] := Redn_deterministic r2 r4 h0. foo h3.
    rewrite [Norm _]resd_destr; simpl.  
    have := Bismd_input (fun v => hcoind _ _ (H1 v) (r3 v) (r5 v)). 
    by apply.  
  - clear H. have [_ h3] := Redn_deterministic r2 r h0. foo h3.
- clear r2 H. rewrite [Norm _]resd_destr; simpl. 
  move => h2; dependent inversion h2.
  - clear r2 H. have [_ h3] := Redn_deterministic r r5 h0. foo h3. 
  - clear r2 H. have [_ h3] := Redn_deterministic r r5 h0. foo h3. 
  - clear r2 H. have [_ h3] := Redn_deterministic r r6 h0. foo h3. 
    rewrite [Norm (Resp_output _ _)]resd_destr; simpl. 
    have := Bismd_output _ (hcoind _ _ H0 r4 r7). by apply.  
Qed.  


Inductive X: stmt -> resd -> resd -> Type :=
| X_input: forall s f0 f1,
  (forall v, X s (f0 v) (f1 v)) ->
  X s (inputd f0) (inputd f1) 
| X_output: forall s r0 r1 v,
  X s r0 r1 -> X s (outputd v r0) (outputd v r1)
| X_seq: forall s r0 r1 r2 r3,
  Execseq s r0 r1 -> 
  forall (h1: Resp r0) (h2: Resp r1),
  Bismd (Norm h1) r2 ->
  Bismd (Norm h2) r3 -> 
  X s r2 r3.  

Lemma X_Setoid: forall s, Setoidd2 (X s).
Proof.
rewrite /Setoidd2. induction 1. 
- move => r0 h0 r1 h1. foo h0. foo h1. apply X_input. move => v.
  have := H _ _ (H1 _) _ (H2 _). by apply. 
- move => r2 h0 r3 h1. foo h0. foo h1. apply X_output. 
  have := IHX _ H3 _ H4. by apply. 
- move => r4 h0 r5 h3. have := X_seq e (Bismd_trans b h0)
  (Bismd_trans b0 h3). by apply.  
Qed.  

Lemma Norm_Wbism: forall r (h: Resp r), Wbism r (Emb (Norm h)).
Proof. 
cofix hcoind. move => r h. 
dependent inversion h; rewrite [Norm _]resd_destr; 
rewrite [Emb _]io_destr; simpl.  
-  have := Wbism_ret (Redn_Red r1) (Red_ret st). by apply. 
- fold Norm. have := Wbism_input (Redn_Red r1) (Red_input (fun v => Bism_refl _))
  (fun v => hcoind _ (r2 v)). by apply. 
- fold Norm. have := Wbism_output (Redn_Red r2) (Red_output _ (Bism_refl _))
  (hcoind _ r3). by apply. 
Qed.


Lemma Execseq_Redn_ret: forall s r0 r1, Execseq s r0 r1 ->
forall n0 st0, Redn n0 r1 (ret st0) ->
{n1: nat & {st1: state & {r2: res & {n2: nat &
 ((Redn n1 r0 (ret st1)) * (Exec s st1 r2) * 
  (Redn n2 r2 (ret st0)) * (n2 <= n0))%type}}}}.
Proof.
have: forall n0 r0 r1, Redn n0 r0 r1 ->
forall st0, Bism r1 (ret st0) ->
forall s r2, Execseq s r2 r0 ->
{n1: nat & {st1: state & {r3: res & {n2: nat &
 (Redn n1 r2 (ret st1) * (Exec s st1 r3) 
  * (Redn n2 r3 (ret st0)) * (n2 <= n0))%type}}}}.
* induction 1.
  - move => st0 h0 s0 r0 h1. foo h0. foo h1. exists 0. 
    exists st. exists (ret st0). exists 0. split; last omega. 
    split; last by apply Redn_ret. by split; [apply Redn_ret | done]. 
  - move => st0 h0 s0 r2 h1. foo h0. foo h1.
    - exists 0. exists st. exists (delay r0). exists (S n). 
      split; last omega. split; last by have := Redn_delay H; apply. 
      by split; [apply Redn_ret | done]. 
    - have [n0 [st1 [r1 [n1 [h0 h1]]]]] := IHRedn _ (Bism_refl _) _ _ H3 => {IHRedn H3}.
      move: h0 => [[h0 h2] h3]. exists (S n0). exists st1.
      exists r1. exists n1. split; last omega. split; last done. 
      split; [have := Redn_delay h0; apply | done ]. 
  - move => st0 h0. foo h0. 
  - move => st0 h0. foo h0.
move => h0. move => s0 r0 r1 h2 n0 st0 h1.
have := h0 _ _ _ h1 _ (Bism_refl _) _ _ h2. apply. 
Qed.

Lemma Redn_Execseq_input: forall n0 r0 f0, Redn n0 r0 (input f0) ->
forall s r1, Execseq s r1 r0 ->
sum 
({n1: nat & {st0: state & Redn n1 r1 (ret st0)}})
({n1: nat & {f1: val -> res &  
  ((Redn n1 r1 (input f1)) * (forall v, Execseq s (f1 v) (f0 v)))%type}}). 
Proof. 
have: forall n0 r0 r, Redn n0 r0 r ->
forall f0, Bism r (input f0) -> 
forall s r1, Execseq s r1 r0 ->
sum 
({n1: nat & {st0: state & Redn n1 r1 (ret st0)}})
({n1: nat & {f1: val -> res & 
  ((Redn n1 r1 (input f1)) * (forall v, Execseq s (f1 v) (f0 v)))%type}}).
* induction 1.
  - move => f0 h0. foo h0.
  - move => f0 h0 s r2 h2. foo h2.
    - left. exists 0. exists st. apply Redn_ret.  
    - have [h3 | h3] := IHRedn _ h0 _ _ H3 => {IHRedn}.
      - move: h3 => [n0 [st0 h3]]. left. exists (S n0). exists st0. 
        have := Redn_delay h3. apply. 
      - move: h3 => [n1 [f1 [h3 h4]]]. right. exists (S n1). exists f1. 
        split; last done. have := Redn_delay h3. apply. 
  - move => f0 h0. foo h0. 
  - move => f0 h0 s r0 h1. foo h1.
    - left. exists 0. exists st. apply Redn_ret. 
    - right. exists 0. exists f1. split. apply Redn_input. move => v.
      apply Bism_refl. move => v. foo h0. 
      have := Execseq_Setoid (H2 v) (Bism_refl _) (Bism_trans (b v) (H1 v)). 
      by apply. 
move => h. move => n0 r0 f0 h0 s r1 h1. 
have [h2 | h2] := h _ _ _ h0 _ (Bism_refl _) _ _ h1.
left. apply h2. right. apply h2. 
Qed.             

Lemma Redn_Execseq_output: forall n0 r0 v0 r1, Redn n0 r0 (output v0 r1) ->
forall s r2, Execseq s r2 r0 ->
sum 
({n1: nat & {st0: state & Redn n1 r2 (ret st0)}})
({n1: nat & {r3: res &  
  ((Redn n1 r2 (output v0 r3)) * (Execseq s r3 r1))%type}}). 
Proof.
have: forall n0 r0 r, Redn n0 r0 r ->
forall v0 r1, Bism r (output v0 r1) -> 
forall s r2, Execseq s r2 r0 ->
sum 
({n1: nat & {st0: state & Redn n1 r2 (ret st0)}})
({n1: nat & {r3: res &  
  ((Redn n1 r2 (output v0 r3)) * (Execseq s r3 r1))%type}}).
* induction 1. 
  - move => v0 r0 h0. foo h0. 
  - move => v0 r2 h0 s r3 h1. foo h0. foo h1. 
    - left. exists 0. exists st. apply Redn_ret. 
    - have [h0 | h0] := IHRedn _ _ (Bism_refl _) _ _ H4 => {IHRedn}. 
      - move: h0 => [n0 [st0 h0]]. left. exists (S n0). exists st0. 
        have := Redn_delay h0. by apply. 
      - move: h0 => [n0 [r3 [h0 h1]]]. right. exists (S n0). exists r3. 
        split. have := Redn_delay h0. by apply. 
        have := Execseq_Setoid h1 (Bism_refl _) H2. by apply.    
  - move => v0 r2 h0 s r3 h1. foo h0. foo h1.
    - left. exists 0. exists st. apply Redn_ret. 
    - right. exists 0. exists r. split. apply Redn_output. apply Bism_refl. 
      have := Execseq_Setoid H3 (Bism_refl _) (Bism_trans b H0). by apply. 
  - move => v0 r0 h0. foo h0.  
move => h n0 r0 v0 r1 h0 s r2 h1. 
have [h2 | h2] := h _ _ _ h0 _ _ (Bism_refl _) _ _ h1.
left. apply h2. right; apply h2.   
Qed.

Lemma Resp_Execseq: forall r0, Resp r0 ->
forall s r1, Execseq s r1 r0 -> Resp r1. 
Proof. 
cofix hcoind. move => r0 h0 s0 r1 h1. foo h0. 
- have := Execseq_Redn_ret h1 H. move => [n0 [st0 [n1 [st1 [h0 _]]]]].
  move: h0 => [[h0 _] _]. have := Resp_ret h0. by apply. 
- have [h0 | h0] := Redn_Execseq_input H h1. 
  - move: h0 => [n0 [st0 h0]]. have := Resp_ret h0. by apply.
  - move: h0 => [n1 [f1 [h0 h2]]]. 
    have := Resp_input h0 (fun v => hcoind _ (H0 v) _ _ (h2 v)).
    by apply. 
- have [h0 | h0] := Redn_Execseq_output H h1. 
  - move: h0 => [n0 [st0 h0]]. have := Resp_ret h0. by apply. 
  - move: h0 => [n0 [r4 [h0 h2]]]. 
    have := Resp_output h0 (hcoind _ H0 _ _ h2). by apply. 
Qed.

Lemma Execseq_Redn_input: forall s r0 r1, Execseq s r0 r1 ->
forall n0 f0, Redn n0 r1 (input f0) ->
(forall x, Resp (f0 x)) ->
sum ({n1: nat & {st0: state &{n2: nat & {r2: res &
  ((Redn n1 r0 (ret st0)) * (Exec s st0 r2) 
   * (Redn n2 r2 (input f0)) * (n2 <= n0))%type}}}})
({n1: nat & {f1: val -> res&
  ((Redn n1 r0 (input f1) * (forall v, Resp (f1 v)) * 
   (forall v, Execseq s (f1 v) (f0 v))))%type}}).     
Proof. 
have: forall n0 r0 r1, Redn n0 r0 r1 ->
forall f0, Bism r1 (input f0) ->
forall s r2, Execseq s r2 r0 -> (forall x, Resp (f0 x)) ->
sum ({n1: nat & {st0: state & {n2: nat & {r3: res &
 ((Redn n1 r2 (ret st0)) * (Exec s st0 r3) *
  (Redn n2 r3 (input f0)) * (n2 <= n0))%type}}}})
({n1: nat & {f1: val -> res &
  ((Redn n1 r2 (input f1)) * (forall v, Resp (f1 v)) *
   (forall v, Execseq s (f1 v) (f0 v)))%type}}). 
* induction 1.
  - move => f0 h0. foo h0. 
  - move => f0 h0 s0 r2 h1 h2. foo h0. foo h1.
    - clear IHRedn. left. exists 0. exists st. exists (S n). exists (delay r0).
      split; last omega. split. split; [apply Redn_ret | done]. 
      have := Redn_Setoid (Redn_delay H) (Bism_refl _) (Bism_input (fun v => H2 v)).
      by apply. 
    - have [h0 | h0] := IHRedn _ (Bism_input (fun v => H2 v)) _ _ H4 h2.
      - move: h0 => [n1 [st0 [n2 [r3 [h0 h1]]]]]. move: h0 => [[h0 h4] h3].
        left. exists (S n1). exists st0. exists n2. exists r3. 
        split; last omega. split; last done. 
        split; [have := Redn_delay h0; apply | done]. 
      - move: h0 => [n1 [f2 [[h0 h1] h3]]]. right. exists (S n1). 
        exists f2. split; last done. 
        split; [have := Redn_delay h0; apply | done]. 
    - move => f0 h0. foo h0. 
    - move => f0 h0 s0 r0 h1 h2. foo h0. foo h1.
      - left. exists 0. exists st. exists 0. exists (input f). 
        split; last omega. split. split; [apply Redn_ret | done]. 
        apply Redn_input. move => x. have := Bism_trans (b x) (H1 x). by apply. 
      - right. exists 0. exists f1.
        have h0 := (fun v => (Bism_trans (Bism_sym (H1 v)) (Bism_sym (b v)))). 
        split. split. apply Redn_input. 
        move => v. apply Bism_refl. move => v. have := Resp_Execseq _ (H3 v). 
        apply. have := Resp_setoid (h2 v) (h0 v). apply. 
        move => v. have := Execseq_Setoid (H3 v) (Bism_refl _) (Bism_sym (h0 v)). 
        apply. 
move => h. move => s0 r0 r1 h0 n0 f0 h2 h3. 
have [h4 | h4]  := h _ _ _ h2 _ (Bism_refl _)  _ _ h0 h3.
left. apply h4. right. apply h4.                     
Qed. 


Lemma Execseq_Redn_output: forall s r0 r1, Execseq s r0 r1 ->
forall n0 v0 r2, Redn n0 r1 (output v0 r2) ->
Resp r2 ->
sum
({n1: nat & {st0: state & {n2: nat & { r3: res &
  (Redn n1 r0 (ret st0) * Exec s st0 r3  
   * Redn n2 r3 (output v0 r2) * (n2 <= n0))%type}}}})     
({n1: nat & {r3: res &
  (Redn n1 r0 (output v0 r3) * Resp r3 * Execseq s r3 r2)%type}}). 
Proof. 
have: forall n0 r0 r1, Redn n0 r0 r1 ->
forall v0 r2, Bism r1 (output v0 r2) ->
forall s r3, Execseq s r3 r0 -> Resp r2 ->
sum
({n1: nat & {st0: state & {n2: nat & {r4: res &
  (Redn n1 r3 (ret st0) * Exec s st0 r4 *
   Redn n2 r4 (output v0 r2) * (n2 <= n0))%type}}}})
({n1: nat & {r4: res &
  (Redn n1 r3 (output v0 r4) * Resp r4 * Execseq s r4 r2)%type}}).
* induction 1. 
  - move => v0 r0 h0. foo h0. 
  - move => v0 r2 h0 s r3 h1 h2. foo h1. 
    - foo h0. clear IHRedn. left. exists 0. exists st. exists (S n). 
      exists (delay r0). split; last omega. split. split. apply Redn_ret. 
      done. apply Redn_delay. have := Redn_Setoid H (Bism_refl _) (Bism_output v0 H3).
      by apply. 
    - have [h3 | h3] := IHRedn _ _ h0 _ _ H3 h2.
      - move: h3 => [n1 [st0 [n2 [r4 [h3 h4]]]]]. move: h3 => [[h3 h5] h6]. 
        left.  exists (S n1). exists st0. exists n2. exists r4. 
        split; last omega. split. split => //. have := Redn_delay h3. apply. done.  
      - move: h3 => [n1 [r4 [[h3 h4] h5]]]. right. exists (S n1). exists r4. 
        split => //. split => //. have := Redn_delay h3; apply. 
  - move => v0 r2 h0 s r3 h1 h2. foo h0. foo h1. 
    - left. exists 0. exists st. exists 0. exists (output v0 r0). split; last omega. 
      split. split => //.  apply Redn_ret. have := Redn_output _ (Bism_trans b H0).
      by apply.
    - right. exists 0. exists r. split. split. have := Redn_output _ (Bism_refl _). 
      by apply. have := Resp_Execseq h2 (Execseq_Setoid H3 (Bism_refl _) (Bism_trans b H0)). 
      by apply. have := Execseq_Setoid H3 (Bism_refl _) (Bism_trans b H0). by apply. 
  - move => v0 r0 h0. foo h0.            
move => h. move => s r0 r1 h0 n0 v0 r2 h1 h2.
have [h3 | h3] := h _ _ _ h1 _ _ (Bism_refl _) _ _ h0 h2.
left; apply h3. right; apply h3.    
Qed. 

Lemma Exec_ExecX_while_ret: forall e s, 
(forall st0 r0 (h: Resp r0), Exec s st0 r0 -> ExecX X s st0 (Norm h)) -> 
forall n m r0 st0 (h0: Redn m r0 (ret st0)) st1, 
m <= n -> Exec (Swhile e s) st1 r0 -> 
ExecX X (Swhile e s) st1 (retd st0).
Proof. 
move => e s hs.  
move => n. induction n.
- move => m r0 st0 h0 st1 h1 h2. 
  have h3: m = 0; first omega. rewrite h3 in h0 => {h3}. foo h0. 
  foo h2. foo H2. foo H5.   
- move => m r0 st0 h0 st1 h1 h2. foo h2.   
  - foo h0. foo H1.  apply ExecX_while_false. done. 
  - foo H2. foo H3. foo H5. foo h0. 
    have h2 := Execseq_Redn_ret H3 H4.
    move: h2 => [n1 [st2 [r2 [n2 [[[h2 h3] h4] h6]]]]]. 
    have h5 := hs _ _ (Resp_ret h2) H2 => {hs}.
    rewrite [Norm _]resd_destr in h5; simpl in h5.
    have := ExecX_while_ret H1 h5. apply.  
    have := IHn _ _ _ h4 _ _ h3. apply. omega.
Qed.

Lemma Exec_ExecX_while_input: forall e s, 
(forall st0 r0 (h: Resp r0), Exec s st0 r0 -> ExecX X s st0 (Norm h)) -> 
forall n m r0 f0 (h0: Redn m r0 (input f0)) 
(h1: forall v, Resp (f0 v)) st1, 
m <= n -> Exec (Swhile e s) st1 r0 -> 
ExecX X (Swhile e s) st1 (inputd (fun v => Norm (h1 v))). 
Proof.
move => e s hs. move => n. induction n. 
- move => m r0 f0 h0 h1 st0 h2 h3. have h4: m = 0; first omega. clear h2. 
  rewrite h4 in h0 => {h4}. foo h0. foo h3. foo H3. foo H6. 
- move => m r0 f0 h0 h1 st0 h2 h3. foo h3. 
  - foo h0. foo H1. 
  - foo H2. foo H3. foo H5. foo h0. 
    have [h3 | h3] := Execseq_Redn_input H3 H4 h1.
    - move: h3 => [n1 [st1 [n2 [r2 [h3 h4]]]]]. move: h3 => [[h3 h5] h6]. 
      have := hs _ _ (Resp_ret h3) H2 => {H2 hs}.
      rewrite [Norm _]resd_destr; simpl. move => h7. 
      have := ExecX_while_ret H1 h7 => {H1 h7}. apply. 
      have := IHn _ _ _ h6 h1 _ _ h5. apply. omega. 
    - move: h3 => [n1 [f1 [[h3 h4] h5]]]. 
      have := hs _ _ (Resp_input h3 h4) H2 => {hs H2}.
      rewrite [Norm _]resd_destr; simpl. move => h6. 
      have := ExecX_while_input H1 h6 => {H1 h6}. apply. 
      apply X_input. move => v. 
     have := X_seq (h5 _) (Bismd_refl _) (Bismd_refl _). apply.         
Qed. 

Lemma Exec_ExecX_while_output: forall e s, 
(forall st0 r0 (h: Resp r0), Exec s st0 r0 -> ExecX X s st0 (Norm h)) -> 
forall n m r0 v0 r1 (h0: Redn m r0 (output v0 r1)) 
(h1: Resp r1) st1, 
m <= n -> Exec (Swhile e s) st1 r0 -> 
ExecX X (Swhile e s) st1 (outputd v0 (Norm h1)). 
Proof. 
move => e s hs.  move => n. induction n. 
- move => m r0 v0 r1 h0 h1 st1 h2 h3. have h4: m = 0; first omega. 
  rewrite h4 in h0 => {h4 h2}. foo h0. foo h3. foo H3. foo H6.   
- move => m r0 v0 r1 h0 h1 st1 h2 h3. foo h3. 
  - foo h0. foo H1.  
  - foo H2. foo H3. foo H5. foo h0. 
    have [h3 | h3] := Execseq_Redn_output H3 H4 h1.
    - move: h3 => [n1 [st2 [n2 [r3 [h3 h4]]]]]. move: h3 => [[h3 h5] h6].
      have h7 := hs _ _ (Resp_ret h3) H2. 
      rewrite [Norm _]resd_destr in h7; simpl in h7. 
      have h8: n2 <= n. omega. 
      have h9 := IHn _ _ _ _ h6 h1 _ h8 h5. 
      rewrite [Norm _]resd_destr in h9; simpl in h9. 
      rewrite [Norm _]resd_destr; simpl. 
      have := ExecX_while_ret H1 h7 h9. by apply. 
    - move: h3 => [n1 [r3 [[h3 h4] h7]]]. clear IHn. 
      have h5 := hs _ _ (Resp_output h3 h4) H2.   
      rewrite [Norm _]resd_destr in h5; simpl in h5. 
      have := ExecX_while_output H1 h5. apply.
      have h6 := (@X_seq _ _ _ _ _ H3 (Resp_output h3 h4) 
     (Resp_output H4 h1) (Bismd_refl _) (Bismd_refl _)).
      rewrite [Norm _]resd_destr in h6; simpl in h6. 
      rewrite [Norm (Resp_output _ _)]resd_destr in h6; simpl in  h6. 
      apply h6.     
Qed.


Lemma Exec_ExecX: forall s st r (h: Resp r),
Exec s st r -> ExecX X s st (Norm h).
Proof. 
move => s. induction s. 
- move => st0 r0 h0 h1. foo h1. dependent inversion h0; subst.  
  rewrite [Norm _]resd_destr; simpl. foo r0. by apply ExecX_skip.
  foo r0. foo r.     
- move => st0 r0 h0 h1. foo h1. dependent inversion h0; subst. 
  rewrite [Norm _]resd_destr; simpl. foo r0. foo H1. 
  apply ExecX_assign. absurd False. done. foo r0. foo H1. 
  absurd False => //. foo r. foo H1.
- move => st0 r0 h0. dependent destruction h0.
  - move => h0. foo h0. rewrite [Norm _]resd_destr; simpl. 
    have := Execseq_Redn_ret H4 r0. 
    move => [n1 [st1 [r2 [n2 [h0 h1]]]]]. move: h0 => [[h0 h2] h3].
    have := IHs1 _ _ (Resp_ret h0) H1 => {H1}. 
    rewrite [Norm _]resd_destr; simpl. move => h4. 
    have := (@X_seq _ _ _ _ _ H4 (Resp_ret h0) (Resp_ret r0) (Bismd_refl _)
    (Bismd_refl _)). rewrite [Norm _]resd_destr; simpl.   
    rewrite [Norm _]resd_destr; simpl.  move => h5.  
    have := ExecX_seq_ret h4 h5. by apply.   
  - move => h0. foo h0. rewrite [Norm _]resd_destr; simpl. 
    have := Execseq_Redn_input H4 r0 r1. move => [h0 | h0].
    - move: h0 => [n1 [st1 [n2 [r3 [h0 _]]]]]. move: h0 => [[h0 _] h1].   
      have := IHs1 _ _ (Resp_ret h0) H1 => {H1}. 
      rewrite [Norm _]resd_destr; simpl. move => h4. 
      have := (@X_seq _ _ _ _ _ H4 (Resp_ret h0) (Resp_input r0 r1) (Bismd_refl _)
      (Bismd_refl _)). rewrite [Norm _]resd_destr; simpl.   
      rewrite [Norm _]resd_destr; simpl.  move => h5.  
      have := ExecX_seq_ret h4 h5. by apply.
    - move: h0 => [n1 [f1 [[h0 h1] h2]]]. 
      have := IHs1 _ _ (Resp_input h0 h1) H1 => {H1}. 
      rewrite [Norm _]resd_destr; simpl. move => h3. 
      have := ExecX_seq_input h3. apply. clear h3.  
      have := (@X_seq _ _ _ _ _ H4 (Resp_input h0 h1)
      (Resp_input r0 r1)) (Bismd_refl _) (Bismd_refl _).
      rewrite [Norm _]resd_destr; simpl. 
      rewrite [Norm (Resp_input _ _)]resd_destr; simpl. by apply. 
  - move => h1. foo h1. rewrite [Norm _]resd_destr; simpl. 
    have := Execseq_Redn_output H4 r h0. move => [h1 | h1].
    - move: h1 => [n1 [st1 [n2 [r3 [h1 _]]]]]. move: h1 => [[h2 _] h1].   
      have := IHs1 _ _ (Resp_ret h2) H1 => {H1}. 
      rewrite [Norm _]resd_destr; simpl. move => h4. 
      have := (@X_seq _ _ _ _ _ H4 (Resp_ret h2) (Resp_output r h0) (Bismd_refl _)
      (Bismd_refl _)). rewrite [Norm _]resd_destr; simpl.   
      rewrite [Norm _]resd_destr; simpl.  move => h5.  
      have := ExecX_seq_ret h4 h5. by apply.
    - move: h1 => [n1 [r3 [[h3 h1] h2]]]. 
      have := IHs1 _ _ (Resp_output h3 h1) H1 => {H1}. 
      rewrite [Norm _]resd_destr; simpl. move => h4. 
      have := ExecX_seq_output h4.  apply. clear h4.  
      have := (@X_seq _ _ _ _ _ H4 (Resp_output h3 h1)
      (Resp_output r h0)) (Bismd_refl _) (Bismd_refl _).
      rewrite [Norm _]resd_destr; simpl. 
      rewrite [Norm (Resp_output _ _)]resd_destr; simpl. by apply.
- move => st0 r0 h0 h1. foo h1. 
  - foo H5. foo H1. dependent inversion h0; subst.
    - inversion r0; subst. rewrite [Norm _]resd_destr; simpl. 
      have h1 := IHs1 _ _ (Resp_ret H1) H2 => {H2}.
      rewrite [Norm _]resd_destr in h1; simpl in h1.
      have := ExecX_ifthenelse_true _ H4 h1. by apply. 
    - inversion r0; subst. rewrite [Norm _]resd_destr; simpl. 
      have h1 := IHs1 _ _ (Resp_input H1 r1) H2 => {H2}.
      rewrite [Norm _]resd_destr in h1; simpl in h1.
      have := ExecX_ifthenelse_true _ H4 h1. by apply.
    - inversion r; subst. rewrite [Norm _]resd_destr; simpl. 
      have h1 := IHs1 _ _ (Resp_output H1 r2) H2 => {H2}.
      rewrite [Norm _]resd_destr in h1; simpl in h1.
      have := ExecX_ifthenelse_true _ H4 h1. by apply.
  - foo H5. foo H1. dependent inversion h0; subst.
    - inversion r0; subst. rewrite [Norm _]resd_destr; simpl. 
      have h1 := IHs2 _ _ (Resp_ret H1) H2 => {H2}.
      rewrite [Norm _]resd_destr in h1; simpl in h1.
      have := ExecX_ifthenelse_false _ H4 h1. by apply. 
    - inversion r0; subst. rewrite [Norm _]resd_destr; simpl. 
      have h1 := IHs2 _ _ (Resp_input H1 r1) H2 => {H2}.
      rewrite [Norm _]resd_destr in h1; simpl in h1.
      have := ExecX_ifthenelse_false _ H4 h1. by apply.
    - inversion r; subst. rewrite [Norm _]resd_destr; simpl. 
      have h1 := IHs2 _ _ (Resp_output H1 r2) H2 => {H2}.
      rewrite [Norm _]resd_destr in h1; simpl in h1.
      have := ExecX_ifthenelse_false _ H4 h1. by apply.      
- move => st0 r0 h0. dependent inversion h0; subst.
  - move => h1. have h2: n <= n; first omega. 
    rewrite [Norm _]resd_destr; simpl. 
    have :=  Exec_ExecX_while_ret IHs r1 h2 h1.  apply. 
  - move => h1. rewrite [Norm _]resd_destr; simpl.
    have h2: n <= n; first omega. 
    have := Exec_ExecX_while_input  IHs r1 r2 h2 h1. by apply.   
  - move => h1. have h2: n <= n; first omega.
    rewrite [Norm _]resd_destr; simpl.  
    have := Exec_ExecX_while_output IHs r r3 h2 h1. by apply. 
- move => st0 r0 h0 h1. foo h1. dependent inversion h0. 
  foo r0. foo r0. rewrite [Norm _]resd_destr; simpl. foo r. foo H2. 
  dependent inversion r2. rewrite [Norm _]resd_destr; simpl.
  foo r0. apply ExecX_write. foo r0. foo r.     
- move => st0 r0 h0 h1. foo h1. dependent inversion h0. 
  foo r0. rewrite [Norm _]resd_destr; simpl. foo r0. 
  have h1: forall v, Bismd (retd (update i v st0)) (Norm (r1 v)). 
  * move => v. have h1 := H3 v. foo h1. 
     have h2: Bism (ret (update i v st0)) (f v). rewrite H. apply Bism_refl.   
     have h1 := Norm_irrelevance (Bism_sym h2) (r1 v) 
     (Resp_ret (Redn_ret (update i v st0))).
     have := Bismd_trans _ (Bismd_sym h1). apply. 
     rewrite [Norm _]resd_destr; simpl. by apply Bismd_refl.  
  have := ExecX_Setoid X_Setoid _ (Bismd_input (fun v => h1 v)).
  apply. apply ExecX_read. foo r.
Qed. 

Lemma X_Execseqnd: forall s, Imp_Setoid (X s) (Execseqnd s). 
Proof. 
cofix hcoind. move => s r0 r1 h0 r2 h1 r3 h2. foo h0.
- foo h1. foo h2. 
  have := Execnd_input (fun v => hcoind _ _ _ (H v) _ (H1 v) _ (H2 v)).
  apply.   
- foo h1. foo h2. 
  have := Execnd_output _ (hcoind _ _ _ H _ H3 _ H4). apply.   
- move: H1. dependent inversion h4.
  - clear r H1. rewrite [Norm _]resd_destr; simpl. move => h5. 
    move: H0. dependent inversion h3. 
    - clear r H0. rewrite [Norm _]resd_destr; simpl. move => h6. 
      foo h5. foo h6. foo h1. foo h2.  have := Execnd_ret X_Setoid hcoind.
      apply. have [n2 [st1 [r8 [n1 h0]]]] := Execseq_Redn_ret H r6.
      move: h0 => [[[h0 h5] h6] _]. 
      have [_ h7] := Redn_deterministic r7 h0 (Bism_refl _). foo h7.  
      have := Exec_ExecX (Resp_ret h6) h5. 
      rewrite [Norm _]resd_destr; simpl. move => h7. 
      apply h7.
    - clear r H0. move => _. have := Execseq_Redn_ret H r6.
      move => [n1 [st1 [r9 [n2 [h6 h7]]]]]. move: h6 => [[h6 h9] h8].
      have [_ h10] := Redn_deterministic r7 h6 (Bism_refl _). foo h10. 
    - clear r7 H0. move => _. have := Execseq_Redn_ret H r6.
      move => [n1 [st1 [r7 [n2 [h6 h7]]]]]. move: h6 => [[h6 h9] h8].
      have [_ h10] := Redn_deterministic r h6 (Bism_refl _). foo h10.
  - clear r H1. rewrite [Norm _]resd_destr; simpl. move => h5. foo h5. 
    move: H0. dependent inversion h3.
    - clear r H0. rewrite [Norm _]resd_destr; simpl. 
      move => h5. foo h5. have [h6 | h6] := Execseq_Redn_input H r6 r7.
      - move: h6 => [n1 [st0 [n2 [r8 [h6 h7]]]]]. move: h6 => [[h6 h8] h9].
        have [_ h10] := Redn_deterministic r1 h6 (Bism_refl _). foo h10. 
        foo h1. foo h2. have := Execnd_ret X_Setoid hcoind. apply. 
        have := Exec_ExecX (Resp_input h9 r7) h8.
        rewrite [Norm _]resd_destr; simpl. move => h10. 
        have := ExecX_Setoid X_Setoid h10
        (Bismd_input (fun v => Bismd_trans (H2 v) (H1 v))). by apply.
      - move: h6 => [n1 [f0 [[h7 h8] h9]]]. 
        have [_ h10] := Redn_deterministic r1 h7 (Bism_refl _). foo h10. 
    - clear r H0. rewrite [Norm _]resd_destr; simpl. move => h5. foo h5.  
      have [h6 | h6] := Execseq_Redn_input H r6 r7.
      - move: h6 => [n1 [st0 [n2 [r9 [h6 h7]]]]]. move: h6 => [[h6 h8] h9].
        have [_ h10] := Redn_deterministic r1 h6 (Bism_refl _). foo h10.  
      - move: h6 => [n1 [f2 [[h7 h8] h9]]]. 
        have [_ h10] := Redn_deterministic r1 h7 (Bism_refl _). foo h10.
        foo h2. foo h1. apply Execnd_input. move => v. 
        have := hcoind _ _ _ _ _ (Bismd_trans (H1 v) (H5 v))
        _ (Bismd_trans (H2 v) (H3 v)). apply.
        have := X_seq (Execseq_Setoid (h9 v) (Bism_sym (H4 v)) (Bism_refl _))
        (Bismd_refl _) (Bismd_refl _).  apply.
    - clear r1 H0. rewrite [Norm _]resd_destr; simpl. move => h5. foo h5.  
      have [h6 | h6] := Execseq_Redn_input H r6 r7.
      - move: h6 => [n1 [st0 [n2 [r11 [h6 h7]]]]]. move: h6 => [[h6 h8] h9].
        have [_ h10] := Redn_deterministic r h6 (Bism_refl _). foo h10.
      - move: h6 => [n1 [f2 [[h7 h8] h9]]]. 
        have [_ h10] := Redn_deterministic r h7 (Bism_refl _). foo h10.        
  - clear r6 H1. rewrite [Norm _]resd_destr; simpl. move => h5. foo h5.  
    move: H0. dependent inversion h3.
    - clear r1 H0. rewrite [Norm _]resd_destr; simpl. 
      move => h5. foo h5. have [h6 | h6] := Execseq_Redn_output H r r8. 
      - move: h6  => [n1 [st0 [n2 [r10 [h6 h7]]]]]. move: h6 => [[h6 h8] h9].
        have [_ h10] := Redn_deterministic r6 h6 (Bism_refl _). foo h10. 
        foo h1. foo h2. have := Execnd_ret X_Setoid hcoind. apply. 
        have := Exec_ExecX (Resp_output h9 r8) h8.
        rewrite [Norm _]resd_destr; simpl. move => h10. 
        have := ExecX_Setoid X_Setoid h10 (Bismd_output _ (Bismd_trans H4 H3)). 
        by apply.
      - move: h6 => [n1 [f0 [[h7 h8] h9]]]. 
        have [_ h10] := Redn_deterministic r6 h7 (Bism_refl _). foo h10. 
    - clear r1 H0. rewrite [Norm _]resd_destr; simpl. move => h5. foo h5.  
      have [h6 | h6] := Execseq_Redn_output H r r8. 
      - move: h6 => [n1 [st0 [n2 [r11 [h6 h7]]]]]. move: h6 => [[h6 h8] h9].
        have [_ h10] := Redn_deterministic r6 h6 (Bism_refl _). foo h10.  
      - move: h6 => [n1 [f9 [[h7 h8] h9]]]. 
        have [_ h10] := Redn_deterministic r6 h7 (Bism_refl _). foo h10.
    - clear r1 H0. rewrite [Norm _]resd_destr; simpl. move => h5. foo h5.
       have [h6 | h6] := Execseq_Redn_output H r r8.  
      - move: h6 => [n1 [st0 [n2 [r13 [h6 h7]]]]]. move: h6 => [[h6 h8] h9].
        have [_ h10] := Redn_deterministic h6 r10 (Bism_refl _). foo h10.  
      - move: h6 => [n1 [r13 [[h7 h8] h9]]]. 
        have [_ h10] := Redn_deterministic r10 h7 (Bism_refl _). foo h10.
        foo h2. foo h1. apply Execnd_output. 
        have := hcoind _ _ _ _ _ (Bismd_trans H3 H7) _ (Bismd_trans H4 H6).
        apply. 
        have := X_seq (Execseq_Setoid h9  (Bism_sym H1)  (Bism_refl _))
        (Bismd_refl _) (Bismd_refl _).  apply.
Qed.

Lemma Exec_Execnd: forall s st r (h: Resp r),
Exec s st r -> ExecX Execseqnd s st (Norm h).
Proof. 
move => s st r h0 h1. 
have := ExecX_monotone X_Execseqnd. apply. 
have := Exec_ExecX h0 h1. apply.
Qed. 
     
