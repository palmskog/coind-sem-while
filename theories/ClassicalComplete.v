Require Import ssreflect. 
Require Export ZArith.
Require Export List.
Require Import Language. 
Require Import resumption.
Require Import BigStep. 
Require Import BigStepClassical.  
Require Import Coq.Program.Equality.  

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma Redn_Divr: forall n0 r0 r1, Redn n0 r0 r1 ->
Divr r0 -> False. 
Proof. 
induction 1. 
- move => h0. foo h0. 
- move => h0. foo h0. have := IHRedn H1. by apply.
- move => h0. foo h0.
- move => h0. foo h0.   
Qed.  

Lemma Divr_Divr_Bism: forall r0 r1, Divr r0 -> Divr r1 ->
Bism r0 r1. 
Proof. cofix hcoind. move => r0 r1 h0 h1; foo h0; foo h1.
have := Bism_delay (hcoind _ _ H H0). by apply. 
Qed.  

Lemma Execseq_Divr: forall s r0 r1,
Execseq s r0 r1 -> Divr r1 -> 
sum (Divr r0) ({n:nat & {st: state & Redn n r0 (ret st) }}).
Proof. 
move => s r0 r1 h0 h1. have [h2 | h2] := toss r0. 
- move: h2 => [n0 [r2 h2]]. right. move: n0 r0 r2 h2 r1 h1 h0.
  induction 1. 
  - move => r0 h0 h1. exists 0. exists st. apply Redn_ret. 
  - move => r2 h0 h1. foo h1. foo h0. 
    have [n0 [st0 h0]] := IHh2 _ H0 H1 => {H0 H1}.
    exists (S n0). exists st0. have := Redn_delay h0. by apply. 
  - move => r2 h0 h1. foo h1. foo h0. 
  - move => r0 h0 h1. foo h1. foo h0. 
- by left.        
Qed.  


Lemma Norm_irr: forall r0 r1 (h0: Commit r0) (h1: Commit r1),
Bism r0 r1 -> Bismc (Norm h0) (Norm h1).
Proof. cofix hcoind. case. 
- move => st0. case. move => st1. move => h0 h1. 
  dependent inversion h0; clear h0.  
  dependent inversion h1; subst; clear h1. move => h0.
  foo h0. rewrite [Norm (Commit_ret r0)]resc_destr; simpl.
  rewrite [Norm _]resc_destr; simpl. 
  have [_ h0] := Redn_deterministic r2 r0 (Bism_refl _).
  foo h0. by apply Bismc_refl. foo r2. foo r3. foo d. foo r0.
  foo r. foo d. move => v0 r0 h0 h1 h2. foo h2. 
  move => f0 h0 h1 h2. foo h2. move => r0 h0 h1 h2. foo h2. 
- move => v0 r0. case. move => st0 h0 h1 h2. foo h2. 
  move => v1 r1 h0 h1. dependent inversion h0; subst; clear h0.
  foo r2. foo r2. dependent inversion h1; subst; clear h1. foo r4. 
  foo r4. move => h0.  
  rewrite [Norm _]resc_destr; simpl. 
  rewrite [Norm (Commit_output _ _)]resc_destr; simpl.
  have [ _ h1] := Redn_deterministic r r5 h0 => {r r5 h0}.
  foo h1. apply Bismc_output. 
  have := hcoind _ _ c c0 H0. by apply. foo d. foo d.
  move => f0 h0 h1 h2. foo h2. 
  move => r1 h0 h1 h2. foo h2.
- move => f0. case. move => st0 h0 h1 h2. foo h2. 
  move => v0 r0 h0 h1 h2. foo h2. move => f1 h0.
  dependent inversion h0; subst; clear h0.  foo r0. move => h1. 
  dependent inversion h1; subst; clear h1. foo r1. move => h0.
  rewrite [Norm _]resc_destr; simpl.
  rewrite [Norm _]resc_destr; simpl.
  apply Bismc_input. move => v0.
  have [_ h1] := Redn_deterministic r0 r1 h0 => {r0 r1 h0}.    
  foo h1. have := hcoind _ _ (c _) (c0 _) (H1 _). by apply. 
  foo r. foo d. foo r. foo d. move => r h0 h1 h2. foo h2. 
- move => r0. case.
  - move => st0 h0 h1 h2. foo h2. 
    move => v0 r1 h0 h1 h2. foo h2. move => f0 h0 h1 h2. foo h2. 
    move => r1 h0. dependent inversion h0; subst; clear h0.
    move => h1. dependent inversion h1; subst; clear h1.  
    move =>  h0. rewrite [Norm _]resc_destr; simpl. 
    rewrite [Norm _]resc_destr; simpl. 
    have [_ h1] := Redn_deterministic r2 r3 h0 => {r2 r3 h0}.
    foo h1.  by apply Bismc_refl. move => h0.
    have [_ h1] := Redn_deterministic r2 r3 h0 => {h0}. foo h1. 
    move => h0.
    have [_ h1] := Redn_deterministic r2 r h0 => {h0}. foo h1.
    move => h0. absurd False => //. 
    have := Redn_Divr r2 (Divr_Setoid d (Bism_sym h0)). by apply. 
  - move => h1. dependent inversion h1; subst; clear h1.  
    move => h0.
    have [_ h1] := Redn_deterministic r2 r3 h0 => {h0}. foo h1. 
    move =>  h0. rewrite [Norm _]resc_destr; simpl. 
    rewrite [Norm _]resc_destr; simpl. 
    have [_ h1] := Redn_deterministic r2 r3 h0 => {r2 r3 h0}.
    foo h1. apply Bismc_input. move => v0. 
    have := hcoind _ _ (c _) (c0 _) (H1 _). by apply. 
    move => h0.
    have [_ h1] := Redn_deterministic r2 r h0 => {h0}. foo h1. 
    move => h0. absurd False => //. 
    have := Redn_Divr r2 (Divr_Setoid d (Bism_sym h0)). by apply. 
  - move => h1. dependent inversion h1; subst; clear h1.  
    move => h0.
    have [_ h1] := Redn_deterministic r r4 h0 => {h0}. foo h1. 
    move => h0.
    have [_ h1] := Redn_deterministic r r4 h0 => {h0}. foo h1. 
    move =>  h0. rewrite [Norm _]resc_destr; simpl. 
    rewrite [Norm (Commit_output _ _)]resc_destr; simpl. 
    have [_ h1] := Redn_deterministic r r5 h0 => {r r5 h0}.
    foo h1. apply Bismc_output.  
    have := hcoind _ _ c c0 H0.  by apply. 
    move => h0. absurd False => //. 
    have := Redn_Divr r (Divr_Setoid d (Bism_sym h0)). by apply. 
  - move => h1. dependent inversion h1; subst; clear h1.  
    move => h0. absurd False => //. 
    have := Redn_Divr r2 (Divr_Setoid d h0). by apply.
    move => h0. absurd False => //. 
    have := Redn_Divr r2 (Divr_Setoid d h0). by apply.
    move => h0. absurd False => //. 
    have := Redn_Divr r (Divr_Setoid d h0). by apply.
    move => h0. foo h0. 
    rewrite [Norm _]resc_destr; simpl. 
    rewrite [Norm _]resc_destr; simpl. 
    by apply Bismc_refl.
Qed.  

Lemma Commit_Wbism: forall r0, Commit r0 ->
forall r1, Wbism r0 r1 -> Commit r1. 
Proof. cofix hcoind. move => r0 h0. foo h0; move => r1 h0.  
- have := Redn_ret_Wbism H h0 => {H h0}. 
  move => [n1 h0]. have := Commit_ret h0. by apply.  
- have [n0 [f0 [h1 h2]]] := Redn_input_Wbism H h0 => {H h0}. 
  have := Commit_input h1. apply. move => v. 
  have := hcoind _ (H0 _) _ (h2 _). apply. 
- have [n0 [r3 [h1 h2]]] := Redn_output_Wbism H h0 => {H h0}. 
  have := Commit_output h1. apply.  
  have := hcoind _ H0 _ h2. by apply.  
- have h1 := Divr_Wbism H h0 => {H h0}. 
  have := Commit_divr h1. by apply. 
Qed. 

Lemma Wbism_Norm: forall r0 r1, Wbism r0 r1 ->
forall (h0: Commit r0) (h1: Commit r1),
Bismc (Norm h0) (Norm h1). 
Proof. cofix hcoind. move => r0 r1 h0 h1. 
dependent inversion h1; subst => {h1}; 
rewrite [Norm _]resc_destr; simpl.   
- move => h1. dependent inversion h1; subst. 
  have [n1 h2] := Redn_ret_Wbism r2 h0 => {r2 h0}.
  rewrite [Norm _]resc_destr; simpl. 
  have [_ h0] := Redn_deterministic r3 h2 (Bism_refl _) => {r3 h2}.
  foo h0. by apply Bismc_refl. absurd False => //. 
  have [n1 h2] := Redn_ret_Wbism r2 h0 => {r2 h0}. 
  have [_ h0] := Redn_deterministic r3 h2 (Bism_refl _). foo h0.    
  absurd False => //. 
  have [n1 h2] := Redn_ret_Wbism r2 h0 => {r2 h0}. 
  have [_ h0] := Redn_deterministic r h2 (Bism_refl _). foo h0.
  absurd False => //. 
  have [n1 h2] := Redn_ret_Wbism r2 h0 => {r2 h0}. 
  have := Redn_Divr h2 d. by apply.          
- move => h1. dependent inversion h1; subst. 
  absurd False => //. 
  have [n1 [f1 [h2 _]]] := Redn_input_Wbism r2 h0 => {r2 h0}. 
  have [_ h0] := Redn_deterministic r3 h2 (Bism_refl _). foo h0.
  have [n1 [f1 [h2 h3]]] := Redn_input_Wbism r2 h0 => {r2 h0}. 
  have [_ h0] := Redn_deterministic r3 h2 (Bism_refl _). foo h0.
  rewrite [Norm _]resc_destr; simpl. 
  apply Bismc_input. move => v. 
  have := hcoind _ _ (Wbism_Setoid (h3 v) (Bism_refl _) (Bism_sym (H1 v)))
  (c v) (c0 v). by apply.   
  absurd False => //. 
  have [n1 [f1 [h2 _]]] := Redn_input_Wbism r2 h0 => {r2 h0}. 
  have [_ h0] := Redn_deterministic r h2 (Bism_refl _). foo h0.
  absurd False => //. 
  have [n1 [f1 [h2 _]]] := Redn_input_Wbism r2 h0 => {r2 h0}. 
  have := Redn_Divr h2 d. by apply. 
- move => h1. dependent inversion h1; subst. 
  absurd False => //. 
  have [n1 [r5 [h2 _]]] := Redn_output_Wbism r h0 => {r2 h0}. 
  have [_ h0] := Redn_deterministic r4 h2 (Bism_refl _). foo h0.
  absurd False => //. 
  have [n1 [r5 [h2 _]]] := Redn_output_Wbism r h0 => {r2 h0}. 
  have [_ h0] := Redn_deterministic r4 h2 (Bism_refl _). foo h0.
  have [n1 [r6 [h2 h3]]] := Redn_output_Wbism r h0 => {r h0}. 
  have [_ h0] := Redn_deterministic r5 h2 (Bism_refl _). foo h0.
  rewrite [Norm (Commit_output _ _)]resc_destr; simpl. 
  apply Bismc_output. 
  have := hcoind _ _ (Wbism_Setoid h3 (Bism_refl _) (Bism_sym H0))
  c c0.  by apply.   
  absurd False => //. 
  have [n1 [r5 [h2 _]]] := Redn_output_Wbism r h0 => {r h0}.
  have := Redn_Divr h2 d. by apply.   
- move => h1. dependent inversion h1; subst. 
  absurd False => //. 
  have [n1 h2] := Redn_ret_Wbism r2 (Wbism_sym h0) => {r2 h0}. 
  have := Redn_Divr h2 d. by apply. 
  absurd False => //. 
  have [n1 [f1 [h2 _]]] := Redn_input_Wbism r2 (Wbism_sym h0) => {r2 h0}. 
  have := Redn_Divr h2 d. by apply. 
  absurd False => //. 
  have [n1 [r6 [h2 h3]]] := Redn_output_Wbism r (Wbism_sym h0) => {r h0}. 
  have := Redn_Divr h2 d. by apply. 
  rewrite [Norm _]resc_destr; simpl. by apply Bismc_refl. 
Qed.   

Inductive X: stmt -> resc -> resc -> Type :=
| X_input: forall s f0 f1,
  (forall v, X s (f0 v) (f1 v)) ->
  X s (inputc f0) (inputc f1) 
| X_output: forall s r0 r1 v,
  X s r0 r1 -> X s (outputc v r0) (outputc v r1)
| X_seq: forall s r0 r1 r2 r3 (h0: Commit r0) (h1: Commit r1),
  Execseq s r0 r1 ->
  Bismc (Norm h0) r2 -> Bismc (Norm h1) r3 -> 
  X s r2 r3.

Lemma  X_Setoid: forall s0, Setoidc2 (X s0). 
Proof.  
rewrite /Setoidc2. induction 1. 
- move => r0 h0 r1 h1. foo h0. foo h1. apply X_input. move => v. 
  have := H _ _ (H1 v) _ (H2 v). by apply. 
- move => r2 h0 r3 h1. foo h0. foo h1. apply X_output. 
  have := IHX _ H3 _ H4. by apply. 
- move => r4 h2 r5 h3. have := X_seq e 
  (Bismc_trans b h2) (Bismc_trans b0 h3). 
  by apply. 
Qed. 

Lemma Execseq_Redn_ret: 
forall s r0 r1, Execseq s r0 r1 ->
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

Lemma Exec_ExecX_while_ret: forall e s, 
(forall st0 r0, Exec s st0 r0 -> (Divr r0 -> False) -> 
 forall (h: Commit r0),  ExecX X s st0 (Norm h)) -> 
forall n m r0 st0 (h0: Redn m r0 (ret st0)) st1, 
m <= n -> Exec (Swhile e s) st1 r0 -> 
ExecX X (Swhile e s) st1 (retc st0).
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
    have h8: Divr r' -> False. 
    * move => h8. have := Redn_Divr h2 h8. by apply.   
    have h5 := hs _ _ H2 h8 (Commit_ret h2) => {hs h8}. 
    rewrite [Norm _]resc_destr in h5; simpl in h5.
    have := ExecX_while_ret H1 h5 => {H1 h5}. apply. 
    have := IHn _ _ _ h4 _ _ h3. apply. omega. 
Qed.

Lemma Execseq_Redn_input: forall s r0 r1, Execseq s r0 r1 ->
forall n0 f0, Redn n0 r1 (input f0) ->
sum ({n1: nat & {st0: state &{n2: nat & {r2: res &
  ((Redn n1 r0 (ret st0)) * (Exec s st0 r2) 
   * (Redn n2 r2 (input f0)) * (n2 <= n0))%type}}}})
({n1: nat & {f1: val -> res&
  ((Redn n1 r0 (input f1) *  (forall v, Execseq s (f1 v) (f0 v))))%type}}).     
Proof. 
have: forall n0 r0 r1, Redn n0 r0 r1 ->
forall f0, Bism r1 (input f0) ->
forall s r2, Execseq s r2 r0 -> 
sum ({n1: nat & {st0: state & {n2: nat & {r3: res &
 ((Redn n1 r2 (ret st0)) * (Exec s st0 r3) *
  (Redn n2 r3 (input f0)) * (n2 <= n0))%type}}}})
({n1: nat & {f1: val -> res &
  ((Redn n1 r2 (input f1)) * 
   (forall v, Execseq s (f1 v) (f0 v)))%type}}). 
* induction 1.
  - move => f0 h0. foo h0. 
  - move => f0 h0 s0 r2 h1. foo h0. foo h1.
    - clear IHRedn. left. exists 0. exists st. exists (S n). exists (delay r0).
      split; last omega. split. split; [apply Redn_ret | done]. 
      have := Redn_Setoid (Redn_delay H) (Bism_refl _) (Bism_input (fun v => H2 v)).
      by apply. 
    - have [h0 | h0] := IHRedn _ (Bism_input (fun v => H2 v)) _ _ H4.
      - move: h0 => [n1 [st0 [n2 [r3 [h0 h1]]]]]. move: h0 => [[h0 h4] h3].
        left. exists (S n1). exists st0. exists n2. exists r3. 
        split; last omega. split; last done. 
        split; [have := Redn_delay h0; apply | done]. 
      - move: h0 => [n1 [f2 [h0 h3]]]. right. exists (S n1). 
        exists f2. split; last done. 
        have := Redn_delay h0; apply. 
    - move => f0 h0. foo h0. 
    - move => f0 h0 s0 r0 h1. foo h0. foo h1.
      - left. exists 0. exists st. exists 0. exists (input f). 
        split; last omega. split. split; [apply Redn_ret | done]. 
        apply Redn_input. move => x. have := Bism_trans (b x) (H1 x). by apply. 
      - right. exists 0. exists f1.
        have h0 := (fun v => (Bism_trans (Bism_sym (H1 v)) (Bism_sym (b v)))). 
        split. apply Redn_input. 
        move => v. apply Bism_refl. move => v. 
        have := Execseq_Setoid (H3 v) (Bism_refl _) (Bism_sym (h0 v)). 
        apply. 
move => h. move => s0 r0 r1 h0 n0 f0 h2. 
have [h4 | h4]  := h _ _ _ h2 _ (Bism_refl _)  _ _ h0.
left. apply h4. right. apply h4.                     
Qed. 



Lemma  Execseq_Redn_output: forall s r0 r1, Execseq s r0 r1 ->
forall n0 v0 r2, Redn n0 r1 (output v0 r2) ->
sum
({n1: nat & {st0: state & {n2: nat & { r3: res &
  (Redn n1 r0 (ret st0) * Exec s st0 r3  
   * Redn n2 r3 (output v0 r2) * (n2 <= n0))%type}}}})     
({n1: nat & {r3: res &
  (Redn n1 r0 (output v0 r3) * Execseq s r3 r2)%type}}). 
Proof. 
have: forall n0 r0 r1, Redn n0 r0 r1 ->
forall v0 r2, Bism r1 (output v0 r2) ->
forall s r3, Execseq s r3 r0 -> 
sum
({n1: nat & {st0: state & {n2: nat & {r4: res &
  (Redn n1 r3 (ret st0) * Exec s st0 r4 *
   Redn n2 r4 (output v0 r2) * (n2 <= n0))%type}}}})
({n1: nat & {r4: res &
  (Redn n1 r3 (output v0 r4) *  Execseq s r4 r2)%type}}).
* induction 1. 
  - move => v0 r0 h0. foo h0. 
  - move => v0 r2 h0 s r3 h1. foo h1. 
    - foo h0. clear IHRedn. left. exists 0. exists st. exists (S n). 
      exists (delay r0). split; last omega. split. split. apply Redn_ret. 
      done. apply Redn_delay. have := Redn_Setoid H (Bism_refl _) (Bism_output v0 H3).
      by apply. 
    - have [h3 | h3] := IHRedn _ _ h0 _ _ H3.
      - move: h3 => [n1 [st0 [n2 [r4 [h3 h4]]]]]. move: h3 => [[h3 h5] h6]. 
        left.  exists (S n1). exists st0. exists n2. exists r4. 
        split; last omega. split. split => //. have := Redn_delay h3. apply. done.  
      - move: h3 => [n1 [r4 [h3 h5]]]. right. exists (S n1). exists r4. 
        split => //.  have := Redn_delay h3; apply. 
  - move => v0 r2 h0 s r3 h1. foo h0. foo h1. 
    - left. exists 0. exists st. exists 0. exists (output v0 r0). split; last omega. 
      split. split => //.  apply Redn_ret. have := Redn_output _ (Bism_trans b H0).
      by apply.
    - right. exists 0. exists r. split.  have := Redn_output _ (Bism_refl _). 
      by apply. have := Execseq_Setoid H3 (Bism_refl _) (Bism_trans b H0). by apply. 
  - move => v0 r0 h0. foo h0.            
move => h. move => s r0 r1 h0 n0 v0 r2 h1.
have [h3 | h3] := h _ _ _ h1 _ _ (Bism_refl _) _ _ h0.
left; apply h3. right; apply h3.    
Qed. 

Lemma Commit_Execseq: forall r0, Commit r0 ->
forall s r1, Execseq s r1 r0 -> Commit r1. 
Proof. 
cofix hcoind. move => r0 h0 s0 r1 h1. foo h0. 
- have := Execseq_Redn_ret h1 H. move => [n0 [st0 [n1 [st1 [h0 _]]]]].
  move: h0 => [[h0 _] _]. have := Commit_ret h0.  by apply. 
- have [h0 | h0] := Execseq_Redn_input h1 H. 
  - move: h0 => [n0 [st0 [n2 [r2 h2]]]]. 
    move: h2 => [[[h0 _] _] _]. have := Commit_ret h0. by apply. 
  - move: h0 => [n1 [f1 [h0 h2]]].
    have := Commit_input h0. apply. move => v. 
    have := hcoind _ (H0 _) _ _ (h2 _). by apply.  
- have [h0 | h0] := Execseq_Redn_output h1 H. 
  - move: h0 => [n0 [st0 [n2 [r4 h0]]]]. 
    move: h0 => [[[h0 _] _] _]. have := Commit_ret h0. by apply.  
  - move: h0 => [n0 [r4 [h0 h2]]].
    have := Commit_output h0. apply. 
    have := hcoind _ H0 _ _ h2. by apply.
- have [h0 | h0] := Execseq_Divr h1 H.
  - have := Commit_divr h0. by apply. 
  - move: h0 => [n0 [st0 h0]]. have := Commit_ret h0. by apply.   
Qed.

Lemma Exec_ExecX_while_input: forall e s, 
(forall st0 r0, Exec s st0 r0 -> (Divr r0 -> False) -> 
 forall (h: Commit r0), ExecX X s st0 (Norm h)) -> 
forall n m r0 f0, Redn m r0 (input f0) ->  
m <= n -> 
forall st1, Exec (Swhile e s) st1 r0 -> 
forall (h: forall v, Commit (f0 v)),
ExecX X (Swhile e s) st1 (inputc(fun v => Norm (h v))). 
Proof.
move => e s hs. move => n. induction n. 
- move => m r0 f0 h0 h1 st0 h2. have h4: m = 0; first omega.  
  rewrite h4 in h0 => {h4}. foo h0. foo h2. foo H3. foo H6. 
- move => m r0 f0 h0 h1 st0 h2. foo h2. 
  - foo h0. foo H1. 
  - foo H2. foo H3. foo H5. foo h0. move => h.  
    have [h3 | h3] := Execseq_Redn_input H3 H4. 
    - move: h3 => [n1 [st1 [n2 [r1 [h2 h3]]]]].  
      move: h2 => [[h2 h4] h5]. 
      have h6: Divr r' -> False.
      * move => h6. have := Redn_Divr h2 h6. apply.   
      have h7 := hs _ _ H2 h6 (Commit_ret h2) => {hs h6 H2}. 
      rewrite [Norm _]resc_destr in h7; simpl in h7. 
      have := ExecX_while_ret H1 h7 => {H1 h7}. apply.  
      have h7: n2 <= n; first omega. 
      have := IHn _ _ _ h5 h7 _ h4. by apply.  
    - move: h3 => [n1 [f1 [h3 h4]]].
      have h5: Divr r' -> False. 
      * move => h5. have := Redn_Divr h3 h5; apply. 
      have h6 := (fun v => Commit_Execseq (h v) (h4 v)). 
      have := hs _ _ H2 h5 (Commit_input h3 h6) => {H2 h5 hs}.
      rewrite [Norm _]resc_destr; simpl. move => h7. 
      have := ExecX_while_input H1 h7. apply. apply X_input. 
      move => v. have := X_seq  (h4 v) (Bismc_refl _) (Bismc_refl _).
      by apply.         
Qed.

Lemma Exec_ExecX_while_output: forall e s, 
(forall st0 r0, Exec s st0 r0 -> (Divr r0 -> False) -> 
 forall (h: Commit r0), ExecX X s st0 (Norm h)) -> 
forall n m r0 v0 r1 (h0: Redn m r0 (output v0 r1)) st1, 
m <= n -> Exec (Swhile e s) st1 r0 -> 
forall (h: Commit r1),  ExecX X (Swhile e s) st1 (outputc v0 (Norm h)). 
Proof.  
move => e s hs.  move => n. induction n. 
- move => m r0 v0 r1 h1 st1 h2 h3. have h4: m = 0; first omega. 
  rewrite h4 in h1 => {h4}. foo h1. foo h3. foo H3. foo H6. 
- move => m r0 v0 r1 h0 st1 h1 h2. foo h2. 
  - foo h0. foo H1. 
  - foo H2. foo H3. foo H5. foo h0. move => h.  
    have [h0 | h0] := Execseq_Redn_output H3 H4. 
    - move: h0 => [n1 [st0 [n2 [r0 [h0 h2]]]]]. move: h0 => [[h0 h3] h4].
      have h5: Divr r' -> False. 
      * move => h5. have := Redn_Divr h0 h5; apply.  
      have := hs _ _ H2 h5 (Commit_ret h0) => {H2 h5}.
      rewrite [Norm _]resc_destr; simpl.  move => h5. 
     have := ExecX_while_ret H1 h5 => {H1 h5}. 
      apply. have := IHn _ _ _ _ h4 _ _ h3.  apply. omega. 
    - move: h0 => [n1 [r3 [h0 h2]]]. 
      have h5: Divr r' -> False. 
      * move => h5. have := Redn_Divr h0 h5; apply.
      have h7 := Commit_Execseq h h2.   
      have := hs _ _ H2 h5 (Commit_output h0 h7) => {H2 h5}.
      rewrite [Norm _]resc_destr; simpl.  move => h5.
      have := ExecX_while_output H1 h5. apply. 
      apply X_output. have := X_seq h2 (Bismc_refl _) (Bismc_refl _); by apply.  
Qed.

Lemma Execseq_Divr_L: forall s r0 r1, Execseq s r0 r1 ->
Divr r0 -> Divr r1. 
Proof. 
cofix hcoind. move => s r0 r1 h0 h1. foo h1. foo h0. 
have := Divr_delay (hcoind _ _ _ H2 H). by apply. 
Qed.  

Lemma Execseq_Commit: forall s r0 r1,
Execseq s r0 r1 -> Commit r1 -> Commit r0.
Proof. move => s. cofix hcoind. move => r0 r1 h0 h1. foo h1. 
- have := Execseq_Redn_ret h0 H => {h0 H}. 
  move => [n1 [st1 [r2 [n2 h0]]]]. move: h0 => [[[h0 h1] h2] _]. 
  have := Commit_ret h0. by apply. 
- have [h1 | h1] := Execseq_Redn_input h0 H => {h0 H}.
  - move: h1 => [n1 [st0 [n2 [r2 h0]]]]. move: h0 => [[[h0 h1] h2] _].
    have := Commit_ret h0. by apply. 
  - move: h1 => [n1 [f0 h0]]. move: h0 => [h0 h1]. 
    have := Commit_input h0. apply. move => v. 
    have := hcoind _ _ (h1 v) (H0 v). by apply. 
- have [h1 | h1] := Execseq_Redn_output h0 H => {h0 H}.
  - move: h1 => [n1 [st0 [n2 [r2 h0]]]]. move: h0 => [[[h0 h1] h2] _].
    have := Commit_ret h0. by apply. 
  - move: h1 => [n1 [r2 h0]]. move: h0 => [h0 h1]. 
    have := Commit_output h0. apply. 
    have := hcoind _ _ h1 H0. apply. 
- have [h1 | h1] := Execseq_Divr h0 H.
  - have := Commit_divr h1. by apply. 
  - move: h1 => [n0 [st0 h1]]. have := Commit_ret h1. by apply. 
Qed.    
   

Lemma Exec_ExecX: forall s st r,
Exec s st r -> (Divr r -> False) ->
forall (h: Commit r),   
ExecX X s st (Norm h).
Proof. 
move => s. induction s. 
- move => st0 r0 h0 _. foo h0. move => h. 
  dependent inversion h; subst => {h}.   
  rewrite [Norm _]resc_destr; simpl. foo r0.  
  by apply ExecX_skip. foo r0. foo r. foo d.     
- move => st0 r0 h0 _. foo h0. move => h. 
  dependent inversion h; subst => {h}. 
  rewrite [Norm _]resc_destr; simpl. foo r0. foo H1.  
  by apply ExecX_assign. absurd False => //.
  foo r0. foo H1. absurd False => //. foo r. foo H1. 
  absurd False => //. foo d. foo H0.         
- move => st0 r0 h0 h1. foo h0.
  have h2: Divr r -> False.
  * move => h0. apply h1. have := Execseq_Divr_L H4 h0. by apply. 
  move => h0. dependent inversion h0; subst;
  rewrite [Norm _]resc_destr; simpl. 
  - have := Execseq_Redn_ret H4 r2 => {r2 H4}.
    move => [n1 [st1 [r2 [n2 h3]]]]. move: h3 => [[[h4 h5]  h6] _]. 
    have h3 := IHs1 _ _ H1 (Redn_Divr h4) (Commit_ret h4).
    clear IHs1 H1. rewrite [Norm _]resc_destr in h3; simpl in h3.
    have := ExecX_seq_ret h3 => {h4 h3}. apply. 
    have := IHs2 _ _ h5 (Redn_Divr h6) (Commit_ret h6) => {H5 IHs2}.
    rewrite [Norm _]resc_destr; simpl. clear h1 h2 h0. move => h0.
    have h1 := Exec_ret h5 => {h5}.  
    have := (@X_seq _ _ _ _ _ (Commit_ret (Redn_ret st1)) 
    (Commit_ret h6) h1). apply; rewrite [Norm _]resc_destr; simpl. 
    by apply Bismc_refl. by apply Bismc_refl. 
  - have [h | h] := Execseq_Redn_input H4 r2 => {r2 H4}.
    - move: h. move => [n1 [st1 [r2 [n2 h3]]]].
      move: h3 => [[[h4 h5]  h6] _]. 
      have h3 := IHs1 _ _ H1 (Redn_Divr h4) (Commit_ret h4).
      clear IHs1 H1. rewrite [Norm _]resc_destr in h3; simpl in h3.
      have := ExecX_seq_ret h3 => {h4 h3}. apply. 
      have := IHs2 _ _ h5 (Redn_Divr h6) (Commit_input h6 c) 
      => {H5 IHs2}.
      rewrite [Norm _]resc_destr; simpl. clear h1 h2 h0. move => h0.
      have h1 := Exec_ret h5 => {h5}.  
      have := (@X_seq _ _ _ _ _ (Commit_ret (Redn_ret st1)) 
      (Commit_input h6 c) h1). apply; rewrite [Norm _]resc_destr; simpl. 
      by apply Bismc_refl. by apply Bismc_refl.
    - move: h => [n1 [f1 [h3 h4]]].  
      have := IHs1 _ _ H1 (Redn_Divr h3) 
      (Commit_input h3 (fun v => (Execseq_Commit (h4 v) (c v)))).
      rewrite [Norm _]resc_destr; simpl. move => h5. 
      have := ExecX_seq_input h5. apply. apply X_input. 
      move => v. 
      have := (@X_seq _ _ _ _ _ (Execseq_Commit (h4 v) (c v))
      (c v) (h4 v)). apply. apply Bismc_refl. apply Bismc_refl.    
  - have [h | h] := Execseq_Redn_output H4 r3 => {r3 H4}.
    - move: h. move => [n1 [st1 [n2 [r3 h3]]]].
      move: h3 => [[[h4 h5]  h6] _]. 
      have h3 := IHs1 _ _ H1 (Redn_Divr h4) (Commit_ret h4).
      clear IHs1 H1. rewrite [Norm _]resc_destr in h3; simpl in h3.
      have := ExecX_seq_ret h3 => {h4 h3}. apply. 
      have := IHs2 _ _ h5 (Redn_Divr h6) (Commit_output h6 c) 
      => {H5 IHs2}.
      rewrite [Norm _]resc_destr; simpl. clear h1 h2 h0. move => h0.
      have h1 := Exec_ret h5 => {h5}.  
      have := (@X_seq _ _ _ _ _ (Commit_ret (Redn_ret st1)) 
      (Commit_output h6 c) h1). apply; rewrite [Norm _]resc_destr; simpl. 
      by apply Bismc_refl. by apply Bismc_refl.
    - move: h => [n1 [r3 [h3 h4]]].  
      have := IHs1 _ _ H1 (Redn_Divr h3) 
      (Commit_output h3 (Execseq_Commit h4 c)). 
      rewrite [Norm _]resc_destr; simpl. move => h5. 
      have := ExecX_seq_output h5. apply. apply X_output. 
      have := (@X_seq _ _ _ _ _ (Execseq_Commit h4 c) c h4). 
      apply. apply Bismc_refl. apply Bismc_refl.
  - absurd False => //.     
- move => st0 r0 h0 h1. foo h0. 
  - clear IHs2. foo H5. foo H1. move => h0. 
     have := ExecX_ifthenelse_true _ H4. apply. 
     have h2: Divr r' -> False. 
     * move => h. apply h1. by apply Divr_delay. 
     have h3 : Commit r'.
     * have := Commit_Wbism h0 (Wbism_delay_L (Wbism_refl _)).
        by apply. 
     have := IHs1 _ _ H2 h2 h3 => {H2 h2}. move => h2. 
     have := Wbism_Norm (Wbism_delay_L (Wbism_refl _)) h0 h3.
     move => h4. have := ExecX_Setoid X_Setoid h2 (Bismc_sym h4).
     by apply. 
  - clear IHs1. foo H5. foo H1. move => h0. 
     have := ExecX_ifthenelse_false _ H4. apply. 
     have h2: Divr r' -> False. 
     * move => h. apply h1. by apply Divr_delay. 
     have h3 : Commit r'.
     * have := Commit_Wbism h0 (Wbism_delay_L (Wbism_refl _)).
        by apply. 
     have := IHs2 _ _ H2 h2 h3 => {H2 h2}. move => h2. 
     have := Wbism_Norm (Wbism_delay_L (Wbism_refl _)) h0 h3.
     move => h4. have := ExecX_Setoid X_Setoid h2 (Bismc_sym h4).
     by apply. 
- move => st0 r0 hexec hnodivr h. 
  dependent destruction h; rewrite [Norm _]resc_destr; simpl.    
  - have h1: n <= n; first omega.  
    have := Exec_ExecX_while_ret IHs r0 h1. apply. apply hexec.
  - have h1: n <= n; first omega.  
    have := Exec_ExecX_while_input IHs r0 h1 hexec. apply. 
  - have h1: n <= n; first omega.  
    have := Exec_ExecX_while_output IHs r h1 hexec. apply.
  - absurd False => //. 
- move => st0 r0 h0 _. foo h0. move => h. dependent destruction h.
  foo r0. foo r0.  rewrite [Norm _]resc_destr; simpl. foo r. foo H1. 
  dependent destruction h. dependent destruction r0. 
  rewrite [Norm _]resc_destr; simpl. apply ExecX_write. 
  foo r0. foo r. foo d. foo d.    
- move => st0 r0 h0 _. foo h0. move => h. dependent destruction h. 
  foo r0. rewrite [Norm _]resc_destr; simpl. foo r0.
  have h1: Bismc (inputc (fun v => Norm (c v))) 
  (inputc (fun v => retc (update i v st0))). 
  * apply Bismc_input. move => v. 
     have := (@Norm_irr _ _ (c v) (Commit_ret (Redn_ret _))
     (Bism_sym (H2 _))). rewrite [Norm (Commit_ret _)]resc_destr; simpl. 
     by apply. 
  have := ExecX_Setoid X_Setoid _ (Bismc_sym h1). apply.
  apply ExecX_read. foo r. foo d.   
Qed.

Lemma Redn_ret_Execseq_Divr: forall n r0 r1,
Redn n r0 r1 -> forall st0, Bism (ret st0) r1 ->
forall s r2, Execseq s r0 r2 -> Divr r2 ->
{r3: res & (Exec s st0 r3 * Divr r3)%type}.  
Proof.
induction 1. 
- move => st0 h0 s r0 h1 h2. foo h0. foo h1. exists r0. by split. 
- move => st0 h0 s r2 h1 h2. foo h1. foo h2. 
  have := IHRedn _ h0 _ _ H2 H1. by apply. 
- move => st0 h0. foo h0. 
- move => st0 h0. foo h0. 
Qed.

Lemma Exec_Execinf: forall s st r,
Exec s st r -> Divr r -> Execinf X s st.
Proof.  
cofix hcoind. move => s st0 r0 hexec hdivr. foo hexec. 
- foo hdivr. 
- foo hdivr. foo H0. 
- have [h0 | h0] := Execseq_Divr H0 hdivr. 
  - have := Execinf_seq_0 _ (hcoind _ _ _ H h0). apply. 
  - move: h0 => [n0 [st1 h0]].  
    have := Exec_ExecX H (Redn_Divr h0) (Commit_ret h0).
    rewrite [Norm _]resc_destr; simpl. move => h1.
    have [r1 [h3 h4]] := Redn_ret_Execseq_Divr h0 (Bism_refl _) H0 hdivr. 
    have := Execinf_seq_1 h1 (hcoind _ _ _ h3 h4). apply. 
- foo H0. foo H3. foo hdivr. 
  have := Execinf_ifthenelse_true _ H (hcoind _ _ _ H2 H1).
  apply.  
- foo H0. foo H3. foo hdivr. 
  have := Execinf_ifthenelse_false _ H (hcoind _ _ _ H2 H1).
  apply.
- foo hdivr. foo H1. 
- foo H0. foo H4. foo H1. foo hdivr. 
  have [h0 | h0] := Execseq_Divr H4 H1. 
  - have := Execinf_while_body H (hcoind _ _ _ H3 h0). apply. 
  - move: h0 => [n0 [st1 h0]].    
    have := Exec_ExecX H3 (Redn_Divr h0) (Commit_ret h0).
    rewrite [Norm _]resc_destr; simpl. move => h1. 
   have [r1 [h3 h4]] := Redn_ret_Execseq_Divr h0 (Bism_refl _) H4 H1. 
   have := Execinf_while_loop H h1 (hcoind _ _ _ h3 h4). apply. 
- foo hdivr.
- foo hdivr. 
Qed.

Lemma X_Execseqc: forall s, Imp_Setoid (X s) (Execseqc s).  
Proof. 
cofix hcoind. move => s r0 r1 h0 r2 hbism1 r3 hbism2. foo h0. 
- foo hbism1. foo hbism2. apply Execc_input. move => v. 
  have := hcoind _ _ _ (H v) _ (H1 v) _ (H2 v). apply.  
- foo hbism1. foo hbism2. apply Execc_output. 
  have := hcoind _ _ _ H _ H3 _ H4. apply.
- foo H. 
  - move: H0. dependent inversion h1; subst; 
    rewrite [Norm _]resc_destr; simpl => h0. foo r4. 
    foo h0. foo hbism1. move: H1. 
    dependent inversion h2; subst; rewrite [Norm _]resc_destr; simpl 
    => h0. have := Execc_ret X_Setoid. apply => //.
    foo h0. foo hbism2.  
    have := Exec_ExecX H2 (Redn_Divr r0) (Commit_ret r0).
    rewrite [Norm _]resc_destr; simpl. apply. 
    foo h0. foo hbism2. have := Execc_ret X_Setoid. apply => //.  
    have := Exec_ExecX H2 (Redn_Divr r0) (Commit_input r0 c).
    rewrite [Norm _]resc_destr; simpl. move => h0. 
    have: Bismc (inputc (fun v => Norm (c v))) (inputc f2).
    * apply Bismc_input. move => v. 
       have := Bismc_trans _ (H1 v). apply. apply H0.       
    move => h3. have := ExecX_Setoid X_Setoid h0 h3. apply. 
    foo h0. foo hbism2. have := Execc_ret X_Setoid. apply => //.  
    have := Exec_ExecX H2 (Redn_Divr r) (Commit_output r c).
    rewrite [Norm _]resc_destr; simpl. move => h0. 
    have: Bismc (outputc v (Norm c)) (outputc v r1).
    * apply Bismc_output. have := Bismc_trans H3. apply. apply H4.       
    move => h3. have := ExecX_Setoid X_Setoid h0 h3. apply. 
    foo h0. foo hbism2. have := Execc_inf X_Setoid. apply => //. 
    have := Exec_Execinf H2 d. apply. 
    foo r4. foo r. foo d.  
  - move: H0. dependent inversion h1; subst; 
    rewrite [Norm _]resc_destr; simpl => h0 {h1}. 
    foo r5. foo r5. foo r6. foo h0. foo hbism1. move: H1. 
    dependent inversion h2; subst; rewrite [Norm _]resc_destr; simpl 
    => h0 {h2}. foo r2. foo r2. foo r7. foo h0. foo hbism2. 
    apply Execc_output. have := (@X_seq _ _ _ _ _ (Commit_Setoid c
    (Bism_sym H3)) (Commit_Setoid c0 (Bism_sym H1)) H2
    (Bismc_refl _) (Bismc_refl _)) => {H2}. move => h0. 
    have := hcoind _ _ _ h0. apply. 
    have := Bismc_trans _ H6. apply. 
    have := Bismc_trans _ H5. apply. 
    apply Norm_irr. done.
    have := Bismc_trans _ H8. apply. 
    have := Bismc_trans _ H7. apply. 
    apply Norm_irr. done. foo d. foo d.  
  - move: H0. dependent inversion h1; subst; 
    rewrite [Norm _]resc_destr; simpl => h0 {h1}. 
    foo r4. foo r4. foo h0. foo hbism1. move: H1. 
    dependent inversion h2; subst; rewrite [Norm _]resc_destr; simpl 
    => h0 {h2}. foo r0. foo r0. foo h0. foo hbism2. 
    apply Execc_input. move => v. 
    have := (@X_seq _ _ _ _ _ (Commit_Setoid (c v)
    (Bism_sym (H4 _))) (Commit_Setoid (c0 _) (Bism_sym (H6 _))) (H2 _)
    (Bismc_refl _) (Bismc_refl _)) => {H2}. move => h0. 
    have := hcoind _ _ _ h0. apply.   
    have := Bismc_trans _ (H3 _). apply. 
    have := Bismc_trans _ (H0 _). apply. 
    apply Norm_irr. done.
    have := Bismc_trans _ (H5 _). apply. 
    have := Bismc_trans _ (H1 _). apply. 
    apply Norm_irr. done. foo r. foo d. foo r. foo d.   
  - move: H1. dependent inversion h2; subst;
    rewrite [Norm _]resc_destr; simpl => {h2} h0.
    - foo r5. foo h0. foo hbism2. 
      have := Execseq_Redn_ret H2 H3 => {H2 H3}.
      move => [n1 [st1 [r3 [n2 h0]]]].
      move: h0 => [[[h0 h2] h3] _].
      have := Exec_ExecX h2 (Redn_Divr h3) (Commit_ret h3). 
      rewrite [Norm _]resc_destr; simpl. move => h4. 
      move: H0. dependent inversion h1; subst;
      rewrite [Norm _]resc_destr; simpl => {h1} h1. 
      foo h1. foo hbism1. foo r4. 
      have := Redn_deterministic h0 H1 (Bism_refl _) => {h0 H1}. 
      move => [_ h0]. foo h0. 
      have := Execc_ret X_Setoid. apply => //.
      foo r4. have := Redn_deterministic h0 H1 (Bism_refl _) => {h0 H1}. 
      move => [_ h0]. foo h0. 
      foo r5. have := Redn_deterministic h0 H1 (Bism_refl _) => {h0 H1}. 
      move => [_ h0]. foo h0. 
      foo d. absurd False =>//. have := Redn_Divr h0 H0. by apply.    
    - foo r5. foo h0. foo hbism2. 
      have [h0 | h0] := Execseq_Redn_input H2 H3 => {H2 H3}.
      - move: h0 => [n1 [st0 [n2 [r1 h0]]]]. 
        move: h0 => [[[h0 h2] h3] _]. 
        have := Exec_ExecX h2 (Redn_Divr h3) (Commit_input h3 c). 
        rewrite [Norm _]resc_destr; simpl. move => h4. 
        move: H0. dependent inversion h1; subst;
        rewrite [Norm _]resc_destr; simpl => {h1} h1.
        foo r4. foo h1. foo hbism1. 
        have := Execc_ret X_Setoid; apply => //. 
        have := Redn_deterministic h0 H2 (Bism_refl _) => {h0 H2}.
        move => [_ h0]. foo h0.
        have: Bismc (inputc (fun v => Norm (c v))) (inputc f2). 
        * apply Bismc_input. move => v. have := Bismc_trans _ (H4 _). 
           apply. have := Bismc_trans _ (H1 _). apply. apply Bismc_refl.
        move => h0. have := ExecX_Setoid X_Setoid h4 h0. by apply. 
        foo r4. have := Redn_deterministic H2 h0 (Bism_refl _) => {H2 h0}.
        move => [_ h0]. foo h0.      
        foo r5. have := Redn_deterministic H2 h0 (Bism_refl _) => {H2 h0}.
        move => [_ h0]. foo h0. foo d. absurd False => //. 
        have := Redn_Divr h0 H0. by apply. 
      - move: h0 => [n1 [f3 [h0 h2]]]. move: H0. 
        dependent inversion h1; subst; 
        rewrite [Norm _]resc_destr; simpl => {h1} h1.
        foo h1. foo hbism1. foo r3. 
        have := Redn_deterministic h0 H2 (Bism_refl _). 
        move => [_ h1].  foo h1. 
        foo r3. foo h1. foo hbism1. 
        have := Redn_deterministic h0 H2 (Bism_refl _)=> {h0 H2}.
        move => [_ h0]. foo h0. apply Execc_input. move => v. 
        have h0 := Execseq_Setoid (h2 v) (H5 _) (Bism_refl _)
        => {h2 H5}.  
        have := (@X_seq _ _ _ _ _ (c0 _) (c _) h0 
        (Bismc_refl _) (Bismc_refl _)) => {h0}. move => h0.
        have := hcoind _ _ _ h0. apply. have := Bismc_trans _ (H3 _). 
        apply =>//. have := Bismc_trans _ (H4 _). apply =>//. 
        foo r4. have := Redn_deterministic h0 H2 (Bism_refl _). 
        move => [_ h3]. foo h3. foo d. 
        have := Redn_Divr h0 H0 => {h0} h0. absurd False => //.
    - foo r6. foo h0. foo hbism2. 
      have [h0 | h0] := Execseq_Redn_output H2 H3.
      - move: h0 => [n1 [st0 [n2 [r3 h0]]]]. move: h0 => [[[h0 h3] h2] _].
        have := Exec_ExecX h3 (Redn_Divr h2) (Commit_output h2 c). 
        rewrite [Norm _]resc_destr; simpl => {h2} h2.             
        move: H0. dependent inversion h1; subst; 
        rewrite [Norm _]resc_destr; simpl => {h1} h1. foo r7. 
        foo h1. foo hbism1. 
        have := Redn_deterministic h0 H1 (Bism_refl _) => {h0 H1}.
        move => [_ h0]. foo h0. 
        have := Execc_ret X_Setoid. apply => //.
        have: Bismc (outputc v (Norm c)) (outputc v r4). 
        * apply Bismc_output. have := Bismc_trans _ H6. by apply.
        move => h4. have := ExecX_Setoid X_Setoid h2 h4. apply. 
        foo r7. have := Redn_deterministic h0 H1 (Bism_refl _). 
        move => [_ h4]. foo h4. foo r8.  
        have := Redn_deterministic h0 H1 (Bism_refl _). 
        move => [_ h4]. foo h4. foo d. 
        have := Redn_Divr h0 H0 => {h0}h0. absurd False => //. 
      - move: h0 => [n1 [r3 [h0 h2]]]. move: H0. dependent inversion h1;
        subst; rewrite [Norm _]resc_destr; simpl => {h1} h1. 
        foo h1. foo hbism1. foo r7. 
        have := Redn_deterministic h0 H1 (Bism_refl _) => {h0 H1}. 
        move => [_ h0]. foo h0. foo r7.   
        have := Redn_deterministic h0 H1 (Bism_refl _) => {h0 H1}. 
        move => [_ h0]. foo h0. foo r8. 
        have := Redn_deterministic h0 H1 (Bism_refl _) => {h0 H1}. 
        move => [_ h0]. foo h0. foo h1. foo hbism1. 
        apply Execc_output. 
        have := Execseq_Setoid h2 H0 (Bism_refl _) => {h2 H0}. 
        move => h2. have := (@X_seq _ _ _ _ _ c0 c h2 (Bismc_refl _)
        (Bismc_refl _)) => {h2}. move => h2. 
        have := hcoind _ _ _ h2. apply. have := Bismc_trans _ H8. 
        by apply. have := Bismc_trans _ H6. by apply. 
        foo d. absurd False => //. have := Redn_Divr h0 H0. by apply. 
    - foo h0. foo hbism2. foo d. have [h0 | h0] := Execseq_Divr H2 H1.
      move: H0. dependent inversion h1; subst; rewrite [Norm _]resc_destr;
      simpl => {h1} h1. foo h1. foo hbism1. foo r3. absurd False => //. 
      have := Redn_Divr H3 h0. by apply. foo r3. absurd False => //. 
      have := Redn_Divr H3 h0. by apply. foo r4. absurd False => //. 
      have := Redn_Divr H3 h0. by apply. foo h1. foo hbism1. 
      apply Execc_bh.  
      move: h0 => [n0 [st0 h0]]. move: H0. dependent inversion h1; subst;
      rewrite [Norm _]resc_destr; simpl => {h1} h1.  foo r3. foo h1.
      foo hbism1. have := Redn_deterministic h0 H3 (Bism_refl _)=> {H3}.
      move => [_ h1]. foo h1. 
      have := Redn_ret_Execseq_Divr h0 (Bism_refl _) H2 H1 => {h0 H2 H1}.
      move => [r0 [h0 h1]]. have := Exec_Execinf h0 h1 => {h0 h1} h0.
      have := Execc_inf X_Setoid. apply => //. foo r3. 
      have := Redn_deterministic H3 h0 (Bism_refl _) => {h0 H3}. 
      move => [_ h0]. foo h0. foo r4. 
      have := Redn_deterministic H3 h0 (Bism_refl _) => {h0 H3}. 
      move => [_ h0]. foo h0. foo d. absurd False => //. 
      have := Redn_Divr h0 H0. by apply. 
Qed.                 

Lemma X_execseqc: forall s, Imp_Setoid (X s) (execseqc s).
Proof. 
move => s r0 r1 h0 r2 h1 r3 h2.
have := Execseqc_execseqc (X_Execseqc h0 h1 h2). by apply. 
Qed.     


Lemma Exec_Execc: forall s st r (h: Commit r), Exec s st r ->
sum (ExecX Execseqc s st (Norm h)) (Execinf Execseqc s st).
Proof. 
move => s st r h0 h1. dependent inversion h0; subst;
rewrite [Norm _]resc_destr; simpl => {h0}.     
- left. have := ExecX_monotone X_Execseqc. apply.  
  have := Exec_ExecX h1 (Redn_Divr r1) (Commit_ret r1).
  rewrite [Norm _]resc_destr; simpl. by apply. 
- left. have := ExecX_monotone X_Execseqc. apply.  
  have := Exec_ExecX h1 (Redn_Divr r1) (Commit_input r1 c).
  rewrite [Norm _]resc_destr; simpl. by apply.
- left. have := ExecX_monotone X_Execseqc. apply.  
  have := Exec_ExecX h1 (Redn_Divr r2) (Commit_output r2 c).
  rewrite [Norm _]resc_destr; simpl. by apply.
- right. have := Execinf_monotone X_Execseqc. apply.  
  have := Exec_Execinf h1 d. by apply.
Qed.     
   
Lemma bot_Divr: Divr bot. 
Proof. cofix hcoind. rewrite [bot]io_destr; simpl. 
have := Divr_delay hcoind. by apply. Qed. 

Lemma Divr_Wbism: forall r0 r1,
Divr r0 -> Divr r1 -> Wbism r0 r1.
Proof. cofix hcoind. move => r0 r1 h0 h1. foo h0; foo h1. 
have := Wbism_delay (hcoind _ _ H H0). by apply. Qed.    
 
Lemma Norm_Bism: forall r (h: Commit r), Wbism r (Emb (Norm h)).
Proof. 
cofix hcoind. move => r h0. dependent inversion h0; subst;
rewrite [Norm _]resc_destr; rewrite [Emb _]io_destr; simpl;
fold Norm.  
- have := Wbism_ret (Redn_Red r1) (Red_ret _). by apply. 
- have := Wbism_input (Redn_Red r1) (Red_input  (fun v => Bism_refl _)).
  apply. move => v. have := hcoind _ (c v). apply. 
- have := Wbism_output (Redn_Red r2) (Red_output _ (Bism_refl _)).
  apply. have := hcoind _ c. by apply. 
- have := Divr_Wbism d (Divr_delay bot_Divr). by apply. 
Qed.    
          
