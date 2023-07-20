Require Import ssreflect.
Require Export ZArith.
Require Export List.
Require Import Language. 
Require Import resumption.
Require Import Coq.Program.Equality. 
 

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* delayful big-step relational semantics *)
CoInductive Exec: stmt -> state -> res -> Type :=
| Exec_skip: forall st, 
    Exec Sskip st (ret st)
| Exec_assign: forall id a st, 
    Exec (Sassign id a) st (delay (ret (update id (a st) st)))
| Exec_seq: forall s1 s2 st r r',
    Exec s1 st r ->
    Execseq s2 r r' -> 
    Exec (Sseq s1 s2) st r'
| Exec_ifthenelse_true: forall a s1 s2 st r,
    is_true (a st) = true ->
    Execseq s1 (delay (ret st)) r ->
    Exec (Sifthenelse a s1 s2) st r
| Exec_ifthenelse_false: forall a s1 s2 st r,
    is_true (a st) = false ->
    Execseq s2 (delay (ret st)) r ->
    Exec (Sifthenelse a s1 s2) st r
| Exec_while_false: forall a s st,
    is_true (a st) = false ->
    Exec (Swhile a s) st (delay (ret st))
| Exec_while_loop: forall a s st r r',
    is_true (a st) = true ->
    Execseq s (delay (ret st)) r ->
    Execseq (Swhile a s) r r' ->
    Exec (Swhile a s) st r'
| Exec_write: forall a st,
   Exec (Swrite a) st (output (a st) (ret st))
| Exec_read: forall x st,
   Exec (Sread x) st (input (fun v => (ret (update x v st))))  
  

with Execseq: stmt -> res -> res -> Type :=
| Exec_ret: forall st s r,
  Exec s st r ->
  Execseq s (ret st) r
| Exec_output: forall s v r r',
  Execseq s r r' ->
  Execseq s (output v r) (output v r')
| Exec_input: forall s f f',
  (forall v, Execseq s (f v) (f' v)) ->
  Execseq s (input f) (input f')
| Exec_delay: forall s r r',
  Execseq s r r' ->
  Execseq s (delay r) (delay r').

Lemma Exec_Setoid: forall s st0, Setoid (Exec s st0). 
Proof. 
cofix hcoind. 
have hcoind0: forall s0, Setoid2 (Execseq s0). 
* cofix hcoind0. move => s0 r0 r1 h0 r2 h1 r3 h2. foo h0. 
  - foo h1. have := Exec_ret (hcoind _ _ _ H _ h2). by apply. 
  - foo h2; foo h1. have := Exec_output _ (hcoind0 _ _ _ H _ H4 _ H3).
    by apply. 
  - foo h1; foo h2. have := Exec_input (fun v => (hcoind0 _ _ _ (H v) _ (H1 v)
  _ (H2 v))). by apply. 
  - foo h1; foo h2. have := Exec_delay (hcoind0 _ _ _ H _ H1 _ H2). by apply. 
move => s st0 r0 h0 r1 h1. foo h0. 
- foo h1. apply Exec_skip.
- foo h1. foo H0. apply Exec_assign.
- have := Exec_seq (hcoind _ _ _ H _ (Bism_refl _)) (hcoind0 _ _ _ H0 _ (Bism_refl _)
  _ h1). by apply. 
- have := Exec_ifthenelse_true _ H (hcoind0 _ _ _ H0 _ (Bism_refl _) _ h1).
  by apply.  
- have := Exec_ifthenelse_false _ H (hcoind0 _ _ _ H0 _ (Bism_refl _) _ h1).
  by apply.
- foo h1. foo H1. have := Exec_while_false _ H. by apply. 
- have := Exec_while_loop H (hcoind0 _ _ _ H0 _ (Bism_refl _) _ (Bism_refl _))
  (hcoind0 _ _ _ H1 _ (Bism_refl _) _ h1). by apply. 
- foo h1. foo H2. apply Exec_write. 
- foo h1. have h: f1 = (fun v => ret (update x v st0)). apply extensionality. 
  move => v. have h0 := H0 v. foo h0. reflexivity. rewrite h. apply Exec_read.         
Qed. 

Lemma Execseq_Setoid: forall s, Setoid2 (Execseq s). 
Proof.
cofix hcoind0. move => s0 r0 r1 h0 r2 h1 r3 h2. foo h0. 
- foo h1. have := Exec_ret (Exec_Setoid H h2). by apply. 
- foo h2; foo h1. have := Exec_output _ (hcoind0 _ _ _ H _ H4 _ H3).
  by apply. 
- foo h1; foo h2. have := Exec_input (fun v => (hcoind0 _ _ _ (H v) _ (H1 v)
  _ (H2 v))). by apply. 
- foo h1; foo h2. have := Exec_delay (hcoind0 _ _ _ H _ H1 _ H2). by apply.  
Qed. 


(* Helper semantics to cope with Coq's guardedness *)
CoInductive Execdup: stmt -> state -> res -> Type :=
| Execdup_skip: forall st, 
    Execdup Sskip st (ret st)
| Execdup_assign: forall id a st, 
    Execdup (Sassign id a) st (delay (delay (ret (update id (a st) st))))
| Execdup_seq: forall s1 s2 st r r',
    Execdup s1 st r ->
    Execseqdup s2 r r' -> 
    Execdup (Sseq s1 s2) st r'
| Execdup_ifthenelse_true: forall a s1 s2 st r,
    is_true (a st) = true ->
    Execseqdup s1 (delay (delay (ret st))) r ->
    Execdup (Sifthenelse a s1 s2) st r
| Execdup_ifthenelse_false: forall a s1 s2 st r,
    is_true (a st) = false ->
    Execseqdup s2 (delay (delay (ret st))) r ->
    Execdup (Sifthenelse a s1 s2) st r
| Execdup_while_false: forall a s st,
    is_true (a st) = false ->
    Execdup (Swhile a s) st (delay (delay (ret st)))
| Execdup_while_loop: forall a s st r r',
    is_true (a st) = true ->
    Execseqdup s (delay (delay (ret st))) r ->
    Execseqdup (Swhile a s) r r' ->
    Execdup (Swhile a s) st r'
| Execdup_write: forall a st,
   Execdup (Swrite a) st (output (a st) (ret st))
| Execdup_read: forall x st,
   Execdup (Sread x) st (input (fun v => (ret (update x v st))))  
  

with Execseqdup: stmt -> res -> res -> Type :=
| Execdup_ret: forall st s r,
  Execdup s st r ->
  Execseqdup s (ret st) r
| Execdup_output: forall s v r r',
  Execseqdup s r r' ->
  Execseqdup s (output v r) (output v r')
| Execdup_input: forall s f f',
  (forall v, Execseqdup s (f v) (f' v)) ->
  Execseqdup s (input f) (input f')
| Execdup_delay: forall s r r',
  Execseqdup s r r' ->
  Execseqdup s (delay r) (delay r').


Lemma Execdup_Setoid: forall s st0, Setoid (Execdup s st0). 
Proof. 
cofix hcoind. 
have hcoind0: forall s0, Setoid2 (Execseqdup s0). 
* cofix hcoind0. move => s0 r0 r1 h0 r2 h1 r3 h2. foo h0. 
  - foo h1. have := Execdup_ret (hcoind _ _ _ H _ h2). by apply. 
  - foo h2; foo h1. have := Execdup_output _ (hcoind0 _ _ _ H _ H4 _ H3).
    by apply. 
  - foo h1; foo h2. have := Execdup_input (fun v => (hcoind0 _ _ _ (H v) _ (H1 v)
  _ (H2 v))). by apply. 
  - foo h1; foo h2. have := Execdup_delay (hcoind0 _ _ _ H _ H1 _ H2). by apply. 
move => s st0 r0 h0 r1 h1. foo h0. 
- foo h1. apply Execdup_skip.
- foo h1. foo H0. foo H1. apply Execdup_assign.
- have := Execdup_seq (hcoind _ _ _ H _ (Bism_refl _)) (hcoind0 _ _ _ H0 _ (Bism_refl _)
  _ h1). by apply. 
- have := Execdup_ifthenelse_true _ H (hcoind0 _ _ _ H0 _ (Bism_refl _) _ h1).
  by apply.  
- have := Execdup_ifthenelse_false _ H (hcoind0 _ _ _ H0 _ (Bism_refl _) _ h1).
  by apply.
- foo h1. foo H1. foo H2. have := Execdup_while_false _ H. by apply. 
- have := Execdup_while_loop H (hcoind0 _ _ _ H0 _ (Bism_refl _) _ (Bism_refl _))
  (hcoind0 _ _ _ H1 _ (Bism_refl _) _ h1). by apply. 
- foo h1. foo H2. apply Execdup_write. 
- foo h1. have h: f1 = (fun v => ret (update x v st0)). apply extensionality. 
  move => v. have h0 := H0 v. foo h0. reflexivity. rewrite h. apply Execdup_read.         
Qed. 

Lemma Execseqdup_Setoid: forall s, Setoid2 (Execseqdup s). 
Proof.
cofix hcoind0. move => s0 r0 r1 h0 r2 h1 r3 h2. foo h0. 
  - foo h1. have := Execdup_ret (Execdup_Setoid H h2). by apply. 
  - foo h2; foo h1. have := Execdup_output _ (hcoind0 _ _ _ H _ H4 _ H3).
    by apply. 
  - foo h1; foo h2. have := Execdup_input (fun v => (hcoind0 _ _ _ (H v) _ (H1 v)
  _ (H2 v))). by apply. 
  - foo h1; foo h2. have := Execdup_delay (hcoind0 _ _ _ H _ H1 _ H2). by apply.
Qed. 

CoFixpoint cut (r: res): res :=
match r with
| ret st => ret st
| input f => input (fun v => cut (f v))
| output v r0 => output v (cut r0)
| delay r0 =>
  match r0 with
  | delay r1 => delay (cut r1)
  | input f => r
  | output v0 r1 => r
  | ret st => r
  end
end.

Lemma cutbot: Bism bot (cut bot). 
Proof. 
cofix hcoind. rewrite [bot]io_destr; simpl. rewrite {2}[bot]io_destr; simpl. 
rewrite [cut _]io_destr; simpl. have := Bism_delay hcoind. by apply. 
Qed. 


CoInductive Cuttable: res -> Type :=
| Cut_ret: forall st, Cuttable (ret st)
| Cut_input: forall f,
  (forall v, Cuttable (f v)) ->
  Cuttable (input f)
| Cut_output: forall v r,
  Cuttable r -> Cuttable (output v r)
| Cut_delay: forall r,
  Cuttable r -> Cuttable (delay (delay r)).

Lemma Execdup_Cuttable: forall s st r,
Execdup s st r -> Cuttable r.
Proof.
move => s. induction s. 
- move => st0 r0 h0. foo h0. apply Cut_ret.  
- move => st0 r0 h0. foo h0.  apply Cut_delay. apply Cut_ret.  
- move => st0 r0 h0. foo h0. have h0 := IHs1 _ _ H1 => {IHs1 st0 H1}. 
  move: r r0 H4 h0. cofix hcoind. move => r0 r1 h0 h1. foo h0.
  - have := IHs2 _ _ H. apply. 
  - foo h1. have := Cut_output _ (hcoind _ _ H H1). by apply. 
  - foo h1. have := Cut_input (fun v => (hcoind _ _ (H v) (H1 v))). apply. 
  - foo h1. foo H. have := Cut_delay (hcoind _ _ H3 H1). apply.    
- move => st0 r0 h0. foo h0. 
  - foo H5. foo H1. foo H2. have := Cut_delay (IHs1 _ _ H1). by apply. 
  - foo H5. foo H1. foo H2. have := Cut_delay (IHs2 _ _ H1). by apply.  
- have hcoind1: forall r0 r1, Execseqdup (Swhile e s) r0 r1 -> 
  Cuttable r0 -> Cuttable r1. 
  * cofix hcoind1. move => r0 r1 h0. foo h0.
    - move => _. foo H. 
      - apply Cut_delay. apply Cut_ret.
      - foo H3. foo H1. foo H3. foo H6. foo H3. 
        have := Cut_delay (hcoind1 _ _ H4 (IHs _ _ H1)). by apply.
    - move => h0. foo h0. have := Cut_output _ (hcoind1 _ _ H H1). apply. 
    - move => h0. foo h0. have := Cut_input (fun v => (hcoind1 _ _ (H v) (H1 v))).
      apply. 
    - move => h0. foo h0. foo H. have := Cut_delay (hcoind1 _ _ H3 H1). apply. 
  move => st0 r0 h0. foo h0. 
  - apply Cut_delay. apply Cut_ret. 
  - foo H2. foo H3. foo H2. foo H5. foo H2. 
    have := Cut_delay (hcoind1 _ _ H4 (IHs _ _ H3)). apply. 
- move => st0 r0 h0. foo h0. apply Cut_output. apply Cut_ret. 
- move => st0 r0 h0. foo h0. apply Cut_input. move => v. apply Cut_ret. 
Qed.

   

Lemma Execdup_Exec: forall s st r,
Execdup s st r -> Exec s st (cut r). 
Proof. 
move => s. induction s. 
- move => st0 r0 h0. foo h0. rewrite [cut _]io_destr; simpl. apply Exec_skip.  
- move => st0 r0 h0. foo h0. rewrite [cut _]io_destr; simpl. 
  rewrite [cut _]io_destr; simpl. apply Exec_assign.  
- move => st0 r0 h0. foo h0. 
  have := Exec_seq (IHs1 _ _ H1); apply. clear IHs1. 
  have: forall r0 r1, Execseqdup s2 r0 r1 -> Cuttable r0 ->
  Execseq s2 (cut r0) (cut r1). 
  * clear r r0 H1 H4. cofix hcoind. move => r0 r1 h0 h1. foo h1;
  rewrite [cut _]io_destr; simpl.  
  - foo h0. have := Exec_ret  (IHs2 _ _ H1). by apply. 
  - foo h0. rewrite [cut (input _)]io_destr; simpl. 
    have := Exec_input (fun v => (hcoind _ _ (H2 v) (H v))). apply.  
  - foo h0. rewrite [cut (output _ _)]io_destr; simpl.
    have := Exec_output _ (hcoind _ _ H4 H). by apply. 
  - foo h0. foo H2. rewrite [cut (delay _)]io_destr; simpl. 
    have := Exec_delay (hcoind _ _ H3 H). by apply.
  apply. apply H4. have := Execdup_Cuttable H1. by apply.
- move => st0 r0 h0. foo h0. 
  - foo H5. foo H1. foo H2. rewrite [cut _]io_destr. simpl. 
    have := Exec_ifthenelse_true _ H4 (Exec_delay (Exec_ret (IHs1 _ _ H1))) => {H1}.
    by apply. 
  - foo H5. foo H1. foo H2. rewrite [cut _]io_destr. simpl. 
    have := Exec_ifthenelse_false _ H4 (Exec_delay (Exec_ret (IHs2 _ _ H1))) => {H1}.
    by apply.      
- cofix hcoind0. 
  have hcoind1: forall r0 r1, Execseqdup (Swhile e s) r0 r1 ->
  Cuttable r0 -> 
  Execseq (Swhile e s) (cut r0) (cut r1).
  * cofix hcoind1. move => r0 r1 h0 h1. foo h1.
    - foo h0. rewrite [cut _]io_destr; simpl. 
      have := Exec_ret (hcoind0 _ _ H1). apply. 
    - foo h0. rewrite [cut _]io_destr; simpl. 
      rewrite [cut (input _)]io_destr; simpl. 
      have := Exec_input (fun v => hcoind1 _ _ (H2 v) (H v)). by apply. 
    - foo h0. rewrite [cut _]io_destr; simpl. 
      rewrite [cut (output _ _)]io_destr; simpl. 
      have := Exec_output _ (hcoind1 _ _ H4 H). apply. 
    - foo h0. foo H2. rewrite [cut _]io_destr; simpl. 
      rewrite [cut (delay _)]io_destr; simpl. 
      have := Exec_delay (hcoind1 _ _ H3 H). apply. 
  move => st0 r0 h0. foo h0. 
  - rewrite [cut _]io_destr; simpl. rewrite [cut _]io_destr; simpl. 
    have := Exec_while_false _ H3. by apply.
  - foo H2. foo H3. foo H2. foo H5. foo H2. 
    rewrite [cut _]io_destr; simpl. 
    have := Exec_while_loop H1 (Exec_delay (Exec_ret (IHs _ _ H3)))  
    (Exec_delay (hcoind1 _ _ H4 (Execdup_Cuttable H3))). apply. 
- move => st0 r0 h0. foo h0. rewrite [cut _]io_destr; simpl. 
  rewrite [cut _]io_destr; simpl. apply Exec_write. 
- move => st0 r0 h0. foo h0. rewrite [cut _]io_destr; simpl.
  have h0: Bism (input (fun v => cut (ret (update i v st0))))
  (input (fun v => ret (update i v st0))). 
  * apply Bism_input. move => v. rewrite [cut _]io_destr; simpl. 
    apply Bism_refl. 
  have := Exec_Setoid _ (Bism_sym h0). apply.
  apply Exec_read.    
Qed.

Inductive steps: res -> res -> Prop :=
| steps_stop: forall r0 r1, bism r0 r1 -> steps r0 r1
| steps_delay: forall r0 r1, steps r0 r1 -> steps (delay r0) r1.

Lemma steps_setoid_bin: setoid2 steps. 
Proof. 
apply skip.  (* proved in Type *)
Qed.  

(* wbism1 allows one or more delay steps to be removed by the delay rule *)
CoInductive wbism1: res -> res -> Prop :=
| wbism1_ret: forall r0 r1 st,
  red r0 (ret st) -> red r1 (ret st) -> wbism1 r0 r1
| wbism1_output: forall v r0 r0' r1 r1',
  red r0 (output v r0') -> red r1 (output v r1') -> wbism1 r0' r1' -> 
  wbism1 r0 r1
| wbism1_input: forall r0 r1 f0 f1,
  red r0 (input f0) -> red r1 (input f1) -> (forall v, wbism1 (f0 v) (f1 v)) ->
  wbism1 r0 r1
| wbism1_delay: forall r0 r1 r2 r3,
  wbism1 r1 r3 ->
  steps r0 r1 -> steps r2 r3 ->
  wbism1 (delay r0) (delay r2).

Lemma wbism1_refl: forall r, wbism1 r r.
Proof.
cofix hcoind. case. 
- move => st0. have := wbism1_ret (red_ret _) (red_ret _). apply. 
- move => v0 r0. have := wbism1_output (red_output _ (bism_refl _))
  (red_output _ (bism_refl _)) (hcoind _). apply. 
- move => f. have := wbism1_input (red_input (fun v => bism_refl _))
  (red_input (fun v => bism_refl _)) (fun v => hcoind _). apply. 
- move => r0. have := wbism1_delay (hcoind _)
  (steps_stop (bism_refl _)) (steps_stop (bism_refl _)). apply.  
Qed. 

Lemma steps_red: forall r0 r1, steps r0 r1 ->
forall r2, red r1 r2 -> red r0 r2.
Proof. 
induction 1. 
- move => r2 h0. have := red_setoid h0 (bism_sym H) (bism_refl _). 
  by apply. 
- move => r2 h0. have := red_delay (IHsteps _ h0). by apply. 
Qed.

Lemma steps_trans: forall r0 r1, steps r0 r1 ->
forall r2, steps r1 r2 -> steps r0 r2. 
Proof. 
induction 1. 
- move => r3 h0. have := steps_setoid_bin h0 (bism_sym H) (bism_refl _). apply.  
- move => r2 h0. have := steps_delay (IHsteps _ h0). apply. 
Qed.
 

Lemma wbism1_wbism: forall r0 r1 r2 r3, 
steps r0 r1 -> steps r2 r3 -> wbism1 r1 r3 -> wbism r0 r2. 
Proof.
cofix hcoind. 
move => r0 r1 r2 r3 h0 h1 h2. foo h2.
- have h2 := steps_red h0 H => {h0 H}. 
  have h3 := steps_red h1 H0 => {h1 H0}. 
  have := wbism_ret h2 h3. by apply.
- have h2 := steps_red h0 H => {h0 H}.
  have h3 := steps_red h1 H0 => {h1 H0}. 
  have := wbism_output h2 h3 (hcoind _ _ _ _ (steps_stop (bism_refl _))
  (steps_stop (bism_refl _)) H1). by apply. 
- have h2 := steps_red h0 H => {h0 H}. 
  have h3 := steps_red h1 H0 => {h1 H0}. 
  have :=  wbism_input h2 h3 (fun v => hcoind _ _ _ _ (steps_stop (bism_refl _))
  (steps_stop (bism_refl _)) (H1 v)). by apply. 
- foo h1; foo h0. 
  - foo H2. foo H3. have := wbism_delay (hcoind _ _ _ _ 
    (steps_setoid_bin H0 (bism_sym H5) (bism_refl _))
    (steps_setoid_bin H1 (bism_sym H6) (bism_refl _)) H). apply. 
  - foo H2.
    have h0 := steps_trans H3 (steps_delay H0) => {H3 H0}.
    have h1 := steps_setoid_bin H1 (bism_sym H6) (bism_refl _). 
    have := wbism_delay (hcoind _ _ _ _ h0 h1 H). apply. 
  - foo H3. 
    have h0 := steps_setoid_bin H0 (bism_sym H6) (bism_refl _). 
    have h1 := steps_trans H2 (steps_delay H1). 
    have := wbism_delay (hcoind _ _ _ _ h0 h1 H). apply. 
  - have h0 := steps_trans H3 (steps_delay H0).
    have h1 := steps_trans H2 (steps_delay H1). 
    have := wbism_delay (hcoind _ _ _ _ h0 h1 H). apply. 
Qed.    
  
Lemma cut_wbism1: forall r, wbism1 r (cut r). 
Proof. 
cofix hcoind. case. 
- move => st0. rewrite [cut _]io_destr; simpl. 
  have := wbism1_ret (red_ret st0) (red_ret st0). apply.  
- move => v0 r0. rewrite [cut _]io_destr; simpl. 
  have := wbism1_output (red_output _ (bism_refl _))
  (red_output _ (bism_refl _)) (hcoind _). apply. 
- move => f. rewrite [cut _]io_destr; simpl. 
  have := wbism1_input (red_input (fun v => bism_refl _))
  (red_input (fun v => bism_refl _)) (fun v => hcoind _). apply.  
- case. 
  - move => st0. rewrite [cut _]io_destr; simpl. 
    have := wbism1_ret (red_delay (red_ret st0))
    (red_delay (red_ret st0)). apply.  
  - move => v0 r0. rewrite [cut _]io_destr; simpl. 
    have := wbism1_output (red_delay (red_output _ (bism_refl _)))
    (red_delay (red_output _ (bism_refl _))) (wbism1_refl _). apply.
  - move => f. rewrite [cut _]io_destr; simpl. 
    have := wbism1_input (red_delay (red_input (fun v => bism_refl _)))
    (red_delay (red_input (fun v => bism_refl _)))
    (fun v => wbism1_refl _). apply. 
  - move => r0. rewrite [cut _]io_destr; simpl. 
    have h0 := steps_delay (steps_stop (bism_refl r0)).
    have h1 := steps_stop (bism_refl (cut r0)). 
    have := wbism1_delay (hcoind r0) h0 h1.
    apply. 
Qed.

Lemma cut_wbism: forall r, wbism r (cut r).
Proof. 
move => r. have := wbism1_wbism (steps_stop (bism_refl _))
(steps_stop (bism_refl _)). apply. apply cut_wbism1.
Qed.     
    
