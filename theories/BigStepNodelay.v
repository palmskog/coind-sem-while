Require Import ssreflect. 
Require Export ZArith.
Require Export List.
Require Import Language. 
Require Import resumption.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

CoInductive resd: Set := 
| retd: state -> resd
| outputd: val -> resd -> resd
| inputd: (val -> resd) -> resd.

Lemma resd_destr: forall r, r = match r with
| retd st => retd st
| outputd v r' => outputd v r'
| inputd f => inputd f
end.
Proof. case; simpl => //. Qed.

Axiom extensionality: forall (f g: val -> resd),
(forall v, f v = g v) -> f = g.   

(* strong bisimilarity *)
CoInductive Bismd: resd -> resd -> Type :=
| Bismd_ret: forall st,
  Bismd (retd st) (retd st)
| Bismd_input: forall f0 f1,
  (forall v, Bismd (f0 v) (f1 v)) ->
  Bismd (inputd f0) (inputd f1)
| Bismd_output: forall r0 r1 v,
  Bismd r0 r1 ->
  Bismd (outputd v r0) (outputd v r1). 

Lemma Bismd_refl: forall r, Bismd r r.
Proof. 
apply skip. (* same as bism_refl *)
Qed.

Lemma Bismd_sym: forall r0 r1, Bismd r0 r1 -> Bismd r1 r0. 
Proof.
apply skip. (* same as bism_sym *)
Qed. 

Lemma Bismd_trans: forall r0 r1 r2, Bismd r0 r1 -> Bismd r1 r2 ->
Bismd r0 r2.
Proof.
apply skip. (* same as bism_trans *)
Qed. 

Definition Setoidd (X:resd -> Type) :=
forall r0, X r0 -> forall r1, Bismd r0 r1 -> X r1. 

Definition Setoidd2 (X: resd -> resd -> Type) :=
forall r0 r1, X r0 r1 -> forall r2, Bismd r0 r2 ->
forall r3, Bismd r1 r3 -> X r2 r3. 

CoFixpoint Emb (r: resd): res :=
match r with
| retd st => ret st
| inputd f => input (fun v => Emb (f v))
| outputd v r0 => output v (Emb r0)
end.

CoFixpoint Norm (r: res) (h: Resp r): resd :=
match h with
| Resp_ret n r st h0 => retd st
| Resp_input n r f h0 h1 => inputd (fun v => Norm (h1 v))
| Resp_output n v r0 r1 h0 h1 => outputd v (Norm h1)
end. 

Inductive ExecX (X:stmt -> resd -> resd -> Type): stmt -> state -> resd -> Type :=
| ExecX_skip: forall st, 
    ExecX X Sskip st (retd st)
| ExecX_assign: forall id a st, 
    ExecX X (Sassign id a) st (retd (update id (a st) st))
| ExecX_seq_ret: forall s1 s2 st0 st1 r,
    ExecX X s1 st0 (retd st1) ->
    X s2 (retd st1) r -> 
    ExecX X (Sseq s1 s2) st0 r
| ExecX_seq_input: forall s1 s2 st f r,
    ExecX X s1 st (inputd f) ->
    X s2 (inputd f) r -> 
    ExecX X (Sseq s1 s2) st r
| ExecX_seq_output: forall s1 s2 st v r0 r1,
    ExecX X s1 st (outputd v r0) ->
    X s2 (outputd v r0) r1 -> 
    ExecX X (Sseq s1 s2) st r1
| ExecX_ifthenelse_true: forall a s1 s2 st r,
    is_true (a st) = true ->
    ExecX X s1 st r ->
    ExecX X (Sifthenelse a s1 s2) st r
| ExecX_ifthenelse_false: forall a s1 s2 st r,
    is_true (a st) = false ->
    ExecX X s2 st r ->
    ExecX X (Sifthenelse a s1 s2) st r
| ExecX_while_false: forall a s st,
    is_true (a st) = false ->
    ExecX X (Swhile a s) st (retd st)
| ExecX_while_ret: forall a s st0 st1 r, 
    is_true (a st0) = true ->
    ExecX X s st0 (retd st1) ->
    ExecX X (Swhile a s) st1 r -> 
    ExecX X (Swhile a s) st0 r
| ExecX_while_input: forall a s st f0 r,
    is_true (a st) = true ->
    ExecX X s st (inputd f0) ->
    X (Swhile a s) (inputd f0) r ->
    ExecX X  (Swhile a s) st r
| ExecX_while_output: forall a s st v r r',
    is_true (a st) = true ->
    ExecX X s st (outputd v r) ->
    X (Swhile a s) (outputd v r) r' -> 
    ExecX X  (Swhile a s) st r'
| ExecX_write: forall a st,
   ExecX X (Swrite a) st (outputd (a st) (retd st))
| ExecX_read: forall x st,
   ExecX X (Sread x) st (inputd (fun v => (retd (update x v st)))).  
  
Definition Imp_Setoid (X Y: resd -> resd -> Type) :=
forall r0 r1, X r0 r1 -> 
forall r2, Bismd r0 r2 -> forall r3, Bismd r1 r3 -> Y r2 r3. 

CoInductive Execseqnd (s: stmt): resd -> resd -> Type :=
| Execnd_ret: forall X st r,
  (forall s0, Setoidd2 (X s0)) -> 
  (forall s0, Imp_Setoid (X s0) (Execseqnd s0)) ->
  ExecX X s st r ->
  Execseqnd s (retd st) r
| Execnd_output: forall v r r',
  Execseqnd s r r' ->
  Execseqnd s (outputd v r) (outputd v r')
| Execnd_input: forall f f',
  (forall v, Execseqnd s (f v) (f' v)) ->
  Execseqnd s (inputd f) (inputd f').


Lemma ExecX_monotone: forall X Y,
(forall s, Imp_Setoid (X s) (Y s)) ->
forall s st r, ExecX X s st r -> ExecX Y s st r. 
Proof.
move => X Y hXY. induction 1.
- apply ExecX_skip. 
- by apply ExecX_assign. 
- have := ExecX_seq_ret IHX0. apply. 
  have := hXY _ _ _ x  _ (Bismd_refl _) _ (Bismd_refl _). by apply. 
- have := ExecX_seq_input IHX0. apply. 
  have := hXY _ _ _ x  _ (Bismd_refl _) _ (Bismd_refl _). by apply.
- have := ExecX_seq_output IHX0. apply. 
  have := hXY _ _ _ x  _ (Bismd_refl _) _ (Bismd_refl _). by apply.
- have := ExecX_ifthenelse_true _ e IHX0. by apply. 
- have := ExecX_ifthenelse_false _ e IHX0. by apply.
- have := ExecX_while_false _ _ e. by apply. 
- have := ExecX_while_ret e IHX0_1 IHX0_2. by apply.   
- have := ExecX_while_input e IHX0. apply. 
  have := hXY _ _ _ x _ (Bismd_refl _ ) _ (Bismd_refl _). by apply. 
- have := ExecX_while_output e IHX0. apply. 
  have := hXY _ _ _ x _ (Bismd_refl _ ) _ (Bismd_refl _). by apply.
- apply ExecX_write. 
- by apply ExecX_read.  
Qed. 

Lemma ExecX_Setoid: 
forall X, (forall s, Setoidd2 (X s)) -> 
forall s st0, Setoidd (ExecX X s st0).
Proof.
move => X hX. rewrite /Setoidd. induction 1. 
- move => r0 h0. foo h0. by apply ExecX_skip. 
- move => r0 h0. foo h0. by apply ExecX_assign. 
- move => r0 h0. have h1 := hX _ _ _ x _ (Bismd_refl _) _ h0 => {h0}.
  have := ExecX_seq_ret X0 h1. by apply. 
- move => r0 h0. have h1 := hX _ _ _ x _ (Bismd_refl _) _ h0 => {h0}.
  have := ExecX_seq_input X0 h1. by apply.
- move => r2 h0. have h1 := hX _ _ _ x _ (Bismd_refl _) _ h0 => {h0}.
  have := ExecX_seq_output X0 h1. by apply.
- move => r0 h0. 
 have := ExecX_ifthenelse_true _  e (IHX0 _ h0). by apply.   
- move => r0 h0. 
 have := ExecX_ifthenelse_false _  e (IHX0 _ h0). by apply.
- move => r0 h0. foo h0. have := ExecX_while_false _ _ e. by apply. 
- move => r0 h0. have := ExecX_while_ret e X0_1 (IHX0_2 _ h0). 
  by apply. 
- move => r0 h0. have := ExecX_while_input e X0. apply. 
  have := hX _ _ _ x _ (Bismd_refl _) _ h0. by apply.      
- move => r0 h0. have := ExecX_while_output e X0. apply. 
  have := hX _ _ _ x _ (Bismd_refl _) _ h0. by apply.
- move => r0 h0. foo h0. foo H2. by apply ExecX_write.
- move => r0 h0. foo h0. 
  have h1: (fun v => retd (update x v st)) = f1. 
  * apply extensionality. move => v. have h1:= H0 v. by foo h1.
  rewrite -h1. by apply ExecX_read.     
Qed.   

Lemma Execseqnd_Setoid: forall s, Setoidd2 (Execseqnd s). 
Proof. 
cofix hcoind. move => s r0 r1 h0. foo h0. 
- move => r0 h0 r2 h1. foo h0. have := Execnd_ret X0 X1. apply. 
  have := ExecX_Setoid X0 X2 h1. by apply. 
- move => r0 h0 r1 h1. foo h0. foo h1. 
  have := Execnd_output _ (hcoind _ _ _ X _ H2 _ H3). by apply. 
- move => r0 h0 r1 h1. foo h0. foo h1. 
  have := Execnd_input (fun v =>  (hcoind _ _ _ (X _) _ (H0 v) _ (H1 v))).
  by apply.  
Qed. 


Inductive execX (X:stmt -> resd -> resd -> Prop): stmt -> state -> resd -> Prop :=
| execX_skip: forall st, 
    execX X Sskip st (retd st)
| execX_assign: forall id a st, 
    execX X (Sassign id a) st (retd (update id (a st) st))
| execX_seq_ret: forall s1 s2 st0 st1 r,
    execX X s1 st0 (retd st1) ->
    X s2 (retd st1) r -> 
    execX X (Sseq s1 s2) st0 r
| execX_seq_input: forall s1 s2 st f r,
    execX X s1 st (inputd f) ->
    X s2 (inputd f) r -> 
    execX X (Sseq s1 s2) st r
| execX_seq_output: forall s1 s2 st v r0 r1,
    execX X s1 st (outputd v r0) ->
    X s2 (outputd v r0) r1 -> 
    execX X (Sseq s1 s2) st r1
| execX_ifthenelse_true: forall a s1 s2 st r,
    is_true (a st) = true ->
    execX X s1 st r ->
    execX X (Sifthenelse a s1 s2) st r
| execX_ifthenelse_false: forall a s1 s2 st r,
    is_true (a st) = false ->
    execX X s2 st r ->
    execX X (Sifthenelse a s1 s2) st r
| execX_while_false: forall a s st,
    is_true (a st) = false ->
    execX X (Swhile a s) st (retd st)
| execX_while_ret: forall a s st0 st1 r, 
    is_true (a st0) = true ->
    execX X s st0 (retd st1) ->
    execX X (Swhile a s) st1 r -> 
    execX X (Swhile a s) st0 r
| execX_while_input: forall a s st f0 r,
    is_true (a st) = true ->
    execX X s st (inputd f0) ->
    X (Swhile a s) (inputd f0) r ->
    execX X  (Swhile a s) st r
| execX_while_output: forall a s st v r r',
    is_true (a st) = true ->
    execX X s st (outputd v r) ->
    X (Swhile a s) (outputd v r) r' -> 
    execX X  (Swhile a s) st r'
| execX_write: forall a st,
   execX X (Swrite a) st (outputd (a st) (retd st))
| execX_read: forall x st,
   execX X (Sread x) st (inputd (fun v => (retd (update x v st)))).  

(*
Definition imp_setoid_bin (X Y: io -> io -> Prop) :=
forall r0 r1, X r0 r1 -> 
forall r2, bism r0 r2 -> forall r3, bism r1 r3 -> Y r2 r3. 
*)

CoInductive execseqnd (s: stmt): resd -> resd -> Prop :=
| execnd_ret: forall X st r,
  (forall s0, Setoidd2 (X s0)) -> 
  (forall s0, Imp_Setoid (X s0) (execseqnd s0)) ->
  ExecX X s st r ->
  execseqnd s (retd st) r
| execnd_output: forall v r r',
  execseqnd s r r' ->
  execseqnd s (outputd v r) (outputd v r')
| execnd_input: forall f f',
  (forall v, execseqnd s (f v) (f' v)) ->
  execseqnd s (inputd f) (inputd f').

Lemma execseqnd_Setoid: forall s, Setoidd2 (execseqnd s).
Proof. 
apply skip. (* proved in Set *)
Qed. 

Axiom execseqnd_Execseqnd: forall s, 
Imp_Setoid (execseqnd s) (Execseqnd s). 

