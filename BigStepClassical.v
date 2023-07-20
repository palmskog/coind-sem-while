Require Import ssreflect. 
Require Export ZArith.
Require Export List.
Require Import Language. 
Require Import resumption.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

CoInductive resc: Set := 
| retc: state -> resc
| outputc: val -> resc -> resc
| inputc: (val -> resc) -> resc
| bh: resc. 

Lemma resc_destr: forall r, r = match r with
| retc st => retc st
| outputc v r' => outputc v r'
| inputc f => inputc f
| bh => bh
end.
Proof. case; simpl => //. Qed.

Axiom extensionality: forall (f g: val -> resc),
(forall v, f v = g v) -> f = g.   



(* strong bisimilarity *)
CoInductive Bismc: resc -> resc -> Type :=
| Bismc_ret: forall st,
  Bismc (retc st) (retc st)
| Bismc_input: forall f0 f1,
  (forall v, Bismc (f0 v) (f1 v)) ->
  Bismc (inputc f0) (inputc f1)
| Bismc_output: forall r0 r1 v,
  Bismc r0 r1 ->
  Bismc (outputc v r0) (outputc v r1)
| Bismc_bh: Bismc bh bh. 

Lemma Bismc_refl: forall r, Bismc r r.
Proof. 
apply skip. (* same as Bism_refl *)
Qed.

Lemma Bismc_sym: forall r0 r1, Bismc r0 r1 -> Bismc r1 r0. 
Proof.
apply skip.  (* same as Bism_sym *)
Qed. 

Lemma Bismc_trans: forall r0 r1 r2, Bismc r0 r1 -> Bismc r1 r2 ->
Bismc r0 r2.
Proof.
apply skip.  (* same as Bism_trans *)
Qed. 

Definition Setoidc (X:resc -> Type) :=
forall r0, X r0 -> forall r1, Bismc r0 r1 -> X r1. 

Definition Setoidc2 (X: resc -> resc -> Type) :=
forall r0 r1, X r0 r1 -> forall r2, Bismc r0 r2 ->
forall r3, Bismc r1 r3 -> X r2 r3. 


CoFixpoint Emb (r: resc): res :=
match r with
| retc st => ret st
| inputc f => input (fun v => Emb (f v))
| outputc v r0 => output v (Emb r0)
| bh => bot
end.

CoFixpoint Norm (r: res) (h: Commit r): resc :=
match h with
| Commit_ret n r st h0 => retc st
| Commit_input n r f h0 h1 => inputc (fun v => Norm (h1 v))
| Commit_output n v r0 r1 h0 h1 => outputc v (Norm h1)
| Commit_divr r h0 => bh
end. 

Inductive ExecX (X:stmt -> resc -> resc -> Type): stmt -> state -> resc -> Type :=
| ExecX_skip: forall st, 
    ExecX X Sskip st (retc st)
| ExecX_assign: forall id a st, 
    ExecX X (Sassign id a) st (retc (update id (a st) st))
| ExecX_seq_ret: forall s1 s2 st0 st1 r,
    ExecX X s1 st0 (retc st1) ->
    X s2 (retc st1) r -> 
    ExecX X (Sseq s1 s2) st0 r
| ExecX_seq_input: forall s1 s2 st f r,
    ExecX X s1 st (inputc f) ->
    X s2 (inputc f) r -> 
    ExecX X (Sseq s1 s2) st r
| ExecX_seq_output: forall s1 s2 st v r0 r1,
    ExecX X s1 st (outputc v r0) ->
    X s2 (outputc v r0) r1 -> 
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
    ExecX X (Swhile a s) st (retc st)
| ExecX_while_ret: forall a s st0 st1 r, 
    is_true (a st0) = true ->
    ExecX X s st0 (retc st1) ->
    ExecX X (Swhile a s) st1 r -> 
    ExecX X (Swhile a s) st0 r
| ExecX_while_input: forall a s st f0 r,
    is_true (a st) = true ->
    ExecX X s st (inputc f0) ->
    X (Swhile a s) (inputc f0) r ->
    ExecX X  (Swhile a s) st r
| ExecX_while_output: forall a s st v r r',
    is_true (a st) = true ->
    ExecX X s st (outputc v r) ->
    X (Swhile a s) (outputc v r) r' -> 
    ExecX X  (Swhile a s) st r'
| ExecX_write: forall a st,
   ExecX X (Swrite a) st (outputc (a st) (retc st))
| ExecX_read: forall x st,
   ExecX X (Sread x) st (inputc (fun v => (retc (update x v st)))).  
  
Definition Imp_Setoid (X Y: resc -> resc -> Type) :=
forall r0 r1, X r0 r1 -> 
forall r2, Bismc r0 r2 -> forall r3, Bismc r1 r3 -> Y r2 r3. 

CoInductive Execinf (X: stmt -> resc -> resc -> Type) : stmt -> state -> Type :=
| Execinf_seq_0: forall s0 s1 st,
  Execinf X s0 st ->
  Execinf X (Sseq s0 s1) st
| Execinf_seq_1: forall s0 s1 st0 st1,
  ExecX X s0 st0 (retc st1) ->
  Execinf X s1 st1 ->
  Execinf X (Sseq s0 s1) st0
| Execinf_ifthenelse_true: forall e s0 s1 st,
  is_true (e st) = true ->
  Execinf X s0 st ->
  Execinf X (Sifthenelse e s0 s1) st
| Execinf_ifthenelse_false: forall e s0 s1 st,
  is_true (e st) = false ->
  Execinf X s1 st ->
  Execinf X (Sifthenelse e s0 s1) st
| Execinf_while_body: forall e s st,
  is_true (e st) = true ->
  Execinf X s st ->
  Execinf X (Swhile e s) st
| Execinf_while_loop: forall e s st0 st1, 
  is_true (e st0) = true ->
  ExecX X s st0 (retc st1) ->
  Execinf X (Swhile e s) st1 ->
  Execinf X (Swhile e s) st0.

Lemma ExecX_Setoid: 
forall X, (forall s, Setoidc2 (X s)) -> 
forall s st0, Setoidc (ExecX X s st0).
Proof.
move => X hX. rewrite /Setoidc. induction 1. 
- move => r0 h0. foo h0. by apply ExecX_skip. 
- move => r0 h0. foo h0. by apply ExecX_assign. 
- move => r0 h0. have h1 := hX _ _ _ x _ (Bismc_refl _) _ h0 => {h0}.
  have := ExecX_seq_ret X0 h1. by apply. 
- move => r0 h0. have h1 := hX _ _ _ x _ (Bismc_refl _) _ h0 => {h0}.
  have := ExecX_seq_input X0 h1. by apply.
- move => r2 h0. have h1 := hX _ _ _ x _ (Bismc_refl _) _ h0 => {h0}.
  have := ExecX_seq_output X0 h1. by apply.
- move => r0 h0. 
 have := ExecX_ifthenelse_true _  e (IHX0 _ h0). by apply.   
- move => r0 h0. 
 have := ExecX_ifthenelse_false _  e (IHX0 _ h0). by apply.
- move => r0 h0. foo h0. have := ExecX_while_false _ _ e. by apply. 
- move => r0 h0. have := ExecX_while_ret e X0_1 (IHX0_2 _ h0). 
  by apply. 
- move => r0 h0. have := ExecX_while_input e X0. apply. 
  have := hX _ _ _ x _ (Bismc_refl _) _ h0. by apply.      
- move => r0 h0. have := ExecX_while_output e X0. apply. 
  have := hX _ _ _ x _ (Bismc_refl _) _ h0. by apply.
- move => r0 h0. foo h0. foo H2. by apply ExecX_write.
- move => r0 h0. foo h0. 
  have h1: (fun v => retc (update x v st)) = f1. 
  * apply extensionality. move => v. have h1:= H0 v. by foo h1.
  rewrite -h1. by apply ExecX_read.     
Qed.

Lemma ExecX_monotone: forall X Y,
(forall s, Imp_Setoid (X s) (Y s)) ->
forall s st r, ExecX X s st r -> ExecX Y s st r. 
Proof.
move => X Y hXY. induction 1.
- apply ExecX_skip. 
- by apply ExecX_assign. 
- have := ExecX_seq_ret IHX0. apply. 
  have := hXY _ _ _ x  _ (Bismc_refl _) _ (Bismc_refl _). by apply. 
- have := ExecX_seq_input IHX0. apply. 
  have := hXY _ _ _ x  _ (Bismc_refl _) _ (Bismc_refl _). by apply.
- have := ExecX_seq_output IHX0. apply. 
  have := hXY _ _ _ x  _ (Bismc_refl _) _ (Bismc_refl _). by apply.
- have := ExecX_ifthenelse_true _ e IHX0. by apply. 
- have := ExecX_ifthenelse_false _ e IHX0. by apply.
- have := ExecX_while_false _ _ e. by apply. 
- have := ExecX_while_ret e IHX0_1 IHX0_2. by apply.   
- have := ExecX_while_input e IHX0. apply. 
  have := hXY _ _ _ x _ (Bismc_refl _ ) _ (Bismc_refl _). by apply. 
- have := ExecX_while_output e IHX0. apply. 
  have := hXY _ _ _ x _ (Bismc_refl _ ) _ (Bismc_refl _). by apply.
- apply ExecX_write. 
- by apply ExecX_read.  
Qed.    

Lemma Execinf_monotone: forall X Y,
(forall s, Imp_Setoid (X s) (Y s)) ->
forall s st, Execinf X s st -> Execinf Y s st. 
Proof.
move => X Y hXY. cofix hcoind. move => s0 st0 h0. foo h0. 
- have := Execinf_seq_0 _ (hcoind _ _ X0). by apply. 
- have := Execinf_seq_1 (ExecX_monotone hXY X0) (hcoind _ _ X1). by apply. 
- have := Execinf_ifthenelse_true _ H (hcoind _ _ X0). by apply.    
- have := Execinf_ifthenelse_false _ H (hcoind _ _ X0). by apply.
- have := Execinf_while_body H (hcoind _ _ X0). by apply. 
- have := Execinf_while_loop H (ExecX_monotone hXY X0) (hcoind _ _ X1). 
  by apply.  
Qed. 
  

CoInductive Execseqc (s: stmt): resc -> resc -> Type :=
| Execc_ret: forall X st r,
  (forall s0,  Setoidc2 (X s0)) ->
  (forall s0, Imp_Setoid (X s0) (Execseqc s0)) ->
  ExecX X s st r ->
  Execseqc s (retc st) r
| Execc_input: forall f0 f1,
  (forall v, Execseqc s (f0 v) (f1 v)) ->
  Execseqc s (inputc f0) (inputc f1) 
| Execc_output: forall v r0 r1,
  Execseqc s r0 r1 ->
  Execseqc s (outputc v r0) (outputc v r1)
| Execc_inf: forall X st,
  (forall s0,  Setoidc2 (X s0)) ->
  (forall s0, Imp_Setoid (X s0) (Execseqc s0)) ->
  Execinf X s st -> 
  Execseqc s (retc st) bh
| Execc_bh: Execseqc s bh bh. 

Lemma Execseqc_Setoid: forall s, Setoidc2 (Execseqc s). 
Proof.
move => s. cofix hcoind. rewrite /Setoidc2. move => r0 r1 h. foo h. 
- move => r0 h0 r2 h1. foo h0. 
  have := Execc_ret X0 X1 (ExecX_Setoid X0 X2 h1). by apply. 
- move => r0 h0 r1 h1. foo h0. foo h1. apply Execc_input. move => v. 
  have := hcoind _ _ (X v) _ (H0 v) _ (H1 v). by apply. 
- move => r0 h0 r1 h1. foo h0. foo h1. apply Execc_output. 
  have := hcoind _ _ X _ H2 _ H3. by apply.
- move => r0 h0 r1 h1. foo h0. foo h1. have := Execc_inf X0 X1 X2. by apply. 
- move => r0 h0 r1 h1. foo h0. foo h1. by apply Execc_bh.   
Qed. 

CoInductive execseqc (s: stmt): resc -> resc -> Prop :=
| execc_ret: forall X st r,
  (forall s0,  Setoidc2 (X s0)) ->
  (forall s0, Imp_Setoid (X s0) (Execseqc s0)) ->
  ExecX X s st r ->
  execseqc s (retc st) r
| execc_input: forall f0 f1,
  (forall v, execseqc s (f0 v) (f1 v)) ->
  execseqc s (inputc f0) (inputc f1) 
| execc_output: forall v r0 r1,
  execseqc s r0 r1 ->
  execseqc s (outputc v r0) (outputc v r1)
| execc_inf: forall X st,
  (forall s0,  Setoidc2 (X s0)) ->
  (forall s0, Imp_Setoid (X s0) (Execseqc s0)) ->
  Execinf X s st -> 
  execseqc s (retc st) bh
| execc_bh: execseqc s bh bh. 


Lemma execseqc_Setoid: forall s, Setoidc2 (execseqc s).
Proof.
apply skip. (* proved in Type *)
Qed. 

Axiom execseqc_Execseqc: forall s0, Imp_Setoid (execseqc s0) (Execseqc s0).
 
Axiom Execseqc_execseqc: forall s r0 r1,
Execseqc s r0 r1 -> execseqc s r0 r1.
