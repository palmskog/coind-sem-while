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

Section Seq.

Variable s: stmt.
Variable f: forall X, (forall s0, Setoidd2 (X s0)) ->
    (forall s0, Imp_Setoid (X s0) (Execseqnd s0)) -> 
    forall s0 st r,  ExecX X s0 st r -> 
s0 = s -> res.
Variable f_Execdup: forall X (h0:forall s0, Setoidd2 (X s0))
(h1: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
s0 st r  (h2: ExecX X s0 st r) 
(h3: s0 = s), Execdup s st (f h0 h1 h2 h3). 
Variable f_irr: 
forall X (hsetoid: forall s0, Setoidd2 (X s0))
(heq: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
s0 st r  (hexec: ExecX X s0 st r) (h0 h1: s0 = s),
Bism (f hsetoid heq hexec h0) (f hsetoid heq hexec h1). 
Variable f_Wbism: forall X (h0:forall s0, Setoidd2 (X s0))
(h1: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
s0 st r  (h2: ExecX X s0 st r) 
(h3: s0 = s), Wbism (Emb r) (f h0 h1 h2 h3).

Variable s': stmt.
Variable f': forall X, (forall s0, Setoidd2 (X s0)) ->
    (forall s0, Imp_Setoid (X s0) (Execseqnd s0)) -> 
    forall s0 st r,  ExecX X s0 st r -> 
s0 = s' -> res.
Variable f'_Execdup: forall X (h0:forall s0, Setoidd2 (X s0))
(h1: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
s0 st r  (h2: ExecX X s0 st r) 
(h3: s0 = s'), Execdup s' st (f' h0 h1 h2 h3). 
Variable f'_irr: 
forall X (hsetoid: forall s0, Setoidd2 (X s0))
(heq: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
s0 st r  (hexec: ExecX X s0 st r) (h0 h1: s0 = s'),
Bism (f' hsetoid heq hexec h0) (f' hsetoid heq hexec h1). 
Variable f'_Wbism: forall X (h0:forall s0, Setoidd2 (X s0))
(h1: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
s0 st r  (h2: ExecX X s0 st r) 
(h3: s0 = s'), Wbism (Emb r) (f' h0 h1 h2 h3).


CoFixpoint seq 
(s0: stmt) (r0: resd) (r1: resd)
(hexecseq: Execseqnd s0 r0 r1) (hstmt: s0 = s') (r2: res) : res := 
match r2 with
| ret st0 =>
  match hexecseq with
  | Execnd_ret X st1 r3 hsetoid heq hexec =>
     f' hsetoid heq hexec hstmt 
  | Execnd_output v r3 r4 _ => r2
  | Execnd_input f0 f1 _ => r2
  end
| output v0 r3 =>
  match hexecseq with
  | Execnd_ret X st1 r3 hsetoid heq hexec => r2 
  | Execnd_output v1 r4 r5 hexecseq0 => 
    output v1 (seq hexecseq0 hstmt r3)
  | Execnd_input f0 f1 _ => r2
  end
| input f0 =>
  match hexecseq with
  | Execnd_ret X st1 r3 hsetoid heq hexec => r2 
  | Execnd_output v1 r4 r5 hexecseq0 => r2
  | Execnd_input f1 f2 hexecseqinput => 
    input (fun v => seq (hexecseqinput v) hstmt (f0 v)) 
  end
| delay r3 => delay (seq hexecseq hstmt r3)
end.

Lemma seq_Setoid: forall (s0: stmt) (r0: resd) (r1: resd)
(he: Execseqnd s0 r0 r1) (hstmt: s0 = s') (r2 r3: res),
Bism r2 r3 ->
Bism (seq he hstmt r2) (seq he hstmt r3).
Proof. 
cofix hcoind. move => s0 r0 r1 he. dependent inversion he.  
- move => hs r2 r3 h0. inversion h0. apply Bism_refl. 
  rewrite [seq _ _ _]io_destr; simpl. 
  rewrite [seq _ _ _]io_destr; simpl. 
  have := Bism_input H1. apply.    
  rewrite [seq _ _ _]io_destr; simpl. 
  rewrite [seq _ _ _]io_destr; simpl. 
  have := Bism_output _ H1.  apply.  
  rewrite [seq _ _ _]io_destr; simpl. 
  rewrite [seq _ _ (delay _)]io_destr; simpl.
  apply Bism_delay. apply hcoind. apply H1. 
- move => hs r2 r3 h0. inversion h0. 
  rewrite [seq _ _ _]io_destr; simpl. by apply Bism_refl. 
  rewrite [seq _ _ _]io_destr; simpl.   
  rewrite [seq _ _ _]io_destr; simpl.   
  have := Bism_input H1. apply. 
  rewrite [seq _ _ _]io_destr; simpl.   
  rewrite [seq _ _ (output _ _)]io_destr; simpl.
  apply Bism_output. apply hcoind. apply H1. 
  rewrite [seq _ _ _]io_destr; simpl.   
  rewrite [seq _ _ (delay _)]io_destr; simpl.
  apply Bism_delay. apply hcoind. apply H1. 
- move => hs r2 r3 h0. inversion h0. 
  rewrite [seq _ _ _]io_destr; simpl. by apply Bism_refl. 
  rewrite [seq _ _ _]io_destr; simpl.   
  rewrite [seq _ _ (input _)]io_destr; simpl.
  apply Bism_input. move => v. apply hcoind. apply H1. 
  rewrite [seq _ _ _]io_destr; simpl.   
  rewrite [seq _ _ (output _ _)]io_destr; simpl.
  have := Bism_output _ H1. apply.  
  rewrite [seq _ _ _]io_destr; simpl.   
  rewrite [seq _ _ (delay _)]io_destr; simpl.
  apply Bism_delay. apply hcoind. apply H1.    
Qed.   

Lemma seq_irr: forall (s0: stmt) (r0: resd) (r1: resd)
(he: Execseqnd s0 r0 r1) (h0 h1: s0 = s') (r2 r3: res),
Bism r2 r3 ->
Bism (seq he h0 r2) (seq he h1 r3).
Proof. 
cofix hcoind. move => s0 r0 r1 hexec heq0 heq1 r2 r3 h0.
inversion h0. 
- dependent inversion hexec; rewrite [seq _ _ _]io_destr; simpl;
  rewrite [seq _ _ (ret st)]io_destr; simpl. 
  have := f'_irr s1 i e heq0 heq1. 
  destruct (f' s1 i e heq0); destruct (f' s1 i e heq1); apply.
  apply Bism_refl. apply Bism_refl.
- dependent inversion hexec; rewrite [seq _ _ _]io_destr; simpl;
  rewrite [seq _ _ (input f1)]io_destr; simpl. 
  have := Bism_input (fun v => H v). by apply. 
  have := Bism_input (fun v => H v). by apply. 
  apply Bism_input. move => v.  apply hcoind. apply H. 
- dependent inversion hexec; rewrite [seq _ _ _]io_destr; simpl;
  rewrite [seq _ _ (output v r5)]io_destr; simpl. 
  have := Bism_output _ H. by apply. 
  apply Bism_output. apply hcoind. apply H.
  have := Bism_output _ H. by apply. 
- dependent inversion hexec; rewrite [seq _ _ _]io_destr; simpl;
  rewrite [seq _ _ (delay r5)]io_destr; simpl.
  apply Bism_delay. apply hcoind. apply H. 
  apply Bism_delay. apply hcoind. apply H. 
  apply Bism_delay. apply hcoind. apply H. 
Qed. 
  
Program Definition seque (X : stmt -> resd -> resd -> Type)
  (hsetoid : forall s0 : stmt, Setoidd2 (X s0))
  (heq : forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) (s0 : stmt)
  (st : state) (r : resd) (hexec : ExecX X s0 st r) (h0 : s0 = (s;; s')) :=
match hexec with
| ExecX_skip st0 => ret st 
| ExecX_assign _ _ _ => ret st
| ExecX_seq_ret  s1 s2 st0 st1 r0 hs1 hs2 => 
  seq (heq _ _ _ hs2 _ (Bismd_refl _) _ (Bismd_refl _) )
   (_: s2 = s') (f hsetoid heq hs1 (_:s1 = s)) 
| ExecX_seq_input  s1 s2 st0 f0 r0 hs1 hs2 => 
  seq (heq _ _ _ hs2 _ (Bismd_refl _) _ (Bismd_refl _) )
   (_: s2 = s') (f hsetoid heq hs1 (_:s1 = s)) 
| ExecX_seq_output  s1 s2 st0 v0 r0 r1 hs1 hs2 => 
  seq (heq _ _ _ hs2 _ (Bismd_refl _) _ (Bismd_refl _) )
   (_: s2 = s') (f hsetoid heq hs1 (_:s1 = s)) 
| ExecX_ifthenelse_true a s1 s2 st r _ _ => ret st
| ExecX_ifthenelse_false a s1 s2 st r _ _ => ret st
| ExecX_while_false a s st _ => delay (ret st) 
| ExecX_while_ret e1 s1 st1 st2 r1 htrue hs hwhile => ret st
| ExecX_while_input e1 s1 st1 f0 r1 htrue hs hwhile => ret st
| ExecX_while_output e1 s1 st1 v1 r1 r2 htrue hs hwhile => ret st 
| ExecX_write a st => ret st
| ExecX_read x st => ret st
end.

Lemma seque_irr: forall (X : stmt -> resd -> resd -> Type)
(hsetoid : forall s0 : stmt, Setoidd2 (X s0))
(heq : forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) (s0 : stmt)
(st : state) (r : resd) (hexec : ExecX X s0 st r) (h0 h1 : s0 = (s;; s')),
Bism (seque hsetoid heq hexec h0) (seque hsetoid heq hexec h1). 
Proof. 
cofix hcoind. move => X hsetoid heq s0 st0 r0 hexec. 
dependent inversion hexec. 
- move => h0. foo h0. 
- move => h0. foo h0. 
- move => h0 h1. rewrite /seque. apply seq_irr. 
  apply f_irr.
- move => h0 h1. rewrite /seque. apply seq_irr. 
  apply f_irr.
- move => h0 h1. rewrite /seque. apply seq_irr. 
  apply f_irr. 
- move => h0. foo h0.
- move => h0. foo h0.
- move => h0. foo h0.
- move => h0. foo h0.
- move => h0. foo h0.    
 - move => h0. foo h0.
- move => h0. foo h0.
- move => h0. foo h0.
Qed.

Lemma seq_correct: forall  (s0: stmt) (r0: resd) (r1: resd)
(hexecseq: Execseqnd s0 r0 r1) (hstmt: s0 = s') (r2: res),
Wbism (Emb r0) r2 -> Execseqdup s0 r2 (seq hexecseq hstmt r2). 
Proof. 
cofix hcoind. move => s0 r0 r1 hexecseq hstmt. case. 
- dependent inversion hexecseq.
 - move => st0 h0.
  rewrite [seq _ _ _]io_destr; simpl. apply Execdup_ret.
  have h1 := f'_Execdup s1 i e hstmt.
  rewrite [Emb _]io_destr in h0; simpl in h0. 
  have h2 := Wbism_retret h0 => {h0}.    
  rewrite -hstmt in h1.
  rewrite {1}[st]h2 in h1.  destruct (f' s1 i e hstmt). 
  apply h1. apply h1. apply h1. apply h1. 
  - move => st0 h0. absurd False. done.
    rewrite [Emb _]io_destr in h0; simpl in h0. 
    have := Wbism_retoutput (Wbism_sym h0). apply. 
  - move => st0 h0. absurd False. done.
    rewrite [Emb _]io_destr in h0; simpl in h0.  
    have := Wbism_retinput (Wbism_sym h0). apply.  
- dependent inversion hexecseq.
  - move => v0 r2 h0. absurd False. done.
    rewrite [Emb _]io_destr in h0; simpl in h0.  
    have := Wbism_retoutput h0. apply. 
  - move => v0 r2 h0. rewrite [Emb _]io_destr in h0; simpl in h0.
    have [h1 h2] := Wbism_outputoutput h0 => {h0}. 
    rewrite [seq _ _ _]io_destr; simpl. rewrite -h1. apply Execdup_output. 
    apply hcoind. apply h2. 
  - move => v0 r2 h0. absurd False. done.
    rewrite [Emb _]io_destr in h0; simpl in h0.  
    have := Wbism_outputinput (Wbism_sym h0). apply. 
- dependent inversion hexecseq. 
  - move => f0 h0. absurd False. done.
    rewrite [Emb _]io_destr in h0; simpl in h0.  
    have := Wbism_retinput h0. apply. 
  - move => f0 h0. absurd False. done.
    rewrite [Emb _]io_destr in h0; simpl in h0.  
    have := Wbism_outputinput h0. apply. 
  - move => f1 h0. rewrite [Emb _]io_destr in h0; simpl in h0. 
    have h1 := Wbism_inputinput h0 => {h0}.
    rewrite [seq _ _ _]io_destr; simpl. apply Execdup_input. move => v. 
   apply hcoind. apply h1. 
- move => r2 h0. dependent inversion hexecseq. 
  rewrite [seq _ _ _]io_destr; simpl. apply Execdup_delay. apply hcoind.
  rewrite -H in h0. have := Wbism_neg_delay_R h0. apply. 
  rewrite [seq _ _ _]io_destr; simpl. apply Execdup_delay. apply hcoind. 
  rewrite -H in h0. have := Wbism_neg_delay_R h0. apply. 
  rewrite [seq _ _ _]io_destr; simpl. apply Execdup_delay. apply hcoind. 
  rewrite -H in h0. have := Wbism_neg_delay_R h0. apply. 
Qed.     

Lemma seq_ret: forall r0 st0, Red r0 (ret st0) ->
forall X (hsetoid: forall s0, Setoidd2 (X s0))
(heq: forall s0, Imp_Setoid (X s0) (Execseqnd s0))
s0 r1 (hexec: ExecX X s0 st0 r1) (hstmt: s0 = s'),
Wbism (Emb r1) (seq (Execnd_ret hsetoid heq hexec) hstmt r0). 
Proof.
have: forall r0 r2, Red r0 r2 ->
forall st0, Bism r2 (ret st0) -> 
forall X (hsetoid: forall s0, Setoidd2 (X s0))
(heq: forall s0, Imp_Setoid (X s0) (Execseqnd s0))
s0 r1 (hexec: ExecX X s0 st0 r1) (hstmt: s0 = s'),
Wbism (Emb r1) (seq (Execnd_ret hsetoid heq hexec) hstmt r0).
* induction 1. 
  - move => st0 h0 X hsetoid heq s0 r1 hexec hstmt. 
    inversion h0. rewrite [seq _ _ _]io_destr; simpl. 
    have h1 := f'_Wbism hsetoid heq hexec hstmt. 
    destruct (f' hsetoid heq hexec hstmt); apply h1. 
  - move => st0 h0 X hsetoid heq s0 r2 hexec hstmt. 
    have h1 := IHRed _ h0 _ hsetoid heq _ _ hexec hstmt.
    rewrite [seq _ _ _]io_destr; simpl. 
    have := Wbism_delay_R h1. apply. 
  - move => st0 h0. foo h0. 
  - move => st0 h0. foo h0. 
move => h. move => r0 st0 h0 X hsetoid heq s0 r1 hexec hstmt. 
have := h _ _ h0 _ (Bism_refl _) _ hsetoid heq _ _ hexec hstmt. apply.     
Qed. 

Lemma seq_output: forall r0 v0 r1, Red r0 (output v0 r1) ->
forall s0 r2 r3 (hexec: Execseqnd s0 r2 r3) (hstmt: s0 = s'),
Red (seq (Execnd_output v0 hexec) hstmt r0)
(output v0 (seq hexec hstmt r1)).
Proof.    
have: forall r0 r4, Red r0 r4 ->
forall v0 r1, Bism r4 (output v0 r1) -> 
forall s0 r2 r3 (hexec: Execseqnd s0 r2 r3) (hstmt: s0 = s'),
Red (seq (Execnd_output v0 hexec) hstmt r0)
(output v0 (seq hexec hstmt r1)).
* induction 1. 
  - move => v0 r1 h0. foo h0. 
  - move => v0 r2 h0 s0 r3 r4 he hs. 
    rewrite [seq _ _ _]io_destr; simpl. 
    have := Red_delay (IHRed _ _ h0 _ _ _ he hs). apply. 
  - move => v0 r2 h0 s0 r3 r4 he hs. inversion h0. 
    rewrite [seq _ _ _]io_destr; simpl. 
    have h1 := Bism_trans b H0.  
    have := Red_output _ (seq_Setoid _ _ h1).
    apply.
  - move => v0 r1 h0. foo h0. 
move => h. move => r0 v0 r1 h0 s0 r2 h3 he hs. 
have := h _ _ h0 _ _ (Bism_refl _) _  _ _ he hs. apply.
Qed. 

Lemma seq_input: forall r0 f0, Red r0 (input f0) ->
forall s0 f1 f2 (he: forall v, Execseqnd s0 (f1 v) (f2 v))
(hs: s0 = s'),
Red (seq (Execnd_input he) hs r0) 
(input (fun v => seq (he v) hs (f0 v))).
Proof.    
have: forall r0 r1, Red r0 r1 ->
forall f0, Bism r1 (input f0) -> 
forall s0 f1 f2 (he: forall v, Execseqnd s0 (f1 v) (f2 v))
(hs: s0 = s'),
Red (seq (Execnd_input he) hs r0) 
(input (fun v => seq (he v) hs (f0 v))).
* induction 1. 
  - move => f0 h0. foo h0. 
  - move => f0 h0 s0 f1 f2 hexec heq.  
    rewrite [seq _ _ _]io_destr; simpl. 
    have := Red_delay (IHRed _  h0 _ _ _ hexec heq). apply.
  - move => f0 h0. foo h0.  
  - move => f1 h0 s0 f2 f3 he hs. inversion h0.   
    rewrite [seq _ _ _]io_destr; simpl.    
    have h := Red_input (fun v => seq_Setoid (he v) _ (Bism_trans (b v) (H1 v))).
    apply h.  
move => h. move => r0 f0 h0 s0 f1 f2  he hs. 
have := h _ _ h0  _ (Bism_refl _) _  _ _ he hs. apply.
Qed. 

Lemma seq_Wbism: forall  (s0: stmt) (r0 r1: resd)
(hexecseq: Execseqnd s0 r0 r1) (hstmt: s0 = s') (r2: res),
Wbism (Emb r0) r2 -> Wbism (Emb r1) (seq hexecseq hstmt r2). 
Proof. 
cofix hcoind. move => s0 r0 r1 hexecseq. 
dependent inversion hexecseq.  
- move => hstmt r2 h0.    
  rewrite [Emb _]io_destr in h0; simpl in h0. 
  have h1 := Wbism_ret_Red h0 => {h0}.
  apply seq_ret. apply h1.
- move => hstmt r2 h0. 
  rewrite [Emb _]io_destr in h0; simpl in h0. 
  have := Wbism_output_Red h0 => {h0}. 
  move => [r3 [h1 h2]].
  rewrite [Emb _]io_destr; simpl.  
  have := Wbism_output (Red_output _ (Bism_refl _ )) _ 
  (hcoind _ _ _ e hstmt _ h2). apply. apply seq_output. apply h1.
- move => hs r2 h0.   
  rewrite [Emb _]io_destr in h0; simpl in h0. 
  have := Wbism_input_Red h0 => {h0}. 
  move => [f1 [h0 h1]].
  rewrite [Emb _]io_destr; simpl.  
  have := Wbism_input (Red_input (fun v => (Bism_refl _))) _
  (fun v => hcoind _ _ _ (e v) hs _ (h1 v)). apply. 
  apply seq_input. apply h0. 
Qed. 

Lemma seque_correct: forall (X : stmt -> resd -> resd -> Type)
(hsetoid : forall s0 : stmt, Setoidd2 (X s0))
(heq : forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) (s0 : stmt)
(st : state) (r : resd) (hexec : ExecX X s0 st r) (hstmt : s0 = (s;; s')),
Execdup (s;; s') st (seque hsetoid heq hexec hstmt).
Proof. 
move => X hsetoid heq s0 st0 r0 hexec. dependent inversion hexec.
- move => h0. foo h0. 
- move => h0. foo h0.
- move => h0. inversion h0. rewrite /seque. 
  have h1 := f_Execdup hsetoid heq e 
  (seque_obligation_2 h0 eq_refl eq_refl eq_refl
  (JMeq_refl (ExecX_seq_ret e x))). 
  have := Execdup_seq h1 => {h1}. apply.
  rewrite -{1}[s']H4. apply seq_correct.
  apply f_Wbism. 
- move => h0. inversion h0. rewrite /seque. 
  have h1 := f_Execdup hsetoid heq e 
  (seque_obligation_4 h0 eq_refl eq_refl eq_refl
  (JMeq_refl (ExecX_seq_input e x))). 
  have := Execdup_seq h1 => {h1}. apply.
  rewrite -{1}[s']H4. apply seq_correct.
  apply f_Wbism.
- move => h0. inversion h0. rewrite /seque. 
  have h1 := f_Execdup hsetoid heq e 
  (seque_obligation_6 h0 eq_refl eq_refl eq_refl
  (JMeq_refl (ExecX_seq_output e x))). 
  have := Execdup_seq h1 => {h1}. apply.
  rewrite -{1}[s']H4. apply seq_correct.
  apply f_Wbism.
- move => h0. foo h0. 
- move => h0. foo h0. 
- move => h0. foo h0.
- move => h0. foo h0. 
- move => h0. foo h0. 
- move => h0. foo h0. 
- move => h0. foo h0. 
- move => h0. foo h0. 
Qed.   

Lemma seque_Wbism: forall (X : stmt -> resd -> resd -> Type)
(hsetoid : forall s0 : stmt, Setoidd2 (X s0))
(heq : forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) (s0 : stmt)
(st : state) (r : resd) (hexec : ExecX X s0 st r) (hstmt : s0 = (s;; s')),
Wbism (Emb r) (seque hsetoid heq hexec hstmt).
Proof.
move => X hsetoid heq s0 st0 r0 hexec. dependent inversion hexec.
- move => h0. foo h0. 
- move => h0. foo h0.
- move => h0. inversion h0. rewrite /seque. 
  have h1 := f_Wbism hsetoid heq e 
  (seque_obligation_2 h0 eq_refl eq_refl eq_refl
  (JMeq_refl (ExecX_seq_ret e x))). apply seq_Wbism.
  apply h1.  
- move => h0. inversion h0. rewrite /seque. 
  have h1 := f_Wbism hsetoid heq e 
  (seque_obligation_4 h0 eq_refl eq_refl eq_refl
  (JMeq_refl (ExecX_seq_input e x))). apply seq_Wbism.
  apply h1.
- move => h0. inversion h0. rewrite /seque. 
  have h1 := f_Wbism hsetoid heq e 
  (seque_obligation_6 h0 eq_refl eq_refl eq_refl
  (JMeq_refl (ExecX_seq_output e x))). apply seq_Wbism.
  apply h1. 
- move => h0. foo h0. 
- move => h0. foo h0. 
- move => h0. foo h0.
- move => h0. foo h0. 
- move => h0. foo h0. 
- move => h0. foo h0. 
- move => h0. foo h0. 
- move => h0. foo h0. 
Qed. 

End Seq.  


Section Loop.

Variable e: expr.
Variable s: stmt. 
Variable f: forall X, (forall s0, Setoidd2 (X s0)) ->
    (forall s0, Imp_Setoid (X s0) (Execseqnd s0)) -> 
    forall s0 st r,  ExecX X s0 st r -> 
s0 = s -> res.
Variable f_Execdup: forall X (h0:forall s0, Setoidd2 (X s0))
(h1: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
s0 st r  (h2: ExecX X s0 st r) 
(h3: s0 = s), Execdup s st (f h0 h1 h2 h3). 
Variable f_irr: 
forall X (hsetoid: forall s0, Setoidd2 (X s0))
(heq: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
s0 st r  (hexec: ExecX X s0 st r) (h0 h1: s0 = s),
Bism (f hsetoid heq hexec h0) (f hsetoid heq hexec h1). 
Variable f_Wbism: forall X (h0:forall s0, Setoidd2 (X s0))
(h1: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
s0 st r  (h2: ExecX X s0 st r) 
(h3: s0 = s), Wbism (Emb r) (f h0 h1 h2 h3). 

Program CoFixpoint loop  
(X: stmt -> resd -> resd -> Type) 
(hXsetoid: forall s0, Setoidd2 (X s0)) 
(hXeq: forall s0, Imp_Setoid (X s0) (Execseqnd s0))  
(s0: stmt) (st: state) (r: resd) 
(hexec:ExecX X s0 st r) (hstmt: s0 = Swhile e s) : res :=
match hexec with
| ExecX_skip st0 => ret st 
| ExecX_assign _ _ _ => ret st
| ExecX_seq_ret _ _ _ _ _ _ _ => ret st
| ExecX_seq_input _ _ _ _ _ _ _ => ret st
| ExecX_seq_output _ _ _ _ _ _ _ _ => ret st
| ExecX_ifthenelse_true a s1 s2 st r _ _ => ret st
| ExecX_ifthenelse_false a s1 s2 st r _ _ => ret st
| ExecX_while_false a s st _ => delay (ret st) 
| ExecX_while_ret e1 s1 st1 st2 r1 htrue hs hwhile =>  
  delay (loopseq (Execnd_ret hXsetoid hXeq hwhile) 
         (_: Swhile e1 s1 = Swhile e s) (f hXsetoid hXeq hs (_: s1 = s)))
| ExecX_while_input e1 s1 st1 f0 r1 htrue hs hwhile => 
  let hwhile1 := hXeq _ _ _ hwhile _ (Bismd_refl _) _ (Bismd_refl _) in 
  delay (loopseq hwhile1 (_: Swhile e1 s1 = Swhile e s) 
             (f hXsetoid hXeq hs (_: s1 = s)))
| ExecX_while_output e1 s1 st1 v1 r1 r2 htrue hs hwhile =>   
  let hwhile1 := hXeq _ _ _ hwhile _ (Bismd_refl _) _ (Bismd_refl _) in 
  delay (loopseq hwhile1 (_: Swhile e1 s1 = Swhile e s) 
            (f hXsetoid hXeq  hs (_: s1 = s))) 
| ExecX_write a st => ret st
| ExecX_read x st => ret st
end   

with loopseq  
(s0: stmt) (r0: resd) (r1: resd)
(hexecseq: Execseqnd s0 r0 r1) (hstmt: s0 = Swhile e s) (r2: res) : res := 
match r2 with
| ret st0 =>
  match hexecseq with
  | Execnd_ret X st1 r3 hsetoid heq hexec =>
    delay (loop hsetoid heq hexec (_: s0 = Swhile e s)) 
  | Execnd_output v r3 r4 _ => r2
  | Execnd_input f0 f1 _ => r2
  end
| output v0 r3 =>
  match hexecseq with
  | Execnd_ret X st1 r3 hsetoid heq hexec => r2 
  | Execnd_output v1 r4 r5 hexecseq0 => 
    output v1 (loopseq hexecseq0 (_: s0 = Swhile e s) r3)
  | Execnd_input f0 f1 _ => r2
  end
| input f0 =>
  match hexecseq with
  | Execnd_ret X st1 r3 hsetoid heq hexec => r2 
  | Execnd_output v1 r4 r5 hexecseq0 => r2
  | Execnd_input f1 f2 hexecseqinput => 
    input (fun v => loopseq (hexecseqinput v) (_: s0 = Swhile e s) (f0 v)) 
  end
| delay r3 => delay (loopseq hexecseq hstmt r3)
end.

Lemma loopseq_Setoid: forall r2 r3,
Bism r2 r3 -> 
forall s0 r0 r1
(hexecseq: Execseqnd s0 r0 r1) (hstmt: s0 = Swhile e s), 
Bism (loopseq hexecseq hstmt r2) (loopseq hexecseq hstmt r3). 
Proof.
cofix hcoind. move => r2 r3 h0. inversion h0; subst.
- move => s0 r0 r1 h2 h1. apply Bism_refl. 
- move => s0 r0 r1 h1 h2. dependent inversion h1. 
  - rewrite [loopseq _ _ _]io_destr; simpl.
    rewrite [loopseq _ _ _]io_destr; simpl. 
    have := Bism_input (fun v => H v). by apply.      
  - rewrite [loopseq _ _ _]io_destr; simpl.
    rewrite [loopseq _ _ _]io_destr; simpl. 
    have := Bism_input (fun v => H v). by apply.      
  - rewrite [loopseq _ _ _]io_destr; simpl.
    rewrite [loopseq _ _ _]io_destr; simpl.
    apply Bism_input. move => v. apply hcoind. 
    by apply H. 
- move => s0 r2 r3 h1 h2. dependent inversion h1. 
  - rewrite [loopseq _ _ _]io_destr; simpl.
    rewrite [loopseq _ _ _]io_destr; simpl. 
    have := Bism_output _ H. by apply.      
  - rewrite [loopseq _ _ _]io_destr; simpl.
    rewrite [loopseq _ _ (output v r1)]io_destr; simpl. 
    apply Bism_output. apply hcoind. by apply H.       
  - rewrite [loopseq _ _ _]io_destr; simpl.
    rewrite [loopseq _ _ _]io_destr; simpl. by apply h0.  
- move => s0 r2 r3 h1 h2. dependent inversion h1. 
  - rewrite [loopseq _ _ _]io_destr; simpl.
    rewrite [loopseq _ _ (delay r1)]io_destr; simpl.
    apply Bism_delay. apply hcoind. apply H.      
  - rewrite [loopseq _ _ _]io_destr; simpl.
    rewrite [loopseq _ _ (delay r1)]io_destr; simpl.
   apply Bism_delay. apply hcoind. by apply H. 
  - rewrite [loopseq _ _ _]io_destr; simpl.
    rewrite [loopseq _ _ (delay r1)]io_destr; simpl.
   apply Bism_delay. apply hcoind. by apply H. 
Qed. 

Lemma loop_irr: forall   
(X: stmt -> resd -> resd -> Type) 
(hsetoid: forall s0, Setoidd2 (X s0)) 
(heq: forall s0, Imp_Setoid (X s0) (Execseqnd s0))  
(s0: stmt) (st: state) (r: resd) 
(hexec:ExecX X s0 st r) (hstmt0 hstmt1: s0 = Swhile e s),
Bism (loop hsetoid heq hexec hstmt0) (loop hsetoid heq hexec hstmt1).
Proof. 
cofix hcoind. 
have hcoind0: forall  
(s0: stmt) (r0 r1: resd)
(hexecseq: Execseqnd s0 r0 r1) (h0 h1: s0 = Swhile e s) (r2 r3: res),
Bism r2 r3 -> 
Bism (loopseq hexecseq h0 r2) (loopseq hexecseq h1 r3).
* cofix hcoind0. move => s0 r0 r1 hexecseq h0 h1 r2 r3 h2. 
  inversion h2.   
  - dependent inversion hexecseq.
    - rewrite [loopseq _ _ _]io_destr; simpl. 
      rewrite [loopseq _ _ _]io_destr; simpl. 
      apply Bism_delay. apply hcoind.
    - rewrite [loopseq _ _ _]io_destr; simpl. 
      rewrite [loopseq _ _ _]io_destr; simpl. by apply Bism_refl. 
    - rewrite [loopseq _ _ _]io_destr; simpl. 
      rewrite [loopseq _ _ _]io_destr; simpl. by apply Bism_refl. 
  - dependent inversion hexecseq.
    - rewrite [loopseq _ _ _]io_destr; simpl. 
      rewrite [loopseq _ _ _]io_destr; simpl. 
      have := Bism_input H. apply. 
    - rewrite [loopseq _ _ _]io_destr; simpl. 
      rewrite [loopseq _ _ _]io_destr; simpl.
      have := Bism_input H; apply.    
    - rewrite [loopseq _ _ _]io_destr; simpl. 
      rewrite [loopseq _ _ _]io_destr; simpl. 
      apply Bism_input. move => v. apply hcoind0. 
      apply H. 
  - dependent inversion hexecseq.
    - rewrite [loopseq _ _ _]io_destr; simpl. 
      rewrite [loopseq _ _ _]io_destr; simpl.
      have := Bism_output _ H. apply.  
    - rewrite [loopseq _ _ _]io_destr; simpl. 
      rewrite [loopseq _ _ (output v r5)]io_destr; simpl. 
      apply Bism_output. apply hcoind0. apply H.   
    - rewrite [loopseq _ _ _]io_destr; simpl. 
      rewrite [loopseq _ _ _]io_destr; simpl.
      have := Bism_output _ H. by apply.  
  - rewrite [loopseq _ _ _]io_destr; simpl. 
    rewrite [loopseq _ _ (delay _)]io_destr; simpl. 
    apply Bism_delay. apply hcoind0. apply H.         
move => X hsetoid heq s0 st0 r0 hexec.
dependent inversion hexec; subst. 
- move => h0. foo h0.   
- move => h0. foo h0.
- move => h0. foo h0.
- move => h0. foo h0.   
- move => h0. foo h0.
- move => h0. foo h0. 
- move => h0. foo h0.    
- move => h0 h1. rewrite [loop _ _ _ _]io_destr; simpl. 
  rewrite [loop _ _ _ _]io_destr; simpl. apply Bism_refl. 
- move => h0 h1. rewrite [loop _ _ _ _]io_destr; simpl.
  rewrite [loop _ _ (ExecX_while_ret _ _ _) h1]io_destr; simpl.
  fold loopseq. apply Bism_delay. apply hcoind0. 
  apply f_irr.   
- move => h0 h1. rewrite [loop _ _ _ _]io_destr; simpl.
  rewrite [loop _ _ (ExecX_while_input _ _ _) h1]io_destr; simpl.  
  fold loopseq. apply Bism_delay. apply hcoind0. 
  apply f_irr. 
- move => h0 h1. rewrite [loop _ _ _ _]io_destr; simpl.
  rewrite [loop _ _ (ExecX_while_output _ _ _) h1]io_destr; simpl.  
  fold loopseq. apply Bism_delay. apply hcoind0.  
  apply f_irr.
- move => h0. foo h0. 
- move => h0. foo h0. 
Qed.
 

Lemma loop_correct:  forall
(X: stmt -> resd -> resd -> Type) 
(hXsetoid: forall s0, Setoidd2 (X s0)) 
(hXeq: forall s0, Imp_Setoid (X s0) (Execseqnd s0))  
(s0: stmt) (st: state) (r: resd) 
(hexec:ExecX X s0 st r) (hstmt: s0 = Swhile e s),
Execdup s0 st (delay (loop hXsetoid hXeq hexec hstmt)).  
Proof.
cofix hcoind. 
have hcoind2: forall 
(s0: stmt) (r0 r1: resd)
(hexecseq: Execseqnd s0 r0 r1) (hstmt: s0 = Swhile e s) (r2: res),
Wbism (Emb r0) r2 -> 
Execseqdup s0 r2 (loopseq hexecseq hstmt r2). 
* cofix hcoind1. move => s0 r0 r1 hexecseq hstmt. case.  
  - dependent inversion hexecseq.
    - move => st0 h0. rewrite [loopseq _ _ _]io_destr; simpl.
      rewrite [Emb _]io_destr in h0; simpl in h0. 
      have h1 := Wbism_retret h0 => {h0}. rewrite -h1.    
      apply Execdup_ret. apply hcoind. 
    - move => st0 h0. absurd False. done.
      rewrite [Emb _]io_destr in h0; simpl in h0. 
      have := Wbism_retoutput (Wbism_sym h0); by apply. 
    - move => st0 h0. absurd False. done.
      rewrite [Emb _]io_destr in h0; simpl in h0. 
      have := Wbism_retinput (Wbism_sym h0); by apply.
  - dependent inversion hexecseq. 
    - move => v0 r2 h0. absurd False. done.
      rewrite [Emb _]io_destr in h0; simpl in h0.  
      have := Wbism_retoutput h0; apply. 
    - move => v0 r2 h0. rewrite [Emb _]io_destr in h0; simpl in h0. 
      have [h1 h2] := Wbism_outputoutput h0 => {h0}. 
      rewrite -h1. rewrite [loopseq _ _ _]io_destr; simpl. 
      apply Execdup_output. apply hcoind1. apply h2.  
    - move => v0 r2 h0. absurd False. done.
      rewrite [Emb _]io_destr in h0; simpl in h0.  
      have := Wbism_outputinput (Wbism_sym h0). apply. 
  - dependent inversion hexecseq. 
    - move => f0 h0. absurd False. done.
      rewrite [Emb _]io_destr in h0; simpl in h0.  
      have := Wbism_retinput h0; apply. 
    - move => f0 h0. absurd False. done.
      rewrite [Emb _]io_destr in h0; simpl in h0.  
      have := Wbism_outputinput h0; apply. 
    - move => f1 h0. rewrite [Emb _]io_destr in h0; simpl in h0. 
      have h1 := Wbism_inputinput h0 => {h0}. 
      rewrite [loopseq _ _ _]io_destr; simpl. 
      apply Execdup_input. move => v. apply hcoind1.
      by apply h1. 
  - move => r2 h0. rewrite [loopseq _ _ _]io_destr; simpl. 
    apply Execdup_delay. apply hcoind1.     
    have := Wbism_neg_delay_R h0. by apply. 
* move => X hsetoid heq s0 st0 r0 hexec. dependent inversion hexec.  
  - move => h0. foo h0. 
  - move => h0. foo h0. 
  - move => h0. foo h0. 
  - move => h0. foo h0. 
  - move => h0. foo h0.
  - move => h0. foo h0. 
  - move => h0. foo h0.  
  - move => h0. inversion h0. subst. 
    rewrite [loop _ _ _ _]io_destr; simpl. apply Execdup_while_false.
    apply e0. 
  - move => h0. inversion h0; subst.           
    rewrite [loop  _ _ _ _]io_destr; simpl. fold loopseq. 
    have h1 := f_Execdup hsetoid heq e1 
    (loop_obligation_2 h0 eq_refl eq_refl eq_refl 
    (JMeq_refl (ExecX_while_ret e0 e1 e2))).
    have := Execdup_while_loop e0 (Execdup_delay (Execdup_delay (Execdup_ret h1))).
    apply. apply Execdup_delay. apply Execdup_delay. apply hcoind2.
    apply f_Wbism. 
  - move => h0. inversion h0; subst. 
    rewrite [loop  _ _ _ _]io_destr; simpl. fold loopseq. 
    have h1 := f_Execdup hsetoid heq e1 
    (loop_obligation_4 h0 eq_refl eq_refl eq_refl 
    (JMeq_refl (ExecX_while_input e0 e1 x))).
    have := Execdup_while_loop e0 (Execdup_delay (Execdup_delay (Execdup_ret h1))).
    apply. apply Execdup_delay. apply Execdup_delay. apply hcoind2.
    apply f_Wbism.
  - move => h0. inversion h0; subst. 
    rewrite [loop  _ _ _ _]io_destr; simpl. fold loopseq. 
    have h1 := f_Execdup hsetoid heq e1 
    (loop_obligation_6 h0 eq_refl eq_refl eq_refl 
    (JMeq_refl (ExecX_while_output e0 e1 x))).
    have := Execdup_while_loop e0 (Execdup_delay (Execdup_delay (Execdup_ret h1))).
    apply. apply Execdup_delay. apply Execdup_delay. apply hcoind2.
    apply f_Wbism.
  - move => h0. foo h0. 
  - move => h0. foo h0.
Qed. 

Inductive Xwhile: res -> res -> Type :=
| Xwhile_intro: forall s0 r0 r1 r2
(hexecseq: Execseqnd s0 r0 r1)
(hstmt: s0 = Swhile e s),  
Wbism (Emb r0) r2 ->     
forall r3, Bism r3 (Emb r1) ->     
forall r4, Bism r4 (loopseq hexecseq hstmt r2) ->
Xwhile r3 r4.

Lemma Xwhile_Setoid: Setoid2 Xwhile. 
Proof.
move => r0 r1 h0 r2 h1 r3 h2. inversion h0. 
have := Xwhile_intro H (Bism_trans (Bism_sym h1) H0)
(Bism_trans (Bism_sym h2) H1). by apply. 
Qed. 

Lemma loopseq_ret: forall X s0 st0 r 
(hsetoid: forall s0, Setoidd2 (X s0)) 
(heq: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
(hexec: ExecX X s0 st0 r) (hstmt: s0 = Swhile e s), 
forall  r1 r2,
Red r1 r2 -> Bism r2 (ret st0) ->  
Bism (loopseq (Execnd_ret hsetoid heq hexec) hstmt r1) 
(append r1 (delay (loop hsetoid heq hexec hstmt))).
Proof.
move => X s0 st0 r hsetoid heq hexec hstmt. 
induction 1. 
- move => h0. inversion h0.  rewrite [loopseq _ _ _]io_destr; simpl. 
  rewrite [append _ _]io_destr; simpl. apply Bism_delay.
  apply loop_irr.
- move => h0. inversion h0. rewrite [loopseq _ _ _]io_destr; simpl. 
  rewrite [append _ _]io_destr; simpl. apply Bism_delay.
  have := IHRed h0. apply. 
- move => h0. foo h0. 
- move => h0. foo h0. 
Qed.   

Lemma Steps_Wbismi_loopseq: forall r0 r1,
Steps r0 r1 ->
forall X r2 s0 r3 r4 (hexecseq: Execseqnd s0 r3 r4)  hstmt,
Setoid2 X -> 
Wbismi X r2 (loopseq hexecseq hstmt r1) ->
Wbismi X r2 (loopseq hexecseq hstmt r0).
Proof.
induction 1.  
- move => X r4 s0 r2 r3 h0 h1 hsetoid h2. 
  have := Wbismi_Setoid hsetoid h2 (Bism_refl _)
  (loopseq_Setoid (Bism_sym b) h0 h1). by apply.   
- move => X r2 s0 r3 r4 hexecseq hstmt hsetoid h0. 
 rewrite [loopseq _ _ _]io_destr; simpl. 
  apply Wbismi_delay_R. have := IHSteps _ _ _ _ _ hexecseq hstmt hsetoid h0.
  by apply. 
Qed.  

Lemma loop_Wbismi:  forall
(X: stmt -> resd -> resd -> Type) 
(hXsetoid: forall s0, Setoidd2 (X s0)) 
(hXeq: forall s0, Imp_Setoid (X s0) (Execseqnd s0))  
(s0: stmt) (st: state) (r: resd) 
(hexec:ExecX X s0 st r) (hstmt: s0 = Swhile e s),
Wbismi Xwhile (Emb r) (delay (loop hXsetoid hXeq hexec hstmt)).  
Proof.
move => X hsetoid heq. move => s0 st0 r0 h0. 
dependent induction h0.
- move => h0. foo h0.
- move => h0. foo h0.
- move => h1. foo h1.
- move => h1. foo h1.
- move => h1. foo h1.
- move => h1. foo h1. 
- move => h1. foo h1.  
- move => h0. rewrite [loop _ _ _ _]io_destr; simpl. 
  apply Wbismi_delay_R. apply Wbismi_delay_R. 
  rewrite [Emb _]io_destr; simpl. apply Wbismi_ret.  
- move => h0. rewrite [loop _ _ _ _]io_destr; simpl. fold loopseq.
  inversion h0; subst. 
  have h1 := IHh0_2 h0.
  have h2 := f_Wbism hsetoid heq h0_1 
  (loop_obligation_2 h0 eq_refl eq_refl eq_refl
  (JMeq_refl (ExecX_while_ret e0 h0_1 h0_2))).
  set r0 := f hsetoid heq h0_1
  (loop_obligation_2 h0 eq_refl eq_refl eq_refl
  (JMeq_refl (ExecX_while_ret e0 h0_1 h0_2))). fold r0 in h2. 
  apply Wbismi_delay_R. apply Wbismi_delay_R.
  rewrite [Emb _]io_destr in h2; simpl in h2. 
  have h5 := Wbism_ret_Red h2. 
  have h3 := loopseq_ret hsetoid heq h0_2
  (loop_obligation_1 h0 eq_refl eq_refl eq_refl
  (JMeq_refl (ExecX_while_ret e0 h0_1 h0_2))) h5 (Bism_refl _).    
  have := Wbismi_Setoid Xwhile_Setoid _ (Bism_refl _) (Bism_sym h3). apply.
  clear h3.   
  have h4 := Wbism_ret_Red h2 => {h2}. 
  have h2 := Red_Steps h4 => {h4}. 
  have := Wbismi_Steps_append h2. apply. apply Xwhile_Setoid. 
  rewrite [append _ _]io_destr; simpl. apply IHh0_2. 
- move => h1. inversion h1; subst.
  have h2 := heq _ _ _ x _ (Bismd_refl _) _ (Bismd_refl _).
  foo h2.
  rewrite [loop _ _ _ _]io_destr; simpl. fold loopseq.
  have h2 := f_Wbism hsetoid heq h0
  (loop_obligation_4 h1 eq_refl eq_refl eq_refl
   (JMeq_refl (ExecX_while_input e0 h0 x))).        
 apply Wbismi_delay_R. apply Wbismi_delay_R.
 set r0 := f hsetoid heq h0
 (loop_obligation_4 h1 eq_refl eq_refl eq_refl 
 (JMeq_refl (ExecX_while_input e0 h0 x))). fold r0 in h2.
 rewrite [Emb _]io_destr in h2; simpl in h2. 
 have [f1 [h3 h4]] := Wbism_input_Red h2 => {h2}.
 have h5 := Red_Steps h3 => {h3}.
 set hexecseq :=  (heq (Swhile e s) (inputd f0) (inputd f') x (inputd f0)
        (Bismd_refl (inputd f0)) (inputd f') (Bismd_refl (inputd f'))).
 have := Steps_Wbismi_loopseq h5.  apply.
 apply Xwhile_Setoid. rewrite [loopseq _ _ _]io_destr; simpl. 
  dependent destruction hexecseq. 
  rewrite -x [Emb _]io_destr; simpl. 
  apply Wbismi_input. 
  move => v. have := Xwhile_intro (h4 v) (Bism_refl _) (Bism_refl _).
  apply.
- move => h1. inversion h1; subst.
  have h2 := heq _ _ _ x _ (Bismd_refl _) _ (Bismd_refl _). foo h2. 
  rewrite [loop _ _ _ _]io_destr; simpl. fold loopseq.
  have h2 := f_Wbism hsetoid heq h0
  (loop_obligation_6 h1 eq_refl eq_refl eq_refl
   (JMeq_refl (ExecX_while_output e0 h0 x))).        
  apply Wbismi_delay_R. apply Wbismi_delay_R.
  set r0 := f hsetoid heq h0
  (loop_obligation_6 h1 eq_refl eq_refl eq_refl
  (JMeq_refl (ExecX_while_output e0 h0 x))). fold r0 in h2.
  rewrite [Emb _]io_destr in h2; simpl in h2. 
  have [r1 [h3 h4]] := Wbism_output_Red h2 => {h2}.
  have h5 := Red_Steps h3 => {h3}.
  set hexecseq :=  heq (Swhile e s) (outputd v r) (outputd v r'0) x (outputd v r)
  (Bismd_refl (outputd v r)) (outputd v r'0) (Bismd_refl (outputd v r'0)).
  have := Steps_Wbismi_loopseq h5.  apply.
  apply Xwhile_Setoid.  
  rewrite [loopseq _ _ _]io_destr; simpl. 
  dependent destruction hexecseq. 
  rewrite -x [Emb _]io_destr; simpl. 
  apply Wbismi_output. 
  have := Xwhile_intro h4 (Bism_refl _) (Bism_refl _). apply.      
- move => h0. foo h0. 
- move => h0. foo h0. 
Qed.

Lemma loopseq_Red_ret: forall r0 st0,
Red r0 (ret st0)  ->
forall X s0 st0 r1 
(hsetoid: forall s0, Setoidd2 (X s0))
(heq: forall s0, Imp_Setoid (X s0) (Execseqnd s0))
(hexec: ExecX X s0 st0 r1) 
(hstmt: s0 = Swhile e s),   
Steps (loopseq (Execnd_ret hsetoid heq hexec) hstmt r0)
(loop hsetoid heq hexec hstmt).
Proof. 
have: forall r0 r2,
Red r0 r2  ->
forall st0, Bism r2 (ret st0) -> 
forall X s0 st0 r1 
(hsetoid: forall s0, Setoidd2 (X s0))
(heq: forall s0, Imp_Setoid (X s0) (Execseqnd s0))
(hexec: ExecX X s0 st0 r1) 
(hstmt: s0 = Swhile e s),   
Steps (loopseq (Execnd_ret hsetoid heq hexec) hstmt r0)
(loop hsetoid heq hexec hstmt).
* induction 1. 
  - move => st0 h0. foo h0. move => X s0 st1 r0 hsetoid heq hexec hstmt.
    rewrite [loopseq _ _ _]io_destr; simpl. apply Steps_delay. 
    apply Steps_stop. apply loop_irr. 
  - move => st0 h0. foo h0. move => X s0 st1 r1 hsetoid heq hexec stmt. 
    rewrite [loopseq _ _ _]io_destr; simpl. apply Steps_delay.
    have := IHRed _ (Bism_refl _). apply. 
  - move => st0 h0. foo h0. 
  - move => st0 h0. foo h0. 
move => h. move => r0 st0 h0 X s0 st1 r1 hsetoid heq hexec hstmt. 
have := h _ _ h0 _ (Bism_refl _) _ _ _ _ hsetoid heq hexec hstmt. 
by apply.  
Qed. 



Lemma loopseq_Red_output: forall r0 v0 r1,
Red r0 (output v0 r1) ->
forall r3, Wbism r1 (Emb r3) -> 
forall s0 r2 (hexecseq: Execseqnd s0 (outputd v0 r3)  r2)
(hstmt: s0 = Swhile e s),   
Red (loopseq hexecseq hstmt r0) (loopseq hexecseq hstmt (output v0 r1)).
Proof. 
have:forall r0 r4,
Red r0 r4 ->
forall v0 r1, Bism r4 (output v0 r1) -> 
forall r3, Wbism r1 (Emb r3) -> 
forall s0 r2 (hexecseq: Execseqnd s0 (outputd v0 r3)  r2)
(hstmt: s0 = Swhile e s),   
Red (loopseq hexecseq hstmt r0) (loopseq hexecseq hstmt (output v0 r1)).
* induction 1. 
  - move => v0 r0 h0. foo h0. 
  - move => v0 r2 h0 r3 h1 s0 r4 h2 h3. 
    rewrite [loopseq _ _ _]io_destr; simpl. apply Red_delay. 
    have := IHRed _ _ h0 _ h1. apply. 
  - move => v0 r2 h0 r3 h1 s0 r4 h2 h3.
    have h4: Bism r0 r2. 
    * foo h0.  have := Bism_trans b H0. by apply.
    have h5: v = v0; first by foo h0.
    rewrite h5 => {h5}. 
    have h5 := loopseq_Setoid (Bism_output v0 h4) h2 h3. 
    have := Red_Setoid _ (Bism_refl _) h5. apply.      
    dependent destruction h2.  
    rewrite [loopseq _ _ _]io_destr; simpl.
    apply Red_output. apply Bism_refl. 
  - move => v0 r1 h0. foo h0. 
move => h0. move => r0 v0 r1 h4 r3 h1 s0 r4 h2 h3.
have := h0 _ _ h4 _ _ (Bism_refl _) _ h1. apply.  
Qed. 


Lemma loopseq_Red_input: forall r0 f0,
Red r0 (input f0) ->
forall f1, (forall v, Wbism (Emb (f1 v)) (f0 v)) ->  
forall s0 f2 (hexecseq: Execseqnd s0 (inputd f1) (inputd f2))
(hstmt: s0 = Swhile e s),   
Red (loopseq hexecseq hstmt r0) 
(loopseq hexecseq hstmt (input f0)).
Proof. 
have: forall r0 r1,
Red r0 r1 ->
forall f0, Bism (input f0) r1 -> 
forall f1, (forall v, Wbism (Emb (f1 v)) (f0 v)) ->  
forall s0 f2 (hexecseq: Execseqnd s0 (inputd f1) (inputd f2))
(hstmt: s0 = Swhile e s),   
Red (loopseq hexecseq hstmt r0) 
(loopseq hexecseq hstmt (input f0)).
* induction 1. 
  - move => f0 h0. foo h0. 
  - move => f0 h0 f1 hwbism s0 f2 hexecseq hstmt. 
    rewrite [loopseq _ _ _]io_destr; simpl. apply Red_delay. 
    have := IHRed _ h0 _ hwbism _ _ hexecseq hstmt. by apply. 
  - move => f0 h0. foo h0. 
  - move => f1 h0 f2 hwbism s0 f3 hexecseq hstmt. 
    rewrite [loopseq _ _ _]io_destr; simpl. 
    rewrite [loopseq _ _ (input f1)]io_destr; simpl.
    dependent destruction hexecseq. 
    apply Red_input. move => v. apply loopseq_Setoid. 
    foo h0. have := Bism_trans (b v) (Bism_sym (H1 v)). by apply.
move => h. move => r0 f0 h0 f1 h1 s0 f2 hexecseq hstmt. 
have := h _ _ h0 _ (Bism_refl _) _ h1 _  _ hexecseq hstmt.
by apply.   
Qed.

Lemma Xwhile_Wbismc: forall r0 r1,
Xwhile r0 r1 -> Wbismc r0 r1.    
Proof. 
cofix hcoind. move => r0 r1 h0. inversion h0. move: H1.  
dependent inversion hexecseq; move => h5.  
- have := Wbismc_intro Xwhile_Setoid hcoind. apply. 
  rewrite -H1 in H. rewrite [Emb _]io_destr in H; simpl in H. 
  have h1 := Wbism_ret_Red H.
  have h2 := loopseq_Red_ret h1 s1 i e0  hstmt.
  have := Wbismi_Setoid Xwhile_Setoid _ (Bism_sym H0) (Bism_sym h5).
  apply.   
  have := Steps_Wbismi h2. apply. apply Xwhile_Setoid. 
  apply Wbismi_neg_delay_R. apply Xwhile_Setoid.  apply loop_Wbismi. 
- rewrite -H1 in H. 
  have := Wbismc_intro Xwhile_Setoid hcoind. apply.
  rewrite [Emb _]io_destr in H; simpl in H.  
  have [r7 [h2 h1]] := Wbism_output_Red H => {H}.
  have h4 := loopseq_Red_output h2 (Wbism_sym h1)  (Execnd_output v e0) hstmt.
  have := Wbismi_Setoid Xwhile_Setoid _ (Bism_sym H0) (Bism_sym h5). 
  apply. 
  have := Red_Wbismi Xwhile_Setoid h4.  apply. rewrite -H4.  
  rewrite [loopseq _ _ _]io_destr; simpl. rewrite [Emb _]io_destr; simpl. 
  apply Wbismi_output. 
  have := Xwhile_intro h1 (Bism_refl _) (Bism_refl _). apply. 
- rewrite -H1 in H. 
  have := Wbismc_intro Xwhile_Setoid hcoind. apply.
  rewrite [Emb _]io_destr in H; simpl in H.  
  have [f1 [h2 h1]] := Wbism_input_Red H => {H}.
  have h4 := loopseq_Red_input h2 h1  (Execnd_input e0) hstmt.
  have := Wbismi_Setoid Xwhile_Setoid _ (Bism_sym H0) (Bism_sym h5).
  apply.  
  have := Red_Wbismi Xwhile_Setoid h4.  apply. 
  rewrite [loopseq _ _ _]io_destr; simpl. rewrite -H4. 
  rewrite [Emb _]io_destr; simpl. apply Wbismi_input. 
  move => v. have := Xwhile_intro (h1 v) (Bism_refl _) (Bism_refl _).
 apply. 
Qed.   

End Loop.  

Section ifthenelse.

Variable e: expr.
Variable s1 s2: stmt. 
Variable f0 : forall X : stmt -> resd -> resd -> Type,
(forall s0 : stmt, Setoidd2 (X s0)) ->
(forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) ->
forall (s0 : stmt) (st : state) (r : resd),
ExecX X s0 st r -> s0 = s1 -> res.
Variable f1 : forall X : stmt -> resd -> resd -> Type,
(forall s0 : stmt, Setoidd2 (X s0)) ->
(forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) ->
forall (s0 : stmt) (st : state) (r : resd),
ExecX X s0 st r -> s0 = s2 -> res.

Program Definition cond (X : stmt -> resd -> resd -> Type)
(hsetoid: forall s0 : stmt, Setoidd2 (X s0))
(himp: forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) 
(s0 : stmt) (st : state) (r : resd)
(hexec: ExecX X s0 st r)(heq: s0 = Sifthenelse e s1 s2) :=
match hexec with
| ExecX_skip st0 => ret st 
| ExecX_assign _ _ _ => ret st
| ExecX_seq_ret  _ _ _ _ _ _ _ => ret st
| ExecX_seq_input  _ _ _ _ _ _ _ => ret st
| ExecX_seq_output _  _ _ _ _ _ _ _ => ret st
| ExecX_ifthenelse_true a s0' _ st r htrue hs => 
  delay (delay (f0 hsetoid himp hs (_: s0' = s1)))
| ExecX_ifthenelse_false a _ s1' st r _ hs => 
  delay (delay (f1 hsetoid himp hs (_: s1' = s2)))
| ExecX_while_false a s st _ => ret st
| ExecX_while_ret _ _ _ _ _ _ _ _ => ret st
| ExecX_while_input e1 s1 st1 f0 r1 htrue hs hwhile => ret st
| ExecX_while_output e1 s1 st1 v1 r1 r2 htrue hs hwhile =>  ret st 
| ExecX_write a st => ret st
| ExecX_read x st => ret st
end.

End ifthenelse.   



Lemma ExecX_Execdup: forall s,
{f: forall X, (forall s0, Setoidd2 (X s0)) ->
(forall s0, Imp_Setoid (X s0) (Execseqnd s0)) -> 
forall s0 st r,  ExecX X s0 st r -> 
s0 = s -> res &   
forall X (hsetoid: forall s0, Setoidd2 (X s0))  
(heq: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
s0 st r (hexec: ExecX X s0 st r) (h0 h1: s0 = s),
(Execdup s st (f X hsetoid heq s0 st r hexec h0) *
 Wbism (Emb r) (f X hsetoid heq s0 st r hexec h0) *
 Bism (f X hsetoid heq s0 st r hexec h0) 
         (f X hsetoid heq s0 st r hexec h1))%type}.  
Proof. 
move => s. induction s. 
- exists (fun (X : stmt -> resd -> resd -> Type) =>
  fun (hsetoid: forall s0 : stmt, Setoidd2 (X s0)) =>
  fun (heq: forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) =>
  fun (s0 : stmt) => fun (st : state) => fun (r : resd) =>
  fun (hexec: ExecX X s0 st r) => fun (hstmt: s0 = Sskip) =>  
  (ret st)). move => X hsetoid himp s0 st0 r0 hexec heq0 heq1.
  split; [split | idtac]. 
  * apply Execdup_skip. 
  * rewrite heq0 in hexec. foo hexec. rewrite [Emb _]io_destr; simpl. 
     have := Wbism_ret (Red_ret st0) (Red_ret st0). by apply. 
  * by apply Bism_refl.  
- exists (fun (X : stmt -> resd -> resd -> Type) =>
  fun (hsetoid: forall s0 : stmt, Setoidd2 (X s0)) =>
  fun (heq: forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) =>
  fun (s0 : stmt) => fun (st : state) => fun (r : resd) =>
  fun (hexec: ExecX X s0 st r) => fun (hstmt: s0 = Sassign i e) =>  
  (delay (delay (ret (update i (e st) st))))).
   move => X hsetoid himp s0 st0 r0 hexec heq0 heq1. split; [split | idtac]. 
  * apply Execdup_assign. 
  * rewrite heq0 in hexec. foo hexec. rewrite [Emb _]io_destr; simpl. 
    have := Wbism_ret (Red_ret _) (Red_delay (Red_delay (Red_ret _))). by apply. 
  * by apply Bism_refl.  
- move: IHs1 => [f0 hf0]. move: IHs2 => [f1 hf1]. exists (seque f0 f1).
  have f1_Execdup: forall X (h0:forall s0, Setoidd2 (X s0))
  (h1: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
  s0 st r  (h2: ExecX X s0 st r) 
  (h3: s0 = s2), Execdup s2 st (f1 _ h0 h1 _ _ _ h2 h3).
  * move => X h0 h1 s0 st0 r0 h2 h3. 
     have [[h4 _] _] := hf1 X h0 h1 s0 st0 r0 h2 h3 h3. by apply h4. 
  have f1_irr: forall X (hsetoid: forall s0, Setoidd2 (X s0))
  (heq: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
  s0 st r  (hexec: ExecX X s0 st r) (h0 h1: s0 = s2),
  Bism (f1 _ hsetoid heq _ _ _ hexec h0) (f1 _ hsetoid heq _ _ _ hexec h1).
  * move => X h0 h1 s0 st0 r0 h2 h3 h4. 
     have [[_ _] h5] := hf1 X h0 h1 s0 st0 r0 h2 h3 h4. by apply h5.    
  have f1_Wbism: forall X (h0:forall s0, Setoidd2 (X s0))
  (h1: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
  s0 st r  (h2: ExecX X s0 st r) 
  (h3: s0 = s2), Wbism (Emb r) (f1 _ h0 h1 _ _ _ h2 h3).
  * move => X h0 h1 s0 st0 r0 h2 h3. 
     have [[_ h4]  _] := hf1 X h0 h1 s0 st0 r0 h2 h3 h3. by apply h4.
  have f0_Execdup: forall X (h0:forall s0, Setoidd2 (X s0))
  (h1: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
  s0 st r  (h2: ExecX X s0 st r) 
  (h3: s0 = s1), Execdup s1 st (f0 _ h0 h1 _ _ _ h2 h3).
  * move => X h0 h1 s0 st0 r0 h2 h3. 
     have [[h4 _] _] := hf0 X h0 h1 s0 st0 r0 h2 h3 h3. by apply h4. 
  have f0_irr: forall X (hsetoid: forall s0, Setoidd2 (X s0))
  (heq: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
  s0 st r  (hexec: ExecX X s0 st r) (h0 h1: s0 = s1),
  Bism (f0 _ hsetoid heq _ _ _ hexec h0) (f0 _ hsetoid heq _ _ _ hexec h1).
  * move => X h0 h1 s0 st0 r0 h2 h3 h4. 
     have [[_ _] h5] := hf0 X h0 h1 s0 st0 r0 h2 h3 h4. by apply h5.    
  have f0_Wbism: forall X (h0:forall s0, Setoidd2 (X s0))
  (h1: forall s0, Imp_Setoid (X s0) (Execseqnd s0)) 
  s0 st r  (h2: ExecX X s0 st r) 
  (h3: s0 = s1), Wbism (Emb r) (f0 _ h0 h1 _ _ _ h2 h3).
  * move => X h0 h1 s0 st0 r0 h2 h3. 
     have [[_ h4]  _] := hf0 X h0 h1 s0 st0 r0 h2 h3 h3. by apply h4.
  move => X hsetoid heq s0 st0 r0 hexec heq0 heq1. split; [split | idtac].
  * apply seque_correct. apply f0_Execdup. apply f0_Wbism. 
     apply f1_Execdup. 
  * apply seque_Wbism. apply f0_Wbism. apply f1_Wbism. 
  * apply seque_irr. apply f0_irr. apply f1_irr.      
- move: IHs1 => [f0 hf0]. move: IHs2 => [f1 hf1]. 
  exists (cond f0 f1). move => X hsetoid heq s0 st0 r0 hexec;
  dependent inversion hexec. 
  - move => h0. foo h0.  
  - move => h0. foo h0.  
  - move => h0. foo h0.
  - move => h0. foo h0. 
  - move => h0. foo h0. 
  - move => h0 h1. inversion h0; subst.
    rewrite [cond _ _ _ _ _ _ ]io_destr; simpl. 
    have [[h2 h3] h4] := hf0 X hsetoid heq s1 st0 r0 e1
      (cond_obligation_1 h0 eq_refl eq_refl eq_refl
        (JMeq_refl (ExecX_ifthenelse_true s2 e0 e1))) 
      (cond_obligation_1 h1 eq_refl eq_refl eq_refl
        (JMeq_refl (ExecX_ifthenelse_true s2 e0 e1))).
    split; [split |  idtac].
    * have := Execdup_ifthenelse_true _ e0. apply.
       apply Execdup_delay. apply Execdup_delay.
       apply Execdup_ret. by apply h2.
    * have := Wbism_delay_R (Wbism_delay_R h3). by apply. 
    * have := Bism_delay (Bism_delay h4). by apply. 
  - move => h0 h1. inversion h0; subst.
    rewrite [cond _ _ _ _ _ _ ]io_destr; simpl. 
    have [[h2 h3] h4] := hf1 X hsetoid heq s2 st0 r0 e1
      (cond_obligation_2 h0 eq_refl eq_refl eq_refl
        (JMeq_refl (ExecX_ifthenelse_false s1 e0 e1))) 
      (cond_obligation_2 h1 eq_refl eq_refl eq_refl
        (JMeq_refl (ExecX_ifthenelse_false s1 e0 e1))).
    split; [split |  idtac].
    * have := Execdup_ifthenelse_false _ e0. apply.
       apply Execdup_delay. apply Execdup_delay.
       apply Execdup_ret. by apply h2.
    * have := Wbism_delay_R (Wbism_delay_R h3). by apply. 
    * have := Bism_delay (Bism_delay h4). by apply.
  - move => h0; foo h0.      
  - move => h0; foo h0.      
  - move => h0; foo h0.      
  - move => h0; foo h0.      
  - move => h0; foo h0.      
  - move => h0; foo h0.          
- move: IHs => [f hf].  
  exists (fun (X : stmt -> resd -> resd -> Type) =>
  fun (hsetoid: forall s0 : stmt, Setoidd2 (X s0)) =>
  fun (heq: forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) =>
  fun (s0 : stmt) => fun (st : state) => fun (r : resd) =>
  fun (hexec: ExecX X s0 st r) => fun (hstmt: s0 = Swhile e s) =>  
  (delay (loop f hsetoid heq hexec hstmt))).
 have f_Execdup: forall (X : stmt -> resd -> resd -> Type)
  (h0 : forall s0 : stmt, Setoidd2 (X s0))
  (h1 : forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) (s0 : stmt)
  (st : state) (r : resd) (h2 : ExecX X s0 st r) (h3 : s0 = s),
  Execdup s st (f X h0 h1 s0 st r h2 h3).
    move => X0 h0 h1 s0 st1 r1 h2 h3.
    have [[h4 _] _] := hf X0 h0 h1 s0 st1 r1 h2 h3 h3.
    apply h4. 
  have f_Wbism: forall (X : stmt -> resd -> resd -> Type)
  (h0 : forall s0 : stmt, Setoidd2 (X s0))
  (h1 : forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) (s0 : stmt)
  (st : state) (r : resd) (h2 : ExecX X s0 st r) (h3 : s0 = s),
  Wbism (Emb r) (f X h0 h1 s0 st r h2 h3). 
    move => X0 h0 h1 s0 st1 r1 h2 h3.
    have [[_ h4] _] := hf X0 h0 h1 s0 st1 r1 h2 h3 h3.
    apply h4.
  have f_irr: forall (X : stmt -> resd -> resd -> Type)
  (h0 : forall s0 : stmt, Setoidd2 (X s0))
  (h1 : forall s0 : stmt, Imp_Setoid (X s0) (Execseqnd s0)) (s0 : stmt)
  (st : state) (r : resd) (h2 : ExecX X s0 st r) (h3 h4 : s0 = s),
  Bism (f X h0 h1 s0 st r h2 h3) (f X h0 h1 s0 st r h2 h4).
    move => X0 h0 h1 s0 st1 r1 h2 h3 h4.
    have [_ h5] := hf X0 h0 h1 s0 st1 r1 h2 h3 h4.
    apply h5.
  move => X hsetoid heq s0 st0 r0 hexec hstmt0 hstmt1.
  split. split. 
  * rewrite -hstmt0. apply loop_correct. apply f_Execdup.  
     apply f_Wbism. 
  * apply Wbismc_Wbism.  
    have := Wbismc_intro (@Xwhile_Setoid e s f).
    apply.
    apply (@Xwhile_Wbismc e s f) => //.
    have := (@loop_Wbismi e s f). apply => //.
    apply Bism_delay.
  * apply loop_irr. apply f_irr. 
- exists (fun (X: stmt -> resd -> resd -> Type)  
  (hXsetoid: forall s0, Setoidd2 (X s0)) 
  (hXeq: forall s0, Imp_Setoid (X s0) (Execseqnd s0))  
  (s0: stmt) (st: state) (r: resd) 
  (hexec:ExecX X s0 st r) (hstmt: s0 = Swrite e) =>
  (output (e st) (ret st))). move => X hsetoid himp s0 st0 r0 hexec heq0 heq1. 
  split; [ split | idtac ]. 
  * apply Execdup_write. 
  * rewrite heq0 in hexec. foo hexec. rewrite [Emb _]io_destr; simpl. 
     rewrite [Emb _]io_destr; simpl. by apply Wbism_refl.
  * by apply Bism_refl.       
- exists (fun (X: stmt -> resd -> resd -> Type)  
  (hXsetoid: forall s0, Setoidd2 (X s0)) 
  (hXeq: forall s0, Imp_Setoid (X s0) (Execseqnd s0))  
  (s0: stmt) (st: state) (r: resd) 
  (hexec:ExecX X s0 st r) (hstmt: s0 = Sread i) =>
  (input (fun v => ret (update i v st)))).
  move => X hsetoid himp s0 st0 r0 hexec heq0 heq1. 
  split; [ split | idtac ]. 
  * apply Execdup_read. 
  * rewrite heq0 in hexec. foo hexec. rewrite [Emb _]io_destr; simpl.
    have := (@Wbism_input  (input (fun v => Emb (retd (update i v st0))))
    (input (fun v => ret (update i v st0)))) 
    (fun v => Emb (retd (update i v st0)))
    (fun v => ret (update i v st0)) (Red_input _) (Red_input _).
    apply. move => v. rewrite [Emb _]io_destr; simpl. apply Bism_refl. 
    move => v. apply Bism_refl. move => v. rewrite [Emb _]io_destr; simpl.
    apply Wbism_refl. by apply Bism_refl.       
Qed.


Lemma Execnd_Exec: forall s st r,
ExecX execseqnd s st r -> 
{r0: res & (Exec s st r0 * Wbism (Emb r) r0)%type}.
Proof. 
move => s st r h0.
have [f hf] := ExecX_Execdup s.
exists 
(cut (f _ execseqnd_Setoid execseqnd_Execseqnd _ _ _ h0 (refl_equal _))). 
have [[h1 h2] _] := hf _ execseqnd_Setoid execseqnd_Execseqnd
_ _ _ h0 (refl_equal _ )  (refl_equal _). split. 
* apply Execdup_Exec.  by apply h1. 
* have := Wbism_trans h2 (wbism_Wbism (cut_wbism _)). 
   by apply.
Qed.   

   
