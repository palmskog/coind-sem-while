Require Import SsrExport.
Require Import Trace.
Require Import Language.
Require Import BigRel.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Exec.

Variable tt: expr.
Hypothesis tt_spec: forall st, is_true (tt st) = true.

CoInductive exec1: stmt -> state -> trace -> Set :=
| exec1_skip: forall st, 
    exec1 Sskip st (Tnil st)
| exec1_assign: forall id a st, 
    exec1 (Sassign id a) st (Tcons st (Tnil (update id (a st) st)))
| exec1_seq: forall s1 s2 st tr tr',
    exec1 s1 st tr ->
    execseq1 s2 tr tr' ->
    exec1 (Sseq s1 s2) st tr'
| exec1_ifthenelse_true: forall a s1 s2 st tr,
    is_true (a st) = true ->
    execseq1 s1 (Tcons st (Tnil st)) tr ->
    exec1 (Sifthenelse a s1 s2) st tr
| exec1_ifthenelse_false: forall a s1 s2 st tr,
    is_true (a st) = false ->
    execseq1 s2 (Tcons st (Tnil st)) tr ->
    exec1 (Sifthenelse a s1 s2) st tr
| exec1_while_false: forall a s st,
    is_true (a st) = false ->
    exec1 (Swhile a s) st (Tnil st)
| exec1_while_loop: forall a s st tr tr',
    is_true (a st) = true ->
    exec1 s st tr ->
    execseq1 (Swhile a s) tr tr' ->
    exec1 (Swhile a s) st tr'

with execseq1: stmt -> trace -> trace -> Set :=
| exec1_nil: forall st s tr,
  exec1 s st tr ->
  execseq1 s (Tnil st) tr
| exec1_cons: forall tr s tr' e,
  execseq1 s tr tr' ->
  execseq1 s (Tcons e tr) (Tcons e tr').

Lemma lemma1: forall st tr, exec1 (Swhile tt Sskip) st tr.
Proof. 
cofix COINDHYP. move => st tr. apply: exec1_while_loop.
* by apply: tt_spec. 
* by apply exec1_skip. 
* by have := exec1_nil (COINDHYP st tr); apply. 
Qed.

CoInductive last_true (e: expr): trace -> Prop :=
| last_true_nil: forall st,
  is_true (e st) = true ->
  last_true e (Tnil st)
| last_true_cons: forall st tr,
  last_true e tr ->
  last_true e (Tcons st tr).
    
CoInductive last_false (e: expr): trace -> Prop :=
| last_false_nil: forall st,
  is_true (e st) = false ->
  last_false e (Tnil st)
| last_false_cons: forall st tr,
  last_false e tr ->
  last_false e (Tcons st tr).

CoFixpoint duplast (tr: trace): trace :=
match tr with
| Tnil st => Tcons st (Tnil st)
| Tcons st tr' => Tcons st (duplast tr')
end.  

CoFixpoint updatelast (id: id) (e: expr) (tr: trace): trace :=
match tr with
| Tnil st => Tcons st (Tnil (update id (e st) st))
| Tcons st tr' => Tcons st (updatelast id e tr')
end.  


CoInductive execseq2: stmt -> trace -> trace -> Set :=
| execseq2_skip: forall tr, 
    execseq2 Sskip tr tr
| execseq2_assign: forall id a tr, 
    execseq2 (Sassign id a) tr (updatelast id a tr)
| execseq2_seq: forall s1 s2 tr tr' tr'',
    execseq2 s1 tr tr' ->
    execseq2 s2 tr' tr'' ->
    execseq2 (Sseq s1 s2) tr tr''
| execseq2_ifthenelse_true: forall a s1 s2 tr tr',
    last_true a tr ->
    execseq2 s1 (duplast tr) tr' ->
    execseq2 (Sifthenelse a s1 s2) tr tr'
| execseq2_ifthenelse_false: forall a s1 s2 tr tr',
    last_false a tr ->    
    execseq2 s2 (duplast tr) tr' ->
    execseq2 (Sifthenelse a s1 s2) tr tr'
| execseq2_while_false: forall a s tr,
    last_false a tr ->
    execseq2 (Swhile a s) tr (duplast tr)
| execseq2_while_loop: forall a s tr tr' tr'',
  last_true a tr ->
  execseq2 s (duplast tr) tr' ->
  execseq2 (Swhile a s) tr' tr'' ->
  execseq2 (Swhile a s) tr tr''.

Inductive exec2: stmt -> state -> trace -> Prop :=
| exec2_intro: forall s st tr,  execseq2 s (Tnil st) tr -> exec2 s st tr.

Lemma lemma2: forall st tr, exec2 (Swhile tt Sskip) st tr.
Proof.
have h1: forall tr tr', execseq2 (Swhile tt Sskip) tr tr'.
* cofix COINDHYP. move => tr tr'. 
  have := (@execseq2_while_loop _ _ _ (duplast tr) tr'); apply.
  * move: tr. cofix COINDHYP2. case. 
    - move => st. apply: last_true_nil. by apply: tt_spec. 
    - move => st tr. by have := last_true_cons _ (COINDHYP2 _); apply. 
  * by apply: execseq2_skip. 
  * by apply: COINDHYP.
* move => st tr. apply: exec2_intro. by apply: h1.  
Qed.

Lemma lemma3: forall x st tr, exec2 (Swhile tt (Sassign x (fun st => (st x + 1)%Z))) st tr.
Proof. 
move => x. 
have h1: forall tr tr', execseq2 (Swhile tt (Sassign x (fun st => (st x + 1)%Z))) tr tr'.
* cofix COINDHYP. move => tr0 tr1. 
  have := (@execseq2_while_loop _ _ _ (updatelast x (fun st => (st x + 1)%Z) (duplast tr0)) tr1); apply. 
  * move: tr0. cofix COINDHYP0. case. 
    - move => st. apply: last_true_nil. by apply: tt_spec. 
    - move => st tr. by have := last_true_cons _ (COINDHYP0 _); apply. 
  * by apply: execseq2_assign. 
  * by apply: COINDHYP.
* move => st tr. apply: exec2_intro. by apply: h1.  
Qed.

End Exec.

CoInductive split: trace -> trace -> state -> trace -> Set :=
| split_nil: forall st, 
  split (Tnil st) (Tnil st) st (Tnil st)
| split_cons: forall st tr,
  split (Tcons st tr) (Tnil st) st (Tcons st tr)
| split_delay: forall st st' tr tr' tr'',
  split tr tr' st' tr'' -> 
  split (Tcons st tr) (Tcons st tr') st' tr''.

CoInductive exec3: stmt -> state -> trace -> Set :=
| exec3_skip: forall st, 
  exec3 Sskip st (Tnil st)
| exec3_assign: forall id a st, 
  exec3 (Sassign id a) st (Tcons st (Tnil (update id (a st) st)))
| exec3_seq: forall s1 s2 st st' tr tr' tr'',
  split tr tr' st' tr'' ->
  exec3 s1 st tr' ->
  exec3 s2 st' tr'' ->
  exec3 (Sseq s1 s2) st tr
| exec3_ifthenelse_true: forall a s1 s2 st tr,
  is_true (a st) = true ->
  exec3 s1 st tr ->
  exec3 (Sifthenelse a s1 s2) st (Tcons st tr)
| exec3_ifthenelse_false: forall a s1 s2 st tr,
  is_true (a st) = false ->
  exec3 s2 st tr ->
  exec3 (Sifthenelse a s1 s2) st (Tcons st tr)
| exec3_while_false: forall a s st,
  is_true (a st) = false ->
  exec3 (Swhile a s) st (Tcons st (Tnil st))
| exec3_while_loop: forall a s st st' tr tr' tr'',
  split tr tr' st' tr'' ->
  is_true (a st) = true ->
  exec3 s st tr' ->
  exec3 (Swhile a s) st' tr'' ->
  exec3 (Swhile a s) st (Tcons st tr).

Lemma lemma4: forall s st tr, exec3 s st tr -> exec s st tr.
Proof. 
cofix  COINDHYP. move => s st tr h1. foo h1. 
- by apply: exec_skip. 
- by apply: exec_assign. 
- have := exec_seq (COINDHYP _ _ _ H0); apply.
  move => {H0}. move: tr' st' tr'' tr H H1. cofix COINDHYP0. 
  move => st0 st1 tr0 tr1 h1 h2. foo h1. 
  - apply execseq_nil. by have := COINDHYP _ _ _ h2; apply.  
  - apply execseq_nil. by have := COINDHYP _ _ _ h2; apply. 
  - apply execseq_cons. by have := COINDHYP0 _ _ _ _ H h2; apply.
- apply exec_ifthenelse_true. 
  * by apply H.
  * apply execseq_cons. apply execseq_nil.
     have := COINDHYP _ _ _ H0; apply.
- apply exec_ifthenelse_false. 
  * by apply H.
  * apply execseq_cons. apply execseq_nil.
    have := COINDHYP _ _ _ H0; apply.
- apply exec_while_false. by apply H. 
- apply: exec_while_loop.
  * by apply H0.
  * apply execseq_cons. apply execseq_nil. 
     have h:= COINDHYP _ _ _ H1. by apply h.
  * apply execseq_cons. move => {H0 H1}. move: tr0 st' tr' tr'' H H2. 
    cofix COINDHYP0. move => tr0 st0 tr1 tr2 h1 h2. foo h1. 
    - apply execseq_nil. by have := COINDHYP _ _ _ h2; apply. 
    - apply execseq_nil. by have := COINDHYP _ _ _ h2; apply. 
    - apply execseq_cons. by have := COINDHYP0 _ _ _ _ H h2. 
Qed.      

     
