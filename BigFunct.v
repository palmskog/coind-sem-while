Require Import ssreflect.
Require Import Trace.
Require Import Language.
Require Import BigRel.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

CoFixpoint loop (k:state -> trace) (p:state -> bool) (st: state) : trace :=
if p st then
  match k st with
  | Tnil st' => Tcons st' (loop k p st')
  | Tcons st' tr => Tcons st' (loopseq k p tr)
  end 
else (Tnil st)

with loopseq (k:state -> trace) (p:state -> bool) (tr:trace) : trace :=
match tr with
| Tnil st => Tcons st (loop k p st) 
| Tcons st tr' => (Tcons st (loopseq k p tr')) 
end.

Lemma loop_true_nil: forall p k st, 
p st = true -> k st = Tnil st -> loop k p st = Tcons st (loop k p st).
Proof.
move => p k st h1 h2. rewrite {1}[loop k p st]trace_destr. 
simpl. rewrite h1. rewrite h2. done. 
Qed. 

Lemma loop_true_cons: forall p k st tr,
p st = true -> k st = Tcons st tr -> loop k p st = Tcons st (loopseq k p tr). 
Proof.
move => p k st tr h1 h2. rewrite {1}[loop k p st]trace_destr.  
simpl. rewrite h1. rewrite h2. done. 
Qed.  

Lemma loop_false: forall k p st, p st = false -> loop k p st = Tnil st.
Proof. 
move => k p st h1. rewrite [loop _ _ _]trace_destr. simpl. rewrite h1. done. 
Qed. 

Lemma loop_nil: forall k p st, loopseq k p (Tnil st) = Tcons st (loop k p st).
Proof.
move => k p st. by rewrite {1}[loopseq _ _ _]trace_destr. 
Qed. 

Lemma loopseq_cons: forall k p st tr, 
loopseq k p (Tcons st tr) = Tcons st (loopseq k p tr).
Proof.
move => k p st tr. by rewrite {1}[loopseq _ _ _]trace_destr. 
Qed. 

CoFixpoint sequence (k: state -> trace) (tr:trace): trace :=
match tr with
| Tnil st => k st
| Tcons st tr' => Tcons st (sequence k tr')
end. 

Lemma sequence_nil: forall k st, sequence k (Tnil st) = k st.
Proof. 
move => k st. rewrite [sequence _ _]trace_destr. 
simpl. rewrite {2}[k st]trace_destr. rewrite /trace_decompose. done. 
Qed.    

Lemma sequence_cons: forall k st tr,
sequence k (Tcons st tr) = Tcons st (sequence k tr).
Proof. 
move => k st tr. rewrite {1}[sequence  _ _]trace_destr. by simpl.  
Qed.   

Fixpoint Exec (s:stmt) (st: state): trace :=
match s with
| Sskip => Tnil st
| Sassign id a => Tcons st (Tnil (update id (a st) st))
| Sseq s1 s2 => sequence (Exec s2) (Exec s1 st) 
| Sifthenelse a s1 s2 =>
  Tcons st (if (is_true (a st)) then (Exec s1 st) else (Exec s2 st))
| Swhile a s =>
  Tcons st (loop (Exec s) (fun st0 => is_true (a st0)) st)
end.

Lemma sequence_correct0: forall s,
(forall st0, exec s st0 (Exec s st0)) -> 
forall tr, execseq s tr (sequence (Exec s) tr).
Proof. 
cofix COINDHYP. move => s h1. case. 
- move => st1. apply execseq_nil. rewrite sequence_nil. by apply h1.
- move => st0 tr0. rewrite sequence_cons. 
  by apply: (execseq_cons _ (COINDHYP _ h1 _)). 
Qed.

Lemma Exec_nil: forall s st1 st2, Exec s st1 = Tnil st2 -> st1 = st2. 
Proof. 
move => s; induction s.
- move => st1 st2 h1. by foo h1.  
- move => st1 st2 h1. by foo h1.  
- move => st1 st2 h1. foo h1. case_eq (Exec s1 st1).
  - move => st3 h2. rewrite h2 in H0. rewrite sequence_nil in H0. 
    move: (IHs1 _ _ h2) => h3 {IHs1 h2}. move: (IHs2 _ _ H0) => h4 {IHs2  H0}.
    by subst.
  - move => st3 tr1 h2. rewrite h2 in H0. rewrite sequence_cons in H0. by inversion H0. 
- move => st1 st2 h1. by inversion h1. 
- move => st1 st2 h1. by inversion h1.
Qed. 

Lemma sequence_eq_nil: forall s  tr st,
sequence (Exec s) tr = Tnil st -> tr = Tnil st /\ Exec s st = Tnil st. 
Proof. 
move => s. case. 
- move => st1 st2 h1. rewrite sequence_nil in h1.
  move: (Exec_nil h1) => h2. subst. by split.   
- move => st1 tr st2 h1. rewrite sequence_cons in h1. by inversion h1. 
Qed. 

Lemma Exec_sound_nil: forall s st st', 
Exec s st = Tnil st' -> exec s st (Tnil st').
Proof.
induction s.  
- move => st1 st2 h1. simpl in h1. foo h1. by apply exec_skip. 
- move => st1 st2 h1. simpl in h1. by inversion h1. 
- move => st1 st2 h1. simpl in h1. move: (sequence_eq_nil h1) => [h2 h3].
  move: (IHs1 _ _ h2) => h4 {IHs1 h2}. move: (IHs2 _ _ h3) => h5 {IHs2 h3}.
  apply: (exec_seq h4). by apply (execseq_nil h5). 
- move => st1 st2 h1. by inversion h1. 
- move => st st1 h1. by inversion h1.  
Qed.

Lemma loop_skip_correct: forall s st e,
Exec s st = Tnil st ->
is_true (e st) = true ->
exec (Swhile e s) st
 (Tcons st (loop (Exec s) (fun st0 => is_true (e st0)) st)). 
Proof. 
move => s st e h1 h2. cofix COINDHYP.
apply: (exec_while_loop h2). apply execseq_cons. apply execseq_nil. 
apply (Exec_sound_nil h1). rewrite [loop _ _ _]trace_destr. simpl.
rewrite h1. rewrite h2. by apply: (execseq_cons _ (execseq_nil COINDHYP)).  
Qed.

Lemma loop_correct0: forall  e s,
(forall st, exec s st (Exec s st)) ->
forall st, exec (Swhile e s) st
 (Tcons st (loop (Exec s) (fun st0 => is_true (e st0)) st)). 
Proof.
move => e s h1. cofix COINDHYP.
have COINDHYP2: forall tr, 
execseq  (Swhile e s) tr (loopseq (Exec s) (fun st0 => is_true (e st0)) tr).
* cofix COINDHYP2. case. 
  - move => st1. rewrite [loopseq _ _ _]trace_destr; simpl. 
    by apply: (execseq_nil (COINDHYP _)). 
  - move => st1 tr1. rewrite [loopseq _ _ _]trace_destr; simpl.  
    by apply: (execseq_cons _ (COINDHYP2 _)).   
* move => st. case_eq (is_true (e st)) => h2.
  - case_eq (Exec s st). 
    - move => st1 h3. have h4 := (Exec_nil h3). rewrite -h4 in h3. 
      by apply: (loop_skip_correct h3 h2). 
    - move => st1 tr1 h3. rewrite [loop _ _ _]trace_destr. simpl.
      rewrite h2. rewrite h3. apply: (exec_while_loop h2 (execseq_cons _  (execseq_nil (h1 _)))).
      rewrite h3.  by apply: (execseq_cons _ (execseq_cons _ (COINDHYP2 _))).
  - rewrite [loop _ _ _]trace_destr. simpl. rewrite h2. by apply: (exec_while_false _ h2).
Qed.    

(* the big-step functional semantics correct wrt the big-step relational semantics *)
Lemma Exec_correct_exec: forall s st, exec s st (Exec s st).
Proof. 
move => s; induction s. 
- move => st. simpl. by apply exec_skip. 
- move => st. simpl. by apply exec_assign. 
- move => st. simpl. have h1 := (IHs1 st). 
  have h2 := sequence_correct0  IHs2 (Exec s1 st). by apply: (exec_seq h1 h2). 
- move => st. simpl. case_eq (is_true (e st)) => h1. 
  - apply: (exec_ifthenelse_true _ h1). by apply: (execseq_cons _ (execseq_nil (IHs1 _))).
  - apply: (exec_ifthenelse_false _ h1). by apply: (execseq_cons _ (execseq_nil (IHs2 _))).
- move => st. simpl. by apply: (loop_correct0 _ IHs).
Qed.

(* the big-step relational semantics correct wrt the big-step functional semantics *)
Lemma exec_correct_Exec: forall s st tr, exec s st tr -> bisim tr (Exec s st).
Proof. 
move => s st tr h1. have h2 := Exec_correct_exec s st. 
by have := exec_deterministic h1 h2; apply.
Qed.  
