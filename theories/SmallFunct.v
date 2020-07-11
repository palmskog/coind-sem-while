Require Import SsrExport.
Require Import Trace.
Require Import Language.
Require Import SmallRel.
Require Import BigRel.
Require Import BigFunct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* one-step reduction function *)
Fixpoint red (s: stmt) (st: state) {struct s}: option (stmt * state) := 
match s with
| Sskip => None 
| (Sassign x a) => Some (Sskip, update x (a st) st)
| (Sseq s1 s2) =>
  match red s1 st with
  | Some (s1', st') => Some (Sseq s1' s2, st')
  | None => red s2 st
  end
| (Sifthenelse a s1 s2) =>
  if is_true (a st) then Some (s1, st) else Some (s2, st)
| (Swhile a s) =>
  if is_true (a st)  then Some (Sseq s (Swhile a s), st) 
  else Some (Sskip, st)
end. 

(* small-step functional semantics *)
CoFixpoint Redm (s: stmt) (st: state): trace :=
match red s st with
| None => Tnil st
| Some (s', st') => Tcons st (Redm s' st') 
end.

Lemma red_then_stop: forall s st,
red s st = None -> stop s. 
Proof. 
move => s; induction s. 
- move => st h1. by apply stop_skip. 
- move => st h1. by inversion h1.  
- move => st h1. foo h1. case_eq (red s1 st).  
  - move => [s1'  st'] h2. rewrite h2 in H0. by inversion H0.  
  - move => h2. rewrite h2 in H0. by have := stop_seq (IHs1 _ h2) (IHs2 _ H0); apply. 
- move => st h1. foo h1.  case_eq (is_true (e st)); move => h2.
  - rewrite h2 in H0. by inversion H0. 
  - rewrite h2 in H0. by inversion H0. 
- move => st h1. foo h1. case_eq (is_true (e st)); move => h2.
  - rewrite h2 in H0. by inversion H0. 
  - rewrite h2 in H0. by inversion H0.  
Qed.

Lemma red_then_step: forall s st s' st',
red s st = Some (s', st') -> step s st s' st'.
Proof. 
move => s; induction s. 
- move => st s st' h1. by inversion h1.  
- move => st s st' h1. foo h1. by apply step_assign. 
- move => st1 s3 st2 h1. case_eq (red s1 st1).  
  - move => [s1' st1'] h2. foo h1. rewrite h2 in H0. foo H0.   
    apply: step_seq1. by have := IHs1 _ _ _ h2; apply.   
  - move => h2. foo h1. rewrite h2 in H0. 
    by have := step_seq2 (red_then_stop h2) (IHs2 _ _ _ H0); apply.   
- move => st1 s3 st2 h1. case_eq (is_true (e st1)) => h2.
  - simpl in h1. rewrite h2 in h1. foo h1.
    apply: step_ifthenelse_true. by apply h2. 
  - simpl in h1. rewrite h2 in h1. foo h1.  
    apply: step_ifthenelse_false. by apply h2. 
- move => st s' st' h1. case_eq (is_true (e st)) => h2. 
  - simpl in h1. rewrite h2 in h1. foo h1. apply: step_while_true. 
    by apply h2.  
  - simpl in h1. rewrite h2 in h1. foo h1. 
    apply: step_while_false. by apply h2.  
Qed.

Lemma stop_then_red: forall s st, stop s -> red s st = None. 
Proof.
induction 1. 
- by simpl.
- simpl. rewrite IHstop1. by apply IHstop2. 
Qed. 

Lemma step_then_red: forall s st s' st', 
step s st s' st' -> red s st = Some (s', st').
Proof. 
induction 1. 
- by simpl.
- simpl. rewrite IHstep. simpl. done. 
- simpl. have h1 := stop_then_red st H. rewrite h1. rewrite IHstep. done. 
- simpl. rewrite H. done. 
- simpl. by rewrite H. 
- simpl. by rewrite H.
- simpl. by rewrite H. 
Qed.
 
(* the small-step functional semantics correct wrt the small-step relational semantics. *)
Lemma Redm_correct_redm: forall st s, redm s st (Redm s st).
Proof.
cofix COINDHYP. move => st s. rewrite [Redm s st]trace_destr.
simpl. case_eq (red s st). 
- move => [s' st'] h1. simpl. have h2 := red_then_step h1. 
  have := redm_step h2; apply. by apply COINDHYP.
- move => h1. apply redm_stop. by have := red_then_stop h1; apply.  
Qed.

(* the small-step relational semantics correct wrt the small-step functional semantics *)
Lemma redm_correct_Redm: forall s st tr, redm s st tr -> bisim tr (Redm s st).
Proof. 
move => s st tr h1. have h2 := Redm_correct_redm st s. 
by have := redm_deterministic h1 h2; apply. 
Qed.   

Lemma redmseq_correct_execseq0: forall s,
(forall st tr, redm s st tr -> exec s st tr) ->
forall tr1 tr2, redm_str s tr1 tr2 ->
execseq s tr1 tr2.
Proof.
move => s h. cofix COINDHYP. move => tr1 tr2 h1. foo h1.  
- by have := execseq_nil (h _ _ H); apply.  
- by have := execseq_cons _  (COINDHYP _ _ H); apply. 
Qed.

Lemma Redm_sequence: forall s1 s2 st,
bisim (Redm (Sseq s1 s2) st) (sequence (Redm s2) (Redm s1 st)).
Proof.
cofix COINDHYP. move => s1 s2 st. 
rewrite [Redm (Sseq s1 s2) st]trace_destr; simpl.  
rewrite [Redm s1 st]trace_destr; simpl. case_eq (red s1 st). 
- move => [s1' st'] h1. rewrite [sequence _ _]trace_destr; simpl. 
  by have := bisim_cons _(COINDHYP _ _ _); apply. 
- move => h1.  rewrite [sequence _ _]trace_destr; simpl. 
  case_eq (red s2 st).
  - move => *. by apply bisim_reflexive. 
  - move => *.  by apply bisim_nil. 
Qed.


Lemma sequence_deterministic0: forall k1 k2,
(forall st, bisim (k1 st) (k2 st)) ->
forall tr1 tr2, bisim tr1 tr2 ->
bisim (sequence k1 tr1) (sequence k2 tr2).
Proof.
move => k1 k2 h1. cofix COINDHYP. move => tr1 tr2 h2. foo h2. 
- rewrite [sequence k1 _]trace_destr. 
  rewrite [sequence k2 _]trace_destr; simpl. 
  have h3 := h1 st. foo h3.
  - by apply bisim_nil. 
  - by have := bisim_cons _ H1; apply. 
- rewrite [sequence k1 _]trace_destr; simpl. 
  rewrite [sequence k2 _]trace_destr; simpl. 
  by have := bisim_cons  _ (COINDHYP _ _ H); apply. 
Qed. 

Lemma Redm_loop_skip: forall a s st,
is_true (a st) = true ->
red s st = None ->
bisim (Redm (Sseq s (Swhile a s)) st)
 (loop (Redm s) (fun st0 => is_true (a st0)) st).
Proof. 
move => a s st h1 h2. cofix COINDHYP. 
rewrite [Redm _ _]trace_destr; simpl. 
rewrite [loop _ _ _]trace_destr; simpl.
rewrite h1; rewrite h2; simpl.
by have := bisim_cons _ COINDHYP; apply. 
Qed.  


Lemma Redm_loop: forall a s,
forall st, bisim (Redm (Swhile a s) st) 
 (Tcons st (loop (Redm s) (fun st0 => is_true (a st0)) st)).
Proof.
cofix COINDHYP. 
have COINDHYP2: forall a s s1 st1, 
bisim (Redm (Sseq s1 (Swhile a s)) st1)
(loopseq (Redm s) (fun st0 => is_true (a st0)) (Redm s1 st1)). 
* cofix COINDHYP2. move => a s s1 st1. case_eq (red s1 st1).
  - move => [s1' st1'] h1. rewrite [loopseq _ _ _]trace_destr; simpl. 
    rewrite [Redm _ _]trace_destr; simpl. rewrite h1. simpl. 
    by have := bisim_cons _ (COINDHYP2 _ _ _ _); apply.   
  - move => h1. case_eq (is_true (a st1)) => h2.
    - rewrite [Redm _ _]trace_destr; simpl. rewrite h1. rewrite h2. simpl. 
      rewrite [loopseq _ _ _]trace_destr; simpl. rewrite h1. 
      rewrite [loop _ _ _]trace_destr; simpl. rewrite h2. 
      case_eq (red s st1). 
      - move => [s' st1'] h3. rewrite [Redm _ _]trace_destr; simpl. 
        rewrite h3. simpl. by have := bisim_cons _ (bisim_cons _ (COINDHYP2 _ _ _ _)); apply.  
      - move => h3. rewrite [Redm _ _]trace_destr; simpl. rewrite h2; rewrite h3; simpl. 
        by apply: (bisim_cons _ (bisim_cons _ (Redm_loop_skip h2 h3))).
    - rewrite [Redm _ _]trace_destr; simpl. rewrite h1; rewrite h2; simpl.
      rewrite [loopseq _ _ _]trace_destr; simpl. rewrite h1; simpl. 
      rewrite [loop _ _ _]trace_destr; simpl. rewrite h2; simpl.
      rewrite [Redm _ _]trace_destr; simpl. by apply bisim_reflexive. 
* move => a s st. case_eq (is_true (a st)) => h1.
  - rewrite [Redm _ _]trace_destr; simpl. rewrite h1. simpl.
    case_eq (red s st). 
    - move => [s' st'] h2. 
      rewrite [loop _ _ _]trace_destr; simpl. rewrite h1; rewrite h2; simpl.
      rewrite [Redm _ _]trace_destr; simpl. rewrite h2; simpl. 
      by apply: (bisim_cons _ (bisim_cons _ (COINDHYP2 _ _ _ _))).
    - move => h2. by apply: (bisim_cons _ (Redm_loop_skip h1 h2)).
  - rewrite [Redm _ _]trace_destr; simpl. rewrite h1; simpl. 
    rewrite [Redm _ _]trace_destr; simpl. 
    rewrite [loop _ _ _]trace_destr; simpl. rewrite h1; simpl. 
    by apply bisim_reflexive. 
Qed.   

Lemma loop_deterministic0: forall k1 k2 p,
(forall st, bisim (k1 st) (k2 st)) ->
forall st, bisim (loop k1 p st) (loop k2 p st).
Proof. 
move => k1 k2 p h1.  cofix COINDHYP. 
have COINDHYP2:forall tr1 tr2,
bisim tr1 tr2 -> bisim (loopseq k1 p tr1) (loopseq k2 p tr2).
- cofix COINDHYP2. move => tr1 tr2 h2. foo h2. 
  - rewrite [loopseq k1 _ _]trace_destr; simpl. 
    rewrite [loopseq k2 _ _]trace_destr; simpl. 
    by apply: (bisim_cons _ (COINDHYP _)). 
  - rewrite [loopseq k1 _ _]trace_destr; simpl. 
    rewrite [loopseq k2 _ _]trace_destr; simpl. 
    by apply: (bisim_cons _ (COINDHYP2 _ _ H)). 
* move => st. case_eq (p st) => h2.
  - have h3 := h1 st. foo h3. 
    - rewrite [loop k1 _ _]trace_destr; simpl.
      rewrite [loop k2 _ _]trace_destr; simpl. 
      rewrite h2; rewrite - H; rewrite -H0. 
      by apply: (bisim_cons _ (COINDHYP _)). 
    - rewrite [loop k1 _ _]trace_destr; simpl.
      rewrite [loop k2 _ _]trace_destr; simpl. 
      rewrite h2; rewrite - H; rewrite -H0. 
      by apply: (bisim_cons _ (COINDHYP2 _ _ H1)).
  - rewrite [loop k1 _ _]trace_destr; simpl.
    rewrite [loop k2 _ _]trace_destr; simpl. rewrite h2. 
    by apply bisim_nil. 
Qed.  

(* equivalence of the small-step functional semantics to the big-step functional semantics *)
Lemma Exec_Redm: forall s st, bisim (Exec s st) (Redm s st).
Proof. 
move => s; induction s. 
- move => st. rewrite [Redm _ _]trace_destr. simpl. by apply bisim_nil. 
- move => st. rewrite [Redm _ _]trace_destr. simpl. 
  rewrite [Redm _ _]trace_destr; simpl. by apply: (bisim_cons _ (bisim_nil _)).
- move => st. simpl. have h1 := IHs1 st. 
  have h2 := sequence_deterministic0 IHs2 h1. 
  have h3 := Redm_sequence s1 s2 st.
  by apply: (bisim_transitive h2 (bisim_symmetric h3)).  
- move => st. case_eq (is_true (e st)) => h1.
  - rewrite [Redm _ _]trace_destr; simpl. rewrite h1; simpl.
    by apply: (bisim_cons _ (IHs1 _)).  
  - rewrite [Redm _ _]trace_destr; simpl. rewrite h1; simpl.
    by apply: (bisim_cons _ (IHs2 _)).
- move => st. simpl. have h1 := Redm_loop e s st.
  have h2 := loop_deterministic0 (fun st0 => is_true (e st0)) IHs st.
  by apply: (bisim_symmetric (bisim_transitive h1 (bisim_cons _ (bisim_symmetric h2)))). 
Qed. 

(* the small-step relational semantics correct wrt the big-step relational semantics *) 
(* by going through the functional semantics *)
Lemma redm_correct_exec: forall s st tr, redm s st tr -> exec s st tr.
Proof.
move => s st tr h1. 
have h2 := Redm_correct_redm st s. 
have h3 := redm_deterministic h1 h2. 
have h4 := Exec_Redm s st. 
have h5 := Exec_correct_exec s st.
by have := exec_insensitive h5 (bisim_transitive h4 (bisim_symmetric h3)); apply. 
Qed.  

