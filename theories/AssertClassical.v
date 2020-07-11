Require Import SsrExport.
Require Import Setoid. 
Require Import Trace.
Require Import Language.
Require Import Assert.
Require Import ClassicalEpsilon.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition follows_dec : forall p tr0 tr1 (h: follows p tr0 tr1),
 { tr & { st | tr0 = Tnil st /\ hd tr = st /\ p tr } } +
 { tr & { tr' & { st | tr0 = Tcons st tr /\ tr1 = Tcons st tr' /\ follows p tr tr'} } }.
intros.
destruct tr0.
- case (excluded_middle_informative (p tr1)) => H.
  * left. exists tr1. exists s. by inversion h; subst.
  * apply False_rect.
    by inversion h.
- destruct tr1.
  * case (excluded_middle_informative (p (Tnil s0))) => H.
    + left. exists (Tnil s0). exists s0. by inversion h; subst.
    + apply False_rect.
      by inversion h.
  * right.
    exists tr0. exists tr1. exists s.
    by inversion h; subst.
Defined.

CoFixpoint midp_dec (p0 p1: trace -> Prop) (tr0 tr1: trace) (h: follows (append p0 p1) tr0 tr1) : trace.
case (follows_dec h).
- case => tr; case => st; case => h1; case => h2 h3.
  apply constructive_indefinite_description in h3.
  case: h3 => x [h4 h5].
  apply x.
- case => tr; case => tr'; case => st; case => h1; case => h2 h3.
  subst.
  apply (Tcons st (@midp_dec _ _ _ _ h3)).
Defined.

Lemma midp_midp_dec : forall (p0 p1: trace -> Prop)  (tr0 tr1: trace) (h : follows (append p0 p1) tr0 tr1),
 midp h (midp_dec h).
Proof.
cofix CIH.
dependent inversion h.
- subst.
  intros.
  rewrite [midp_dec _]trace_destr. simpl.
  case (excluded_middle_informative _); simpl; last by move => n.
  case (constructive_indefinite_description _ _); simpl.
  move => x a0 hm.
  destruct a0.  
  apply midp_follows_nil => //.
  by destruct x.
  by destruct x.
- subst.
  rewrite [midp_dec _]trace_destr. simpl.
  by apply (@midp_follows_delay p0 p1 (Tcons st tr) (Tcons st tr') (follows_delay st f) tr tr' f st (midp_dec f)).
Qed.

Lemma append_assoc_R: forall p1 p2 p3,
forall tr, (append p1 (append p2 p3)) tr -> (append (append p1 p2)  p3) tr.
Proof. 
move => p1 p2 p3 tr0 h1.  move: h1 => [tr1 [h1 h2]].
exists (midp_dec h2). split. 
- exists tr1. split.
  * done.  
  * by have := midp_before (midp_midp_dec h2).
- by have := midp_after (midp_midp_dec h2).
Qed.

(* Lemma 3.4 (4) <= *)
Lemma Append_assoc_R: forall p1 p2 p3,
(p1 *** p2 *** p3) =>> (p1 *** p2) *** p3.
Proof. 
move => p1 p2 p3 tr0 h1. destruct p1 as [f1 hf1]. destruct p2 as [f2 hf2]. 
destruct p3 as [f3 hf3]. simpl. simpl in h1. apply append_assoc_R. by apply h1. 
Qed.
