From CoindSemWhile Require Import SsrExport Trace Language Semax SemaxSound.
From CoindSemWhile Require Import Assert AssertClassical BigFunct.
From Coq Require Import Lia Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition udt (u: assertS) (x: id) (a: expr): assertS :=
fun st => exists st0 : state, (u st0) /\ ((update x (a st0) st0) = st).

Inductive tsemax2: assertS -> stmt -> assertS -> Prop :=

| tsemax2_skip: forall u, tsemax2 u Sskip u

| tsemax2_assign: forall u x a, 
  tsemax2 u (Sassign x a) (udt u x a)

| tsemax2_seq: forall s1 s2 u1 u2 u3,
  tsemax2 u1 s1 u2->
  tsemax2 u2 s2 u3 ->
  tsemax2 u1 (Sseq s1 s2) u3

| tsemax2_ifthenelse: forall a s1 s2 u1 u2,
  tsemax2 (u1 andS eval_true a) s1 u2 ->
  tsemax2 (u1 andS eval_false a) s2 u2 ->
  tsemax2 u1 (Sifthenelse a s1 s2) u2

| tsemax2_while:forall a s m (J: nat -> assertS),
  (forall n, tsemax2 (eval_true a andS (J n)) s 
   (exS (fun k => (fun st => k < n) andS (J k))))->
  tsemax2 (J m) (Swhile a s) (exS (fun k => (fun st => k <= m) andS J k andS eval_false a))

| tsemax2_conseq: forall s u1 u2 v1 v2,
  u1 ->> u2 -> 
  v2 ->> v1 -> 
  tsemax2 u2 s v2 ->
  tsemax2 u1 s v1

| tsemax2_ex: forall s (A: Type) (u: A -> assertS) (v: A -> assertS),
  (forall x, tsemax2 (u x) s (v x)) ->
  tsemax2 (exS u) s (exS v). 

Lemma tsemax2_conseq_L: forall s u1 u2 v,
u1 ->> u2 -> tsemax2 u2 s v -> tsemax2 u1 s v.
Proof. 
move => s u1 u2 v h0 h1. 
have := tsemax2_conseq h0 (@assertS_imp_refl _) h1. apply.
Qed.

Lemma tsemax2_conseq_R: forall s u v1 v2,
v2 ->> v1 -> tsemax2 u s v2 -> tsemax2 u s v1.
Proof.
move => s u v1 v2 h0 h1. have := tsemax2_conseq (@assertS_imp_refl _) h0 h1; apply.
Qed.

Lemma tsemax2_false: forall s u, tsemax2 ffS s u. 
Proof.
move => s. induction s. 
- move => u. have hs := tsemax2_skip ffS. have := tsemax2_conseq_R _ hs. 
  apply. done. 
- move => u. have hs := tsemax2_assign ffS. have := tsemax2_conseq_R _ (hs _ _) => {hs}.
  apply. move => st0 [st1 [h0 _]]. done. 
- move => u. have hs1 := IHs1 ffS => {IHs1}. have hs2 := IHs2 u => {IHs2}.
  have := tsemax2_seq hs1 hs2. done. 
- move => u. have hs1 := IHs1 u => {IHs1}. have hs2 := IHs2 u => {IHs2}.
  have htrue : (ffS andS eval_true e) ->> ffS.
  * move => st0 [h0 h1]. done.
  have hfalse : (ffS andS eval_false e) ->> ffS.
  * move => st0 [h0 h1]. done.     
  have := tsemax2_ifthenelse (tsemax2_conseq_L htrue hs1) (tsemax2_conseq_L hfalse hs2).
  done. 
- move => u. set J := fun m: nat => ffS. 
  have hs: forall n, tsemax2 (eval_true e andS J n) s (exS (fun k => (fun st => k < n)
  andS (J k))).
  * move => n. have := tsemax2_conseq _ _ (IHs (exS (fun k => (fun st => k < n) andS J k))). 
    apply => //. rewrite /J. move => st [_ h]. done. 
  have := tsemax2_conseq _ _ (tsemax2_while 0 hs). apply => //. move => st0.
  move => [n0 h0]. destruct h0 as [h0 [h1 h2]]. done. 
Qed.

Inductive len: nat -> trace -> Prop :=
| len_stop: forall n st, len n (Tnil st)
| len_delay: forall n st tr, len n tr -> len (S n) (Tcons st tr).

Lemma len_S: forall n tr, len n tr -> len (S n) tr.
Proof. induction 1. 
- apply len_stop. 
- apply len_delay => //.
Qed.

Lemma len_monotone: forall n m, n <= m -> 
forall tr, len n tr -> len m tr.
Proof. have: forall n m tr, len m tr -> len (n + m) tr.
move => n. induction n. 
- move => m tr. rewrite (_: 0 + m = m). done.  by lia.
- move => m tr h0. have := IHn _ _ h0 => {IHn h0}. move => h0. 
  rewrite (_: S n + m = S (n + m)); last by lia.
  have := len_S h0. done. 
move => h. move => n m h0 tr h1. 
rewrite (_: m = (m - n) + n); last by lia. 
have := h _ _ _ h1. apply.
Qed.

Definition Len (p: assertT) (n: nat) : assertS :=
fun st => forall tr, (hd tr = st) /\ (satisfy p tr) -> len n tr.

(* Lemma 4.1: ⌈P⌉n is anti-monotone. *)
Lemma Len_monotone: forall n p q, q =>> p -> (Len p n) ->> (Len q n).
Proof. move => n p q hpq st0. rewrite /Len. move => hp tr0 [h0 h1]. 
apply hp. split => //. have := hpq _ h1. done. Qed. 

Lemma Len_monotone2: forall p n m, n <= m -> Len p n ->> Len p m.
Proof. move => p n m hnm st0 h0 tr0 [h1 h2].
have : len n tr0. apply h0 => //. clear h0 h1 h2. move => h0.
have := len_monotone hnm h0. done.
Qed.

Definition after (p: assertT) (q: assertT) := 
let: exist p hp := p in let: exist q hq := q in
forall tr, p tr -> exists tr0: trace, follows q tr tr0. 

(* Lemma 4.2: ◃ is monotone on the left argument . *)
Lemma after_monotone_L: forall p0 p1 q, p0 =>> p1 ->
after p1 q -> after p0 q.
Proof. move => [p0 hp0] [p1 hp1] [q hq]. move => h0 h1 tr1 h2.
have := h0 _ h2. simpl. clear h2. move => h2. have := h1 _ h2.
done. Qed.

Definition invert_fin_delay (tr : trace) (st st0 : state)
 (h : fin (Tcons st tr) st0) : fin tr st0.
Proof.
by depelim h.
Defined.

Fixpoint cut (tr0 : trace) (st0 : state) (h : fin tr0 st0) (tr1 : trace) { struct h }: trace :=
match tr0 as tr0' return (fin tr0' st0 -> trace) with
| Tnil _ => fun _ => tr1
| Tcons st tr => fun h' =>
  match tr1 with
  | Tnil _ => tr1
  | Tcons st1 tr1' => cut (invert_fin_delay h') tr1'
  end
end h.

Lemma tsemax2_complete_aux: forall (p q : trace -> Prop) tr0 st0 (h:fin tr0 st0), 
 forall tr1 tr2, hd tr1 = st0 -> follows q (tr0 +++ tr1) tr2 ->   
 p tr1 -> append p q (cut h tr2).
Proof.
move => p q.
refine (fix IH tr st h {struct h} := _).
case: tr st h.
- depelim h => tr0 tr1 h0 h2 h3.
  rewrite trace_append_nil in h2. simpl.
  exists tr0. split => //.
- depelim h => tr0 tr1 h1 h2 h3.
  rewrite trace_append_cons in h2. foo h2.
  simpl. by apply: (IH _ _ _ _ _ _ H2).
Qed.

Lemma tsemax2_complete_aux2: forall p tr0 st0 (h: fin tr0 st0),
 forall tr1 tr2, follows p (tr0 +++ tr1) tr2 -> 
 hd (cut h tr2) = hd tr1.
Proof.
move => p.
refine (fix IH tr st h {struct h} := _).
case: tr st h.
- depelim h => tr0 tr1.
  rewrite trace_append_nil. simpl. move => h0.
  have := follows_hd h0. done.
- depelim h => tr0 tr1.
  rewrite trace_append_cons. simpl. move => h1. foo h1 . 
  by apply: (IH  _ _ _ _ _ H2).
Qed.

Lemma tsemax2_complete_aux3: forall u0 w u p st0, u0 ->> u ->
 Last (<< u0 andS w >> *** Iter (p *** << u >>)) st0 -> u st0.
Proof.
move => u0 w u p st0 a0 h2.
have : Last ((<< u >>) *** Iter (ttT *** (<< u >>))) st0. 
* have := Last_monotone _ h2. apply. apply Append_monotone. 
  move => tr0 [st1 [h4 h5]]. simpl. foo h5. foo H1. destruct h4 as [h4 h5]. 
  exists st1. split => //. have := a0 _ h4. done. apply bisim_reflexive.
  apply Iter_monotone. apply Append_monotone_L => //. move => h4. clear h2.
have := Last_chop_sglt (Last_monotone (@iter_last_dup _) h4). done.
Qed.

(* Lemma 4.3: (P ** Q) ◃ R ⊧ (<Last P> ** Q) ◃ R *)
Lemma after_Append: forall p q r, after (p *** q) r -> after ([|Last p|] *** q) r.   
Proof.
move => [p hp] [q hq] [r hr]. simpl. move => h0 tr0 [tr1 [h1 h2]].
destruct h1 as [st0 [h1 h3]]. foo h3. foo h2. destruct h1 as [tr1 [h1 h2]].
have h3: (p *+* q) (tr1 +++ tr0).
* exists tr1; split => //. clear h1. move: tr0 tr1 H1 h2. cofix hcoind. 
  move => tr0. case. 
  - move => st0 h2 h1. foo h1. rewrite trace_append_nil. apply follows_nil => //.
  - move => st0 tr1 h2 h3. foo h3. rewrite [Tcons st0 tr1 +++ _]trace_destr. 
    simpl. apply follows_delay. have := hcoind _ _ h2 H2. done. 
have := h0 _ h3 => {h0 h3}. move => [tr2 h0]. clear H1 h1. 
move h1 : (hd tr0) => st0. rewrite h1 in h2. move: tr1 st0 h2 tr0 h1 tr2 h0.
induction 1. 
- move => tr0 h0 tr1 h1. rewrite trace_append_nil in h1. exists tr1. done. 
- move => tr0 h0 tr1 h1. rewrite trace_append_cons in h1. foo h1. 
  have := IHh2 _ _ _ H2. apply => //. 
Qed.

(* Lemma 4.4 *)
Lemma after_Last: forall p r, after ([|Last p|]) r -> after p r.
Proof.
move => [p hp] [q hq]. simpl. move => h0 tr0 h1.
apply: fin_hd_follows.
exact: (singleton_last_fin h0).
Qed.

(* Proposition 4.4: projecting the total-correctness Hoare logic into
   the trace-based Hoare logic. *)
Lemma tsemax2_complete: forall u s p, semax u s p ->
forall m w r, after ([|w|] *** p) r -> tsemax2 (u andS w andS (Len (p *** r) m)) s 
(Last ([|w|] *** p) andS (Len r m)). 
Proof. induction 1.
- move => m w r hafter. have h0 := tsemax2_skip (u andS w andS Len (([|u|]) *** r) m).
  have := tsemax2_conseq_R _ h0 => {h0}. apply. move => st h0.
  move: h0 => [h0 [h1 h2]]. split. exists (Tnil st). split. exists (Tnil st).
  split. exists st. split => //. apply bisim_reflexive. apply follows_nil => //.
  exists st. split => //. apply bisim_reflexive. apply fin_nil.
  move => tr [h3 h4]. apply h2. split => //. destruct r as [r hr]. simpl. 
  simpl in h4. exists (Tnil st). split. exists st. split => //. apply bisim_reflexive. 
  apply follows_nil => //. 
- move => m w r hafter. have h0 := tsemax2_assign (u andS w andS Len (Updt u x a *** r) m)
  x a. have := tsemax2_conseq_R _ h0 => {h0}. apply. move => st [st1 [h0 h1]].
  move: h0 => [h0 [h2 h3]]. split. exists (Tcons st1 (Tnil st)). split. 
  exists (Tnil st1). split. exists st1. split => //. apply bisim_reflexive. 
  apply follows_nil => //. exists st1. split => //. rewrite h1. apply bisim_reflexive. 
  apply fin_delay. apply fin_nil. move => tr0 [h4 h5].
  have: len m (Tcons st1 tr0). 
  * apply h3 => {h3}. split => //. destruct r as [r hr]. simpl. exists (Tcons st1 (Tnil st)). 
    split. exists st1. split => //. rewrite h1. apply bisim_reflexive.
    apply follows_delay. apply follows_nil => //. 
  clear h0 h1 h2 h3 h4 h5. move => h0. foo h0.      
  have := len_S H1. done. 
- move => m w r hafter. 
  have hr: after ([|w|] *** p1 *** [|v|]) (p2 *** r). 
  * have h: after ([|w|] *** p1 *** [|v|]) p2. 
    * have := after_monotone_L (@Append_assoc_R _ _ _). apply. 
      apply after_Last.
      have := after_monotone_L (Singleton_monotone (@Last_chop_sglt _ _)).
      apply. destruct p2 as [p2 hp2]. simpl. move => tr0 [st0 [h0 h1]]. 
      foo h1. have := semax_total H0 h0 => {h0}. move =>[tr0 [h0 h1]].
      simpl in h1. exists tr0. apply follows_nil => //. 
    destruct p1 as [p1 hp1]. destruct p2 as [p2 hp2]. destruct r as [r hr].
    simpl. simpl in hafter. simpl in h. move => tr0 h0. 
    have := h _ h0 => {h}. move => [tr1 h1]. 
    have : (singleton w *+* p1 *+* p2) tr1. 
    * apply append_assoc_L. exists tr0. split => //. 
      have := append_assoc_R h0 => {h0}. move => h0.              
      have := append_singleton _ h0. apply. apply append_setoid => //.
    move => h2. have := hafter _ h2 => {hafter}. move => [tr2 h3]. 
    exists tr2. have := follows_follows h1 h3. apply.    
  have hs1 := IHsemax1 m w (p2 *** r) hr => {IHsemax1 hr}. 
  have: (Len ((p1 *** p2) *** r) m) ->> Len ((p1 *** [|v|]) *** p2 *** r) m.
  * apply Len_monotone. have := impT_conseq_L (@Append_monotone_L _ p1 _ _). apply.
    apply Append_Singleton. by apply Append_assoc_R. 
  move => h0. have : tsemax2 (u andS w andS Len ((p1 *** p2) *** r) m)
  s1 (Last (([|w|]) *** p1 *** ([|v|])) andS Len (p2 *** r) m).
  have := tsemax2_conseq_L _ hs1 => {hs1}. apply. move => st0 [h1 [h2 h3]].
  split => //. split => //. have := h0 _ h3. done. clear h0 hs1. move => hs1.
  have hr: after ([|Last ([|w|] *** p1 *** [|v|])|] *** p2) r. 
  * destruct p1 as [p1 hp1]. destruct p2 as [p2 hp2]. destruct r as [r hr]. 
    simpl. simpl in hafter. clear hs1. move => tr0 h0. destruct h0 as [tr1 [h0 h1]]. 
    destruct h0 as [st0 [h0 h2]]. foo h2. foo h1. destruct h0 as [tr1 [h0 h1]].
    have : (singleton w *+* p1 *+* p2) (tr1 +++ tr0). 
    * apply append_assoc_L. have := append_assoc_R h0 => {h0}. move => h0.
      have := append_fin _ H3. apply => //. have := append_singleton _ h0. apply => //. 
      apply append_setoid => //. clear h0 H3. move => h0. 
      have := hafter _ h0 => {hafter h0}. move => [tr2 h0].
      move h2: (hd tr0) => st0. rewrite h2 in h1. 
      exists (cut h1 tr2). move: tr1 st0 h1 tr0 h2 tr2 h0.
      refine (fix IH tr st h {struct h} := _).
      case: tr st h.
      - depelim h; move => tr0 h0 tr2 h1. rewrite trace_append_nil in h1. simpl. done. 
      - depelim h; move => tr0 h2 tr2 h1. simpl. rewrite trace_append_cons in h1. foo h1. 
        have := IH  _ _ _ _ _ _ H4. apply => //.
  have hs2 := IHsemax2 m (Last (([|w|]) *** p1 *** ([|v|]))) r hr => {IHsemax2 hr}. 
  have: (Last (([|w|]) *** p1 *** ([|v|]))) ->> v. 
  * move => st0 h0. have := Last_monotone (@Append_assoc_R _ _ _) h0.
    clear h0. move => h0. have := Last_chop_sglt h0. done. 
  move => h0. 
  have: tsemax2 (Last (([|w|]) *** p1 *** ([|v|]))andS Len (p2 *** r) m) s2
  (Last (([|Last (([|w|]) *** p1 *** ([|v|]))|]) *** p2) andS Len r m). 
  * have := tsemax2_conseq_L _ hs2 => {hs2}. apply. move => st0 [h1 h2].
    split => //. have := h0 _ h1. done. 
  clear hs2. move => hs2. 
  have := tsemax2_seq hs1 hs2 => {hs1 hs2}. clear h0. move => hs. 
  have := tsemax2_conseq_R _ hs. apply. clear hs. move => st0 [h0 h1].
  split => //. clear h1. have := Last_Last h0 => {h0}. move => h0. 
  have := Last_monotone _ h0. apply. clear h0. 
  have := impT_conseq_R (@Append_assoc_L _ _ _). apply. apply Append_monotone_L. 
  apply Append_monotone_R. apply Append_Singleton. 
- move => m w r hafter. 
  * have haftertt: after ([|w andS u|] *** p) r. 
    * destruct p as [p hp]. destruct r as [r hr]. simpl. clear IHsemax1 IHsemax2.
      simpl in hafter. move => tr0 [tr1 [h0 h1]]. destruct h0 as [st0 [h0 h2]].
      foo h2. foo h1. destruct h0 as [h0 h1]. 
      have: (singleton w *+* dup u *+* p) (Tcons (hd tr0) tr0). 
      * exists (Tnil (hd tr0)). split. exists (hd tr0). split => //. apply bisim_reflexive.  
        apply follows_nil => //. exists (Tcons (hd tr0) (Tnil (hd tr0))). 
        split. exists (hd tr0). split => //. apply bisim_reflexive. 
        apply follows_delay. by apply follows_nil. 
      move => h2. have := hafter _ h2. move => [tr1 h3]. clear h0 h1 h2. foo h3. 
      exists tr'. done.   
    apply tsemax2_ifthenelse. 
    have := IHsemax1 m _ _ haftertt => {IHsemax1 haftertt}. move => hsemax.
    have := tsemax2_conseq _ _ hsemax. apply => {hsemax}.
    * move => st0 [[h0 [h1 h3]] h2]. split => //. split => //. 
      have := Len_monotone (@Append_assoc_R _ _ _) h3. clear h3. move => h3. 
      destruct p as [p hp]. destruct r as [r hr]. clear h1 h2. move => tr0 [h1 h2].
      simpl in h2. have : ((dup u) *+* (p *+* r)) (Tcons (hd tr0) tr0).
      exists (Tcons (hd tr0) (Tnil (hd tr0))). split. exists (hd tr0). split.   
      rewrite h1. done. apply bisim_reflexive. apply follows_delay.
      by apply follows_nil. move => h4. 
      have: len m (Tcons (hd tr0) tr0). apply h3. simpl. clear h3. by split. 
      move => h5. foo h5. have := len_S H3. done. 
     * move => st0 [h0 h1]. split => //. clear h1. destruct p as [p hp]. 
       destruct h0 as [tr0 [h0 h1]]. exists (Tcons (hd tr0) tr0).
       destruct h0 as [tr1 [h0 h2]]. destruct h0 as [st1 [h0 h3]].
       foo h3. foo h2. destruct h0 as [h0 h2]. split. exists (Tnil (hd tr0)).
       split. exists (hd tr0). split => //. apply bisim_reflexive. apply follows_nil => //. 
       exists (Tcons (hd tr0) (Tnil (hd tr0))). split. exists (hd tr0). split => //.
       apply bisim_reflexive. apply follows_delay. by apply follows_nil. 
       by apply fin_delay. 
    have := IHsemax2 m _ _ haftertt => {IHsemax2 haftertt}. move => hsemax.
    have := tsemax2_conseq _ _ hsemax. apply => {hsemax}.
    * move => st0 [[h0 [h1 h3]] h2]. split => //. split => //. 
      have := Len_monotone (@Append_assoc_R _ _ _) h3. clear h3. move => h3. 
      destruct p as [p hp]. destruct r as [r hr]. clear h1 h2. move => tr0 [h1 h2].
      simpl in h2. have : ((dup u) *+* (p *+* r)) (Tcons (hd tr0) tr0).
      exists (Tcons (hd tr0) (Tnil (hd tr0))). split. exists (hd tr0). split.   
      rewrite h1. done. apply bisim_reflexive. apply follows_delay.
      by apply follows_nil. move => h4. 
      have: len m (Tcons (hd tr0) tr0). apply h3. simpl. clear h3. by split. 
      move => h5. foo h5. have := len_S H3. done. 
     * move => st0 [h0 h1]. split => //. clear h1. destruct p as [p hp]. 
       destruct h0 as [tr0 [h0 h1]]. exists (Tcons (hd tr0) tr0).
       destruct h0 as [tr1 [h0 h2]]. destruct h0 as [st1 [h0 h3]].
       foo h3. foo h2. destruct h0 as [h0 h2]. split. exists (Tnil (hd tr0)).
       split. exists (hd tr0). split => //. apply bisim_reflexive. apply follows_nil => //. 
       exists (Tcons (hd tr0) (Tnil (hd tr0))). split. exists (hd tr0). split => //.
       apply bisim_reflexive. apply follows_delay. by apply follows_nil. 
       by apply fin_delay.     
- move => m w r hafter. set J0 := Last (<< u0 andS w >> *** (Iter (p *** << u >>))). 
  set J1 := (Iter (p *** << u >>) *** [|eval_false a|] *** r). 
  set Q := <<u>> *** (Iter (p *** <<u>>)) *** [|eval_false a|] *** r.

  have hs: forall n, tsemax2 (eval_true a andS J0 andS Len J1 n) s
  (exS (fun k => (fun st => k < n) andS J0 andS Len J1 k)).
 
  have hn0: (eval_true a andS J0 andS Len J1 0) ->> ffS.
  * move => st0. rewrite /J0. rewrite /J1. move => [h1 [h2 h3]].
  have hfalse: forall tr0, satisfy (Iter (p *** <<u>>) *** [|eval_false a|] *** r) tr0 
  -> hd tr0 = st0 -> False.
  * destruct p as [p hp]. destruct r as [r hr]. simpl. move => tr0 h4 h5. 
     have : len 0 tr0. apply h3. clear h3. split => //. clear h3.
     move => h3. destruct h4 as [tr1 [h4 h6]]. foo h4. 
     - foo h6. destruct H3 as [tr1 [h0 h4]]. destruct h0 as [st1 [h0 h5]]. 
       foo h5. foo h4. rewrite /eval_true in h1. rewrite /eval_false in h0. 
       rewrite h1 in h0. by foo h0.
     - destruct H1 as [tr2 [h0 h4]]. destruct tr2.
       - clear h0. foo h4. destruct H4 as [st0 [_ h0]]. foo h0. foo H4. 
         foo H2. foo h6. foo h3. 
       - foo h4. foo H2. foo h6. foo h3.  

    have hsemax := semax_while (@assertS_imp_refl _) H0 => {H0}.
    have h0 := semax_total hsemax => {hsemax}.
    have hu : u st0. have := tsemax2_complete_aux3 H h2. done. 
    have := h0 _ hu => {h0}. move => [tr0 [h0 h4]].

    have: after ([|w|] *** <<u0>> *** Iter (p *** <<u>>) *** Iter (p *** <<u>>)
    *** [|eval_false a|]) r.
   * have := after_monotone_L _ hafter => {hafter}. apply. 
     apply Append_monotone_R. apply Append_monotone_R. have := assertT_imp_trans (@Append_assoc_R _ _ _). 
     apply. apply Append_monotone_L. apply Iter_Iter. 
    clear hafter. move => hafter.      
 
    set P := ([|w|] *** << u0 >> *** Iter (p *** <<u>>) *** Iter (p *** <<u>>) *** [|eval_false a|]).      
    destruct p as [p hp]. 
    destruct r as [r hr]. simpl in h4. simpl in h2. 
    destruct h2 as [tr1 [h2 h5]]. destruct h2 as [tr2 [h2 h6]]. 
    destruct h2 as [st1 [h2 h7]]. foo h7. foo H2. destruct h2 as [h2 h0]. 
    foo h6. foo h5. foo H3. destruct h4 as [tr1 [h4 h5]]. destruct h4 as [st0 [h4 h6]]. 
    foo h6. foo H3. foo h5. simpl in H4. simpl in h0. simpl in h2.
    simpl. simpl in h1. foo H5. 
    have : append (iter (append p (dup u))) 
    (append (iter (append p (dup u))) (singleton (eval_false a))) (tr' +++ tr'0).
    * exists tr'. split => //. clear hu hfalse H2 h2 h0 h4 h1 h3. move: tr' tr'0 H4 H3.
      cofix hcoind. move => tr0 tr1 h0. foo h0. move => h0. apply follows_nil => //.
      by rewrite trace_append_nil. move => h0. rewrite [Tcons st tr +++ tr1]trace_destr; simpl.
      apply follows_delay. have := hcoind _ _ H0 h0. done.
    move => h5.
    have : satisfy P (Tcons (hd tr') (tr' +++ tr'0)).
    * rewrite /P. simpl. exists (Tnil (hd tr')). split. exists (hd tr'). 
      split => //. apply bisim_reflexive. apply follows_nil => //. 

      exists (Tcons (hd tr') (Tnil (hd tr'))). split. 
      exists (hd tr'). split => //. apply bisim_reflexive. apply follows_delay. 
      apply follows_nil => //. have := hd_append H4 (refl_equal _). by apply. move => hP. 
    simpl in hfalse. rewrite -trace_append_cons in hP. 
    have hfinite: fin (Tcons (hd tr') tr') (hd tr'0). by apply fin_delay. 
    clear H4. clear h3. 
    have := hafter _ hP => {hP hafter}. move => [tr0 h3].  
    move heq: (Tcons (hd tr') tr') => tr1. rewrite heq in h3 hfinite. 
    have := tsemax2_complete_aux hfinite (refl_equal _) h3 H3 => {H3}.
    move => h6. have := append_assoc_L h6. clear h6. move => h6. 
    have := hfalse _ h6. clear heq. clear h6.
    move => h6. have := tsemax2_complete_aux2 hfinite h3. move => h7.
    have := h6 h7 => {h6 h7}. move => h6. absurd False => //.
 
  (* end of hn0 *)

 
  have hpre: forall n, (eval_true a andS J0 andS Len J1 n) ->>
  (eval_true a andS u andS J0 andS Len (p *** [|u|] *** Q) n). 
  * move => n st0 [h0 [h1 h2]]. split => //. split => //. 
  rewrite /J0 in h1. have h3:((<< u0 andS w >>) *** Iter (p *** (<< u >>)))      
  =>> <<u>> *** Iter (ttT *** <<u>>). apply Append_monotone. 
  apply Dup_monotone. move => st1 [h3 h4]. have := H _ h3. done. 
  apply Iter_monotone. apply Append_monotone_L => //.
  have := assertT_imp_trans h3 (@iter_last_dup _) => {h3}. move => h3.   
  have := Last_monotone h3 => {h3}. move => h3. have := h3 _ h1 => {h3 h1}.
  apply Last_chop_sglt. split => //. rewrite /J1 in h2. rewrite /Q. 
  have := Len_monotone _ h2. apply. 
  have := impT_conseq_L (@Append_assoc_R _ _ _). apply.
  have := impT_conseq_L (@Append_assoc_R _ _ _). apply. 
  have := impT_conseq_L (Append_monotone_L (@Append_assoc_L _ _ _)). apply. 
  have h3: ([|u|] *** <<u>>) =>> <<u>>.
  * move => st1. simpl. move => [tr0 [[st2 [h3 h5]] h4]]. foo h5.
    foo h4. done. 
  have := impT_conseq_L (Append_monotone_L (Append_monotone_R h3)). apply. 
  have := impT_conseq_L (@Append_assoc_R _ _ _). apply.
  have := Append_monotone_L. apply. apply Iter_fold_L. 

  (* end of hpre *)

  have hpost: forall n, n > 0 -> (Last ([|J0|] *** p *** [|u|]) andS Len Q n) ->>
  (exS (fun k => (fun st => k < n) andS J0 andS Len J1 k)).
  * clear hn0 hpre. move => n hn st0 h0. rewrite /J0 in h0. 
    have: (Last (<<u0 andS w>> *** Iter (p *** <<u>>)) andS Len Q n) st0.
    move: h0 => [h0 h1]. split => //. clear h1. have := Last_Last h0. 
    clear h0. move => h0. 
    have := Last_monotone (@Append_assoc_R _ _ _) h0. clear h0. move => h0. 
    have := Last_dup h0 => {h0}. move => h0. 
    have := Last_monotone (@Append_assoc_L _ _ _) h0 => {h0}. move => h0. 
    have := Last_monotone (@Append_assoc_L _ _ _) h0 => {h0}.
    apply Last_monotone. apply Append_monotone_R.
    apply Iter_unfold_1.
    clear h0. rewrite /Q. move => h0. 
    have : (Last (<< u0 andS w >> *** Iter (p *** << u >>))
      andS Len (Iter (p *** << u >>) *** [|eval_false a|] *** r) 
    (n-1)) st0.
    * destruct h0 as [h0 h1]. split => //. destruct p as [p hp]. 
      destruct r as [r hr]. move => tr0 [h2 h3]. simpl in h3. 
      have: len n (Tcons (hd tr0) tr0).   
      apply h1. simpl. split => //. have hu := tsemax2_complete_aux3 H h0. 
      exists (Tcons (hd tr0) (Tnil (hd tr0))). split. exists (hd tr0). 
      split => //. rewrite h2. done. apply bisim_reflexive. apply follows_delay. 
      apply follows_nil => //. 
      move => h4. foo h4. rewrite (_: S n0 - 1 = n0); last by lia. done. 
     clear h0. move => h0. 
    fold J0 in h0. fold J1 in h0. exists (n-1). destruct h0 as [h0 h1]. 
    split => //. lia.   

   (* end of hpost *)
   
  case. 
  * have := tsemax2_conseq_L hn0 => {hn0}. apply. apply tsemax2_false. 
  * move => n. have hn : (S n) > 0; first by lia.
    have := tsemax2_conseq (hpre _) (hpost _ hn) => {hpre hpost hn hn0}. apply.
    have hpre : (eval_true a andS u andS J0 andS Len (p *** [|u|] *** Q) (S n)) 
    ->> (eval_true a andS u andS J0 andS (Len ([|J0|] *** p *** [|u|] *** Q) (S n))).
    * move => st0 [h0 [h1 [h2 h3]]]. split => //. split => //. split => //. 
      move => tr0 [h4 h5]. apply h3. split => //. have := Singleton_Append _.
      apply. apply h5.  
    have := tsemax2_conseq_L hpre => {hpre}. apply. 
    have := tsemax2_conseq _ _ (IHsemax (S n) J0 Q _) => {IHsemax}. apply => //.  
    move => st0 [h0 [h1 [h2 h3]]]. split => //. split => //. move => tr0 [h4 h5].
    apply h3. split => //. have := (@Append_assoc_L _ _ _ _ h5) => {h5}.
    move => h5. destruct p as [p hp]. destruct r as [r hr]. 
    simpl. simpl in h5. exists (Tnil (hd tr0)). split. exists st0. 
    split => //. rewrite h4. apply bisim_reflexive. apply follows_nil => //. 

(* prove after ([J0] *** p *** [u]) Q *)
    rewrite /J0. apply after_Append. 
    have := after_monotone_L (@Append_assoc_L _ _ _) hafter => {hafter}.
    move => hafter. 
    have h0: <<u0 andS w>> =>> [|w|] *** <<u0>>. 
    * move => tr0. simpl. move => [st0 [h0 h1]]. foo h1. foo H3. destruct h0 as [h0 h1]. 
      exists (Tnil st0). split. exists st0. split => //. apply bisim_reflexive. 
      apply follows_nil => //. exists st0. split => //. apply bisim_reflexive. 
      have := after_monotone_L (Append_monotone_L h0) hafter => {hafter h0}. move => hafter.

    have h0: after (<< u0 andS w >> *** Iter (p *** << u >>) *** p *** [|u|])
    (<< u >> *** Iter (p *** << u >>) *** [|eval_false a|]).
    * have := after_monotone_L (@Append_assoc_R _ _ _). apply.
      have := after_monotone_L (@Append_assoc_R _ _ _). apply. 
      apply after_Last.
      have := after_monotone_L (Singleton_monotone (@Last_chop_sglt _ _)).
      apply. clear hafter.     
      have hsemax := semax_while (@assertS_imp_refl _) H0 => {H0}.
      have h0 := semax_total hsemax => {hsemax}.
      destruct p as [p hp]. simpl. move => tr0 [st0 [h1 h2]]. foo h2. 
      have := h0 _ h1 => {h0 h1}. move => [tr0 [h0 h1]]. simpl in h1. 
      exists tr0. apply follows_nil => //.
  
  (** end of h0 **)

   destruct p as [p hp]. rewrite /Q. destruct r as [r hr]. simpl. 
   simpl in hafter. simpl in h0. move => tr0 h1.
   have := append_assoc_L h1 => {h1}. move => h1.   
   have := h0 _ h1 => {h0}. move => [tr1 h0].
   have :((dup (u0 andS w) *+* iter (p *+* dup u) *+* p *+* singleton u) 
   *+* (dup u *+* iter (p *+* dup u) *+* singleton (eval_false a))) tr1.
   exists tr0. split => //. clear h1. move => h3.
   have: (dup (u0 andS w) *+* iter (p *+* dup u) *+* singleton (eval_false a)) tr1. 
   * clear h0. have := append_assoc_L h3. move => h0. 
     have := append_monotone_R _ h0. apply. clear h0. move => tr2 h0.
     have := append_assoc_R h0 => {h0}. move => h0.    
     have := append_assoc_R h0 => {h0}. move => h0.    
     have := append_cont_L _ h0 => {h0}. apply. clear tr2. 
     move => tr2 h0. have := append_assoc_L h0 => {h0}. move => h0.   
     have := append_assoc_L h0 => {h0}. move => h0.
     have : forall tr, ((p *+* singleton u) *+* dup u *+* iter (p *+* dup u)) tr ->
     iter (p *+* dup u) tr.
     * clear tr0 h0. move => tr0 h0. have := append_assoc_R h0 => {h0}.
       move => [tr3 [h0 h1]]. have := iter_loop _ h1. apply. clear h1. 
       have := append_cont_L _ h0. apply. apply append_singleton => //.
     move => h1. have := append_monotone_R h1 h0 => {h0 h1}. move => h0.      
     have := iter_iter h0. done.
   clear h3. move => h1. have := hafter _ h1 => {h1}. move => [tr2 h1]. 
   exists tr2. have := follows_monotone (@append_assoc_L _ _ _). apply. 
   have := follows_monotone (@append_assoc_L _ _ _). apply. 
   have := follows_follows h0 h1 => {h0 h1}. clear tr1. move => h0. 
   have := follows_monotone (append_cont_L (@append_assoc_R _ _ _)) h0 => {h0}. done. 

  have := (@tsemax2_while _ _ m _ hs). clear hs. move => hs. 
  have hpre: (u0 andS w andS Len ((<<u0>> *** Iter (p *** <<u>>) *** 
  [| eval_false a|]) *** r) m) ->> J0 andS Len J1 m.
  * have h0: (u0 andS w) ->> J0.
     * move => st0 [h0 h1]. rewrite /J0. destruct p as [p hp]. simpl. 
        exists (Tcons st0 (Tnil st0)). split. exists (Tcons st0 (Tnil st0)). split. 
        exists st0. split => //. apply bisim_reflexive. apply follows_delay. 
        apply follows_nil => //. apply iter_stop. apply fin_delay. apply fin_nil.
     have h1: (u0 andS Len ((<<u0>> *** Iter (p *** <<u>>) *** [|eval_false a|]) *** r) m) ->>
     Len J1 m.
     * destruct p as [p hp]. destruct r as [r hr]. move => st0. move => [h1 h2].
        rewrite /J1. move => tr0 [h4 h3]. simpl in h3. 
        have h5: len m (Tcons (hd tr0) tr0). 
        * apply h2. simpl. split => //. destruct h3 as [tr1 [h3 h5]].
           have h6 := follows_hd h5. exists (Tcons (hd tr1) tr1). split.
           exists (Tcons (hd tr1) (Tnil (hd tr1))).  split. exists (hd tr1). split => //.
           rewrite h6. rewrite h4. done. apply bisim_reflexive. apply follows_delay. 
           apply follows_nil => //. exists tr1. split => //. 
           clear h0 h1 h2 h4 h3 h6. move: tr1 tr0 h5. cofix hcoind.
           move => tr0 tr1 h0. foo h0. destruct H2 as [tr0 [h0 h1]]. 
           destruct h0 as [st1 [h0 h2]]. foo h2. foo h1. apply follows_nil => //. 
           exists (hd tr1). split => //. apply bisim_reflexive. apply follows_delay.  
           have := hcoind _ _ H1. done. 
           rewrite h6. apply follows_delay. clear h0 h1 h2 h3 h4 h6. move: tr1 tr0 h5. 
           cofix hcoind. move => tr0 tr1 h0. foo h0. destruct H2 as [tr0 [h0 h1]]. 
           destruct h0 as [st1 [h0 h2]]. foo h2. foo h1. apply follows_nil => //.
           apply follows_delay. have := hcoind _ _ H1. done. 
        foo h5. have := len_S H3. done. 
        move => st0 [h2 [h3 h4]]. split. apply h0. split => //. apply h1. 
        split => //. 
  have := tsemax2_conseq_L hpre. apply. clear hpre. 
  have hpost : (exS (fun k => (fun _ => k <= m) andS
  (J0 andS Len J1 k) andS eval_false a)) ->> J0 andS Len J1 m andS eval_false a.
  * move => st0 [x h0]. destruct h0 as [h0 [[h1 h2] h3]].
    split => //. split => //. have := Len_monotone2 h0 h2. done. 
  have := tsemax2_conseq_R hpost hs. clear hpost hs. move => hs. 
  have hpost: (J0 andS Len J1 m andS eval_false a) ->>
  Last ([|w|] *** <<u0>> *** Iter (p *** <<u>>) *** [|eval_false a|])
  andS Len r m.
  * move => st0. rewrite /J0. rewrite /J1. move => [h0 [h1 h2]]. split. 
    have h3 : (Last (<< u0 andS w >> *** Iter (p *** << u >>)) andS eval_false a) st0.
    * by split => //.
    have := Last_andS h3 => {h3}. apply Last_monotone.
    have := assertT_imp_trans (@Append_assoc_L _ _ _). apply.
    have := assertT_imp_trans _ (@Append_assoc_L _ _ _). apply.
    apply Append_monotone_L. clear h0 h1 h2. move => tr0 [st1 [h0 h1]].
    foo h1. foo H3. destruct h0 as [h0 h1]. simpl. exists (Tnil st1). 
    split. exists st1. split => //. apply bisim_reflexive. apply follows_nil => //. 
    exists st1. split => //. apply bisim_reflexive. clear h0. 
    move => tr0 [h0 h3]. apply h1. split => //. rewrite -h0 in h2. clear h1 h0. 
    destruct r as [r hr]. destruct p as [p hp]. simpl. simpl in h3.
    exists (Tnil (hd tr0)). split. apply iter_stop. apply follows_nil => //. 
    exists (Tnil (hd tr0)). split. exists (hd (tr0)). split => //.
    apply bisim_reflexive. apply follows_nil => //.
  have := tsemax2_conseq_R hpost hs => {hs hpost}. done.     

- move => m w r hafter. have h: after ([|w|] *** p2) r. 
  have := after_monotone_L _ hafter. apply. by apply Append_monotone.
  have := IHsemax m _ _ h => {hafter h IHsemax}. move => htsemax. 
  have := tsemax2_conseq _ _ htsemax => {htsemax}. apply. 
  * move => st0 [h0 [h1 h2]]. split => //. have := H _ h0. done. 
    split => //. have := Len_monotone _ h2. apply. by apply Append_monotone_L. 
  * move => st0 [h0 h1]. split => //. have := Last_monotone _ h0. apply. 
    by apply Append_monotone_R. 

- move => m w r hafter. 
  have hsemax: forall x, tsemax2 (u x andS w andS Len (p x *** r) m) s
      (Last (([|w|]) *** p x) andS Len r m).
  * move => x. apply H0. move hp: (p x) => q. destruct q as [q hq]. 
    destruct r as [r hr]. move => tr0 h0. destruct h0 as [tr1 [h0 h1]]. 
    have: satisfy ([|w|] *** exT p) tr0. simpl. exists tr1. split => //. clear h0. 
    move: tr1 tr0 h1. cofix hcoind. move => tr0 tr1 h0. foo h0. apply follows_nil => //. 
    exists x. rewrite hp. simpl. done. apply follows_delay. have := hcoind _ _ H1. done.
    move => h2. have := hafter _ h2. done. 
  have := tsemax2_ex hsemax. clear hafter hsemax. move => hsemax.
  have := tsemax2_conseq _ _ hsemax => {hsemax}. apply. 
  * move => st0 [h0 [h1 h2]]. destruct h0 as [x h0]. exists x. split => //. 
    split => //. move => tr0 [h3 h4]. apply h2. split => //. 
    have := Append_monotone_L _ h4. apply. move => tr1. move hp: (p x) => q. 
    destruct q as [q hq]. simpl. move => h5. exists x. rewrite hp. by simpl.
  * move => st0 [x [h0 h1]]. split => //. clear h1. move hp: (p x) => q. 
    rewrite hp in h0. destruct q as [q hq]. destruct h0 as [tr0 [h1 h0]].
    simpl. exists tr0. split => //. clear h0. destruct h1 as [tr1 [h0 h1]]. 
    exists tr1. split => //. destruct h0 as [st1 [h0 h2]]. foo h2. foo h1. 
    apply follows_nil => //. exists x. by rewrite hp.                
Qed.

(* Corollary 4.3 *)
Lemma tsemax2_complete_main: forall u s p, semax u s p ->
 tsemax2 (u andS (exS (fun m => Len p m))) s (Last p).
Proof.
move => U s P hsemax. 
have h0: (U andS exS (fun m => Len P m)) ->> (exS (fun m => U andS Len P m)). 
- move => st0 [h0 [n h1]]. exists n. by split.
have h1: (exS (fun (m:nat) => Last P)) ->> (Last P).
- move => st0 [n hP]. done. 
have := tsemax2_conseq h0 h1 => {h0 h1}. apply. 
apply tsemax2_ex. move => n. have := (@tsemax2_complete _ _ _ hsemax  n ttS ([| ttS |])). 
clear hsemax; move => hsemax. 
have : after (([|ttS|]) *** P) ([|ttS|]). 
- clear hsemax. destruct P as [P hP]. move => tr0 h0. exists tr0. apply follows_ttS. 
move => h0; have := hsemax h0 => {h0 hsemax}; move => hsemax. 
have := (tsemax2_conseq _ _ hsemax) => {hsemax}. apply. 
- move => st0 h0. destruct h0 as [h0 h1]. try (repeat split; auto).
  move => tr0. clear h0. move => [h0 h2]. have := h1 tr0 => {h1}. apply; split => //. 
  destruct P as [P hP]. simpl in h2. simpl. have := (append_singleton _ h2). 
  by apply. 
- destruct P as [P hP]. simpl. move => st0 [h0 _]. have := (last_cont _ h0).
  apply. move => tr0 [tr1 [h1 h2]]. destruct h1 as [st1 [_ h1]]. 
  inversion h1; subst; clear h1. inversion h2; subst; clear h2. done. 
Qed.

Inductive tsemax : assertS -> stmt -> assertS -> Prop :=

| tsemax_skip: forall u, tsemax u Sskip u 

| tsemax_assign: forall u x a, 
  tsemax u (Sassign x a) (udt u x a) 

| tsemax_seq: forall s1 s2 u1 u2 u3,
  tsemax u1 s1 u2->
  tsemax u2 s2 u3 ->
  tsemax u1 (Sseq s1 s2)  u3

| tsemax_ifthenelse: forall a s1 s2 u1 u2,
  tsemax (u1 andS eval_true a) s1 u2 ->
  tsemax (u1 andS eval_false a) s2 u2 ->
  tsemax u1 (Sifthenelse a s1 s2) u2

| tsemax_while:forall a s u (t: state -> nat),
  (forall n, tsemax (eval_true a andS u andS (fun st => t st = n)) s 
   (u andS (fun st => t st < n))) ->
  tsemax u (Swhile a s) (u andS eval_false a)

| tsemax_conseq: forall s u1 u2 v1 v2,
  u1 ->> u2 -> 
  v2 ->> v1 -> 
  tsemax u2 s v2 ->
  tsemax u1 s v1.

Lemma tsemax_conseq_L: forall s u1 u2 v,
 u1 ->> u2 -> tsemax u2 s v -> tsemax u1 s v.
Proof.
move => s u1 u2 v h0 h1.
exact: (tsemax_conseq h0 (@assertS_imp_refl _) h1).
Qed.

Lemma tsemax_conseq_R: forall s u v1 v2,
 v2 ->> v1 -> tsemax u s v2 -> tsemax u s v1.
Proof. 
move => s u v1 v2 h0 h1.
exact: (tsemax_conseq (@assertS_imp_refl _) h0 h1).
Qed.

(* Proposition 4.2: embedding the total-correctness Hoare logic into
   the trace-based Hoare logic. *)
Lemma tsemax_correct_semax: forall u s v, tsemax u s v ->
 forall u0, semax (u andS u0) s ([|u0|] *** Finite *** [|v|]).
Proof.
induction 1. 
- move => u0. have h0 := semax_skip (u andS u0). 
  have h1: [|u andS u0 |] =>> ([|u0|] *** Finite *** [|u|]).
  * clear h0. move => tr0 [st0 [h0 h1]]. foo h1. move: h0 => [h0 h1].  
    exists (Tnil st0). split. exists st0. split; [done | apply bisim_reflexive].
    apply follows_nil => //. exists (Tnil st0). split. 
    apply finite_nil. apply follows_nil => //. exists st0. 
    split; [done | apply bisim_reflexive].
  have := semax_conseq_R h1 h0. by apply.  
- move => u0.  have h0 := semax_assign (u andS u0) x a. 
  have h1: (Updt (u andS u0) x a) =>> ([|u0|] *** Finite *** [|udt u x a|]). 
  * clear h0. move => tr0 [st0 [h0 h1]]. foo h1. foo H1.
    move: h0 => [h0 h1]. exists (Tnil st0). split.
    have := mk_singleton_nil h1; apply. 
    apply follows_nil => //. exists (Tcons st0 (Tnil (update x (a st0) st0))). 
    split. apply finite_delay; apply finite_nil.
    apply follows_delay; apply follows_nil => //. exists (update x (a st0) st0). 
    split; last apply bisim_nil. exists st0. by split.   
  have := semax_conseq_R h1 h0. by apply. 
- move => u0.  
  have h0 := semax_conseq_R (@Append_assoc_R _ _ _) (IHtsemax1 u0) => {IHtsemax1}.
  have h: u2 ->> (u2 andS u2); first done. 
  have h1 := semax_seq h0 (semax_conseq_L h (IHtsemax2 u2)) => {h h0 IHtsemax2}.  
  have h0: ((([|u0|]) *** Finite) *** ([|u2|]) *** Finite *** ([|u3|]))
  =>> (([|u0|]) *** Finite *** ([|u3|])).
  * clear h1. move => tr0 h0. have h1 := Append_assoc_L h0 => {h0}.
    have := Append_monotone_R _ h1 => {h1}. apply. clear tr0. move => tr0 h0.
    have h1 := Append_assoc_R h0 => {h0}.
    have h0 := Append_assoc_R h1 => {h1}. 
    have := Append_monotone_L _ h0 => {h0}. apply. 
    have := assertT_imp_trans (Append_monotone_L (@Finite_singleton u2)). apply. 
    by apply Finite_idem_1. 
     have := semax_conseq_R h0 h1. by apply. 
- move => u0. 
  have h: ((u1 andS u0) andS eval_true a) ->> (u1 andS eval_true a) andS u0; 
  first (move => st0 [[h0 h1] h2]; split; [ split; done | done]).
  have h0: ((u1 andS u0) andS eval_false a) ->> (u1 andS eval_false a) andS u0; 
  first (move => st0 [[h0 h1] h2]; split; [ split; done | done]). 
  have := semax_conseq _ _ 
  (semax_ifthenelse (semax_conseq_L h (IHtsemax1 u0)) 
  (semax_conseq_L h0 (IHtsemax2 u0))) => {h h0 IHtsemax1 IHtsemax2}. apply. 
  done. move => tr0 [tr1 [h0 h1]]. move: h0 => [st0 [h0 h2]]. foo h2. 
  foo H3. foo h1. exists (Tnil st0). split. move: h0 => [_ h0]. 
  by have := mk_singleton_nil h0 => {h0}; apply. foo H4. clear h0. 
  move: H3 => [tr0 [h0 h1]]. move: h0 => [st0 [h0 h2]]. foo h2. foo h1. 
  clear h0. apply follows_nil => //. move: H3 => [tr0 [h0 h1]].
  exists (Tcons (hd tr') tr'). split. have h2 := follows_singleton h1. 
  have h3 := finite_setoid h0 h2 => {h0 h2}. 
  have := finite_delay _ h3. by apply.
  have h2 := follows_singleton h1. 
  have h3 := follows_setoid_L h1 h2 => {h1 h2}.
  have := follows_delay _ h3 => {h3}; by apply. 
- clear H. move => u0.  
  have h: forall n, 
 semax ((eval_true a andS u andS (fun st : state => t st = n)) andS (fun st => t st = n )) s
 (([|fun st => t st = n |]) *** Finite *** ([|u andS (fun st : state => t st < n)|])).
 * move => n. have := H0 n. by apply.
  have h0 := semax_ex h => {H0 h}. 
  have h1 : (u andS eval_true a) ->> (exS (fun n : nat => 
  (eval_true a andS u andS (fun st : state => t st = n)) andS (fun st => t st = n))).
  * clear h0. move => st0 [h0 h1]. exists (t st0). by split.  
  have h2 := semax_conseq_L h1 h0 => {h1 h0}.
  have h0:(exT (fun n : nat =>
           ([| fun st : state => t st = n |]) ***
           Finite *** ([|u andS (fun st : state => t st < n)|]))) =>>
  ((exT (fun n: nat =>
   [| (fun st: state => t st = n) |] *** Finite ***
   [| (fun st: state => t st < n) |])) *** [|u|]).
  * clear h2. move => tr0 [x h0]. move: h0 => [tr1 [h0 h1]].
    move: h0 => [st0 [h2 h0]]. foo h0. foo h1. move: H1 => [tr1 [h0 h1]]. 
    have h3 := follows_singleton h1. 
    have h4 := finite_setoid h0 h3 => {h0}. 
    have h0 := follows_setoid_L h1 h3 => {h3 h1}. exists tr0.
    have h5 := follows_singleton_andS_R h0. 
    have h6 := follows_singleton_andS_L h0 => {h0}.
    split; last done. exists (t (hd tr0)). exists (Tnil (hd tr0)). split. 
    exists (hd tr0). split; [done | apply bisim_reflexive]. apply follows_nil => //. 
    exists tr0. by split.  
  have h1 := semax_conseq_R h0 h2 => {h0 h2}.
  have h: (u andS u0) ->> u.  move => st [h0 h2]; done. 
  have h0 := semax_while h h1 => { h h1}.
  have h1: ((<< u andS u0 >>) ***
        Iter
          (exT
             (fun n : nat =>
              ([|fun st : state => t st = n|]) ***
              Finite *** ([|fun st : state => t st < n|])) *** (<< u >>)) ***
        ([|eval_false a|])) =>>
  (([|u0 |]) *** Finite *** ([|u andS eval_false a|])).
  * clear h0. move => tr0 [tr1 [h0 h1]]. move: h0 => [st0 [[h0 h] h2]]. 
    foo h2. foo H1. foo h1. foo H2. exists (Tnil (hd tr')). split. exists (hd tr'). 
    split; [done | apply bisim_reflexive]. apply follows_nil => //. 
    move: H1 => [tr0 [h1 h2]]. exists (Tcons (hd tr') tr'). split; first last. 
    apply follows_delay. apply singleton_andS_follows; first last.
    have h3 := follows_singleton h2. 
    have h4 := follows_setoid (@singleton_setoid _) h2 h3 (bisim_reflexive _) => {h2 h3}.
    by apply h4. have h4 := follows_singleton h2. 
    have := follows_setoid (@singleton_setoid  _) _ h4 h4 => {h4}. apply.  
    have h3 := follows_hd h2 => {h2}. rewrite -h3 in h0 => {h3}. 
    have := iter_append_dup h0 h1. by apply. apply finite_delay.
    clear h0. have h0 := follows_singleton h2 => {h2}.
    have := finite_setoid _ h0 => {h0}. apply. foo h1. apply finite_nil. 
    move: H => [tr1 [h0 h1]]. move: h0 => [n [tr2 [h0 h2]]]. 
    move: h0 => [st0 [h0 h3]]. foo h3. foo h2. 
    move h0: (t (hd tr1)) => n. rewrite h0 in H2. clear h0.  clear h tr'. 
    have h: forall (m: nat) (n : nat) (tr1 tr tr0 : trace),
    n <= m -> 
    append (fun tr2 : trace => finite tr2)
    (singleton (fun st : state => t st < n)) tr1 ->
    follows (dup u) tr1 tr ->
    follows
    (iter
     (append
        (fun tr2 : trace =>
         exists x : nat,
         satisfy
           (([|fun st : state => t st = x|]) ***
            Finite *** ([|fun st : state => t st < x|])) tr2) (dup u))) tr
    tr0 -> finite tr0. clear tr0 tr H0 tr1 h1 n H2.
    move => m. induction m.
    - move => n tr0 tr1 tr2 h h1 h2 h3.
      have h4: n = 0; first by lia. rewrite h4 in h1 => {h4 h}.  
      move: h1 => [tr3 [h1 h4]].
      move: tr3 h1 tr0 tr1 tr2 h2 h3 h4. induction 1.
      - move => tr0 tr1 tr2 h0 h1 h2. foo h2. move: H1 => [st0 [h3 h4]].
        absurd False. done. by inversion h3.
      - move => tr0 tr1 tr2 h0 h2 h3. foo h3. foo h0. 
        foo h2. apply finite_delay.
        have := IHh1 _ _ _ H3 H4 H2. by apply. 
    - move => n tr0 tr1 tr2 h h0 h1 h2. move: h0 => [tr3 [h0 h3]]. 
      move: tr3 h0 tr0 tr1 tr2 h3 h1 h2. induction 1. 
      - move => tr0 tr1 tr2 h0 h1 h2. foo h0. move: H1 => [st0 [h0 h3]]. 
        foo h3. foo h1. move: H1 => [st0 [h1 h3]]. foo h3. foo H1. simpl in h0. 
        foo h2. foo H2. apply finite_delay. foo H1. apply finite_nil. 
        move: H => [tr0 [h2 h3]]. move: h2 =>[n0 [tr1 [h2 h4]]].
        move: h2 => [st0 [h2 h5]]. foo h5. foo h4.
        have h2 := follows_hd H0. rewrite -h2 in h0 => {h2}. 
        have h2 := follows_hd h3. rewrite -h2 in h0 => {h2}. 
        have h2: t (hd tr0) <= m; first by lia. clear h0. 
        have := IHm _ _ _ _ h2 H2 h3 H0. by apply. 
    - clear IHm. move => tr0 tr1 tr2 h3 h1 h2. foo h3. foo h1. foo h2. 
      apply finite_delay. have := IHh0 _ _ _ H2 H3 H4. by apply. 
    have := h n _ _ _ _ _ H2 h1 H0. apply. lia. 
  have := semax_conseq_R h1 h0. by apply.  
- clear H1. move => u0. 
  have h0 := IHtsemax u0 => {IHtsemax}. 
  have := semax_conseq _ _ h0. apply. 
  * clear h0. move => st0 [h0 h1]. by split; [ have := H _ h0; apply | done]. 
  * clear h0. move => tr0 [tr1 [h0 h1]]. move: h0 => [st0 [h0 h2]]. 
    foo h2. foo h1. exists (Tnil (hd tr0)).  split. exists (hd tr0). 
    by split; [ done | apply bisim_reflexive]. apply follows_nil => //. 
    clear h0. move: H3 => [tr1 [h0 h1]]. exists tr1. split; first done. 
    have := follows_monotone (singleton_monotone _) h1. apply. done. 
Qed.

(* Corollary 4.1 *)
Lemma tsemax_correct_for_semax: forall s U V, tsemax U s V ->
 semax U s (Finite *** [| V |]).
Proof.
move => s U V htsemax.
have := (tsemax_correct_semax htsemax ttS) => {htsemax}. move => htsemax. 
have := semax_conseq _ _  htsemax. apply. 
- by move => st0 hU; split; auto.
- have := (assertT_imp_trans (@Append_assoc_R _ _ _)). apply. 
  apply Append_monotone_L. move => tr [tr1 [h0 h1]]. 
  destruct h0 as [st0 [h0 h2]]. inversion h1; subst; clear h1. 
  * inversion h2; subst; clear h2. auto. 
  * inversion h2. 
Qed.
