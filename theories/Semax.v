Require Import SsrExport.
Require Import Setoid. 
Require Import Trace.
Require Import Language.
Require Import Assert.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive semax: assertS -> stmt -> assertT -> Prop :=

| semax_skip: forall u,   semax u Sskip ([|u|]) 

| semax_assign: forall u x a, semax u (Sassign x a) (Updt u x a)

| semax_seq: forall s1 s2 u v p1 p2,
  semax u s1 (p1 *** [|v|]) -> 
  semax v s2 p2 ->
  semax u (Sseq s1 s2)  (p1 *** p2)

| semax_ifthenelse: forall a s1 s2 u p,
  semax (u andS eval_true a) s1 p ->
  semax (u andS eval_false a) s2 p ->
  semax u (Sifthenelse a s1 s2) (<< u >> *** p)

| semax_while:forall a s u u0 p, 
  u0 ->> u ->
  semax  (u andS eval_true a) s (p *** [|u|]) ->
  semax u0 (Swhile a s) (<<u0>> *** (Iter (p *** <<u>>)) *** [|eval_false a|])

| semax_conseq: forall s u1 u2 p1 p2,
  u1 ->> u2 -> 
  p2 =>> p1 -> 
  semax u2 s p2 ->
  semax u1 s p1

| semax_ex: forall s (A: Set) (u: A -> assertS) (p: A -> assertT),
  (forall x, semax (u x) s (p x)) ->
  semax (exS u) s (exT p).   

Lemma semax_conseq_R: forall u s p q,
p =>> q -> semax u s p -> semax u s q. 
Proof. 
move => u s p q h0 h1. 
have := semax_conseq (@assertS_imp_refl u) h0 h1. apply. 
Qed.   

Lemma semax_conseq_L: forall u v s p,
v ->> u -> semax u s p -> semax v s p. 
Proof. 
move => u v s p h0 h1. 
have := semax_conseq h0 _ h1.
apply. done.   
Qed.   

(* Lemma 3.5 *)
(*
Lemma push_pre: forall u s p, semax u s p -> semax u s ([|u|] *** p). 
Proof. 
have: forall u s p, semax u s p -> forall v, semax (u andS v) s ([|v|] *** p).
induction 1. 
- move => v. have := semax_conseq_R _ (semax_skip _). apply. 
  move => tr0. simpl. move => [st0 [h0 h1]]. foo h1. exists (Tnil st0).
  destruct h0 as [h0 h1]. split. exists st0. split => //. apply bisim_reflexive. 
  apply follows_nil => //. exists st0. split => //. apply bisim_reflexive. 
- move => v. have := semax_conseq_R _ (semax_assign _ _ _). apply. 
  move => tr0. simpl. move => [st0 [h0 h1]]. foo h1. foo H1. 
  destruct h0 as [h0 h1]. exists (Tnil st0). split. exists st0. split => //. 
  apply bisim_reflexive. apply follows_nil => //. exists st0. split => //. 
  apply bisim_reflexive. 
- move => v0. have hs1 := IHsemax1 v0 => {IHsemax1}.
  have hs2 := IHsemax2 v => {IHsemax2}.
  have := semax_conseq_R (@Append_assoc_R _ _ _) hs1.
  clear hs1. move => hs1. have := semax_conseq_R _ (semax_seq hs1 
  (semax_conseq_L _ hs2)). apply.
  have := assertT_imp_trans _ (@Append_assoc_L _ _ _). apply.
  apply Append_monotone_R. apply Singleton_Append.      
  move => st0 h0. split => //. 
- move => v. have hs1 := IHX1 v => {IHX1}.
  have h0: ((u andS v) andS eval_true a) ->> ((u andS eval_true a) andS v).
  * move => st0 [[h0 h1] h2] => //.
  have := semax_conseq_L h0 hs1 => {hs1}. move => hs1.   
  have hs2 := IHX2 v => {IHX2}. clear h0. 
  have h0: ((u andS v) andS eval_false a) ->> ((u andS eval_false a) andS v).
  * move => st0 [[h0 h1] h2] => //.
  have := semax_conseq_L h0 hs2 => {hs2}. move => hs2.
  have := semax_ifthenelse hs1 hs2 => {hs1 hs2}. clear h0. move => h. 
  have := semax_conseq_R _ h. apply. 
  have := assertT_imp_trans (@Append_assoc_R _ _ _). apply.
  have := assertT_imp_trans _ (@Append_assoc_L _ _ _). apply. 
  apply Append_monotone_L. move => tr0. simpl. move => [tr1 [h0 h1]].
  destruct h0 as [st0 [h0 h2]]. foo h2. foo H1. destruct h0 as [h0 h2]. 
  foo h1. foo X. destruct X0 as [st0 [h1 h3]]. foo h3. simpl in h0. simpl in h2. 
  simpl. exists (Tnil st0). split. exists st0; split => //. apply bisim_reflexive. 
  apply follows_nil => //. exists st0. split => //. apply bisim_reflexive. 
- move => v. have := IHX ttS => {IHX}. 
  move => hs. have hpre: (u andS eval_true a) ->> 
  (u andS eval_true a) andS ttS. move => st0 [h0 h1]. split => //. 
  have := semax_conseq_L hpre hs => {hs hpre}. move => hs. 
  have := semax_conseq_R (@ttS_Chop _) hs => {hs}. move => hs. 
  have := semax_conseq_R _ (semax_while _ hs). apply.
  have := assertT_imp_trans _ (@Append_assoc_L _ _ _). apply.
  apply Append_monotone_L. move => tr0 [st0 [h0 h1]]. destruct h0 as [h0 h2]. 
  foo h1. foo H1. simpl. exists (Tnil st0). split. exists st0. split => //. 
  apply bisim_reflexive. apply follows_nil => //. exists st0. split => //. 
  apply bisim_reflexive. move => st0 [h0 h1]. have := a0 _ h0. done. 
- move => v. have hs := IHX v => {IHX}. 
  have := semax_conseq _ _ hs. apply. move => st0 [h0 h1].
  split => //. have := a _ h0. done. apply Append_monotone_R. done. 
- move => v. have hpre: (exS u andS v) ->> exS (fun x => u x andS v). 
  * move => st0 [h0 h1]. destruct h0 as [x h0]. exists x. split => //. 
  have hpost: (exT (fun x => [|v|] *** p x)) =>> ([|v|] *** exT p).
  * move => tr0 [x h0]. move hp: (p x) => px. rewrite hp in h0. 
    destruct px as [q hq]. simpl in h0. destruct h0 as [tr1 [h0 h1]]. 
    destruct h0 as [st0 [h0 h2]]. foo h2. foo h1. simpl. 
    exists (Tnil (hd tr0)). split. exists (hd tr0). split => //.  apply bisim_reflexive. 
    apply follows_nil => //. exists x. rewrite hp. simpl. done. 
  have := semax_conseq hpre hpost. apply. apply semax_ex. 
  clear hpre hpost. move => x. have := X _ v. done. 
move => h u s p hs. have := h _ _ _ hs => {hs}. move => hs.
have := semax_conseq_L _ (hs _). apply. done.
Qed.
*)
