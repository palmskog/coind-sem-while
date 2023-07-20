Require Import SsrExport.
Require Export ZArith.
Require Export List.
Require Import Language. 

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Ltac foo h := inversion h; subst => {h}.

(* This must be found in the library ... *)
Lemma Empty_set_elim: forall (T: Type), Empty_set -> T. 
Proof.
move => T h0.  pose f := fun e: Empty_set => T.  
have := Empty_set_rect f h0. move => h1. rewrite /f in h1. by apply h1. 
Qed. 

CoInductive res: Set := 
| ret: state -> res
| output: val -> res -> res
| input: (val -> res) -> res
| delay: res -> res.

CoFixpoint bot := delay bot. 

Lemma io_destr: forall r, r = match r with
| ret st => ret st
| output v r' => output v r'
| input f => input f
| delay r' => delay r'
end. 
Proof. by case; simpl => //. Qed.

Axiom extensionality: forall (f g: val -> res),
(forall v, f v = g v) -> f = g.   
 

(* strong bisimilarity *)
CoInductive bism: res -> res -> Prop :=
| bism_ret: forall st,
  bism (ret st) (ret st)
| bism_input: forall f0 f1,
  (forall v, bism (f0 v) (f1 v)) ->
  bism (input f0) (input f1)
| bism_output: forall r0 r1 v,
  bism r0 r1 ->
  bism (output v r0) (output v r1)
| bism_delay: forall r0 r1,
  bism r0 r1 ->
  bism (delay r0) (delay r1).


(* bisimilarity is reflexive *)
Lemma bism_refl: forall r, bism r r. 
Proof. 
cofix COINDHYP. case. 
- move => st. by apply bism_ret. 
- move => v r. apply bism_output. apply COINDHYP.  
- move => i. apply bism_input. move => v. apply COINDHYP. 
- move => i. apply bism_delay. apply COINDHYP. 
Qed.  

(* bisimilarity is symmetric *)
Lemma bism_sym: forall r0 r1, bism r0 r1 -> bism r1 r0. 
Proof. 
cofix COINDHYP. move => r0 r1 h0. foo h0. 
- apply bism_ret. 
- apply bism_input. move => v. have := COINDHYP _ _ (H v). apply. 
- apply bism_output. have := COINDHYP _ _ H; apply. 
- have := bism_delay (COINDHYP _ _ H); apply. 
Qed. 

(* bisimilarity is transitive *)
Lemma bism_trans: forall r0 r1 r2, bism r0 r1 -> bism r1 r2 -> bism r0 r2. 
Proof. 
cofix COINDHYP. 
move => r0 r1 r2 h0. foo h0. 
- move => h0. foo h0. apply bism_ret. 
- move => h0. foo h0. apply bism_input. move => v.
  have := COINDHYP _ _ _ (H v) (H1 v). apply. 
- move => h0. foo h0. apply bism_output. have := COINDHYP _ _ _ H H3; apply. 
- move => h0. foo h0. have := bism_delay (COINDHYP _ _ _ H H1). apply. 
Qed. 

Definition setoid (P: res -> Prop) :=
forall r0, P r0 -> forall r1, bism r0 r1 -> P r1. 

Definition setoid2 (P: res -> res -> Prop) :=
forall r0 r1, P r0 r1 -> forall r2, bism r0 r2 -> forall r3, bism r1 r3 ->
P r2 r3.

Lemma bism_setoid: setoid2 bism. 
Proof. rewrite /setoid2. move => r0 r1 h0 r2 h2 r3 h3. 
have := (bism_trans (bism_trans (bism_sym h2) h0) h3). by apply.
Qed.    

CoFixpoint append (r0 r1: res) :=
match r0 with
| ret st0 => r1
| input f => input (fun v => append (f v) r1)
| output v r2 => output v (append r2 r1)
| delay r2 => delay (append r2 r1)
end. 

Lemma append_setoid: forall r0 r1, bism r0 r1 ->
forall r2 r3, bism r2 r3 -> 
bism (append r0 r2) (append r1 r3). 
Proof. 
cofix hcoind. move => r0 r1 h0 r2 r3 h1. foo h0;
rewrite [append _ _]io_destr; simpl.
- rewrite [append _ _]io_destr; simpl. foo h1.
  by apply bism_refl. apply bism_input. move => v. 
  by apply H. apply bism_output. by apply H. apply bism_delay. 
  by apply H. 
- rewrite [append (input _) _]io_destr; simpl. apply bism_input. 
  move => v. have := hcoind _ _ (H v) _ _ h1. by apply. 
- rewrite [append (output _ _ ) _ ]io_destr; simpl. apply bism_output. 
  have := hcoind _ _ H _ _ h1. by apply. 
- rewrite [append (delay _) _]io_destr; simpl. apply bism_delay. 
  have := hcoind _ _ H _ _ h1. by apply. 
Qed.      

 
(* head convergence *)
Inductive red: res -> res -> Prop :=
| red_ret: forall st, red (ret st) (ret st)
| red_delay: forall r0 r1,  red r0 r1 -> red (delay r0) r1
| red_output: forall r0 r1 v,
  bism r0 r1 ->  red (output v r0) (output v r1) 
| red_input: forall f g, 
  (forall x, bism (f x) (g x)) -> red (input f) (input g).

(* convergence is setoid *)
Lemma red_setoid: setoid2 red. 
Proof. 
rewrite /setoid2. induction 1. 
- move => r0 h0 r1 h1. foo h0. foo h1. by apply red_ret. 
- move => r2 h0 r3 h1. foo h0. have := red_delay (IHred _ H1 _ h1). 
  by apply. 
- move => r2 h0 r3 h1. foo h0. foo h1. 
  have := red_output _ (bism_trans (bism_trans (bism_sym H3) H) H4).
  by apply. 
- move => r0 h0 r1 h1. foo h0. foo h1. 
  have := red_input (fun v => (bism_trans (bism_trans (bism_sym (H1 v)) (H v)) (H2 v))). 
  by apply. 
Qed.  

Lemma red_deterministic: forall r0 r1, red r0 r1 ->
forall r2, red r0 r2 -> bism r1 r2. 
Proof. 
induction 1. 
- move => r0 h0. foo h0. by apply bism_refl. 
- move => r2 h0. foo h0. have := IHred _ H1; by apply. 
- move => r2 h0. foo h0. 
  have := bism_output _ (bism_trans (bism_sym H) H3). by apply. 
- move => r2 h0. foo h0. 
  have := bism_input (fun v => (bism_trans (bism_sym (H v)) (H1 v))). 
  by apply. 
Qed. 

(* divergence *)
CoInductive div: res -> Prop :=
| div_delay: forall r,  div r -> div (delay r).  

Lemma div_setoid: setoid div.
Proof. 
cofix hcoind. move => r0 h0 r1 h1. foo h0. foo h1. 
have := div_delay (hcoind _ H _ H1). by apply. 
Qed. 

Lemma nonred_div: forall r,
~(exists r0, red r r0) -> div r.  
Proof. 
cofix COINDHYP. case. 
- move => st0 h0. absurd False => //. apply h0. exists (ret st0). apply red_ret. 
- move => v r h0. absurd False => //. apply h0. exists (output v r). 
  apply red_output. apply bism_refl. 
- move => f h0. absurd False => //. apply h0. exists (input f). 
  apply red_input. move => v. apply bism_refl. 
- move => r h0. have := div_delay (COINDHYP _ _). apply. move => [r0 h1]. 
  apply h0. exists r0. have := red_delay h1. apply. 
Qed.   

(* weak bisimilarity via head convergence *)

CoInductive wbism: res -> res -> Prop :=
| wbism_ret: forall r0 r1 st,
  red r0 (ret st) -> red r1 (ret st) -> wbism r0 r1
| wbism_output: forall v r0 r0' r1 r1',
  red r0 (output v r0') -> red r1 (output v r1') -> wbism r0' r1' -> 
  wbism r0 r1
| wbism_input: forall r0 r1 f0 f1,
  red r0 (input f0) -> red r1 (input f1) -> (forall v, wbism (f0 v) (f1 v)) ->
  wbism r0 r1
| wbism_delay: forall r0 r1,
  wbism r0 r1 -> wbism (delay r0) (delay r1). 

Lemma wbism_setoid: setoid2 wbism. 
Proof. 
cofix hcoind. move => r0 r1 h0 r2 h1 r3 h2. foo h0. 
- have := wbism_ret (red_setoid H h1 (bism_refl _))
  (red_setoid H0 h2 (bism_refl _)). by apply. 
- have := wbism_output (red_setoid H h1 (bism_refl _))
  (red_setoid H0 h2 (bism_refl _)) H1. by apply. 
- have := wbism_input (red_setoid H h1 (bism_refl _))
  (red_setoid H0 h2 (bism_refl _)) H1. by apply. 
- foo h2. foo h1. have := wbism_delay (hcoind _ _ H _ H2 _ H1).
  by apply. 
Qed.    

Lemma bism_wbism: forall r0 r1, bism r0 r1 -> wbism r0 r1. 
Proof.
cofix hcoind. move => r0 r1 h0. foo h0. 
- have := wbism_ret (red_ret _) (red_ret _). by apply. 
- have := wbism_input (red_input (fun v => bism_refl _))
  (red_input (fun v => bism_refl _)).  apply. move => v. 
  apply hcoind. by apply H. 
- have := wbism_output (red_output _ (bism_refl _))
  (red_output _ (bism_refl _)). apply. have := hcoind _ _ H. by apply. 
- apply wbism_delay. have := hcoind _ _ H. by apply. 
Qed.  

Lemma wbism_refl: forall r, wbism r r. 
Proof. 
cofix hcoind. case. 
- move => st. have := wbism_ret (red_ret st) (red_ret st). by apply. 
- move => v r. 
  have := wbism_output (red_output v (bism_refl _)) 
  (red_output v (bism_refl _)) (hcoind _). by apply. 
- move => f. 
  have := wbism_input (red_input (fun v => bism_refl (f v)))
  (red_input (fun v => bism_refl (f v))) (fun v => hcoind (f v)).
  by apply. 
- move => r. have := wbism_delay (hcoind _). by apply.    
Qed.

Lemma wbism_sym: forall r0 r1, wbism r0 r1 -> wbism r1 r0.
Proof.
cofix hcoind. move => r0 r1 h0. foo h0. 
- have := wbism_ret H0 H. by apply. 
- have := wbism_output H0 H (hcoind _ _ H1). by apply. 
- have := wbism_input H0 H (fun v => hcoind _ _ (H1 v)). by apply. 
- have := wbism_delay (hcoind _ _ H). by apply.   
Qed.

Lemma wbism_delay_R: forall r0 r1, wbism r0 r1 -> wbism r0 (delay r1). 
Proof. 
cofix hcoind. move => r0 r1 h0. foo h0. 
- have h0 := red_delay H0 => {H0}. have := wbism_ret H h0. by apply. 
- have h0 := red_delay H0 => {H0}. have := wbism_output H h0 H1. by apply.
- have h0 := red_delay H0 => {H0}. have := wbism_input H h0 H1. by apply.
- have := wbism_delay (hcoind _ _ H). by apply.    
Qed. 

Lemma wbism_neg_delay_L: forall r0 r1, wbism (delay r0) r1 ->
wbism r0 r1. 
Proof. 
move => r0 r1 h0. foo h0. 
- foo H. have := wbism_ret H2 H0. apply. 
- foo H. have := wbism_output H3 H0 H1. by apply. 
- foo H. have := wbism_input H3 H0 H1. by apply.
- have := wbism_delay_R H0. by apply. 
Qed.  

Lemma red_ret_wbism: forall r0 st0,
red r0 (ret st0) -> forall r1, wbism r0 r1 ->
red r1 (ret st0).     
Proof. 
have: forall r0 r2,
red r0 r2 -> 
forall st0, bism r2 (ret st0) -> forall r1, wbism r0 r1 ->
red r1 (ret st0).
* induction 1. 
  - move => st0 h0 r1 h1. foo h0. foo h1. foo H. by apply H0.
    foo H. foo H. 
  - move => st0 h0 r2 h1.
    have := IHred _ h0 _ (wbism_neg_delay_L h1). by apply. 
    move => st0 h0. foo h0. move => st0 h0. foo h0. 
move => h r0 st0 h0 r1 h1. have := h _ _ h0 _ (bism_refl _) _ h1. 
by apply. 
Qed.  

Lemma red_output_wbism: forall r0 v0 r1, red r0 (output v0 r1) ->
forall r2, wbism r0 r2 -> exists r3, red r2 (output v0 r3) /\ wbism r1 r3. 
Proof. 
have: forall r0 r4, red r0 r4 ->
forall v0 r1, bism (output v0 r1) r4 -> 
forall r2, wbism r0 r2 -> exists r3, red r2 (output v0 r3) /\ wbism r1 r3.
* induction 1.
  - move => v0 r0 h0. foo h0. 
  - move => v0 r2 h0 r3 h1. 
    have := IHred _ _ h0 _ (wbism_neg_delay_L h1). apply. 
  - move => v0 r2 h0 r3 h1. foo h0. foo h1. foo H0. foo H0. 
    exists r1'. split; first done. 
    have := wbism_setoid H3 (bism_trans (bism_trans (bism_sym H5) H)
    (bism_sym H1)) (bism_refl _). by apply. foo H0. 
  - move => v0 r0 h0. foo h0. 
move => h r0 v0 r1 h0 r2 h1. have := h _  _ h0 _ _ (bism_refl _) _ h1. 
by apply. 
Qed.            

Lemma red_input_wbism: forall r0 f0, red r0 (input f0) ->
forall r2, wbism r0 r2 -> 
exists f1, red r2 (input f1) /\ (forall v, wbism (f0 v) (f1 v)).   
Proof. 
have: forall r0 r1, red r0 r1 ->
forall f0, bism (input f0) r1 -> 
forall r2, wbism r0 r2 -> 
exists f1, red r2 (input f1) /\ (forall v, wbism (f0 v) (f1 v)).
* induction 1. 
  - move => f0 h0. foo h0. 
  - move => f0 h0 r2 h1. have := IHred _ h0 _ (wbism_neg_delay_L h1). 
     by apply.
  - move => f0 h0. foo h0. 
  - move => f0 h0 r0 h1. foo h0. foo h1. foo H0. foo H0. 
    foo H0. exists f2. split; first done. move => v. 
    have := wbism_setoid (H3 v) (bism_trans (bism_trans (bism_sym (H6 v))
    (H v)) (bism_sym (H2 v))) (bism_refl _). by apply. 
move => h r0 f0 h0 r2 h1. have := h _ _ h0 _ (bism_refl _) _ h1. 
by apply. 
Qed.      

Lemma wbism_trans: forall r0 r1 r2, wbism r0 r1 -> wbism r1 r2 ->
wbism r0 r2.
Proof. 
cofix hcoind. move => r0 r1 r2 h0 h1; foo h0; foo h1.  
- have h0 := red_deterministic H0 H1. foo h0. 
  have := wbism_ret H H2. by apply. 
- have h0 := red_deterministic H0 H1. foo h0. 
- have h0 := red_deterministic H0 H1. foo h0.
- foo H0. have h0 := red_ret_wbism H3 H1. 
  have := wbism_ret H (red_delay h0). by apply.   
- have h0 := red_deterministic H0 H2. foo h0.
- have h0 := red_deterministic H0 H2. foo h0.
- have := wbism_output H H3 (hcoind _ _ _ H1 
  (wbism_setoid H4 (bism_sym H6) (bism_refl _))). by apply. 
- have h0 := red_deterministic H0 H2. foo h0.
- foo H0. have [r1 [h0 h1]] := red_output_wbism H4 H2. 
  have := wbism_output H (red_delay h0) (hcoind _ _ _ H1 h1). 
  by apply. 
- have h0 := red_deterministic H0 H2. foo h0.
- have h0 := red_deterministic H0 H2. foo h0.
- have h0 := red_deterministic H0 H2. foo h0.
  have := wbism_input H H3 (fun v => hcoind _ _ _ (wbism_setoid (H1 v)
  (bism_refl _) (H7 v)) (H4 v)). by apply. 
- foo H0. have [f2 [h0 h1]] := red_input_wbism H4 H2. 
  have := wbism_input H (red_delay h0) (fun v => hcoind _ _ _
  (H1 v) (h1 v)). by apply. 
- foo H0. have h0 := red_ret_wbism H3 (wbism_sym H). 
  have := wbism_ret (red_delay h0) H1. by apply. 
- foo H0. have [r0 [h0 h1]] := red_output_wbism H4 (wbism_sym H). 
  have := wbism_output (red_delay h0) H1 (hcoind _ _ _  (wbism_sym h1) H2). 
  by apply. 
- foo H0. have [f2 [h0 h1]] := red_input_wbism H4 (wbism_sym H). 
  have := wbism_input (red_delay h0) H1 (fun v => hcoind _ _ _ 
  (wbism_sym (h1 v)) (H2 v)). by apply. 
- have := wbism_delay (hcoind _ _ _ H H1). by apply. 
Qed. 

(* weak bisimilarity 2 *)
(* with nested induction-coinduction *)

Inductive wbismi (X: res -> res -> Prop) : res -> res -> Prop :=
| wbismi_delay_L: forall r0 r1,
  wbismi X r0 r1 -> wbismi X (delay r0) r1
| wbismi_delay_R: forall r0 r1,
  wbismi X r0 r1 -> wbismi X r0 (delay r1)
| wbismi_ret: forall st, wbismi X (ret st) (ret st)
| wbismi_input: forall f0 f1,
  (forall v, X (f0 v) (f1 v)) ->
  wbismi X  (input f0) (input f1)
| wbismi_output: forall v r0 r1,
  X r0 r1 -> wbismi X  (output v r0) (output v r1).

CoInductive wbismc: res -> res -> Prop :=
| wbismc_intro: forall (X: res -> res -> Prop) r0 r1,
  (setoid2 X) -> 
  (forall r0 r1, X r0 r1 -> wbismc r0 r1) -> 
  wbismi X r0 r1 -> wbismc r0 r1 
| wbismc_delay: forall r0 r1, wbismc r0 r1 -> wbismc (delay r0) (delay r1).

Lemma wbismi_monotone: forall (X Y: res -> res -> Prop),
(forall x y, X x y -> Y x y) -> 
forall r0 r1, wbismi X r0 r1 -> wbismi Y r0 r1.
Proof. 
move => X Y hXY. induction 1. 
- have := wbismi_delay_L IHwbismi. by apply.   
- have := wbismi_delay_R IHwbismi. by apply.
- by apply wbismi_ret. 
- apply wbismi_input. move => v. apply hXY. done. 
- apply wbismi_output. have := hXY _ _ H. by apply. 
Qed.    

Lemma wbismi_setoid: forall X, setoid2 X ->
setoid2 (wbismi X). 
Proof. 
move => X hsetoid. rewrite /setoid2. induction 1. 
- move => r2 h0 r3 h1. foo h0. have h0 := IHwbismi _ H1 _ h1. 
  have := wbismi_delay_L h0. by apply. 
- move => r2 h0 r3 h1. foo h1. 
  have := wbismi_delay_R (IHwbismi _ h0 _ H1). by apply. 
- move => r2 h0 r3  h1. foo h0. foo h1. by apply wbismi_ret.
- move => r2 h0 r3 h1. foo h0. foo h1. apply wbismi_input.
  move => v. have := hsetoid _ _ (H v) _ (H1 v) _ (H2 v). by apply. 
- move => r2 h0 r3 h1. foo h0. foo h1. apply wbismi_output. 
  have := hsetoid _ _ H _ H3 _ H4. by apply. 
Qed.

Lemma wbismc_setoid: setoid2 wbismc. 
Proof. 
rewrite /setoid2. cofix hcoind. move => r0 r1 h0. foo h0. 
- move => r2 h0 r3 h1. have := wbismc_intro H H0. apply.
  have := wbismi_setoid H H1 h0 h1. by apply. 
- move => r0 h0 r1 h1. foo h0. foo h1. 
  have := wbismc_delay (hcoind _ _ H _ H1 _ H2). by apply. 
Qed.   

Lemma bism_wbismc: forall r0 r1, bism r0 r1 -> wbismc r0 r1. 
Proof. 
cofix hcoind. move => r0 r1 h0. foo h0. 
- have := wbismc_intro bism_setoid.  apply. apply hcoind.
  by apply wbismi_ret. 
- have := wbismc_intro bism_setoid. apply. apply hcoind.
  by apply wbismi_input.
- have := wbismc_intro bism_setoid. apply. apply hcoind.
  by apply wbismi_output.
- have := wbismc_delay (hcoind _ _ H). by apply. 
Qed.

(* wbismc is reflexive *)
Lemma wbismc_refl: forall r, wbismc r r. 
Proof.
move => r. have := bism_wbismc (bism_refl _). by apply. 
Qed.  

(* wbismc is symmetric *)
Lemma wbismc_sym: forall r0 r1, wbismc r0 r1 -> wbismc r1 r0. 
Proof. 
cofix hcoind. move => r0 r1 h0. foo h0.
- have h: setoid2 (fun r0 => fun r1 => wbismc r1 r0). 
  * rewrite /setoid2. move => r2 r3 h0 r4 h1 r5 h2. 
     have := wbismc_setoid h0 h2 h1. by apply.  
  have := wbismc_intro h. apply. move => r2 r3 h0. 
  have := hcoind _ _ h0. by apply. have h0 := wbismi_monotone H0 H1. 
  clear H0 H1 H h. move: r0 r1 h0. induction 1.
  - have := wbismi_delay_R IHh0. by apply.        
  - have := wbismi_delay_L IHh0. by apply.
  - apply wbismi_ret. 
  - by apply wbismi_input. 
  - by apply wbismi_output. 
- have := wbismc_delay (hcoind _ _ H). by apply. 
Qed.

Definition comp (X Y: res -> res -> Prop) (r0 r1: res) :=  
exists r2, X r0 r2 /\ Y r2 r1. 

Lemma comp_setoid: forall (X Y: res -> res -> Prop),
(setoid2 X) -> (setoid2 Y) -> (setoid2 (comp X Y)). 
Proof. 
move => X Y hX hY r0 r1 [r4 [h1 h2]] r2 h3 r3 h4. exists r4. split. 
have := hX _ _ h1 _ h3 _ (bism_refl _). done. 
have := hY _ _ h2 _ (bism_refl _) _ h4. done. 
Qed.    

Lemma wbismi_comp: forall (X Y: res -> res -> Prop),
(setoid2 X) -> (setoid2 Y) -> 
forall r0 r1, wbismi X r0 r1 -> forall r2 r3, wbismi Y r2 r3 -> bism r1 r2 ->
wbismi (comp X Y) r0 r3. 
Proof. 
move => X Y hX hY. induction 1; induction 1; move => h0; foo h0.  
- have := wbismi_delay_L (IHwbismi _ _ (wbismi_delay_L H0) 
  (bism_delay H3)). by apply. 
- have := wbismi_delay_R (IHwbismi0 (bism_refl _)). by apply. 
- have := wbismi_delay_R (IHwbismi0 (bism_input H1)). by apply.
- have := wbismi_delay_R (IHwbismi0 (bism_output _ H1)). by apply.
- have := wbismi_delay_R (IHwbismi0 (bism_delay H1)). by apply.
- have := wbismi_delay_L (IHwbismi _ _ (wbismi_ret _ _) (bism_refl _)).
  by apply. 
- have := wbismi_delay_L (IHwbismi _ _ (wbismi_input H0) (bism_input H3)).
  by apply.
- have := wbismi_delay_L (IHwbismi _ _ (wbismi_output _ H0) (bism_output _ H3)).
  by apply.
- have := IHwbismi _ _ H0 H3. by apply. 
- have := wbismi_delay_R (IHwbismi0 (bism_delay H2)). by apply.
- have := wbismi_delay_R (IHwbismi (bism_refl _)). by apply. 
- by apply wbismi_ret. 
- have := wbismi_delay_R (IHwbismi (bism_input H2)). by apply. 
- apply wbismi_input. move => v. exists (f1 v). split. 
   have := H v; by apply. have := hY _ _ (H0 _) _ (bism_sym (H3 _))  _ (bism_refl _).
   by apply. 
- have := wbismi_delay_R (IHwbismi (bism_output _ H4)). by apply. 
- apply wbismi_output. exists r1. split => //. 
  have := hY _ _ H0 _ (bism_sym H2)  _ (bism_refl _). by apply.
Qed.  

Lemma wbismi_neg_delay_R: forall X,
setoid2 X ->
forall r0 r1, wbismi X r0 (delay r1) -> wbismi X r0 r1.
Proof. 
move => X hsetoid. 
have h: forall r0 r1, wbismi X r0 r1 -> forall r2, bism r1 (delay r2) ->
wbismi X r0 r2.
* induction 1. 
  - move => r2 h0. have := wbismi_delay_L (IHwbismi _ h0). by apply. 
  - move => r2 h0. foo h0. have := wbismi_setoid hsetoid H (bism_refl _)
    H2. by apply. 
  - move => r0 h0. foo h0. 
  - move => r2 h0. foo h0. 
  - move => r2 h0. foo h0. 
move => r0 r1 h0. have := h _ _ h0 _ (bism_refl _). by apply. 
Qed. 



Lemma red_wbismi_ret: forall tr0 tr1 st0,
red tr0 (ret st0) -> red tr1 (ret st0) ->
wbismi wbism tr0 tr1.
Proof.
have h: forall tr0 tr1, red tr0 tr1 -> 
forall tr2 tr3, red tr2 tr3 -> 
forall st0, bism tr1 (ret st0) -> bism tr3 (ret st0) ->
wbismi wbism tr0 tr2.
induction 1; induction 1. 
- move => st1 h0 h1. foo h0. foo h1. apply wbismi_ret. 
- move => st0 h0 h1. have := wbismi_delay_R (IHred _ h0 h1). by apply. 
- move => st0 h0 h1. foo h1.
- move => st0 h0 h1. foo h1. 
- move => st0 h1 h2. have := wbismi_delay_L (IHred _ _ _ _ h1 h2). apply. 
  by apply red_ret. 
- move => st0 h0 h1. have := wbismi_delay_R (IHred0 _ h0 h1). by apply. 
- move => st0 h0 h1. foo h1. 
- move => st0 h0 h1. foo h1. 
- move => st0 h0. foo h0. 
- move => st0 h0. foo h0. 
- move => st0 h0. foo h0. 
- move => st0 h0. foo h0. 
- move => st0 h0. foo h0. 
- move => st0 h0. foo h0. 
- move => st0 h0. foo h0. 
- move => st0 h0. foo h0. 
* move => tr0 tr1 st0 h0 h1. have := h _ _ h0 _ _ h1 _ _ _. apply. 
apply bism_ret. apply bism_ret. 
Qed.       

Lemma wbismi_neg_delay_L: forall X,
setoid2 X ->
forall r0 r1, wbismi X (delay r0) r1-> wbismi X r0 r1.
Proof. 
move => X hsetoid. 
have h: forall r0 r1, wbismi X r0 r1 -> forall r2, bism r0 (delay r2) ->
wbismi X r2 r1.
* induction 1. 
  - move => r2 h0. foo h0. have := wbismi_setoid hsetoid H H2 (bism_refl _).
    by apply. 
  - move => r2 h0.  have := wbismi_delay_R (IHwbismi _ h0). by apply. 
  - move => r0 h0. foo h0. 
  - move => r2 h0. foo h0. 
  - move => r2 h0. foo h0. 
move => r0 r1 h0. have := h _ _ h0 _ (bism_refl _). by apply. 
Qed. 


Lemma wbismc_delay_R: forall r0 r1, wbismc r0 r1 -> wbismc r0 (delay r1). 
Proof.
cofix hcoind. move => r0 r1 h0. foo h0. 
- have := wbismc_intro H H0. apply. have := wbismi_delay_R H1. by apply. 
- have := wbismc_delay (hcoind _ _ H) . by apply. 
Qed. 

Lemma wbismc_delay_L: forall r0 r1, wbismc r0 r1 -> wbismc (delay r0) r1. 
Proof.
cofix hcoind. move => r0 r1 h0. foo h0. 
- have := wbismc_intro H H0. apply. have := wbismi_delay_L H1. by apply. 
- have := wbismc_delay (hcoind _ _ H) . by apply. 
Qed. 



Lemma wbismc_neg_delay_L: forall r0 r1, wbismc (delay r0) r1 ->
wbismc r0 r1. 
Proof. 
move => r0 r1 h0. foo h0. 
- have := wbismc_intro H H0. apply. have := wbismi_neg_delay_L H H1.
  by apply.
- have := wbismc_delay_R H0. by apply. 
Qed.

Lemma wbismc_neg_delay_R: forall r0 r1, wbismc r0 (delay r1) ->
wbismc r0 r1. 
Proof. 
move => r0 r1 h0. foo h0. 
- have := wbismc_intro H H0. apply. have := wbismi_neg_delay_R H H1.
  by apply.
- have := wbismc_delay_L H1. by apply. 
Qed.


(* wbismc is transitive *)
Lemma wbismc_trans: forall r0 r1 r2, wbismc r0 r1 -> wbismc r1 r2 ->
wbismc r0 r2. 
Proof. 
cofix hcoind. move => r0 r1 r2 h0. foo h0; move => h0; foo h0. 
- have := wbismc_intro (comp_setoid H H2). apply. 
  * move => r3 r4 h0. destruct h0 as [r5 [h0 h1]]. 
     have := hcoind _ _ _ (H0 _ _ h0) (H3 _ _ h1). by apply. 
  * have := wbismi_comp H H2 H1 H4 (bism_refl _). by apply.
- have h := wbismi_neg_delay_R H H1. 
  have := wbismc_intro  (comp_setoid H wbismc_setoid). apply. 
  * move => r1 r2 [r5 [h0 h1]]. have := hcoind _ _ _ (H0 _ _ h0) h1.
     by apply. 
  * apply wbismi_delay_R. clear H1.  move: r0 r3 h r4 H2. induction 1. 
     - move => r2 h0. have := wbismi_delay_L (IHh _ h0). by apply. 
     - move => r2 h0. have := IHh _ (wbismc_neg_delay_L h0). by apply. 
     - move => r2 h0. foo h0. move h: (ret st) => r0. rewrite h in H3. 
       move: r0 r2 H3 h. induction 1.
       - move => h0. foo h0. 
       - move => h0. have := wbismi_delay_R (IHwbismi h0). by apply.
       - move => h0. apply wbismi_ret. 
       - move => h0. foo h0. 
       - move => h0. foo h0. 
     - move => r2 h0. foo h0. move h: (input f1) => r0. rewrite h in H4. 
       move: r0 r2 H4 h. induction 1.
       - move => h0. foo h0. 
       - move => h0. have := wbismi_delay_R (IHwbismi h0). by apply.
       - move => h0. foo h0. 
       - move => h0. foo h0. apply wbismi_input. move => v. exists (f2 v). 
         split =>//. have := H3 _ _ (H4 _). by apply.  
       - move => h0. foo h0.
     - move => r2 h0. foo h0. move h: (output v r1) => r3. rewrite h in H4. 
       move: r3 r2 H4 h. induction 1.
       - move => h0. foo h0. 
       - move => h0. have := wbismi_delay_R (IHwbismi h0). by apply.
       - move => h0. foo h0.
       - move => h0. foo h0.  
       - move => h0. foo h0. apply wbismi_output. exists r2.  
         split =>//. have := H3 _ _ H4. by apply.
- have h := wbismi_neg_delay_L H0 H2. clear H2. 
  have := wbismc_intro  (comp_setoid wbismc_setoid H0). apply. 
  * move => r0 r1 [r5 [h0 h1]]. have := hcoind _ _ _ h0 (H1 _ _ h1).
     by apply. 
  * apply wbismi_delay_L. move: r4 r2 h r3 H. induction 1. 
     - move => r2 h0. have := IHh _ (wbismc_neg_delay_R h0). by apply. 
     - move => r2 h0. have := wbismi_delay_R (IHh _ h0). by apply.  
     - move => r2 h0. foo h0. move h: (ret st) => r0. rewrite h in H3. 
       move: r0 r2 H3 h. induction 1.
       - move => h0. have := wbismi_delay_L (IHwbismi h0). by apply.
       - move => h0. foo h0. 
       - move => h0. apply wbismi_ret. 
       - move => h0. foo h0. 
       - move => h0. foo h0. 
     - move => r2 h0. foo h0. move h: (input f0) => r0. rewrite h in H4. 
       move: r0 r2 H4 h. induction 1.  
       - move => h0. have := wbismi_delay_L (IHwbismi h0). by apply.
       - move => h0. foo h0. 
       - move => h0. foo h0. 
       - move => h0. foo h0. apply wbismi_input. move => v. exists (f3 v). 
         split =>//. have := H3 _ _ (H4 _). by apply.  
       - move => h0. foo h0.
     - move => r2 h0. foo h0. move h: (output v r0) => r3. rewrite h in H4. 
       move: r3 r2 H4 h. induction 1.
       - move => h0. have := wbismi_delay_L (IHwbismi h0). by apply.
       - move => h0. foo h0.
       - move => h0. foo h0.
       - move => h0. foo h0.   
       - move => h0. foo h0. apply wbismi_output. exists r3.  
         split =>//. have := H3 _ _ H4. by apply.
- have := wbismc_delay (hcoind _ _ _ H H1). by apply. 
Qed. 

(* the rest proves equivalence of the two definitions of *)
(* weak bisimilarity *)

Lemma red_wbismi_output: forall v r0 r1 r2 r3,
red r0 (output v r1) -> red r2 (output v r3) ->
wbism r1 r3 -> wbismi wbism r0 r2.  
Proof. 
have h: forall r0 r1, red r0 r1 ->
forall r2 r3, red r2 r3 ->
forall v r1', bism r1 (output v r1') ->
forall r3', bism r3 (output v r3') ->
wbism r1' r3' -> wbismi wbism r0 r2. 
induction 1; induction 1.
- move => v0 r0 h0. foo h0. 
- move => v0 r2 h0. foo h0.
- move => v0 r2 h0. foo h0. 
- move => v0 r2 h0. foo h0. 
- move => v0 r2 h0 r3 h1 h2. foo h1. 
- move => v0 r4 h0 r5 h1 h2. 
  have := wbismi_delay_R (IHred0 _ _ h0 _ h1 h2). by apply. 
- move => v0 r4 h0 r5 h1 h2. 
  have := wbismi_delay_L (IHred _ _ (red_output _ H0) _ _ h0 _ h1 h2).
  by apply. 
- move => v0 r2 h0 r3 h1. foo h1. 
- move => v0 r2 h0 r3 h1. foo h1. 
- move => v0 r4 h0 r5 h1 h2. 
  have := wbismi_delay_R (IHred _ _ h0 _ h1 h2). by apply. 
- move => v1 r4 h0 r5 h1 h2. foo h0. foo h1. apply wbismi_output. 
  have := wbism_setoid _ (bism_sym (bism_trans H H2))
  (bism_sym (bism_trans H0 H3)). apply. by apply h2. 
- move => v1 r2 h0 r3 h1. foo h1. 
- move => v0 r0 h0. foo h0. 
- move => v0 r2 h0. foo h0. 
- move => v0 r2 h0. foo h0. 
- move => v0 r0 h0. foo h0.
move => v r0 r1 r2 r3 h0 h1 h2.
have := h _ _ h0 _ _ h1 _ _ (bism_refl _) _ (bism_refl _) h2. by apply.          
Qed.

Lemma red_wbismi_input: forall r0 r1 f0 f1, 
red r0 (input f0) -> red r1 (input f1) ->
(forall v, wbism (f0 v) (f1 v))-> wbismi wbism r0 r1.  
Proof.
have h: forall r0 r1, red r0 r1 -> forall r2 r3, red r2 r3 ->
forall f0, bism r1 (input f0) -> forall f1, bism r3 (input f1) ->
(forall v, wbism (f0 v) (f1 v)) ->
wbismi wbism r0 r2. 
* induction 1; induction 1.
  - move => f0 h0. foo h0. 
  - move => f0 h0. foo h0. 
  - move => f0 h0. foo h0. 
  - move => f0 h0. foo h0. 
  - move => f0 h0 f1 h1. foo h1. 
  - move => f0 h0 f1 h1 h2.
    have := wbismi_delay_R (IHred0 _ h0 _ h1 h2). by apply. 
  - move => f0 h0 f1 h1. foo h1. 
  - move => f0 h0 f1 h1 h2.      
    have := wbismi_delay_L (IHred _ _ (red_input H0)
    _ h0 _ h1 h2). by apply. 
  - move => f0 h0. foo h0. 
  - move => f0 h0. foo h0. 
  - move => f0 h0. foo h0. 
  - move => f0 h0. foo h0. 
  - move => f0 h0 f1 h1. foo h1. 
  - move => f0 h0 f1 h1 h2. 
    have := wbismi_delay_R (IHred _ h0 _ h1 h2). by apply. 
  - move => f0 h0 f1 h1. foo h1. 
  - move => f2 h0 f1 h1 h2. apply wbismi_input. move => v. 
    foo h1. foo h0. 
    have := wbism_setoid (h2 v) (bism_sym (bism_trans (H v) (H4 v)))
    (bism_sym (bism_trans (H0 v) (H3 v))). by apply. 
move => r0 r1 f0 f1 h0 h1 h2. 
have := h _ _ h0 _ _ h1 _ (bism_refl _) _ (bism_refl _) h2. by apply.    
Qed. 

Lemma wbism_wbismc:
forall tr0 tr1, wbism tr0 tr1 -> wbismc tr0 tr1.
Proof. 
cofix hcoind. move => tr0 tr1 h0. foo h0. 
- have := wbismc_intro wbism_setoid hcoind (red_wbismi_ret H H0). by apply.  
- have := wbismc_intro wbism_setoid hcoind (red_wbismi_output H H0 H1). by apply.   
- have := wbismc_intro wbism_setoid hcoind (red_wbismi_input H H0 H1). by apply.  
- have := wbismc_delay (hcoind _ _ H). apply.
Qed. 

Lemma wbismi_red: forall X r0 r1, wbismi X r0 r1 -> 
(exists st0, red r0 (ret st0) /\ red r1 (ret st0))
\/ (exists f0, exists f1, red r0 (input f0) /\ red r1 (input f1) 
    /\ (forall v, X (f0 v) (f1 v)))
\/ (exists v0, exists r2, exists r3, red r0 (output v0 r2) /\ red r1 (output v0 r3)
    /\ X r2 r3). 
Proof.
induction 1. 
- move: IHwbismi => [h0 | [h0 | h0]].
  - move: h0 => [st0 [h0 h1]]. 
    left. exists st0. split. have := red_delay h0. by apply. by apply h1. 
  - move: h0 => [f0 [f1 [h0 [h1 h2]]]]. right. left. exists f0. exists f1.
    split; last split => //. have := red_delay h0. by apply. 
  - move: h0 => [v0 [r2 [r3 [h0 [h1 h2]]]]]. right; right. exists v0. 
    exists r2. exists r3. split; last split => //. have := red_delay h0; by apply. 
- move: IHwbismi => [h0 | [h0 | h0]].
  - move: h0 => [st0 [h0 h1]]. 
    left. exists st0. split => //. have := red_delay h1. by apply.  
  - move: h0 => [f0 [f1 [h0 [h1 h2]]]]. right. left. exists f0. exists f1.
    split; last split => //. apply h0. have := red_delay h1. by apply.  
  - move: h0 => [v0 [r2 [r3 [h0 [h1 h2]]]]]. right; right. exists v0. 
    exists r2. exists r3. split; last split => //. apply h0.  
    have := red_delay h1; by apply.
- left. exists st. split; by apply red_ret. 
- right; left. exists f0. exists f1. split; last split => //. 
  apply red_input. move => v. apply bism_refl.       
  apply red_input. move => v. apply bism_refl.       
- right; right. exists v. exists r0. exists r1. split; last split => //.
  apply red_output. apply bism_refl.
  apply red_output. apply bism_refl.
Qed.        

Lemma wbismc_wbism: forall tr0 tr1, wbismc tr0 tr1 -> wbism tr0 tr1. 
Proof. 
cofix hcoind. move => tr0 tr1 h0. foo h0.
- have [h0 | [h0 | h0]] := wbismi_red H1.
  - move: h0 => [st0 [h0 h1]]. have := wbism_ret h0 h1. by apply. 
  - move: h0 => [f0 [f1 [h0 [h1 h2]]]]. 
    have := wbism_input h0 h1 (fun v => hcoind _ _ (H0 _ _ (h2 v))). by apply. 
  - move: h0 => [v0 [r2 [r3 [h0 [h1 h2]]]]]. 
    have := wbism_output h0 h1 (hcoind _ _ (H0 _ _ h2)). by apply. 
- have := wbism_delay (hcoind _ _ H). by apply. 
Qed.


(* weak bisimilarity in a classical style *)
CoInductive cwbism: res -> res -> Prop :=
| cwbism_ret: forall r0 r1 st,
  red r0 (ret st) -> red r1 (ret st) -> cwbism r0 r1
| cwbism_output: forall v r0 r0' r1 r1',
  red r0 (output v r0') -> red r1 (output v r1') -> cwbism r0' r1' -> 
  cwbism r0 r1
| cwbism_input: forall r0 r1 f0 f1,
  red r0 (input f0) -> red r1 (input f1) -> (forall v, cwbism (f0 v) (f1 v)) ->
  cwbism r0 r1
| cwbism_div: forall r0 r1, div r0 -> div r1 -> cwbism r0 r1.

Lemma div_wbism: forall r0 r1, div r0 -> div r1 -> wbism r0 r1. 
Proof. 
cofix hcoind. move => r0 r1 h0 h1. foo h0; foo h1. 
have := wbism_delay (hcoind _ _ H H0). by apply. 
Qed. 

(* classical-style weak bisimilarity implies constructive-style one *)
Lemma cwbism_wbism: forall r0 r1, cwbism r0 r1 -> wbism r0 r1.
Proof. 
cofix hcoind. move => r0 r1 h0. foo h0. 
- have := wbism_ret H H0. by apply. 
- have := wbism_output H H0 (hcoind _ _ H1). by apply. 
- have := wbism_input H H0 (fun v => hcoind _ _ (H1 v)). by apply. 
- have := div_wbism H H0. by apply. 
Qed.

Lemma red_wbism: forall r0 r1, red r0 r1 -> 
forall r2 r3, red r2 r3 -> wbism r0 r2 ->
(exists st0, red r0 (ret st0) /\ red r2 (ret st0))
\/ (exists f0, exists f1, red r0 (input f0) /\ red r2 (input f1) 
    /\ (forall v, wbism (f0 v) (f1 v)))
\/ (exists v0, exists r4, exists r5, red r0 (output v0 r4) /\ red r2 (output v0 r5)
    /\ wbism r4 r5).
Proof.
induction 1.  
- move => r0 r1 h0 h1. foo h1. foo H. have h1 := red_deterministic h0 H0.   
  foo h1. left. exists st0. split => //. apply red_ret. 
  foo H. foo H. 
- move => r2 r3 h0 h1. have h2 := wbism_neg_delay_L h1 => {h1}.
  have := IHred _ _ h0 h2 => {IHred}. move => [h1 | [h1 | h1]]. 
  - move: h1 => [st0 [h1 h3]].  left. exists st0. split => //. 
    have := red_delay h1. by apply. 
  - move: h1 => [f0 [f1 [h1 [h3 h4]]]]. right. left. exists f0. exists f1. 
    split; [idtac | split] => //. have := red_delay h1; by apply. 
  - move: h1 => [v0 [r4 [r5 [h1 [h3 h4]]]]]. right. right. exists v0.
    exists r4. exists r5. split; [idtac | split] => //. 
    have := red_delay h1; by apply. 
- move => r2 r3 h0 h1. foo h1. foo H0. foo H0. 
  have h1 := red_deterministic h0 H1. foo h1. right. right. 
  exists v0. exists r0. exists r4. split; [idtac | split] => //. 
  have := red_output _ (bism_refl _). by apply. 
  have := wbism_setoid H2 (bism_sym H4) (bism_sym H5). by apply. foo H0. 
- move => r0 r1 h0 h1. foo h1. foo H0. foo H0. foo H0.
  have h1 := red_deterministic H1 h0. foo h1. right. left. 
  exists f0. exists f1. split; [idtac | split] => //. apply red_input. 
  move => v. by apply H5. 
Qed.  
         

Lemma red_div_false: forall r0 r1, red r0 r1 -> div r0 -> False. 
Proof. 
induction 1. 
- move => h0. foo h0. 
- move => h0. foo h0. have := IHred H1; by apply. 
- move => h0. foo h0. 
- move => h0. foo h0.  
Qed.   

Lemma red_div_wbism: forall r0 r1, red r0 r1 -> forall r2, div r2 ->
wbism r0 r2 -> False.
Proof. 
induction 1. 
- move => r0 h0 h1. foo h1. 
  - foo H. have := red_div_false H0 h0. by apply. 
  - foo H. 
  - foo H. 
- move => r2 h0 h1. have h2 := IHred _ h0 => {IHred}. foo h1. 
  - have := red_div_false H1 h0. by apply. 
  - have := red_div_false H1 h0. by apply. 
  - have := red_div_false H1 h0. by apply. 
  - have := h2 (wbism_delay_R H1). by apply. 
- move => r2 h0 h1. foo h1. 
  - have := red_div_false H1 h0. by apply. 
  - have := red_div_false H1 h0. by apply. 
  - have := red_div_false H1 h0. by apply.        
- move => r0 h0 h1. foo h1. 
  - have := red_div_false H1 h0. by apply.
  - have := red_div_false H1 h0. by apply. 
  - have := red_div_false H1 h0. by apply.     
Qed.       

(* Classically, constructive-style weak bisimilarity implies the classical-style one *)

Axiom red_or_not: forall r,
(exists r0, red r r0) \/ ~(exists r0, red r r0).  

Lemma wbism_cwbism: forall r0 r1, wbism r0 r1 -> cwbism r0 r1. 
Proof. 
cofix hcoind. move => r0 r1 h0. 
have [h1 | h1] := red_or_not r0; have [h2 | h2] := red_or_not r1.
- move: h1 => [r2 h1]. move: h2 => [r3 h2].
  have [h3 | [h3 | h3]] := red_wbism h1 h2 h0 => {h0 h2 h1}.
  - move: h3 => [st0 [h3 h4]]. have := cwbism_ret h3 h4. by apply.
  - move: h3 => [f0 [f1 [h0 [h1 h2]]]]. 
    have := cwbism_input h0 h1 (fun v => hcoind _ _ (h2 v)). by apply. 
  - move: h3 => [v [r4 [r5 [h0 [h1 h2]]]]].
    have := cwbism_output h0 h1 (hcoind _ _ h2). by apply.
- have h3 := nonred_div h2 => {h2}. move: h1 => [r2 h1].
  absurd False => //. have := red_div_wbism h1 h3 h0. by apply. 
- have h3 := nonred_div h1 => {h1}. move: h2 => [r2 h2].
  absurd False => //. have := red_div_wbism h2 h3 (wbism_sym h0). by apply.
- have h3 := nonred_div h1 => {h1}. have h1 := nonred_div h2 => {h2}. 
  have := cwbism_div h3 h1. by apply. 
Qed.    

(****** We [skip] proofs proved in Prop *****)

Axiom skip: forall (P: Type), P. 

(* strong bisimilarity *)
CoInductive Bism: res -> res -> Type :=
| Bism_ret: forall st,
  Bism (ret st) (ret st)
| Bism_input: forall f0 f1,
  (forall v, Bism (f0 v) (f1 v)) ->
  Bism (input f0) (input f1)
| Bism_output: forall r0 r1 v,
  Bism r0 r1 ->
  Bism (output v r0) (output v r1)
| Bism_delay: forall r0 r1,
  Bism r0 r1 ->
  Bism (delay r0) (delay r1).

Definition Setoid (X:res -> Type) :=
forall r0, X r0 -> forall r1, Bism r0 r1 -> X r1. 

Definition Setoid2 (X: res -> res -> Type) :=
forall r0 r1, X r0 r1 -> forall r2, Bism r0 r2 ->
forall r3, Bism r1 r3 -> X r2 r3. 

Lemma Bism_refl: forall r, Bism r r.
Proof. 
apply skip. (* proved in Prop *)
Qed. 

Lemma Bism_sym: forall r0 r1, Bism r0 r1 -> Bism r1 r0.
Proof.
apply skip. (* proved in Prop *)
Qed. 

Lemma Bism_trans: forall r0 r1 r2, Bism r0 r1 -> Bism r1 r2 -> Bism r0 r2. 
Proof. 
apply skip. (* proved in Prop *)
Qed. 
   
Inductive Red: res -> res -> Type :=
| Red_ret: forall st, Red (ret st) (ret st)
| Red_delay: forall r0 r1,
  Red r0 r1 -> Red (delay r0) r1
| Red_output: forall r0 r1 v,
  Bism r0 r1 ->
  Red (output v r0) (output v r1) 
| Red_input: forall f g, 
  (forall x, Bism (f x) (g x)) ->
  Red (input f) (input g).

Lemma Red_Setoid: Setoid2 Red. 
Proof. 
apply skip. (* proved in Prop *)
Qed. 

Lemma Red_deterministic: forall r0 r1 r2,
Red r0 r1 -> Red r0 r2 -> Bism r1 r2. 
Proof.
apply skip. (* proved in Prop *)
Qed. 

Inductive Wbismi (X: res -> res -> Type) : res -> res -> Type :=
| Wbismi_delay_L: forall r0 r1,
  Wbismi X r0 r1 -> Wbismi X (delay r0) r1
| Wbismi_delay_R: forall r0 r1,
  Wbismi X r0 r1 -> Wbismi X r0 (delay r1)
| Wbismi_ret: forall st, Wbismi X (ret st) (ret st)
| Wbismi_input: forall f0 f1,
  (forall v, X (f0 v) (f1 v)) ->
  Wbismi X  (input f0) (input f1)
| Wbismi_output: forall v r0 r1,
  X r0 r1 -> Wbismi X  (output v r0) (output v r1).


Lemma Wbismi_neg_delay_R: forall X,
Setoid2 X ->
forall r0 r1, Wbismi X r0 (delay r1) -> Wbismi X r0 r1.
Proof.
apply skip. (* proved in Prop *)
Qed. 


CoInductive Wbismc: res -> res -> Type :=
| Wbismc_intro: forall (X: res -> res -> Type) r0 r1,
  Setoid2 X -> 
  (forall r0 r1, X r0 r1 -> Wbismc r0 r1) -> 
  Wbismi X r0 r1 -> Wbismc r0 r1 
| Wbismc_delay: forall r0 r1, Wbismc r0 r1 -> Wbismc (delay r0) (delay r1).


Lemma Wbismi_Setoid: forall X, Setoid2 X ->
Setoid2 (Wbismi X). 
Proof. 
apply skip. (* proved in Prop *)
Qed. 

Lemma Wbismc_Setoid: Setoid2 Wbismc.
Proof. apply skip. (* proved in Prop *) Qed. 

CoInductive Wbism: res -> res -> Type :=
| Wbism_ret: forall r0 r1 st,
  Red r0 (ret st) -> Red r1 (ret st) -> Wbism r0 r1
| Wbism_output: forall v r0 r0' r1 r1',
  Red r0 (output v r0') -> Red r1 (output v r1') -> Wbism r0' r1' -> 
  Wbism r0 r1
| Wbism_input: forall r0 r1 f0 f1,
  Red r0 (input f0) -> Red r1 (input f1) -> (forall v, Wbism (f0 v) (f1 v)) ->
  Wbism r0 r1
| Wbism_delay: forall r0 r1,
  Wbism r0 r1 -> Wbism (delay r0) (delay r1). 

Lemma Wbism_Setoid: Setoid2 Wbism. 
Proof.
apply skip. (* proved in Prop *)
Qed. 

Lemma Bism_Wbism: forall r0 r1, Bism r0 r1 -> Wbism r0 r1. 
Proof. 
apply skip. (* proved in Prop *)  
Qed.

Lemma Red_Wbismi: forall X, Setoid2 X -> 
forall r0 r1, Red r0 r1 ->
forall r2, Wbismi X r2 r1 -> Wbismi X r2 r0.
Proof.
move => X hX. induction 1. 
- move => r0 h0. apply h0. 
- move => r2 h0. have := Wbismi_delay_R (IHRed _ h0). by apply. 
- move => r2 h0. have := Wbismi_Setoid hX h0 
  (Bism_refl _) (Bism_output _ (Bism_sym b)). by apply. 
- move => r0 h0. have := Wbismi_Setoid hX h0
  (Bism_refl _) (Bism_sym (Bism_input b)). by apply. 
Qed.

Lemma Wbism_refl: forall r, Wbism r r. 
Proof.
apply skip. (* proved in Prop *)
Qed. 

Lemma Wbism_sym: forall r0 r1, Wbism r0 r1 -> Wbism r1 r0.
Proof.
apply skip. (* proved in Prop *)
Qed.

Lemma Wbism_trans: forall r0 r1 r2, Wbism r0 r1 -> Wbism r1 r2 ->
Wbism r0 r2. 
Proof.
apply skip. (* proved in Prop *)
Qed. 

Lemma Wbismc_Wbism: forall r0 r1, Wbismc r0 r1 -> Wbism r0 r1. 
Proof.
apply skip. (* proved in Prop *)
Qed. 

Lemma Wbism_Wbismc: forall r0 r1, Wbism r0 r1 -> Wbismc r0 r1.
Proof.
apply skip. (* proved in Prop *)
Qed.

Lemma Wbism_delay_R: forall r0 r1,
Wbism r0 r1 -> Wbism r0 (delay r1).
Proof. 
apply skip. (* proved in Prop *)
Qed.

Lemma Wbism_delay_L: forall r0 r1,
Wbism r0 r1 -> Wbism (delay r0) r1.   
Proof.
cofix hcoind. move => r0 r1 h0. foo h0. 
- have h0 := Red_delay H => {H}. have := Wbism_ret h0 H0. by apply. 
- have h0 := Red_delay H => {H}. have := Wbism_output h0 H0 H1. by apply.
- have h0 := Red_delay H => {H}. have := Wbism_input h0 H0 H1. by apply.
- have := Wbism_delay (hcoind _ _ H). by apply.    
Qed. 

Lemma Wbism_neg_delay_L: forall r0 r1, Wbism (delay r0) r1 ->
Wbism r0 r1. 
Proof.
apply skip. (* Proved in Prop *)
Qed. 

Lemma Wbism_neg_delay_R: forall r0 r1,
Wbism r0 (delay r1) -> Wbism r0 r1. 
Proof.
move => r0 r1 h0. foo h0. 
- foo H0. have := Wbism_ret H H2. apply. 
- foo H0. have := Wbism_output H H3 H1. by apply. 
- foo H0. have := Wbism_input H H3 H1. by apply.
- have := Wbism_delay_L H1. by apply.
Qed.

Lemma append_Setoid: forall r0 r1, Bism r0 r1 ->
forall r2 r3, Bism r2 r3 -> 
Bism (append r0 r2) (append r1 r3). 
Proof. 
apply skip.  (* proved in Prop *)
Qed. 

CoInductive Divr: res -> Type :=
| Divr_delay: forall r, Divr r -> Divr (delay r).  

Lemma Divr_Setoid: Setoid Divr.
Proof. apply skip. (* proved in Prop *) Qed.

Lemma Red_Divr: forall r0 r1, Red r0 r1 ->
Divr r0 -> False. 
Proof. 
induction 1. 
- move => h0. foo h0. 
- move => h0. foo h0. have := IHRed H1. by apply.
- move => h0. foo h0.
- move => h0. foo h0.   
Qed.  

Lemma Divr_Wbism: forall r, Divr r -> forall r0, Wbism r r0 ->
Divr r0. 
Proof. cofix hcoind. move => r0 h0. foo h0.
move => r0 h0. foo h0.
- foo H0. absurd False => //. have := Red_Divr H3 H. by apply. 
- foo H0. absurd False => //. have := Red_Divr H4 H. by apply.
- foo H0. absurd False => //. have := Red_Divr H4 H. by apply.
- apply Divr_delay. have := hcoind _ H _ H1. by apply. 
Qed.   

Inductive Redn: nat -> res -> res -> Type :=
| Redn_ret: forall st, Redn 0  (ret st) (ret st)
| Redn_delay: forall n r0 r1,
  Redn n r0 r1 -> Redn (S n) (delay r0) r1
| Redn_output: forall r0 r1 v,
  Bism r0 r1 ->
  Redn 0 (output v r0) (output v r1) 
| Redn_input: forall f g, 
  (forall x, Bism (f x) (g x)) ->
  Redn 0 (input f) (input g).

Lemma Redn_Setoid: forall n, Setoid2 (Redn n).
Proof. 
apply skip. (* same as for Red *)
Qed.  

Lemma Redn_deterministic: forall n0 r0 r1, Redn n0 r0 r1 ->
forall n1 r2 r3, Redn n1 r2 r3 -> Bism r0 r2 ->
((n0 = n1) * (Bism r1 r3))%type. 
Proof. 
apply skip. (* same as for Redn *) 
Qed.

Lemma Redn_Red: forall n r0 r1, Redn n r0 r1 -> Red r0 r1. 
Proof. 
induction 1. 
- apply Red_ret. 
- have := Red_delay IHRedn. by apply. 
- have := Red_output _ b. by apply. 
- have := Red_input b. by apply. 
Qed.

Lemma Red_Redn: forall r0 r1, Red r0 r1 -> {n: nat & Redn n r0 r1}.
Proof. induction 1. 
- exists 0. apply Redn_ret.
- move: IHRed => [n0 h0]. exists (S n0). 
  have := Redn_delay h0. by apply. 
- exists 0. apply Redn_output. done. 
- exists 0. by apply Redn_input. 
Qed.   

Lemma Redn_ret_Wbism: forall r0 n0 st0,
Redn n0 r0 (ret st0) -> forall r1, Wbism r0 r1 ->
{n1: nat & Redn n1 r1 (ret st0)}.     
Proof.  apply skip. (* Proved in Prop *) Qed. 

Lemma Redn_input_Wbism: forall r0 n0 f0, Redn n0 r0 (input f0) ->
forall r2, Wbism r0 r2 -> 
{n1: nat & {f1: val -> res &
(Redn n1 r2 (input f1) * (forall v, Wbism (f0 v) (f1 v)))%type}}.   
Proof. apply skip. (* Proved in Prop *) Qed.  

Lemma Redn_output_Wbism: forall n0 r0 v0 r1, 
Redn n0 r0 (output v0 r1) ->
forall r2, Wbism r0 r2 -> 
{ n1: nat & {r3: res &
  (Redn n1 r2 (output v0 r3) * Wbism r1 r3)%type}}. 
Proof. apply skip. (* Proved in Prop *) Qed. 

Lemma Bism_botbot: Bism bot bot.
Proof.
cofix hcoind. rewrite [bot]io_destr; simpl. 
have := Bism_delay hcoind. by apply. 
Qed. 
 

Lemma Wbism_retret: forall st0 st1,
Wbism (ret st0) (ret st1) -> st0 = st1. 
Proof.
move => st0 st1 h0. foo h0. 
- foo H; foo H0. reflexivity. 
- foo H. 
- foo H. 
Qed. 

Lemma Wbism_retoutput: forall st0 v0 r0,
Wbism (ret st0) (output v0 r0) -> False.
Proof.
move => st0 v0 r0 h0; foo h0. 
- foo H0. 
- foo H. 
- foo H. 
Qed. 

Lemma Wbism_retinput: forall st0 f0,
Wbism (ret st0) (input f0) -> False.
Proof.
move => st0 f0 h0. foo h0. 
- foo H0. 
- foo H. 
- foo H.
Qed. 

Lemma Wbism_outputoutput: forall v0 r0 v1 r1,
Wbism (output v0 r0) (output v1 r1) ->
((v0 = v1) * Wbism r0 r1)%type. 
Proof. 
move => v0 r0 v1 r1 h0. foo h0.
- foo H. 
- foo H. foo H0. split. reflexivity. have := Wbism_Setoid H1 (Bism_sym H3)
  (Bism_sym H2). by apply. 
- foo H0.    
Qed. 

Lemma Wbism_outputinput: forall v0 r0 f0,
Wbism (output v0 r0) (input f0) -> False.
Proof.
move => v0 r0 f0 h0. foo h0. 
- foo H. 
- foo H0. 
- foo H.
Qed. 

Lemma Wbism_inputinput: forall f0 f1,
Wbism (input f0) (input f1) -> 
forall v, Wbism (f0 v) (f1 v). 
Proof.
move => f0 f1 h0 v. foo h0. 
- foo H. 
- foo H. 
- foo H. foo H0. have := Wbism_Setoid (H1 v) (Bism_sym (H4 v))
  (Bism_sym (H3 v)). by apply. 
Qed.

Lemma Red_bot: forall r0, Red bot r0 -> False.
Proof. 
have: forall r0 r1, Red r0 r1 -> Bism r0 bot -> False. 
* induction 1; rewrite [bot]io_destr; simpl; move => h0; try foo h0. 
  - have := IHRed H2. by apply. 
  - move => h0 r0 h1. have := h0 _ _ h1 (Bism_refl _). by apply. 
Qed.   

Lemma Wbism_botret: forall st, Wbism bot (ret st) -> False. 
Proof.
move => st0 h0. foo h0.
- have := Red_bot H. by apply. 
- foo H0. 
- foo H0. 
Qed. 

Lemma Wbism_botinput: forall f, Wbism bot (input f) -> False.
Proof.
move => f0 h0. foo h0. 
- foo H0.  
- foo H0. 
- have := Red_bot H. by apply. 
Qed.

Lemma Wbism_botoutput: forall v r, Wbism bot (output v r) -> False.
Proof.
move => v0 r0 h0. foo h0. 
- foo H0. 
- have := Red_bot H. by apply. 
- foo H0. 
Qed. 

Lemma Wbism_ret_Red: forall st0 r0,
Wbism (ret st0) r0 -> Red r0 (ret st0).
Proof. 
move => st0 r0 h0. foo h0. 
- foo H.  apply H0. 
- foo H. 
- foo H. 
Qed. 

Lemma Wbism_input_Red: forall f0 r0,
Wbism (input f0) r0 ->
{f1: val -> res & (Red r0 (input f1) * (forall v,  Wbism (f0 v) (f1 v)))%type}.
Proof.
move => f0 r0 h0. foo h0. 
- foo H. 
- foo H. 
- foo H. exists f2. split; first done. move => v.
  have := Wbism_Setoid (H1 v) (Bism_sym (H4 v)) (Bism_refl _). 
  by apply. 
Qed. 

Lemma Wbism_output_Red: forall v0 r0 r1,
Wbism (output v0 r0) r1 ->
{r2: res & (Red r1 (output v0 r2) * Wbism r0 r2)%type}.
Proof.
move => v0 r0 r1 h0. foo h0. 
- foo H. 
- foo H. exists r1'. split; first done. have := Wbism_Setoid H1
  (Bism_sym H3) (Bism_refl _). by apply. 
- foo H.  
Qed.

Lemma Bism_Wbismc: forall r0 r1, Bism r0 r1 -> Wbismc r0 r1. 
Proof.
move => r0 r1 h0. have := Wbism_Wbismc (Bism_Wbism h0). 
by apply. 
Qed.


Lemma Wbism_bot: forall r, Wbism bot r -> Bism bot r.
Proof.
cofix hcoind. move => r0 h0. foo h0; 
try (by absurd False; [ done | have := Red_bot H; apply]).
- rewrite [bot]io_destr in H; simpl in H. foo H. 
  have := Bism_delay (hcoind _ H0). by apply. 
Qed.  


Inductive Steps: res -> res -> Type :=
| Steps_stop: forall r0 r1, Bism r0 r1 -> Steps r0 r1
| Steps_delay: forall r0 r1, Steps r0 r1 ->
  Steps (delay r0) r1. 

Lemma Red_Steps: forall r0 r1,
Red r0 r1 -> Steps r0 r1.
Proof.
induction 1. 
- have := Steps_stop (Bism_ret _). by apply. 
- have := Steps_delay IHRed.  by apply. 
- have := Steps_stop (Bism_output _ b). by apply. 
- have := Steps_stop (Bism_input b). by apply. 
Qed. 

Lemma Steps_Wbismi: forall r0 r1, Steps r0 r1 ->
forall X, Setoid2 X -> 
forall r2, Wbismi X r2 r1 ->
Wbismi X r2 r0.
induction 1. 
- move => X h0 r2 h1.  
  have := Wbismi_Setoid h0 h1 (Bism_refl _) (Bism_sym b).
  by apply. 
- move => X hsetoid r2 h1. have h0 := IHSteps _ hsetoid _ h1 => {hsetoid h1}.
  have := Wbismi_delay_R h0. by apply. 
Qed.   

Lemma Wbismi_Steps_append: forall r0 r1,
Steps r0 r1 ->
forall X, Setoid2 X ->  
forall r2 r3, Wbismi X r2 (append r1 r3) ->
Wbismi X r2 (append r0 r3).
Proof.
induction 1.
- move => X h0 r2 r3 h1. have := Wbismi_Setoid h0 h1 
  (Bism_refl _) (append_Setoid (Bism_sym b) (Bism_refl _)).
  by apply. 
- move => X h0 r2 r3 h1. rewrite [append _ _]io_destr; simpl. 
  have h2 := IHSteps _ h0 _ _ h1. 
  have := Wbismi_delay_R h2. by apply.  
Qed.

(* responsiveness *)
CoInductive Resp: res -> Type :=
| Resp_ret: forall n r st, 
  Redn n r (ret st) -> Resp r
| Resp_input: forall n r f,
  Redn n r (input f) ->
  (forall x, Resp (f x)) ->  
  Resp r
| Resp_output: forall n v r0 r1,
  Redn n r0 (output v r1) ->
  Resp r1 ->
  Resp r0.

Lemma Resp_setoid: Setoid Resp. 
Proof. 
cofix hcoind. case.
- move => st0 h0 r1 h1. foo h1. have := Resp_ret (Redn_ret st0). by apply. 
- move => v0 r0 h0 r1 h1. foo h1. foo h0. foo H. foo H. foo H. 
  have := Resp_output (Redn_output _ (Bism_refl _)) (hcoind _ H0 _  
  (Bism_trans (Bism_sym H4) H2)). by apply. 
- move => f h0 r0 h1. foo h1. foo h0. foo H. foo H. 
  have := Resp_input (Redn_input (fun v => (Bism_refl _))) 
  (fun v => hcoind _ (H1 v)
  _  (Bism_trans (Bism_sym (H5 v)) (H0 v))). by apply.  foo H. 
- move => r0 h0 r1 h1. foo h1. foo h0. 
  - have := Resp_ret (Redn_Setoid H (Bism_delay H0) (Bism_refl _)).
    by apply. 
  - have := Resp_input (Redn_Setoid H (Bism_delay H0) (Bism_refl _)). 
    by apply. 
  - have := Resp_output (Redn_Setoid H (Bism_delay H0) (Bism_refl _)). 
    by apply.         
Qed.

CoInductive Commit: res -> Type :=
| Commit_ret: forall n r st, 
  Redn n r (ret st) ->
  Commit r
| Commit_input: forall n r f,
  Redn n r (input f) ->
  (forall x, Commit (f x)) ->  
  Commit r
| Commit_output: forall n v r0 r1,
  Redn n r0 (output v r1) ->
  Commit r1 ->
  Commit r0
| Commit_divr: forall r,
  Divr r -> Commit r.

Lemma Commit_Setoid: Setoid Commit. 
Proof. cofix hcoind. rewrite /Setoid. move => r0 h0. foo h0. 
- move => r1 h0. have := Redn_Setoid H h0 (Bism_refl _).
  move => h1. have := Commit_ret h1. apply. 
- move => r1 h0. have := Redn_Setoid H h0 (Bism_refl _).
  move => h1. have := Commit_input h1 H0. apply.
- move => r1 h0. have := Redn_Setoid H h0 (Bism_refl _).
  move => h1. have := Commit_output h1 H0. apply.
- move => r1 h0. have := Divr_Setoid H h0. move => h1. 
  have := Commit_divr h1. by apply. Qed.    
 

Lemma Redn_nodelay: forall n0 r0 r1, Redn n0 r0 (delay r1) -> False. 
Proof. 
have h: forall n0 r0 r1, Redn n0 r0 r1 -> 
forall r2, Bism r1 (delay r2) -> False.
* induction 1. 
  - move => r0 h0. foo h0.
  - move => r2 h0. foo h0. have := IHRedn _ (Bism_delay H2). by apply. 
  - move => r2 h0. foo h0. 
  - move => r2 h0. foo h0. 
move => n0 r0 r1 h0. have := h _ _ _ h0 _ (Bism_refl _). apply. 
Qed. 

(* Classically, [commit]tedness is a tautology.*)

Axiom toss: forall r,
sum ({n: nat & {r0: res & Redn n r r0}}) (Divr r).

Lemma Commit_tautology: forall r, Commit r. 
Proof.
cofix hcoind. move => r.
have [[n0 [r0 h0]] | h0] := toss r.
- destruct r0. 
  - have := Commit_ret h0. by apply. 
  - have := Commit_output h0 (hcoind _). by apply. 
  - have := Commit_input h0 (fun v => hcoind _). by apply.
  - absurd False => //. have := Redn_nodelay h0. by apply. 
- have := Commit_divr h0. by apply.
Qed. 

(* Mendler trick costs us impredicativity *) 
Axiom wbism_Wbism: forall r0 r1, wbism r0 r1 -> Wbism r0 r1. 

     
