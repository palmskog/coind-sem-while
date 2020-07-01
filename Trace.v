Require Import ssreflect. 
Require Export ZArith.
Require Export List.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Ltac foo h := inversion h; subst => {h}.

Definition id := Z.
Definition val := Z.
Definition state := id -> val. 

CoInductive trace: Set := | Tnil (_: state) | Tcons (_: state) (_: trace) .

Definition trace_decompose (tr: trace): trace :=
match tr with
| Tnil st => Tnil st
| Tcons a tr' => Tcons a tr'
end. 

Lemma trace_destr:
forall tr, tr = trace_decompose tr.
Proof. case => //=. Qed.  

(* bisimilarity of two traces *)
CoInductive bisim: trace -> trace -> Set :=
| bisim_nil: forall st,
  bisim (Tnil st) (Tnil st)
| bisim_cons: forall e tr tr',
  bisim tr tr' ->
  bisim (Tcons e tr) (Tcons e tr').

(* Bisimilarity is reflexive *) 
Lemma bisim_reflexive: forall tr, bisim tr tr. 
Proof. 
cofix COINDHYP. case.
- move => st. by apply bisim_nil. 
- move => st tr. by have := bisim_cons _ (COINDHYP _); apply.  
Qed. 

(* Bisimilarity is symmetric *)
Lemma bisim_symmetric: forall tr1 tr2, bisim tr1 tr2 -> bisim tr2 tr1. 
Proof.
cofix COINDHYP. case. 
- move => s tr2 h1. foo h1.  by apply: bisim_nil.  
- move => s tr0 tr1 h1. foo h1. 
  by have := bisim_cons _ (COINDHYP _ _ H2); apply.
Qed.   

(* Bisimilarity is trnasitive *)
Lemma bisim_transitive: forall tr1 tr2 tr3,
bisim tr1 tr2 -> bisim tr2 tr3 -> bisim tr1 tr3. 
Proof.
cofix COINDHYP. case.  
- move => st tr0 tr1 h1 h2. foo h1. foo h2. by apply: bisim_nil.
- move => st tr0 tr1 tr2 h1 h2. foo h1. foo h2. 
  by have := bisim_cons _ (COINDHYP _ _ _ H2 H3); apply.  
Qed.    


CoFixpoint trace_append (tr tr': trace): trace :=
match tr with
| Tnil st => tr'
| Tcons e tr0 => Tcons e (trace_append tr0 tr')
end. 

Infix "+++" := trace_append (at level 60, right associativity).

Lemma trace_append_nil: forall st tr,
(Tnil st) +++ tr = tr.
Proof. 
move => st tr. rewrite [Tnil st +++ tr]trace_destr. by case tr; simpl. 
Qed. 
   
Lemma trace_append_cons: forall e tr tr',
(Tcons e tr) +++ tr' = Tcons e (tr +++ tr').
Proof.
move => st tr tr'. rewrite [Tcons st tr +++ tr']trace_destr. by case tr; simpl.
Qed.

Lemma trace_eq_append: forall tr1 tr2 tr3 tr4, 
bisim tr1 tr2 -> bisim tr3 tr4 -> bisim (tr1 +++ tr3) (tr2 +++ tr4).
Proof. 
cofix COINDHYP. case. 
- move => st1 tr1 tr2 tr3 h1 h2. foo h1.
  do 2 rewrite trace_append_nil. by apply: h2. 
- move => st tr1 tr2 tr3 tr4 h1 h2. foo h1. 
  do 2 rewrite trace_append_cons.
  have := bisim_cons _ (COINDHYP _ _ _ _ H2 h2); apply.
Qed. 

  
