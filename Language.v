Require Import ssreflect.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition id := Z.
Definition val := nat.
Definition state := id -> val. 

Definition expr := state -> val.
Parameter is_true: val -> bool. 

Inductive stmt : Set :=
| Sskip | Sassign (_ :id) (_: expr) | Sseq (_: stmt) (_ :stmt)
| Sifthenelse (_: expr) (_: stmt) (_: stmt)
| Swhile (_: expr) (_ :stmt)
| Swrite (_:expr) | Sread (_:id).

Definition update (x: id) (v: val) (st:state): state :=
  fun y => if Zeq_bool x  y  then v  else st y.

Notation "x <- e" := (Sassign x e) (at level 80).
Notation "s1 ';;' s2" := 
  (Sseq s1 s2) (at level 80, right associativity).
