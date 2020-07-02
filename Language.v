Require Import SsrExport.
Require Import Trace.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition expr := state -> val.
Parameter is_true: val -> bool. 

Inductive stmt : Set :=
| Sskip | Sassign (_ :id) (_: expr) | Sseq (_: stmt) (_ :stmt)
| Sifthenelse (_: expr) (_: stmt) (_: stmt)
| Swhile (_: expr) (_ :stmt).

Definition update (x: id) (v: val) (st:state): state :=
  fun y => if Zeq_bool x  y  then v  else st y.

