Require Import Arith Omega String.

Inductive exp : Set :=
| Var : string -> exp
| Const : nat -> exp
| Plus : exp -> exp -> exp
| Times : exp -> exp -> exp.

Fixpoint eval (e : exp) (f : string -> nat) : nat :=
  match e with
    | Var x => f x
    | Const n => n
    | Plus e1 e2 => eval e1 f + eval e2 f
    | Times e1 e2 => eval e1 f * eval e2 f
  end.

Fixpoint cfold (e : exp) : exp :=
  match e with
    | Var x => Var x
    | Const n => Const n
    | Plus e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
        | Const n1, Const n2 => Const (n1 + n2)
        | Const 0, _ => e2'
        | _, Const 0 => e1'
        | _,  _ => Plus e1' e2'
      end
    | Times e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
        | Const n1, Const n2 => Const (n1 * n2)
        | Const 1, _ => e2'
        | _, Const 1 => e1'
        | Const 0, _ => Const 0
        | _, Const 0 => Const 0
        | _,  _ => Times e1' e2'
      end
  end.

Fixpoint cfold' (e : exp) : exp :=
  match e with
    | Var x => Var x
    | Const n => Const n
    | Plus e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
        | Const n1, Const n2 => Const (n1 + n2)
        | Const 0, _ => e2'
        | _, Const 0 => e1'
        | _,  _ => Plus e1' e2'
      end
    | Times e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
        | Const n1, Const n2 => Const (n1 * n2)
        | Const 1, _ => e2'
        | _, Const 1 => e1'
        | Const 0, _ => Const 0
        | _, Const 0 => Const 0
        | _,  _ => Times e1' e2'
      end
  end.

Hint Extern 1 (_ = _) => omega.

Theorem cfold_ok : forall f e, eval (cfold e) f = eval e f.
Proof.
  induction e; simpl; intuition;
  repeat match goal with
           | [ |- context[match ?E with _ => _ end] ] =>
             destruct E; simpl in *; subst; auto
         end.
Qed.
