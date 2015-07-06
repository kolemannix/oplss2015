Require Import String Arith.

Inductive exp : Set :=
  | SLit : string -> exp
  | NLit : nat -> exp
  | Plus : exp -> exp -> exp
  | Times : exp -> exp -> exp.

Fixpoint eval (e: exp) (f: string -> nat): nat :=
  match e with
    | SLit s => f s
    | NLit n => n
    | Plus e1 e2 => (eval e1 f) + (eval e2 f)
    | Times e1 e2 => (eval e1 f) * (eval e2 f)
  end.

Open Scope string_scope.
Definition exampleF (s: string): nat :=
  match s with
    | "x" => 1
    | "y" => 2
    | "z" => 3
    | _ => 0
  end.

Fixpoint optimize (e: exp): exp :=
  match e with
    | Plus e1 (NLit 0) => (optimize e1)
    (* | Plus (NLit n) (NLit m) => (NLit (n + m)) *)
    | Times (NLit 0) e2 => (NLit 0)
    | _ => e
  end.

Require Import Omega.

Ltac solve_exp := repeat match goal with
                           | _ =>  progress simpl
                           | [  |- ?a = ?a ] => reflexivity
                           | [  |- context[match ?blah with _ => _ end]] => destruct blah
                           | [ H: ?a = ?b |- context[?a] ] => rewrite H; clear H
                           | _ => omega
                         end.

Theorem optimize_correct: forall e f, eval e f = eval (optimize e) f.
Proof.
  intros e f.
  induction e; solve_exp.
Qed.
