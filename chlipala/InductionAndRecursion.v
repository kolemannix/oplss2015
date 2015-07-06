(* We start with a boring input of 2 standard-library modules that we'll use. *)
Require Import Coq.Unicode.Utf8 Arith String.


(** * A good example of general inductive types: syntax trees for a small programming language *)

(** Specifically, here's a type of simple trees of arithmetic operations on natural numbers.
  * [nat] is Coq's type for natural numbers, defined in the standard library.
  * (More on those below!) *)
Inductive exp : Set :=
| Constant : nat -> exp
| Plus : exp -> exp -> exp
| Times : exp -> exp -> exp.

(** Recursive function to evaluate an arithmetic expression to a number. *)
Fixpoint eval (e : exp) : nat :=
  match e with
  | Constant n => n
  | Plus e1 e2 => eval e1 + eval e2
  | Times e1 e2 => eval e1 * eval e2
  end.

(** A mischievous function to swap the operands of all operators *)
Fixpoint commuter (e : exp) : exp :=
  match e with
    | Constant _ => e
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

(** We of course want to be *proving* theorems about these definitions,
  * but let's back up and look at a more basic type first. *)


(** * The most basic inductive type that actually deserves the name: natural numbers *)

(** Let's define these with different names than usual, to avoid clashing with the standard library. *)
Inductive natural : Set :=
| Zero : natural
| Succ : natural -> natural.
(* [Succ] for "successor".  Any number [n] is represented as [Succ^n(Zero)]. *)

(** Addition is easy to define recursively.  Here's we're working from first principles, instead of using a built-in type of machine numbers as in most programming languages. *)
Fixpoint add (n m : natural) : natural :=
  match n with
  | Zero => m
  | Succ n' => Succ (add n' m)
  end.

(** Our first example of a proof!  Addition is associative. *)
Theorem add_assoc : forall n m o, add (add n m) o = add n (add m o).
Proof.
  (** Here we are writing *tactics*, or commands for reducing one proof goal into zero or more new goals.  In general, we use semicolon to sequence tactics, with each step run on all goals left over after the previous steps.  We use periods to terminate tactics that we want to run interactively to see the results. *)
  induction n; simpl; intros.
  (**
    * You can guess what [induction] means.
    * [simpl] triggers algebraic simplification.
    * [intros] replaces [forall] quantifiers with new free variables. *)

  reflexivity.
  (** [reflexivity] proves any goal of the form [E = E]. *)

  rewrite IHn.
  (** [rewrite H] uses hypothesis or lemma [H] establishing some fact [E1 = E2] to replace all occurrences of [E1] in the goal with [E2]. *)
  reflexivity.
Qed.
(** If the [Qed] command succeeds, then we know that the theorem is really true, regardless of which tactics we chose. *)

(** ** Proving commutativity of addition *)

(** Sometimes it's useful to prove some lemmas, which formally are the same as theorems, but using the name "lemma" signifies that they just play a supporting role. *)

(** Lemma #1: zero is a right identity of addition. *)
Lemma add_Zero : forall n, add n Zero = n.
Proof.
  induction n; simpl.

  reflexivity.

  rewrite IHn.
  reflexivity.
Qed.

(** Lemma #2: we can pull a [Succ] from the 2nd operand to the front. *)
Lemma add_Succ : forall n m, add n (Succ m) = Succ (add n m).
Proof.
  induction n; simpl; intros.

  reflexivity.

  rewrite IHn.
  reflexivity.
Qed.

(** The main event! *)
Theorem add_comm : forall n m, add n m = add m n.
Proof.
  induction n; simpl; intros.

  rewrite add_Zero.
  reflexivity.

  rewrite add_Succ.
  rewrite IHn.
  reflexivity.
Qed.

(** In the other examples, we'll show both these more manual proofs and more automated proofs.  For natural numbers, it's not even worth doing the automated proofs, since Coq has built-in automation for goals like these, when we use the [nat] type from the standard library. *)


(** * Now we're ready to go back and prove properties of expressions. *)

(** [commuter] has no effect on the meaning of an expression. *)
Theorem eval_commuter : forall e, eval (commuter e) = eval e.
Proof.
  induction e; simpl; intros.

  reflexivity.

  rewrite IHe1.
  rewrite IHe2.
  rewrite plus_comm.
  reflexivity.

  rewrite IHe1.
  rewrite IHe2.
  rewrite mult_comm.
  reflexivity.
Qed.


(** ** Let's see how we can automate that proof more thoroughly using Coq's language Ltac for scripted proof automation.  In general, Ltac details are beyond the scope of these lectures, so think of these automated examples as an advertisement for learning more, say via Adam's book "Certified Programming with Dependent Types," and/or the Coq reference manual. *)

Ltac exp_solver := simpl; intuition;
                   repeat match goal with
                          | [ H : _ = _ |- _ ] => rewrite H
                          end; intuition.

Theorem eval_commuter_automated : forall e, eval (commuter e) = eval e.
Proof.
  induction e; exp_solver.
Qed.


(** * Next (and final) example: lambda terms *)

(** Here's the syntax of the untyped lambda calculus, using the library type of strings. *)
Inductive term : Set :=
| Var : string -> term
| Abs : string -> term -> term
| App : term -> term -> term.

(** At this point, we might be tempted to begin by writing an interpreter, but we can't, since Coq only allows *terminating* functional programs!  Let's work with substitution instead. *)
Fixpoint subst (rep : term) (x : string) (e : term) : term :=
  match e with
  | Var y => if string_dec y x then rep else Var y
  | Abs y e1 => Abs y (if string_dec y x then e1 else subst rep x e1)
  | App e1 e2 => App (subst rep x e1) (subst rep x e2)
  end.
(** Warning: this version is only designed for [rep] that are *closed*, with no free variables! *)

(** In Coq, [Prop] is the type of propositions, or mathematical statements.  It's subtlely different from the type [bool] of Booleans, in a way that may be clear from the OPLSS lectures on type-theory foundations, but it's also fine (for now) to pretend that [Prop] is just a peculiar kind of truth value or Boolean, with its own distinctive operators.  Let's define what it means for a variable not to appear free in a term.  We write [<>] for not-equal, [\/] for logical "or," and [/\] for logical "and." *)
Fixpoint notFreeIn (x : string) (e : term) : Prop :=
  match e with
  | Var y => y <> x
  | Abs y e1 => y = x \/ notFreeIn x e1
  | App e1 e2 => notFreeIn x e1 /\ notFreeIn x e2
  end.

(** We'd like to prove that the order of substitution operations doesn't matter, when the terms we are substituting ([rep] parameter in the [subst] definition) have no free variables.  A useful first lemma is that substitution has no effect on a term without free occurrences of the variable. *)
Lemma subst_notFree : forall rep x e,
  notFreeIn x e
  -> subst rep x e = e.
Proof.
  induction e; simpl; intros.

  destruct (string_dec s x).
  (** [destruct] is for case analysis on the ways some term might be constructed.
    * In this case, [string_dec] has a funny expressive Boolean type that we won't dwell on.
    * The two cases considered are basically "true" and "false," extending the context with information on what the case implies logically about the arguments to [string_dec]. *)
  congruence.
  (** [congruence] is a general decision procedure for the theory of equality.
    * For instance, it knows that [a = b] and [b <> a] together are inconsistent, establishing any goal by contradiction.
    * Though [congruence] subsumes [reflexivity], we'll keep using the latter where applicable, for clarity. *)
  reflexivity.

  destruct (string_dec s x).
  reflexivity.
  (** [destruct] also does double-duty when applied to an [\/] ("or") hypothesis, splitting out two goals, one for each branch of the "or." *)
  destruct H.
  congruence.
  
  rewrite IHe.
  reflexivity.
  assumption.

  (** [destruct] will also split an [/\] ("and") hypothesis into two. *)
  destruct H.
  rewrite IHe1.
  rewrite IHe2.
  reflexivity.
  assumption.
  assumption.
Qed.

(** Now we prove the main fact about commutativity of substitution. *)
Theorem subst_comm : forall rep1 x1 rep2 x2 e,
  (* The two replacements have no free variables: *)
  (forall x, notFreeIn x rep1)
  -> (forall x, notFreeIn x rep2)

  (* It's important to require that the two variables are different! *)
  -> x1 <> x2

  -> subst rep1 x1 (subst rep2 x2 e) = subst rep2 x2 (subst rep1 x1 e).
Proof.
  induction e; simpl; intros.

  destruct (string_dec s x1), (string_dec s x2); simpl.
  congruence.
  destruct (string_dec s x1).
  rewrite subst_notFree.
  reflexivity.
  apply H.
  (* [apply H] works to prove [P] when [H] is a hypothesis or lemma that establishes [P], perhaps given some other premises.  Those premises become new goals. *)
  congruence.
  destruct (string_dec s x2).
  rewrite subst_notFree.
  reflexivity.
  apply H0.
  congruence.

  destruct (string_dec s x1), (string_dec s x2); simpl.
  congruence.
  congruence.
  congruence.
  reflexivity.

  destruct (string_dec s x1), (string_dec s x2); simpl.
  congruence.
  congruence.
  congruence.
  rewrite IHe.
  reflexivity.
  assumption.
  (* It's probably not hard to guess what [assumption] does. :-) *)
  assumption.
  assumption.

  rewrite IHe1.
  rewrite IHe2.
  reflexivity.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

(** That was painfully repetitive proving.  Here's an Ltac script that can eat the whole thing for breakfast. *)

Ltac subst_solver := simpl; intuition;
                     repeat (match goal with
                             | [ H : _ = _ |- _ ] => rewrite H
                             | [ |- context[string_dec ?X ?Y] ] => destruct (string_dec X Y)
                             end; simpl in *; intuition; try congruence).

Lemma subst_notFree_automated : forall rep x e,
  notFreeIn x e
  -> subst rep x e = e.
Proof.
  induction e; subst_solver.
Qed.

Hint Resolve subst_notFree_automated.
(** We register a proved lemma as a hint, to be used automatically by the tactics we call in [subst_solver].  (It turns out to be [intuition] that is using the hints here; details are beyond the scope of these lectures.) *)

(** It will be helpful to prove a mirror-image hint, too. *)
Lemma subst_notFree_automated_sym : forall rep x e,
  notFreeIn x e
  -> e = subst rep x e.
Proof.
  intros; symmetry; auto.
Qed.

Hint Resolve subst_notFree_automated_sym.

(** Now the main theorem is a piece of cake. *)
Theorem subst_comm_automated : forall rep1 x1 rep2 x2 e,
  (forall x, notFreeIn x rep1)
  -> (forall x, notFreeIn x rep2)
  -> x1 <> x2
  -> subst rep1 x1 (subst rep2 x2 e) = subst rep2 x2 (subst rep1 x1 e).
Proof.
  induction e; subst_solver.
Qed.