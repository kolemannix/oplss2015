Require Import Coq.Unicode.Utf8 Arith FunctionalExtensionality String Coq.Program.Equality.

Set Implicit Arguments.

(** * BEGIN BLACK MAGIC (Ltac details beyond the scope of this lecture, to define some tactics that will be handy, extending built-in tactics) *)

(** * Here lies some black magic to define a smarter version of the normal [induction] tactic.
    * Details are beyond the scope of the lecture! *)
Ltac inductN n :=
  match goal with
    | [ |- forall x : ?E, _ ] =>
      match type of E with
        | Prop =>
          let H := fresh in intro H;
            match n with
              | 1 => dependent induction H
              | S ?n' => inductN n'
            end
        | _ => intro; inductN n
      end
  end.

Ltac induct e := inductN e || dependent induction e.

Ltac invert' H := inversion H; clear H; subst.

Ltac invertN n :=
  match goal with
    | [ |- forall x : ?E, _ ] =>
      match type of E with
        | Prop =>
          let H := fresh in intro H;
            match n with
              | 1 => invert' H
              | S ?n' => invertN n'
            end
        | _ => intro; invertN n
      end
  end.

Ltac invert e := invertN e || invert' e.
Ltac invert1 e := invert e; [].

(** * END BLACK MAGIC *)


(** * Transitive-reflexive closure of a relation, from last time *)

Inductive star A (R : A -> A -> Prop) : A -> A -> Prop :=
| StarRefl : forall x,
  star R x x
| StarStep : forall x1 x2 x3,
  R x1 x2
  -> star R x2 x3
  -> star R x1 x3.


(** Difference here? *)
Inductive star'' A (R : A -> A -> Prop) : A -> A -> Prop :=
| StarRefl'' : forall x x',
  x = x' -> star'' R x x'
| StarStep'' : forall x1 x2 x3,
  R x1 x2
  -> star'' R x2 x3
  -> star'' R x1 x3.

(** * Arithmetic expressions *)
Module Arithmetic.
  (** As a warm-up, let's prove type safety for simple arihmetic expresions with naturals and Booleans. *)

  (** Here's the language of terms. *)
  Inductive exp : Set :=
  | Number : nat -> exp
  | Plus : exp -> exp -> exp
  | Minus : exp -> exp -> exp
  | Boolean : bool -> exp
  | Equal : exp -> exp -> exp
  | If : exp -> exp -> exp -> exp.

  (** This next relation identifies which subset of terms are *values*, meaning they need not be evaluated further to produce a final result. *)
  Inductive value : exp -> Prop :=
  | VNumber : forall n, value (Number n)
  | VBoolean : forall b, value (Boolean b).

  (** Here's a simple small-step semantics, not taking advantage of evaluation contexts. *)

  Reserved Notation " a ==> b " (at level 60, right associativity).
  
  Inductive step : exp -> exp -> Prop :=
  | StepPlus : forall n1 n2,
    (Plus (Number n1) (Number n2)) ==> (Number (n1 + n2))
  | StepPlus1 : forall e1 e1' e2,
    e1 ==> e1'
    -> (Plus e1 e2) ==> (Plus e1' e2)
  | StepPlus2 : forall e1 e2 e2',
    value e1
    -> e2 ==> e2'
    -> (Plus e1 e2) ==> (Plus e1 e2')
  | StepMinus : forall n1 n2,
                  (Minus (Number n1) (Number n2)) ==> (Number (n1 - n2))
  | StepMinus1 : forall e1 e1' e2,
                   e1 ==> e1' ->
                   (Minus e1 e2) ==> (Minus e1' e2)
  | StepMinus2 : forall e1 e2 e2',
                   value e1 ->
                   e2 ==> e2' ->
                   (Minus e1 e2) ==> (Minus e1 e2')
  | StepEqual : forall n1 n2,
    (Equal (Number n1) (Number n2)) ==> (Boolean (beq_nat n1 n2))
  | StepEqual1 : forall e1 e1' e2,
    e1 ==> e1'
    -> (Equal e1 e2) ==> (Equal e1' e2)
  | StepEqual2 : forall e1 e2 e2',
    value e1
    -> e2 ==> e2'
    -> (Equal e1 e2) ==> (Equal e1 e2')
  | StepIfTrue : forall e2 e3,
    (If (Boolean true) e2 e3) ==> e2
  | StepIfFalse : forall e2 e3,
    (If (Boolean false) e2 e3) ==> e3
  | StepIf1 : forall e1 e1' e2 e3,
    e1 ==> e1'
    -> (If e1 e2 e3) ==> (If e1' e2 e3)
  where " a ==> b " := (step a b).

  (** Our simple set of two types helps us classify expressions. *)
  Inductive ty : Set :=
  | Nat : ty
  | Bool : ty.

  (** Here's the typing judgment, relating expressions and their types.
      A :: B is read as "A has type B" *)
  Inductive hasType : exp -> ty -> Prop :=
  | HtNumber : forall n, (Number n) :: Nat
  | HtPlus : forall e1 e2, e1 :: Nat
    -> e2 :: Nat
    -> (Plus e1 e2) :: Nat
  | HTMinus : forall e1 e2, e1 :: Nat
    -> e2 :: Nat
    -> (Minus e1 e2) :: Nat
  | HtBoolean : forall b, (Boolean b) :: Bool
  | HtEqual : forall e1 e2, e1 :: Nat
    -> e2 :: Nat
    -> (Equal e1 e2) :: Bool
  | HtIf : forall e1 e2 e3 t, e1 :: Bool
    -> e2 :: t
    -> e3 :: t
    -> (If e1 e2 e3) :: t
  where "a :: b" := (hasType a b).

  (** Next, some hints and tactic definitions whose details are beyond the scope of this lecture, but which will help us do nice automated proofs below *)
  
  Hint Constructors step value hasType.

  Ltac t0 := match goal with
             | [ H : ex _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H

             | [ |- context[step (If (Boolean ?x) _ _) _] ] => is_var x; destruct x
             | [ H : hasType ?e _, H' : value ?e |- _ ] => invert H'; invert H
             | [ H : hasType _ _ |- _ ] => invert1 H
             end; subst.

  Ltac t := simpl; intuition; repeat t0; eauto.

  (** We are going to prove that "has type t" is an invariant, during the small-step evaluation of a term of that type.  The *progress* property is one half of the invariant proof: a term satisfying the invariant is either already a value or can take a step. *)
  Lemma progress : forall e t, e :: t
    -> value e
       \/ (exists e', e ==> e').
  Proof.
    induction 1; t.
  Qed.

  (** Here's the other half of the inavriant proof: *preservation* says that the invariant is closed under taking a step. *)
  Lemma preservation : forall e1 e2, e1 ==> e2
    -> forall t, e1 :: t
    -> e2 :: t.
  Proof.
    induction 1; t.
  Qed.

  Hint Resolve progress preservation.

  (** Together, they imply this key property: any term reachable by stepping from a well-typed term is *not stuck*, meaning that either it's a value or it can take a step. *)
  Theorem safety : forall e1 e2, star step e1 e2
    -> forall t, e1 :: t
    -> value e2 \/ (exists e3, e2 ==> e3).
  Proof.
    induct 1; t.
  Qed.

  (** Note that this style of type safety adapts very naturally to a broad range of languages, including those whose step relations are nondeterministic, though we won't look at any such examples in these lectures. *)
End Arithmetic.


(** * Simply typed lambda calculus *)
Module Stlc.
  (** Now we come to one of the classic examples for type soundness proofs: simply typed lambda calculus, where we have one distinguished base type (natural numbers here) and build up function types on top of it. *)

  (** Expression syntax *)
  Inductive exp : Set :=
  | Var : string -> exp
  | Const : nat -> exp
  | Plus : exp -> exp -> exp
  | Abs : string -> exp -> exp
  | App : exp -> exp -> exp.

  (** Values (final results of evaluation) *)
  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1).

  (** Substitution (not applicable when [e1] isn't closed, as before, to avoid some complexity that we don't need) *)

  Reserved Notation "e' [ x |-> a ]" (at level 10).
  
  Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
    match e2 with
      | Var y => if string_dec y x then e1 else Var y
      | Const n => Const n
      | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
      | Abs y e2' => Abs y (if string_dec y x then e2' else subst e1 x e2')
      | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
    end where "e' [ x |-> e ]" := (subst e x e').

  (** Evaluation contexts *)
  Inductive context : Set :=
  | Hole : context
  | Plus1 : context -> exp -> context
  | Plus2 : exp -> context -> context
  | App1 : context -> exp -> context
  | App2 : exp -> context -> context.

  (** Plugging an expression into a context *)

  Reserved Notation " E [ e ] == X " (at level 10).
  
  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, Hole[e] == e
  | PlugPlus1 : forall e e' C e2,
    C[e] == e'
    -> (Plus1 C e2)[e] == (Plus e' e2)
  | PlugPlus2 : forall e e' v1 C,
    value v1
    -> C[e] == e'
    -> (Plus2 v1 C)[e] == (Plus v1 e')
  | PlugApp1 : forall e e' C e2,
    C[e] == e'
    -> (App1 C e2)[e] == (App e' e2)
  | PlugApp2 : forall e e' v1 C,
    value v1
    -> C[e] == e'
    -> (App2 v1 C)[e] == (App v1 e')
  where " E [ e ] == X " := (plug E e X).

  (** Small-step, call-by-value evaluation.  In contrast to the way we did contextual semantics for basic untyped lambda calculus, here we stage the small-step relation as two relations, one capturing primitive steps and the other lifting them to apply inside of contexts. *)

  Reserved Notation "e ==>r e'" (at level 10).
  
  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
    value v
    -> (App (Abs x e) v) ==>r (subst v x e)
  | Add : forall n1 n2,
    (Plus (Const n1) (Const n2)) ==>r (Const (n1 + n2))
  where "e ==>r e'" := (step0 e e').

  
  Inductive step : exp -> exp -> Prop :=
  | Step : forall C e1 e2 e1' e2',
    C[e1] == e1'
    -> C[e2] == e2'
    -> e1 ==>r e2
    -> step e1' e2'.

  Notation "e ==> e'" := (step e e') (at level 10).

  (** Syntax of types *)
  Inductive type : Set :=
  | Nat : type
  | Fun : type -> type -> type.

  (** Our typing judgment uses *typing contexts* (not to be confused with evaluation contexts) to map free variables to their types.  This notation is a convenient way to indicate a typing context that covers no variables. *)
  Notation empty := (fun _ => None).

  (** Here's a function to add a new binding to a typing context, setting the type of variable [x] to be [t]. *)
  Definition override (G : string -> option type) (x : string) (t : type) : string -> option type :=
    fun y => if string_dec y x then Some t else G y.

  (** Expression typing relation *)
  Inductive hasType : (string -> option type) -> exp -> type -> Prop :=
  | HtVar : forall G x t,
    G x = Some t
    -> hasType G (Var x) t
  | HtConst : forall G n,
    hasType G (Const n) Nat
  | HtPlus : forall G e1 e2,
    hasType G e1 Nat
    -> hasType G e2 Nat
    -> hasType G (Plus e1 e2) Nat
  | HtAbs : forall G x e1 t1 t2,
    hasType (override G x t1) e1 t2
    -> hasType G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
    hasType G e1 (Fun t1 t2)
    -> hasType G e2 t1
    -> hasType G (App e1 e2) t2.

  Hint Constructors value plug step0 step hasType.

  (** Two useful facts about [override] *)
  Lemma override_eq : forall G t x t',
    override G x t' x = Some t
    -> t = t'.
  Proof.
    unfold override; intros; destruct (string_dec x x); congruence.
  Qed.

  Lemma override_neq : forall G t x y t',
    override G x t' y = Some t
    -> x <> y
    -> G y = Some t.
  Proof.
    unfold override; intros; destruct (string_dec y x); try congruence.
  Qed.

  (** Some automation *)

  Ltac t0 := match goal with
             | [ H : ex _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ |- context[string_dec ?x ?y] ] => destruct (string_dec x y)
             | [ H : override _ _ _ _ = Some _ |- _ ] => apply override_eq in H
             | [ H : override _ _ _ _ = Some _ |- _ ] => apply override_neq in H; [ | congruence ]

             | [ H : step _ _ |- _ ] => invert H
             | [ H : step0 _ _ |- _ ] => invert1 H
             | [ H : hasType _ ?e _, H' : value ?e |- _ ] => invert H'; invert H
             | [ H : hasType _ _ _ |- _ ] => invert1 H
             | [ H : plug _ _ _ |- _ ] => invert1 H
             end; subst.

  Ltac t := simpl; intuition subst; repeat t0; try congruence; eauto 6.

  (** Now we're ready for the first of the two key properties, to show that "has type t in the empty typing context" is an invariant. *)
  Lemma progress : forall e t,
    hasType empty e t
    -> value e \/ (exists e' : exp, e ==> e').
  Proof.
    induct 1; t.
    (** Here I use [induct] instead of [induction] because the [hasType] premise includes an argument [empty] that isn't just a variable.  Try using [induction] instead to see how information is dropped, counterproductively. *)
  Qed.

  (** Inclusion between typing contexts is preserved by adding the same new mapping to both. *)
  Lemma weakening_override : forall G G' x t,
    (forall x' t', G x' = Some t' -> G' x' = Some t')
    -> (forall x' t', override G x t x' = Some t'
                      -> override G' x t x' = Some t').
  Proof.
    unfold override; t.
  Qed.

  Hint Resolve weakening_override.

  (** Raising a typing derivation to a larger typing context *)
  Lemma weakening : forall G e t,
    hasType G e t
    -> forall G', (forall x t, G x = Some t -> G' x = Some t)
      -> hasType G' e t.
  Proof.
    induct 1; t.
  Qed.

  Hint Resolve weakening.

  Hint Extern 1 (_ = Some _) => cbv beta in *; congruence.

  (** Replacing a typing context with an equal one has no effect (useful to guide proof search). *)
  Lemma hasType_change : forall G e t,
    hasType G e t
    -> forall G', G' = G
      -> hasType G' e t.
  Proof.
    t.
  Qed.

  Hint Resolve hasType_change.

  Hint Extern 2 (override _ _ _ = _) =>
    unfold override; let x := fresh "x" in extensionality x;
      repeat match goal with
             | [ |- context[string_dec ?x ?y] ] => destruct (string_dec x y)
             end.

  (** Replacing a variable with a properly typed term preserves typing. *)
  Lemma substitution : forall G x t' e t e',
    hasType (override G x t') e t
    -> hasType empty e' t'
    -> hasType G (subst e' x e) t.
  Proof.
    induct 1; t.
  Qed.

  Hint Resolve substitution.

  (** We're almost ready for the main preservation property.  Let's prove it first for the more basic [step0] relation. *)
  Lemma preservation0 : forall e1 e2,
    e1 ==>r e2
    -> forall t, hasType empty e1 t
      -> hasType empty e2 t.
  Proof.
    invert 1; t.
  Qed.

  Hint Resolve preservation0.

  (** We also need this key property, essentially saying that, if [e1] and [e2] are "type-equivalent," then they remain "type-equivalent" after wrapping the same context around both. *)
  Lemma generalize_plug : forall e1 C e1',
    C[e1] == e1'
    -> forall e2 e2', C[e2] == e2'
      -> (forall t, hasType empty e1 t -> hasType empty e2 t)
      -> (forall t, hasType empty e1' t -> hasType empty e2' t).
  Proof.
    induct 1; t.
  Qed.

  Hint Resolve generalize_plug.

  (** From here, the proof proceeds almost identically to the one for the arithmetic language. *)
  Lemma preservation : forall e1 e2,
    e1 ==> e2
    -> forall t, hasType empty e1 t
      -> hasType empty e2 t.
  Proof.
    invert 1; t.
  Qed.

  Hint Resolve progress preservation.

  Theorem safety : forall e1 e2, star step e1 e2
    -> forall t, hasType empty e1 t
    -> value e2 \/ (exists e3, step e2 e3).
  Proof.
    induct 1; t.
  Qed.
  
End Stlc.