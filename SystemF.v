Require Import Coq.Unicode.Utf8 Arith FunctionalExtensionality String Coq.Program.Equality.
(** Polymorphic types in system F promise not to **depend** upon the given type itself
T := bool | t1 -> t1 | alpha | Forall alpha. z
e := x | true | false | if ... | lam x:t. e | e1 e2 | LAM alph. e | e [t]
v ::= true | false | lam x: t. e | LAM alph. e
E ::= [dot] | if E then e1 else e2 | E e | v E | E [ t ]

e |--> e'
---------------
E[e] |---> E[e']

System F has impredicative polymorphism (we can do the bigger universe loopy thing)

*)

(* 1) Plan: Implement without polymorphic types
   2) switch to duhbrown indices
   3) Then add polymorphic types*

Try to prove progres and preservation at each step *)
Require Import String.

Inductive Id := mk_id: string -> Id.

Definition id_eq_dec : forall i i': Id, {i = i'} + {i <> i'}.
  Proof.
    decide equality. generalize s, s0. exact string_dec.
  Defined.

Inductive type : Set :=
 | Bool : type
 | Num : type
 | Fun : type -> type -> type
 (* | alpha *)
 (* | Quant *)
.

Inductive exp : Set :=
  | ConstB: bool -> exp
  | ConstN: nat -> exp
  | If: exp -> exp -> exp -> exp
  | Plus: exp -> exp -> exp
  | Var : Id -> exp
  | Abs: Id -> exp -> exp
  | App: exp -> exp -> exp
  (** tabs = Big lambda abstraction - quantification over a type *)
  (* | Tabs: id -> exp -> exp *)
.

Notation "\ x , e" := (Abs x e) (at level 10).

Coercion mk_id : string >-> Id.
Coercion ConstN : nat >-> exp.
Coercion ConstB : bool >-> exp.
Coercion Var : Id >-> exp.

Definition var_context := Id -> option type.
Notation empty := (fun _ => None).
Definition override (G : var_context) (x : Id) (t : type) : var_context :=
  fun y => if id_eq_dec y x then Some t else G y.

Inductive value : exp -> Prop :=
  | ValueConstB : forall b,  value (ConstB b)
  | ValueConstN : forall n, value (ConstN n)
  | ValueAbs : forall i e, value (Abs i e)
  (* | ValueTabs : forall i t, value (Tabs i t) *)
.
Inductive hasType : var_context -> exp -> type -> Prop :=
  | HTBoolean : forall G b, hasType G (ConstB b) Bool
  | HTNumber : forall G n, hasType G (ConstN n) Num
  | HTIf : forall G t e1 e2 e3,
    hasType G e1 Bool
    -> hasType G e2 t
    -> hasType G e3 t
    -> hasType G (If e1 e2 e3) t
  | HTPlus : forall G e1 e2,
    hasType G e1 Num
    -> hasType G e2 Num
    -> hasType G (Plus e1 e2) Num
  | HTVar : forall G id t,
    G id = Some t
    -> hasType G (Var id) t
  | HTAbs : forall G x e1 t1 t2,
    hasType (override G x t1) e1 t2
    -> hasType G (Abs x e1) (Fun t1 t2)
  | HTApp : forall G e1 e2 t1 t2,
    hasType G e1 (Fun t1 t2)
    -> hasType G e2 t1
    -> hasType G (App e1 e2) t2.

Inductive context : Set :=
  | Hole: context
  | AppE: context -> exp -> context
  | AppV: exp -> context -> context
  | Plus1: context -> exp -> context
  | Plus2: exp -> context -> context
  | If1: context -> exp -> exp -> context
  | If2: exp -> context -> exp -> context
  | If3: exp -> exp -> context -> context.

Reserved Notation " C [ e ] == e' " (at level 10).

Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, Hole[e] == e
  | PlugAppE : forall C e e' e2,
                 C[e] == e'
                 -> (AppE C e2)[e] == (App e' e2)
  | PlugAppV : forall C e e' v,
                 C[e] == e' -> value v
                 -> (AppV v C)[e] == (App v e')
  | PlugPlus1 : forall C e e' e2,
                  C[e] == e'
                  -> (Plus1 C e2)[e] == (Plus e' e2)
  | PlugPlus2 : forall C e1 e e',
                  C[e] == e' -> value e1
                  -> (Plus2 e1 C)[e] == (Plus e1 e')
  | PlugIf1 : forall C e e' e2 e3,
                C[e] == e'
                -> (If1 C e2 e3)[e] == (If e' e2 e3)
  | PlugIf2 : forall C e1 e e' e3,
                C[e] == e'
                -> (If2 e1 C e3)[e] == (If e1 e' e3)
  | PlugIf3 : forall C e1 e2 e e',
                C[e] == e'
                -> (If3 e1 e2 C)[e] == (If e1 e2 e')
                         where " C [ e ] == e' " := (plug C e e'). 


Fixpoint subst (e': exp) (x: Id) (e: exp): exp :=
  match e with
  | ConstB b => ConstB b
  | ConstN n => ConstN n
  | If e1 e2 e3 => If (subst e' x e1) (subst e' x e2) (subst e' x e3)
  | Plus e1 e2 => Plus (subst e' x e1) (subst e' x e2)
  | Var x' => if (id_eq_dec x x') then e' else Var x'
  | Abs x' e1 => Abs x' (if (id_eq_dec x x') then e1 else subst e' x e1)
  | App e1 e2 => App (subst e' x e1) (subst e' x e2)
  (* tabs = Big lambda abstraction - quantification over a type *)
  (* | Tabs: id -> exp -> exp *)
  end.

Notation "[ e' // x ] e" := (subst e' x e) (at level 9).

Open Scope string_scope.

Check \"x", "x".

Compute \"x", (Plus "x" "x").
Compute subst 1 "x" (Plus (Var "x") (Var "y")).

Inductive step_prim : exp -> exp -> Prop :=
  | Beta : forall x e v, value v -> step_prim (App (Abs x e) v) (subst v x e)
  | BranchT: forall e2 e3, step_prim (If (ConstB true) e2 e3) e2
  | BranchF: forall e2 e3, step_prim (If (ConstB false) e2 e3) e3
  | Add : forall n m, step_prim (Plus (ConstN n) (ConstN m)) (ConstN (n + m)).

Inductive step : exp -> exp -> Prop :=
  | Step : forall C e1 e2 e1' e2',
    C[e1] == e1'
  -> C[e2] == e2'
  -> step_prim e1 e2
  -> step e1' e2'.

Notation "e ==> e'" := (step e e') (at level 10).

Lemma override_eq : forall G t x t',
  override G x t' x = Some t
  -> t = t'.
Proof.
  unfold override; intros; destruct (id_eq_dec x x); congruence.
Qed.

Lemma override_neq : forall G t x y t',
  override G x t' y = Some t
  -> x <> y
  -> G y = Some t.
Proof.
  unfold override; intros; destruct (id_eq_dec y x); try congruence.
Qed.

Set Implicit Arguments.

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

Ltac t0 := match goal with
           | [ H : ex _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ |- context[string_dec ?x ?y] ] => destruct (string_dec x y)
           | [ H : override _ _ _ _ = Some _ |- _ ] => apply override_eq in H
           | [ H : override _ _ _ _ = Some _ |- _ ] => apply override_neq in H; [ | congruence ]
           (* | [b : bool |- context[If ?b ?e1 ?e2] ] => destruct b *)
           | [ H : step _ _ |- _ ] => invert H
           | [ H : step_prim _ _ |- _ ] => invert1 H
           | [ H : hasType _ ?e _, H' : value ?e |- _ ] => invert H'; invert H
           | [ H : hasType _ _ _ |- _ ] => invert1 H
           | [ H : plug _ _ _ |- _ ] => invert1 H
           end; subst.

Ltac t := simpl; intuition subst; repeat t0; try congruence; eauto 6.

Hint Constructors step step_prim value hasType.

(* Lemma if_change_true: forall e e1 e2,  e ==> true -> (If e e1 e2) ==> e1. *)

Lemma progress : forall e t G,
  hasType G e t -> value e \/ (exists e', e ==> e').
Proof.
  intros.
    induction e.
      auto. auto.
      inversion H; subst. clear H.
      right.
        inversion H4; subst. clear H4.
        inversion H6; subst. clear H6.
        inversion H7; subst. clear H7.
        destruct b.
          exists b0. eapply Step; repeat constructor.
          exists b1. eapply Step; repeat constructor. 
        destruct b.
          exists b0. eapply Step; repeat constructor.
          exists (If e1 e2 e0). eapply Step; repeat constructor.
        destruct b.
          exists b0. eapply Step; repeat constructor.
          exists id. eapply Step; repeat constructor.
        destruct b.
          exists b0. eapply Step; repeat constructor.
          exists (App e1 e2). eapply Step; repeat constructor.
        destruct b.
          exists n. eapply Step; repeat constructor.
          exists e3. eapply Step; repeat constructor.
        destruct b.
          exists (If e1 e0 e4). eapply Step; repeat constructor.
          exists e3. eapply Step; repeat constructor.
        destruct b.
          exists (Plus e1 e0). eapply Step; repeat constructor.
          exists e3. eapply Step; repeat constructor.
        destruct b.
          exists id. eapply Step; repeat constructor.
          exists e3. eapply Step; repeat constructor.
        destruct b.
          exists (\ x, e1). eapply Step; repeat constructor.
          exists e3. eapply Step; repeat constructor.
        destruct b.
          exists (App e1 e0). eapply Step; repeat constructor.
          exists e3. eapply Step; repeat constructor.
        inversion H; subst. clear H.
        inversion H0; subst. clear H0.
        inversion H1; subst. clear H1.
        inversion H4; subst.
        inversion H3.
        destruct b, b0, b1.
        exists e2.
        eapply Step.
        eapply PlugIf1. eapply PlugIf1.
        subst.


          exists e3. eapply Step; repeat constructor.

