Require Import Coq.Unicode.Utf8 Arith List Omega String Coq.Program.Equality.

Open Scope string_scope.


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


(** We're going to work with *variable assignments*, which have a lot in common with typing contexts from the last lecture.  For instance, we can reuse this notation for an empty assignment. *)
Notation empty := (fun _ => O).

(** From reverse-engineering that notation, you may have guessed that variable assignments map variable names (strings) to values (naturals).  Here is an operator to override the value for a variable, within an assignment. *)
Definition assign (m : string -> nat) (x : string) (v : nat) : string -> nat :=
  fun x' => if string_dec x' x then v else m x'.

(** We'll also work with *memories*, which map numeric addresses to numeric values, reusing the same [empty] notation as above.  Here's an equivalent to [assign] for memories, for overriding the value stored at some address. *)
Definition write (m : nat -> nat) (a v : nat) : nat -> nat :=
  fun a' => if eq_nat_dec a' a then v else m a'.

(** Let's prove some basic properties about these notions of overriding and equality. *)

Ltac assign :=
  unfold assign, write; intros;
  repeat match goal with
         | [ |- context[if ?E then _ else _] ] => destruct E
         end; congruence.

Theorem assign_eq : forall m x v, assign m x v x = v.
Proof.
  assign.
Qed.

Theorem assign_neq : forall m x v y, y <> x -> assign m x v y = m y.
Proof.
  assign.
Qed.

Theorem write_eq : forall m x v, write m x v x = v.
Proof.
  assign.
Qed.

Theorem write_neq : forall m x v y, y <> x -> write m x v y = m y.
Proof.
  assign.
Qed.

(** We'll add all four lemmas as *rewrite hints*, so that the Coq tactic [autorewrite] will apply them for us later. *)
Hint Rewrite assign_eq assign_neq write_eq write_neq using (congruence || omega).


(** * Syntax and semantics of a simple imperative language *)

(** Here's some appropriate syntax for expressions (side-effect-free) of a simple imperatve language with a mutable memory. *)
Inductive exp :=
| Const : nat -> exp
| Var : string -> exp
| Read : exp -> exp
| Plus : exp -> exp -> exp
| Minus : exp -> exp -> exp
| Mult : exp -> exp -> exp.

(** Those were the expressions of numeric type.  Here are the Boolean expressions. *)
Inductive bexp :=
| Equal : exp -> exp -> bexp
| Less : exp -> exp -> bexp.

(** An important concept for this development will be that of an *invariant*, a property of machine states that should hold every time we reach some line of code.  Here our machine state consists of a variable assignment and a memory, so an invariant is a predicate over those two. *)
Definition invariant := (nat -> nat) -> (string -> nat) -> Prop.

(** Here's the syntax of side-effecting commands, where we attach an invariant to every "while" loop, for reasons that should become clear later.  The invariant is ignored in the operational semantics! *)
Inductive cmd :=
| Skip : cmd
(** A no-op *)
| Assign : string -> exp -> cmd
(** Writing a value to a variable *)
| Write : exp -> exp -> cmd
(** Writing to a cell of memory *)
| Seq : cmd -> cmd -> cmd
(** This one is for sequencing, like semicolon (";") in C. *)
| If_ : bexp -> cmd -> cmd -> cmd
(** Regular old conditional *)
| While_ : invariant -> bexp -> cmd -> cmd
(** Regular old while loops *).

(** Start of expression semantics: meaning of expressions, as a function of state *)
Fixpoint eval (e : exp) (m : nat -> nat) (s : string -> nat) : nat :=
  match e with
  | Const n => n
  | Var x => s x
  | Read e1 => m (eval e1 m s)
  | Plus e1 e2 => eval e1 m s + eval e2 m s
  | Minus e1 e2 => eval e1 m s - eval e2 m s
  | Mult e1 e2 => eval e1 m s * eval e2 m s
  end.

(** Meaning of Boolean expressions *)
Fixpoint beval (b : bexp) (m : nat -> nat) (s : string -> nat) : bool :=
  match b with
  | Equal e1 e2 => if eq_nat_dec (eval e1 m s) (eval e2 m s) then true else false
  | Less e1 e2 => if le_lt_dec (eval e2 m s) (eval e1 m s) then false else true
  end.

(** A big-step operational semantics for commands.  Instead of stepping to another command, we step to a new imperative state, consisting of a variable assignment and a memory. *)
Inductive exec : (nat -> nat) -> (string -> nat) -> cmd -> (nat -> nat) -> (string -> nat) -> Prop :=
| ExSkip : forall m s,
  exec m s Skip m s
| ExAssign : forall m s x e,
  exec m s (Assign x e) m (assign s x (eval e m s))
| ExWrite : forall m s e1 e2,
  exec m s (Write e1 e2) (write m (eval e1 m s) (eval e2 m s)) s
| ExSeq : forall m1 s1 c1 m2 s2 c2 m3 s3,
  exec m1 s1 c1 m2 s2
  -> exec m2 s2 c2 m3 s3
  -> exec m1 s1 (Seq c1 c2) m3 s3
| ExIfTrue : forall m1 s1 b c1 c2 m2 s2,
  beval b m1 s1 = true
  -> exec m1 s1 c1 m2 s2
  -> exec m1 s1 (If_ b c1 c2) m2 s2
| ExIfFalse : forall m1 s1 b c1 c2 m2 s2,
  beval b m1 s1 = false
  -> exec m1 s1 c2 m2 s2
  -> exec m1 s1 (If_ b c1 c2) m2 s2
| ExWhileFalse : forall I m s b c,
  beval b m s = false
  -> exec m s (While_ I b c) m s
| ExWhileTrue : forall I m1 s1 b c m2 s2 m3 s3,
  beval b m1 s1 = true
  -> exec m1 s1 c m2 s2
  -> exec m2 s2 (While_ I b c) m3 s3
  -> exec m1 s1 (While_ I b c) m3 s3.


(** * Hoare logic *)

(** How do we prove, in practice, that commands behave correctly?  The *Hoare triple* captures a common correctness condition, in terms of a *precondition* [P] and a *postcondition* [Q]. *)
Definition hoare_triple (P : invariant) (c : cmd) (Q : invariant) :=
  forall m1 s1, P m1 s1
    -> forall m2 s2, exec m1 s1 c m2 s2
      -> Q m2 s2.
(** In other words, if [P] holds before running the command, and if the command terminates, then [Q] holds afterward. *)

(** BEGIN BLACK MAGIC to declare parsing & spec notations, so that we can enter imperative programs with pretty standard syntax *)
Coercion Const : nat >-> exp.
Coercion Var : string >-> exp.
Notation "[ e ]" := (Read e) : cmd_scope.
Infix "+" := Plus : cmd_scope.
Infix "-" := Minus : cmd_scope.
Infix "*" := Mult : cmd_scope.
Infix "=" := Equal : cmd_scope.
Infix "<" := Less : cmd_scope.
Definition set (dst src : exp) : cmd :=
  match dst with
  | Read dst' => Write dst' src
  | Var dst' => Assign dst' src
  | _ => Assign "Bad LHS" 0
  end.
Infix "<-" := set (no associativity, at level 70) : cmd_scope.
Infix ";" := Seq (right associativity, at level 75) : cmd_scope.
Notation "'If' b { c1 } 'else' { c2 }" := (If_ b c1 c2) (at level 75, b at level 0) : cmd_scope.
Notation "{ I } 'While' b { c }" := (While_ I b c) (at level 75, b at level 0) : cmd_scope.
Delimit Scope cmd_scope with cmd.

Infix "+" := plus : reset_scope.
Infix "-" := minus : reset_scope.
Infix "*" := mult : reset_scope.
Infix "=" := eq : reset_scope.
Infix "<" := lt : reset_scope.
Delimit Scope reset_scope with reset.
Open Scope reset_scope.
(** END BLACK MAGIC *)

(** We should draw some attention to the next two notations, which define special lambdas for writing invariants.  The first form is parameterized over just the variable assignment, while the second is parameterized over both the memory and the variable assignment. *)
Notation "s ~> e" := (fun _ s => e%reset) (at level 99).
Notation "m , s ~~> e" := (fun m s => e%reset) (at level 99).

(** Also, here's the shorthand we'll usually apply for Hoare triples. *)
Notation "{{ P }} c {{ Q }}" := (hoare_triple P c%cmd Q) (at level 90, c at next level).


(** ** Let's verify some useful inference rules for deducing Hoare triples.  We start with a tactic that happenns to prove all of them pretty effectively. *)

Ltac basic :=
  unfold hoare_triple; intros;
  match goal with
  | [ H : exec _ _ _ _ _ |- _ ] => inversion H; subst; eauto
  end.

(** [Skip] has no effect. *)
Theorem HtSkip : forall (P : invariant),
  {{P}} Skip {{P}}.
Proof.
  basic.
Qed.

(** Assignment changes the state by running [assign]. *)
Theorem HtAssign : forall (P : invariant) x e,
  {{P}} Assign x e {{fun m s => exists s', P m s' /\ s = assign s' x (eval e m s')}}.
Proof.
  basic.
Qed.

(** Writing changes the state by running [write]. *)
Theorem HtWrite : forall (P : invariant) (e1 e2 : exp),
  {{P}} Write e1 e2 {{fun m s => exists m', P m' s /\ m = write m' (eval e1 m' s) (eval e2 m' s)}}.
Proof.
  basic.
Qed.

(** Sequencing composes specs in a natural way. *)
Theorem HtSeq : forall (P Q R : invariant) c1 c2,
  {{P}} c1 {{Q}}
  -> {{Q}} c2 {{R}}
  -> {{P}} Seq c1 c2 {{R}}.
Proof.
  basic.
Qed.

(** Correctness of [If] can be reduced to correctness of the two branches, w.r.t. appropriate assumptions. *)
Theorem HtIf : forall (P Q1 Q2 : invariant) b c1 c2,
  {{fun m s => P m s /\ beval b m s = true}} c1 {{Q1}}
  -> {{fun m s => P m s /\ beval b m s = false}} c2 {{Q2}}
  -> {{P}} If_ b c1 c2 {{fun m s => Q1 m s \/ Q2 m s}}.
Proof.
  basic.
Qed.

(** Let's use this notation for implication between invariants. *)
Notation "P ==> Q" := (forall m s, P m s -> Q m s) (at level 70, only parsing).

(** Now we come to the reason for including invariants in the syntax of loops: we need an invariant to apply our chosen rule for [While], and it's helpful to convey the choice of invariant by writing it within the code.  To prove the most convenient rule, we start with this lemma. *)
Lemma HtWhile' : forall (I Q : invariant) b c,
  {{fun m s => I m s /\ beval b m s = true}} c {{I}}
  -> (fun m s => I m s /\ beval b m s = false) ==> Q
  -> {{I}} While_ I b c {{Q}}.
Proof.
  unfold hoare_triple; induct 4; eauto.
Qed.
(** That is, the loop body preserves the invariant, and the invariant implies the postcondition, with a suitable side condition in each case. *)

(** A very useful, general transformation on Hoare triples: *weakening the precondition* *)
Lemma HtWeakenPrecondition : forall (P P' Q : invariant) c,
  {{P}} c {{Q}}
  -> P' ==> P
  -> {{P'}} c {{Q}}.
Proof.
  basic.
Qed.

(** We can use weakening to wrap our earlier [While] lemma in a form that applies handily for any precondition and postcondition. *)
Theorem HtWhile : forall (I P Q : invariant) b c,
  P ==> I
  -> {{fun m s => I m s /\ beval b m s = true}} c {{I}}
  -> (fun m s => I m s /\ beval b m s = false) ==> Q
  -> {{P}} While_ I b c {{Q}}.
Proof.
  intros; eapply HtWeakenPrecondition; try apply HtWhile'; auto.
Qed.

(** ...but the result is even easier to prove if we get to pick the postcondition. *)
Theorem HtWhileEasy : forall (I P : invariant) b c,
  P ==> I
  -> {{fun m s => I m s /\ beval b m s = true}} c {{I}}
  -> {{P}} While_ I b c {{fun m s => I m s /\ beval b m s = false}}.
Proof.
  intros; eapply HtWeakenPrecondition; try apply HtWhile'; auto.
Qed.

(** A dual operation to weakening the precondition is *strengthening the postcondition*. *)
Lemma HtStrengthenPostcondition : forall (P Q Q' : invariant) c,
  {{P}} c {{Q}}
  -> Q ==> Q'
  -> {{P}} c {{Q'}}.
Proof.
  basic.
Qed.

(** BEGIN BLACK MAGIC for applying our Hoare rules automatically, to verify a particular program *)
Ltac step1 c :=
  match eval hnf in c with
  | Skip => apply HtSkip
  | Assign _ _ => apply HtAssign
  | Write _ _ => apply HtWrite
  | Seq _ _ => eapply HtSeq
  | If_ _ _ _ => apply HtIf
  | While_ _ _ _ => apply HtWhileEasy || apply HtWhile
  end.

Ltac step := match goal with
             | [ |- {{_}} ?c {{_}} ] =>
               step1 c || (eapply HtStrengthenPostcondition; [ step1 c | ])
             end.

Ltac correct := intros; repeat step; cbv beta;
                repeat (intuition subst;
                        repeat match goal with
                               | [ H : ex _ |- _ ] => destruct H
                               end);
                repeat (autorewrite with core in *;
                         repeat match goal with
                                | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
                                end;
                         simpl in *; intuition);
                repeat match goal with
                       | [ H : ?X = ?X |- _ ] => clear H
                       end;
                try match goal with
                    | [ H : _ = ?X |- _ = ?X ] => rewrite <- H; try ring
                    end.
(** END BLACK MAGIC (we'll just call [correct] in the examples below) *)


(** * Some examples of verified programs *)

(** ** Swapping the values in two variables *)

Theorem swap_ok : forall a b,
  {{s ~> s "x" = a /\ s "y" = b}}
    "tmp" <- "x";
    "x" <- "y";
    "y" <- "tmp"
  {{s ~> s "x" = b /\ s "y" = a}}.
Proof.
  correct.
Qed.

(** ** Computing the maximum of two variables *)

(** Two basic facts will be useful as rewrite hints: *)
Lemma max_left : forall a b,
  a < b
  -> max a b = b.
Proof.
  intros; destruct (Max.max_spec a b); intuition.
Qed.

Lemma max_right : forall a b,
  a >= b
  -> max a b = a.
Proof.
  intros; destruct (Max.max_spec a b); intuition.
Qed.

Hint Rewrite max_left max_right using omega.

Theorem max_ok : forall a b,
  {{s ~> s "x" = a /\ s "y" = b}}
    If ("x" < "y") {
      "m" <- "y"
    } else {
      "m" <- "x"
    }
  {{s ~> s "m" = max a b}}.
Proof.
  correct.
Qed.

(** ** Iterative factorial *)

(** These two rewrite rules capture the definition of functional [fact], in exactly the form useful in our Hoare-logic proof. *)
Lemma fact_base : forall n,
  n = 0
  -> fact n = 1.
Proof.
  intros; subst; intuition.
Qed.

Lemma fact_rec : forall n,
  n > 0
  -> fact n = n * fact (n - 1).
Proof.
  destruct n; simpl; intuition.
Qed.

Hint Rewrite fact_base fact_rec using omega.

(** Note the careful choice of loop invariant below.  It may look familiar from our state-machine example 3 lectures back! *)
Theorem fact_ok : forall n,
  {{s ~> s "n" = n}}
    "acc" <- 1;
    {s ~> s "acc" * fact (s "n") = fact n}
    While (0 < "n") {
      "acc" <- "acc" * "n";
      "n" <- "n" - 1
    }
  {{s ~> s "acc" = fact n}}.
Proof.
  correct.
Qed.

(** ** Selection sort *)

(** This is our one example of a program reading/writing memory, which holds the representation of an array that we want to sort in-place. *)

(** One simple lemma turns out to be helpful to guide [auto] properly. *)
Lemma leq_f : forall A (f : A -> nat) x y,
  x = y
  -> f x <= f y.
Proof.
  correct.
Qed.

Hint Resolve leq_f.
Hint Extern 1 (@eq nat _ _) => omega.
(** We also register [omega] as a step to try during proof search. *)

(** These invariants are fairly hairy, but probably the best way to understand them is just to spend a while reading them.  They generally talk about sortedness of subsets of the array.  See the final postcondition for how we interpret a part of memory as an array.  Also note that we only prove hre that the final array is sorted, *not* that it's a permutation of the original array!  (Exercise for the reader?  I'm not sure how much work it would take.) *)
Theorem selectionSort_ok :
  {{m, s ~~> True}}
    "i" <- 0;
    { m, s ~~> s "i" <= s "n"
         /\ (forall i j, i < j < s "i" -> m (s "a" + i) <= m (s "a" + j))
         /\ (forall i j, i < s "i" -> s "i" <= j < s "n" -> m (s "a" + i) <= m (s "a" + j)) }
    While ("i" < "n") {
      "j" <- "i"+1;
      "best" <- "i";
      { m, s ~~> s "i" < s "j" <= s "n"
         /\ s "i" <= s "best" < s "n"
         /\ (forall k, s "i" <= k < s "j" -> m (s "a" + s "best") <= m (s "a" + k))
         /\ (forall i j, i < j < s "i" -> m (s "a" + i) <= m (s "a" + j))
         /\ (forall i j, i < s "i" -> s "i" <= j < s "n" -> m (s "a" + i) <= m (s "a" + j)) }
      While ("j" < "n") {
        If (["a" + "j"] < ["a" + "best"]) {
          "best" <- "j"
        } else {
          Skip
        };
        "j" <- "j" + 1
      };
      "tmp" <- ["a" + "best"];
      ["a" + "best"] <- ["a" + "i"];
      ["a" + "i"] <- "tmp";
      "i" <- "i" + 1
    }
  {{m, s ~~> forall i j, i < j < s "n" -> m (s "a" + i) <= m (s "a" + j)}}.
Proof.
  correct;
  repeat match goal with
         | [ |- context[write _ (?a + ?x) _ (?a + ?y)] ] =>
           destruct (eq_nat_dec x y); correct
         end.

  destruct (eq_nat_dec k (x0 "j")); correct.
  specialize (H k); correct.

  destruct (eq_nat_dec k (x "j")); correct.
Qed.