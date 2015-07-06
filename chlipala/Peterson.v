(* Exercise for the reader: look into what these standard-library modules contain :-) *)
Require Import Coq.Unicode.Utf8 Arith Bool Ring Setoid.

(** This next command (roughly) turns on the sort of implicit-argument behavior we're used to from Haskell or ML: type arguments to polymorphic functions need not be passed explicitly. *)
Set Implicit Arguments.


(** * A simple state machine for factorial *)

(** Here's a classic recursive, functional program for factorial. *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => fact n' * S n'
  end.

(** But let's reformulate factorial relationally, as an example to explore treatment of inductive relations in Coq.  First, these are the states of our state machine. *)
Inductive fact_state : Set :=
| AnswerIs : nat -> fact_state
| WithAccumulator : nat -> nat -> fact_state.

(** This predicate captures which states are starting states. *)
Inductive fact_init (original_input : nat) : fact_state -> Prop :=
| FactInit : fact_init original_input (WithAccumulator original_input 1).

(** And here are the states where we declare execution complete. *)
Inductive fact_final : fact_state -> Prop :=
| FactFinal : forall ans, fact_final (AnswerIs ans).

(** The most important part: the relation to step between states *)
Inductive fact_step : fact_state -> fact_state -> Prop :=
| FactDone : forall acc,
  fact_step (WithAccumulator O acc) (AnswerIs acc)
| FactStep : forall n acc,
  fact_step (WithAccumulator (S n) acc) (WithAccumulator n (acc * S n)).

(** To prove that our state machine really computes factorial, we introduce an *invariant* on states. *)
Definition fact_invariant (original_input : nat) (st : fact_state) : Prop :=
  match st with
  | AnswerIs ans => fact original_input = ans
  | WithAccumulator n acc => fact original_input = fact n * acc
  end.

(** It should hold at the start. *)
Theorem fact_invariant_init : forall original_input st,
  fact_init original_input st
  -> fact_invariant original_input st.
Proof.
  destruct 1; simpl.
  (** Notice that here we have done case analysis (with [destruct]) on *which*rule*was*used*to*derive*a*predicate*, in the same way that we would use case analysis on e.g. whether a list is [nil] or [cons]. *)
  ring.
  (** Here's a handy tactic for proving goals that follow from the axioms of the algebraic structure *ring*.  Actually, it's generalized to semirings, and here we appeal to the semiring structure of the naturals. *)
Qed.

(** And every step should preserve the invariant. *)
Theorem fact_invariant_preserve : forall original_input st st',
  fact_step st st'
  -> fact_invariant original_input st
  -> fact_invariant original_input st'.
Proof.
  destruct 1; simpl; intros.
  
  rewrite H.
  ring.

  rewrite H.
  ring.
Qed.

(** Finally, when the state machine completes, the state must look how we expected. *)
Theorem fact_invariant_final : forall original_input st,
  fact_final st
  -> fact_invariant original_input st
  -> st = AnswerIs (fact original_input).
Proof.
  destruct 1; simpl; intros.

  rewrite H.
  reflexivity.
Qed.


(** * Transition systems in general *)

(** Let's define a polymorphic type of states machines, packaging the components we coded in an ad-hoc way for factorial. *)
Record transition_system' (State : Set) := {
  Init : State -> Prop;
  Step : State -> State -> Prop;
  Final : State -> Prop
}.

(** Here's a fun construction, to package a type along with its associated polymorphic value.  The [:>] declares a *coercion*, where the [transition_system'] within a [transition_system] is automatically extracted as required by typing. *)
Record transition_system := {
  State : Set;
  Super :> transition_system' State
}.

(** As an example, here's factorial in the new format. *)
Definition fact_ts (original_input : nat) := {|
  State := fact_state;
  Super := {| Init := fact_init original_input;
              Step := fact_step;
              Final := fact_final |}
|}.

(** Now a general relation to capture zero or more steps of transition-system execution *)
Inductive runFrom (ts : transition_system) : State ts -> State ts -> Prop :=
| RunFinal : forall st,
  Final ts st
  -> runFrom ts st st
| RunStep : forall st st' st'',
  Step ts st st'
  -> runFrom ts st' st''
  -> runFrom ts st st''.

(** Wrapping it with an extra check that we start in an initial state *)
Inductive run (ts : transition_system) (st : State ts) : Prop :=
| Run : forall st0,
  Init ts st0
  -> runFrom ts st0 st
  -> run ts st.

(** Here's our first example of *rule*induction*, using the inductive tree structure of proofs.  Let's show that [runFrom] only finishes in final states. *)
Lemma runFrom_final : forall ts st st',
  runFrom ts st st'
  -> Final ts st'.
Proof.
  induction 1.

  assumption.

  assumption.
Qed.

(** It's a simple corollary to lift to [run] insteadof [runFrom]. *)
Lemma run_final : forall ts st,
  run ts st
  -> Final ts st.
Proof.
  destruct 1.

  eapply runFrom_final.
  (** [eapply]: like [apply], but leaves *unification*variables* to be determined later *)
  eassumption.
  (** [eassumption]: like [assumption], but will try to fill in *unification*variables *)
Qed.

(** A formal characterization for when a predicate is an invariant of a transition system *)
Inductive isInvariant (ts : transition_system) (inv : State ts -> Prop) : Prop :=
| IsInvariant : (forall st, Init ts st -> inv st)
  -> (forall st st', Step ts st st' -> inv st -> inv st')
  -> isInvariant ts inv.

(** Let's prove that the conditions we chose are strong enough to show that the invariant is preserved by [runFrom]. *)
Theorem invariant_preserved : forall ts (inv : State ts -> Prop),
  (forall st st', Step ts st st' -> inv st -> inv st')
  -> forall st st', runFrom ts st st'
    -> inv st
    -> inv st'.
Proof.
  induction 2; intros.

  assumption.

  apply IHrunFrom.
  eapply H.
  eassumption.
  assumption.
Qed.

(** And it's easy to lift to [run] again. *)
Theorem invariant_final : forall ts inv st,
  isInvariant ts inv
  -> run ts st
  -> inv st.
Proof.
  destruct 1.
  destruct 1.
  eapply invariant_preserved.
  assumption.
  eassumption.
  apply H.
  assumption.
Qed.

(** So now we can do another proof of factorial via our generic machinery. *)
Theorem fact_ts_correct : forall original_input st,
  run (fact_ts original_input) st
  -> st = AnswerIs (fact original_input).
Proof.
  intros.

  assert (Final (fact_ts original_input) st).
  (** [assert]: a kind of "cut": prove an extra fact, then have it as a new hypothesis *)
  apply run_final.
  assumption.

  assert (fact_invariant original_input st).
  apply invariant_final.
  apply IsInvariant.
  apply fact_invariant_init.
  apply fact_invariant_preserve.
  assumption.

  destruct H0.
  simpl in H1.
  rewrite H1.
  reflexivity.
Qed.

(** * Running transition systems in parallel *)

(** Consider two transition systems with a common notion of shared state and (potentially) their own notions of private state.  Let's build a transition system for running them in parallel with nondeterministic interleaving. *)
Inductive parallel_init (Shared Private1 Private2 : Set)
  (Init1 : Shared * Private1 -> Prop)
  (Init2 : Shared * Private2 -> Prop)
  : Shared * Private1 * Private2 -> Prop :=
| Pinit : forall sh pr1 pr2,
  Init1 (sh, pr1)
  -> Init2 (sh, pr2)
  -> parallel_init Init1 Init2 (sh, pr1, pr2).

Inductive parallel_step (Shared Private1 Private2 : Set)
          (Step1 : Shared * Private1 -> Shared * Private1 -> Prop)
          (Step2 : Shared * Private2 -> Shared * Private2 -> Prop)
          : Shared * Private1 * Private2 -> Shared * Private1 * Private2 -> Prop :=
| Pstep1 : forall sh pr1 pr2 sh' pr1',
  Step1 (sh, pr1) (sh', pr1')
  -> parallel_step Step1 Step2 (sh, pr1, pr2) (sh', pr1', pr2)
| Pstep2 : forall sh pr1 pr2 sh' pr2',
  Step2 (sh, pr2) (sh', pr2')
  -> parallel_step Step1 Step2 (sh, pr1, pr2) (sh', pr1, pr2').

Inductive parallel_final (Shared Private1 Private2 : Set)
          (Final1 : Shared * Private1 -> Prop)
          (Final2 : Shared * Private2 -> Prop)
  : Shared * Private1 * Private2 -> Prop :=
| Pfinal : forall sh pr1 pr2,
  Final1 (sh, pr1)
  -> Final2 (sh, pr2)
  -> parallel_final Final1 Final2 (sh, pr1, pr2).

Definition parallel (Shared Private1 Private2 : Set)
           (ts1 : transition_system' (Shared * Private1))
           (ts2 : transition_system' (Shared * Private2)) := {|
  State := Shared * Private1 * Private2;
  Super := {| Init := parallel_init (Init ts1) (Init ts2);
              Step := parallel_step (Step ts1) (Step ts2);
              Final := parallel_final (Final ts1) (Final ts2) |}
|}.

(** * A simple example of another program as a state transition system *)

(** We'll formalize this pseudocode for one thread of a concurrent, shared-memory program.
  thread(me, other):
    flag[me] = true; (I'm going to wait)
    turn = other;  (You go ahead)
    while (flag[other] && turn == other); (I'll wait until you're done)
    local = global; (Access the global state)
    global = local + 1; (increment the global state)
    flag[me] = false; (I'm done)
 *)

(** This inductive state effectively encodes all possible combinations of two kinds of *local*state* in a thread:
    * program counter
    * values of local variables that may be ready eventually *)

Inductive peterson_program : Set :=
| Flag: peterson_program
| Wait: peterson_program
| Read : peterson_program
| Write : nat -> peterson_program
| Unlock : peterson_program
| Done : peterson_program.

(** Next, a type for state shared between threads, using Coq's handy record facility, which desugars to single-constructor inductive definitions. *)
Record pet_state := {
    FlagOne : bool;
    FlagTwo : bool;
    Turn : bool;
    Global : nat   (** A shared counter *)
}.

(** The combined state, from one thread's perspective.  [%type] gets [*] to be parsed as Cartesian product instead of numeric multiplication. *)
Definition peterson_state := (pet_state * peterson_program)%type.

(** Now a routine definition of the three key relations of a state-transition system.  The most interesting logic surrounds saving the counter value in the local state after reading. *)

Inductive peterson_init : peterson_state -> Prop :=
| IncInit :
  peterson_init ({| FlagOne := false;
                    FlagTwo := false;
                    Turn := false;
                    Global := O |}, Flag).

Inductive peterson_step : peterson_state -> peterson_state -> Prop :=
| IncFlag : forall g t,
  peterson_step ({| FlagOne := false; FlagTwo := false; Turn := t; Global := g |}, Flag)
                 ({| FlagOne := true; FlagTwo := false; Turn := false; Global := g |}, Wait)
| IncWait : forall f1 f2 t g,
  peterson_step ({| FlagOne := f1; FlagTwo := f2; Turn := t; Global := g |}, Wait)
                 ({| FlagOne := f1; FlagTwo := f2; Turn := t; Global := g |}, Read)
| IncRead : forall f1 f2 t g,
  peterson_step ({| FlagOne := f1; FlagTwo := f2; Turn := t; Global := g |}, Read)
                 ({| FlagOne := f1; FlagTwo := f2; Turn := t; Global := g |}, Write g)
| IncWrite : forall f1 f2 t g v,
  peterson_step ({| FlagOne := f1; FlagTwo := f2; Turn := t; Global := g |}, Write v)
                 ({| FlagOne := f1; FlagTwo := f2; Turn := t; Global := S v |}, Unlock)
| IncUnlock : forall f1 f2 t g,
  peterson_step ({| FlagOne := f1;    FlagTwo := f2; Turn := t; Global := g |}, Unlock)
                 ({| FlagOne := false; FlagTwo := f2; Turn := t; Global := g |}, Done).

Inductive peterson_final : peterson_state -> Prop :=
| IncFinal : forall p: pet_state,
  peterson_final (p, Done).

Definition peterson_ts := {|
  State := peterson_state;
  Super := {| Init := peterson_init;
              Step := peterson_step;
              Final := peterson_final |}
|}.

(** * Running transition systems in parallel *)

(** Consider two transition systems with a common notion of shared state and (potentially) their own notions of private state.  Let's build a transition system for running them in parallel with nondeterministic interleaving. *)

(** Example: composing two threads of the kind we formalized earlier *)
Definition peterson2_ts := parallel peterson_ts peterson_ts.

(** Let's prove that the counter is always 2 when the composed program terminates. *)

(** First big idea: the program counter of a thread tells us how much it has added to the shared counter so far. *)
Definition contribution_from (pr : peterson_program) : nat :=
  match pr with
  | Unlock | Done => 1
  | _ => 0
  end.

(** Second big idea: the program counter also tells us whether a thread holds the lock. *)
Definition has_lock (pr : peterson_program) : bool :=
  match pr with
  | Read => true
  | Write _ => true
  | Unlock => true
  | _ => false
  end.

(** Now we see that the shared state is a function of the two program counters, as follows. *)
Definition shared_from_private (pr1 pr2 : peterson_program) :=
  {| FlagOne := has_lock pr1;
     FlagTwo := has_lock pr2;
     Global :=  contribution_from pr1 + contribution_from pr2 |}.

(** We also need a condition to formalize compatibility between program counters, e.g. that they shouldn't both be in the critical section at once. *)
Definition instruction_ok (self other : peterson_program): Prop :=
  match self with
  | Flag => True
  | Wait => True
  | Read => has_lock other = false
  | Write n => has_lock other = false /\ n = contribution_from other
  | Unlock => has_lock other = false
  | Done => True
  end.

(** Now we have the ingredients to state the invariant. *)
Inductive peterson2_invariant : State peterson2_ts -> Prop :=
| Inc2Inv : forall pr1 pr2,
  instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> peterson2_invariant (shared_from_private pr1 pr2, pr1, pr2).

(** It's convenient to prove this alternative equality-based "constructor" for the invariant. *)
Lemma Inc2Inv' : forall sh pr1 pr2,
  sh = shared_from_private pr1 pr2
  -> instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> peterson2_invariant (sh, pr1, pr2).
Proof.
  intros.
  rewrite H.
  apply Inc2Inv; assumption.
Qed.

Lemma final_eq : forall st,
  Final peterson2_ts st
  -> peterson2_invariant st
  -> st = ({| FlagOne := false; FlagTwo := false; Turn := false; Global := 2 |}, Done, Done).
Proof.
  destruct 1.
  inversion H; subst.
  inversion H0; subst.
  intros.
  inversion H1; subst. compute.
  reflexivity.
Qed.

Hint Resolve run_final.

(** Now we can prove that the system only runs to happy states. *)
Theorem increment2_ts_correct : forall st,
  run peterson2_ts st
  -> st = ({| FlagOne := false; FlagTwo := false; Turn := false; Global := 2 |}, Done, Done).
Proof.
  intros.
  apply final_eq; eauto.
  apply invariant_final; auto.
  constructor.
  (** [constructor]: a convenient shorthand for [apply] that picks the rule to apply for you, by searching through the constructors for the inductive type you're trying to prove *)

  destruct 1.
  inversion H0; subst.
  inversion H1; subst.
  change {| FlagOne := false; FlagTwo := false; Turn := false; Global := 0 |} with (shared_from_private Flag Flag).
  (** [change]: replace one term with another, when it is sufficiently easy for Coq to see that the two terms are equal (actually when they are *definitionally*equal*, but I won't go into the details here). *)
  constructor; simpl; intuition.
  (** [intuition] simplifies goals according to the rules of propositional (Boolean) logic.  (The name tells us that it follows *intuitionistic*, rather than classical, logic.) *)

  destruct 1.

  (** Some long tactic chains help us consider many cases whether bothering with the details manually.  Details are a bit beyond the scope of this lecture.  We use [subst], which finds equalities over variables and then eliminates those variables, replacing them with the terms they are equated to. *)

  destruct pr2; inversion H0; subst; inversion 1; subst; apply Inc2Inv'; simpl in *; intuition; subst. compute.
  reflexivity || congruence.

  destruct pr1; inversion H0; subst; inversion 1; subst; apply Inc2Inv'; simpl in *; intuition; subst;
  reflexivity || congruence.
Qed.

(* assignment *)

