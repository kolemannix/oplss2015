Require Import Coq.Unicode.Utf8 Arith Ring Setoid.

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => fact n' * S n'
  end.

Inductive fact_state : Set :=
| AnswerIs : nat -> fact_state
| WithAccumulator : nat -> nat -> fact_state.

Inductive fact_init (original_input : nat) : fact_state -> Prop :=
| FactInit : fact_init original_input (WithAccumulator original_input 1).

Inductive fact_final : fact_state -> Prop :=
| FactFinal : forall ans, fact_final (AnswerIs ans).

Inductive fact_step : fact_state -> fact_state -> Prop :=
| FactDone : forall acc,
  fact_step (WithAccumulator O acc) (AnswerIs acc)
| FactStep : forall n acc,
  fact_step (WithAccumulator (S n) acc) (WithAccumulator n (acc * S n)).

Definition fact_invariant (original_input : nat) (st : fact_state) : Prop :=
  match st with
  | AnswerIs ans => fact original_input = ans
  | WithAccumulator n acc => fact original_input = fact n * acc
  end.

Ltac t := simpl; intuition;
          repeat match goal with
                 | [ H : _ = _ |- _ ] => rewrite H
                 end; intuition; ring || eauto.

Theorem fact_invariant_init : forall original_input st,
  fact_init original_input st
  -> fact_invariant original_input st.
Proof.
  destruct 1; t.
Qed.

Theorem fact_invariant_preserve : forall original_input st st',
  fact_step st st'
  -> fact_invariant original_input st
  -> fact_invariant original_input st'.
Proof.
  destruct 1; t.
Qed.

Theorem fact_invariant_final : forall original_input st,
  fact_final st
  -> fact_invariant original_input st
  -> st = AnswerIs (fact original_input).
Proof.
  destruct 1; t.
Qed.

Record transition_system := {
  State : Set;
  Init : State -> Prop;
  Step : State -> State -> Prop;
  Final : State -> Prop
}.

Definition fact_ts (original_input : nat) := {|
  State := fact_state;
  Init := fact_init original_input;
  Step := fact_step;
  Final := fact_final
|}.

Inductive runFrom (ts : transition_system) : State ts -> State ts -> Prop :=
| RunFinal : forall st,
  Final ts st
  -> runFrom ts st st
| RunStep : forall st st' st'',
  Step ts st st'
  -> runFrom ts st' st''
  -> runFrom ts st st''.

Inductive run (ts : transition_system) (st : State ts) : Prop :=
| Run : forall st0,
  Init ts st0
  -> runFrom ts st0 st
  -> run ts st.

Lemma runFrom_final : forall ts st st',
  runFrom ts st st'
  -> Final ts st'.
Proof.
  induction 1; t.
Qed.

Hint Resolve runFrom_final.

Lemma run_final : forall ts st,
  run ts st
  -> Final ts st.
Proof.
  destruct 1; t.
Qed.

Inductive isInvariant (ts : transition_system) (inv : State ts -> Prop) : Prop :=
| IsInvariant : (forall st, Init ts st -> inv st)
  -> (forall st st', Step ts st st' -> inv st -> inv st')
  -> isInvariant ts inv.

Theorem invariant_preserved : forall ts (inv : State ts -> Prop),
  (forall st st', Step ts st st' -> inv st -> inv st')
  -> forall st st', runFrom ts st st'
    -> inv st
    -> inv st'.
Proof.
  induction 2; t.
Qed.

Theorem invariant_final : forall ts inv st,
  isInvariant ts inv
  -> run ts st
  -> inv st.
Proof.
  destruct 1; destruct 1; eapply invariant_preserved; t.
Qed.

Lemma fact_right_answer : forall original_input st,
  Final (fact_ts original_input) st
  -> fact_invariant original_input st
  -> st = AnswerIs (fact original_input).
Proof.
  destruct 1; destruct 1; reflexivity.
Qed.

Hint Constructors isInvariant.
Hint Extern 1 (Init _ _) => constructor.
Hint Resolve run_final fact_right_answer.
Hint Extern 1 (fact_invariant _ _) => eapply invariant_final.
Hint Extern 1 (fact_invariant _ _) => apply fact_invariant_init.
Hint Extern 1 (fact_invariant _ _) => eapply fact_invariant_preserve; eassumption.

Theorem fact_ts_correct : forall original_input st,
  run (fact_ts original_input) st
  -> st = AnswerIs (fact original_input).
Proof.
  eauto 6.
Qed.

(* ---------- Exercise ------------- *)

