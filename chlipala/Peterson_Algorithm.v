Require Import Arith Bool Ring Setoid Top.Relations.

Set Implicit Arguments.


(* Peterson's Lock Algorithm <https://en.wikipedia.org/wiki/Peterson%27s_algorithm> *)

(** Equivalent to this code:
  flag[me] = true;
  turn = other;
  while (flag[other] && turn == other);
  local = global;
  global = local + 1;
  flag[me] = false;
*)

Inductive increment_program : Set :=
| SetFlag : increment_program
| SetTurn : increment_program
| ReadFlag : increment_program
| ReadTurn : increment_program
| Read : increment_program
| Write : nat -> increment_program
| UnsetFlag : increment_program
| Done : increment_program.

Record inc_state := {
  Flag1 : bool;
  Flag2 : bool;
  Turn : bool;
  Global : nat
}.

Definition increment_state := (inc_state * increment_program)%type.

Inductive increment_init : increment_state -> Prop :=
| IncInit :
  increment_init ({| Flag1 := false; Flag2 := false; Turn := false; Global := O |}, SetFlag).

Inductive increment_step : bool (* am I process 2? *) -> increment_state -> increment_state -> Prop :=
| IncSetFlag1 : forall fl1 fl2 tu g,
  increment_step false
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, SetFlag)
                 ({| Flag1 := true; Flag2 := fl2; Turn := tu; Global := g |}, SetTurn)
| IncSetFlag2 : forall fl1 fl2 tu g,
  increment_step true
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, SetFlag)
                 ({| Flag1 := fl1; Flag2 := true; Turn := tu; Global := g |}, SetTurn)
| IncSetTurn : forall am2 fl1 fl2 tu g,
  increment_step am2
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, SetTurn)
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := negb am2; Global := g |}, ReadFlag)
| IncReadFlag1True : forall fl1 fl2 tu g,
  fl2 = true
  -> increment_step false
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, ReadFlag)
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, ReadTurn)
| IncReadFlag1False : forall fl1 fl2 tu g,
  fl2 = false
  -> increment_step false
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, ReadFlag)
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, Read)
| IncReadFlag2True : forall fl1 fl2 tu g,
  fl1 = true
  -> increment_step true
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, ReadFlag)
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, ReadTurn)
| IncReadFlag2False : forall fl1 fl2 tu g,
  fl1 = false
  -> increment_step true
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, ReadFlag)
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, Read)
| IncReadTurnTrue : forall am2 fl1 fl2 g,
  increment_step am2
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := negb am2; Global := g |}, ReadTurn)
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := negb am2; Global := g |}, ReadFlag)
| IncReadTurnFalse : forall am2 fl1 fl2 g,
  increment_step am2
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := am2; Global := g |}, ReadTurn)
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := am2; Global := g |}, Read)
| IncRead : forall am2 fl1 fl2 tu g,
  increment_step am2
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, Read)
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, Write g)
| IncWrite : forall am2 fl1 fl2 tu g v,
  increment_step am2
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, Write v)
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := S v |}, UnsetFlag)
| IncUnsetFlag1 : forall fl1 fl2 tu g,
  increment_step false
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, UnsetFlag)
                 ({| Flag1 := false; Flag2 := fl2; Turn := tu; Global := g |}, Done)
| IncUnsetFlag2 : forall fl1 fl2 tu g,
  increment_step true
                 ({| Flag1 := fl1; Flag2 := fl2; Turn := tu; Global := g |}, UnsetFlag)
                 ({| Flag1 := fl1; Flag2 := false; Turn := tu; Global := g |}, Done).

Inductive increment_final : increment_state -> Prop :=
| IncFinal : forall st,
  increment_final (st, Done).

Definition increment_ts am2 := {|
  State := increment_state;
  Super := {| Init := increment_init;
              Step := increment_step am2;
              Final := increment_final |}
|}.

Definition increment2_ts := parallel (increment_ts false) (increment_ts true).

Definition flag_for (pr : increment_program) : bool :=
  match pr with
    | SetFlag => false
    | SetTurn => true
    | ReadFlag => true
    | ReadTurn => true
    | Read => true
    | Write _ => true
    | UnsetFlag => true
    | Done => false
  end.

Definition contribution_from (pr : increment_program) : nat :=
  match pr with
  | UnsetFlag => 1
  | Done => 1
  | _ => 0
  end.

Definition in_critical_section (pr : increment_program) : Prop :=
  match pr with
  | Read => True
  | Write _ => True
  | UnsetFlag => True
  | _ => False
  end.

Definition instruction_ok (self other : increment_program) :=
  match self with
    | Write n => n = contribution_from other
    | _ => True
  end.

Inductive increment2_invariant : State increment2_ts -> Prop :=
| Inc2Inv : forall tu pr1 pr2,
  instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> (in_critical_section pr1
      -> (pr2 = SetFlag \/ pr2 = Done)
         \/ (tu = false /\ (pr2 = ReadFlag \/ pr2 = ReadTurn))
         \/ pr2 = SetTurn)
  -> (in_critical_section pr2
      -> (pr1 = SetFlag \/ pr1 = Done)
         \/ (tu = true /\ (pr1 = ReadFlag \/ pr1 = ReadTurn))
         \/ pr1 = SetTurn)
  -> increment2_invariant ({| Flag1 := flag_for pr1; Flag2 := flag_for pr2; Turn := tu;
                              Global := contribution_from pr1 + contribution_from pr2 |},
                           pr1, pr2).

Lemma Inc2Inv' : forall sh tu pr1 pr2,
  sh = {| Flag1 := flag_for pr1; Flag2 := flag_for pr2; Turn := tu;
          Global := contribution_from pr1 + contribution_from pr2 |}
  -> instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> (in_critical_section pr1
      -> (pr2 = SetFlag \/ pr2 = Done)
         \/ (tu = false /\ (pr2 = ReadFlag \/ pr2 = ReadTurn))
         \/ pr2 = SetTurn)
  -> (in_critical_section pr2
      -> (pr1 = SetFlag \/ pr1 = Done)
         \/ (tu = true /\ (pr1 = ReadFlag \/ pr1 = ReadTurn))
         \/ pr1 = SetTurn)
  -> increment2_invariant (sh, pr1, pr2).
Proof.
  intros.
  rewrite H.
  apply Inc2Inv; auto.
Qed.

Lemma final_eq : forall st,
  Final increment2_ts st
  -> increment2_invariant st
  -> exists tu, st = ({| Flag1 := false; Flag2 := false; Turn := tu; Global := 2 |}, Done, Done).
Proof.
  destruct 1.
  inversion H.
  inversion H0.
  inversion 1.
  eauto.
Qed.

Hint Resolve run_final.

Theorem increment2_ts_correct : forall st,
  run increment2_ts st
  -> exists tu, st = ({| Flag1 := false; Flag2 := false; Turn := tu; Global := 2 |}, Done, Done).
Proof.
  intros.
  apply final_eq; eauto.
  apply invariant_final; auto.
  constructor.

  destruct 1.
  inversion H0; subst.
  inversion H1; subst.
  change {| Flag1 := false; Flag2 := false; Turn := false; Global := 0 |}
  with {| Flag1 := flag_for SetFlag; Flag2 := flag_for SetFlag; Turn := false;
          Global := contribution_from SetFlag + contribution_from SetFlag |}.
  repeat constructor; simpl in *; intuition congruence.

  destruct 1.

  destruct pr2; inversion 1; subst; inversion H0; subst; eapply Inc2Inv'; simpl in *;
  intuition subst; try (reflexivity || congruence).

  destruct pr1; inversion 1; subst; inversion H0; subst; eapply Inc2Inv'; simpl in *;
  intuition subst; try (reflexivity || congruence).
Qed.
