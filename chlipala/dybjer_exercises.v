Inductive bool := true | false.

Inductive even : nat -> Prop :=
  | zero_even: even 0 
  | ssn_even: forall n, even n -> even (S (S n)).

Lemma ev8 : even 8. apply ssn_even. apply ssn_even. apply ssn_even. apply ssn_even.
                    apply zero_even.
                    Qed.