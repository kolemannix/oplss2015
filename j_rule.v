Set Implicit Arguments.

Section EqdepDec.

  Variable A : Type.

  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    eq_ind _ (fun a => a = y') eq2 _ eq1.

  Check eq_ind.
  Check comp.

  Check refl_equal.

  Remark trans_sym_eq : forall (x y:A) (u:x = y), comp u u = refl_equal y.
  Proof.
    intros. Check comp u u.
    case u; trivial.
  Qed.

  Variable eq_dec : forall x y:A, x = y \/ x <> y.

  Variable x : A.

  Let nu (y:A) (u:x = y) : x = y :=
    match eq_dec x y with
      | or_introl eqxy => eqxy
      | or_intror neqxy => False_ind _ (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
    intros.
    unfold nu in |- *.
    case (eq_dec x y); intros.
    reflexivity.

    case n; trivial.
  Qed.

  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (refl_equal x)) v.

  Remark nu_left_inv : forall (y:A) (u:x = y), nu_inv (nu u) = u.
  Proof.
    intros.
    case u; unfold nu_inv in |- *.
    apply trans_sym_eq.
  Qed.

  Theorem eq_proofs_unicity : forall (y:A) (p1 p2:x = y), p1 = p2.
  Proof.
    intros.
    elim nu_left_inv with (u := p1).
    elim nu_left_inv with (u := p2).
    elim nu_constant with y p1 p2.
    reflexivity.
  Qed.

  Theorem K_dec : 
    forall P:x = x -> Prop, P (refl_equal x) -> forall p:x = x, P p.
  Proof.
    intros.
    elim eq_proofs_unicity with x (refl_equal x) p.
    trivial.
  Qed.