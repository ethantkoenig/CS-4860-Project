Require Import Arith.
Require Import NatIntf CanonicalNatImpl CommutingNatIntf.

Module Type VerifiedNaturalInterface <: CommutingNaturalInterface.
  Parameter N : Type.

  Parameter zero : N.
  Parameter succ : N -> N.
  Parameter pred : N -> N.
  Parameter add : N -> N -> N.
  Parameter sub : N -> N -> N.
  Parameter comp : N -> N -> comparison.
  Parameter inject : N -> nat.

  Axiom injective : forall n n' : N, inject n = inject n' -> n = n'.
  Axiom zero_commutes : inject zero = CanonicalNaturalImpl.zero.
  Axiom succ_commutes : forall n : N,
    inject (succ n) = CanonicalNaturalImpl.succ (inject n).
  Axiom pred_commutes : forall n : N,
    inject (pred n) = CanonicalNaturalImpl.pred (inject n).
  Axiom add_commutes : forall n n' : N,
    inject (add n n') = CanonicalNaturalImpl.add (inject n) (inject n').
  Axiom sub_commutes : forall n n' : N,
    inject (sub n n') = CanonicalNaturalImpl.sub (inject n) (inject n').
  Axiom comp_commutes : forall n n' : N,
    comp n n' = CanonicalNaturalImpl.comp (inject n) (inject n').

  Axiom pos_succ : forall (n:N), comp n zero = Gt -> exists n', n = succ n'.
  Axiom pred_succ : forall (n:N), pred (succ n) = n.

  Axiom add_zero : forall (n:N), add zero n = n.
  Axiom add_succ : forall (m n:N), add (succ m) n = succ (add m n).
  Axiom add_succ_right : forall (m n:N), add m (succ n) = add (succ m) n.

  Axiom sub_zero : forall (n:N), sub n zero = n.
  Axiom sub_succ : forall (m n:N), sub (succ m) (succ n) = sub m n.
  Axiom sub_pred : forall (m n:N), sub (pred m) n = sub m (succ n).

  Axiom comp_zero : forall (n:N), comp n zero <> Lt.
  Axiom comp_succ : forall (m n:N), comp (succ m) (succ n) = comp m n.
  Axiom comp_eq : forall (m n:N), comp m n = Eq <-> m = n.
  Axiom comp_zero_succ : forall (n:N), comp zero (succ n) = Lt.
End VerifiedNaturalInterface.

Module VerifiedCommutingNaturalImpl (C : CommutingNaturalInterface) : VerifiedNaturalInterface.
  Definition N := C.N.
  Definition zero := C.zero.
  Definition succ := C.succ.
  Definition pred := C.pred.
  Definition add := C.add.
  Definition sub := C.sub.
  Definition comp := C.comp.
  Definition inject := C.inject.
  Definition injective := C.injective.
  Definition zero_commutes := C.zero_commutes.
  Definition succ_commutes := C.succ_commutes.
  Definition pred_commutes := C.pred_commutes.
  Definition add_commutes := C.add_commutes.
  Definition sub_commutes := C.sub_commutes.
  Definition comp_commutes := C.comp_commutes.

  Lemma pos_succ : forall (n:N),
      comp n C.zero = Gt -> exists n', n = succ n'.
    intros n.
    rewrite comp_commutes.
    rewrite zero_commutes.
    remember (C.inject n) as m.
    destruct m;
        symmetry in Heqm; simpl.
      (* 0 *)
      congruence.
      (* S m *)
      intros _.
      refine (ex_intro _ (pred n) _).
        apply C.injective.
        rewrite succ_commutes.
        rewrite pred_commutes.
        rewrite Heqm.
        simpl.
        reflexivity.
  Defined.

  Lemma pred_succ : forall (n:N), pred (succ n) = n.
    intros n.
    apply C.injective.
    rewrite C.pred_commutes.
    rewrite C.succ_commutes.
    auto.
  Defined.

  Lemma add_zero : forall (n:N), add C.zero n = n.
    intros n.
    apply (C.injective).
    rewrite (C.add_commutes _ _).
    rewrite (C.zero_commutes).
    auto.
  Defined.

  Lemma add_succ : forall (m n : N), add (succ m) n = succ (add m n).
    intros m n.
    apply (C.injective).
    rewrite (C.add_commutes _ _).
    rewrite (C.succ_commutes _).
    rewrite (C.succ_commutes _).
    rewrite (C.add_commutes _ _).
    simpl.
    reflexivity.
  Defined.

  Lemma add_succ_right : forall (m n : N),
      add m (succ n) = add (succ m) n.
    intros m n.
    apply (C.injective).
    rewrite (C.add_commutes _ _).
    rewrite (C.succ_commutes _).
    rewrite (C.add_commutes _ _).
    rewrite (C.succ_commutes _).
    rewrite plus_Snm_nSm.
    reflexivity.
  Defined.

  Lemma sub_zero : forall (n : N), sub n C.zero = n.
    intros n.
    apply C.injective.
    rewrite (C.sub_commutes _ _).
    rewrite C.zero_commutes.
    destruct (C.inject n); auto.
  Defined.

  Lemma sub_succ : forall (m n:N), sub (succ m) (succ n) = sub m n.
    intros m n.
    apply C.injective.
    rewrite C.sub_commutes.
    rewrite C.sub_commutes.
    rewrite C.succ_commutes.
    rewrite C.succ_commutes.
    auto.
  Defined.

  Lemma sub_pred : forall (m n:N), sub (pred m) n = sub m (succ n).
    intros m n.
    apply C.injective.
    rewrite C.sub_commutes.
    rewrite C.sub_commutes.
    rewrite C.pred_commutes.
    rewrite C.succ_commutes.
    destruct (C.inject m);
      simpl; reflexivity.
  Defined.

  Lemma comp_zero :forall (n:N), comp n C.zero <> Lt.
    intros n.
    rewrite C.comp_commutes.
    rewrite C.zero_commutes.
    destruct (C.inject n);
      simpl; congruence.
  Defined.

  Lemma comp_succ : forall (m n:N), comp (succ m) (succ n) = comp m n.
    intros m n.
    rewrite C.comp_commutes.
    rewrite C.comp_commutes.
    rewrite C.succ_commutes.
    rewrite C.succ_commutes.
    auto.
  Defined.

  Lemma comp_eq : forall (m n:N), comp m n = Eq <-> m = n.
    intros m n.
    refine (conj _ _).
      (* -> *)
      rewrite (C.comp_commutes _ _).
      intros Hcomp.
      apply C.injective.
      apply (CanonicalNatImpl.comp_eq).
      assumption.
      (* <- *)
      intros Heq.
      rewrite Heq.
      rewrite (C.comp_commutes _ _).
      apply (CanonicalNatImpl.comp_eq).
      reflexivity.
  Defined.

  Lemma comp_zero_succ : forall (n:N), comp C.zero (succ n) = Lt.
    intros n.
    rewrite (C.comp_commutes _ _).
    rewrite C.zero_commutes.
    rewrite (C.succ_commutes _).
    simpl.
    reflexivity.
  Defined.
End VerifiedCommutingNaturalImpl.