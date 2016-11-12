Require Import Arith Bool List.
Require Import Cpdt.CpdtTactics.

Import ListNotations.


Fixpoint value (l : list bool) : nat :=
  match l with
  | [] => 0
  | false :: l' => value l' + value l'
  | true :: l' => S (value l' + value l')
  end.


Fixpoint strip (l : list bool) : list bool :=
  match l with
  | [] => []
  | false :: l' =>
      match strip l' with
      | [] => []
      | l'' => false :: l'
      end
  | true :: l' => true :: strip l'
  end.

Lemma strip_same_value : forall l, value l = value (strip l).
  intros l.
  induction l.
    (* [] *)
    crush.
    (* a :: l *)
    simpl.
    induction a.
      (* true *)
      crush.
      (* false *)
      induction (strip l); crush.
Defined.

Fixpoint succ_bl (l : list bool) : list bool :=
  match l with
  | [] => [true]
  | false :: l' => true :: l'
  | true :: l' => false :: succ_bl l'
  end.

Fixpoint pred_bl' (l : list bool) : list bool :=
  match l with
  | [] => []
  | true :: l' => false :: l'
  | false :: l' =>
      match pred_bl' l' with
      | [] => []
      | l'' => true :: l''
      end
  end.

Lemma pred_bl'_lemma : forall l, pred_bl' l = [] -> value l = 0.
  intros l.
  induction l.
    crush.
    induction a.
      crush.
      remember (pred_bl' l) as pbl.
      induction pbl as [ | a pbl' ].
        crush.
        simpl.
        rewrite <- Heqpbl.
        congruence.
Defined.

Lemma pred_bl'_lemma2 : forall l, pred_bl' l <> [] -> value l > 0.
  intros l.
  induction l.
    (* [] *)
    crush.
    (* a :: l *)
    simpl.
    induction a.
      (* true *)
      crush.
      (* false *)
      remember (pred_bl' l) as pbl.
      destruct pbl.
        (* [] *)
        crush.
        (* _ :: _ *)
        assert (value l > 0) as Hpos.
          apply IHl; crush.
        crush.
Defined.

Lemma pred_bl'_lemma3 : forall l, value (pred_bl' l) = pred (value l).
  intros l.
  induction l.
    (* [] *)
    crush.
    (* a :: l *)
    induction a.
      (* true *)
      crush.
      (* false *)
      simpl.
      remember (pred_bl' l) as pbl.
      induction pbl.
        (* [] *)
        simpl.
        assert (value l = 0) as H.
          apply (pred_bl'_lemma l).
          crush.
        crush.
        (* a :: pbl *)
        simpl.
        induction a.
          (* true *)
          crush.
          (* false *)
          simpl in IHl.
          assert (value l > 0) as Hpos.
            apply pred_bl'_lemma2; crush.
          crush.
Defined.

Fixpoint add_bl (carry : bool) (l l' : list bool) : list bool :=
  match carry, l, l' with
  | false, [], _ => l'
  | true, [], _ => succ_bl l'
  | false, _, [] => l
  | true, _, [] => succ_bl l
  | _, x::t, x'::t' =>
      let (x'', carry') :=
        match carry, x, x' with
        | false, false, false => (false, false)
        | true, false, false
        | false, true, false
        | false, false, true => (true, false)
        | true, true, false
        | true, false, true
        | false, true, true => (false, true)
        | true, true, true => (true, true)
        end in
      x'' :: add_bl carry' t t'
  end.


Lemma add_bl_comm : forall l c l', add_bl c l l' = add_bl c l' l.
  intros l.
  induction l.
    (* l = [] *)
    intros c l'.
    induction l'; crush.
    (* a :: l *)
    intros c l'.
    induction l'.
      (* l' = [] *)
      crush.
      (* a0 :: l' *)
      simpl.
      induction c; induction a; induction a0; crush.
Defined.

Lemma succ_value : forall l, S (value l) = value (succ_bl l).
  intros l.
  induction l.
    crush.
    induction a; crush.
Defined.

Lemma add_succ : forall l1 l2,
        S (value (add_bl false l1 l2)) = value (add_bl true l1 l2).
  intros l1.
  induction l1.
    crush; apply succ_value.

    intros l'.
    simpl.
    induction l'.
      (* [] *)
      induction a.
        (* true *)
        simpl.
        rewrite <- (succ_value l1); crush.
        (* false *)
        crush.
      (* a0 :: l' *)
        simpl.
        induction a.
          (* true *)
          induction a0.
            (* true *)
            auto.
            (* false *)
            simpl.
            rewrite <- (IHl1 l').
            crush.
          (* false *)
          induction a0.
            (* true *)
            simpl.
            rewrite <- (IHl1 l').
            crush.
            (* false *)
            auto.
Defined.

Lemma add_value : forall l1 l2,
        value (add_bl false l1 l2) = value l1 + value l2.
  intros l1.
  induction l1.
    (* [] *)
    crush.

    (* a :: l *)
    intros l'.
    induction l'.
      (* [] *)
      crush.

      (* a0 :: l' *)
      simpl.
      induction a.
        (* true *)
        induction a0.
          (* true *)
          simpl.
          rewrite <- (add_succ l1 l').
          rewrite (IHl1 l').
          crush.
          (* false *)
          simpl.
          rewrite (IHl1 l').
          crush.
        induction a0; crush.
Defined.
