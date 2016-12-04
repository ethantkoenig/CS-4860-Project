(* Various lemmas about the BinNums and BinPos modules *)

Require Import NatIntf CanonicalNatImpl.
Require Import Cpdt.CpdtTactics.
Require Import Arith BinNums BinNatDef.

Lemma iter_op_mul : forall p n nn,
    nn = n + n ->
    BinPos.Pos.iter_op plus p nn =
      (BinPos.Pos.iter_op plus p n) + (BinPos.Pos.iter_op plus p n).
  intros p.
  induction p;
      intros n nn Heq; simpl.
    rewrite (IHp (n + n) (nn + nn)); crush. (* xI *)
    rewrite (IHp (n + n) (nn + nn)); crush. (* xO *)
    crush.                                  (* xH *)
Defined.

Lemma succ_commutes : forall n, N.to_nat (N.succ n) = S (N.to_nat n).
  destruct n;
      auto; simpl.
    (* Pos p *)
    induction p; auto;
      simpl;
      unfold BinPos.Pos.to_nat in IHp;
      unfold BinPos.Pos.to_nat;
      simpl;
      apply BinPos.Pos.iter_op_succ; apply plus_assoc.
Defined.

Lemma exists_succ : forall n, n = xH \/ exists n', n = BinPos.Pos.succ n'.
  intros n.
  induction n.
    (* xI *)
    refine (or_intror _ _).
      refine (ex_intro _ (xO n) _).
        auto.
    (* xO *)
    refine (or_intror _ _).
      refine (ex_intro _ (BinPos.Pos.pred_double n) _).
        pose (BinPos.Pos.succ_pred_double n); auto.
    (* xH *)
    refine (or_introl _ _); auto.
Defined.

Lemma pred_commutes : forall n, N.to_nat (N.pred n) = pred (N.to_nat n).
  intros n.
  induction n; simpl; auto.
   (* Pos p *)
   induction p; auto.
     (* xO *)
     simpl.
     unfold BinPos.Pos.to_nat in IHp.
     unfold BinPos.Pos.to_nat.
     simpl.
     destruct (exists_succ p) as [Hl|Hr].
       (* Hl : p = 1 *)
       rewrite Hl; auto.
       (* Hr : exists x. p = succ x *)
       destruct Hr as [x H]; rewrite H.
       rewrite (BinPos.Pos.pred_double_succ x).
       rewrite (BinPos.Pos.iter_op_succ _ plus plus_assoc x 2).
       auto.
Defined.

Lemma iter_op_add :
        forall p p' a,
        (BinPos.Pos.iter_op plus p a) + (BinPos.Pos.iter_op plus p' a)
          = BinPos.Pos.iter_op plus (BinPos.Pos.add p p') a.
  induction p.
    (* xI *)
    intros p' a.
    destruct p'; simpl;
      try rewrite (BinPos.Pos.add_carry_spec p p');
      try rewrite (BinPos.Pos.iter_op_succ _ plus plus_assoc _ (a + a));
      try rewrite <- (IHp p' (a + a));
      crush.
    (* xO *)
    intros p' a.
    destruct p'; simpl;
      try rewrite <- (IHp p' (a + a)); crush.
    (* xH *)
    intros p' a.
    destruct p'; simpl;
      try rewrite (BinPos.Pos.iter_op_succ _ plus plus_assoc _ (a + a));
      crush.
Defined.

Lemma pos_add_commutes : forall p p',
    BinPos.Pos.to_nat (BinPos.Pos.add p p') =
      (BinPos.Pos.to_nat p) + (BinPos.Pos.to_nat p').
  destruct p.
    (* xI *)
    destruct p';
        simpl; unfold BinPos.Pos.to_nat; simpl;
      [ rewrite (BinPos.Pos.add_carry_spec p p'); simpl;
        rewrite (BinPos.Pos.iter_op_succ _ plus plus_assoc _ 2);
        rewrite <- (iter_op_add p p' 2)
      | rewrite (iter_op_add p p' 2)
      | rewrite (BinPos.Pos.iter_op_succ _ plus plus_assoc _ 2) ];
      crush.
    (* xO *)
    destruct p';
      simpl; unfold BinPos.Pos.to_nat; simpl;
      try rewrite <- (iter_op_add p p' 2);
      crush.
    (* xH *)
    destruct p'; simpl; unfold BinPos.Pos.to_nat;
      try rewrite <- (BinPos.Pos.iter_op_succ _ plus plus_assoc _ 1);
      crush.
Defined.

Lemma add_commutes : forall n n',
        N.to_nat (N.add n n') = (N.to_nat n) + (N.to_nat n').
  induction n; simpl; auto.
    (* Pos p *)
    destruct n'; simpl; auto.
      (* Pos _ *)
      apply pos_add_commutes.
Defined.

Lemma pos_sub_commutes : forall p p' q,
        (BinPos.Pos.sub_mask p p' = BinPos.Pos.IsPos q) ->
        (BinPos.Pos.to_nat p) - (BinPos.Pos.to_nat p') = BinPos.Pos.to_nat q.
  intros p p' q Hsub.
  pose (Hadd := BinPos.Pos.sub_mask_add p p' q Hsub).
  pose (Hcom := pos_add_commutes p' q).
  assert (BinPos.Pos.to_nat p = BinPos.Pos.to_nat p' + BinPos.Pos.to_nat q).
    crush.
  crush.
Defined.

Lemma sub_commutes : forall n n',
        N.to_nat (N.sub n n') = (N.to_nat n) - (N.to_nat n').
  destruct n; simpl; auto.
    (* Pos p *)
    destruct n' as [|p']; simpl.
      (* Zero *)
      crush.
      (* Pos p' *)
      remember (BinPos.Pos.sub_mask p p') as sm.
      induction sm as [|pos|]; symmetry in Heqsm.
        (* IsNul *)
        destruct (BinPos.Pos.sub_mask_nul_iff p p') as [H _].
        rewrite (H Heqsm).
        crush.
        (* IsPos pos *)
        rewrite (pos_sub_commutes p p' pos Heqsm).
        auto.
        (* IsNeg *)
        simpl.
        destruct (BinPos.Pos.sub_mask_neg_iff p p') as [H _].
        destruct (H Heqsm) as [q H'].
        pose (H'' := pos_add_commutes p q).
        rewrite H' in H''.
        crush.
Defined.

Lemma pos_comp_eq : forall p p',
        BinPos.Pos.compare p p' = Eq -> BinPos.Pos.to_nat p = BinPos.Pos.to_nat p'.
  intros p p'.
  pose (BinPos.Pos.compare_eq_iff p p').
  crush.
Defined.

Lemma to_nat_pos : forall p, BinPos.Pos.to_nat p > 0.
  intros p.
  unfold BinPos.Pos.to_nat.
  induction p.
    (* xI *)
    crush.
    (* xO *)
    simpl.
    rewrite (iter_op_mul p 1 _); crush.
    (* xH *)
    auto.
Defined.

Lemma pos_to_nat_inj : forall p p',
    BinPos.Pos.to_nat p = BinPos.Pos.to_nat p' -> p = p'.
  induction p;
      destruct p'; unfold BinPos.Pos.to_nat; simpl;
      try rewrite (iter_op_mul p 1 _); auto;
      try rewrite (iter_op_mul p' 1 _); auto;
      intros Heq; simpl in Heq.
    (* xI xI *)
    assert (BinPos.Pos.to_nat p = BinPos.Pos.to_nat p') as Heq'.
      unfold BinPos.Pos.to_nat.
      crush.
    rewrite (IHp p' Heq'); crush.
    (* xI xO *)
    crush.
    (* xI xH *)
    pose (H := to_nat_pos p).
    unfold BinPos.Pos.to_nat in H; crush.
    (* xO xI *)
    crush.
    (* xO xO *)
    assert (BinPos.Pos.to_nat p = BinPos.Pos.to_nat p') as Heq'.
      unfold BinPos.Pos.to_nat.
      crush.
    rewrite (IHp p' Heq'); reflexivity.
    (* xO xH *)
    pose (H := to_nat_pos p).
    unfold BinPos.Pos.to_nat in H; crush.
    (* xH xI *)
    pose (Hpos := to_nat_pos p').
    unfold BinPos.Pos.to_nat in Hpos.
    crush.
    (* xH xO *)
    pose (Hpos := to_nat_pos p').
    unfold BinPos.Pos.to_nat in Hpos.
    crush.
Defined.

Lemma pos_comp_lt : forall p p',
        BinPos.Pos.compare p p' = Lt -> BinPos.Pos.to_nat p < BinPos.Pos.to_nat p'.
  intros p p' Hlt.
  destruct (BinPos.Pos.lt_iff_add p p') as [H _].
  destruct (H Hlt) as (r, H').
  assert (BinPos.Pos.to_nat p' = BinPos.Pos.to_nat p + BinPos.Pos.to_nat r).
    rewrite <- H'.
    apply pos_add_commutes.
  pose (Hpos := to_nat_pos r).
  crush.
Defined.

Lemma pos_comp_gt : forall p p',
        BinPos.Pos.compare p p' = Gt -> BinPos.Pos.to_nat p > BinPos.Pos.to_nat p'.
  intros p p' Hgt.
  destruct (BinPos.Pos.gt_iff_add p p') as [H _].
  destruct (H Hgt) as (r, H').
  assert (BinPos.Pos.to_nat p = BinPos.Pos.to_nat p' + BinPos.Pos.to_nat r).
    rewrite <- H'.
    apply pos_add_commutes.
  pose (Hpos := to_nat_pos r).
  crush.
Defined.

Lemma nonzero_succ : forall n, n > 0 -> exists n', n = S n'.
  intros n; remember n as n'.
  destruct n'.
    crush.
    intros _; refine (ex_intro _ n' _); reflexivity.
Defined.

Lemma comp_commutes : forall b b',
        N.compare b b' = CanonicalNat.comp (N.to_nat b) (N.to_nat b').
  destruct b.
    (* Zero *)
    destruct b'; auto.
      (* Pos p *)
      unfold N.compare; unfold N.to_nat.
      destruct (nonzero_succ _ (to_nat_pos p)) as [n H].
      rewrite H.
      auto.
   (* Pos p *)
   destruct b' as [|p'];
       simpl.
     (* Zero *)
     destruct (nonzero_succ _ (to_nat_pos p)) as [n H].
     rewrite H.
     auto.
     (* Pos p' *)
     remember (BinPos.Pos.compare p p') as res.
     destruct res; symmetry;
       [ pose (pos_comp_eq p p') as Heq; apply comp_eq
       | pose (pos_comp_lt p p') as Heq; apply comp_lt
       | pose (pos_comp_gt p p') as Heq; apply comp_gt];
       crush.
Defined.

Lemma to_nat_inj : forall n n', N.to_nat n = N.to_nat n' -> n = n'.
  destruct n as [|p];
    destruct n' as [|p']; auto.
      (* Zero, Pos p' *)
      pose (to_nat_pos p'); crush.
      (* Pos p, Zero *)
      pose (to_nat_pos p); crush.
      (* Pos p, Pos p' *)
      intros Heq.
      rewrite (pos_to_nat_inj p p' Heq).
      reflexivity.
Defined.
