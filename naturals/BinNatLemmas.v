Require Import Naturals.NatIntf Naturals.CanonicalNatImpl.
Require Import Cpdt.CpdtTactics.
Require Import Arith BinNums BinNatDef.


Lemma iter_op_mul : forall p n,
        BinPos.Pos.iter_op plus p n = n * (BinPos.Pos.iter_op plus p 1).
  intros p.
  induction p.
    (* xI *)
    simpl.
    intros n.
    rewrite (IHp (n + n)).
    rewrite (IHp 2).
    simpl.
    rewrite (plus_0_r _).
    rewrite (mult_comm n _).
    simpl.
    rewrite (mult_comm _ n).
    rewrite (mult_plus_distr_r n n _).
    rewrite (mult_plus_distr_l n _ _).
    congruence.
    (* xO *)
    simpl.
    intros n.
    rewrite (IHp (n + n)).
    rewrite (IHp 2).
    simpl.
    rewrite (plus_0_r _).
    rewrite (mult_plus_distr_r n n _).
    rewrite (mult_plus_distr_l n _ _).
    congruence.
    (* xH *)
    crush.
Defined.


Lemma succ_commutes : forall n, N.to_nat (N.succ n) = S (N.to_nat n).
  intros n.
  induction n.
    (* Zero *)
    auto.
    (* Pos *)
    simpl.
    induction p.
      (* xI *)
      simpl.
      unfold BinPos.Pos.to_nat in IHp.
      unfold BinPos.Pos.to_nat.
      simpl.
      apply (BinPos.Pos.iter_op_succ).
        apply plus_assoc.
      (* xO *)
      simpl.
      unfold BinPos.Pos.to_nat in IHp.
      unfold BinPos.Pos.to_nat.
      simpl.  
      congruence.
      (* 1 *)
      auto.
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
        pose (BinPos.Pos.succ_pred_double n); symmetry; assumption.
    (* xH *)
    refine (or_introl _ _); auto.
Defined.

Lemma pred_commutes : forall n, N.to_nat (N.pred n) = pred (N.to_nat n).
  intros n.
  induction n.
   (* Zero *)
   auto.
   (* positive *)
   simpl.
   induction p.
     (* xI *)
     simpl.
     unfold BinPos.Pos.to_nat.
     simpl.
     congruence.
     (* xO *)
     simpl.
     unfold BinPos.Pos.to_nat in IHp.
     unfold BinPos.Pos.to_nat.
     simpl.
     destruct (exists_succ p) as [H|H].
       (* H : p = 1 *)
       rewrite H; auto.
       (* H : exists x. p = succ x *)
       destruct H.
       rewrite H.
       rewrite (BinPos.Pos.pred_double_succ x).
       simpl.
       rewrite (BinPos.Pos.iter_op_succ _ plus plus_assoc x 2).
       simpl.
       congruence.
  (* xH *)
  auto.
Defined.

Lemma iter_op_add : forall A (op:A->A->A),
        (forall x y, op x y = op y x) -> 
        (forall x y z, op x (op y z) = op (op x y) z) ->
        forall p p' a, 
        op (BinPos.Pos.iter_op op p a) (BinPos.Pos.iter_op op p' a)
          = BinPos.Pos.iter_op op (BinPos.Pos.add p p') a.
  intros A op op_comm op_assoc.
  intros p.
  induction p.
    (* xI *)
    intros p' a.
    induction p'.
      (* xI *)
      clear IHp'.
      simpl.
      rewrite (BinPos.Pos.add_carry_spec p p').
      rewrite (BinPos.Pos.iter_op_succ A op op_assoc _ (op a a)).
      rewrite <- (IHp p' (op a a)).
      crush.
      (* xO *)
      clear IHp'.
      simpl.
      rewrite <- (IHp p' (op a a)). 
      crush.
      (* xH *)
      simpl.
      rewrite (BinPos.Pos.iter_op_succ A op op_assoc _ (op a a)).
      crush.
    (* xO *)
    intros p' a.
    induction p'.
      (* xI *)
      clear IHp'.
      simpl.
      rewrite <- (IHp p' (op a a)).
      crush.
      (* xO *)
      clear IHp'.
      simpl.
      rewrite <- (IHp p' (op a a)).
      congruence.
      (* xH *)
      crush.
    (* xH *)
    intros p' a.
    induction p'.
      (* xI *)
      simpl.
      rewrite (BinPos.Pos.iter_op_succ A op op_assoc _ (op a a)).
      crush.
      (* xO *)
      simpl; congruence.
      (* xH *)
      auto.
Defined.
    
    
      


Lemma pos_add_commutes : forall p p',
        BinPos.Pos.to_nat (BinPos.Pos.add p p') = (BinPos.Pos.to_nat p) + (BinPos.Pos.to_nat p').
  intros p.
  induction p.
    (* xI *)
    intros p'.
    induction p'; simpl; unfold BinPos.Pos.to_nat.
      (* xI *)
      clear IHp'.
      rewrite (BinPos.Pos.add_carry_spec p p').
      simpl.
      rewrite (BinPos.Pos.iter_op_succ _ plus plus_assoc _ 2).
      rewrite <- (iter_op_add _ plus plus_comm plus_assoc p p' 2).
      crush.
      (* xO *)
      clear IHp'.
      simpl.
      rewrite (iter_op_add _ plus plus_comm plus_assoc p p' 2).
      congruence.
      (* xH *)
      simpl.
      rewrite (BinPos.Pos.iter_op_succ _ plus plus_assoc _ 2).
      crush.
    (* xO *)   
    intros p'.
    induction p'; simpl; unfold BinPos.Pos.to_nat.
      (* xI *)
      clear IHp'.
      simpl.
      rewrite <- (iter_op_add _ plus plus_comm plus_assoc p p' 2).
      crush.
      (* xO *)
      clear IHp'.
      simpl.
      rewrite <- (iter_op_add _ plus plus_comm plus_assoc p p' 2).
      congruence.
      (* xH *)
      crush.
    (* xH *)
    induction p'.
      (* xI *)
      simpl.
      unfold BinPos.Pos.to_nat.
      rewrite <- (BinPos.Pos.iter_op_succ _ plus plus_assoc _ 1).
      simpl.
      congruence.
      (* xO *)
      crush.
      (* xH *)
      crush.
Defined.      

Lemma add_commutes : forall n n', 
        N.to_nat (N.add n n') = (N.to_nat n) + (N.to_nat n').
  intros n.
  induction n.
    (* Zero *)
    simpl; congruence.
    (* positive *)
    intros n'.
    induction n'.
      (* Zero *)
      simpl; auto.
      (* positive *)
      simpl.
      apply pos_add_commutes.
Defined.

Lemma pos_sub_commutes : forall p p' q,
        (BinPos.Pos.sub_mask p p' = BinPos.Pos.IsPos q) ->
        (BinPos.Pos.to_nat p) - (BinPos.Pos.to_nat p') = BinPos.Pos.to_nat q.
  intros p p' q.
  intros Hsub.
  pose (Hadd := BinPos.Pos.sub_mask_add p p' q Hsub).
  pose (Hcom := pos_add_commutes p' q).
  assert (BinPos.Pos.to_nat p = BinPos.Pos.to_nat p' + BinPos.Pos.to_nat q).
    crush.
  crush.
Defined.

Lemma sub_commutes : forall n n',
        N.to_nat (N.sub n n') = (N.to_nat n) - (N.to_nat n').
  intros n.
  induction n.
    (* Zero *)
    simpl; auto.
    (* positive *)
    intros n'.
    induction n'.
      (* Zero *)      
      crush.
      (* positive *)
      simpl.
      remember (BinPos.Pos.sub_mask p p0) as sm.
      induction sm; symmetry in Heqsm.
        (* IsNul *)
        destruct (BinPos.Pos.sub_mask_nul_iff p p0) as [H _].
        rewrite (H Heqsm).
        crush.
        (* IsPos *)
        rewrite (pos_sub_commutes p p0 p1 Heqsm).
        auto.
        (* IsNeg *)
        simpl.
        destruct (BinPos.Pos.sub_mask_neg_iff p p0) as [H _].
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
    rewrite (iter_op_mul p 2).
    crush.
    (* xH *)
    auto.
Defined.

Lemma pos_to_nat_inj : forall p p',
    BinPos.Pos.to_nat p = BinPos.Pos.to_nat p' -> p = p'.
  intros p.
  induction p.
    (* xI *)
    intros p'.
    destruct p';
        unfold BinPos.Pos.to_nat; simpl.
      (* xI *)
      rewrite (iter_op_mul p _).
      rewrite (iter_op_mul p' _).
      intros Heq.
      assert (BinPos.Pos.to_nat p = BinPos.Pos.to_nat p') as Heq'.
        unfold BinPos.Pos.to_nat.
        crush.
      rewrite (IHp p' Heq'); reflexivity.
      (* xO *)
      rewrite (iter_op_mul p _).
      rewrite (iter_op_mul p' _).
      crush.
      (* xH *)
      rewrite (iter_op_mul p _).
      pose (H := to_nat_pos p).
      unfold BinPos.Pos.to_nat in H.
      crush.
    (* xO *)
      intros p'.
      destruct p';
          unfold BinPos.Pos.to_nat; simpl.
      (* xI *)
      rewrite (iter_op_mul p _).
      rewrite (iter_op_mul p' _).
      crush.
      (* xO *)
      rewrite (iter_op_mul p _).
      rewrite (iter_op_mul p' _).
      intros Heq.
      assert (BinPos.Pos.to_nat p = BinPos.Pos.to_nat p') as Heq'.
        unfold BinPos.Pos.to_nat.
        crush.
      rewrite (IHp p' Heq'); reflexivity.
      (* xH *)
      rewrite (iter_op_mul p _).
      pose (H := to_nat_pos p).
      unfold BinPos.Pos.to_nat in H.
      crush.
    (* xH *)
    admit. (* TODO *)
Defined.


Lemma pos_comp_lt : forall p p',
        BinPos.Pos.compare p p' = Lt -> BinPos.Pos.to_nat p < BinPos.Pos.to_nat p'.
  intros p p' Hlt.
  destruct (BinPos.Pos.lt_iff_add p p') as [H _].
  destruct (H Hlt) as (r, H').
  assert (BinPos.Pos.to_nat p' = BinPos.Pos.to_nat p + BinPos.Pos.to_nat r).
    rewrite <- H'.
    apply pos_add_commutes.
  assert (BinPos.Pos.to_nat r > 0).
    apply to_nat_pos.
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
  assert (BinPos.Pos.to_nat r > 0).
    apply to_nat_pos.
  crush.
Defined.

Require Import CanonicalNatImpl.

Lemma duh2 : forall n, n > 0 -> exists n', n = S n'.
  intros n.
  remember n as n'.
  induction n'.
    crush.
    intros useless; clear useless.
    refine (ex_intro _ n' _); reflexivity.
Defined.


Lemma comp_commutes : forall b b',
        N.compare b b' = CanonicalNaturalImpl.comp (N.to_nat b) (N.to_nat b').
  intros b.
  destruct b.
    (* zero *)
    intros b'.
    destruct b'.
      (* zero *)
      auto.
      (* positive *)
      unfold N.compare.
      unfold N.to_nat.
      destruct (duh2 _ (to_nat_pos p)) as [n H].
      rewrite H.
      simpl.
      congruence.
   (* positive *)
   intros b'.
   destruct b'.
     (* zero *)
     simpl.
     destruct (duh2 _ (to_nat_pos p)) as [n H].
     rewrite H.
     simpl.
     congruence.
     (* positive *)
     simpl.
     remember (BinPos.Pos.compare p p0) as res.
     destruct res; symmetry.
       (* Eq *)
       pose (pos_comp_eq p p0) as Heq.
       apply comp_eq.
       crush.
       (* Lt *)
       pose (pos_comp_lt p p0) as Hlt.
       apply comp_lt.
       crush.
       (* Gt *)
       pose (pos_comp_gt p p0) as Hgt.
       apply comp_gt.
       crush.
Defined.
       
Lemma to_nat_inj : forall n n', N.to_nat n = N.to_nat n' -> n = n'.
  intros n.
  destruct n.
    intros n'.
    destruct n'.
      auto.
      simpl.
      pose (to_nat_pos p); crush.
    intros n'.
    destruct n'.
      pose (to_nat_pos p); crush.

      simpl.
      intros Heq.
      rewrite (pos_to_nat_inj p p0 Heq).
      reflexivity.
Defined.
