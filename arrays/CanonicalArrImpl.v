Require Import List.
Require Import Cpdt.CpdtTactics.
Require Import NatIntf ArrayIntf VerifiedNatIntf.

Set Implicit Arguments.
Import ListNotations.

Module Type CanonicalArrayIntf (N : VerifiedNaturalInterface) <: ArrayInterface N with Definition M := list.
  Definition M := list.

  Parameter make : forall A : Type, nat -> A -> M A.
  Parameter len : forall A : Type, M A -> N.N.
  Parameter get : forall A : Type, M A -> N.N -> option A.
  Parameter set : forall A : Type, M A -> N.N -> A -> M A.
  Parameter concat : forall A : Type, M A -> M A -> M A.

  Axiom make_def : forall A (n:nat) (x:A),
      make n x = match n with
                 | O => []
                 | S n' => x::make n' x
                 end.
  Axiom len_def : forall A (l:list A), 
      len l = match l with
              | [] => N.zero
              | _::t => N.succ (len t)
              end.
  Axiom get_def : forall A (l:list A) (n:N.N),
      get l n = match l with
                | [] => None
                | h::t => 
                    match N.comp n N.zero with
                    | Lt 
                    | Eq => Some h
                    | Gt => get t (N.pred n)
                    end
                end.
  Axiom set_def : forall A (l:list A) (n:N.N) (x:A),
      set l n x = match l with
                  | [] => []
                  | h::l' =>
                      match N.comp n N.zero with
                      | Lt
                      | Eq => x::l'
                      | Gt => h::set l' (N.pred n) x
                      end
                  end.
  Axiom concat_def : forall A (l l':list A), concat l l' = l ++ l'.

  Axiom len_make : forall A (n:nat) (x:A),
      N.inject (len (make n x)) = n.
  Axiom concat_make : forall A (m n:nat) (x:A),
      concat (make m x) (make n x) = make (m + n) x.
  Axiom make_concat : forall A (l l':list A) (n:nat) (x:A),
      concat l l' = make n x -> exists m m', l = make m x /\ l' = make m' x /\ m + m' = n. 
  Axiom len_concat : forall A (l l' : list A), 
      len (concat l l') = N.add (len l) (len l').
  Axiom get_concat : forall A (l r : list A) (n:N.N), get (concat l r) n =
      match N.comp n (len l) with
      | Lt => get l n
      | Eq
      | Gt => get r (N.sub n (len l))
      end.
  Axiom set_concat : forall A (l l':list A) (n:N.N) (x:A), set (concat l l') n x =
      match N.comp n (len l) with
      | Lt => concat (set l n x) l'
      | Eq
      | Gt => concat l (set l' (N.sub n (len l)) x)
      end.
End CanonicalArrayIntf.

Module CanonicalArrayImpl (N : VerifiedNaturalInterface) : CanonicalArrayIntf N 
    with Definition M := list.
  Definition M := list.

  Fixpoint make A (n : nat) (x : A) : list A :=
    match n with
    | O => []
    | S n' => x::make n' x
   end.

  Fixpoint len A (ls : list A) : N.N :=
    match ls with
    | [] => N.zero
    | _::t => N.succ (len t)
    end.

  Fixpoint get A (ls : list A) (index : N.N) : option A :=
    match ls with
    | [] => None
    | h::t => 
        match N.comp index N.zero with
        | Lt 
        | Eq => Some h
        | Gt => get t (N.pred index)
        end
    end.

  Fixpoint set A (ls : list A) (index : N.N) (x : A) : list A :=
    match ls with
    | [] => []
    | h::ls' =>
        match N.comp index N.zero with
        | Lt
        | Eq => x::ls'
        | Gt => h::set ls' (N.pred index) x
        end
    end.

  Definition concat A (l l' : list A) : list A := l ++ l'.

  Lemma make_def : forall A (n:nat) (x:A),
      make n x = match n with
                 | O => []
                 | S n' => x::make n' x
                 end.
    intros; destruct n; auto.
  Defined.

  Lemma len_def : forall A (l:list A), 
      len l = match l with
              | [] => N.zero
              | _::t => N.succ (len t)
              end.
    intros; destruct l; auto.
  Defined.

  Lemma get_def : forall A (l:list A) (n:N.N),
      get l n = match l with
                | [] => None
                | h::t => 
                    match N.comp n N.zero with
                    | Lt 
                    | Eq => Some h
                    | Gt => get t (N.pred n)
                    end
                end.
    intros; destruct l; auto.
  Defined.

  Lemma set_def : forall A (l:list A) (n:N.N) (x:A),
      set l n x = match l with
                  | [] => []
                  | h::l' =>
                      match N.comp n N.zero with
                      | Lt
                      | Eq => x::l'
                      | Gt => h::set l' (N.pred n) x
                      end
                  end.
    intros; destruct l; auto.
  Defined.

  Lemma concat_def : forall A (l l':list A), concat l l' = l ++ l'.
    intros; auto.
  Defined.

  Lemma len_make : forall A (n:nat) (x:A),
      N.inject (len (make n x)) = n.
    intros A n x.
    induction n;
        simpl.
      (* 0 *)
      rewrite N.zero_commutes.
      auto.
      (* S n *)
      rewrite N.succ_commutes.
      rewrite IHn.
      auto.
  Defined.

  Lemma concat_make : forall A (m n:nat) (x:A),
      concat (make m x) (make n x) = make (m + n) x.
    intros A m n x.
    induction m;
        simpl.
      reflexivity.
      rewrite IHm.
      reflexivity.
  Defined.
 
  Lemma make_concat : forall A (l l':list A) (n:nat) (x:A),
      concat l l' = make n x -> 
        exists m m', l = make m x /\ l' = make m' x /\ m + m' = n.
    intros A l l'.
    induction l;
        intros n x;
        simpl.
      (* [] *)
      intros Heq.
      refine (ex_intro _ 0 _).
      refine (ex_intro _ n _).
      auto.
      (* a::l *)
      destruct n;
          simpl.
        (* 0 *)
        congruence.
        (* S n *)
        intros Heq.
        assert (a = x) as Ha. congruence.
        rewrite Ha; clear Ha.
        assert (concat l l' = make n x) as H. congruence.
        destruct (IHl n x H) as [m H'].
        destruct H' as [m' H''].
        refine (ex_intro _ (S m) _).  
        refine (ex_intro _ m' _).
        crush.
  Defined.

  Lemma len_concat : forall A (l l' : list A), 
      len (concat l l') = N.add (len l) (len l').
    intros.
    induction l.
      (* [] *)
      simpl.
      rewrite (N.add_zero).
      reflexivity.
      (* a :: l *)
      simpl.
      rewrite (N.add_succ).
      rewrite IHl.
      reflexivity.
  Defined.

  Lemma get_concat : forall A (l r:list A) (n:N.N), get (concat l r) n =
      match N.comp n (len l) with
      | Lt => get l n
      | Eq
      | Gt => get r (N.sub n (len l))
      end.
    intros A l.
    induction l;
        intros r n; simpl.
      (* [] *)
      rewrite (N.sub_zero n).
      remember (N.comp n N.zero) as cmp.
      destruct cmp;
          symmetry in Heqcmp.
        (* Eq *)
        reflexivity.
        (* Lt *)
        destruct (N.comp_zero n Heqcmp).
        (* Gt *)
        reflexivity.
      (* a::l *)
      remember (N.comp n N.zero) as cmp.
      destruct cmp;
          symmetry in Heqcmp.
        (* Eq *)
        destruct (N.comp_eq n N.zero) as [ Hcmp _ ].
        rewrite (Hcmp Heqcmp).
        rewrite (N.comp_zero_succ _).
        reflexivity.
        (* Lt *)
        destruct (N.comp_zero n Heqcmp).
        (* Gt *)
        pose (IH := IHl r (N.pred n)).
        rewrite (N.sub_pred _ _) in IH.
        destruct (N.pos_succ n Heqcmp) as [ n' Hn' ].
        rewrite Hn'.
        rewrite Hn' in IH.
        rewrite (N.pred_succ _).
        rewrite (N.pred_succ _) in IH.
        rewrite N.comp_succ.
        exact IH.
  Defined.

  Lemma set_concat : forall A (l l':list A) (n:N.N) (x:A), set (concat l l') n x =
      match N.comp n (len l) with
      | Lt => concat (set l n x) l'
      | Eq
      | Gt => concat l (set l' (N.sub n (len l)) x)
      end.
    intros A l l'.
    induction l;
        intros n x; simpl.
      (* [] *)
      remember (N.comp n N.zero) as cmp.
      destruct cmp; 
          symmetry in Heqcmp.
        (* Eq *)
        rewrite N.sub_zero; reflexivity.
        (* Lt *)
        destruct (N.comp_zero n Heqcmp).
        (* Gt *)
        rewrite N.sub_zero; reflexivity.
      (* a::l *)
      remember (N.comp n N.zero) as cmp.
      destruct cmp;
          symmetry in Heqcmp.
        (* Eq *)
        destruct (N.comp_eq n N.zero) as [Hcmp _].
        rewrite (Hcmp Heqcmp).
        rewrite (N.comp_zero_succ).
        auto.
        (* Lt *)
        destruct (N.comp_zero n Heqcmp).
        (* Gt *)
        pose (IH := IHl (N.pred n) x).
        destruct (N.pos_succ n Heqcmp) as [n' Hn'].
        rewrite Hn' in IH.
        rewrite Hn'.
        rewrite N.pred_succ in IH.
        rewrite N.pred_succ.
        rewrite N.comp_succ.
        rewrite N.sub_succ.
        rewrite IH.
        simpl.
        destruct (N.comp n' (len l)); auto.
  Defined.
 
End CanonicalArrayImpl.


