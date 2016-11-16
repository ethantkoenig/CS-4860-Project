Require Import Arith Bool List BinNums BinNatDef.
Require Import Cpdt.CpdtTactics.
Require Import BinNatLemmas NatIntf CanonicalNatImpl VerifiedNatIntf.

Import ListNotations.

Module BinaryNaturalImpl <: VerifiedNaturalInterface.
  Definition N := BinNums.N.

  Definition zero : N := N0.
  Definition succ : N -> N := N.succ.
  Definition pred : N -> N := N.pred.
  Definition add : N -> N -> N := N.add.
  Definition sub : N -> N -> N := N.sub.
  Definition comp : N -> N -> comparison := N.compare.

  Definition inject : N -> nat := N.to_nat.

  Lemma zero_commutes : inject zero = 0.
    auto.
  Defined.

  Definition succ_commutes := BinNatLemmas.succ_commutes.
  Definition pred_commutes := BinNatLemmas.pred_commutes.
  Definition add_commutes := BinNatLemmas.add_commutes.
  Definition sub_commutes := BinNatLemmas.sub_commutes.
  Definition comp_commutes := BinNatLemmas.comp_commutes.
End BinaryNaturalImpl.


  

