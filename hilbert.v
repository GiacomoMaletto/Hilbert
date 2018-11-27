Require Import Classical.

Class Hilbert := {
  Line : Type;
  Point : Type;
  Inc : Point -> Line -> Prop;
  Par l m := forall P:Point, ~(Inc P l /\ Inc P m);
  Algn A B C := exists l:Line, Inc A l /\ Inc B l /\ Inc C l;
  nAlgn A B C := forall l:Line, ~(Inc A l /\ Inc B l /\ Inc C l);

  I1: forall P Q:Point, P<>Q -> (exists ! l:Line, Inc P l /\ Inc Q l);
  I2: forall l:Line, (exists P Q:Point, Inc P l /\ Inc Q l /\ P<>Q);
  I3: exists A B C:Point, (A<>B/\B<>C/\C<>A) /\ nAlgn A B C;
}.

Context `{Hilbert}.

Proposition prop3_1: (forall l m:Line, 
  l<>m -> ~(Par l m) -> exists ! P:Point, Inc P l /\ Inc P m).
Proof.
  intros l m l_ne_m nPar.
  apply not_all_ex_not in nPar.
  destruct nPar as [P].
  apply NNPP in H0.
  refine (ex_intro _ P _).
  split.
    assumption.

    intros Q H1.
    case (classic (P = Q)).
      trivial.

      intros P_ne_Q.
      pose (I1 P Q) as only.
      apply only in P_ne_Q.
      unfold unique in P_ne_Q.
      destruct P_ne_Q as [s].
      destruct H2 as [H2 only_s].

      specialize (only_s l) as only_sl.
      pose (conj (proj1 H0) (proj1 H1)) as bothl.
      apply only_sl in bothl.

      specialize (only_s m) as only_sm.
      pose (conj (proj2 H0) (proj2 H1)) as bothm.
      apply only_sm in bothm.
      rewrite bothl in bothm.
      apply l_ne_m in bothm.
      case bothm.
Qed.

Proposition prop3_2 : (exists l m n: Line, (l<>m/\m<>n/\n<>l) /\
  forall P:Point, ~(Inc P l /\ Inc P m /\ Inc P n)).
Proof.
  destruct I3 as [A [B [C [[AneB [BneC CneA]] nAlgnABC]]]].

  destruct ((I1 A B) AneB) as [AB [incAB unAB]].
  destruct ((I1 B C) BneC) as [BC [incBC unBC]].
  destruct ((I1 C A) CneA) as [CA [incCA unCA]].

  exists AB, BC, CA.
  assert(AB <> BC) as AB_neq_BC.
    case (classic (AB = BC)).
    intros AB_e_BC.
    rewrite AB_e_BC in incAB.
    pose (conj incBC (proj2 incAB)) as incABC.
    specialize (nAlgnABC BC).
    tauto.
    trivial.

  assert(BC <> CA) as BC_neq_CA.
    case (classic (BC = CA)).
    intros BC_e_CA.
    rewrite BC_e_CA in incBC.
    pose (conj incCA (proj2 incBC)) as incABC.
    specialize (nAlgnABC CA).
    tauto.
    trivial.

  assert(CA <> AB) as CA_neq_AB.
    case (classic (CA = AB)).
    intros CA_e_AB.
    rewrite CA_e_AB in incCA.
    pose (conj incAB (proj2 incCA)) as incABC.
    specialize (nAlgnABC AB).
    tauto.
    trivial.

  split.
  tauto.

  intros P.
  case (classic (Inc P AB /\ Inc P BC /\ Inc P CA)).
  intros absurd.
  case (classic (P = A)).
    intros P_eq_A.
    case (classic (P = B)).
      intros P_eq_B.
      rewrite P_eq_A in P_eq_B.
      tauto.

      intros P_neq_B.
      destruct ((I1 P B) P_neq_B) as [PB [ incPB unPB]].

      pose (conj (proj1 absurd) (proj2 incAB)) as BnP_inc_AB.
      pose ((unPB AB) BnP_inc_AB) as PB_eq_AB.

      pose (conj (proj1 (proj2 absurd)) (proj1 incBC)) as BnP_inc_BC.
      pose ((unPB BC) BnP_inc_BC) as PB_eq_BC.

      rewrite PB_eq_AB in PB_eq_BC.
      tauto.

    intros P_neq_A.
    destruct ((I1 P A) P_neq_A) as [PA [ incPA unPA]].

    pose (conj (proj1 absurd) (proj1 incAB)) as AnP_inc_AB.
    pose ((unPA AB) AnP_inc_AB) as PA_eq_AB.

    pose (conj (proj2 (proj2 absurd)) (proj2 incCA)) as AnP_inc_CA.
    pose ((unPA CA) AnP_inc_CA) as PA_eq_CA.

    rewrite PA_eq_CA in PA_eq_AB.
    tauto.

  trivial.
Qed.

Proposition prop3_3 : (forall r:Line, exists P:Point, ~(Inc P r)).
Proof.
  intros r.
  destruct I3.
  destruct H0.
  destruct H0.
  apply proj2 in H0.
  specialize (H0 r).
  apply not_and_or in H0.
  case H0.
    intros nInc_x_r.
    refine (ex_intro _ x _).
    assumption.

    intros H1.
    apply not_and_or in H1.
    case H1.
      intros nInc_x0_r.
      exists x0.
      assumption.

      intros nInc_x1_r.
      exists x1.
      assumption.
Qed.

Proposition prop3_4: (forall P:Point, exists r:Line, ~(Inc P r)).
Proof.
  intros P.
  destruct prop3_2 as [l [m [n [[l_ne_m [m_ne_n n_ne_l]] nAlgn_lmn]]]].
  case (classic(forall r : Line, Inc P r)).

  intros all_inc.
  specialize (nAlgn_lmn P).
  pose (all_inc l) as l_inc.
  pose (all_inc m) as m_inc.
  pose (all_inc n) as n_inc.
  tauto.

  intros not_all_inc.
  apply not_all_ex_not in not_all_inc.
  trivial.
Qed.