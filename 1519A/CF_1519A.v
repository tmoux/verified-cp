Require Import Lia.
Require Import Bool.
Require Import List.
Require Import Arith.Arith.
Import ListNotations.

Require Extraction.

(** Define extraction to Ocaml. *)
(** Quite unsafe! *)
Module ExtractionDefs.
Module ExtrNatToInt64.
Extract Inductive nat => "int64"
  [ "Int64.zero" "(fun x -> Int64.succ x)" ]
  "(fun zero succ n -> if Int64.compare n 0 = 0 then zero () else succ (Int64.pred n))".
Extract Constant plus => "Int64.add".
Extract Constant mult => "Int64.mul".
Extract Constant leb => "(fun x y -> Int64.compare x y <= 0)".
End ExtrNatToInt64.

Extract Inductive bool => "bool" [ "true" "false" ].

End ExtractionDefs.

(** https://codeforces.com/contest/1519/problem/A *)

Definition absLeq (x y d : nat) := x-y <= d /\ y-x <= d.

Definition can_distribute (r b d : nat) : bool :=
  (b <=? (r * (d + 1))) && (r <=? (b * (d + 1))).

(** Define problem specification *)
(** A few lemmas about arithmetic that will come in handy. 
    We make heavy use of the [lia] to avoid having to deal with most of these proofs by hand, but for some cases (multiplication by non-constants, we need to help guide the solver: *)

Lemma d_leq_mult_d : forall d r, r > 0 -> d <= r * d.
Proof.
  intros. 
  induction d; lia.
Qed.

Lemma d_bound : forall r b d x y,
  r > 0 ->
  b <= r + d ->
  y <= x * (d+1) -> 
  b + y <= (r + x) * (d + 1).
Proof.
  intros.
  assert ((r+x)*(d+1) = x*(d+1) + r*(d+1)). { lia. } rewrite H2.
  assert (r+d <= r*(d+1)); try lia. 
  pose proof (d_leq_mult_d d r). lia.
Qed.

Module InductiveSpec.
Inductive correct_distribution (d : nat) : nat -> nat -> Prop :=
  | no_packets : correct_distribution d 0 0
  | add_packet : forall r b r' b',
      correct_distribution d r b ->
      r' > 0 ->
      b' > 0 ->
      absLeq r' b' d ->
      correct_distribution d (r'+r) (b'+b).
Hint Constructors correct_distribution : core.

Lemma distribution_flip : forall r b d,
  correct_distribution d r b <-> correct_distribution d b r.
  assert (H:forall r b d, correct_distribution d r b -> correct_distribution d b r). { 
  intros r b d H.
  induction H.
  - auto.
  - constructor; auto. unfold absLeq in *. lia. }

  split; apply H.
Qed.

Lemma can_make_distr : forall r b d,
    r <= b -> 
    b <= r * (d+1) ->
    correct_distribution d r b.
Proof.
  intros r b d r_leq_b H.
  generalize dependent b.
  induction r; intros.
  - assert (b = 0). lia. subst. auto.
  - remember (min (b - r) (d + 1)) as t.
    specialize IHr with (b-t).
    assert (Hb: b = t+(b-t)). { lia. } rewrite Hb.
    assert (Hr: S r = 1 + r). { lia. } rewrite Hr.
    constructor; unfold absLeq; try apply IHr; try lia. 
Qed.

Definition algorithm_iff_correct_distribution := 
  forall r b d, 
    can_distribute r b d = true <-> correct_distribution d r b.
Theorem algorithm_correct : algorithm_iff_correct_distribution.
  unfold algorithm_iff_correct_distribution.
  split; intros.
  - unfold can_distribute in H.
    rewrite andb_true_iff in H. repeat rewrite Nat.leb_le in H. destruct H as [H1 H2].
    (*** Case on whether r <= b or b <= r. *)
    assert (r <= b \/ b <= r) as [Hrb | Hbr]. lia.
    + apply can_make_distr; auto. 
    + apply distribution_flip. apply can_make_distr; auto.
  - unfold can_distribute.
    rewrite andb_true_iff. repeat rewrite Nat.leb_le. 
    induction H.
    + lia.
    + split; apply d_bound; unfold absLeq in H2; try lia.
Qed.

End InductiveSpec.

Module ListSpec.
(** Prove that our program returns true if and only if there exists a correct distribution. *)
Definition packet : Set := nat * nat.

Fixpoint packet_sum (l : list packet) := match l with
  | [] => (0,0)
  | (r,b) :: rest => let (x,y) := packet_sum rest in (r+x,b+y)
  end.


(** There exists a *correct distribution* for (r,b,d) if and only if there exists a set of packets which sum to (r,d), where each packet has a nonzero number of red and blue elements. *)
Definition correct_distribution (r b d : nat) :=
  exists l, packet_sum l = (r,b) /\ Forall (fun '(x,y) => absLeq x y d /\ x > 0 /\ y > 0) l.

Example ex1 : correct_distribution 1 1 0.
Proof.
  exists [(1,1)].
  split; unfold absLeq; auto.
  repeat constructor; lia.
Qed.

Example ex2 : correct_distribution 2 7 3.
Proof.
  exists [(1,4);(1,3)].
  split; unfold absLeq; auto.
  repeat constructor; lia.
Qed.

(** We can exchange the uses of r and b: *)
Lemma distribution_flip : forall r b d,
  correct_distribution r b d <-> correct_distribution b r d.
Proof.
  assert (H:forall r b d, correct_distribution r b d -> correct_distribution b r d). {
  unfold correct_distribution.
  intros r b d [l [H2 H3]].
  generalize dependent r.
  generalize dependent b.
  induction l; intros.
  + simpl in H2. inversion H2; subst. exists []; auto.
  + destruct a as [r' b']. simpl in H2. 
    remember (packet_sum l) as X. destruct X as [x y]. 
    inversion H2; subst.
    specialize IHl with y x.
    destruct IHl; auto. inversion H3; auto.
    destruct H.
    exists ((b',r')::x0).
    split. simpl. rewrite H. auto.
    constructor; auto. inversion H3; subst. destruct H5 as [Ha [Hr Hb]]. split; auto; unfold absLeq in *; try lia.
  }
  split; apply H.
Qed.

(** The crucial lemma proving that our algorithm's conditions is sufficient: *)
Lemma can_make_distr : forall r b d,
    r <= b -> 
    b <= r * (d+1) ->
    correct_distribution r b d.
Proof.
  intros r b d r_leq_b H.
  generalize dependent b.
  induction r; intros.
  - assert (b = 0). lia. subst. exists []. auto.
  - remember (min (b - r) (d + 1)) as t.
    specialize IHr with (b-t).
    assert (Hr : r <= b - t). { lia. } apply IHr in Hr.
    destruct Hr as [l [Hl1 Hl2]].
    exists ((1,t) :: l); split. 
    + simpl. rewrite Hl1. 
      assert (Htb: t + (b - t) = b). { lia. } rewrite Htb. 
      reflexivity.
    + constructor; try auto; split; try lia. unfold absLeq; lia. 
    + simpl in H. 
      pose proof (Nat.min_spec (b-r) (d+1)) as [[Hmin1 minEq] | [Hmin2 minEq]]; rewrite minEq in Heqt. 
      subst. assert (b - (b - r) = r). lia. rewrite H0. 
      rewrite plus_comm. rewrite <- mult_n_Sm. lia.

      subst. lia.
Qed. 

Definition algorithm_iff_correct_distribution := 
  forall r b d, 
    can_distribute r b d = true <-> correct_distribution r b d.
Theorem algorithm_correct : algorithm_iff_correct_distribution.
  unfold algorithm_iff_correct_distribution.
  intros.
  split; intros.
  - unfold can_distribute in H.
    rewrite andb_true_iff in H. repeat rewrite Nat.leb_le in H. destruct H as [H1 H2].
    (** Case on whether r <= b or b <= r. *)
    assert (r <= b \/ b <= r) as [Hrb | Hbr]. lia.
    + apply can_make_distr; auto.
    + apply distribution_flip. apply can_make_distr; auto.

  - destruct H as [l [H1 H2]].
    unfold can_distribute.
    rewrite andb_true_iff. repeat rewrite Nat.leb_le. 
    generalize dependent b.
    generalize dependent r.
    induction l; intros.
    + simpl in H1. inversion H1; subst. lia.
    + destruct a as [r' b']. simpl in H1. remember (packet_sum l) as X. destruct X as [x y]. inversion H1; subst. clear H1. 
      inversion H2; subst. apply IHl with x y in H3; auto. 
      unfold absLeq in H1.
      split; apply d_bound; lia.
Qed.
End ListSpec.


(** Extract the program to Ocaml. 
   See sol.ml for the boilerplate input/output plumbing. *)
Extraction "1519A/imp.ml" can_distribute.

