Require Import Lia.
Require Import Bool.
Require Import List.
Import PeanoNat.Nat.
Import ListNotations.
Require Extraction.

(** ** Definitions *)
Module Definitions.
Inductive bit := B0 | B1.

Definition broken_list := list bool.
Definition message := list bit.
Definition packet : Set := bit * bit * bit.
Definition chunk : Set := bool * bool * bool.

Fixpoint encode_nat (n : nat) : message. Admitted.
Fixpoint decode_nat (x : message) : nat. Admitted.

Fixpoint bools_to_chunks (p : broken_list) : list chunk :=  match p with
  | a :: b :: c :: rest => (a,b,c) :: bools_to_chunks rest
  | _ => []
  end.

Definition sum_chunk '((a,b,c) : chunk) := b2n a + b2n b + b2n c.

Fixpoint packets_to_message (ps : list packet) := match ps with
  | [] => []
  | (a,b,c) :: rest => a :: b :: c :: packets_to_message rest
  end.

Fixpoint message_to_packets (x : message) := match x with
  | a :: b :: c :: rest => (a,b,c) :: message_to_packets rest
  | _ => []
  end.

(** Converting a list of packets to a message and back to packets is the identity. *)
Lemma packets_message_inverses : forall ps,
  message_to_packets (packets_to_message ps) = ps.
Proof.
  intros.
  induction ps as [| p ps IH].
  - reflexivity.
  - destruct p as [[a b] c]. simpl. rewrite IH. reflexivity.
Qed.

Definition encode_packet '((a,b,c) : chunk) (x : message) : packet := 
    let '(b1, b2) := (match x with
      | []                => (B0 , B0)
      | [b1']             => (b1', B0)
      | b1' :: b2' :: bs' => (b1', b2')
    end) in
    match sum_chunk (a,b,c) with
    | 0 => (match b1, b2 with
        | B0, B0 => (B0, B1, B1)
        | B0, B1 => (B1, B1, B1)
        | B1, B0 => (B1, B0, B0)
        | B1, B1 => (B1, B0, B1)
        end)
    | 1 => if a then (match b1 with
        | B0 => (B0, B0, B1)
        | B1 => (B0, B1, B0)
        end)
        else if c then (match b1 with
        | B0 => (B1, B1, B0)
        | B1 => (B0, B1, B0)
        end)
        else (match b1, b2 with
        | B0, _  => (B0, B0, B1)
        | B1, B0 => (B1, B0, B0)
        | B1, B1 => (B1, B0, B1)
        end)
    | _ => (B0, B0, B0)
    end.

Definition decode_packet (p : packet) : message := match p with
    | (B0, B0, B0) => []
    | (B0, B0, B1) => [B0]
    | (B0, B1, B0) => [B1]
    | (B0, B1, B1) => [B0; B0]
    | (B1, B0, B0) => [B1; B0]
    | (B1, B0, B1) => [B1; B1]
    | (B1, B1, B0) => [B0]
    | (B1, B1, B1) => [B0; B1]
    end.

Fixpoint drop {A} (n : nat) (l : list A) : list A := match n, l with
  | n  , []      => l
  | 0  , l       => l
  | S n, x :: ls => drop n ls
  end.

Fixpoint encode (x : message) (p : list chunk) : list packet := match p with
  | c :: rest => let pack := encode_packet c x in
    pack :: encode (drop (length (decode_packet pack)) x) rest
  | _ => []
  end.

Fixpoint decode (x : list packet) : message := match x with
  | p :: rest => decode_packet p ++ decode rest
  | _ => []
  end.      

Definition anna (x : message) (p : broken_list) : message :=
  packets_to_message (encode x (bools_to_chunks p)).

Definition bruno (x : message) : message :=
  decode (message_to_packets x).
End Definitions.

Module Examples.
Import Definitions.
Definition falses := [false; false; false; false; false; false; false; false; false].
Compute anna [B1; B0; B1] falses.
Compute bruno (anna [B1; B0; B1] falses).
End Examples.
  

(** ** Verification *)
Module Verification.
Import Definitions.
Inductive matches_broken_list : message -> broken_list -> Prop :=
  | matches_nil  : forall p,
      matches_broken_list [] p
  | matches_true : forall x p,
      matches_broken_list x p ->
      matches_broken_list (B0 :: x) (true :: p)
  | matches_false : forall x p b,
      matches_broken_list x p ->
      matches_broken_list (b :: x) (false :: p).
Hint Constructors matches_broken_list : core.

(** A modified induction principle for lists *)
Theorem list_two_induction {A} (P : list A -> Prop) :
  P [] -> 
  (forall a, P [a]) -> 
  (forall a b l, P l -> 
                   P (a :: l) -> 
                   P (a :: b :: l)) ->
  (forall l, P l).
Proof.
  intros H0 H1 IH l.
  enough (P l /\ (forall a, P (a :: l))) by easy.
  induction l; intuition. 
Qed.

Theorem list_three_induction {A} (P : list A -> Prop) :
  P [] -> 
  (forall a, P [a]) -> 
  (forall a b, P [a; b]) -> 
  (forall a b c l, P l -> 
                   P (a :: l) -> 
                   P (a :: b :: l) -> 
                   P (a :: b :: c :: l)) ->
  (forall l, P l).
Proof.
  intros H0 H1 H2 IH l.
  enough (P l /\ (forall a, P (a :: l)) /\ (forall a b, P (a :: b :: l))) by easy.
  induction l; intuition. 
Qed.

(** Anna's encoding respects the list of broken bits. This can basically be shown by the above induction principle (inducting on groups of threes) and casework. *)
Theorem anna_respects_broken : forall x p,
  matches_broken_list (anna x p) p.
Proof.
  intros x p.
  unfold anna.
  generalize dependent x.
  induction p as [| | | a b c p IH1 _ _] using list_three_induction; intros; auto.
  simpl.
  destruct x as [| x1 x]. 
    { unfold encode_packet. destruct a, b, c; simpl; auto. } 
  destruct x as [| x2 x].
    { destruct x1; unfold encode_packet; destruct a, b, c; simpl; auto. } 
    { destruct x1, x2, a, b, c; simpl; auto. }
Qed.


(** Two message are equal if they are the same elements, ignoring tailing zeros*)
(** This definition is still kind of stupid, may adjust it to make the proofs easier *)
Inductive equal_message : message -> message -> Prop :=
  | equal_nil : 
      equal_message [] []
  | equal_cons : forall xs ys x y,
      equal_message xs ys ->
      equal_message (x :: xs) (y :: ys)
  | equal_tail_0 : forall xs ys,
      equal_message xs ys ->
      equal_message xs (ys ++ [B0])
  | equal_symm : forall xs ys,
      equal_message xs ys ->
      equal_message ys xs.
Hint Constructors equal_message : core.

Example equal_ex : equal_message [B1; B0; B1] [B1; B0; B1; B0; B0; B0].
Proof.
  assert (H : [B1; B0; B1; B0; B0; B0] = (([B1; B0; B1] ++ [B0]) ++ [B0]) ++ [B0]).
  auto.
  rewrite H.
  repeat apply equal_tail_0.
  auto.
Qed.

Fixpoint count_broken (p : list chunk) := match p with
  | c :: rest => sum_chunk c + count_broken rest
  | _ => 0
  end.

(** Encoding a message [B0] is the same as encoding nothing. May adapt as needed. *)
Lemma encode_B0 : forall l, encode [B0] l = encode [] l.
Proof.
  intros.
  induction l.
  simpl. auto.
  destruct a as [[a b] c].
  destruct a, b, c; simpl; try rewrite IHl; auto.
Qed.

(** The number of bits transmitted in a packet depends on the number of true (broken) bits in the chunk. *)
Lemma number_of_bits_in_packet: forall c msg,
  length (decode_packet (encode_packet c msg)) >= 2 - (sum_chunk c).
Proof.
  intros [[a b] c] [| [|] [| [|] x]]; destruct a, b, c; simpl; auto.
Qed.
  
(** chunk_count records the number of chunks in a list with count 0, 1, 2/3*)
Inductive chunk_count : list chunk -> nat -> nat -> nat -> Prop :=
  | cc_nil : chunk_count [] 0 0 0
  | cc_0   : forall l x y z c,
      sum_chunk c = 0 ->
      chunk_count l x y z ->
      chunk_count (c::l) (S x) y z
  | cc_1   : forall l x y z c,
      sum_chunk c = 1 ->
      chunk_count l x y z ->
      chunk_count (c::l) x (S y) z
  | cc_2_or_3   : forall l x y z c,
      sum_chunk c = 2 \/ sum_chunk c = 3 ->
      chunk_count l x y z ->
      chunk_count (c::l) x y (S z).
Hint Constructors chunk_count : core.

Lemma list_to_chunk_count : forall (l : list chunk),
    exists x y z, chunk_count l x y z.
Proof.
  intros.
  induction l; eauto.
  remember (sum_chunk a) as sum.
  destruct IHl as [x [y [z IHl]]].
  destruct a as [[a b] c].
  destruct a, b, c; pose proof Heqsum as H; simpl in H;
  repeat eexists; match goal with 
    | [ _ : sum = 0 |- _] => apply cc_0
    | [ _ : sum = 1 |- _] => apply cc_1
    | [ _ : sum = 2 |- _] => apply cc_2_or_3
    | [ _ : sum = 3 |- _] => apply cc_2_or_3
  end; simpl; try lia; apply IHl.
Qed.

Lemma chunk_count_total : forall l x y z,
  chunk_count l x y z ->
  x + y + z = length l.
Proof.
  intros. induction H; simpl; lia.
Qed.

Lemma chunk_count_sumsto_count_broken : forall l x y z,
  chunk_count l x y z -> 
  y + 2*z <= count_broken l.
Proof.
  intros. induction H; simpl; try rewrite H; lia.
Qed.  

Lemma chunk_count_decoded_length : forall msg l x y z,
  chunk_count l x y z ->
  length (decode (encode msg l)) >= 2*x + y.
Proof.
  intros.
  generalize dependent msg.
  induction H; intros; try (simpl; lia); simpl;
    rewrite app_length;
    remember (encode_packet c msg) as ep;
    pose proof (number_of_bits_in_packet c msg); rewrite <- Heqep in H1;
    specialize IHchunk_count with (drop (length (decode_packet ep)) msg); lia.
Qed.

Definition message_preserved (N K L : nat) := forall x p, 
  length p = N ->
  count_broken (bools_to_chunks p) = K ->
  length x = L ->
  equal_message (bruno (anna x p)) x.

Lemma bools_to_chunks_length : forall p (m n : nat),
  length p = n ->
  3 * m = n ->
  length (bools_to_chunks p) = m.
Proof.
  intros.
  generalize dependent n.
  generalize dependent m.
  induction p using list_three_induction; intros; simpl in *; auto; try lia.
  clear IHp0. clear IHp1.
  rewrite (IHp (m-1) (n-3)); lia. 
Qed.

Theorem correct_message_for_given_constraints :
  message_preserved 150 40 60.
Proof.
  unfold message_preserved.
  intros msg p H1 H2 H3.
  unfold bruno, anna. rewrite packets_message_inverses.
  remember (bools_to_chunks p) as l.
  destruct (list_to_chunk_count l) as [x [y [z Hcnt]]].
  assert (xy_lb : 2*x + y >= 60). { 
    assert (Hp_length : length l = 50). { subst. apply bools_to_chunks_length with (n := 150); auto. }
    pose proof (chunk_count_total l x y z Hcnt).
    pose proof (chunk_count_sumsto_count_broken l x y z Hcnt).
    lia. }
  pose proof (chunk_count_decoded_length msg l x y z Hcnt) as H_decoded_length.
  (* Now we know that the length of the decoded message is at least 60 (the length of the original message). *)
  (* Next, we must show that any decoded message is either a prefix of the original message, or it is equal (possibly with tailing zeros). 
     Since we know that it cannot be a strict prefix since its length is >= 60, it must indeed be equal. *)
Admitted.  

End Verification.
