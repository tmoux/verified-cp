Require Import Lia.
Require Import Bool.
Require Import List.
Import PeanoNat.Nat.
Import ListNotations.
Require Extraction.

(** ** Definitions *)
Inductive bit := B0 | B1.

Definition broken_list := list bool.
Definition message := list bit.
Definition packet : Set := bit * bit * bit.

Fixpoint encode_nat (n : nat) : message. Admitted.
Fixpoint decode_nat (x : message) : nat. Admitted.

Fixpoint count_broken (p : broken_list) := match p with
  | [] => 0
  | r :: rest => b2n r + count_broken rest
  end.


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

Definition encode_packet (a b c : bool) (b1 b2 : bit) : (packet * nat) := 
    let cnt := b2n a + b2n b + b2n c in
    match cnt with
    | 3 => let packet := (match b1, b2 with
        | B0, B0 => (B0, B1, B1)
        | B0, B1 => (B1, B1, B1)
        | B1, B0 => (B1, B0, B0)
        | B1, B1 => (B1, B0, B1)
        end) in (packet, 2)
    | 2 => if negb a then let packet := (match b1 with
        | B0 => (B0, B0, B1)
        | B1 => (B0, B1, B0)
        end) in (packet, 1)
        else if negb c then let packet := (match b1 with
        | B0 => (B1, B1, B0)
        | B1 => (B0, B1, B0)
        end) in (packet, 1) 
        else (match b1, b2 with
        | B0, _  => ((B0, B0, B1), 1)
        | B1, B0 => ((B1, B0, B0), 2)
        | B1, B1 => ((B1, B0, B1), 2)
        end)
    | _ => ((B0, B0, B0), 0)
    end.

Fixpoint drop {A} (n : nat) (l : list A) : list A := match n, l with
  | n  , []      => l
  | 0  , l       => l
  | S n, x :: ls => drop n ls
  end.

Fixpoint encode (x : message) (p : broken_list) : list packet := match p with
  | a :: b :: c :: rest => 
    let '(b1, b2, bs) := (match x with
      | []                => (B0 , B0 , [])
      | [b1']             => (b1', B0 , [])
      | b1' :: b2' :: bs' => (b1', b2', bs')
    end) in
    let '(packet, d) := encode_packet a b c b1 b2 in
      packet :: encode (drop d x) rest
  | _ => []
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

Fixpoint decode (x : list packet) : message := match x with
  | p :: rest => decode_packet p ++ decode rest
  | _ => []
  end.      

Definition anna (x : message) (p : broken_list) : message :=
  packets_to_message (encode x p).

Definition bruno (x : message) : message :=
  decode (message_to_packets x).

Module Examples.
Example ex1 : list packet := encode [B1; B0; B1] [true; true; true; true; true; true; true; true].
Compute ex1.
Compute anna [B1; B0; B1] [true; true; true; true; true; true; true; true].
Compute bruno (anna [B1; B0; B1] [true; true; true; true; true; true; true; true]).
End Examples.
  

(** ** Verification *)

(** Anna's encoding respects the list of broken bits. *)
Inductive matches_broken_list : message -> broken_list -> Prop :=
  | matches_nil  : 
      matches_broken_list [] []
  | matches_true : forall x p,
      matches_broken_list x p ->
      matches_broken_list (B0 :: x) (true :: p)
  | matches_false : forall x p b,
      matches_broken_list x p ->
      matches_broken_list (b :: x) (true :: p)
  | matches_extra : forall x p b,
      matches_broken_list x p ->
      matches_broken_list x (b :: p).

(** This isn't a correct definition, since the decoded message can have extras zeros. *)
Definition scheme_correct (N K L : nat) := forall (x : message) (p : broken_list), 
    length p = N ->
    count_broken p = K ->
    length x = L -> 
    decode (encode x p) = x.
