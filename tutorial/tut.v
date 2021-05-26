(** * Verifying Programming Contest Problems *)

(** ** Introduction *)

(** 
    In programming contests, one of the most frustrating (and common!) verdicts to receive is Wrong Answer (WA).
    One of the reasons behind this is that there are often many potential sources of WA that a programmer has to hunt down.
    A WA could come from a typo in the implementation, or it could come from the use of a greedy observation which does not always hold, or many other reasons.

    In this tutorial, I will try to give a brief overview of how you can _prove your programs correct_ by writing specifications and proofs in the Coq proof assistant.
    Coq is based on a dependent type theory that allows you to define your programs and write proofs about them. 
    Writing proofs by hand can be quite laborious, so Coq also has an interactive proving system using _tactics_ that allows you to automate away tedious parts of proofs and also prove things in a much more natural way.
    This very document is a (literate) Coq file, so you can download the source and follow along.
    By the end of this tutorial, you should be able to compile this Coq file, extract it to Ocaml, and submit your solution to an online judge!
*)

(** *** Some Disclaimers *)

(**    There are, of course, several caveats I should point out.
    The first of which is that writing out a specification and proving an algorithm correct takes a significant amount of time, even for experienced users. 
    It would be utterly impractical for a contest setting, where "proofs by AC" are quite common.
    My goal is to use contest problems as a vehicle to introduce formal verification in a small-scale, concrete way--although of course program verification is also used on much larger projects.

    Secondly, we may be limited in the kinds of problems we can (easily) verify and write efficient solutions for.
    For instance, many contest problems involve mutable arrays, while when using Coq, we tend to prefer lists and other functional data structures because they are easier to reason about.
*)


(** ** A Simple Example *)

(** 
    For our example, we'll solve the Codeforces problem Red and Blue Beans:
    #<a href="https://codeforces.com/contest/1519/problem/A">https://codeforces.com/contest/1519/problem/A</a># 
    %\url{https://codeforces.com/contest/1519/problem/A}%.

    This is a pretty basic problem involving only basic arithmetic.
    The answer is [YES] if and only if [b <= r * (d+1)] and [r <= b * (d+1)].

    How can we prove this is the right condition? 
    Without loss of generality, we can assume that [r <= b]. 
    If we wanted to maximize the number of blue beans for a given number of red beans, we would create [r] packets, each with [1] red bean and [d+1] blue beans.
    Therefore, if we have more than [r * (d+1)] blue beans, we cannot distribute all the beans; otherwise, we can.

    Now, let's get to programming our solution!
*)


Require Import Lia.
Require Import Bool.
Require Import List.
Require Import Arith.Arith.
Import ListNotations.
Require Extraction.

Definition can_distribute (r b d : nat) : bool :=
  (b <=? (r * (d + 1))) && (r <=? (b * (d + 1))).

(** 
    That wasn't too bad!
    If we were programming in another language like Java or C++, we would stop here and submit our solution.
    However, even after passing hundreds of tests, we still can't be sure that is correct for all inputs. 
    The only way to be certain of a program's correctness is to prove it, like we did above.
    But how do we know our _proof_ is correct? 
    People make mistakes in proofs all the time.
    Luckily, Coq's type system is expressive enough to allow you to write propositions about your programs as types. 
    If we can find a term [t] that has type [T], we say that [T] is _inhabited_. Interpreting [T] as a proposition, we say that [t] is _evidence_ for [T] being true.  
    This effectively means that we can use Coq's type-checker as a proof-checker!
    This is known as the 
    #<a href="https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence">Curry-Howard correspondence</a>#.
*)

(**
   Okay, here's a concrete example of writing a proposition and its proof in Coq.
   When writing a specification for our original problem, we'll need to define a function [abs] that takes two natural numbers [a] and [b] and returns the absolute value [|a-b|].
*)

Definition abs (a b : nat) := max (b-a) (a-b).

(** 
    Note that since we are working with natural numbers, subtraction is capped at zero--so [3 - 5 = 0], for instance.

    To show that [abs] is defined correctly, we can prove that it satisfies the properties want for all possible inputs.
    For instance, we would expect that [abs a b] is the same as [abs b a].
    We can write this proposition in Coq like so:
*)
Theorem abs_comm : forall (a b : nat), abs a b = abs b a.
(** 
    We can read this like a sentence in first-order logic:
    "For all [a b], [abs a b] and [abs b a] are equal."
    
    By writing Proof., we enter into the interactive proving mode, where we can prove our goal by entering a series of tactics.
*)
Proof.
  (* This will make the most sense if you are following along in your own IDE! *)
  (* First, we move [a] and [b] into our local context using the [intros] tactic. 
     This is like writing "Let a and b be arbitrary natural numbers." in a written proof. *)
  intros a b.
  (* Next, we unfold the definition of [abs] using the [unfold] tactic. 
     Since [abs] is defined in terms of the [max] function, we can use properties about [max] to prove our goal. *)
  unfold abs.
  (* The theorem [Nat.max_comm] should be useful. We can check its type using the [Check] directive: *)
  Check Nat.max_comm.
  (* We can introduce a new hypothesis using [assert], prove it, and then use it to help prove our original goal. 
   This is like introducing a lemma in a written proof. *) 
  assert (H : max (b-a) (a-b) = max (a-b) (b-a)). 
  (* Our lemma follows directly from the [Nat.max_comm] theorem, so we can use the [apply] tactic: *)
  { apply Nat.max_comm. }
  (* The most important thing about equalities is that if [x = y], 
     then [x] and [y] are interchangeable in every context.
     We can use the [rewrite] tactic to change [max (b-a) (a-b)] in our goal to [max (a-b) (b-a)].*)
  rewrite H.
  (* Now, both sides of the equality are exactly the same, so we can discharge the goal using [reflexivity].*)
  reflexivity.
Qed.

(** It's important to stress that tactics are only high-level directions that tell Coq how to create the proof. 
    The proof term itself is often much longer and harder to understand, and it is what is checked by the typechecker to verify that you have proven your theorem. You can view the proof [abs_comm] using the [Print] directive.
*)
Print abs_comm.
(* begin details : *)
(**
[[
abs_comm = 
fun a b : nat =>
let H :
  Init.Nat.max (b - a) (a - b) = Init.Nat.max (a - b) (b - a) :=
  Nat.max_comm (b - a) (a - b) in
eq_ind_r (fun n : nat => n = Init.Nat.max (a - b) (b - a))
  eq_refl H
     : forall a b : nat, abs a b = abs b a
]]
*)

(* end details *)


(** 
    Let's prove one more property about [abs].
    [abs a b] should be equal to the distance between [a] and [b], so if [a < b], then [a + abs a b = b], and if [b < a], then [b + abs a b = b].

    To prove this, we can use the [lia] tactic, which is a decision procedure for linear integer arithmetic.
    As our original problem involves a lot of arithmetic, [lia] will frequently come in handy.
*)

Theorem abs_correct : forall (a b : nat),
    (a < b -> a + abs a b = b) /\
    (b < a -> b + abs a b = a).
Proof.
  intros. 
  unfold abs.
  lia.
Qed.


(** ** Specification Using Lists 
*)

(** Now let's return to our original problem. 
    We can write a proposition that defines whether there is a valid distribution of beans.
    For any [r,b,d], there exists a _correct distribution_ of beans if and only if there exists a set of packets such that
    - the sum of all the red beans is [r],
    - the sum of all the blue beans is [b],
    - each packet contains a positive number of red and blue beans,
    - for each packet, the number of red and blue beans should not differ by more than [d].

    The simplest way to represent a set of packets is a list.
    We'll define a [packet] as a pair of natural numbers, and we'll define the function [packet_sum] which adds up the number of red and blue beans in a list of packets.
*)

Module ListSpec.

Definition packet : Set := nat * nat.

Fixpoint packet_sum (l : list packet) := match l with
  | [] => (0,0)
  | (r,b) :: rest => let (x,y) := packet_sum rest in (r+x,b+y)
  end.

(** Now we can define what a [correct_distribution] means as define above. Here, we use the existential quantifier [exists], meaning that to prove this proposition, we must supply a valid list that all the conditions. *)

Definition correct_distribution (r b d : nat) :=
  exists l, packet_sum l = (r,b) /\ Forall (fun '(x,y) => abs x y <= d /\ x > 0 /\ y > 0) l. 


Example ex1 : correct_distribution 1 1 0.
Proof.
  exists [(1,1)].
  split; unfold abs; auto.
  repeat constructor; lia.
Qed.

Example ex2 : correct_distribution 2 7 3.
Proof.
  exists [(1,4);(1,3)].
  split; unfold abs; auto.
  repeat constructor; lia.
Qed.

(** Finally, we can relate our algorithm [can_distribute] to our specification [correct_distribution]. 
    Our algorithm should return true if and only if [correct_distribution] is provable, meaning that there exists a list of packets that meets the conditions defined in [correct_distribution].
*)

Definition algorithm_iff_correct_distribution := 
  forall r b d, 
    can_distribute r b d = true <-> correct_distribution r b d.


(** If we can prove this theorem (meaning we can find a term which has this type), we know that our algorithm is correct.
    Moreover, other people do not even need to read our proof to trust that our algorithm is correct.
    They can simply read the specification and make sure the program typechecks.
*)

(** *** Some helpful lemmas
*)

(** A few lemmas about arithmetic that will come in handy. 
    We make heavy use of the [lia] to avoid having to deal with most of these proofs by hand, but for some cases (multiplication by non-constants), we need to help guide the solver: *)

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

(** This lemma says that we can exchange the uses of [r] and [b], meaning that if we can distribute [r] red beans and [b] blue beans, we must also be able to distribute [b] red beans and [r] blue beans, and vice versa.
    Although the proof is a bit complicated, the intuition is simple: we can flip the number of blue and red beans in each packet.
*)

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
    constructor; auto. inversion H3; subst. destruct H5 as [Ha [Hr Hb]]. split; auto; unfold abs in *; try lia.
  }
  split; apply H.
Qed.

(** Here is the crucial lemma proving that our algorithm's conditions is sufficient. Note that we assume that [r <= b], like we did in the informal proof. 
 *)
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
    + constructor; try auto; split; try lia. unfold abs; lia. 
    + simpl in H. 
      pose proof (Nat.min_spec (b-r) (d+1)) as [[Hmin1 minEq] | [Hmin2 minEq]]; rewrite minEq in Heqt. 
      subst. assert (b - (b - r) = r). lia. rewrite H0. 
      rewrite plus_comm. rewrite <- mult_n_Sm. lia.

      subst. lia.
Qed. 

(** Next, we'll prove that our algorithm's condition is necessary, meaning that if there is a list [l] that shows that [correct_distribution r b d] is true, then [b <= r * (d + 1)] and [r <= b * (d + 1)].

    The proof proceeds by induction on the list [l].
    
*)
Theorem algorithm_condition_necessary : forall r b d,
  correct_distribution r b d -> can_distribute r b d = true.
Proof.
  unfold correct_distribution, can_distribute.
  intros.
  destruct H as [l [H1 H2]].
  unfold can_distribute.
  rewrite andb_true_iff. repeat rewrite Nat.leb_le. 
  generalize dependent b.
  generalize dependent r.
  induction l; intros.
  + simpl in H1. inversion H1; subst. lia.
  + destruct a as [r' b']. simpl in H1. remember (packet_sum l) as X. destruct X as [x y]. inversion H1; subst; clear H1. 
    inversion H2; subst. apply IHl with x y in H3; auto. 
    unfold abs in H1.
    split; apply d_bound; lia.
Qed.

(** *** The proof of correctness!
*)
Theorem algorithm_correct : algorithm_iff_correct_distribution.
Proof.
  unfold algorithm_iff_correct_distribution.
  intros.
  split; intros.
  - unfold can_distribute in H.
    rewrite andb_true_iff in H. repeat rewrite Nat.leb_le in H. destruct H as [H1 H2].
    (* Case on whether r <= b or b <= r. *)
    assert (r <= b \/ b <= r) as [Hrb | Hbr]. lia.
    + apply can_make_distr; auto.
    + apply distribution_flip. apply can_make_distr; auto.

  - apply algorithm_condition_necessary; auto. 
Qed.
End ListSpec.


(** ** Specification Using Inductive Relations *)

(** 
    We've done it! We have defined our specification using lists and proven that our algorithm always computes the correct answer according to our specification.
    
    Now that we know for certain that our program is correct, we can proceed to extracting the program into Ocaml.
    Before we move on, however, I want to present another specification for this problem, this time defining [correct_distribution] as an inductive proposition.
    
    While it may be natural to interpret the specification using lists, it does make the definitions more complicated, which affects the length and readability of the proofs.
    This alternate specification is equivalent (in fact, proving that these two specifications are equivalent is a good exercise), but it requires a lot less unfolding and destructing, which simplifies the proofs.

*)

Module InductiveSpec.
Inductive correct_distribution : nat -> nat -> nat -> Prop :=
  | no_packets : forall d, 
      correct_distribution 0 0 d
  | add_packet : forall r b r' b' d,
      correct_distribution r b d ->
      r' > 0 ->
      b' > 0 ->
      abs r' b' <= d ->
      correct_distribution (r'+r) (b'+b) d.
Hint Constructors correct_distribution : core.

Definition algorithm_iff_correct_distribution := 
  forall r b d, 
    can_distribute r b d = true <-> correct_distribution r b d.

Lemma distribution_flip : forall r b d,
  correct_distribution r b d <-> correct_distribution b r d.
Proof.
  assert (H:forall r b d, correct_distribution r b d -> correct_distribution b r d). { 
  intros r b d H.
  induction H.
  - auto.
  - constructor; auto. unfold abs in *. lia. }

  split; apply H.
Qed.

Lemma can_make_distr : forall r b d,
    r <= b -> 
    b <= r * (d+1) ->
    correct_distribution r b d.
Proof.
  intros r b d r_leq_b H.
  generalize dependent b.
  induction r; intros.
  - assert (b = 0). lia. subst. auto.
  - remember (min (b - r) (d + 1)) as t.
    specialize IHr with (b-t).
    assert (Hb: b = t+(b-t)). { lia. } rewrite Hb.
    assert (Hr: S r = 1 + r). { lia. } rewrite Hr.
    constructor; unfold abs; try apply IHr; try lia. 
Qed.

Theorem algorithm_correct : algorithm_iff_correct_distribution.
Proof.
  unfold algorithm_iff_correct_distribution.
  split; intros.
  - unfold can_distribute in H.
    rewrite andb_true_iff in H. repeat rewrite Nat.leb_le in H. destruct H as [H1 H2].
    (* Case on whether r <= b or b <= r. *)
    assert (r <= b \/ b <= r) as [Hrb | Hbr]. lia.
    + apply can_make_distr; auto. 
    + apply distribution_flip. apply can_make_distr; auto.
  - unfold can_distribute.
    rewrite andb_true_iff. repeat rewrite Nat.leb_le. 
    induction H.
    + lia.
    + split; apply ListSpec.d_bound; unfold abs in H2; try lia.
Qed.

End InductiveSpec.



(** ** Extraction *)
(** 
    Now we can extract our verified algorithm to Ocaml.
    We don't extract our proofs, since they not actually meant to be run.
    So in this case, we only need to extract our function [can_distribute], which is quite simple.
    We can try running the extraction command now:
*)
Extraction "imp.ml" can_distribute.
(** 
    If you look in the file [imp.ml], you will see the following datatype definitions at the top:

[[
type bool =
  | True
  | False
]]

[[
type nat =
  | O
  | S of nat
]]

Without any directions on how to perform the extraction, Coq will redefine all the datatypes that are used, including booleans and nat.
This is a big problem for nat, since defining numbers Peano-style is quite inefficient--if you look how addition is defined, adding two numbers is actually linear in the size of the first number.
We can tell Coq to extract nat to [int] or [int64], but this can be quite dangerous. This is because theorems about nat may no longer hold. For instance, it is a theorem for nat that [x + y >= x], but this is not true for [int] or [int64], since there may be overflow cases.

In this case, since we know that the inputs are less than [10^9], we can determine that we will not run into overflow issues.
So, we can safely extract nat to [int64].
So, I chose
If you would like, you can also extract to an arbitrary precision integer type like [big_int].
*)

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

Extraction "imp.ml" can_distribute.
(** 
    And there we have it--a fully verified program that you can submit to Codeforces!
    You can see #<a href="https://github.com/tmoux/verified-cp/blob/master/1519A/sol.ml">here</a># for a version that includes the input/output plumbing.

*)



