(** * Intrinsically verified Levenshtein distance

    This file defines edit scripts as an indexed type and computes the
    Levenshtein distance together with a witness script.  The main result,
    [levenshtein_recursive_is_minimal], proves that the computed script length is no
    larger than the length of any other script between the same strings. *)
From Stdlib Require Import String Ascii Nat Lia.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Arith.Wf_nat.

Local Open Scope string_scope.
Local Infix "::" := String (at level 60, right associativity) : string_scope.
Local Notation "[ x ]" := (String x EmptyString) : string_scope.
Local Notation "[ x ; y ; .. ; z ]" := (String x (String y .. (String z EmptyString) ..)) : string_scope.

Module Levenshtein.

(** A single edit operation.  Insertions and deletions change the head of a
    string; [update] replaces a non-equal character at the head. *)
Inductive edit : string -> string -> Type :=
| insertion (a : ascii) {s : string} : edit s (a :: s)
| deletion (a : ascii) {s : string} : edit (a :: s) s
| update (a' : ascii) (a : ascii)
         {neq : a' <> a} {s : string} : edit (a' :: s) (a :: s).

(** A [chain s t n] is an edit script from [s] to [t] with exactly [n]
    charged edits.  Equal leading characters are skipped for free. *)
Inductive chain : string -> string -> nat -> Type :=
| empty : chain "" "" 0
| skip {a : ascii} {s t : string} {n : nat} :
    chain s t n -> chain (a :: s) (a :: t) n
| change {s t u : string} {n : nat} :
    edit s t -> chain t u n -> chain s u (S n).

(** Any edit script bounds the difference between source and target lengths. *)
Lemma chain_length_bounds :
  forall s t n (c : chain s t n),
    length t <= length s + n /\ length s <= length t + n.
Proof.
  intros s t n c.
  induction c as [|a s t n c IH|s t u n e c IH].
  - simpl. split; lia.
  - destruct IH as [IH1 IH2].
    simpl in *.
    split; lia.
  - destruct IH as [IH1 IH2].
    destruct e.
    + simpl in *.
      split; lia.
    + simpl in *.
      split; lia.
    + simpl in *.
      split; lia.
Qed.

(** Identity edit chain: every string edits to itself at cost zero. *)
Lemma same_chain : forall s, chain s s 0.
Proof.
  intros s. induction s; constructor; auto.
Defined.

(** A zero-cost edit chain can only relate equal strings. *)
Lemma chain_is_same : forall s t, chain s t 0 -> s = t.
Proof.
  intros s t c. dependent induction c.
  auto. f_equal. auto.
Qed.

(** Smart constructors for extending a script with the three charged edit
    operations. *)
Lemma insert_chain : forall c s1 s2 n, chain s1 s2 n -> chain s1 (c :: s2) (S n).
Proof.
  intros c s1 s2 n C.
  apply (@change _ (c :: s1)); constructor. auto.
Defined.

(** Inserts a whole prefix in front of the target endpoint. *)
Lemma inserts_chain : forall s1 s2, chain s2 (s1 ++ s2) (length s1).
Proof.
  intros.
  induction s1; simpl.
  induction s2; constructor; auto.
  apply insert_chain; auto.
Defined.

(** Transparent string version of [app_nil_r], kept transparent so later
    dependent terms can compute through it. *)
Lemma tr_app_empty_r : forall {A : Type} (l : string), l ++ "" = l.
Proof.
  intros A l; induction l. auto. simpl; rewrite IHl; auto.
Defined.

(** Builds a string from empty by inserting all of its characters. *)
Lemma inserts_chain_empty : forall s, chain "" s (length s).
Proof.
  intros s.
  induction s; simpl.
  constructor.
  apply insert_chain. auto.
Defined.

(** Deletes one source character before following an existing edit chain. *)
Lemma delete_chain : forall c s1 s2 n, chain s1 s2 n -> chain (c :: s1) s2 (S n).
Proof.
  intros c s1 s2 n C.
  apply (@change _ s1). constructor. auto.
Defined.

(** Deletes a whole source prefix before the shared suffix. *)
Lemma deletes_chain : forall s1 s2, chain (s1 ++ s2) s2 (length s1).
Proof.
  intros.
  induction s1; simpl.
  apply same_chain.
  apply delete_chain.
  auto.
Defined.

(** Reduces a string to empty by deleting all of its characters. *)
Lemma deletes_chain_empty : forall s, chain s "" (length s).
Proof.
  intros s.
  induction s; simpl.
  constructor. apply delete_chain. auto.
Defined.

(** Updates a non-equal source head before following an existing edit chain. *)
Lemma update_chain : forall c c' s1 s2 n,
    c <> c' -> chain s1 s2 n -> chain (c :: s1) (c' :: s2) (S n).
Proof.
  intros c c' s1 s2 n neq C.
  apply (@change _ (c' :: s1)). constructor. auto. apply skip. auto.
Defined.

(** Auxiliary casts used by [levenshtein_chain].  They keep the dependent
    result type aligned with the equations produced by pattern matching. *)
Lemma aux_insert : forall s t x xs y ys n,
    s = x :: xs -> t = y :: ys -> chain s ys n -> chain s t (S n).
Proof.
  intros s t x xs y ys n eq1 eq2 r1.
  subst.
  apply (insert_chain y (x :: xs) ys n r1).
Defined.

(** Dependent helper for the deletion branch of [levenshtein_chain]. *)
Lemma aux_delete : forall s t x xs y ys n,
    s = x :: xs -> t = y :: ys -> chain xs (y :: ys) n -> chain s t (S n).
Proof.
  intros s t x xs y ys n eq1 eq2 r2.
  subst.
  apply (delete_chain x xs (y :: ys) n r2).
Defined.

(** Dependent helper for the update branch of [levenshtein_chain]. *)
Lemma aux_update : forall s t x xs y ys n,
    x <> y -> s = x :: xs -> t = y :: ys -> chain xs ys n -> chain s t (S n).
Proof.
  intros s t x xs y ys n neq eq1 eq2 r3.
  subst.
  apply (update_chain x y xs ys n neq r3).
Defined.

(** Dependent helper for the equal-head branch of [levenshtein_chain]. *)
Lemma aux_eq_char : forall s t x xs y ys n,
    s = x :: xs -> t = y :: ys -> x = y -> chain xs ys n -> chain s t n.
Proof.
  intros s t x xs y ys n eq1 eq2 ceq C.
  subst. apply skip. auto.
Defined.

(** Dependent helper for the branch where both inputs are empty. *)
Lemma aux_both_empty : forall s t, s = "" -> t = "" -> chain s t 0.
Proof.
  intros s t eq1 eq2. subst. constructor.
Defined.

(** Boolean order conversion used by the three-way minimum proof. *)
Lemma leb_false : forall (n m : nat), (n <=? m)%nat = false -> (m <? n)%nat = true.
Proof.
  intros n m H.
  rewrite PeanoNat.Nat.leb_antisym in *.
  assert (eq : forall b, negb b = false -> b = true).
    intros; destruct b; auto.
  exact (eq _ H).
Qed.

(** Chooses one of three candidates whose score under [f] is minimal. *)
Definition min3_app {t : Type} (x y z : t) (f : t -> nat) : t :=
  let n1 := f x in let n2 := f y in let n3 := f z in
  match (Nat.leb n1 n2) with
  | true => match (Nat.leb n1 n3) with | true => x | false => z end
  | false => match (Nat.leb n2 n3) with | true => y | false => z end
  end.

(** The candidate selected by [min3_app] is no larger than any input candidate. *)
Lemma min3_app_pf {t : Type} (x y z : t) (f : t -> nat) :
    (f (min3_app x y z f) <= f x
  /\ f (min3_app x y z f) <= f y
  /\ f (min3_app x y z f) <= f z)%nat.
Proof.
  unfold min3_app.
  destruct (Nat.leb (f x) (f y)) eqn:leb1.
  * destruct (Nat.leb (f x) (f z)) eqn:leb2.
    - rewrite (PeanoNat.Nat.leb_le (f x) (f y)) in *.
      rewrite (PeanoNat.Nat.leb_le (f x) (f z)) in *.
      auto.
    - rewrite (PeanoNat.Nat.leb_le (f x) (f y)) in *.
      pose ((proj1 (PeanoNat.Nat.ltb_lt (f z) (f x))) (leb_false _ _ leb2)).
      lia.
  * destruct (Nat.leb (f y) (f z)) eqn:leb3.
    - rewrite (PeanoNat.Nat.leb_le (f y) (f z)) in *.
      pose ((proj1 (PeanoNat.Nat.ltb_lt (f y) (f x))) (leb_false _ _ leb1)).
      lia.
    - pose ((proj1 (PeanoNat.Nat.ltb_lt (f z) (f y))) (leb_false _ _ leb3)).
      pose ((proj1 (PeanoNat.Nat.ltb_lt (f y) (f x))) (leb_false _ _ leb1)).
      lia.
Qed.

(** To prove a property of [min3_app], it is enough to prove it for all three
    candidate inputs. *)
Lemma min3_app_cases {t : Type} (x y z : t) (f : t -> nat) (P : t -> Prop) :
  P x -> P y -> P z -> P (min3_app x y z f).
Proof.
  intros Hx Hy Hz.
  unfold min3_app.
  destruct (Nat.leb (f x) (f y)); destruct (Nat.leb _ _); auto.
Qed.

(** The score selected by [min3_app] is the numeric minimum of the three scores. *)
Lemma min3_app_value {t : Type} (x y z : t) (f : t -> nat) :
  f (min3_app x y z f) = Nat.min (f x) (Nat.min (f y) (f z)).
Proof.
  unfold min3_app.
  destruct (Nat.leb (f x) (f y)) eqn:Hxy.
  - destruct (Nat.leb (f x) (f z)) eqn:Hxz.
    + apply PeanoNat.Nat.leb_le in Hxy.
      apply PeanoNat.Nat.leb_le in Hxz.
      rewrite (PeanoNat.Nat.min_l (f x) (Nat.min (f y) (f z))).
      2:{ apply PeanoNat.Nat.min_glb; lia. }
      reflexivity.
    + apply PeanoNat.Nat.leb_le in Hxy.
      apply PeanoNat.Nat.leb_gt in Hxz.
      rewrite (PeanoNat.Nat.min_r (f y) (f z)) by lia.
      rewrite (PeanoNat.Nat.min_r (f x) (f z)) by lia.
      reflexivity.
  - destruct (Nat.leb (f y) (f z)) eqn:Hyz.
    + apply PeanoNat.Nat.leb_gt in Hxy.
      apply PeanoNat.Nat.leb_le in Hyz.
      rewrite (PeanoNat.Nat.min_l (f y) (f z)) by lia.
      rewrite (PeanoNat.Nat.min_r (f x) (f y)) by lia.
      reflexivity.
    + apply PeanoNat.Nat.leb_gt in Hxy.
      apply PeanoNat.Nat.leb_gt in Hyz.
      rewrite (PeanoNat.Nat.min_r (f y) (f z)) by lia.
      rewrite (PeanoNat.Nat.min_r (f x) (f z)) by lia.
      reflexivity.
Qed.

(** Swapping the first two candidates does not change a nested [Nat.min]. *)
Lemma min3_comm12 : forall a b c : nat,
  Nat.min a (Nat.min b c) = Nat.min b (Nat.min a c).
Proof.
  intros a b c.
  lia.
Qed.

(** Compute an edit script by structural recursion on the source string and
    nested recursion on the target string.  The dependent pair contains both
    the distance and a concrete [chain] witnessing that distance. *)
Fixpoint levenshtein_chain (s : string)  :=
  fix levenshtein_chain1 (t : string) : {n : nat & chain s t n} :=
    (match s as s', t as t' return s = s' -> t = t' -> {n : nat & chain s t n} with
    | "" , "" =>
        fun eq1 eq2 => existT _ 0 (aux_both_empty s t eq1 eq2)
    | "" , _ =>
        fun eq1 eq2 =>
          existT _ (length t)
            ltac:(rewrite eq1; apply (inserts_chain_empty t))
    | y :: ys , "" =>
        fun eq1 eq2 =>
          existT _ (length s)
            ltac:(rewrite eq1, eq2; apply (deletes_chain_empty (y :: ys)))
    | x :: xs, y :: ys =>
      fun eq1 eq2 =>
        match ascii_dec x y with
        | left ceq =>
          let (n, c) := levenshtein_chain xs ys in
          existT _ n (aux_eq_char s t x xs y ys n eq1 eq2 ceq c)
        | right neq =>
          let (n1, r1) := levenshtein_chain1 ys in
          let (n2, r2) := levenshtein_chain xs (y :: ys) in
          let (n3, r3) := levenshtein_chain xs ys in
          let r1' : chain s t (S n1) :=
              aux_insert s t x xs y ys n1 eq1 eq2 r1 in
          let r2' : chain s t (S n2) :=
              aux_delete s t x xs y ys n2 eq1 eq2 r2 in
          let r3' : chain s t (S n3) :=
              aux_update s t x xs y ys n3 neq eq1 eq2 r3 in
          min3_app (existT (fun (n : nat) => chain s t n) (S n1) r1')
                   (existT _ (S n2) r2')
                   (existT _ (S n3) r3')
                   (fun p => projT1 p)
        end
    end) (eq_refl s) (eq_refl t).

(** Numeric recursive model on strings.  This is the recursive counterpart of
    [levenshtein_dp] in [Levenshtein_dp.v]. *)
Definition levenshtein_recursive (s t : string) : nat :=
  projT1 (levenshtein_chain s t).

(** Extracting the numeric component from a previously remembered
    [levenshtein_chain] equation. *)
Lemma levenshtein_recursive_of_chain :
  forall s t n (c : chain s t n),
    levenshtein_chain s t = existT (fun k : nat => chain s t k) n c ->
    levenshtein_recursive s t = n.
Proof.
  intros s t n c Hc.
  unfold levenshtein_recursive.
  rewrite Hc.
  reflexivity.
Qed.

(** Public recurrence equations for the recursive distance. *)
Lemma levenshtein_recursive_nil_l :
  forall t, levenshtein_recursive EmptyString t = length t.
Proof.
  intros t.
  unfold levenshtein_recursive.
  destruct t as [|a t']; cbn; reflexivity.
Qed.

(** The distance from a string to empty is its length. *)
Lemma levenshtein_recursive_nil_r :
  forall s, levenshtein_recursive s EmptyString = length s.
Proof.
  intros s.
  unfold levenshtein_recursive.
  destruct s as [|a s']; cbn; reflexivity.
Qed.

(** Any edit distance is large enough to account for the input length gap. *)
Lemma levenshtein_recursive_length_bounds :
  forall s t,
    length t <= length s + levenshtein_recursive s t
    /\ length s <= length t + levenshtein_recursive s t.
Proof.
  intros s t.
  unfold levenshtein_recursive.
  destruct (levenshtein_chain s t) as [n c].
  simpl.
  exact (chain_length_bounds s t n c).
Qed.

(** Equal heads are skipped without increasing the recursive distance. *)
Lemma levenshtein_recursive_skip_eq : forall a s t,
    levenshtein_recursive (a :: s) (a :: t) = levenshtein_recursive s t.
Proof.
  intros a s t.
  unfold levenshtein_recursive.
  cbn.
  destruct (ascii_dec a a) as [Haa|Haa].
  - dependent destruction Haa.
    destruct (levenshtein_chain s t) as [n c].
    cbn.
    reflexivity.
  - exfalso.
    apply Haa.
    reflexivity.
Qed.

(** Non-equal heads satisfy the insert/delete/update recurrence. *)
Lemma levenshtein_recursive_cons_neq :
  forall a b s t,
    a <> b ->
    levenshtein_recursive (a :: s) (b :: t) =
      Nat.min (S (levenshtein_recursive (a :: s) t))
              (Nat.min (S (levenshtein_recursive s (b :: t)))
                       (S (levenshtein_recursive s t))).
Proof.
  intros a b s t Hneq.
  unfold levenshtein_recursive.
  cbn.
  destruct (ascii_dec a b) as [Heq|Hneqab].
  - exfalso.
    apply Hneq.
    exact Heq.
  - remember (levenshtein_chain (a :: s) t) as p1.
    remember (levenshtein_chain s (b :: t)) as p2.
    remember (levenshtein_chain s t) as p3.
    destruct p1 as [n1 c1], p2 as [n2 c2], p3 as [n3 c3].
    cbn.
    try match goal with
    | |- context [let (_, _) := ?p in _] =>
        change p with (levenshtein_chain (a :: s) t)
    end.
    try rewrite <- Heqp1.
    cbn.
    try match goal with
    | |- context [let (_, _) := ?p in _] =>
        change p with (levenshtein_chain s (b :: t))
    end.
    try rewrite <- Heqp2.
    cbn.
    try match goal with
    | |- context [let (_, _) := ?p in _] =>
        change p with (levenshtein_chain s t)
    end.
    try rewrite <- Heqp3.
    cbn.
    rewrite (min3_app_value
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n1)
              (insert_chain b (a :: s) t n1 c1))
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n2)
              (delete_chain a s (b :: t) n2 c2))
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n3)
              (update_chain a b s t n3 Hneqab c3))
      (fun p => projT1 p)).
    pose proof
      (levenshtein_recursive_of_chain (a :: s) t n1 c1 (eq_sym Heqp1))
      as Hp1.
    pose proof
      (levenshtein_recursive_of_chain s (b :: t) n2 c2 (eq_sym Heqp2))
      as Hp2.
    pose proof
      (levenshtein_recursive_of_chain s t n3 c3 (eq_sym Heqp3))
      as Hp3.
    cbn.
    reflexivity.
Qed.

(** In a mismatch, the insertion branch is an upper bound for the recurrence. *)
Lemma levenshtein_recursive_mismatch_upper_insert : forall a b s t,
    a <> b ->
    levenshtein_recursive (a :: s) (b :: t) <= S (levenshtein_recursive (a :: s) t).
Proof.
  intros a b s t Hneq.
  rewrite levenshtein_recursive_cons_neq by exact Hneq.
  lia.
Qed.

(** In a mismatch, the deletion branch is an upper bound for the recurrence. *)
Lemma levenshtein_recursive_mismatch_upper_delete : forall a b s t,
    a <> b ->
    levenshtein_recursive (a :: s) (b :: t) <= S (levenshtein_recursive s (b :: t)).
Proof.
  intros a b s t Hneq.
  rewrite levenshtein_recursive_cons_neq by exact Hneq.
  lia.
Qed.

(** In a mismatch, the update branch is an upper bound for the recurrence. *)
Lemma levenshtein_recursive_mismatch_upper_update : forall a b s t,
    a <> b ->
    levenshtein_recursive (a :: s) (b :: t) <= S (levenshtein_recursive s t).
Proof.
  intros a b s t Hneq.
  rewrite levenshtein_recursive_cons_neq by exact Hneq.
  lia.
Qed.

(** Adding one source character can increase distance by at most one. *)
Lemma levenshtein_recursive_insert_lower :
  forall a s t,
    levenshtein_recursive s t <= S (levenshtein_recursive (a :: s) t).
Proof.
  intros a0 s0 t0.
  refine (
    well_founded_induction
      lt_wf
      (fun m =>
         forall a s t, length s + length t = m ->
           levenshtein_recursive s t <= S (levenshtein_recursive (a :: s) t))
      _
      (length s0 + length t0)
      a0 s0 t0 eq_refl).
  intros m IH a s t Hm.
  destruct s as [|x xs], t as [|y ys].
  - rewrite levenshtein_recursive_nil_l, levenshtein_recursive_nil_r.
    simpl. lia.
  - assert (Hlen :
        length ys <= levenshtein_recursive (a :: "") (y :: ys)).
    {
      pose proof (levenshtein_recursive_length_bounds (a :: "") (y :: ys)) as [H1 _].
      simpl in H1.
      lia.
    }
    rewrite levenshtein_recursive_nil_l.
    simpl. lia.
  - rewrite !levenshtein_recursive_nil_r.
    simpl. lia.
  - destruct (ascii_dec x y) as [Hxy|Hxy].
    + subst y.
      rewrite levenshtein_recursive_skip_eq.
      destruct (ascii_dec a x) as [Hax|Hax].
      * subst a.
        rewrite levenshtein_recursive_skip_eq.
        assert (Hrec :
          levenshtein_recursive xs ys <=
          S (levenshtein_recursive (x :: xs) ys)).
        {
          apply (IH (length xs + length ys)).
          - simpl in Hm. lia.
          - reflexivity.
        }
        exact Hrec.
      * unfold levenshtein_recursive.
        cbn.
        destruct (ascii_dec a x) as [Hcontra|Hnax].
        { exfalso. apply Hax. exact Hcontra. }
        remember (levenshtein_chain (a :: x :: xs) ys) as p1.
        remember (levenshtein_chain (x :: xs) (x :: ys)) as p2.
        remember (levenshtein_chain (x :: xs) ys) as p3.
        destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
        cbn.
        assert (H3 :
          levenshtein_recursive xs ys <= S n3).
        {
          assert (Hrec :
            levenshtein_recursive xs ys <=
            S (levenshtein_recursive (x :: xs) ys)).
          {
            apply (IH (length xs + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          pose proof
            (levenshtein_recursive_of_chain (x :: xs) ys n3 r3 (eq_sym Heqp3))
            as Hc3.
          rewrite Hc3 in Hrec.
          exact Hrec.
        }
        assert (H1 :
          levenshtein_recursive xs ys <= S (S n1)).
        {
          assert (Hxys :
            levenshtein_recursive (x :: xs) ys <= S n1).
          {
            assert (Htmp :
              levenshtein_recursive (x :: xs) ys <=
              S (levenshtein_recursive (a :: x :: xs) ys)).
            {
              apply (IH (S (length xs) + length ys)).
              - simpl in Hm. lia.
              - reflexivity.
            }
            pose proof
              (levenshtein_recursive_of_chain (a :: x :: xs) ys n1 r1 (eq_sym Heqp1))
              as Hc1.
            rewrite Hc1 in Htmp.
            exact Htmp.
          }
          assert (Hrec :
            levenshtein_recursive xs ys <=
            S (levenshtein_recursive (x :: xs) ys)).
          {
            apply (IH (length xs + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          lia.
        }
        assert (H2 :
          levenshtein_recursive xs ys <= S (S n2)).
        {
          pose proof
            (levenshtein_recursive_of_chain (x :: xs) (x :: ys) n2 r2 (eq_sym Heqp2))
            as Hc2.
          rewrite levenshtein_recursive_skip_eq in Hc2.
          lia.
        }
        match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (a :: x :: xs) ys)
        end.
        try rewrite <- Heqp1.
        cbn.
        match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (x :: xs) (x :: ys))
        end.
        rewrite <- Heqp2.
        cbn.
        match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (x :: xs) ys)
        end.
        rewrite <- Heqp3.
        cbn.
        eapply (min3_app_cases
          (existT (fun n : nat => chain (a :: x :: xs) (x :: ys) n) (S n1)
                  (insert_chain x (a :: x :: xs) ys n1 r1))
          (existT (fun n : nat => chain (a :: x :: xs) (x :: ys) n) (S n2)
                  (delete_chain a (x :: xs) (x :: ys) n2 r2))
          (existT (fun n : nat => chain (a :: x :: xs) (x :: ys) n) (S n3)
                  (update_chain a x (x :: xs) ys n3 Hnax r3))
          (fun p => projT1 p)
          (fun p => levenshtein_recursive xs ys <= S (projT1 p))).
        -- exact H1.
        -- exact H2.
        -- cbn. lia.
    + unfold levenshtein_recursive.
      cbn.
      remember (levenshtein_chain (x :: xs) ys) as q1.
      remember (levenshtein_chain xs (y :: ys)) as q2.
      remember (levenshtein_chain xs ys) as q3.
      destruct q1 as [l1 c1], q2 as [l2 c2], q3 as [l3 c3].
      cbn.
      pose proof (min3_app_pf
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                (insert_chain y (x :: xs) ys l1 c1))
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                (delete_chain x xs (y :: ys) l2 c2))
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                (update_chain x y xs ys l3 Hxy c3))
        (fun p => projT1 p)) as [HL1 [HL2 HL3]].
      destruct (ascii_dec a y) as [Hay|Hay].
      * subst a.
        assert (Hq1 :
          levenshtein_recursive (x :: xs) ys = l1).
        {
          exact (levenshtein_recursive_of_chain (x :: xs) ys l1 c1 (eq_sym Heqq1)).
        }
        destruct (ascii_dec x y) as [Hcontra|Hxy'].
        { exfalso. apply Hxy. exact Hcontra. }
        cbn.
        match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (x :: xs) ys)
        end.
        rewrite <- Heqq1.
        cbn.
        pose proof (min3_app_pf
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                  (insert_chain y (x :: xs) ys l1 c1))
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                  (delete_chain x xs (y :: ys) l2 c2))
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                  (update_chain x y xs ys l3 Hxy' c3))
          (fun p => projT1 p)) as [HL1' _].
        cbn in HL1'.
        exact HL1'.
      * unfold levenshtein_recursive.
        cbn.
        destruct (ascii_dec a y) as [Hcontra|Hnay].
        { exfalso. apply Hay. exact Hcontra. }
        remember (levenshtein_chain (a :: x :: xs) ys) as p1.
        remember (levenshtein_chain (x :: xs) (y :: ys)) as p2.
        remember (levenshtein_chain (x :: xs) ys) as p3.
        destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
        cbn.
        assert (Hc1 :
          projT1 (min3_app
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                    (insert_chain y (x :: xs) ys l1 c1))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                    (delete_chain x xs (y :: ys) l2 c2))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                    (update_chain x y xs ys l3 Hxy c3))
            (fun p => projT1 p)) <= S l1).
        {
          exact HL1.
        }
        assert (H1 :
          projT1 (min3_app
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                    (insert_chain y (x :: xs) ys l1 c1))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                    (delete_chain x xs (y :: ys) l2 c2))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                    (update_chain x y xs ys l3 Hxy c3))
            (fun p => projT1 p)) <= S (S n1)).
        {
          assert (Hrec :
            levenshtein_recursive (x :: xs) ys <=
            S (levenshtein_recursive (a :: x :: xs) ys)).
          {
            apply (IH (S (length xs) + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          assert (Hl1n3 : l1 = n3).
          { inversion Heqq1. reflexivity. }
          pose proof
            (levenshtein_recursive_of_chain (x :: xs) ys n3 r3 (eq_sym Heqp3))
            as Hq3.
          pose proof
            (levenshtein_recursive_of_chain (a :: x :: xs) ys n1 r1 (eq_sym Heqp1))
            as Hp1.
          rewrite Hq3 in Hrec.
          rewrite Hp1 in Hrec.
          assert (Hl1le : l1 <= S n1).
          { rewrite Hl1n3. exact Hrec. }
          lia.
        }
        assert (H2 :
          projT1 (min3_app
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                    (insert_chain y (x :: xs) ys l1 c1))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                    (delete_chain x xs (y :: ys) l2 c2))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                    (update_chain x y xs ys l3 Hxy c3))
            (fun p => projT1 p)) <= S (S n2)).
        {
          assert (Hrec2 :
            levenshtein_recursive xs (y :: ys) <=
            S (levenshtein_recursive (x :: xs) (y :: ys))).
          {
            apply (IH (length xs + S (length ys))).
            - simpl in Hm. lia.
            - reflexivity.
          }
          pose proof
            (levenshtein_recursive_of_chain xs (y :: ys) l2 c2 (eq_sym Heqq2))
            as Hq2.
          pose proof
            (levenshtein_recursive_of_chain (x :: xs) (y :: ys) n2 r2 (eq_sym Heqp2))
            as Hp2.
          rewrite Hq2 in Hrec2.
          rewrite Hp2 in Hrec2.
          eapply PeanoNat.Nat.le_trans.
          - exact HL2.
          - cbn. lia.
        }
        assert (H3 :
          projT1 (min3_app
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                    (insert_chain y (x :: xs) ys l1 c1))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                    (delete_chain x xs (y :: ys) l2 c2))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                    (update_chain x y xs ys l3 Hxy c3))
            (fun p => projT1 p)) <= S (S n3)).
        {
          assert (Hrec3 :
            levenshtein_recursive xs ys <=
            S (levenshtein_recursive (x :: xs) ys)).
          {
            apply (IH (length xs + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          pose proof
            (levenshtein_recursive_of_chain xs ys l3 c3 (eq_sym Heqq3))
            as Hq3'.
          pose proof
            (levenshtein_recursive_of_chain (x :: xs) ys n3 r3 (eq_sym Heqp3))
            as Hp3.
          rewrite Hq3' in Hrec3.
          rewrite Hp3 in Hrec3.
          eapply PeanoNat.Nat.le_trans.
          - exact HL3.
          - cbn. lia.
        }
        destruct (ascii_dec x y) as [Hcontra|Hxy'].
        { exfalso. apply Hxy. exact Hcontra. }
        cbn.
        assert (Hn3n1 : n3 <= S n1).
        {
          assert (Hrecx :
            levenshtein_recursive (x :: xs) ys <=
            S (levenshtein_recursive (a :: x :: xs) ys)).
          {
            apply (IH (S (length xs) + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          pose proof
            (levenshtein_recursive_of_chain (x :: xs) ys n3 r3 (eq_sym Heqp3))
            as Hp3.
          pose proof
            (levenshtein_recursive_of_chain (a :: x :: xs) ys n1 r1 (eq_sym Heqp1))
            as Hp1.
          rewrite Hp3 in Hrecx.
          rewrite Hp1 in Hrecx.
          exact Hrecx.
        }
        remember (min3_app
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n3)
                  (insert_chain y (x :: xs) ys n3 r3))
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                  (delete_chain x xs (y :: ys) l2 c2))
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                  (update_chain x y xs ys l3 Hxy' c3))
          (fun p => projT1 p)) as q2.
        destruct q2 as [m2 c2'].
        cbn.
        pose proof (min3_app_pf
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n3)
                  (insert_chain y (x :: xs) ys n3 r3))
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                  (delete_chain x xs (y :: ys) l2 c2))
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                  (update_chain x y xs ys l3 Hxy' c3))
          (fun p => projT1 p)) as [Hm2_1 [Hm2_2 Hm2_3]].
        cbn in Hm2_1, Hm2_2, Hm2_3.
        assert (Hm2_1' : m2 <= S n3).
        {
          change m2 with
            (projT1
               (existT (fun n : nat => chain (x :: xs) (y :: ys) n) m2 c2')).
          rewrite Heqq0.
          exact Hm2_1.
        }
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (x :: xs) ys)
        end.
        rewrite <- Heqp3.
        cbn.
        try rewrite <- Heqq0.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (a :: x :: xs) ys)
        end.
        try rewrite <- Heqp1.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (x :: xs) (y :: ys))
        end.
        try rewrite <- Heqq0.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (x :: xs) ys)
        end.
        try rewrite <- Heqp3.
        cbn.
        eapply (min3_app_cases
          (existT (fun n : nat => chain (a :: x :: xs) (y :: ys) n) (S n1)
                  (insert_chain y (a :: x :: xs) ys n1 r1))
          (existT (fun n : nat => chain (a :: x :: xs) (y :: ys) n) (S m2)
                  (delete_chain a (x :: xs) (y :: ys) m2 c2'))
          (existT (fun n : nat => chain (a :: x :: xs) (y :: ys) n) (S n3)
                  (update_chain a y (x :: xs) ys n3 Hay r3))
          (fun p => projT1 p)
          (fun p => m2 <= S (projT1 p))).
        -- eapply PeanoNat.Nat.le_trans.
           ++ exact Hm2_1'.
           ++ cbn. lia.
        -- cbn. lia.
        -- eapply PeanoNat.Nat.le_trans.
           ++ exact Hm2_1'.
           ++ cbn. lia.
Qed.

(** Levenshtein distance is symmetric. *)
Lemma levenshtein_recursive_sym :
  forall s t, levenshtein_recursive s t = levenshtein_recursive t s.
Proof.
  intros s0 t0.
  refine (
    well_founded_induction
      lt_wf
      (fun m =>
         forall s t, length s + length t = m ->
           levenshtein_recursive s t = levenshtein_recursive t s)
      _
      (length s0 + length t0)
      s0 t0 eq_refl).
  intros m IH s t Hm.
  destruct s as [|x xs], t as [|y ys].
  - reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - destruct (ascii_dec x y) as [Hxy|Hxy].
    + subst y.
      rewrite levenshtein_recursive_skip_eq.
      rewrite (levenshtein_recursive_skip_eq x ys xs).
      apply (IH (length xs + length ys)).
      { simpl in Hm. lia. }
      { reflexivity. }
    + unfold levenshtein_recursive.
      cbn.
      destruct (ascii_dec x y) as [Hcontra|Hnxy].
      { exfalso. apply Hxy. exact Hcontra. }
      destruct (ascii_dec y x) as [Hyx|Hnyx].
      { exfalso. apply Hxy. symmetry. exact Hyx. }
      remember (levenshtein_chain (x :: xs) ys) as p1.
      remember (levenshtein_chain xs (y :: ys)) as p2.
      remember (levenshtein_chain xs ys) as p3.
      remember (levenshtein_chain (y :: ys) xs) as q1.
      remember (levenshtein_chain ys (x :: xs)) as q2.
      remember (levenshtein_chain ys xs) as q3.
      destruct p1 as [n1 c1], p2 as [n2 c2], p3 as [n3 c3].
      destruct q1 as [m1 c4], q2 as [m2 c5], q3 as [m3 c6].
      cbn.
      assert (H12 : n1 = m2).
      {
        assert (Hrec :
          levenshtein_recursive (x :: xs) ys =
          levenshtein_recursive ys (x :: xs)).
        {
          apply (IH (S (length xs) + length ys)).
          { simpl in Hm. lia. }
          { reflexivity. }
        }
        pose proof
          (levenshtein_recursive_of_chain (x :: xs) ys n1 c1 (eq_sym Heqp1))
          as Hp1.
        pose proof
          (levenshtein_recursive_of_chain ys (x :: xs) m2 c5 (eq_sym Heqq2))
          as Hq2.
        rewrite Hp1 in Hrec.
        rewrite Hq2 in Hrec.
        exact Hrec.
      }
      assert (H21 : n2 = m1).
      {
        assert (Hrec :
          levenshtein_recursive xs (y :: ys) =
          levenshtein_recursive (y :: ys) xs).
        {
          apply (IH (length xs + S (length ys))).
          { simpl in Hm. lia. }
          { reflexivity. }
        }
        pose proof
          (levenshtein_recursive_of_chain xs (y :: ys) n2 c2 (eq_sym Heqp2))
          as Hp2.
        pose proof
          (levenshtein_recursive_of_chain (y :: ys) xs m1 c4 (eq_sym Heqq1))
          as Hq1.
        rewrite Hp2 in Hrec.
        rewrite Hq1 in Hrec.
        exact Hrec.
      }
      assert (H33 : n3 = m3).
      {
        assert (Hrec :
          levenshtein_recursive xs ys =
          levenshtein_recursive ys xs).
        {
          apply (IH (length xs + length ys)).
          { simpl in Hm. lia. }
          { reflexivity. }
        }
        pose proof
          (levenshtein_recursive_of_chain xs ys n3 c3 (eq_sym Heqp3))
          as Hp3.
        pose proof
          (levenshtein_recursive_of_chain ys xs m3 c6 (eq_sym Heqq3))
          as Hq3.
        rewrite Hp3 in Hrec.
        rewrite Hq3 in Hrec.
        exact Hrec.
      }
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain (x :: xs) ys)
      end.
      try rewrite <- Heqp1.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain xs (y :: ys))
      end.
      try rewrite <- Heqp2.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain xs ys)
      end.
      try rewrite <- Heqp3.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain (y :: ys) xs)
      end.
      try rewrite <- Heqq1.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain ys (x :: xs))
      end.
      try rewrite <- Heqq2.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain ys xs)
      end.
      try rewrite <- Heqq3.
      cbn.
      rewrite (min3_app_value
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n1)
                (insert_chain y (x :: xs) ys n1 c1))
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n2)
                (delete_chain x xs (y :: ys) n2 c2))
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n3)
                (update_chain x y xs ys n3 Hnxy c3))
        (fun p => projT1 p)).
      rewrite (min3_app_value
        (existT (fun n : nat => chain (y :: ys) (x :: xs) n) (S m1)
                (insert_chain x (y :: ys) xs m1 c4))
        (existT (fun n : nat => chain (y :: ys) (x :: xs) n) (S m2)
                (delete_chain y ys (x :: xs) m2 c5))
        (existT (fun n : nat => chain (y :: ys) (x :: xs) n) (S m3)
                (update_chain y x ys xs m3 Hnyx c6))
        (fun p => projT1 p)).
      cbn.
      rewrite <- H12, <- H21, <- H33.
      f_equal.
      apply min3_comm12.
Qed.

(** Adding one target character can increase distance by at most one. *)
Lemma levenshtein_recursive_insert_lower_r :
  forall a s t,
    levenshtein_recursive s t <= S (levenshtein_recursive s (a :: t)).
Proof.
  intros a s t.
  rewrite (levenshtein_recursive_sym s t).
  rewrite (levenshtein_recursive_sym s (a :: t)).
  apply levenshtein_recursive_insert_lower.
Qed.

(** Deleting one source head gives a one-step upper bound. *)
Lemma levenshtein_recursive_delete_upper :
  forall a s t,
    levenshtein_recursive (a :: s) t <= S (levenshtein_recursive s t).
  Proof.
  intros a s t.
  destruct t as [|b ys].
  - rewrite !levenshtein_recursive_nil_r.
    simpl. lia.
  - destruct (ascii_dec a b) as [Hab|Hab].
    + subst b.
      rewrite levenshtein_recursive_skip_eq.
      apply levenshtein_recursive_insert_lower_r.
    + apply levenshtein_recursive_mismatch_upper_delete.
      exact Hab.
Qed.

(** Updating the source head gives a one-step upper bound. *)
Lemma levenshtein_recursive_update_upper :
  forall a a' s t,
    a' <> a ->
    levenshtein_recursive (a' :: s) t <= S (levenshtein_recursive (a :: s) t).
Proof.
  intros a0 a'0 s0 t0 Hneq0.
  refine (
    well_founded_induction
      lt_wf
      (fun m =>
         forall a a' s t, a' <> a ->
           length s + length t = m ->
           levenshtein_recursive (a' :: s) t <=
           S (levenshtein_recursive (a :: s) t))
      _
      (length s0 + length t0)
      a0 a'0 s0 t0 Hneq0 eq_refl).
  intros m IH a a' s t Hneq Hm.
  destruct t as [|b ys].
  - rewrite !levenshtein_recursive_nil_r.
    simpl. lia.
  - destruct (ascii_dec a' b) as [Ha'b|Ha'b].
    + subst b.
      rewrite levenshtein_recursive_skip_eq.
      unfold levenshtein_recursive.
      cbn.
      destruct (ascii_dec a a') as [Hcontra|Hna].
      { exfalso. apply Hneq. symmetry. exact Hcontra. }
      remember (levenshtein_chain (a :: s) ys) as p1.
      remember (levenshtein_chain s (a' :: ys)) as p2.
      remember (levenshtein_chain s ys) as p3.
      destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
      cbn.
      assert (H1 : levenshtein_recursive s ys <= S (S n1)).
      {
        assert (Hrec : levenshtein_recursive s ys <= S (levenshtein_recursive (a :: s) ys)).
        { apply levenshtein_recursive_insert_lower. }
        pose proof
          (levenshtein_recursive_of_chain (a :: s) ys n1 r1 (eq_sym Heqp1))
          as Hp1.
        rewrite Hp1 in Hrec.
        lia.
      }
      assert (H2 : levenshtein_recursive s ys <= S (S n2)).
      {
        assert (Hrec : levenshtein_recursive s ys <= S (levenshtein_recursive s (a' :: ys))).
        { apply levenshtein_recursive_insert_lower_r. }
        pose proof
          (levenshtein_recursive_of_chain s (a' :: ys) n2 r2 (eq_sym Heqp2))
          as Hp2.
        rewrite Hp2 in Hrec.
        lia.
      }
      assert (H3 : levenshtein_recursive s ys <= S (S n3)).
      {
        pose proof
          (levenshtein_recursive_of_chain s ys n3 r3 (eq_sym Heqp3))
          as Hp3.
        rewrite Hp3.
        lia.
      }
      pose proof
        (levenshtein_recursive_of_chain s ys n3 r3 (eq_sym Heqp3))
        as Hs.
      try rewrite <- Hs.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain (a :: s) ys)
      end.
      try rewrite <- Heqp1.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain s (a' :: ys))
      end.
      try rewrite <- Heqp2.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain s ys)
      end.
      try rewrite <- Heqp3.
      cbn.
      eapply (min3_app_cases
        (existT (fun n : nat => chain (a :: s) (a' :: ys) n) (S n1)
                (insert_chain a' (a :: s) ys n1 r1))
        (existT (fun n : nat => chain (a :: s) (a' :: ys) n) (S n2)
                (delete_chain a s (a' :: ys) n2 r2))
        (existT (fun n : nat => chain (a :: s) (a' :: ys) n) (S n3)
                (update_chain a a' s ys n3 Hna r3))
        (fun p => projT1 p)
        (fun p => n3 <= S (projT1 p))).
      * rewrite Hs in H1. exact H1.
      * rewrite Hs in H2. exact H2.
      * rewrite Hs in H3. exact H3.
    + unfold levenshtein_recursive.
      cbn.
      destruct (ascii_dec a' b) as [Hcontra|Hna'b].
      { exfalso. apply Ha'b. exact Hcontra. }
      remember (levenshtein_chain (a' :: s) ys) as q1.
      remember (levenshtein_chain s (b :: ys)) as q2.
      remember (levenshtein_chain s ys) as q3.
      destruct q1 as [l1 c1], q2 as [l2 c2], q3 as [l3 c3].
      cbn.
      pose proof (min3_app_pf
        (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                (insert_chain b (a' :: s) ys l1 c1))
        (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                (delete_chain a' s (b :: ys) l2 c2))
        (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                (update_chain a' b s ys l3 Hna'b c3))
        (fun p => projT1 p)) as [HL1 [HL2 HL3]].
      destruct (ascii_dec a b) as [Hab|Hab].
      * subst b.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (a' :: s) ys)
        end.
        try rewrite <- Heqq1.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain s (a :: ys))
        end.
        try rewrite <- Heqq2.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain s ys)
        end.
        try rewrite <- Heqq3.
        cbn.
        exact HL3.
      * unfold levenshtein_recursive.
        cbn.
        destruct (ascii_dec a b) as [Hcontra2|Hnab].
        { exfalso. apply Hab. exact Hcontra2. }
        remember (levenshtein_chain (a :: s) ys) as p1.
        remember (levenshtein_chain s (b :: ys)) as p2.
        remember (levenshtein_chain s ys) as p3.
        destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
        cbn.
        assert (H1 :
          projT1 (min3_app
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                    (insert_chain b (a' :: s) ys l1 c1))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                    (delete_chain a' s (b :: ys) l2 c2))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                    (update_chain a' b s ys l3 Hna'b c3))
            (fun p => projT1 p)) <= S (S n1)).
        {
          assert (Hl1n1 : l1 <= S n1).
          {
            assert (Hrec :
              levenshtein_recursive (a' :: s) ys <=
              S (levenshtein_recursive (a :: s) ys)).
            {
              apply (IH (length s + length ys)).
              - simpl in Hm. lia.
              - exact Hneq.
              - reflexivity.
            }
            pose proof
              (levenshtein_recursive_of_chain (a' :: s) ys l1 c1 (eq_sym Heqq1))
              as Hq1.
            pose proof
              (levenshtein_recursive_of_chain (a :: s) ys n1 r1 (eq_sym Heqp1))
              as Hp1.
            rewrite Hq1 in Hrec.
            rewrite Hp1 in Hrec.
            exact Hrec.
          }
          eapply PeanoNat.Nat.le_trans.
          - exact HL1.
          - cbn. lia.
        }
        assert (H2 :
          projT1 (min3_app
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                    (insert_chain b (a' :: s) ys l1 c1))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                    (delete_chain a' s (b :: ys) l2 c2))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                    (update_chain a' b s ys l3 Hna'b c3))
            (fun p => projT1 p)) <= S (S n2)).
        {
          assert (Hl2n2 : l2 = n2).
          {
            inversion Heqq2.
            reflexivity.
          }
          eapply PeanoNat.Nat.le_trans.
          - exact HL2.
          - cbn. lia.
        }
        assert (H3 :
          projT1 (min3_app
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                    (insert_chain b (a' :: s) ys l1 c1))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                    (delete_chain a' s (b :: ys) l2 c2))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                    (update_chain a' b s ys l3 Hna'b c3))
            (fun p => projT1 p)) <= S (S n3)).
        {
          assert (Hl3n3 : l3 = n3).
          {
            inversion Heqq3.
            reflexivity.
          }
          eapply PeanoNat.Nat.le_trans.
          - exact HL3.
          - cbn. lia.
        }
        assert (Heq2' :
          existT (fun n : nat => chain s (b :: ys) n) l2 c2 =
          levenshtein_chain s (b :: ys)).
        {
          rewrite Heqq2.
          exact Heqp2.
        }
        assert (Heq3' :
          existT (fun n : nat => chain s ys n) l3 c3 =
          levenshtein_chain s ys).
        {
          rewrite Heqq3.
          exact Heqp3.
        }
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (a' :: s) ys)
        end.
        try rewrite <- Heqq1.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain s (b :: ys))
        end.
        try rewrite <- Heq2'.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain s ys)
        end.
        try rewrite <- Heq3'.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (a :: s) ys)
        end.
        try rewrite <- Heqp1.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain s (b :: ys))
        end.
        try rewrite <- Heqp2.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain s ys)
        end.
        try rewrite <- Heqp3.
        cbn.
        eapply (min3_app_cases
          (existT (fun n : nat => chain (a :: s) (b :: ys) n) (S n1)
                  (insert_chain b (a :: s) ys n1 r1))
          (existT (fun n : nat => chain (a :: s) (b :: ys) n) (S l2)
                  (delete_chain a s (b :: ys) l2 c2))
          (existT (fun n : nat => chain (a :: s) (b :: ys) n) (S l3)
                  (update_chain a b s ys l3 Hab c3))
          (fun p => projT1 p)
          (fun p =>
             projT1 (min3_app
                (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                       (insert_chain b (a' :: s) ys l1 c1))
               (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                       (delete_chain a' s (b :: ys) l2 c2))
               (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                        (update_chain a' b s ys l3 Hna'b c3))
                (fun p0 => projT1 p0))
              <= S (projT1 p))).
        -- exact H1.
        -- assert (Hn2l2 : n2 = l2).
           { inversion Heqq2. reflexivity. }
           rewrite Hn2l2 in H2.
           exact H2.
        -- assert (Hn3l3 : n3 = l3).
           { inversion Heqq3. reflexivity. }
           rewrite Hn3l3 in H3.
           exact H3.
Qed.

(** [levenshtein_recursive] is a lower bound for every edit script, hence the
    script produced by [levenshtein_chain] is optimal. *)
Theorem levenshtein_recursive_is_minimal :
  forall s t n (c : chain s t n),
    levenshtein_recursive s t <= n.
Proof.
  intros s t n c.
  induction c.
  - reflexivity.
  - rewrite levenshtein_recursive_skip_eq.
    exact IHc.
  - destruct e.
    + eapply PeanoNat.Nat.le_trans.
      * apply (levenshtein_recursive_insert_lower a s u).
      * apply (proj1 (PeanoNat.Nat.succ_le_mono _ _)).
        exact IHc.
    + eapply PeanoNat.Nat.le_trans.
      * apply (levenshtein_recursive_delete_upper a s u).
      * apply (proj1 (PeanoNat.Nat.succ_le_mono _ _)).
        exact IHc.
    + eapply PeanoNat.Nat.le_trans.
      * apply (levenshtein_recursive_update_upper a a' s u).
        exact neq.
      * apply (proj1 (PeanoNat.Nat.succ_le_mono _ _)).
        exact IHc.
Qed.

(* Eval compute in (levenshtein_chain "pascal" "haskell"). *)

End Levenshtein.
