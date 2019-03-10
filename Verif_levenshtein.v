Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Peano.
Require Import Omega.
Require Import Coq.Program.Equality.

Open Scope string_scope.
Print string.
Infix "::" := String (at level 60, right associativity) : string_scope.

Inductive edit : string -> string -> Type :=
| insertion (a : ascii) {s : string} : edit s (a :: s)
| deletion (a : ascii) {s : string} : edit (a :: s) s
| update (a' : ascii) (a : ascii) {s : string} : edit (a' :: s) (a :: s).

Inductive chain : string -> string -> Type :=
| empty : chain "" ""
| skip {a : ascii} {s t : string} : chain s t -> chain (a :: s) (a :: t)
| change {s t u : string} : edit s t -> chain t u -> chain s u.

Fixpoint count {s t : string} (c : chain s t) : nat :=
  match c with
  | empty => 0
  | skip c' => count c'
  | change _ c' => S (count c')
  end.

Lemma same_chain : forall s, chain s s.
intros s. induction s; constructor. auto.
Defined.

Lemma insert_chain : forall c s1 s2, chain s1 s2 -> chain s1 (c :: s2).
intros c s1 s2 C.
apply (@change _ (c :: s1)); constructor. auto.
Defined.

Lemma inserts_chain : forall s1 s2, chain s2 (s1 ++ s2).
intros.
induction s1; simpl.
induction s2; constructor; auto.
apply insert_chain; auto.
Defined.

(* transparent string version of app_nil_r *)
Lemma tr_app_empty_r : forall {A : Type} (l : string), l ++ "" = l.
intros A l; induction l. auto. simpl; rewrite IHl; auto.
Defined.


Lemma inserts_chain_empty : forall s, chain "" s.
intros s.
induction s; simpl.
constructor.
apply insert_chain. auto.
Defined.

Lemma delete_chain : forall c s1 s2, chain s1 s2 -> chain (c :: s1) s2.
intros c s1 s2 C.
apply (@change _ s1). constructor. auto.
Defined.

Lemma deletes_chain : forall s1 s2, chain (s1 ++ s2) s2.
intros.
induction s1; simpl.
apply same_chain.
apply delete_chain.
auto.
Defined.

Lemma deletes_chain_empty : forall s, chain s "".
intros s.
induction s; simpl.
constructor. apply delete_chain. auto.
Defined.

Lemma update_chain : forall c c' s1 s2, chain s1 s2 -> chain (c :: s1) (c' :: s2).
intros c c' s1 s2 C.
apply (@change _ (c' :: s1)). constructor. apply skip. auto.
Defined.

Lemma chain_trans : forall s t u, chain s t -> chain t u -> chain s u.
intros s t u c1 c2.
induction c1.
* auto.
Admitted.

Lemma chain_reverse : forall s t, chain s t -> chain t s.
Admitted.

(* These aux lemmas are needed because Coq wants to use the fixpoint
   we are defining as a higher order function otherwise. *)
Lemma aux_insert : forall s t x xs y ys, s = x :: xs -> t = y :: ys -> chain s ys -> chain s t.
intros s t x xs y ys eq1 eq2 r1.
subst.
apply (insert_chain y (x :: xs) ys r1).
Defined.

Lemma aux_delete : forall s t x xs y ys, s = x :: xs -> t = y :: ys -> chain xs (y :: ys) -> chain s t.
intros s t x xs y ys eq1 eq2 r2.
subst.
apply (delete_chain x xs (y :: ys) r2).
Defined.

Lemma aux_update : forall s t x xs y ys, s = x :: xs -> t = y :: ys -> chain xs ys -> chain s t.
intros s t x xs y ys eq1 eq2 r3.
subst.
apply (update_chain x y xs ys r3).
Defined.

Lemma aux_eq_char : forall s t x xs y ys,
    s = x :: xs -> t = y :: ys -> x = y -> chain xs ys -> chain s t.
intros s t x xs y ys eq1 eq2 ceq C.
subst. apply skip. auto.
Defined.

Lemma aux_both_empty : forall s t, s = "" -> t = "" -> chain s t.
intros s t eq1 eq2. subst. constructor.
Defined.

Definition min3_app {t : Type} (x y z : t) (f : t -> nat) : t :=
  let n1 := f x in let n2 := f y in let n3 := f z in
  match (Nat.leb n1 n2) with
  | true => match (Nat.leb n1 n3) with | true => x | false => z end
  | false => match (Nat.leb n2 n3) with | true => y | false => z end
  end.

Lemma leb_false : forall n m, (n <=? m) = false -> (m <? n) = true.
intros n m H.
rewrite Nat.leb_antisym in *.
assert (eq : forall b, negb b = false -> b = true).
  intros; destruct b; auto.
exact (eq _ H).
Qed.

Lemma min3_app_pf {t : Type} (x y z : t) (f : t -> nat) :
     f (min3_app x y z f) <= f x
  /\ f (min3_app x y z f) <= f y
  /\ f (min3_app x y z f) <= f z.
Proof.
unfold min3_app.
destruct (Nat.leb (f x) (f y)) eqn:leb1.
* destruct (Nat.leb (f x) (f z)) eqn:leb2.
  - rewrite (Nat.leb_le (f x) (f y)) in *.
    rewrite (Nat.leb_le (f x) (f z)) in *.
    auto.
  - rewrite (Nat.leb_le (f x) (f y)) in *.
    pose ((proj1 (Nat.ltb_lt (f z) (f x))) (leb_false _ _ leb2)).
    omega.
* destruct (Nat.leb (f y) (f z)) eqn:leb3.
  - rewrite (Nat.leb_le (f y) (f z)) in *.
    pose ((proj1 (Nat.ltb_lt (f y) (f x))) (leb_false _ _ leb1)).
    omega.
  - pose ((proj1 (Nat.ltb_lt (f z) (f y))) (leb_false _ _ leb3)).
    pose ((proj1 (Nat.ltb_lt (f y) (f x))) (leb_false _ _ leb1)).
    omega.
Qed.

Fixpoint levenshtein_chain (s : string)  :=
  fix levenshtein_chain1 (t : string) : chain s t :=
    (match s as s', t as t' return s = s' -> t = t' -> chain s t with
    | "" , "" =>
        fun eq1 eq2 => aux_both_empty s t eq1 eq2
    | "" , _ =>
        fun eq1 eq2 =>
          ltac:(rewrite eq1; apply (inserts_chain_empty t))
    | y :: ys , "" =>
        fun eq1 eq2 =>
          ltac:(rewrite eq1, eq2; apply (deletes_chain_empty (y :: ys)))
    | x :: xs, y :: ys =>
      fun eq1 eq2 =>
        match ascii_dec x y with
        | left ceq => aux_eq_char s t x xs y ys eq1 eq2 ceq (levenshtein_chain xs ys)
        | right neq =>
          let r1 := levenshtein_chain1 ys in
          let r2 := levenshtein_chain xs (y :: ys) in
          let r3 := levenshtein_chain xs ys in
          let r1' : chain s t :=
              aux_insert s t x xs y ys eq1 eq2 r1 in
          let r2' : chain s t :=
              aux_delete s t x xs y ys eq1 eq2 r2 in
              (* ltac:(rewrite eq1, eq2; *)
              (*       apply (delete_chain x xs (y :: ys) r2)) in *)
          let r3' : chain s t :=
              aux_update s t x xs y ys eq1 eq2 r3 in
              (* ltac:(rewrite eq1, eq2; *)
              (*       apply (update_chain x y xs ys r3)) in *)
          min3_app r1' r2' r3' count
        end
    end) (eq_refl s) (eq_refl t).

Eval compute in (levenshtein_chain "Appel" "apple").
Eval compute in (count (levenshtein_chain "Appel" "apple")).

Lemma count_over_skip {a : ascii} {s t : string} (c : chain s t) :
    count c = count (@skip a s t c).
Proof.
auto.
Qed.

Ltac unfold_eq := unfold eq_rec_r, eq_rec, eq_rect, eq_sym.

Lemma count_chain_skip : forall a s t c,
     count (levenshtein_chain s t) <= count c
  -> count (levenshtein_chain (a :: s) (a :: t)) <= count (@skip a s t c).
Proof.
intros a s t c le.
simpl.
destruct (ascii_dec a a) as [ceq|neq].
- simpl in *.
  unfold aux_eq_char.
  unfold_eq.
  destruct ceq.
  auto.
- contradiction.
Qed.

Lemma first_empty_chain_is_length (s : string) :
  count (inserts_chain_empty s) = length s.
Proof.
induction s as [|x xs].
* auto.
* simpl. f_equal. auto.
Qed.

Lemma length_le_first_empty_chain (s : string) (c : chain "" s) :
  length s <= count c.
Proof.
induction s.
* apply Nat.le_0_l.
* inversion c.
  inversion H.
  subst.
  (* dependent induction c. *)
  (* simpl. *)
  (* apply le_n_S. *)

  (* assert (c' : chain t s). *)
  (* induction t. *)
  (* inversion e. *)

Admitted.


Lemma second_empty_chain_is_length (s : string) :
  count (deletes_chain_empty s) = length s.
Proof.
induction s as [|x xs].
* auto.
* simpl. f_equal. auto.
Qed.

Lemma length_le_second_empty_chain (s : string) (c : chain s "") :
  length s <= count c.
Proof.
dependent induction c.
apply Nat.le_0_l.
dependent induction e;
pose (IHc c (eq_refl _) (JMeq_refl _)); simpl in *; omega.
Qed.

(* Definition remove_head_in_chain : forall a s t,  *)
(*     chain (a :: s) (a :: t) -> chain s t. *)
(* intros a s t c. *)
(* inversion c. *)
(* * auto. *)
(* * inversion H0. *)


Fixpoint min_chain (s : string) :
  forall (t : string) (c : chain s t),
    count (levenshtein_chain s t) <= count c.
Proof.
refine (fix min_chain1 (t : string) (c : chain s t) := _).
destruct s as [|x xs] eqn:s_eq, t as [|y ys] eqn:t_eq.
* simpl. omega.
* pose (first_empty_chain_is_length (y :: ys)).
  pose (length_le_first_empty_chain _ c).
  simpl in *.
  omega.
* pose (second_empty_chain_is_length (x :: xs)).
  pose (length_le_second_empty_chain _ c).
  simpl in *.
  omega.
* simpl.
  destruct (ascii_dec x y) eqn:c_eq.
  + destruct e. simpl.
    epose (r := min_chain xs ys _).
    admit.
  + epose (m1 := min_chain1 ys).
    epose (m2 := min_chain xs (y :: ys)).
    epose (m3 := min_chain xs ys).
    Check min3_app_pf.
    edestruct (min3_app_pf _ _ _ count) as [le1 le2 le3].

  + induction c.
    - auto.
    - apply count_chain_skip.

Admitted.


(*
Theorem min_chain (s t : string) (c : chain s t) :
    count (levenshtein_chain s t) <= count c.
Proof.
induction s as [|x xs] eqn:s_eq, t as [|y ys] eqn:t_eq.
* simpl. omega.
* pose (first_empty_chain_is_length (y :: ys)).
  pose (length_le_first_empty_chain _ c).
  simpl in *.
  omega.
* pose (second_empty_chain_is_length (x :: xs)).
  pose (length_le_second_empty_chain _ c).
  simpl in *.
  omega.
* simpl.
  destruct (ascii_dec x y) eqn:c_eq.
  + unfold aux_eq_char. unfold_eq. destruct e.
    simpl.
  + induction c.
    - auto.
    - apply count_chain_skip.

    (* generalize dependent s0. *)
    (* generalize dependent t0. *)
    (* intros. *)

  -

Admitted.
*)
