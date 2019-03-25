Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Peano.
Require Import Omega.
Require Import Coq.Program.Equality.

Require Import StringFacts.

Open Scope string_scope.

Inductive edit : string -> string -> Type :=
| insertion (a : ascii) {s : string} : edit s (a :: s)
| deletion (a : ascii) {s : string} : edit (a :: s) s
| update (a' : ascii) (a : ascii)
         {neq : a' <> a} {s : string} : edit (a' :: s) (a :: s).

Inductive chain : string -> string -> nat -> Type :=
| empty : chain "" "" 0
| skip {a : ascii} {s t : string} {n : nat} :
    chain s t n -> chain (a :: s) (a :: t) n
| change {s t u : string} {n : nat} :
    edit s t -> chain t u n -> chain s u (S n).

Lemma same_chain : forall s, chain s s 0.
intros s. induction s; constructor; auto.
Defined.

Lemma insert_chain : forall c s1 s2 n, chain s1 s2 n -> chain s1 (c :: s2) (S n).
intros c s1 s2 n C.
apply (@change _ (c :: s1)); constructor. auto.
Defined.

Lemma inserts_chain : forall s1 s2, chain s2 (s1 ++ s2) (length s1).
intros.
induction s1; simpl.
induction s2; constructor; auto.
apply insert_chain; auto.
Defined.

(* transparent string version of app_nil_r *)
Lemma tr_app_empty_r : forall {A : Type} (l : string), l ++ "" = l.
intros A l; induction l. auto. simpl; rewrite IHl; auto.
Defined.

Lemma inserts_chain_empty : forall s, chain "" s (length s).
intros s.
induction s; simpl.
constructor.
apply insert_chain. auto.
Defined.

Lemma delete_chain : forall c s1 s2 n, chain s1 s2 n -> chain (c :: s1) s2 (S n).
intros c s1 s2 n C.
apply (@change _ s1). constructor. auto.
Defined.

Lemma deletes_chain : forall s1 s2, chain (s1 ++ s2) s2 (length s1).
intros.
induction s1; simpl.
apply same_chain.
apply delete_chain.
auto.
Defined.

Lemma deletes_chain_empty : forall s, chain s "" (length s).
intros s.
induction s; simpl.
constructor. apply delete_chain. auto.
Defined.

Lemma update_chain : forall c c' s1 s2 n,
    c <> c' -> chain s1 s2 n -> chain (c :: s1) (c' :: s2) (S n).
intros c c' s1 s2 n neq C.
apply (@change _ (c' :: s1)). constructor. auto. apply skip. auto.
Defined.

(* Lemma chain_trans : forall s t u, chain s t -> chain t u -> chain s u. *)
(* intros s t u c1 c2. *)
(* induction c2. *)
(* * auto. *)
(* * *)
(* Abort. *)

(* Lemma chain_reverse : forall s t, chain s t -> chain t s. *)
(* intros s t c. *)
(* induction c. *)
(* * constructor. *)
(* * constructor; auto. *)
(* * induction e eqn:e_eq. *)
(*   - admit. *)
(*   - admit. *)
(*   - *)
(* Abort. *)

(* These aux lemmas are needed because Coq wants to use the fixpoint
   we are defining as a higher order function otherwise. *)
Lemma aux_insert : forall s t x xs y ys n,
    s = x :: xs -> t = y :: ys -> chain s ys n -> chain s t (S n).
intros s t x xs y ys n eq1 eq2 r1.
subst.
apply (insert_chain y (x :: xs) ys n r1).
Defined.

Lemma aux_delete : forall s t x xs y ys n,
    s = x :: xs -> t = y :: ys -> chain xs (y :: ys) n -> chain s t (S n).
intros s t x xs y ys n eq1 eq2 r2.
subst.
apply (delete_chain x xs (y :: ys) n r2).
Defined.

Lemma aux_update : forall s t x xs y ys n,
    x <> y -> s = x :: xs -> t = y :: ys -> chain xs ys n -> chain s t (S n).
intros s t x xs y ys n neq eq1 eq2 r3.
subst.
apply (update_chain x y xs ys n neq r3).
Defined.

Lemma aux_eq_char : forall s t x xs y ys n,
    s = x :: xs -> t = y :: ys -> x = y -> chain xs ys n -> chain s t n.
intros s t x xs y ys n eq1 eq2 ceq C.
subst. apply skip. auto.
Defined.

Lemma aux_both_empty : forall s t, s = "" -> t = "" -> chain s t 0.
intros s t eq1 eq2. subst. constructor.
Defined.

Lemma leb_false : forall n m, (n <=? m) = false -> (m <? n) = true.
intros n m H.
rewrite Nat.leb_antisym in *.
assert (eq : forall b, negb b = false -> b = true).
  intros; destruct b; auto.
exact (eq _ H).
Qed.

Definition min3_app {t : Type} (x y z : t) (f : t -> nat) : t :=
  let n1 := f x in let n2 := f y in let n3 := f z in
  match (Nat.leb n1 n2) with
  | true => match (Nat.leb n1 n3) with | true => x | false => z end
  | false => match (Nat.leb n2 n3) with | true => y | false => z end
  end.

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
              (* ltac:(rewrite eq1, eq2; *)
              (*       apply (delete_chain x xs (y :: ys) r2)) in *)
          let r3' : chain s t (S n3) :=
              aux_update s t x xs y ys n3 neq eq1 eq2 r3 in
              (* ltac:(rewrite eq1, eq2; *)
              (*       apply (update_chain x y xs ys r3)) in *)
          min3_app (existT (fun (n : nat) => chain s t n) (S n1) r1')
                   (existT _ (S n2) r2')
                   (existT _ (S n3) r3')
                   (fun p => projT1 p)
        end
    end) (eq_refl s) (eq_refl t).

Eval compute in (levenshtein_chain "Appel" "apple").
Eval compute in (projT1 (levenshtein_chain "Appel" "apple")).
Eval compute in (levenshtein_chain "pascal" "haskell").
Eval compute in (projT1 (levenshtein_chain "pascal" "haskell")).

Eval compute in (levenshtein_chain "ap" "ma").

Lemma chain_add_last_edit : forall s x xs n,
    chain s xs n -> chain s (xs ++ [x]) (S n).
intros s x xs n c.
induction c.
* simpl. eapply change. eapply insertion. apply same_chain.
* simpl. apply skip. auto.
* apply (change e IHc).
Defined.

Section TransparentLemmas.
Lemma plus_n_O' : forall n:nat, n = n + 0.
intros n. induction n.
* auto.
* simpl. rewrite <- IHn. auto.
Defined.

(* for some reason Coq still uses the opaque version in the defn *)
Lemma plus_n_Sm' : forall n m : nat, S (m + n) = m + S n.
intros n m. induction m.
* simpl. reflexivity.
* simpl. rewrite IHm. auto.
Defined.

Lemma app_empty_end' : forall s : string, s = s ++ "".
intros s. induction s.
* auto.
* simpl. f_equal. auto.
Defined.

Lemma rev_length_same : forall s, length (rev s) = length s.
intro s. induction s.
* simpl; reflexivity.
* simpl.
  rewrite length_app_last.
  rewrite IHs.
  reflexivity.
Defined.
End TransparentLemmas.

Fixpoint chain_append_end (s t u : string) : forall n,
    chain s t n -> chain s (t ++ u) (n + length u).
intros n c.
destruct u as [|x xs].
* rewrite <- plus_n_O'.
  rewrite <- app_empty_end'.
  auto.
* pose (c' := chain_add_last_edit s x t n c).
  pose (c'' := chain_append_end s (t ++ [x]) xs _ c').
  rewrite app_ass' in c''.
  simpl in *.
  assert ((S (n + length xs)) = (n + S (length xs))) as eq.
  rewrite plus_n_Sm'. auto.
  rewrite <- eq.
  auto.
Defined.

Eval compute in (chain_append_end "" "abc" "def" 3
                   (projT2 (levenshtein_chain "" "abc"))).
Eval compute in (levenshtein_chain "cd" "ce").
Eval compute in (levenshtein_chain "abcd" "ce").

Fixpoint chain_append_front' (s t u : string) {struct u} : forall n,
    chain s t n -> chain (rev u ++ s) t (length u + n).
intros n c.
induction u as [|x xs].
* simpl. auto.
* pose (c' := chain_append_front' (x :: s) t xs (S n) (change (deletion x) c)).
  simpl in *. rewrite app_ass. simpl.
  rewrite <- plus_n_Sm' in c'.
  auto.
Defined.

Definition chain_append_front (s t u : string) : forall n,
    chain s t n -> chain (u ++ s) t (length u + n).
intros n c.
pose (c' := chain_append_front' s t (rev u) n c).
rewrite rev_length_same in c'.
rewrite rev_involutive in c'.
auto.
Defined.

Lemma chain_trans : forall s t u n m,
    chain s t n -> chain t u m -> chain s u (n + m).
intros s t u n m c1 c2.
induction t.
* dependent induction c1; simpl.
  - auto.
  - apply (change e). apply IHc1; auto.
* dependent induction c2.
Abort.

Lemma chain_lengthen : forall s t m,
    chain "" s (length s) -> chain s t m -> chain "" t (length s + m).
intros s t m c1 c2.
induction s as [|x xs].
* auto.
* simpl in *.

Abort.

Lemma chain_without_last_insert : forall l x n,
    chain "" (l ++ [x]) (S n) -> chain "" l n.
intros l x n c.
Admitted.

Lemma chain_without_first_delete : forall l x n,
    chain (x :: l) "" (S n) -> chain l "" n.
intros l x n c.
Admitted.

Lemma non_empty_chain_length_is_not_zero : forall s t n,
    chain s t n -> s <> t -> {m : nat & n = S m}.
intros s t n c neq.
induction c.
* contradiction.
* apply IHc. congruence.
* exists n. reflexivity.
Defined.

Lemma inserts_chain_empty_min : forall s n (c : chain "" s n), length s <= n.
intros s n c.
refine (rev_ind (fun q => forall m (c' : chain "" q m), length q <= m)
                _ _ s n c).
* intuition.
* intros x l IH m c'.
  Search (_ ++ [_]).
  rewrite length_app_last.
  destruct (non_empty_chain_length_is_not_zero _ _ _ c') as [m' m_eq].
  induction l; simpl; intuition; discriminate.
  rewrite m_eq in *.
  pose (c'' := chain_without_last_insert _ _ _ c').
  pose (le := IH m' c'').
  omega.
Qed.

Lemma deletes_chain_empty_min : forall s n (c : chain s "" n), length s <= n.
intros s n c.
dependent induction s.
* intuition.
* simpl.
  destruct (non_empty_chain_length_is_not_zero _ _ _ c) as [m' m_eq].
  congruence.
  rewrite m_eq in *.
  pose (c' := chain_without_first_delete _ _ _ c).
  pose (le := IHs m' c').
  omega.
Qed.

Check projT1.
Lemma projT1_eq : forall {A : Type} {P P' : A -> Type} (x x' : A) (pf : P x) (pf' : P' x'),
    x = x' ->
    projT1 (existT _ x pf) = projT1 (existT _ x' pf').
intuition.
Defined.

Lemma levenshtein_chain_same_first_chars : forall x y s t,
    x = y ->
    projT1 (levenshtein_chain (x :: s) (y :: t)) = projT1 (levenshtein_chain s t).
intros x y s t eq.
simpl.
destruct (ascii_dec x y); try contradiction.
eapply (@projT1_eq
           nat
           (fun n0 : nat => chain (x :: s) (x :: t) n0)
           (fun n0 : nat => chain s t n0)
        ).
Admitted.


Fixpoint min_chain (s : string) :
  forall (t : string) (n : nat) (c : chain s t n),
    projT1 (levenshtein_chain s t) <= n.
Proof.
refine (fix min_chain1 (t : string) (n : nat) (c : chain s t n) := _).
destruct s as [|x xs] eqn:s_eq, t as [|y ys] eqn:t_eq.
* simpl. omega.
* apply inserts_chain_empty_min; auto.
* apply deletes_chain_empty_min; auto.
* simpl.
  destruct (ascii_dec x y) as [eq | neq].
  - pose (IH := min_chain (x :: xs) (y :: ys) n c).
    rewrite -> (levenshtein_chain_same_first_chars x y xs ys eq) in IH.
    destruct (levenshtein_chain xs ys) as [n' c'] eqn:c_eq.
    auto.
  -


Abort.
