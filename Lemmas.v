Require Import Coq.Init.Peano.

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

