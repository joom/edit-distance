(** * VST verification of [levenshtein_n]

    This file connects the generated CompCert Clight program to the verified
    dynamic-programming model.  The exported specification states that the C
    function [levenshtein_n] returns the intrinsic Levenshtein distance between
    the two byte arrays interpreted as strings. *)

From Stdlib Require Import List String ZArith.
From VST.floyd Require Import proofauto.
From VST.floyd Require Import library.

(** VST's [forward_while] prints advisory text when a following postcondition
    is known.  The proof intentionally keeps [forward_while] here because its
    generated obligations match the existing loop invariants, so silence that
    advisory hook for reproducible quiet builds. *)
Ltac forward_while_advise_loop ::= idtac.

Require Import EditDistance.levenshtein.
Require Import EditDistance.Levenshtein_recursive.
Require Import EditDistance.Levenshtein_dp.

#[export] Existing Instance NullExtension.Espec.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** CompCert composite specifications generated from the Clight program. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

(** VST global variable specifications generated from the Clight program. *)
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** The C implementation uses [size_t], represented by CompCert as
    unsigned 64-bit integers on the target model used by [levenshtein.v]. *)
Definition size_t := tulong.

(** Embed a mathematical integer into a CompCert [size_t] value.  All uses in
    the proof are accompanied by range obligations. *)
Definition Vsize_t (z : Z) : val :=
  Vlong (Int64.repr z).

(** Interpret VST byte arrays as Rocq strings by mapping each byte to the
    corresponding 8-bit [ascii] character. *)
Fixpoint bytes_to_string (s : list byte) : string :=
  match s with
  | nil => EmptyString
  | cons x xs =>
      String (Ascii.ascii_of_N (Z.to_N (Byte.unsigned x))) (bytes_to_string xs)
  end.

(** Interpreting bytes as a string preserves the list length. *)
Lemma bytes_to_string_length:
  forall s, String.length (bytes_to_string s) = length s.
Proof.
  induction s; simpl; auto.
Qed.

(** Convert a CompCert byte to the corresponding Rocq [ascii] character. *)
Definition byte_to_ascii (b : byte) : Ascii.ascii :=
  Ascii.ascii_of_N (Z.to_N (Byte.unsigned b)).

(** Byte/ascii conversion facts used when the C equality test on [char] values
    is reflected into the functional DP model. *)
Lemma list_ascii_of_string_bytes :
  forall s,
    list_ascii_of_string (bytes_to_string s) = map byte_to_ascii s.
Proof.
  induction s as [|x xs IH]; cbn; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(** Unsigned byte values are exactly in the 8-bit range. *)
Lemma byte_unsigned_range :
  forall b, 0 <= Byte.unsigned b < 256.
Proof.
  intros b. pose proof (Byte.unsigned_range b).
  change Byte.modulus with 256 in *. lia.
Qed.

(** Signed byte values are exactly in CompCert's signed-byte range. *)
Lemma byte_signed_range :
  forall b, Byte.min_signed <= Byte.signed b <= Byte.max_signed.
Proof.
  intros b. apply Byte.signed_range.
Qed.

(** Signed-byte interpretation is injective on CompCert bytes. *)
Lemma byte_signed_inj :
  forall b1 b2, Byte.signed b1 = Byte.signed b2 -> b1 = b2.
Proof.
  intros b1 b2 H.
  rewrite <- (Byte.repr_signed b1), <- (Byte.repr_signed b2), H.
  reflexivity.
Qed.

(** Equality of signed byte values after [Int.repr] implies byte equality. *)
Lemma int_repr_byte_signed_inj :
  forall b1 b2,
    Int.repr (Byte.signed b1) = Int.repr (Byte.signed b2) -> b1 = b2.
Proof.
  intros b1 b2 H.
  apply byte_signed_inj.
  pose proof (byte_signed_range b1) as Hb1.
  pose proof (byte_signed_range b2) as Hb2.
  change Byte.min_signed with (-128) in *.
  change Byte.max_signed with 127 in *.
  apply repr_inj_signed in H; auto;
  unfold repable_signed; change Int.min_signed with (-2147483648);
  change Int.max_signed with 2147483647; lia.
Qed.

(** Size and signedness facts needed to move between CompCert integers and
    mathematical integers. *)

Lemma byte_to_ascii_inj :
  forall b1 b2, byte_to_ascii b1 = byte_to_ascii b2 -> b1 = b2.
Proof.
  intros b1 b2 H.
  unfold byte_to_ascii in H.
  pose proof (byte_unsigned_range b1) as Hb1.
  pose proof (byte_unsigned_range b2) as Hb2.
  assert (HN1 : (Z.to_N (Byte.unsigned b1) < 256)%N).
  { change 256%N with (Z.to_N 256). apply Z2N.inj_lt; lia. }
  assert (HN2 : (Z.to_N (Byte.unsigned b2) < 256)%N).
  { change 256%N with (Z.to_N 256). apply Z2N.inj_lt; lia. }
  apply (f_equal Ascii.N_of_ascii) in H.
  rewrite !Ascii.N_ascii_embedding in H by assumption.
  assert (Hu : Byte.unsigned b1 = Byte.unsigned b2).
  { apply Z2N.inj; lia. }
  rewrite <- (Byte.repr_unsigned b1), <- (Byte.repr_unsigned b2), Hu.
  reflexivity.
Qed.

(** The recursive model on an empty left byte string returns the right length. *)
Lemma levenshtein_recursive_empty_bytes_l:
  forall b,
    Levenshtein.levenshtein_recursive (bytes_to_string nil) (bytes_to_string b) =
    length b.
Proof.
  intros b.
  simpl.
  rewrite Levenshtein.levenshtein_recursive_nil_l.
  apply bytes_to_string_length.
Qed.

(** The recursive model on an empty right byte string returns the left length. *)
Lemma levenshtein_recursive_empty_bytes_r:
  forall a,
    Levenshtein.levenshtein_recursive (bytes_to_string a) (bytes_to_string nil) =
    length a.
Proof.
  intros a.
  simpl.
  rewrite Levenshtein.levenshtein_recursive_nil_r.
  apply bytes_to_string_length.
Qed.

(** The recursive model gives distance zero from a string to itself. *)
Lemma levenshtein_recursive_same:
  forall s,
    Levenshtein.levenshtein_recursive s s = 0%nat.
Proof.
  induction s as [|x xs IH].
  - apply Levenshtein.levenshtein_recursive_nil_l.
  - rewrite Levenshtein.levenshtein_recursive_skip_eq.
    exact IH.
Qed.

(** A bounded integer represented as [Int64.zero] is mathematically zero. *)
Lemma Int64_repr_eq_zero:
  forall z, 0 <= z <= Int64.max_unsigned -> Int64.repr z = Int64.zero -> z = 0.
Proof.
  intros z Hz Hrepr.
  change Int64.zero with (Int64.repr 0) in Hrepr.
  eapply repr_inj_unsigned64; eauto; lia.
Qed.

(** The allocation-size bound implies the value itself fits in [size_t]. *)
Lemma size_t_array_bound:
  forall z, 0 <= z <= Int64.max_unsigned / sizeof tulong ->
    0 <= z <= Int64.max_unsigned.
Proof.
  intros z Hz.
  change (Int64.max_unsigned / sizeof tulong) with 2305843009213693951 in Hz.
  change Int64.max_unsigned with 18446744073709551615.
  lia.
Qed.

(** Name the hypotheses generated by [start_function] from
    [levenshtein_n_spec].  The proof below intentionally refers to these
    semantic names instead of fragile generated numeric names. *)
Ltac name_levenshtein_n_preconditions a_val b_val a b :=
  match goal with
  | H : readable_share _ |- _ => rename H into Hsh
  end;
  match goal with
  | H : isptr a_val |- _ => rename H into Ha_isptr
  end;
  match goal with
  | H : isptr b_val |- _ => rename H into Hb_isptr
  end;
  match goal with
  | H : a_val = b_val -> a = b |- _ => rename H into Hab_same_ptr
  end;
  match goal with
  | H : 0 <= Zlength a <= Int64.max_unsigned / sizeof tulong |- _ =>
      rename H into Ha_size_bound
  end;
  match goal with
  | H : 0 <= Zlength b <= Int64.max_unsigned / sizeof tulong |- _ =>
      rename H into Hb_size_bound
  end;
  match goal with
  | H : 0 <= Z.of_nat (Levenshtein.levenshtein_recursive _ _) <= Int64.max_unsigned |- _ =>
      rename H into Hdistance_size_bound
  end.

(** Solve arithmetic range goals showing that DP natural numbers fit in
    [size_t].  The proof bounds input lengths by [Int64.max_unsigned /
    sizeof tulong], and every DP cell is bounded by a sum of those lengths. *)
Ltac solve_size_t_nat_bound :=
  change Int64.max_unsigned with 18446744073709551615;
  change (Int64.max_unsigned / sizeof tulong) with 2305843009213693951 in *;
  lia.

(** Reflect a successful unsigned [size_t] comparison into a [Z] inequality. *)
Ltac apply_size_t_ltu_true Hlt :=
  apply ltu_repr64 in Hlt;
  [ lia
  | apply size_t_array_bound; lia
  | apply size_t_array_bound; lia ].

(** Reflect a failed unsigned [size_t] comparison into a [Z] inequality. *)
Ltac apply_size_t_ltu_false Hlt :=
  apply ltu_repr_false64 in Hlt;
  [ lia
  | apply size_t_array_bound; lia
  | apply size_t_array_bound; lia ].

(** Finish one successful outer-loop iteration after the inner cache-update
    loop has terminated.  Both outer-loop cases use the same proof: identify
    [i] with [Zlength a], connect [inner_steps] back to [inner_loop], unfold
    one step of [outer_cache] / [outer_result], and re-establish the continue
    invariant for [j + 1]. *)
Ltac finish_outer_continue a a_ascii b_ascii init Hinit_len Hlen_a_ascii Hla_eq
    i j prev b_j :=
  assert (Hi_done : i = Zlength a);
  [ match goal with
    | Htest : Int64.ltu (Int64.repr i) (Int64.repr (Zlength a)) = false |- _ =>
        apply_size_t_ltu_false Htest
    end
  | subst i;
    forward;
    Exists (j + 1);
    Exists (Vlong (Int64.repr (Z.of_nat
      (snd (inner_steps (Z.to_nat (Zlength a)) a_ascii b_j
             prev (Z.to_nat j) (Z.to_nat j))))));
    assert (Hjp1 : Z.to_nat (j + 1) = S (Z.to_nat j)) by lia;
    assert (Hprev_len : length prev = length a);
    [ subst prev;
      rewrite outer_cache_length;
      [ exact Hinit_len
      | rewrite Hlen_a_ascii, Hinit_len; reflexivity ]
    | assert (Hin_full :
        inner_steps (Z.to_nat (Zlength a)) a_ascii b_j
          prev (Z.to_nat j) (Z.to_nat j) =
        inner_loop a_ascii b_j prev (Z.to_nat j) (Z.to_nat j));
      [ rewrite Hla_eq, <- Hlen_a_ascii;
        apply inner_steps_full;
        rewrite Hlen_a_ascii, <- Hprev_len;
        reflexivity
      | assert (Houtc :
          outer_cache a_ascii b_ascii init (Z.to_nat (j + 1)) =
          fst (fst (inner_loop a_ascii b_j prev (Z.to_nat j) (Z.to_nat j))));
        [ rewrite Hjp1;
          cbn [outer_cache];
          subst prev b_j;
          unfold process_row;
          destruct (inner_loop a_ascii (nth (Z.to_nat j) b_ascii Ascii.zero)
                     (outer_cache a_ascii b_ascii init (Z.to_nat j))
                     (Z.to_nat j) (Z.to_nat j)) as [[c d] r] eqn:Hil;
          reflexivity
        | assert (Houtr :
            outer_result a_ascii b_ascii init (Z.to_nat (j + 1)) =
            snd (inner_loop a_ascii b_j prev (Z.to_nat j) (Z.to_nat j)));
          [ rewrite Hjp1;
            cbn [outer_result];
            subst prev b_j;
            unfold process_row;
            destruct (inner_loop a_ascii (nth (Z.to_nat j) b_ascii Ascii.zero)
                       (outer_cache a_ascii b_ascii init (Z.to_nat j))
                       (Z.to_nat j) (Z.to_nat j)) as [[c d] r] eqn:Hil;
            reflexivity
          | assert (Hskipn_nil : skipn (Z.to_nat (Zlength a)) prev = nil);
            [ apply List.skipn_all2; rewrite Hprev_len; lia
            | rewrite Hskipn_nil;
              rewrite app_nil_r;
              rewrite Hin_full;
              rewrite <- Houtc, <- Houtr;
              destruct (Z.eq_dec (j + 1) 0) as [Hz|Hnz]; [lia|];
              entailer! ] ] ] ] ] ].

(** [dp_min] preserves an upper bound shared by its three candidate cells. *)
Lemma dp_min_le_bound:
  forall (r d bd bound : nat),
    (r <= bound)%nat -> (d <= bound)%nat -> (bd <= bound)%nat ->
    (dp_min r d bd <= bound)%nat.
Proof.
  intros r d bd bound Hr Hd Hbd.
  unfold dp_min.
  destruct (Nat.ltb r d) eqn:Hrd.
  - apply Nat.ltb_lt in Hrd.
    destruct (Nat.ltb r bd) eqn:Hrb.
    + lia.
    + lia.
  - destruct (Nat.ltb d bd) eqn:Hdb.
    + apply Nat.ltb_lt in Hdb. lia.
    + lia.
Qed.

(** Bounds showing that the natural-number DP values fit in [size_t] under the
    allocation preconditions used by the C specification. *)
Lemma init_cache_bound:
  forall n, Forall (fun x => (x <= n)%nat) (init_cache n).
Proof.
  intros n.
  unfold init_cache.
  apply Forall_forall.
  intros x Hx.
  rewrite in_map_iff in Hx.
  destruct Hx as [y [Hy Hin]].
  subst x.
  apply in_seq in Hin.
  lia.
Qed.

(** Reading from a list that satisfies a pointwise bound preserves that bound. *)
Lemma Forall_le_nth:
  forall l bound i default,
    (default <= bound)%nat ->
    Forall (fun x => (x <= bound)%nat) l ->
    (nth i l default <= bound)%nat.
Proof.
  intros l bound i default Hdefault Hall.
  revert i.
  induction Hall as [|x xs Hx Hall IH]; intros i.
  - destruct i; exact Hdefault.
  - destruct i; simpl; auto.
Qed.

(** Weakens a pointwise natural-number bound over a list. *)
Lemma Forall_le_mono:
  forall l bound1 bound2,
    (bound1 <= bound2)%nat ->
    Forall (fun x => (x <= bound1)%nat) l ->
    Forall (fun x => (x <= bound2)%nat) l.
Proof.
  intros l bound1 bound2 Hle Hall.
  induction Hall.
  - constructor.
  - constructor; [lia | exact IHHall].
Qed.

(** Reading the head of [skipn k l] is the same as reading position [k] of
    [l].  VST cache updates use this to identify the value currently stored at
    [cache[i]]. *)
Lemma nth_skipn_default:
  forall {A : Type} (default : A) (l : list A) k,
    nth 0 (skipn k l) default = nth k l default.
Proof.
  intros A default l.
  induction l as [|x xs IH]; intros k.
  - destruct k; reflexivity.
  - destruct k; [reflexivity|].
    cbn. apply IH.
Qed.

(** Decompose [skipn k l] at a valid index into the current element and the
    remaining suffix. *)
Lemma skipn_cons_nth:
  forall {A : Type} (default : A) (l : list A) k,
    (k < length l)%nat ->
    skipn k l = nth k l default :: skipn (S k) l.
Proof.
  intros A default l.
  induction l as [|x xs IH]; intros k Hk.
  - cbn in Hk. lia.
  - destruct k as [|k].
    + reflexivity.
    + cbn. apply IH. cbn in Hk. lia.
Qed.

(** Updating a concatenated [prefix ++ skipn i l] at array index [i] appends
    the new value to [prefix] and advances the suffix.  This is the key list
    equation behind the inner-loop cache invariant. *)
Lemma upd_Znth_prefix_skipn:
  forall {A : Type} (default v : A) i prefix l,
    0 <= i ->
    length prefix = Z.to_nat i ->
    (Z.to_nat i < length l)%nat ->
    upd_Znth i (prefix ++ skipn (Z.to_nat i) l) v =
    (prefix ++ [v]) ++ skipn (S (Z.to_nat i)) l.
Proof.
  intros A default v i prefix l Hi Hprefix_len Hi_l.
  rewrite upd_Znth_app2.
  2:{
    rewrite !Zlength_correct, Hprefix_len, skipn_length.
    rewrite Nat2Z.inj_sub by lia.
    lia.
  }
  rewrite Zlength_correct, Hprefix_len.
  replace (i - Z.of_nat (Z.to_nat i)) with 0 by lia.
  rewrite (skipn_cons_nth default l (Z.to_nat i)) by exact Hi_l.
  rewrite upd_Znth0.
  rewrite <- app_assoc.
  reflexivity.
Qed.

(** Bounds for the step-indexed inner-loop model used in the VST invariant. *)
Lemma inner_steps_bound:
  forall n a_chars b_char old_cache distance result bound,
    Forall (fun x => (x <= bound)%nat) old_cache ->
    (distance <= bound)%nat ->
    (result <= bound)%nat ->
    (snd (fst (inner_steps n a_chars b_char old_cache distance result)) <= bound + n)%nat /\
    (snd (inner_steps n a_chars b_char old_cache distance result) <= bound + n)%nat /\
    Forall (fun x => (x <= bound + n)%nat)
      (fst (fst (inner_steps n a_chars b_char old_cache distance result))).
Proof.
  intros n.
  induction n as [|n IH]; intros a_chars b_char old_cache distance result bound Hall Hd Hr.
  - cbn. split; [lia|split; [lia|constructor]].
  - destruct a_chars as [|a0 a_rest].
    { cbn. split; [lia|split; [lia|constructor]]. }
    destruct old_cache as [|c0 c_rest].
    { cbn. split; [lia|split; [lia|constructor]]. }
    inversion Hall as [|? ? Hc0 Hcrest]; subst.
    cbn [inner_steps].
    set (bd := if Ascii.ascii_dec b_char a0 then distance else S distance).
    assert (Hbd : (bd <= S bound)%nat).
    { subst bd. destruct (Ascii.ascii_dec b_char a0); lia. }
    assert (Hnew : (dp_min result c0 bd <= S bound)%nat).
    { apply dp_min_le_bound; lia. }
    specialize (IH a_rest b_char c_rest c0 (dp_min result c0 bd) (S bound)).
    destruct IH as [Hd' [Hr' Hpfx]].
    { eapply Forall_le_mono; [|exact Hcrest]. lia. }
    { lia. }
    { exact Hnew. }
	    destruct (inner_steps n a_rest b_char c_rest c0 (dp_min result c0 bd))
	      as [[pfx d] r].
	    cbn in *.
	    repeat split; try lia.
	    constructor; [lia|].
	    eapply Forall_le_mono; [|exact Hpfx]. lia.
Qed.

(** Tighter bounds for a complete inner-loop row update. *)
Lemma inner_loop_bound_tight:
  forall a_chars b_char old_cache distance result bound,
    Forall (fun x => (x < bound)%nat) old_cache ->
    (distance < bound)%nat ->
    (result <= bound)%nat ->
    let '(cache, d, r) := inner_loop a_chars b_char old_cache distance result in
    Forall (fun x => (x <= bound)%nat) cache /\ (d < bound)%nat /\ (r <= bound)%nat.
Proof.
  intros a_chars.
  induction a_chars as [|a0 a_rest IH];
    intros b_char old_cache distance result bound Hall Hd Hr.
  - cbn. repeat split; auto; constructor.
  - destruct old_cache as [|c0 c_rest].
    + cbn. repeat split; auto; constructor.
    + inversion Hall as [|? ? Hc0 Hcrest]; subst.
      cbn [inner_loop].
      set (bd := if Ascii.ascii_dec b_char a0 then distance else S distance).
      assert (Hbd : (bd <= bound)%nat).
      { subst bd. destruct (Ascii.ascii_dec b_char a0); lia. }
      assert (Hnew : (dp_min result c0 bd <= bound)%nat).
      { apply dp_min_le_bound; lia. }
      specialize (IH b_char c_rest c0 (dp_min result c0 bd) bound Hcrest Hc0 Hnew).
	      destruct (inner_loop a_rest b_char c_rest c0 (dp_min result c0 bd))
	        as [[cache d] r].
	      cbn in IH |- *.
	      destruct IH as [Hcache [Hd' Hr']].
	      split.
	      { constructor; auto. }
	      split; auto.
Qed.

(** Bounds for the cache and result after [k] outer-loop iterations. *)
Lemma outer_cache_result_bound:
  forall k a_chars b_chars init,
    length init = length a_chars ->
    Forall (fun x => (x <= length a_chars)%nat) init ->
    Forall (fun x => (x <= length a_chars + k)%nat)
      (outer_cache a_chars b_chars init k) /\
    (outer_result a_chars b_chars init k <= length a_chars + k)%nat.
Proof.
  intros k.
  induction k as [|k IH]; intros a_chars b_chars init Hlen_init Hinit.
  - cbn [outer_cache outer_result].
    split; [eapply Forall_le_mono; [|exact Hinit]; lia|lia].
  - cbn [outer_cache outer_result].
    destruct (IH a_chars b_chars init Hlen_init Hinit) as [Hcache _].
    unfold process_row.
    pose proof (inner_loop_bound_tight a_chars
                  (nth k b_chars Ascii.zero)
                  (outer_cache a_chars b_chars init k) k k
                  (length a_chars + S k)) as Hbound.
    assert (Hcache' : Forall (fun x => (x < length a_chars + S k)%nat)
                       (outer_cache a_chars b_chars init k)).
    { apply Forall_forall.
      intros x Hinx.
      apply Forall_forall with (x := x) in Hcache; [lia|exact Hinx]. }
    specialize (Hbound Hcache' ltac:(lia) ltac:(lia)).
    destruct (inner_loop a_chars (nth k b_chars Ascii.zero)
                (outer_cache a_chars b_chars init k) k k)
      as [[cache' d] r].
    cbn in Hbound.
    destruct Hbound as [Hcache_out [_ Hr]].
    split; auto.
Qed.

(** Separation-logic predicate for a concrete C byte array. *)
Definition byte_array_at (sh : share) (contents : list byte) (p : val) : mpred :=
  data_at sh (tarray tschar (Zlength contents)) (map Vbyte contents) p.

(** Separation-logic predicate for a concrete unsigned-long cache array. *)
Definition ulong_array_at (contents : list Z) (p : val) : mpred :=
  data_at Ews (tarray tulong (Zlength contents))
    (map (fun z => Vlong (Int64.repr z)) contents) p.

(** Converts natural-number cache contents into [size_t] values. *)
Definition Vsize_t_list (contents : list nat) : list val :=
  map (fun n => Vsize_t (Z.of_nat n)) contents.

(** Initial cache values as VST values.  The C loop initializes cache cell
    [i] with [i + 1]. *)
Definition full_init_cache (n : Z) : list val :=
  Vsize_t_list (init_cache (Z.to_nat n)).

(** Partially initialized cache: initialized prefix followed by undefined
    cells not yet written by the first C loop. *)
Definition init_cache_prefix (i n : Z) : list val :=
  sublist 0 i (full_init_cache n) ++ repeat Vundef (Z.to_nat (n - i)).

(** Facts about the partially initialized cache used by the first C loop. *)
Lemma Zlength_full_init_cache:
  forall n, 0 <= n -> Zlength (full_init_cache n) = n.
Proof.
  intros n Hn.
  unfold full_init_cache, Vsize_t_list, init_cache.
  rewrite Zlength_map, Zlength_map, Zlength_correct, length_seq.
  lia.
Qed.

(** The partially initialized cache always has the full allocation length. *)
Lemma init_cache_prefix_length:
  forall i n, 0 <= i <= n -> Zlength (init_cache_prefix i n) = n.
Proof.
  intros i n Hi.
  unfold init_cache_prefix.
  rewrite Zlength_app.
  rewrite (Zlength_sublist 0 i (full_init_cache n)).
  2:{ lia. }
  2:{ rewrite Zlength_full_init_cache; lia. }
  rewrite Zlength_repeat.
  2:{ lia. }
  lia.
Qed.

(** Before the initialization loop, the whole cache view is undefined. *)
Lemma init_cache_prefix_zero:
  forall n, 0 <= n -> init_cache_prefix 0 n = Zrepeat Vundef n.
Proof.
  intros n Hn.
  unfold init_cache_prefix.
  rewrite sublist_nil by (rewrite Zlength_full_init_cache; lia).
  rewrite Z.sub_0_r.
  unfold Zrepeat.
  reflexivity.
Qed.

(** The fully initialized cache stores [i + 1] at index [i]. *)
Lemma Znth_full_init_cache:
  forall i n,
    0 <= i < n ->
    Znth i (full_init_cache n) = Vsize_t (i + 1).
Proof.
  intros i n Hi.
  unfold full_init_cache, Vsize_t_list, init_cache.
  rewrite !Znth_map by
    (rewrite Zlength_map, Zlength_correct, length_seq; lia).
  rewrite Znth_map by (rewrite Zlength_correct, length_seq; lia).
  rewrite <- nth_Znth by (rewrite Zlength_correct, length_seq; lia).
  rewrite seq_nth by lia.
  replace (Z.of_nat (S (0 + Z.to_nat i))) with (i + 1) by lia.
  reflexivity.
Qed.

(** One initialization step writes the next initialized cache cell. *)
Lemma init_cache_prefix_step:
  forall i n,
    0 <= i < n ->
    upd_Znth i (init_cache_prefix i n) (Vsize_t (i + 1)) =
    init_cache_prefix (i + 1) n.
Proof.
  intros i n Hi.
  unfold init_cache_prefix.
  rewrite upd_init.
  2:{ lia. }
  2:{ rewrite Zlength_sublist; [lia | lia | rewrite Zlength_full_init_cache; lia]. }
  rewrite sublist_last_1.
  2:{ lia. }
  2:{ rewrite Zlength_full_init_cache; lia. }
  rewrite Znth_full_init_cache by lia.
  rewrite <- app_assoc.
  reflexivity.
Qed.

(** After all initialization steps, the prefix view is the full initialized cache. *)
Lemma init_cache_prefix_full:
  forall n,
    0 <= n ->
    init_cache_prefix n n = full_init_cache n.
Proof.
  intros n Hn.
  unfold init_cache_prefix.
  rewrite (sublist_same 0 n (full_init_cache n)) by
    (try reflexivity; rewrite Zlength_full_init_cache; lia).
  replace (n - n) with 0 by lia.
  rewrite repeat_0.
  rewrite app_nil_r.
  reflexivity.
Qed.

(** VST specification for the external [calloc] used by the C implementation. *)
Definition calloc_spec :=
 DECLARE _calloc
  WITH n : Z, gv : globals
  PRE [ size_t, size_t ]
    PROP (0 < n;
          n <= Int64.max_unsigned;
          n * sizeof tulong <= Ptrofs.max_unsigned)
    PARAMS (Vsize_t n; Vsize_t (sizeof tulong)) GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [ tptr tvoid ] EX p : val,
    PROP (p <> nullval)
    RETURN (p)
    SEP (mem_mgr gv;
         malloc_token Ews (tarray tulong n) p;
         data_at_ Ews (tarray tulong n) p).

(** Public VST specification for [levenshtein_n].  The precondition gives
    readable input arrays and size bounds; the postcondition returns the
    verified intrinsic distance. *)
Definition levenshtein_n_spec :=
 DECLARE _levenshtein_n
  WITH gv: globals, sh: share, a : list byte, a_val: val, b : list byte, b_val: val
  PRE [ tptr tschar, size_t, tptr tschar, size_t ]
    PROP (readable_share sh;
          isptr a_val;
          isptr b_val;
          a_val = b_val -> a = b;
          0 <= Zlength a <= Int64.max_unsigned / sizeof tulong;
          0 <= Zlength b <= Int64.max_unsigned / sizeof tulong;
          0 <= Z.of_nat (Levenshtein.levenshtein_recursive
                            (bytes_to_string a) (bytes_to_string b))
             <= Int64.max_unsigned)
    PARAMS (a_val; Vsize_t (Zlength a); b_val; Vsize_t (Zlength b))
    GLOBALS (gv)
    SEP (mem_mgr gv;
         (byte_array_at sh a a_val && valid_pointer a_val);
         (byte_array_at sh b b_val && valid_pointer b_val))
  POST [ size_t ]
    PROP ()
    RETURN
      (Vsize_t (Z.of_nat
        (Levenshtein.levenshtein_recursive
           (bytes_to_string a) (bytes_to_string b))))
    SEP (mem_mgr gv; byte_array_at sh a a_val; byte_array_at sh b b_val).

(** Function-specification environment used by the body proof. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog (List.cons calloc_spec (List.cons levenshtein_n_spec nil))).

(** The DP model on bytes agrees with the intrinsic string model, giving the
    mathematical postcondition used by the C proof. *)
Theorem levenshtein_n_dp_model_eq_intrinsic :
  forall a b,
    levenshtein_dp (bytes_to_string a) (bytes_to_string b) =
    Levenshtein.levenshtein_recursive (bytes_to_string a) (bytes_to_string b).
Proof.
  intros a b.
  apply levenshtein_dp_eq_levenshtein_recursive.
Qed.

(** Main proof obligation for the generated Clight body. *)
(** Named body-verification proposition for [levenshtein_n]. *)
Definition levenshtein_n_body_obligation : Prop :=
  semax_body Vprog Gprog f_levenshtein_n levenshtein_n_spec.

(** VST proof that the generated Clight body satisfies [levenshtein_n_spec]. *)
Lemma body_levenshtein_n: semax_body Vprog Gprog f_levenshtein_n levenshtein_n_spec.
Proof.
  start_function.
  name_levenshtein_n_preconditions a_val b_val a b.
  forward. (* index = 0 *)
  forward. (* bIndex = 0 *)
  forward_if
    (PROP (readable_share sh;
           isptr a_val;
           isptr b_val;
           a_val = b_val -> a = b;
           0 <= Zlength a <= Int64.max_unsigned / sizeof tulong;
           0 <= Zlength b <= Int64.max_unsigned / sizeof tulong;
           0 <= Z.of_nat (Levenshtein.levenshtein_recursive
                             (bytes_to_string a) (bytes_to_string b))
              <= Int64.max_unsigned)
     LOCAL (temp _bIndex (Vsize_t 0);
            temp _index (Vsize_t 0);
            gvars gv;
            temp _a a_val;
            temp _length (Vsize_t (Zlength a));
            temp _b b_val;
            temp _bLength (Vsize_t (Zlength b)))
     SEP (mem_mgr gv; byte_array_at sh a a_val; byte_array_at sh b b_val)).
  - forward_return.
    entailer!;
      try (specialize (Hab_same_ptr eq_refl);
           subst b;
           unfold Vsize_t;
           rewrite levenshtein_recursive_same;
           reflexivity);
      try (change (((byte_array_at sh a b_val && valid_pointer b_val) *
                    (byte_array_at sh b b_val && valid_pointer b_val))%logic
                    |-- (byte_array_at sh a b_val * byte_array_at sh b b_val)%logic);
           apply sepcon_derives; apply andp_left1; apply derives_refl).
  - forward.
    entailer!;
      try (change (((byte_array_at sh a a_val && valid_pointer a_val) *
                    (byte_array_at sh b b_val && valid_pointer b_val))%logic
                    |-- (byte_array_at sh a a_val * byte_array_at sh b b_val)%logic);
           apply sepcon_derives; apply andp_left1; apply derives_refl).
  - forward_if; try entailer!.
    + forward.
	      entailer!.
	      f_equal. f_equal.
    assert (Za0: Zlength a = 0).
    {
      match goal with
      | Hzero: Int64.repr (Zlength a) = Int64.zero |- _ =>
          apply Int64_repr_eq_zero;
          [apply size_t_array_bound; exact Ha_size_bound | exact Hzero]
      end.
    }
    apply Zlength_nil_inv in Za0.
    subst a.
    rewrite levenshtein_recursive_empty_bytes_l.
    rewrite Zlength_correct.
    reflexivity.
    + forward_if; try entailer!.
      * forward.
	        entailer!.
	        f_equal. f_equal.
	      assert (Zb0: Zlength b = 0).
	      {
	        match goal with
	        | Hzero: Int64.repr (Zlength b) = Int64.zero |- _ =>
	            apply Int64_repr_eq_zero;
              [apply size_t_array_bound; exact Hb_size_bound | exact Hzero]
	        end.
	      }
      apply Zlength_nil_inv in Zb0.
      subst b.
      rewrite levenshtein_recursive_empty_bytes_r.
      rewrite Zlength_correct.
      reflexivity.
      * forward_call (Zlength a, gv).
        { split3.
           ++ assert (Zlength a <> 0).
           {
             intro Hz.
             match goal with
             | Hnz: Int64.repr (Zlength a) <> Int64.repr 0 |- _ =>
                 rewrite Hz in Hnz; apply Hnz; reflexivity
             end.
           }
           lia.
           ++ apply size_t_array_bound; exact Ha_size_bound.
           ++ change (sizeof tulong) with 8.
           change Ptrofs.max_unsigned with 18446744073709551615.
           change (Int64.max_unsigned / sizeof tulong) with 2305843009213693951 in Ha_size_bound.
           lia. }
        Intros cache.
        forward_while
          (EX i : Z,
            PROP (0 <= i <= Zlength a)
            LOCAL (temp _cache cache;
                   temp _bIndex (Vlong (Int64.repr 0));
                   temp _index (Vlong (Int64.repr i));
                   gvars gv;
                   temp _a a_val;
                   temp _length (Vsize_t (Zlength a));
                   temp _b b_val;
                   temp _bLength (Vsize_t (Zlength b)))
            SEP (mem_mgr gv;
                 malloc_token Ews (tarray tulong (Zlength a)) cache;
                 data_at Ews (tarray tulong (Zlength a))
                   (init_cache_prefix i (Zlength a)) cache;
                 byte_array_at sh a a_val;
                 byte_array_at sh b b_val)).
        -- Exists 0.
           entailer!.
           rewrite data_at__tarray.
           rewrite init_cache_prefix_zero by lia.
           entailer!.
        -- entailer!.
        -- assert (Hi_lt: 0 <= i < Zlength a).
           {
             match goal with
             | Hlt: Int64.ltu (Int64.repr i) (Int64.repr (Zlength a)) = true |- _ =>
                 apply_size_t_ltu_true Hlt
             end.
           }
           forward.
           change (Int.signed (Int.repr 1)) with 1.
           rewrite add64_repr.
           change (Vlong (Int64.repr (i + 1))) with (Vsize_t (i + 1)).
           rewrite (init_cache_prefix_step i (Zlength a)) by exact Hi_lt.
           forward.
           Exists (i + 1).
           entailer!.
        -- (* After init loop exits: i = Zlength a *)
           assert (Hi_eq : i = Zlength a).
           {
             match goal with
             | H : Int64.ltu (Int64.repr i) (Int64.repr (Zlength a)) = false |- _ =>
                 apply_size_t_ltu_false H
             end.
           }
           subst i.
           rewrite init_cache_prefix_full by lia.
           (* Define helpful abbreviations. *)
           set (a_ascii := map byte_to_ascii a).
           set (b_ascii := map byte_to_ascii b).
           set (init := init_cache (Z.to_nat (Zlength a))).
           assert (Zlength_full_init :
                     Zlength (full_init_cache (Zlength a)) = Zlength a)
             by (apply Zlength_full_init_cache; lia).
           assert (Hla_eq : Z.to_nat (Zlength a) = length a)
             by (rewrite Zlength_correct; lia).
           assert (Hlb_eq : Z.to_nat (Zlength b) = length b)
             by (rewrite Zlength_correct; lia).
           assert (Hlen_a_ascii : length a_ascii = length a)
             by (subst a_ascii; apply length_map).
           assert (Hlen_b_ascii : length b_ascii = length b)
             by (subst b_ascii; apply length_map).
           assert (Hinit_len : length init = length a)
             by (subst init; unfold init_cache;
                 rewrite length_map, length_seq; lia).
           assert (Hinit_bound : Forall (fun x => (x <= length a_ascii)%nat) init).
           { subst init. rewrite Hla_eq, <- Hlen_a_ascii. apply init_cache_bound. }
           (* Bridge: full_init_cache (Zlength a) as Vsize_t_list init. *)
           assert (Hfull_init :
             full_init_cache (Zlength a) = Vsize_t_list init).
           { subst init. unfold full_init_cache. reflexivity. }
           rewrite Hfull_init.
           assert (Hla_pos : 0 < Zlength a).
           {
             match goal with
             | H : Int64.repr (Zlength a) <> Int64.repr 0 |- _ =>
                 destruct (Z.eq_dec (Zlength a) 0) as [Hz|Hnz]; [
                   exfalso; apply H; rewrite Hz; reflexivity
                 | pose proof (Zlength_nonneg a); lia
                 ]
             end.
           }
           assert (Hlb_pos : 0 < Zlength b).
           {
             match goal with
             | H : Int64.repr (Zlength b) <> Int64.repr 0 |- _ =>
                 destruct (Z.eq_dec (Zlength b) 0) as [Hz|Hnz]; [
                   exfalso; apply H; rewrite Hz; reflexivity
                 | pose proof (Zlength_nonneg b); lia
                 ]
             end.
           }
           assert (Ha_ne : a_ascii <> []).
           {
             subst a_ascii.
             destruct a as [|x xs]; [rewrite Zlength_nil in Hla_pos; lia|].
             simpl. discriminate.
           }
           assert (Hb_ne : b_ascii <> []).
           {
             subst b_ascii.
             destruct b as [|x xs]; [rewrite Zlength_nil in Hlb_pos; lia|].
             simpl. discriminate.
           }
           (* OUTER LOOP *)
           (* We initialize _result before the loop with the value it would
              get on the FIRST iteration's "result = bIndex" assignment. The
              C source does not contain this initialization; we treat it
              logically by using forward_loop with a precondition that includes
              temp _result Vundef.  But VST disallows Vundef temps, so we
              instead use forward_loop in a form that does not require
              _result to be defined initially.  This is achieved by NOT
              including temp _result in the initial invariant; we'll insert
              it during the body via assert_PROP after the assignment. *)
           forward_loop
             (EX j : Z, EX result_v : val,
               PROPx
                 [0 <= j <= Zlength b;
                  j > 0 ->
                    result_v = Vsize_t (Z.of_nat
                      (outer_result a_ascii b_ascii init (Z.to_nat j)))]
                 (LOCALx
                   (temp _cache cache ::
                    temp _bIndex (Vsize_t j) ::
                    temp _index (Vsize_t (Zlength a)) ::
                    gvars gv ::
                    temp _a a_val ::
                    temp _length (Vsize_t (Zlength a)) ::
                    temp _b b_val ::
                    temp _bLength (Vsize_t (Zlength b)) ::
                    (if Z.eq_dec j 0 then nil
                     else [temp _result result_v]))
                   (SEPx [
                     mem_mgr gv;
                     malloc_token Ews (tarray tulong (Zlength a)) cache;
                     data_at Ews (tarray tulong (Zlength a))
                       (Vsize_t_list
                         (outer_cache a_ascii b_ascii init (Z.to_nat j))) cache;
                     byte_array_at sh a a_val;
                     byte_array_at sh b b_val
                   ])))
             break:
             (PROP ()
              LOCAL (
                temp _cache cache;
                temp _result (Vsize_t (Z.of_nat
                  (outer_result a_ascii b_ascii init (length b))));
                gvars gv;
                temp _a a_val;
                temp _length (Vsize_t (Zlength a));
                temp _b b_val;
                temp _bLength (Vsize_t (Zlength b))
              )
             SEP (
                mem_mgr gv;
                malloc_token Ews (tarray tulong (Zlength a)) cache;
                data_at Ews (tarray tulong (Zlength a))
                  (Vsize_t_list
                    (outer_cache a_ascii b_ascii init (length b))) cache;
                byte_array_at sh a a_val;
                byte_array_at sh b b_val
             )).
           { (* Initial entailment: j = 0, result_v unused (since j=0) *)
             Exists 0 Vundef.
             change (Z.to_nat 0) with 0%nat.
             cbn [outer_cache].
             destruct (Z.eq_dec 0 0) as [_|Hne]; [|congruence].
             entailer!.
           }
           { (* Loop body: from Inv, execute body (with test as if-break). *)
             Intros j result_v.
             destruct (Z.eq_dec j 0) as [Hj0|Hj_pos].
             - (* j = 0 case *)
               replace (if Z.eq_dec j 0 then nil else [temp _result result_v])
                  with (@nil localdef)
                  by (destruct (Z.eq_dec j 0); [reflexivity|contradiction]).
               forward_if.
               + (* body continue: j < Zlength b *)
                 assert (Hj_lt : 0 <= j < Zlength b).
                 { match goal with
                   | H : Int64.ltu _ _ = true |- _ =>
                       apply_size_t_ltu_true H
                   end. }
	                 unfold byte_array_at, Vsize_t.
	                 unfold Vsize_t_list.
	                 Intros.
	                 normalize.
	                 forward.  (* _t'3 = b[j] *)
                 forward.  (* _code = _t'3 *)
                 forward.  (* _distance = _bIndex *)
                 forward.  (* _result = _bIndex *)
                 forward.  (* _bIndex = _bIndex + 1 *)
                 forward.  (* _index = 0 *)
                 (* Inner loop. Let `prev` be the cache at the start of the
                    j-th outer iteration, and `b_j` the j-th ascii char. *)
                 set (prev := outer_cache a_ascii b_ascii init (Z.to_nat j)).
                 set (b_j := nth (Z.to_nat j) b_ascii Ascii.zero).
                 forward_while
                   (EX i : Z,
                     PROP (0 <= i <= Zlength a)
                     LOCAL (
                       temp _index (Vlong (Int64.repr i));
                       temp _bIndex (Vlong (Int64.repr (j + 1)));
                       temp _result (Vlong (Int64.repr
                         (Z.of_nat (snd (inner_steps (Z.to_nat i) a_ascii b_j
                                          prev (Z.to_nat j) (Z.to_nat j))))));
                       temp _distance (Vlong (Int64.repr
                         (Z.of_nat (snd (fst (inner_steps (Z.to_nat i) a_ascii b_j
                                               prev (Z.to_nat j) (Z.to_nat j)))))));
                       temp _code (Vint (Int.repr (Byte.signed (Znth j b))));
                       temp _cache cache;
                       gvars gv;
                       temp _a a_val;
                       temp _length (Vlong (Int64.repr (Zlength a)));
                       temp _b b_val;
                       temp _bLength (Vlong (Int64.repr (Zlength b)))
                     )
                     SEP (
                       mem_mgr gv;
                       malloc_token Ews (tarray tulong (Zlength a)) cache;
                       data_at Ews (tarray tulong (Zlength a))
                         (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                           (fst (fst (inner_steps (Z.to_nat i) a_ascii b_j
                                       prev (Z.to_nat j) (Z.to_nat j)))
                            ++ skipn (Z.to_nat i) prev))
                         cache;
                       data_at sh (tarray tschar (Zlength a))
                         (map Vbyte a) a_val;
                       data_at sh (tarray tschar (Zlength b))
                         (map Vbyte b) b_val
                     )).
                 { (* Initial entailment: i = 0 *)
                   Exists 0.
                   change (Z.to_nat 0) with 0%nat.
                   cbn [inner_steps fst snd app skipn].
                   replace (Z.of_nat (Z.to_nat j)) with j by lia.
                   change (Int.signed (Int.repr 1)) with 1.
                   change (Int.signed (Int.repr 0)) with 0.
                   rewrite add64_repr.
                   entailer!.
                 }
                 { (* Typecheck of test *)
                   entailer!.
                 }
                 { (* Inner body *)
                   assert (Hi_lt : 0 <= i < Zlength a).
                   { match goal with
                     | H : Int64.ltu _ _ = true |- _ =>
                         apply_size_t_ltu_true H
                     end. }
                   forward.  (* _t'2 = a[i] *)
                   (* Abbreviations. *)
                   set (d_i := snd (fst (inner_steps (Z.to_nat i) a_ascii b_j
                                          prev (Z.to_nat j) (Z.to_nat j)))).
                   set (r_i := snd (inner_steps (Z.to_nat i) a_ascii b_j
                                     prev (Z.to_nat j) (Z.to_nat j))).
                   set (a_i := nth (Z.to_nat i) a_ascii Ascii.zero).
                   set (bdist := if Ascii.ascii_dec b_j a_i then d_i else S d_i).
                   forward_if
                     (PROP ()
                      LOCAL (
                        temp _bDistance (Vlong (Int64.repr (Z.of_nat bdist)));
                        temp _t'2 (Vbyte (Znth i a));
                        temp _index (Vlong (Int64.repr i));
                        temp _bIndex (Vlong (Int64.repr (j + 1)));
                        temp _result (Vlong (Int64.repr (Z.of_nat r_i)));
                        temp _distance (Vlong (Int64.repr (Z.of_nat d_i)));
                        temp _code (Vint (Int.repr (Byte.signed (Znth j b))));
                        temp _cache cache;
                        gvars gv;
                        temp _a a_val;
                        temp _length (Vlong (Int64.repr (Zlength a)));
                        temp _b b_val;
                        temp _bLength (Vlong (Int64.repr (Zlength b)))
                      )
                      SEP (
                        mem_mgr gv;
                        malloc_token Ews (tarray tulong (Zlength a)) cache;
                        data_at Ews (tarray tulong (Zlength a))
                          (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                            (fst (fst (inner_steps (Z.to_nat i) a_ascii b_j
                                        prev (Z.to_nat j) (Z.to_nat j)))
                             ++ skipn (Z.to_nat i) prev))
                          cache;
                        data_at sh (tarray tschar (Zlength a))
                          (map Vbyte a) a_val;
                        data_at sh (tarray tschar (Zlength b))
                          (map Vbyte b) b_val
                      )).
                   { (* True branch: bytes equal *)
                     forward.
                     entailer!.
                     unfold bdist.
                     destruct (Ascii.ascii_dec b_j a_i) as [_|Hne].
                     - reflexivity.
                     - exfalso. apply Hne.
                       subst b_j a_i.
                       match goal with
                       | H : Znth ?jb b = Znth i a |- _ =>
                           set (jb0 := jb) in *; rename H into Hba
                       end.
                       assert (Hlmb : length (map byte_to_ascii b) = length b)
                         by apply length_map.
                       assert (Hlma : length (map byte_to_ascii a) = length a)
                         by apply length_map.
                       rewrite (nth_indep _ Ascii.zero (byte_to_ascii Byte.zero))
                         by lia.
                       rewrite (nth_indep (map byte_to_ascii a) Ascii.zero
                                   (byte_to_ascii Byte.zero)) by lia.
                       unfold Znth in Hba.
                       destruct (Z_lt_dec jb0 0); [lia|].
                       destruct (Z_lt_dec i 0); [lia|].
                       unfold b_ascii, a_ascii.
                       change Ascii.zero with (byte_to_ascii Byte.zero).
                       rewrite !map_nth.
                       f_equal.
                       exact Hba.
                   }
                   { (* False branch: bytes differ *)
                     forward.
                     entailer!.
                     unfold bdist.
                     destruct (Ascii.ascii_dec b_j a_i) as [Heq|_].
                     - exfalso.
                       subst b_j a_i.
                       (* From Heq: nth k b_ascii Ascii.zero = nth k' a_ascii Ascii.zero *)
                       unfold b_ascii, a_ascii in Heq.
                       change Ascii.zero with (byte_to_ascii Byte.zero) in Heq.
                       rewrite !map_nth in Heq.
                       apply byte_to_ascii_inj in Heq.
                       (* Heq : nth (Z.to_nat j) b Byte.zero = nth (Z.to_nat i) a Byte.zero *)
                       (* The hypothesis from forward_if false branch says Znth j b <> Znth i a. *)
                       match goal with
                       | H : Znth ?jb b <> Znth i a |- _ =>
                           set (jb0 := jb) in *;
                           apply H;
                           unfold Znth;
                           destruct (Z_lt_dec jb0 0); [lia|];
                           destruct (Z_lt_dec i 0); [lia|];
                           exact Heq
                       end.
                     - cbn. f_equal. f_equal. lia.
                   }
                   (* Set up the cache view as the concatenated prefix + suffix. *)
                   set (prefix_i := fst (fst (inner_steps (Z.to_nat i) a_ascii b_j
                                              prev (Z.to_nat j) (Z.to_nat j)))).
                   set (c_i := nth (Z.to_nat i) prev 0%nat).
                   (* length facts *)
                   assert (Hprev_len : length prev = length a).
                   { subst prev. rewrite outer_cache_length;
                     [exact Hinit_len|
                      rewrite Hlen_a_ascii, Hinit_len; reflexivity]. }
                   assert (Hprefix_len : length prefix_i = Z.to_nat i).
                   { subst prefix_i. apply inner_steps_length; lia. }
                   assert (Hskipn_len : (length (skipn (Z.to_nat i) prev) =
                                        length a - Z.to_nat i)%nat).
                   { rewrite skipn_length, Hprev_len. reflexivity. }
                   assert (Hcache_zlen :
                     Zlength (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                              (prefix_i ++ skipn (Z.to_nat i) prev)) = Zlength a).
                   { rewrite Zlength_map, Zlength_app, !Zlength_correct.
                     rewrite Hprefix_len, Hskipn_len.
                     rewrite Nat2Z.inj_sub by lia.
                     rewrite <- Hla_eq, Z2Nat.id by lia.
                     lia. }
                   assert (Hpfx_skipn_zlen :
                     Zlength (prefix_i ++ skipn (Z.to_nat i) prev) = Zlength a).
                   { rewrite Zlength_app, !Zlength_correct.
                     rewrite Hprefix_len, Hskipn_len.
                     rewrite Nat2Z.inj_sub by lia.
                     rewrite <- Hla_eq, Z2Nat.id by lia.
                     lia. }
                   (* Znth i (map ... (prefix ++ skipn i prev)) = c_i (as Vlong). *)
                   assert (Hcache_at_i :
                     Znth i (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                              (prefix_i ++ skipn (Z.to_nat i) prev))
                     = Vlong (Int64.repr (Z.of_nat c_i))).
                   { rewrite Znth_map by lia.
                     unfold Znth.
                     destruct (Z_lt_dec i 0); [lia|].
                     rewrite app_nth2 by lia.
                     rewrite Hprefix_len.
                     replace (Z.to_nat i - Z.to_nat i)%nat with 0%nat by lia.
                     f_equal. f_equal.
                     subst c_i.
                     rewrite <- (nth_skipn_default 0%nat prev (Z.to_nat i)).
                     reflexivity. }
                   forward.  (* _distance = cache[i] *)
                   { entailer!. rewrite Znth_map by lia. apply I. }
                   replace (Znth i (map
                     (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                     (prefix_i ++ skipn (Z.to_nat i) prev)))
                     with (Vlong (Int64.repr (Z.of_nat c_i)))
                     by (symmetry; exact Hcache_at_i).
                   (* The 4 branches of the nested ifs all compute dp_min r_i c_i bdist. *)
                   set (new_r := dp_min r_i c_i bdist).
                   assert (Hprev_bound :
                     Forall (fun x => (x <= length a_ascii + Z.to_nat j)%nat) prev).
                   { subst prev.
                     pose proof (outer_cache_result_bound (Z.to_nat j) a_ascii b_ascii init)
                       as [Hcache_bound _].
                     - rewrite Hinit_len, Hlen_a_ascii. reflexivity.
                     - exact Hinit_bound.
                     - exact Hcache_bound. }
                   assert (Hstep_bound :
                     (snd (fst (inner_steps (Z.to_nat i) a_ascii b_j
                       prev (Z.to_nat j) (Z.to_nat j))) <=
                      length a_ascii + Z.to_nat j + Z.to_nat i)%nat /\
                     (snd (inner_steps (Z.to_nat i) a_ascii b_j
                       prev (Z.to_nat j) (Z.to_nat j)) <=
                      length a_ascii + Z.to_nat j + Z.to_nat i)%nat).
                   { pose proof (inner_steps_bound (Z.to_nat i) a_ascii b_j prev
                       (Z.to_nat j) (Z.to_nat j) (length a_ascii + Z.to_nat j))
                       as Hstep.
                     specialize (Hstep Hprev_bound ltac:(lia) ltac:(lia)).
                     destruct Hstep as [Hd [Hr _]].
                     split; assumption. }
                   assert (Hr_nat_bound :
                     (r_i <= length a_ascii + Z.to_nat j + Z.to_nat i)%nat).
                   { subst r_i. exact (proj2 Hstep_bound). }
                   assert (Hd_nat_bound :
                     (d_i <= length a_ascii + Z.to_nat j + Z.to_nat i)%nat).
                   { subst d_i. exact (proj1 Hstep_bound). }
                   assert (Hc_nat_bound :
                     (c_i <= length a_ascii + Z.to_nat j)%nat).
                   { subst c_i.
                     eapply Forall_le_nth; [lia|exact Hprev_bound]. }
                   assert (Hb_nat_bound :
                     (bdist <= S (length a_ascii + Z.to_nat j + Z.to_nat i))%nat).
                   { subst bdist. destruct (Ascii.ascii_dec b_j a_i); lia. }
                   forward_if
                     (PROP ()
                      LOCAL (
                        temp _result (Vlong (Int64.repr (Z.of_nat new_r)));
                        temp _distance (Vlong (Int64.repr (Z.of_nat c_i)));
                        temp _bDistance (Vlong (Int64.repr (Z.of_nat bdist)));
                        temp _t'2 (Vbyte (Znth i a));
                        temp _index (Vlong (Int64.repr i));
                        temp _bIndex (Vlong (Int64.repr (j + 1)));
                        temp _code (Vint (Int.repr (Byte.signed (Znth j b))));
                        temp _cache cache;
                        gvars gv; temp _a a_val;
                        temp _length (Vlong (Int64.repr (Zlength a)));
                        temp _b b_val;
                        temp _bLength (Vlong (Int64.repr (Zlength b)))
                      )
                      SEP (
                        mem_mgr gv;
                        malloc_token Ews (tarray tulong (Zlength a)) cache;
                        data_at Ews (tarray tulong (Zlength a))
                          (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                            (prefix_i ++ skipn (Z.to_nat i) prev))
                          cache;
                        data_at sh (tarray tschar (Zlength a))
                          (map Vbyte a) a_val;
                        data_at sh (tarray tschar (Zlength b))
                          (map Vbyte b) b_val
                      )).
                   { (* True: distance > result, i.e., r_i < c_i *)
                     (* Existing loop bounds and [solve_size_t_nat_bound] show
                        all candidate DP cells fit in [size_t]. *)
                     assert (Hbnd_r : 0 <= Z.of_nat r_i <= Int64.max_unsigned)
                       by (solve_size_t_nat_bound).
                     assert (Hbnd_c : 0 <= Z.of_nat c_i <= Int64.max_unsigned)
                       by (solve_size_t_nat_bound).
                     assert (Hbnd_b : 0 <= Z.of_nat bdist <= Int64.max_unsigned)
                       by (solve_size_t_nat_bound).
	                     assert (Hrc : (r_i < c_i)%nat).
	                     { match goal with
	                       | Hlt : Int64.ltu _ _ = true |- _ =>
	                           apply ltu_repr64 in Hlt;
	                           [lia | exact Hbnd_r | exact Hbnd_c]
	                       end. }
                     forward_if
                       (PROP ()
                        LOCAL (
                          temp _result (Vlong (Int64.repr (Z.of_nat new_r)));
                          temp _distance (Vlong (Int64.repr (Z.of_nat c_i)));
                          temp _bDistance (Vlong (Int64.repr (Z.of_nat bdist)));
                          temp _t'2 (Vbyte (Znth i a));
                          temp _index (Vlong (Int64.repr i));
                          temp _bIndex (Vlong (Int64.repr (j + 1)));
                          temp _code (Vint (Int.repr (Byte.signed (Znth j b))));
                          temp _cache cache;
                          gvars gv; temp _a a_val;
                          temp _length (Vlong (Int64.repr (Zlength a)));
                          temp _b b_val;
                          temp _bLength (Vlong (Int64.repr (Zlength b)))
                        )
                        SEP (
                          mem_mgr gv;
                          malloc_token Ews (tarray tulong (Zlength a)) cache;
                          data_at Ews (tarray tulong (Zlength a))
                            (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                              (prefix_i ++ skipn (Z.to_nat i) prev))
                            cache;
                          data_at sh (tarray tschar (Zlength a))
                            (map Vbyte a) a_val;
                          data_at sh (tarray tschar (Zlength b))
                            (map Vbyte b) b_val
                        )).
                     { (* T-T: r_i < bdist. result = result + 1 = S r_i. *)
                       assert (Hrb : (r_i < bdist)%nat).
                       { match goal with
                         | H : Int64.ltu _ _ = true |- _ =>
                             apply ltu_repr64 in H;
                             [lia
                             | exact Hbnd_r || exact Hbnd_c || exact Hbnd_b
                             | exact Hbnd_r || exact Hbnd_c || exact Hbnd_b]
                         end. }
                       forward.  (* _result = _result + 1 *)
                       entailer!.
                       subst new_r. unfold dp_min.
                       rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)) by exact Hrc.
                       rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)) by exact Hrb.
                       f_equal. f_equal. lia.
                     }
                     { (* T-F: r_i >= bdist. result = bDistance. *)
                       assert (Hrb : (bdist <= r_i)%nat) by lia.
                       forward.  (* _result = _bDistance *)
                       entailer!.
                       subst new_r. unfold dp_min.
                       rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)) by exact Hrc.
                       rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)) by exact Hrb.
                       reflexivity.
                     }
                   }
                   { (* False: distance <= result, i.e., r_i >= c_i *)
                     assert (Hbnd_r : 0 <= Z.of_nat r_i <= Int64.max_unsigned)
                       by (solve_size_t_nat_bound).
                     assert (Hbnd_c : 0 <= Z.of_nat c_i <= Int64.max_unsigned)
                       by (solve_size_t_nat_bound).
                     assert (Hbnd_b : 0 <= Z.of_nat bdist <= Int64.max_unsigned)
                       by (solve_size_t_nat_bound).
                     assert (Hrc : (c_i <= r_i)%nat).
                     { match goal with
                       | H : Int64.ltu _ _ = false |- _ =>
                           apply ltu_repr_false64 in H;
                           [lia
                             | exact Hbnd_r || exact Hbnd_c || exact Hbnd_b
                             | exact Hbnd_r || exact Hbnd_c || exact Hbnd_b]
                       end. }
                     forward_if
                       (PROP ()
                        LOCAL (
                          temp _result (Vlong (Int64.repr (Z.of_nat new_r)));
                          temp _distance (Vlong (Int64.repr (Z.of_nat c_i)));
                          temp _bDistance (Vlong (Int64.repr (Z.of_nat bdist)));
                          temp _t'2 (Vbyte (Znth i a));
                          temp _index (Vlong (Int64.repr i));
                          temp _bIndex (Vlong (Int64.repr (j + 1)));
                          temp _code (Vint (Int.repr (Byte.signed (Znth j b))));
                          temp _cache cache;
                          gvars gv; temp _a a_val;
                          temp _length (Vlong (Int64.repr (Zlength a)));
                          temp _b b_val;
                          temp _bLength (Vlong (Int64.repr (Zlength b)))
                        )
                        SEP (
                          mem_mgr gv;
                          malloc_token Ews (tarray tulong (Zlength a)) cache;
                          data_at Ews (tarray tulong (Zlength a))
                            (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                              (prefix_i ++ skipn (Z.to_nat i) prev))
                            cache;
                          data_at sh (tarray tschar (Zlength a))
                            (map Vbyte a) a_val;
                          data_at sh (tarray tschar (Zlength b))
                            (map Vbyte b) b_val
                        )).
                     { (* F-T: c_i < bdist. result = distance + 1 = S c_i. *)
                       assert (Hdb : (c_i < bdist)%nat) by lia.
                       forward.  (* _result = _distance + 1 *)
                       entailer!.
                       subst new_r. unfold dp_min.
                       rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)) by exact Hrc.
                       rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)) by exact Hdb.
                       f_equal. f_equal. lia.
                     }
                     { (* F-F: c_i >= bdist. result = bDistance. *)
                       assert (Hdb : (bdist <= c_i)%nat) by lia.
                       forward.  (* _result = _bDistance *)
                       entailer!.
                       subst new_r. unfold dp_min.
                       rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)) by exact Hrc.
                       rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)) by exact Hdb.
                       reflexivity.
                     }
                   }
                   (* Now _result = Vsize_t (Z.of_nat new_r). *)
                   (* Write cache[i] = _result *)
                   forward.  (* cache[i] = _result *)
                   (* _index = _index + 1 *)
                   forward.
                   (* Show inner loop invariant for i + 1 *)
                   Exists (i + 1).
                   (* Use inner_steps_extend to rewrite the new state. *)
                   assert (HSi : Z.to_nat (i + 1) = S (Z.to_nat i)) by lia.
                   rewrite HSi.
                   pose proof (inner_steps_extend (Z.to_nat i) a_ascii b_j
                                 prev (Z.to_nat j) (Z.to_nat j)) as Hext.
                   assert (Hi_a_bnd : (Z.to_nat i < length a_ascii)%nat).
                   { rewrite Hlen_a_ascii. lia. }
                   assert (Hi_p_bnd : (Z.to_nat i < length prev)%nat).
                   { rewrite Hprev_len. lia. }
                   specialize (Hext Hi_a_bnd Hi_p_bnd).
                   (* Hext relates inner_steps (S (Z.to_nat i)) ... to inner_steps (Z.to_nat i) ... *)
                   rewrite Hext.
                   cbv zeta.
                   (* Destruct the prior inner_steps to expose its components. *)
                   destruct (inner_steps (Z.to_nat i) a_ascii b_j
                               prev (Z.to_nat j) (Z.to_nat j))
                     as [[pfx d] r] eqn:Hpdr.
                   cbn [fst snd].
                   change (Int.signed (Int.repr 1)) with 1.
                   rewrite add64_repr.
                   (* The destruct substituted inner_steps with (pfx, d, r),
                      so the set'd definitions also reduce. *)
                   (* Get a fresh length fact for pfx (before any subst). *)
                   assert (Hpfx_len : length pfx = Z.to_nat i).
                   { pose proof (f_equal (fun p => length (fst (fst p))) Hpdr) as Hl.
                     cbn in Hl. rewrite <- Hl.
                     apply inner_steps_length; lia. }
                   subst r_i d_i prefix_i.
                   entailer!.
                   subst bdist a_i new_r.
                   (* SEP: upd_Znth = map ((pfx ++ [new_r]) ++ skipn (S i) prev) *)
                   rewrite (upd_Znth_map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))).
                   apply derives_refl'.
                   f_equal.
                   rewrite (upd_Znth_prefix_skipn 0%nat).
                   - reflexivity.
                   - lia.
                   - exact Hpfx_len.
                   - rewrite Hprev_len, <- Hla_eq. lia.
                 }
                 finish_outer_continue a a_ascii b_ascii init
                   Hinit_len Hlen_a_ascii Hla_eq i j prev b_j.
               + (* break: j = Zlength b, produce break invariant. *)
                 forward.
                 assert (Hj_eq : j = Zlength b).
                 {
                   match goal with
                   | H : Int64.ltu _ _ = false |- _ =>
                       apply_size_t_ltu_false H
                   end.
                 }
                 subst j.
                 exfalso; lia.
             - (* j > 0 case *)
               replace (if Z.eq_dec j 0 then nil else [temp _result result_v])
                  with [temp _result result_v]
                  by (destruct (Z.eq_dec j 0); [contradiction|reflexivity]).
               forward_if.
               + (* body continue: j < Zlength b *)
                 assert (Hj_lt : 0 <= j < Zlength b).
                 { match goal with
                   | H : Int64.ltu _ _ = true |- _ =>
                       apply_size_t_ltu_true H
                   end. }
                 unfold byte_array_at, Vsize_t.
                 unfold Vsize_t_list.
                 Intros.
                 forward.  (* _t'3 = b[j] *)
                 forward.  (* _code = _t'3 *)
                 forward.  (* _distance = _bIndex *)
                 forward.  (* _result = _bIndex *)
                 forward.  (* _bIndex = _bIndex + 1 *)
                 forward.  (* _index = 0 *)
                 (* Inner loop. Let `prev` be the cache at the start of the
                    j-th outer iteration, and `b_j` the j-th ascii char. *)
                 set (prev := outer_cache a_ascii b_ascii init (Z.to_nat j)).
                 set (b_j := nth (Z.to_nat j) b_ascii Ascii.zero).
                 forward_while
                   (EX i : Z,
                     PROP (0 <= i <= Zlength a)
                     LOCAL (
                       temp _index (Vlong (Int64.repr i));
                       temp _bIndex (Vlong (Int64.repr (j + 1)));
                       temp _result (Vlong (Int64.repr
                         (Z.of_nat (snd (inner_steps (Z.to_nat i) a_ascii b_j
                                          prev (Z.to_nat j) (Z.to_nat j))))));
                       temp _distance (Vlong (Int64.repr
                         (Z.of_nat (snd (fst (inner_steps (Z.to_nat i) a_ascii b_j
                                               prev (Z.to_nat j) (Z.to_nat j)))))));
                       temp _code (Vint (Int.repr (Byte.signed (Znth j b))));
                       temp _cache cache;
                       gvars gv;
                       temp _a a_val;
                       temp _length (Vlong (Int64.repr (Zlength a)));
                       temp _b b_val;
                       temp _bLength (Vlong (Int64.repr (Zlength b)))
                     )
                     SEP (
                       mem_mgr gv;
                       malloc_token Ews (tarray tulong (Zlength a)) cache;
                       data_at Ews (tarray tulong (Zlength a))
                         (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                           (fst (fst (inner_steps (Z.to_nat i) a_ascii b_j
                                       prev (Z.to_nat j) (Z.to_nat j)))
                            ++ skipn (Z.to_nat i) prev))
                         cache;
                       data_at sh (tarray tschar (Zlength a))
                         (map Vbyte a) a_val;
                       data_at sh (tarray tschar (Zlength b))
                         (map Vbyte b) b_val
                     )).
                 { (* Initial entailment: i = 0 *)
                   Exists 0.
                   change (Z.to_nat 0) with 0%nat.
                   cbn [inner_steps fst snd app skipn].
                   replace (Z.of_nat (Z.to_nat j)) with j by lia.
                   change (Int.signed (Int.repr 1)) with 1.
                   change (Int.signed (Int.repr 0)) with 0.
                   rewrite add64_repr.
                   entailer!.
                 }
                 { (* Typecheck of test *)
                   entailer!.
                 }
                 { (* Inner body *)
                   assert (Hi_lt : 0 <= i < Zlength a).
                   { match goal with
                     | H : Int64.ltu _ _ = true |- _ =>
                         apply_size_t_ltu_true H
                     end. }
                   forward.  (* _t'2 = a[i] *)
                   (* Abbreviations. *)
                   set (d_i := snd (fst (inner_steps (Z.to_nat i) a_ascii b_j
                                          prev (Z.to_nat j) (Z.to_nat j)))).
                   set (r_i := snd (inner_steps (Z.to_nat i) a_ascii b_j
                                     prev (Z.to_nat j) (Z.to_nat j))).
                   set (a_i := nth (Z.to_nat i) a_ascii Ascii.zero).
                   set (bdist := if Ascii.ascii_dec b_j a_i then d_i else S d_i).
                   forward_if
                     (PROP ()
                      LOCAL (
                        temp _bDistance (Vlong (Int64.repr (Z.of_nat bdist)));
                        temp _t'2 (Vbyte (Znth i a));
                        temp _index (Vlong (Int64.repr i));
                        temp _bIndex (Vlong (Int64.repr (j + 1)));
                        temp _result (Vlong (Int64.repr (Z.of_nat r_i)));
                        temp _distance (Vlong (Int64.repr (Z.of_nat d_i)));
                        temp _code (Vint (Int.repr (Byte.signed (Znth j b))));
                        temp _cache cache;
                        gvars gv;
                        temp _a a_val;
                        temp _length (Vlong (Int64.repr (Zlength a)));
                        temp _b b_val;
                        temp _bLength (Vlong (Int64.repr (Zlength b)))
                      )
                      SEP (
                        mem_mgr gv;
                        malloc_token Ews (tarray tulong (Zlength a)) cache;
                        data_at Ews (tarray tulong (Zlength a))
                          (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                            (fst (fst (inner_steps (Z.to_nat i) a_ascii b_j
                                        prev (Z.to_nat j) (Z.to_nat j)))
                             ++ skipn (Z.to_nat i) prev))
                          cache;
                        data_at sh (tarray tschar (Zlength a))
                          (map Vbyte a) a_val;
                        data_at sh (tarray tschar (Zlength b))
                          (map Vbyte b) b_val
                      )).
                   { (* True branch: bytes equal *)
                     forward.
                     entailer!.
                     unfold bdist.
                     destruct (Ascii.ascii_dec b_j a_i) as [_|Hne].
                     - reflexivity.
                     - exfalso. apply Hne.
                       subst b_j a_i.
                       match goal with
                       | H : Znth ?jb b = Znth i a |- _ =>
                           set (jb0 := jb) in *; rename H into Hba
                       end.
                       assert (Hlmb : length (map byte_to_ascii b) = length b)
                         by apply length_map.
                       assert (Hlma : length (map byte_to_ascii a) = length a)
                         by apply length_map.
                       rewrite (nth_indep _ Ascii.zero (byte_to_ascii Byte.zero))
                         by lia.
                       rewrite (nth_indep (map byte_to_ascii a) Ascii.zero
                                   (byte_to_ascii Byte.zero)) by lia.
                       unfold Znth in Hba.
                       destruct (Z_lt_dec jb0 0); [lia|].
                       destruct (Z_lt_dec i 0); [lia|].
                       unfold b_ascii, a_ascii.
                       change Ascii.zero with (byte_to_ascii Byte.zero).
                       rewrite !map_nth.
                       f_equal.
                       exact Hba.
                   }
                   { (* False branch: bytes differ *)
                     forward.
                     entailer!.
                     unfold bdist.
                     destruct (Ascii.ascii_dec b_j a_i) as [Heq|_].
                     - exfalso.
                       subst b_j a_i.
                       (* From Heq: nth k b_ascii Ascii.zero = nth k' a_ascii Ascii.zero *)
                       unfold b_ascii, a_ascii in Heq.
                       change Ascii.zero with (byte_to_ascii Byte.zero) in Heq.
                       rewrite !map_nth in Heq.
                       apply byte_to_ascii_inj in Heq.
                       (* Heq : nth (Z.to_nat j) b Byte.zero = nth (Z.to_nat i) a Byte.zero *)
                       (* The hypothesis from forward_if false branch says Znth j b <> Znth i a. *)
                       match goal with
                       | H : Znth ?jb b <> Znth i a |- _ =>
                           set (jb0 := jb) in *;
                           apply H;
                           unfold Znth;
                           destruct (Z_lt_dec jb0 0); [lia|];
                           destruct (Z_lt_dec i 0); [lia|];
                           exact Heq
                       end.
                     - cbn. f_equal. f_equal. lia.
                   }
                   (* Set up the cache view as the concatenated prefix + suffix. *)
                   set (prefix_i := fst (fst (inner_steps (Z.to_nat i) a_ascii b_j
                                              prev (Z.to_nat j) (Z.to_nat j)))).
                   set (c_i := nth (Z.to_nat i) prev 0%nat).
                   (* length facts *)
                   assert (Hprev_len : length prev = length a).
                   { subst prev. rewrite outer_cache_length;
                     [exact Hinit_len|
                      rewrite Hlen_a_ascii, Hinit_len; reflexivity]. }
                   assert (Hprefix_len : length prefix_i = Z.to_nat i).
                   { subst prefix_i. apply inner_steps_length; lia. }
                   assert (Hskipn_len : (length (skipn (Z.to_nat i) prev) =
                                        length a - Z.to_nat i)%nat).
                   { rewrite skipn_length, Hprev_len. reflexivity. }
                   assert (Hcache_zlen :
                     Zlength (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                              (prefix_i ++ skipn (Z.to_nat i) prev)) = Zlength a).
                   { rewrite Zlength_map, Zlength_app, !Zlength_correct.
                     rewrite Hprefix_len, Hskipn_len.
                     rewrite Nat2Z.inj_sub by lia.
                     rewrite <- Hla_eq, Z2Nat.id by lia.
                     lia. }
                   assert (Hpfx_skipn_zlen :
                     Zlength (prefix_i ++ skipn (Z.to_nat i) prev) = Zlength a).
                   { rewrite Zlength_app, !Zlength_correct.
                     rewrite Hprefix_len, Hskipn_len.
                     rewrite Nat2Z.inj_sub by lia.
                     rewrite <- Hla_eq, Z2Nat.id by lia.
                     lia. }
                   (* Znth i (map ... (prefix ++ skipn i prev)) = c_i (as Vlong). *)
                   assert (Hcache_at_i :
                     Znth i (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                              (prefix_i ++ skipn (Z.to_nat i) prev))
                     = Vlong (Int64.repr (Z.of_nat c_i))).
                   { rewrite Znth_map by lia.
                     unfold Znth.
                     destruct (Z_lt_dec i 0); [lia|].
                     rewrite app_nth2 by lia.
                     rewrite Hprefix_len.
                     replace (Z.to_nat i - Z.to_nat i)%nat with 0%nat by lia.
                     f_equal. f_equal.
                     subst c_i.
                     rewrite <- (nth_skipn_default 0%nat prev (Z.to_nat i)).
                     reflexivity. }
                   forward.  (* _distance = cache[i] *)
                   { entailer!. rewrite Znth_map by lia. apply I. }
                   replace (Znth i (map
                     (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                     (prefix_i ++ skipn (Z.to_nat i) prev)))
                     with (Vlong (Int64.repr (Z.of_nat c_i)))
                     by (symmetry; exact Hcache_at_i).
                   (* The 4 branches of the nested ifs all compute dp_min r_i c_i bdist. *)
                   set (new_r := dp_min r_i c_i bdist).
                   assert (Hprev_bound :
                     Forall (fun x => (x <= length a_ascii + Z.to_nat j)%nat) prev).
                   { subst prev.
                     pose proof (outer_cache_result_bound (Z.to_nat j) a_ascii b_ascii init)
                       as [Hcache_bound _].
                     - rewrite Hinit_len, Hlen_a_ascii. reflexivity.
                     - exact Hinit_bound.
                     - exact Hcache_bound. }
                   assert (Hstep_bound :
                     (snd (fst (inner_steps (Z.to_nat i) a_ascii b_j
                       prev (Z.to_nat j) (Z.to_nat j))) <=
                      length a_ascii + Z.to_nat j + Z.to_nat i)%nat /\
                     (snd (inner_steps (Z.to_nat i) a_ascii b_j
                       prev (Z.to_nat j) (Z.to_nat j)) <=
                      length a_ascii + Z.to_nat j + Z.to_nat i)%nat).
                   { pose proof (inner_steps_bound (Z.to_nat i) a_ascii b_j prev
                       (Z.to_nat j) (Z.to_nat j) (length a_ascii + Z.to_nat j))
                       as Hstep.
                     specialize (Hstep Hprev_bound ltac:(lia) ltac:(lia)).
                     destruct Hstep as [Hd [Hr _]].
                     split; assumption. }
                   assert (Hr_nat_bound :
                     (r_i <= length a_ascii + Z.to_nat j + Z.to_nat i)%nat).
                   { subst r_i. exact (proj2 Hstep_bound). }
                   assert (Hd_nat_bound :
                     (d_i <= length a_ascii + Z.to_nat j + Z.to_nat i)%nat).
                   { subst d_i. exact (proj1 Hstep_bound). }
                   assert (Hc_nat_bound :
                     (c_i <= length a_ascii + Z.to_nat j)%nat).
                   { subst c_i.
                     eapply Forall_le_nth; [lia|exact Hprev_bound]. }
                   assert (Hb_nat_bound :
                     (bdist <= S (length a_ascii + Z.to_nat j + Z.to_nat i))%nat).
                   { subst bdist. destruct (Ascii.ascii_dec b_j a_i); lia. }
                   forward_if
                     (PROP ()
                      LOCAL (
                        temp _result (Vlong (Int64.repr (Z.of_nat new_r)));
                        temp _distance (Vlong (Int64.repr (Z.of_nat c_i)));
                        temp _bDistance (Vlong (Int64.repr (Z.of_nat bdist)));
                        temp _t'2 (Vbyte (Znth i a));
                        temp _index (Vlong (Int64.repr i));
                        temp _bIndex (Vlong (Int64.repr (j + 1)));
                        temp _code (Vint (Int.repr (Byte.signed (Znth j b))));
                        temp _cache cache;
                        gvars gv; temp _a a_val;
                        temp _length (Vlong (Int64.repr (Zlength a)));
                        temp _b b_val;
                        temp _bLength (Vlong (Int64.repr (Zlength b)))
                      )
                      SEP (
                        mem_mgr gv;
                        malloc_token Ews (tarray tulong (Zlength a)) cache;
                        data_at Ews (tarray tulong (Zlength a))
                          (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                            (prefix_i ++ skipn (Z.to_nat i) prev))
                          cache;
                        data_at sh (tarray tschar (Zlength a))
                          (map Vbyte a) a_val;
                        data_at sh (tarray tschar (Zlength b))
                          (map Vbyte b) b_val
                      )).
                   { (* True: distance > result, i.e., r_i < c_i *)
                     (* Existing loop bounds and [solve_size_t_nat_bound] show
                        all candidate DP cells fit in [size_t]. *)
                     assert (Hbnd_r : 0 <= Z.of_nat r_i <= Int64.max_unsigned)
                       by (solve_size_t_nat_bound).
                     assert (Hbnd_c : 0 <= Z.of_nat c_i <= Int64.max_unsigned)
                       by (solve_size_t_nat_bound).
                     assert (Hbnd_b : 0 <= Z.of_nat bdist <= Int64.max_unsigned)
                       by (solve_size_t_nat_bound).
	                     assert (Hrc : (r_i < c_i)%nat).
	                     { match goal with
	                       | Hlt : Int64.ltu _ _ = true |- _ =>
	                           apply ltu_repr64 in Hlt;
	                           [lia | exact Hbnd_r | exact Hbnd_c]
	                       end. }
                     forward_if
                       (PROP ()
                        LOCAL (
                          temp _result (Vlong (Int64.repr (Z.of_nat new_r)));
                          temp _distance (Vlong (Int64.repr (Z.of_nat c_i)));
                          temp _bDistance (Vlong (Int64.repr (Z.of_nat bdist)));
                          temp _t'2 (Vbyte (Znth i a));
                          temp _index (Vlong (Int64.repr i));
                          temp _bIndex (Vlong (Int64.repr (j + 1)));
                          temp _code (Vint (Int.repr (Byte.signed (Znth j b))));
                          temp _cache cache;
                          gvars gv; temp _a a_val;
                          temp _length (Vlong (Int64.repr (Zlength a)));
                          temp _b b_val;
                          temp _bLength (Vlong (Int64.repr (Zlength b)))
                        )
                        SEP (
                          mem_mgr gv;
                          malloc_token Ews (tarray tulong (Zlength a)) cache;
                          data_at Ews (tarray tulong (Zlength a))
                            (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                              (prefix_i ++ skipn (Z.to_nat i) prev))
                            cache;
                          data_at sh (tarray tschar (Zlength a))
                            (map Vbyte a) a_val;
                          data_at sh (tarray tschar (Zlength b))
                            (map Vbyte b) b_val
                        )).
                     { (* T-T: r_i < bdist. result = result + 1 = S r_i. *)
                       assert (Hrb : (r_i < bdist)%nat).
                       { match goal with
                         | H : Int64.ltu _ _ = true |- _ =>
                             apply ltu_repr64 in H;
                             [lia
                             | exact Hbnd_r || exact Hbnd_c || exact Hbnd_b
                             | exact Hbnd_r || exact Hbnd_c || exact Hbnd_b]
                         end. }
                       forward.  (* _result = _result + 1 *)
                       entailer!.
                       subst new_r. unfold dp_min.
                       rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)) by exact Hrc.
                       rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)) by exact Hrb.
                       f_equal. f_equal. lia.
                     }
                     { (* T-F: r_i >= bdist. result = bDistance. *)
                       assert (Hrb : (bdist <= r_i)%nat) by lia.
                       forward.  (* _result = _bDistance *)
                       entailer!.
                       subst new_r. unfold dp_min.
                       rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)) by exact Hrc.
                       rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)) by exact Hrb.
                       reflexivity.
                     }
                   }
                   { (* False: distance <= result, i.e., r_i >= c_i *)
                     assert (Hbnd_r : 0 <= Z.of_nat r_i <= Int64.max_unsigned)
                       by (solve_size_t_nat_bound).
                     assert (Hbnd_c : 0 <= Z.of_nat c_i <= Int64.max_unsigned)
                       by (solve_size_t_nat_bound).
                     assert (Hbnd_b : 0 <= Z.of_nat bdist <= Int64.max_unsigned)
                       by (solve_size_t_nat_bound).
                     assert (Hrc : (c_i <= r_i)%nat).
                     { match goal with
                       | H : Int64.ltu _ _ = false |- _ =>
                           apply ltu_repr_false64 in H;
                           [lia
                             | exact Hbnd_r || exact Hbnd_c || exact Hbnd_b
                             | exact Hbnd_r || exact Hbnd_c || exact Hbnd_b]
                       end. }
                     forward_if
                       (PROP ()
                        LOCAL (
                          temp _result (Vlong (Int64.repr (Z.of_nat new_r)));
                          temp _distance (Vlong (Int64.repr (Z.of_nat c_i)));
                          temp _bDistance (Vlong (Int64.repr (Z.of_nat bdist)));
                          temp _t'2 (Vbyte (Znth i a));
                          temp _index (Vlong (Int64.repr i));
                          temp _bIndex (Vlong (Int64.repr (j + 1)));
                          temp _code (Vint (Int.repr (Byte.signed (Znth j b))));
                          temp _cache cache;
                          gvars gv; temp _a a_val;
                          temp _length (Vlong (Int64.repr (Zlength a)));
                          temp _b b_val;
                          temp _bLength (Vlong (Int64.repr (Zlength b)))
                        )
                        SEP (
                          mem_mgr gv;
                          malloc_token Ews (tarray tulong (Zlength a)) cache;
                          data_at Ews (tarray tulong (Zlength a))
                            (map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))
                              (prefix_i ++ skipn (Z.to_nat i) prev))
                            cache;
                          data_at sh (tarray tschar (Zlength a))
                            (map Vbyte a) a_val;
                          data_at sh (tarray tschar (Zlength b))
                            (map Vbyte b) b_val
                        )).
                     { (* F-T: c_i < bdist. result = distance + 1 = S c_i. *)
                       assert (Hdb : (c_i < bdist)%nat) by lia.
                       forward.  (* _result = _distance + 1 *)
                       entailer!.
                       subst new_r. unfold dp_min.
                       rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)) by exact Hrc.
                       rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)) by exact Hdb.
                       f_equal. f_equal. lia.
                     }
                     { (* F-F: c_i >= bdist. result = bDistance. *)
                       assert (Hdb : (bdist <= c_i)%nat) by lia.
                       forward.  (* _result = _bDistance *)
                       entailer!.
                       subst new_r. unfold dp_min.
                       rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)) by exact Hrc.
                       rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)) by exact Hdb.
                       reflexivity.
                     }
                   }
                   (* Now _result = Vsize_t (Z.of_nat new_r). *)
                   (* Write cache[i] = _result *)
                   forward.  (* cache[i] = _result *)
                   (* _index = _index + 1 *)
                   forward.
                   (* Show inner loop invariant for i + 1 *)
                   Exists (i + 1).
                   (* Use inner_steps_extend to rewrite the new state. *)
                   assert (HSi : Z.to_nat (i + 1) = S (Z.to_nat i)) by lia.
                   rewrite HSi.
                   pose proof (inner_steps_extend (Z.to_nat i) a_ascii b_j
                                 prev (Z.to_nat j) (Z.to_nat j)) as Hext.
                   assert (Hi_a_bnd : (Z.to_nat i < length a_ascii)%nat).
                   { rewrite Hlen_a_ascii. lia. }
                   assert (Hi_p_bnd : (Z.to_nat i < length prev)%nat).
                   { rewrite Hprev_len. lia. }
                   specialize (Hext Hi_a_bnd Hi_p_bnd).
                   (* Hext relates inner_steps (S (Z.to_nat i)) ... to inner_steps (Z.to_nat i) ... *)
                   rewrite Hext.
                   cbv zeta.
                   (* Destruct the prior inner_steps to expose its components. *)
                   destruct (inner_steps (Z.to_nat i) a_ascii b_j
                               prev (Z.to_nat j) (Z.to_nat j))
                     as [[pfx d] r] eqn:Hpdr.
                   cbn [fst snd].
                   change (Int.signed (Int.repr 1)) with 1.
                   rewrite add64_repr.
                   (* The destruct substituted inner_steps with (pfx, d, r),
                      so the set'd definitions also reduce. *)
                   (* Get a fresh length fact for pfx (before any subst). *)
                   assert (Hpfx_len : length pfx = Z.to_nat i).
                   { pose proof (f_equal (fun p => length (fst (fst p))) Hpdr) as Hl.
                     cbn in Hl. rewrite <- Hl.
                     apply inner_steps_length; lia. }
                   subst r_i d_i prefix_i.
                   entailer!.
                   subst bdist a_i new_r.
                   (* SEP: upd_Znth = map ((pfx ++ [new_r]) ++ skipn (S i) prev) *)
                   rewrite (upd_Znth_map (fun n : nat => Vlong (Int64.repr (Z.of_nat n)))).
                   apply derives_refl'.
                   f_equal.
                   rewrite (upd_Znth_prefix_skipn 0%nat).
                   - reflexivity.
                   - lia.
                   - exact Hpfx_len.
                   - rewrite Hprev_len, <- Hla_eq. lia.
                 }
                 finish_outer_continue a a_ascii b_ascii init
                   Hinit_len Hlen_a_ascii Hla_eq i j prev b_j.
               + (* break: j = Zlength b, produce break invariant. *)
                 forward.
                 assert (Hj_eq : j = Zlength b).
                 {
                   match goal with
                   | H : Int64.ltu _ _ = false |- _ =>
                       apply_size_t_ltu_false H
                   end.
                 }
                 subst j.
                 assert (Hres : result_v = Vsize_t (Z.of_nat
                            (outer_result a_ascii b_ascii init (length b)))).
                 { rewrite <- Hlb_eq.
                   match goal with
                   | H : _ > 0 -> _ |- _ => apply H; lia
                   end. }
                 rewrite Hres.
                 rewrite <- Hlb_eq.
                 entailer!.
           }
           (* After loop break, we have BInv state. *)
           (* Free the cache. *)
           forward_call (tarray tulong (Zlength a), cache, gv).
           { (* Precondition for free *)
             rewrite if_false; [|intro; subst cache; contradiction].
             cancel.
           }
           (* Return result. *)
           forward.
           entailer!.
           do 2 f_equal.
           assert (Hinit : init = init_cache (length a_ascii)).
           { unfold init. rewrite Hlen_a_ascii. f_equal. exact Hla_eq. }
           assert (Hlb_eq2 : length b = length b_ascii) by lia.
           rewrite Hinit, Hlb_eq2.
           assert (Ha_str : bytes_to_string a <> EmptyString).
           { intro Hempty. apply Ha_ne. unfold a_ascii.
             rewrite <- list_ascii_of_string_bytes. rewrite Hempty. reflexivity. }
           assert (Hb_str : bytes_to_string b <> EmptyString).
           { intro Hempty. apply Hb_ne. unfold b_ascii.
             rewrite <- list_ascii_of_string_bytes. rewrite Hempty. reflexivity. }
           unfold a_ascii, b_ascii.
           rewrite <- !list_ascii_of_string_bytes.
           rewrite !list_ascii_of_string_length.
           rewrite <- (levenshtein_dp_via_outer_result _ _ Ha_str Hb_str).
           apply levenshtein_dp_eq_levenshtein_recursive.
Qed.
