Require Import VST.floyd.proofauto.
Require Import levenshtein.
Require Import Extrinsic_levenshtein.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* copied from VC *)
Fixpoint string_to_list_byte (s: string) : list byte :=
  match s with
  | EmptyString => nil
  | String a s' => Byte.repr (Z.of_N (Ascii.N_of_ascii a)) :: string_to_list_byte s'
  end.

Fixpoint to_string (l : list byte) : string :=
  match l with
  | nil => EmptyString
  | cons x xs => String (Ascii.ascii_of_N (Z.to_N (Byte.intval x)))
                        (to_string xs)
  end.

Definition strlen_spec :=
 DECLARE _strlen
  WITH sh: share, s : list byte, str: val
  PRE [ _str OF tptr tschar ]
    PROP (readable_share sh)
    LOCAL (temp _str str)
    SEP (cstring sh s str)
  POST [ tuint ]
    PROP ()
    LOCAL (temp ret_temp (Vptrofs (Ptrofs.repr (Zlength s))))
    SEP (cstring sh s str).

(* specification for the helper function
   that also takes string lengths as arguments *)
Definition levenshtein_n_spec :=
 DECLARE _levenshtein
  WITH sh: share, a : list byte, a_val: val, a_len : Z, b : list byte, b_val : val, b_len : Z
  PRE [ _a OF tptr tschar, _length OF tuint, _b OF tptr tschar, _bLength OF tuint ]
    PROP (readable_share sh ; Zlength a = a_len ; Zlength b = b_len)
    LOCAL (temp _a a_val ; temp _b b_val ;
           temp _length (Vint (Int.repr a_len)) ;
           temp _length (Vint (Int.repr a_len)))
    SEP (cstring sh a a_val ; cstring sh b b_val)
  POST [ tuint ]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr
            (Z.of_nat (levenshtein (to_string a) (to_string b))))))
    SEP (cstring sh a a_val).

Definition levenshtein_spec :=
 DECLARE _levenshtein
  WITH sh: share, a : list byte, a_val: val, b : list byte, b_val : val
  PRE [ _a OF tptr tschar, _b OF tptr tschar ]
    PROP (readable_share sh)
    LOCAL (temp _a a_val ; temp _b b_val)
    SEP (cstring sh a a_val ; cstring sh b b_val)
  POST [ tuint ]
    PROP ()
    LOCAL (temp ret_temp (Vptrofs (Ptrofs.repr
            (Z.of_nat (levenshtein (to_string a) (to_string b))))))
    SEP (cstring sh a a_val).

Definition Gprog : funspecs :=
  ltac:(with_library prog [ strlen_spec; levenshtein_n_spec; levenshtein_spec ]).

Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
start_function.
unfold cstring in *.
Intros.
forward. (* i=0; *)
forward_loop  (EX i : Z,
  PROP (0 <= i < Zlength s + 1)
  LOCAL (temp _str str; temp _i (Vptrofs (Ptrofs.repr i)))
  SEP (data_at sh (tarray tschar (Zlength s + 1))
          (map Vbyte (s ++ [Byte.zero])) str)).
* (* Prove the precondition entails the loop invariant *)
Exists 0.
entailer!.
* (* Prove the loop body preserves the invariant *)
Intros i.
forward.
forward_if.
forward. entailer!.
repeat f_equal.
cstring.
forward.
Exists (i + 1).
entailer!.
cstring.
Qed.

Lemma body_levenshtein_n: semax_body Vprog Gprog f_levenshtein_n levenshtein_n_spec.
Proof.
start_function.
unfold cstring in *.
Admitted.

Lemma body_levenshtein: semax_body Vprog Gprog f_levenshtein levenshtein_spec.
Proof.
start_function.


Admitted.


Lemma prog_correct: semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_strlen.
semax_func_cons body_levenshtein_n.
semax_func_cons body_levenshtein.
Qed.
