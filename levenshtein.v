From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.4"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "levenshtein.c"%string.
  Definition normalized := false.
End Info.

Definition ___builtin_annot : ident := 7%positive.
Definition ___builtin_annot_intval : ident := 8%positive.
Definition ___builtin_bswap : ident := 1%positive.
Definition ___builtin_bswap16 : ident := 3%positive.
Definition ___builtin_bswap32 : ident := 2%positive.
Definition ___builtin_bswap64 : ident := 33%positive.
Definition ___builtin_clz : ident := 34%positive.
Definition ___builtin_clzl : ident := 35%positive.
Definition ___builtin_clzll : ident := 36%positive.
Definition ___builtin_ctz : ident := 37%positive.
Definition ___builtin_ctzl : ident := 38%positive.
Definition ___builtin_ctzll : ident := 39%positive.
Definition ___builtin_debug : ident := 51%positive.
Definition ___builtin_fabs : ident := 4%positive.
Definition ___builtin_fmadd : ident := 42%positive.
Definition ___builtin_fmax : ident := 40%positive.
Definition ___builtin_fmin : ident := 41%positive.
Definition ___builtin_fmsub : ident := 43%positive.
Definition ___builtin_fnmadd : ident := 44%positive.
Definition ___builtin_fnmsub : ident := 45%positive.
Definition ___builtin_fsqrt : ident := 5%positive.
Definition ___builtin_membar : ident := 9%positive.
Definition ___builtin_memcpy_aligned : ident := 6%positive.
Definition ___builtin_nop : ident := 50%positive.
Definition ___builtin_read16_reversed : ident := 46%positive.
Definition ___builtin_read32_reversed : ident := 47%positive.
Definition ___builtin_va_arg : ident := 11%positive.
Definition ___builtin_va_copy : ident := 12%positive.
Definition ___builtin_va_end : ident := 13%positive.
Definition ___builtin_va_start : ident := 10%positive.
Definition ___builtin_write16_reversed : ident := 48%positive.
Definition ___builtin_write32_reversed : ident := 49%positive.
Definition ___compcert_i64_dtos : ident := 18%positive.
Definition ___compcert_i64_dtou : ident := 19%positive.
Definition ___compcert_i64_sar : ident := 30%positive.
Definition ___compcert_i64_sdiv : ident := 24%positive.
Definition ___compcert_i64_shl : ident := 28%positive.
Definition ___compcert_i64_shr : ident := 29%positive.
Definition ___compcert_i64_smod : ident := 26%positive.
Definition ___compcert_i64_smulh : ident := 31%positive.
Definition ___compcert_i64_stod : ident := 20%positive.
Definition ___compcert_i64_stof : ident := 22%positive.
Definition ___compcert_i64_udiv : ident := 25%positive.
Definition ___compcert_i64_umod : ident := 27%positive.
Definition ___compcert_i64_umulh : ident := 32%positive.
Definition ___compcert_i64_utod : ident := 21%positive.
Definition ___compcert_i64_utof : ident := 23%positive.
Definition ___compcert_va_composite : ident := 17%positive.
Definition ___compcert_va_float64 : ident := 16%positive.
Definition ___compcert_va_int32 : ident := 14%positive.
Definition ___compcert_va_int64 : ident := 15%positive.
Definition _a : ident := 57%positive.
Definition _b : ident := 59%positive.
Definition _bDistance : ident := 65%positive.
Definition _bIndex : ident := 63%positive.
Definition _bLength : ident := 60%positive.
Definition _cache : ident := 61%positive.
Definition _calloc : ident := 55%positive.
Definition _code : ident := 67%positive.
Definition _distance : ident := 64%positive.
Definition _free : ident := 56%positive.
Definition _i : ident := 53%positive.
Definition _index : ident := 62%positive.
Definition _length : ident := 58%positive.
Definition _levenshtein : ident := 69%positive.
Definition _levenshtein_n : ident := 68%positive.
Definition _main : ident := 70%positive.
Definition _result : ident := 66%positive.
Definition _str : ident := 52%positive.
Definition _strlen : ident := 54%positive.
Definition _t'1 : ident := 71%positive.
Definition _t'2 : ident := 72%positive.
Definition _t'3 : ident := 73%positive.
Definition _t'4 : ident := 74%positive.
Definition _t'5 : ident := 75%positive.
Definition _t'6 : ident := 76%positive.
Definition _t'7 : ident := 77%positive.
Definition _t'8 : ident := 78%positive.
Definition _t'9 : ident := 79%positive.

Definition f_strlen := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      Sskip
      (Sifthenelse (Ebinop Oeq
                     (Ederef
                       (Ebinop Oadd (Etempvar _str (tptr tschar))
                         (Etempvar _i tuint) (tptr tschar)) tschar)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sreturn (Some (Etempvar _i tuint)))
        Sskip))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint))))
|}.

Definition f_levenshtein_n := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tschar)) :: (_length, tuint) ::
                (_b, (tptr tschar)) :: (_bLength, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_cache, (tptr tuint)) :: (_index, tuint) ::
               (_bIndex, tuint) :: (_distance, tuint) ::
               (_bDistance, tuint) :: (_result, tuint) :: (_code, tschar) ::
               (_t'9, tuint) :: (_t'8, tuint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _calloc (Tfunction Tnil tint
                      {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
      ((Etempvar _length tuint) :: (Esizeof tuint tuint) :: nil))
    (Sset _cache (Etempvar _t'1 tint)))
  (Ssequence
    (Sset _index (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _bIndex (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _a (tptr tschar))
                       (Etempvar _b (tptr tschar)) tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          Sskip)
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _length tuint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sreturn (Some (Etempvar _bLength tuint)))
            Sskip)
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _bLength tuint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sreturn (Some (Etempvar _length tuint)))
              Sskip)
            (Ssequence
              (Swhile
                (Ebinop Olt (Etempvar _index tuint) (Etempvar _length tuint)
                  tint)
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _cache (tptr tuint))
                        (Etempvar _index tuint) (tptr tuint)) tuint)
                    (Ebinop Oadd (Etempvar _index tuint)
                      (Econst_int (Int.repr 1) tint) tuint))
                  (Sset _index
                    (Ebinop Oadd (Etempvar _index tuint)
                      (Econst_int (Int.repr 1) tint) tuint))))
              (Ssequence
                (Swhile
                  (Ebinop Olt (Etempvar _bIndex tuint)
                    (Etempvar _bLength tuint) tint)
                  (Ssequence
                    (Sset _code
                      (Ecast
                        (Ederef
                          (Ebinop Oadd (Etempvar _b (tptr tschar))
                            (Etempvar _bIndex tuint) (tptr tschar)) tschar)
                        tschar))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'2 (Etempvar _bIndex tuint))
                              (Sset _bIndex
                                (Ebinop Oadd (Etempvar _t'2 tuint)
                                  (Econst_int (Int.repr 1) tint) tuint)))
                            (Sset _t'3 (Ecast (Etempvar _t'2 tuint) tuint)))
                          (Sset _distance (Etempvar _t'3 tuint)))
                        (Sset _result (Etempvar _t'3 tuint)))
                      (Ssequence
                        (Sset _index (Econst_int (Int.repr (-1)) tuint))
                        (Sloop
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'4
                                  (Ecast
                                    (Ebinop Oadd (Etempvar _index tuint)
                                      (Econst_int (Int.repr 1) tint) tuint)
                                    tuint))
                                (Sset _index (Etempvar _t'4 tuint)))
                              (Sifthenelse (Ebinop Olt (Etempvar _t'4 tuint)
                                             (Etempvar _length tuint) tint)
                                Sskip
                                Sbreak))
                            (Ssequence
                              (Ssequence
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _code tschar)
                                               (Ederef
                                                 (Ebinop Oadd
                                                   (Etempvar _a (tptr tschar))
                                                   (Etempvar _index tuint)
                                                   (tptr tschar)) tschar)
                                               tint)
                                  (Sset _t'5
                                    (Ecast (Etempvar _distance tuint) tuint))
                                  (Sset _t'5
                                    (Ecast
                                      (Ebinop Oadd (Etempvar _distance tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)
                                      tuint)))
                                (Sset _bDistance (Etempvar _t'5 tuint)))
                              (Ssequence
                                (Sset _distance
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _cache (tptr tuint))
                                      (Etempvar _index tuint) (tptr tuint))
                                    tuint))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sifthenelse (Ebinop Ogt
                                                     (Etempvar _distance tuint)
                                                     (Etempvar _result tuint)
                                                     tint)
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _bDistance tuint)
                                                       (Etempvar _result tuint)
                                                       tint)
                                          (Ssequence
                                            (Sset _t'7
                                              (Ecast
                                                (Ebinop Oadd
                                                  (Etempvar _result tuint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tuint) tuint))
                                            (Sset _t'6
                                              (Ecast (Etempvar _t'7 tuint)
                                                tuint)))
                                          (Ssequence
                                            (Sset _t'7
                                              (Ecast
                                                (Etempvar _bDistance tuint)
                                                tuint))
                                            (Sset _t'6
                                              (Ecast (Etempvar _t'7 tuint)
                                                tuint))))
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _bDistance tuint)
                                                       (Etempvar _distance tuint)
                                                       tint)
                                          (Ssequence
                                            (Sset _t'8
                                              (Ecast
                                                (Ebinop Oadd
                                                  (Etempvar _distance tuint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tuint) tuint))
                                            (Sset _t'6
                                              (Ecast (Etempvar _t'8 tuint)
                                                tuint)))
                                          (Ssequence
                                            (Sset _t'8
                                              (Ecast
                                                (Etempvar _bDistance tuint)
                                                tuint))
                                            (Sset _t'6
                                              (Ecast (Etempvar _t'8 tuint)
                                                tuint)))))
                                      (Sset _t'9
                                        (Ecast (Etempvar _t'6 tuint) tuint)))
                                    (Sset _result (Etempvar _t'9 tuint)))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _cache (tptr tuint))
                                        (Etempvar _index tuint) (tptr tuint))
                                      tuint) (Etempvar _t'9 tuint))))))
                          Sskip)))))
                (Ssequence
                  (Scall None
                    (Evar _free (Tfunction Tnil tint
                                  {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
                    ((Etempvar _cache (tptr tuint)) :: nil))
                  (Sreturn (Some (Etempvar _result tuint))))))))))))
|}.

Definition f_levenshtein := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tschar)) :: (_b, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_length, tuint) :: (_bLength, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tuint cc_default))
      ((Etempvar _a (tptr tschar)) :: nil))
    (Sset _length (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tuint cc_default))
        ((Etempvar _b (tptr tschar)) :: nil))
      (Sset _bLength (Etempvar _t'2 tuint)))
    (Ssequence
      (Scall (Some _t'3)
        (Evar _levenshtein_n (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons tuint
                                   (Tcons (tptr tschar) (Tcons tuint Tnil))))
                               tuint cc_default))
        ((Etempvar _a (tptr tschar)) :: (Etempvar _length tuint) ::
         (Etempvar _b (tptr tschar)) :: (Etempvar _bLength tuint) :: nil))
      (Sreturn (Some (Etempvar _t'3 tuint))))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_strlen, Gfun(Internal f_strlen)) ::
 (_calloc,
   Gfun(External (EF_external "calloc"
                   (mksignature nil (Some AST.Tint)
                     {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
     Tnil tint {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|})) ::
 (_free,
   Gfun(External EF_free Tnil tint
     {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|})) ::
 (_levenshtein_n, Gfun(Internal f_levenshtein_n)) ::
 (_levenshtein, Gfun(Internal f_levenshtein)) :: nil).

Definition public_idents : list ident :=
(_levenshtein :: _levenshtein_n :: _free :: _calloc :: _strlen ::
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


