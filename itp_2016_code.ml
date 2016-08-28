(* ========================================================================= *)
(*---------------------------------------------------------------------------*)
(*                         Fourier Transform Theory                          *)
(*---------------------------------------------------------------------------*)
(*                                                                           *)
(*    (c)  Adnan Rashid & Osman Hasan	                                     *)
(*	   SYSTEM ANALYSIS & VERIFICATION (SAVe) LAB                         *)
(*	   National University of Sciences and Technology (NUST), PAKISTAN   *)
(*                                                                           *)
(* NOTE: This Script is written in HOL-Light (latest version) 
                                           in Linux Opearting System         *)
(*                                                                           *)
(* ========================================================================= *)


(*==================================================================*)
(*                         Theories to load                         *)
(*==================================================================*)

needs "Multivariate/realanalysis.ml";;
needs "Multivariate/cauchy.ml";; 

(*==================================================================*)
(*==================================================================*)
(*             Fourier Transform and Existence Condition            *)
(*==================================================================*)

(*--------Fourier Definition---------*)

let fourier_comp = new_definition
  `fourier_comp (f:real^1->complex) (w:real) = 
      (integral (:real^1) (\ (t:real^1). 
         (cexp(--((ii * Cx (w)) * Cx(drop(t)))) * (f t))))`;;

(*--------Fourier Existence condition---------*)

let fourier_exists = new_definition
  `fourier_exists (f:real^1->complex) =
   ((!a b. f piecewise_differentiable_on interval [lift a, lift b]) /\ 
   (f absolutely_integrable_on {x | &0 <= drop (x)}) /\
   (f absolutely_integrable_on {x | drop(x) <= &0}))`;;

(*==================================================================*)
(*==================================================================*)
(*                       Some Useful Theorems                       *)
(*==================================================================*)

g `{x | drop(x) <= &0} = IMAGE (--) {x | &0 <= drop(x)}`;;

e (REWRITE_TAC [EXTENSION; IN_UNION; IN_IMAGE; IN_UNIV; IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x (x':real^1). (x = --x' <=> --x = x')` ASSUME_TAC);;
e (VECTOR_ARITH_TAC);;
e (ASM_REWRITE_TAC []);;
e (POP_ASSUM (K ALL_TAC));;
e (STRIP_TAC);;
e (EQ_TAC);;
e (STRIP_TAC);;
e (EXISTS_TAC `-- x:real^1`);;
e (REWRITE_TAC [DROP_NEG]);;
e (POP_ASSUM MP_TAC);;
e (REAL_ARITH_TAC);;
e (REPEAT STRIP_TAC);;
e (ONCE_REWRITE_TAC [VECTOR_ARITH `x = -- (-- x:real^1)`]);;
e (ONCE_REWRITE_TAC [DROP_NEG]);;
e (ASM_REWRITE_TAC []);;
e (POP_ASSUM MP_TAC);;
e (REAL_ARITH_TAC);;

let NEG_REAL_INTERVAL_EQUIV = top_thm();;

(*------------------------------------------------------------------*)
(*                          UNIV_SET_BREAK                          *)
(*------------------------------------------------------------------*)

let UNIV_SET_BREAK = prove
 (`(:real^1) = ({x | &0 <= drop (x)} UNION IMAGE (--) {x | &0 <= drop(x)})`,
  REWRITE_TAC [EXTENSION; IN_UNION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
  SUBGOAL_THEN `!x (x':real^1). (x = --x' <=> --x = x')` ASSUME_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [UNWIND_THM1; DROP_NEG] THEN REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*                       INTEGRABLE_SPIKE_1                         *)
(*------------------------------------------------------------------*)

let INTEGRABLE_SPIKE_1 = prove
 (`!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        /\ f integrable_on t ==> g integrable_on t`,
  REWRITE_TAC[integrable_on] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `y:real^N` THEN
  MP_TAC(SPEC_ALL HAS_INTEGRAL_SPIKE) THEN ASM_REWRITE_TAC[]);;

(*------------------------------------------------------------------*)
(*                       INTEGRABLE_UNION                           *)
(*------------------------------------------------------------------*)

let INTEGRABLE_UNION = prove
 (`!f:real^M->real^N s t.
        f integrable_on s /\ f integrable_on t /\ negligible(s INTER t)
        ==> f integrable_on (s UNION t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [GSYM INTEGRABLE_RESTRICT_UNIV] THEN
  REWRITE_TAC [CONJ_ASSOC] THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC INTEGRABLE_SPIKE_1 THEN
  EXISTS_TAC
    `(\x. if x IN (s INTER t) then &2 % f(x)
                   else if x IN (s UNION t) then f(x)
                   else vec 0):real^M->real^N` THEN
  EXISTS_TAC `s INTER t:real^M->bool` THEN
  ASM_REWRITE_TAC [IN_DIFF; IN_UNION; IN_INTER; IN_UNIV] THEN CONJ_TAC THENL
   [MESON_TAC []; ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP INTEGRABLE_ADD) THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(x:real^M) IN t`] THEN
  ASM_REWRITE_TAC [] THEN VECTOR_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*            INTEGRABLE_POS_NEG_IMP_INTEGRABLE_WHOLE               *)
(*------------------------------------------------------------------*)

let INTEGRABLE_POS_NEG_IMP_INTEGRABLE_WHOLE = prove
 (`!f:real^1->real^2.
       (f integrable_on {x | &0 <= drop (x)}) /\
   (f integrable_on (IMAGE (--) {x | &0 <= drop(x)}))
        ==> f integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [UNIV_SET_BREAK] 
  THEN MATCH_MP_TAC INTEGRABLE_UNION THEN
  ASM_SIMP_TAC [] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{(vec 0):real^1}` THEN
  REWRITE_TAC
    [NEGLIGIBLE_SING; IN_ELIM_THM;
     SET_RULE
       `s INTER IMAGE f s SUBSET {a} <=> !x. x IN s /\ f x IN s ==> f x = a`] THEN
  REWRITE_TAC [GSYM LIFT_NUM; DROP_NEG] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM DROP_EQ; LIFT_DROP; DROP_NEG] THEN ASM_REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*          ABS_INTEGRABLE_POS_NEG_IMP_INTEGRABLE_WHOLE             *)
(*------------------------------------------------------------------*)

let ABS_INTEGRABLE_POS_NEG_IMP_INTEGRABLE_WHOLE = prove
 (`!f:real^1->real^2.
       (f absolutely_integrable_on {x | &0 <= drop (x)}) /\
   (f absolutely_integrable_on (IMAGE (--) {x | &0 <= drop(x)}))
        ==> f absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [UNIV_SET_BREAK] 
  THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_UNION THEN
  ASM_SIMP_TAC [] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{(vec 0):real^1}` THEN
  REWRITE_TAC
    [NEGLIGIBLE_SING; IN_ELIM_THM;
     SET_RULE
       `s INTER IMAGE f s SUBSET {a} <=> !x. x IN s /\ f x IN s ==> f x = a`] THEN
  REWRITE_TAC [GSYM LIFT_NUM; DROP_NEG] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM DROP_EQ; LIFT_DROP; DROP_NEG] THEN ASM_REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*                       INTEGRAL_UNIV_BREAK                        *)
(*------------------------------------------------------------------*)

let INTEGRAL_UNIV_BREAK = prove
 (`!f:real^1->real^2.
       (f absolutely_integrable_on {x | &0 <= drop (x)}) /\
   (f absolutely_integrable_on (IMAGE (--) {x | &0 <= drop(x)}))
        ==> integral (:real^1) f =
	integral {t | &0 <= drop t} f +
	integral (IMAGE (--) {t | &0 <= drop t}) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [UNIV_SET_BREAK] 
  THEN MATCH_MP_TAC INTEGRAL_UNION THEN
  REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC [absolutely_integrable_on] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{(vec 0):real^1}` THEN
  REWRITE_TAC
    [NEGLIGIBLE_SING; IN_ELIM_THM;
     SET_RULE
       `s INTER IMAGE f s SUBSET {a} <=> !x. x IN s /\ f x IN s ==> f x = a`] THEN
  REWRITE_TAC [GSYM LIFT_NUM; DROP_NEG] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM DROP_EQ; LIFT_DROP; DROP_NEG] THEN ASM_REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*                      INTEGRAL_UNIV_BREAK_1                       *)
(*------------------------------------------------------------------*)

let INTEGRAL_UNIV_BREAK_1 = prove
 (`!f:real^1->real^2.
       (f integrable_on {x | &0 <= drop (x)}) /\
   (f integrable_on (IMAGE (--) {x | &0 <= drop(x)}))
        ==> integral (:real^1) f =
	integral {t | &0 <= drop t} f +
	integral (IMAGE (--) {t | &0 <= drop t}) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [UNIV_SET_BREAK] 
  THEN MATCH_MP_TAC INTEGRAL_UNION THEN
  ASM_SIMP_TAC [] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{(vec 0):real^1}` THEN
  REWRITE_TAC
    [NEGLIGIBLE_SING; IN_ELIM_THM;
     SET_RULE
       `s INTER IMAGE f s SUBSET {a} <=> !x. x IN s /\ f x IN s ==> f x = a`] THEN
  REWRITE_TAC [GSYM LIFT_NUM; DROP_NEG] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM DROP_EQ; LIFT_DROP; DROP_NEG] THEN ASM_REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*                        LINEAR_CX_DROP                            *)
(*------------------------------------------------------------------*)

let LINEAR_CX_DROP = prove
 (`linear(Cx o drop)`,
  SIMP_TAC[linear; o_THM; COMPLEX_CMUL; DROP_ADD;CX_ADD; CX_ADD;DROP_CMUL; CX_MUL]);;

(*------------------------------------------------------------------*)
(*                       CONTINUOUS_ON_CX_DROP                      *)
(*------------------------------------------------------------------*)

let CONTINUOUS_ON_CX_DROP = prove
 (`!s. (Cx o drop) continuous_on s`,
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_CX_DROP]);;

(*------------------------------------------------------------------*)
(*                  INTEGRABLE_LIM_AT_POSINFINITY                   *)
(*------------------------------------------------------------------*)

let INTEGRABLE_LIM_AT_POSINFINITY = prove
 (`!f. (f integrable_on {t | &0 <= drop t}) <=>
        (!a. f integrable_on interval[vec 0,a]) /\
        ?(l:real^2). ((\a. integral (interval[vec 0,lift a]) f) --> l) at_posinfinity`,
  REPEAT GEN_TAC THEN REWRITE_TAC [integrable_on] THEN EQ_TAC THENL
   [STRIP_TAC THEN REWRITE_TAC [GSYM integrable_on] THEN CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_ALT] THEN
      REWRITE_TAC [INTEGRAL_RESTRICT_INTER; INTEGRABLE_RESTRICT_INTER] THEN
      SUBGOAL_THEN
        `!a b. {t | &0 <= drop t} INTER interval[a,b] =
          interval[lift(max (&0) (drop a)),b]`
        (fun th -> REWRITE_TAC [th]) THENL
       [REWRITE_TAC
          [EXTENSION; FORALL_LIFT; IN_INTER; IN_INTERVAL_1; LIFT_DROP;
           IN_ELIM_THM] THEN
        REAL_ARITH_TAC;
        STRIP_TAC THEN X_GEN_TAC `a:real^1` THEN
        FIRST_X_ASSUM (MP_TAC o SPECL [`vec 0:real^1`; `a:real^1`]) THEN
        REWRITE_TAC [DROP_VEC; LIFT_NUM; REAL_ARITH `max x x = x`]];
      EXISTS_TAC `y:complex` THEN POP_ASSUM MP_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_ALT] THEN
      REWRITE_TAC [INTEGRAL_RESTRICT_INTER; INTEGRABLE_RESTRICT_INTER] THEN
      SUBGOAL_THEN
        `!a b. {t | &0 <= drop t} INTER interval[a,b] =
          interval[lift(max (&0) (drop a)),b]`
        (fun th -> REWRITE_TAC [th]) THENL
       [REWRITE_TAC
          [EXTENSION; FORALL_LIFT; IN_INTER; IN_INTERVAL_1; LIFT_DROP;
           IN_ELIM_THM] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC [LIM_AT_POSINFINITY; dist; real_ge] THEN STRIP_TAC THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
      X_GEN_TAC `b:real` THEN DISCH_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPECL [`lift(--b)`; `lift b`]) THEN
      REWRITE_TAC [DROP_VEC; LIFT_NUM; LIFT_DROP] THEN
      SUBGOAL_THEN `max (&0) (--b) = &0` SUBST1_TAC THENL
       [ALL_TAC;
        REWRITE_TAC [LIFT_NUM] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC [BALL_1; SUBSET_INTERVAL_1] THEN
        REWRITE_TAC [DROP_ADD; DROP_SUB; DROP_VEC; LIFT_DROP]] THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC [GSYM integrable_on] THEN STRIP_TAC THEN
    REWRITE_TAC [integrable_on] THEN EXISTS_TAC `l:complex` THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [HAS_INTEGRAL_ALT] THEN
    REWRITE_TAC [INTEGRAL_RESTRICT_INTER; INTEGRABLE_RESTRICT_INTER] THEN
    SUBGOAL_THEN
      `!a b. {t | &0 <= drop t} INTER interval[a,b] =
          interval[lift(max (&0) (drop a)),b]`
      (fun th -> REWRITE_TAC [th]) THENL
     [REWRITE_TAC
        [EXTENSION; FORALL_LIFT; IN_INTER; IN_INTERVAL_1; LIFT_DROP;
         IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC [LIM_AT_POSINFINITY; dist; real_ge] THEN STRIP_TAC THEN
    REWRITE_TAC [LIFT_NUM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `b:real^1`) THEN
      MATCH_MP_TAC (REWRITE_RULE [IMP_CONJ_ALT] INTEGRABLE_SUBINTERVAL) THEN
      SIMP_TAC [SUBSET_INTERVAL_1; DROP_ADD; DROP_SUB; DROP_VEC; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN `B:real` (LABEL_TAC "*")) THEN
      EXISTS_TAC `abs B + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN
      REWRITE_TAC [BALL_1; SUBSET_INTERVAL_1] THEN
      REWRITE_TAC [DROP_ADD; DROP_SUB; DROP_VEC; LIFT_DROP] THEN STRIP_TAC THENL
       [ALL_TAC;
        SUBGOAL_THEN `max (&0) (drop a) = &0` SUBST1_TAC THENL
         [ALL_TAC;
          REWRITE_TAC [LIFT_NUM] THEN FIRST_X_ASSUM (MP_TAC o SPEC `drop b`) THEN
          REWRITE_TAC [LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC]] THEN
      ASM_REAL_ARITH_TAC]]);;

(*------------------------------------------------------------------*)
(*              PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV             *)
(*------------------------------------------------------------------*)

let PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV = prove
 (`!(f:real^1->complex) c. 
   (!a b. f piecewise_differentiable_on interval [lift a,lift b]) 
       ==>
   f piecewise_differentiable_on interval [lift (&0),lift c]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET THEN
  EXISTS_TAC `interval [-- lift c,lift c]` THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN (MP_TAC o SPEC `-- c:real`) THEN
  DISCH_THEN (MP_TAC o SPEC `c:real`) THEN SIMP_TAC [LIFT_NEG] THEN 
  DISCH_TAC THEN
  REWRITE_TAC [SUBSET; IN_INTERVAL_1; DROP_NEG; LIFT_DROP] THEN
  REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*                  CONTINUOUS_ON_SUBSET_UNIV                       *)
(*------------------------------------------------------------------*)

let CONTINUOUS_ON_SUBSET_UNIV = prove
 (`!(f:real^1->complex) c. 
   (!a b. f continuous_on interval [lift a,lift b]) 
       ==>
   f continuous_on interval [lift (&0),lift c]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval [-- lift c,lift c]` THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN (MP_TAC o SPEC `-- c:real`) THEN
  DISCH_THEN (MP_TAC o SPEC `c:real`) THEN SIMP_TAC [LIFT_NEG] THEN 
  DISCH_TAC THEN
  REWRITE_TAC [SUBSET; IN_INTERVAL_1; DROP_NEG; LIFT_DROP] THEN
  REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*                  ABS_REAL_CONTINUOUS_ATREAL                      *)
(*------------------------------------------------------------------*)

let ABS_REAL_CONTINUOUS_ATREAL = prove
 (`!x. abs real_continuous (atreal x)`,
  REWRITE_TAC[real_continuous_atreal] THEN
  GEN_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*                  ABS_REAL_CONTINUOUS_WITHIN                      *)
(*------------------------------------------------------------------*)

let ABS_REAL_CONTINUOUS_WITHIN = prove
 (`!s x. abs real_continuous (atreal x within s)`,
  MESON_TAC[ABS_REAL_CONTINUOUS_ATREAL; REAL_CONTINUOUS_ATREAL_WITHINREAL]);;

(*------------------------------------------------------------------*)
(*                   CEXP_S_T_CONTINUOUS_COMPOSE                    *)
(*------------------------------------------------------------------*)

let CEXP_S_T_CONTINUOUS_COMPOSE = prove
 (`! (s:complex) (t:real^1) (b:real) (x:real).
    (\t. cexp (--(s * Cx t))) continuous atreal x within real_interval [&0,b]`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `!t. ( cexp (--(s * Cx((t))))) =
		(\t. cexp ((\t. (--(s * Cx((t))))) t)) t`
    ASSUME_TAC THENL
   [GEN_TAC THEN SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN
  REWRITE_TAC [REAL_CONTINUOUS_WITHIN_ID] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_WITHINREAL_COMPOSE THEN
  REWRITE_TAC [CONTINUOUS_WITHIN_CEXP] THEN
  REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC [CONTINUOUS_CONST] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN `(Cx x) = Cx (drop (lift x) )` ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_WITHIN THEN
  REWRITE_TAC [LINEAR_CX_DROP]);;

(*------------------------------------------------------------------*)
(*                    ABS_RE_REAL_FOURIER_INTEGRABLE                *)
(*------------------------------------------------------------------*)
 
let ABS_RE_REAL_FOURIER_INTEGRABLE = prove
 (`!f:real^1->complex w:real b:real .
    fourier_exists f ==>(\x. abs (Re (cexp (--((ii * Cx w) * Cx x)) * f (lift x)))) real_integrable_on real_interval [&0, b]`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
   REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  SUBGOAL_THEN
    `abs o Re o (\x. cexp (--((ii * Cx w) * Cx x)) * f (lift x)) =
   (abs o Re) o (\x. cexp (--((ii * Cx w) * Cx x)) * (f:real^1->complex) (lift x))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN SIMP_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_COMPOSE THEN
    REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN] THEN
    REWRITE_TAC [ABS_REAL_CONTINUOUS_WITHIN]] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
  REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN
    `(f:real^1->complex) (lift x) = 
   f (lift (drop (lift x) ) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [LIFT_DROP] THEN
  SUBGOAL_THEN
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
   (real_interval [&0,b])`
    ASSUME_TAC THENL
   [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
    REWRITE_TAC
      [SET_RULE
         `IMAGE (\x. x) (interval [lift (&0),lift b])
   = (interval [lift (&0),lift b])`] THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV;
    REWRITE_TAC [CONTINUOUS_WITHIN] THEN
    UNDISCH_TAC
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
   (real_interval [&0,b])` THEN
    REWRITE_TAC [CONTINUOUS_ON] THEN
    DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
    ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
    ONCE_ASM_REWRITE_TAC [LIFT_DROP]] THEN
  ASM_SIMP_TAC []);;

(*------------------------------------------------------------------*)
(*                    ABS_IM_REAL_FOURIER_INTEGRABLE                *)
(*------------------------------------------------------------------*)

let ABS_IM_REAL_FOURIER_INTEGRABLE = prove
 (`! f:real^1->complex w:real b.
  fourier_exists f ==>
  (\x. abs (Im (cexp (--((ii * Cx w) * Cx x)) * f (lift x)))) real_integrable_on real_interval [&0, b]`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
   REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  SUBGOAL_THEN
    `abs o Im o (\x. cexp (--((ii * Cx w) * Cx x)) * f (lift x)) =
  		(abs o Im) o (\x. cexp (--((ii * Cx w) * Cx x)) * f (lift x))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN SIMP_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_COMPOSE THEN
    REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN] THEN
    REWRITE_TAC [ABS_REAL_CONTINUOUS_WITHIN]] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
  REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN
    `(f:real^1->complex) (lift x) = 
    f (lift (drop (lift x) ) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [LIFT_DROP] THEN
  SUBGOAL_THEN
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
    (real_interval [&0,b])`
    ASSUME_TAC THENL
   [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
    REWRITE_TAC
      [SET_RULE
         `IMAGE (\x. x) (interval [lift (&0),lift b])
    = (interval [lift (&0),lift b])`] THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV;
    REWRITE_TAC [CONTINUOUS_WITHIN] THEN
    UNDISCH_TAC
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
    (real_interval [&0,b])` THEN
    REWRITE_TAC [CONTINUOUS_ON] THEN
    DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
    ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
    ONCE_ASM_REWRITE_TAC [LIFT_DROP]] THEN
  ASM_SIMP_TAC []);;

(*------------------------------------------------------------------*)
(*                  CEXP_S_T_CONTINUOUS_COMPOSE_1                   *)
(*------------------------------------------------------------------*)

let CEXP_S_T_CONTINUOUS_COMPOSE_1 = prove
 (`! (s:complex) (b:real) (x:real).
    (\t. cexp (--(s * Cx t))) continuous atreal x within real_interval [--b,&0]`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `!t. ( cexp (--(s * Cx((t))))) =
		(\t. cexp ((\t. (--(s * Cx((t))))) t)) t`
    ASSUME_TAC THENL
   [GEN_TAC THEN SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN
  REWRITE_TAC [REAL_CONTINUOUS_WITHIN_ID] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_WITHINREAL_COMPOSE THEN
  REWRITE_TAC [CONTINUOUS_WITHIN_CEXP] THEN
  REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC [CONTINUOUS_CONST] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN `(Cx x) = Cx (drop (lift x) )` ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_WITHIN THEN
  REWRITE_TAC [LINEAR_CX_DROP]);;

(*------------------------------------------------------------------*)
(*         PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV          *)
(*------------------------------------------------------------------*)

let PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV = prove
 (`!(f:real^1->complex) c. 
   (!a b. f piecewise_differentiable_on interval [lift a,lift b]) 
       ==>
   f piecewise_differentiable_on interval [lift (-- c),lift (&0)]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET THEN
  EXISTS_TAC `interval [-- lift c,lift c]` THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN (MP_TAC o SPEC `-- c:real`) THEN
  DISCH_THEN (MP_TAC o SPEC `c:real`) THEN SIMP_TAC [LIFT_NEG] THEN DISCH_TAC THEN
  REWRITE_TAC [SUBSET; IN_INTERVAL_1; DROP_NEG; LIFT_DROP] THEN
  REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*               CONTINUOUS_ON_SUBSET_REFLECT_UNIV                  *)
(*------------------------------------------------------------------*)

let CONTINUOUS_ON_SUBSET_REFLECT_UNIV = prove
 (`!(f:real^1->complex) c. 
   (!a b. f continuous_on interval [lift a,lift b]) 
       ==>
   f continuous_on interval [lift (-- c),lift (&0)]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval [-- lift c,lift c]` THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN (MP_TAC o SPEC `-- c:real`) THEN
  DISCH_THEN (MP_TAC o SPEC `c:real`) THEN SIMP_TAC [LIFT_NEG] THEN DISCH_TAC THEN
  REWRITE_TAC [SUBSET; IN_INTERVAL_1; DROP_NEG; LIFT_DROP] THEN
  REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*               RE_REAL_FOURIER_INTEGRABLE_REFLECT                 *)
(*------------------------------------------------------------------*)

let RE_REAL_FOURIER_INTEGRABLE_REFLECT = prove
 (`! f:real^1->complex w:real  b:real .
    fourier_exists f ==> (\x. Re (cexp (--((ii * Cx w) * Cx (--x))) * f (lift (--x)))) real_integrable_on real_interval [&0, b]`,
  SUBGOAL_THEN
    `!f w b.(\x. (Re (cexp (--((ii * Cx w) * Cx (--x))) * (f:real^1->complex) (lift (--x))))) = (\x. (\x. (Re (cexp (--((ii * Cx w) * Cx x)) * f (lift x)))) (--x))`
    ASSUME_TAC THENL
   [SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [REAL_INTEGRABLE_REFLECT_GEN] THEN 
   REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(IMAGE (--) (real_interval [&0,b])) = (real_interval [--b,(&0)])`
    ASSUME_TAC THENL
   [REWRITE_TAC [EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [ALL_TAC;
      ALL_TAC;
      EXISTS_TAC `--(x:real)` THEN STRIP_TAC THENL
       [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN]] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL 
  THEN REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE_1] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN
    `(f:real^1->complex) (lift x) = 
    f (lift (drop (lift x) ) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [LIFT_DROP] THEN
  SUBGOAL_THEN
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [--b,(&0)])`
    ASSUME_TAC THENL
   [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
    REWRITE_TAC
      [SET_RULE
         `IMAGE (\x. x) (interval [lift (--b),lift (&0)])
     = (interval [lift (--b),lift (&0)])`] THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV;
    REWRITE_TAC [CONTINUOUS_WITHIN] THEN
    UNDISCH_TAC
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [--b,(&0)])` THEN
    REWRITE_TAC [CONTINUOUS_ON] THEN
    DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
    ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
    ONCE_ASM_REWRITE_TAC [LIFT_DROP]] THEN
  ASM_SIMP_TAC []);;

(*------------------------------------------------------------------*)
(*             ABS_RE_REAL_FOURIER_INTEGRABLE_REFLECT               *)
(*------------------------------------------------------------------*)

let ABS_RE_REAL_FOURIER_INTEGRABLE_REFLECT = prove
 (`!f:real^1->complex w:real b:real .
    fourier_exists f ==>(\x. abs (Re (cexp (--((ii * Cx w) * Cx (--x))) * f (lift (--x))))) real_integrable_on real_interval [&0, b]`,
  SUBGOAL_THEN
    `!f w b.(\x. abs (Re (cexp (--((ii * Cx w) * Cx (--x))) * (f:real^1->complex) (lift (--x))))) = (\x. (\x. abs (Re (cexp (--((ii * Cx w) * Cx x)) * f (lift x)))) (--x))`
    ASSUME_TAC THENL
   [SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [REAL_INTEGRABLE_REFLECT_GEN] THEN 
    REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(IMAGE (--) (real_interval [&0,b])) = (real_interval [--b,(&0)])`
    ASSUME_TAC THENL
   [REWRITE_TAC [EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [ALL_TAC;
      ALL_TAC;
      EXISTS_TAC `--(x:real)` THEN STRIP_TAC THENL
       [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  SUBGOAL_THEN
    `abs o Re o (\x. cexp (--((ii * Cx w) * Cx x)) * f (lift x)) =
   (abs o Re) o (\x. cexp (--((ii * Cx w) * Cx x)) * (f:real^1->complex) (lift x))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN SIMP_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_COMPOSE THEN
    REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN] THEN
    REWRITE_TAC [ABS_REAL_CONTINUOUS_WITHIN]] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN 
  REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE_1] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN
    `(f:real^1->complex) (lift x) = 
   f (lift (drop (lift x) ) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [LIFT_DROP] THEN
  SUBGOAL_THEN
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
   (real_interval [--b,(&0)])`
    ASSUME_TAC THENL
   [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
    REWRITE_TAC
      [SET_RULE
         `IMAGE (\x. x) (interval [lift (--b),lift (&0)])
   = (interval [lift (--b),lift (&0)])`] THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV;
    REWRITE_TAC [CONTINUOUS_WITHIN] THEN
    UNDISCH_TAC
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
   (real_interval [--b,(&0)])` THEN
    REWRITE_TAC [CONTINUOUS_ON] THEN
    DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
    ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
    ONCE_ASM_REWRITE_TAC [LIFT_DROP]] THEN
  ASM_SIMP_TAC []);;

(*------------------------------------------------------------------*)
(*             ABS_IM_REAL_FOURIER_INTEGRABLE_REFLECT               *)
(*------------------------------------------------------------------*)

let ABS_IM_REAL_FOURIER_INTEGRABLE_REFLECT = prove
 (`!f:real^1->complex w:real b.
  fourier_exists f ==>
  (\x. abs (Im (cexp (--((ii * Cx w) * Cx (--x))) * f (lift (--x))))) real_integrable_on real_interval [&0, b]`,
  SUBGOAL_THEN
    `!f w b.(\x. abs (Im (cexp (--((ii * Cx w) * Cx (--x))) * (f:real^1->complex) (lift (--x))))) = (\x. (\x. abs (Im (cexp (--((ii * Cx w) * Cx x)) * f (lift x)))) (--x))`
    ASSUME_TAC THENL
   [SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [REAL_INTEGRABLE_REFLECT_GEN] THEN 
   REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(IMAGE (--) (real_interval [&0,b])) = (real_interval [--b,(&0)])`
    ASSUME_TAC THENL
   [REWRITE_TAC [EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [ALL_TAC;
      ALL_TAC;
      EXISTS_TAC `--(x:real)` THEN STRIP_TAC THENL
       [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  SUBGOAL_THEN
    `abs o Im o (\x. cexp (--((ii * Cx w) * Cx x)) * f (lift x)) =
  		(abs o Im) o (\x. cexp (--((ii * Cx w) * Cx x)) * f (lift x))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN SIMP_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_COMPOSE THEN
    REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN] THEN
    REWRITE_TAC [ABS_REAL_CONTINUOUS_WITHIN]] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN 
  REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE_1] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN
    `(f:real^1->complex) (lift x) = 
   f (lift (drop (lift x) ) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [LIFT_DROP] THEN
  SUBGOAL_THEN
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
   (real_interval [--b,(&0)])`
    ASSUME_TAC THENL
   [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
    REWRITE_TAC
      [SET_RULE
         `IMAGE (\x. x) (interval [lift (--b),lift (&0)])
   = (interval [lift (--b),lift (&0)])`] THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV;
    REWRITE_TAC [CONTINUOUS_WITHIN] THEN
    UNDISCH_TAC
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
   (real_interval [--b,(&0)])` THEN
    REWRITE_TAC [CONTINUOUS_ON] THEN
    DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
    ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
    ONCE_ASM_REWRITE_TAC [LIFT_DROP]] THEN
  ASM_SIMP_TAC []);;

(*------------------------------------------------------------------*)
(*                   RE_REAL_FOURIER_INTEGRABLE                     *)
(*------------------------------------------------------------------*)

let RE_REAL_FOURIER_INTEGRABLE = prove
 (`!f:real^1->complex w:real  b:real .
    fourier_exists f ==> (\x. Re (cexp (--((ii * Cx w) * Cx x)) * f (lift x))) real_integrable_on real_interval [&0, b]`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
    REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN]] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
  REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN
    `(f:real^1->complex) (lift x) = 
    f (lift (drop (lift x) ) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [LIFT_DROP] THEN
  SUBGOAL_THEN
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])`
    ASSUME_TAC THENL
   [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
    REWRITE_TAC
      [SET_RULE
         `IMAGE (\x. x) (interval [lift (&0),lift b])
     = (interval [lift (&0),lift b])`] THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV;
    REWRITE_TAC [CONTINUOUS_WITHIN] THEN
    UNDISCH_TAC
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])` THEN
    REWRITE_TAC [CONTINUOUS_ON] THEN
    DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
    ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
    ONCE_ASM_REWRITE_TAC [LIFT_DROP]] THEN
  ASM_SIMP_TAC []);;

(*------------------------------------------------------------------*)
(*              IM_REAL_FOURIER_INTEGRABLE_REFLECT                  *)
(*------------------------------------------------------------------*)

let IM_REAL_FOURIER_INTEGRABLE_REFLECT = prove
 (`!(f:real^1->complex) w:real b:real .
    fourier_exists f ==>
     (\x. Im (cexp (--((ii * Cx w) * Cx (--x))) * f (lift (--x)))) real_integrable_on real_interval [(&0), b]`,
  SUBGOAL_THEN
    `!f w b.(\x. (Im (cexp (--((ii * Cx w) * Cx (--x))) * (f:real^1->complex) (lift (--x))))) = (\x. (\x. (Im (cexp (--((ii * Cx w) * Cx x)) * f (lift x)))) (--x))`
    ASSUME_TAC THENL
   [SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [REAL_INTEGRABLE_REFLECT_GEN] THEN 
   REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(IMAGE (--) (real_interval [&0,b])) = (real_interval [--b,(&0)])`
    ASSUME_TAC THENL
   [REWRITE_TAC [EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [ALL_TAC;
      ALL_TAC;
      EXISTS_TAC `--(x:real)` THEN STRIP_TAC THENL
       [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN]] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN 
  REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE_1] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN `(f:real^1->complex) (lift x) = f (lift (drop (lift x) ) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [LIFT_DROP] THEN
  SUBGOAL_THEN
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
        (real_interval [--b,(&0)])`
    ASSUME_TAC THENL
   [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
    REWRITE_TAC
      [SET_RULE
         `IMAGE (\x. x) (interval [lift (--b),lift (&0)]) = (interval [lift (--b),lift (&0)])`] THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV;
    REWRITE_TAC [CONTINUOUS_WITHIN] THEN
    UNDISCH_TAC
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
        (real_interval [--b,(&0)])` THEN
    REWRITE_TAC [CONTINUOUS_ON] THEN
    DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
    ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
    ONCE_ASM_REWRITE_TAC [LIFT_DROP]] THEN
  ASM_SIMP_TAC []);;

(*------------------------------------------------------------------*)
(*                  IM_REAL_FOURIER_INTEGRABLE                      *)
(*------------------------------------------------------------------*)

let IM_REAL_FOURIER_INTEGRABLE = prove
 (`!(f:real^1->complex) w:real b:real .
    fourier_exists f ==>
     (\x. Im (cexp (--((ii * Cx w) * Cx x)) * f (lift x))) real_integrable_on real_interval [&0, b]`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
   REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN]] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
  REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN `(f:real^1->complex) (lift x) = f (lift (drop (lift x) ) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [LIFT_DROP] THEN
  SUBGOAL_THEN
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
        (real_interval [&0,b])`
    ASSUME_TAC THENL
   [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
    REWRITE_TAC
      [SET_RULE
         `IMAGE (\x. x) (interval [lift (&0),lift b]) = (interval [lift (&0),lift b])`] THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV;
    REWRITE_TAC [CONTINUOUS_WITHIN] THEN
    UNDISCH_TAC
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
        (real_interval [&0,b])` THEN
    REWRITE_TAC [CONTINUOUS_ON] THEN
    DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
    ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
    ONCE_ASM_REWRITE_TAC [LIFT_DROP]] THEN
  ASM_SIMP_TAC []);;

(*------------------------------------------------------------------*)
(*              HAS_INTEGRAL_LIM_AT_POSINFINITY_GEN                 *)
(*------------------------------------------------------------------*)

let HAS_INTEGRAL_LIM_AT_POSINFINITY_GEN = prove
 (`!f a l:real^N.
        (f has_integral l) {t | a <= drop t} <=>
        (!b. f integrable_on interval[lift a,lift b]) /\
        ((\b. integral (interval[lift a,lift b]) f) --> l) at_posinfinity`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `{t | a <= drop t} = IMAGE (\x. lift a + x) {t | &0 <= drop t}`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[IN_ELIM_THM; DROP_ADD; LIFT_DROP; REAL_LE_ADDR] THEN
    MESON_TAC[VECTOR_SUB_ADD2];
    REWRITE_TAC[GSYM HAS_INTEGRAL_TRANSLATION]] THEN
  REWRITE_TAC[HAS_INTEGRAL_LIM_AT_POSINFINITY] THEN
  REWRITE_TAC[INTEGRABLE_TRANSLATION; INTEGRAL_TRANSLATION] THEN
  REWRITE_TAC[GSYM INTERVAL_TRANSLATION; VECTOR_ADD_RID] THEN
  REWRITE_TAC[FORALL_LIFT; GSYM LIFT_ADD] THEN
  MP_TAC(MESON[REAL_SUB_ADD2] `!P. (!b:real. P(a + b)) <=> (!b. P b)`) THEN
  SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  DISCH_TAC THEN
  REWRITE_TAC[LIM_AT_POSINFINITY; real_ge] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real`) THEN EXISTS_TAC `abs a + abs b:real` THEN
  X_GEN_TAC `c:real` THEN DISCH_TAC THENL
   [SUBST1_TAC(REAL_ARITH `c:real = a + (c - a)`) THEN
    REWRITE_TAC[GSYM LIFT_ADD];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*             ABS_INTEG_IMP_NORM_FUN_POSINFINITY                   *)
(*------------------------------------------------------------------*)

let ABS_INTEG_IMP_NORM_FUN_POSINFINITY = prove
 (`!f:real^1->real^2 a.
        f absolutely_integrable_on {t | a <= drop t}
        ==> ?k. ((\b. real_integral (real_interval[a,b])
                                    (\t. norm(f(lift t))))
                 ---> k) at_posinfinity`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
    ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  REWRITE_TAC[HAS_INTEGRAL_LIM_AT_POSINFINITY_GEN] THEN
  SIMP_TAC[REAL_INTEGRAL; REAL_INTEGRABLE_ON; o_DEF; LIFT_DROP;
           IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[REAL_TENDSTO; o_DEF] THEN MESON_TAC[]);;

(*------------------------------------------------------------------*)
(*                  CEXP_S_T_CONTINUOUS_GEN                         *)
(*------------------------------------------------------------------*)

let CEXP_S_T_CONTINUOUS_GEN = prove
 (`! (a:complex) (t:real^1) s.
      (\t. cexp (--(a * Cx (drop t)))) continuous_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `!t. ( cexp (--(a * Cx(drop(t))))) =
		(\t. cexp ((\t. (--(a * Cx(drop(t))))) t)) t`
    ASSUME_TAC THENL
   [GEN_TAC THEN SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC [CONTINUOUS_ON_CEXP] THEN REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
  REWRITE_TAC [CONTINUOUS_ON_CONST] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  REWRITE_TAC [CONTINUOUS_ON_CX_DROP]);;

(*------------------------------------------------------------------*)
(*                      CEXP_S_T_CONTINUOUS                         *)
(*------------------------------------------------------------------*)

let CEXP_S_T_CONTINUOUS = prove
 (`! (s:complex) (t:real^1) (b:real^1).
      (\t. cexp (--(s * Cx (drop t)))) continuous_on interval [lift (&0),b]`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `!t. ( cexp (--(s * Cx(drop(t))))) =
		(\t. cexp ((\t. (--(s * Cx(drop(t))))) t)) t`
    ASSUME_TAC THENL
   [GEN_TAC THEN SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC [CONTINUOUS_ON_CEXP] THEN REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
  REWRITE_TAC [CONTINUOUS_ON_CONST] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  REWRITE_TAC [CONTINUOUS_ON_CX_DROP]);;

(*------------------------------------------------------------------*)
(*                     HAS_INTEGRAL_COMPLEX_MUL                     *)
(*------------------------------------------------------------------*)

let HAS_INTEGRAL_COMPLEX_MUL = prove
 (`!(f:real^1->complex) (k:complex) s (c:complex) .
      (f has_integral k) s ==> ((\x. z * (f(x) )) has_integral (z * k)) s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE [o_DEF] HAS_INTEGRAL_LINEAR) THEN
  ASM_REWRITE_TAC [linear] THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC [COMPLEX_CMUL]] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*                       INTEGRAL_COMPLEX_MUL                       *)
(*------------------------------------------------------------------*)

let INTEGRAL_COMPLEX_MUL = prove
 (`!f:real^1->complex c s.
     f integrable_on s ==> integral s (\x. c * f(x)) = c * integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_MUL THEN
  ASM_SIMP_TAC [INTEGRABLE_INTEGRAL]);;

(*------------------------------------------------------------------*)
(*                           VSUM_CX2                               *)
(*------------------------------------------------------------------*)

let VSUM_CX2 = prove
 (`!f:real^1#(real^1->bool)->real s:real^1#(real^1->bool)->bool.
   FINITE s ==> vsum s (\a :real^1#(real^1->bool) . Cx(f a)) = Cx(sum s f)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; COMPLEX_VEC_0; CX_ADD]);;

(*------------------------------------------------------------------*)
(*                          VSUM_LIFT2                              *)
(*------------------------------------------------------------------*)

let VSUM_LIFT2 = prove
 (`!f:real^1#(real^1->bool)->real s:real^1#(real^1->bool)->bool.
  FINITE s ==> vsum s (\a :real^1#(real^1->bool) . lift (f a)) = lift (sum s f)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES;  LIFT_ADD; LIFT_NUM]);;

(*------------------------------------------------------------------*)
(*                     CX_HAS_REAL_INTERGRAL                        *)
(*------------------------------------------------------------------*)

let CX_HAS_REAL_INTERGRAL = prove
 (`! (f:real->real) (s:complex) (t:real)(l:real).
    (f has_real_integral (l) ) (real_interval [(&0),t])
     ==> ((\t:real^1. Cx (f (drop t ) ) ) has_integral Cx(l) ) (interval [lift (&0),lift t])`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `(f has_real_integral (l ) ) (real_interval [(&0),t]) <=>
       ((\t. lift (f (drop t))) has_integral lift ( l))
         (interval [lift (&0),lift t])`
    ASSUME_TAC THENL
   [REWRITE_TAC [has_real_integral] THEN REWRITE_TAC [o_DEF] THEN
    REWRITE_TAC [INTERVAL_REAL_INTERVAL] THEN REWRITE_TAC [LIFT_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN REWRITE_TAC [has_integral] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(e:real)`) THEN ASM_SIMP_TAC [] THEN
  STRIP_TAC THEN EXISTS_TAC `(d:real^1->real^1->bool)` THEN ASM_SIMP_TAC [] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(p:real^1#(real^1->bool)->bool)`) THEN
  ASM_SIMP_TAC [] THEN REWRITE_TAC [GSYM LIFT_CMUL] THEN STRIP_TAC THEN
  REWRITE_TAC [COMPLEX_CMUL] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  SUBGOAL_THEN
    `( (vsum (p:real^1#(real^1->bool)->bool)
   (\ (a:real^1#(real^1->bool)) . Cx ( (\ (a:real^1#(real^1->bool)). content (SND a) * f (drop (FST a) ))a ) ) ) = 
    (Cx (sum p (\ (a:real^1#(real^1->bool)). content (SND a) * (f:real->real) (drop (FST a)) ) ) ))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC VSUM_CX2 THEN MATCH_MP_TAC TAGGED_DIVISION_OF_FINITE THEN
    EXISTS_TAC `interval [lift (&0),lift t]` THEN ASM_SIMP_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `(\ (x,k). Cx ((\ (x:real^1,k:(real^1->bool)). content k * f (drop x) ) (x , k))) =
    (\(a:real^1#(real^1->bool)). Cx ((\a. content (SND a) * (f:real->real)  (drop (FST a) ) ) a))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
    SUBGOAL_THEN
      `(\(a:real^1#(real^1->bool)). Cx ((\a. content (SND a) *  (f:real->real) (drop (FST a) )) a)) x = 
    ( (\a. Cx ((\a. content (SND a) * f (drop (FST a)) ) a)) (FST x , SND x) )`
      ASSUME_TAC THENL
     [SIMP_TAC [FST; SND; PAIR]; ALL_TAC] THEN
    SUBGOAL_THEN
      `(\(x,k). Cx ((\(x,k). content k * (f:real->real) (drop x) ) (x,k))) (x:real^1#(real^1->bool)) = 
   ((\ (x,k). Cx ((\ (x,k). content k * f (drop x) ) (x,k))) (FST x , SND x) )`
      ASSUME_TAC THENL
     [PURE_ONCE_REWRITE_TAC [PAIR] THEN SIMP_TAC [];
      PURE_ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC [FST; SND]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `vsum p (\ (x:real^1,k:real^1->bool). Cx (content k * (f:real->real) (drop x) )) =
    vsum p (\ (x,k). Cx ((\ (x,k). content k * f (drop x) ) (x,k)))`
    ASSUME_TAC THENL
   [SIMP_TAC []; ALL_TAC] THEN
  PURE_ONCE_ASM_REWRITE_TAC [] THEN PURE_ONCE_ASM_REWRITE_TAC [] THEN
  PURE_ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CX_SUB] THEN
  REWRITE_TAC [COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN
    `( (vsum (p:real^1#(real^1->bool)->bool)
    (\ (a:real^1#(real^1->bool)) . lift ( (\ (a:real^1#(real^1->bool)). content (SND a) * f (drop (FST a) ) )a ) ) ) = 
     (lift (sum p (\ (a:real^1#(real^1->bool)). content (SND a) * (f:real->real) (drop (FST a)) ) ) ))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC VSUM_LIFT2 THEN MATCH_MP_TAC TAGGED_DIVISION_OF_FINITE THEN
    EXISTS_TAC `interval [lift (&0),lift t]` THEN ASM_SIMP_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `(\ (x,k). lift ((\ (x:real^1,k:(real^1->bool)). content k * f (drop x) ) (x , k))) =
     (\(a:real^1#(real^1->bool)). lift ((\a. content (SND a) * (f:real->real)  (drop (FST a))) a))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
    SUBGOAL_THEN
      `(\(a:real^1#(real^1->bool)). lift ((\a. content (SND a) *  (f:real->real) (drop (FST a) )) a)) x = 
    ( (\a. lift ((\a. content (SND a) * f (drop (FST a))) a)) (FST x , SND x) )`
      ASSUME_TAC THENL
     [SIMP_TAC [FST; SND; PAIR]; ALL_TAC] THEN
    SUBGOAL_THEN
      `(\(x,k). lift ((\(x,k). content k * (f:real->real) (drop x) ) (x,k))) (x:real^1#(real^1->bool)) = 
   ((\ (x,k). lift ((\ (x,k). content k * f (drop x)) (x,k))) (FST x , SND x) )`
      ASSUME_TAC THENL
     [PURE_ONCE_REWRITE_TAC [PAIR] THEN SIMP_TAC [];
      PURE_ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC [FST; SND]];
    SUBGOAL_THEN
      `vsum p (\ (x:real^1,k:real^1->bool). lift (content k * (f:real->real) (drop x) )) =
    vsum p (\ (x,k). lift ((\ (x,k). content k * f (drop x) ) (x,k)))`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    UNDISCH_TAC
      `norm (vsum (p:real^1#(real^1->bool)->bool)
     (\(x:real^1,k:real^1->bool). lift (content k *  (f:real->real) (drop x) )) - lift (l)) < e` THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN PURE_ONCE_ASM_REWRITE_TAC [] THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM LIFT_SUB] THEN
    REWRITE_TAC [NORM_LIFT]]);;

(*------------------------------------------------------------------*)
(*              REAL_CONVERGENT_BOUNDED_INCREASING_ALT              *)
(*------------------------------------------------------------------*)

let REAL_CONVERGENT_BOUNDED_INCREASING_ALT = prove
 (`! (f:real->real) b. (!m n. m <= n ==> f m <= f n)
    /\ (!n. abs(f n) <= b) ==> ?l. !e. &0 < e ==> ?N. !n. n >= N ==> abs(f n - l) < e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [real_ge] THEN
  MP_TAC (SPEC `\x. ?n. (f:real->real) n = x` REAL_COMPLETE) THEN
  REWRITE_TAC [] THEN ANTS_TAC THENL
   [ASM_MESON_TAC [REAL_ARITH `abs(x) <= b ==> x <= b`]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  UNDISCH_TAC `!M'. (!x. (?n. (f:real->real) n = x) ==> x <= M') ==> l <= M'` THEN
  DISCH_THEN (MP_TAC o SPEC `((l:real) - e)`) THEN
  ASM_MESON_TAC
    [REAL_ARITH `&0 < e ==> ~(l <= l - e)`;
     REAL_ARITH `x <= y /\ y <= l /\ ~(x <= l - e) ==> abs(y - l) < e`]);;

(*------------------------------------------------------------------*)
(*                        REAL_LE_EPS                               *)
(*------------------------------------------------------------------*)

let REAL_LE_EPS = prove
 (`!x y. (!e. &0 < e ==> x <= y + e) ==> x <= y`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(&0 < x - y)` ASSUME_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `~(&0 < x - y)` THEN
    SIMP_TAC [REAL_NOT_LT; REAL_LE_SUB_RADD; REAL_ADD_LID]] THEN
  STRIP_TAC THEN UNDISCH_TAC `!e. &0 < e ==> x <= y + e` THEN SIMP_TAC [] THEN
  SIMP_TAC [NOT_FORALL_THM] THEN SIMP_TAC [NOT_IMP] THEN
  SUBGOAL_THEN `!(a:real) b c . ~(a <= b + c) = c < a - b` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN SIMP_TAC [REAL_LT_SUB_LADD; REAL_NOT_LE] THEN
    MESON_TAC [REAL_ADD_SYM];
    ASM_SIMP_TAC [] THEN ASM_MESON_TAC [REAL_DOWN]]);;

(*------------------------------------------------------------------*)
(*                          abs_if1                                 *)
(*------------------------------------------------------------------*)

let abs_if1 = new_definition `
 !x. abs x = if &0 <= x then x else --x `;;

(*------------------------------------------------------------------*)
(*                      REAL_ABS_LE_POS                             *)
(*------------------------------------------------------------------*)

let REAL_ABS_LE_POS = prove
 (`!x y . (abs(x) <= y) ==>  ( x <= y)`,
  REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*                       REAL_NEG_ABS_EQ                            *)
(*------------------------------------------------------------------*)

let REAL_NEG_ABS_EQ = prove
 (`!x . (x < &0) ==>  (abs(x) = --(x) )`,
  REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*                        SEQ_MONO_LE                               *)
(*------------------------------------------------------------------*)

let SEQ_MONO_LE = prove
 (`!(f:real->real) x n k. (&0 <= n) /\ (!n m.(n <= m) ==> ( f n <= f (m) ))
      /\ ( (f ---> k) at_posinfinity ) ==>  f n <= k`,
  REPEAT GEN_TAC THEN REWRITE_TAC [REALLIM_AT_POSINFINITY] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_EPS THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(e:real)`) THEN ASM_SIMP_TAC [] THEN
  SIMP_TAC [real_ge] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`b:real`; `n:real`] REAL_LE_TOTAL) THEN STRIP_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `n:real`) THEN ASM_SIMP_TAC [] THEN
    ASM_REWRITE_TAC [abs_if1] THEN ASM_REWRITE_TAC [REAL_LE_SUB_LADD] THEN
    ASM_REWRITE_TAC [REAL_ADD_LID] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [REAL_LT_SUB_RADD] THEN STRIP_TAC THEN
      ASM_MESON_TAC [REAL_LT_LE; REAL_ADD_SYM];
      ASM_REWRITE_TAC [REAL_NEG_SUB] THEN ASM_REWRITE_TAC [REAL_LT_SUB_RADD] THEN
      STRIP_TAC THEN UNDISCH_TAC `~(k <= (f:real->real) n)` THEN
      ASM_REWRITE_TAC [REAL_NOT_LE] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `k:real` THEN
      ASM_MESON_TAC [REAL_LT_LE; REAL_LE_ADDR]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!(i:num). f ((b:real) - &i) <= k + (e : real)` ASSUME_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN REWRITE_TAC [REAL_SUB_RZERO] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(f:real->real) b` THEN CONJ_TAC THENL
     [UNDISCH_TAC `!n m. n <= m ==> (f:real->real) n <= f  m` THEN
      DISCH_THEN (MP_TAC o SPEC `n:real`) THEN
      DISCH_THEN (MP_TAC o SPEC `b:real`);
      ALL_TAC] THEN
    ASM_SIMP_TAC []] THEN
  INDUCT_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `b:real`) THEN
    SUBGOAL_THEN `b <= (b:real)` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN ASM_REWRITE_TAC [abs_if1] THEN
    SIMP_TAC [REAL_SUB_RZERO] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [REAL_LT_SUB_RADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(&0 <= (f:real->real) b - k)` THEN
    ASM_REWRITE_TAC [REAL_NOT_LE] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `abs((f:real->real) b - k) = --(f b - k)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_NEG_ABS_EQ THEN ASM_SIMP_TAC []; ALL_TAC] THEN
    ONCE_REWRITE_TAC [REAL_ADD_AC] THEN REWRITE_TAC [GSYM REAL_LE_SUB_RADD] THEN
    MATCH_MP_TAC REAL_ABS_LE_POS THEN ASM_SIMP_TAC [] THEN
    UNDISCH_TAC `--((f:real->real) b - k) < e` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `!n m. n <= m ==> (f:real->real) n <= f  m` THEN
    DISCH_THEN (MP_TAC o SPEC `( (b:real) - &(SUC (i:num)))`) THEN
    DISCH_THEN (MP_TAC o SPEC `(b:real) - &(SUC (i:num)) + &1`) THEN
    SUBGOAL_THEN `b - &(SUC i) <=  b - &(SUC i) + &1` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `n:real` THEN CONJ_TAC THENL
         [ASM_SIMP_TAC []; REAL_ARITH_TAC];
        REWRITE_TAC [GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC];
      ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN `( b - & (SUC i) ) + &1 = ( b - &i)` ASSUME_TAC THENL
       [REWRITE_TAC [GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(f:real->real)(b - &(SUC i) + &1)` THEN CONJ_TAC THEN
        ASM_SIMP_TAC []]]]);;

(*------------------------------------------------------------------*)
(*                     INTEGRAL_COMPARISON_TEST                     *)
(*------------------------------------------------------------------*)

let INTEGRAL_COMPARISON_TEST = prove
 (`!(f:real->real) (g:real->real) a. 
  (!x. a <= x ==> (&0 <= f x /\ f x <= g x)) /\ (&0 <= a) /\
    (!b. ( g real_integrable_on real_interval [a,b] ) ) /\
      (?k.( ( (\b. (real_integral (real_interval [a,b]) g) ) ---> k) at_posinfinity  ) )  /\
      (!b. ( f real_integrable_on real_interval [a,b] ) ) ==>
        (?k.( ( (\b. (real_integral (real_interval [a,b]) f) ) ---> k) at_posinfinity  ) )`,
  REWRITE_TAC [REALLIM_AT_POSINFINITY] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONVERGENT_BOUNDED_INCREASING_ALT THEN
  EXISTS_TAC `k:real` THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC (SPECL [`a:real`; `m:real`] REAL_LET_TOTAL) THEN
    REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN
        `real_integral (real_interval [a,x]) (f:real->real) =
      real_integral (real_interval [a,m]) f +
         real_integral (real_interval [m,x]) f`
        ASSUME_TAC THENL
       [REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
        ASM_SIMP_TAC [];
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [REAL_LE_ADDR] THEN
      SUBGOAL_THEN
        `(&0 <= real_integral (real_interval [m,x]) f) =
    ( ( real_integral (real_interval [m,x])  (\t. &0) ) <=
     real_integral (real_interval [m,x]) f )`
        ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTEGRAL_0]; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_INTEGRABLE_0]; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `!b. f real_integrable_on real_interval [a,b]` THEN
        DISCH_THEN (MP_TAC o SPEC `x:real`) THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN EXISTS_TAC `a:real` THEN
        EXISTS_TAC `x:real` THEN ASM_SIMP_TAC [] THEN
        REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN DISJ2_TAC THEN
        ASM_SIMP_TAC [] THEN REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN SIMP_TAC [] THEN
        SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m:real` THEN CONJ_TAC THENL
           [ASM_SIMP_TAC []; ALL_TAC] THEN
          SUBGOAL_THEN `(m:real) <= x'  /\ x' <= x` ASSUME_TAC THENL
           [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
          UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
          DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC []]];
      SUBGOAL_THEN `real_interval [a,m]= {}` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY] THEN ASM_MESON_TAC [REAL_LE_LT];
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [REAL_INTEGRAL_EMPTY] THEN
      SUBGOAL_THEN
        `(&0 <= real_integral (real_interval [a,x]) f) =
     ( ( real_integral (real_interval [a,x])  (\t. &0) ) <=
        real_integral (real_interval [a,x]) f )`
        ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTEGRAL_0]; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_INTEGRABLE_0]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC []; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      SIMP_TAC [] THEN SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
       [SUBGOAL_THEN `(a:real) <= x'  /\ x' <= x` ASSUME_TAC THENL
         [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
        UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
        DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC []]];
    ALL_TAC] THEN
  GEN_TAC THEN MP_TAC (SPECL [`a:real`; `x:real`] REAL_LET_TOTAL) THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a:real` THEN
      ASM_SIMP_TAC [];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `abs (real_integral (real_interval [a,x]) f) =
    (real_integral (real_interval [a,x]) f)`
      ASSUME_TAC THENL
     [REWRITE_TAC [REAL_ABS_REFL] THEN
      SUBGOAL_THEN
        `(&0 <= real_integral (real_interval [a,x]) f) =
     ( ( real_integral (real_interval [a,x])  (\t. &0) ) <=
        real_integral (real_interval [a,x]) f )`
        ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTEGRAL_0]; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_INTEGRABLE_0]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC []; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      SIMP_TAC [] THEN SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
       [SUBGOAL_THEN `(a:real) <= x'  /\ x' <= x` ASSUME_TAC THENL
         [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
        UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
        DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC []];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN
      `real_integral (real_interval [a,x]) (f:real->real) =
    (\t.real_integral (real_interval [a,t]) f ) x`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(\t. real_integral  (real_interval [a,t]) g) x` THEN CONJ_TAC THENL
     [SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_SIMP_TAC [] THEN
      REPEAT STRIP_TAC THEN SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
       [SUBGOAL_THEN `(a:real) <= x'  /\ x' <= x` ASSUME_TAC THENL
         [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
        UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
        DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC []];
      ALL_TAC] THEN
    MATCH_MP_TAC SEQ_MONO_LE THEN CONJ_TAC THENL [ASM_SIMP_TAC []; ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC
        `!e. &0 < e ==> (?b. !x. x >= b
       ==> abs (real_integral (real_interval [a,x]) g - k) < e)` THEN
      ASM_REWRITE_TAC [GSYM REALLIM_AT_POSINFINITY]] THEN
    REPEAT STRIP_TAC THEN SIMP_TAC [] THEN
    MP_TAC (SPECL [`a:real`; `n:real`] REAL_LET_TOTAL) THEN REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN
        `real_integral (real_interval [a,m]) (g:real->real) =
     real_integral (real_interval [a,n]) g +
       real_integral (real_interval [n,m]) g`
        ASSUME_TAC THENL
       [REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
        ASM_SIMP_TAC [];
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [REAL_LE_ADDR] THEN
      SUBGOAL_THEN
        `(&0 <= real_integral (real_interval [n,m]) g) =
  ( ( real_integral (real_interval [n,m])  (\t. &0) ) <=
    real_integral (real_interval [n,m]) g )`
        ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTEGRAL_0]; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_INTEGRABLE_0]; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `!b. g real_integrable_on real_interval [a,b]` THEN
        DISCH_THEN (MP_TAC o SPEC `m:real`) THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN EXISTS_TAC `a:real` THEN
        EXISTS_TAC `m:real` THEN ASM_SIMP_TAC [] THEN
        REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN DISJ2_TAC THEN
        ASM_SIMP_TAC [] THEN REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN SIMP_TAC [] THEN
        SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `n:real` THEN CONJ_TAC THENL
           [ASM_SIMP_TAC []; ALL_TAC] THEN
          SUBGOAL_THEN `(n:real) <= x'  /\ x' <= m` ASSUME_TAC THENL
           [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
          UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
          DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC [] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `(f:real->real) x'` THEN ASM_SIMP_TAC []]];
      SUBGOAL_THEN `real_interval [a,n]= {}` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY] THEN ASM_MESON_TAC [REAL_LE_LT];
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [REAL_INTEGRAL_EMPTY] THEN
      SUBGOAL_THEN
        `(&0 <= real_integral (real_interval [a,m]) g) =
   ( ( real_integral (real_interval [a,m])  (\t. &0) ) <=
      real_integral (real_interval [a,m]) g )`
        ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTEGRAL_0]; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_INTEGRABLE_0]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC []; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      SIMP_TAC [] THEN SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
       [SUBGOAL_THEN `(a:real) <= x'  /\ x' <= m` ASSUME_TAC THENL
         [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
        UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
        DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC [] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(f:real->real) x'` THEN ASM_SIMP_TAC []]];
    SUBGOAL_THEN `real_interval [a,x]= {}` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY] THEN ASM_SIMP_TAC []; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [REAL_INTEGRAL_EMPTY] THEN
    SIMP_TAC [REAL_ARITH `abs(&0) = &0`] THEN
    MP_TAC (SPECL [`k:real`; `&0`] REAL_LTE_TOTAL) THEN STRIP_TAC THEN
    MATCH_MP_TAC (REAL_ARITH `~(k < &0) ==> (&0 <= k)`) THEN ASM_SIMP_TAC [] THEN
    UNDISCH_TAC
      `!e. &0 < e ==> (?b. !x. x >= b
       ==> abs (real_integral (real_interval [a,x]) g - k) < e)` THEN
    DISCH_THEN (MP_TAC o SPEC `abs( k :real)/ &2`) THEN
    ASM_SIMP_TAC [REAL_ARITH `( (x < &0) ==> (&0 < (abs(x) / &2)) )`] THEN
    STRIP_TAC THEN
    UNDISCH_TAC
      `!x. x >= b ==> abs (real_integral (real_interval [a,x]) g - k) <  abs k / &2` THEN
    DISCH_THEN (MP_TAC o SPEC `b:real`) THEN
    ASM_REWRITE_TAC [REAL_ARITH `x >= x`] THEN REWRITE_TAC [REAL_NOT_LT] THEN
    MP_TAC (SPECL [`b:real`; `a:real`] REAL_LTE_TOTAL) THEN STRIP_TAC THENL
     [SUBGOAL_THEN `real_interval [a,b]= {}` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY] THEN ASM_SIMP_TAC [];
        ASM_SIMP_TAC [] THEN REWRITE_TAC [REAL_INTEGRAL_EMPTY] THEN
        SIMP_TAC [REAL_ARITH `abs(&0 - k) = abs(k)`] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SIMP_TAC [REAL_ARITH `(x:real) - y = x + --y`] THEN
    SUBGOAL_THEN `--k = abs(k)` ASSUME_TAC THENL
     [MATCH_MP_TAC (REAL_ARITH `(k < &0) ==> (--k = abs(k))`) THEN
      ASM_SIMP_TAC [];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN
      `real_integral (real_interval [a,b]) g =  
    abs(real_integral (real_interval [a,b]) g)`
      ASSUME_TAC THENL
     [ALL_TAC;
      SUBGOAL_THEN
        `abs (real_integral (real_interval [a,b]) g + abs k) = 
     abs (abs(real_integral (real_interval [a,b]) g) + abs k)`
        ASSUME_TAC THENL
       [ASM_MESON_TAC []; ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN
      SIMP_TAC [REAL_ARITH `abs( abs(x) + abs(y)) = abs(x) + abs(y)`] THEN
      SIMP_TAC [REAL_ARITH `(abs(x) / &2) <= ( abs(y) + abs(x))`]] THEN
    MATCH_MP_TAC (REAL_ARITH `(&0 <= x) ==> (x = abs(x))`) THEN
    SUBGOAL_THEN
      `(&0 <= real_integral (real_interval [a,b]) g) =
     ( ( real_integral (real_interval [a,b])  (\t. &0) ) <=
        real_integral (real_interval [a,b]) g )`
      ASSUME_TAC THENL
     [REWRITE_TAC [REAL_INTEGRAL_0]; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN CONJ_TAC THENL
     [REWRITE_TAC [REAL_INTEGRABLE_0]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC []; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC [] THEN SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
     [SUBGOAL_THEN `(a:real) <= x'  /\ x' <= b` ASSUME_TAC THENL
       [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
      UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
      DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC [] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(f:real->real) x'` THEN ASM_SIMP_TAC []]]);;

(*------------------------------------------------------------------*)
(*                        REAL_LE_POW_ADD_2                         *)
(*------------------------------------------------------------------*)

let REAL_LE_POW_ADD_2 = prove
 (`!x y. &0 <= (x - y) pow 2`,
  REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]);;

(*------------------------------------------------------------------*)
(*                        REAL_LT_ADD2_SYM                          *)
(*------------------------------------------------------------------*)

let REAL_LT_ADD2_SYM = prove
 (`!x y z. x < z /\ y < z ==> (x + y) < (&2 * z)`,
  REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*                    LIM_COMPLEX_REAL_COMPONENTS                   *)
(*------------------------------------------------------------------*)

let LIM_COMPLEX_REAL_COMPONENTS = prove
 (`!(f:real->complex) (L1:real) (L2:real). 
    ( ( (\t. Re (f t) ) ---> L1) at_posinfinity )  /\
     ( ( (\t. Im (f t) ) ---> L2) at_posinfinity ) ==>
        (  ( f --> complex(L1, L2) ) at_posinfinity )`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [REALLIM_AT_POSINFINITY; LIM_AT_POSINFINITY] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(e:real)* inv (sqrt(&2))`) THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(e:real)* inv (sqrt(&2))`) THEN
  SUBGOAL_THEN `&0 < e * inv (sqrt (&2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_SIMP_TAC []; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN `inv(sqrt (&2) ) = sqrt (inv (&2 ))` ASSUME_TAC THENL
   [SIMP_TAC [GSYM SQRT_INV]; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `max (b:real) (b':real)` THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN
  SUBGOAL_THEN `(x:real) >= (b:real)` ASSUME_TAC THENL
   [ASM_MESON_TAC [REAL_ARITH `x >= max y z ==>x >= y`]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real) >= (b':real)` ASSUME_TAC THENL
   [ASM_MESON_TAC [REAL_ARITH `x >= max y z ==>x >= z`]; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [dist] THEN
  ONCE_REWRITE_TAC [GSYM COMPLEX] THEN REWRITE_TAC [RE_SUB] THEN
  ONCE_REWRITE_TAC [RE] THEN REWRITE_TAC [IM_SUB] THEN ONCE_REWRITE_TAC [IM] THEN
  REWRITE_TAC [complex_norm] THEN ONCE_REWRITE_TAC [RE; IM] THEN
  SUBGOAL_THEN
    `abs (Re ((f:real->complex) x) - L1) pow 2 < (e * inv (sqrt (&2))) pow 2`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC []];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `abs (Im ((f:real->complex) x) - L2) pow 2 < (e * inv (sqrt (&2))) pow 2`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC []];
    ALL_TAC] THEN
  UNDISCH_TAC
    `abs (Re ((f:real->complex) x) - L1) pow 2 < (e * inv (sqrt (&2))) pow 2` THEN
  REWRITE_TAC [REAL_POW2_ABS] THEN STRIP_TAC THEN
  UNDISCH_TAC
    `abs (Im ((f:real->complex) x) - L2) pow 2 < (e * inv (sqrt (&2))) pow 2` THEN
  REWRITE_TAC [REAL_POW2_ABS] THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(Re ((f:real->complex) x) - L1) pow 2 + (Im (f x) - L2) pow 2 <
      &2 * (e * inv (sqrt (&2))) pow 2`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_ADD2_SYM THEN CONJ_TAC THEN ASM_SIMP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * (e * inv (sqrt (&2))) pow 2 ) = e pow 2` ASSUME_TAC THENL
   [REWRITE_TAC [REAL_POW_MUL] THEN ONCE_REWRITE_TAC [GSYM REAL_INV_POW] THEN
    SUBGOAL_THEN `(sqrt (&2) pow 2) = &2` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2; ASM_SIMP_TAC []] THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC
      `(Re ((f:real->complex) x) - L1) pow 2 + (Im (f x) - L2) pow 2 <
      &2 * (e * inv (sqrt (&2))) pow 2` THEN
    ASM_SIMP_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC []] THEN
    REWRITE_TAC [REAL_LE_POW_ADD_2] THEN REWRITE_TAC [REAL_LE_POW_ADD_2] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]);;

(*==================================================================*)
(*==================================================================*)
(*                  Properties of Fourier Transform                 *)
(*==================================================================*)
(*------------------------------------------------------------------*)
(*                        Property 01                               *)
(*------------------------------------------------------------------*)
(*      Integrability and Limit Existsence of Improper Integral     *)
(*------------------------------------------------------------------*)
(*==================================================================*)

(*------------------------------------------------------------------*)
(*                    LIM_FOURIER_EXISTS_LEMMA_1                    *)
(*------------------------------------------------------------------*)

let LIM_FOURIER_EXISTS_LEMMA_1 = prove
 (`!(f:real^1->complex) (w:real).
     fourier_exists f ==> 
       ?l. ((\a. integral (interval [lift (&0),lift a])
           (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t)) -->
      l)
     at_posinfinity`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
    REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [prove ( `!t.  cexp (--((ii * Cx w) * Cx (drop t))) * f t =
   Cx(Re(cexp (--((ii * Cx w) * Cx (drop t))) * f t))  + ii *
       Cx(Im( cexp (--((ii * Cx w) * Cx (drop t))) * f t)) `, MESON_TAC [COMPLEX_EXPAND] ) ] THEN
  SUBGOAL_THEN
    `!t.(integral (interval [lift (&0),lift t]) (\t. Cx (Re (cexp (--((ii * Cx w) * Cx (drop t))) * f t)) +
     ii * Cx (Im (cexp (--((ii * Cx w) * Cx (drop t))) * f t)))) =
      (integral (interval [lift (&0),lift t])
       (\t. Cx (Re (cexp (--((ii * Cx w) * Cx (drop t))) * f t)) )) + 
      (integral (interval [lift (&0),lift t])
       (\t. ii * Cx (Im (cexp (--((ii * Cx w) * Cx (drop t))) * f t))))`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_ADD THEN STRIP_TAC THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THENL
     [REWRITE_TAC [GSYM o_DEF] THEN
      SUBGOAL_THEN
        `!s. Cx o Re o (\t. cexp (--(s * Cx (drop t))) * f t) =
          (Cx o Re) o (\t. cexp (--(s * Cx (drop t))) * f t)`
        ASSUME_TAC THENL
       [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ALL_TAC; ONCE_REWRITE_TAC [CONTINUOUS_ON_CX_RE]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [SIMP_TAC [CEXP_S_T_CONTINUOUS];
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV THEN ASM_SIMP_TAC []];
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC [ii] THEN REWRITE_TAC [CONTINUOUS_ON_CONST]; ALL_TAC] THEN
      REWRITE_TAC [GSYM o_DEF] THEN
      SUBGOAL_THEN
        `!s. Cx o Im o (\t. cexp (--(s * Cx (drop t))) * f t) =
    (Cx o Im) o (\t. cexp (--(s * Cx (drop t))) * f t)`
        ASSUME_TAC THENL
       [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ALL_TAC; ONCE_REWRITE_TAC [CONTINUOUS_ON_CX_IM]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [SIMP_TAC [CEXP_S_T_CONTINUOUS];
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `!t s. integral (interval [lift (&0),lift t])
   (\t. ii * Cx (Im (cexp (--(s * Cx (drop t))) * f t))) =
     ii * integral (interval [lift (&0),lift t])
     (\t. Cx (Im (cexp (--(s * Cx (drop t))) * f t)))`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRAL_COMPLEX_MUL THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN REWRITE_TAC [GSYM o_DEF] THEN
    SUBGOAL_THEN
      `Cx o Im o (\t. cexp (--(s * Cx (drop t))) * f t) =
    (Cx o Im) o (\t. cexp (--(s * Cx (drop t))) * f t)`
      ASSUME_TAC THENL
     [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ALL_TAC; ONCE_REWRITE_TAC [CONTINUOUS_ON_CX_IM]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [SIMP_TAC [CEXP_S_T_CONTINUOUS];
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV]];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `! b s. integral (interval [lift (&0),lift b])
    (\t. Cx (Re (cexp (--(s * Cx (drop t))) * (f:real^1->complex) t))) = 
     Cx( real_integral (real_interval [&0, b])
      (\x:real. (\t. (Re (cexp (--(s * Cx (drop t))) * f t))) (lift x) ) )`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    SUBGOAL_THEN
      `!t. (Re (cexp (--(s * Cx (drop t))) * f t)) = 
    (\t. (Re (cexp (--(s * Cx (t))) * f (lift t))) ) (drop t)`
      ASSUME_TAC THENL
     [SIMP_TAC [LIFT_DROP]; ALL_TAC] THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    MATCH_MP_TAC CX_HAS_REAL_INTERGRAL THEN SIMP_TAC [LIFT_DROP] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN]] THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE]; ALL_TAC] THEN
    REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
    REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
    SUBGOAL_THEN `(f:real^1->complex) (lift x) = f (lift (drop (lift x) ) )`
      ASSUME_TAC THENL
     [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN REWRITE_TAC [LIFT_DROP] THEN
    SUBGOAL_THEN
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])`
      ASSUME_TAC THENL
     [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
      REWRITE_TAC
        [SET_RULE
           `IMAGE (\x. x) (interval [lift (&0),lift b]) = (interval [lift (&0),lift b])`] THEN
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV;
      REWRITE_TAC [CONTINUOUS_WITHIN] THEN
      UNDISCH_TAC
        `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])` THEN
      REWRITE_TAC [CONTINUOUS_ON] THEN
      DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
      ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
      ONCE_ASM_REWRITE_TAC [LIFT_DROP]] THEN
    ASM_SIMP_TAC [];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `! b s. integral (interval [lift (&0),lift b])
    (\t. Cx (Im (cexp (--(s * Cx (drop t))) * (f:real^1->complex) t))) =
      Cx (real_integral (real_interval [&0, b])
        (\x:real. (\t. (Im (cexp (--(s * Cx (drop t))) * f t))) (lift x) )  )`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    SUBGOAL_THEN
      `!t. (Im (cexp (--(s * Cx (drop t))) * f t)) = 
    (\t. (Im (cexp (--(s * Cx (t))) * f (lift t))) ) (drop t)`
      ASSUME_TAC THENL
     [SIMP_TAC [LIFT_DROP]; ALL_TAC] THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CX_HAS_REAL_INTERGRAL THEN
    SIMP_TAC [LIFT_DROP] THEN MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN]] THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE]; ALL_TAC] THEN
    REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
    REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
    SUBGOAL_THEN `(f:real^1->complex) (lift x) = f (lift (drop (lift x) ) )`
      ASSUME_TAC THENL
     [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
    REWRITE_TAC [LIFT_DROP] THEN
    SUBGOAL_THEN
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])`
      ASSUME_TAC THENL
     [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
      REWRITE_TAC
        [SET_RULE
           `IMAGE (\x. x) (interval [lift (&0),lift b]) = (interval [lift (&0),lift b])`] THEN
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV];
      REWRITE_TAC [CONTINUOUS_WITHIN] THEN
      UNDISCH_TAC
        `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])` THEN
      REWRITE_TAC [CONTINUOUS_ON] THEN
      DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
      ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
      ONCE_ASM_REWRITE_TAC [LIFT_DROP] THEN ASM_SIMP_TAC []];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `?k. ((\b. real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
     f (lift x))))) ---> k) at_posinfinity`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_COMPARISON_TEST THEN
    EXISTS_TAC
      `(\t. norm (cexp (--((ii * Cx w) * Cx (drop (lift t)))) * (f (lift t) ) ))` THEN
    STRIP_TAC THENL
     [REPEAT STRIP_TAC THENL
       [REAL_ARITH_TAC; SIMP_TAC [COMPLEX_NORM_GE_RE_IM]];
      ALL_TAC] THEN
    SIMP_TAC [REAL_ARITH `&0 <= &0`] THEN STRIP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [REAL_INTEGRABLE_ON] THEN REWRITE_TAC [o_DEF] THEN
      SIMP_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN
      MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      SUBGOAL_THEN
        `lift o norm o (\x. cexp (--((ii * Cx w) * Cx (drop (lift (drop x))))) * f (lift (drop x))) = (lift o norm) o (\x. cexp (--((ii * Cx w) * Cx (drop (lift (drop x))))) * f (lift (drop x)))`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN
        SIMP_TAC [];
        ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [CONTINUOUS_ON_LIFT_NORM] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN SIMP_TAC [LIFT_DROP] THEN
      CONJ_TAC THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THENL
       [SIMP_TAC [CONTINUOUS_ON_CEXP] THEN SIMP_TAC [GSYM COMPLEX_MUL_LNEG] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
        SIMP_TAC [CONTINUOUS_ON_CONST] THEN REWRITE_TAC [GSYM o_DEF] THEN
        REWRITE_TAC [CONTINUOUS_ON_CX_DROP];
        SIMP_TAC [CONTINUOUS_ON_ID] THEN
        REWRITE_TAC
          [SET_RULE
             `IMAGE (\x. x) (interval [lift (&0),lift b]) = (interval [lift (&0),lift b])`] THEN
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV]];
      CONJ_TAC THENL
       [ALL_TAC;
        GEN_TAC THEN REWRITE_TAC [LIFT_DROP] THEN 
	MATCH_MP_TAC ABS_RE_REAL_FOURIER_INTEGRABLE THEN
        REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
         ASM_SIMP_TAC []] THEN
      REWRITE_TAC [COMPLEX_NORM_MUL] THEN REWRITE_TAC [LIFT_DROP] THEN
      SIMP_TAC [NORM_CEXP] THEN ONCE_REWRITE_TAC [RE_NEG] THEN
      REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((x * y) * z) = (x * ((y:complex) * z))`] THEN
      REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [RE_MUL_CX] THEN
      REWRITE_TAC [RE_II] THEN
      REWRITE_TAC [REAL_ARITH `-- ((&0) * y * z) = (&0)`] THEN
      REWRITE_TAC [REAL_EXP_0] THEN
      REWRITE_TAC [REAL_ARITH `((&1) * x) = (x)`] THEN 
    ASM_SIMP_TAC [ABS_INTEG_IMP_NORM_FUN_POSINFINITY]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `?k. ((\b.  real_integral (real_interval [&0,b])
    (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
      f (lift x))))) ---> k) at_posinfinity`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_COMPARISON_TEST THEN
    EXISTS_TAC
      `(\t. norm (cexp (--((ii * Cx w) * Cx (drop (lift t)))) * (f (lift t) ) ))` THEN
    STRIP_TAC THENL
     [REPEAT STRIP_TAC THENL
       [REAL_ARITH_TAC; SIMP_TAC [COMPLEX_NORM_GE_RE_IM]];
      ALL_TAC] THEN
    SIMP_TAC [REAL_ARITH `&0 <= &0`] THEN STRIP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [REAL_INTEGRABLE_ON] THEN REWRITE_TAC [o_DEF] THEN
      SIMP_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN
      MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      SUBGOAL_THEN
        `lift o norm o (\x. cexp (--((ii * Cx w) * Cx (drop (lift (drop x))))) * f (lift (drop x))) = (lift o norm) o (\x. cexp (--((ii * Cx w) * Cx (drop (lift (drop x))))) * f (lift (drop x)))`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN
        SIMP_TAC [];
        ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [CONTINUOUS_ON_LIFT_NORM] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN SIMP_TAC [LIFT_DROP] THEN
      CONJ_TAC THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THENL
       [SIMP_TAC [CONTINUOUS_ON_CEXP] THEN SIMP_TAC [GSYM COMPLEX_MUL_LNEG] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
        SIMP_TAC [CONTINUOUS_ON_CONST] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        REWRITE_TAC [CONTINUOUS_ON_CX_DROP];
        SIMP_TAC [CONTINUOUS_ON_ID] THEN
        REWRITE_TAC
          [SET_RULE
             `IMAGE (\x. x) (interval [lift (&0),lift b]) = (interval [lift (&0),lift b])`] THEN
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV]];
      CONJ_TAC THENL
       [ALL_TAC;
        GEN_TAC THEN REWRITE_TAC [LIFT_DROP] THEN 
      MATCH_MP_TAC ABS_IM_REAL_FOURIER_INTEGRABLE THEN
        REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
       ASM_SIMP_TAC []] THEN
      REWRITE_TAC [COMPLEX_NORM_MUL] THEN REWRITE_TAC [LIFT_DROP] THEN
      SIMP_TAC [NORM_CEXP] THEN ONCE_REWRITE_TAC [RE_NEG] THEN
      REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((x * y) * z) = (x * ((y:complex) * z))`] THEN
      REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [RE_MUL_CX] THEN
      REWRITE_TAC [RE_II] THEN
      REWRITE_TAC [REAL_ARITH `-- ((&0) * y * z) = (&0)`] THEN
      REWRITE_TAC [REAL_EXP_0] THEN
      REWRITE_TAC [REAL_ARITH `((&1) * x) = (x)`] THEN 
    ASM_SIMP_TAC [ABS_INTEG_IMP_NORM_FUN_POSINFINITY]];
    UNDISCH_TAC
      `?k. ((\b. real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
     f (lift x))))) ---> k) at_posinfinity` THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC
      `?k. ((\b.  real_integral (real_interval [&0,b])
    (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
      f (lift x))))) ---> k) at_posinfinity` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `?m. ((\b. real_integral (real_interval [&0,b])
    (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
      Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)))) --->  m)  at_posinfinity`
      ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_COMPARISON_TEST THEN
      EXISTS_TAC
        `(\x. &2 * abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) )` THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THENL
         [SIMP_TAC [REAL_ABS_LE; REAL_SUB_LE];
          SIMP_TAC [REAL_MUL_2] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
        SIMP_TAC [LIFT_DROP] THEN 
      MATCH_MP_TAC ABS_RE_REAL_FOURIER_INTEGRABLE THEN
        REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
       ASM_SIMP_TAC [];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN
          `!b. real_integral (real_interval [&0,b])
   (\x. &2 *  abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)))) = &2 * real_integral (real_interval [&0,b])(\x.  abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))))`
          ASSUME_TAC THENL
         [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
          SIMP_TAC [LIFT_DROP] THEN 
        MATCH_MP_TAC ABS_RE_REAL_FOURIER_INTEGRABLE THEN
          REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
          ASM_SIMP_TAC [];
          ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
          SUBGOAL_THEN
            `?k. ((\b. real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
     f (lift x))))) ---> k) at_posinfinity`
            ASSUME_TAC THENL
           [EXISTS_TAC `k:real` THEN ASM_SIMP_TAC []; ALL_TAC] THEN
          EXISTS_TAC `&2 * k:real` THEN
          SUBGOAL_THEN
            `!b. &2 *  real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) ) =
    (\b. &2)b * (\ b . real_integral (real_interval [&0,b])
     (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) )) b`
            ASSUME_TAC THENL
           [SIMP_TAC []; ALL_TAC] THEN
          ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC REALLIM_MUL THEN
          SIMP_TAC [REALLIM_CONST] THEN ASM_SIMP_TAC []];
        GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
        SIMP_TAC [LIFT_DROP] THENL 
     [MATCH_MP_TAC ABS_RE_REAL_FOURIER_INTEGRABLE; 
      MATCH_MP_TAC RE_REAL_FOURIER_INTEGRABLE] THEN
        REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
       ASM_SIMP_TAC []];
      SUBGOAL_THEN
        `?m. ((\b. real_integral (real_interval [&0,b])
  (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
     Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)))) --->  m) at_posinfinity`
        ASSUME_TAC THENL
       [MATCH_MP_TAC INTEGRAL_COMPARISON_TEST THEN
        EXISTS_TAC
          `(\x. &2 * abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *f (lift x))) )` THEN
        CONJ_TAC THENL
         [REPEAT STRIP_TAC THENL
           [SIMP_TAC [REAL_ABS_LE; REAL_SUB_LE];
            SIMP_TAC [REAL_MUL_2] THEN REAL_ARITH_TAC];
          ALL_TAC] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
         [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
          SIMP_TAC [LIFT_DROP] THEN 
        MATCH_MP_TAC ABS_IM_REAL_FOURIER_INTEGRABLE THEN
          REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
          ASM_SIMP_TAC [];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN
            `!b. real_integral (real_interval [&0,b]) (\x. &2 *  abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
    f (lift x)))) = &2 * real_integral (real_interval [&0,b])
      (\x.  abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))))`
            ASSUME_TAC THENL
           [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
            SIMP_TAC [LIFT_DROP] THEN 
       MATCH_MP_TAC ABS_IM_REAL_FOURIER_INTEGRABLE THEN
            REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
            ASM_SIMP_TAC [];
            ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
            SUBGOAL_THEN
              `?k. ((\b.  real_integral (real_interval [&0,b])
    (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
      f (lift x))))) ---> k) at_posinfinity`
              ASSUME_TAC THENL
             [EXISTS_TAC `k':real` THEN ASM_SIMP_TAC []; ALL_TAC] THEN
            EXISTS_TAC `&2 * k':real` THEN
            SUBGOAL_THEN
              `!b. &2 *  real_integral (real_interval [&0,b])
   (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) ) =
     (\b. &2)b * (\ b . real_integral (real_interval [&0,b])
      (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) )) b`
              ASSUME_TAC THENL
             [SIMP_TAC []; ALL_TAC] THEN
            ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC REALLIM_MUL THEN
            SIMP_TAC [REALLIM_CONST] THEN ASM_SIMP_TAC []];
          GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
          SIMP_TAC [LIFT_DROP] THENL
           [MATCH_MP_TAC ABS_IM_REAL_FOURIER_INTEGRABLE; 
            MATCH_MP_TAC IM_REAL_FOURIER_INTEGRABLE] THEN
          REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
         ASM_SIMP_TAC []];
        UNDISCH_TAC
          `?m. ((\b. real_integral (real_interval [&0,b])
    (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
      Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)))) --->  m)  at_posinfinity` THEN
        REPEAT STRIP_TAC THEN
        UNDISCH_TAC
          `?m. ((\b. real_integral (real_interval [&0,b])
  (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
     Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)))) --->  m) at_posinfinity` THEN
        REPEAT STRIP_TAC THEN EXISTS_TAC `complex (k - m, k' - m')` THEN
        MATCH_MP_TAC LIM_COMPLEX_REAL_COMPONENTS THEN SIMP_TAC [] THEN
        SIMP_TAC [GSYM COMPLEX_TRAD] THEN SIMP_TAC [RE; IM] THEN
        ASM_SIMP_TAC [] THEN CONJ_TAC THENL
         [SUBGOAL_THEN
            `!x. Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * (f:real^1->complex) (lift x)) =
    abs( Re(cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
     ( abs(Re(cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
      Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)) )`
            ASSUME_TAC THENL
           [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
          SUBGOAL_THEN
            `!b. real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
     (abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
       Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))))  =
    real_integral (real_interval [&0,b])
     (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) ) -
    real_integral (real_interval [&0,b])
     (\x.  abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
       Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)) )`
            ASSUME_TAC THENL
           [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
             [SIMP_TAC [LIFT_DROP] THEN MATCH_MP_TAC ABS_RE_REAL_FOURIER_INTEGRABLE;
              MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
              SIMP_TAC [LIFT_DROP] THENL
               [MATCH_MP_TAC ABS_RE_REAL_FOURIER_INTEGRABLE; 
                MATCH_MP_TAC RE_REAL_FOURIER_INTEGRABLE]] THEN
            REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV];
            ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
            MATCH_MP_TAC REALLIM_SUB] THEN
          ASM_SIMP_TAC [];
          SUBGOAL_THEN
            `!x. Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * (f:real^1->complex) (lift x)) =
   abs( Im(cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
    ( abs(Im(cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
     Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)) )`
            ASSUME_TAC THENL
           [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
          SUBGOAL_THEN
            `!b. real_integral (real_interval [&0,b])
    (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
      (abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
      Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))))  =
    real_integral (real_interval [&0,b])
      (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) ) -
    real_integral (real_interval [&0,b])
      (\x.  abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
             Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)) )`
            ASSUME_TAC THENL
           [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
             [SIMP_TAC [LIFT_DROP] THEN MATCH_MP_TAC ABS_IM_REAL_FOURIER_INTEGRABLE;
              MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
              SIMP_TAC [LIFT_DROP] THENL
               [MATCH_MP_TAC ABS_IM_REAL_FOURIER_INTEGRABLE; 
                MATCH_MP_TAC IM_REAL_FOURIER_INTEGRABLE]] THEN
            REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV];
            ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
            MATCH_MP_TAC REALLIM_SUB] THEN
          ASM_SIMP_TAC []]]]]);;

(*========================================================*)
(*                LIM_COMPLEX_MUL_EXISTS                  *)
(*========================================================*)

let LIM_COMPLEX_MUL_EXISTS = prove
 (`!net f g l m. (?l. (f --> l) net) /\ (?m. (g --> m) net) ==> ?n. ((\x. f x * g x) --> n) net`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `l * m` THEN MATCH_MP_TAC LIM_COMPLEX_MUL THEN
  ASM_REWRITE_TAC []);; 

(*------------------------------------------------------------------*)
(*                LIM_FOURIER_EXISTS_LEMMA_1_GEN                    *)
(*------------------------------------------------------------------*)

let LIM_FOURIER_EXISTS_LEMMA_1_GEN = prove
 (`!(f:real^1->complex) (w:real) c.
     fourier_exists f ==> 
       ?l. ((\a. integral (interval [lift (&0),lift a])
           (\t. c * cexp (--((ii * Cx w) * Cx (drop t))) * f t)) -->
      l)
     at_posinfinity`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
    REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!a. integral (interval [lift (&0),lift a])
           (\t. c * cexp (--((ii * Cx w) * Cx (drop t))) * (f:real^1->complex) t) = 
	   c * integral (interval [lift (&0),lift a])
           (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t)`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_COMPLEX_MUL THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    SUBGOAL_THEN
      `!t. (cexp (--((ii * Cx w) * Cx (drop t))) * f t) = ((\t. cexp (--((ii * Cx w) * Cx (drop t)))) t * f t)`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
    ASM_SIMP_TAC [CEXP_S_T_CONTINUOUS_GEN] THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV];
    ASM_SIMP_TAC [] THEN MATCH_MP_TAC LIM_COMPLEX_MUL_EXISTS THEN CONJ_TAC THENL
     [EXISTS_TAC `c:real^2` THEN SIMP_TAC [LIM_CONST];
      MATCH_MP_TAC LIM_FOURIER_EXISTS_LEMMA_1 THEN 
     REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
      ASM_SIMP_TAC []]]);;

(*------------------------------------------------------------------*)
(*             PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV_1            *)
(*------------------------------------------------------------------*)

let PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV_1 = prove
 (`!(f:real^1->complex) c. 
   (!a b. f piecewise_differentiable_on interval [lift a,lift b]) 
       ==>
   f piecewise_differentiable_on interval [lift (&0),c]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET THEN
  EXISTS_TAC `interval [lift (&0),c]` THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN (MP_TAC o SPEC `&0`) THEN
  DISCH_THEN (MP_TAC o SPEC `drop (c:real^1)`) THEN SIMP_TAC [LIFT_DROP] THEN
  DISCH_TAC THEN REWRITE_TAC [SUBSET; IN_INTERVAL_1; DROP_NEG; LIFT_DROP]);;

(*------------------------------------------------------------------*)
(*        PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV_1         *)
(*------------------------------------------------------------------*)

let PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV_1 = prove
 (`!(f:real^1->complex) c. 
   (!a b. f piecewise_differentiable_on interval [lift a,lift b]) 
       ==>
   f piecewise_differentiable_on interval [c,lift (&0)]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET THEN
  EXISTS_TAC `interval [(c:real^1),lift (&0)]` THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN (MP_TAC o SPEC `drop (c:real^1)`) THEN
  DISCH_THEN (MP_TAC o SPEC `&0`) THEN SIMP_TAC [LIFT_DROP] THEN DISCH_TAC THEN
  REWRITE_TAC [SUBSET; IN_INTERVAL_1; DROP_NEG; LIFT_DROP]);;

(*------------------------------------------------------------------*)
(*                   CONTINUOUS_ON_SUBSET_UNIV_1                    *)
(*------------------------------------------------------------------*)

let CONTINUOUS_ON_SUBSET_UNIV_1 = prove
 (`!(f:real^1->complex) c. 
   (!a b. f continuous_on interval [lift a,lift b]) 
       ==>
   f continuous_on interval [lift (&0),c]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval [lift (&0),c]` THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN (MP_TAC o SPEC `&0`) THEN
  DISCH_THEN (MP_TAC o SPEC `drop (c:real^1)`) THEN SIMP_TAC [LIFT_DROP] THEN
  DISCH_TAC THEN REWRITE_TAC [SUBSET; IN_INTERVAL_1; DROP_NEG; LIFT_DROP]);;

(*------------------------------------------------------------------*)
(*             CONTINUOUS_ON_SUBSET_REFLECT_UNIV_1                  *)
(*------------------------------------------------------------------*)

let CONTINUOUS_ON_SUBSET_REFLECT_UNIV_1 = prove
 (`!(f:real^1->complex) c. 
   (!a b. f continuous_on interval [lift a,lift b]) 
       ==>
   f continuous_on interval [c,lift (&0)]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval [(c:real^1),lift (&0)]` THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN (MP_TAC o SPEC `drop (c:real^1)`) THEN
  DISCH_THEN (MP_TAC o SPEC `&0`) THEN SIMP_TAC [LIFT_DROP] THEN DISCH_TAC THEN
  REWRITE_TAC [SUBSET; IN_INTERVAL_1; DROP_NEG; LIFT_DROP]);;

(*------------------------------------------------------------------*)
(*               FOURIER_INTEGRAND_INTEGRABLE_LEMMA_1               *)
(*------------------------------------------------------------------*)

let FOURIER_INTEGRAND_INTEGRABLE_LEMMA_1 = prove
 (`!(f:real^1->complex) (w:real).
     fourier_exists f ==> 
       (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t) integrable_on
 {x | &0 <= drop x}`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
   REPEAT STRIP_TAC THEN
  REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN 
  REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM LIFT_NUM] THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [SIMP_TAC [CEXP_S_T_CONTINUOUS];
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV_1]];
    MATCH_MP_TAC LIM_FOURIER_EXISTS_LEMMA_1 THEN 
   REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
  ASM_SIMP_TAC []]);;

(*------------------------------------------------------------------*)
(*           FOURIER_INTEGRAND_INTEGRABLE_LEMMA_1_GEN               *)
(*------------------------------------------------------------------*)

let FOURIER_INTEGRAND_INTEGRABLE_LEMMA_1_GEN = prove
 (`!(f:real^1->complex) (w:real) c.
     fourier_exists f ==> 
       (\t. c * cexp (--((ii * Cx w) * Cx (drop t))) * f t) integrable_on
 {x | &0 <= drop x}`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
   REPEAT STRIP_TAC THEN
  REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN 
   REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM LIFT_NUM] THENL
   [ALL_TAC;
    MATCH_MP_TAC LIM_FOURIER_EXISTS_LEMMA_1_GEN THEN 
   REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
    ASM_SIMP_TAC []] THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC [CONTINUOUS_ON_CONST]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [SIMP_TAC [CEXP_S_T_CONTINUOUS];
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV_1]]);;

(*------------------------------------------------------------------*)
(*       PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV_ALT        *)
(*------------------------------------------------------------------*)

let PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV_ALT = prove
 (`!(f:real^1->complex) c. 
   (!a b. f piecewise_differentiable_on interval [lift a,lift b]) 
       ==>
   f piecewise_differentiable_on IMAGE (--) (interval [lift (&0),lift c])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET THEN
  EXISTS_TAC `(interval [lift (-- c),lift (&0)])` THEN
  UNDISCH_TAC
    `!a b. (f:real^1->complex) piecewise_differentiable_on interval [lift a,lift b]` THEN
  DISCH_THEN (MP_TAC o SPEC `-- c:real`) THEN DISCH_THEN (MP_TAC o SPEC `&0`) THEN
  SIMP_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [SUBSET] THEN
  REWRITE_TAC [IN_IMAGE; IN_INTERVAL_1] THEN REWRITE_TAC [LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [DROP_NEG] THEN
  ASM_REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*      PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV_ALT_1       *)
(*------------------------------------------------------------------*)

let PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV_ALT_1 = prove
 (`!(f:real^1->complex) c. 
   (!a b. f piecewise_differentiable_on interval [lift a,lift b]) 
       ==>
   f piecewise_differentiable_on IMAGE (--) (interval [lift (&0),c])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET THEN
  EXISTS_TAC `(interval [(-- c:real^1),lift (&0)])` THEN
  UNDISCH_TAC
    `!a b. (f:real^1->complex) piecewise_differentiable_on interval [lift a,lift b]` THEN
  DISCH_THEN (MP_TAC o SPEC `drop (-- c:real^1)`) THEN
  DISCH_THEN (MP_TAC o SPEC `&0`) THEN SIMP_TAC [LIFT_DROP] THEN DISCH_TAC THEN
  REWRITE_TAC [SUBSET] THEN REWRITE_TAC [IN_IMAGE; IN_INTERVAL_1] THEN
  REWRITE_TAC [LIFT_DROP] THEN REWRITE_TAC [DROP_NEG] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN REWRITE_TAC [DROP_NEG] THEN ASM_REAL_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*                  LIM_FOURIER_EXISTS_LEMMA_2                      *)
(*------------------------------------------------------------------*)

let LIM_FOURIER_EXISTS_LEMMA_2 = prove
 (`!(f:real^1->complex) (w:real).
     fourier_exists f ==> 
       ?l. ((\a. integral (interval [lift (&0),lift a])
           (\x. cexp (--((ii * Cx w) * Cx (drop (--x)))) * f (--x))) -->
      l)
     at_posinfinity`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
   REPEAT STRIP_TAC THEN
  MP_TAC LIM_FOURIER_EXISTS_LEMMA_1 THEN
  DISCH_THEN (MP_TAC o SPEC `(\x. (f:real^1->complex) (--x))`) THEN
  DISCH_THEN (MP_TAC o SPEC `-- (w:real)`) THEN REWRITE_TAC [CX_NEG] THEN
  REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH
       `(--((ii * --Cx w) * Cx (drop t))) = (--((ii * Cx w) * -- Cx (drop t)))`] THEN
  REWRITE_TAC [GSYM CX_NEG; GSYM DROP_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN CONJ_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL
     [ASM_SIMP_TAC [ABSOLUTELY_INTEGRABLE_REFLECT_GEN]; ALL_TAC] THEN
    ONCE_REWRITE_TAC [GSYM ABSOLUTELY_INTEGRABLE_REFLECT_GEN] THEN
    SIMP_TAC [] THEN ASM_SIMP_TAC [VECTOR_NEG_NEG; ETA_AX]] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC
    [VECTOR_ARITH `!x:real^1 f. (--(x)) = (--(&1) % x + (vec 0):real^1)`] THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_AFFINE THEN
  ONCE_REWRITE_TAC
    [VECTOR_ARITH `!x:real^1 f. (--(&1) % x + (vec 0):real^1) = (--(x))`] THEN
  REWRITE_TAC
    [SET_RULE
       `IMAGE (\x. --x) (interval [lift a,lift b]) = (IMAGE (--) (interval [lift a,lift b]))`] THEN
  SUBGOAL_THEN
    `IMAGE (--) (interval [lift a,lift b]) = (interval [lift (--b),lift (--a)])`
    ASSUME_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC []] THEN
  REWRITE_TAC [EXTENSION; IN_UNION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
  REWRITE_TAC [IN_INTERVAL_1] THEN REWRITE_TAC [LIFT_DROP] THEN STRIP_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC [] THEN REWRITE_TAC [DROP_NEG];
    ASM_SIMP_TAC [] THEN REWRITE_TAC [DROP_NEG] THEN POP_ASSUM MP_TAC;
    EXISTS_TAC `-- (x:real^1)` THEN REWRITE_TAC [VECTOR_NEG_NEG; DROP_NEG] THEN
    POP_ASSUM MP_TAC] THEN
  POP_ASSUM MP_TAC THEN SIMPLE_COMPLEX_ARITH_TAC);;

(*------------------------------------------------------------------*)
(*              FOURIER_INTEGRAND_INTEGRABLE_LEMMA_2                *)
(*------------------------------------------------------------------*)

let FOURIER_INTEGRAND_INTEGRABLE_LEMMA_2 = prove
 (`!(f:real^1->complex) (w:real).
     fourier_exists f ==> 
       (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t) integrable_on
 IMAGE (--) {x | &0 <= drop x}`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM INTEGRABLE_REFLECT_GEN] THEN 
  REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM LIFT_NUM] THENL
   [ALL_TAC; MATCH_MP_TAC LIM_FOURIER_EXISTS_LEMMA_2 THEN 
    ASM_SIMP_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV]] THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC [DROP_NEG; CX_NEG] THEN REWRITE_TAC [COMPLEX_MUL_RNEG] THEN
    ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
    SIMP_TAC [CEXP_S_T_CONTINUOUS];
    ONCE_REWRITE_TAC [VECTOR_ARITH `!x:real^1 a f. (--(x)) = (--(&1) % x)`] THEN
    ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC [CONTINUOUS_ON_ID];
      ONCE_REWRITE_TAC [VECTOR_ARITH `!x:real^1 a f. (--(&1) % x) = (--(x))`] THEN
      REWRITE_TAC [ETA_AX] THEN
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV_ALT_1]]]);;

(*------------------------------------------------------------------*)
(*                LIM_FOURIER_EXISTS_LEMMA_2_GEN                    *)
(*------------------------------------------------------------------*)

let LIM_FOURIER_EXISTS_LEMMA_2_GEN = prove
 (`!(f:real^1->complex) (w:real).
     fourier_exists f ==> 
       ?l. ((\a. integral (interval [lift (&0),lift a])
           (\x. c * cexp (--((ii * Cx w) * Cx (drop (--x)))) * f (--x))) -->
      l)
     at_posinfinity`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!a. integral (interval [lift (&0),lift a])
           (\x. c * cexp (--((ii * Cx w) * Cx (drop (--x)))) * f (--x)) = 
	   c * integral (interval [lift (&0),lift a])
           (\x. cexp (--((ii * Cx w) * Cx (drop (--x)))) * f (--x))`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_COMPLEX_MUL THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC [DROP_NEG; CX_NEG] THEN REWRITE_TAC [COMPLEX_MUL_RNEG] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
      SIMP_TAC [CEXP_S_T_CONTINUOUS];
      ONCE_REWRITE_TAC [VECTOR_ARITH `!x:real^1 a f. (--(x)) = (--(&1) % x)`] THEN
      ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC [CONTINUOUS_ON_ID];
        ONCE_REWRITE_TAC
          [VECTOR_ARITH `!x:real^1 a f. (--(&1) % x) = (--(x))`] THEN
        REWRITE_TAC [ETA_AX] THEN
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV_ALT_1]]];
    ASM_SIMP_TAC [] THEN MATCH_MP_TAC LIM_COMPLEX_MUL_EXISTS THEN CONJ_TAC THENL
     [EXISTS_TAC `c:real^2` THEN SIMP_TAC [LIM_CONST];
      MATCH_MP_TAC LIM_FOURIER_EXISTS_LEMMA_2 THEN 
      REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
      ASM_SIMP_TAC []]]);;

(*------------------------------------------------------------------*)
(*            FOURIER_INTEGRAND_INTEGRABLE_LEMMA_2_GEN              *)
(*------------------------------------------------------------------*)

let FOURIER_INTEGRAND_INTEGRABLE_LEMMA_2_GEN = prove
 (`!(f:real^1->complex) (w:real) c.
     fourier_exists f ==> 
       (\t. c * cexp (--((ii * Cx w) * Cx (drop t))) * f t) integrable_on
 IMAGE (--) {x | &0 <= drop x}`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM INTEGRABLE_REFLECT_GEN] THEN
  REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM LIFT_NUM] THENL
   [ALL_TAC;
    MATCH_MP_TAC LIM_FOURIER_EXISTS_LEMMA_2_GEN THEN
    REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
   ASM_SIMP_TAC []] THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC [CONTINUOUS_ON_CONST]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC [DROP_NEG; CX_NEG] THEN REWRITE_TAC [COMPLEX_MUL_RNEG] THEN
    ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
    SIMP_TAC [CEXP_S_T_CONTINUOUS];
    ONCE_REWRITE_TAC [VECTOR_ARITH `!x:real^1 a f. (--(x)) = (--(&1) % x)`] THEN
    ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC [CONTINUOUS_ON_ID];
      ONCE_REWRITE_TAC [VECTOR_ARITH `!x:real^1 a f. (--(&1) % x) = (--(x))`] THEN
      REWRITE_TAC [ETA_AX] THEN
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV_ALT_1]]]);;

(*------------------------------------------------------------------*)
(*                    FOURIER_INTEGRAND_INTEGRABLE                  *)
(*------------------------------------------------------------------*)

let FOURIER_INTEGRAND_INTEGRABLE = prove
 (`!(f:real^1->complex) (w:real).
     fourier_exists f ==> 
       (\ t. (cexp(--((ii * Cx (w)) * Cx(drop(t)))) * (f t))) integrable_on (:real^1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [INTEGRAL_UNIV_BREAK] THEN REWRITE_TAC [UNIV_SET_BREAK] THEN
  MATCH_MP_TAC INTEGRABLE_UNION THEN CONJ_TAC THENL
   [MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_1 THEN 
    REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
    ASM_SIMP_TAC [];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_2 THEN 
    REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
    ASM_SIMP_TAC [];
    ALL_TAC] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{(vec 0):real^1}` THEN
  REWRITE_TAC [NEGLIGIBLE_SING] THEN
  REWRITE_TAC
    [IN_ELIM_THM;
     SET_RULE
       `s INTER IMAGE f s SUBSET {a} <=> !x. x IN s /\ f x IN s ==> f x = a`] THEN
  REWRITE_TAC [GSYM LIFT_NUM] THEN REWRITE_TAC [DROP_NEG] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM DROP_EQ] THEN
  REWRITE_TAC [LIFT_DROP] THEN REWRITE_TAC [DROP_NEG] THEN ASM_REAL_ARITH_TAC);;

(*==================================================================*)
(*------------------------------------------------------------------*)
(*                        Property 02                               *)
(*------------------------------------------------------------------*)
(*                         Linearity                                *)
(*------------------------------------------------------------------*)
(*==================================================================*)

(*==================================================================*)
(*                     FOURIER_ADD_LINEARITY                        *)
(*==================================================================*)

let FOURIER_ADD_LINEARITY = prove
 (`! (f:real^1->complex) g (w:real).
    fourier_exists f /\ fourier_exists g ==>
     (fourier_comp (\x. f x + g x ) w = fourier_comp f w + fourier_comp g w)`,
  REWRITE_TAC [fourier_comp] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [COMPLEX_ADD_LDISTRIB] THEN MATCH_MP_TAC INTEGRAL_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE THEN 
  ASM_REWRITE_TAC []);;

(*==================================================================*)
(*                     FOURIER_MUL_LINEARITY                        *)
(*==================================================================*)

let FOURIER_MUL_LINEARITY = prove
 (`!(f:real^1->complex) (w:real) (a:real).
   fourier_exists f ==> (fourier_comp (\x. a % f x) w = a % fourier_comp f w)`,
  REWRITE_TAC [fourier_comp] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [COMPLEX_CMUL] THEN
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `x:complex * y * z = y * x * z`] THEN
  REWRITE_TAC [GSYM COMPLEX_CMUL] THEN MATCH_MP_TAC INTEGRAL_CMUL THEN
  ASM_SIMP_TAC [FOURIER_INTEGRAND_INTEGRABLE]);;

(*==================================================================*)
(*                  FOURIER_MUL_ADD_LINEARITY                       *)
(*==================================================================*)

let FOURIER_MUL_ADD_LINEARITY = prove
 (`! (f:real^1->complex) g (w:real) (a:real) (b:real).
 fourier_exists f /\ fourier_exists g ==>
(fourier_comp (\x. a % f x + b % g x ) w = a % fourier_comp f w + b % fourier_comp g w)`,
  REWRITE_TAC [fourier_comp] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [COMPLEX_CMUL] THEN
  ONCE_REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH
       `v:complex * (w * x + y * z) = w * v * x + y * v * z`] THEN
  SUBGOAL_THEN
    `integral (:real^1)
 (\t. Cx a * cexp (--((ii * Cx w) * Cx (drop t))) * (f:real^1->complex) t +
      Cx b * cexp (--((ii * Cx w) * Cx (drop t))) * g t) =
      integral (:real^1)
 (\t. Cx a * cexp (--((ii * Cx w) * Cx (drop t))) * f t) + 
      integral (:real^1)
 (\t. Cx b * cexp (--((ii * Cx w) * Cx (drop t))) * g t)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_ADD THEN CONJ_TAC THEN
    REWRITE_TAC [GSYM COMPLEX_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    ASM_SIMP_TAC [FOURIER_INTEGRAND_INTEGRABLE];
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [GSYM COMPLEX_CMUL] THEN
    SUBGOAL_THEN
      `integral (:real^1) (\t. a % (cexp (--((ii * Cx w) * Cx (drop t))) * f t)) =
 a % integral (:real^1) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * (f:real^1->complex) t)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_CMUL THEN 
      ASM_SIMP_TAC [FOURIER_INTEGRAND_INTEGRABLE]; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN
      `integral (:real^1) (\t. b % (cexp (--((ii * Cx w) * Cx (drop t))) * g t)) =
 b % integral (:real^1) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * (g:real^1->complex) t)`
      ASSUME_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC []] THEN
    MATCH_MP_TAC INTEGRAL_CMUL THEN 
    ASM_SIMP_TAC [FOURIER_INTEGRAND_INTEGRABLE]]);;

(*==================================================================*)
(*------------------------------------------------------------------*)
(*                        Property 03                               *)
(*------------------------------------------------------------------*)
(*                      Frequency Shifting                          *)
(*------------------------------------------------------------------*)
(*==================================================================*)

(*==================================================================*)
(*                  FOURIER_SHIFT_IN_W_DOMAIN                       *)
(*==================================================================*)

let FOURIER_SHIFT_IN_W_DOMAIN = prove
 (`! (f:real^1->complex) (w:real) (w0:real).
     fourier_exists f  ==> (fourier_comp (\t. cexp ((ii * Cx (w0)) * Cx(drop(t))) * f t) w = fourier_comp f (w - w0))`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV; fourier_comp] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `x:complex * y * z = (x * y) * z`] THEN
  SIMP_TAC [GSYM CEXP_ADD; GSYM COMPLEX_MUL_LNEG; GSYM COMPLEX_ADD_RDISTRIB] THEN
  SIMP_TAC
    [SIMPLE_COMPLEX_ARITH `(--s * (x:complex) + s * y) = --s * (x - y)`] THEN
  REWRITE_TAC [CX_SUB]);;

(*==================================================================*)
(*------------------------------------------------------------------*)
(*                        Property 04                               *)
(*------------------------------------------------------------------*)
(*                        Modulation                                *)
(*------------------------------------------------------------------*)
(*==================================================================*)

(*==================================================================*)
(*                  FOURIER_COSINE_MODULATION                       *)
(*==================================================================*)

let FOURIER_COSINE_MODULATION = prove
 (`! (f:real^1->complex) (w:real) (w0:real).
     fourier_exists f  ==> 
   (fourier_comp (\t. ccos (Cx (w0) * Cx(drop(t))) * f t) w = 
    (fourier_comp f (w - w0) + fourier_comp f (w + w0)) / Cx (&2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC [fourier_comp] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [ccos] THEN REWRITE_TAC [complex_div] THEN
  SIMP_TAC
    [SIMPLE_COMPLEX_ARITH `((a:complex * (b * d) * c) = ((a * b) * c) * d)`] THEN
  REWRITE_TAC [COMPLEX_ADD_LDISTRIB] THEN REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN
  SIMP_TAC
    [GSYM CEXP_ADD; GSYM COMPLEX_MUL_LNEG; COMPLEX_MUL_ASSOC;
     GSYM COMPLEX_ADD_RDISTRIB] THEN
  SIMP_TAC
    [SIMPLE_COMPLEX_ARITH `(--s * (x:complex) + s * y) = --s * (x - y)`] THEN
  SIMP_TAC
    [SIMPLE_COMPLEX_ARITH `(--s * (x:complex) + --s * y) = --s * (x + y)`] THEN
  REWRITE_TAC [GSYM CX_SUB; GSYM CX_ADD] THEN
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(a:complex * b) = (b * a)`] THEN
  SUBGOAL_THEN
    `integral (:real^1)
 (\t. inv (Cx (&2)) *
      (cexp ((--ii * Cx (w - w0)) * Cx (drop t)) +
       cexp ((--ii * Cx (w + w0)) * Cx (drop t))) *
      f t) = inv (Cx (&2)) * integral (:real^1)
 (\t. (cexp ((--ii * Cx (w - w0)) * Cx (drop t)) +
       cexp ((--ii * Cx (w + w0)) * Cx (drop t))) *
      f t)`
    ASSUME_TAC THENL
   [REWRITE_TAC [GSYM CX_INV; GSYM COMPLEX_CMUL] THEN
    MATCH_MP_TAC INTEGRAL_CMUL THEN ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THEN
    REWRITE_TAC [COMPLEX_MUL_LNEG];
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN
    REWRITE_TAC [COMPLEX_MUL_LNEG] THEN MATCH_MP_TAC INTEGRAL_ADD THEN
    CONJ_TAC] THEN
  MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE THEN ASM_SIMP_TAC []);;

(*==================================================================*)
(*                   FOURIER_SINE_MODULATION                        *)
(*==================================================================*)

let FOURIER_SINE_MODULATION = prove
 (`! (f:real^1->complex) (w:real) (w0:real).
     fourier_exists f  ==> 
   (fourier_comp (\t. csin (Cx (w0) * Cx(drop(t))) * f t) w = 
    (fourier_comp f (w - w0) - fourier_comp f (w + w0)) / (Cx (&2) * ii))`,
  REPEAT GEN_TAC THEN REWRITE_TAC [fourier_comp] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [csin] THEN REWRITE_TAC [complex_div] THEN
  SIMP_TAC
    [SIMPLE_COMPLEX_ARITH `((a:complex * (b * d) * c) = ((a * b) * c) * d)`] THEN
  REWRITE_TAC [COMPLEX_SUB_LDISTRIB] THEN REWRITE_TAC [COMPLEX_SUB_RDISTRIB] THEN
  SIMP_TAC
    [GSYM CEXP_ADD; GSYM COMPLEX_MUL_LNEG; COMPLEX_MUL_ASSOC;
     GSYM COMPLEX_ADD_RDISTRIB] THEN
  SIMP_TAC
    [SIMPLE_COMPLEX_ARITH `(--s * (x:complex) + s * y) = --s * (x - y)`] THEN
  SIMP_TAC
    [SIMPLE_COMPLEX_ARITH `(--s * (x:complex) + --s * y) = --s * (x + y)`] THEN
  REWRITE_TAC [GSYM CX_SUB; GSYM CX_ADD] THEN
  ONCE_REWRITE_TAC [GSYM COMPLEX_SUB_RDISTRIB] THEN
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(a:complex * b) = (b * a)`] THEN
  SUBGOAL_THEN
    `integral (:real^1)
 (\t. inv (Cx (&2) * ii) *
      (cexp ((--ii * Cx (w - w0)) * Cx (drop t)) -
       cexp ((--ii * Cx (w + w0)) * Cx (drop t))) *
      f t) = inv (Cx (&2) * ii) * integral (:real^1)
 (\t. (cexp ((--ii * Cx (w - w0)) * Cx (drop t)) -
       cexp ((--ii * Cx (w + w0)) * Cx (drop t))) *
      f t)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_COMPLEX_MUL THEN
    ONCE_REWRITE_TAC [COMPLEX_SUB_RDISTRIB] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
    CONJ_TAC THEN REWRITE_TAC [COMPLEX_MUL_LNEG];
    ONCE_REWRITE_TAC [GSYM COMPLEX_SUB_RDISTRIB] THEN ASM_SIMP_TAC [] THEN
    POP_ASSUM (K ALL_TAC) THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC [COMPLEX_SUB_RDISTRIB] THEN
    REWRITE_TAC [COMPLEX_MUL_LNEG] THEN MATCH_MP_TAC INTEGRAL_SUB THEN
    CONJ_TAC] THEN
  MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE THEN ASM_SIMP_TAC []);;

(*==================================================================*)
(*------------------------------------------------------------------*)
(*                        Property 05                               *)
(*------------------------------------------------------------------*)
(*                       Time Reversal                              *)
(*------------------------------------------------------------------*)
(*==================================================================*)

(*==================================================================*)
(*                      FOURIER_TIME_REVERSAL                       *)
(*==================================================================*)

let FOURIER_TIME_REVERSAL = prove
 (`! (f:real^1->complex) (w:real).
     fourier_exists f  ==> 
   (fourier_comp (\t. f (--t)) w = fourier_comp f (--w))`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV; fourier_comp] THEN 
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `integral (:real^1) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f (--t)) = integral {t | &0 <= drop t} (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f (--t)) + integral (IMAGE (--) {t | &0 <= drop t}) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * (f:real^1->complex) (--t))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_UNIV_BREAK_1 THEN CONJ_TAC THENL
     [REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(--((ii * Cx w) * Cx (drop t))) = (--((ii * --Cx w) * --Cx (drop t)))`] THEN
      REWRITE_TAC [GSYM CX_NEG] THEN REWRITE_TAC [GSYM DROP_NEG] THEN
      SUBGOAL_THEN
        `!t. (cexp (--((ii * Cx (--w)) * Cx (drop (--t)))) * f (--t)) = (\t. cexp (--((ii * Cx (--w)) * Cx (drop t))) * f t) (--t)`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      REWRITE_TAC [INTEGRABLE_REFLECT_GEN] THEN 
      MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_2 THEN
      ASM_SIMP_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV];
      REWRITE_TAC [GSYM INTEGRABLE_REFLECT_GEN] THEN
      REWRITE_TAC [VECTOR_NEG_NEG] THEN REWRITE_TAC [DROP_NEG] THEN
      REWRITE_TAC [CX_NEG] THEN
      REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(--((ii * Cx w) * --Cx (drop t))) = (--((ii * --Cx w) * Cx (drop t)))`] THEN
      REWRITE_TAC [GSYM CX_NEG] 
      THEN MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_1 THEN
      ASM_SIMP_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV]];
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `integral (:real^1) (\t. cexp (--((ii * Cx (--w)) * Cx (drop t))) * f t) = integral {t | &0 <= drop t} (\t. cexp (--((ii * Cx (--w)) * Cx (drop t))) * f t) + integral (IMAGE (--) {t | &0 <= drop t}) (\t. cexp (--((ii * Cx (--w)) * Cx (drop t))) * (f:real^1->complex) t)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_UNIV_BREAK_1 THEN CONJ_TAC THENL
       [MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_1; 
        MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_2] THEN
      ASM_SIMP_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `integral {t | &0 <= drop t}
 (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f (--t)) = integral (IMAGE (--) {t | &0 <= drop t})
 (\t. cexp (--((ii * Cx (--w)) * Cx (drop t))) * (f:real^1->complex) t)`
      ASSUME_TAC THENL
     [REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(--((ii * Cx w) * Cx (drop t))) = (--((ii * --Cx w) * --Cx (drop t)))`] THEN
      REWRITE_TAC [GSYM CX_NEG] THEN REWRITE_TAC [GSYM DROP_NEG] THEN
      SUBGOAL_THEN
        `!t. (cexp (--((ii * Cx (--w)) * Cx (drop (--t)))) * f (--t)) = (\t. cexp (--((ii * Cx (--w)) * Cx (drop t))) * f t) (--t)`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [INTEGRAL_REFLECT_GEN] THEN
      REWRITE_TAC [DROP_NEG; CX_NEG] THEN AP_TERM_TAC THEN
      REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN CONV_TAC COMPLEX_FIELD;
      ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `(((a:complex) + b) = (c + a)) = (b = c)`] THEN
      REWRITE_TAC [CX_NEG] THEN
      REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(--((ii * --Cx w) * Cx (drop t))) = (--((ii * Cx w) * --Cx (drop t)))`] THEN
      REWRITE_TAC [GSYM CX_NEG] THEN REWRITE_TAC [GSYM DROP_NEG] THEN
      SUBGOAL_THEN
        `!t. (cexp (--((ii * Cx w) * Cx (drop (--t)))) * f t) = (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f (--t)) (--t)`
        ASSUME_TAC THENL
       [SIMP_TAC [] THEN REWRITE_TAC [VECTOR_NEG_NEG];
        ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
        REWRITE_TAC [INTEGRAL_REFLECT_GEN]]]]);;

(*==================================================================*)
(*------------------------------------------------------------------*)
(*                        Property 06                               *)
(*------------------------------------------------------------------*)
(*                Differentiation in Time Domain                    *)
(*------------------------------------------------------------------*)
(*==================================================================*)

(*=======================================================*)
(*                    convergent_f                       *)
(*=======================================================*)

let  convergent_f = new_definition
`convergent_f (f:real->real^M)  net = 
(?l. (f --> l) net) ` ;;

(*=======================================================*)
(*                       FUN_LIM                         *)
(*=======================================================*)

let FUN_LIM = prove
 (`!(f:real->real^M) . convergent_f f net = 
    (f --> (lim net f) ) net`,
  GEN_TAC THEN REWRITE_TAC [convergent_f] THEN EQ_TAC THENL
   [DISCH_THEN (MP_TAC o SELECT_RULE) THEN REWRITE_TAC [lim];
    DISCH_TAC THEN EXISTS_TAC `lim net (f:real->real^M)` THEN
    POP_ASSUM ACCEPT_TAC]);;

(*=======================================================*)
(*              FOURIER_UNILATERAL_ALT_REP_1             *)
(*=======================================================*)

let FOURIER_UNILATERAL_ALT_REP_1 = prove
 (`!(f:real^1->complex) w. fourier_exists f ==>
  (integral {t | &0 <= drop t}
   (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t) ) =
    ( lim at_posinfinity
         (\b. integral (interval [vec 0,lift b])
              (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t)) )`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  REWRITE_TAC [HAS_INTEGRAL_LIM_AT_POSINFINITY] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM LIFT_NUM] THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [SIMP_TAC [CEXP_S_T_CONTINUOUS];
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV_1]];
    ALL_TAC] THEN
  REWRITE_TAC [GSYM LIFT_NUM] THEN REWRITE_TAC [GSYM FUN_LIM] THEN
  REWRITE_TAC [convergent_f] THEN 
  ONCE_REWRITE_TAC [prove ( `!t.  cexp (--((ii * Cx w) * Cx (drop t))) * f t =
   Cx(Re(cexp (--((ii * Cx w) * Cx (drop t))) * f t))  + ii *
       Cx(Im( cexp (--((ii * Cx w) * Cx (drop t))) * f t)) `, MESON_TAC [COMPLEX_EXPAND] ) ] THEN
  SUBGOAL_THEN
    `!t.(integral (interval [lift (&0),lift t]) (\t. Cx (Re (cexp (--((ii * Cx w) * Cx (drop t))) * f t)) +
     ii * Cx (Im (cexp (--((ii * Cx w) * Cx (drop t))) * f t)))) =
      (integral (interval [lift (&0),lift t])
       (\t. Cx (Re (cexp (--((ii * Cx w) * Cx (drop t))) * f t)) )) + 
      (integral (interval [lift (&0),lift t])
       (\t. ii * Cx (Im (cexp (--((ii * Cx w) * Cx (drop t))) * f t))))`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_ADD THEN STRIP_TAC THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THENL
     [REWRITE_TAC [GSYM o_DEF] THEN
      SUBGOAL_THEN
        `!s. Cx o Re o (\t. cexp (--(s * Cx (drop t))) * f t) =
          (Cx o Re) o (\t. cexp (--(s * Cx (drop t))) * f t)`
        ASSUME_TAC THENL
       [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ALL_TAC; ONCE_REWRITE_TAC [CONTINUOUS_ON_CX_RE]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [SIMP_TAC [CEXP_S_T_CONTINUOUS];
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV_1]];
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC [ii] THEN REWRITE_TAC [CONTINUOUS_ON_CONST]; ALL_TAC] THEN
      REWRITE_TAC [GSYM o_DEF] THEN
      SUBGOAL_THEN
        `!s. Cx o Im o (\t. cexp (--(s * Cx (drop t))) * f t) =
    (Cx o Im) o (\t. cexp (--(s * Cx (drop t))) * f t)`
        ASSUME_TAC THENL
       [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ALL_TAC; ONCE_REWRITE_TAC [CONTINUOUS_ON_CX_IM]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [SIMP_TAC [CEXP_S_T_CONTINUOUS];
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV_1]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `!t s. integral (interval [lift (&0),lift t])
   (\t. ii * Cx (Im (cexp (--(s * Cx (drop t))) * f t))) =
     ii * integral (interval [lift (&0),lift t])
     (\t. Cx (Im (cexp (--(s * Cx (drop t))) * f t)))`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRAL_COMPLEX_MUL THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN REWRITE_TAC [GSYM o_DEF] THEN
    SUBGOAL_THEN
      `Cx o Im o (\t. cexp (--(s * Cx (drop t))) * f t) =
    (Cx o Im) o (\t. cexp (--(s * Cx (drop t))) * f t)`
      ASSUME_TAC THENL
     [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ALL_TAC; ONCE_REWRITE_TAC [CONTINUOUS_ON_CX_IM]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [SIMP_TAC [CEXP_S_T_CONTINUOUS];
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV]];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `! b s. integral (interval [lift (&0),lift b])
    (\t. Cx (Re (cexp (--(s * Cx (drop t))) * (f:real^1->complex) t))) = 
     Cx( real_integral (real_interval [&0, b])
      (\x:real. (\t. (Re (cexp (--(s * Cx (drop t))) * f t))) (lift x) ) )`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    SUBGOAL_THEN
      `!t. (Re (cexp (--(s * Cx (drop t))) * f t)) = 
    (\t. (Re (cexp (--(s * Cx (t))) * f (lift t))) ) (drop t)`
      ASSUME_TAC THENL
     [SIMP_TAC [LIFT_DROP]; ALL_TAC] THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    MATCH_MP_TAC CX_HAS_REAL_INTERGRAL THEN SIMP_TAC [LIFT_DROP] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN]] THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE]; ALL_TAC] THEN
    REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
    REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
    SUBGOAL_THEN `(f:real^1->complex) (lift x) = f (lift (drop (lift x) ) )`
      ASSUME_TAC THENL
     [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN REWRITE_TAC [LIFT_DROP] THEN
    SUBGOAL_THEN
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])`
      ASSUME_TAC THENL
     [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
      REWRITE_TAC
        [SET_RULE
           `IMAGE (\x. x) (interval [lift (&0),lift b]) = (interval [lift (&0),lift b])`] THEN
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV];
      REWRITE_TAC [CONTINUOUS_WITHIN] THEN
      UNDISCH_TAC
        `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])` THEN
      REWRITE_TAC [CONTINUOUS_ON] THEN
      DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
      ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
      ONCE_ASM_REWRITE_TAC [LIFT_DROP] THEN ASM_SIMP_TAC []];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `! b s. integral (interval [lift (&0),lift b])
    (\t. Cx (Im (cexp (--(s * Cx (drop t))) * (f:real^1->complex) t))) =
      Cx (real_integral (real_interval [&0, b])
        (\x:real. (\t. (Im (cexp (--(s * Cx (drop t))) * f t))) (lift x) )  )`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    SUBGOAL_THEN
      `!t. (Im (cexp (--(s * Cx (drop t))) * f t)) = 
    (\t. (Im (cexp (--(s * Cx (t))) * f (lift t))) ) (drop t)`
      ASSUME_TAC THENL
     [SIMP_TAC [LIFT_DROP]; ALL_TAC] THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CX_HAS_REAL_INTERGRAL THEN
    SIMP_TAC [LIFT_DROP] THEN MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN]] THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE]; ALL_TAC] THEN
    REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
    REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
    SUBGOAL_THEN `(f:real^1->complex) (lift x) = f (lift (drop (lift x) ) )`
      ASSUME_TAC THENL
     [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
    REWRITE_TAC [LIFT_DROP] THEN
    SUBGOAL_THEN
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])`
      ASSUME_TAC THENL
     [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
      REWRITE_TAC
        [SET_RULE
           `IMAGE (\x. x) (interval [lift (&0),lift b]) = (interval [lift (&0),lift b])`] THEN
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV];
      REWRITE_TAC [CONTINUOUS_WITHIN] THEN
      UNDISCH_TAC
        `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])` THEN
      REWRITE_TAC [CONTINUOUS_ON] THEN
      DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
      ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
      ONCE_ASM_REWRITE_TAC [LIFT_DROP] THEN ASM_SIMP_TAC []];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `?k. ((\b. real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
     f (lift x))))) ---> k) at_posinfinity`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_COMPARISON_TEST THEN
    EXISTS_TAC
      `(\t. norm (cexp (--((ii * Cx w) * Cx (drop (lift t)))) * (f (lift t) ) ))` THEN
    STRIP_TAC THENL
     [REPEAT STRIP_TAC THENL
       [REAL_ARITH_TAC; SIMP_TAC [COMPLEX_NORM_GE_RE_IM]];
      ALL_TAC] THEN
    SIMP_TAC [REAL_ARITH `&0 <= &0`] THEN STRIP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [REAL_INTEGRABLE_ON] THEN REWRITE_TAC [o_DEF] THEN
      SIMP_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN
      MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      SUBGOAL_THEN
        `lift o norm o (\x. cexp (--((ii * Cx w) * Cx (drop (lift (drop x))))) * f (lift (drop x))) = (lift o norm) o (\x. cexp (--((ii * Cx w) * Cx (drop (lift (drop x))))) * f (lift (drop x)))`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN
        SIMP_TAC [];
        ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [CONTINUOUS_ON_LIFT_NORM] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN SIMP_TAC [LIFT_DROP] THEN
      CONJ_TAC THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THENL
       [SIMP_TAC [CONTINUOUS_ON_CEXP] THEN SIMP_TAC [GSYM COMPLEX_MUL_LNEG] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
        SIMP_TAC [CONTINUOUS_ON_CONST] THEN REWRITE_TAC [GSYM o_DEF] THEN
        REWRITE_TAC [CONTINUOUS_ON_CX_DROP];
        SIMP_TAC [CONTINUOUS_ON_ID] THEN
        REWRITE_TAC
          [SET_RULE
             `IMAGE (\x. x) (interval [lift (&0),lift b]) = (interval [lift (&0),lift b])`] THEN
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV]];
      CONJ_TAC THENL
       [ALL_TAC;
        GEN_TAC THEN REWRITE_TAC [LIFT_DROP] THEN
        MATCH_MP_TAC ABS_RE_REAL_FOURIER_INTEGRABLE THEN
        REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
       ASM_SIMP_TAC []] THEN
      REWRITE_TAC [COMPLEX_NORM_MUL] THEN REWRITE_TAC [LIFT_DROP] THEN
      SIMP_TAC [NORM_CEXP] THEN ONCE_REWRITE_TAC [RE_NEG] THEN
      REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((x * y) * z) = (x * ((y:complex) * z))`] THEN
      REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [RE_MUL_CX] THEN
      REWRITE_TAC [RE_II] THEN
      REWRITE_TAC [REAL_ARITH `-- ((&0) * y * z) = (&0)`] THEN
      REWRITE_TAC [REAL_EXP_0] THEN
      REWRITE_TAC [REAL_ARITH `((&1) * x) = (x)`] THEN
      ASM_SIMP_TAC [ABS_INTEG_IMP_NORM_FUN_POSINFINITY]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `?k. ((\b.  real_integral (real_interval [&0,b])
    (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
      f (lift x))))) ---> k) at_posinfinity`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_COMPARISON_TEST THEN
    EXISTS_TAC
      `(\t. norm (cexp (--((ii * Cx w) * Cx (drop (lift t)))) * (f (lift t) ) ))` THEN
    STRIP_TAC THENL
     [REPEAT STRIP_TAC THENL
       [REAL_ARITH_TAC; SIMP_TAC [COMPLEX_NORM_GE_RE_IM]];
      ALL_TAC] THEN
    SIMP_TAC [REAL_ARITH `&0 <= &0`] THEN STRIP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [REAL_INTEGRABLE_ON] THEN REWRITE_TAC [o_DEF] THEN
      SIMP_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN
      MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      SUBGOAL_THEN
        `lift o norm o (\x. cexp (--((ii * Cx w) * Cx (drop (lift (drop x))))) * f (lift (drop x))) = (lift o norm) o (\x. cexp (--((ii * Cx w) * Cx (drop (lift (drop x))))) * f (lift (drop x)))`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN
        SIMP_TAC [];
        ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [CONTINUOUS_ON_LIFT_NORM] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN SIMP_TAC [LIFT_DROP] THEN
      CONJ_TAC THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THENL
       [SIMP_TAC [CONTINUOUS_ON_CEXP] THEN SIMP_TAC [GSYM COMPLEX_MUL_LNEG] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
        SIMP_TAC [CONTINUOUS_ON_CONST] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        REWRITE_TAC [CONTINUOUS_ON_CX_DROP];
        SIMP_TAC [CONTINUOUS_ON_ID] THEN
        REWRITE_TAC
          [SET_RULE
             `IMAGE (\x. x) (interval [lift (&0),lift b]) = (interval [lift (&0),lift b])`] THEN
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV]];
      CONJ_TAC THENL
       [ALL_TAC;
        GEN_TAC THEN REWRITE_TAC [LIFT_DROP] THEN
        MATCH_MP_TAC ABS_IM_REAL_FOURIER_INTEGRABLE THEN
        REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
       ASM_SIMP_TAC []] THEN
      REWRITE_TAC [COMPLEX_NORM_MUL] THEN REWRITE_TAC [LIFT_DROP] THEN
      SIMP_TAC [NORM_CEXP] THEN ONCE_REWRITE_TAC [RE_NEG] THEN
      REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((x * y) * z) = (x * ((y:complex) * z))`] THEN
      REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [RE_MUL_CX] THEN
      REWRITE_TAC [RE_II] THEN
      REWRITE_TAC [REAL_ARITH `-- ((&0) * y * z) = (&0)`] THEN
      REWRITE_TAC [REAL_EXP_0] THEN
      REWRITE_TAC [REAL_ARITH `((&1) * x) = (x)`] THEN
      ASM_SIMP_TAC [ABS_INTEG_IMP_NORM_FUN_POSINFINITY]];
    UNDISCH_TAC
      `?k. ((\b. real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
     f (lift x))))) ---> k) at_posinfinity` THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC
      `?k. ((\b.  real_integral (real_interval [&0,b])
    (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
      f (lift x))))) ---> k) at_posinfinity` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `?m. ((\b. real_integral (real_interval [&0,b])
    (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
      Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)))) --->  m)  at_posinfinity`
      ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_COMPARISON_TEST THEN
      EXISTS_TAC
        `(\x. &2 * abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) )` THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THENL
         [SIMP_TAC [REAL_ABS_LE; REAL_SUB_LE];
          SIMP_TAC [REAL_MUL_2] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
        SIMP_TAC [LIFT_DROP] THEN MATCH_MP_TAC ABS_RE_REAL_FOURIER_INTEGRABLE THEN
        REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
        ASM_SIMP_TAC [];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN
          `!b. real_integral (real_interval [&0,b])
   (\x. &2 *  abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)))) = &2 * real_integral (real_interval [&0,b])(\x.  abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))))`
          ASSUME_TAC THENL
         [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
          SIMP_TAC [LIFT_DROP] THEN
          MATCH_MP_TAC ABS_RE_REAL_FOURIER_INTEGRABLE THEN
          REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
          ASM_SIMP_TAC [];
          ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
          SUBGOAL_THEN
            `?k. ((\b. real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
     f (lift x))))) ---> k) at_posinfinity`
            ASSUME_TAC THENL
           [EXISTS_TAC `k:real` THEN ASM_SIMP_TAC []; ALL_TAC] THEN
          EXISTS_TAC `&2 * k:real` THEN
          SUBGOAL_THEN
            `!b. &2 *  real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) ) =
    (\b. &2)b * (\ b . real_integral (real_interval [&0,b])
     (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) )) b`
            ASSUME_TAC THENL
           [SIMP_TAC []; ALL_TAC] THEN
          ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC REALLIM_MUL THEN
          SIMP_TAC [REALLIM_CONST] THEN ASM_SIMP_TAC []];
        GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
        SIMP_TAC [LIFT_DROP] THENL
         [MATCH_MP_TAC ABS_RE_REAL_FOURIER_INTEGRABLE;
          MATCH_MP_TAC RE_REAL_FOURIER_INTEGRABLE] THEN
        REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
       ASM_SIMP_TAC []];
      SUBGOAL_THEN
        `?m. ((\b. real_integral (real_interval [&0,b])
  (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
     Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)))) --->  m) at_posinfinity`
        ASSUME_TAC THENL
       [MATCH_MP_TAC INTEGRAL_COMPARISON_TEST THEN
        EXISTS_TAC
          `(\x. &2 * abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *f (lift x))) )` THEN
        CONJ_TAC THENL
         [REPEAT STRIP_TAC THENL
           [SIMP_TAC [REAL_ABS_LE; REAL_SUB_LE];
            SIMP_TAC [REAL_MUL_2] THEN REAL_ARITH_TAC];
          ALL_TAC] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
         [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
          SIMP_TAC [LIFT_DROP] THEN
          MATCH_MP_TAC ABS_IM_REAL_FOURIER_INTEGRABLE THEN
          REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
          ASM_SIMP_TAC [];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN
            `!b. real_integral (real_interval [&0,b]) (\x. &2 *  abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
    f (lift x)))) = &2 * real_integral (real_interval [&0,b])
      (\x.  abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))))`
            ASSUME_TAC THENL
           [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
            SIMP_TAC [LIFT_DROP] THEN
            MATCH_MP_TAC ABS_IM_REAL_FOURIER_INTEGRABLE THEN
            REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
            ASM_SIMP_TAC [];
            ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
            SUBGOAL_THEN
              `?k. ((\b.  real_integral (real_interval [&0,b])
    (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) *
      f (lift x))))) ---> k) at_posinfinity`
              ASSUME_TAC THENL
             [EXISTS_TAC `k':real` THEN ASM_SIMP_TAC []; ALL_TAC] THEN
            EXISTS_TAC `&2 * k':real` THEN
            SUBGOAL_THEN
              `!b. &2 *  real_integral (real_interval [&0,b])
   (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) ) =
     (\b. &2)b * (\ b . real_integral (real_interval [&0,b])
      (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) )) b`
              ASSUME_TAC THENL
             [SIMP_TAC []; ALL_TAC] THEN
            ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC REALLIM_MUL THEN
            SIMP_TAC [REALLIM_CONST] THEN ASM_SIMP_TAC []];
          GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
          SIMP_TAC [LIFT_DROP] THENL
           [MATCH_MP_TAC ABS_IM_REAL_FOURIER_INTEGRABLE;
            MATCH_MP_TAC IM_REAL_FOURIER_INTEGRABLE] THEN
          REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
         ASM_SIMP_TAC []];
        UNDISCH_TAC
          `?m. ((\b. real_integral (real_interval [&0,b])
    (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
      Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)))) --->  m)  at_posinfinity` THEN
        REPEAT STRIP_TAC THEN
        UNDISCH_TAC
          `?m. ((\b. real_integral (real_interval [&0,b])
  (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
     Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)))) --->  m) at_posinfinity` THEN
        REPEAT STRIP_TAC THEN EXISTS_TAC `complex (k - m, k' - m')` THEN
        MATCH_MP_TAC LIM_COMPLEX_REAL_COMPONENTS THEN SIMP_TAC [] THEN
        SIMP_TAC [GSYM COMPLEX_TRAD] THEN SIMP_TAC [RE; IM] THEN
        ASM_SIMP_TAC [] THEN CONJ_TAC THENL
         [SUBGOAL_THEN
            `!x. Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * (f:real^1->complex) (lift x)) =
    abs( Re(cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
     ( abs(Re(cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
      Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)) )`
            ASSUME_TAC THENL
           [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
          SUBGOAL_THEN
            `!b. real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
     (abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
       Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))))  =
    real_integral (real_interval [&0,b])
     (\x. abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) ) -
    real_integral (real_interval [&0,b])
     (\x.  abs (Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
       Re (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)) )`
            ASSUME_TAC THENL
           [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
             [SIMP_TAC [LIFT_DROP] THEN
              MATCH_MP_TAC ABS_RE_REAL_FOURIER_INTEGRABLE;
              MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
              SIMP_TAC [LIFT_DROP] THENL
               [MATCH_MP_TAC ABS_RE_REAL_FOURIER_INTEGRABLE;
                MATCH_MP_TAC RE_REAL_FOURIER_INTEGRABLE]] THEN
            REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV];
            ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
            MATCH_MP_TAC REALLIM_SUB] THEN
          ASM_SIMP_TAC [];
          SUBGOAL_THEN
            `!x. Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * (f:real^1->complex) (lift x)) =
   abs( Im(cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
    ( abs(Im(cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
     Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)) )`
            ASSUME_TAC THENL
           [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
          SUBGOAL_THEN
            `!b. real_integral (real_interval [&0,b])
    (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
      (abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
      Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))))  =
    real_integral (real_interval [&0,b])
      (\x. abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) ) -
    real_integral (real_interval [&0,b])
      (\x.  abs (Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x))) -
             Im (cexp (--((ii * Cx w) * Cx (drop (lift x)))) * f (lift x)) )`
            ASSUME_TAC THENL
           [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
             [SIMP_TAC [LIFT_DROP] THEN
              MATCH_MP_TAC ABS_IM_REAL_FOURIER_INTEGRABLE;
              MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
              SIMP_TAC [LIFT_DROP] THENL
               [MATCH_MP_TAC ABS_IM_REAL_FOURIER_INTEGRABLE;
                MATCH_MP_TAC IM_REAL_FOURIER_INTEGRABLE]] THEN
            REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV];
            ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
            MATCH_MP_TAC REALLIM_SUB] THEN
          ASM_SIMP_TAC []]]]]);;

(*=======================================================*)
(*              FOURIER_UNILATERAL_ALT_REP_2             *)
(*=======================================================*)

let FOURIER_UNILATERAL_ALT_REP_2 = prove
 (`!(f:real^1->complex) w. fourier_exists f ==>
  (integral (IMAGE (--) {t | &0 <= drop t})
 (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t) ) =
    ( lim at_posinfinity
         (\a. integral (IMAGE (--) (interval [vec 0, lift a]))
              (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t)) )`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  REWRITE_TAC [GSYM HAS_INTEGRAL_REFLECT_GEN] THEN
  REWRITE_TAC [HAS_INTEGRAL_LIM_AT_POSINFINITY] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM LIFT_NUM] THENL
   [ALL_TAC;
    REWRITE_TAC [GSYM INTEGRAL_REFLECT_GEN] THEN REWRITE_TAC [GSYM FUN_LIM] THEN
    REWRITE_TAC [convergent_f] THEN
    MATCH_MP_TAC LIM_FOURIER_EXISTS_LEMMA_2 THEN
    ASM_SIMP_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV]] THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC [DROP_NEG; CX_NEG] THEN REWRITE_TAC [COMPLEX_MUL_RNEG] THEN
    ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
    SIMP_TAC [CEXP_S_T_CONTINUOUS];
    ONCE_REWRITE_TAC [VECTOR_ARITH `!x:real^1 a f. (--(x)) = (--(&1) % x)`] THEN
    ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC [CONTINUOUS_ON_ID];
      ONCE_REWRITE_TAC [VECTOR_ARITH `!x:real^1 a f. (--(&1) % x) = (--(x))`] THEN
      REWRITE_TAC [ETA_AX] THEN
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV_ALT_1]]]);;

(*==================================================================*)
(*                     FOURIER_EXISTS_INTEGRABLE                    *)
(*==================================================================*)

let FOURIER_EXISTS_INTEGRABLE = prove
 (`!(f:real^1->complex) (s:complex) (a:real).
     fourier_exists f ==> 
       (\ (t:real^1).( cexp(--(s * Cx(drop(t)))) * (f t))) integrable_on interval [lift (&0),lift(a)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [CEXP_S_T_CONTINUOUS];
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV]]);;

(*==================================================================*)
(*                  FOURIER_EXISTS_INTEGRABLE_ALT                   *)
(*==================================================================*)

let FOURIER_EXISTS_INTEGRABLE_ALT = prove
 (`!(f:real^1->complex) (w:real) (a:real).
     fourier_exists f ==> 
       (\ (t:real^1).( cexp(--((ii * Cx (w)) * Cx(drop(t)))) * (f t))) integrable_on interval [lift (&0),lift(a)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [CEXP_S_T_CONTINUOUS];
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV]]);;

(*==================================================================*)
(*                    FOURIER_EXISTS_INTEGRABLE_1                   *)
(*==================================================================*)

let FOURIER_EXISTS_INTEGRABLE_1 =  prove
 (`!(f:real^1->complex) (s:complex) (a:real^1).
     fourier_exists f ==> 
       (\ (t:real^1).( cexp(--(s * Cx(drop(t)))) * (f t))) integrable_on interval [a,lift (&0)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [CEXP_S_T_CONTINUOUS_GEN];
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV_1]]);;

(*==================================================================*)
(*                    LIM_TRANSFORM_BOUND_1                         *)
(*==================================================================*)

let LIM_TRANSFORM_BOUND_1 = prove
 (`!(f:real->complex) (g:real->complex) net.
         eventually (\n. norm (f n) <= norm (g n)) net /\ (g --> vec 0) net
         ==> (f --> vec 0) net`,
  REWRITE_TAC [LIM_TRANSFORM_BOUND]);;

(*==================================================================*)
(*                FUNLIM_POSINF_EQ_FUNLIM_NEGINF                    *)
(*==================================================================*)

let FUNLIM_POSINF_EQ_FUNLIM_NEGINF = prove
 (`!(f:real^1->complex). 
    (((\x. f (lift x)) --> vec 0) at_neginfinity) <=> 
    (((\x. f (--lift x)) --> vec 0) at_posinfinity)`,
  GEN_TAC THEN REWRITE_TAC [LIM_AT_POSINFINITY; LIM_AT_NEGINFINITY] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [UNDISCH_TAC
      `!e. &0 < e ==> (?b. !x. x <= b ==> dist ((f:real^1->complex) (lift x),vec 0) < e)` THEN
    DISCH_THEN (MP_TAC o SPEC `e:real`) THEN ASM_SIMP_TAC [] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `-- b:real` THEN REWRITE_TAC [real_ge] THEN
    ONCE_REWRITE_TAC [REAL_ARITH `!x. (--b <= x:real) = (--x <= b)`] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC
      `!x. x <= b ==> dist ((f:real^1->complex) (lift x),vec 0) < e` THEN
    DISCH_THEN (MP_TAC o SPEC `-- x:real`) THEN ASM_SIMP_TAC [LIFT_NEG];
    UNDISCH_TAC
      `!e. &0 < e ==> (?b. !x. x >= b ==> dist ((f:real^1->complex) (--lift x),vec 0) < e)` THEN
    DISCH_THEN (MP_TAC o SPEC `e:real`) THEN ASM_SIMP_TAC [] THEN
    REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC [real_ge] THEN
    DISCH_TAC THEN EXISTS_TAC `-- b:real` THEN
    ONCE_REWRITE_TAC [REAL_ARITH `!x. (x <= -- b:real) = (b <= -- x)`] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC
      `!x. b <= x ==> dist ((f:real^1->complex) (--lift x),vec 0) < e` THEN
    DISCH_THEN (MP_TAC o SPEC `-- x:real`) THEN ASM_SIMP_TAC [LIFT_NEG] THEN
    REWRITE_TAC
      [VECTOR_ARITH `!(f:real^1->complex). (-- -- lift x) = (lift x)`]]);;

(*==================================================================*)
(*                          LIM_ABS_LIM                             *)
(*==================================================================*)

let LIM_ABS_LIM = prove
 (`!f:real->complex l . ((\i. f(abs i)) --> l) at_posinfinity ==> (f --> l) at_posinfinity`,
  REWRITE_TAC [LIM_AT_POSINFINITY] THEN REWRITE_TAC [real_ge] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`&0`; `b:real`] REAL_LE_TOTAL) THEN STRIP_TAC THENL
   [EXISTS_TAC `b:real` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= x:real` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `b:real`;
      FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN `abs x = x:real` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_ABS_REFL]; ALL_TAC]];
    EXISTS_TAC `&0` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `b:real <= x:real` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0`;
      UNDISCH_TAC `b <= x ==> dist ((f:real->complex) (abs x) ,l) < e` THEN
      ASM_SIMP_TAC [] THEN SUBGOAL_THEN `abs x = x:real` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_ABS_REFL]; ALL_TAC]]] THEN
  ASM_SIMP_TAC []);;

(*==================================================================*)
(*                          LIM_ABS_LIM_1                           *)
(*==================================================================*)

let LIM_ABS_LIM_1 = prove
 (`!f:real->complex l . (f --> l) at_posinfinity  ==> ((\i. f(abs i)) --> l) at_posinfinity`,
  REWRITE_TAC [LIM_AT_POSINFINITY] THEN REWRITE_TAC [real_ge] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`&0`; `b:real`] REAL_LE_TOTAL) THEN STRIP_TAC THENL
   [EXISTS_TAC `b:real` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= x:real` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `b:real`;
      FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN `abs x = x:real` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_ABS_REFL]; ALL_TAC]];
    EXISTS_TAC `&0` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `b:real <= x:real` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0`;
      UNDISCH_TAC `b <= x ==> dist ((f:real->complex) x , l) < e` THEN
      ASM_SIMP_TAC [] THEN SUBGOAL_THEN `abs x = x:real` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_ABS_REFL]; ALL_TAC]]] THEN
  ASM_SIMP_TAC []);;

(*==================================================================*)
(*                         LIM_ABS_LIM_EQ                           *)
(*==================================================================*)

let LIM_ABS_LIM_EQ = prove
 (`!f:real->real^2 l . (f --> l) at_posinfinity  ==> lim at_posinfinity f = 
   lim at_posinfinity (\x . f(abs x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TENDSTO_LIM THEN
  SIMP_TAC [TRIVIAL_LIMIT_AT_POSINFINITY] THEN
  SUBGOAL_THEN
    `(   (\x. (f:real->complex) (abs x))  --> lim at_posinfinity 
    (\x. f (abs x))) at_posinfinity`
    ASSUME_TAC THENL
   [SIMP_TAC [GSYM FUN_LIM] THEN REWRITE_TAC [convergent_f] THEN
    EXISTS_TAC `l:complex` THEN MATCH_MP_TAC LIM_ABS_LIM_1;
    MATCH_MP_TAC LIM_ABS_LIM] THEN
  ASM_SIMP_TAC []);;

(*==================================================================*)
(*                      INTEGRATION_BY_PARTS_AT                     *)
(*==================================================================*)

let INTEGRATION_BY_PARTS_AT = prove
 (`!(f:real^1->complex) (g:real^1->complex) f' g' a:real^1 b:real^1 .  drop a <= drop b /\ (!x.(f  has_vector_derivative f'(x)) (at x ))  /\
   (!x.(g  has_vector_derivative g'(x)) (at x) )  ==> ((\x. f'(x) * g(x) + f(x) * g'(x)) has_integral (f(b) * g(b) - f(a) * g(a) )) 
     (interval [a , b])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC [SIMPLE_COMPLEX_ARITH `(a:complex) + (b:complex) = b + a`] THEN
  SUBGOAL_THEN
    `((\x. (\x y . x * y) ((f:real^1->complex) x) ((g:real^1->complex) x)) has_vector_derivative
    ((\x y . x * y) (f x) ((g':real^1->complex) x) + (\x y . x * y) ((f':real^1->complex) x) (g x))) (at x within interval [a,b])`
    ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN THEN
    SUBGOAL_THEN `drop a <= drop x /\ drop x <= drop b` ASSUME_TAC THENL
     [ASM_MESON_TAC [IN_INTERVAL_1]; ALL_TAC] THEN
    SUBGOAL_THEN
      `((f:real^1->complex) has_vector_derivative f' x) (at x within interval [a,b])`
      ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC [];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `((g:real^1->complex) has_vector_derivative g' x) (at x within interval [a,b])`
      ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC [];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN REWRITE_TAC [bilinear] THEN CONJ_TAC THEN GEN_TAC THEN
    REWRITE_TAC [linear] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC [COMPLEX_CMUL];
      ALL_TAC;
      REWRITE_TAC [COMPLEX_CMUL]] THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    SUBGOAL_THEN
      `(f:real^1->complex) x * (g':real^1->complex) x + f' x * (g:real^1->complex) x =
   (\x y. x * y) (f x) (g' x) + (\x y. x * y) ((f':real^1->complex) x) (g x)`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN
      `!a. (f:real^1->complex) a * (g:real^1->complex) a = (\x y. x * y) (f a) (g a)`
      ASSUME_TAC THENL
     [SIMP_TAC []; PURE_ONCE_ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC []]]);;

(*==================================================================*)
(*                      INTEGRATION_BY_PARTS_AT                     *)
(*==================================================================*)

let INTEGRAL_BY_PARTS_AT = prove
 (`!(f:real^1->complex) (g:real^1->complex) f' g' a:real^1 b:real^1 .  drop a <= drop b /\
    (!x.  (f  has_vector_derivative f'(x)) (at x) )  /\ (!x. (g  has_vector_derivative g'(x)) (at x) )  
     /\  (\x. f' x * g x) integrable_on  (interval [a,b]) /\ (\x. f x * g' x) integrable_on  (interval [a,b]) ==>
      (integral (interval [a , b])  (\x. f x * g' x) = (f b * g b - f a * g a) - integral (interval [a , b])(\x. f' x * g x))`,
  MP_TAC INTEGRATION_BY_PARTS_AT THEN
  SIMP_TAC [SIMPLE_COMPLEX_ARITH `(x:complex = y - z) <=> (x + z = y)`] THEN
  SIMP_TAC [GSYM INTEGRAL_ADD] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC [SIMPLE_COMPLEX_ARITH `(x + z = y) <=> (x:complex = y - z)`] THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN PURE_ONCE_REWRITE_TAC [COMPLEX_ADD_SYM] THEN
  UNDISCH_TAC
    `!f g f' g' a b. drop a <= drop b /\ (!x. (f has_vector_derivative f' x) (at x)) /\
  (!x. (g has_vector_derivative g' x) (at x)) ==> ((\x. f' x * g x + f x * g' x) has_integral f b * g b - f a * g a)
    (interval [a,b])` THEN
  DISCH_THEN (MP_TAC o SPEC `(f:real^1->complex)`) THEN
  DISCH_THEN (MP_TAC o SPEC `(g:real^1->complex)`) THEN
  DISCH_THEN (MP_TAC o SPEC `(f':real^1->complex)`) THEN
  DISCH_THEN (MP_TAC o SPEC `(g':real^1->complex)`) THEN
  DISCH_THEN (MP_TAC o SPEC `a:real^1`) THEN
  DISCH_THEN (MP_TAC o SPEC `b:real^1`) THEN ASM_SIMP_TAC []);;

(*==================================================================*)
(*                   VECTOR_COMPLEX_DIFF_CHAIN_AT                   *)
(*==================================================================*)

let  VECTOR_COMPLEX_DIFF_CHAIN_AT = prove
 (`!(f:real^1->complex) (g:complex->complex) (f':complex) (g':complex) x .
         (f has_vector_derivative f') (at x) /\
         (g has_complex_derivative g') (at (f x))
         ==> ((g o f) has_vector_derivative (f' * g')) (at x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [has_vector_derivative; has_complex_derivative] THEN
  DISCH_THEN (MP_TAC o MATCH_MP DIFF_CHAIN_AT) THEN
  REWRITE_TAC [o_DEF; COMPLEX_CMUL; COMPLEX_MUL_AC]);;

(*==================================================================*)
(*                             CX_CMUL                              *)
(*==================================================================*)

let CX_CMUL = prove
 (`!c x. c % Cx(x) = Cx( c * x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [COMPLEX_CMUL] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

(*==================================================================*)
(*                 HAS_CX_FRECHET_DERIVATIVE_WITHIN                 *)
(*==================================================================*)

let HAS_CX_FRECHET_DERIVATIVE_WITHIN = prove
 (`(f has_real_derivative f') (atreal x within s) <=>
        ((Cx o f o drop) has_derivative (\x . f' % Cx (drop x ) ))
        (at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC [has_derivative_within; HAS_REAL_DERIVATIVE_WITHINREAL] THEN
  REWRITE_TAC [o_THM; LIFT_DROP; LIM_WITHIN; REALLIM_WITHINREAL] THEN
  SUBGOAL_THEN `linear (\x. f' % Cx (drop x))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN SIMP_TAC [linear] THEN
    SIMP_TAC [DROP_ADD; CX_ADD] THEN SIMP_TAC [DROP_CMUL; CX_CMUL];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN REWRITE_TAC [IMP_CONJ] THEN
  REWRITE_TAC [FORALL_IN_IMAGE] THEN REWRITE_TAC [DIST_LIFT] THEN
  REWRITE_TAC [GSYM LIFT_SUB] THEN REWRITE_TAC [LIFT_DROP] THEN
  REWRITE_TAC [NORM_ARITH `dist(x,vec 0) = norm x`] THEN
  REWRITE_TAC [NORM_LIFT] THEN REWRITE_TAC [CX_CMUL] THEN
  REWRITE_TAC [GSYM CX_ADD] THEN REWRITE_TAC [GSYM CX_SUB] THEN
  REWRITE_TAC [CX_CMUL] THEN REWRITE_TAC [COMPLEX_NORM_CX] THEN
  SIMP_TAC
    [REAL_FIELD
       `&0 < abs(y - x)
    ==> fy - (fx + f' * (y - x)) = (y - x) * ((fy - fx) / (y - x) - f')`] THEN
  REWRITE_TAC [REAL_ABS_MUL; REAL_MUL_ASSOC; REAL_ABS_INV; REAL_ABS_ABS] THEN
  SIMP_TAC [REAL_LT_IMP_NZ; REAL_MUL_LINV; REAL_MUL_LID]);;

(*==================================================================*)
(*                   HAS_CX_FRECHET_DERIVATIVE_AT                   *)
(*==================================================================*)

let HAS_CX_FRECHET_DERIVATIVE_AT = prove
 (`(f has_real_derivative f') (atreal x) <=>
      ((Cx o f o drop) has_derivative (\x . f' % Cx (drop x ) ))(at (lift x))`,
  ONCE_REWRITE_TAC [GSYM WITHINREAL_UNIV; GSYM WITHIN_UNIV] THEN
  REWRITE_TAC [HAS_CX_FRECHET_DERIVATIVE_WITHIN] THEN
  REWRITE_TAC [IMAGE_LIFT_UNIV]);;

(*==================================================================*)
(*                    HAS_CX_VECTOR_DERIVATIVE_AT                   *)
(*==================================================================*)

let HAS_CX_VECTOR_DERIVATIVE_AT = prove
 (`(f has_real_derivative f') (atreal x ) <=>
        ((Cx o f o drop) has_vector_derivative (Cx f'))
        (at (lift x))`,
  REWRITE_TAC [has_vector_derivative; HAS_CX_FRECHET_DERIVATIVE_AT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC [FUN_EQ_THM; CX_CMUL; REAL_MUL_SYM]);;

(*==================================================================*)
(*                      HAS_COMPLEX_INTEGRAL_CMUL                   *)
(*==================================================================*)

let HAS_COMPLEX_INTEGRAL_CMUL = prove
  (`!(f:real^1->complex) k s c:complex.
   (f has_integral k) s  ==> ((\x. c * f(x)) has_integral (c * k)) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
   (REWRITE_RULE[o_DEF] HAS_INTEGRAL_LINEAR) THEN
  ASM_REWRITE_TAC[linear] THEN REWRITE_TAC[COMPLEX_CMUL] THEN SIMPLE_COMPLEX_ARITH_TAC);;

(*==================================================================*)
(*                        COMPLEX_INTEGRAL_CMUL                     *)
(*==================================================================*)

let COMPLEX_INTEGRAL_CMUL = prove
  (`!f:real^1->complex c s.  f integrable_on s ==> integral s (\x. c * f(x)) = c * integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_COMPLEX_INTEGRAL_CMUL THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

(*==================================================================*)
(*                     FOURIER_DIFF_THEOREM_AT                      *)
(*==================================================================*)

let FOURIER_DIFF_THEOREM_AT = prove
 (`!(f:real^1->complex) f' (w:real).
    (((\x. f (lift x)) --> vec 0) at_posinfinity) /\
    (((\x. f (lift x)) --> vec 0) at_neginfinity) /\
    fourier_exists f /\ fourier_exists f' /\ (!x. (f has_vector_derivative f' x) (at x))  ==>
     (fourier_comp f' w = (ii * Cx (w) * (fourier_comp f w)))`,
  REWRITE_TAC [fourier_comp] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [UNIV_SET_BREAK] THEN
  SUBGOAL_THEN
    `integral ({x | &0 <= drop x} UNION IMAGE (--) {x | &0 <= drop x}) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * (f':real^1->complex) t) = 
    integral {t | &0 <= drop t} (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f' t) + integral (IMAGE (--) {t | &0 <= drop t}) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f' t)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_1 THEN 
    ASM_SIMP_TAC []; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_2 THEN 
      ASM_SIMP_TAC []; ALL_TAC] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{(vec 0):real^1}` THEN
    REWRITE_TAC [NEGLIGIBLE_SING] THEN
    REWRITE_TAC
      [IN_ELIM_THM;
       SET_RULE
         `s INTER IMAGE f s SUBSET {a} <=> !x. x IN s /\ f x IN s ==> f x = a`] THEN
    REWRITE_TAC [GSYM LIFT_NUM] THEN REWRITE_TAC [DROP_NEG] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM DROP_EQ] THEN
    REWRITE_TAC [LIFT_DROP] THEN REWRITE_TAC [DROP_NEG] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `integral ({x | &0 <= drop x} UNION IMAGE (--) {x | &0 <= drop x}) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * (f:real^1->complex) t) = 
    integral {t | &0 <= drop t} (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t) + integral (IMAGE (--) {t | &0 <= drop t}) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_1 THEN 
     ASM_SIMP_TAC []; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_2 THEN 
      ASM_SIMP_TAC []; ALL_TAC] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{(vec 0):real^1}` THEN
    REWRITE_TAC [NEGLIGIBLE_SING] THEN
    REWRITE_TAC
      [IN_ELIM_THM;
       SET_RULE
         `s INTER IMAGE f s SUBSET {a} <=> !x. x IN s /\ f x IN s ==> f x = a`] THEN
    REWRITE_TAC [GSYM LIFT_NUM] THEN REWRITE_TAC [DROP_NEG] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM DROP_EQ] THEN
    REWRITE_TAC [LIFT_DROP] THEN REWRITE_TAC [DROP_NEG] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [COMPLEX_ADD_LDISTRIB] THEN 
  ASM_SIMP_TAC [FOURIER_UNILATERAL_ALT_REP_1] THEN
  ASM_SIMP_TAC [FOURIER_UNILATERAL_ALT_REP_2] THEN
  SUBGOAL_THEN
    `( lim at_posinfinity
 (\b. integral (interval [vec 0,lift b])
      (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f' t)) ) =
    ( (ii *
 Cx w *
 lim at_posinfinity
 (\b. integral (interval [vec 0,lift b])
      (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t))) - f (lift (&0)) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [GSYM LIFT_NUM] THEN
    SUBGOAL_THEN
      `lim at_posinfinity (\b. integral (interval [lift (&0),lift b]) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f' t))=
   lim at_posinfinity (\b. (\b. integral (interval [lift (&0),lift (b)]) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f' t)) (abs b))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC LIM_ABS_LIM_EQ THEN
      ASM_SIMP_TAC [LIM_FOURIER_EXISTS_LEMMA_1];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `lim at_posinfinity (\b. integral (interval [lift (&0),lift b]) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t)) =
   lim at_posinfinity (\b. (\b. integral (interval [lift (&0),lift (b)]) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t)) (abs b))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC LIM_ABS_LIM_EQ THEN
      ASM_SIMP_TAC [LIM_FOURIER_EXISTS_LEMMA_1];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `!b s. integral (interval [lift (&0),lift (abs b)]) (\t. (\t. cexp (--(s * Cx (drop t)))) t * (f':real^1->complex) t) =
    ((\ t . cexp (--(s * Cx (drop t)))  ) (lift (abs b) ) ) * ((f:real^1->complex) (lift (abs b)) ) - ((\ t . cexp (--(s * Cx (drop t)))  ) (lift (&0) ) ) * (f (lift (&0)) ) 
     - (integral (interval [lift (&0),lift (abs b)]) (\t. (\t. cexp (--(s * Cx (drop t))) * (--s)) t * f t) )`
      ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRAL_BY_PARTS_AT THEN CONJ_TAC THENL
       [SIMP_TAC [LIFT_DROP] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [SIMP_TAC [LIFT_DROP] THEN REPEAT STRIP_TAC THEN
        ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
        ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        PURE_ONCE_REWRITE_TAC [COMPLEX_MUL_AC] THEN
        MATCH_MP_TAC VECTOR_COMPLEX_DIFF_CHAIN_AT THEN CONJ_TAC THENL
         [ALL_TAC;
          SIMP_TAC [] THEN
          SUBGOAL_THEN `(Cx (drop t) * --s)=(--s * Cx (drop t) )` ASSUME_TAC THENL
           [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
          ONCE_ASM_SIMP_TAC [] THEN SIMP_TAC [HAS_COMPLEX_DERIVATIVE_CEXP]] THEN
        PURE_ONCE_REWRITE_TAC [COMPLEX_MUL_AC] THEN
        SUBGOAL_THEN
          `((\t. --s * Cx (drop t)) has_vector_derivative --s) (at t) = ((\t. (\x y. x * y) ((\x:real^1. --s:complex) t)
   ((\x. Cx (drop x))  t)) has_vector_derivative (\x y. x * y) ((\x:real^1. --s:complex) t) (Cx (&1)) +
    (\x y. x * y) (Cx (&0)) ((\x. Cx (drop x))  t)) (at t)`
          ASSUME_TAC THENL
         [SIMP_TAC [] THEN
          SIMP_TAC [COMPLEX_MUL_RID; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID];
          ALL_TAC] THEN
        ONCE_ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_BILINEAR_AT THEN
        SIMP_TAC [GSYM COMPLEX_VEC_0] THEN
        SIMP_TAC [HAS_VECTOR_DERIVATIVE_CONST] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `(\x. Cx (drop x)) = Cx o (\x . x) o drop` ASSUME_TAC THENL
           [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
          ONCE_ASM_SIMP_TAC [] THEN REWRITE_TAC [INTERVAL_REAL_INTERVAL] THEN
          ONCE_REWRITE_TAC [LIFT_DROP] THEN ONCE_REWRITE_TAC [GSYM LIFT_DROP] THEN
          ONCE_REWRITE_TAC [GSYM HAS_CX_VECTOR_DERIVATIVE_AT] THEN
          ONCE_REWRITE_TAC [LIFT_DROP] THEN
          REWRITE_TAC [HAS_REAL_DERIVATIVE_ID];
          REWRITE_TAC [bilinear] THEN CONJ_TAC THEN GEN_TAC THEN
          REWRITE_TAC [linear] THEN CONJ_TAC THENL
           [ALL_TAC;
            REWRITE_TAC [COMPLEX_CMUL];
            ALL_TAC;
            REWRITE_TAC [COMPLEX_CMUL]] THEN
          SIMPLE_COMPLEX_ARITH_TAC];
        CONJ_TAC THENL
         [SIMP_TAC [LIFT_DROP] THEN REPEAT STRIP_TAC;
          SIMP_TAC [] THEN CONJ_TAC THENL
           [SIMP_TAC
              [SIMPLE_COMPLEX_ARITH `(x * y) * z = y:complex * (x * z)`] THEN
            MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
            MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
            SIMP_TAC [CONTINUOUS_ON_CONST] THEN
            MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
            SIMP_TAC [CEXP_S_T_CONTINUOUS] THEN
            MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
            UNDISCH_TAC `fourier_exists f` THEN 
            REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
            REPEAT STRIP_TAC THEN
            MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_SUBSET_UNIV;
            MP_TAC FOURIER_EXISTS_INTEGRABLE THEN
            DISCH_THEN (MP_TAC o SPEC `f':real^1->complex`) THEN
            DISCH_THEN (MP_TAC o SPEC `s:real^2`) THEN
            DISCH_THEN (MP_TAC o SPEC `abs(b:real)`)]] THEN
        ASM_SIMP_TAC []];
      SUBGOAL_THEN
        `!b s. integral (interval [lift (&0),lift (abs b)])(\t. cexp (--(s * Cx (drop t))) * f' t)=
   integral (interval [lift (&0),lift (abs b)]) (\t. (\t. cexp (--(s * Cx (drop t)))) t * f' t)`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      POP_ASSUM (K ALL_TAC) THEN
      SIMP_TAC
        [LIFT_DROP; COMPLEX_MUL_RZERO; COMPLEX_NEG_0; CEXP_0; COMPLEX_MUL_LID] THEN
      SUBGOAL_THEN
        `!s. s * lim at_posinfinity (\b. integral (interval [lift (&0),lift (abs b)])
   (\t. cexp (--(s * Cx (drop t))) * f t)) - f (lift (&0)) = Cx(&0) - ( --s * lim at_posinfinity
    (\b. integral (interval [lift (&0),lift (abs b)])
     (\t. cexp (--(s * Cx (drop t))) * f t)) +  f (lift (&0)))`
        ASSUME_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN ASM_SIMP_TAC [] THEN
      POP_ASSUM (K ALL_TAC) THEN
      SIMP_TAC [SIMPLE_COMPLEX_ARITH `(x * --y)* z:complex = --x * y * z`] THEN
      SUBGOAL_THEN
        `!b s. cexp (--(s * Cx (abs b))) * f (lift (abs b)) - f (lift (&0)) -
    integral (interval [lift (&0),lift (abs b)])(\t. --cexp (--(s * Cx (drop t))) * s * f t)  =
    (\b. cexp (--(s * Cx (abs b))) * f (lift (abs b))) b - (\b. (\b. integral (interval [lift (&0),lift (abs b)])
     (\t. --cexp (--(s * Cx (drop t))) * s * f t) ) b + (\b. f (lift (&0) ) )b) b`
        ASSUME_TAC THENL
       [SIMP_TAC [] THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC TENDSTO_LIM THEN SIMP_TAC [TRIVIAL_LIMIT_AT_POSINFINITY] THEN
      MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THENL
       [SIMP_TAC [GSYM COMPLEX_VEC_0] THEN UNDISCH_TAC `fourier_exists f` THEN
        UNDISCH_TAC `fourier_exists f'` THEN 
       REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
        REPEAT STRIP_TAC THEN
        UNDISCH_TAC
          `(f:real^1->complex) absolutely_integrable_on {x | &0 <= drop x}` THEN
        UNDISCH_TAC
          `(f':real^1->complex) absolutely_integrable_on {x | &0 <= drop x}` THEN
        REWRITE_TAC [absolutely_integrable_on] THEN
        REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC LIM_TRANSFORM_BOUND_1 THEN
        EXISTS_TAC `(\x. (f:real^1->complex) (lift (abs x)))` THEN CONJ_TAC THENL
         [ALL_TAC;
          SUBGOAL_THEN
            `((\x. (f:real^1->complex) (lift x)) --> vec 0) at_posinfinity 
    ==> ((\x. f (lift (abs x))) --> vec 0) at_posinfinity`
            ASSUME_TAC THENL
           [DISCH_TAC THEN MATCH_MP_TAC LIM_ABS_LIM_1;
            POP_ASSUM MP_TAC THEN DISCH_THEN MATCH_MP_TAC] THEN
          ASM_SIMP_TAC []] THEN
        SUBGOAL_THEN
          `!n. norm (cexp (--((ii * Cx w) * Cx (abs n))) * f (lift (abs n))) <= norm ((f:real^1->complex) (lift (abs n)))`
          ASSUME_TAC THENL
         [ALL_TAC; ASM_SIMP_TAC [] THEN REWRITE_TAC [EVENTUALLY_TRUE]] THEN
        GEN_TAC THEN REWRITE_TAC [COMPLEX_NORM_MUL] THEN
        REWRITE_TAC [NORM_CEXP] THEN REWRITE_TAC [RE_NEG] THEN
        REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN
        REWRITE_TAC
          [SIMPLE_COMPLEX_ARITH
             `((ii * Cx w) * Cx (abs n)) = (ii * Cx w * Cx (abs n))`] THEN
        REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [RE_MUL_CX] THEN
        REWRITE_TAC [RE_II] THEN
        REWRITE_TAC [REAL_ARITH `(--(&0 * w * abs n)) = &0`] THEN
        REWRITE_TAC [REAL_EXP_0] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC LIM_ADD THEN SIMP_TAC [LIM_CONST] THEN
        SUBGOAL_THEN
          `!b t. (--cexp (--((ii * Cx w) * Cx (drop t))) * (ii * Cx w) * f t) = (-- (ii * Cx w) * (cexp (--((ii * Cx w) * Cx (drop t)))) * f t)`
          ASSUME_TAC THENL
         [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
        SUBGOAL_THEN
          `!b s. integral (interval [lift (&0),lift (abs b)])(\t. --s * cexp (--(s * Cx (drop t))) * f t) =
    --s * integral (interval [lift (&0),lift (abs b)]) (\t. cexp (--(s * Cx (drop t))) * (f:real^1->complex) t)`
          ASSUME_TAC THENL
         [REPEAT GEN_TAC THEN
          SUBGOAL_THEN
            `(\t. --s * cexp (--(s * Cx (drop t))) * (f:real^1->complex) t) =
   (\t.  --s  * (\t. cexp (--(s * Cx (drop t))) * f t) t)`
            ASSUME_TAC THENL
           [SIMP_TAC []; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
          MATCH_MP_TAC COMPLEX_INTEGRAL_CMUL THEN 
          MATCH_MP_TAC FOURIER_EXISTS_INTEGRABLE THEN
          ASM_SIMP_TAC [];
          ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
          MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
          SUBGOAL_THEN
            `!s. lim at_posinfinity (\b. integral (interval [lift (&0),lift (abs b)])(\t. cexp (--(s * Cx (drop t))) * f t)) =
   lim at_posinfinity (\b. (\x. integral (interval [lift (&0),lift (x)])(\t. cexp (--(s * Cx (drop t))) * f t)) (abs b))`
            ASSUME_TAC THENL
           [SIMP_TAC []; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
          SUBGOAL_THEN
            `lim at_posinfinity (\b. (\x. integral (interval [lift (&0),lift x])
     (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t))(abs b)) = lim at_posinfinity (\b. integral (interval [lift (&0),lift (b)])
       (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t))`
            ASSUME_TAC THENL
           [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC LIM_ABS_LIM_EQ;
            ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LIM_ABS_LIM_1 THEN
            SIMP_TAC [GSYM FUN_LIM] THEN REWRITE_TAC [convergent_f]] THEN
          MATCH_MP_TAC LIM_FOURIER_EXISTS_LEMMA_1 THEN ASM_SIMP_TAC []]]];
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH
         `(((a:complex) - b + c) = (a + d)) = (c = (b + d))`] THEN
    REWRITE_TAC [GSYM LIFT_NUM] THEN REWRITE_TAC [GSYM INTEGRAL_REFLECT_GEN] THEN
    SUBGOAL_THEN
      `lim at_posinfinity (\b. integral (interval [lift (&0),lift b]) (\t. cexp (--((ii * Cx w) * Cx (drop (--t)))) * f' (--t))) =
   lim at_posinfinity (\b. (\b. integral (interval [lift (&0),lift (b)]) (\t. cexp (--((ii * Cx w) * Cx (drop (--t)))) * f' (--t))) (abs b))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC LIM_ABS_LIM_EQ THEN
      ASM_SIMP_TAC [LIM_FOURIER_EXISTS_LEMMA_2];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `lim at_posinfinity (\b. integral (interval [lift (&0),lift b]) (\t. cexp (--((ii * Cx w) * Cx (drop (--t)))) * f (--t))) =
   lim at_posinfinity (\b. (\b. integral (interval [lift (&0),lift (b)]) (\t. cexp (--((ii * Cx w) * Cx (drop (--t)))) * f (--t))) (abs b))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC LIM_ABS_LIM_EQ THEN
      ASM_SIMP_TAC [LIM_FOURIER_EXISTS_LEMMA_2];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `(lim at_posinfinity
 (\a. integral (interval [lift (&0),lift (abs a)])
      (\x. cexp (--((ii * Cx w) * Cx (drop (--x)))) * (f':real^1->complex) (--x))) =
 f (lift (&0)) +
 ii *
 Cx w *
 lim at_posinfinity
 (\a. integral (interval [lift (&0),lift (abs a)])
      (\x. cexp (--((ii * Cx w) * Cx (drop (--x)))) * f (--x)))) 
     = (lim at_posinfinity
 (\a. integral (IMAGE (--) (interval [lift (&0),lift (abs a)]))
      (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f' t)) =
 f (lift (&0)) +
 ii *
 Cx w *
 lim at_posinfinity
 (\a. integral (IMAGE (--) (interval [lift (&0),lift (abs a)]))
      (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t)))`
      ASSUME_TAC THENL
     [REWRITE_TAC [INTEGRAL_REFLECT_GEN]; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `!a. (IMAGE (--) (interval [lift (&0),lift (a)])) = (interval [--lift (a),lift (&0)])`
      ASSUME_TAC THENL
     [REWRITE_TAC [EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTERVAL_1] THEN
      REWRITE_TAC [DROP_NEG; LIFT_DROP] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
      REPEAT STRIP_TAC THENL
       [ALL_TAC;
        ALL_TAC;
        EXISTS_TAC `--(x:real^1)` THEN STRIP_TAC THENL
         [VECTOR_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC [DROP_NEG] THEN ASM_REAL_ARITH_TAC] THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [DROP_NEG] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `!b s. integral (interval [--(lift (abs b)),lift (&0)]) (\t. (\t. cexp (--(s * Cx (drop t)))) t * (f':real^1->complex) t) =
    ((\ t . cexp (--(s * Cx (drop t)))  ) (lift (&0) ) ) * ((f:real^1->complex) (lift (&0)) ) - ((\ t . cexp (--(s * Cx (drop t)))  ) (--(lift (abs b)) ) ) * (f (--(lift (abs b))) ) 
     - (integral (interval [--(lift (abs b)),lift (&0)]) (\t. (\t. cexp (--(s * Cx (drop t))) * (--s)) t * f t) )`
      ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRAL_BY_PARTS_AT THEN CONJ_TAC THENL
       [SIMP_TAC [DROP_NEG; LIFT_DROP] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [SIMP_TAC [LIFT_DROP] THEN REPEAT STRIP_TAC THEN
        ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
        ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        PURE_ONCE_REWRITE_TAC [COMPLEX_MUL_AC] THEN
        MATCH_MP_TAC VECTOR_COMPLEX_DIFF_CHAIN_AT THEN CONJ_TAC THENL
         [ALL_TAC;
          SIMP_TAC [] THEN
          SUBGOAL_THEN `(Cx (drop t) * --s)=(--s * Cx (drop t) )` ASSUME_TAC THENL
           [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
          ONCE_ASM_SIMP_TAC [] THEN SIMP_TAC [HAS_COMPLEX_DERIVATIVE_CEXP]] THEN
        PURE_ONCE_REWRITE_TAC [COMPLEX_MUL_AC] THEN
        SUBGOAL_THEN
          `((\t. --s * Cx (drop t)) has_vector_derivative --s) (at t) = ((\t. (\x y. x * y) ((\x:real^1. --s:complex) t)
   ((\x. Cx (drop x))  t)) has_vector_derivative (\x y. x * y) ((\x:real^1. --s:complex) t) (Cx (&1)) +
    (\x y. x * y) (Cx (&0)) ((\x. Cx (drop x))  t)) (at t)`
          ASSUME_TAC THENL
         [SIMP_TAC [] THEN
          SIMP_TAC [COMPLEX_MUL_RID; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID];
          ALL_TAC] THEN
        ONCE_ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_BILINEAR_AT THEN
        SIMP_TAC [GSYM COMPLEX_VEC_0] THEN
        SIMP_TAC [HAS_VECTOR_DERIVATIVE_CONST] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `(\x. Cx (drop x)) = Cx o (\x . x) o drop` ASSUME_TAC THENL
           [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
          ONCE_ASM_SIMP_TAC [] THEN REWRITE_TAC [INTERVAL_REAL_INTERVAL] THEN
          ONCE_REWRITE_TAC [LIFT_DROP] THEN ONCE_REWRITE_TAC [GSYM LIFT_DROP] THEN
          ONCE_REWRITE_TAC [GSYM HAS_CX_VECTOR_DERIVATIVE_AT] THEN
          ONCE_REWRITE_TAC [LIFT_DROP] THEN
          REWRITE_TAC [HAS_REAL_DERIVATIVE_ID];
          REWRITE_TAC [bilinear] THEN CONJ_TAC THEN GEN_TAC THEN
          REWRITE_TAC [linear] THEN CONJ_TAC THENL
           [ALL_TAC;
            REWRITE_TAC [COMPLEX_CMUL];
            ALL_TAC;
            REWRITE_TAC [COMPLEX_CMUL]] THEN
          SIMPLE_COMPLEX_ARITH_TAC];
        CONJ_TAC THENL
         [SIMP_TAC [LIFT_DROP] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [];
          ALL_TAC] THEN
        SIMP_TAC [] THEN CONJ_TAC THENL
         [SIMP_TAC [SIMPLE_COMPLEX_ARITH `(x * y) * z = y:complex * (x * z)`] THEN
          MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
          SIMP_TAC [CONTINUOUS_ON_CONST] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
          SIMP_TAC [CEXP_S_T_CONTINUOUS_GEN] THEN
          MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
          UNDISCH_TAC `fourier_exists f` THEN 
          REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN
          REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM LIFT_NEG] THEN
          ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_SUBSET_REFLECT_UNIV];
          MP_TAC FOURIER_EXISTS_INTEGRABLE_1 THEN 
          DISCH_THEN (MP_TAC o SPEC `f':real^1->complex`) THEN
          DISCH_THEN (MP_TAC o SPEC `s:real^2`) THEN
          DISCH_THEN (MP_TAC o SPEC `--lift (abs b)`) THEN ASM_SIMP_TAC []]];
      SUBGOAL_THEN
        `!b s. integral (interval [--lift (abs b), lift (&0)])(\t. cexp (--(s * Cx (drop t))) * f' t)=
   integral (interval [--lift (abs b), lift (&0)]) (\t. (\t. cexp (--(s * Cx (drop t)))) t * f' t)`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      POP_ASSUM (K ALL_TAC) THEN
      SIMP_TAC
        [LIFT_DROP; COMPLEX_MUL_RZERO; COMPLEX_NEG_0; CEXP_0; COMPLEX_MUL_LID] THEN
      REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((a:complex) - b - c) = (a + (--b) - c)`] THEN
      SUBGOAL_THEN
        `!a s. f (lift (&0)) +
      --(cexp (--((ii * Cx w) * Cx (drop (--lift (abs a))))) *
         f (--lift (abs a))) -
      integral (interval [--lift (abs a),lift (&0)])
      (\t. (cexp (--((ii * Cx w) * Cx (drop t))) * --(ii * Cx w)) * f t) =
      (\a. f (lift (&0)) ) a +
     (\a. --(cexp (--((ii * Cx w) * Cx (drop (--lift (abs a))))) *
         f (--lift (abs a))) -
      integral (interval [--lift (abs a),lift (&0)])
      (\t. (cexp (--((ii * Cx w) * Cx (drop t))) * --(ii * Cx w)) * f t) ) a`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC TENDSTO_LIM THEN SIMP_TAC [TRIVIAL_LIMIT_AT_POSINFINITY] THEN
      MATCH_MP_TAC LIM_ADD THEN SIMP_TAC [LIM_CONST] THEN
      SUBGOAL_THEN
        `!s. s * lim at_posinfinity (\a. integral (interval [--lift (abs a),lift (&0)])
   (\t. cexp (--(s * Cx (drop t))) * f t)) = --Cx(&0) - ( --s * lim at_posinfinity
    (\a. integral (interval [--lift (abs a),lift (&0)])
     (\t. cexp (--(s * Cx (drop t))) * f t)) )`
        ASSUME_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN ASM_SIMP_TAC [] THEN
      POP_ASSUM (K ALL_TAC) THEN
      SUBGOAL_THEN
        `!a . (\a. --(cexp (--((ii * Cx w) * Cx (drop (--lift (abs a))))) *
          f (--lift (abs a))) -
       integral (interval [--lift (abs a),lift (&0)])
       (\t. (cexp (--((ii * Cx w) * Cx (drop t))) * --(ii * Cx w)) * f t)) = 
       (\a. (\a. --(cexp (--((ii * Cx w) * Cx (drop (--lift (abs a))))) *
          f (--lift (abs a))) ) a -
     (\a.  integral (interval [--lift (abs a),lift (&0)])
       (\t. (cexp (--((ii * Cx w) * Cx (drop t))) * --(ii * Cx w)) * f t)) a)`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC LIM_NEG THEN SIMP_TAC [GSYM COMPLEX_VEC_0] THEN
        UNDISCH_TAC `fourier_exists f` THEN UNDISCH_TAC `fourier_exists f'` THEN
        REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
        REPEAT STRIP_TAC THEN
        UNDISCH_TAC
          `(f:real^1->complex) absolutely_integrable_on IMAGE (--) {x | &0 <= drop x}` THEN
        UNDISCH_TAC
          `(f':real^1->complex) absolutely_integrable_on IMAGE (--) {x | &0 <= drop x}` THEN
        REWRITE_TAC [GSYM ABSOLUTELY_INTEGRABLE_REFLECT_GEN] THEN
        REWRITE_TAC [absolutely_integrable_on] THEN
        REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC LIM_TRANSFORM_BOUND_1 THEN
        EXISTS_TAC `(\x. (f:real^1->complex) (--lift (abs x)))` THEN CONJ_TAC THENL
         [ALL_TAC;
          SUBGOAL_THEN
            `((\x. (f:real^1->complex) (--lift x)) --> vec 0) at_posinfinity 
    ==> ((\x. f (--lift (abs x))) --> vec 0) at_posinfinity`
            ASSUME_TAC THENL
           [DISCH_TAC THEN MATCH_MP_TAC LIM_ABS_LIM_1 THEN ASM_SIMP_TAC [];
            POP_ASSUM MP_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
            ASM_SIMP_TAC [GSYM FUNLIM_POSINF_EQ_FUNLIM_NEGINF]]] THEN
        SIMP_TAC [] THEN REWRITE_TAC [DROP_NEG; LIFT_DROP] THEN
        SUBGOAL_THEN
          `!n. norm (cexp (--((ii * Cx w) * Cx (--abs n))) * f (--lift (abs n))) <= norm ((f:real^1->complex) (--lift (abs n)))`
          ASSUME_TAC THENL
         [ALL_TAC; ASM_SIMP_TAC [] THEN REWRITE_TAC [EVENTUALLY_TRUE]] THEN
        GEN_TAC THEN REWRITE_TAC [COMPLEX_NORM_MUL] THEN
        REWRITE_TAC [NORM_CEXP] THEN REWRITE_TAC [RE_NEG] THEN
        REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN
        REWRITE_TAC
          [SIMPLE_COMPLEX_ARITH
             `((ii * Cx w) * Cx (--abs n)) = (ii * Cx w * Cx (--abs n))`] THEN
        REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [RE_MUL_CX] THEN
        REWRITE_TAC [RE_II] THEN
        REWRITE_TAC [REAL_ARITH `(--(&0 * w * --abs n)) = &0`] THEN
        REWRITE_TAC [REAL_EXP_0] THEN REAL_ARITH_TAC;
        SUBGOAL_THEN
          `!a t. ((cexp (--((ii * Cx w) * Cx (drop t))) * --(ii * Cx w)) * f t) = (-- (ii * Cx w) * (cexp (--((ii * Cx w) * Cx (drop t)))) * f t)`
          ASSUME_TAC THENL
         [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
        SUBGOAL_THEN
          `!a s. integral (interval [--lift (abs a),lift (&0)]) (\t. --s * cexp (--(s * Cx (drop t))) * f t) =
    --s * integral (interval [--lift (abs a),lift (&0)]) (\t. cexp (--(s * Cx (drop t))) * (f:real^1->complex) t)`
          ASSUME_TAC THENL
         [REPEAT GEN_TAC THEN
          SUBGOAL_THEN
            `(\t. --s * cexp (--(s * Cx (drop t))) * (f:real^1->complex) t) =
   (\t.  --s  * (\t. cexp (--(s * Cx (drop t))) * f t) t)`
            ASSUME_TAC THENL
           [SIMP_TAC []; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
          MATCH_MP_TAC COMPLEX_INTEGRAL_CMUL THEN 
          MATCH_MP_TAC FOURIER_EXISTS_INTEGRABLE_1 THEN
          ASM_SIMP_TAC [];
          ALL_TAC] THEN
        ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
        MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
        SUBGOAL_THEN
          `!s. lim at_posinfinity (\a. integral (interval [--lift (abs a),lift (&0)]) (\t. cexp (--(s * Cx (drop t))) * (f:real^1->complex) t)) =
   lim at_posinfinity (\a. (\i. integral (interval [--lift i,lift (&0)]) (\t. cexp (--(s * Cx (drop t))) * f t)) (abs a))`
          ASSUME_TAC THENL
         [SIMP_TAC []; ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
        SUBGOAL_THEN
          `lim at_posinfinity
  (\a. (\i. integral (interval [--lift i,lift (&0)])
            (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t))
       (abs a)) = 
       lim at_posinfinity
  (\a. integral (interval [--lift a,lift (&0)])
            (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t))`
          ASSUME_TAC THENL
         [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC LIM_ABS_LIM_EQ THEN
          SUBGOAL_THEN
            `!a. (IMAGE (--) (interval [lift (&0),lift (a)])) = (interval [--lift (a),lift (&0)])`
            ASSUME_TAC THENL
           [REWRITE_TAC [EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTERVAL_1] THEN
            REWRITE_TAC [DROP_NEG; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
            EQ_TAC THEN REPEAT STRIP_TAC THENL
             [ALL_TAC;
              ALL_TAC;
              EXISTS_TAC `--(x:real^1)` THEN STRIP_TAC THENL
               [VECTOR_ARITH_TAC; ALL_TAC] THEN
              REWRITE_TAC [DROP_NEG] THEN ASM_REAL_ARITH_TAC] THEN
            ASM_SIMP_TAC [] THEN REWRITE_TAC [DROP_NEG] THEN
            ASM_REAL_ARITH_TAC;
            POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
            SIMP_TAC [] THEN DISCH_TAC THEN
            REWRITE_TAC [GSYM INTEGRAL_REFLECT_GEN] THEN
            MATCH_MP_TAC LIM_FOURIER_EXISTS_LEMMA_2 THEN ASM_SIMP_TAC []];
          ASM_SIMP_TAC [] THEN MATCH_MP_TAC LIM_ABS_LIM_1 THEN
          SIMP_TAC [GSYM FUN_LIM] THEN REWRITE_TAC [convergent_f] THEN
          SUBGOAL_THEN
            `!a. (IMAGE (--) (interval [lift (&0),lift (a)])) = (interval [--lift (a),lift (&0)])`
            ASSUME_TAC THENL
           [REWRITE_TAC [EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTERVAL_1] THEN
            REWRITE_TAC [DROP_NEG; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
            EQ_TAC THEN REPEAT STRIP_TAC THENL
             [ALL_TAC;
              ALL_TAC;
              EXISTS_TAC `--(x:real^1)` THEN STRIP_TAC THENL
               [VECTOR_ARITH_TAC; ALL_TAC] THEN
              REWRITE_TAC [DROP_NEG] THEN ASM_REAL_ARITH_TAC] THEN
            ASM_SIMP_TAC [] THEN REWRITE_TAC [DROP_NEG] THEN
            ASM_REAL_ARITH_TAC;
            POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
            SIMP_TAC [] THEN DISCH_TAC THEN
            REWRITE_TAC [GSYM INTEGRAL_REFLECT_GEN] THEN
            MATCH_MP_TAC LIM_FOURIER_EXISTS_LEMMA_2 THEN ASM_SIMP_TAC []]]]]]);;

(*==================================================================*)
(*                  FOURIER_DIFF_F_THEOREM_AT                       *)
(*==================================================================*)

let FOURIER_DIFF_F_THEOREM_AT = prove
 (`! (f:real^1->complex) (w:real).
     (((\x. f (lift x)) --> vec 0) at_posinfinity) /\
     (((\x. f (lift x)) --> vec 0) at_neginfinity) /\
     	fourier_exists f /\ 
            fourier_exists (\x. vector_derivative f ( at x )) /\ 
 	        (!x. f differentiable at x) 
         ==>
     (fourier_comp (\x. vector_derivative f (at x)) w 
                        = (ii * Cx w * (fourier_comp f w)) )`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FOURIER_DIFF_THEOREM_AT THEN 
  ASM_SIMP_TAC [] THEN GEN_TAC THEN
  REWRITE_TAC [GSYM VECTOR_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC []);;

(*==================================================================*)
(*                        FOURIER_F_EQ_EQ                           *)
(*==================================================================*)

let FOURIER_F_EQ_EQ = prove
 (`! f:real^1->complex g w.  (!x . f x = g x) /\  
      fourier_exists f /\  fourier_exists g   ==>
     fourier_comp f w = fourier_comp g w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [fourier_comp] THEN
  REWRITE_TAC [UNIV_SET_BREAK] THEN
  SUBGOAL_THEN
    `integral ({x | &0 <= drop x} UNION IMAGE (--) {x | &0 <= drop x}) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * (f:real^1->complex) t) = 
    integral {t | &0 <= drop t} (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t) + integral (IMAGE (--) {t | &0 <= drop t}) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * f t)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_1 THEN 
      ASM_SIMP_TAC []; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_2 THEN 
      ASM_SIMP_TAC []; ALL_TAC] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{(vec 0):real^1}` THEN
    REWRITE_TAC [NEGLIGIBLE_SING] THEN
    REWRITE_TAC
      [IN_ELIM_THM;
       SET_RULE
         `s INTER IMAGE f s SUBSET {a} <=> !x. x IN s /\ f x IN s ==> f x = a`] THEN
    REWRITE_TAC [GSYM LIFT_NUM] THEN REWRITE_TAC [DROP_NEG] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM DROP_EQ] THEN
    REWRITE_TAC [LIFT_DROP] THEN REWRITE_TAC [DROP_NEG] THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `integral ({x | &0 <= drop x} UNION IMAGE (--) {x | &0 <= drop x}) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * (g:real^1->complex) t) = 
    integral {t | &0 <= drop t} (\t. cexp (--((ii * Cx w) * Cx (drop t))) * g t) + integral (IMAGE (--) {t | &0 <= drop t}) (\t. cexp (--((ii * Cx w) * Cx (drop t))) * g t)`
      ASSUME_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC []] THEN
    MATCH_MP_TAC INTEGRAL_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_1 THEN 
      ASM_SIMP_TAC []; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FOURIER_INTEGRAND_INTEGRABLE_LEMMA_2 THEN 
      ASM_SIMP_TAC []; ALL_TAC] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{(vec 0):real^1}` THEN
    REWRITE_TAC [NEGLIGIBLE_SING] THEN
    REWRITE_TAC
      [IN_ELIM_THM;
       SET_RULE
         `s INTER IMAGE f s SUBSET {a} <=> !x. x IN s /\ f x IN s ==> f x = a`] THEN
    REWRITE_TAC [GSYM LIFT_NUM] THEN REWRITE_TAC [DROP_NEG] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM DROP_EQ] THEN
    REWRITE_TAC [LIFT_DROP] THEN REWRITE_TAC [DROP_NEG] THEN
    ASM_REAL_ARITH_TAC]);;

(*==================================================================*)
(*                        NUM_ZERO_TOTAL                            *)
(*==================================================================*)

let NUM_ZERO_TOTAL = prove
 (`!n:num. (n = 0) \/ (0 < n)`,
  ARITH_TAC);;

(*==================================================================*)
(*                         SUC_GT_ZERO                              *)
(*==================================================================*)

let SUC_GT_ZERO = prove
 (`!n:num. (0 < n) ==> SUC (n - 1)= n`,
  ARITH_TAC);;

(*==================================================================*)
(*                FOURIER_HIGHER_DIFF_F_THEOREM_AT                  *)
(*==================================================================*)

let higher_vector_derivative = new_recursive_definition num_RECURSION
   `(higher_vector_derivative 0 (f:real^1->complex) (x:real^1) = f x ) /\
     (!n. higher_vector_derivative (SUC n) (f:real^1->complex) (x:real^1) =
    (vector_derivative (\x. higher_vector_derivative n f x ) (at x)))`;;

let fourier_exists_higher_deriv = new_recursive_definition num_RECURSION
`(fourier_exists_higher_deriv 0 (f:real^1->complex) = (fourier_exists f)  )   /\
   (!n. fourier_exists_higher_deriv (SUC n) (f:real^1->complex) =
    ((fourier_exists (\x:real^1. higher_vector_derivative (SUC n) f x)) /\ 
     (fourier_exists_higher_deriv n f) ))`;;

let differentiable_higher_derivative = new_recursive_definition num_RECURSION
`(differentiable_higher_derivative 0 (f:real^1->complex) (x:real^1) = (f differentiable at x)  )  /\
   (!n. differentiable_higher_derivative  (SUC n) (f:real^1->complex) (x:real^1) =
     ((((\x:real^1. higher_vector_derivative (SUC n) f x)) differentiable at x) /\ (differentiable_higher_derivative  n f x) ))`;;

(*==================================================================*)
(*                     Proof of the theorem                         *)
(*==================================================================*)

let FOURIER_HIGHER_DIFF_F_THEOREM_AT = prove
 (`!(f:real^1->complex) (w:real) (n:num).
    ((fourier_exists_higher_deriv n f) /\
     (!x:real^1. differentiable_higher_derivative n f x)) /\
    (!p. p < n ==> ((\x. higher_vector_derivative p f (lift x)) --> vec 0) at_posinfinity) /\
    (!p. p < n ==> ((\x. higher_vector_derivative p f (lift x)) --> vec 0) at_neginfinity) 
        ==> 
      (fourier_comp (\x.  higher_vector_derivative n f x ) w =
       (((ii * Cx(w)) pow n) * (fourier_comp f w)) )`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC
      [higher_vector_derivative;
       complex_pow; COMPLEX_MUL_LID] THEN
    SIMP_TAC [ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC
    [higher_vector_derivative;
     fourier_exists_higher_deriv;
     differentiable_higher_derivative] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC
    `(fourier_exists_higher_deriv n f /\
      (!x. differentiable_higher_derivative n f x)) /\
      (!p. p < n
           ==> ((\x. higher_vector_derivative p f (lift x)) --> vec 0)
               at_posinfinity) /\
      (!p. p < n
           ==> ((\x. higher_vector_derivative p f (lift x)) --> vec 0)
               at_neginfinity) 
      ==> fourier_comp (\x. higher_vector_derivative n f x) w =
          (ii * Cx w) pow n * fourier_comp f w` THEN
  ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN
    `(!p. p < n
       ==> ((\x. higher_vector_derivative p (f:real^1->complex) (lift x)) --> vec 0)
           at_posinfinity)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC
      `!p. p < SUC n
          ==> ((\x. higher_vector_derivative p f (lift x)) --> vec 0)
              at_posinfinity` THEN
    DISCH_THEN (MP_TAC o SPEC `p:num`) THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `n:num` THEN ASM_SIMP_TAC [] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `(!p. p < n
       ==> ((\x. higher_vector_derivative p (f:real^1->complex) (lift x)) --> vec 0)
           at_neginfinity)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC
      `!p. p < SUC n
          ==> ((\x. higher_vector_derivative p f (lift x)) --> vec 0)
              at_neginfinity` THEN
    DISCH_THEN (MP_TAC o SPEC `p:num`) THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `n:num` THEN ASM_SIMP_TAC [] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `fourier_comp (\x. vector_derivative (\x. higher_vector_derivative n (f:real^1->complex) x) (at x)) w = 
     ii * Cx w * fourier_comp (\x. higher_vector_derivative n f x) w`
    ASSUME_TAC THENL
   [ALL_TAC;
    ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC [COMPLEX_SUB_LDISTRIB; complex_pow] THEN
    SUBGOAL_THEN
      `(ii * Cx w * fourier_comp (\x. higher_vector_derivative n (f:real^1->complex) x) w) = ((ii * Cx w) * fourier_comp (\x. higher_vector_derivative n f x) w)`
      ASSUME_TAC THENL
     [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `((ii * Cx w) * (ii * Cx w) pow n) * fourier_comp f w = (ii * Cx w) * ((ii * Cx w) pow n * fourier_comp f w)`
      ASSUME_TAC THENL
     [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN REWRITE_TAC []] THEN
  MATCH_MP_TAC FOURIER_DIFF_F_THEOREM_AT THEN ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN
    `((\x. higher_vector_derivative n (f:real^1->complex) (lift x)) --> vec 0) at_posinfinity`
    ASSUME_TAC THENL
   [UNDISCH_TAC
      `!p. p < SUC n
          ==> ((\x. higher_vector_derivative p f (lift x)) --> vec 0)
              at_posinfinity` THEN
    DISCH_THEN (MP_TAC o SPEC `n:num`) THEN DISCH_THEN MATCH_MP_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `((\x. higher_vector_derivative n (f:real^1->complex) (lift x)) --> vec 0) at_neginfinity`
    ASSUME_TAC THENL
   [UNDISCH_TAC
      `!p. p < SUC n
          ==> ((\x. higher_vector_derivative p f (lift x)) --> vec 0)
              at_neginfinity` THEN
    DISCH_THEN (MP_TAC o SPEC `n:num`) THEN DISCH_THEN MATCH_MP_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN CONJ_TAC THENL
   [MP_TAC NUM_ZERO_TOTAL THEN DISCH_THEN (MP_TAC o SPEC `n:num`) THEN
    REPEAT STRIP_TAC THENL
     [UNDISCH_TAC `fourier_exists_higher_deriv n f` THEN ASM_SIMP_TAC [] THEN
      REWRITE_TAC
        [higher_vector_derivative] THEN
      SIMP_TAC
        [fourier_exists_higher_deriv;
         ETA_AX];
      SUBGOAL_THEN `n = SUC (n - 1)` ASSUME_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUC_GT_ZERO;
        UNDISCH_TAC `fourier_exists_higher_deriv n f` THEN
        ONCE_ASM_REWRITE_TAC [] THEN
        REWRITE_TAC
          [fourier_exists_higher_deriv]] THEN
      ASM_SIMP_TAC []];
    GEN_TAC THEN
    UNDISCH_TAC
      `!x. (\x. vector_derivative (\x. higher_vector_derivative n f x) (at x)) differentiable
          at x /\
          differentiable_higher_derivative n f x` THEN
    DISCH_THEN (MP_TAC o SPEC `x:real^1`) THEN REPEAT STRIP_TAC THEN
    MP_TAC NUM_ZERO_TOTAL THEN DISCH_THEN (MP_TAC o SPEC `n:num`) THEN
    REPEAT STRIP_TAC THENL
     [UNDISCH_TAC `differentiable_higher_derivative n f x` THEN
      ASM_SIMP_TAC [] THEN
      REWRITE_TAC
        [higher_vector_derivative; differentiable_higher_derivative] THEN
      SIMP_TAC [ETA_AX];
      SUBGOAL_THEN `n = SUC (n - 1)` ASSUME_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUC_GT_ZERO;
        UNDISCH_TAC `differentiable_higher_derivative n f x` THEN
        ONCE_ASM_REWRITE_TAC [] THEN
        REWRITE_TAC
          [differentiable_higher_derivative]] THEN
      ASM_SIMP_TAC []]]);;

(*=======================================================*)
(*                  CEXP_S_T_CONTINUOUS1                 *)
(*=======================================================*)

let CEXP_S_T_CONTINUOUS1 = prove
 (`! (s:complex) (t:real^1) (b:real).
     (\t. cexp (--(s * Cx (drop t)))) continuous_on interval [lift (&0),lift(b)]`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `!t. ( cexp (--(s * Cx(drop(t))))) =
		(\t. cexp ((\t. (--(s * Cx(drop(t))))) t)) t`
    ASSUME_TAC THENL
   [GEN_TAC THEN SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC [CONTINUOUS_ON_CEXP] THEN REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
  REWRITE_TAC [CONTINUOUS_ON_CONST] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  REWRITE_TAC [CONTINUOUS_ON_CX_DROP]);;

(*=======================================================*)
(*                   REAL_LE_POS_ABS                     *)
(*=======================================================*)

let REAL_LE_POS_ABS = prove
 (`!x y . ((x  <= y ) /\ (&0 <= y) )==> x <= abs(y) `,
  REAL_ARITH_TAC);;

(*=======================================================*)
(*                   REALLIM_ABS_LIM                     *)
(*=======================================================*)

let REALLIM_ABS_LIM = prove
 (`!f:real->real l . ((\i. f(abs i)) ---> l) at_posinfinity ==> (f ---> l) at_posinfinity`,
  REWRITE_TAC [REALLIM_AT_POSINFINITY] THEN REWRITE_TAC [real_ge] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`&0`; `b:real`] REAL_LE_TOTAL) THEN STRIP_TAC THENL
   [EXISTS_TAC `b:real` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= x:real` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `b:real`;
      FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN `abs x = x:real` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_ABS_REFL]; ALL_TAC]];
    EXISTS_TAC `&0` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `b:real <= x:real` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0`;
      UNDISCH_TAC `b <= x ==> abs (f (abs x) - l) < e` THEN ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN `abs x = x:real` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_ABS_REFL]; ALL_TAC]]] THEN
  ASM_SIMP_TAC []);;

(*=======================================================*)
(*                  REALLIM_ABS_LIM_1                    *)
(*=======================================================*)

let REALLIM_ABS_LIM_1 = prove
 (`!f:real->real l . (f ---> l) at_posinfinity  ==>
     ((\i. f(abs i)) ---> l) at_posinfinity`,
  REWRITE_TAC [REALLIM_AT_POSINFINITY] THEN REWRITE_TAC [real_ge] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`&0`; `b:real`] REAL_LE_TOTAL) THEN STRIP_TAC THENL
   [EXISTS_TAC `b:real` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= x:real` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `b:real`;
      FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN `abs x = x:real` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_ABS_REFL]; ALL_TAC]];
    EXISTS_TAC `&0` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `b:real <= x:real` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0`;
      UNDISCH_TAC `b <= x ==> abs (f x - l) < e` THEN ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN `abs x = x:real` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_ABS_REFL]; ALL_TAC]]] THEN
  ASM_SIMP_TAC []);;

(*=======================================================*)
(*                     REAL_LE_11                        *)
(*=======================================================*)

let REAL_LE_11 = prove
 (`!x y z. (x < y) /\ (y = z) ==> (x < z) `,
  REAL_ARITH_TAC);;

(*=======================================================*)
(*             EXP_A_TENDSTO_0_INFINITY                  *)
(*=======================================================*)

let EXP_A_TENDSTO_0_INFINITY = prove
 (`!(a:real) . &0 < a ==>
    ( (\(x:real). exp (--(a * x))) ---> &0) (at_posinfinity)`,
  REWRITE_TAC [REALLIM_AT_POSINFINITY] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `(--inv (a) * log(e)) + &1` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(--inv (a) * log(e)) + &1 <= x` ASSUME_TAC THENL
   [REWRITE_TAC [GSYM real_ge] THEN ASM_SIMP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `x > --inv(a) * log(e)` ASSUME_TAC THENL
   [REWRITE_TAC [real_gt] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(--inv (a) * log(e)) + &1` THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC []];
    ALL_TAC] THEN
  REWRITE_TAC [REAL_SUB_RZERO] THEN REWRITE_TAC [REAL_ABS_EXP] THEN
  SUBGOAL_THEN `(--inv a *log(e) < x)` ASSUME_TAC THENL
   [REWRITE_TAC [GSYM real_gt] THEN ASM_SIMP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `(--inv a *log(e) < (inv(a) * a) *  x)` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(a) * (a:real) = &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN UNDISCH_TAC `&0 < a` THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC [] THEN REWRITE_TAC [REAL_MUL_LID] THEN ASM_SIMP_TAC []];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(a) * --log(e) < inv(a)* (a * x)` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(a) * --log(e) = --inv(a) * log(e)` ASSUME_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN ASM_REWRITE_TAC [REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--log e <  (a * x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `inv(a:real)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC []] THEN UNDISCH_TAC `&0 < a` THEN
    REWRITE_TAC [REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp (--(a * x)) < exp(--(--log(e)))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(log(inv e) = --(log e))` ASSUME_TAC THENL
       [MATCH_MP_TAC LOG_INV;
        SUBGOAL_THEN `( --(log e) = log(inv e))` ASSUME_TAC THENL
         [ALL_TAC;
          ONCE_ASM_SIMP_TAC [] THEN SUBGOAL_THEN `&0 < inv e` ASSUME_TAC THENL
           [MATCH_MP_TAC REAL_LT_INV;
            SUBGOAL_THEN `exp(log(inv e))= inv e` ASSUME_TAC THENL
             [MATCH_MP_TAC EXP_LOG; ALL_TAC]]]];
      REWRITE_TAC [REAL_EXP_MONO_LT]];
    SUBGOAL_THEN `exp (-- --log e) = e` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_NEG_NEG] THEN REWRITE_TAC [REAL_EXP_LOG];
      SUBGOAL_THEN `e=exp (-- --log e)` ASSUME_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC REAL_LE_11 THEN EXISTS_TAC `exp (-- --log e)` THEN
        CONJ_TAC]]] THEN
  ASM_SIMP_TAC []);;

(*========================================================*)
(*                   DIFFERENTIABLE_MUL                   *)
(*========================================================*)

let DIFFERENTIABLE_MUL = prove
 (`!(f:real^1->complex) g x:real^1.
        f differentiable at x /\ g differentiable at x
        ==> (\x. f x * g x) differentiable at x`,
  REWRITE_TAC [differentiable] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC
    `(\d. (f:real^1->complex) x * (f'':real^1->complex) d + f' d * g x)` THEN
  SUBGOAL_THEN
    `((\x. (\x y . x * y) ((f:real^1->complex) x) ((g:real^1->complex) x)) has_derivative
   (\d. ((\x y . x * y) (f x) ((f'':real^1->complex) d) + (\x y . x * y) ((f':real^1->complex) d) (g x)))) (at x)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_BILINEAR_AT THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [bilinear] THEN CONJ_TAC THEN GEN_TAC THEN
    REWRITE_TAC [linear] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC [COMPLEX_CMUL];
      ALL_TAC;
      REWRITE_TAC [COMPLEX_CMUL]] THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    SUBGOAL_THEN
      `!d. (\d. (f:real^1->complex) x * (f'':real^1->complex) d + f' d * g x)  = (\d. (\x y. x * y) (f x) (f'' d) + (\x y. x * y) (f' d) (g x))`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN
      `!x. (\x. (f:real^1->complex) x * (g:real^1->complex) x) = (\x. (\x y. x * y) (f x) (g x))`
      ASSUME_TAC THENL
     [SIMP_TAC []; PURE_ONCE_ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC []]]);;

(*========================================================*)
(*               PIECEWISE_DIFFERENTIABLE_MUL             *)
(*========================================================*)

let PIECEWISE_DIFFERENTIABLE_MUL = prove
 (`!f g:real^1->real^2 s:real^1->bool.
        f piecewise_differentiable_on s /\
        g piecewise_differentiable_on s
        ==> (\x. f x * g x) piecewise_differentiable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC [piecewise_differentiable_on] THEN
  DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC [CONTINUOUS_ON_COMPLEX_MUL] THEN
  FIRST_X_ASSUM (X_CHOOSE_THEN `t:real^1->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM (X_CHOOSE_THEN `u:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t UNION u :real^1->bool` THEN ASM_SIMP_TAC [FINITE_UNION] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  SIMP_TAC
    [SET_RULE
       `(s:real^1->bool) DIFF (t UNION u) = (s DIFF t) INTER (s DIFF u)`;
     IN_INTER] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `!x. x IN s DIFF t ==> (g:real^1->real^2) differentiable at x` THEN
  DISCH_THEN (MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC [] THEN
  UNDISCH_TAC `!x. x IN s DIFF u ==> (f:real^1->real^2) differentiable at x` THEN
  DISCH_THEN (MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC [] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [DIFFERENTIABLE_MUL]);;

(*==================================================================*)
(*                PIECEWISE_DIFFERENTIBLE_CONST                     *)
(*==================================================================*)

let PIECEWISE_DIFFERENTIABLE_CONST = prove
 (`!a:real^1 b c. (\x. c) piecewise_differentiable_on interval [a,b]`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE THEN
  REWRITE_TAC [DIFFERENTIABLE_ON_CONST]);;

(*==================================================================*)
(*                 FOURIER_EXISTS_MUL_LINEARITY                     *)
(*==================================================================*)

let FOURIER_EXISTS_MUL_LINEARITY = prove
 (`!(f:real^1->complex) g a b. 
  	     fourier_exists f
	     ==> fourier_exists (\t. a % f t)`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [COMPLEX_CMUL] THEN 
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_MUL THEN
    REWRITE_TAC [PIECEWISE_DIFFERENTIABLE_CONST] THEN ASM_MESON_TAC [];
    ALL_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN ASM_SIMP_TAC []);;

(*==================================================================*)
(*               FOURIER_EXISTS_MUL_ADD_LINEARITY                   *)
(*==================================================================*)

let FOURIER_EXISTS_MUL_ADD_LINEARITY = prove
 (`!(f:real^1->complex) g a b. 
  	     fourier_exists f /\  fourier_exists g
	     ==> fourier_exists (\t. a % f t + b % g t)`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ADD THEN CONJ_TAC THEN
    REWRITE_TAC [COMPLEX_CMUL] THEN 
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_MUL THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC []; ALL_TAC; ASM_MESON_TAC []] THEN
    REWRITE_TAC [PIECEWISE_DIFFERENTIABLE_CONST];
    ALL_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN ASM_SIMP_TAC []);;

(*=============================================================*)
(*               FOURIER_EXISTS_ADD_LINEARITY                  *)
(*=============================================================*)

let FOURIER_EXISTS_ADD_LINEARITY = prove
 (`!(f:real^1->complex) g. 
  	     fourier_exists f /\  fourier_exists g
	     ==> fourier_exists (\t. f t + g t)`,
  REWRITE_TAC [fourier_exists; NEG_REAL_INTERVAL_EQUIV] THEN 
   REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ADD]; ALL_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [ABSOLUTELY_INTEGRABLE_ADD]);;

(*=============================================================*)
(*                 FOURIER_SECOND_ORDER_DERIV                  *)
(*=============================================================*)

let FOURIER_SECOND_ORDER_DERIV = prove
 (`!(f:real^1->complex) (w:real) (n:num).
    ((fourier_exists_higher_deriv 2 f) /\
     (!x:real^1. differentiable_higher_derivative 2 f x)) /\
    (!p. p < 2 ==> ((\x. higher_vector_derivative p f (lift x)) --> vec 0) at_posinfinity) /\
    (!p. p < 2 ==> ((\x. higher_vector_derivative p f (lift x)) --> vec 0) at_neginfinity) 
        ==> 
      (fourier_comp (\t. vector_derivative (\x. vector_derivative f (at x)) (at t)) w =
       (((ii * Cx (w)) pow 2) * (fourier_comp f w)) )`,
  REPEAT STRIP_TAC THEN MP_TAC FOURIER_HIGHER_DIFF_F_THEOREM_AT THEN
  DISCH_THEN (MP_TAC o SPEC `f:real^1->complex`) THEN
  DISCH_THEN (MP_TAC o SPEC `w:real`) THEN DISCH_THEN (MP_TAC o SPEC `2`) THEN
  ASM_SIMP_TAC [] THEN SIMP_TAC [TWO] THEN
  REWRITE_TAC [higher_vector_derivative] THEN SIMP_TAC [ONE] THEN
  REWRITE_TAC [higher_vector_derivative] THEN
  REWRITE_TAC [ETA_AX; GSYM ONE; GSYM TWO]);;

(*=============================================================*)
(*                       Application                           *)
(*-------------------------------------------------------------*)
(*      Frequency response of Automobile Suspension System     *)
(*=============================================================*)
(*=============================================================*)

(*=============================================================*)
(*              nth order differential equation                *)
(*=============================================================*)

let diff_eq = new_definition
    `diff_eq (lst:(real^1->complex) list) (f:real^1->complex) (n:num)(x:real^1)=
    		( vsum (0..n) (\t. (EL t lst x) * (higher_vector_derivative t f x))) `;; 

(*=============================================================*)
(* Differential Equation modeling Automobile Suspension System *)
(*=============================================================*)

let diff_eq_ASS = new_definition
   `diff_eq_ASS (y:real^1->complex) (u:real^1->complex) M (b:real) k = 
   (!x:real^1. 
    (diff_eq [(\x. Cx (k)); (\x. Cx (b)); (\x. Cx (M))] y (2:num) x  = 
     diff_eq [(\x. Cx (k)); (\x. Cx (b))] u (1:num) x)) `;; 

(*=============================================================*)
(*      FREQUENCY_RESPONSE_AUTOMOBILE_SUSPENSION_SYSTEM        *)
(*=============================================================*)

let FREQUENCY_RESPONSE_AUTOMOBILE_SUSPENSION_SYSTEM = prove
 (`!y:real^1->complex u:real^1->complex  w:real M b k. 
    (&0 < M) /\ (&0 < b) /\ (&0 < k) /\
    (!x . differentiable_higher_derivative 2 y x ) /\ 
    (!x . differentiable_higher_derivative 1 u x) /\ 
    (fourier_exists_higher_deriv 2 y)  /\ 
    (fourier_exists_higher_deriv 1 u) /\
    (!p. p < 2 ==> ((\x. higher_vector_derivative p y (lift x)) --> vec 0) at_posinfinity) /\
    (!p. p < 2 ==> ((\x. higher_vector_derivative p y (lift x)) --> vec 0) at_neginfinity) /\
    (!p. p < 1 ==> ((\x. higher_vector_derivative p u (lift x)) --> vec 0) at_posinfinity) /\
    (!p. p < 1 ==> ((\x. higher_vector_derivative p u (lift x)) --> vec 0) at_neginfinity) /\
       diff_eq_ASS y u M b k
         ==> 
          (((ii * Cx w) pow 2 + Cx (b / M) * ii * Cx w + Cx (k / M)) * fourier_comp y w = (Cx (b / M) * ii * Cx w + Cx (k / M)) * fourier_comp u w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(Cx (b / M) * ii * Cx w + Cx (k / M)) = ((ii * Cx (b / M) * Cx (w)) + Cx (k / M))`
    ASSUME_TAC THENL
   [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `((ii * Cx w) pow 2 + ii * Cx (b / M) * Cx w + Cx (k / M)) = ((--((Cx (w)) pow 2)) + (ii * Cx (b / M) * Cx (w)) + Cx (k / M))`
    ASSUME_TAC THENL
   [REWRITE_TAC [COMPLEX_POW_MUL] THEN CONV_TAC COMPLEX_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC [diff_eq_ASS; diff_eq] THEN REWRITE_TAC [TWO] THEN
  REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN SIMP_TAC [ARITH_RULE `0 <= SUC 1`] THEN
  REWRITE_TAC [ONE] THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  SIMP_TAC [ARITH_RULE `0 <= SUC 0`] THEN SIMP_TAC [EL; TL; HD] THEN
  REWRITE_TAC [higher_vector_derivative] THEN
  SIMP_TAC
    [GSYM ONE; ETA_AX; GSYM TWO; COMPLEX_MUL_LID; COMPLEX_MUL_LZERO;
     COMPLEX_ADD_RID] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `fourier_comp (\x. (Cx k * (y:real^1->complex) x + Cx b * vector_derivative y (at x)) + Cx M * vector_derivative (\x. vector_derivative y (at x)) (at x)) w = fourier_comp (\x. (Cx k * (u:real^1->complex) x + Cx b * vector_derivative u (at x) )) w`
    ASSUME_TAC THENL
   [MATCH_MP_TAC FOURIER_F_EQ_EQ THEN CONJ_TAC THENL
     [SIMP_TAC [] THEN ASM_SIMP_TAC []; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `!x. differentiable_higher_derivative 2 y x` THEN
      SIMP_TAC [TWO] THEN SIMP_TAC [differentiable_higher_derivative] THEN
      SIMP_TAC [ONE] THEN SIMP_TAC [differentiable_higher_derivative] THEN
      REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
      REPEAT STRIP_TAC THEN UNDISCH_TAC `fourier_exists_higher_deriv 2 y` THEN
      SIMP_TAC [TWO] THEN REWRITE_TAC [fourier_exists_higher_deriv] THEN
      SIMP_TAC [ONE] THEN REWRITE_TAC [fourier_exists_higher_deriv] THEN
      REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
        `!x.( (Cx k * (y:real^1->complex) x + Cx b * vector_derivative y (at x)) + Cx M * vector_derivative (\x. vector_derivative y (at x)) (at x)) = ( (\x. (Cx k * y x + Cx b * vector_derivative y (at x)) ) x + (\x. Cx M * vector_derivative (\x. vector_derivative y (at x)) (at x) ) x)`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      PURE_ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      SUBGOAL_THEN
        `!x. (Cx k * (u:real^1->complex) x + Cx b * vector_derivative u (at x))  = ((\x. (Cx k * u x) ) x + (\x.  Cx b * vector_derivative u (at x)) x)`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      PURE_ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC FOURIER_EXISTS_ADD_LINEARITY THEN CONJ_TAC THEN
      REWRITE_TAC [GSYM COMPLEX_CMUL] THEN
      UNDISCH_TAC `fourier_exists_higher_deriv 1 u` THEN SIMP_TAC [ONE] THEN
      REWRITE_TAC [fourier_exists_higher_deriv] THEN
      REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FOURIER_EXISTS_MUL_LINEARITY];
      SUBGOAL_THEN
        `!x. (Cx k * (u:real^1->complex) x + Cx b * vector_derivative u (at x))  = ((\x. (Cx k * u x) ) x + (\x.  Cx b * vector_derivative u (at x)) x)`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      PURE_ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC FOURIER_EXISTS_ADD_LINEARITY THEN CONJ_TAC THEN
      REWRITE_TAC [GSYM COMPLEX_CMUL] THEN
      UNDISCH_TAC `fourier_exists_higher_deriv 1 u` THEN SIMP_TAC [ONE] THEN
      REWRITE_TAC [fourier_exists_higher_deriv] THEN
      REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FOURIER_EXISTS_MUL_LINEARITY]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `fourier_comp (\x. Cx k * (u:real^1->complex) x + Cx b * vector_derivative u (at x)) w = (ii * Cx b * Cx w + Cx k) * fourier_comp u w`
    ASSUME_TAC THENL
   [SUBGOAL_THEN
      `!x. (Cx k * (u:real^1->complex) x + Cx b * vector_derivative u (at x))  = ((\x. (Cx k * u x) ) x + (\x.  Cx b * vector_derivative u (at x)) x)`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `fourier_comp
 (\x. (\x. Cx k * u x) x + (\x. Cx b * vector_derivative u (at x)) x) w = 
   fourier_comp (\x. Cx k * u x) w + fourier_comp (\x. Cx b * vector_derivative u (at x)) w`
      ASSUME_TAC THENL
     [MATCH_MP_TAC FOURIER_ADD_LINEARITY THEN CONJ_TAC THEN
      REWRITE_TAC [GSYM COMPLEX_CMUL] THEN
      UNDISCH_TAC `fourier_exists_higher_deriv 1 u` THEN SIMP_TAC [ONE] THEN
      REWRITE_TAC [fourier_exists_higher_deriv] THEN
      REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FOURIER_EXISTS_MUL_LINEARITY];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `fourier_comp (\x. Cx k * u x) w = Cx k * fourier_comp (u:real^1->complex) w`
      ASSUME_TAC THENL
     [REWRITE_TAC [GSYM COMPLEX_CMUL] THEN MATCH_MP_TAC FOURIER_MUL_LINEARITY THEN
      UNDISCH_TAC `fourier_exists_higher_deriv 1 u` THEN SIMP_TAC [ONE] THEN
      REWRITE_TAC [fourier_exists_higher_deriv] THEN
      REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
      REPEAT STRIP_TAC;
      ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `fourier_comp (\x. Cx b * vector_derivative u (at x)) w = Cx b * (ii * Cx (w)) * fourier_comp (u:real^1->complex) w`
      ASSUME_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      SIMPLE_COMPLEX_ARITH_TAC] THEN
    SUBGOAL_THEN
      `fourier_comp (\x. Cx b * vector_derivative u (at x)) w = Cx b * fourier_comp (\x. vector_derivative u (at x)) w`
      ASSUME_TAC THENL
     [REWRITE_TAC [GSYM COMPLEX_CMUL] THEN MATCH_MP_TAC FOURIER_MUL_LINEARITY THEN
      UNDISCH_TAC `fourier_exists_higher_deriv 1 u` THEN SIMP_TAC [ONE] THEN
      REWRITE_TAC [fourier_exists_higher_deriv] THEN
      REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
      REPEAT STRIP_TAC;
      ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `fourier_comp (\x. vector_derivative u (at x)) w = ii * Cx w * fourier_comp (u:real^1->complex) w`
      ASSUME_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      SIMPLE_COMPLEX_ARITH_TAC] THEN
    MATCH_MP_TAC FOURIER_DIFF_THEOREM_AT THEN CONJ_TAC THENL
     [UNDISCH_TAC
        `!p. p < 1
          ==> ((\x. higher_vector_derivative p u (lift x)) --> vec 0)
              at_posinfinity` THEN
      DISCH_THEN (MP_TAC o SPEC `0`) THEN SUBGOAL_THEN `0 < 1` ASSUME_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [higher_vector_derivative];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC
        `!p. p < 1
          ==> ((\x. higher_vector_derivative p u (lift x)) --> vec 0)
              at_neginfinity` THEN
      DISCH_THEN (MP_TAC o SPEC `0`) THEN SUBGOAL_THEN `0 < 1` ASSUME_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [higher_vector_derivative];
      UNDISCH_TAC `fourier_exists_higher_deriv 1 u` THEN SIMP_TAC [ONE] THEN
      REWRITE_TAC [fourier_exists_higher_deriv] THEN
      REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
      REPEAT STRIP_TAC THENL
       [ALL_TAC;
        ALL_TAC;
        REWRITE_TAC [GSYM VECTOR_DERIVATIVE_WORKS] THEN
        UNDISCH_TAC `!x. differentiable_higher_derivative 1 u x` THEN
        DISCH_THEN (MP_TAC o SPEC `x:real^1`) THEN SIMP_TAC [ONE] THEN
        REWRITE_TAC [differentiable_higher_derivative] THEN SIMP_TAC []] THEN
      ASM_SIMP_TAC []];
    SUBGOAL_THEN
      `((ii * Cx (b / M) * Cx w + Cx (k / M)) * fourier_comp u w) = Cx (&1 / M) * ((ii * Cx b * Cx w + Cx k) * fourier_comp u w)`
      ASSUME_TAC THENL
     [REWRITE_TAC [CX_DIV] THEN REWRITE_TAC [complex_div] THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN DISCH_TAC THEN ONCE_ASM_SIMP_TAC [] THEN
    POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN DISCH_TAC THEN ONCE_ASM_SIMP_TAC [] THEN
    POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    SUBGOAL_THEN
      `(--(Cx w pow 2) + ii * Cx (b / M) * Cx w + Cx (k / M)) * fourier_comp y w = Cx (&1 / M) * ((--(Cx w pow 2) * Cx M + ii * Cx b * Cx w + Cx k) * fourier_comp y w)`
      ASSUME_TAC THENL
     [REWRITE_TAC [CX_DIV] THEN REWRITE_TAC [complex_div] THEN
      ONCE_REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&1) * x) = x`] THEN
      REWRITE_TAC [COMPLEX_ADD_LDISTRIB] THEN
      SUBGOAL_THEN `inv (Cx M) * --(Cx w pow 2) * Cx M = --(Cx w pow 2)`
        ASSUME_TAC THENL
       [ALL_TAC; ASM_SIMP_TAC [] THEN SIMPLE_COMPLEX_ARITH_TAC] THEN
      REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `(inv x * (y:complex) * x) = ((x * inv x) * y)`] THEN
      REWRITE_TAC [GSYM CX_INV] THEN REWRITE_TAC [GSYM CX_MUL] THEN
      SUBGOAL_THEN `M * inv M = &1` ASSUME_TAC THENL
       [ALL_TAC; ASM_SIMP_TAC [] THEN SIMPLE_COMPLEX_ARITH_TAC] THEN
      ONCE_REWRITE_TAC [GSYM real_div] THEN MATCH_MP_TAC REAL_DIV_REFL THEN
      REWRITE_TAC [REAL_NOT_EQ] THEN DISJ2_TAC THEN ASM_SIMP_TAC [];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN AP_TERM_TAC THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ASM_SIMP_TAC [] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
      `!x.( (Cx k * (y:real^1->complex) x + Cx b * vector_derivative y (at x)) + Cx M * vector_derivative (\x. vector_derivative y (at x)) (at x)) = ( (\x. (Cx k * y x + Cx b * vector_derivative y (at x)) ) x + (\x. Cx M * vector_derivative (\x. vector_derivative y (at x)) (at x) ) x)`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `fourier_comp
 (\x. (\x. Cx k * y x + Cx b * vector_derivative (y:real^1->complex) (at x)) x + (\x. Cx M * vector_derivative (\x. vector_derivative y (at x)) (at x)) x) w = 
   fourier_comp (\x. Cx k * y x + Cx b * vector_derivative (y:real^1->complex) (at x)) w + fourier_comp (\x. Cx M * vector_derivative (\x. vector_derivative y (at x)) (at x)) w`
      ASSUME_TAC THENL
     [MATCH_MP_TAC FOURIER_ADD_LINEARITY THEN
      UNDISCH_TAC `fourier_exists_higher_deriv 2 y` THEN SIMP_TAC [TWO] THEN
      REWRITE_TAC [fourier_exists_higher_deriv] THEN SIMP_TAC [ONE] THEN
      REWRITE_TAC [fourier_exists_higher_deriv] THEN
      REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
      REPEAT STRIP_TAC THENL
       [ALL_TAC;
        REWRITE_TAC [GSYM COMPLEX_CMUL] THEN
        ASM_SIMP_TAC [FOURIER_EXISTS_MUL_LINEARITY]] THEN
      SUBGOAL_THEN
        `!x. ( Cx k * (y:real^1->complex) x + Cx b * vector_derivative y (at x)) = ( (\x. Cx k * y x) x + (\x. Cx b * vector_derivative y (at x)) x)`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      PURE_ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      REWRITE_TAC [GSYM COMPLEX_CMUL] THEN
      ASM_SIMP_TAC [FOURIER_EXISTS_MUL_ADD_LINEARITY];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN
    REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH `((a + b + c) = ((c + b) + a:complex))`] THEN
    SUBGOAL_THEN
      `fourier_comp (\x. Cx k * (y:real^1->complex) x + Cx b * vector_derivative y (at x)) w = fourier_comp (\x. (\x. Cx k * y x) x + (\x. Cx b * vector_derivative y (at x)) x) w`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `fourier_comp (\x. (\x. Cx k * y x) x + (\x. Cx b * vector_derivative (y:real^1->complex) (at x)) x) w = fourier_comp (\x. Cx k * y x) w + fourier_comp (\x. Cx b * vector_derivative y (at x)) w`
      ASSUME_TAC THENL
     [MATCH_MP_TAC FOURIER_ADD_LINEARITY THEN REWRITE_TAC [GSYM COMPLEX_CMUL] THEN
      CONJ_TAC THEN MATCH_MP_TAC FOURIER_EXISTS_MUL_LINEARITY THEN
      UNDISCH_TAC `fourier_exists_higher_deriv 2 y` THEN SIMP_TAC [TWO] THEN
      REWRITE_TAC [fourier_exists_higher_deriv] THEN SIMP_TAC [ONE] THEN
      REWRITE_TAC [fourier_exists_higher_deriv] THEN
      REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
      REPEAT STRIP_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `fourier_comp (\x. Cx k * (y:real^1->complex) x) w = Cx k * fourier_comp y w`
      ASSUME_TAC THENL
     [REWRITE_TAC [GSYM COMPLEX_CMUL] THEN MATCH_MP_TAC FOURIER_MUL_LINEARITY THEN
      UNDISCH_TAC `fourier_exists_higher_deriv 2 y` THEN SIMP_TAC [TWO] THEN
      REWRITE_TAC [fourier_exists_higher_deriv] THEN SIMP_TAC [ONE] THEN
      REWRITE_TAC [fourier_exists_higher_deriv] THEN
      REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
      REPEAT STRIP_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `fourier_comp (\x. Cx b * vector_derivative y (at x)) w = (ii * Cx b * Cx w) * fourier_comp (y:real^1->complex) w`
      ASSUME_TAC THENL
     [SUBGOAL_THEN
        `fourier_comp (\x. Cx b * vector_derivative y (at x)) w = Cx b * fourier_comp (\x. vector_derivative y (at x)) w`
        ASSUME_TAC THENL
       [REWRITE_TAC [GSYM COMPLEX_CMUL] THEN
        MATCH_MP_TAC FOURIER_MUL_LINEARITY THEN
        UNDISCH_TAC `fourier_exists_higher_deriv 2 y` THEN SIMP_TAC [TWO] THEN
        REWRITE_TAC [fourier_exists_higher_deriv] THEN SIMP_TAC [ONE] THEN
        REWRITE_TAC [fourier_exists_higher_deriv] THEN
        REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
        REPEAT STRIP_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `((a * b) = ((c * a * d) * e:real^2)) = ((a * b) = (a * (c * d * e)))`] THEN
      REWRITE_TAC [COMPLEX_EQ_MUL_LCANCEL] THEN DISJ2_TAC THEN
      MATCH_MP_TAC FOURIER_DIFF_THEOREM_AT THEN CONJ_TAC THENL
       [UNDISCH_TAC
          `!p. p < 2
          ==> ((\x. higher_vector_derivative p y (lift x)) --> vec 0)
              at_posinfinity` THEN
        DISCH_THEN (MP_TAC o SPEC `0`) THEN SUBGOAL_THEN `0 < 2` ASSUME_TAC THENL
         [ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC [] THEN REWRITE_TAC [higher_vector_derivative];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC
          `!p. p < 2
          ==> ((\x. higher_vector_derivative p y (lift x)) --> vec 0)
              at_neginfinity` THEN
        DISCH_THEN (MP_TAC o SPEC `0`) THEN SUBGOAL_THEN `0 < 2` ASSUME_TAC THENL
         [ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC [] THEN REWRITE_TAC [higher_vector_derivative];
        UNDISCH_TAC `fourier_exists_higher_deriv 2 y` THEN SIMP_TAC [TWO] THEN
        REWRITE_TAC [fourier_exists_higher_deriv] THEN SIMP_TAC [ONE] THEN
        REWRITE_TAC [fourier_exists_higher_deriv] THEN
        REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
        REPEAT STRIP_TAC THENL
         [ALL_TAC;
          ALL_TAC;
          REWRITE_TAC [GSYM VECTOR_DERIVATIVE_WORKS] THEN
          UNDISCH_TAC `!x. differentiable_higher_derivative 2 y x` THEN
          DISCH_THEN (MP_TAC o SPEC `x:real^1`) THEN SIMP_TAC [TWO] THEN
          REWRITE_TAC [differentiable_higher_derivative] THEN SIMP_TAC [ONE] THEN
          REWRITE_TAC [differentiable_higher_derivative] THEN SIMP_TAC []] THEN
        ASM_SIMP_TAC []];
      ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN AP_TERM_TAC THEN
      REWRITE_TAC [GSYM COMPLEX_CMUL] THEN
      SUBGOAL_THEN
        `fourier_comp
 (\x. M % vector_derivative (\x. vector_derivative y (at x)) (at x))
 w = M % fourier_comp
 (\x.vector_derivative (\x. vector_derivative y (at x)) (at x))
 w`
        ASSUME_TAC THENL
       [MATCH_MP_TAC FOURIER_MUL_LINEARITY THEN
        UNDISCH_TAC `fourier_exists_higher_deriv 2 y` THEN SIMP_TAC [TWO] THEN
        REWRITE_TAC [fourier_exists_higher_deriv] THEN SIMP_TAC [ONE] THEN
        REWRITE_TAC [fourier_exists_higher_deriv] THEN
        REWRITE_TAC [higher_vector_derivative] THEN REWRITE_TAC [ETA_AX] THEN
        REPEAT STRIP_TAC;
        ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
        REWRITE_TAC [COMPLEX_CMUL] THEN
        REWRITE_TAC
          [SIMPLE_COMPLEX_ARITH `((a * b:complex) * c) = (b * (a * c))`] THEN
        AP_TERM_TAC THEN
        SUBGOAL_THEN `--(Cx w pow 2) = (ii * Cx w) pow 2` ASSUME_TAC THENL
         [REWRITE_TAC [COMPLEX_POW_MUL] THEN REWRITE_TAC [COMPLEX_POW_II_2] THEN
          SIMPLE_COMPLEX_ARITH_TAC;
          ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
          ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
          MATCH_MP_TAC FOURIER_SECOND_ORDER_DERIV THEN ASM_SIMP_TAC []]]]]);;

(*-------------------------------------------------------------*)
(*    FREQUENCY_RESPONSE_AUTOMOBILE_SUSPENSION_SYSTEM_FINAL    *)
(*-------------------------------------------------------------*)

let FREQUENCY_RESPONSE_AUTOMOBILE_SUSPENSION_SYSTEM_FINAL = prove
 (`!y:real^1->complex u:real^1->complex  w:real M b k. 
    (&0 < M) /\ (&0 < b) /\ (&0 < k) /\
    (!x . differentiable_higher_derivative 2 y x ) /\ 
    (!x . differentiable_higher_derivative 1 u x) /\ 
    (fourier_exists_higher_deriv 2 y)  /\ 
    (fourier_exists_higher_deriv 1 u) /\
    (!p. p < 2 ==> ((\x. higher_vector_derivative p y (lift x)) --> vec 0) at_posinfinity) /\
    (!p. p < 2 ==> ((\x. higher_vector_derivative p y (lift x)) --> vec 0) at_neginfinity) /\
    (!p. p < 1 ==> ((\x. higher_vector_derivative p u (lift x)) --> vec 0) at_posinfinity) /\
    (!p. p < 1 ==> ((\x. higher_vector_derivative p u (lift x)) --> vec 0) at_neginfinity) /\
       diff_eq_ASS y u M b k /\
 ~(fourier_comp u w = Cx (&0)) /\
 ~((((ii * Cx (w)) pow 2) + (Cx (b / M) * (ii * Cx (w))) + Cx (k / M)) = Cx (&0))
         ==> 
          (fourier_comp y w / fourier_comp u w = ((Cx (b / M) * (ii * Cx (w))) + Cx (k / M)) / (((ii * Cx (w)) pow 2) + (Cx (b / M) * (ii * Cx (w))) + Cx (k / M)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [complex_div] THEN
  SUBGOAL_THEN
    `(fourier_comp y w * inv (fourier_comp (u:real^1->complex) w)) = ((fourier_comp y w * inv (fourier_comp u w)) * (((ii * Cx w) pow 2 + Cx (b / M) * ii * Cx w + Cx (k / M)) / ((ii * Cx w) pow 2 + Cx (b / M) * ii * Cx w + Cx (k / M))))`
    ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [complex_div] THEN REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC [COMPLEX_EQ_MUL_RCANCEL] THEN DISJ1_TAC THEN
  SUBGOAL_THEN
    `((Cx (b / M) * ii) * Cx w + Cx (k / M)) = (((Cx (b / M) * ii) * Cx w + Cx (k / M)) * ((fourier_comp (u:real^1->complex) w) / (fourier_comp u w)))`
    ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [complex_div] THEN REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH `! a b d. ((a * b) * (d:complex)) = ((d * a) * b)`] THEN
  ONCE_REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH
       `! a b . ((inv b * a) * (b:complex)) = ((a * b) * inv b)`] THEN
  REWRITE_TAC [COMPLEX_EQ_MUL_RCANCEL] THEN DISJ1_TAC THEN
  ONCE_REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH
       `(((a:complex) + (b * c) * inv c) * d) = ((a + (b * (c * inv c))) * d)`] THEN
  SUBGOAL_THEN `fourier_comp u w * inv (fourier_comp u w) = Cx (&1)`
    ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD;
    ONCE_ASM_REWRITE_TAC [] THEN
    REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH
         `((ii * Cx w) pow 2 + ((Cx (b / M) * ii) * Cx w + Cx (k / M)) * Cx (&1)) = ((ii * Cx w) pow 2 + ((Cx (b / M) * ii) * Cx w + Cx (k / M)))`] THEN
    REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH
         `((ii * Cx (b / M)) * Cx w + Cx (k / M)) = (ii * Cx (b / M) * Cx w + Cx (k / M))`] THEN
    REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
    MATCH_MP_TAC FREQUENCY_RESPONSE_AUTOMOBILE_SUSPENSION_SYSTEM THEN
    ASM_SIMP_TAC []]);;

(*==================================================================*)
(*------------------------------------------------------------------*)
(*                      End of the Verification                     *)
(*------------------------------------------------------------------*)
(*==================================================================*)
