//! Small test suite for Tstp ASTs generation, from Alethe proof certificates.

#[cfg(test)]
use crate::translation::tstp::tests::*;

#[test]
fn test_simple_cong_example() {
    // Test from files simple-cong.*

    let alethe_problem = "(set-logic QF_UF)
(set-option :simplification none)

(declare-sort U 0)

(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)

(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-fun f (U U) U)

(assert (= a b))
(assert (= c d))
(assert (and p1 true))
(assert (or (not p1) (and p2 p3)))
(assert (or (not p3) (not (= (f a c) (f b d)))))

(check-sat)";

    let alethe_certificate = "
(assume a0 (= a b))
(assume a1 (= c d))
(assume a2 (and p1 true))
(assume a3 (or (not p1) (and p2 p3)))
(assume a4 (or (not p3) (not (= (f a c) (f b d)))))
(step t0 (cl (and (= a b) (= c d)) (not (= a b)) (not (= c d))) :rule and_neg)
(step t1 (cl (=> (and (= a b) (= c d)) (= (f a c) (f b d))) (and (= a b) (= c d))) :rule implies_neg1)
(anchor :step t2)
(assume t2.a0 (= a b))
(assume t2.a1 (= c d))
(step t2.t0 (cl (= (f a c) (f b d))) :rule cong :premises (t2.a0 t2.a1))
(step t2 (cl (not (= a b)) (not (= c d)) (= (f a c) (f b d))) :rule subproof :discharge (t2.a0 t2.a1))
(step t3 (cl (not (and (= a b) (= c d))) (= a b)) :rule and_pos :args (0))
(step t4 (cl (not (and (= a b) (= c d))) (= c d)) :rule and_pos :args (1))
(step t5 (cl (= (f a c) (f b d)) (not (and (= a b) (= c d))) (not (and (= a b) (= c d)))) :rule resolution :premises (t2 t3 t4))
(step t6 (cl (not (and (= a b) (= c d))) (not (and (= a b) (= c d))) (= (f a c) (f b d))) :rule reordering :premises (t5))
(step t7 (cl (not (and (= a b) (= c d))) (= (f a c) (f b d))) :rule contraction :premises (t6))
(step t8 (cl (=> (and (= a b) (= c d)) (= (f a c) (f b d))) (= (f a c) (f b d))) :rule resolution :premises (t1 t7))
(step t9 (cl (=> (and (= a b) (= c d)) (= (f a c) (f b d))) (not (= (f a c) (f b d)))) :rule implies_neg2)
(step t10 (cl (=> (and (= a b) (= c d)) (= (f a c) (f b d))) (=> (and (= a b) (= c d)) (= (f a c) (f b d)))) :rule resolution :premises (t8 t9))
(step t11 (cl (=> (and (= a b) (= c d)) (= (f a c) (f b d)))) :rule contraction :premises (t10))
(step t12 (cl (not (and (= a b) (= c d))) (= (f a c) (f b d))) :rule implies :premises (t11))
(step t13 (cl (not (= a b)) (not (= c d)) (= (f a c) (f b d))) :rule resolution :premises (t0 t12))
(step t14 (cl (= (f a c) (f b d)) (not (= a b)) (not (= c d))) :rule reordering :premises (t13))
(step t15 (cl (not p3) (not (= (f a c) (f b d)))) :rule or :premises (a4))
(step t16 (cl (not (and p2 p3)) p3) :rule and_pos :args (1))
(step t17 (cl p3 (not (and p2 p3))) :rule reordering :premises (t16))
(step t18 (cl (not p1) (and p2 p3)) :rule or :premises (a3))
(step t19 (cl p1) :rule and :premises (a2) :args (0))
(step t20 (cl (and p2 p3)) :rule resolution :premises (t18 t19))
(step t21 (cl p3) :rule resolution :premises (t17 t20))
(step t22 (cl (not (= (f a c) (f b d)))) :rule resolution :premises (t15 t21))
(step t23 (cl) :rule resolution :premises (t14 t22 a1 a0))";

    let tstp_problem = "tff(type_1, type, U: $tType).
tff(type_2, type, p1: $o).
tff(type_3, type, p2: $o).
tff(type_4, type, p3: $o).
tff(type_5, type, a: 'U').
tff(type_6, type, b: 'U').
tff(type_7, type, c: 'U').
tff(type_8, type, d: 'U').
tff(type_9, type, f: ( 'U' * 'U' ) > 'U').
tff(axiom_1, axiom, ( a = b )).
tff(axiom_2, axiom, ( c = d )).
tff(axiom_3, axiom, ( p1 & $true )).
tff(axiom_4, axiom, ( ~ p1 | ( p2 & p3 ) )).
tff(axiom_5, axiom, ( ~ p3 | ~ ( f(a, c) = f(b, d) ) )).
";

    let tstp_certificate = "tff(t0,plain,
    ( ( ( a = b )
      & ( c = d ) )
    | ( a != b )
    | ( c != d ) ),
    introduced(tautology,[and_neg],[]) ).
tff(t1,plain,
    ( ( ( ( a = b )
        & ( c = d ) )
     => ( f(a,c) = f(b,d) ) )
    | ( ( a = b )
      & ( c = d ) ) ),
    introduced(tautology,[implies_neg1],[]) ).
tff(t2.a0,assumption,
    a = b,
    introduced(assumption,[],[]) ).
tff(t2.a1,assumption,
    c = d,
    introduced(assumption,[],[]) ).
tff(t2.t0,plain,
    f(a,c) = f(b,d),
    inference(cong,[status(thm),assumptions(['t2.a0','t2.a1'])],['t2.a0','t2.a1']) ).
tff(t2,plain,
    ( ( a != b )
    | ( c != d )
    | ( f(a,c) = f(b,d) ) ),
    inference(subproof,[status(thm),discharge(subproof,['t2.a0','t2.a1'])],['t2.a0','t2.a1','t2.t0']) ).
tff(t3,plain,
    ( ~ ( ( a = b )
        & ( c = d ) )
    | ( a = b ) ),
    introduced(tautology,[and_pos(0)],[]) ).
tff(t4,plain,
    ( ~ ( ( a = b )
        & ( c = d ) )
    | ( c = d ) ),
    introduced(tautology,[and_pos(1)],[]) ).
tff(t5,plain,
    ( ( f(a,c) = f(b,d) )
    | ~ ( ( a = b )
        & ( c = d ) )
    | ~ ( ( a = b )
        & ( c = d ) ) ),
    inference(resolution,[status(thm)],[t2,t3,t4]) ).
tff(t6,plain,
    ( ~ ( ( a = b )
        & ( c = d ) )
    | ~ ( ( a = b )
        & ( c = d ) )
    | ( f(a,c) = f(b,d) ) ),
    inference(reordering,[status(thm)],[t5]) ).
tff(t7,plain,
    ( ~ ( ( a = b )
        & ( c = d ) )
    | ( f(a,c) = f(b,d) ) ),
    inference(contraction,[status(thm)],[t6]) ).
tff(t8,plain,
    ( ( ( ( a = b )
        & ( c = d ) )
     => ( f(a,c) = f(b,d) ) )
    | ( f(a,c) = f(b,d) ) ),
    inference(resolution,[status(thm)],[t1,t7]) ).
tff(t9,plain,
    ( ( ( ( a = b )
        & ( c = d ) )
     => ( f(a,c) = f(b,d) ) )
    | ( f(a,c) != f(b,d) ) ),
    introduced(tautology,[implies_neg2],[]) ).
tff(t10,plain,
    ( ( ( ( a = b )
        & ( c = d ) )
     => ( f(a,c) = f(b,d) ) )
    | ( ( ( a = b )
        & ( c = d ) )
     => ( f(a,c) = f(b,d) ) ) ),
    inference(resolution,[status(thm)],[t8,t9]) ).
tff(t11,plain,
    ( ( ( a = b )
      & ( c = d ) )
   => ( f(a,c) = f(b,d) ) ),
    inference(contraction,[status(thm)],[t10]) ).
tff(t12,plain,
    ( ~ ( ( a = b )
        & ( c = d ) )
    | ( f(a,c) = f(b,d) ) ),
    inference(implies,[status(thm)],[t11]) ).
tff(t13,plain,
    ( ( a != b )
    | ( c != d )
    | ( f(a,c) = f(b,d) ) ),
    inference(resolution,[status(thm)],[t0,t12]) ).
tff(t14,plain,
    ( ( f(a,c) = f(b,d) )
    | ( a != b )
    | ( c != d ) ),
    inference(reordering,[status(thm)],[t13]) ).
tff(axiom_6, axiom, ( ~ p3 | ~ ( f(a, c) = f(b, d) ) )).
tff(t15,plain,
    ( ~ p3
    | ( f(a,c) != f(b,d) ) ),
    inference(or,[status(thm)],[a4]) ).
tff(t16,plain,
    ( ~ ( p2
        & p3 )
    | p3 ),
    introduced(tautology,[and_pos(1)],[]) ).
tff(t17,plain,
    ( p3
    | ~ ( p2
        & p3 ) ),
    inference(reordering,[status(thm)],[t16]) ).
tff(axiom_7, axiom, ( ~ p1 | ( p2 & p3 ) )).
tff(t18,plain,
    ( ~ p1
    | ( p2
      & p3 ) ),
    inference(or,[status(thm)],[a3]) ).
tff(axiom_8, axiom, ( p1 & $true )).
tff(t19,plain,
    p1,
    inference(and(0),[status(thm)],[a2]) ).
tff(t20,plain,
    ( p2
    & p3 ),
    inference(resolution,[status(thm)],[t18,t19]) ).
tff(t21,plain,
    p3,
    inference(resolution,[status(thm)],[t17,t20]) ).
tff(t22,plain,
    f(a,c) != f(b,d),
    inference(resolution,[status(thm)],[t15,t21]) ).
tff(axiom_9, axiom, ( c = d )).
tff(axiom_10, axiom, ( a = b )).
tff(t23,plain,
    $false,
    inference(resolution,[status(thm)],[t14,t22,a1,a0]) ).";
    
    tstp_full_translation_test(alethe_problem, alethe_certificate, tstp_problem, tstp_certificate);
}

#[test]
fn test_onepoint_example() {
    // Test from files onepoint-example.*
      let alethe_problem = "(set-logic UFLIA)
(declare-const a Int)
(assert (not (= a 0)))
(assert (forall ((y Int) (z Int)) (=> (= z a) (= (+ a y) z))))
(check-sat)
";
        let alethe_certificate = "(assume h1 (not (= a 0)))
(assume h2 (forall ((y Int) (z Int)) (=> (= a z) (= z (+ a y)))))
(anchor :step t3 :args ((y Int) (:= (z Int) a)))
(step t3.t1 (cl (= a z)) :rule refl)
(step t3.t2 (cl (= (= a z) (= a a))) :rule cong :premises (t3.t1))
(step t3.t3 (cl (= a z)) :rule refl)
(step t3.t4 (cl (= (= z (+ a y)) (= a (+ a y)))) :rule cong :premises (t3.t3))
(step t3.t5 (cl (= (=> (= a z) (= z (+ a y))) (=> (= a a) (= a (+ a y))))) :rule cong :premises (t3.t2 t3.t4))
(step t3 (cl (= (forall ((y Int) (z Int)) (=> (= a z) (= z (+ a y)))) (forall ((y Int)) (=> (= a a) (= a (+ a y)))))) :rule onepoint)
(step t4 (cl (not (= (forall ((y Int) (z Int)) (=> (= a z) (= z (+ a y)))) (forall ((y Int)) (=> (= a a) (= a (+ a y)))))) (not (forall ((y Int) (z Int)) (=> (= a z) (= z (+ a y))))) (forall ((y Int)) (=> (= a a) (= a (+ a y))))) :rule equiv_pos2)
(step t5 (cl (forall ((y Int)) (=> (= a a) (= a (+ a y))))) :rule th_resolution :premises (h2 t3 t4))
(anchor :step t6 :args ((veriT_vr0 Int) (:= (y Int) veriT_vr0)))
(step t6.t1 (cl (= y veriT_vr0)) :rule refl)
(step t6.t2 (cl (= (+ a y) (+ a veriT_vr0))) :rule cong :premises (t6.t1))
(step t6.t3 (cl (= (= a (+ a y)) (= a (+ a veriT_vr0)))) :rule cong :premises (t6.t2))
(step t6.t4 (cl (= (=> (= a a) (= a (+ a y))) (=> (= a a) (= a (+ a veriT_vr0))))) :rule cong :premises (t6.t3))
(step t6 (cl (= (forall ((y Int)) (=> (= a a) (= a (+ a y)))) (forall ((veriT_vr0 Int)) (=> (= a a) (= a (+ a veriT_vr0)))))) :rule bind)
(step t7 (cl (not (= (forall ((y Int)) (=> (= a a) (= a (+ a y)))) (forall ((veriT_vr0 Int)) (=> (= a a) (= a (+ a veriT_vr0)))))) (not (forall ((y Int)) (=> (= a a) (= a (+ a y))))) (forall ((veriT_vr0 Int)) (=> (= a a) (= a (+ a veriT_vr0))))) :rule equiv_pos2)
(step t8 (cl (forall ((veriT_vr0 Int)) (=> (= a a) (= a (+ a veriT_vr0))))) :rule th_resolution :premises (t5 t6 t7))
(anchor :step t9 :args ((veriT_vr0 Int) (:= (veriT_vr0 Int) veriT_vr0)))
(step t9.t1 (cl (= (= a a) true)) :rule eq_simplify)
(step t9.t2 (cl (= (=> (= a a) (= a (+ a veriT_vr0))) (=> true (= a (+ a veriT_vr0))))) :rule cong :premises (t9.t1))
(step t9.t3 (cl (= (=> true (= a (+ a veriT_vr0))) (= a (+ a veriT_vr0)))) :rule implies_simplify)
(step t9.t4 (cl (= (=> (= a a) (= a (+ a veriT_vr0))) (= a (+ a veriT_vr0)))) :rule trans :premises (t9.t2 t9.t3))
(step t9 (cl (= (forall ((veriT_vr0 Int)) (=> (= a a) (= a (+ a veriT_vr0)))) (forall ((veriT_vr0 Int)) (= a (+ a veriT_vr0))))) :rule bind)
(step t10 (cl (not (= (forall ((veriT_vr0 Int)) (=> (= a a) (= a (+ a veriT_vr0)))) (forall ((veriT_vr0 Int)) (= a (+ a veriT_vr0))))) (not (forall ((veriT_vr0 Int)) (=> (= a a) (= a (+ a veriT_vr0))))) (forall ((veriT_vr0 Int)) (= a (+ a veriT_vr0)))) :rule equiv_pos2)
(step t11 (cl (forall ((veriT_vr0 Int)) (= a (+ a veriT_vr0)))) :rule th_resolution :premises (t8 t9 t10))
(anchor :step t12 :args ((veriT_vr1 Int) (:= (veriT_vr0 Int) veriT_vr1)))
(step t12.t1 (cl (= veriT_vr0 veriT_vr1)) :rule refl)
(step t12.t2 (cl (= (+ a veriT_vr0) (+ a veriT_vr1))) :rule cong :premises (t12.t1))
(step t12.t3 (cl (= (= a (+ a veriT_vr0)) (= a (+ a veriT_vr1)))) :rule cong :premises (t12.t2))
(step t12 (cl (= (forall ((veriT_vr0 Int)) (= a (+ a veriT_vr0))) (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1))))) :rule bind)
(step t13 (cl (not (= (forall ((veriT_vr0 Int)) (= a (+ a veriT_vr0))) (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1))))) (not (forall ((veriT_vr0 Int)) (= a (+ a veriT_vr0)))) (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) :rule equiv_pos2)
(step t14 (cl (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) :rule th_resolution :premises (t11 t12 t13))
(step t15 (cl (or (not (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1))))) :rule qnt_cnf)
(step t16 (cl (or (not (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) (= a (+ a 0)))) :rule forall_inst :args (0))
(anchor :step t17)
(assume t17.h1 (= a (+ a 0)))
(step t17.t2 (cl (= a (+ a 0))) :rule sum_simplify)
(step t17.t3 (cl (= (= a (+ a 0)) (= a a))) :rule cong :premises (t17.t2))
(step t17.t4 (cl (= (= a a) true)) :rule eq_simplify)
(step t17.t5 (cl (= (= a (+ a 0)) true)) :rule trans :premises (t17.t3 t17.t4))
(step t17.t6 (cl (not (= (= a (+ a 0)) true)) (not (= a (+ a 0))) true) :rule equiv_pos2)
(step t17.t7 (cl true) :rule th_resolution :premises (t17.h1 t17.t5 t17.t6))
(step t17 (cl (not (= a (+ a 0))) true) :rule subproof :discharge (h1))
(step t18 (cl (not (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) (= a (+ a 0))) :rule or :premises (t16))
(step t19 (cl (or (not (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) true) (not (not (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))))) :rule or_neg :args (0))
(step t20 (cl (not (not (not (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))))) (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) :rule not_not)
(step t21 (cl (or (not (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) true) (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) :rule th_resolution :premises (t20 t19))
(step t22 (cl (or (not (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) true) (not true)) :rule or_neg :args (1))
(step t23 (cl (or (not (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) true)) :rule th_resolution :premises (t18 t17 t21 t22))
(step t24 (cl (or (not (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) (= a (+ a a)))) :rule forall_inst :args (a))
(step t25 (cl true) :rule true)
(step t26 (cl (not (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) true) :rule or :premises (t23))
(step t27 (cl (not (forall ((veriT_vr1 Int)) (= a (+ a veriT_vr1)))) (= a (+ a a))) :rule or :premises (t24))
(step t28 (cl (= a (+ a a))) :rule resolution :premises (t27 t14))
(step t29 (cl (or (= a 0) (not (<= a 0)) (not (<= 0 a)))) :rule la_disequality)
(step t30 (cl (= a 0) (not (<= a 0)) (not (<= 0 a))) :rule or :premises (t29))
(step t31 (cl (not (<= a 0)) (not (<= 0 a))) :rule resolution :premises (t30 h1))
(step t32 (cl (<= 0 a) (not (= a (+ a a)))) :rule la_generic :args (1.0 (- 1.0)))
(step t33 (cl (<= 0 a)) :rule resolution :premises (t32 t28))
(step t34 (cl (not (<= a 0))) :rule resolution :premises (t31 t33))
(step t35 (cl (<= a 0) (not (= a (+ a a)))) :rule la_generic :args (1.0 1.0))
(step t36 (cl) :rule resolution :premises (t35 t28 t34))";

    let tstp_problem = "tff(type_1, type, a: $int).
tff(axiom_1, axiom, ~ ( a = 0 )).
tff(axiom_2, axiom, (! [Y:$int, Z:$int] : ( (Z = a) => ($sum(a, Y) = Z)))).";

    let tstp_certificate = "tff(a_decl,type,a: $int).

tff(h1,axiom,
    a != 0,
    file('onepoint-example.tptp',formula_1) ).

tff(h2,axiom,
    ! [Y:$int, Z:$int] :
      ( (Z = a)
     => ($sum(a, Y) = Z)),
    file('onepoint-example.tptp',formula_2) ).

tff(t3_rigid_y_decl,type,t3_rigid_y:$int).
tff(t3_rigid_z_decl,type,t3_rigid_z:$int).

tff(t3_rigid_z_assigned_a,assumption,
    t3_rigid_z = a,
    introduced(assumption,[anchor],[]) ).

tff(t3_rigid_z_generalize,axiom,
    ( t3_rigid_z = a
   => ! [Z:$int] : Z = a ) ).

tff('t3.t1',assumption,
    a = t3_rigid_z,
    introduced(assumption,[refl],[]) ).

tff('t3.t2',plain,
    ( a = t3_rigid_z <=> a = a ),
    inference(cong,[status(thm),assumptions(['t3.t1'])],['t3.t1']) ).

tff('t3.t3',assumption,
    a = t3_rigid_z,
    introduced(assumption,[refl],[]) ).

tff('t3.t4',plain,
    (t3_rigid_z = $sum(a,t3_rigid_y) <=> a = $sum(a,t3_rigid_y) ),
    inference(cong,[status(thm),assumptions(['t3.t3'])],['t3.t3']) ).

tff('t3.t5',plain,
    ( ( a = t3_rigid_z 
     => t3_rigid_z = $sum(a,t3_rigid_y) )
  <=> ( a = a
     => a = $sum(a,t3_rigid_y) ) ),
    inference(cong,[status(thm),assumptions(['t3.t1','t3.t3'])],['t3.t2','t3.t4']) ).

tff(t3,plain,
    ( ! [Y: $int,Z: $int] :
        ( a = Z
       => Z = $sum(a,Y) )
  <=> ! [Y: $int] :
        ( a = a
       => a = $sum(a,Y) ) ),
    inference(onepoint,[status(thm),discharge(onepoint,['t3.t1','t3.t3'])],[t3_rigid_z_generalize,'t3.t1','t3.t3','t3.t5']) ).

tff(t4,plain,
    ( ( ! [Y:$int,Z:$int] :
          ( a = Z
         => Z = $sum(a,Y) )
    <~> ! [Y:$int] :
          ( a = a
         => a = $sum(a,Y) ) )
    | ~ ! [Y:$int,Z:$int] :
          ( a = Z
         => Z = $sum(a,Y) )
    | ! [Y:$int] :
        ( a = a
       => a = $sum(a,Y) ) ),
    introduced(tautology,[equiv_pos2],[]) ).


tff(t5,plain,
    ! [Y:$int] :
      ( a = a
     => a = $sum(a,Y) ),
    inference(th_resolution,[status(thm)],[h2,t3,t4]) ).

tff(t6_rigid_veriT_vr0_decl,type,t6_rigid_veriT_vr0: $int).
tff(t6_rigid_y_decl,type,t6_rigid_y: $int).

tff(t6_rigid_y_assigned_veriT_vr0,assumption,
    t6_rigid_y = t6_rigid_veriT_vr0,
    introduced(assumption,[anchor],[]) ).

tff(t6_rigid_y_generalize,axiom,
    ( t6_rigid_y = t6_rigid_veriT_vr0
   => ! [Y:$int] : Y = t6_rigid_veriT_vr0 ) ).

tff('t6.t1',assumption,
    t6_rigid_y = t6_rigid_veriT_vr0,
    introduced(assumption,[refl],[]) ).

tff('t6.t2',plain,
    $sum(a,t6_rigid_y) = $sum(a,t6_rigid_veriT_vr0),
    inference(cong,[status(thm),assumptions(['t6.t1'])],['t6.t1']) ).

tff('t6.t3',plain,
    ( a = $sum(a,t6_rigid_y)
  <=> a = $sum(a,t6_rigid_veriT_vr0) ),
    inference(cong,[status(thm),assumptions(['t6.t1'])],['t6.t2']) ).

tff('t6.t4',plain,
    ( ( a = a
     => a = $sum(a,t6_rigid_y) )
  <=> ( a = a
     => a = $sum(a,t6_rigid_veriT_vr0) ) ),
   inference(cong,[status(thm),assumptions(['t6.t1'])],['t6.t3']) ).

tff(t6,plain,
    ( ! [Y:$int] : 
        ( a = a
       => a = $sum(a,Y) )
  <=> ! [VeriT_vr0:$int] :
        ( a = a
       => a = $sum(a,VeriT_vr0) ) ),
    inference(bind,[status(thm),discharge(bind,['t6.t1'])],[t6_rigid_y_generalize,'t6.t1','t6.t4']) ).


tff(t7,plain,
    ( ( ! [Y:$int] :
          ( a = a
         => a = $sum(a,Y) )
    <~> ! [VeriT_vr0:$int] :
          ( a = a
         => a = $sum(a,VeriT_vr0) ) )
    | ~ ! [Y:$int] :
          ( a = a
         => a = $sum(a,Y) )
    | ! [VeriT_vr0:$int] :
        ( a = a
       => a = $sum(a,VeriT_vr0) ) ),
    introduced(tautology,[equiv_pos2],[]) ).


tff(t8,plain,
    ! [VeriT_vr0:$int] :
      ( a = a
     => a = $sum(a,VeriT_vr0) ),
    inference(th_resolution,[status(thm)],[t5,t6,t7]) ).

tff(t9_rigid_veriT_vr0_decl,type,
    t9_rigid_veriT_vr0: $int).

tff(t9_rigid_veriT_vr0_assigned_t9_rigid_veriT_vr0,assumption,
    t9_rigid_veriT_vr0 = t9_rigid_veriT_vr0,
    introduced(assumption,[anchor],[]) ).

tff(t9_rigid_veriT_vr0_generalize,axiom,
    ( t9_rigid_veriT_vr0 = t9_rigid_veriT_vr0
   => ! [VeriT_vr0:$int] : VeriT_vr0 = t9_rigid_veriT_vr0 ) ).

tff('t9.t1',plain,
    a = a,
    introduced(tautology,[eq_simplify],[]) ).


tff('t9.t2',plain,
    ( ( a = a
     => a = $sum(a,t9_rigid_veriT_vr0) )
  <=> ( $true
     => a = $sum(a,t9_rigid_veriT_vr0) ) ),
    inference(cong,[status(thm)],['t9.t1']) ).


tff('t9.t3',plain,
    ( ( $true
     => a = $sum(a,t9_rigid_veriT_vr0) )
  <=> a = $sum(a,t9_rigid_veriT_vr0) ),
    introduced(tautology,[implies_simplify],[]) ).


tff('t9.t4',plain,
    ( ( a = a
     => a = $sum(a,t9_rigid_veriT_vr0) )
  <=> a = $sum(a,t9_rigid_veriT_vr0) ),
    inference(trans,[status(thm)],['t9.t2','t9.t3']) ).


tff(t9,plain,
    ( ! [VeriT_vr0:$int] :
        ( a = a
       => a = $sum(a,VeriT_vr0) )
  <=> ! [VeriT_vr0:$int] : a = $sum(a,VeriT_vr0) ),
    inference(bind,[status(thm)],['t9.t4']) ).


tff(t10,plain,
    ( ( ! [VeriT_vr0:$int] :
          ( a = a
         => a = $sum(a,VeriT_vr0) )
    <~> ! [VeriT_vr0:$int] : a = $sum(a,VeriT_vr0) )
    | ~ ! [VeriT_vr0:$int] :
          ( a = a
         => a = $sum(a,VeriT_vr0) )
    | ! [VeriT_vr0:$int] : a = $sum(a,VeriT_vr0) ),
    introduced(tautology,[equiv_pos2],[]) ).


tff(t11,plain,
    ! [VeriT_vr0:$int] : a = $sum(a,VeriT_vr0),
    inference(th_resolution,[status(thm)],[t8,t9,t10]) ).


tff(t12_rigid_veriT_vr1_decl,type,t12_rigid_veriT_vr1: $int).
tff(t12_rigid_veriT_vr0_decl,type,t12_rigid_veriT_vr0: $int).

tff(t12_y_generalize,axiom,
    ( t12_rigid_veriT_vr0 = t12_rigid_veriT_vr1
   => ! [VeriT_vr0:$int] : VeriT_vr0 = t12_rigid_veriT_vr1 ) ).


tff('t12.t1',plain,
    t12_rigid_veriT_vr0 = t12_rigid_veriT_vr1,
    introduced(assumption,[refl],[]) ).


tff('t12.t2',plain,
    $sum(a,t12_rigid_veriT_vr0) = $sum(a,t12_rigid_veriT_vr1),
    inference(cong,[status(thm),asumptions(['t12.t1'])],['t12.t1']) ).


tff('t12.t3',plain,
    ( a = $sum(a,t12_rigid_veriT_vr0)
  <=> a = $sum(a,t12_rigid_veriT_vr1) ),
    inference(cong,[status(thm),asumptions(['t12.t1'])],['t12.t2']) ).


tff(t12,plain,
    ( ! [VeriT_vr0:$int] : a = $sum(a,VeriT_vr0)
  <=> ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1) ),
    inference(bind,[status(thm),discharge(bind,['t12.t1'])],[t12_y_generalize,'t12.t1','t12.t3']) ).

tff(t13,plain,
    ( ( ! [VeriT_vr0:$int] : a = $sum(a,VeriT_vr0)
    <~> ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1) )
    | ~ ! [VeriT_vr0:$int] : a = $sum(a,VeriT_vr0)
    | ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1) ),
    introduced(tautology,[equiv_pos2],[]) ).

tff(t14,plain,
    ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1),
    inference(th_resolution,[status(thm)],[t11,t12,t13]) ).


tff(t15,plain,
    ( ~ ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1)
    | ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1) ),
    introduced(tautology,[qnt_cnf],[]) ).


tff(t16,plain,
    ( ~ ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1)
    | a = $sum(a,0) ),
    introduced(tautology,[forall_inst],[]) ).

tff('t17.h1',assumption,
    a = $sum(a,0),
    introduced(assumption,[],[]) ).


tff('t17.t2',plain,
    a = $sum(a,0),
    introduced(tautology,[sum_simplify],[]) ).


tff('t17.t3',plain,
    ( a = $sum(a,0)
  <=> a = a ),
    inference(cong,[status(thm)],['t17.t2']) ).


tff('t17.t4',plain,
    ( a = a
  <=> $true ),
    introduced(tautology,[eq_simplify],[]) ).


tff('t17.t5',plain,
    ( a = $sum(a,0)
  <=> $true ),
    inference(trans,[status(thm)],['t17.t3','t17.t4']) ).


tff('t17.t6',plain,
    ( ( a = $sum(a,0)
    <~> $true )
    | a != $sum(a,0)
    | $true ),
    introduced(tautology,[equiv_pos2],[]) ).


tff('t17.t7',plain,
    $true,
    inference(th_resolution,[status(thm),assumptions(['t17.h1'])],['t17.h1','t17.t5','t17.t6']) ).


tff(t17,plain,
    ( a = $sum(a,0)
    | $true ),
    inference(subproof,[status(thm),discharge(subproof,['t17.h1'])],['t17.h1','t17.t7']) ).


tff(t18,plain,
    ( ~ ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1)
    | a = $sum(a,0) ),
    inference(or,[status(thm)],[t16]) ).


tff(t19,plain,
    ( ( ~ ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1)
      | $true )
    | ~ ~ ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1) ),
    introduced(tautology,[or_neg],[]) ).


tff(t20,plain,
    ( ~ ~ ~ ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1)
    | ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1) ),
    introduced(tautology,[not_not],[]) ).
 

tff(t21,plain,
    ( ( ~ ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1)
      | $true )
    | ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1) ),
    inference(th_resolution,[status(thm)],[t20,t19]) ).


tff(t22,plain,
    ( ( ~ ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1)
      | $true )
    | ~ $true ),
    introduced(tautology,[or_neg],[]) ).


tff(t23,plain,
    ( ~ ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1)
    | $true ),
    inference(th_resolution,[status(thm)],[t18,t17,t21,t22]) ).


tff(t24,plain,
    ( ~ ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1)
    | a = $sum(a,a) ),
    introduced(tautology,[forall_inst],[]) ).


tff(t25,plain,
    $true,
    introduced(tautology,[true],[]) ).


tff(t26,plain,
    ( ~ ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1)
    | $true),
    introduced(tautology,[or],[]) ).


tff(t27,plain,
    ( ~ ! [VeriT_vr1:$int] : a = $sum(a,VeriT_vr1)
    | a = $sum(a,a) ),
    inference(or,[status(thm)],[t24]) ).


tff(t28,plain,
    a = $sum(a,a),
    inference(resolution,[status(thm)],[t27,t14]) ).


tff(t29,plain,
    ( ( a = 0
      | ~ $lesseq(a,0) )
    | ~ $lesseq(0,a) ),
    introduced(tautology,[la_disequality],[]) ).


tff(t30,plain,
    ( a = 0
    | ~ $lesseq(a,0)
    | ~ $lesseq(0,a) ),
    inference(or,[status(thm)],[t29]) ).


tff(t31,plain,
    ( ~ $lesseq(a,0)
    | ~ $lesseq(0,a) ),
    inference(resolution,[status(thm)],[t30,h1]) ).


tff(t32,plain,
    ( $lesseq(0,a)
    | a != $sum(a,a) ),
    introduced(tautology,[la_generic],[]) ).


tff(t33,plain,
    $lesseq(0,a),
    inference(resolution,[status(thm)],[t32,t28]) ).


tff(t34,plain,
    ~ $lesseq(a,0),
    inference(resolution,[status(thm)],[t31,t33]) ).


tff(t35,plain,
    ( $lesseq(a,0)
    | a != $sum(a,a) ),
    introduced(tautology,[la_generic],[]) ).


tff(t36,plain,
    $false,
    inference(resolution,[status(thm)],[t35,t28,t34]) ).
";

    tstp_full_translation_test(alethe_problem, alethe_certificate, tstp_problem, tstp_certificate);
}
