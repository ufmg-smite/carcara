//! Small test suite for Eunoia ASTs generation, from Alethe proof certificates.

#[cfg(test)]
use crate::translation::eunoia::tests::*;

#[test]
fn test_small_example() {
    let alethe_problem = "(declare-const a Real)
                   (declare-const b Real)
                   (assert (xor (not (> a 5.0)) (= b 10.0)))
                   (assert (not (= b 10.0)))
                   (assert (not (<= a 5.0)))";

    let alethe_certificate = "(assume h1 (xor (not (> a 5.0)) (! (= b 10.0) :named s1)))
                          (assume h2 (not (= b 10.0)))
                          (assume h3 (not (<= a 5.0)))

                          (step t1 (cl (not (> a 5.0)) s1) :rule xor1 :premises (h1))
                          (step t2 (cl (<= a 5.0) (> a 5.0)) :rule la_generic :args (1.0 1.0))
                          (step t3 (cl) :rule resolution :premises (t1 t2 h2 h3))";

    let eunoia_problem = "(declare-const a Real)\n\
                          (declare-const b Real)\n";
    
    let eunoia_certificate = "(define ctx1 ( ) true)\n\
         (assume context ctx1)\n\
         (assume h1 (@cl (xor (not (> a 5.0)) (= b 10.0))))\n\
         (step t1 (@cl (not (> a 5.0)) (= b 10.0)) :rule xor1 :premises ( h1 ))\n\
         (step t2 (@cl (<= a 5.0) (> a 5.0)) :rule la_generic :args ( (@varlist 1.0 1.0) ))\n\
         (assume h2 (@cl (not (= b 10.0))))\n\
         (assume h3 (@cl (not (<= a 5.0))))\n\
         (step t3 @empty_cl :rule resolution :premises ( t1 t2 h2 h3 ) :args ( (@varlist) ))\n";

    eunoia_full_translation_test(alethe_problem, alethe_certificate, eunoia_problem, eunoia_certificate);
}

#[test]
fn test_let_example() {
    let alethe_problem = "(set-logic UF)
                           (declare-sort S 0)
                           (declare-const a S)
                           (declare-const b S)
                           (assert (= a b))";

    let alethe_certificate = "(assume h1 (= a b))
                              (anchor :step t2 :args ((:= x b)))
                              (step t1 (cl (= x b)) :rule refl)
                              (step t2 (cl (= (let ((x a)) x) b)) :rule let :premises (h1))";

    let eunoia_problem = "(declare-const S Type)\n\
         (declare-const a S)\n\
         (declare-const b S)\n";

    let eunoia_certificate = "(define ctx1 ( ) true)\n\
         (assume context ctx1)\n\
         (assume h1 (@cl (= a b)))\n\
         (define ctx2 ( ) (@ctx ( ( x S ) ) (and (= (@var ( ( x S ) ) x) b) ctx1)))\n\
         (assume-push context ctx2)\n\
         (step t1 (@cl (= (@var ( ( x S ) ) x) b)) \
         :rule refl :premises ( context ))\n\
         (step-pop t2 (@cl (= ( _ (@let ( ( x S ) ) (@var ( ( x S ) ) x)) a) b)) \
         :rule let_elim :premises ( h1 t1 ))\n";

    eunoia_full_translation_test(alethe_problem, alethe_certificate, eunoia_problem, eunoia_certificate);
}
