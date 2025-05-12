#[test]
fn ult() {
    test_cases! {
        definitions = "
            (declare-fun x4 () (_ BitVec 4))
            (declare-fun y4 () (_ BitVec 4))
        ",
        "Using bvult with x and y as bitvectors" {
          "(step t3 (cl (= (bvult x4 y4) (or (= ((_ @bit_of 3) x4) ((_ @bit_of 2) y4)) ((_ @bit_of 3) x4) ((_ @bit_of 2) y4)))) :rule bitblast_ult)": false,
          "(step t3 (cl (= (bvult x4 y4) (or (and (= ((_ @bit_of 3) x4) ((_ @bit_of 3) y4)) (or (and (= ((_ @bit_of 2) x4) ((_ @bit_of 2) y4)) (or (and (= ((_ @bit_of 1) x4) ((_ @bit_of 1) y4)) (and (not ((_ @bit_of 0) x4)) ((_ @bit_of 0) y4))) (and (not ((_ @bit_of 1) x4)) ((_ @bit_of 1) y4)))) (and (not ((_ @bit_of 2) x4)) ((_ @bit_of 2) y4)))) (and (not ((_ @bit_of 3) x4)) ((_ @bit_of 3) y4))))) :rule bitblast_ult)": true,
        }
        "Using bvult with x and y as bbterms" {
          "(step t1 (cl (= (bvult (@bbterm ((_ @bit_of 0) x4) ((_ @bit_of 1) x4) ((_ @bit_of 2) x4) ((_ @bit_of 3) x4)) (@bbterm ((_ @bit_of 0) y4) ((_ @bit_of 1) y4) ((_ @bit_of 2) y4) ((_ @bit_of 3) y4))) (or (and (= ((_ @bit_of 3) x4) ((_ @bit_of 3) y4)) (or (and (= ((_ @bit_of 2) x4) ((_ @bit_of 2) y4)) (or (and (= ((_ @bit_of 1) x4) ((_ @bit_of 1) y4)) (and (not ((_ @bit_of 0) x4)) ((_ @bit_of 0) y4))) (and (not ((_ @bit_of 1) x4)) ((_ @bit_of 1) y4)))) (and (not ((_ @bit_of 2) x4)) ((_ @bit_of 2) y4)))) (and (not ((_ @bit_of 3) x4)) ((_ @bit_of 3) y4))))) :rule bitblast_ult)": true,
          "(step t2 (cl (= (bvult (@bbterm ((_ @bit_of 0) x4) ((_ @bit_of 1) x4) ((_ @bit_of 2) x4) ((_ @bit_of 3) x4)) (@bbterm ((_ @bit_of 4) y4) ((_ @bit_of 1) y4) ((_ @bit_of 2) y4) ((_ @bit_of 3) y4))) (or (and (= ((_ @bit_of 3) x4) ((_ @bit_of 3) y4)) (or (and (= ((_ @bit_of 2) x4) ((_ @bit_of 2) y4)) (or (and (= ((_ @bit_of 1) x4) ((_ @bit_of 1) y4)) (and (not ((_ @bit_of 0) x4)) ((_ @bit_of 0) y4))) (and (not ((_ @bit_of 1) x4)) ((_ @bit_of 1) y4)))) (and (not ((_ @bit_of 2) x4)) ((_ @bit_of 2) y4)))) (and (not ((_ @bit_of 3) x4)) ((_ @bit_of 3) y4))))) :rule bitblast_ult)": false,
        }
    }
}

#[test]
fn add() {
    test_cases! {
        definitions = "
            (declare-fun x4 () (_ BitVec 4))
            (declare-fun y4 () (_ BitVec 4))
        ",
        "Using bvadd with x and y as bitvectors" {
          "(step t3 (cl (= (bvadd x4 y4) (@bbterm ((_ @bit_of 0) x4) ((_ @bit_of 1) y4) ((_ @bit_of 2) x4) ((_ @bit_of 3) y4)))) :rule bitblast_bvadd)": false,
          "(step t4 (cl (= (bvadd x4 y4) (@bbterm (xor (xor ((_ @bit_of 0) x4) ((_ @bit_of 0) y4)) false) (xor (xor ((_ @bit_of 1) x4) ((_ @bit_of 1) y4)) (or (and ((_ @bit_of 0) x4) ((_ @bit_of 0) y4)) (and (xor ((_ @bit_of 0) x4) ((_ @bit_of 0) y4)) false))) (xor (xor ((_ @bit_of 2) x4) ((_ @bit_of 2) y4)) (or (and ((_ @bit_of 1) x4) ((_ @bit_of 1) y4)) (and (xor ((_ @bit_of 1) x4) ((_ @bit_of 1) y4)) (or (and ((_ @bit_of 0) x4) ((_ @bit_of 0) y4)) (and (xor ((_ @bit_of 0) x4) ((_ @bit_of 0) y4)) false))))) (xor (xor ((_ @bit_of 3) x4) ((_ @bit_of 3) y4)) (or (and ((_ @bit_of 2) x4) ((_ @bit_of 2) y4)) (and (xor ((_ @bit_of 2) x4) ((_ @bit_of 2) y4)) (or (and ((_ @bit_of 1) x4) ((_ @bit_of 1) y4)) (and (xor ((_ @bit_of 1) x4) ((_ @bit_of 1) y4)) (or (and ((_ @bit_of 0) x4) ((_ @bit_of 0) y4)) (and (xor ((_ @bit_of 0) x4) ((_ @bit_of 0) y4)) false)))))))))) :rule bitblast_bvadd)": true,
        }
        "Using bvadd with x and y as @bbterms" {
          "(step t1 (cl (= (bvadd (@bbterm false (xor (xor (not ((_ @bit_of 0) x4)) false) true) (xor (xor (not ((_ @bit_of 1) x4)) false) (or (and (not ((_ @bit_of 0) x4)) false) (and (xor (not ((_ @bit_of 0) x4)) false) true))) (xor (xor (not ((_ @bit_of 2) x4)) false) (or (and (not ((_ @bit_of 1) x4)) false) (and (xor (not ((_ @bit_of 1) x4)) false) (or (and (not ((_ @bit_of 0) x4)) false) (and (xor (not ((_ @bit_of 0) x4)) false) true)))))) (@bbterm true true true true)) (@bbterm (xor (xor false true) false) (xor (xor (xor (xor (not ((_ @bit_of 0) x4)) false) true) true) (or (and false true) (and (xor false true) false))) (xor (xor (xor (xor (not ((_ @bit_of 1) x4)) false) (or (and (not ((_ @bit_of 0) x4)) false) (and (xor (not ((_ @bit_of 0) x4)) false) true))) true) (or (and (xor (xor (not ((_ @bit_of 0) x4)) false) true) true) (and (xor (xor (xor (not ((_ @bit_of 0) x4)) false) true) true) (or (and false true) (and (xor false true) false))))) (xor (xor (xor (xor (not ((_ @bit_of 2) x4)) false) (or (and (not ((_ @bit_of 1) x4)) false) (and (xor (not ((_ @bit_of 1) x4)) false) (or (and (not ((_ @bit_of 0) x4)) false) (and (xor (not ((_ @bit_of 0) x4)) false) true))))) true) (or (and (xor (xor (not ((_ @bit_of 1) x4)) false) (or (and (not ((_ @bit_of 0) x4)) false) (and (xor (not ((_ @bit_of 0) x4)) false) true))) true) (and (xor (xor (xor (not ((_ @bit_of 1) x4)) false) (or (and (not ((_ @bit_of 0) x4)) false) (and (xor (not ((_ @bit_of 0) x4)) false) true))) true) (or (and (xor (xor (not ((_ @bit_of 0) x4)) false) true) true) (and (xor (xor (xor (not ((_ @bit_of 0) x4)) false) true) true) (or (and false true) (and (xor false true) false)))))))))) :rule bitblast_bvadd)": true,
          "(step t2 (cl (= (bvadd (@bbterm false (xor (xor (not ((_ @bit_of 0) x4)) false) true) (xor (xor (not ((_ @bit_of 1) x4)) false) (or (and (not ((_ @bit_of 0) x4)) false) (and (xor (not ((_ @bit_of 0) x4)) false) true))) (xor (xor (not ((_ @bit_of 2) x4)) false) (or (and (not ((_ @bit_of 1) x4)) false) (and (xor (not ((_ @bit_of 1) x4)) false) (or (and (not ((_ @bit_of 0) x4)) false) (and (xor (not ((_ @bit_of 0) x4)) false) true)))))) (@bbterm true true true true)) (@bbterm (xor (xor false true) false) (xor (xor (xor (xor (not ((_ @bit_of 0) x4)) false) true) true) (or (and false true) (and (xor false true) false))) (xor (xor (xor (xor (not ((_ @bit_of 1) x4)) false) (or (and (not ((_ @bit_of 0) x4)) false) (and (xor (not ((_ @bit_of 0) x4)) false) true))) true) (or (and (xor (xor (not ((_ @bit_of 0) x4)) false) true) true) (and (xor (xor (xor (not ((_ @bit_of 0) x4)) false) true) true) (or (and false true) (and (xor false true) false))))) (xor (xor (xor (xor (not ((_ @bit_of 2) x4)) false) (or (and (not ((_ @bit_of 1) x4)) false) (and (xor (not ((_ @bit_of 1) x4)) false) (or (and (not ((_ @bit_of 0) x4)) false) (and (xor (not ((_ @bit_of 0) x4)) false) true))))) true) (or (and (xor (xor (not ((_ @bit_of 1) x4)) false) (or (and (not ((_ @bit_of 0) x4)) false) (and (xor (not ((_ @bit_of 0) x4)) false) true))) true) (and (xor (xor (xor (not ((_ @bit_of 1) x4)) false) (or (and (not ((_ @bit_of 0) x4)) false) (and (xor (not ((_ @bit_of 0) x4)) false) true))) true) (or (and (xor (xor (not ((_ @bit_of 0) x4)) false) true) true) (and (xor (xor (xor (not ((_ @bit_of 0) x4)) false) true) true) (or (and true true) (and (xor false true) false)))))))))) :rule bitblast_bvadd)": false,
        }
    }
}

#[test]
fn extract() {
    test_cases! {
        definitions = "
            (declare-fun a () Bool)
            (declare-fun zz () (_ BitVec 12))
            (declare-fun xx () (_ BitVec 12))
        ",
        "Using extract with x and y as @bbterms" {
          "(step t2 (cl (= ((_ extract 1 0) (@bbterm ((_ @bit_of 0) (ite a #b110 #b011)) ((_ @bit_of 1) (ite a #b110 #b011)) ((_ @bit_of 2) (ite a #b110 #b011)))) (@bbterm ((_ @bit_of 0) (ite a #b110 #b011)) ((_ @bit_of 1) (ite a #b110 #b011))))) :rule bitblast_extract)": true,
          "(step t3 (cl (= ((_ extract 1 0) (@bbterm ((_ @bit_of 0) (ite a #b110 #b011)) ((_ @bit_of 1) (ite a #b110 #b011)) ((_ @bit_of 2) (ite a #b110 #b011)))) (@bbterm ((_ @bit_of 0) (ite a #b111 #b011)) ((_ @bit_of 1) (ite a #b111 #b011))))) :rule bitblast_extract)": false,
          "(step t2 (cl (= ((_ extract 1 0) (@bbterm ((_ @bit_of 0) (ite a #b110 #b011)) ((_ @bit_of 1) (ite a #b110 #b011)) ((_ @bit_of 2) (ite a #b110 #b011)))) (@bbterm ((_ @bit_of 1) (ite a #b110 #b011)) ((_ @bit_of 1) (ite a #b110 #b011))))) :rule bitblast_extract)": false,
          "(step t4 (cl (= ((_ extract 11 4) (@bbterm ((_ @bit_of 0) zz) ((_ @bit_of 1) zz) ((_ @bit_of 2) zz) ((_ @bit_of 3) zz) ((_ @bit_of 4) zz) ((_ @bit_of 5) zz) ((_ @bit_of 6) zz) ((_ @bit_of 7) zz) ((_ @bit_of 8) zz) ((_ @bit_of 9) zz) ((_ @bit_of 10) zz) ((_ @bit_of 11) zz))) (@bbterm ((_ @bit_of 4) zz) ((_ @bit_of 5) zz) ((_ @bit_of 6) zz) ((_ @bit_of 7) zz) ((_ @bit_of 8) zz) ((_ @bit_of 9) zz) ((_ @bit_of 10) zz) ((_ @bit_of 11) zz)))) :rule bitblast_extract)": true,
          "(step t5 (cl (= ((_ extract 11 4) (@bbterm ((_ @bit_of 0) zz) ((_ @bit_of 1) zz) ((_ @bit_of 2) zz) ((_ @bit_of 3) zz) ((_ @bit_of 4) zz) ((_ @bit_of 5) zz) ((_ @bit_of 6) zz) ((_ @bit_of 7) zz) ((_ @bit_of 8) zz) ((_ @bit_of 9) zz) ((_ @bit_of 10) zz) ((_ @bit_of 11) zz))) (@bbterm ((_ @bit_of 3) zz) ((_ @bit_of 5) zz) ((_ @bit_of 6) zz) ((_ @bit_of 7) zz) ((_ @bit_of 8) zz) ((_ @bit_of 9) zz) ((_ @bit_of 10) zz) ((_ @bit_of 11) zz)))) :rule bitblast_extract)": false,
          "(step t5 (cl (= ((_ extract 11 4) (@bbterm ((_ @bit_of 0) zz) ((_ @bit_of 1) zz) ((_ @bit_of 2) zz) ((_ @bit_of 3) zz) ((_ @bit_of 4) zz) ((_ @bit_of 5) zz) ((_ @bit_of 6) zz) ((_ @bit_of 7) zz) ((_ @bit_of 8) zz) ((_ @bit_of 9) zz) ((_ @bit_of 10) zz) ((_ @bit_of 11) zz))) (@bbterm ((_ @bit_of 4) xx) ((_ @bit_of 5) zz) ((_ @bit_of 6) zz) ((_ @bit_of 7) zz) ((_ @bit_of 8) zz) ((_ @bit_of 9) zz) ((_ @bit_of 10) zz) ((_ @bit_of 11) zz)))) :rule bitblast_extract)": false,
        }
    }
}
