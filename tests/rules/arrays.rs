#[test]
fn idx() {
    test_cases! {
        definitions = "
            (declare-fun A () (Array Int Int))
            (declare-const x Int)
            (declare-const y Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (select (store A 1 x) 1) x)) :rule arrays_idx)": true,
            "(step t1 (cl (= (select (store A x 2) x) 2)) :rule arrays_idx)": true,
        }
        "Indices are different" {
            "(step t1 (cl (= (select (store A 1 x) 2) x)) :rule arrays_idx)": false,
        }
        "Elements are different" {
            "(step t1 (cl (= (select (store A 1 x) 1) y)) :rule arrays_idx)": false,
        }
    }
}

#[test]
fn row() {
    test_cases! {
        definitions = "
            (declare-fun A () (Array Int Int))
            (declare-fun B () (Array Int Int))
            (declare-const x Int)
            (declare-const i Int)
            (declare-const j Int)
            (declare-const k Int)
        ",
        "Simple working examples" {
            "(assume h1 (not (= i j)))
            (step t2 (cl (= (select (store A i x) j) (select A j)))
                :rule arrays_row :premises (h1))": true,
        }
        "Indices in the conclusion are different" {
            "(assume h1 (not (= i j)))
            (step t2 (cl (= (select (store A i x) j) (select A k)))
                :rule arrays_row :premises (h1))": false,
        }
        "Arrays in the conclusion are different" {
            "(assume h1 (not (= i j)))
            (step t2 (cl (= (select (store A i x) j) (select B j)))
                :rule arrays_row :premises (h1))": false,
        }
        "Indices are not the same as in the premise" {
            "(assume h1 (not (= i k)))
            (step t2 (cl (= (select (store A i x) j) (select A j)))
                :rule arrays_row :premises (h1))": false,
        }
    }
}

#[test]
fn row_contra() {
    test_cases! {
        definitions = "
            (declare-fun A () (Array Int Int))
            (declare-fun B () (Array Int Int))
            (declare-const x Int)
            (declare-const i Int)
            (declare-const j Int)
            (declare-const k Int)
        ",
        "Simple working examples" {
            "(assume h1 (not (= (select (store A i x) j) (select A j))))
            (step t2 (cl (= i j)) :rule arrays_row_contra :premises (h1))": true,
        }
        "Conclusion may be flipped" {
            "(assume h1 (not (= (select (store A i x) j) (select A j))))
            (step t2 (cl (= j i)) :rule arrays_row_contra :premises (h1))": true,
        }
        "Conclusion has the wrong index" {
            "(assume h1 (not (= (select (store A i x) j) (select A j))))
            (step t2 (cl (= i k)) :rule arrays_row_contra :premises (h1))": false,
        }
        "Indices in the premise are different" {
            "(assume h1 (not (= (select (store A i x) j) (select A k))))
            (step t2 (cl (= i j)) :rule arrays_row_contra :premises (h1))": false,
        }
        "Arrays in the premise are different" {
            "(assume h1 (not (= (select (store A i x) j) (select B j))))
            (step t2 (cl (= i j)) :rule arrays_row_contra :premises (h1))": false,
        }
    }
}

#[test]
fn ext() {
    test_cases! {
        definitions = "
            (declare-fun A () (Array Int Int))
            (declare-fun B () (Array Int Int))
            (declare-fun C () (Array Int Int))
        ",
        "Simple working examples" {
            "(assume h1 (not (= A B)))
            (step t2 (cl (not (=
                (select A (choice ((x Int)) (or (= A B) (not (= (select A x) (select B x))))))
                (select B (choice ((x Int)) (or (= A B) (not (= (select A x) (select B x))))))
            ))) :rule arrays_ext :premises (h1))": true,
        }
        "Arrays are not the same as in the premise" {
            "(assume h1 (not (= A B)))
            (step t2 (cl (not (=
                (select A (choice ((x Int)) (or (= A B) (not (= (select A x) (select B x))))))
                (select C (choice ((x Int)) (or (= A B) (not (= (select A x) (select B x))))))
            ))) :rule arrays_ext :premises (h1))": false,
        }
        "Indices in the conclusion are different" {
            "(assume h1 (not (= A B)))
            (step t2 (cl (not (=
                (select A (choice ((x Int)) (or (= A B) (not (= (select A x) (select B x))))))
                (select B (choice ((y Int)) (or (= A B) (not (= (select A y) (select B y))))))
            ))) :rule arrays_ext :premises (h1))": false,
        }
        "Index is not the skolem term" {
            "(assume h1 (not (= A B)))
            (step t2 (cl (not (= (select A 0) (select B 0))))
                :rule arrays_ext :premises (h1))": false,
        }
        "Empty conclusion" {
            "(assume h1 (not (= A B)))
            (step t2 (cl) :rule arrays_ext :premises (h1))": false,
        }
    }
}
