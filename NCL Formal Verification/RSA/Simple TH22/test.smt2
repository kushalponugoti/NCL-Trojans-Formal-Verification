; Formal verification proof - observability XOR
(set-logic QF_BV)

; Inputs: A, B, K
(declare-fun A () (_ BitVec 2))
(declare-fun B () (_ BitVec 2))
(declare-fun K () (_ BitVec 2))

; Outputs: Z
;(declare-fun F () (_ BitVec 2))

; Extract rail0 of a dual rail signal
(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 0 0) a)
)

; Extract rail1 of a dual rail signal
(define-fun rail1 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 1 1) a)
)

(define-fun datap ((a (_ BitVec 2))) (Bool)
    (or
        (= (_ bv1 2) a)
        (= (_ bv2 2) a)
    )
)

; Determine if the dual rail signal is null (0b00)
(define-fun nullp ((a (_ BitVec 2))) (Bool)
    (and
        (= (_ bv0 1) (rail0 a))
        (= (_ bv0 1) (rail1 a))
    )
)

; NCL Gate Boolean Function - TH22: (AB)
(define-fun th22 ((a (_ BitVec 1)) (b (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
    (ite
        (=
            (_ bv1 1)
            (bvand
                (bvnot a)
                (bvnot b)))
        (_ bv0 1)
        (ite
            (=
                (_ bv1 1)
                (bvand a b))
            (_ bv1 1)
            gl))
)

; NCL Gate Boolean Function - TH12: (A + B)
(define-fun th12 ((a (_ BitVec 1)) (b (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
    (ite
        (=
            (_ bv1 1)
            (bvand
                (bvnot a)
                (bvnot b)))
        (_ bv0 1)
        (ite
            (=
                (_ bv1 1)
                (bvor a b))
            (_ bv1 1)
            gl))
)

; NCL Gate Boolean Function - TH23w2: (A + BC)
(define-fun th23w2 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
    (ite
        (=
            (_ bv1 1)
            (bvand
                (bvnot a)
                (bvnot b)
                (bvnot c)))
        (_ bv0 1)
        (ite
            (=
                (_ bv1 1)
                (bvor a
                    (bvand b c)))
            (_ bv1 1)
            gl))
)

(define-fun mux ((a (_ BitVec 1)) (b (_ BitVec 1)) (sel (_ BitVec 1))) (_ BitVec 1)
	(ite (= sel (_ bv0 1)) a b)
)
; Current values of threshold gates
(declare-fun Gc_0 () (_ BitVec 1))

(assert
    (not
        (let
            ( (T (th22 (rail1 A) (rail0 A) Gc_0)))
        (let
            ((F (concat (mux (rail1 B) (rail1 K) T) (mux (rail0 B) (rail0 K) T))))
        (=>
            (and
                (datap A)
				;(= (bvand (rail1 A) (rail0 A)) (_ bv1 1))
                (datap B)
                (datap K)
				;(= T (_ bv1 1))
                ;(= Gc_0 (_ bv0 1))
			)
            (not
                (datap F)))))
	)
)

(check-sat)
(get-model)