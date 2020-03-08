;formal verification of module1 design
(set-logic QF_BV)

;inputs: x, y, n0 to n3, e0 to e3, d0 to d3, gc for threshold gate
(declare-fun x () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))

(declare-fun n0 () (_ BitVec 2))
(declare-fun n1 () (_ BitVec 2))
(declare-fun n2 () (_ BitVec 2))
(declare-fun n3 () (_ BitVec 2))

(declare-fun e0 () (_ BitVec 2))
(declare-fun e1 () (_ BitVec 2))
(declare-fun e2 () (_ BitVec 2))
(declare-fun e3 () (_ BitVec 2))

(declare-fun d0 () (_ BitVec 2))
(declare-fun d1 () (_ BitVec 2))
(declare-fun d2 () (_ BitVec 2))
(declare-fun d3 () (_ BitVec 2))

;outputs: z
(declare-fun z () (_ BitVec 8))

; NCL Gate Boolean Function - TH14: (A + B + C + D)
(define-fun th14 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
    (ite
        (=
            (_ bv1 1)
            (bvand
                (bvnot a)
                (bvnot b)
                (bvnot c)
                (bvnot d)))
        (_ bv0 1)
        (ite
            (=
                (_ bv1 1)
                (bvor a b c d))
            (_ bv1 1)
            gl))
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

; NCL Gate Boolean Function - TH33: (ABC)
(define-fun th33 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
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
                (bvand a b c))
            (_ bv1 1)
            gl))
)
	
;extract rail0
(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
	((_ extract 0 0) a)
)
	
;extract rail1
(define-fun rail1 ((a (_ BitVec 2))) (_ BitVec 1)
	((_ extract 1 1) a)
)
	
;determine if dual rail is valid data
(define-fun datap ((a (_ BitVec 2))) (Bool)
	(or
		(= (_ bv1 2) a)
		(= (_ bv2 2) a)
	)
)

;boolean mux
(define-fun boolmux ((a (_ BitVec 8)) (b (_ BitVec 8)) (s (_ BitVec 1))) (_ BitVec 8)
	(ite (= s (_ bv0 1)) a b)
)

(declare-fun gc0 () (_ BitVec 1))
(declare-fun gc1 () (_ BitVec 1))
(declare-fun gc2 () (_ BitVec 1))
(declare-fun gc3 () (_ BitVec 1))
(declare-fun gc4 () (_ BitVec 1))
(declare-fun gc5 () (_ BitVec 1))
(declare-fun gc6 () (_ BitVec 1))
(declare-fun gc7 () (_ BitVec 1))
(declare-fun gc8 () (_ BitVec 1))
(declare-fun gc9 () (_ BitVec 1))
(declare-fun gc10 () (_ BitVec 1))
(declare-fun gc11 () (_ BitVec 1))
(declare-fun gc12 () (_ BitVec 1))
(declare-fun gc13 () (_ BitVec 1))
(declare-fun gc14 () (_ BitVec 1))
(declare-fun gc15 () (_ BitVec 1))
(declare-fun gc16 () (_ BitVec 1))
(declare-fun gc17 () (_ BitVec 1))
(declare-fun gc18 () (_ BitVec 1))
(declare-fun gc19 () (_ BitVec 1))
(declare-fun gc20 () (_ BitVec 1))
(declare-fun gc21 () (_ BitVec 1))
(declare-fun gc22 () (_ BitVec 1))
(declare-fun gc23 () (_ BitVec 1))
(declare-fun gc24 () (_ BitVec 1))
(declare-fun gc25 () (_ BitVec 1))
(declare-fun gc26 () (_ BitVec 1))
(declare-fun gc27 () (_ BitVec 1))
(declare-fun gc28 () (_ BitVec 1))
(declare-fun gc29 () (_ BitVec 1))
(declare-fun gc30 () (_ BitVec 1))
(declare-fun gc31 () (_ BitVec 1))
(declare-fun gc32 () (_ BitVec 1))
(declare-fun gc33 () (_ BitVec 1))
(declare-fun gc34 () (_ BitVec 1))
(declare-fun gc35 () (_ BitVec 1))
(declare-fun gc36 () (_ BitVec 1))
(declare-fun gc37 () (_ BitVec 1))
(declare-fun gc38 () (_ BitVec 1))
(declare-fun gc39 () (_ BitVec 1))
(declare-fun gc40 () (_ BitVec 1))
	
;SAT/UNSAT assertion
(assert
	(not
		(let
			(
				(K (concat e3 e2 e1 e0))
				(L (concat d3 d2 d1 d0))
				(sel (th22 (rail1 y) (rail0 y) gc0))
			)
		(let
			(
				(m (boolmux K L sel))
			)
		(let
			(
				(m3 ((_ extract 7 6) m))
				(m2 ((_ extract 5 4) m))
				(m1 ((_ extract 3 2) m))
				(m0 ((_ extract 1 0) m))
			)
		(let
			(
				(I0 (th33 (rail0 n0) (rail0 m0) (_ bv0 1) gc1))
				(I1 (th33 (rail0 n0) (rail0 m0) (rail1 x) gc2))
				(I2 (th33 (rail0 n0) (rail1 m0) (_ bv0 1) gc3))
				(I3 (th33 (rail1 n0) (rail0 m0) (rail1 x) gc4))
				(I4 (th33 (rail0 n0) (rail1 m0) (rail1 x) gc5))
				(I5 (th33 (rail1 n0) (rail1 m0) (_ bv0 1) gc6))
				(I6 (th33 (rail1 n0) (rail1 m0) (rail1 x) gc7))
				(I7 (th33 (rail1 n0) (rail0 m0) (_ bv0 1) gc8))
				
				(I10 (th33 (rail0 n1) (rail0 m1) (_ bv0 1) gc9))
				(I11 (th33 (rail0 n1) (rail0 m1) (rail1 x) gc10))
				(I12 (th33 (rail0 n1) (rail1 m1) (_ bv0 1) gc11))
				(I13 (th33 (rail1 n1) (rail0 m1) (rail1 x) gc12))
				(I14 (th33 (rail0 n1) (rail1 m1) (rail1 x) gc13))
				(I15 (th33 (rail1 n1) (rail1 m1) (_ bv0 1) gc14))
				(I16 (th33 (rail1 n1) (rail1 m1) (rail1 x) gc15))
				(I17 (th33 (rail1 n1) (rail0 m1) (_ bv0 1) gc16))
				
				(I20 (th33 (rail0 n2) (rail0 m2) (_ bv0 1) gc17))
				(I21 (th33 (rail0 n2) (rail0 m2) (rail1 x) gc18))
				(I22 (th33 (rail0 n2) (rail1 m2) (_ bv0 1) gc19))
				(I23 (th33 (rail1 n2) (rail0 m2) (rail1 x) gc20))
				(I24 (th33 (rail0 n2) (rail1 m2) (rail1 x) gc21))
				(I25 (th33 (rail1 n2) (rail1 m2) (_ bv0 1) gc22))
				(I26 (th33 (rail1 n2) (rail1 m2) (rail1 x) gc23))
				(I27 (th33 (rail1 n2) (rail0 m2) (_ bv0 1) gc24))
				
				(I30 (th33 (rail0 n3) (rail0 m3) (_ bv0 1) gc25))
				(I31 (th33 (rail0 n3) (rail0 m3) (rail1 x) gc26))
				(I32 (th33 (rail0 n3) (rail1 m3) (_ bv0 1) gc27))
				(I33 (th33 (rail1 n3) (rail0 m3) (rail1 x) gc28))
				(I34 (th33 (rail0 n3) (rail1 m3) (rail1 x) gc29))
				(I35 (th33 (rail1 n3) (rail1 m3) (_ bv0 1) gc30))
				(I36 (th33 (rail1 n3) (rail1 m3) (rail1 x) gc31))
				(I37 (th33 (rail1 n3) (rail0 m3) (_ bv0 1) gc32))
			)
		(let
			(
				(F0_0 (th14 I0 I1 I2 I3 gc33))
				(F0_1 (th14 I4 I5 I6 I7 gc34))
			
				(F1_0 (th14 I10 I11 I12 I13 gc35))
				(F1_1 (th14 I14 I15 I16 I17 gc36))
			
				(F2_0 (th14 I20 I21 I22 I23 gc37))
				(F2_1 (th14 I24 I25 I26 I27 gc38))
			
				(F3_0 (th14 I30 I31 I32 I33 gc39))
				(F3_1 (th14 I34 I35 I36 I37 gc40))
			)
		(let
			(
				(F0 (concat F0_1 F0_0))
				(F1 (concat F1_1 F1_0))
				(F2 (concat F2_1 F2_0))
				(F3 (concat F3_1 F3_0))
			)
		
		(=>
			(and
				(= (_ bv0 1) gc0)
				(= (_ bv0 1) gc1)
				(= (_ bv0 1) gc2)
				(= (_ bv0 1) gc3)
				(= (_ bv0 1) gc4)
				(= (_ bv0 1) gc5)
				(= (_ bv0 1) gc6)
				(= (_ bv0 1) gc7)
				(= (_ bv0 1) gc8)
				(= (_ bv0 1) gc9)
				(= (_ bv0 1) gc10)
				(= (_ bv0 1) gc11)
				(= (_ bv0 1) gc12)
				(= (_ bv0 1) gc13)
				(= (_ bv0 1) gc14)
				(= (_ bv0 1) gc15)
				(= (_ bv0 1) gc16)
				(= (_ bv0 1) gc17)
				(= (_ bv0 1) gc18)
				(= (_ bv0 1) gc19)
				(= (_ bv0 1) gc20)
				(= (_ bv0 1) gc21)
				(= (_ bv0 1) gc22)
				(= (_ bv0 1) gc23)
				(= (_ bv0 1) gc24)
				(= (_ bv0 1) gc25)
				(= (_ bv0 1) gc26)
				(= (_ bv0 1) gc27)
				(= (_ bv0 1) gc28)
				(= (_ bv0 1) gc29)
				(= (_ bv0 1) gc30)
				(= (_ bv0 1) gc31)
				(= (_ bv0 1) gc32)
				(= (_ bv0 1) gc33)
				(= (_ bv0 1) gc34)
				(= (_ bv0 1) gc35)
				(= (_ bv0 1) gc36)
				(= (_ bv0 1) gc37)
				(= (_ bv0 1) gc38)
				(= (_ bv0 1) gc39)
				(= (_ bv0 1) gc40)
				(= (_ bv1 1) (rail0 x))
				(datap n3)
				(datap n2)
				(datap n1)
				(datap n0)
				(datap e3)
				(datap e2)
				(datap e1)
				(datap e0)
				(datap d3)
				(datap d2)
				(datap d1)
				(datap d0)
				(datap x)
				(datap y)
			)
			(not
				(and (datap F0) (datap F1) (datap F2) (datap F3))
			)
		)))))))
	)
)

(check-sat)
(get-model)