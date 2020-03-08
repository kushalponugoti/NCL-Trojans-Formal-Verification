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

(declare-fun gc () (_ BitVec 1))

;outputs: z
(declare-fun z () (_ BitVec 8))

;NCL gate Boolean function - TH14: (A + B + C + D)
(define-fun th14 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (g1 (_ BitVec 1))) (_ BitVec 1)
	(bvor a (bvor b (bvor c d)))
)

;NCL gate Boolean function - TH22: (AB)
(define-fun th22 ((a (_ BitVec 1)) (b (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
	(bvand a b)
)

;NCL gate Boolean function - TH33: (ABC)
(define-fun th33 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
	(bvand a (bvand b c))
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
	
;SAT/UNSAT assertion
(assert
	(not
		(let
			(
				(K (concat e3 e2 e1 e0))
				(L (concat d3 d2 d1 d0))
				(sel (th22 (rail1 y) (rail0 y) gc))
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
				(I0 (th33 (rail0 n0) (rail0 m0) (rail0 x) gc))
				(I1 (th33 (rail0 n0) (rail0 m0) (rail1 x) gc))
				(I2 (th33 (rail0 n0) (rail1 m0) (rail0 x) gc))
				(I3 (th33 (rail1 n0) (rail0 m0) (rail1 x) gc))
				(I4 (th33 (rail0 n0) (rail1 m0) (rail1 x) gc))
				(I5 (th33 (rail1 n0) (rail1 m0) (rail0 x) gc))
				(I6 (th33 (rail1 n0) (rail1 m0) (rail1 x) gc))
				(I7 (th33 (rail1 n0) (rail0 m0) (rail0 x) gc))
				
				(I10 (th33 (rail0 n1) (rail0 m1) (rail0 x) gc))
				(I11 (th33 (rail0 n1) (rail0 m1) (rail1 x) gc))
				(I12 (th33 (rail0 n1) (rail1 m1) (rail0 x) gc))
				(I13 (th33 (rail1 n1) (rail0 m1) (rail1 x) gc))
				(I14 (th33 (rail0 n1) (rail1 m1) (rail1 x) gc))
				(I15 (th33 (rail1 n1) (rail1 m1) (rail0 x) gc))
				(I16 (th33 (rail1 n1) (rail1 m1) (rail1 x) gc))
				(I17 (th33 (rail1 n1) (rail0 m1) (rail0 x) gc))
				
				(I20 (th33 (rail0 n2) (rail0 m2) (rail0 x) gc))
				(I21 (th33 (rail0 n2) (rail0 m2) (rail1 x) gc))
				(I22 (th33 (rail0 n2) (rail1 m2) (rail0 x) gc))
				(I23 (th33 (rail1 n2) (rail0 m2) (rail1 x) gc))
				(I24 (th33 (rail0 n2) (rail1 m2) (rail1 x) gc))
				(I25 (th33 (rail1 n2) (rail1 m2) (rail0 x) gc))
				(I26 (th33 (rail1 n2) (rail1 m2) (rail1 x) gc))
				(I27 (th33 (rail1 n2) (rail0 m2) (rail0 x) gc))
				
				(I30 (th33 (rail0 n3) (rail0 m3) (rail0 x) gc))
				(I31 (th33 (rail0 n3) (rail0 m3) (rail1 x) gc))
				(I32 (th33 (rail0 n3) (rail1 m3) (rail0 x) gc))
				(I33 (th33 (rail1 n3) (rail0 m3) (rail1 x) gc))
				(I34 (th33 (rail0 n3) (rail1 m3) (rail1 x) gc))
				(I35 (th33 (rail1 n3) (rail1 m3) (rail0 x) gc))
				(I36 (th33 (rail1 n3) (rail1 m3) (rail1 x) gc))
				(I37 (th33 (rail1 n3) (rail0 m3) (rail0 x) gc))
			)
		(let
			(
				(F0_0 (th14 I0 I1 I2 I3 gc))
				(F0_1 (th14 I4 I5 I6 I7 gc))
			
				(F1_0 (th14 I10 I11 I12 I13 gc))
				(F1_1 (th14 I14 I15 I16 I17 gc))
			
				(F2_0 (th14 I20 I21 I22 I23 gc))
				(F2_1 (th14 I24 I25 I26 I27 gc))
			
				(F3_0 (th14 I30 I31 I32 I33 gc))
				(F3_1 (th14 I34 I35 I36 I37 gc))
			)
		
		(=>
			(and
				(= (_ bv0 1) gc)
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
			
				(= (_ bv0 1) sel)
		))))))
	)
)

(check-sat)
(get-model)