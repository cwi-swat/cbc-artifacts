(declare-datatypes () ((Set (constSet (elems (Array Int Bool)) (size Int) ))))
(declare-datatypes () ((Map (constMap (elems (Array Int Int)) (size Int) ))))
(declare-datatypes () ((FuncOverTime (constFT (elems (Array Int Int)) (size Int) ))))

(define-fun add ((old Set) (new Set) (elem Int)) Bool
	(forall ((x Int))
		(ite (select (elems old) x)
			(select (elems new) x)
			(ite (= x elem)
				(select (elems new) x)
				(and (not (select (elems new) x)) (= (size new) (+ (size old) 1)))
			)
		)	
	)
)

(declare-const test1 Set)
(declare-const test2 Set)

(assert (select (elems test1) 1))
(assert (select (elems test1) 2))
(assert (select (elems test1) 3))
(assert (select (elems test1) 4))
(assert (select (elems test1) 5))
(assert (select (elems test1) 6))
(assert (select (elems test1) 7))
(assert (select (elems test1) 8))

(assert (= (size test1) 8))

(assert (add test1 test2 10))
(assert (= (size test2) 9))

(assert (not (select (elems test1) 10)))
(assert (select (elems test2) 10))

(assert (select (elems test1) 1))
(assert (select (elems test2) 1))

(check-sat)
(get-model)