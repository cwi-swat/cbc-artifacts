(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model.compact true)

(declare-fun sum_0 (Int Int (Array Int Int)) Int)
(declare-fun s_0 (Int Int (Array Int Int)) Int)

(define-fun filter ((aa (Array Int Int)) (k Int)) Bool
	true
)

(define-fun term ((aa (Array Int Int)) (k Int)) Int
	(select aa k)
)

; Synonym axiom
;(assert 
;	(forall ( (lo Int) (hi Int) (aa (Array Int Int))) (!
;			(= (sum_0 lo hi aa) (s_0 lo hi aa))
;	:pattern ( (sum_0 lo hi aa) ) ))
;)

; Unit axiom
;(assert
;	(forall ( (lo Int) (hi Int) (aa (Array Int Int))) (!
;		(=> 
;			(forall ((k Int))
;				(=> (and (<= lo k) (and (< k hi) (filter aa k))) (= (term aa k) 0))
;			)
;			(= (s_0 lo hi aa) 0)
;		)
;	:pattern ((s_0 lo hi aa)) ))
;)

; Induction below axioms
(assert
	(forall ((lo Int) (hi Int) (aa (Array Int Int))) (!
		(=> (and (< lo hi) (filter aa lo))
			(= (s_0 lo hi aa) (+ (s_0 (+ lo 1) hi aa) (term aa lo)))
		)
	:pattern ((s_0 lo hi aa)) ))
)
;(assert
;	(forall ((lo Int) (hi Int) (aa (Array Int Int))) (!
;		(=> (and (< lo hi) (not (filter aa lo)))
;			(= (s_0 lo hi aa) (s_0 (+ lo 1) hi aa))
;		)
;	:pattern ((sum_0 lo hi aa)) ))
;)

; Induction above axioms
(assert
	(forall ((lo Int) (hi Int) (aa (Array Int Int))) (!
		(=> (and (< lo hi) (filter aa (- hi 1)))
			(= (s_0 lo hi aa) (+ (s_0 lo (- hi 1) aa) (term aa (- hi 1))))
		)
	:pattern ((s_0 lo hi aa)) ))
)
;(assert
;	(forall ((lo Int) (hi Int) (aa (Array Int Int))) (!
;		(=> (and (< lo hi) (not (filter aa (- hi 1))))
;			(= (s_0 lo hi aa) (s_0 lo (- hi 1) aa))
;		)
;	:pattern ((sum_0 lo hi aa)) ))
;)

; Split range axiom
(assert
	(forall ((lo Int) (mid Int) (hi Int) (aa (Array Int Int))) (!
		(=> (and (<= lo mid) (<= mid hi))
			(= (s_0 lo hi aa) (+ (s_0 lo mid aa) (s_0 mid hi aa)))
		)
	:pattern ((s_0 lo mid aa) (s_0 mid hi aa))
	:pattern ((s_0 lo mid aa) (s_0 lo hi aa)) 
	))
)

; Same terms axiom
;(assert
;	(forall ((lo Int) (hi Int) (aa (Array Int Int)) (bb (Array Int Int))) (!
;		(=> (forall ((k Int))
;				(=> (and (<= lo k) (< k hi)) 
;					(and (= (filter aa k) (filter bb k)) 
;						(=> (filter aa k) (= (term aa k) (term bb k)))
;					)
;				)
;			)
;			(= (s_0 lo hi aa) (s_0 lo hi bb))
;		)
;	:pattern ((sum_0 lo hi aa) (s_0 lo hi bb)) ))
;)

(declare-const result Int)
;(assert (= result 15))

(declare-const testArr (Array Int Int))

(assert (= (select testArr 0) 1))
(assert (= (select testArr 1) 1))
(assert (= (select testArr 2) 1))
(assert (= (select testArr 3) 1))
(assert (= (select testArr 4) 1))
(assert (= (select testArr 5) 1))
(assert (= (select testArr 6) 1))
(assert (= (select testArr 7) 1))
(assert (= (select testArr 8) 1))
(assert (= (select testArr 9) 1))
(assert (= (select testArr 10) 1))
(assert (= (select testArr 11) 1))
(assert (= (select testArr 12) 1))
(assert (= (select testArr 13) 1))
(assert (= (select testArr 14) 1))
(assert (= (select testArr 15) 1))
(assert (= (select testArr 16) 1))
(assert (= (select testArr 17) 1))
(assert (= (select testArr 18) 1))
(assert (= (select testArr 19) 1))
(assert (= (select testArr 20) 1))
(assert (= (select testArr 21) 1))
(assert (= (select testArr 22) 1))

;(assert (= result 11))
(assert (= result (s_0 0 23 testArr))) 

(push 1)
(check-sat)

(get-model)