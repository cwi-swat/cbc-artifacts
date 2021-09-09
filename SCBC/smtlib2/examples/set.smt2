(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
;(set-option :produce-unsat-cores true)
(set-option :model.compact true)

(define-sort Set () (Array Int Bool))

(define-fun add ((aa Set) (elem Int)) Set
	(store aa elem true)
)

(define-fun filter ((aa Set) (k Int)) Bool
	true
)

(define-fun term ((aa Set) (k Int)) Bool
	(select aa k)
)

; SUMMATION AXIOMS ;;;;;;;;;;;;;
(declare-fun setSum (Int Int Set) Int)
(declare-fun setS (Int Int Set) Int)

; Synonym axiom
(assert 
	(forall ( (lo Int) (hi Int) (aa Set)) (!
			(= (setSum lo hi aa) (setS lo hi aa))
	:pattern ( (setSum lo hi aa) ) ))
)

; Induction below axioms
(assert
	(forall ((lo Int) (hi Int) (aa Set)) (!
		(=> (< lo hi) 
			(ite (and (filter aa lo) (term aa lo))
				(= (setS lo hi aa) (+ (setS (+ lo 1) hi aa) lo))
				(= (setS lo hi aa) (setS (+ lo 1) hi aa))
			)
		)
	:pattern ((setS lo hi aa)) ))
)

; Induction above axioms
(assert
	(forall ((lo Int) (hi Int) (aa Set)) (!
		(=> (< lo hi) 
			(ite (and (filter aa (- hi 1)) (term aa (- hi 1)))
				(= (setS lo hi aa) (+ (setS lo (- hi 1) aa) (- hi 1)))
				(= (setS lo hi aa) (setS lo (- hi 1) aa))
			)
		)
	:pattern ((setS lo hi aa)) ))
)

; Split range axiom
(assert
	(forall ((lo Int) (mid Int) (hi Int) (aa Set)) (!
		(=> (and (<= lo mid) (<= mid hi))
			(= (+ (setS lo mid aa) (setS mid hi aa)) (setS lo hi aa))
		)
		
		:pattern ((setS lo mid aa) (setS mid hi aa))
		;:pattern ((s_0 lo mid aa) (s_0 lo hi aa)) 
	))
)

(declare-const test1 Set)
(declare-const test2 Set)

(assert (forall ((x Int))
	(ite (or (= x 1) (= x 4) (= x 5) (= x 6) (= x 7) (= x 8) (= x 30))
		(select test1 x)
		(not (select test1 x))
	)
))

(declare-const result Int)

(push 1)
(check-sat)
(get-model)

(get-value (result))
