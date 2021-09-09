(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
;(set-option :produce-unsat-cores true)
(set-option :model.compact true)

(declare-datatypes () ((Set (constSet (elems (Array Int Bool)) (size Int) ))))
(declare-datatypes () ((Map (constMap (elems (Array Int Int)) (size Int) ))))
(declare-datatypes () ((FunctionType (constFT (elems (Array Int Int)) (size Int) ))))

(declare-datatypes () ((State (consState (balance (Array Int Int)) (step Int) (idx Int) ))))

(declare-datatypes () ((StateList nil (consList (head State) (tail StateList)))))

(declare-const withdrawAmount Int)
(declare-const depositAmount Int)

(define-fun notEmpty ((p StateList)) Bool 
  (not (= p nil))
)

(define-fun isEmpty ((p StateList)) Bool
  (= p nil)
)

(define-fun initial ((state State)) Bool
  (and (forall ((x Int)) (ite (= x 0) (and (>= (select (balance state) x) 50) (<= (select (balance state) x) 100)) (= (select (balance state) x) 0))) 
    (and (= (step state) 0) (= (idx state) 0))
  )
)

(define-fun copyAndAdd ((old (Array Int Int)) (new (Array Int Int)) (newVal Int) (idx Int)) Bool
  (forall ((x Int))
    (ite (= x idx)
      (= (select new x) newVal)
      (= (select new x) (select old x))
    ) 
  )
)

(define-fun withdraw ((cur State) (nex State)) Bool
  (and (= (step nex) 1) 
    (and (= (idx nex) (+ (idx cur) 1)) 
      (and (> withdrawAmount 0) 
        (and (>= (- (select (balance cur) (idx cur)) withdrawAmount) 0) 
          (copyAndAdd (balance cur) (balance nex) (- (select (balance cur) (idx cur)) withdrawAmount) (idx nex))
        )
      )
    )
  )
)

(define-fun deposit ((cur State) (nex State)) Bool
	(and (= (step nex) 2)
    (and  (= (idx nex) (+ (idx cur) 1)) 
      (and (> depositAmount 0) 
        (and (<= (+ (select (balance cur) (idx cur)) depositAmount) 150) 
          (copyAndAdd (balance cur) (balance nex) (+ (select (balance cur) (idx cur)) depositAmount) (idx nex))
        )
      )
    )
  )
)

(declare-fun sum_0 (Int Int (Array Int Int)) Int)
(declare-fun s_0 (Int Int (Array Int Int)) Int)

(define-fun filter ((aa (Array Int Int)) (k Int)) Bool
  true
)

(define-fun term ((aa (Array Int Int)) (k Int)) Int
  (select aa k)
)

; Synonym axiom
(assert 
  (forall ( (lo Int) (hi Int) (aa (Array Int Int))) (!
      (= (sum_0 lo hi aa) (s_0 lo hi aa))
  :pattern ( (sum_0 lo hi aa) ) ))
)

; Induction below axioms
(assert
  (forall ((lo Int) (hi Int) (aa (Array Int Int))) (!
    (=> (< lo hi) 
      (ite (filter aa lo)
        (= (s_0 lo hi aa) (+ (s_0 (+ lo 1) hi aa) (term aa lo)))
        (= (s_0 lo hi aa) (s_0 (+ lo 1) hi aa))
      )
    )
  :pattern ((s_0 lo hi aa)) ))
)

; Induction above axioms
(assert
  (forall ((lo Int) (hi Int) (aa (Array Int Int))) (!
    (=> (< lo hi) 
      (ite (filter aa (- hi 1))
        (= (s_0 lo hi aa) (+ (s_0 lo (- hi 1) aa) (term aa (- hi 1))))
        (= (s_0 lo hi aa) (s_0 lo (- hi 1) aa))
      )
    )
  :pattern ((s_0 lo hi aa)) ))
)

; Split range axiom
(assert
  (forall ((lo Int) (mid Int) (hi Int) (aa (Array Int Int))) (!
    (=> (and (<= lo mid) (<= mid hi))
      (= (+ (s_0 lo mid aa) (s_0 mid hi aa)) (s_0 lo hi aa))
    )
  :pattern ((s_0 lo mid aa) (s_0 mid hi aa))
  ;:pattern ((s_0 lo mid aa) (s_0 lo hi aa)) 
  ))
)

(define-fun sumOfBalanceOverTwoHundred ((state State)) Bool
  (> (sum_0 0 (+ (idx state) 1) (balance state)) 299)
)

(define-fun balanceUnderZero ((state State)) Bool
  	(< (select (balance state) (idx state)) 0) 
)

(define-fun balanceOverHundredFifty ((state State)) Bool
	(> (select (balance state) (idx state)) 149)
)

(define-fun transitionCondition ((cur State) (nex State)) Bool
	(and (or (withdraw cur nex) (deposit cur nex)) (< (idx cur) 2)); (deposit cur nex)) (< (idx cur) 11))  (withdraw cur nex)
) 

(define-fun errorCondition ((state State)) Bool
	(or (balanceUnderZero state) (balanceOverHundredFifty state) (sumOfBalanceOverTwoHundred state)) ;(balanceOverThousand state))
)

(declare-fun checkTransition ((StateList)) Bool)

(assert 
	(forall ((sts StateList))
  	(!	
  		(and 
  			(= (isEmpty (tail sts)) (errorCondition (head sts)))
  			(=> (and (notEmpty sts) (notEmpty (tail sts)))
 	    	 		  (and (transitionCondition (head sts) (head (tail sts)))
     					  (checkTransition (tail sts))
      			  )
     		) 
      )
     	:pattern ((checkTransition sts))
  	) 
  ) 
)

(declare-const states StateList)

(assert (and (> withdrawAmount 10) (< withdrawAmount 20)))
(assert (and (> depositAmount 10) (< depositAmount 20)))

(assert 
  (and (notEmpty states) 
    (and (initial (head states))
      (checkTransition states)
    ) 
  )
)

(push 1)
(check-sat)

(get-model)
