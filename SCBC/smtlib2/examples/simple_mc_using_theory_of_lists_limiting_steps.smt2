(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model.compact true)

(declare-datatypes () ((State (state (counter Int) (step Int)))))
(declare-datatypes () ((StateList (lst (head State) (tail StateList)) nil)))

(define-fun isEmpty ((sl StateList)) Bool
  (= sl nil)
)

(define-fun notEmpty ((sl StateList)) Bool
  (not (isEmpty sl))
)
 
(define-fun initial ((st State)) Bool
  (and 
    (= (counter st) 0)
    (= (step st) 0)
  )
)

(define-fun transitionCondition ((cur State) (nex State)) Bool
  (and
    (or
      (= (counter nex) (+ (counter cur) 1))
      (= (counter nex) (- (counter cur) 1))
    )
    (= (step nex) (+ (step cur) 1))
    (< (step cur) 10)
  )
) 

(define-fun errorCondition ((st State)) Bool
  (> (counter st) 9)
)

(declare-fun checkTransition (StateList) Bool)

(assert 
	(forall ((sts StateList))
  	(!	
  		(and 
        (= (isEmpty (tail sts)) (errorCondition (head sts)))
  			(=> (and (notEmpty sts) (notEmpty (tail sts)))	  
          (and (transitionCondition (head sts) (head (tail sts))) (checkTransition (tail sts)))
     		) 
      )
     	:pattern ((checkTransition sts))
  	) 
  ) 
)

(declare-const states StateList)

(assert (and (notEmpty states) (initial (head states)) (checkTransition states)))

(push 1)

(check-sat)
(get-model)
