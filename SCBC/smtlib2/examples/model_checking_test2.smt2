(declare-datatypes () ((State (mkState (balance Int)))))

(define-fun initial ((state State)) Bool
  (= (balance state) 100)
)

(define-fun loseMoney ((current State) (next State)) Bool
  (= (balance next) (- (balance current) 20))
)

(define-fun notEmpty ((p (List State))) Bool 
  (not (= p nil))
)

(define-fun empty ((p (List State))) Bool
  (= p nil)
)

(define-fun balanceUnderZero ((state State)) Bool
  (< (balance state) 0) 
)

(define-fun checkTransition ((states (List State))) Bool
  (implies (and (notEmpty states) (notEmpty (tail states)))
    (and (loseMoney (head states) (head (tail states)))
      (and (checkTransition (tail states))
        (ite (balanceUnderZero (head (tail states)))
          (empty (tail (tail states)))
          (notEmpty (tail (tail states)))
        )
      )
    )
  )    
)

(declare-fun checkTransition ((List State)) Bool)

(assert 
	(forall ((states (List State))) 
	  	(!
		    (checkTransition states) 
		    :pattern (checkTransition states) 
	  	)
  	)
)

;(assert 
;  (forall ((states (List State)))
;    (!
;      (implies (and (notEmpty states) (notEmpty (tail states)))
;      (and (loseMoney (head states) (head (tail states)))
        ;(and (checkTransition (tail states))
;          (ite (balanceUnderZero (head (tail states)))
;            (empty (tail (tail states)))
;            (notEmpty (tail (tail states)))
;          )
        ;)
;      )
;    ) :pattern (checkTransition states))
;  )
;)

(declare-const states (List State))

(assert 
  (and (notEmpty states) 
    (and (initial (head states))
      (and (notEmpty (tail states))
        (and (loseMoney (head states) (head (tail states)))
          (checkTransition states)
        )
      ) 
    ) 
  )
)

(check-sat)
(get-model)

(get-value ((head states) (head (tail states))))
