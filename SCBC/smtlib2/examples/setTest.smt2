(define-sort Set (T) (Array T Bool))

(declare-const x (Set Int))

(define-fun in ((e Int) (E (Set Int))) Bool 
	(select E e)
)

(assert (in 5 x))

(check-sat)
(get-model)