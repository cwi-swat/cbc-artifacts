(declare-datatypes () (  ( Date (consDate (date Int) (month Int) (year Int)) (undefDate) ) ))

(define-fun > ( (d1 Date) (d2 Date)) Bool
  (and (>  (year  d1) (year  d2))
    (>  (month  d1) (month  d2))
    (>  (date  d1) (date  d2))))

(define-fun fun_int ( (int1 Int) (int2 Int)) Bool
  (> int1 int2))