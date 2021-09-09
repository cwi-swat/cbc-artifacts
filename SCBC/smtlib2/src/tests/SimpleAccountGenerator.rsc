module tests::SimpleAccountGenerator

import IO;

void generateAccountProblem(int goalBalance, int amountLowerBound, int amountUpperBound, int maxDepth, loc output) {
  str problem = "(declare-sort State)
                '
                '(declare-fun balance (State) Int)
                '(declare-fun amount (State) Int)
                '(declare-fun step (State) Int)
                '
                '(define-fun withdraw ((current State) (next State)) Bool
                '  (and 
                '    (\> (amount next) <amountLowerBound>) (\< (amount next) <amountUpperBound>)
                '    (\> (- (balance current) (amount next)) 0)
                '    (= (balance next) (- (balance current) (amount next)))
                '    (= (step next) 1)
                '  )    
                ') 
                '
                '(define-fun deposit ((current State) (next State)) Bool
                '  (and 
                '    (\> (amount next) <amountLowerBound>) (\< (amount next) <amountUpperBound>)
                '    (= (balance next) (+ (balance current) (amount next)))
                '    (= (step next) 2)
                '  )    
                ') 
                '
                '(define-fun transition ((current State) (next State)) Bool
                '  (or 
                '    (deposit current next) 
                '    (withdraw current next)
                '  ) 
                ')
                '
                '(define-fun initial ((state State)) Bool
                '  (and
                '    (= (balance state) 0)
                '    (= (amount state) 0)
                '    (= (step state) 0)
                '  )  
                ')
                '
                '(define-fun goal ((state State)) Bool
                '  (\>= (balance state) <goalBalance>) 
                ')
                '<for (int i <- [0..maxDepth]) {>
                '(declare-const S<i> State)<}>
                '
                '(assert 
                '  (and
                '    (initial S0)
                '    (or <for (int i <- [1..maxDepth]) {>
                '      (and <for (int j <- [0..i]) {> (transition S<j> S<j+1>) <}> (goal S<i>))<}>
                '    )
                '  )
                ')
                '
                '(check-sat)";
                
  writeFile(output, problem);
}

void generateTransferProblem(int maxDepth, loc output) {
  str problem = "(declare-sort State)
                '(declare-fun balance1 (State) Int)
                '(declare-fun balance2 (State) Int)
                '(declare-fun amount (State) Int)
                '
                '(define-fun from1To2 ((current State) (next State)) Bool
                '  (and
                '    (\>= (balance1 current) (amount current)) ; guard
                '    
                '    
                '    (= (- (balance1 current) (amount current)) (balance1 next))
                '    (= (+ (balance2 current) (amount current)) (balance2 next))
                '    (\> (amount next) 0)
                '  )    
                ') 
                '(define-fun from2To1 ((current State) (next State)) Bool
                '  (and
                '    (\>= (balance2 current) (amount current)) ; guard
                '        
                '    (= (+ (balance1 current) (amount current)) (balance1 next))
                '    (= (- (balance2 current) (amount current)) (balance2 next))
                '    (\> (amount next) 0)
                '  )    
                ') 
                '(define-fun transition ((current State) (next State)) Bool
                '  (or 
                '    (from1To2 current next) 
                '    (from2To1 current next)
                '  ) 
                ')
                '(define-fun initial ((state State)) Bool
                '  (and
                '    (= (balance1 state) 100)
                '    (= (balance2 state) 100)
                '    (\> (amount state) 0)
                '  )  
                ')
                '(define-fun goal ((state State)) Bool
                '  (\> (balance1 state) 200) 
                ')
                '<for (int i <- [0..maxDepth]) {>
                '(declare-const S<i> State)<}>
                '
                '(assert 
                '  (and
                '    (initial S0)
                '    (or <for (int i <- [1..maxDepth]) {>
                '      (and <for (int j <- [0..i]) {> (transition S<j> S<j+1>) <}> (goal S<i>))<}>
                '    )
                '  )
                ')
                '
                '(check-sat)";
                
  writeFile(output, problem);
}