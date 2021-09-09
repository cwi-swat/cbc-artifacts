(set-logic HORN)

;(set-option :fixedpoint.engine duality)
;(set-option :fixedpoint.print_certificate true)

;(declare-const car_red_ver Int)
;(declare-const st Int)
;(declare-const car_blue_ver Int)
;(declare-const truck_green_ver Int)
;(declare-const car_orange_hor Int)
;(declare-const car_red_ver Int)
;(declare-const truck_blue_hor Int)
;(declare-const truck_yellow_hor Int)

(declare-datatypes () ((Fixed (cons
	(car_red_ver Int)
	(car_green_ver Int)
	(car_blue_ver Int)
	(truck_green_ver Int)
	(car_orange_hor Int)
	(truck_purple_hor Int)
	(truck_blue_hor Int)
	(truck_yellow_hor Int)
))))

(declare-datatypes () ((State (cons 
	(fixed Fixed)
	(car_red_hor Int) 
	(car_green_hor Int) 
	(car_blue_hor Int) 
	(truck_green_hor Int) 
	(car_orange_ver Int)
	(truck_purple_ver Int)
	(truck_blue_ver Int)
	(truck_yellow_ver Int)
))))

(define-fun fixedPos ((st State)) Bool
	(and 
		(= (car_red_ver (fixed st)) 2) 
		(= (car_green_ver (fixed st)) 0) 
		(= (car_blue_ver (fixed st)) 4) 
		(= (truck_green_ver (fixed st)) 5)
		(= (car_orange_hor (fixed st)) 0)
		(= (truck_purple_hor (fixed st)) 0)
		(= (truck_blue_hor (fixed st)) 3)
		(= (truck_yellow_hor (fixed st)) 5) 
	)
)

(define-fun initial ((st State)) Bool 
	(and
		(fixedPos st)
		(= (car_red_hor st) 1)
		(= (car_green_hor st) 0)
		(= (car_blue_hor st) 4)
		(= (truck_green_hor st) 2)
		(= (car_orange_ver st) 4)
		(= (truck_purple_ver st) 1)
		(= (truck_blue_ver st) 1)
		(= (truck_yellow_ver st) 0)
	)
)

(define-fun stayInLane ((pos Int) (length Int)) Bool
	(and (>= pos 0) (<= (+ pos length) 6)) ; watch out, + 1 on the total size of lane because of location + length. should have been location + length - 1.
)

(define-fun carRedMoveLeft ((current State) (next State)) Bool
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed current)) (car_red_hor next)) (<= (truck_purple_hor (fixed current)) (car_red_hor current)))
			(or (>= (+ (car_red_ver (fixed current))(* (- 1) (truck_purple_ver current))) 3)
				(> (truck_purple_ver current) (car_red_ver (fixed current)))))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed current)) (car_red_hor next)) (<= (car_orange_hor (fixed current)) (car_red_hor current)))
			(or (>= (+ (car_red_ver (fixed current))(* (- 1) (car_orange_ver current))) 2)
				(> (car_orange_ver current) (car_red_ver (fixed current))))) 

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed current)) (car_red_hor next)) (<= (truck_blue_hor (fixed current)) (car_red_hor current)))
			(or (>= (+ (car_red_ver (fixed current))(* (- 1) (truck_blue_ver current))) 3)
				(> (truck_blue_ver current) (car_red_ver (fixed current)))))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed current)) (car_red_hor next)) (<= (truck_yellow_hor (fixed current)) (car_red_hor current)))
			(or (>= (+ (car_red_ver (fixed current))(* (- 1) (truck_yellow_ver current))) 3)
				(> (truck_yellow_ver current) (car_red_ver (fixed current)))))
	)
)

(define-fun carRedMoveRight ((current State) (next State)) Bool
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed current))(+ (car_red_hor current) 2)) (<= (truck_purple_hor (fixed current))(+ (car_red_hor next) 2)))
			(or (>= (+ (car_red_ver (fixed current))(* (- 1) (truck_purple_ver current))) 3)
				(> (truck_purple_ver current) (car_red_ver (fixed current)))))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed current)) (+ (car_red_hor current) 2)) (<= (car_orange_hor (fixed current)) (+ (car_red_hor next) 2)))
			(or (>= (+ (car_red_ver (fixed current))(* (- 1) (car_orange_ver current))) 2)
				(> (car_orange_ver current) (car_red_ver (fixed current))))) 

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed current)) (+ (car_red_hor current) 2)) (<= (truck_blue_hor (fixed current)) (+ (car_red_hor next) 2)))
			(or (>= (+ (car_red_ver (fixed current))(* (- 1) (truck_blue_ver current))) 3)
				(> (truck_blue_ver current) (car_red_ver (fixed current)))))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed current)) (+ (car_red_hor current) 2)) (<= (truck_yellow_hor (fixed current)) (+ (car_red_hor next) 2)))
			(or (>= (+ (car_red_ver (fixed current))(* (- 1) (truck_yellow_ver current))) 3)
				(> (truck_yellow_ver current) (car_red_ver (fixed current)))))
	)
)

(define-fun carRedStateInvariant ((st State)) Bool 
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed st))(car_red_hor st)) (< (truck_purple_hor (fixed st))(+ (car_red_hor st) 2)))
			(or (>= (+ (car_red_ver (fixed st))(* (- 1) (truck_purple_ver st))) 3)
				(> (truck_purple_ver st) (car_red_ver (fixed st)))))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed st)) (car_red_hor st)) (< (car_orange_hor (fixed st)) (+ (car_red_hor st) 2)))
			(or (>= (+ (car_red_ver (fixed st))(* (- 1) (car_orange_ver st))) 2)
				(> (car_orange_ver st) (car_red_ver (fixed st))))) 

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed st)) (car_red_hor st)) (< (truck_blue_hor (fixed st)) (+ (car_red_hor st) 2)))
			(or (>= (+ (car_red_ver (fixed st))(* (- 1) (truck_blue_ver st))) 3)
				(> (truck_blue_ver st) (car_red_ver (fixed st)))))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed st)) (car_red_hor st)) (< (truck_yellow_hor (fixed st)) (+ (car_red_hor st) 2)))
			(or (>= (+ (car_red_ver (fixed st))(* (- 1) (truck_yellow_ver st))) 3)
				(> (truck_yellow_ver st) (car_red_ver (fixed st)))))
	)
)

(define-fun carGreenMoveLeft ((current State) (next State)) Bool
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed current))(car_green_hor next)) (<= (truck_purple_hor (fixed current))(car_green_hor current)))
			(or (>= (+ (car_green_ver (fixed current)) (* (- 1) (truck_purple_ver current))) 3)
				(> (truck_purple_ver current) (car_green_ver (fixed current)))))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed current)) (car_green_hor next)) (<= (car_orange_hor (fixed current)) (car_green_hor current)))
			(or (>= (+ (car_green_ver (fixed current)) (* (- 1) (car_orange_ver current))) 2)
				(> (car_orange_ver current) (car_green_ver (fixed current))))) 

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed current)) (car_green_hor next)) (<= (truck_blue_hor (fixed current)) (car_green_hor current)))
			(or (>= (+ (car_green_ver (fixed current))(* (- 1) (truck_blue_ver current))) 3)
				(> (truck_blue_ver current) (car_green_ver (fixed current)))))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed current)) (car_green_hor next)) (<= (truck_yellow_hor (fixed current)) (car_green_hor current)))
			(or (>= (+ (car_green_ver (fixed current))(* (- 1) (truck_yellow_ver current))) 3)
				(> (truck_yellow_ver current) (car_green_ver (fixed current)))))
	)
)

(define-fun carGreenMoveRight ((current State) (next State)) Bool
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed current))(+ (car_green_hor current) 2)) (<= (truck_purple_hor (fixed current))(+ (car_green_hor next) 2)))
			(or (>= (+ (car_green_ver (fixed current))(* (- 1) (truck_purple_ver current))) 3)
				(> (truck_purple_ver current) (car_green_ver (fixed current)))))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed current)) (+ (car_green_hor current) 2)) (<= (car_orange_hor (fixed current)) (+ (car_green_hor next) 2)))
			(or (>= (+ (car_green_ver (fixed current))(* (- 1) (car_orange_ver current))) 2)
				(> (car_orange_ver current) (car_green_ver (fixed current))))) 

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed current)) (+ (car_green_hor current) 2)) (<= (truck_blue_hor (fixed current)) (+ (car_green_hor next) 2)))
			(or (>= (+ (car_green_ver (fixed current))(* (- 1) (truck_blue_ver current))) 3)
				(> (truck_blue_ver current) (car_green_ver (fixed current)))))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed current)) (+ (car_green_hor current) 2)) (<= (truck_yellow_hor (fixed current)) (+ (car_green_hor next) 2)))
			(or (>= (+ (car_green_ver (fixed current))(* (- 1) (truck_yellow_ver current))) 3)
				(> (truck_yellow_ver current) (car_green_ver (fixed current)))))
	)
)

(define-fun carGreenStateInvariant ((st State)) Bool 
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed st)) (car_green_hor st)) (< (truck_purple_hor (fixed st)) (+ (car_green_hor st) 2)))
			(or (>= (+ (car_green_ver (fixed st))(* (- 1) (truck_purple_ver st))) 3)
				(> (truck_purple_ver st) (car_green_ver (fixed st)))))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed st)) (car_green_hor st)) (< (car_orange_hor (fixed st)) (+ (car_green_hor st) 2)))
			(or (>= (+ (car_green_ver (fixed st))(* (- 1) (car_orange_ver st))) 2)
				(> (car_orange_ver st) (car_green_ver (fixed st))))) 

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed st)) (car_green_hor st)) (< (truck_blue_hor (fixed st)) (+ (car_green_hor st) 2)))
			(or (>= (+ (car_green_ver (fixed st))(* (- 1) (truck_blue_ver st))) 3)
				(> (truck_blue_ver st) (car_green_ver (fixed st)))))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed st)) (car_green_hor st)) (< (truck_yellow_hor (fixed st)) (+ (car_green_hor st) 2)))
			(or (>= (+ (car_green_ver (fixed st))(* (- 1) (truck_yellow_ver st))) 3)
				(> (truck_yellow_ver st) (car_green_ver (fixed st)))))
	)
)

(define-fun carBlueMoveLeft ((current State) (next State)) Bool
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed current))(car_blue_hor next)) (<= (truck_purple_hor (fixed current))(car_blue_hor current)))
			(or (>= (+ (car_blue_ver (fixed current))(* (- 1) (truck_purple_ver current))) 3)
				(> (truck_purple_ver current) (car_blue_ver (fixed current)))))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed current)) (car_blue_hor next)) (<= (car_orange_hor (fixed current)) (car_blue_hor current)))
			(or (>= (+ (car_blue_ver (fixed current))(* (- 1) (car_orange_ver current))) 2)
				(> (car_orange_ver current) (car_blue_ver (fixed current))))) 

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed current)) (car_blue_hor next)) (<= (truck_blue_hor (fixed current)) (car_blue_hor current)))
			(or (>= (+ (car_blue_ver (fixed current))(* (- 1) (truck_blue_ver current))) 3)
				(> (truck_blue_ver current) (car_blue_ver (fixed current)))))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed current)) (car_blue_hor next)) (<= (truck_yellow_hor (fixed current)) (car_blue_hor current)))
			(or (>= (+ (car_blue_ver (fixed current))(* (- 1) (truck_yellow_ver current))) 3)
				(> (truck_yellow_ver current) (car_blue_ver (fixed current)))))
	)
)

(define-fun carBlueMoveRight ((current State) (next State)) Bool
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed current))(+ (car_blue_hor current) 2)) (<= (truck_purple_hor (fixed current))(+ (car_blue_hor next) 2)))
			(or (>= (+ (car_blue_ver (fixed current))(* (- 1) (truck_purple_ver current))) 3)
				(> (truck_purple_ver current) (car_blue_ver (fixed current)))))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed current)) (+ (car_blue_hor current) 2)) (<= (car_orange_hor (fixed current)) (+ (car_blue_hor next) 2)))
			(or (>= (+ (car_blue_ver (fixed current))(* (- 1) (car_orange_ver current))) 2)
				(> (car_orange_ver current) (car_blue_ver (fixed current))))) 

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed current)) (+ (car_blue_hor current) 2)) (<= (truck_blue_hor (fixed current)) (+ (car_blue_hor next) 2)))
			(or (>= (+ (car_blue_ver (fixed current))(* (- 1) (truck_blue_ver current))) 3)
				(> (truck_blue_ver current) (car_blue_ver (fixed current)))))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed current)) (+ (car_blue_hor current) 2)) (<= (truck_yellow_hor (fixed current)) (+ (car_blue_hor next) 2)))
			(or (>= (+ (car_blue_ver (fixed current))(* (- 1) (truck_yellow_ver current))) 3)
				(> (truck_yellow_ver current) (car_blue_ver (fixed current)))))
	)
)

(define-fun carBlueStateInvariant ((st State)) Bool 
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed st)) (car_blue_hor st)) (< (truck_purple_hor (fixed st)) (+ (car_blue_hor st) 2)))
			(or (>= (+ (car_blue_ver (fixed st))(* (- 1) (truck_purple_ver st))) 3)
				(> (truck_purple_ver st) (car_blue_ver (fixed st)))))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed st)) (car_blue_hor st)) (< (car_orange_hor (fixed st)) (+ (car_blue_hor st) 2)))
			(or (>= (+ (car_blue_ver (fixed st))(* (- 1) (car_orange_ver st))) 2)
				(> (car_orange_ver st) (car_blue_ver (fixed st))))) 

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed st)) (car_blue_hor st)) (< (truck_blue_hor (fixed st)) (+ (car_blue_hor st) 2)))
			(or (>= (+ (car_blue_ver (fixed st))(* (- 1) (truck_blue_ver st))) 3)
				(> (truck_blue_ver st) (car_blue_ver (fixed st)))))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed st)) (car_blue_hor st)) (< (truck_yellow_hor (fixed st)) (+ (car_blue_hor st) 2)))
			(or (>= (+ (car_blue_ver (fixed st))(* (- 1) (truck_yellow_ver st))) 3)
				(> (truck_yellow_ver st) (car_blue_ver (fixed st)))))
	)
)

(define-fun truckGreenMoveLeft ((current State) (next State)) Bool
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed current))(truck_green_hor next)) (<= (truck_purple_hor (fixed current))(truck_green_hor current)))
			(or (>= (+ (truck_green_ver (fixed current))(* (- 1) (truck_purple_ver current))) 3)
				(> (truck_purple_ver current) (truck_green_ver (fixed current)))))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed current)) (truck_green_hor next)) (<= (car_orange_hor (fixed current)) (truck_green_hor current)))
			(or (>= (+ (truck_green_ver (fixed current))(* (- 1) (car_orange_ver current))) 2)
				(> (car_orange_ver current) (truck_green_ver (fixed current))))) 

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed current)) (truck_green_hor next)) (<= (truck_blue_hor (fixed current)) (truck_green_hor current)))
			(or (>= (+ (truck_green_ver (fixed current))(* (- 1) (truck_blue_ver current))) 3)
				(> (truck_blue_ver current) (truck_green_ver (fixed current)))))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed current)) (truck_green_hor next)) (<= (truck_yellow_hor (fixed current)) (truck_green_hor current)))
			(or (>= (+ (truck_green_ver (fixed current))(* (- 1) (truck_yellow_ver current))) 3)
				(> (truck_yellow_ver current) (truck_green_ver (fixed current)))))
	)
)

(define-fun truckGreenMoveRight ((current State) (next State)) Bool
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed current))(+ (truck_green_hor current) 3)) (<= (truck_purple_hor (fixed current))(+ (truck_green_hor next) 3)))
			(or (>= (+ (truck_green_ver (fixed current))(* (- 1) (truck_purple_ver current))) 3)
				(> (truck_purple_ver current) (truck_green_ver (fixed current)))))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed current)) (+ (truck_green_hor current) 3)) (<= (car_orange_hor (fixed current)) (+ (truck_green_hor next) 3)))
			(or (>= (+ (truck_green_ver (fixed current))(* (- 1) (car_orange_ver current))) 2)
				(> (car_orange_ver current) (truck_green_ver (fixed current))))) 

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed current)) (+ (truck_green_hor current) 3)) (<= (truck_blue_hor (fixed current)) (+ (truck_green_hor next) 3)))
			(or (>= (+ (truck_green_ver (fixed current))(* (- 1) (truck_blue_ver current))) 3)
				(> (truck_blue_ver current) (truck_green_ver (fixed current)))))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed current)) (+ (truck_green_hor current) 3)) (<= (truck_yellow_hor (fixed current)) (+ (truck_green_hor next) 3)))
			(or (>= (+ (truck_green_ver (fixed current))(* (- 1) (truck_yellow_ver current))) 3)
				(> (truck_yellow_ver current) (truck_green_ver (fixed current)))))
	)
)

(define-fun truckGreenStateInvariant ((st State)) Bool 
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed st)) (truck_green_hor st)) (< (truck_purple_hor (fixed st)) (+ (truck_green_hor st) 3)))
			(or (>= (+ (truck_green_ver (fixed st))(* (- 1) (truck_purple_ver st))) 3)
				(> (truck_purple_ver st) (truck_green_ver (fixed st)))))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed st)) (truck_green_hor st)) (< (car_orange_hor (fixed st)) (+ (truck_green_hor st) 3)))
			(or (>= (+ (truck_green_ver (fixed st))(* (- 1) (car_orange_ver st))) 2)
				(> (car_orange_ver st) (truck_green_ver (fixed st))))) 

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed st)) (truck_green_hor st)) (< (truck_blue_hor (fixed st)) (+ (truck_green_hor st) 3)))
			(or (>= (+ (truck_green_ver (fixed st))(* (- 1) (truck_blue_ver st))) 3)
				(> (truck_blue_ver st) (truck_green_ver (fixed st)))))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed st)) (truck_green_hor st)) (< (truck_yellow_hor (fixed st)) (+ (truck_green_hor st) 3)))
			(or (>= (+ (truck_green_ver (fixed st))(* (- 1) (truck_yellow_ver st))) 3)
				(> (truck_yellow_ver st) (truck_green_ver (fixed st)))))
	)
)

(define-fun carOrangeMoveUp ((current State) (next State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed current)) (car_orange_ver next)) (< (truck_green_ver (fixed current)) (car_orange_ver current)))
			(or (>= (+ (car_orange_hor (fixed current)) (* (- 1) (truck_green_hor current))) 3)
				(> (truck_green_hor current) (car_orange_hor (fixed current)))))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed current)) (car_orange_ver next)) (< (car_blue_ver (fixed current)) (car_orange_ver current)))
			(or (>= (+ (car_orange_hor (fixed current)) (* (- 1) (car_blue_hor current))) 2)
				(> (car_blue_hor current) (car_orange_hor (fixed current)))))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed current))(car_orange_ver next)) (< (car_red_ver (fixed current))(car_orange_ver current)))
			(or (>= (+ (car_orange_hor (fixed current)) (* (- 1) (car_red_hor current))) 2)
				(> (car_red_hor current) (car_orange_hor (fixed current)))))

		; check the green car
		(=> (and (>= (car_green_ver (fixed current)) (car_orange_ver next)) (< (car_green_ver (fixed current)) (car_orange_ver current)))
			(or (>= (+ (car_orange_hor (fixed current)) (* (- 1) (car_green_hor current))) 2)
				(> (car_green_hor current) (car_orange_hor (fixed current)))))

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (car_orange_ver next) (* (- 1) (truck_purple_ver current))) 3)
			(> (truck_purple_ver current) (car_orange_ver current)))

	)
)

(define-fun carOrangeMoveDown ((current State) (next State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed current)) (+ (car_orange_ver current) 2)) (< (truck_green_ver (fixed current)) (+ (car_orange_ver next) 2)))
			(or (>= (+ (car_orange_hor (fixed current)) (* (- 1) (truck_green_hor current))) 3)
				(> (truck_green_hor current) (car_orange_hor (fixed current)))))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed current)) (+ (car_orange_ver current) 2)) (< (car_blue_ver (fixed current)) (+ (car_orange_ver next) 2)))
			(or (>= (+ (car_orange_hor (fixed current)) (* (- 1) (car_blue_hor current))) 2)
				(> (car_blue_hor current) (car_orange_hor (fixed current)))))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed current))(+ (car_orange_ver current) 2)) (< (car_red_ver (fixed current))(+ (car_orange_ver next) 2)))
			(or (>= (+ (car_orange_hor (fixed current)) (* (- 1) (car_red_hor current))) 2)
				(> (car_red_hor current) (car_orange_hor (fixed current)))))

		; check the green car
		(=> (and (>= (car_green_ver (fixed current)) (+ (car_orange_ver current) 2)) (< (car_green_ver (fixed current)) (+ (car_orange_ver next) 2)))
			(or (>= (+ (car_orange_hor (fixed current)) (* (- 1) (car_green_hor current))) 2)
				(> (car_green_hor current) (car_orange_hor (fixed current)))))

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (+ (car_orange_ver next) 2) (* (- 1) (truck_purple_ver current))) 3)
			(>= (truck_purple_ver current) (+ (car_orange_ver current) 2)))
	)
)

(define-fun carOrangeStateInvariant ((st State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed st)) (car_orange_ver st)) (< (truck_green_ver (fixed st)) (+ (car_orange_ver st) 2)))
			(or (>= (+ (car_orange_hor (fixed st)) (* (- 1) (truck_green_hor st))) 3)
				(> (truck_green_hor st) (car_orange_hor (fixed st)))))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed st)) (car_orange_ver st)) (< (car_blue_ver (fixed st)) (+ (car_orange_ver st) 2)))
			(or (>= (+ (car_orange_hor (fixed st)) (* (- 1) (car_blue_hor st))) 2)
				(> (car_blue_hor st) (car_orange_hor (fixed st)))))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed st))(car_orange_ver st)) (< (car_red_ver (fixed st))(+ (car_orange_ver st) 2)))
			(or (>= (+ (car_orange_hor (fixed st)) (* (- 1) (car_red_hor st))) 2)
				(> (car_red_hor st) (car_orange_hor (fixed st)))))

		; check the green car
		(=> (and (>= (car_green_ver (fixed st)) (car_orange_ver st)) (< (car_green_ver (fixed st)) (+ (car_orange_ver st) 2)))
			(or (>= (+ (car_orange_hor (fixed st)) (* (- 1) (car_green_hor st))) 2)
				(> (car_green_hor st) (car_orange_hor (fixed st)))))

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (car_orange_ver st) (* (- 1) (truck_purple_ver st))) 3)
			(> (truck_purple_ver st) (+ (car_orange_ver st) 2)))
	)
)

(define-fun truckPurpleMoveUp ((current State) (next State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed current)) (truck_purple_ver next)) (< (truck_green_ver (fixed current)) (truck_purple_ver current)))
			(or (>= (+ (truck_purple_hor (fixed current))(* (- 1) (truck_green_hor current))) 3)
				(> (truck_green_hor current) (truck_purple_hor (fixed current)))))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed current)) (truck_purple_ver next)) (< (car_blue_ver (fixed current)) (truck_purple_ver current)))
			(or (>= (+ (truck_purple_hor (fixed current))(* (- 1) (car_blue_hor current))) 2)
				(> (car_blue_hor current) (truck_purple_hor (fixed current)))))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed current))(truck_purple_ver next)) (< (car_red_ver (fixed current))(truck_purple_ver current)))
			(or (>= (+ (truck_purple_hor (fixed current))(* (- 1) (car_red_hor current))) 2)
				(> (car_red_hor current) (truck_purple_hor (fixed current)))))

		; check the green car
		(=> (and (>= (car_green_ver (fixed current)) (truck_purple_ver next)) (< (car_green_ver (fixed current)) (truck_purple_ver current)))
			(or (>= (+ (truck_purple_hor (fixed current))(* (- 1) (car_green_hor current))) 2)
				(> (car_green_hor current) (truck_purple_hor (fixed current)))))

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (truck_purple_ver next) (* (- 1) (car_orange_ver current))) 2)
			(> (car_orange_ver current) (truck_purple_ver current)))

	)
)

(define-fun truckPurpleMoveDown ((current State) (next State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed current)) (+ (truck_purple_ver current) 3)) (< (truck_green_ver (fixed current)) (+ (truck_purple_ver next) 3)))
			(or (>= (+ (truck_purple_hor (fixed current))(* (- 1) (truck_green_hor current))) 3)
				(> (truck_green_hor current) (truck_purple_hor (fixed current)))))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed current)) (+ (truck_purple_ver current) 3)) (< (car_blue_ver (fixed current)) (+ (truck_purple_ver next) 3)))
			(or (>= (+ (truck_purple_hor (fixed current))(* (- 1) (car_blue_hor current))) 2)
				(> (car_blue_hor current) (truck_purple_hor (fixed current)))))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed current))(+ (truck_purple_ver current) 3)) (< (car_red_ver (fixed current))(+ (truck_purple_ver next) 3)))
			(or (>= (+ (truck_purple_hor (fixed current))(* (- 1) (car_red_hor current))) 2)
				(> (car_red_hor current) (truck_purple_hor (fixed current)))))

		; check the green car
		(=> (and (>= (car_green_ver (fixed current)) (+ (truck_purple_ver current) 3)) (< (car_green_ver (fixed current)) (+ (truck_purple_ver next) 3)))
			(or (>= (+ (truck_purple_hor (fixed current))(* (- 1) (car_green_hor current))) 2)
				(> (car_green_hor current) (truck_purple_hor (fixed current)))))

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (+ (truck_purple_ver current) 3) (* (- 1) (car_orange_ver current))) 2)
			(>= (car_orange_ver current) (+ (truck_purple_ver next) 3)))
	)
)

(define-fun truckPurpleStateInvariant ((st State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed st)) (truck_purple_ver st)) (< (truck_green_ver (fixed st)) (+ (truck_purple_ver st) 3)))
			(or (>= (+ (truck_purple_hor (fixed st))(* (- 1) (truck_green_hor st))) 3)
				(> (truck_green_hor st) (truck_purple_hor (fixed st)))))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed st)) (truck_purple_ver st)) (< (car_blue_ver (fixed st)) (+ (truck_purple_ver st) 3)))
			(or (>= (+ (truck_purple_hor (fixed st))(* (- 1) (car_blue_hor st))) 2)
				(> (car_blue_hor st) (truck_purple_hor (fixed st)))))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed st))(truck_purple_ver st)) (< (car_red_ver (fixed st))(+ (truck_purple_ver st) 3)))
			(or (>= (+ (truck_purple_hor (fixed st))(* (- 1) (car_red_hor st))) 2)
				(> (car_red_hor st) (truck_purple_hor (fixed st)))))

		; check the green car
		(=> (and (>= (car_green_ver (fixed st)) (truck_purple_ver st)) (< (car_green_ver (fixed st)) (+ (truck_purple_ver st) 3)))
			(or (>= (+ (truck_purple_hor (fixed st))(* (- 1) (car_green_hor st))) 2)
				(> (car_green_hor st) (truck_purple_hor (fixed st)))))

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (truck_purple_ver st) (* (- 1) (car_orange_ver st))) 2)
			(>= (car_orange_ver st) (+ (truck_purple_ver st) 3)))
	)
)

(define-fun truckBlueMoveUp ((current State) (next State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed current)) (truck_blue_ver next)) (< (truck_green_ver (fixed current)) (truck_blue_ver current)))
			(or (>= (+ (truck_blue_hor (fixed current)) (* (- 1) (truck_green_hor current))) 3)
				(> (truck_green_hor current) (truck_blue_hor (fixed current)))))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed current)) (truck_blue_ver next)) (< (car_blue_ver (fixed current)) (truck_blue_ver current)))
			(or (>= (+ (truck_blue_hor (fixed current)) (* (- 1) (car_blue_hor current))) 2)
				(> (car_blue_hor current) (truck_blue_hor (fixed current)))))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed current)) (truck_blue_ver next)) (< (car_red_ver (fixed current))(truck_blue_ver current)))
			(or (>= (+ (truck_blue_hor (fixed current)) (* (- 1) (car_red_hor current))) 2)
				(> (car_red_hor current) (truck_blue_hor (fixed current)))))

		; check the green car
		(=> (and (>= (car_green_ver (fixed current)) (truck_blue_ver next)) (< (car_green_ver (fixed current)) (truck_blue_ver current)))
			(or (>= (+ (truck_blue_hor (fixed current)) (* (- 1) (car_green_hor current))) 2)
				(> (car_green_hor current) (truck_blue_hor (fixed current)))))
	)
)

(define-fun truckBlueMoveDown ((current State) (next State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed current)) (+ (truck_blue_ver current) 3)) (< (truck_green_ver (fixed current)) (+ (truck_blue_ver next) 3)))
			(or (>= (+ (truck_blue_hor (fixed current)) (* (- 1) (truck_green_hor current))) 3)
				(> (truck_green_hor current) (truck_blue_hor (fixed current)))))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed current)) (+ (truck_blue_ver current) 3)) (< (car_blue_ver (fixed current)) (+ (truck_blue_ver next) 3)))
			(or (>= (+ (truck_blue_hor (fixed current)) (* (- 1) (car_blue_hor current))) 2)
				(> (car_blue_hor current) (truck_blue_hor (fixed current)))))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed current))(+ (truck_blue_ver current) 3)) (< (car_red_ver (fixed current))(+ (truck_blue_ver next) 3)))
			(or (>= (+ (truck_blue_hor (fixed current)) (* (- 1) (car_red_hor current))) 2)
				(> (car_red_hor current) (truck_blue_hor (fixed current)))))

		; check the green car
		(=> (and (>= (car_green_ver (fixed current)) (+ (truck_blue_ver current) 3)) (< (car_green_ver (fixed current)) (+ (truck_blue_ver next) 3)))
			(or (>= (+ (truck_blue_hor (fixed current)) (* (- 1) (car_green_hor current))) 2)
				(> (car_green_hor current) (truck_blue_hor (fixed current)))))
	)
)

(define-fun truckBlueStateInvariant ((st State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed st)) (truck_blue_ver st)) (< (truck_green_ver (fixed st)) (+ (truck_blue_ver st) 3)))
			(or (>= (+ (truck_blue_hor (fixed st)) (* (- 1) (truck_green_hor st))) 3)
				(> (truck_green_hor st) (truck_blue_hor (fixed st)))))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed st)) (truck_blue_ver st)) (< (car_blue_ver (fixed st)) (+ (truck_blue_ver st) 3)))
			(or (>= (+ (truck_blue_hor (fixed st)) (* (- 1) (car_blue_hor st))) 2)
				(> (car_blue_hor st) (truck_blue_hor (fixed st)))))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed st)) (truck_blue_ver st)) (< (car_red_ver (fixed st)) (+ (truck_blue_ver st) 3)))
			(or (>= (+ (truck_blue_hor (fixed st)) (* (- 1) (car_red_hor st))) 2)
				(> (car_red_hor st) (truck_blue_hor (fixed st)))))

		; check the green car
		(=> (and (>= (car_green_ver (fixed st)) (truck_blue_ver st)) (< (car_green_ver (fixed st)) (+ (truck_blue_ver st) 3)))
			(or (>= (+ (truck_blue_hor (fixed st)) (* (- 1) (car_green_hor st))) 2)
				(> (car_green_hor st) (truck_blue_hor (fixed st)))))
	)
)

(define-fun truckYellowMoveUp ((current State) (next State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed current)) (truck_yellow_ver next)) (< (truck_green_ver (fixed current)) (truck_yellow_ver current)))
			(or (>= (+ (truck_yellow_hor (fixed current)) (* (- 1) (truck_green_hor current))) 3)
				(> (truck_green_hor current) (truck_yellow_hor (fixed current)))))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed current)) (truck_yellow_ver next)) (< (car_blue_ver (fixed current)) (truck_yellow_ver current)))
			(or (>= (+ (truck_yellow_hor (fixed current)) (* (- 1) (car_blue_hor current))) 2)
				(> (car_blue_hor current) (truck_yellow_hor (fixed current)))))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed current))(truck_yellow_ver next)) (< (car_red_ver (fixed current))(truck_yellow_ver current)))
			(or (>= (+ (truck_yellow_hor (fixed current)) (* (- 1) (car_red_hor current))) 2)
				(> (car_red_hor current) (truck_yellow_hor (fixed current)))))

		; check the green car
		(=> (and (>= (car_green_ver (fixed current)) (truck_yellow_ver next)) (< (car_green_ver (fixed current)) (truck_yellow_ver current)))
			(or (>= (+ (truck_yellow_hor (fixed current)) (* (- 1) (car_green_hor current))) 2)
				(> (car_green_hor current) (truck_yellow_hor (fixed current)))))
	)
)

(define-fun truckYellowMoveDown ((current State) (next State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed current)) (+ (truck_yellow_ver current) 3)) (< (truck_green_ver (fixed current)) (+ (truck_yellow_ver next) 3)))
			(or (>= (+ (truck_yellow_hor (fixed current)) (* (- 1) (truck_green_hor current))) 3)
				(> (truck_green_hor current) (truck_yellow_hor (fixed current)))))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed current)) (+ (truck_yellow_ver current) 3)) (< (car_blue_ver (fixed current)) (+ (truck_yellow_ver next) 3)))
			(or (>= (+ (truck_yellow_hor (fixed current)) (* (- 1) (car_blue_hor current))) 2)
				(> (car_blue_hor current) (truck_yellow_hor (fixed current)))))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed current))(+ (truck_yellow_ver current) 3)) (< (car_red_ver (fixed current))(+ (truck_yellow_ver next) 3)))
			(or (>= (+ (truck_yellow_hor (fixed current)) (* (- 1) (car_red_hor current))) 2)
				(> (car_red_hor current) (truck_yellow_hor (fixed current)))))

		; check the green car
		(=> (and (>= (car_green_ver (fixed current)) (+ (truck_yellow_ver current) 3)) (< (car_green_ver (fixed current)) (+ (truck_yellow_ver next) 3)))
			(or (>= (+ (truck_yellow_hor (fixed current)) (* (- 1) (car_green_hor current))) 2)
				(> (car_green_hor current) (truck_yellow_hor (fixed current)))))
	)
)

(define-fun truckYellowStateInvariant ((st State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed st)) (truck_yellow_ver st)) (< (truck_green_ver (fixed st)) (+ (truck_yellow_ver st) 3)))
			(or (>= (+ (truck_yellow_hor (fixed st)) (* (- 1) (truck_green_hor st))) 3)
				(> (truck_green_hor st) (truck_yellow_hor (fixed st)))))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed st)) (truck_yellow_ver st)) (< (car_blue_ver (fixed st)) (+ (truck_yellow_ver st) 3)))
			(or (>= (+ (truck_yellow_hor (fixed st)) (* (- 1) (car_blue_hor st))) 2)
				(> (car_blue_hor st) (truck_yellow_hor (fixed st)))))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed st))(truck_yellow_ver st)) (< (car_red_ver (fixed st))(+ (truck_yellow_ver st) 3)))
			(or (>= (+ (truck_yellow_hor (fixed st)) (* (- 1) (car_red_hor st))) 2)
				(> (car_red_hor st) (truck_yellow_hor (fixed st)))))

		; check the green car
		(=> (and (>= (car_green_ver (fixed st)) (truck_yellow_ver st)) (< (car_green_ver (fixed st)) (+ (truck_yellow_ver st) 3)))
			(or (>= (+ (truck_yellow_hor (fixed st)) (* (- 1) (car_green_hor st))) 2)
				(> (car_green_hor st) (truck_yellow_hor (fixed st)))))
	)
)
   
(define-fun move ((current State) (next State)) Bool
	(and
		(not (= current next))
		
		(fixedPos current)
		(fixedPos next)
		
		(stayInLane (car_red_hor next) 2)
		(stayInLane (car_green_hor next) 2)
		(stayInLane (car_blue_hor next) 2)
		(stayInLane (truck_green_hor next) 3)
		(stayInLane (car_orange_ver next) 2)
		(stayInLane (truck_purple_ver next) 3) 	
		(stayInLane (truck_blue_ver next) 3)
		(stayInLane (truck_yellow_ver next) 3)

		;(= (car_red_hor next) (car_red_hor current))
		;(= (car_green_hor next) (car_green_hor current))
		;(= (car_blue_hor next) (car_blue_hor current))
		;(= (truck_green_hor next) (truck_green_hor current)) 

		(=> (< (car_red_hor next) (car_red_hor current)) (carRedMoveLeft current next))
		(=> (> (car_red_hor next) (car_red_hor current)) (carRedMoveRight current next))
		(carRedStateInvariant next)

		(=> (< (car_green_hor next) (car_green_hor current)) (carGreenMoveLeft current next))
		(=> (> (car_green_hor next) (car_green_hor current)) (carGreenMoveRight current next))
		(carGreenStateInvariant next)

		(=> (< (car_blue_hor next) (car_blue_hor current)) (carBlueMoveLeft current next))
		(=> (> (car_blue_hor next) (car_blue_hor current)) (carBlueMoveRight current next))
		(carBlueStateInvariant next)
		
		(=> (< (truck_green_hor next) (truck_green_hor current)) (truckGreenMoveLeft current next))
		(=> (> (truck_green_hor next) (truck_green_hor current)) (truckGreenMoveRight current next))
		(truckGreenStateInvariant next)
		
		(=> (< (car_orange_ver next) (car_orange_ver current)) (carOrangeMoveUp current next))
		(=> (> (car_orange_ver next) (car_orange_ver current)) (carOrangeMoveDown current next))
		(carOrangeStateInvariant next)
		
		(=> (< (truck_purple_ver next) (truck_purple_ver current)) (truckPurpleMoveUp current next))
		(=> (> (truck_purple_ver next) (truck_purple_ver current)) (truckPurpleMoveDown current next))
		(truckPurpleStateInvariant next)

		(=> (< (truck_blue_ver next) (truck_blue_ver current)) (truckBlueMoveUp current next))
		(=> (> (truck_blue_ver next) (truck_blue_ver current)) (truckBlueMoveDown current next))
		(truckBlueStateInvariant next)
		
		(=> (< (truck_yellow_ver next) (truck_yellow_ver current)) (truckYellowMoveUp current next))
		(=> (> (truck_yellow_ver next) (truck_yellow_ver current)) (truckYellowMoveDown current next))
		(truckYellowStateInvariant next)
	)
)

(define-fun canExit ((st State)) Bool 
	(>= (car_red_hor st) 4)
)

;(push 1)
;
;(assert 
;	(exists ((s1 State) (s2 State)) 
;		(and 
;			(not (canExit s1))
;			(move s1 s2)
;			(canExit s2)
;		)
;	)
;)
;
;(check-sat)
;(get-model)
;
;(pop 1)

;(declare-fun reach (State) Bool)
;
;(assert (forall ((s State)) (=> (initial s) (reach s))))
;
;(assert (forall ((s1 State) (s2 State)) (=> (and (reach s1) (move s1 s2)) (reach s2))))
;
;(assert (forall ((s State)) (=> (reach s) (not (canExit s)))))
;
;(check-sat)

(push 1)

(declare-const s0 State)
(declare-const s1 State)
(declare-const s2 State)
(declare-const s3 State)
(declare-const s4 State)
(declare-const s5 State)
(declare-const s6 State)

(assert (initial s0))
(assert (move s0 s1))
(assert (move s1 s2))
(assert (move s2 s3))
(assert (move s3 s4))
(assert (move s4 s5))
(assert (move s5 s6))

(assert (canExit s6))

(check-sat)
(get-value (s0 s1 s2 s3 s4 s5 s6))
(echo "Move 1")
(echo "Red car hor:")(eval (- (car_red_hor s1) (car_red_hor s0)))
(echo "Green car hor:")(eval (- (car_green_hor s1) (car_green_hor s0)))
(echo "Blue car hor:")(eval (- (car_blue_hor s1) (car_blue_hor s0)))
(echo "Green truck hor:")(eval (- (truck_green_hor s1) (truck_green_hor s0)))
(echo "Orange car ver:")(eval (- (car_orange_ver s1) (car_orange_ver s0)))
(echo "Purple truck ver:")(eval (- (truck_purple_ver s1) (truck_purple_ver s0)))
(echo "Blue truck ver:")(eval (- (truck_blue_ver s1) (truck_blue_ver s0)))
(echo "Yellow truck ver:")(eval (- (truck_yellow_ver s1) (truck_yellow_ver s0)))

(echo "Move 2")
(echo "Red car hor:")(eval (- (car_red_hor s2) (car_red_hor s1)))
(echo "Green car hor:")(eval (- (car_green_hor s2) (car_green_hor s1)))
(echo "Blue car hor:")(eval (- (car_blue_hor s2) (car_blue_hor s1)))
(echo "Green truck hor:")(eval (- (truck_green_hor s2) (truck_green_hor s1)))
(echo "Orange car ver:")(eval (- (car_orange_ver s2) (car_orange_ver s1)))
(echo "Purple truck ver:")(eval (- (truck_purple_ver s2) (truck_purple_ver s1)))
(echo "Blue truck ver:")(eval (- (truck_blue_ver s2) (truck_blue_ver s1)))
(echo "Yellow truck ver:")(eval (- (truck_yellow_ver s2) (truck_yellow_ver s1)))

(echo "Move 3")
(echo "Red car hor:")(eval (- (car_red_hor s3) (car_red_hor s2)))
(echo "Green car hor:")(eval (- (car_green_hor s3) (car_green_hor s2)))
(echo "Blue car hor:")(eval (- (car_blue_hor s3) (car_blue_hor s2)))
(echo "Green truck hor:")(eval (- (truck_green_hor s3) (truck_green_hor s2)))
(echo "Orange car ver:")(eval (- (car_orange_ver s3) (car_orange_ver s2)))
(echo "Purple truck ver:")(eval (- (truck_purple_ver s3) (truck_purple_ver s2)))
(echo "Blue truck ver:")(eval (- (truck_blue_ver s3) (truck_blue_ver s2)))
(echo "Yellow truck ver:")(eval (- (truck_yellow_ver s3) (truck_yellow_ver s2)))

(echo "Move 4")
(echo "Red car hor:")(eval (- (car_red_hor s4) (car_red_hor s3)))
(echo "Green car hor:")(eval (- (car_green_hor s4) (car_green_hor s3)))
(echo "Blue car hor:")(eval (- (car_blue_hor s4) (car_blue_hor s3)))
(echo "Green truck hor:")(eval (- (truck_green_hor s4) (truck_green_hor s3)))
(echo "Orange car ver:")(eval (- (car_orange_ver s4) (car_orange_ver s3)))
(echo "Purple truck ver:")(eval (- (truck_purple_ver s4) (truck_purple_ver s3)))
(echo "Blue truck ver:")(eval (- (truck_blue_ver s4) (truck_blue_ver s3)))
(echo "Yellow truck ver:")(eval (- (truck_yellow_ver s4) (truck_yellow_ver s3)))

(echo "Move 5")
(echo "Red car hor:")(eval (- (car_red_hor s5) (car_red_hor s4)))
(echo "Green car hor:")(eval (- (car_green_hor s5) (car_green_hor s4)))
(echo "Blue car hor:")(eval (- (car_blue_hor s5) (car_blue_hor s4)))
(echo "Green truck hor:")(eval (- (truck_green_hor s5) (truck_green_hor s4)))
(echo "Orange car ver:")(eval (- (car_orange_ver s5) (car_orange_ver s4)))
(echo "Purple truck ver:")(eval (- (truck_purple_ver s5) (truck_purple_ver s4)))
(echo "Blue truck ver:")(eval (- (truck_blue_ver s5) (truck_blue_ver s4)))
(echo "Yellow truck ver:")(eval (- (truck_yellow_ver s5) (truck_yellow_ver s4)))

(echo "Move 6")
(echo "Red car hor:")(eval (- (car_red_hor s6) (car_red_hor s5)))
(echo "Green car hor:")(eval (- (car_green_hor s6) (car_green_hor s5)))
(echo "Blue car hor:")(eval (- (car_blue_hor s6) (car_blue_hor s5)))
(echo "Green truck hor:")(eval (- (truck_green_hor s6) (truck_green_hor s5)))
(echo "Orange car ver:")(eval (- (car_orange_ver s6) (car_orange_ver s5)))
(echo "Purple truck ver:")(eval (- (truck_purple_ver s6) (truck_purple_ver s5)))
(echo "Blue truck ver:")(eval (- (truck_blue_ver s6) (truck_blue_ver s5)))
(echo "Yellow truck ver:")(eval (- (truck_yellow_ver s6) (truck_yellow_ver s5)))

(pop 1)


