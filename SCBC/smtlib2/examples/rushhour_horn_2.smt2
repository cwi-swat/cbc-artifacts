(set-logic HORN)

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

(define-fun vehicleMovedLeftOf ((hPosCurVehOfInterest Int) (hPosNextVehOfInterest Int) (hPosOtherVehicle Int)) Bool 
	(and 
		(< hPosOtherVehicle hPosCurVehOfInterest) 	; the vehicle of interest was on the right side of the other vehicle
		(>= hPosOtherVehicle hPosNextVehOfInterest) ; the vehicle of interest moved to the left side of the other vehicle 
	)
)

(define-fun vehicleMovedRightOf ((hPosCurVehOfInterest Int) (hPosNextVehOfInterest Int) (hPosOtherVehicle Int) (length Int)) Bool 
	(and 
		(>= hPosOtherVehicle (+ hPosCurVehOfInterest length)) 	; the vehicle of interest was on the left side of the other vehicle 
		(< hPosOtherVehicle (+ hPosNextVehOfInterest length)) 	; the vehicle of interest moved to the right side of the other vehicle
	)
)

(define-fun vehicleMovedAboveOf ((vPosCurVehOfInterest Int) (vPosNextVehOfInterest Int) (vPosOtherVehicle Int)) Bool
	(and 
		(< vPosOtherVehicle vPosCurVehOfInterest) 	; the vehicle of interest was below the other vehicle 
		(>= vPosOtherVehicle vPosNextVehOfInterest) ; the vehicle of interest moved above the other vehicle
	) 
)

(define-fun vehicleMovedBelowOf ((vPosCurVehOfInterest Int) (vPosNextVehOfInterest Int) (vPosOtherVehicle Int) (length Int)) Bool
	(and 
		(>= vPosOtherVehicle (+ vPosCurVehOfInterest length)) ; the vehicle of interest was above the other vehicle
		(< vPosOtherVehicle (+ vPosNextVehOfInterest length)) ; the vehicle of interest moved below the other vehicle
	)
) 

(define-fun noOverlap ((posVehOfInterest Int) (posOtherVehicle Int) (lengthOtherVehicle Int)) Bool
	(or (>= (+ posVehOfInterest (* (- 1) posOtherVehicle)) lengthOtherVehicle) 	; the other vehicle is above the vehicle of interest 
		(> posOtherVehicle posVehOfInterest)) 									; the other vehicle is below the vehicle of interest
)

(define-fun moveLeft ((hPosCur Int) (hPosNext Int) (vPos Int) (length Int) (current State) (next State)) Bool
	(and
		; If the vehicle moved left of the purple truck, then the purple truck should be above or below of the vehicle
		(=> (vehicleMovedLeftOf hPosCur hPosNext (truck_purple_hor (fixed current))) (noOverlap vPos (truck_purple_ver current) 3))

		; If the vehicle moved left of the orange car, then the orange car should be above or below of the vehicle
		(=> (vehicleMovedLeftOf hPosCur hPosNext (car_orange_hor (fixed current))) (noOverlap vPos (car_orange_ver current) 2))

		; If the vehicle moved left of the blue truck, then the blue truck should be above or below of the vehicle
		(=> (vehicleMovedLeftOf hPosCur hPosNext (truck_blue_hor (fixed current))) (noOverlap vPos (truck_blue_ver current) 3))

		; If the vehicle moved left of the yellow truck, then the yellow truck should be above or below of the vehicle
		(=> (vehicleMovedLeftOf hPosCur hPosNext (truck_yellow_hor (fixed current))) (noOverlap vPos (truck_yellow_ver current) 3))
	)
)

(define-fun moveRight ((hPosCur Int) (hPosNext Int) (vPos Int) (length Int) (current State) (next State)) Bool
	(and
		; If the vehicle moved right of the purple truck, then the purple truck should be above or below of the vehicle
		(=> (vehicleMovedRightOf hPosCur hPosNext (truck_purple_hor (fixed current)) length) (noOverlap vPos (truck_purple_ver current) 3))

		; If the vehicle moved right of the orange car, then the orange car should be above or below of the vehicle
		(=> (vehicleMovedRightOf hPosCur hPosNext (car_orange_hor (fixed current)) length) (noOverlap vPos (car_orange_ver current) 2))

		; If the vehicle moved right of the blue truck, then the blue truck should be above or below of the vehicle
		(=> (vehicleMovedRightOf hPosCur hPosNext (truck_blue_hor (fixed current)) length) (noOverlap vPos (truck_blue_ver current) 3))
 
 		; If the vehicle moved right of the yellow truck, then the yellow truck should be above or below of the vehicle
		(=> (vehicleMovedRightOf hPosCur hPosNext (truck_yellow_hor (fixed current)) length) (noOverlap vPos (truck_yellow_ver current) 3))
	)
)

(define-fun horizontalStateInvariant ((hPos Int) (vPos Int) (length Int) (st State)) Bool 
	(and
		; check the purple truck
		(=> (and (>= (truck_purple_hor (fixed st)) hPos) (< (truck_purple_hor (fixed st)) (+ hPos length)))
			(noOverlap vPos (truck_purple_ver st) 3))

		; check the orange car
		(=> (and (>= (car_orange_hor (fixed st)) hPos) (< (car_orange_hor (fixed st)) (+ hPos length)))
			(noOverlap vPos (car_orange_ver st) 2))

		; check the blue truck
		(=> (and (>= (truck_blue_hor (fixed st)) hPos) (< (truck_blue_hor (fixed st)) (+ hPos length)))
			(noOverlap vPos (truck_blue_ver st) 3))

		; check the yellow truck
		(=> (and (>= (truck_yellow_hor (fixed st)) hPos) (< (truck_yellow_hor (fixed st)) (+ hPos length)))
			(noOverlap vPos (truck_yellow_ver st) 3))
	)
)

(define-fun moveUp ((vPosCur Int) (vPosNext Int) (hPos Int) (length Int) (current State) (next State)) Bool
	(and
		; If the vehicle moved above of the green truck, then the green truck should be to the right or left of the vehicle
		(=> (vehicleMovedAboveOf vPosCur vPosNext (truck_green_ver (fixed current))) (noOverlap hPos (truck_green_hor current) 3))

		; If the vehicle moved above of the blue car, then the blue car should be to the right or left of the vehicle
		(=> (vehicleMovedAboveOf vPosCur vPosNext (car_blue_ver (fixed current))) (noOverlap hPos (car_blue_hor current) 2))
				
		; If the vehicle moved above of the red car, then the red car should be to the right or left of the vehicle
		(=> (vehicleMovedAboveOf vPosCur vPosNext (car_red_ver (fixed current))) (noOverlap hPos (car_red_hor current) 2))

		; If the vehicle moved above of the green car, then the green car should be to the right or left of the vehicle
		(=> (vehicleMovedAboveOf vPosCur vPosNext (car_green_ver (fixed current))) (noOverlap hPos (car_green_hor current) 2))
	)
)

(define-fun moveDown ((vPosCur Int) (vPosNext Int) (hPos Int) (length Int) (current State) (next State)) Bool
	(and
		; If the vehicle moved below of the green truck, then the green truck should be to the right or left of the vehicle
		(=> (vehicleMovedBelowOf vPosCur vPosNext (truck_green_ver (fixed current)) length) (noOverlap hPos (truck_green_hor current) 3))

		; If the vehicle moved below of the blue car, then the blue car should be to the right or left of the vehicle
		(=> (vehicleMovedBelowOf vPosCur vPosNext (car_blue_ver (fixed current)) length) (noOverlap hPos (car_blue_hor current) 2))
				
		; If the vehicle moved below of the red car, then the red car should be to the right or left of the vehicle
		(=> (vehicleMovedBelowOf vPosCur vPosNext (car_red_ver (fixed current)) length) (noOverlap hPos (car_red_hor current) 2))

		; If the vehicle moved below of the green car, then the green car should be to the right or left of the vehicle
		(=> (vehicleMovedBelowOf vPosCur vPosNext (car_green_ver (fixed current)) length) (noOverlap hPos (car_green_hor current) 2))
	)
)

(define-fun verticalStateInvariant ((hPos Int) (vPos Int) (length Int) (st State)) Bool
	(and
		; check the green truck
		(=> (and (>= (truck_green_ver (fixed st)) vPos) (< (truck_green_ver (fixed st)) (+ vPos length)))
			(noOverlap hPos (truck_green_hor st) 3))

		; check the blue car
		(=> (and (>= (car_blue_ver (fixed st)) vPos) (< (car_blue_ver (fixed st)) (+ vPos length)))
			(noOverlap hPos (car_blue_hor st) 2))
				
		; check the red car
		(=> (and (>= (car_red_ver (fixed st)) vPos) (< (car_red_ver (fixed st))(+ vPos length)))
			(noOverlap hPos (car_red_hor st) 2))

		; check the green car
		(=> (and (>= (car_green_ver (fixed st)) vPos) (< (car_green_ver (fixed st)) (+ vPos length)))
			(noOverlap hPos (car_green_hor st) 2))
	)
)


(define-fun carRedMoveLeft ((current State) (next State)) Bool
	(moveLeft (car_red_hor current) (car_red_hor next) (car_red_ver (fixed current)) 2 current next)
)

(define-fun carRedMoveRight ((current State) (next State)) Bool
	(moveRight (car_red_hor current) (car_red_hor next) (car_red_ver (fixed current)) 2 current next)
)

(define-fun carRedStateInvariant ((st State)) Bool 
	(horizontalStateInvariant (car_red_hor st) (car_red_ver (fixed st)) 2 st)
)

(define-fun carGreenMoveLeft ((current State) (next State)) Bool
	(moveLeft (car_green_hor current) (car_green_hor next) (car_green_ver (fixed current)) 2 current next)
)

(define-fun carGreenMoveRight ((current State) (next State)) Bool
	(moveRight (car_green_hor current) (car_green_hor next) (car_green_ver (fixed current)) 2 current next)
)

(define-fun carGreenStateInvariant ((st State)) Bool 
	(horizontalStateInvariant (car_green_hor st) (car_green_ver (fixed st)) 2 st)
)

(define-fun carBlueMoveLeft ((current State) (next State)) Bool
	(moveLeft (car_blue_hor current) (car_blue_hor next) (car_blue_ver (fixed current)) 2 current next)
)

(define-fun carBlueMoveRight ((current State) (next State)) Bool
	(moveRight (car_blue_hor current) (car_blue_hor next) (car_blue_ver (fixed current)) 2 current next)
)

(define-fun carBlueStateInvariant ((st State)) Bool 
	(horizontalStateInvariant (car_blue_hor st) (car_blue_ver (fixed st)) 2 st)
)

(define-fun truckGreenMoveLeft ((current State) (next State)) Bool
	(moveLeft (truck_green_hor current) (truck_green_hor next) (truck_green_ver (fixed current)) 3 current next)
)

(define-fun truckGreenMoveRight ((current State) (next State)) Bool
	(moveRight (truck_green_hor current) (truck_green_hor next) (truck_green_ver (fixed current)) 3 current next)
)

(define-fun truckGreenStateInvariant ((st State)) Bool 
	(horizontalStateInvariant (truck_green_hor st) (truck_green_ver (fixed st)) 3 st)
)

(define-fun carOrangeMoveUp ((current State) (next State)) Bool
	(and
		(moveUp (car_orange_ver current) (car_orange_ver next) (car_orange_hor (fixed current)) 2 current next)

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (car_orange_ver next) (* (- 1) (truck_purple_ver current))) 3)
			(> (truck_purple_ver current) (car_orange_ver current)))
	)
)

(define-fun carOrangeMoveDown ((current State) (next State)) Bool
	(and
		(moveDown (car_orange_ver current) (car_orange_ver next) (car_orange_hor (fixed current)) 2 current next)

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (+ (car_orange_ver next) 2) (* (- 1) (truck_purple_ver current))) 3)
			(>= (truck_purple_ver current) (+ (car_orange_ver current) 2)))
	)
)

(define-fun carOrangeStateInvariant ((st State)) Bool
	(and
		(verticalStateInvariant (car_orange_hor (fixed st)) (car_orange_ver st) 2 st)
		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (car_orange_ver st) (* (- 1) (truck_purple_ver st))) 3)
			(>= (truck_purple_ver st) (+ (car_orange_ver st) 2)))
	)
)

(define-fun truckPurpleMoveUp ((current State) (next State)) Bool
	(and
		(moveUp (truck_purple_ver current) (truck_purple_ver next) (truck_purple_hor (fixed current)) 3 current next)

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (truck_purple_ver next) (* (- 1) (car_orange_ver current))) 2)
			(>= (car_orange_ver current) (truck_purple_ver current)))

	)
)

(define-fun truckPurpleMoveDown ((current State) (next State)) Bool
	(and
		(moveDown (truck_purple_ver current) (truck_purple_ver next) (truck_purple_hor (fixed current)) 3 current next)

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (+ (truck_purple_ver current) 3) (* (- 1) (car_orange_ver current))) 2)
			(>= (car_orange_ver current) (+ (truck_purple_ver next) 3)))
	)
)

(define-fun truckPurpleStateInvariant ((st State)) Bool
	(and
		(verticalStateInvariant (truck_purple_hor (fixed st)) (truck_purple_ver st) 2 st)

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (truck_purple_ver st) (* (- 1) (car_orange_ver st))) 2)
			(>= (car_orange_ver st) (+ (truck_purple_ver st) 3)))
	)
)

(define-fun truckBlueMoveUp ((current State) (next State)) Bool
	(moveUp (truck_blue_ver current) (truck_blue_ver next) (truck_blue_hor (fixed current)) 3 current next)
)

(define-fun truckBlueMoveDown ((current State) (next State)) Bool
	(moveDown (truck_blue_ver current) (truck_blue_ver next) (truck_blue_hor (fixed current)) 3 current next)
)

(define-fun truckBlueStateInvariant ((st State)) Bool
	(verticalStateInvariant (truck_blue_hor (fixed st)) (truck_blue_ver st) 3 st)
)

(define-fun truckYellowMoveUp ((current State) (next State)) Bool
	(moveUp (truck_yellow_ver current) (truck_yellow_ver next) (truck_yellow_hor (fixed current)) 3 current next)
)

(define-fun truckYellowMoveDown ((current State) (next State)) Bool
	(moveDown (truck_yellow_ver current) (truck_yellow_ver next) (truck_yellow_hor (fixed current)) 3 current next)
)

(define-fun truckYellowStateInvariant ((st State)) Bool
	(verticalStateInvariant (truck_yellow_hor (fixed st)) (truck_yellow_ver st) 3 st)
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

(declare-fun reach (State) Bool)

(assert (forall ((s State)) (=> (initial s) (reach s))))

(assert (forall ((s1 State) (s2 State)) (=> (and (reach s1) (move s1 s2)) (reach s2))))

(assert (forall ((s State)) (=> (reach s) (not (canExit s)))))

(check-sat)

;(push 1)
;
;(declare-const s0 State)
;(declare-const s1 State)
;(declare-const s2 State)
;(declare-const s3 State)
;(declare-const s4 State)
;(declare-const s5 State)
;(declare-const s6 State)
;
;(assert (initial s0))
;(assert (move s0 s1))
;(assert (move s1 s2))
;(assert (move s2 s3))
;(assert (move s3 s4))
;(assert (move s4 s5))
;(assert (move s5 s6))
;
;(assert (canExit s6))
;
;(check-sat)
;(get-value (s0 s1 s2 s3 s4 s5 s6))
;
;(pop 1)

