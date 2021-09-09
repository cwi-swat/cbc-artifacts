(set-logic HORN)

(declare-datatypes () ((Fixed (cons
	(car_red_ver Int)
	(car_lightgreen_ver Int)
	(truck_blue_ver Int)
	(car_black_ver Int)
	(car_brown_ver Int)
	(car_yellow_ver Int)
	(truck_yellow_hor Int)
	(car_blue_hor Int)
	(car_pink_hor Int)
	(car_darkgreen_hor Int)
	(car_purple_hor Int)
	(car_orange_hor Int)
	(truck_purple_hor Int)
))))

(declare-datatypes () ((State (cons 
	(fixed Fixed)
	(car_red_hor Int)
	(car_lightgreen_hor Int)
	(truck_blue_hor Int)
	(car_black_hor Int)
	(car_brown_hor Int)
	(car_yellow_hor Int)
	(truck_yellow_ver Int)
	(car_blue_ver Int)
	(car_pink_ver Int)
	(car_darkgreen_ver Int)
	(car_purple_ver Int)
	(car_orange_ver Int)
	(truck_purple_ver Int)
))))

(define-fun fixedPos ((st State)) Bool
	(and 
	(= (car_red_ver (fixed st)) 2)
	(= (car_lightgreen_ver (fixed st)) 0)
	(= (truck_blue_ver (fixed st)) 3)
	(= (car_black_ver (fixed st)) 4)
	(= (car_brown_ver (fixed st)) 5)
	(= (car_yellow_ver (fixed st)) 5)
	(= (truck_yellow_hor (fixed st)) 0)
	(= (car_blue_hor (fixed st)) 1)
	(= (car_pink_hor (fixed st)) 2)
	(= (car_darkgreen_hor (fixed st)) 2)
	(= (car_purple_hor (fixed st)) 3)
	(= (car_orange_hor (fixed st)) 4)
	(= (truck_purple_hor (fixed st)) 5)
	)
)

(define-fun initial ((st State)) Bool 
	(and
		(fixedPos st)
		(= (car_red_hor st) 3)
		(= (car_lightgreen_hor st) 1)
		(= (truck_blue_hor st) 0)
		(= (car_black_hor st) 4)
		(= (car_brown_hor st) 0)
		(= (car_yellow_hor st) 3)
		(= (truck_yellow_ver st) 0)
		(= (car_blue_ver st) 1)
		(= (car_pink_ver st) 1)
		(= (car_darkgreen_ver st) 4)
		(= (car_purple_ver st) 3)
		(= (car_orange_ver st) 0)
		(= (truck_purple_ver st) 1)
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
		(=> (vehicleMovedLeftOf hPosCur hPosNext (truck_yellow_hor (fixed current))) (noOverlap vPos (truck_yellow_ver current) 3))
		(=> (vehicleMovedLeftOf hPosCur hPosNext (car_blue_hor (fixed current))) (noOverlap vPos (car_blue_ver current) 2))
		(=> (vehicleMovedLeftOf hPosCur hPosNext (car_pink_hor (fixed current))) (noOverlap vPos (car_pink_ver current) 2))
		(=> (vehicleMovedLeftOf hPosCur hPosNext (car_darkgreen_hor (fixed current))) (noOverlap vPos (car_darkgreen_ver current) 2))
		(=> (vehicleMovedLeftOf hPosCur hPosNext (car_purple_hor (fixed current))) (noOverlap vPos (car_purple_ver current) 2))
		(=> (vehicleMovedLeftOf hPosCur hPosNext (car_orange_hor (fixed current))) (noOverlap vPos (car_orange_ver current) 2))
		(=> (vehicleMovedLeftOf hPosCur hPosNext (truck_purple_hor (fixed current))) (noOverlap vPos (truck_purple_ver current) 3))
	)
)

(define-fun moveRight ((hPosCur Int) (hPosNext Int) (vPos Int) (length Int) (current State) (next State)) Bool
	(and
		(=> (vehicleMovedRightOf hPosCur hPosNext (truck_yellow_hor (fixed current)) length) (noOverlap vPos (truck_yellow_ver current) 3))
		(=> (vehicleMovedRightOf hPosCur hPosNext (car_blue_hor (fixed current)) length) (noOverlap vPos (car_blue_ver current) 2))
		(=> (vehicleMovedRightOf hPosCur hPosNext (car_pink_hor (fixed current)) length) (noOverlap vPos (car_pink_ver current) 2))
		(=> (vehicleMovedRightOf hPosCur hPosNext (car_darkgreen_hor (fixed current)) length) (noOverlap vPos (car_darkgreen_ver current) 2))
		(=> (vehicleMovedRightOf hPosCur hPosNext (car_purple_hor (fixed current)) length) (noOverlap vPos (car_purple_ver current) 2))
		(=> (vehicleMovedRightOf hPosCur hPosNext (car_orange_hor (fixed current)) length) (noOverlap vPos (car_orange_ver current) 2))
		(=> (vehicleMovedRightOf hPosCur hPosNext (truck_purple_hor (fixed current)) length) (noOverlap vPos (truck_purple_ver current) 3))
	)
)

(define-fun horizontalStateInvariant ((hPos Int) (vPos Int) (length Int) (st State)) Bool 
	(and
		(=> (and (>= (truck_yellow_hor (fixed st)) hPos) (< (truck_yellow_hor (fixed st)) (+ hPos length))) (noOverlap vPos (truck_yellow_ver st) 3))
		(=> (and (>= (car_blue_hor (fixed st)) hPos) (< (car_blue_hor (fixed st)) (+ hPos length))) (noOverlap vPos (car_blue_ver st) 2))
		(=> (and (>= (car_pink_hor (fixed st)) hPos) (< (car_pink_hor (fixed st)) (+ hPos length))) (noOverlap vPos (car_pink_ver st) 2))
		(=> (and (>= (car_darkgreen_hor (fixed st)) hPos) (< (car_darkgreen_hor (fixed st)) (+ hPos length))) (noOverlap vPos (car_darkgreen_ver st) 2))
		(=> (and (>= (car_purple_hor (fixed st)) hPos) (< (car_purple_hor (fixed st)) (+ hPos length))) (noOverlap vPos (car_purple_ver st) 2))
		(=> (and (>= (car_orange_hor (fixed st)) hPos) (< (car_orange_hor (fixed st)) (+ hPos length))) (noOverlap vPos (car_orange_ver st) 2))
		(=> (and (>= (truck_purple_hor (fixed st)) hPos) (< (truck_purple_hor (fixed st)) (+ hPos length))) (noOverlap vPos (truck_purple_ver st) 3))
	)
)

(define-fun moveUp ((vPosCur Int) (vPosNext Int) (hPos Int) (length Int) (current State) (next State)) Bool
	(and
		(=> (vehicleMovedAboveOf vPosCur vPosNext (truck_blue_ver (fixed current))) (noOverlap hPos (truck_blue_hor current) 3))
		(=> (vehicleMovedAboveOf vPosCur vPosNext (car_brown_ver (fixed current))) (noOverlap hPos (car_brown_hor current) 2))
		(=> (vehicleMovedAboveOf vPosCur vPosNext (car_lightgreen_ver (fixed current))) (noOverlap hPos (car_lightgreen_hor current) 2))
		(=> (vehicleMovedAboveOf vPosCur vPosNext (car_red_ver (fixed current))) (noOverlap hPos (car_red_hor current) 2))
		(=> (vehicleMovedAboveOf vPosCur vPosNext (car_yellow_ver (fixed current))) (noOverlap hPos (car_yellow_hor current) 2))
		(=> (vehicleMovedAboveOf vPosCur vPosNext (car_black_ver (fixed current))) (noOverlap hPos (car_black_hor current) 2))
	)
)

(define-fun moveDown ((vPosCur Int) (vPosNext Int) (hPos Int) (length Int) (current State) (next State)) Bool
	(and
		(=> (vehicleMovedBelowOf vPosCur vPosNext (truck_blue_ver (fixed current)) length) (noOverlap hPos (truck_blue_hor current) 3))
		(=> (vehicleMovedBelowOf vPosCur vPosNext (car_brown_ver (fixed current)) length) (noOverlap hPos (car_brown_hor current) 2))
		(=> (vehicleMovedBelowOf vPosCur vPosNext (car_lightgreen_ver (fixed current)) length) (noOverlap hPos (car_lightgreen_hor current) 2))
		(=> (vehicleMovedBelowOf vPosCur vPosNext (car_red_ver (fixed current)) length) (noOverlap hPos (car_red_hor current) 2))
		(=> (vehicleMovedBelowOf vPosCur vPosNext (car_yellow_ver (fixed current)) length) (noOverlap hPos (car_yellow_hor current) 2))
		(=> (vehicleMovedBelowOf vPosCur vPosNext (car_black_ver (fixed current)) length) (noOverlap hPos (car_black_hor current) 2))
	)
)

(define-fun verticalStateInvariant ((hPos Int) (vPos Int) (length Int) (st State)) Bool
	(and
		(=> (and (>= (truck_blue_ver (fixed st)) vPos) (< (truck_blue_ver (fixed st)) (+ vPos length))) (noOverlap hPos (truck_blue_hor st) 3))
		(=> (and (>= (car_brown_ver (fixed st)) vPos) (< (car_brown_ver (fixed st)) (+ vPos length)))	(noOverlap hPos (car_brown_hor st) 2))
		(=> (and (>= (car_lightgreen_ver (fixed st)) vPos) (< (car_lightgreen_ver (fixed st))(+ vPos length))) (noOverlap hPos (car_lightgreen_hor st) 2))
		(=> (and (>= (car_red_ver (fixed st)) vPos) (< (car_red_ver (fixed st)) (+ vPos length))) (noOverlap hPos (car_red_hor st) 2))
		(=> (and (>= (car_yellow_ver (fixed st)) vPos) (< (car_yellow_ver (fixed st)) (+ vPos length))) (noOverlap hPos (car_yellow_hor st) 2))
		(=> (and (>= (car_black_ver (fixed st)) vPos) (< (car_black_ver (fixed st)) (+ vPos length))) (noOverlap hPos (car_black_hor st) 2))
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

(define-fun carLightGreenMoveLeft ((current State) (next State)) Bool
	(moveLeft (car_lightgreen_hor current) (car_lightgreen_hor next) (car_lightgreen_ver (fixed current)) 2 current next)
)

(define-fun carLightGreenMoveRight ((current State) (next State)) Bool
	(moveRight (car_lightgreen_hor current) (car_lightgreen_hor next) (car_lightgreen_ver (fixed current)) 2 current next)
)

(define-fun carLightGreenStateInvariant ((st State)) Bool 
	(horizontalStateInvariant (car_lightgreen_hor st) (car_lightgreen_ver (fixed st)) 2 st)
)

(define-fun truckBlueMoveLeft ((current State) (next State)) Bool
	(moveLeft (truck_blue_hor current) (truck_blue_hor next) (truck_blue_ver (fixed current)) 3 current next)
)

(define-fun truckBlueMoveRight ((current State) (next State)) Bool
	(moveRight (truck_blue_hor current) (truck_blue_hor next) (truck_blue_ver (fixed current)) 3 current next)
)

(define-fun truckBlueStateInvariant ((st State)) Bool 
	(horizontalStateInvariant (truck_blue_hor st) (truck_blue_ver (fixed st)) 3 st)
)

(define-fun carBrownMoveLeft ((current State) (next State)) Bool
	(and
		(moveLeft (car_brown_hor current) (car_brown_hor next) (car_brown_ver (fixed current)) 2 current next)
		; brown and yellow car are in the same lane
		(or (>= (+ (car_brown_hor next) (* (- 1) (car_yellow_hor current))) 2)
			(> (car_yellow_hor current) (car_brown_hor current)))

	)
)

(define-fun carBrownMoveRight ((current State) (next State)) Bool
	(and 
		(moveRight (car_brown_hor current) (car_brown_hor next) (car_brown_ver (fixed current)) 2 current next)
	
		(or (>= (+ (+ (car_brown_hor next) 2) (* (- 1) (car_yellow_hor current))) 2)
			(>= (car_yellow_hor current) (+ (car_brown_hor current) 2)))
	)
)

(define-fun carBrownStateInvariant ((st State)) Bool 
	(and
		(horizontalStateInvariant (car_brown_hor st) (car_brown_ver (fixed st)) 2 st)
	
		(or (>= (+ (car_brown_hor st) (* (- 1) (car_yellow_hor st))) 2)
			(>= (car_yellow_hor st) (+ (car_brown_hor st) 2)))
	)
)

(define-fun carYellowMoveLeft ((current State) (next State)) Bool
	(and
		(moveLeft (car_yellow_hor current) (car_yellow_hor next) (car_yellow_ver (fixed current)) 2 current next)
		; brown and yellow car are in the same lane
		(or (>= (+ (car_yellow_hor next) (* (- 1) (car_brown_hor current))) 2)
			(> (car_brown_hor current) (car_yellow_hor current)))

	)
)

(define-fun carYellowMoveRight ((current State) (next State)) Bool
	(and 
		(moveRight (car_yellow_hor current) (car_yellow_hor next) (car_yellow_ver (fixed current)) 2 current next)
	
		(or (>= (+ (+ (car_yellow_hor next) 2) (* (- 1) (car_brown_hor current))) 2)
			(>= (car_brown_hor current) (+ (car_yellow_hor current) 2)))
	)
)

(define-fun carYellowStateInvariant ((st State)) Bool 
	(and
		(horizontalStateInvariant (car_yellow_hor st) (car_yellow_ver (fixed st)) 2 st)
	
		(or (>= (+ (car_yellow_hor st) (* (- 1) (car_brown_hor st))) 2)
			(>= (car_brown_hor st) (+ (car_yellow_hor st) 2)))
	)
)

(define-fun carBlackMoveLeft ((current State) (next State)) Bool
	(moveLeft (car_black_hor current) (car_black_hor next) (car_black_ver (fixed current)) 2 current next)
)

(define-fun carBlackMoveRight ((current State) (next State)) Bool
	(moveRight (car_black_hor current) (car_black_hor next) (car_black_ver (fixed current)) 2 current next)
)

(define-fun carBlackStateInvariant ((st State)) Bool 
	(horizontalStateInvariant (car_black_hor st) (car_black_ver (fixed st)) 2 st)
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

(define-fun carBlueMoveUp ((current State) (next State)) Bool
	(moveUp (car_blue_ver current) (car_blue_ver next) (car_blue_hor (fixed current)) 2 current next)
)

(define-fun carBlueMoveDown ((current State) (next State)) Bool
	(moveDown (car_blue_ver current) (car_blue_ver next) (car_blue_hor (fixed current)) 2 current next)
)

(define-fun carBlueStateInvariant ((st State)) Bool
	(verticalStateInvariant (car_blue_hor (fixed st)) (car_blue_ver st) 2 st)
)

(define-fun carPinkMoveUp ((current State) (next State)) Bool
	(and
		(moveUp (car_pink_ver current) (car_pink_ver next) (car_pink_hor (fixed current)) 2 current next)

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (car_pink_ver next) (* (- 1) (car_darkgreen_ver current))) 2)
			(> (car_darkgreen_ver current) (car_pink_ver current)))
	)
)

(define-fun carPinkMoveDown ((current State) (next State)) Bool
	(and
		(moveDown (car_pink_ver current) (car_pink_ver next) (car_pink_hor (fixed current)) 2 current next)

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (+ (car_pink_ver next) 2) (* (- 1) (car_darkgreen_ver current))) 2)
			(>= (car_darkgreen_ver current) (+ (car_pink_ver current) 2)))
	)
)

(define-fun carPinkStateInvariant ((st State)) Bool
	(and
		(verticalStateInvariant (car_pink_hor (fixed st)) (car_pink_ver st) 2 st)
		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (car_pink_ver st) (* (- 1) (car_darkgreen_ver st))) 2)
			(>= (car_darkgreen_ver st) (+ (car_pink_ver st) 2)))
	)
)

(define-fun carDarkGreenMoveUp ((current State) (next State)) Bool
	(and
		(moveUp (car_darkgreen_ver current) (car_darkgreen_ver next) (car_darkgreen_hor (fixed current)) 2 current next)

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (car_darkgreen_ver next) (* (- 1) (car_pink_ver current))) 2)
			(> (car_pink_ver current) (car_darkgreen_ver current)))
	)
)

(define-fun carDarkGreenMoveDown ((current State) (next State)) Bool
	(and
		(moveDown (car_darkgreen_ver current) (car_darkgreen_ver next) (car_darkgreen_hor (fixed current)) 2 current next)

		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (+ (car_darkgreen_ver next) 2) (* (- 1) (car_pink_ver current))) 2)
			(>= (car_pink_ver current) (+ (car_darkgreen_ver current) 2)))
	)
)

(define-fun carDarkGreenStateInvariant ((st State)) Bool
	(and
		(verticalStateInvariant (car_darkgreen_hor (fixed st)) (car_darkgreen_ver st) 2 st)
		; orange car is in same lane as the purple truck, extra checks are needed
		(or (>= (+ (car_darkgreen_ver st) (* (- 1) (car_pink_ver st))) 2)
			(>= (car_pink_ver st) (+ (car_darkgreen_ver st) 2)))
	)
)


(define-fun carPurpleMoveUp ((current State) (next State)) Bool
	(moveUp (car_purple_ver current) (car_purple_ver next) (car_purple_hor (fixed current)) 2 current next)
)

(define-fun carPurpleMoveDown ((current State) (next State)) Bool
	(moveDown (car_purple_ver current) (car_purple_ver next) (car_purple_hor (fixed current)) 2 current next)
)

(define-fun carPurpleStateInvariant ((st State)) Bool
	(verticalStateInvariant (car_purple_hor (fixed st)) (car_purple_ver st) 2 st)
)

(define-fun carOrangeMoveUp ((current State) (next State)) Bool
	(moveUp (car_orange_ver current) (car_orange_ver next) (car_orange_hor (fixed current)) 2 current next)
)

(define-fun carOrangeMoveDown ((current State) (next State)) Bool
	(moveDown (car_orange_ver current) (car_orange_ver next) (car_orange_hor (fixed current)) 2 current next)
)

(define-fun carOrangeStateInvariant ((st State)) Bool
	(verticalStateInvariant (car_orange_hor (fixed st)) (car_orange_ver st) 2 st)
)

(define-fun truckPurpleMoveUp ((current State) (next State)) Bool
	(moveUp (truck_purple_ver current) (truck_purple_ver next) (truck_purple_hor (fixed current)) 3 current next)
)

(define-fun truckPurpleMoveDown ((current State) (next State)) Bool
	(moveDown (truck_purple_ver current) (truck_purple_ver next) (truck_purple_hor (fixed current)) 3 current next)
)

(define-fun truckPurpleStateInvariant ((st State)) Bool
	(verticalStateInvariant (truck_purple_hor (fixed st)) (truck_purple_ver st) 3 st)
)
   
(define-fun move ((current State) (next State)) Bool
	(and
		(not (= current next))
		
		(fixedPos current)
		(fixedPos next)
		
		(stayInLane (car_red_hor next) 2)
		(stayInLane (car_lightgreen_hor next) 2)
		(stayInLane (truck_blue_hor next) 3)
		(stayInLane (car_black_hor next) 2)
		(stayInLane (car_brown_hor next) 2)
		(stayInLane (car_yellow_hor next) 2)
		(stayInLane (truck_yellow_ver next) 3)
		(stayInLane (car_blue_ver next) 2)
		(stayInLane (car_pink_ver next) 2)
		(stayInLane (car_darkgreen_ver next) 2)
		(stayInLane (car_purple_ver next) 2)
		(stayInLane (car_orange_ver next) 2)
		(stayInLane (truck_purple_ver next) 3)		

		(=> (< (car_red_hor next) (car_red_hor current)) (carRedMoveLeft current next))
		(=> (> (car_red_hor next) (car_red_hor current)) (carRedMoveRight current next))
		(carRedStateInvariant next)

		(=> (< (car_lightgreen_hor next) (car_lightgreen_hor current)) (carLightGreenMoveLeft current next))
		(=> (> (car_lightgreen_hor next) (car_lightgreen_hor current)) (carLightGreenMoveRight current next))
		(carLightGreenStateInvariant next)
		
		(=> (< (truck_blue_hor next) (truck_blue_hor current)) (truckBlueMoveLeft current next))
		(=> (> (truck_blue_hor next) (truck_blue_hor current)) (truckBlueMoveRight current next))
		(truckBlueStateInvariant next)
		
		(=> (< (car_black_hor next) (car_black_hor current)) (carBlackMoveLeft current next))
		(=> (> (car_black_hor next) (car_black_hor current)) (carBlackMoveRight current next))
		(carBlackStateInvariant next)

		(=> (< (car_brown_hor next) (car_brown_hor current)) (carBrownMoveLeft current next))
		(=> (> (car_brown_hor next) (car_brown_hor current)) (carBrownMoveRight current next))
		(carBrownStateInvariant next)
		
		(=> (< (car_yellow_hor next) (car_yellow_hor current)) (carYellowMoveLeft current next))
		(=> (> (car_yellow_hor next) (car_yellow_hor current)) (carYellowMoveRight current next))
		(carYellowStateInvariant next)
				
		(=> (< (truck_yellow_ver next) (truck_yellow_ver current)) (truckYellowMoveUp current next))
		(=> (> (truck_yellow_ver next) (truck_yellow_ver current)) (truckYellowMoveDown current next))
		(truckYellowStateInvariant next)
		
		(=> (< (car_blue_ver next) (car_blue_ver current)) (carBlueMoveUp current next))
		(=> (> (car_blue_ver next) (car_blue_ver current)) (carBlueMoveDown current next))
		(carBlueStateInvariant next)

		(=> (< (car_pink_ver next) (car_pink_ver current)) (carPinkMoveUp current next))
		(=> (> (car_pink_ver next) (car_pink_ver current)) (carPinkMoveDown current next))
		(carPinkStateInvariant next)

		(=> (< (car_darkgreen_ver next) (car_darkgreen_ver current)) (carDarkGreenMoveUp current next))
		(=> (> (car_darkgreen_ver next) (car_darkgreen_ver current)) (carDarkGreenMoveDown current next))
		(carDarkGreenStateInvariant next)
		
		(=> (< (car_purple_ver next) (car_purple_ver current)) (carPurpleMoveUp current next))
		(=> (> (car_purple_ver next) (car_purple_ver current)) (carPurpleMoveDown current next))
		(carPurpleStateInvariant next)
		
		(=> (< (car_orange_ver next) (car_orange_ver current)) (carOrangeMoveUp current next))
		(=> (> (car_orange_ver next) (car_orange_ver current)) (carOrangeMoveDown current next))
		(carOrangeStateInvariant next)		

		(=> (< (truck_purple_ver next) (truck_purple_ver current)) (truckPurpleMoveUp current next))
		(=> (> (truck_purple_ver next) (truck_purple_ver current)) (truckPurpleMoveDown current next))
		(truckPurpleStateInvariant next)

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
(declare-const s7 State)
(declare-const s8 State)
(declare-const s9 State)
(declare-const s10 State)
(declare-const s11 State)
(declare-const s12 State)
(declare-const s13 State)
(declare-const s14 State)
(declare-const s15 State)
(declare-const s16 State)
(declare-const s17 State)
(declare-const s18 State)
(declare-const s19 State)
(declare-const s20 State)
(declare-const s21 State)
(declare-const s22 State)
(declare-const s23 State)
(declare-const s24 State)
(declare-const s25 State)
(declare-const s26 State)
(declare-const s27 State)
(declare-const s28 State)
(declare-const s29 State)
(declare-const s30 State)
(declare-const s31 State)
(declare-const s32 State)
(declare-const s33 State)
(declare-const s34 State)
(declare-const s35 State)
(declare-const s36 State)
(declare-const s37 State)
(declare-const s38 State)
(declare-const s39 State)
(declare-const s40 State)
(declare-const s41 State)
(declare-const s42 State)
(declare-const s43 State)
(declare-const s44 State)
(declare-const s45 State)
(declare-const s46 State)
(declare-const s47 State)
(declare-const s48 State)
(declare-const s49 State)
(declare-const s50 State)

(assert (initial s0))
(assert (move s0 s1))
(assert (move s1 s2))
(assert (move s2 s3))
(assert (move s3 s4))
(assert (move s4 s5))
(assert (move s5 s6))
(assert (move s6 s7))
(assert (move s7 s8))
(assert (move s8 s9))
(assert (move s9 s10))
(assert (move s10 s11))
(assert (move s11 s12))
(assert (move s12 s13))
(assert (move s13 s14))
(assert (move s14 s15))
(assert (move s15 s16))
(assert (move s16 s17))
(assert (move s17 s18))
(assert (move s18 s19))
(assert (move s19 s20))
(assert (move s20 s21))
(assert (move s21 s22))
(assert (move s22 s23))
(assert (move s23 s24))
(assert (move s24 s25))
(assert (move s25 s26))
(assert (move s26 s27))
(assert (move s27 s28))
(assert (move s28 s29))
(assert (move s29 s30))
(assert (move s30 s31))
(assert (move s31 s32))
(assert (move s32 s33))
(assert (move s33 s34))
(assert (move s34 s35))

(assert (canExit s35))

(check-sat)
(get-value (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34 s35))

(pop 1)

