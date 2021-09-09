(declare-const p Bool)
(declare-const q Bool)

; Thruth table for implication (=>)
(assert (=> p q))

(push 1)
(assert (not q))

(push 2)
(assert p)
(check-sat)
(pop 2)

(push 2)
(assert (not p))
(check-sat)
(pop 2)

(pop 1)

(push 1)
(assert q)

(push 2)
(assert p)
(check-sat)
(pop 2)

(push 2)
(assert (not p))
(check-sat)
(pop 2)

(pop 1)

