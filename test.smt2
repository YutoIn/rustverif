(declare-fun main (Int) Bool)
(declare-fun seven (Int Int) Bool)
(assert	
	(forall 
		((n Int) (ret Int)) 
		(=> 
			(and (<= n 4) (= ret (+ n 3))) 
			(seven n ret)
		)
	)
)

(assert 
	(forall 
		((n Int) (ret Int)) 
		(=> 
			(and 
				(not (<= n 4)) 
				(= ret (seven (seven (- n 4))))
			) 
			(seven n ret)
		)
	)
)
(assert 
	(forall 
		((ret Int)) 
		(=> 
			(= ret 0) 
			(main  ret)
		)
	)
)

(check-sat)
(get-model)
