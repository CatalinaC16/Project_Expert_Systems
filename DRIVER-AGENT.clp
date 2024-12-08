;
;-------Auxiliary facts ---------------------------------------
;

(defrule AGENT::initCycle-speeding
    (declare (salience 99))
    (timp (valoare ?)) ;make sure it fires each cycle
=>
    (if (eq ?*ag-in-debug* TRUE) then (printout t "" crlf))
    ;(facts AGENT)
)

(defrule AGENT::init_speeding
     (declare (salience 99))
     (timp (valoare 1))
     ?f<-(speeding (speed ?v)(default ?d))
=>
     (assert (ag_bel (bel_type fluent) (bel_pname speeding-limit) (bel_pval ?v)))
     (assert (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?d)))
     (assert (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval national)))
     (assert (ag_bel (bel_type fluent) (bel_pname in_locality) (bel_pval false)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "    init speeed " crlf))
     (retract ?f)
)

;;---------------------------------------
;;
;;      Made by us
;;
;;---------------------------------------


;--- semn forbidding a certain speeding
(defrule AGENT::semn_speed_limit
     (declare (salience 40))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname forbidden_over ) (percept_pval ?limita))
     ?s <- (ag_bel (bel_type fluent)(bel_pname speeding-limit) (bel_pval ?))
=>
     (modify ?s (bel_pval ?limita))
     (if (eq ?*ag-in-debug* TRUE) then (printout t " interzis peste ?speed_value "  crlf))
     (retract ?f)
)

; ;--- semn ending certain speed limit
(defrule AGENT::semn_speed_limit_end
      (declare (salience 50))
      (timp (valoare ?t))
      ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname end_of_forbidden_over) (percept_pval ?limita))
      ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit) (bel_pval ?current))
      ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?old))
=>
      (if (eq ?current ?limita) then (modify ?s (bel_pval ?old)))
      (retract ?f)
)

;--- semn intra localitate
(defrule AGENT::r-semn-intra-localitate
     (declare (salience 51))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname localitate) (percept_pval intra))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?))
     ?i <- (ag_bel (bel_type fluent) (bel_pname in_locality) (bel_pval ?))
=>
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in localitate si am viteza maxima : ?value "  crlf))
     ;;(printout t "Cff" crlf)
     (modify ?s (bel_pval 50))
     (modify ?d (bel_pval 50))
     (modify ?i (bel_pval true))
     (retract ?f)
)

;--- semn we left localitate
(defrule AGENT::r-semn-paraseste-localitate
    (declare (salience 51)) ; Importanța regulii (vezi notele de mai jos despre salience)
    (timp (valoare ?t)) ; Capturăm timpul
    ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname localitate) (percept_pval paraseste))
    ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit) (bel_pval ?sl)) ; Limită de viteză curentă
    ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?sd)) ; Limită implicită
    ?i <- (ag_bel (bel_type fluent) (bel_pname in_locality) (bel_pval ?inLoc)) ; Starea în localitate
=>
    ; Actualizăm starea "în localitate" și afișăm rezultatul
    (modify ?i (bel_pval false))
    (if (eq ?*ag-in-debug* TRUE)
        then (printout t "    am iesit din localitate" crlf))
    
    ; Retragerea percepțiilor procesate
    (retract ?f)
)



; ;--- semn intra on a national european road
(defrule AGENT::r-drum-european
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname drum_european) (percept_pval intra))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?))
=>
     (modify ?s (bel_pval 100))
     (modify ?d (bel_pval 100))
     (modify ?l (bel_pval european))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in drum_european"  crlf))
     (retract ?f)
)

;--- Gps info we are on a european road
(defrule AGENT::r-drum-european-gps
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj gps_info) (percept_pname drum_european) (percept_pval true))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?))
=>
     (modify ?s (bel_pval 100))
     (modify ?d (bel_pval 100))
     (modify ?l (bel_pval european))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in drum_european"  crlf))
     (retract ?f)
)


;---semn zona rezidentiala
(defrule AGENT::r-semn-zona-rezidentiala
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname zona_rezidentiala) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 20)))
     (if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in zona rezidentiala"  crlf))
     (retract ?f)
)

;---semn end of zona rezidentiala
(defrule AGENT::r-semn-end-of-zona-rezidentiala
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname zona_rezidentiala) (percept_pval paraseste))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (modify ?s (bel_pval ?def))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "  am iesit din zona rezidentiala"  crlf))
     (retract ?f)
)

;---semn zona pietonala
(defrule AGENT::r-semn-zona-pietonala
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname zona_pietonala) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 5)))
     (if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in zona pietonala"  crlf))
     (retract ?f)
)

;---semn end of zona pietonala
(defrule AGENT::r-semn-end-of-zona-pietonala
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname zona_pietonala) (percept_pval paraseste))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (modify ?s (bel_pval ?def))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit din zona pietonala"  crlf))
     (retract ?f)
)

;---semn drum in lucru
(defrule AGENT::r-semn-drum-in-lucru-limitare-viteza
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname drum_in_lucru) (percept_pval ?v))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
=>
     (modify ?s (bel_pval ?v))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat pe un drum in lucru"  crlf))
     (retract ?f)
)

;--semn trecere de pietoni
(defrule AGENT::r-semn-trecere-de-pietoni
     (declare (salience 50))
     (timp (valoare ?t))
     ?b <- (ag_percept (percept_pobj gps_info) (percept_pname lanes) (percept_pval 1))
     ?p <- (ag_percept (percept_pobj pieton) (percept_pname distance_to_trecere) (percept_pval close))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname information_semn) (percept_pval trecere_de_pietoni))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
=>
     (modify ?s (bel_pval 30))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   Am intalnit o trecede de pietoni"  crlf))
     (retract ?b)
     (retract ?p)
     (retract ?f)
)


;--Senzorul masinii ne anunta ca am trecut de trecerea de pietoni
(defrule AGENT::r-trecere-de-pietoni-end
     (declare (salience 50))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj car_sensor) (percept_pname trecere_de_pietoni) (percept_pval iesire))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?default))
=>
     (modify ?s (bel_pval ?default))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am trecut de trecerea de pietoni"  crlf))
     (retract ?p)
)


;---semn curba deosebit de periculoasa
(defrule AGENT::r-semn-curba-deosebit-de-periculoasa
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname indicator_de_avertizare) (percept_pval curba_deosebit_de_periculoasa))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?speed))
     ?i <- (ag_bel (bel_type fluent) (bel_pname in_locality) (bel_pval ?boolean))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?))
=>
     (modify ?d (bel_pval ?speed))
     (if (eq ?boolean true) then (modify ?s (bel_pval 30)))
     (if (eq ?boolean false) then (modify ?s (bel_pval 50)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   Am intalnit o curba deosebit de periculoasa"  crlf))
     (retract ?f)
)


;--Senzorul masinii ne anunta cand am iesit din curba periculoasa
(defrule AGENT::r-curba-deosebit-de-periculoasa-end
     (declare (salience 40))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj car_sensor) (percept_pname curba_deosebit_de_periculoasa) (percept_pval iesire))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?default))
=>
     (modify ?s (bel_pval ?default))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am trecut de curba deosebit de periculoasa"  crlf))
     (retract ?p)
)


;---semn intra highway
(defrule AGENT::r-semn-autostrada
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname autostrada) (percept_pval intra))
     ?c <- (ag_percept (percept_pobj gps_info) (percept_pname country) (percept_pval ?country))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?))
=>
     (if (eq ?country Germania) then (modify ?s (bel_pval none)) (modify ?d (bel_pval none))
     else (modify ?s (bel_pval 130)) (modify ?d (bel_pval 130)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in localitate"  crlf))
     (modify ?l (bel_pval autostrada))
     (retract ?f)
     (retract ?c)
)

;---semn exiting highway
(defrule AGENT::semn-autostrada-exit
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pval autostrada_exit))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?))
=>
     (modify ?s (bel_pval 90))
     (modify ?d (bel_pval 90))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in localitate"  crlf))
     (modify ?l (bel_pval /NA))
     (retract ?f)
)

;--Senzorul de ploaie ne atentioneaza ca incepe sa ploua
(defrule AGENT::r-raining
     (declare (salience 20))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj raining_sensor) (percept_pname is_raining) (percept_pval true))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?road))
     ?i <- (ag_bel (bel_type fluent) (bel_pname in_locality) (bel_pval ?boolean))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?))
=>
     (if (eq ?road autostrada) 
         then 
         (modify ?s (bel_pval 80)) 
         (modify ?d (bel_pval 80))
         else
         (if (eq ?boolean true) 
             then 
             (modify ?s (bel_pval 30)) 
             (modify ?d (bel_pval 30)))
         (if (eq ?boolean false) 
             then 
             (modify ?s (bel_pval 50)) 
             (modify ?d (bel_pval 50)))
     )
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   a inceput sa ploua" crlf))
     (retract ?p)
)

;--Senzorul de ploaie ne atentioneaza ca nu mai ploua
(defrule AGENT::r-rain-stops
     (declare (salience 40))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj raining_sensor) (percept_pname is_raining) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit) (bel_pval ?))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?road))
     ?i <- (ag_bel (bel_type fluent) (bel_pname in_locality) (bel_pval ?boolean))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?))
=>
     (if (eq ?road autostrada)
         then 
         (modify ?s (bel_pval 130)) 
         (modify ?d (bel_pval 130))
         else
         (if (eq ?boolean true)
             then 
             (modify ?s (bel_pval 50)) 
             (modify ?d (bel_pval 50)))
         (if (eq ?boolean false)
             then 
             (modify ?s (bel_pval 90)) 
             (modify ?d (bel_pval 90)))
     )
     (if (eq ?road european)
        then 
            (modify ?s (bel_pval 100)) ; Setăm viteza curentă la 100
            (modify ?d (bel_pval 100)) ; Setăm viteza implicită la 100
            (if (eq ?*ag-in-debug* TRUE)
                then (printout t "   Drum european detectat: viteza setată la 100 km/h." crlf)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   ploaia s-a oprit" crlf))
     (retract ?p)
)


;--Semn de trecere de frontiera
(defrule AGENT::r-trecere-de-frontiera
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname information_semn) (percept_pval punct_vamal))
     ?g <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname country) (percept_pval ?country))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval autostrada))
=>
     (if (eq ?country Germania) then (modify ?s (bel_pval none)) (modify ?d (bel_pval none))
     else (modify ?s (bel_pval 130)) (modify ?d (bel_pval 130))
     )
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am trecut de curba deosebit de periculoasa"  crlf))
     (retract ?f)
     (retract ?g)
)








;;;;;;;;;;;;;;;;;;;;;;;;;; Me ;;;;;;;;;;;;;;;;;;;;;;;;;;
;---semn zona sens giratoriu
(defrule AGENT::r_semn_zona_sens_giratoriu
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname zona_sens_giratoriu) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 30)))
     (if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in zona de sens giratoriu"  crlf))
	 ;;(printout t "   am intrat in zona de sens giratoriu"  crlf)
     (retract ?f)
)

;---semn end zona sens giratoriu
(defrule AGENT::r_semn_end_sens_giratoriu
	(declare (salience 50))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj car_sensor) (percept_pname zona_sens_giratoriu) (percept_pval iesire))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?default))
=>
     (modify ?s (bel_pval ?default))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit din zona de sens giratoriu"  crlf))
	 ;;(printout t "   am iesit din zona de sens giratoriu"  crlf)
	 (retract ?p)
)

;--- Gps info iesire sens giratoriu 
(defrule AGENT::r-end-sens-giratoriu-gps
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj gps_info) (percept_pname zona_sens_giratoriu) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?def))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?r_t))
=>
     (modify ?s (bel_pval ?def))
     (modify ?d (bel_pval ?def))
     (modify ?l (bel_pval ?r_t))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit din sensul giratoriu GPS"  crlf))
	 ;;(printout t "   am iesit din sensul giratoriu GPS"  crlf)
	 (retract ?f)
)


;---semn drum cu denivelari (viteza = 30 in localitate si 50 in afara)
(defrule AGENT::r_semn_drum_cu_denivelari
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname drum_cu_denivelari) (percept_pval intra))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?speed))
	 ?i <- (ag_bel (bel_type fluent) (bel_pname in_locality) (bel_pval ?boolean))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?))
=>
     (modify ?d (bel_pval ?speed))
     (if (eq ?boolean true) then (modify ?s (bel_pval 30)))
     (if (eq ?boolean false) then (modify ?s (bel_pval 50)))
	 (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat pe un drum cu denivelari"  crlf))
	 ;;(printout t "   am intrat pe un drum cu denivelari"  crlf)
     (retract ?f)
)


;--- semn ca se sfarseste drumul cu denivelari (viteza = 30 in localitate si 50 in afara)
(defrule AGENT::r_semn_end_drum_cu_denivelari
	(declare (salience 50))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj car_sensor) (percept_pname drum_cu_denivelari) (percept_pval iesire))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?default))
=>
     (modify ?s (bel_pval ?default))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit din zona de drum cu denivelari"  crlf))
	 ;;(printout t "   am iesit din zona de drum cu denivelari"  crlf)
	 (retract ?p)
)



;--- semn drum offroad (viteza = 20 in localitate si in afara)
(defrule AGENT::r_semn_drum_offroad
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname drum_offroad) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?def))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 20)) ) 
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat pe drum offroad"  crlf))
	 ;;(printout t "   am intrat pe drum offroad"  crlf)
     (retract ?f)
)

;--- semn end drum offroad (viteza = 20 in localitate si in afara)
(defrule AGENT::r_semn_end_drum_offroad
	(declare (salience 40))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj car_sensor) (percept_pname drum_offroad) (percept_pval iesire))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?default))
	 ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?r_t))
=>
     (modify ?s (bel_pval ?default))
	 (modify ?d (bel_pval ?default))
	 (modify ?l (bel_pval ?r_t))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit din zona de drum offroad"  crlf))
	 ;;(printout t "   am iesit din zona de drum offroad"  crlf)
	 (retract ?p)
)


;--- semn zona in care se afla copii (viteza = 30 in localitate si 50 in afara)
(defrule AGENT::r_semn_atentie_copii
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname atentie_copii) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 30)))
     (if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in zona scoala"  crlf))
	 ;;(printout t "   am intrat in zona de atentie copii"  crlf)
     (retract ?f)
)

;--- semn iesire din zona atentie copii (viteza = 30 in localitate si 50 in afara)
(defrule AGENT::r_semn_end_atentie_copii
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj gps_info) (percept_pname atentie_copii) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?def))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?r_t))
=>
     (modify ?s (bel_pval ?def))
     (modify ?d (bel_pval ?def))
     (modify ?l (bel_pval ?r_t))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit din zona de atentie copii"  crlf))
	 ;;(printout t "   am iesit din zona de atentie copii"  crlf)
	 (retract ?f)
)


;--- semn drumuri private (dupa caz viteza = 5, 10, 15 sau 30 km/h)
(defrule AGENT::r_semn_drumuri_private_5
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname drum_privat_5) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 5)))
     (if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in zona de drum privat 5"  crlf))
	 ;;(printout t "   am intrat in zona de drum privat 5"  crlf)
     (retract ?f)
)

;--- semn end drumuri private (dupa caz viteza = 5, 10, 15 sau 30 km/h)
(defrule AGENT::r_semn_end_drumuri_private_5
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj gps_info) (percept_pname drum_privat_5) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?def))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?r_t))
=>
     (modify ?s (bel_pval ?def))
     (modify ?d (bel_pval ?def))
     (modify ?l (bel_pval ?r_t))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit din zona de drum privat 5"  crlf))
	 ;;(printout t "   am iesit din zona de drum privat 5"  crlf)
	 (retract ?f)
)


;--- semn drumuri private (dupa caz viteza = 5, 10, 15 sau 30 km/h)
(defrule AGENT::r_semn_drumuri_private_10
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname drum_privat_10) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 10)))
     (if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in zona de drum privat 10"  crlf))
	 ;;(printout t "   am intrat in zona de drum privat 10"  crlf)
     (retract ?f)
)

;--- semn end drumuri private (dupa caz viteza = 5, 10, 15 sau 30 km/h)
(defrule AGENT::r_semn_end_drumuri_private_10
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj gps_info) (percept_pname drum_privat_10) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?def))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?r_t))
=>
     (modify ?s (bel_pval ?def))
     (modify ?d (bel_pval ?def))
     (modify ?l (bel_pval ?r_t))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit din zona de drum privat 10"  crlf))
	 ;;(printout t "   am iesit din zona de drum privat 10"  crlf)
	 (retract ?f)
)

;--- semn drumuri private (dupa caz viteza = 5, 10, 15 sau 30 km/h)
(defrule AGENT::r_semn_drumuri_private_15
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname drum_privat_15) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 15)))
     (if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in zona de drum privat 15"  crlf))
	 ;;(printout t "   am intrat in zona de drum privat 15"  crlf)
     (retract ?f)
)

;--- semn end drumuri private (dupa caz viteza = 5, 10, 15 sau 30 km/h)
(defrule AGENT::r_semn_end_drumuri_private_15
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj gps_info) (percept_pname drum_privat_15) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?def))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?r_t))
=>
     (modify ?s (bel_pval ?def))
     (modify ?d (bel_pval ?def))
     (modify ?l (bel_pval ?r_t))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit din zona de drum privat 15"  crlf))
	 ;;(printout t "   am iesit din zona de drum privat 15"  crlf)
	 (retract ?f)
)

;--- semn drumuri private (dupa caz viteza = 5, 10, 15 sau 30 km/h)
(defrule AGENT::r_semn_drumuri_private_30
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname drum_privat_30) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 30)))
     (if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in zona de drum privat 30"  crlf))
	 ;;(printout t "   am intrat in zona de drum privat 30"  crlf)
     (retract ?f)
)

;--- semn end drumuri private (dupa caz viteza = 5, 10, 15 sau 30 km/h)
(defrule AGENT::r_semn_end_drumuri_private_30
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj gps_info) (percept_pname drum_privat_30) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?def))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?r_t))
=>
     (modify ?s (bel_pval ?def))
     (modify ?d (bel_pval ?def))
     (modify ?l (bel_pval ?r_t))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit din zona de drum privat 30"  crlf))
	 ;;(printout t "   am iesit din zona de drum privat 30"  crlf)
	 (retract ?f)
)


;--- semn dispozitive de limitare viteza (denivelari/hopuri/bumpere): viteza = 30km/h
(defrule AGENT::r_semn_dispozitive_limitare_viteza
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname dispozitive_limitare_viteza) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 30)))
     (if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in zona unde sunt dispozitive de limitare pentru viteza"  crlf))
	 ;;(printout t "   am intrat in zona unde sunt dispozitive de limitare pentru viteza"  crlf)
     (retract ?f)
)

;--- semn end dispozitive de limitare viteza (denivelari/hopuri/bumpere): viteza = 30km/h
(defrule AGENT::r_semn_end_dispozitive_limitare_viteza
	(declare (salience 40))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj car_sensor) (percept_pname dispozitive_limitare_viteza) (percept_pval iesire))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?default))
=>
     (modify ?s (bel_pval ?default))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit din zona unde sunt dispozitive de limitare pentru viteza"  crlf))
	 ;;(printout t "   am iesit din zona unde sunt dispozitive de limitare pentru viteza"  crlf)
     (retract ?p)
)


;--- semn trecere linie de cale ferata cu bariera (viteza = 5 km/h)
(defrule AGENT::r_semn_trecere_de_cale_ferata_cu_bariera
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname trecere_de_cale_ferata_cu_bariera) (percept_pval ?val))
	?p <- (ag_percept (percept_pobj senzor_bariera) (percept_pname perceptie_bariera) (percept_pval ?is_there))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (if (and (eq ?val intra) (eq ?is_there barrier) ) then (modify ?s (bel_pval 0))
								(if (eq ?*ag-in-debug* TRUE) then (printout t "   Suntem la o trecere de cale ferata cu bariera si asteptam sa se ridice bariera"  crlf) )
								;;(printout t "   Suntem la o trecere de cale ferata cu bariera si asteptam sa se ridice bariera"  crlf) 
	)
	 (if (and (eq ?val intra) (eq ?is_there no_barrier) ) then (modify ?s (bel_pval 5)) 
								(if (eq ?*ag-in-debug* TRUE) then (printout t "   Suntem la o trecere de cale ferata cu bariera, iar bariera este sus"  crlf) )
								;;(printout t "   Suntem la o trecere de cale ferata cu bariera, iar bariera este sus"  crlf)
	)
     (if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
     ;;(if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat in zona de trecere cu cale ferata cu bariera"  crlf))
     (retract ?f)
	 (retract ?p)
)

;--- semn end trecere de cale ferata cu bariera (viteza = 5 km/h)
(defrule AGENT::r_semn_end_trecere_de_cale_ferata_cu_bariera
	(declare (salience 50))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj car_sensor) (percept_pname trecere_de_cale_ferata_cu_bariera) (percept_pval iesire))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?default))
=>
     (modify ?s (bel_pval ?default))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit din zona de trecere a caii ferate cu bariera prin senzori"  crlf))
	 ;;(printout t "   am iesit din zona de trecere a caii ferate cu bariera prin senzori"  crlf)
     (retract ?p)
)


;--- semn intra pe un drum judetean
(defrule AGENT::r_drum_judetean
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname drum_judetean) (percept_pval intra))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?))
=>
     (modify ?s (bel_pval 90))
     (modify ?d (bel_pval 90))
     (modify ?l (bel_pval judetean))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat pe un drum judetean"  crlf))
	 ;;(printout t "   am intrat pe un drum judetean"  crlf)
     (retract ?f)
)

;--- Gps info - suntem pe un drum judetean
(defrule AGENT::r_drum_judetean_gps
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj gps_info) (percept_pname drum_judetean) (percept_pval true))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?))
=>
     (modify ?s (bel_pval 90))
     (modify ?d (bel_pval 90))
     (modify ?l (bel_pval judetean))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am intrat pe un drum judetean folosind GPS"  crlf))
	 ;;(printout t "   am intrat pe un drum judetean folosind GPS"  crlf)
     (retract ?f)
)

;--- Gps info - NU mai suntem pe un drum judetean
(defrule AGENT::r_drum_judetean_gps_end
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj gps_info) (percept_pname drum_judetean) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?def))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?r_t))
=>
     (modify ?s (bel_pval ?def))
     (modify ?l (bel_pval ?r_t))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit de pe un drum judetean folosind GPS"  crlf))
	 ;;(printout t "   am intrat pe un drum judetean folosind GPS"  crlf)
     (retract ?f)
)



;--- semn trecere dintr-o granita in alta (dintr-o tara in alta)
(defrule AGENT::r_trecere_granita
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname trecere_granita) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 0)))
     (if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   suntem in procesul de trecere dintr-o tara in alta"  crlf))
	 ;;(printout t "   suntem in procesul de trecere dintr-o tara in alta"  crlf)
     (retract ?f)
)

;--- semn end GPS trecere dintr-o granita in alta (dintr-o tara in alta)
(defrule AGENT::r_end_trecere_granita
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj gps_info) (percept_pname trecere_granita) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?def))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?r_t))
=>
     (modify ?s (bel_pval ?def))
     (modify ?d (bel_pval ?def))
     (modify ?l (bel_pval ?r_t))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am trecut granita !!!"  crlf))
	 ;;(printout t "   am trecut granita !!!"  crlf)
	 (retract ?f)
)


;--- semn atentionare pericol de animale
(defrule AGENT::r_drum_animale_localitate
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname pericol_animale) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
	 ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?road))
     ?i <- (ag_bel (bel_type fluent) (bel_pname in_locality) (bel_pval ?locality))
=>
     ;;;;(if (eq ?val intra) then (modify ?s (bel_pval 30)))
	 (if (eq ?val intra) then  
				(if (eq ?road autostrada) then (modify ?s (bel_pval 50)) 
				else
					(if (eq ?locality true) then (modify ?s (bel_pval 30)) 
						(if (eq ?*ag-in-debug* TRUE) then (printout t "   suntem in zona de pericol de animale in localitate"  crlf))
						;;(printout t "   suntem in zona de pericol de animale in localitate"  crlf) 
					)
					(if (eq ?locality false) then (modify ?s (bel_pval 50)) 
						(if (eq ?*ag-in-debug* TRUE) then (printout t "   suntem in zona de pericol de animale in afara localitatii"  crlf) )
						;;(printout t "   suntem in zona de pericol de animale in afara localitatii"  crlf) 
					)
				)  
	 )
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   suntem in zona de pericol de animale"  crlf))
	 ;;(printout t "   suntem in zona de pericol de animale"  crlf)
     (retract ?f)
)

;--- Gps info intalnim indicatorul de atentionare la animale in localitate
(defrule AGENT::r-end-drum-animale-localitate-gps
     (declare (salience 5))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj gps_info) (percept_pname pericol_animale) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?def))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?r_t))
=>
     (modify ?s (bel_pval ?def))
     (modify ?d (bel_pval ?def))
     (modify ?l (bel_pval ?r_t))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am iesit de pe un drum cu atentionare la animale GPS"  crlf))
	 ;;(printout t "   am iesit de pe un drum cu atentionare la animale GPS"  crlf)
	 (retract ?f)
)


;--- semn indicator care arata viteza maxima admisa este 50 km/h
(defrule AGENT::r_viteza_maxima_50
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname viteza_maxima_50) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 50)))
     (if (eq ?val intra) then (modify ?d (bel_pval 50)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   Am intalnit un indicator care indica viteza maxima 50 km/h"  crlf))
	 ;;(printout t "   Am intalnit un indicator care indica viteza maxima 50 km/h"  crlf)
     (retract ?f)
)

;--- semn end indicator care arata viteza maxima admisa este 50 km/h
(defrule AGENT::r_semn_end_viteza_maxima_50
    (declare (salience 50)) ; Prioritate standard
    (timp (valoare ?t)) ; Capturăm timpul
    ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname viteza_maxima_50) (percept_pval paraseste)) ; Semn de ieșire
    ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit) (bel_pval ?sl)) ; Limită de viteză curentă
    ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def)) ; Limită implicită
    ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?rt)) ; Tipul drumului
=>
    (if (eq ?rt european)
        then 
            (modify ?s (bel_pval 100)) ; Setăm viteza curentă la 100
            (modify ?d (bel_pval 100)) ; Setăm viteza implicită la 100
            (if (eq ?*ag-in-debug* TRUE)
                then (printout t "   Drum european detectat: viteza setată la 100 km/h." crlf)))
    (if (neq ?rt european)
        then 
            (modify ?s (bel_pval ?def)) ; Revenim la valoarea implicită
            (if (eq ?*ag-in-debug* TRUE)
                then (printout t "   Drum non-european detectat: viteza resetată la valoarea implicită (" ?def ")." crlf)))
    (if (eq ?*ag-in-debug* TRUE)
        then (printout t "   Am ieșit din zona în care viteza maximă era 50 km/h la timpul: " ?t crlf))
    (retract ?f)
)



;--- semn indicator care arata viteza maxima admisa este 30km/h
(defrule AGENT::r_viteza_maxima_30
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname viteza_maxima_30) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     (if (eq ?val intra) then (modify ?s (bel_pval 30)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   Am intalnit un indicator care indica viteza maxima 30 km/h"  crlf))
	 ;;(printout t "   Am intalnit un indicator care indica viteza maxima 30 km/h"  crlf)
     (retract ?f)
)

;--- semn end indicator care arata viteza maxima admisa este 30km/h
(defrule AGENT::r_semn_end_viteza_maxima_30
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname viteza_maxima_30) (percept_pval paraseste))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
     ;;;(if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
	 (modify ?s (bel_pval ?def))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   Am iesit din zona in care viteza maxima era 30 km/h"  crlf))
	 ;;(printout t "   Am iesit din zona in care viteza maxima era 30 km/h"  crlf)
     (retract ?f)
)


;--- semn trecere pietoni semaforizata
(defrule AGENT::r_trecere_pietoni_semaforizata
	(declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname trecere_pietoni_semafor) (percept_pval ?val))
	 ?p <- (ag_percept (percept_pobj senzor_semafor_culoare) (percept_pname perceptie_semafor_culoare) (percept_pval ?culoare))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
=>
    (if (and (eq ?val intra) (or (eq ?culoare rosu) (eq ?culoare galben) ) ) then (modify ?s (bel_pval 0))
								(if (eq ?*ag-in-debug* TRUE) then (printout t "   suntem in asteptare la o trecere de pietoni semaforizata"  crlf) )
								;;(printout t "   suntem in asteptare la o trecere de pietoni semaforizata"  crlf) 
	)
     (if (and (eq ?val intra) (eq ?culoare verde) ) then (modify ?s (bel_pval 30)) 
								(if (eq ?*ag-in-debug* TRUE) then (printout t "   Semaforul indica culoarea verde"  crlf) )
								;;(printout t "   Semaforul indica culoarea verde"  crlf) 
	)
     ;;(if (eq ?val paraseste)  then (modify ?s (bel_pval ?def)))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   suntem in asteptare la o trecere de pietoni semaforizata"  crlf))
	 ;;(printout t "   suntem in asteptare la o trecere de pietoni semaforizata"  crlf)
     (retract ?f)
	 (retract ?p)
)

;--- semn end trecere pietoni semaforizata
(defrule AGENT::r_end_trecere_pietoni_semaforizata
	(declare (salience 50))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj car_sensor) (percept_pname trecere_pietoni_semafor) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?default))
=>
     (modify ?s (bel_pval ?default))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   am trecut de trecerea de pietoni semaforizata cu ajutorul senzorului "  crlf))
	 ;;(printout t "   am trecut de trecerea de pietoni semaforizata cu ajutorul senzorului "  crlf)
     (retract ?p)
)
	 

;--Senzorul de ninsoare ne atentioneaza ca incepe sa ninga
(defrule AGENT::r-snowing
     (declare (salience 40))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj snowing_sensor) (percept_pname is_snowing) (percept_pval true))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?road))
     ?i <- (ag_bel (bel_type fluent) (bel_pname in_locality) (bel_pval ?locality))
=>
    (if (eq ?road autostrada) then (modify ?s (bel_pval 50)) 
	 else
		(if (eq ?locality true) then (modify ?s (bel_pval 30)) 
			(if (eq ?*ag-in-debug* TRUE) then (printout t "   a inceput sa ninga in localitate"  crlf) )
			;;(printout t "   a inceput sa ninga in localitate"  crlf) 
		)
		(if (eq ?locality false) then (modify ?s (bel_pval 50)) 
			(if (eq ?*ag-in-debug* TRUE) then (printout t "   a inceput sa ninga in afara localitatii"  crlf) )
			;;(printout t "   a inceput sa ninga in afara localitatii"  crlf) 
		)
	)
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   a inceput sa ninga "  crlf))
	 ;;;(printout t "   a inceput sa ninga "  crlf)
     (retract ?p)
)

;--Senzorul de ninsoare ne atentioneaza ca NU mai ninge
(defrule AGENT::r-snow-stops
     (declare (salience 40))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj snowing_sensor) (percept_pname is_snowing) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?default))
=>
     (modify ?s (bel_pval ?default))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   a incetat ninsoarea "  crlf))
	 ;;(printout t "   a incetat ninsoarea "  crlf)
     (retract ?p)
)


;Trecere de pietoni in localitate + in afara localitatii _ sunt pietoni pe trecere
(defrule AGENT::r-trecere_de_pietoni
     (declare (salience 50))
     (timp (valoare ?t))
	 ?p <- (ag_percept (percept_pobj car_sensor) (percept_pname perceptie_pieton) (percept_pval walking))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname trecere_de_pietoni) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
	 ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?road))
	 ?i <- (ag_bel (bel_type fluent) (bel_pname in_locality) (bel_pval ?locality))
=>
	 ;(if (eq ?road autostrada) then (modify ?s (bel_pval 30)) 
	 ;else
	;	(if (eq ?locality true) then (modify ?s (bel_pval 30)) 
	;		(if (eq ?*ag-in-debug* TRUE) then (printout t "   Suntem la o trecere de pietoni in localitate"  crlf) )
	;		;;(printout t "   Suntem la o trecere de pietoni in localitate"  crlf) 
	;	)
	;	(if (eq ?locality false) then (modify ?s (bel_pval 30)) 
	;		(if (eq ?*ag-in-debug* TRUE) then (printout t "   Suntem la o trecere de pietoni in afara localitatii"  crlf) )
	;		;;(printout t "   Suntem la o trecere de pietoni in afara localitatii"  crlf) 
	;	)
     ;)
	 
	(if (eq ?val intra) then (modify ?s (bel_pval 0)) 
		(if (eq ?*ag-in-debug* TRUE) then (printout t "   Suntem la o trecere de pietoni in localitate si trec pietoni"  crlf))
	)
	 
	 (retract ?p)
     (retract ?f)
	 (retract ?p)
)


;--Trecere de pietoni in localitate + in afara localitatii _ e liber
(defrule AGENT::r-trecere_de_pietoni_liber
     (declare (salience 50))
     (timp (valoare ?t))
	 ?p <- (ag_percept (percept_pobj car_sensor) (percept_pname perceptie_pieton) (percept_pval all_clear))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname trecere_de_pietoni) (percept_pval ?val))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?def))
	 ?l <- (ag_bel (bel_type fluent) (bel_pname road_type) (bel_pval ?road))
	 ?i <- (ag_bel (bel_type fluent) (bel_pname in_locality) (bel_pval ?locality))
=>
	 (if (eq ?road autostrada) then (modify ?s (bel_pval 30)) 
	 else
		(if (eq ?locality true) then (modify ?s (bel_pval 30)) 
			(if (eq ?*ag-in-debug* TRUE) then (printout t "   Suntem la o trecere de pietoni in localitate"  crlf) )
			;;(printout t "   Suntem la o trecere de pietoni in localitate"  crlf) 
		)
		(if (eq ?locality false) then (modify ?s (bel_pval 30)) 
			(if (eq ?*ag-in-debug* TRUE) then (printout t "   Suntem la o trecere de pietoni in afara localitatii"  crlf) )
			;;(printout t "   Suntem la o trecere de pietoni in afara localitatii"  crlf) 
		)
     )
    
	(if (eq ?val intra) then (modify ?s (bel_pval 30)) 
		(if (eq ?*ag-in-debug* TRUE) then (printout t "   Suntem la o trecere de pietoni in localitate si este liber"  crlf))
	)
	 
	 (retract ?p)
     (retract ?f)
	 (retract ?p)
)


;semn end trecere de pietoni in localitate + in afara localitatii senzor
(defrule AGENT::r-semn-end_trecere_de_pietoni_sensor
     (declare (salience 50))
     (timp (valoare ?t))
     ?p <- (ag_percept (percept_pobj car_sensor) (percept_pname trecere_de_pietoni) (percept_pval false))
     ?s <- (ag_bel (bel_type fluent) (bel_pname speeding-limit)(bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default) (bel_pval ?default))
=>
     (modify ?s (bel_pval ?default))
     (if (eq ?*ag-in-debug* TRUE) then (printout t "   Am trecut de o trecere de pietoni "  crlf))
	 ;;(printout t "   Am trecut de o trecere de pietoni din localitate "  crlf)
     (retract ?p)
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;










;--- End of all restrictions
(defrule AGENT::r-incetare-tuturor-restrictiilor
     (declare (salience 50))
     (timp (valoare ?t))
     ?f <- (ag_percept (percept_pobj semn_de_circulatie) (percept_pname restrictions) (percept_pval iesire))
     ?s <- (ag_bel (bel_type fluent)(bel_pname speeding-limit) (bel_pval ?))
     ?d <- (ag_bel (bel_type fluent) (bel_pname speeding-default)(bel_pval ?def))
=>
     (if (eq ?*ag-in-debug* TRUE) then (printout t " toate restrictiile intrerupte" crlf))
     (modify ?s (bel_pval ?def))
     (retract ?f)
)

;;---------------------------------------
;;
;;      End made by us
;;
;;---------------------------------------

;
;--------Print decision-----------------------------------

(defrule AGENT::tell
    (declare (salience -50))
    (timp (valoare ?)) ;make sure it fires each cycle
    (ASK ?bprop)
    ?fcvd <- (ag_bel (bel_type fluent) (bel_pname ?bprop) (bel_pval ?bval))
=>
    (printout t "         AGENT " ?bprop " " ?bval crlf)
   ;(retract ?fcvd)
)


;
;---------Housekeeping----------------------------------
;

;---------Delete auxiliary facts----------

;---------Delete instantaneous beliefs, i.e, those which are not fluents
;(defrule AGENT::hk-eliminate-momentan-current-bel
;    (declare (salience -90))
;    (timp (valoare ?)) ;make sure it fires each cycle
;    ?fmcb <- (ag_bel (bel_type moment) (bel_timeslice 0) (bel_pname ?p) (bel_pval ?v))
;=>
;    (if (eq ?*ag-in-debug* TRUE) then (printout t "    <D>hk-eliminate-momentan-current-bel " ?p " " ?v crlf))
;    (retract ?fmcb)
;)


;
;---------measure running time 
;
(defrule AGENT::time_end
  (declare (salience -92))
  ?fsta <- (tstart ?time_start)
=>
  (bind ?time_end (time))
  (bind ?ex_time (- ?time_end ?time_start))
  (if (eq ?*ag-measure-time* TRUE) then (printout t "            <M> AGENT Decision time: " ?ex_time " sec." crlf))
  (retract ?fsta))


