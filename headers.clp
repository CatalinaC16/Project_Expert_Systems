;
;----------Modul: MAIN-------------
;
(defmodule MAIN
    (export deftemplate tic)
)

(deftemplate MAIN::tic)

(defglobal ?*main-in-debug* = FALSE)
;(defglobal ?*main-in-debug* = TRUE)
(defglobal ?*ag-tic-in-debug* = FALSE)
;(defglobal ?*ag-tic-in-debug* = TRUE)

;
;----------Modul: PERCEPT-MANAGER-----------
;
(defmodule PERCEPT-MANAGER
 (import MAIN deftemplate tic)
 (export deftemplate timp)
 (export deftemplate speeding)
 (export deftemplate ag_percept)
)


(defglobal ?*sim-in-debug* = FALSE)
;(defglobal ?*sim-in-debug* = TRUE)
(defglobal ?*percepts-in-debug* = FALSE)
;(defglobal ?*percepts-in-debug* = TRUE)

;(defglobal ?*perceptsDir* = "./scenariu1/")
;(defglobal ?*perceptsDir* = "./scenariu2/")
;(defglobal ?*perceptsDir* = "./scenariu3/")
;(defglobal ?*perceptsDir* = "./scenariu4/")
;(defglobal ?*perceptsDir* = "./scenariu5/")
(defglobal ?*perceptsDir* = "./scenariu6/")


(deftemplate PERCEPT-MANAGER::timp (slot valoare))

(deftemplate PERCEPT-MANAGER::speeding (slot speed)(slot default))

(deftemplate PERCEPT-MANAGER::ag_percept
    (slot percept_pname) ; animal|indicator|marcaj|GPS-info
    (slot percept_pval); albina|barza|... or depasire_interzisa|... or (linie_continua|...)
    (slot percept_pobj); left|right|ahead|speed_value
    (slot percept_pdistance (default nil)) ;; Distanța față de obiect (opțional, implicit nil)
)
;
;-------------Modul: DRIVER-AGENT
;
(defmodule AGENT
    (import PERCEPT-MANAGER deftemplate timp)
    (import PERCEPT-MANAGER deftemplate speeding)
    (import PERCEPT-MANAGER deftemplate ag_percept)
)

(defglobal ?*ag-in-debug* = FALSE)
;(defglobal ?*ag-in-debug* = TRUE)


(defglobal ?*ag-percepts-in-debug* = FALSE)
;(defglobal ?*ag-percepts-in-debug* = TRUE)


(defglobal ?*ag-measure-time* = FALSE)
;(defglobal ?*ag-measure-time* = TRUE)

(deftemplate ag_bel
    (slot bel_type) ; fluent|moment
    (slot bel_timeslice) ; in which time slice bel_type is true: 0=crt, 1,2,...=future
    (slot bel_pname) ; which property we're talking about: overtaking-maneuver|no-overtaking-zone|speed_limit
    (slot bel_pval) ; bel_pname value: (prohibited|allowed) or (yes|no) or (50|90|100|130)
    (slot bel_pobj); left|right|ahead
    (slot bel_pdistance (default nil)) ;
)
