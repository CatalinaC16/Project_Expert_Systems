(deffacts PERCEPT-MANAGER::timp
    (timp (valoare 0))
)
; added 

(deffacts PERCEPT-MANAGER::speeding
    (speeding (speed 21) (default 30))
)

(deffacts MAIN::succesiune-module
   (secventa PERCEPT-MANAGER AGENT)
)
