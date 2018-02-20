#lang scheme
(require redex)

;;; TO DO LIST
; + Root Subject
;;; - Root in insert-priv
; - Basic Rights (Done)
; + Administrative Rights
;;; - grant_control
;;; - transfer_own
; + Create/Delete Obj 
;;; - destroy_object
;;; - destroy_subject
; + Well-formness 
;;; GDWF1
;;; GDWF2
;;; GDWF3
;;; GDWF4
;;; GDWF5
;;; GDWF6
;;; GDWF7

(define-language GD
  [Root  root]
  [NRSub (sub natural)]
  [Sub   Root
         NRSub]
  [PObj  (obj natural)]
  [Obj   Sub
         PObj]
  [AR    own
         control]
  [BR    (variable-except own control)]
  [TR    (trans BR)]
  [Right BR
         AR
         TR]
  [Priv  (Sub Right Obj)]
  [S     (Sub ...)]
  [O     (PObj ...)]
  [R     (BR ...)]
  [M     (Priv ...)]
  [State (st natural natural S O R M)]
)

(define s0 (term (sub 0)))
(define s1 (term (sub 1)))

(define o0 (term (obj 0)))
(define o1 (term (obj 1)))
(define o2 (term (obj 2)))
(define o3 (term (obj 3)))

(define r1 (term read))
(define r2 (term write))

(define br (term (,r1 ,r2)))

(define m1 (term ((,s0 (trans ,r1) ,o0) (,s1 ,r2 ,o1))))
(define m2 (term ((,s0 (trans ,r1) ,o0) (,s1 ,r2 ,o1) (,s1 own ,o2))))
(define m3 (term ((,s0 (trans ,r1) ,o0) (,s1 ,r1 ,o0) (,s1 ,r2, o1))))
(define m4 (term ((,s0 (trans ,r1) ,o0) (,s0 own ,o3) (,s1 ,r2 ,o1) (,s1 own ,o2))))

; s0 own o0, s0 own o1, s0 own s1, s0 tRead o0, s1 read o1
(define m5 (term ((,s0 own ,o0) (,s0 own ,o1) (,s0 own ,s1) (,s0 (trans ,r1) ,o0) (,s1 ,r1 ,o1))))
; s0 own o0, s0 own o1, s0 own s1, s0 tRead o0 
(define m6 (term ((,s0 own ,o0) (,s0 own ,o1) (,s0 own ,s1) (,s0 (trans ,r1) ,o0) )))


(module+ test
  (test-equal (redex-match? GD Sub s0) #true)
  (test-equal (redex-match? GD Sub s1) #true)
  (test-equal (redex-match? GD Obj o0) #true)
  (test-equal (redex-match? GD Obj o1) #true)
  (test-equal (redex-match? GD Obj o2) #true)
  (test-equal (redex-match? GD Obj o3) #true)
  (test-equal (redex-match? GD BR r1) #true)
  (test-equal (redex-match? GD BR r2) #true)
  (test-equal (redex-match? GD M m1) #true)
  (test-equal (redex-match? GD M m2) #true)
  (test-equal (redex-match? GD M m3) #true)
  (test-equal (redex-match? GD M m4) #true)
  (test-equal (redex-match? GD State st1) #true)
  (test-equal (redex-match? GD State st2) #true)
  (test-equal (redex-match? GD State st3) #true)
  (test-equal (redex-match? GD State st4) #true)
)

(module+ test
  (test-equal (insert-priv (list s1 r1 o0) m1) m3)
  (test-equal (insert-priv (list s1 'own o2) m1) m2)
  (test-equal (insert-priv (list s0 'own o3) m2) m4)
)

(define st1
  (term (st 2 2 (,s0 ,s1) (,o0 ,o1) ,br ,m1)))

(define st2
  (term (st 2 3 (,s0 ,s1) (,o0 ,o1 ,o2) ,br ,m2)))

(define st3
  (term (st 2 2 (,s0 ,s1) (,o0, o1) ,br ,m3)))
            
(define st4
  (term (st 2 4 (,s0 ,s1) (,o0 ,o1 ,o2 ,o3) ,br ,m4)))

;;; Testing delete_r(Own)
(define st5 (term (st 2 2 (,s0 ,s1) (,o0 ,o1) ,br ,m5)))
(define st6 (term (st 2 2 (,s0 ,s1) (,o0 ,o1) ,br ,m6)))

(define red
  (reduction-relation GD
  ; NOTES:
  ; (--> {Original state} {Resulting state} {pattern matching} )
  ; (st {Subject count} {PObj count} S O R M)

  ; <------------------------- BEGIN: Basic Rights ------------------------->
  ; grant_r (i,s,o)
  (--> (st natural_1 natural_2 S O R M_1)
       (st natural_1 natural_2 S O R M_2)

       ; Find a Sub_1 (i) that owns Obj (o)
       (where (Priv_1 ... (Sub_1 own Obj) Priv_2 ...) M_1)
       ; Find any Sub_2 (s)
       (where (Sub_3 ... Sub_2 Sub_4 ...) S)
       ; Find a BR in R (r) to grant
       (where (BR_1 ... BR BR_2 ...) R)

       ; Insert priv to new matrix M_2
       (where M_2 ,(insert-priv (term (Sub_2 BR Obj)) (term M_1)))

       ; Give this transition a name
       (computed-name (term (grant BR Sub_1 Sub_2 Obj)))
  )
  
  ; delete_r [OWN] (i,s,o)
  (--> (st natural_1 natural_2 S O R M_1)
       (st natural_1 natural_2 S O R M_2)

       ; Find a Sub_1 (i) that owns Obj (o)
       (where (Priv_1 ... (Sub_1 own Obj) Priv_2 ...) M_1)
       ; Find any Sub_2 (s) 
       (where (Sub_3 ... Sub_2 Sub_4 ...) S)
       ; Find a BR in R (r) to delete
       (where (BR_1 ... BR BR_2 ...) R)

       ; Remove priv from the matrix, assign it to M_2
       (where M_2 ,(remove (term (Sub_2 BR Obj)) (term M_1)))

       ; Give this transition a name
       (computed-name (term (remove-own BR Sub_1 Sub_2 Obj)))
  )

  ; delete_r [CONTROL] (i,s,o)
  (--> (st natural_1 natural_2 S O R M_1)
       (st natural_1 natural_2 S O R M_2)

       ; Find a Sub_1 (i) that controls Sub_2 (s)
       (where (Priv_1 ... (Sub_1 control Sub_2) Priv_2 ...) M_1)
       ; Find any Obj (o)
       (where (Obj_1 ... Obj Obj_2 ...) O)
       ; Find a BR in R (r) to delete
       (where (BR_1 ... BR BR_2 ...) R)

       ; Remove priv from the matrix, assign it to M_2
       (where M_2 ,(remove (term (Sub_2 BR Obj)) (term M_1)))

       ; Give this transition a name
       (computed-name (term (remove-control BR Sub_1 Sub_2 Obj)))
  )

  ; transfer_r(i,s,o)
  (--> (st natural_1 natural_2 S O R M_1)
       (st natural_1 natural_2 S O R M_2)

       (where (Priv_1 ... (Sub_1 (trans BR) Obj) Priv_2 ...) M_1)
       (where (Sub_3 ... Sub_2 Sub_4 ...) S)
       (where M_2 ,(insert-priv (term (Sub_2 BR Obj)) (term M_1)))
       (computed-name (term (transfer BR Sub_1 Sub_2 Obj)))
  )

  ; <------------------------- BEGIN: Basic TR Rights ------------------------->
  ; grant_r* (i,s,o)
  (--> (st natural_1 natural_2 S O R M_1)
       (st natural_1 natural_2 S O R M_2)

       ; Find a Sub_1 (i) that owns Obj (o)
       (where (Priv_1 ... (Sub_1 own Obj) Priv_2 ...) M_1)
       ; Find any Sub_2 (s)
       (where (Sub_3 ... Sub_2 Sub_4 ...) S)
       ; Find a BR in R (r) to grant
       (where (BR_1 ... BR BR_2 ...) R)

       ; Insert priv to new matrix M_2
       (where M_2 ,(insert-priv (term (Sub_2 (trans BR) Obj)) (term M_1)))

       ; Give this transition a name
       (computed-name (term (grant (trans BR) Sub_1 Sub_2 Obj)))
  )
  
  ; delete_r* [OWN] (i,s,o)
  (--> (st natural_1 natural_2 S O R M_1)
       (st natural_1 natural_2 S O R M_2)

       ; Find a Sub_1 (i) that owns Obj (o)
       (where (Priv_1 ... (Sub_1 own Obj) Priv_2 ...) M_1)
       ; Find any Sub_2 (s) 
       (where (Sub_3 ... Sub_2 Sub_4 ...) S)
       ; Find a BR in R (r) to delete
       (where (BR_1 ... BR BR_2 ...) R)

       ; Remove priv from the matrix, assign it to M_2
       (where M_2 ,(remove (term (Sub_2 (trans BR) Obj)) (term M_1)))

       ; Give this transition a name
       (computed-name (term (remove-own (trans BR) Sub_1 Sub_2 Obj)))
  )

  ; delete_r* [CONTROL] (i,s,o)
  (--> (st natural_1 natural_2 S O R M_1)
       (st natural_1 natural_2 S O R M_2)

       ; Find a Sub_1 (i) that controls Sub_2 (s)
       (where (Priv_1 ... (Sub_1 control Sub_2) Priv_2 ...) M_1)
       ; Find any Obj (o)
       (where (Obj_1 ... Obj Obj_2 ...) O)
       ; Find a BR in R (r) to delete
       (where (BR_1 ... BR BR_2 ...) R)

       ; Remove priv from the matrix, assign it to M_2
       (where M_2 ,(remove (term (Sub_2 (trans BR) Obj)) (term M_1)))

       ; Give this transition a name
       (computed-name (term (remove-control (trans BR) Sub_1 Sub_2 Obj)))
  )

  ; transfer_r*(i,s,o)
  (--> (st natural_1 natural_2 S O R M_1)
       (st natural_1 natural_2 S O R M_2)

       ; Find a Sub_1 (i) that has the r* to Obj (o)
       (where (Priv_1 ... (Sub_1 (trans BR) Obj) Priv_2 ...) M_1)
       ; Find any Sub_2 (s)
       (where (Sub_3 ... Sub_2 Sub_4 ...) S)
       
       ; Insert priv, assign it to M_2
       (where M_2 ,(insert-priv (term (Sub_2 (trans BR) Obj)) (term M_1)))

       (computed-name (term (transfer (trans BR) Sub_1 Sub_2 Obj)))
  )

  ; <------------------------- BEGIN: Administrative Rights ------------------------->
  ; grant_control(i,s,o)

  ; grant_own(i,s,o)
  (--> (st natural_1 natural_2 S O R M_1)
       (st natural_1 natural_2 S O R M_2)

       ; Find any PObj (o)
       (where (Obj_1 ... PObj Obj_2 ...) O)
       ; Find a Sub_1 (i) that owns PObj(o)
       (where (Priv_1 ... (Sub_1 own PObj) Priv_2 ...) M_1)
       ; Find any Sub_2 (s)
       (where (Sub_3 ... Sub_2 Sub_4 ...) S)
       
       ; Insert priv, assign it to M_2
       (where M_2 ,(insert-priv (term (Sub_2 own PObj)) (term M_1)))

       ; Give this trnx a name
       (computed-name (term (grant-own Sub_1 Sub_2 PObj))))
  )

  ; transfer_own(i,s,o)

  ; <------------------------- BEGIN: Create/Destroy Object ------------------------->
  ; create_object(i,o)
  (--> (st natural_1 natural_2
          S (PObj ...)
          R M_1)
       (st natural_1 ,(+ 1 (term natural_2))
          S (PObj ... (obj natural_2))
          R M_2)
       (where (Sub_1 ... Sub_2 Sub_3 ...) S)
       (where M_2 ,(insert-priv (term (Sub_2 own (obj natural_2)))
                                (term M_1)))
       (computed-name (term (create-object Sub_2 (obj natural_2))))
  )

; create_subject(i,s)
  (--> (st natural_1 natural_2 (Sub ...) O R M_1)
       ; Increment SubCount by 1, add another Sub into S
       (st ,(+ 1 (term natural_1)) natural_2 (Sub ... (sub natural_1)) O R M_2)

       ; Find any Sub_1 (i)
       (where (Sub_2 ... Sub_1 Sub_3 ...) (Sub ...))
       
       ; Insert (Sub_1 own (new sub)) and ((new sub) control (new sub)) into M_2
       (where M_2 ,(insert-priv (term ((sub natural_1) control (sub natural_1))) (insert-priv (term (Sub_1 own (sub natural_1))) (term M_1))))

       ; Give this transition a name
       (computed-name (term (create-subject Sub_1 (sub natural_1))))
  )

  ; destroy_object(i,o)

  ; destroy_subject(i,s)
  )
)

(define (insert-priv priv matrix)
  (if (null? matrix)
      (list priv)
      (case (priv-comp priv (car matrix))
        [(-1) (cons priv matrix)]
        [( 0) matrix]
        [(+1) (cons (car matrix) (insert-priv priv (cdr matrix)))])))

(define (right-comp r1 r2)
  (if (symbol? r1)
      (if (symbol? r2)
          (let ([s1 (symbol->string r1)]
                [s2 (symbol->string r2)])
            (cond
              [(string<? s1 s2) -1]
              [(string>? s1 s2) +1]
              [else              0]))
          -1)
      (if (symbol? r2)
          +1
          (right-comp (second r1) (second r2)))))

(define (priv-comp priv1 priv2)
  (let ([s1 (first priv1)]
        [r1 (second priv1)]
        [o1 (third priv1)]
        [s2 (first priv2)]
        [r2 (second priv2)]
        [o2 (third priv2)])
    (cond
      [(< (second s1) (second s2)) -1]
      [(> (second s1) (second s2)) +1]
      [(and
        (eqv? (first o1) 'sub)
        (not (eqv? (first o2) 'sub))) -1]
      [(and
        (not (eqv? (first o1) 'sub))
        (eqv? (first o2) 'sub)) +1]
      [(< (second o1) (second o2)) -1]
      [(> (second o1) (second o2)) +1]
      [else (right-comp r1 r2)])))


(module+ test
  (test-->>E #:steps 1 red st1 st3)
  (test-->>E #:steps 1 red st1 st2)
  (test-->>E #:steps 1 red st2 st4)
  (test-->>E #:steps 2 red st1 st4)
  (test-->>E #:steps 1 red st5 st6)     ; testing delete_r(own)
  (test-->>E #:steps 1 red st6 st5)     ; testing grant_r
)

(define (well-formed-so-list? so-count so-list)
  (or (null? so-list)
      (and (< (second (first so-list)) so-count)
           (well-formed-so-list? so-count (rest so-list)))))

(define (sorted-so-list? so-list)
  (or (null? so-list)
      (null? (rest so-list))
      (and (< (second (first so-list))
              (second (second so-list)))
           (sorted-so-list? (rest so-list)))))

(define (well-formed-priv-list? sub-list obj-list priv-list)
  (or (null? priv-list)
      (let* ([priv (first priv-list)]
             [sub  (first priv)]
             [obj  (third priv)])
        (and (member sub sub-list)
             (or (member obj sub-list)
                 (member obj obj-list))
             (well-formed-priv-list? sub-list obj-list (rest priv-list))))))

(define (sorted-priv-list? priv-list)
  (or (null? priv-list)
      (null? (rest priv-list))
      (let ([priv1 (first priv-list)]
            [priv2 (second priv-list)])
        (and (< (priv-comp priv1 priv2) 0)
             (sorted-priv-list? (rest priv-list))))))
                            
(define (well-formed-state? state)
  (let ([sub-count (second state)]
        [obj-count (third state)]
        [sub-list (fourth state)]
        [obj-list (fifth state)]
        [priv-list (seventh state)])
    (and (well-formed-so-list? sub-count sub-list)
         (sorted-so-list? sub-list)
         (well-formed-so-list? obj-count obj-list)
         (sorted-so-list? obj-list)
         (well-formed-priv-list? sub-list obj-list priv-list)
         (sorted-priv-list? priv-list))))

; <------------------------- BEGIN: GD-WF-# ------------------------->
; 1. Every PObj is owned by at least one Sub

; 2. No PObj is controlled
(define (gd-wf-2? obj-list priv-list)
  (or (null? priv-list)
      (let* ([priv (first priv-list)]
             [right (second priv)]
             [obj (third priv)])
          (and (member obj obj-list)
               (not (eq? right control))
               (gd-wf-2? obj-list (rest priv-list))
          )
      )
  )
)

(module+ test
  (test-equal (well-formed-state? st1) #true)
  (test-equal (well-formed-state? st2) #true)
  (test-equal (well-formed-state? st3) #true)
  (test-equal (well-formed-state? st4) #true)
)


(module+ test
  (test-results))
