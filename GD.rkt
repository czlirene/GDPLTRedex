#lang scheme
(require redex)
(require racket/trace)

;;; TO DO LIST
; + Root Subject
;;; - Root in insert-priv
; - Basic Rights (Done)
; + Administrative Rights
;;; - transfer_own
; - Create/Delete Obj (done)
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
(define s2 (term (sub 2)))

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

; s0 own o0, s0 read o0, s0 read o1, s1 read o0, s1 write o1
;;; (define m7 (term ((,s0 own ,o0) (,s0 ,r1 ,o0) (,s0 ,r1 ,o1) (,s1 ,r2 ,o1))))
(define m7 (term ((,s0 own ,o0) (,s0 ,r1 ,o0) (,s0 ,r1 ,o1) (,s1 own ,s0) (,s1 ,r2 ,o1))))

(define m9 (term ((,s1 own ,o0) (,s1 ,r2 ,o1))))

; s0 read o1, s1 write o1
(define m8 (term ((,s0 ,r1 ,o1) (,s1 ,r2 ,o1))))


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
(define st5 
  (term (st 2 2 (,s0 ,s1) (,o0 ,o1) ,br ,m5)))
(define st6 
  (term (st 2 2 (,s0 ,s1) (,o0 ,o1) ,br ,m6)))

;;; Testing destroy-obj
(define st7 
  (term (st 2 2 (,s0 ,s1) (,o0 ,o1) ,br ,m7)))

(define st8 
  (term (st 2 1 (,s0 ,s1) (,o1)     ,br ,m8)))

;;; Testing destroy-sub
(define st9 
  (term (st 1 2 (,s1) (,o0 ,o1) ,br ,m9)))

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
  (--> (st natural_1 natural_2 S O R M_1)
       (st natural_1 natural_2 S O R M_2)

       ; find any Sub_O (o)
       (where (Sub_X ... Sub_O Sub_Y ...) S)
       ; find any Sub_S (s)
       (where (Sub_X ... Sub_S Sub_Y ...) S)
       ; find any Sub_1 (i) owns Sub_O (o)
       (where (Priv_1 ... (Sub_1 own Sub_O) Priv_2 ...) M_1)

       ; Insert-control
       (where M_2 ,(insert-control (term Sub_S) (term Sub_O) (term M_1)))

       ; Give this transition a name
       (computed-name (term (grant-control Sub_1 Sub_S Sub_O)))

  )

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
       (computed-name (term (grant-own Sub_1 Sub_2 PObj)))
  )
  

  ; transfer_own(i,s,o)
  ;;; TODO

  ; <------------------------- BEGIN: Create/Destroy Object ------------------------->
  ; create_object(i,o)
  (--> (st natural_1 natural_2
          S (PObj ...)
          R M_1)
       (st natural_1 ,(+  1 (term natural_2))
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
  (--> (st natural_1 natural_2 S O_1 R M_1)
       ; Decrement ObjCount by 1, 
       (st natural_1 ,(- (term natural_2) 1) S O_2 R M_2)

       ; Find any Obj (o)
       (where (PObj_1 ... Obj PObj_2 ...) O_1)
       ; Find any Sub_1 (i) that owns Obj
       (where (Priv_1 ... (Sub_1 own Obj) Priv_2 ...) M_1)

       ; Remove all the rights pertaining to Obj
       (where M_2 ,(remove-obj (term Obj) (term M_1)))

       ; Update O with the new list of PObjs
       (where O_2 ,(remove (term Obj) (term O_1)))

       ; Give this transition a name
       (computed-name (term (destroy-object Sub_1 Obj)))
  )

  ; destroy_subject(i,s)
  (--> (st natural_1 natural_2 S_1 O R M_1)
       (st ,(- (term natural_1) 1) natural_2 S_2 O R M_2)

       ; For every Sub_1 and Sub_2 that are Subjects
       (where (Sub_X ... Sub_2 Sub_Y ...) S_1)
       (where (Sub_Z ... Sub_1 Sub_V ...) S_1)

       ; Find a Sub_1 (i) that owns Sub_2 (s)
       (where (Priv_1 ... (Sub_1 own Sub_2) Priv_2 ...) M_1)

       ; Transfer all Sub_2 own objects to Sub_1
       (where M_2 ,(replace-sub (term Sub_1) (term Sub_2) (term M_1)))

       ; Update S with the new list of subject
       (where S_2 ,(remove (term Sub_2) (term S_1)))

       ; Give this transition a name
       (computed-name (term (destroy-subject Sub_1 Sub_2)))
  )
  )
)

;  <------------------------- BEGIN: Helper Functions ------------------------->
(define (insert-control sub obj matrix)
  (case (check-control sub obj matrix)
    ; found another controller, return matrix as it is
    [(-1) matrix]  
    ; No controller found, insert priv
    [( 0) (insert-priv (list sub 'control obj) matrix)]
  )
)

(define (check-control sub obj matrix)
  ; if we reached the end of the matrix, then that means no other ctrler is found
  (if (or (null? matrix)
          (null? (rest matrix)))
      (term 0)
      ; otherwise
      (case (find-control sub obj (first matrix))
        ; found another controller
        [(-1) (term -1)]
        ; Didn't find anything yet, go to the next one
        [(+1) (check-control sub obj (rest matrix))]
      )
  )
)

(define (find-control sub obj priv)
  (let ([s1 (first priv)]
        [r1 (second priv)]
        [o1 (third priv)])
    (cond 
        ; r1 = control, o1 = obj, s1 != o1 means ANOTHER CONTROLLER
        [(and 
            (eqv? r1 'control)
            (eqv? o1 obj)
            (not (eqv? s1 o1)))   -1]
        ; otherwise, check next
        [else                     +1]
    )
  )
)

;1 compile list of all the objs del owned
;2 remove all rights (del r o)
;3 insert sub own objs based on list from 1

(define (replace-sub sub del matrix)
  (if (null? matrix)
      (remove null matrix)
      (let ([own-list (list-sub-own del matrix)])
          (let ([new-own-matrix (add-sub-own sub own-list matrix)])
              (remove-sub del new-own-matrix)
          )
      )
  )
)
; (trace replace-sub)

; for every obj in obj-list, insert priv
(define (add-sub-own sub obj-list matrix)
  (if (null? matrix)
      (remove null matrix)
      (case (null? obj-list)
        [(#true ) matrix]
        [(#false) (add-sub-own sub (rest obj-list) (insert-priv (list sub 'own (first obj-list)) matrix))]
      )
  )
)
;;; (trace add-sub-own)

; return list of all the obj del owns
(define (list-sub-own sub matrix)
  (if (null? matrix)
      (remove null matrix)
      (case (find-sub-own sub (car matrix))
        ; -1: Not owned by sub, remove it from matrix
        [(-1) (list-sub-own sub (cdr matrix))]
        ;  0: done, return matrix
        [( 0) matrix]
        ; +1: Owned by sub, keep it and go to next 
        [(+1) (cons (third (car matrix)) (list-sub-own sub (cdr matrix)))]
      )
  )
)
;;; (trace list-sub-own)

(define (find-sub-own sub priv)
  (if (null? priv)
      (0)
      (let ([s1 (first priv)]
            [r1 (second priv)])
          (cond 
            [(and 
              (eqv? s1 sub)
              (eqv? r1 'own)) +1]
            [else            -1]
          )
      )
  )
)

; step2 - THIS IS THE LAST PART, will return back a SUB_2-less matrix
(define (remove-sub sub matrix)
  (if (null? matrix)
      (remove null matrix)
      (case (find-sub sub (car matrix))
        ; -1: Remove the current priv
        [(-1) (remove-sub sub (cdr matrix))]
        ;  0: done, return matrix
        [( 0) matrix]
        ; +1: Not related to sub, go to next
        [(+1) (cons (car matrix) (remove-sub sub (cdr matrix)))]
      )
  )
)
; (trace remove-sub)

(define (find-sub sub priv)
  (if (null? priv)
      (0)
      (let ([s1 (first priv)]
            [r1 (second priv)]
            [o1 (third priv)])
          (cond 
            [(or 
                (eqv? s1 sub)
                (and (eqv? r1 'own)
                     (eqv? o1 sub))) -1]
            [else                    +1]
          )
      )
  )
)
; (trace find-sub)

(define (remove-obj obj matrix)
  (if (null? matrix)
      (remove null matrix)
      (case (find-obj obj (car matrix))
        ; -1: Remove the current priv
        [(-1) (remove-obj obj (cdr matrix))]
        ;  0: Done, return matrix
        [( 0) matrix]
        ; +1: Not the obj I want, go to next
        [(+1) (cons (car matrix) (remove-obj obj (cdr matrix)))]
      )
  )
)
;(trace remove-obj)

(define (find-obj obj priv)
  (if (null? priv)
      (0)
      (let ([o1 (third priv)])
          (cond 
            [(eqv? o1 obj) -1]
            [else          +1]
          )
      )
  )
)
;(trace find-obj)

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


; (module+ test
;   ;;; (test-->>E #:steps 1 red st1 st3)
;   ;;; (test-->>E #:steps 1 red st1 st2)
;   ;;; (test-->>E #:steps 1 red st2 st4)
;   ;;; (test-->>E #:steps 2 red st1 st4)
;   ;;; (test-->>E #:steps 1 red st5 st6)     ; testing delete_r(own)
;   ;;; (test-->>E #:steps 1 red st6 st5)     ; testing grant_r
; ;  (test-->>E #:steps 1 red st7 st8)     ; testing destroy-obj
;   ; (test-->>E #:steps 1 red st7 st9)
; )

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
;;; (define (gd-wf-2? obj-list priv-list)
;;;   (or (null? priv-list)
;;;       (let* ([priv (first priv-list)]
;;;              [right (second priv)]
;;;              [obj (third priv)])
;;;           (and (member obj obj-list)
;;;                (not (eq? right control))
;;;                (gd-wf-2? obj-list (rest priv-list))
;;;           )
;;;       )
;;;   )
;;; )

(module+ test
  (test-equal (well-formed-state? st1) #true)
  (test-equal (well-formed-state? st2) #true)
  (test-equal (well-formed-state? st3) #true)
  (test-equal (well-formed-state? st4) #true)
)


(module+ test
  (test-results)
)