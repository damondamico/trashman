#lang plai/gc2/collector

(print-only-errors)

#|
flat:    ... | 'flat | <payload>   | ...
cons:    ... | 'cons | <first-ptr> | <rest-ptr> | ...
closure: ... | 'clos | <code-ptr>  | <n-fvs> | <fv0> | <fv1> | ... | ...
forward: ... | 'f    | <forward-ptr> | ...
|#

#|
First 4 addresses are state variables
0: Allocation pointer
1: Pointer to start of from-space
2: GC queue start
3: GC queue end
|#

(define (init-allocator)
  (heap-set! 0 4)
  (heap-set! 1 4) ; will only ever be 4 or (heap-size/2) + 2
  ) ; all other cells are empty until allocated

;; malloc : size -> address
(define (malloc n roots1 roots2)
  (define address (heap-ref 0))
  (define freeSpace
    (if (equal? (heap-ref 1) 4)
        (- (+ (/ (heap-size) 2) 2) address)
        (- (heap-size) address)))
  (cond
    [(>= freeSpace n)
     (heap-set! 0 (+ address n))
     address]
    [else
     (trash-man roots1 roots2)
     (define address (heap-ref 0))
     (define freeSpace
       (if (equal? (heap-ref 1) 4)
           (- (+ (/ (heap-size) 2) 2) address)
           (- (heap-size) address)))
     (cond
       [(>= freeSpace n)
        (heap-set! 0 (+ address n))
        address]
       [else
        (error 'malloc "out of memory")])
     ]))

;; GARBAGE COLLECTOR
(define (trash-man roots1 roots2)
  ;; Preliminary check
  ;(validate-heap)
  (reset-queue)
  
  ;; Process roots to start gc queue
  (traverse/roots (get-root-set))
  (traverse/roots roots1)
  (traverse/roots roots2)

  ;; Go through queue
  (process-queue)
 
  
  ;; Update state variables
  (heap-set! 0 (heap-ref 3))
  (if (equal? (heap-ref 1) 4)
      (heap-set! 1 (+ (/ (heap-size) 2) 2))
      (heap-set! 1 4))

  ;; Last check
  ;(validate-heap))
  )


(define (reset-queue) ;; reset the queue to the start of the to-space
  (cond
      [(equal? (heap-ref 1) 4)
       (heap-set! 2 (+ (/ (heap-size) 2) 2))
       (heap-set! 3 (+ (/ (heap-size) 2) 2))]
      [else
       (heap-set! 2 4)
       (heap-set! 3 4)]))

(define (validate-heap) 
  (define (validate-pointer ptr)
    (if (equal? (heap-ref 1) 4)
        (unless (and (number? ptr)
                     (< ptr (+ (/ (heap-size) 2) 2))
                     (>= ptr 4)
                     (member (heap-ref ptr) '(flat cons clos)))
          (error 'validate-pointer "invalid pointer: ~a" ptr))
        (unless (and (number? ptr)
                     (< ptr (heap-size))
                     (>= ptr (+ (/ (heap-size) 2) 2))
                     (member (heap-ref ptr) '(flat cons clos)))
          (error 'validate-pointer "invalid pointer: ~a" ptr))))
  (define (loop address)
    (when (< address (heap-ref 0)) ; all memory up to allocation state var should be full
      (case (heap-ref address)
        [(flat)
         (loop (+ address 2))]
        [(cons)
         (validate-pointer (heap-ref (+ address 1)))
         (validate-pointer (heap-ref (+ address 2)))
         (loop (+ address 3))]
        [(clos)
         (for ([i (in-range (heap-ref (+ address 2)))])
           (validate-pointer (heap-ref (+ address 3 i))))
         (loop (+ address 3 (heap-ref (+ address 2))))]
        [else
         (error 'validate-heap "unexpected tag @ ~a" address)])))
  (loop (heap-ref 1))) ; start at start of from-space (address stored in 1)

(define (traverse/roots roots)
  (cond [(list? roots)
         (for-each traverse/roots roots)]
        [(root? roots)
         (define address (read-root roots))
         (cond
           [(equal? (heap-ref address) 'f)
            (set-root! roots (heap-ref (+ address 1)))]
           [else
            (set-root! roots (heap-ref 3)) ;; set root to address at queue end
            (enqueue address)])] ;; enqueue the data root points to
        [(false? roots)
         (void)]
        [else (error 'traverse/roots "unexpected roots: ~a" roots)]))

;; Adds an entry to the queue and copies it to the to-space
(define (enqueue ptr)
  (define q-end (heap-ref 3))
  (case (heap-ref ptr)
    [(flat)
     (heap-set! q-end (heap-ref ptr)) ;; move data to end of queue
     (heap-set! (+ q-end 1) (heap-ref (+ ptr 1)))
     (heap-set! ptr 'f) ;; set ptr to a forward pointer
     (heap-set! (+ ptr 1) q-end)
     (heap-set! 3 (+ q-end 2))] ;; increment queue end
    [(cons)
     (heap-set! q-end (heap-ref ptr)) ;; move data to end of queue
     (heap-set! (+ q-end 1) (heap-ref (+ ptr 1)))
     (heap-set! (+ q-end 2) (heap-ref (+ ptr 2)))
     (heap-set! ptr 'f) ;; set ptr to a forward pointer
     (heap-set! (+ ptr 1) q-end)
     (heap-set! 3 (+ q-end 3))] ;; increment queue end
    [(clos)
     (heap-set! q-end (heap-ref ptr)) ;; move data to end of queue
     (heap-set! (+ q-end 1) (heap-ref (+ ptr 1)))
     (heap-set! (+ q-end 2) (heap-ref (+ ptr 2)))
     (for ([i (in-range (heap-ref (+ ptr 2)))]) ;; move free var pointers
       (heap-set! (+ q-end 3 i) (heap-ref (+ ptr 3 i))))
     (heap-set! ptr 'f) ;; set ptr to a forward pointer
     (heap-set! (+ ptr 1) q-end)
     (heap-set! 3 (+ q-end 3 (heap-ref (+ ptr 2))))] ;; increment queue end
    [(f) ; if forward pointer, do nothing. This will be handled in dequeue
     (void)]
    [else
     (error 'copy-to-space "unexpected tag @ ~a" ptr)]))

;; recursively go through the queue
(define (process-queue)
  (cond
    [(> (heap-ref 3) (heap-ref 2)) ; if items still queued
     (dequeue (heap-ref 2))
     (process-queue)]
    [else ; queue is empty
     (void)]
    ))

(define (dequeue ptr) ;; ptr = queue start
  (case (heap-ref ptr)
    [(flat)
     (heap-set! 2 (+ ptr 2))] ;; dequeue flat element
    [(cons)
     (define first-ptr (heap-ref (+ ptr 1)))
     (define rest-ptr (heap-ref (+ ptr 2)))
     (enqueue first-ptr) ; Copy first and rest to to-space, make into forwarding pointers if not done already
     (enqueue rest-ptr)
     (heap-set! (+ ptr 1) (heap-ref (+ first-ptr 1))) ; take new addresses from forwarding pointers
     (heap-set! (+ ptr 2) (heap-ref (+ rest-ptr 1)))
     (heap-set! 2 (+ ptr 3))] ; increment queue start
    [(clos)
     (for ([i (in-range (heap-ref (+ ptr 2)))]) ; enqueue all fvs
       (define fv-ptr (heap-ref (+ ptr 3 i)))
       (enqueue fv-ptr) ; Copy to to-space and make forwarding pointers if not done already
       (heap-set! (+ ptr 3 i) (heap-ref (+ fv-ptr 1)))) ; Get new addresses from 'f ptrs
     (heap-set! 2 (+ ptr 3 (heap-ref (+ ptr 2))))] ; increment queue start
    [else
     (error 'dequeue "unexpected tag @ ~a" ptr)]))

;; ----------------------------------------------------------------------

#|
flat:    ... | 'flat | <payload> | ...
|#
;; gc:alloc-flat : flat-value -> address
(define (gc:alloc-flat value)
  (define address (malloc 2 #f #f))
  (heap-set! address 'flat)
  (heap-set! (+ address 1) value)
  address)
;; gc:flat? : address -> boolean
(define (gc:flat? address)
  (equal? (heap-ref address) 'flat))
;; gc:deref : address -> flat-value
(define (gc:deref address)
  (unless (gc:flat? address)
    (error 'gc:deref "expected flat @ ~a" address))
  (heap-ref (+ address 1)))


#|
pair:    ... | 'cons | <first-ptr> | <rest-ptr> | ...
|#
;; gc:cons : root root -> address
(define (gc:cons root1 root2)
  (define address (malloc 3 root1 root2))
  (heap-set! address 'cons)
  (heap-set! (+ address 1) (read-root root1))
  (heap-set! (+ address 2) (read-root root2))
  address)
;; gc:cons? : address -> boolean
(define (gc:cons? address)
  (equal? (heap-ref address) 'cons))
;; gc:first : address -> address
(define (gc:first address)
  (unless (gc:cons? address)
    (error 'gc:first "expected cons @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:rest : address -> address
(define (gc:rest address)
  (unless (gc:cons? address)
    (error 'gc:rest "expected cons @ ~a" address))
  (heap-ref (+ address 2)))
;; gc:set-first! : address address -> void
(define (gc:set-first! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-first! "expected cons @ ~a" address))
  (heap-set! (+ address 1) new-value-address))
;; gc:set-rest! : address address -> void
(define (gc:set-rest! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-rest! "expected cons @ ~a" address))
  (heap-set! (+ address 2) new-value-address))


#|
closure: ... | 'clos | <code-ptr> | <n-fvs> | <fv0> | <fv1> | ... | ...
|#
;; gc:closure : opaque-value (listof root) -> address
(define (gc:closure code-ptr free-vars)
  (define address (malloc (+ 3 (length free-vars))
                          free-vars
                          #f))
  (heap-set! address 'clos)
  (heap-set! (+ address 1) code-ptr)
  (heap-set! (+ address 2) (length free-vars))
  (for ([i  (in-range (length free-vars))]
        [fv (in-list free-vars)])
    (heap-set! (+ address 3 i)
               (read-root fv)))
  address)
;; gc:closure? : address -> boolean
(define (gc:closure? address)
  (equal? (heap-ref address) 'clos))
;; gc:closure-code-ptr : address -> opaque-value
(define (gc:closure-code-ptr address)
  (unless (gc:closure? address)
    (error 'gc:closure-code-ptr "expected closure @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:closure-env-ref : address integer -> address
(define (gc:closure-env-ref address i)
  (unless (gc:closure? address)
    (error 'gc:closure-env-ref "expected closure @ ~a" address))
  (heap-ref (+ address 3 i)))


;; TESTS
; Most testing was done using mutators in separate files, as such these tests do not cover much
(test (with-heap (make-vector 20)
        (init-allocator)
        (gc:deref (gc:alloc-flat 2)))
      2)

(test (with-heap (make-vector 10)
        (init-allocator)
        (gc:alloc-flat 2)
        (gc:alloc-flat 2)
        (gc:alloc-flat 2)
        (gc:deref (gc:alloc-flat 2)))
      2)

(test (with-heap (make-vector 20)
        (init-allocator)
        (gc:alloc-flat 4)
        (gc:alloc-flat 5)
        (gc:alloc-flat 6)
        (gc:alloc-flat 7)
        (gc:alloc-flat 8)
        (gc:alloc-flat 9)
        (gc:deref (gc:first (gc:cons (simple-root 4) (simple-root 6)))))
      4)
