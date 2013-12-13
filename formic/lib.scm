
#lang racket

(require data/gvector)


(require "prim.scm")


;; UTILITIES

(define-syntax-rule (push-back! x y)
  (set! y (cons x y)))

(define-syntax-rule (variant x)
  (vector-ref (struct->vector x) 0))

(define __symbol string->symbol)

(define (__escape body)
  (call-with-current-continuation
   (lambda (k)
     (body (proxy k)))))

(define nil '())

(define (force-list xs)
  (let loop ((z (force xs)))
    (if (null? z)
        '()
        (cons (car z)
              (loop (force (cdr z)))))))

(define-syntax-rule (getfail stmt)
  (call-with-current-continuation
   (lambda (k)
     (call-with-exception-handler
      (lambda (exc)
        (k (s-fail exc)))
      (lambda ()
        (s-ok stmt))))))


;; (define (ann1 obj k v)
;;   (let* ((obj (if (s-ann? obj) obj (s-ann obj (make-immutable-hash))))
;;          (h (s-ann-annotations obj)))
;;     (s-ann obj (hash-set h k v))))

(define (ann1 obj k v)
  (let* ((x (if (s-ann? obj) (s-ann-object obj) obj))
         (h (if (s-ann? obj) (s-ann-annotations obj) (make-immutable-hash))))
    (s-ann x (hash-set h k v))))

(define (ann obj)
  (s-ann-annotations obj))

(define (%<< a b)
  (if (s-ann? b)
      (begin
        (for-each
         (lambda (x)
           (set! a (ann1 a (car x) (cdr x))))
         (hash->list (s-ann-annotations b)))
        a)
      a))

(define (@ _ x)
  (ugcall x))

(define dyn make-parameter)

(define (inexact n)
  (exact->inexact n))

(define (pr x)
  (display x)
  (newline))

(define (empty x)
  (null? (force (iter x))))


(define (unzip v . rest)
  (let ((l (vector->list v)))
    (if (null? rest)
        (map list l)
        (map (lambda (x y) (cons x y))
             l (apply unzip rest)))))


(define (_zip lists)
  (let* ((lists (map (lambda (x) (extract x)) lists))
         (first (car lists))
         (rest (cdr lists)))
    (if (null? first)
        (begin
          (for-each
           (lambda (x)
             (if (not (null? x))
                 (error "Lists are not the same length!")
                 #t))
           rest)
          '())
        (cons (apply vector-immutable (map car lists))
              (lazy (_zip (map cdr lists)))))))

(define (zip . lists)
  (if (null? lists)
      '()
      (_zip (map iter lists))))


(define (_chain xs . others)
  (if (null? others)
      xs
      (lazy
        (let ((fxs (force xs)))
          (if (null? fxs)
              (apply _chain others)
              (cons (car fxs)
                    (apply _chain (cdr fxs) others)))))))

(define (chain . lists)
  (if (null? lists)
      '()
      (apply _chain (map (lambda (x) (iter x)) lists))))

(define (_enumerate seq i)
  (let ((fseq (force seq)))
    (if (null? fseq)
        '()
        (cons (vector i (car fseq))
              (_enumerate (cdr fseq) (+ i 1))))))

(define (enumerate seq (start 0))
  (_enumerate (iter seq) start))

(define (_neighbours xs)
  (let ((xs (force-list xs)))
    (if (null? xs)
        '()
        (let loop ((x1 xs)
                   (x2 (cdr xs)))
          (if (null? x2)
              '()
              (cons (vector (car x1) (car x2))
                    (loop (cdr x1) (cdr x2))))))))

(define (neighbours xs)
  (_neighbours (iter xs)))


(define (group grouper xs)
  (if (null? xs)
      '()
      (let ((first (car xs))
            (rest (cdr xs)))
        (if (null? rest)
            (cons xs '())
            (let ((second (car rest))
                  (rest2 (cdr rest)))
              (if (grouper first second)
                  (cons (list first) (group grouper rest))
                  (let ((results (group grouper rest)))
                    (cons (cons first (car results))
                          (cdr results)))))))))



(define (__patch_table . hashes)
  (make-hash
   (foldr
    append
    '()
    (map
     (lambda (h)
       (hash->list h))
     hashes))))

(define (__patch_vector . vectors)
  (foldr vector-append '#() vectors))

(define (__patch_assoc . assocs)
  (s-assoc
   (foldr
    vector-append
    '#()
    (map s-assoc-vector assocs))))

(define patch_table __patch_table)
(define patch_vector __patch_vector)
(define patch_assoc __patch_assoc)



;; GENERAL SEND

(define (proxy-app object message)
  (let* ((type (typekey object)) ;; (variant object))
         (proxy (hash-ref proxy-map type #f)))
    (if proxy
        ((proxy object) message)
        (error "Could not find a proxy for" type object "to send" message))))

(define (ugsend object message)
  (cond
   ((promise? object)
    (ugsend (force object) message))
   ((s-ann? object)
    (ugsend (s-ann-object object) message))
   ;; ((parameter? object)
   ;;  ((__parameter_proxy object) message))
   ((procedure? object)
    (let ((message (if (promise? message) (force message) message)))
      (cond
       ((vector? message)
        (apply object (vector->list message)))
       ((null? message)
        (object))
       ((pair? message)
        (apply object (force-list message)))
       (#t
        (proxy-app object message)))))
   ;; ((and (procedure? object)
   ;;       (vector? message))
   ;;  (apply object (vector->list message)))
   ((prefab-struct-key object)
    ((__struct_proxy object) message))
   (#t
    (proxy-app object message))))

(define (ugsend-soft object message)
  (cond
   ((promise? object)
    (ugsend-soft (force object) message))
   ((and (procedure? object)
         (vector? message))
    (getfail
     (apply object (vector->list message))))
   ((clause-map? object)
    (send-to-clause-map-noerr object (clause-map-clauses object) message 0 '() #t))
   ((prefab-struct-key object)
    (getfail
     ((__struct_proxy object) message)))
   (#t
    (let* ((type (variant object))
           (proxy (hash-ref proxy-map type #f)))
      (if proxy
          (getfail
           ((proxy object) message))
          (s-fail (vector "Could not find a proxy for" type object)))))))

(define (responds_to object message)
  (cond
   ((promise? object)
    (responds_to (force object) message))
   ((and (procedure? object)
         (vector? message))
    #t)
   ((clause-map? object)
    (clause-map-responds-to? object (clause-map-clauses object) message 0))
   (#t
    #f)))

(define (ugcall object . args)
  (cond
   ((procedure? object)
    (apply object args))
   (#t
    (ugsend object (list->vector args)))))

;; HASH TABLE CONTAINING PROXIES FOR SEND
;; typename -> (lambda (object message) ...)

;; (define proxies (make-hasheq))


;; Clause maps

(struct
 clause-map
 (clauses)
 #:transparent)

(define (clause-map-responds-to? cmap clauses message i)
  (if (= i (vector-length clauses))
      #f
      (let* ((clause (vector-ref clauses i))
             (contract (car clause))
             (guard (cadr clause))
             (body (caddr clause))
             (succ-args
              (call-with-current-continuation
               (lambda (k)
                 (call-with-exception-handler
                  (lambda (exc)
                    (k (cons #f exc)))
                  (lambda ()
                    (cons #t (contract message)))))))
             (success (car succ-args))
             (arguments (cdr succ-args)))
        (if success
            (if (or (not guard) (apply guard arguments))
                #t
                (clause-map-responds-to? cmap clauses message (+ i 1)))
            (clause-map-responds-to?
             cmap clauses message (+ i 1))))))

(define (send-to-clause-map-noerr cmap clauses message i errors all-guard?)
  (if (= i (vector-length clauses))
      (let ((errors (reverse errors)))
        (if all-guard?
            (s-guard-fail errors)
            (s-fail errors)))
      (let* ((clause (vector-ref clauses i))
             (contract (car clause))
             (guard (cadr clause))
             (body (caddr clause))
             (succ-args
              (call-with-current-continuation
               (lambda (k)
                 (call-with-exception-handler
                  (lambda (exc)
                    (k (cons #f exc)))
                  (lambda ()
                    (cons #t (contract message)))))))
             (success (car succ-args))
             (arguments (cdr succ-args)))
        (if success
            (if (or (not guard) (apply guard arguments))
                (s-ok (apply body arguments))
                (send-to-clause-map-noerr
                 cmap clauses message (+ i 1) (cons (list 'GE message) errors) all-guard?))
            (send-to-clause-map-noerr
             cmap clauses message (+ i 1) (cons arguments errors) #f)))))

(define (send-to-clause-map cmap message)
  (match (send-to-clause-map-noerr cmap (clause-map-clauses cmap) message 0 '() #t)
   ((s-ok value)
    value)
   ((s-fail errors)
    (raise errors))
   ((s-guard-fail errors)
    (raise errors))
   (x
    (error "Cannot match in send-to-clause-map" x))))


;; (define (send-to-clause-map cmap clauses message i errors)
;;   (if (= i (vector-length clauses))
;;       (error "no matching clause" (reverse errors))
;;       (let* ((clause (vector-ref clauses i))
;;              (contract (car clause))
;;              (guard (cadr clause))
;;              (body (caddr clause))
;;              (succ-args
;;               (call-with-current-continuation
;;                (lambda (k)
;;                  (call-with-exception-handler
;;                   (lambda (exc)
;;                     (k (cons #f exc)))
;;                   (lambda ()
;;                     (cons #t (contract message)))))))
;;              (success (car succ-args))
;;              (arguments (cdr succ-args)))
;;         (if success
;;             (if (or (not guard) (apply guard arguments))
;;                 (apply body arguments)
;;                 (send-to-clause-map cmap clauses message (+ i 1) (cons 'GE errors)))
;;             (send-to-clause-map cmap clauses message (+ i 1) (cons arguments errors))))))

(define (__clause-map_proxy cmap)
  (lambda (message)
    (send-to-clause-map cmap message)))





;; Prefab patterns
(struct p-project (projector pattern)
 #:prefab
 #:reflection-name 'project)
(struct p-deconstruct (deconstructor pattern)
 #:prefab
 #:reflection-name 'deconstruct)
(struct p-star (name)
 #:prefab
 #:reflection-name 'star)
(struct p-dstar (name)
 #:prefab
 #:reflection-name 'dstar)
(struct p-default (name dflt)
 #:prefab
 #:reflection-name 'default)
(struct p-assoc (key value)
 #:prefab
 #:reflection-name 'assoc)

;; Basic structures
(struct s-hybrid (vector assoc)
 #:transparent
 #:reflection-name 'hybrid)
(struct s-assoc (vector)
 #:transparent
 #:reflection-name 'assoc)
;; TODO: add step?
(struct s-range (start end)
 #:transparent
 #:reflection-name 'range)
(struct s-ann (object annotations)
 #:transparent
 #:reflection-name 'ann)
(struct s-err (tags fields)
 #:transparent
 #:reflection-name 'err)

;; Raised structures
;; Control flow
(define nothing (gensym 'nothing))
(struct s-break (value)
 #:transparent
 #:reflection-name 'break)
(define (__break (value nothing))
  (s-break value))
(struct s-continue (value)
 #:transparent
 #:reflection-name 'continue)
(define (__continue (value nothing))
  (s-continue value))
;; Result wrappers
(struct s-ok (value)
 #:transparent
 #:reflection-name 'ok)
(struct s-fail (errors)
 #:transparent
 #:reflection-name 'fail)
(struct s-guard-fail (errors)
 #:transparent
 #:reflection-name 'guard-fail)


;; Proxy

(define (__proxy_proxy p)
  (lambda (message)
    ((proxy-f p) message)))

;; Record proxy

(define record-map (make-hasheq))

(define (register_record key proxy)
  (hash-set! record-map key proxy))

(define (__record_proxy s)
  (let-values (((type _) (struct-info s)))
    (let ((prox (hash-ref record-map type)))
      (prox s))))

;; Errors

(define (tagset tags)
  (list->set (vector->list tags)))

(define (__error_type tags)
  (proxy
   (match-lambda
    ((s-assoc (vector fields ...))
     (s-err tags
            (make-immutable-hash fields)))
    ((? symbol? s)
     (__error_type (vector-append tags (vector s))))
     ;; (__error_type (set-add tags s)))
    ((== projector eq?)
     (lambda (value)
       (let* ((value (extract value))
              (tags (tagset tags)))
         (if (s-err? value)
             (if (equal? tags (set-intersect tags (tagset (s-err-tags value))))
                 value
                 (error "not the right tags"))
             (error "not an Error")))))
    ((== deconstructor eq?)
     (lambda (value)
       (let* ((value (extract value))
              (tags (tagset tags)))
         (if (s-err? value)
             (if (equal? tags (set-intersect tags (tagset (s-err-tags value))))
                 (s-err-fields value)
                 (error "not the right tags"))
             (error "not an Error"))))))))

(define Error (__error_type '#()))

(define (__error_proxy e)
  (match-lambda
   ((? symbol? s)
    (hash-ref (s-err-fields e) s))
   ((== repr eq?)
    (let* ((f (hash-copy (s-err-fields e)))
           (msg (extract (hash-ref f 'message #f)))
           (loc (extract (hash-ref f 'location #f)))
           (fields (hash->list f)))
           ;; (locs (cond
           ;;        ((vector? loc) (apply __union (vector->list loc)))
           ;;        ((pair? loc) (apply __union loc))
           ;;        (#t loc))))
      (hash-remove! f 'message)
      (hash-remove! f 'location)
      `#s(error
          ,(repr (s-err-tags e))
          ,(if msg `#s(group #s(text ,msg)) #s(void))
          ,(if loc (repr loc) #s(void))
          ,(repr f))))))



;; messages
(struct m-dispatch (argnum fn)
 #:prefab
 #:reflection-name 'dispatch)
(struct m-assign (item value)
 #:prefab
 #:reflection-name 'assign)
(struct m-index (index)
 #:prefab
 #:reflection-name 'index)

(define (projector obj)
  (ugsend obj projector))
(define (deconstructor obj)
  (ugsend obj deconstructor))
(define (iter obj)
  ((ugsend obj iter)))

(define reprhook
  (make-parameter (lambda (obj rec) (rec obj))))
(define (repr obj)
  ((reprhook)
   obj
   (lambda (obj)
     (call-with-current-continuation
      (lambda (k)
        (call-with-exception-handler
         (lambda (exc)
           (k `#s(text ,(~a obj))))
         (lambda ()
           (ugsend obj repr))))))))

;; (define (repr obj)
;;   (ugsend obj repr))

(define all
  (proxy
   (lambda (x)
     (force-list x))))

(define mut
  (proxy
   (lambda (obj)
     ((ugsend obj mut)))))

(define frz
  (proxy
   (lambda (obj)
     ((ugsend obj frz)))))

(define exhaust
  (proxy
   (lambda (xs)
     (let ((xs (force xs)))
       (if (null? xs)
           #f
           (let loop ((z xs))
             (let ((tail (force (cdr z))))
               (if (null? tail)
                   (car z)
                   (loop tail)))))))))


;; ;; For extraction
;; (struct s-extracted (object)
;;  #:transparent
;;  #:reflection-name 'extracted)

(define (extract-vector object)
  (cond
   ;; ((s-extracted? object) (s-extracted-object object))
   ((vector? object) object)
   ((s-hybrid? object) (s-hybrid-vector object))
   ((hash? object) '#())
   ((s-assoc? object) '#())
   (#t (error "Not deconstructible 1"))))

;; (define (extract-assoc object)
;;   (cond
;;    ;; ((s-extracted? object) (s-extracted-object object))
;;    ((vector? object) '#())
;;    ((s-hybrid? object) (s-assoc-vector (s-hybrid-assoc object)))
;;    ((s-assoc? object) (s-assoc-vector object))
;;    (#t (error "Not deconstructible"))))

(define (extract-assoc-and-hash object)
  (cond
   ;; ((s-extracted? object) (s-extracted-object object))
   ((vector? object) (cons #f (make-hash)))
   ((hash? object) (cons #f (hash-copy object)))
   ((s-hybrid? object) (extract-assoc-and-hash (s-hybrid-assoc object)))
   ((s-assoc? object)
    (let* ((v (s-assoc-vector object))
           (a (vector->list v)))
      (cons a (make-hash a))))
   (#t (error "Not deconstructible 2"))))


(struct s-stddec (leadpos defpos star trailpos keys dstar)
 #:transparent
 #:reflection-name 'stddec
 #:property prop:procedure
 (lambda (self object)
   (let* ((v (extract-vector object))
          (vl (vector-length v))
          ;; (a (extract-assoc object))
          (apart (extract-assoc-and-hash object))
          (i 0)
          (results '()))

     ;; vector part
     (for-each
      (lambda (dec)
        (if (= i vl)
            (error "Not enough arguments")
            (begin
              (push-back! (dec (vector-ref v i)) results)
              (set! i (+ i 1)))))
      (s-stddec-leadpos self))

     (for-each
      (lambda (dec-and-default)
        (let ((dec (car dec-and-default))
              (default (cdr dec-and-default)))
          (if (= i vl)
              (push-back! (dec default) results)
              (begin
                (push-back! (dec (vector-ref v i)) results)
                (set! i (+ i 1))))))
      (s-stddec-defpos self))

     (let ((stardec (s-stddec-star self)))
       (if stardec
           (let* ((trailpos (s-stddec-trailpos self))
                  (ntrail (length trailpos))
                  (j (- vl ntrail)))
             (if (< j i)
                 (error "Not enough arguments (2)" object)
                 (begin
                   (push-back! (stardec (vector-copy v i j)) results)
                   (for-each
                    (lambda (dec)
                      (push-back! (dec (vector-ref v j)) results)
                      (set! j (+ j 1)))
                    trailpos))))
           (if (not (= i vl))
               (error "Too many arguments" object)
               #f)))

     ;; keys part
     (let* (;; (a (vector->list a))
            ;; (h (make-hash a))
            (a (car apart))
            (h (cdr apart))
            (keys (s-stddec-keys self)))
       (for-each
        (lambda (kdd)
          (let ((key (car kdd))
                (dec (cadr kdd))
                (default (caddr kdd)))
            (push-back!
             (dec
              (if (hash-has-key? h key)
                  (let ((value (hash-ref h key)))
                    (hash-remove! h key)
                    value)
                  (if (eq? default no-default)
                      (error "Missing key" key)
                      default)))
             results)))
        keys)
       (let ((dstardec (s-stddec-dstar self)))
         (if dstardec
             (push-back!
              (dstardec
               (if a
                   (s-assoc
                    (list->vector
                     (let loop ((remainder a))
                       (if (null? remainder)
                           '()
                           (let ((key (car (car remainder))))
                             (if (hash-has-key? h key)
                                 (cons (cons key (hash-ref h key))
                                       (loop (cdr remainder)))
                                 (loop (cdr remainder))))))))
                   (s-assoc (list->vector (hash->list h)))))
              results)
             (if (= (hash-count h) 0)
                 #f
                 (error "Extra keys" h)))))

     (apply append (reverse results)))))


(define no-default (gensym 'no-default))

(define-syntax spec-state
  (lambda (stx)
    (let* ((indexes (cdr (syntax->datum stx)))
           (nums '((pos . 0)
                   (posdef . 1)
                   (star . 2)
                   (assoc . 3)
                   (assocdef . 4)
                   (dstar . 5)))
           (to-num (lambda (x) (cdr (assoc x nums))))
           (here (to-num (car indexes)))
           (ban (map to-num (cadr indexes)))
           (allow (map to-num (caddr indexes))))
      (datum->syntax
       stx
       `(if (vector-ref allowed ,here)
            (begin
              ,@(let loop ((b ban))
                  (if (null? b)
                      '()
                      (cons `(vector-set! allowed ,(car b) #f)
                            (loop (cdr b)))))
              ,@(let loop ((b allow))
                  (if (null? b)
                      '()
                      (cons `(vector-set! allowed ,(car b) #t)
                            (loop (cdr b)))))
              #f)
            (error "Nope"))))))

(define __plain_variable (lambda (x) (list x)))

(define spec->deconstructor

  (match-lambda

   ((p-project obj pattern)
    (let ((fn (projector obj))
          (dec (spec->deconstructor pattern)))
      (lambda (x)
        (dec (fn x)))))

   ((p-deconstruct obj pattern)
    (let ((fn (deconstructor obj))
          (dec (spec->deconstructor pattern)))
      (lambda (x)
        (dec (fn x)))))

   ((? symbol? s)
    __plain_variable)

   (#f
    (lambda (x) '()))

   ((vector elems ...)
    (let ((rec spec->deconstructor)
          (star-seen? #f)
          (leadpos '())
          (defpos '())
          (trailpos '())
          (keys '())
          (the-star #f)
          (the-dstar #f)
          ;; order: positional posdefault star positional keyword dstar
          ;; vector positions: pos posdef star assoc assocdef dstar
          (allowed (vector #t #t #t #t #t #t)))
      (for-each
       (match-lambda

        ((p-star name)
         (spec-state star (posdef star) (pos))
         (set! star-seen? #t)
         (set! the-star (rec name)))

        ((p-dstar name)
         (spec-state dstar (pos posdef star assoc assocdef dstar) ())
         (set! the-dstar (rec name)))

        ((p-assoc key value)
         (spec-state assoc (pos posdef star) ())
         (push-back! (list key (rec value) no-default) keys))

        ((p-default (p-assoc key value) dflt)
         (spec-state assocdef (pos posdef star assoc) ())
         (push-back! (list key (rec value) dflt) keys))

        ((p-default name dflt)
         (spec-state posdef (pos) ())
         (push-back! (cons (rec name) dflt) defpos))

        (value
         (spec-state pos () ())
         (let ((entry (rec value)))
           (if star-seen?
               (push-back! entry trailpos)
               (push-back! entry leadpos))))
        )
       elems)

      (s-stddec
       (reverse leadpos)
       (reverse defpos)
       the-star
       (reverse trailpos)
       (reverse keys)
       the-dstar)))
   
   (x
    (error "Cannot match in spec->deconstructor" x))))

(define (__make_object . components)
  (let ((clauses (map vector->list components)))
    (define (all-vars? vs)
      (let loop ((vs vs))
        (if (null? vs)
            #t
            (if (eq? (car vs) __plain_variable)
                (loop (cdr vs))
                #f))))
    (match clauses
      ((list (list (s-stddec (? all-vars? vs) '() #f '() '() #f) #f fn))
       ;; This is a plain function, like
       ;; [x] -> ... or [x, y] -> ...
       ;; No keyword or rest arguments and no checking of arguments
       ;; In this case we can just return fn directly.
       fn)
      (x
       (clause-map (list->vector clauses))))))

    ;; ;; (if (and (not (null? clauses))
    ;; ;;          (null? (cdr clauses))
    ;; ;;          )
    ;; (pretty-print clauses)
    ;; (clause-map (list->vector clauses))))








;; Standard operators

(define-syntax-rule (catch stmt)
  (call-with-current-continuation
   (lambda (k)
     (call-with-exception-handler
      (lambda (exc)
        (k (cons #f exc)))
      (lambda ()
        (cons #t stmt))))))


(define (make-arithmetic-operator operator associativity)
  (define (binapp x y)
    (cond
     ((and (number? x) (number? y))
      (operator x y))
     (#t
      (match-let (((cons success result)
                   (catch (ugsend x (m-dispatch 0 app)))))
        (if success
            (ugcall result y)
            (match-let (((cons success result2)
                         (catch (ugsend y (m-dispatch 1 app)))))
              (if success
                  (ugcall result2 x)
                  (error "operator not implemented" result result2))))))))
  (define app
    (case associativity
      ((left)
       (lambda (arg0 . args)
         (foldl (lambda (x y) (binapp y x)) arg0 args)))
      ((right)
       (lambda args
         (let* ((rargs (reverse args))
                (last (car rargs)))
           (foldl (lambda (x y) (binapp x y)) last (cdr rargs)))))))

  (values binapp app))

(define (make-binary-operator associativity)
  (define (binapp x y)
    (match-let (((cons success result)
                 (catch (ugsend x (m-dispatch 0 app)))))
      (if success
          (ugcall result y)
          (match-let (((cons success result2)
                       (catch (ugsend y (m-dispatch 1 app)))))
            (if success
                (ugcall result2 x)
                (error "operator not implemented" result result2))))))
  (define app
    (case associativity
      ((left)
       (lambda (arg0 . args)
         (foldl (lambda (x y) (binapp y x)) arg0 args)))
      ((right)
       (lambda args
         (let* ((rargs (reverse args))
                (last (car rargs)))
           (foldl (lambda (x y) (binapp x y)) last (cdr rargs)))))))

  (values binapp app))



(define-values (__plus_bin __plus) (make-arithmetic-operator + 'left))
(define-values (__minus_bin __minus) (make-arithmetic-operator - 'left))
(define-values (__times_bin __times) (make-arithmetic-operator * 'left))
(define-values (__div_bin __div) (make-arithmetic-operator / 'left))
(define-values (__pow_bin __pow) (make-arithmetic-operator expt 'right))
(define-values (__union_bin __union) (make-arithmetic-operator bitwise-ior 'left))
(define-values (__inter_bin __inter) (make-arithmetic-operator bitwise-and 'left))

(define-values (__plusplus_bin __plusplus) (make-binary-operator 'left))

(define (in x y)
  ((ugsend y (m-dispatch 1 in)) x))



(define-syntax-rule (extract x)
  (let ((realx (force x)))
    (if (s-ann? realx)
        (s-ann-object realx)
        realx)))


(define-syntax-rule (check x predicate message)
  (let ((realx (extract x)))
    (if (predicate realx)
        realx
        (error message realx))))


;; Data primitives
;; .  1. Integer     Int
;; .  2. Real        Real
;; .  3. Complex     Cx
;; .  4. Number      Num
;; .  5. Symbol      Sym
;; .  6. Character   Char
;; .  7. String      Str
;; .  8. Bool        Bool

;; Brute types
;; .  1. Fixnum      Fix
;; .  2. Fractional  Frac
;; .  3. Float       Flo

;; Singletons
;; x  1. hole
;; .  2. true
;; .  3. false


;; hole
(define __hole
  (proxy
   (match-lambda
    ((== repr eq?)
     #s(special hole))
    ((== projector eq?)
     (lambda (value)
       (let ((value (extract value)))
         (if (eq? value __hole)
             value
             (error "not a hole")))))
    ((== deconstructor eq?)
     (error "hole is not deconstructible"))
    (x
     (error "Cannot match for hole" x)))))

(define Hole __hole)
(define hole __hole)

;; true
(define (__true_proxy _)
  (match-lambda
   ((== repr eq?)
    #s(special true))
   ((== projector eq?)
    (lambda (value)
      (let ((value (extract value)))
        (if value
            value
            (error "not true")))))
   ((== deconstructor eq?)
    (error "truth is not deconstructible"))
   (x
     (error "Cannot match for true" x))))

;; false
(define (__false_proxy _)
  (match-lambda
   ((== repr eq?)
    #s(special false))
   ((== projector eq?)
    (lambda (value)
      (let ((value (extract value)))
        (if value
            (error "not false")
            value))))
   ((== deconstructor eq?)
    (error "falsehood is not deconstructible"))
   (x
     (error "Cannot match for false" x))))

;; nil
(define (__nil_proxy _)
  (match-lambda
   ((== repr eq?)
    #s(special nil))
   ((== iter eq?)
    (lambda () '()))
   ((== projector eq?)
    (lambda (value)
      (let ((value (extract value)))
        (if (not (null? value))
            (error "not nil")
            value))))
   ((== deconstructor eq?)
    (error "emptiness is not deconstructible"))
   (x
     (error "Cannot match for nil" x))))


;; Number

;; Number class
;; x Number projector [value]     ==> match value
;; x Number deconstructor [value] ==> not deconstructible

(define Number
  (proxy
   (match-lambda
    ((vector (? string? s))
     (string->number s))
    ((== repr eq?)
     #s(type Number))
    ((== projector eq?)
     (lambda (value)
       (check value number? "Not a number!")))
    ((== deconstructor eq?)
     (error "numbers are not deconstructible"))
    (x
     (error "Cannot match for type Number" x)))))

;; Number instance
;; x n.abs[]                      ==> absolute value
;; x n.mag[]                      ==> magnitude of the number
;; x n.floor[]                    ==> flooring
;; x n.ceil[]                     ==> ceiling
;; x n.truncate[]                 ==> truncate
;; * n.round[ndec = 0]            ==> round to number of decimals
;; x n.numerator[]                ==> numerator
;; x n.denominator[]              ==> denominator
;; x n.real[]                     ==> real part
;; x n.imag[]                     ==> imaginary part
;; . n #dispatch[+, 0][other]     ==> addition
;; . n #dispatch[*, 0][other]     ==> multiplication

(define (__number_proxy n)
  (match-lambda

   ('abs
    (lambda () (magnitude n)))

   ('floor
    (lambda () (floor n)))
   ('ceil
    (lambda () (ceiling n)))
   ('truncate
    (lambda () (truncate n)))
   ('round
    (lambda () (round n)))

   ('numerator
    (lambda () (numerator n)))
   ('denominator
    (lambda () (denominator n)))

   ('real
    (lambda () (real-part n)))
   ('imag
    (lambda () (imag-part n)))
   ('angle
    (lambda () (angle n)))

   ;; TODO: move this to exact integers _specifically
   ('bitlength
    (lambda () (integer-length n)))

   ((m-dispatch 0 (== __plus eq?))
    (match-lambda
     ((== __hole eq?) (error "no suffix +"))
     (x (+ n x))))

   ((m-dispatch 1 (== __plus eq?))
    (match-lambda
     ((== __hole eq?) n)
     (x (+ x n))))

   ((m-dispatch 0 (== __minus eq?))
    (match-lambda
     ((== __hole eq?) (error "no suffix -"))
     (x (- n x))))

   ((m-dispatch 1 (== __minus eq?))
    (match-lambda
     ((== __hole eq?) (- n))
     (x (- x n))))

   ((== repr eq?)
    n)

   (x
     (error "Cannot match for Number" n x))
   ))



;; String

;; String class
;; x String projector [value]     ==> match value
;; x String deconstructor [value] ==> deconstruct characters

(define String
  (proxy
   (match-lambda
    ((vector (? number? n))
     (number->string n))
    ((vector (? symbol? s))
     (symbol->string s))
    ((vector (? string? s))
     s)
    ((vector chars ...)
     (apply string chars))
    ((== repr eq?)
     #s(type String))
    ((== projector eq?)
     (lambda (value)
       (check value string? "Not a string!")))
    ((== deconstructor eq?)
     (lambda (value)
       (if (string? value)
           (list->vector (string->list value))
           (error "Not a string!"))))
    (x
     (error "Cannot match for type String" x)))))

;; String instance
;; x s[index]                     ==> character at index
;; x s.length                     ==> string length
;; x s.replace[subs, repl]        ==> replace substring
;; x s.split[sep]                 ==> split string around separator
;; x s.sym                        ==> make symbol
;; x s(iter)[]                    ==> vector of characters

(define (__string_proxy s)
  (match-lambda
   ((vector (s-range start end))
    (cond
     ((and start end)
      (substring s start end))
     (start
      (substring s start (string-length s)))
     (end
      (substring s 0 end))
     (#t
      s)))
   ((vector index)
    (string-ref s index))
   ('length
    (string-length s))
   ('replace
    (proxy
     (match-lambda
      ((s-assoc vec)
       (let ((rval s))
         (vector-map
          (lambda (p)
            (set! rval (string-replace rval (car p) (cdr p))))
          vec)
         rval)))))
   ('split
    (lambda (sep)
      (string-split s sep)))
   ('sym
    (string->symbol s))
   ('empty
    (= (string-length s) 0))
   ('codepoints
    (string->list s))

   ((== repr eq?)
    s)

   ((== iter eq?)
     (lambda ()
       (string->list s)))

   ((m-dispatch 0 (== __plusplus eq?))
    (match-lambda
     ((== __hole eq?) (error "no suffix ++"))
     (x (string-append s x))))

   (x
     (error "Cannot match for String" s x))

   ))



;; Symbol

;; Symbol class
;; x Symbol projector [value]     ==> match value
;; x Symbol deconstructor [value] ==> n/a

(define Symbol
  (proxy
   (match-lambda
    ((vector (? string? s))
     (string->symbol s))
    ((== repr eq?)
     #s(type Symbol))
    ((== projector eq?)
     (lambda (value)
       (check value symbol? "Not a symbol!")))
    ((== deconstructor eq?)
     (error "symbols are not deconstructible"))
    (x
     (error "Cannot match for type Symbol" x)))))

;; Symbol instance

(define (__symbol_proxy s)
  (match-lambda
   ((== repr eq?)
    s)
   (x
     (error "Cannot match for Symbol" s x))))



;; Character

;; Char class
;; x Char projector [value]     ==> match value
;; x Char deconstructor [value] ==> n/a

(define Char
  (proxy
   (match-lambda
    ((vector (? integer? i))
     (integer->char i))
    ((== repr eq?)
     #s(type Char))
    ((== projector eq?)
     (lambda (value)
       (check value char? "Not a character!")))
    ((== deconstructor eq?)
     (error "characters are not deconstructible")))))

;; Char instance

(define (__char_proxy c)
  (match-lambda
   ('numcode
    (char->integer c))
   ((== repr eq?)
    c)
   (x
     (error "Cannot match for Char" c x))))



;; Data structures
;; [Immutable]
;; x  1. Vector   [1, 2, 3]
;; x  2. Assoc    [a = 1, b = 2, c = 3]
;; x  3. Set      {1, 2, 3}
;; x  4. Table    {a = 1, b = 2, c = 3}
;; .              {1, 2, a = 3} <=> {1 => true, 2 => true, a = 3}
;; x  5. Hybrid   [1, 2, a = 3]
;; x  6. Pair     1 :: 2 :: 3 :: ()
;; x  7. Struct   #tag[1, 2, 3]
;; .              #tag[a = 1, b = 2, c = 3]
;; .              #tag{1, 2, 3}
;; .              #tag{a = 1, b = 2, c = 3}
;; [Mutable]
;; x  8. MVector  mut [1, 2, 3]
;; .  9. MAssoc   mut [a = 1, b = 2, c = 3]
;; . 10. MSet     mut {1, 2, 3}
;; x 11. MTable   mut {a = 1, b = 2, c = 3}
;; . 12. MStruct  mut #tag[1, 2, 3]
;; .              mut #tag[a = 1, b = 2, c = 3]
;; .              mut #tag{1, 2, 3}
;; .              mut #tag{a = 1, b = 2, c = 3}
;; No MHybrid, no MList




;; VECTOR

;; Vector class
;; x Vector[...]                  ==> create vector
;; x Vector list                  ==> create vector
;; x Vector projector [value]     ==> match value
;; x Vector deconstructor [value] ==> match value

(define Vector
  (proxy
   (match-lambda
    ((? promise? p)
     (ugsend Vector (force p)))
    ((? vector? v)
     v)
    ((? set? s)
     (list->vector (set->list s)))
    ((? pair? p)
     (list->vector (force-list p)))
    ((? null? p)
     #())
    ((== repr eq?)
     #s(type Vector))
    ((== projector eq?)
     (lambda (value)
       (check value vector? "Not a vector!")))
    ((== deconstructor eq?)
     (lambda (value)
       (check value vector? "Not a vector!"))))))

;; Vector instance
;; x v[index]                     ==> get value at index
;; x v.length                     ==> length of vector
;; x v.find[value]                ==> index of value if present
;; . v.findall[value]             ==> indices of value (lazy)
;; . v(contains)                  ==> true or false
;; x v(iter)[]                    ==> vector->list
;; . v #dispatch[++][other]       ==> concatenate vectors

(define (__vector_proxy v)
  (match-lambda
   ((m-index index)
    (vector-ref v index))
   ((vector (s-range start end))
    (vector-copy v start end))
   ((vector index)
    (vector-ref v index))
   ((== repr eq?)
    `#s(vector ,@(map repr (vector->list v))))
   ('length
    (vector-length v))
   ('empty
    (= (vector-length v) 0))
   ('first
    (vector-ref v 0))
   ('last
    (vector-ref v (- (vector-length v) 1)))
   ('find
    (lambda (value)
      (let loop ((i 0))
        (if (= i (vector-length v))
            (error "Value not found" value)
            (if (equal? (vector-ref v i) value)
                i
                (loop (+ i 1)))))))

   ((m-dispatch 0 (== __plusplus eq?))
    (match-lambda
     ((== __hole eq?) (error "no suffix ++"))
     (v2 (vector-append v v2))))

   ((== iter eq?)
    (lambda ()
      (vector->list v)))
   ((== mut eq?)
    (lambda ()
      (ugsend MVector v)))
   ((== frz eq?)
    (lambda ()
      v))
   (x
     (error "Cannot match for Vector" v x))))



;; MUTABLE VECTOR

;; MVector class
;; x MVector[...]                  ==> create mvector
;; x MVector list                  ==> create mvector
;; x MVector projector [value]     ==> match value
;; x MVector deconstructor [value] ==> match value

(define MVector
  (proxy
   (match-lambda
    ((? promise? p)
     (ugsend MVector (force p)))
    ((? vector? v)
     (let ((gv (make-gvector #:capacity (max (vector-length v) 1))))
       (vector-map
        (lambda (x) (gvector-add! gv x))
        v)
       gv))
    ((? pair? p)
     (let ((gv (make-gvector)))
       (for-each
        (lambda (x) (gvector-add! gv x))
        (force-list p))
       gv))
    ((? null? p)
     (gvector))
    ((== projector eq?)
     (lambda (value)
       (check value gvector? "Not a mvector!")))
    ((== deconstructor eq?)
     (lambda (value)
       (let ((value (extract value)))
         (if (gvector? value)
             (gvector->vector value)
             (error "Not a mvector!"))))))))

;; MVector instance
;; x mv[index]                     ==> get value at index
;; x mv[a..b]                      ==> get vector for that range
;; x mv.length                     ==> length of vector
;; x mv.find[value]                ==> index of value if present
;; x mv.push[value]                ==> add at end
;; x mv.pop[value]                 ==> pop at end
;; . mv.insert[i, value]           ==> insert at index
;; . mv.remove[i]                  ==> remove at index
;; . mv #assign[i, value]          ==> set at index
;; . mv.findall[value]             ==> indices of value (lazy)
;; . mv(contains)                  ==> true or false
;; x mv(iter)[]                    ==> vector->list
;; . mv #dispatch[++][other]       ==> concatenate vectors

(define (__mvector_proxy v)
  (match-lambda
   ((vector (s-range start end))
    (vector-copy (gvector->vector v) start end))
   ((vector index)
    (gvector-ref v index))
   ('length
    (gvector-count v))
   ('empty
    (= (gvector-count v) 0))
   ('find
    (lambda (value)
      (let loop ((i 0))
        (if (= i (gvector-count v))
            (error "Value not found" value)
            (if (equal? (gvector-ref v i) value)
                i
                (loop (+ i 1)))))))
   ((m-assign (vector item) value)
    (gvector-set! v item value))
   ('push
    (lambda (value)
      (gvector-add! v value)))
   ('pop
    (lambda ((i #f))
      (if i
          (let ((rval (gvector-ref v i)))
            (gvector-remove! v i)
            rval)
          (gvector-remove-last! v))))
   ((== repr eq?)
    `#s(prop #s(vector ,@(map repr (gvector->list v))) mutable))
   ((== iter eq?)
     (lambda ()
       (gvector->list v)))
   ((== mut eq?)
     (lambda ()
       v))
   ((== frz eq?)
     (lambda ()
       (gvector->vector v)))
   (x
     (error "Cannot match for MVector" v x))))



;; ASSOC

;; Assoc class
;; x Assoc[...]                  ==> Assoc
;; x Assoc projector [value]     ==> match value
;; x Assoc deconstructor [value] ==> match value

(define (__assoc (vector #()))
  (s-assoc vector))

(define Assoc
  (proxy
   (match-lambda
    ((? promise? p)
     (ugsend Assoc (force p)))
    ((? vector? v)
     (s-assoc v))
    ((? pair? p)
     (s-assoc (list->vector (force-list p))))
    ((? null? p)
     (s-assoc #()))
    ((== projector eq?)
     (lambda (value)
       (check value s-assoc? "Not an assoc!")))
    ((== deconstructor eq?)
     (lambda (value)
       (check value s-assoc? "Not an assoc!"))))))

;; Assoc instance
;; x a[key]                       ==> get value with that key
;; x a.length                     ==> length of vector
;; . a(contains)[key]             ==> true or false
;; . a(iter)[]                    ==> vector->list

(define (s-assoc-ref a key)
  (let* ((v (s-assoc-vector a))
         (vl (vector-length v)))
    (let loop ((i 0))
      (if (= i vl)
          (error "Not found" key a)
          (let ((entry (vector-ref v i)))
            (if (equal? (car entry) key)
                (cdr entry)
                (loop (+ i 1))))))))

(define (__assoc_proxy a)
  (let* ((v (s-assoc-vector a))
         (vl (vector-length v)))
    (match-lambda
     ((vector key)
      (s-assoc-ref a key))
     ((m-index key)
      (s-assoc-ref a key))
     ('length
      (vector-length v))
     ((== repr eq?)
      `#s(assoc ,@(map repr (vector->list (s-assoc-vector a)))))
     ((== iter eq?)
      (lambda ()
        (vector->list (s-assoc-vector a))))
     (x
      (error "Cannot match for Assoc" a x)))))


;; SET

;; Set class
;; x Set[...]                  ==> create Set
;; x Set projector [value]     ==> match value
;; x Set deconstructor [value] ==> match value

(define (__set (elements #()))
  (apply set (vector->list elements)))

(define Set
  (proxy
   (match-lambda
    ((? promise? p)
     (ugsend Set (force p)))
    ((? vector? v)
     (__set v))
    ((? pair? p)
     (list->set (force-list p)))
    ((? null? p)
     (set))

    ((== projector eq?)
     (lambda (value)
       (check value set? "Not a set!")))
    ((== deconstructor eq?)
     (lambda (value)
       (check value set? "Not a set!"))))))

;; Set instance
;; x s[key]                       ==> true if key in set
;; x s.length                     ==> length of vector
;; . s.findall[value]             ==> indices of value (lazy)
;; . s(contains)                  ==> true or false
;; x s(iter)[]                    ==> set->list

(define (__set_proxy s)
  (match-lambda
   (`#(,key)
    (set-member? s key))
   ('length
    (set-count s))

   ((m-dispatch 0 (== __union eq?))
    (match-lambda
     ((== __hole eq?) (error "no suffix |"))
     (x (set-union s x))))
   ((m-dispatch 0 (== __inter eq?))
    (match-lambda
     ((== __hole eq?) (error "no suffix &"))
     (x (set-intersect s x))))
   ((m-dispatch 1 (== in eq?))
    (lambda (x)
      (set-member? s x)))
   ((== repr eq?)
    `#s(set ,@(map repr (set->list s))))
   ((== iter eq?)
    (lambda ()
      (set->list s)))

   (x
    (error "Cannot match for Set" s x))))


;; TABLE

;; Table class
;; x Table[...]                  ==> create Table
;; x Table projector [value]     ==> match value
;; x Table deconstructor [value] ==> match value

(define (__table (elements #()))
  (make-immutable-hash (vector->list elements)))

(define (table? t)
  (and (hash? t) (immutable? t)))

(define (_Table type)
  (define make
    (case type
      ((equals) make-immutable-hash)
      ((eq?) make-immutable-hasheq)))
  (proxy
   (match-lambda
    ((? promise? p)
     (ugsend Table (force p)))
    ((? pair? p)
     (make (force-list p)))
    ((? null? p)
     (make '()))
    ((? vector? v)
     (make (vector->list v)))
    ((? s-assoc? a)
     (make (vector->list (s-assoc-vector a))))
    ((== equal? eq?)
     _TableEqual)
    ((== eq? eq?)
     _TableEq)
    ((== projector eq?)
     (lambda (value)
       (check value table? "Not a table!")))
    ((== deconstructor eq?)
     (lambda (value)
       (check value table? "Not a table!"))))))

(define _TableEqual (_Table 'equals))
(define _TableEq (_Table 'eq?))
(define Table _TableEqual)

;; Table instance
;; x s[key]                       ==> fetch value associated to key
;; x s.length                     ==> length of table
;; . s(contains)                  ==> true or false
;; x s(iter)[]                    ==> hash->list

;; MTable instance
;; x s[key]                       ==> fetch value associated to key
;; x s.length                     ==> length of table
;; . s(contains)                  ==> true or false
;; x s(iter)[]                    ==> hash->list
;; x s[key] := value              ==> assign

(define (__table_proxy t)

  (if (immutable? t)

      (match-lambda
       ((vector key)
        (hash-ref t (extract key)))
       ('get
        (lambda (key default)
          (hash-ref t (extract key) default)))
       ('length
        (hash-count t))
       ('has_key
        (lambda (key)
          (hash-has-key? t key)))
       ((== repr eq?)
        `#s(table ,@(map repr (hash->list t))))
       ((== mut eq?)
        (lambda ()
          (if (hash-eq? t)
              (make-hasheq (hash->list t))
              (make-hash (hash->list t)))))
       ((== iter eq?)
        (lambda ()
          (hash->list t))))

      (match-lambda
       ((vector key)
        (hash-ref t (extract key)))
       ('get
        (lambda (key default)
          (hash-ref t (extract key) default)))
       ('length
        (hash-count t))
       ('has_key
        (lambda (key)
          (hash-has-key? t key)))
       ((m-assign (vector item) value)
        (hash-set! t item value))
       ((== repr eq?)
        `#s(prop #s(table ,@(map repr (hash->list t))) mutable))
       ((== frz eq?)
        (lambda ()
          (if (hash-eq? t)
              (make-immutable-hasheq (hash->list t))
              (make-immutable-hash (hash->list t)))))
       ((== iter eq?)
        (lambda ()
          (hash->list t)))
       (x
        (error "Cannot match for Table" t x)))))


;; MTABLE

;; MTable class
;; x MTable[...]                  ==> create Table
;; x MTable projector [value]     ==> match value
;; x MTable deconstructor [value] ==> match value

(define (__mtable (elements #()))
  (make-hash (vector->list elements)))

(define (mtable? t)
  (and (hash? t) (not (immutable? t))))

(define MTable
  (proxy
   (match-lambda
    ((? vector? v)
     (__mtable v))
    ((== projector eq?)
     (lambda (value)
       (check value mtable? "Not a table!")))
    ((== deconstructor eq?)
     (lambda (value)
       (check value mtable? "Not a table!"))))))


;; HYBRID

;; Hybrid class
;; x Hybrid[v, a]                 ==> create Hybrid
;; x Hybrid projector [value]     ==> match value
;; x Hybrid deconstructor [value] ==> match value

(define __hybrid s-hybrid)

(define Hybrid
  (proxy
   (match-lambda
    ((vector v a)
     (s-hybrid v a))
    ((== projector eq?)
     (lambda (value)
       (check value s-hybrid? "Not a hybrid!")))
    ((== deconstructor eq?)
     (lambda (value)
       (check value s-hybrid? "Not a hybrid!"))))))

;; Hybrid instance
;; x h[key]                       ==> number -> v[key], other a[key]
;; x h.vector                     ==> vector part
;; x h.assoc                      ==> assoc part
;; x h.length                     ==> sum length of parts
;; ? h(iter)[]                    ==> not sure

(define (__hybrid_proxy h)
  (match-lambda
   (`#(,key)
    (if (and (integer? key) (>= key 0))
        (vector-ref (s-hybrid-vector h) key)
        (s-assoc-ref (s-hybrid-assoc h) key)))
   ((m-index key)
    (if (and (integer? key) (>= key 0))
        (vector-ref (s-hybrid-vector h) key)
        (s-assoc-ref (s-hybrid-assoc h) key)))
   ('vector
    (s-hybrid-vector h))
   ('assoc
    (s-hybrid-assoc h))
   ('length
    (+ (vector-length (s-hybrid-vector h))
       (vector-length (s-assoc-vector (s-hybrid-assoc h)))))
   ((== repr eq?)
    `#s(hybrid ,(repr (s-hybrid-vector h))
               ,(repr (s-hybrid-assoc h))))
   (x
    (error "Cannot match for Hybrid" h x))))


;; PAIR

;; Pair class
;; x Pair[h, t]                 ==> create Pair
;; x Pair projector [value]     ==> match value
;; x Pair deconstructor [value] ==> match value

(define Pair
  (proxy
   (match-lambda
    ((vector h t)
     (cons h t))
    ((== projector eq?)
     (lambda (value)
       (check value pair? "Not a pair!")))
    ((== deconstructor eq?)
     (lambda (value)
       (let ((value (extract value)))
         (if (pair? value)
             (vector (car value) (cdr value))
             (error "Not a pair!" value))))))))

;; Pair instance
;; x p[key]                       ==> list-ref
;; x p.head                       ==> first element
;; x p.tail                       ==> second element
;; x p.length                     ==> total length of the sequence
;; x p(iter)[]                    ==> returns self

(define (__pair_proxy p)
  (match-lambda
   ((vector key)
    (list-ref p key))
   ((m-index key)
    (list-ref p key))
   ('head
    (car p))
   ('tail
    (cdr p))
   ('length
    (length p))
   ((== repr eq?)
    `#s(pair ,(repr (car p)) ,(repr (cdr p))))
   ((== iter eq?)
     (lambda ()
       p))
   (x
    (error "Cannot match for Pair" p x))))



;; STRUCT

;; Struct builder
;; . #tag                       ==> create structure named tag
;; . (#) projector [value]      ==> match value
;; . (#) deconstructor [value]  ==> deconstruct into [tag, elements...]

(define (__struct-type tag)
  (define me
    (proxy
     (match-lambda
      ((? promise? p)
       (ugsend me (force p)))
      ((vector elems ...)
       (apply make-prefab-struct tag elems))
      ((? pair? p)
       (apply make-prefab-struct tag (force-list p)))
      ((? null? p)
       (make-prefab-struct tag))
      ('name
       tag)
      ((== repr eq?)
       `#s(struct_type ,tag))
      ((== projector eq?)
       (lambda (value)
         (let ((value (extract value)))
           (let ((k (prefab-struct-key value)))
             (if (eq? k tag)
                 value
                 (error "Not struct" tag))))))
      ((== deconstructor eq?)
       (lambda (value)
         (let ((value (extract value)))
           (let ((k (prefab-struct-key value)))
             (if (eq? k tag)
                 (let ((v (struct->vector value)))
                   (vector-copy v 1 (vector-length v)))
                 (error "Not struct" tag))))))
      (x
       (error "Cannot match for struct type" tag x))
      )))
  me)

(define Struct
  (proxy
   (match-lambda
    ((? symbol? tag)
     (__struct-type tag))
    ((vector elems ...)
     (apply ugcall (__struct-type '||) elems))
    ((== projector eq?)
     (lambda (value)
       (check value prefab-struct-key "Not a struct!")))
    ((== deconstructor eq?)
     (lambda (value)
       (if (prefab-struct-key value)
           (let* ((v (struct->vector value))
                  (tag0 (vector-ref v 0))
                  (tag (string->symbol (substring (symbol->string tag0) 7))))
             (vector-set! v 0 (__struct-type tag))
             v)
           (error "Not a struct!"))))
    (x
       (error "Cannot match for Struct" x))
    )))

;; Struct instance
;; . #x[index]                    ==> entry at index

(define (__struct_proxy s)
  (match-lambda
   ((vector index)
    (vector-ref (struct->vector s) (+ index 1)))
   ((== repr eq?)
    (let* ((v ((ugsend Struct deconstructor) s))
           (l (vector->list v)))
      `#s(struct ,(ugsend (car l) 'name) ,@(map repr (cdr l)))))
   (x
    (error "Cannot match for Struct" s x))
   ))



;; RANGE

;; Range class
;; x Range[start, end]           ==> create Range
;; x Range projector [value]     ==> match value
;; x Range deconstructor [value] ==> match value

(define (__range start end)
  (cond
   ((eq? start __hole)
    (if (eq? end __hole)
        (s-range 0 #f)
        (s-range 0 end)))
   ((eq? end __hole)
    (s-range start #f))
   (#t
    (s-range start end))))

(define Range
  (proxy
   (match-lambda
    ((vector start end)
     (s-range start end))
    ((== projector eq?)
     (lambda (value)
       (check value s-range? "Not a range!")))
    ((== deconstructor eq?)
     (lambda (value)
       (if (s-range? value)
           (vector (s-range-start value) (s-range-end value))
           (error "Not a range!")))))))

;; Range instance
;; x r.start                      ==> start of the range
;; x r.end                        ==> end of the range
;; x r.length                     ==> length of the range
;; x r(iter)[]                    ==> iterate through the range's values

(define (__range_proxy r)
  (let ((start (s-range-start r))
        (end (s-range-end r)))
    (match-lambda
     ('start
      start)
     ('end
      end)
     ('length
      (if (>= end start)
          (- end start)
          (error "This range is not iterable")))
     ((== repr eq?)
      `#s(range ,(repr start) ,(repr end)))
     ((== iter eq?)
      (lambda ()
        (stream->list (in-range start end))))
     (x
      (error "Cannot match for Range" r x)))))




;; REGEXP

;; Rx class
;; x Rx str                   ==> create regular expression
;; x Rx projector [value]     ==> match value
;; x Rx deconstructor [value] ==> match value

(define Rx
  (proxy
   (match-lambda
    ((? string? s)
     (pregexp s))
    ('quote
     (lambda (s)
       (regexp-quote s)))
    ((== projector eq?)
     (lambda (value)
       (check value regexp? "Not a regular expression!")))
    ((== deconstructor eq?)
     (lambda (value)
       (error "cannot deconstruct regular expressions"))))))

;; Rx instance
;; . rx[s]                     ==> match all of s
;; . rx.match[s]               ==> list of matches
;; . rx.match_positions[s]     ==> list of match positions

(define (__regexp_proxy r)
  (match-lambda
   ((vector s)
    (regexp-match-exact? r s))
   ('match
    (lambda (s (pos 0))
      (let ((result (regexp-match r s pos)))
        (if result
            (list->vector result)
            #f))))
   ('match_pos
    (lambda (s (pos 0))
      (let ((result (regexp-match-positions r s pos)))
        (if result
            (list->vector
             (map (lambda (y) (and y (s-range (car y) (cdr y)))) result))
            #f))))
   ('match_all
    (lambda (s (which 'all))
      (let* ((selector (if (eq? which 'all)
                          values
                          (lambda (l) (list-ref l which))))
             (results
              (regexp-match* r s #:match-select selector)))
        (if (eq? which 'all)
            (map list->vector results)
            results))))
   ('match_all_pos
    (lambda (s (which 'all))
      (let* ((selector (if (eq? which 'all)
                          values
                          (lambda (l) (list-ref l which))))
             (results
              (regexp-match-positions* r s #:match-select selector)))
        (if (eq? which 'all)
            (map (lambda (x)
                   (list->vector
                    (map (lambda (y) (s-range (car y) (cdr y))) x)))
                 results)
            (map (lambda (y) (s-range (car y) (cdr y))) results)))))
   ((== repr eq?)
    (let* ((s (~a r))
           (l (string-length s)))
      `#s(regexp ,(substring s 4 (- l 1)))))
   ))





;; PROMISE

;; Promise class
;; x Promise projector [value]     ==> match value
;; x Promise deconstructor [value] ==> match value

(define Promise
  (proxy
   (match-lambda
    ((vector x)
     (lazy x))
    ((== projector eq?)
     (lambda (value)
       (check value promise? "Not a promise!")))
    ((== deconstructor eq?)
     (lambda (value)
       (error "promises are not deconstructible"))))))


;; ANN

;; Ann class (annotations)
;; x Ann projector [value]     ==> match value
;; x Ann deconstructor [value] ==> match value

(define Ann
  (proxy
   (match-lambda
    ((== projector eq?)
     (lambda (value)
       (let ((value (force value)))
         (if (s-ann? value)
             (vector (s-ann-object value)
                     (s-ann-annotations value))
             (vector value (make-hash))))))
    ((== deconstructor eq?)
     (lambda (value)
       (let ((value (force value)))
         (if (s-ann? value)
             (vector (s-ann-object value)
                     (s-ann-annotations value))
             (vector value (make-hash)))))))))






(define (__check_equal value)
  (let ((value (extract value)))
   (proxy
    (match-lambda
     ((== projector eq?)
      (lambda (other-value)
        (let ((other-value (extract other-value)))
          (if (equal? value other-value)
              value
              (error "Not equal to" value other-value)))))))))

(define (__while cond body)
  (define last #f)
  (let loop ()
    (if (cond)
        (begin (set! last (body))
               (loop))
        last)))

(register_proxy 'fixnum_integer __number_proxy)
(register_proxy 'bignum_integer __number_proxy)
(register_proxy 'fractional_number __number_proxy)
(register_proxy 'inexact_number __number_proxy)
(register_proxy 'complex_number __number_proxy)

(register_proxy 'string __string_proxy)
(register_proxy 'symbol __symbol_proxy)
(register_proxy 'regexp __regexp_proxy)
(register_proxy 'char __char_proxy)

(register_proxy 'pair __pair_proxy)
(register_proxy 'vector __vector_proxy)
(register_proxy 'mvector __mvector_proxy)
(register_proxy 'table __table_proxy)
(register_proxy 'mtable __table_proxy)
(register_proxy 'set __set_proxy)
(register_proxy 'mset __set_proxy)
(register_proxy 'struct __struct_proxy)
(register_proxy 'record __record_proxy)

(register_proxy 'true __true_proxy)
(register_proxy 'false __false_proxy)
(register_proxy 'nil __nil_proxy)


(register_record struct:proxy __proxy_proxy)
(register_record struct:clause-map __clause-map_proxy)
(register_record struct:s-hybrid __hybrid_proxy)
(register_record struct:s-assoc __assoc_proxy)
(register_record struct:s-range __range_proxy)
(register_record struct:s-err __error_proxy)

;; (register_record struct: ___proxy)


;; ITERATION

(define __raise
  (proxy
   (lambda (x)
     (raise x))))
  

(define (__generate sequence object)

  (let ((l (ugcall (ugsend sequence iter))))
    (let loop ((elems (force l)))

      (define (handle result rest)
        (match result
          ((s-ok (== nothing eq?))
           (loop (force rest)))
          ((s-ok value)
           (cons value (loop (force rest))))
          ((s-guard-fail errors)
           (loop (force rest)))
          ((s-fail errors)
           (raise errors))))

      (if (null? elems)
          '()
          (let ((first (car elems))
                (rest (cdr elems)))
            (lazy
             (call-with-current-continuation
              (lambda (k)
                (call-with-exception-handler
                 (match-lambda
                  ((s-break value)
                   (k (handle (s-ok value) '())))
                  ((s-continue value)
                   (k (handle (s-ok value) rest)))
                  (x x))
                 (lambda ()
                   (handle (ugsend-soft object first) rest)))))))))))


(define (__catch body handler else finally)
  (call-with-current-continuation
   (lambda (k)
     (call-with-exception-handler
      (lambda (exc)
        (match-let (((cons success result)
                     (catch (ugsend handler exc))))
          (if success
              (k result)
              exc)))
      (lambda ()
        (ugsend body #()))))))




;; @library_function("gen")
;; def uggen(seq, obj):
;;     _SHOW_FRAME = SHF
;;     for entry in seq:
;;         try:
;;             result = send_safeguard(obj, entry)
;;         except BreakException as e:
;;             if hasattr(e, "value"):
;;                 yield e.value
;;             break
;;         except ContinueException as e:
;;             if hasattr(e, "value"):
;;                 yield e.value
;;             continue

;;         if isinstance(result, hs.ok):
;;             yield result[0]
;;         elif isinstance(result, hs.guard_fail):
;;             continue
;;         else:
;;             raise TypeError("Match failed", result)





;; (__minus __hole 2)

;; ((ugsend -21 (m-dispatch 0 __plus)) -9)


;; Short names
;; Num Str Sym
;; Int Exact Real (Cx Int) (Cx Exact) (Cx Real) Cx

;; Vector Assoc Set Table Pair
;; V A S T

(define Num Number)
;; (define Sym Symbol)
(define Str String)
;; (define Int Integer)
;; (define Exact Exact)
;; (define Real Real)

(define V Vector)
(define A Assoc)
(define S Set)
(define T Table)


(provide

 __break
 __continue

 ugsend
 ugcall

 responds_to
 ann1
 ann
 %<<
 @
 dyn
 inexact
 all
 pr
 empty
 repr
 reprhook
 zip
 unzip
 chain
 enumerate
 neighbours
 group
 exhaust
 projector
 deconstructor
 iter
 mut
 frz
 __patch_vector
 __patch_table
 __patch_assoc
 patch_vector
 patch_table
 patch_assoc

 Number
 String
 Symbol
 Char

 Error

 Vector
 __assoc
 Assoc
 __set
 Set
 __table
 Table
 __hybrid
 Hybrid
 Struct
 Pair
 __range
 Range
 V A S T

 MVector
 MTable

 Rx
 Promise
 Ann
 Hole
 hole

 __symbol
 __hole
 __plus
 __minus
 __times
 __div
 __pow
 __plusplus
 __union
 __inter
 in

 nil

 spec->deconstructor
 p-project
 p-deconstruct
 p-star
 p-dstar
 p-default
 p-assoc
 __make_object
 __check_equal

 __generate
 __catch
 __raise
 __escape
 __while
 )







;; (define v #(1 2 3 4))
;; (define vp (__vector_proxy v))
;; (ugsend v 'length)
;; (ugsend v '#(0))
;; ((projector __Vector) #(1 2 3 4))
;; ((projector __Vector) "oops!")











;; (define (__hybrid_proxy x)
;;   (match-lambda
;;    ('project (check x hybrid? "Not a hybrid!"))
;;    ('vector (hybrid-vector x))
;;    ('assoc (hybrid-assoc x))))

;;  #:property prop:procedure
;;  (lambda (self object)
   




