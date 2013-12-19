
#lang racket

(require data/gvector)


(struct proxy (f)
 #:transparent)


(define proxy-map (make-hasheq))

(define (register_proxy key maker)
  (hash-set! proxy-map key maker))


(define (typekey x)

  (cond

   ((number? x)
    (cond
     ((fixnum? x) 'fixnum_integer)
     ((integer? x) 'bignum_integer)
     ((exact? x) 'fractional_number)
     ((real? x) 'inexact_number)
     ((complex? x) 'complex_number)
     (#t (error "what is this?"))))

   ((symbol? x)
    'symbol)
   ((string? x)
    'string)

   ((pair? x)
    'pair)

   ((vector? x)
    'vector)
   ((gvector? x)
    'mvector)

   ((hash? x)
    (if (immutable? x) 'table 'mtable))
   ((set? x)
    (if (immutable? x) 'set 'mset))

   ((prefab-struct-key x)
    'struct)
   ((struct? x)
    'record)

   ((char? x)
    'char)
   ((regexp? x)
    'regexp)

   ((eq? x #t)
    'true)
   ((eq? x #f)
    'false)
   ((eq? x '())
    'nil)

   (#t
    (error "Unknown data" x))))


(define prim
  (proxy
   (match-lambda

    ('vector
     (proxy
      (match-lambda
       ('check vector?)
       ('ref vector-ref)
       ('length vector-length))))

    ('pair
     (proxy
      (match-lambda
       ('check pair?)
       ('head car)
       ('tail cdr))))

    ('location
     (proxy
      (match-lambda
       ('check srcloc?)
       ('make srcloc)
       ('source srcloc-source)
       ('line srcloc-line)
       ('column srcloc-column)
       ('position srcloc-position)
       ('span srcloc-span))))

)))


(provide
 struct:proxy
 proxy
 proxy?
 proxy-f
 proxy-map
 register_proxy
 typekey
 prim)

