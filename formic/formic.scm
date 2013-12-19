
#lang racket

(require syntax/strip-context)
(require "prim.scm")
(require "lib.scm")
(require "common.scm")
(require "bridge.scm")

(provide read read-syntax)

(define (read in)
  (syntax->datum (read-syntax #f in)))


(define (read-syntax src in)

  ;; (define in2 (open-input-file src))

  (define s (port->string in))
  (define ptree
    (__catch
     (lambda () (compile s src))
     (proxy
      (lambda (e)
        (<> #f e)))
     #f #f))

  (define rval
    (with-syntax ((X ptree))
      (strip-context
       #'(module whatever "formic-mod.scm"
           X))))

  (pretty-print (syntax->datum ptree))

  rval)







;; (module test "formic-mod.scm"
;;  ("hello" 3))

;; (require 'test)



;; (define (clac x) (+ x x x x))

;; (define expr `(,clac 3))

;; expr

;; (eval (datum->syntax #f expr) (make-base-namespace))









;; (require syntax/strip-context)

;; (provide read read-syntax)

;; (define (read in)
;;   (syntax->datum (read-syntax #f in)))

;; ;; (define (read-syntax src in)
;; ;;   (pretty-print src)
;; ;;   (pretty-print in)
;; ;;   (datum->syntax #f
;; ;;                  #'(module whatever racket
                           
;; ;;                  (vector src 1 1 1 1)))

;; (define (read-syntax src in)
;;   (define in2 (open-input-file src))

;;   ;; consume port
;;   (define s (port->string in))

;;   (define s2 "\n\nabcdef\n")
;;   (define s3 (port->string in2))
;;   (pretty-print s)
;;   (pretty-print (equal? s s2))

;;   (define rval
;;     (with-syntax ([str s3])
;;       (strip-context
;;        #'(module anything racket
;;            (provide data)
;;            (define data 'str)
;;            (/ 1 0)
;;            (display data)))))

;;   (pretty-print (syntax->datum rval))
;;   rval)
