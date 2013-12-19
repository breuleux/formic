
#lang racket

(require "lib.scm")

(provide
 (rename-out
  (if #%if)
  (lambda #%lambda)
  (formic-app #%app)
  (formic-module-begin #%module-begin)
  (formic-top #%top)
  (formic-datum #%datum)
  (quote #%quote)
  (begin #%begin)
  (vector-immutable #%vector)
  (cons #%pair)
))

(define-syntax-rule (formic-app f . args)
  (if (procedure? f)
      (#%app f . args)
      (ugsend f (vector-immutable . args))))

(define-syntax-rule (formic-module-begin . stmts)
  (#%module-begin . stmts))

(define-syntax-rule (formic-datum . dat)
  (#%datum . dat))

(define-syntax-rule (formic-top . id)
  (error "Unbound" 'id))

