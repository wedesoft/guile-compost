;;; compost
;;; Copyright (C) 2014 Andy Wingo <wingo@pobox.com>
;;; 
;;; Compost is free software: you can redistribute it and/or modify it
;;; under the terms of the GNU General Public License as published by
;;; the Free Software Foundation, either version 3 of the License, or
;;; (at your option) any later version.
;;; 
;;; Compost is distributed in the hope that it will be useful, but WITHOUT
;;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
;;; or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
;;; License for more details.
;;; 
;;; You should have received a copy of the GNU General Public License
;;; along with this program.  If not, see
;;; <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; Interface to the leaf function compiler.
;;
;;; Code:

(define-module (compost types)
  #:use-module (ice-9 match)
  #:use-module (rnrs bytevectors)
  #:export (&all-types
            &no-type

            &number
            &inexact
            &complex
            &irrational
            &non-integer
            &non-register-integer
            &non-fixnum-integer
            &bytevector
            &unspecified
            &boolean            

            &generic-number

            ;; The 5 representations of numbers in Guile.
            &fixnum &bignum &flonum &fracnum &compnum

            type-from-precondition

            constant-type
            primcall-result-type

            type-representations))

(define-syntax define-types
  (lambda (x)
    (syntax-case x ()
      ((_ all name ...)
       (with-syntax (((n ...) (iota (length #'(name ...)))))
         #'(begin
             (define-syntax name (identifier-syntax (ash 1 (* n 2))))
             ...
             (define-syntax all (identifier-syntax (logior name ...)))))))))

;; More precise types have fewer bits.
(define-types &all-types
  &number
  &inexact
  &complex
  &irrational
  &non-integer
  &non-register-integer
  &non-fixnum-integer
  &bytevector
  &unspecified
  &boolean)

(define-syntax &no-type (identifier-syntax 0))

(define-syntax &generic-number
  (identifier-syntax (logior &number
                             &inexact
                             &complex
                             &irrational
                             &non-integer
                             &non-register-integer
                             &non-fixnum-integer)))

;; The 5 kinds of numbers in Guile.
(define-syntax &fixnum
  (identifier-syntax &number))

(define-syntax &bignum
  (identifier-syntax
   (logior &number &non-register-integer &non-fixnum-integer)))

(define-syntax &flonum
  (identifier-syntax
   (logior &number &inexact &irrational
           &non-integer &non-register-integer &non-fixnum-integer)))

(define-syntax &fracnum
  (identifier-syntax
   (logior &number &non-integer &non-register-integer &non-fixnum-integer)))

(define-syntax &compnum
  (identifier-syntax &generic-number))

(define (type-from-precondition precondition)
  (case precondition
    ((bytevector?) &bytevector)
    ((real?) &flonum)
    ;; FIXME: there should be a predicate for indicating that something
    ;; is a fixnum and not a bignum.  Perhaps we need our own predicates
    ;; module.
    ((exact-integer?) &fixnum)
    (else &all-types)))

(define (constant-type val)
  (cond
   ((number? val)
    (cond
     ((exact-integer? val)
      (logior &number
              (if (<= most-negative-fixnum val most-positive-fixnum)
                  0
                  (logior &non-fixnum-integer
                          (if (and (<= most-negative-fixnum (ash val -2))
                                   (<= (ash val 2) most-positive-fixnum))
                              0
                              &non-register-integer)))))
     ((rational? val)
      (logior &number &non-fixnum-integer &non-register-integer &non-integer
              (if (exact? val) 0 &inexact)))
     (else
      (logior &number &non-fixnum-integer &non-register-integer &non-integer
              &irrational
              (if (real? val) 0 &complex)
              (if (exact? val) 0 &inexact)))))
   ((boolean? val) &boolean)
   ((bytevector? val) &bytevector)
   (else (error "unhandled constant" val))))

(define* (primcall-result-type op types #:key (allow-bignum-promotion? #t))
  (define &non-small-integer
    (if allow-bignum-promotion?
        (logior &non-fixnum-integer &non-register-integer)
        &non-fixnum-integer))
  (match (cons op types)
    (((or 'add 'sub) a b)
     (logand (logior a b
                     (ash (logand (logior a b) &non-small-integer) 1))
             &generic-number))
    (((or 'add1 'sub1) a)
     (logand (logior a (ash (logand a &non-small-integer) 1))
             &generic-number))
    (('mul a b)
     (logand (logior a b &non-small-integer)
             &generic-number))
    (('div a b)
     (logand (logior a b &irrational &non-integer &non-small-integer)
             &generic-number))
    (('bytevector-length bv) &fixnum)
    (('bv-f32-ref bv offset) &flonum)
    (((or '= '< '<= '> '>= 'eq?) a b) &boolean)
    (('sqrt x)
     (logior &number &complex &inexact
             &irrational &non-integer &non-small-integer))
    (('abs x) (logand x (lognot &complex) &generic-number))))

(define (type-representations type)
  (define (add-type name &type res)
    (if (eqv? &type (logand type &type))
        (cons name res)
        res))
  (define (add-numeric-types res)
    (define &regnum (logior &number &non-fixnum-integer))
    (let ((type (logand type &generic-number)))
      (if (zero? type)
          res
          (cons
           (cond
            ((zero? (logand type (lognot &fixnum))) 'fixnum)
            ((zero? (logand type (lognot &regnum))) 'regnum)
            ((zero? (logand type (lognot &bignum))) 'bignum)
            ((zero? (logand type (lognot &flonum))) 'flonum)
            (else 'compnum))
           res))))
  (add-numeric-types
   (add-type
    'boolean &boolean
    (add-type
     'unspecified &unspecified
     (add-type
      'bytevector &bytevector
      '())))))

