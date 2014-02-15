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

(define-module (compost representations)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-26)
  #:use-module (compost types)
  #:use-module (compost error)
  #:use-module (language cps)
  #:export (choose-representations
            check-representations))

;; A representation is either "fpr" (for floating-point register) or
;; "gpr" (for general-purpose register).

(define (choose-representation type)
  (cond
   ((eqv? type &no-type) #f) ; ?
   ((eqv? type &fixnum) 'gpr)
   ((eqv? type (logior &fixnum &non-fixnum-integer)) 'gpr)
   ((eqv? type &flonum) 'fpr)
   ((eqv? type (logand &flonum (lognot &irrational))) 'fpr)
   ((eqv? type &bytevector) 'gpr)
   ((eqv? type &unspecified) 'gpr)
   ((eqv? type &boolean) 'gpr)
   (else (error "unhandled type" type))))

(define (choose-representations types)
  (let ((reprs (make-hash-table)))
    (hash-for-each (lambda (sym type)
                     (hashq-set! reprs sym (choose-representation type)))
                   types)
    reprs))

(define (check-primcall-argument-reprs src op reprs)
  (match (cons op reprs)
    ((or ((or 'add 'sub 'mul 'div) 'fpr 'fpr)
         ((or 'add 'sub 'mul 'div) 'gpr 'gpr)
         ((or 'add1 'sub1) 'gpr)
         ('bytevector-length 'gpr)
         ('bv-f32-ref 'gpr 'gpr)
         ('bv-f32-set! 'gpr 'gpr 'fpr)
         ((or '= '< '<= '> '>=) 'gpr 'gpr)
         ((or '= '< '<= '> '>=) 'fpr 'fpr)
         ('eq? 'gpr 'gpr)
         ('sqrt 'fpr)
         ('abs 'fpr))
     #t)
    (else (compilation-error src "unsupported reprs for op: ~a ~a" op reprs))))

(define (check-representations fun reprs)
  (define get-repr (cut hashq-ref reprs <>))
  (define (visit-cont cont)
    (match cont
      (($ $cont k ($ $kargs names syms body))
       (visit-term body))
      (($ $cont k ($ $kentry self tail (clause)))
       (visit-cont clause))
      (($ $cont k ($ $kclause ($ $arity _ () #f () #f) body))
       (visit-cont body))
      (($ $cont k ($ $kif)) #t)))
  (define (visit-term term)
    (match term
      (($ $letk conts body)
       (for-each visit-cont conts)
       (visit-term body))
      (($ $continue k src exp)
       (match exp
         ((or ($ $void) ($ $values) ($ $const)) #t)
         (($ $primcall op args)
          (check-primcall-argument-reprs src op (map get-repr args)))))))
  (match fun
    (($ $fun src meta () body)
     (visit-cont body))))
