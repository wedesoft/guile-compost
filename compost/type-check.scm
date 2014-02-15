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

(define-module (compost type-check)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-26)
  #:use-module (compost error)
  #:use-module (compost types)
  #:use-module (language cps)
  #:export (check-types))

(define (check-primcall-argument-types src op types)
  (let lp ((expected (primcall-argument-types op))
           (actual types)
           (n 0))
    (match (cons expected actual)
      ((() . ()) #t)
      (((expected . expected*) . (actual . actual*))
       (when (zero? actual)
         (compilation-error src "~a: argument ~a: expected ~a, got no type"
                            op n (type-representations expected)))
       (unless (zero? (logand actual (lognot expected)))
         (compilation-error src "~a: argument ~a: expected ~a, got ~a"
                            op n (type-representations expected)
                            (type-representations actual)))
       (lp expected* actual* (1+ n))))))

(define (check-types fun types)
  (define get-type (cut hashq-ref types <>))
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
          (check-primcall-argument-types src op (map get-type args)))))))
  (match fun
    (($ $fun src meta () body)
     (visit-cont body))))
