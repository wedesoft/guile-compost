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

(define-module (compost signs)
  #:use-module (ice-9 match)
  #:use-module (compost bitfield)
  #:export (&all-signs
            &no-sign

            &negative
            &zero
            &positive

            sign-from-precondition
            constant-sign
            negate-sign
            primcall-result-sign

            sign-representations))

(define-bitfield &all-signs
  &negative
  &zero
  &positive)

(define-syntax &no-sign (identifier-syntax 0))

(define (sign-from-precondition precondition)
  &all-signs)

(define (constant-sign val)
  (cond
   ((number? val)
    (cond
     ((nan? val) &all-signs)
     ((< val 0) &negative)
     ((> val 0) &positive)
     (else &zero)))
   (else &all-signs)))

(define (negate-sign sign)
  (logior (logand (ash sign -2) &negative)
          (logand sign &zero)
          (logand (ash sign 2) &positive)))

(define (primcall-result-sign op signs)
  (match (cons op signs)
    (('add a b)
     (cond
      ((eqv? a &zero) b)
      ((eqv? b &zero) a)
      ;; If we have both + and - we have 0 as well.
      ((eqv? (logior a b &zero) &all-signs) &all-signs)
      ((eqv? a b) a)
      (else (error "unhandled" a b))))
    (('sub a b) (primcall-result-sign 'add (list a (negate-sign b))))
    (('add1 a) (primcall-result-sign 'add (list a &positive)))
    (('sub1 a) (primcall-result-sign 'add (list a &negative)))
    (('mul a b)
     (cond
      ((or (eqv? a &zero) (eqv? b &zero)) &zero)
      ((zero? (logand a b (lognot &zero)))
       (logior &negative (logand (logior a b) &zero)))
      (else (logior a b))))
    (('div a b) (primcall-result-sign 'mul signs))
    (('bytevector-length bv) (logior &zero &positive))
    (('bv-f32-ref bv offset) &all-signs)
    (((or '= '< '<= '> '>= 'eq?) a b) &all-signs)
    (('sqrt x) (logand (logior &positive &zero) x))
    (('abs x) (logand (logior &positive &zero) x))))

(define (sign-representations sign)
  (define (add-sign name &sign res)
    (if (zero? (logand sign &sign))
        res
        (cons name res)))
  (add-sign
   '- &negative
   (add-sign
    0 &zero
    (add-sign
     '+ &positive
     '()))))

