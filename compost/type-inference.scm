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

(define-module (compost type-inference)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-26)
  #:use-module (compost types)
  #:use-module (language cps)
  #:use-module (language cps dfg)
  #:export (infer-types))

(define (make-variable-mapping fun)
  (let ((mapping (make-hash-table)) (n 0))
    (define (add-var! sym)
      (hashq-set! mapping sym n)
      (set! n (1+ n)))
    (define (visit-cont cont)
      (match cont
        (($ $cont k cont)
         (match cont
           (($ $kargs names syms body)
            (for-each add-var! syms)
            (visit-term body k))
           (($ $kentry self tail (clause))
            (visit-cont clause))
           (($ $kclause ($ $arity _ () #f () #f) body)
            (visit-cont body))
           (($ $kreceive) #t)
           (($ $kif) #t)))))
    (define (visit-term term k)
      (match term
        (($ $letk conts body)
         (for-each visit-cont conts)
         (visit-term body k))
        (($ $continue) #t)))
    (match fun
      (($ $fun src meta () body)
       (visit-cont body)
       (values mapping n)))))

(define (populate-uses-and-defs fun cfa var-map expv usev defv)
  (define var-idx (cut hashq-ref var-map <>))
  (define (visit-cont cont)
    (match cont
      (($ $cont k cont)
       (let ((k (cfa-k-idx cfa k #:default (lambda (k) #f))))
         (when k
           (match cont
             (($ $kargs names syms body)
              (for-each (lambda (pred)
                          (vector-set! defv pred (map var-idx syms)))
                        (cfa-predecessors cfa k))
              (visit-term body k))
             (($ $kentry self tail (clause))
              (visit-cont clause))
             (($ $kclause ($ $arity _ () #f () #f) body)
              (visit-cont body))
             ;; wat.
             (($ $kreceive) #t)
             (($ $kif) #t)))))))
  (define (visit-term term k)
    (match term
      (($ $letk conts body)
       (for-each visit-cont conts)
       (visit-term body k))
      (($ $continue _ _ exp)
       (vector-set! expv k exp)
       (match exp
         (($ $void) #t)
         (($ $values args)
          (vector-set! usev k (map var-idx args)))
         (($ $const val) #t)
         (($ $primcall op args)
          (vector-set! usev k (map var-idx args)))))))
  (match fun
    (($ $fun src meta () body)
     (visit-cont body))))

(define (infer-types fun dfg)
  "Compute types for all variables in @var{fun}.  Returns a hash table
mapping symbols to types."
  (call-with-values (lambda () (make-variable-mapping fun))
    (lambda (var-map nvars)
      (let* ((cfa (analyze-control-flow fun dfg))
             (expv (make-vector (cfa-k-count cfa) #f))
             (usev (make-vector (cfa-k-count cfa) '()))
             (defv (make-vector (cfa-k-count cfa) '()))
             (typev (make-vector nvars &no-type)))
        (define (adjoin-type var type)
          (let ((existing (vector-ref typev var)))
            (cond
             ((eqv? existing type) #f)
             (else
              (vector-set! typev var (logior existing type))
              #t))))

        (define (adjoin-types vars types)
          (let lp ((vars vars) (types types) (changed? #f))
            (if (null? vars)
                changed?
                (lp (cdr vars) (cdr types)
                    (or (adjoin-type (car vars) (car types))
                        changed?)))))

        (define (adjoin-unknown-types vars)
          (let lp ((vars vars) (changed? #f))
            (if (null? vars)
                changed?
                (lp (cdr vars)
                    (or (adjoin-type (car vars) &all-types)
                        changed?)))))

        (populate-uses-and-defs fun cfa var-map expv usev defv)

        (let lp ((n 0) (changed? #f))
          (cond
           ((< n (cfa-k-count cfa))
            (lp (1+ n)
                (match (list (vector-ref expv n)
                             (map (cut vector-ref typev <>)
                                  (vector-ref usev n))
                             (vector-ref defv n))
                  ((#f () defs)
                   (adjoin-unknown-types defs))
                  ((($ $void) () (def))
                   (adjoin-type def &unspecified))
                  ((($ $values) use-types defs)
                   (adjoin-types defs use-types))
                  ((($ $const val) () (def))
                   (adjoin-type def (constant-type val)))
                  ((($ $primcall op) use-types (def))
                   (adjoin-type def (primcall-result-type op use-types)))
                  ((($ $primcall op) use-types ())
                   #t))))
           (changed?
            (lp 0 #f))
           (else
            (let ((ret (make-hash-table)))
              (hash-for-each (lambda (sym idx)
                               (hashq-set! ret sym (pk sym (vector-ref typev idx))))
                             var-map)
              ret))))))))

