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

(define (fun-arguments fun)
  (match fun
    (($ $fun _ _ ()
        ($ $cont _
           ($ $kentry _
              ($ $cont)
              (($ $cont _
                  ($ $kclause arity
                     ($ $cont _
                        ($ $kargs names syms))))))))
     syms)))

(define* (infer-result-types cfa expv usev defv typev
                             #:key (allow-bignum-promotion? #t))
  (define (adjoin-type var type)
    (let* ((existing (vector-ref typev var))
           (new (logior existing type)))
      (cond
       ((eqv? existing new) #f)
       (else
        (vector-set! typev var new)
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

  (let lp ((n 0) (changed? #f))
    (cond
     ((< n (cfa-k-count cfa))
      (lp (1+ n)
          (match (list (vector-ref expv n)
                       (map (cut vector-ref typev <>)
                            (vector-ref usev n))
                       (vector-ref defv n))
            ((#f () defs) #f) ; ?
            ((($ $void) () (def))
             (adjoin-type def &unspecified))
            ((($ $values) use-types defs)
             (adjoin-types defs use-types))
            ((($ $const val) () (def))
             (adjoin-type def (constant-type val)))
            ((($ $primcall op) use-types (def))
             (adjoin-type def (primcall-result-type op use-types
                                                    #:allow-bignum-promotion?
                                                    allow-bignum-promotion?)))
            ((($ $primcall op) use-types ())
             #t))))
     (changed?
      (lp 0 #f)))))

(define (infer-types fun dfg preconditions)
  "Compute types for all variables in @var{fun}.  Returns a hash table
mapping symbols to types."
  (call-with-values (lambda () (make-variable-mapping fun))
    (lambda (var-map nvars)
      (let* ((cfa (analyze-control-flow fun dfg))
             (expv (make-vector (cfa-k-count cfa) #f))
             (usev (make-vector (cfa-k-count cfa) '()))
             (defv (make-vector (cfa-k-count cfa) '()))
             (typev (make-vector nvars &no-type)))
        (populate-uses-and-defs fun cfa var-map expv usev defv)
        (for-each (lambda (arg precondition)
                    (vector-set! typev (hashq-ref var-map arg)
                                 (type-from-precondition precondition)))
                  (fun-arguments fun) preconditions)
        (infer-result-types cfa expv usev defv typev
                            #:allow-bignum-promotion? #f)
        (let ((ret (make-hash-table)))
          (hash-for-each (lambda (sym idx)
                           (pk sym (type-representations (vector-ref typev idx)))
                           (hashq-set! ret sym (vector-ref typev idx)))
                         var-map)
          ret)))))
