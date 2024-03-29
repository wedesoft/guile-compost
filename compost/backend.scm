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

(define-module (compost backend)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:use-module (language cps)
  #:use-module (language cps dfg)
  #:use-module (compost assembler)
  #:use-module (compost error)
  #:use-module (compost register-allocation)
  #:export (emit-assembly))

(define (collect-conts f cfa)
  (let ((contv (make-vector (cfa-k-count cfa) #f)))
    (fold-local-conts
     (lambda (k cont tail)
       (let ((idx (cfa-k-idx cfa k #:default (lambda (k) #f))))
         (when idx
           (vector-set! contv idx cont))))
     '()
     (match f
       (($ $fun src meta free entry)
        entry)))
    contv))

(define (compile-fun f asm dfg allocation)
  (let* ((cfa (analyze-control-flow f dfg))
         (contv (collect-conts f cfa)))
    (define (lookup-cont k)
      (vector-ref contv (cfa-k-idx cfa k)))

    (define (reg sym)
      (lookup-register sym allocation))

    (define (constant sym)
      (lookup-constant-value sym allocation))

    (define (maybe-mov dst src)
      (unless (eq? dst src)
        (emit-mov asm dst src)))

    (define (compile-entry meta)
      (match (vector-ref contv 0)
        (($ $kentry self tail clauses)
         (emit-begin-program asm (cfa-k-sym cfa 0) meta)
         (let lp ((n 1)
                  (ks (map (match-lambda (($ $cont k) k)) clauses)))
           (match ks
             (()
              (unless (= n (vector-length contv))
                (error "unexpected end of clauses"))
              (emit-end-program asm))
             ((k . ks)
              (unless (eq? (cfa-k-sym cfa n) k)
                (error "unexpected k" k))
              (lp (compile-clause n (and (pair? ks) (car ks)))
                  ks)))))))

    (define (compile-clause n alternate)
      (match (vector-ref contv n)
        (($ $kclause ($ $arity req () #f () #f))
         (let ((k (cfa-k-sym cfa n)))
           (emit-label asm k)
           (emit-save-registers asm)
           (compile-body (1+ n))))))

    (define (compile-body n)
      (let compile-cont ((n n))
        (if (= n (vector-length contv))
            n
            (match (vector-ref contv n)
              (($ $kclause) n)
              (($ $kargs _ _ term)
               (emit-label asm (cfa-k-sym cfa n))
               (let find-exp ((term term))
                 (match term
                   (($ $letk conts term)
                    (find-exp term))
                   (($ $continue k src exp)
                    (when src
                      (emit-source asm src))
                    (compile-expression n k exp)
                    (compile-cont (1+ n))))))
              (_
               (emit-label asm (cfa-k-sym cfa n))
               (compile-cont (1+ n)))))))

    (define (compile-expression n k exp)
      ;; (pk exp)
      (let* ((label (cfa-k-sym cfa n))
             (k-idx (cfa-k-idx cfa k))
             (fallthrough? (= k-idx (1+ n))))
        (define (maybe-emit-jump)
          (unless (= k-idx (1+ n))
            (emit-br asm k)))
        (match (vector-ref contv k-idx)
          (($ $ktail)
           (compile-tail label exp))
          (($ $kargs (name) (sym))
           (compile-value label exp (reg sym))
           (maybe-emit-jump))
          (($ $kargs () ())
           (compile-effect label exp k)
           (maybe-emit-jump))
          (($ $kargs names syms)
           (compile-values label exp syms)
           (maybe-emit-jump))
          (($ $kif kt kf)
           (compile-test label exp kt kf
                         (and (= k-idx (1+ n))
                              (< (+ n 2) (cfa-k-count cfa))
                              (cfa-k-sym cfa (+ n 2))))))))

    (define (compile-tail label exp)
      (match exp
        (($ $values ()) #t)
        (($ $values (arg))
         (emit-prepare-return asm (reg arg)))
        (($ $primcall 'return (arg))
         (emit-prepare-return asm (reg arg))))
      (emit-restore-registers asm)
      (emit-return asm))

    (define (compile-value label exp dst)
      (match exp
        (($ $values (arg))
         (maybe-mov dst (reg arg)))
        (($ $void)
         ;; wat.
         (emit-load-constant asm dst (object-address *unspecified*)))
        (($ $const exp)
         (emit-load-constant asm dst exp))
        (($ $primcall 'add (a b))
         (emit-add asm dst (reg a) (reg b)))
        (($ $primcall 'sub (a b))
         (emit-sub asm dst (reg a) (reg b)))
        (($ $primcall 'mul (a b))
         (emit-mul asm dst (reg a) (reg b)))
        (($ $primcall 'sqrt (x))
         (emit-sqrt asm dst (reg x)))
        (($ $primcall 'max (x y))
         (emit-max asm dst (reg x)))
        (($ $primcall 'div (a b))
         (emit-div asm dst (reg a) (reg b)))
        (($ $primcall 'add1 (a))
         (emit-add1 asm dst (reg a)))
        (($ $primcall 'bv-f32-ref (bv idx))
         (emit-bv-f32-ref asm dst (reg bv) (reg idx)))))

    (define (compile-effect label exp k)
      (match exp
        (($ $values ()) #f)
        (($ $primcall 'bv-f32-set! (bv idx val))
         (emit-bv-f32-set! asm (reg bv) (reg idx) (reg val)))))

    (define (compile-values label exp syms)
      (match exp
        (($ $values args)
         (for-each (match-lambda
                    ((src . dst) (emit-mov asm dst src)))
                   (lookup-parallel-moves label allocation)))))

    (define (compile-test label exp kt kf next-label)
      (define (unary op sym)
        (cond
         ((eq? kt next-label)
          (op asm (reg sym) #t kf))
         (else
          (op asm (reg sym) #f kt)
          (unless (eq? kf next-label)
            (emit-br asm kf)))))
      (define (binary op a b)
        (cond
         ((eq? kt next-label)
          (op asm (reg a) (reg b) #t kf))
         (else
          (op asm (reg a) (reg b) #f kt)
          (unless (eq? kf next-label)
            (emit-br asm kf)))))
      (match exp
        (($ $values (sym)) (unary emit-br-if-true sym))
        (($ $primcall 'eq? (a b)) (binary emit-br-if-eq a b))
        (($ $primcall '< (a b)) (binary emit-br-if-< a b))
        (($ $primcall '<= (a b)) (binary emit-br-if-<= a b))
        (($ $primcall '= (a b)) (binary emit-br-if-= a b))
        (($ $primcall '>= (a b)) (binary emit-br-if-<= b a))
        (($ $primcall '> (a b)) (binary emit-br-if-< b a))))

    (match f
      (($ $fun src meta free ($ $cont k ($ $kentry self tail clauses)))
       (when src
         (emit-source asm src))
       (compile-entry (or meta '()))))))

(define (emit-assembly fun dfg allocation)
  (let ((asm (make-assembler)))
    (compile-fun fun asm dfg allocation)
    (link-assembly asm)))
