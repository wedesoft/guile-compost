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

(define (make-assembler)
  (make-variable '()))
(define (emit! asm inst)
  (pk inst)
  (variable-set! asm (cons inst (variable-ref asm))))
(define (link-assembly asm)
  (reverse (variable-ref asm)))

(define (emit-source asm src)
  (emit! asm `(source ,src)))

(define (emit-begin-program asm label meta)
  (emit! asm `(begin-program ,label ,meta)))

(define (emit-end-program asm)
  (emit! asm `(end-program)))

(define (emit-label asm label)
  (emit! asm `(label ,label)))

(define (emit-end-program asm)
  (emit! asm `(end-program)))

(define (emit-begin-arity asm req)
  (emit! asm `(begin-arity ,req)))

(define (emit-end-arity asm)
  (emit! asm `(end-arity)))

(define (emit-br asm k)
  (emit! asm `(br ,k)))

(define (emit-mov asm dst src)
  (emit! asm `(mov ,dst ,src)))

(define (emit-bv-f32-set! asm bv idx k)
  (emit! asm `(bv-f32-set! ,bv ,idx ,k)))

(define (emit-br-if-true asm sym invert? k)
  (emit! asm `(br-if-true ,sym ,invert? k)))
(define (emit-br-if-eq asm a b invert? k)
  (emit! asm `(br-if-eq ,a ,b ,invert? k)))
(define (emit-br-if-< asm a b invert? k)
  (emit! asm `(br-if-< ,a ,b ,invert? k)))
(define (emit-br-if-<= asm a b invert? k)
  (emit! asm `(br-if-<= ,a ,b ,invert? k)))
(define (emit-br-if-= asm a b invert? k)
  (emit! asm `(br-if-= ,a ,b ,invert? k)))
(define (emit-br-if-<= asm b a invert? k)
  (emit! asm `(br-if-<= ,b ,a ,invert? k)))
(define (emit-br-if-< asm b a invert? k)
  (emit! asm `(br-if-< ,b ,a ,invert? k)))

(define (emit-return asm val)
  (emit! asm `(return ,val)))

(define (emit-return-void asm)
  (emit! asm `(return-void)))

(define (emit-load-constant asm dst val)
  (emit! asm `(load-constant ,dst ,val)))

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
           (emit-begin-arity asm req)
           (let ((next (compile-body (1+ n))))
             (emit-end-arity asm)
             next)))))

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
        (($ $values ())
         (emit-return-void asm))
        (($ $values (arg))
         (emit-return asm (reg arg)))
        (($ $primcall 'return (arg))
         (emit-return asm (reg arg)))))

    (define (compile-value label exp dst)
      (match exp
        (($ $values (arg))
         (maybe-mov dst (reg arg)))
        (($ $void)
         (emit-load-constant asm dst *unspecified*))
        (($ $const exp)
         (emit-load-constant asm dst exp))
        ;; all value-producing primcalls: fixme.
        (($ $primcall op args)
         (emit! asm `(,op ,dst ,@(map reg args))))))

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
