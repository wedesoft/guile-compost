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

(define-module (compost compiler)
  #:use-module (ice-9 match)
  #:use-module (ice-9 format)
  #:use-module (system base compile)
  #:use-module (language cps)
  #:use-module (language cps dfg)
  #:use-module (compost type-inference)
  #:export (compile/compost))

(define compilation-error-prompt (make-parameter #f))

(define (compilation-error msg . args)
  (abort-to-prompt (compilation-error-prompt) msg args))

(define (extract-thunk-body cps k)
  (match cps
    (($ $fun _ _ ()
        ($ $cont _
           ($ $kentry _
              ($ $cont ktail _)
              (($ $cont _
                  ($ $kclause ($ $arity () () #f () #f)
                     ($ $cont _
                        ($ $kargs () () body))))))))
     (k body ktail))))

(define (extract-fun cps)
  (extract-thunk-body
   cps
   (lambda (body ktail)
     (match body
       (($ $letk
           (($ $cont kfun
               ($ $kargs (_) (fun-sym)
                  ($ $continue ktail _
                     ($ $primcall 'return (fun-sym))))))
           ($ $continue kfun _
              (and ($ $fun) fun)))
        fun)
       (_
        (pk body)
        (compilation-error "not a function with only primitive references"))))))

(define (issue-compilation-warning port message args source)
  (display ";;; " port)
  (when source
    (let ((filename (or (assq-ref source 'filename) "<unnamed port>"))
          (line (assq-ref source 'line))
          (col (assq-ref source 'column)))
      (format port "~a:~a:~a: " filename (1+ line) col)))
  (format port "warning: optimized compile failed: ~?\n" message args))

(define (known-primcall? op)
  (memq op '(return
             add sub mul div
             add1 sub1
             bytevector-length
             bv-f32-ref bv-f32-set!
             = < <= > >=
             sqrt abs
             eq?)))

(define (assert-compilable-function fun)
  (define (visit-cont cont)
    (match cont
      (($ $cont sym cont)
       (match cont
         (($ $kargs names syms body)
          (visit-term body))
         (($ $kentry self tail clauses)
          (match clauses
            ((clause) (visit-cont clause))
            (_ (compilation-error "function has more than one clause"))))
         (($ $kclause arity body)
          (match arity
            (($ $arity _ () #f () #f)
             (visit-cont body))
            (_
             (compilation-error "function has optional, rest, or keyword args"))))
         (($ $kreceive)
          ;; wat.
          #t
          #;
          (compilation-error "function calls other non-primitive functions"))
         (($ $kif) #t)))))
  (define (visit-term term)
    (match term
      (($ $letk conts body)
       (for-each visit-cont conts)
       (visit-term body))
      (($ $letrec names syms funs body)
       (compilation-error "function contains closures"))
      (($ $continue k src exp)
       (match exp
         ;; FIXME: void only supported in tail context
         ((or ($ $void) ($ $values)) #t)
         (($ $const val)
          (unless (number? val)
            (compilation-error "non-numeric constant: ~a" val))
          (unless (or (and (exact-integer? val)
                           (<= most-negative-fixnum val most-positive-fixnum))
                      (and (inexact? val) (real? val)))
            (compilation-error "constant not a fixnum or flonum: ~a" val)))
         (($ $primcall op)
          (unless (known-primcall? op)
            (compilation-error "unhandled primcall: ~a" op)))
         (($ $prim) (compilation-error "prim nodes unsupported"))
         (($ $fun) (compilation-error "nested functions unsupported"))
         ((or ($ $call) ($ $callk))
          (compilation-error "nested calls unsupported"))
         (($ $prompt) (compilation-error "prompts unsupported"))))))
  (match fun
    (($ $fun src meta () body)
     (visit-cont body))))

(define (compile/compost exp env source)
  (let ((cps ((@@ (language cps compile-bytecode) optimize)
              ((@@ (language cps compile-bytecode) fix-arities)
               (compile exp #:to 'cps #:env env))
              '()))
        (prompt (make-prompt-tag)))
    (call-with-prompt
     prompt
     (lambda ()
       (parameterize ((compilation-error-prompt prompt))
         (let ((fun (extract-fun cps)))
           (assert-compilable-function fun)
           (let ((dfg (compute-dfg fun #:global? #f)))
             (infer-types fun dfg)
             #f))))
     (lambda (k message args)
       (issue-compilation-warning (current-warning-port) message args source)
       #f))))
