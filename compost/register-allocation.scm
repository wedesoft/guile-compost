;;; compost
;;; Copyright (C) 2014 Andy Wingo <wingo@pobox.com>
;;; Copyright (C) 2013, 2014 Free Software Foundation, Inc.
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
;; Register allocator for compost.  Based on slot-allocation.scm in
;; Guile.
;;
;;; Code:

(define-module (compost register-allocation)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-26)
  #:use-module (language cps)
  #:use-module (language cps dfg)
  #:use-module (compost bitfield)
  #:use-module (compost error)
  #:export (allocate-registers
            lookup-register
            lookup-maybe-register
            lookup-constant-value
            lookup-maybe-constant-value
            lookup-parallel-moves))

(define-syntax define-enumeration
  (lambda (x)
    (syntax-case x ()
      ((_ all get-name name ...)
       (with-syntax (((n ...) (iota (length #'(name ...))))
                     (len (length #'(name ...))))
         #'(begin
             (define-syntax name (identifier-syntax n))
             ...
             (define-syntax all (identifier-syntax len))
             (define (get-name val)
               (vector-ref #(name ...) val))))))))

;; Only caller-save registers.
(define-enumeration &registers register-name
  ;; rdi gets the first GPR argument, and so on up to r9.
  &rdi
  &rsi
  &rdx
  &rcx
  &r8
  &r9
  &rax
  &r10
  &r11

  ;; Likewise, FPR arguments are passed in xmm0 to xmm7.
  &xmm0
  &xmm1
  &xmm2
  &xmm3
  &xmm4
  &xmm5
  &xmm6
  &xmm7
  &xmm8
  &xmm9
  &xmm10
  &xmm11
  &xmm12
  &xmm13
  &xmm14
  &xmm15)

(define-syntax &gpr (identifier-syntax (1- (ash 1 (1+ &r11)))))
(define-syntax &all-registers (identifier-syntax (1- (ash 1 &registers))))
(define-syntax &fpr (identifier-syntax (logand &all-registers (lognot &gpr))))

(define-record-type $allocation
  (make-allocation dfa regs
                   has-constv constant-values
                   parallel-moves)
  allocation?
  (dfa allocation-dfa)
  (regs allocation-regs)
  (has-constv allocation-has-constv)
  (constant-values allocation-constant-values)
  (parallel-moves allocation-parallel-moves))

(define (lookup-maybe-register sym allocation)
  (match allocation
    (($ $allocation dfa regs)
     (and=> (vector-ref regs (dfa-var-idx dfa sym))
            register-name))))

(define (lookup-register sym allocation)
  (or (lookup-maybe-register sym allocation)
      (error "Variable not allocated to a register" sym)))

(define (lookup-constant-value sym allocation)
  (match allocation
    (($ $allocation dfa regs has-constv constant-values)
     (let ((idx (dfa-var-idx dfa sym)))
       (if (bitvector-ref has-constv idx)
           (vector-ref constant-values idx)
           (error "Variable does not have constant value" sym))))))

(define (lookup-maybe-constant-value sym allocation)
  (match allocation
    (($ $allocation dfa regs has-constv constant-values)
     (let ((idx (dfa-var-idx dfa sym)))
       (values (bitvector-ref has-constv idx)
               (vector-ref constant-values idx))))))

(define (lookup-parallel-moves k allocation)
  (or (hashq-ref (allocation-parallel-moves allocation) k)
      (error "Continuation has no parallel moves" k)))

(define (parallel-move src dst tmp)
  "Solve the parallel move problem between src and dst reg lists, which
are comparable with eqv?.  A tmp reg may be used."

  ;; This algorithm is taken from: "Tilting at windmills with Coq:
  ;; formal verification of a compilation algorithm for parallel moves"
  ;; by Laurence Rideau, Bernard Paul Serpette, and Xavier Leroy
  ;; <http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf>

  (define (split-move moves reg)
    (let loop ((revhead '()) (tail moves))
      (match tail
        (((and s+d (s . d)) . rest)
         (if (eqv? s reg)
             (cons d (append-reverse revhead rest))
             (loop (cons s+d revhead) rest)))
        (_ #f))))

  (define (replace-last-source reg moves)
    (match moves
      ((moves ... (s . d))
       (append moves (list (cons reg d))))))

  (let loop ((to-move (map cons src dst))
             (being-moved '())
             (moved '())
             (last-source #f))
    ;; 'last-source' should always be equivalent to:
    ;; (and (pair? being-moved) (car (last being-moved)))
    (match being-moved
      (() (match to-move
            (() (reverse moved))
            (((and s+d (s . d)) . t1)
             (if (or (eqv? s d)         ; idempotent
                     (not s)) ; src is a constant and can be loaded directly
                 (loop t1 '() moved #f)
                 (loop t1 (list s+d) moved s)))))
      (((and s+d (s . d)) . b)
       (match (split-move to-move d)
         ((r . t1) (loop t1 (acons d r being-moved) moved last-source))
         (#f (match b
               (() (loop to-move '() (cons s+d moved) #f))
               (_ (if (eqv? d last-source)
                      (loop to-move
                        (replace-last-source tmp b)
                        (cons s+d (acons d tmp moved))
                        tmp)
                      (loop to-move b (cons s+d moved) last-source))))))))))

(define (dead-after-def? def-k v-idx dfa)
  (let ((l (dfa-k-idx dfa def-k)))
    (not (bitvector-ref (dfa-k-in dfa l) v-idx))))

(define (dead-after-use? use-k v-idx dfa)
  (let ((l (dfa-k-idx dfa use-k)))
    (not (bitvector-ref (dfa-k-out dfa l) v-idx))))

(define (find-first-zero n)
  ;; Naive implementation.
  (let lp ((reg 0))
    (cond
     ((>= reg &xmm15)
      (compilation-error #f "register allocation would spill"))
     ((logbit? reg n) (lp (1+ reg)))
     (else reg))))

(define (allocate-registers fun dfg reprs)
  (let* ((dfa (compute-live-variables fun dfg))
         (cfa (analyze-control-flow fun dfg))
         (usev (make-vector (cfa-k-count cfa) '()))
         (defv (make-vector (cfa-k-count cfa) '()))
         (contv (make-vector (cfa-k-count cfa) #f))
         (classes (make-vector (dfa-var-count dfa) 0))
         (regs (make-vector (dfa-var-count dfa) #f))
         (constant-values (make-vector (dfa-var-count dfa) #f))
         (has-constv (make-bitvector (dfa-var-count dfa) #f))
         (parallel-moves (make-hash-table)))

    (define (empty-live-regs) #b0)

    (define (add-live-reg reg live-regs)
      (logior live-regs (ash 1 reg)))

    (define (kill-dead-reg reg live-regs)
      (logand live-regs (lognot (ash 1 reg))))

    (define (compute-reg live-regs hint class)
      (let ((live-regs (logior live-regs (lognot class))))
        (if (and hint (not (logbit? hint live-regs)))
            hint
            (find-first-zero live-regs))))

    (define (recompute-live-regs k)
      (let ((in (dfa-k-in dfa (dfa-k-idx dfa k))))
        (let lp ((v 0) (live-regs (empty-live-regs)))
          (let ((v (bit-position #t in v)))
            (if v
                (let ((reg (vector-ref regs v)))
                  (lp (1+ v)
                      (if reg
                          (add-live-reg reg live-regs)
                          live-regs)))
                live-regs)))))

    (define* (allocate! var-idx hint live)
      (cond
       ((vector-ref regs var-idx) => (cut add-live-reg <> live))
       (else
        (let ((reg (compute-reg live hint (vector-ref classes var-idx))))
          #;
          (pk (dfa-var-sym dfa var-idx) (register-name reg))
          (vector-set! regs var-idx reg)
          (add-live-reg reg live)))))

    (define (solve-parallel-move src dst live)
      ;; Although some parallel moves may proceed without a temporary
      ;; reg, in general one is needed.  That temporary reg must not be
      ;; part of the source or destination sets, and that reg should not
      ;; correspond to a live variable.
      (define (compute-tmp-reg live class)
        (compute-reg live #f class))

      ;; Each parallel-move problem is actually two problems: one for
      ;; the GPR registers, and one for the FPRs.
      (let lp ((src src) (dst dst)
               (gpr-src '()) (gpr-dst '())
               (fpr-src '()) (fpr-dst '()))
        (match (cons src dst)
          ((() . ())
           (append (parallel-move (reverse gpr-src) (reverse gpr-dst)
                                  (register-name
                                   (compute-tmp-reg live &gpr)))
                   (parallel-move (reverse fpr-src) (reverse fpr-dst)
                                  (register-name
                                   (compute-tmp-reg live &fpr)))))
          (((src . src*) . (dst . dst*))
           (if (< src &xmm0)
               (lp src* dst*
                   (cons (register-name src) gpr-src)
                   (cons (register-name dst) gpr-dst)
                   fpr-src fpr-dst)
               (lp src* dst*
                   gpr-src gpr-dst
                   (cons (register-name src) fpr-src)
                   (cons (register-name dst) fpr-dst)))))))

    ;; Find variables that are actually constant.
    (define (compute-constants!)
      (let lp ((n 0))
        (when (< n (vector-length constant-values))
          (let ((sym (dfa-var-sym dfa n)))
            (call-with-values (lambda () (find-constant-value sym dfg))
              (lambda (has-const? const)
                (when has-const?
                  (bitvector-set! has-constv n has-const?)
                  (vector-set! constant-values n const))
                (lp (1+ n))))))))

    (define (compute-register-classes!)
      (let lp ((n 0))
        (when (< n (vector-length classes))
          (vector-set! classes n
                       (case (hashq-ref reprs (dfa-var-sym dfa n))
                         ((gpr) &gpr)
                         ((fpr) &fpr)
                         (else 0)))
          (lp (1+ n)))))

    ;; Transform the DFG's continuation table to a vector, for easy
    ;; access.
    (define (compute-conts!)
      (let ((cont-table (dfg-cont-table dfg)))
        (let lp ((n 0))
          (when (< n (vector-length contv))
            (vector-set! contv n (lookup-cont (cfa-k-sym cfa n) cont-table))
            (lp (1+ n))))))

    ;; Record uses and defs, as lists of variable indexes, indexed by
    ;; CFA continuation index.
    (define (compute-uses-and-defs!)
      (let lp ((n 0))
        (when (< n (vector-length usev))
          (match (vector-ref contv n)
            (($ $kentry self)
             (vector-set! defv n (list (dfa-var-idx dfa self))))
            (($ $kargs names syms body)
             (vector-set! defv n (map (cut dfa-var-idx dfa <>) syms))
             (vector-set! usev n
                          (map (cut dfa-var-idx dfa <>)
                               (match (find-expression body)
                                 (($ $call proc args)
                                  (cons proc args))
                                 (($ $callk k proc args)
                                  (cons proc args))
                                 (($ $primcall name args)
                                  args)
                                 (($ $values args)
                                  args)
                                 (($ $prompt escape? tag handler)
                                  (list tag))
                                 (_ '())))))
            (_ #f))
          (lp (1+ n)))))

    (define (allocate-values label k uses pre-live post-live)
      (match (vector-ref contv (cfa-k-idx cfa k))
        (($ $ktail)
         (match uses
           (()
            (hashq-set! parallel-moves label '()))
           ((use)
            (let* ((src-reg (vector-ref regs use))
                   (dst-reg (if (< src-reg &xmm0) &rax &xmm0))
                   (result-live (ash 1 dst-reg))
                   (moves (solve-parallel-move (list src-reg) (list dst-reg)
                                               (logior pre-live result-live))))
              (hashq-set! parallel-moves label moves)))
           (uses
            (compilation-error #f "multiple-value return"))))
        (($ $kargs)
         (let* ((src-regs (map (cut vector-ref regs <>) uses))
                (dst-vars (vector-ref defv (cfa-k-idx cfa k)))
                (result-live (fold allocate! post-live dst-vars src-regs))
                (dst-regs (map (cut vector-ref regs <>) dst-vars))
                (moves (solve-parallel-move src-regs dst-regs
                                            (logior pre-live result-live))))
           (hashq-set! parallel-moves label moves)))
        (($ $kif) #f)))

    (define (allocate-defs! n live)
      (fold (cut allocate! <> #f <>) live (vector-ref defv n)))

    ;; This traversal will visit definitions before uses, as
    ;; definitions dominate uses and a block's dominator will appear
    ;; before it, in reverse post-order.
    (define (visit-clause n live)
      (let lp ((n n) (live live))
        (define (kill-dead live vars-by-cfa-idx pred)
          (fold (lambda (v live)
                  (let ((reg (vector-ref regs v)))
                    (if (and reg (pred (cfa-k-sym cfa n) v dfa))
                        (kill-dead-reg reg live)
                        live)))
                live
                (vector-ref vars-by-cfa-idx n)))
        (define (kill-dead-defs live)
          (kill-dead live defv dead-after-def?))
        (define (kill-dead-uses live)
          (kill-dead live usev dead-after-use?))
        (if (= n (cfa-k-count cfa))
            n
            (let* ((label (cfa-k-sym cfa n))
                   (live (if (control-point? label dfg)
                             (recompute-live-regs label)
                             live))
                   (live (kill-dead-defs (allocate-defs! n live)))
                   (post-live (kill-dead-uses live)))
              ;; LIVE are the live regs coming into the term.
              ;; POST-LIVE is the subset that is still live after the
              ;; term uses its inputs.
              (match (vector-ref contv n)
                (($ $kclause) n)
                (($ $kargs names syms body)
                 (let ((uses (vector-ref usev n)))
                   (match (find-call body)
                     (($ $continue k src ($ $const)) #t)
                     (($ $continue k src ($ $void)) #t)
                     (($ $continue k src ($ $primcall)) #t)
                     (($ $continue k src ($ $values))
                      (allocate-values label k uses live post-live))))
                 (lp (1+ n) post-live))
                ((or ($ $kif) ($ $ktail))
                 (lp (1+ n) post-live)))))))

    (define (visit-entry)
      (define (visit-clauses n)
        (match (vector-ref contv n)
          (($ $kclause arity ($ $cont kbody ($ $kargs names)))
           (unless (eq? (cfa-k-sym cfa (1+ n)) kbody)
             (error "Unexpected CFA order"))
           (let ((next (visit-clause (1+ n) (empty-live-regs))))
             (when (< next (cfa-k-count cfa))
               (visit-clauses next))))))
      (match (vector-ref contv 0)
        (($ $kentry)
         (visit-clauses 1))))

    (compute-conts!)
    (compute-constants!)
    (compute-register-classes!)
    (compute-uses-and-defs!)
    (visit-entry)

    (make-allocation dfa regs has-constv constant-values parallel-moves)))
