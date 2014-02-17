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
;; x86-64 assembler.  Based on Guile's (system vm assembler), which has
;; more comments.
;;
;;; Code:

(define-module (compost assembler)
  #:use-module (system vm dwarf)
  #:use-module (system vm elf)
  #:use-module (system vm linker)
  #:use-module (rnrs bytevectors)
  #:use-module (ice-9 binary-ports)
  #:use-module (ice-9 vlist)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-4)
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-11)
  #:export (make-assembler

            emit-source
            emit-begin-program
            emit-end-program
            emit-label

            emit-add
            emit-add1
            emit-mul
            emit-div
            emit-sqrt
            emit-br
            emit-mov
            emit-bv-f32-ref
            emit-bv-f32-set!
            emit-br-if-true
            emit-br-if-eq
            emit-br-if-<
            emit-br-if-<=
            emit-br-if-=
            emit-return
            emit-return-void
            emit-load-constant

            link-assembly))




;;; A <meta> entry collects metadata for one procedure.  Procedures are
;;; written as contiguous ranges of bytecode.
;;;
(define-syntax-rule (assert-match arg pattern kind)
  (let ((x arg))
    (unless (match x (pattern #t) (_ #f))
      (error (string-append "expected " kind) x))))

(define-record-type <meta>
  (%make-meta label properties low-pc high-pc arities)
  meta?
  (label meta-label)
  (properties meta-properties set-meta-properties!)
  (low-pc meta-low-pc)
  (high-pc meta-high-pc set-meta-high-pc!)
  (arities meta-arities set-meta-arities!))

(define (make-meta label properties low-pc)
  (assert-match label (? symbol?) "symbol")
  (assert-match properties (((? symbol?) . _) ...) "alist with symbolic keys")
  (%make-meta label properties low-pc #f '()))

(define (meta-name meta)
  (assq-ref (meta-properties meta) 'name))

(define-syntax *block-size* (identifier-syntax 256))

;;; An assembler collects all of the words emitted during assembly, and
;;; also maintains ancillary information such as the constant table, a
;;; relocation list, and so on.
;;;
(define-record-type <asm>
  (make-asm cur idx prev written
            labels relocs
            flonums
            shstrtab next-section-number
            meta sources)
  asm?

  ;; We write bytecode into what is logically a growable vector,
  ;; implemented as a list of blocks.  asm-cur is the current block, and
  ;; asm-idx is the current index into that block, in bytes.
  ;;
  (cur asm-cur set-asm-cur!)
  (idx asm-idx set-asm-idx!)

  ;; The list of previously written blocks.
  ;;
  (prev asm-prev set-asm-prev!)

  ;; The number of bytes written in asm-prev, which is the same as the
  ;; offset of the current block.
  ;;
  (written asm-written set-asm-written!)

  ;; An alist of symbol -> position pairs, indicating the labels defined
  ;; in this compilation unit.
  ;;
  (labels asm-labels set-asm-labels!)

  ;; A list of relocations needed by the program text.  We use an
  ;; internal representation for relocations, and handle textual
  ;; relative relocations in the assembler.  Other kinds of relocations
  ;; are later reified as linker relocations and resolved by the linker.
  ;;
  (relocs asm-relocs set-asm-relocs!)

  ;; The constant table, as a vhash of object -> label.  All flonums
  ;; get de-duplicated and written into the .rodata section.
  ;;
  (flonums asm-flonums set-asm-flonums!)

  ;; The shstrtab, for section names.
  ;;
  (shstrtab asm-shstrtab set-asm-shstrtab!)

  ;; The section number for the next section to be written.
  ;;
  (next-section-number asm-next-section-number set-asm-next-section-number!)

  ;; A list of <meta>, corresponding to procedure metadata.
  ;;
  (meta asm-meta set-asm-meta!)

  ;; A list of (pos . source) pairs, indicating source information.  POS
  ;; is relative to the beginning of the text section, and SOURCE is in
  ;; the same format that source-properties returns.
  ;;
  (sources asm-sources set-asm-sources!))

(define-inlinable (fresh-block)
  (make-bytevector *block-size*))

(define (make-assembler)
  "Create an assembler for a given target @var{word-size} and
@var{endianness}, falling back to appropriate values for the configured
target."
  (make-asm (fresh-block) 0 '() 0
            (make-hash-table) '()
            vlist-null
            (make-string-table) 1
            '() '()))

(define (intern-section-name! asm string)
  "Add a string to the section name table (shstrtab)."
  (string-table-intern! (asm-shstrtab asm) string))

(define-inlinable (asm-pos asm)
  "The offset of the next word to be written into the code buffer, in
bytes."
  (+ (asm-idx asm) (asm-written asm)))

(define (allocate-new-block asm)
  "Close off the current block, and arrange for the next word to be
written to a fresh block."
  (let ((new (fresh-block)))
    (set-asm-prev! asm (cons (asm-cur asm) (asm-prev asm)))
    (set-asm-written! asm (asm-pos asm))
    (set-asm-cur! asm new)
    (set-asm-idx! asm 0)))

(define-inlinable (emit-u8 asm byte)
  "Emit one byte word into the instruction stream.  Assumes that there
is space for the byte, and ensures that there is space for the next
byte."
  (bytevector-u8-set! (asm-cur asm) (asm-idx asm) byte)
  (set-asm-idx! asm (1+ (asm-idx asm)))
  (if (= (asm-idx asm) *block-size*)
      (allocate-new-block asm)))

(define-inlinable (make-reloc label pos offset)
  "Make an internal relocation of referencing symbol @var{label},
@var{offset} bytes after position @var{pos}.  The signed 32-bit word at
position pos + offset will get patched up by the assembler, if the
reference is within the same compilation unit, or by the assembler."
  (list label pos offset))

(define (record-label-reference asm label offset)
  "Record an local label reference.  This 32-bit value will get patched
up later by the assembler."
  (let ((reloc (make-reloc label (asm-pos asm) offset)))
    (set-asm-relocs! asm (cons reloc (asm-relocs asm)))))

(define-inlinable (immediate? x)
  "Return @code{#t} if @var{x} is immediate, and @code{#f} otherwise."
  (not (zero? (logand (object-address x) 6))))

(define (intern-flonum asm obj)
  (let ((obj (exact->inexact obj)))
    (unless (real? obj)
      (error "not a flonum" obj))
    (cond
     ((vhash-assoc obj (asm-flonums asm)) => cdr)
     (else
      (let ((label (gensym "constant")))
        (set-asm-flonums! asm (vhash-cons obj label (asm-flonums asm)))
        label)))))

(define general-purpose-registers (make-hash-table))
(define xmm-registers (make-hash-table))

(for-each
 (match-lambda
  ((sym . val)
   (hashq-set! general-purpose-registers sym val)))
 '((&rax . 0)
   (&rcx . 1)
   (&rdx . 2)
   (&rbx . 3)
   (&rsp . 4)
   (&rbp . 5)
   (&rsi . 6)
   (&rdi . 7)
   (&r8 . 8)
   (&r9 . 9)
   (&r10 . 10)
   (&r11 . 11)
   (&r12 . 12)
   (&r13 . 13)
   (&r14 . 14)
   (&r15 . 15)))

(for-each
 (match-lambda
  ((sym . val)
   (hashq-set! xmm-registers sym val)))
 '((&xmm0 . 0)
   (&xmm1 . 1)
   (&xmm2 . 2)
   (&xmm3 . 3)
   (&xmm4 . 4)
   (&xmm5 . 5)
   (&xmm6 . 6)
   (&xmm7 . 7)
   (&xmm8 . 8)
   (&xmm9 . 9)
   (&xmm10 . 10)
   (&xmm11 . 11)
   (&xmm12 . 12)
   (&xmm13 . 13)
   (&xmm14 . 14)
   (&xmm15 . 15)))

(define (gp-register-code reg)
  (hashq-ref general-purpose-registers reg))

(define (xmm-register-code reg)
  (hashq-ref xmm-registers reg))

(define (emit-u32 asm u32)
  (let ((bv (make-bytevector 4)))
    (bytevector-u32-native-set! bv 0 u32)
    (emit-u8 asm (bytevector-u8-ref bv 0))
    (emit-u8 asm (bytevector-u8-ref bv 1))
    (emit-u8 asm (bytevector-u8-ref bv 2))
    (emit-u8 asm (bytevector-u8-ref bv 3))))

(define (emit-u64 asm u64)
  (let ((bv (make-bytevector 8)))
    (bytevector-u64-native-set! bv 0 u64)
    (emit-u8 asm (bytevector-u8-ref bv 0))
    (emit-u8 asm (bytevector-u8-ref bv 1))
    (emit-u8 asm (bytevector-u8-ref bv 2))
    (emit-u8 asm (bytevector-u8-ref bv 3))
    (emit-u8 asm (bytevector-u8-ref bv 4))
    (emit-u8 asm (bytevector-u8-ref bv 5))
    (emit-u8 asm (bytevector-u8-ref bv 6))
    (emit-u8 asm (bytevector-u8-ref bv 7))))

(define (emit-br asm label)
  (emit-u8 asm #xe9)
  (emit-u32 asm 0)
  (record-label-reference asm label -4))

(define (emit-rex64 asm a b)
  (emit-u8 asm (logior #x48
                       (ash (logand a #x8) -1)
                       (ash (logand b #x8) -3))))

(define (emit-modrm/disp0 asm a b)
  (emit-u8 asm (logior (ash (logand a #x7) 3)
                       (logand b #x7))))

(define (emit-modrm/disp8 asm a b)
  (emit-u8 asm (logior #x40
                       (ash (logand a #x7) 3)
                       (logand b #x7))))

(define (emit-modrm/disp32 asm a b)
  (emit-u8 asm (logior #x80
                       (ash (logand a #x7) 3)
                       (logand b #x7))))

(define (emit-modrm/reg asm a b)
  (emit-u8 asm (logior #xc0
                       (ash (logand a #x7) 3)
                       (logand b #x7))))

(define (emit-movq asm dst src)
  (emit-rex64 asm dst src)
  (emit-u8 asm #x8b)
  (emit-modrm/reg asm dst src))

(define (emit-movq/imm asm dst bits)
  (emit-rex64 asm 0 dst)
  (emit-u8 asm (logior #xb8 (logand dst #x7)))
  (emit-u64 asm bits))

(define (emit-mov asm dst src)
  (cond
   ((xmm-register-code dst)
    => (lambda (xmm)
         (emit-movsd asm xmm (xmm-register-code src))))
   (else
    (emit-movq asm (gp-register-code dst) (gp-register-code src)))))

(define (make-operand/base+index+disp8 base index disp)
  (u8vector
   ;; REX.
   (ash (logior (ash (logand index #x8) 1) (logand disp #x8)) -3)
   ;; ModR/M.
   (logior (ash 1 6) (gp-register-code '&rsp))
   ;; SIB.
   (logior (ash (logand index #x7) 3) (logand base #x7))
   ;; Disp.
   16))

(define (emit-optional-rex32 asm a b)
  (let ((rex-bits (logior (ash (logand a #x8) -1)
                          (ash (logand b #x8) -3))))
    (unless (zero? rex-bits)
      (emit-u8 asm (logior #x40 rex-bits)))))

(define (emit-optional-rex32/mem asm xmm mem)
  (let ((rex-bits (logior (ash (logand xmm #x8) -1)
                          (bytevector-u8-ref mem 0))))
    (unless (zero? rex-bits)
      (emit-u8 asm (logior #x40 rex-bits)))))

(define (emit-operand/mem asm code mem)
  (let ((length (bytevector-length mem)))
    (emit-u8 asm (logior (bytevector-u8-ref mem 1)
                         (ash (logand code #x7) 3)))
    (let lp ((n 2))
      (when (< n length)
        (emit-u8 asm (bytevector-u8-ref mem n))
        (lp (1+ n))))))

(define (emit-cvtsd2ss asm dst src)
  (emit-u8 asm #xf2)
  (emit-optional-rex32 asm dst src)
  (emit-u8 asm #x0f)
  (emit-u8 asm #x5a)
  (emit-modrm/reg asm dst src))

(define (emit-cvtss2sd/mem asm dst mem)
  (emit-u8 asm #xf3)
  (emit-optional-rex32/mem asm dst mem)
  (emit-u8 asm #x0f)
  (emit-u8 asm #x5a)
  (emit-operand/mem asm dst mem))

(define (emit-movss/store asm src mem)
  (emit-u8 asm #xf3)
  (emit-optional-rex32/mem asm src mem)
  (emit-u8 asm #x0f)
  (emit-u8 asm #x11)
  (emit-operand/mem asm src mem))

(define (emit-movsd asm dst src)
  (emit-u8 asm #xf2)
  (emit-optional-rex32 asm dst src)
  (emit-u8 asm #x0f)
  (emit-u8 asm #x10)
  (emit-modrm/reg asm dst src))

(define (emit-movsd/load asm dst label)
  (emit-u8 asm #xf2)
  (emit-optional-rex32 asm dst 0)
  (emit-u8 asm #x0f)
  (emit-u8 asm #x10)
  (emit-modrm/disp0 asm dst 5) ; ebp = 5
  (record-label-reference asm label 0)
  (emit-u32 asm 0))

(define (emit-bv-f32-set! asm bv idx val)
  ;; FIXME: use tmp register
  (emit-cvtsd2ss asm (xmm-register-code val) (xmm-register-code val))
  (emit-movss/store asm
                    (xmm-register-code val)
                    (make-operand/base+index+disp8 (gp-register-code bv)
                                                   (gp-register-code idx)
                                                   16)))

(define (emit-bv-f32-ref asm dst bv idx)
  (emit-cvtss2sd/mem asm
                     (xmm-register-code dst)
                     (make-operand/base+index+disp8 (gp-register-code bv)
                                                    (gp-register-code idx)
                                                    16)))

(define (emit-addsd asm dst a b)
  (cond
   ((eqv? dst a)
    (emit-u8 asm #xf2)
    (emit-optional-rex32 asm dst b)
    (emit-u8 asm #x0f)
    (emit-u8 asm #x58)
    (emit-modrm/reg asm dst b))
   ((eqv? dst b)
    (emit-addsd asm dst b a))
   (else
    (emit-movsd asm dst a)
    (emit-addsd asm dst dst b))))

(define (emit-addq asm dst a b)
  (cond
   ((eqv? dst a)
    (emit-rex64 asm dst b)
    (emit-u8 asm #x03)
    (emit-modrm/reg asm dst b))
   ((eqv? dst b)
    (emit-addq asm dst b a))
   (else
    (emit-movq asm dst a)
    (emit-addq asm dst dst b))))

(define (emit-add asm dst a b)
  (cond
   ((xmm-register-code dst)
    => (lambda (dst)
         (emit-addsd asm dst (xmm-register-code a) (xmm-register-code b))))
   (else
    (emit-addq asm (gp-register-code dst)
               (gp-register-code a)  (gp-register-code b)))))

(define (emit-add1 asm dst a)
  (let ((dst (gp-register-code dst))
        (a (gp-register-code a)))
    (unless (eqv? dst a)
      (emit-movq asm dst a))
    (emit-rex64 asm 0 dst)
    (emit-u8 asm #xff)
    (emit-modrm/reg asm 0 dst)))

(define (emit-mulsd asm dst a b)
  (cond
   ((eqv? dst a)
    (emit-u8 asm #xf2)
    (emit-optional-rex32 asm dst b)
    (emit-u8 asm #x0f)
    (emit-u8 asm #x59)
    (emit-modrm/reg asm dst b))
   ((eqv? dst b)
    (emit-mulsd asm dst b a))
   (else
    (emit-movsd asm dst a)
    (emit-mulsd asm dst dst b))))

(define (emit-imulq asm dst a b)
  (cond
   ((eqv? dst a)
    (emit-rex64 asm dst b)
    (emit-u8 asm #x0f)
    (emit-u8 asm #xaf)
    (emit-modrm/reg asm dst b))
   ((eqv? dst b)
    (emit-imulq asm dst b a))
   (else
    (emit-movq asm dst a)
    (emit-imulq asm dst dst b))))

(define (emit-mul asm dst a b)
  (cond
   ((xmm-register-code dst)
    => (lambda (dst)
         (emit-mulsd asm dst (xmm-register-code a) (xmm-register-code b))))
   (else
    (emit-imulq asm (gp-register-code dst)
                (gp-register-code a)  (gp-register-code b)))))

(define (emit-divsd asm dst a b)
  (cond
   ((eqv? dst a)
    (emit-u8 asm #xf2)
    (emit-optional-rex32 asm dst b)
    (emit-u8 asm #x0f)
    (emit-u8 asm #x5e)
    (emit-modrm/reg asm dst b))
   ((eqv? dst b)
    (emit-divsd asm dst b a))
   (else
    (emit-movsd asm dst a)
    (emit-divsd asm dst dst b))))

(define (emit-div asm dst a b)
  (emit-divsd asm (xmm-register-code dst)
              (xmm-register-code a) (xmm-register-code b)))

(define (emit-sqrtsd asm dst a)
  (emit-u8 asm #xf2)
  (emit-optional-rex32 asm dst a)
  (emit-u8 asm #x0f)
  (emit-u8 asm #x51)
  (emit-modrm/reg asm dst a))

(define (emit-sqrt asm dst a)
  (emit-sqrtsd asm (xmm-register-code dst) (xmm-register-code a)))

(define (emit-cmpq asm a b)
  (emit-rex64 asm a b)
  (emit-u8 asm #x3b)
  (emit-modrm/reg asm b a))

(define (emit-jge asm label)
  (emit-u8 asm #x0f)
  (emit-u8 asm #x8d)
  (emit-u32 asm 0)
  (record-label-reference asm label -4))

(define (emit-jl asm label)
  (emit-u8 asm #x0f)
  (emit-u8 asm #x8c)
  (emit-u32 asm 0)
  (record-label-reference asm label -4))

(define (emit-br-if-true asm var invert? label)
  (error "unimplemented" 'br-if-true var))
(define (emit-br-if-eq asm a b invert? label)
  (error "unimplemented" 'br-if-eq a b))
(define (emit-br-if-< asm a b invert? label)
  (emit-cmpq asm (gp-register-code a) (gp-register-code b))
  (if invert?
      (emit-jge asm label)
      (emit-jl asm label)))
(define (emit-br-if-<= asm a b invert? label)
  (error "unimplemented" 'br-if-<= a b))
(define (emit-br-if-= asm a b invert? label)
  (error "unimplemented" 'br-if-= a b))

(define (emit-return asm val)
  (unless (eq? val '&rax)
    (emit-mov asm '&rax val))
  (emit-return-void asm))

(define (emit-return-void asm)
  (emit-u8 asm #xc3))

(define (emit-load-constant asm dst obj)
  (cond
   ((xmm-register-code dst)
    => (lambda (xmm)
         (emit-movsd/load asm xmm (intern-flonum asm obj))))
   (else
    (unless (exact-integer? obj)
      (error "not an exact integer" obj))
    (emit-movq/imm asm (gp-register-code dst) obj))))

(define (emit-begin-program asm label properties)
  (emit-label asm label)
  (let ((meta (make-meta label properties (asm-pos asm))))
    (set-asm-meta! asm (cons meta (asm-meta asm)))))

(define (emit-end-program asm)
  (let ((meta (car (asm-meta asm))))
    (set-meta-high-pc! meta (asm-pos asm))
    (set-meta-arities! meta (reverse (meta-arities meta)))))

(define (emit-label asm sym)
  (hashq-set! (asm-labels asm) sym (asm-pos asm)))

(define (emit-source asm source)
  (set-asm-sources! asm (acons (asm-pos asm) source (asm-sources asm))))

(define (make-object asm name bv relocs labels . kwargs)
  "Make a linker object.  This helper handles interning the name in the
shstrtab, assigning the size, allocating a fresh index, and defining a
corresponding linker symbol for the start of the section."
  (let ((name-idx (intern-section-name! asm (symbol->string name)))
        (index (asm-next-section-number asm)))
    (set-asm-next-section-number! asm (1+ index))
    (make-linker-object (apply make-elf-section
                               #:index index
                               #:name name-idx
                               #:size (bytevector-length bv)
                               kwargs)
                        bv relocs
                        (cons (make-linker-symbol name 0) labels))))

(define (link-flonums asm)
  (let ((data (asm-flonums asm)))
    (cond
     ((vlist-null? data) #f)
     (else
      (let* ((byte-len (* (vlist-length data) 8))
             (buf (make-bytevector byte-len 0)))
        (let lp ((i 0) (pos 0) (symbols '()))
          (if (< i (vlist-length data))
              (let* ((pair (vlist-ref data i))
                     (obj (car pair))
                     (obj-label (cdr pair)))
                (bytevector-ieee-double-native-set! buf pos obj)
                (lp (1+ i)
                    (+ pos 8)
                    (cons (make-linker-symbol obj-label pos) symbols)))
              (make-object asm '.rodata buf '() symbols
                           #:flags SHF_ALLOC))))))))

;; FIXME
(define (process-relocs buf relocs labels)
  (fold
   (lambda (reloc tail)
     (match reloc
       ((label base offset)
        (let ((abs (hashq-ref labels label))
              (dst (+ base offset)))
          (if abs
              (let ((rel (- abs base)))
                (bytevector-s32-native-set! buf dst rel)
                tail)
              (cons (make-linker-reloc 'rel32/1 dst offset label)
                    tail))))))
   '()
   relocs))

(define (process-labels labels)
  "Define linker symbols for the label-offset map in @var{labels}.
The offsets are expected to be expressed in bytes."
  (hash-map->list make-linker-symbol labels))

(define (link-text-object asm)
  "Link the .text section."
  (let ((buf (make-bytevector (asm-pos asm))))
    (let lp ((pos 0) (prev (reverse (asm-prev asm))))
      (if (null? prev)
          (let ((byte-size (asm-idx asm)))
            (bytevector-copy! (asm-cur asm) 0 buf pos byte-size)
            (make-object asm '.text
                         buf
                         (process-relocs buf (asm-relocs asm)
                                         (asm-labels asm))
                         (process-labels (asm-labels asm))
                         #:flags (logior SHF_ALLOC SHF_EXECINSTR)))
          (let ((len *block-size*))
            (bytevector-copy! (car prev) 0 buf pos len)
            (lp (+ pos len) (cdr prev)))))))



;;;
;;; Linking other sections of the ELF file, like the dynamic segment,
;;; the symbol table, etc.
;;;

(define (link-dynamic-section asm text strsz)
  "Link the dynamic section for an ELF image with @var{text}."
  (let ((buf (u64vector DT_STRTAB 0
                        DT_SYMTAB 0
                        DT_STRSZ strsz
                        DT_SYMENT (elf-symbol-len 8)
                        DT_NULL 0))
        (relocs (list (make-linker-reloc 'abs64/1 8 0 '.dynstr)
                      (make-linker-reloc 'abs64/1 24 0 '.dynsym))))
    (make-object asm '.dynamic buf relocs '()
                 #:type SHT_DYNAMIC #:flags SHF_ALLOC)))

(define (link-shstrtab asm)
  "Link the string table for the section headers."
  (intern-section-name! asm ".shstrtab")
  (make-object asm '.shstrtab
               (link-string-table! (asm-shstrtab asm))
               '() '()
               #:type SHT_STRTAB #:flags 0))

(define (elf-symbol-hash str)
  (let ((bv (string->utf8 str)))
    (let lp ((h 0) (n 0))
      (cond
       ((< n (bytevector-length bv))
        (let* ((h (+ (logand (ash h 4) #xffffffff)
                    (bytevector-u8-ref bv n)))
               (g (logand h #xf0000000))
               (h (if (zero? g) h (logxor h (ash g -24))))
               (h (logand h (lognot g))))
          (lp h (1+ n))))
       (else h)))))

;; ♥ ♥ ♥  peval completely unrolls this  ♥ ♥ ♥
(define (choose-nbuckets n)
  (let ((sizes #(7 23 47 113 223)))
    (let lp ((idx 0))
      (if (or (= (1+ idx) (vector-length sizes))
              (< n (vector-ref sizes idx)))
          (vector-ref sizes idx)
          (lp (1+ idx))))))

(define (link-hash asm)
  (let* ((word-size 8)
         (names (cons "" (map (compose symbol->string meta-name)
                              (reverse (asm-meta asm)))))
         (nchains (length names))
         (nbuckets (choose-nbuckets nchains))
         (bv (make-bytevector (* (+ 2 nchains nbuckets) 4) 0)))
    (define STN_UNDEF 0)
    (u32vector-set! bv 0 nbuckets)
    (u32vector-set! bv 1 nchains)
    (let lp ((n 0))
      (when (< n nbuckets)
        (u32vector-set! bv (+ 2 n) STN_UNDEF)
        (lp (1+ n))))
    (let lp ((n 0) (names names))
      (when (< n nchains)
        (let* ((bucket (modulo (elf-symbol-hash (car names)) nbuckets))
               (existing (u32vector-ref bv (+ 2 bucket))))
          (u32vector-set! bv (+ 2 bucket) n)
          (u32vector-set! bv (+ 2 nbuckets n) existing)
          (lp (1+ n) (cdr names)))))
    (make-object asm '.hash bv '() '()
                 #:type SHT_HASH #:flags SHF_ALLOC)))

(define (link-dynsym asm text-section)
  (let* ((word-size 8)
         (size (elf-symbol-len word-size))
         (meta (reverse (asm-meta asm)))
         (n (length meta))
         (strtab (make-string-table))
         (bv (make-bytevector (* (1+ n) size) 0)))
    (define (intern-string! name)
      (string-table-intern! strtab (if name (symbol->string name) "")))
    (write-elf-symbol bv 0 (endianness little) word-size
                      (make-elf-symbol
                       #:name 0 #:value 0 #:size 0 #:type STT_NOTYPE
                       #:binding STB_LOCAL #:visibility STV_DEFAULT
                       #:shndx 0))
    (for-each
     (lambda (meta n)
       (let ((name (intern-string! (meta-name meta))))
         (write-elf-symbol bv (* (1+ n) size) (endianness little) word-size
                           (make-elf-symbol
                            #:name name
                            #:value (meta-low-pc meta)
                            #:size (- (meta-high-pc meta) (meta-low-pc meta))
                            #:type STT_FUNC
                            #:binding STB_GLOBAL
                            #:visibility STV_DEFAULT
                            #:shndx (elf-section-index text-section)))))
     meta (iota n))
    (let ((strtab (make-object asm '.dynstr
                               (link-string-table! strtab)
                               '() '()
                               #:type SHT_STRTAB #:flags SHF_ALLOC)))
      (values (make-object asm '.dynsym
                           bv
                           (map (lambda (meta n)
                                  (make-linker-reloc
                                   'abs64/1
                                   (+ (* (1+ n) size)
                                      (elf-symbol-value-offset word-size))
                                   0
                                   (meta-label meta)))
                                meta (iota n))
                           '()
                           #:type SHT_DYNSYM #:flags SHF_ALLOC #:entsize size
                           #:info 1 #:link (elf-section-index
                                            (linker-object-section strtab)))
              strtab
              (link-hash asm)))))

;;;
;;; The DWARF .debug_info, .debug_abbrev, .debug_str, and .debug_loc
;;; sections provide line number and local variable liveness
;;; information.  Their format is defined by the DWARF
;;; specifications.
;;;

;; -> 5 values: .debug_info, .debug_abbrev, .debug_str, .debug_loc, .debug_lines
(define (link-debug asm)
  (define (put-s8 port val)
    (let ((bv (make-bytevector 1)))
      (bytevector-s8-set! bv 0 val)
      (put-bytevector port bv)))

  (define (put-u16 port val)
    (let ((bv (make-bytevector 2)))
      (bytevector-u16-native-set! bv 0 val)
      (put-bytevector port bv)))

  (define (put-u32 port val)
    (let ((bv (make-bytevector 4)))
      (bytevector-u32-native-set! bv 0 val)
      (put-bytevector port bv)))

  (define (put-u64 port val)
    (let ((bv (make-bytevector 8)))
      (bytevector-u64-native-set! bv 0 val)
      (put-bytevector port bv)))

  (define (put-uleb128 port val)
    (let lp ((val val))
      (let ((next (ash val -7)))
        (if (zero? next)
            (put-u8 port val)
            (begin
              (put-u8 port (logior #x80 (logand val #x7f)))
              (lp next))))))

  (define (put-sleb128 port val)
    (let lp ((val val))
      (if (<= 0 (+ val 64) 127)
          (put-u8 port (logand val #x7f))
          (begin
            (put-u8 port (logior #x80 (logand val #x7f)))
            (lp (ash val -7))))))

  (define (port-position port)
    (seek port 0 SEEK_CUR))

  (define (meta->subprogram-die meta)
    `(subprogram
      (@ ,@(cond
            ((meta-name meta)
             => (lambda (name) `((name ,(symbol->string name)))))
            (else
             '()))
         (low-pc ,(meta-label meta))
         (high-pc ,(- (meta-high-pc meta) (meta-low-pc meta))))))

  (define (make-compile-unit-die asm)
    `(compile-unit
      (@ (producer ,(string-append "Guile " (version)))
         (language scheme)
         (low-pc .text)
         (high-pc ,(asm-pos asm))
         (stmt-list 0))
      ,@(map meta->subprogram-die (reverse (asm-meta asm)))))

  (let-values (((die-port get-die-bv) (open-bytevector-output-port))
               ((die-relocs) '())
               ((abbrev-port get-abbrev-bv) (open-bytevector-output-port))
               ;; (tag has-kids? attrs forms) -> code
               ((abbrevs) vlist-null)
               ((strtab) (make-string-table))
               ((line-port get-line-bv) (open-bytevector-output-port))
               ((line-relocs) '())
               ;; file -> code
               ((files) vlist-null))

    (define (write-abbrev code tag has-children? attrs forms)
      (put-uleb128 abbrev-port code)
      (put-uleb128 abbrev-port (tag-name->code tag))
      (put-u8 abbrev-port (children-name->code (if has-children? 'yes 'no)))
      (for-each (lambda (attr form)
                  (put-uleb128 abbrev-port (attribute-name->code attr))
                  (put-uleb128 abbrev-port (form-name->code form)))
                attrs forms)
      (put-uleb128 abbrev-port 0)
      (put-uleb128 abbrev-port 0))

    (define (intern-abbrev tag has-children? attrs forms)
      (let ((key (list tag has-children? attrs forms)))
        (match (vhash-assoc key abbrevs)
          ((_ . code) code)
          (#f (let ((code (1+ (vlist-length abbrevs))))
                (set! abbrevs (vhash-cons key code abbrevs))
                (write-abbrev code tag has-children? attrs forms)
                code)))))

    (define (intern-file file)
      (match (vhash-assoc file files)
        ((_ . code) code)
        (#f (let ((code (1+ (vlist-length files))))
              (set! files (vhash-cons file code files))
              code))))

    (define (write-sources)
      ;; Choose line base and line range values that will allow for an
      ;; address advance range of 16 bytes.  The special opcode range is
      ;; from 10 to 255, so 246 values.
      (define base -4)
      (define range 15)

      (let lp ((sources (asm-sources asm)) (out '()))
        (match sources
          (((pc . s) . sources)
           (let ((file (assq-ref s 'filename))
                 (line (assq-ref s 'line))
                 (col (assq-ref s 'column)))
             (lp sources
                 ;; Guile line and column numbers are 0-indexed, but
                 ;; they are 1-indexed for DWARF.
                 (cons (list pc
                             (if file (intern-file file) 0)
                             (if line (1+ line))
                             (if col (1+ col)))
                       out))))
          (()
           ;; Compilation unit header for .debug_line.  We write in
           ;; DWARF 2 format because more tools understand it than DWARF
           ;; 4, which incompatibly adds another field to this header.

           (put-u32 line-port 0) ; Length; will patch later.
           (put-u16 line-port 2) ; DWARF 2 format.
           (put-u32 line-port 0) ; Prologue length; will patch later.
           (put-u8 line-port 1) ; Minimum instruction length: 1 byte.
           (put-u8 line-port 1) ; Default is-stmt: true.

           (put-s8 line-port base) ; Line base.  See the DWARF standard.
           (put-u8 line-port range) ; Line range.  See the DWARF standard.
           (put-u8 line-port 10) ; Opcode base: the first "special" opcode.

           ;; A table of the number of uleb128 arguments taken by each
           ;; of the standard opcodes.
           (put-u8 line-port 0) ; 1: copy
           (put-u8 line-port 1) ; 2: advance-pc
           (put-u8 line-port 1) ; 3: advance-line
           (put-u8 line-port 1) ; 4: set-file
           (put-u8 line-port 1) ; 5: set-column
           (put-u8 line-port 0) ; 6: negate-stmt
           (put-u8 line-port 0) ; 7: set-basic-block
           (put-u8 line-port 0) ; 8: const-add-pc
           (put-u8 line-port 1) ; 9: fixed-advance-pc

           ;; Include directories, as a zero-terminated sequence of
           ;; nul-terminated strings.  Nothing, for the moment.
           (put-u8 line-port 0)

           ;; File table.  For each file that contributes to this
           ;; compilation unit, a nul-terminated file name string, and a
           ;; uleb128 for each of directory the file was found in, the
           ;; modification time, and the file's size in bytes.  We pass
           ;; zero for the latter three fields.
           (vlist-fold-right
            (lambda (pair seed)
              (match pair
                ((file . code)
                 (put-bytevector line-port (string->utf8 file))
                 (put-u8 line-port 0)
                 (put-uleb128 line-port 0) ; directory
                 (put-uleb128 line-port 0) ; mtime
                 (put-uleb128 line-port 0))) ; size
              seed)
            #f
            files)
           (put-u8 line-port 0) ; 0 byte terminating file list.

           ;; Patch prologue length.
           (let ((offset (port-position line-port)))
             (seek line-port 6 SEEK_SET)
             (put-u32 line-port (- offset 10))
             (seek line-port offset SEEK_SET))

           ;; Now write the statement program.
           (let ()
             (define (extended-op opcode payload-len)
               (put-u8 line-port 0)                     ; extended op
               (put-uleb128 line-port (1+ payload-len)) ; payload-len + opcode
               (put-uleb128 line-port opcode))
             (define (set-address sym)
               (extended-op 2 8)
               (set! line-relocs
                     (cons (make-linker-reloc 'abs64/1
                                              (port-position line-port)
                                              0
                                              sym)
                           line-relocs))
               (put-u64 line-port 0))
             (define (end-sequence pc)
               (let ((pc-inc (- (asm-pos asm) pc)))
                 (put-u8 line-port 2)   ; advance-pc
                 (put-uleb128 line-port pc-inc))
               (extended-op 1 0))
             (define (advance-pc pc-inc line-inc)
               (let ((spec (+ (- line-inc base) (* pc-inc range) 10)))
                 (cond
                  ((or (< line-inc base) (>= line-inc (+ base range)))
                   (advance-line line-inc)
                   (advance-pc pc-inc 0))
                  ((<= spec 255)
                   (put-u8 line-port spec))
                  ((< spec 500)
                   (put-u8 line-port 8) ; const-advance-pc
                   (advance-pc (- pc-inc (floor/ (- 255 10) range))
                               line-inc))
                  (else
                   (put-u8 line-port 2) ; advance-pc
                   (put-uleb128 line-port pc-inc)
                   (advance-pc 0 line-inc)))))
             (define (advance-line inc)
               (put-u8 line-port 3)
               (put-sleb128 line-port inc))
             (define (set-file file)
               (put-u8 line-port 4)
               (put-uleb128 line-port file))
             (define (set-column col)
               (put-u8 line-port 5)
               (put-uleb128 line-port col))

             (set-address '.text)

             (let lp ((in out) (pc 0) (file 1) (line 1) (col 0))
               (match in
                 (()
                  (when (null? out)
                    ;; There was no source info in the first place.  Set
                    ;; file register to 0 before adding final row.
                    (set-file 0))
                  (end-sequence pc))
                 (((pc* file* line* col*) . in*)
                  (cond
                   ((and (eqv? file file*) (eqv? line line*) (eqv? col col*))
                    (lp in* pc file line col))
                   (else
                    (unless (eqv? col col*)
                      (set-column col*))
                    (unless (eqv? file file*)
                      (set-file file*))
                    (advance-pc (- pc* pc) (- line* line))
                    (lp in* pc* file* line* col*)))))))))))

    (define (compute-code attr val)
      (match attr
        ('name (string-table-intern! strtab val))
        ('low-pc val)
        ('high-pc val)
        ('producer (string-table-intern! strtab val))
        ('language (language-name->code val))
        ('stmt-list val)))

    (define (exact-integer? val)
      (and (number? val) (integer? val) (exact? val)))

    (define (choose-form attr val code)
      (cond
       ((string? val) 'strp)
       ((eq? attr 'stmt-list) 'sec-offset)
       ((exact-integer? code)
        (cond
         ((< code 0) 'sleb128)
         ((<= code #xff) 'data1)
         ((<= code #xffff) 'data2)
         ((<= code #xffffffff) 'data4)
         ((<= code #xffffffffffffffff) 'data8)
         (else 'uleb128)))
       ((symbol? val) 'addr)
       (else (error "unhandled case" attr val code))))

    (define (add-die-relocation! kind sym)
      (set! die-relocs
            (cons (make-linker-reloc kind (port-position die-port) 0 sym)
                  die-relocs)))

    (define (write-value code form)
      (match form
        ('data1 (put-u8 die-port code))
        ('data2 (put-u16 die-port code))
        ('data4 (put-u32 die-port code))
        ('data8 (put-u64 die-port code))
        ('uleb128 (put-uleb128 die-port code))
        ('sleb128 (put-sleb128 die-port code))
        ('addr
         (add-die-relocation! 'abs64/1 code)
         (put-u64 die-port 0))
        ('sec-offset (put-u32 die-port code))
        ('strp (put-u32 die-port code))))

    (define (write-die die)
      (match die
        ((tag ('@ (attrs vals) ...) children ...)
         (let* ((codes (map compute-code attrs vals))
                (forms (map choose-form attrs vals codes))
                (has-children? (not (null? children)))
                (abbrev-code (intern-abbrev tag has-children? attrs forms)))
           (put-uleb128 die-port abbrev-code)
           (for-each write-value codes forms)
           (when has-children?
             (for-each write-die children)
             (put-uleb128 die-port 0))))))

    ;; Compilation unit header.
    (put-u32 die-port 0) ; Length; will patch later.
    (put-u16 die-port 4) ; DWARF 4.
    (put-u32 die-port 0) ; Abbrevs offset.
    (put-u8 die-port 8) ; Address size.

    (write-die (make-compile-unit-die asm))

    ;; Terminate the abbrevs list.
    (put-uleb128 abbrev-port 0)

    (write-sources)

    (values (let ((bv (get-die-bv)))
              ;; Patch DWARF32 length.
              (bytevector-u32-native-set! bv 0 (- (bytevector-length bv) 4))
              (make-object asm '.debug_info bv die-relocs '()
                           #:type SHT_PROGBITS #:flags 0))
            (make-object asm '.debug_abbrev (get-abbrev-bv) '() '()
                         #:type SHT_PROGBITS #:flags 0)
            (make-object asm '.debug_str (link-string-table! strtab) '() '()
                         #:type SHT_PROGBITS #:flags 0)
            (make-object asm '.debug_loc #vu8() '() '()
                         #:type SHT_PROGBITS #:flags 0)
            (let ((bv (get-line-bv)))
              ;; Patch DWARF32 length.
              (bytevector-u32-native-set! bv 0 (- (bytevector-length bv) 4))
              (make-object asm '.debug_line bv line-relocs '()
                           #:type SHT_PROGBITS #:flags 0)))))

(define (link-objects asm)
  (let*-values (((ro) (link-flonums asm))
                ((text) (link-text-object asm))
                ((symtab strtab hash) (link-dynsym
                                       asm
                                       (linker-object-section text)))
                ((dt) (link-dynamic-section asm text
                                            (bytevector-length
                                             (linker-object-bv strtab))))
                ((dinfo dabbrev dstrtab dloc dline) (link-debug asm))
                ;; This needs to be linked last, because linking other
                ;; sections adds entries to the string table.
                ((shstrtab) (link-shstrtab asm)))
    (filter identity
            (list text ro dt symtab strtab hash
                  dinfo dabbrev dstrtab dloc dline
                  shstrtab))))




;;;
;;; High-level public interfaces.
;;;

(define (link-assembly asm)
  "Produce an ELF image from the code and data emitted into @var{asm}.
The result is a bytevector, by default linked so that read-only and
writable data are on separate pages.  Pass @code{#:page-aligned? #f} to
disable this behavior."
  (link-elf (link-objects asm) #:page-aligned? #t
            #:abi ELFOSABI_NONE #:machine-type EM_X86_64))
