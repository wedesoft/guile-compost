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

(define-module (compost syntax)
  #:use-module (compost compiler)
  #:use-module (system foreign)
  #:use-module (ice-9 binary-ports)
  #:export (lambda/compost define/compost))

(define-syntax-rule (define/compost (proc arg+guard ...) body ...)
  (define proc (lambda/compost proc (arg+guard ...) body ...)))

(define (ensure-dir path)
  (unless (file-exists? path)
    (ensure-dir (dirname path))
    (mkdir path #o700)))

(define (write-cache-file bv project extension)
  (let* ((home (or (getenv "HOME") (passwd:dir (getpwuid (getuid)))))
         (templ (string-append home "/.cache/" project "/XXXXXX")))
    (ensure-dir (dirname templ))
    (let ((port (mkstemp! templ)))
      (put-bytevector port bv)
      (close-port port)
      (let ((new-name (string-append templ extension)))
        (rename-file templ new-name)
        new-name))))

(define-syntax lambda/compost
  (lambda (x)
    (define (guard->type guard)
      (case (syntax->datum guard)
        ((bytevector?) #''*)
        ((real?) #'double)
        ((exact-integer?) #'int64)
        (else (error "unknown type" guard))))
    (define (guard->unbox guard)
      (case (syntax->datum guard)
        ((bytevector?) #'bytevector->pointer)
        ((real? exact-integer?) #'(lambda (x) x))
        (else (error "unknown type" guard))))
    (syntax-case x ()
      ((lambda/compost name* ((arg guard) ...) body body* ...)
       (let ((proc #'(lambda (arg ...) #((name . name*)) body body* ...)))
         (define (inner-proc)
           (cond
            ((compile/compost (syntax->datum proc)
                              (syntax->datum #'(guard ...))
                              (current-module)
                              (syntax-source x))
             => (lambda (compiled)
                  (with-syntax
                      ((name-str (symbol->string (syntax->datum #'name*)))
                       (obj-str (write-cache-file compiled
                                                  "guile/compost" ".so"))
                       ((type ...) (map guard->type #'(guard ...)))
                       ((unbox ...) (map guard->unbox #'(guard ...))))
                    #'(let ((foreign (pointer->procedure
                                      void
                                      (dynamic-pointer name-str
                                                       (dynamic-link obj-str))
                                      (list type ...))))
                        (lambda (arg ...)
                          #((name . name*))
                          (foreign (unbox arg) ...))))))
            (else proc)))
         #`(let ((proc #,(inner-proc)))
             (lambda (arg ...)
               #((name . name*))
               (unless (guard arg)
                 (error "pre-condition failed" 'guard 'arg))
               ...
               (proc arg ...))))))))
