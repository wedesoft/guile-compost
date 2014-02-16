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
  #:use-module (compost runtime)
  #:export (lambda/compost define/compost))

(define-syntax-rule (define/compost (proc arg+guard ...) body ...)
  (define proc (lambda/compost proc (arg+guard ...) body ...)))

(define-syntax lambda/compost
  (lambda (x)
    (syntax-case x ()
      ((lambda/compost name* ((arg guard) ...) body body* ...)
       (let ((proc #'(lambda (arg ...)
                       #((name . name*))
                       body body* ...)))
         #`(let ((proc
                  (load/compost
                   #,(datum->syntax #'lambda/compost
                                    (compile/compost
                                     (syntax->datum proc)
                                     (syntax->datum #'(guard ...))
                                     (current-module)
                                     (syntax-source x)))
                   #,proc)))
             (lambda (arg ...)
               #((name . name*))
               (unless (guard arg)
                 (error "pre-condition failed" 'guard 'arg))
               ...
               (proc arg ...))))))))
