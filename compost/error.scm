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

(define-module (compost error)
  #:use-module (ice-9 format)
  #:export (compilation-error
            call-with-compilation-error-handling))

(define compilation-error-prompt (make-parameter #f))

(define (compilation-error msg . args)
  (abort-to-prompt (compilation-error-prompt) msg args))

(define (issue-compilation-warning port message args source)
  (display ";;; " port)
  (when source
    (let ((filename (or (assq-ref source 'filename) "<unnamed port>"))
          (line (assq-ref source 'line))
          (col (assq-ref source 'column)))
      (format port "~a:~a:~a: " filename (1+ line) col)))
  (format port "warning: optimized compile failed: ~?\n" message args))

(define (call-with-compilation-error-handling default-source proc)
  (let ((prompt (make-prompt-tag)))
    (call-with-prompt
     prompt
     (lambda ()
       (parameterize ((compilation-error-prompt prompt))
         (proc)))
     (lambda* (k message args #:optional (source default-source))
       (issue-compilation-warning (current-warning-port) message args source)
       #f))))
