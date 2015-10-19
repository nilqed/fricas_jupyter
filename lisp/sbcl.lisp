;;;
;;; Load dependencies and ispad source
;;;
(load "lisp/quick.lisp")
(load "lisp/ispad.lisp")


(in-package #:cl-jupyter-user)

;;;
;;; Debugger hook
;;;
(defun debug-ignore (c h) (declare (ignore h)) (print c) (abort))
(setf *debugger-hook* #'debug-ignore)


;;;
;;; Get argument: for connect-file
;;;
(defun get-argv1 ()
  (cdr sb-ext:*posix-argv*))


;;;
;;; iSPAD main function
;;;
(defun ispad-main ()
  (let ((connect-file (car (last (get-argv1)))))
     (when (probe-file connect-file)
       (princ connect-file)
       (boot::fricas-init)
       (boot::|parseAndEvalToString| ")version")
       (cl-jupyter::kernel-start connect-file)))) 


;;;
;;; Save image as iSPAD (call: iSPAD <connect-file>)
;;;
(sb-ext:save-lisp-and-die "iSPAD" :toplevel #'cl-jupyter-user::ispad-main 
                                  :executable t 
                                  :save-runtime-options t)
  

