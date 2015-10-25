;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; iSPAD - Jupyter kernel for SPAD clients (FriCAS, Axiom, OpenAxiom)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; __author__ = "Kurt Pagani <nilqed@gmail.com>"
;;; __svn_id__ = "$Id: ispad.lisp 9 2015-10-24 3:28:52Z pagani $"
;;;
;;; Credits
;;; -------
;;; Based on Frederic Peschanski's cl-jupyter kernel for Common Lisp.
;;; https://github.com/fredokun/cl-jupyter
;;;
;;; Prerequisites (tested with)
;;; ---------------------------
;;; Jupyter 3.2, 4.0
;;; QuickLisp
;;; FricAS compiled with SBCL 1.2.14
;;;
;;;
;;; Revision history:
;;; -----------------
;;;   Version 0.1 
;;;   - merge into one lisp file (ispad.lisp)
;;;   - removed Python 3 dependencies
;;;   - started by shell script "ispad" with parameter $1={connection-file}
;;;   - provided function "kernel-start" with argument "connect-file") 
;;;   - In function "evaluate-code" replaced (eval code-to-eval) by ... 
;;;     (boot::|parseAndEvalToString| code)
;;;
;;;   Version 0.2
;;;   - function 'evaluate-code' cleared out
;;;   - method 'render-plain' customized (stripping quotation marks)
;;;   - in section 'Evaluator'
;;;   -- new function 'constr'
;;;
;;;   Version 0.3
;;;   - in function 'shell-loop' : (equal msg-type "complete_request")
;;;   - in section 'Messages':
;;;   -- new functions: get-token, starts-with-p, get-match-list,
;;;        get-candidates, handle-complete-request
;;;   -- new parameter: ax-tokens
;;;   ** TAB completion working **
;;;
;;;   Version 0.4
;;;   - in function 'shell-loop' : (equal msg-type "inspect_request")
;;;   - in section "Display" 
;;;   -- new function 'extract-tex'
;;;   -- update: method 'render-latex' 
;;;   --- (renders strings of the form "$$ ...$$"), basics
;;;
;;;   Version 0.5
;;;   - New functions in section "Evaluator":
;;;   -- ispad-eval (replaces parseAndEvalToString in 'evaluate-code')
;;;   -- has-type, has-error, get-type, get-tex, get-algebra 
;;;   - Moved function 'concstr' to section "Display"
;;;   - Moved parameter 'ax-tokens' to the end of ispad.lisp
;;;   - Rewrite of 'render-latex' (get-tex) => extract-tex is obsolete!
;;;   - New parameter in section "Display": *pretex* (fix Axiom TeX, leqno ...)
;;;   -- TeX-rendered output now iff: ")set output tex on" 
;;;
;;;   Version 0.6
;;;   - In section "Shell", function 'handle-execute-request':
;;;   -- error handling (stout<->stderr) => red background in cell if 'error'.
;;;   -- added function 'pre-process': detecting if multiline input => do a
;;;      ")read /tmp/tmp.input )quiet )ifthere" after the code has been
;;;      written to "/tmp/tmp.input". See 'handle-execute-request'.
;;;   - Plotting: gnuDraw -> gnuplot file -> )system gnuplot -e -> use html
;;;      <img src= .... > to display. Rudimentary but it works.
;;;   - added function 'get-token2' to get inspection tokens (lookup tbd)
;;;     -- remark: should also be used for 'complete-request' 
;;;
;;;   Version 0.7
;;;   - In section "Shell":
;;;   -- new macros: catch-stream, syscmd-catch-stream (catching io-streams)
;;;   -- new function: get-inspect-list -> returns inspetion text
;;;      *Issue*: if token too short (<3) a yes/no question by the 
;;;               interpreter inhibits further input (to be short: the
;;;               kernel hangs). Solution for the moment: #token >=3.
;;;               Moreover, the lookup has to be done in package :boot,
;;;               otherwise 'not found' message. Revert!
;;;   - In section "Display": 
;;;   -- render-latex (formatting), 
;;;   -- new parameter: *type-format*            
;;;
;;;   Version 0.8
;;;   - Incorporated changes to cl-jupyter up to: e31f2c9f19
;;;   -- message signing ... working
;;;   -- vector-push-extend
;;;   - In section "Shell":
;;;   -- message "comm_open" ... catch -> nil
;;;   -- formatting options (html code in render-latex?)
;;;   -- centering equations only with non CSS engines!! tbd
;;;   - To do: installation procedure not satisfactory / 
;;;   -- quicklisp loading now in ispad.lisp => update README.
;;;      (by courtesy of Ralf Hemmecke)
;;;   -- sbcl save image (malfromed message)
;;;
;;;   
;;;   Version 0.9
;;;   - In section "Shell":
;;;   -- modified "get-token" such that "sin(inte...)" are recognized for
;;;      instance (mainly due to automatic parenthesis pairing).
;;;   -- modified "get-inspect-list" such that token is looked up in
;;;      ax-tokens. Therefore no "y/n" blocking should occur. Inspection
;;;      only works as follows: func() ctrl-tab while cursor is right to 
;;;      the left parenthesis (or between).
;;;   - Extended ax-tokens by domains and packages.
;;;   - Info record updated: codemirror/lexer mode "spad".
;;;   - Changed "pre-process" to filter system commands ($=reserved).
;;;   -- favourable would be a "defclass result" (later?). 
;;;   - CodeMirror/pygments:
;;;   -- added folder 'meta':
;;;   --- renamed axioms.js by Bill Page to spad.js.
;;;   --- https://github.com/billpage/CodeMirror/tree/master/mode/axiom
;;;   --- lexer SPAD in languages.lexer.spad/math. 
;;;   ---- mode and lexer working if properly placed and initialized !!
;;; 
;;;   Version 0.9.1
;;;   - render-png: displays type "FileName" if ending in "png". 
;;;   -- E.g. "plot.png"::FileName => insert bas64 png image, provided that
;;;   --      not in $texmode and file exists. This way we can define plot
;;;           functions which return type "FileName". Should also work for
;;;           svg, ps, html ...
;;;
;;;   Version 0.9.2
;;;   - Rendering of html, markdown, json, svg and javascript files added.
;;;   -- works along the lines as "png" in V 0.9.1.
;;;    
;;;
;;;   Version 0.9.3
;;;   - Removed "quicklisp" / created new file "quick.lisp"
;;;   - Install version @ https://github.com/nilqed/fricas_jupyter
;;;   - Docker version  @ https://hub.docker.com/r/nilqed/fricas_jupyter/
;;;     automated build from GitGub (source sync to ispad.lisp)
;;;
;;;   Version 0.9.4
;;;   - Patches 220d037 from cl-jupyter (evaluator injected in eval)
;;;   -- New: (defvar *evaluator* nil)
;;;   - Patches 843d4db from cl-jupyter (evaluator/user)
;;;   -- New: history management (%in/%out)
;;;   - Up to 843d4db sync 
;;;     "progn" not helpful, quo: warnings as errors? I leave it f.t.m. 
;;;   - Debugger hook does not work in the "load" version, whatever the 
;;;     value of *debugger-hook* is set to. However, it works in the 
;;;     "binary" version.
;;;   +++ Aldor: #<SB-KERNEL:PARSE-UNKNOWN-TYPE {1007D5DC13}>
;;;   +++ Evaluator: in function eval-code -> handling-errors disabled
;;;   +++ Error handling linked to Fricas system.
;;;
;;;   Version 1.0
;;;   soon ;-)
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|  cl-jupyter -- Copyright (c) 2014-2015, Frederic Peschanski
All rights reserved.

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

* Redistributions of source code must retain the above copyright notice, this
  list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright notice, this
  list of conditions and the following disclaimer in the documentation and/or
  other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; QuickLisp loading  ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

;; removed
;; see "quick.lisp"


;;;;;;;;;;;;;;;;
;;; Packages ;;;
;;;;;;;;;;;;;;;;

(defpackage #:fredokun-utilities
  (:nicknames #:fredo-utils)
  (:use #:cl)
  (:export #:*logg-enabled*
           #:*logg-level*
           #:logg
           #:vbinds
           #:afetch
	   #:while
	   #:read-file-lines
	   #:read-string-file
	   #:read-binary-file))

(defpackage #:myjson
  (:use #:cl #:fredo-utils)
  (:export #:parse-json
	   #:parse-json-from-string
	   #:encode-json
	   #:encode-json-to-string))

(defpackage #:cl-jupyter
  (:use #:cl #:fredo-utils #:myjson)
  (:export 
   #:display
   #:display-plain render-plain
   #:display-html render-html
   #:display-markdown render-markdown
   #:display-latex render-latex
   #:display-png render-png
   #:display-jpeg render-jpeg
   #:display-svg render-svg
   #:display-json render-json
   #:display-javascript render-javascript
   #:kernel-start))

(defpackage #:cl-jupyter-user
  (:use #:cl #:fredo-utils #:cl-jupyter #:common-lisp-user)
  (:export 
   #:display
   #:display-plain render-plain
   #:display-html render-html
   #:display-markdown render-markdown
   #:display-latex render-latex
   #:display-png render-png
   #:display-jpeg render-jpeg
   #:display-svg render-svg
   #:display-json render-json
   #:display-javascript render-javascript
   #:html #:latex #:svg
   #:png-from-file
   #:svg-from-file
   #:quit))

(in-package #:cl-jupyter)

;;;;;;;;;;;;;;
;;; Config ;;;
;;;;;;;;;;;;;;
(defparameter +KERNEL-IMPLEMENTATION-NAME+ "cl-jupyter")
(defparameter +KERNEL-IMPLEMENTATION-VERSION+ "0.7")
(defparameter +KERNEL-PROTOCOL-VERSION+ "5.0")
(defparameter +ISPAD-VERSION+ "0.9.4 :: 24-OCT-2015")


;;;;;;;;;;;;;
;;; Utils ;;;
;;;;;;;;;;;;;

(in-package #:fredokun-utilities)

(defmacro logg (level fmt &rest args)
  "Log the passed ARGS using the format string FMT and its
 arguments ARGS."
  (if (or (not *log-enabled*)
          (< level *log-level*))
      (values);; disabled
      ;; when enabled
      `(progn (format ,*log-out-stream* "[LOG]:")
              (format ,*log-out-stream* ,fmt ,@args)
              (format ,*log-out-stream* "~%"))))
  

(defmacro vbinds (binders expr &body body)
  "An abbreviation for MULTIPLE-VALUE-BIND."
  (labels ((replace-underscores (bs &optional (result nil) (fresh-vars nil) (replaced nil))
             (if (null bs)
                 (let ((nresult (nreverse result))
                       (nfresh (nreverse fresh-vars)))
                   (values replaced nresult nfresh))
                 (if (equal (symbol-name (car bs)) "_")
                     (let ((fresh-var (gensym "underscore-")))
                       (replace-underscores (cdr bs) (cons fresh-var result) (cons fresh-var fresh-vars) t))
                     (replace-underscores (cdr bs) (cons (car bs) result) fresh-vars replaced)))))
    (multiple-value-bind (has-underscore nbinders fresh-vars) (replace-underscores binders)
      (if has-underscore
          `(multiple-value-bind ,nbinders ,expr
             (declare (ignore ,@fresh-vars))
             ,@body)
          `(multiple-value-bind ,binders ,expr ,@body)))))


(defun afetch (comp alist &key (test #'eql))
  (let ((binding (assoc comp alist :test test)))
    (if binding
        (cdr binding)
        (error "No such key: ~A" comp))))


(defmacro while (condition &body body)
  (let ((eval-cond-var (gensym "eval-cond-"))
        (body-val-var (gensym "body-val-")))
    `(flet ((,eval-cond-var () ,`,condition))
       (do ((,body-val-var nil (progn ,@body)))
           ((not (,eval-cond-var))
            ,body-val-var)))))


(defun read-file-lines (filename)
  (with-open-file (input filename)
    (loop
       for line = (read-line input nil 'eof)
       until (eq line 'eof)
       collect line)))


(defun read-binary-file (filename)
  (with-open-file (stream filename :element-type '(unsigned-byte 8))
    (let ((bytes (make-array (file-length stream) :element-type '(unsigned-byte 8))))
      (read-sequence bytes stream)
      bytes)))


(defun read-string-file (filename)
  (with-open-file (stream filename)
    (let ((str (make-array (file-length stream) :element-type 'character :fill-pointer t)))
      (setf (fill-pointer str) (read-sequence str stream))
      str)))

;;;;;;;;;;;;;;
;;; MyJson ;;;
;;;;;;;;;;;;;;

(in-package #:myjson)


;; Mapping types 
;; - JSon objects map to Lisp a-lists with string keys
;; - Json arrays map to Lisp vectors
;; - JSon strings map to Lisp strings
;; - JSon true maps to :true
;; - JSon false maps to :false
;; - JSon null maps to :null


(define-condition json-parse-error (error)
  ((message :initarg :message
	    :reader match-error-message))
  (:report (lambda (condition stream)
	     (format stream "[JSon parse error] ~A"
		     (match-error-message condition)))))

(defun char-whitespace-p (char)
  (or (char= char #\Space)
      (char= char #\Tab)
      (char= char #\Return)
      (char= char #\Linefeed)))

(defun read-next-char (input)
  (loop 
     (let ((char (read-char input nil :eof)))
       (cond ((eql char :eof) (error 'json-parse-error :message "Unexpected end of file"))
	     ((char= char #\\) ; c-style escape chars
	      (let ((char (read-char input nil :eof)))
		(cond ((eql char :eof) (error 'json-parse-error :message "Unexpected end of file (after '\'"))
		      ((char= char #\n) (return #\Newline))
		      (t (return char)))))
	     ((not (char-whitespace-p char)) (return char))))))


(defun peek-next-char (input)
  (loop 
     (let ((char (peek-char nil input nil :eof)))
       (cond ((eql char :eof) (error 'json-parse-error :message "Unexpected end of file"))
	     ((char-whitespace-p char) (read-char input))
	     (t (return char))))))


(defun parse-json (input)
  "Parse a JSon document from stream INPUT."
  (let ((char (read-next-char input)))
    (cond ((char= char #\{) (parse-json-object input))
	  ((char= char #\[) (parse-json-array input))
	  ((char= char #\") (parse-json-string input))
	  ((or (char= char #\-)
	       (and (char>= char #\0)
		    (char<= char #\9))) (parse-json-number char input))
	  ((char= char #\t) (parse-json-literal-true input))
	  ((char= char #\f) (parse-json-literal-false input))
	  ((char= char #\n) (parse-json-literal-null input))
	  (t (error 'json-parse-error :message (format nil "Unexpected character: ~A" char))))))

(defun parse-json-literal (input first literal)
  (loop 
     for expect across literal
     do (let ((char (read-char input nil :eof)))
	  (cond ((eql char :eof)  (error 'json-parse-error :message (format nil "Unexpected end of file while parsing literal: ~A~A" first literal)))
		((not (char= char expect)) (error 'json-parse-error :message (format nil "While parsing literal, expecting '~A' instead of: ~A (literal ~A~A)" expect char first literal))))))
  t)

(defun parse-json-literal-true (input)
  (when (parse-json-literal input #\t "rue")
    :true))

(defun parse-json-literal-false (input)
  (when (parse-json-literal input #\f "alse")
    :false))

(defun parse-json-literal-null (input)
  (when (parse-json-literal input #\n "ull")
    :null))

(defun parse-json-string (input)
  (let ((str (make-array 32 :fill-pointer 0 :adjustable t :element-type 'character)))
    (loop
       (let ((char (read-char input nil :eof)))
	 ;(format t "char = ~A~%" char)
	 (cond ((eql char :eof) (error 'json-parse-error :message "Unexpected end of file"))
	       ((char= char #\\)
		(let ((escape-char (read-char input nil :eof)))
		  ;(format t "escape char = ~A~%" escape-char)
		  (cond ((eql escape-char :eof) (error 'json-parse-error :message "Unexpected end of file (after '\')"))
			((char= escape-char #\n) (vector-push-extend #\Newline str))
			(t 
			 ;;(vector-push-extend char str) ;; XXX: escaping is performed on the lisp side
			 (vector-push-extend escape-char str)))))
	       ((char= char #\") (return str))
	       (t (vector-push-extend char str)))))))


(defun parse-json-object (input)
  (let ((obj (list)))
    (loop
       (let ((ckey (read-next-char input)))
	 (cond ((char= ckey #\}) (return (nreverse obj))) ;; special case : empty object 
	       ((not (char= ckey #\"))
		(error 'json-parse-error :message (format nil "Expecting \" for object key, found: ~A" ckey))))
	 (let ((key (parse-json-string input)))
	   (let ((sep (read-next-char input)))
	     (when (not (char= sep #\:))
	       (error 'json-parse-error :message "Missing key/value separator ':' in object"))
	     (let ((val (parse-json input)))
	       (setf obj (cons (cons key val) obj))
	       (let ((term (read-next-char input)))
		 (cond ((char= term #\,) t) ; continue
		       ((char= term #\}) (return (nreverse obj))) ; in-place is ok
		       (t (error 'json-parse-error :message (format nil "Unexpected character in object: ~A" term))))))))))))

(defun parse-json-array (input)
  (let ((array (make-array 32 :fill-pointer 0 :adjustable t)))
    (loop
       (let ((char (peek-next-char input)))
	 (if (char= char #\]) 
	     (progn (read-char input) ; consume the character
		    (return array))
	     ;; any other character
	     (let ((val (parse-json input)))
	       (vector-push-extend val array)
	       (let ((term (read-next-char input)))
		 (cond ((char= term #\]) (return array))
		       ((char= term #\,) t)  ; continue
		       (t (error 'json-parse-error :message (format nil "Unexpected array separator/terminator: ~A" term)))))))))))


(defun parse-json-digit (input &key (min #\0) (max #\9))
  (let ((char (read-next-char input)))
    (if (or (char< char min)
	    (char> char max))
	(error 'json-parse-error :message (format nil "Expecting digit between in range [~A..~A], found: ~A" min max char))
	char)))


(defun parse-json-digits (input &key (min #\0) (max #\9))
  (let ((digits (make-array 8 :fill-pointer 0 :adjustable t :element-type 'character)))
    (loop
       (let ((char (peek-char nil input nil :eof)))
	 (cond ((eql char :eof) (return digits))
	       ((and (char>= char min)
		     (char<= char max))
		(read-char input)
		(vector-push-extend char digits))
	       (t (return digits)))))))


(defun parse-json-number (init input)
  (let ((number (format nil "~A" init)))
    ;; (format t "Initial = ~A ~%" number)
    (let ((fractpart (parse-json-number-fractional-part init input)))
      ;; (format t "Fractional = ~A ~%" fractpart)
      (setf number (concatenate 'string number fractpart)))
    (let ((sep (peek-char nil input nil :eof)))
      (when (eql sep #\.)
	(read-char input)
	(let ((decpart (parse-json-number-decimal-part input)))
	  ;; (format t "Decimal = ~A ~%" decpart)
	  (setf number (concatenate 'string number decpart))
	  (setf sep (peek-char nil input nil :eof))))
      (when (or (eql sep #\e) (eql sep #\E))
	(read-char input)
	(let ((exppart (parse-json-number-exponent-part (format nil "~A" sep) input)))
	  ;; (format t "Exponent = ~A ~%" exppart)
	  (setf number (concatenate 'string number exppart)))))
      ;; return the resulting number
      (read-from-string number)))
	      
(defun parse-json-number-fractional-part (init input)
  (cond ((char= init #\0) "")
	((and (char>= init #\1)
	      (char<= init #\9)) (parse-json-digits input))
	(t
	 (concatenate 'string 
		      (format nil "~A" (parse-json-digit input :min #\1))
		      (parse-json-digits input)))))


(defun parse-json-number-decimal-part (input)
  (concatenate 'string "." (parse-json-digits input)))

(defun parse-json-number-exponent-part (exp input)
  (let ((exponent exp))
    (let ((char (peek-char nil input nil :eof)))
      (cond ((eql char #\+) (read-char input) (setf exponent (concatenate 'string exponent "+")))
	    ((eql char #\-) (read-char input) (setf exponent (concatenate 'string exponent "-")))
	    ((and (characterp char)
		  (char>= char #\0) 
		  (char<= char #\9)) (read-char input) (setf exponent (concatenate 'string exponent (format nil "~A" char))))
	    (t (error 'json-parse-error :message (format nil "Missing exponent digit(s) or sign, found: ~A" char)))))
    (concatenate 'string exponent (parse-json-digits input))))


(defun parse-json-from-string (str)
  "Parse a JSon document encoded in the string STR."
  (with-input-from-string (s str)
    (parse-json s)))


(defparameter *json-encoder-indent-level* 2
  "Indentation level (number of space(s) per indent) for the
 JSon encoder (default is 2).")

(defgeneric encode-json (stream thing &key indent)
  (:documentation "Encode on STREAM a JSon representation of THING. 
The INDENT can be given for beautiful/debugging output (default is NIL
 for deactivating the indentation)."))

(defun encode-json-to-string (thing &key indent)
  "Encode as a string a JSon representation of THING. 
The INDENT can be given for beautiful/debugging output (default is NIL
 for deactivating the indentation)."
  (with-output-to-string (stream)
    (encode-json stream thing :indent indent)))

(defun gen-indent (level)
  (if level
      (make-string (* level *json-encoder-indent-level*) :initial-element #\Space)
      ""))


(defun string-to-json-string (str)
  (let ((jstr (make-array (length str) :fill-pointer 0 :adjustable t :element-type 'character)))               
    (loop
       for char across str
       do (cond ((char= char #\Newline)
                 (vector-push-extend #\\ jstr)
                 (vector-push-extend #\n jstr))
                (t (vector-push-extend char jstr))))
    jstr))


(defun json-write (stream indent with-newline str)
  (when indent
    (write-string (gen-indent indent) stream))
  (write-string str stream)
  (when with-newline
    (terpri stream))) 


(defmethod encode-json (stream (thing cons) &key (indent nil) (first-line nil))
  (json-write stream (if first-line nil indent) (if indent t nil) "{")
  (let ((sepstr (if indent (format nil ",~%") ",")))
    (loop 
       for (key . val) in thing
       for sep = "" then sepstr
       do (progn (json-write stream nil nil sep)
		 (json-write stream (if indent (1+ indent) nil) nil (format nil "~W: " key))
		 (encode-json stream val :indent (if indent (+ 2 indent) nil) :first-line t))))
  (when (and thing indent)
    (format stream "~%"))
  (json-write stream indent nil "}"))

(defmethod encode-json (stream (thing null) &key (indent nil) (first-line nil))
  (json-write stream (if first-line nil indent) (if indent t nil) "{}"))

(defmethod encode-json (stream (thing array) &key (indent nil) (first-line nil))
  (json-write stream (if first-line nil indent) (if indent t nil) "[")
  (let ((sepstr (if indent (format nil ",~%") ",")))
    (loop 
       for val across thing
       for sep = "" then sepstr
       do (progn (json-write stream nil nil sep)
		 (encode-json stream val :indent (if indent (+ 1 indent) nil) :first-line t))))
  (when (and thing indent)
    (format stream "~%"))
  (json-write stream indent nil "]"))

(defmethod encode-json (stream (thing string) &key (indent nil) (first-line nil))
  (json-write stream (if first-line nil indent) nil (string-to-json-string (with-output-to-string (str) (prin1 thing str)))))


(defmethod encode-json (stream (thing integer) &key (indent nil) (first-line nil))
  (json-write stream (if first-line nil indent) nil (format nil "~A" thing)))


(defmethod encode-json (stream (thing float) &key (indent nil) (first-line nil))
  (json-write stream (if first-line nil indent) nil (format nil "~A" thing)))


(defmethod encode-json (stream (thing (eql :true)) &key (indent nil) (first-line nil))
  (json-write stream (if first-line nil indent) nil "true"))


(defmethod encode-json (stream (thing (eql :false)) &key (indent nil) (first-line nil))
  (json-write stream (if first-line nil indent) nil "false"))


(defmethod encode-json (stream (thing (eql :null)) &key (indent nil) (first-line nil))
  (json-write stream (if first-line nil indent) nil "null"))

;;;;;;;;;;;;;;;;
;;; Messages ;;;
;;;;;;;;;;;;;;;;


(in-package #:cl-jupyter)

(defclass header ()
  ((msg-id :initarg :msg-id :reader header-msg-id :type string)
   (username :initarg :username :reader header-username :type string)
   (session :initarg :session :reader header-session :type string)
   (msg-type :initarg :msg-type :reader header-msg-type :type string)
   (version :initarg :version :initform +KERNEL-PROTOCOL-VERSION+ :reader header-version :type string))
  (:documentation "Header representation for IPython messages"))


(defmethod encode-json (stream (object header) &key (indent nil) (first-line nil))
  (with-slots (msg-id username session msg-type version) object
    (encode-json stream `(("msg_id" . ,msg-id)
                          ("username" . ,username)
                          ("session" . ,session)
                          ("msg_type" . ,msg-type)
                          ("version" . ,version))
                 :indent indent :first-line first-line)))



(defun wire-deserialize-header (hdr)
  (let ((json-list (parse-json-from-string hdr)))
    (if json-list
        (make-instance 'header
                       :msg-id (afetch "msg_id" json-list :test #'equal)
                       :username (afetch "username"json-list :test #'equal)
                       :session (afetch "session" json-list :test #'equal)
                       :msg-type (afetch "msg_type" json-list :test #'equal))
        nil)))


(defclass message ()
  ((header :initarg :header :accessor message-header)
   (parent-header :initarg :parent-header :initform nil :accessor message-parent-header)
   (metadata :initarg :metadata :initform nil :accessor message-metadata)
   (content :initarg :content :initform nil :accessor message-content))
  (:documentation "Representation of IPython messages"))

(defun make-message (parent_msg msg_type metadata content) 
  (let ((hdr (message-header parent_msg)))
    (make-instance 
     'message
     :header (make-instance 
	      'header
	      :msg-id (format nil "~W" (uuid:make-v4-uuid))
	      :username (header-username hdr)
	      :session (header-session hdr)
	      :msg-type msg_type
	      :version (header-version hdr))
     :parent-header hdr
     :metadata metadata
     :content content)))

(defun make-orphan-message (session-id msg-type metadata content) 
  (make-instance 
   'message
   :header (make-instance 
	    'header
	    :msg-id (format nil "~W" (uuid:make-v4-uuid))
	    :username "kernel"
	    :session session-id
	    :msg-type msg-type
	    :version +KERNEL-PROTOCOL-VERSION+)
   :parent-header '()
   :metadata metadata
   :content content))


(defun octets-to-hex-string (bytes)
  (apply #'concatenate (cons 'string (map 'list (lambda (x) (format nil "~(~2,'0X~)" x)) bytes))))

(defun message-signing (key parts)
  (let ((hmac (ironclad:make-hmac key :SHA256)))
    ;; updates
    (loop for part in parts
       do (let ((part-bin (babel:string-to-octets part)))
            (ironclad:update-hmac hmac part-bin)))
    ;; digest
    (octets-to-hex-string (ironclad:hmac-digest hmac))))


;; XXX: should be a defconstant but  strings are not EQL-able...
(defvar +WIRE-IDS-MSG-DELIMITER+ "<IDS|MSG>")

(defmethod wire-serialize ((msg message) &key (identities nil)(key nil))
  (with-slots (header parent-header metadata content) msg
    (let ((header-json (encode-json-to-string header))
          (parent-header-json (if parent-header
                                  (encode-json-to-string parent-header)
                                  "{}"))
          (metadata-json (if metadata
                             (encode-json-to-string metadata)
                             "{}"))
          (content-json (if content
                            (encode-json-to-string content)
                            "{}")))
      (let ((sig (if key
                     (message-signing key (list header-json parent-header-json metadata-json content-json))
                     "")))
        (append identities
                (list +WIRE-IDS-MSG-DELIMITER+
                      sig
                      header-json
                      parent-header-json
                      metadata-json
                      content-json))))))     


(defun wire-deserialize (parts)
  (let ((delim-index (position +WIRE-IDS-MSG-DELIMITER+ parts :test  #'equal)))
    (when (not delim-index)
      (error "no <IDS|MSG> delimiter found in message parts"))
    (let ((identities (subseq parts 0 delim-index))
          (signature (nth (1+ delim-index) parts)))
      (let ((msg (destructuring-bind (header parent-header metadata content)
                     (subseq parts (+ 2 delim-index) (+ 6 delim-index))
                   (make-instance 'message
                                  :header (wire-deserialize-header header)
                                  :parent-header (wire-deserialize-header parent-header)
                                  :metadata metadata
                                  :content content))))
        (values identities
                signature
                msg
                (subseq parts (+ 6 delim-index)))))))

(defun message-send (socket msg &key (identities nil)(key nil))
  (let ((wire-parts (wire-serialize msg :identities identities :key key)))
    ;;(format t "~%[Send] wire parts: ~W~%" wire-parts)
    (dolist (part wire-parts)
      (pzmq:send socket part :sndmore t))
    (pzmq:send socket nil)))


;;; update:88f28d1 

(defun recv-string (socket &key dontwait (encoding cffi:*default-foreign-encoding*))
  "Receive a message part from a socket as a string."
  (pzmq:with-message msg
    (pzmq:msg-recv msg socket :dontwait dontwait)
    (values
     (handler-case 
         (cffi:foreign-string-to-lisp (pzmq:msg-data msg) :count (pzmq:msg-size msg) :encoding encoding)
       (BABEL-ENCODINGS:INVALID-UTF8-STARTER-BYTE
           ()
         ;; if it's not utf-8 we try latin-1 (Ugly !)
         (format t "[Recv]: issue with UTF-8 decoding~%")
         (cffi:foreign-string-to-lisp (pzmq:msg-data msg) :count (pzmq:msg-size msg) :encoding :latin-1)))
     (pzmq:getsockopt socket :rcvmore))))



(defun zmq-recv-list (socket &optional (parts nil) (part-num 1))
  (multiple-value-bind (part more)
      (recv-string socket)
    ;;(format t "[Shell]: received message part #~A: ~W (more? ~A)~%" part-num part more)
    (if more
        (zmq-recv-list socket (cons part parts) (+ part-num 1))
        (reverse (cons part parts)))))



(defun message-recv (socket)
  (let ((parts (zmq-recv-list socket)))
    ;;(format t "[Recv]: parts: ~A~%" (mapcar (lambda (part) (format nil "~W" part)) parts))
    (wire-deserialize parts)))

;;;;;;;;;;;;;
;;; Shell ;;;
;;;;;;;;;;;;;

(in-package #:cl-jupyter)


(defclass shell-channel ()
  ((kernel :initarg :kernel :reader shell-kernel)
   (socket :initarg :socket :initform nil :accessor shell-socket)))


(defun make-shell-channel (kernel)
  (let ((socket (pzmq:socket (kernel-ctx kernel) :router)))
    (let ((shell (make-instance 'shell-channel
                                :kernel kernel
                                :socket socket)))
      (let ((config (slot-value kernel 'config)))
        (let ((endpoint (format nil "~A://~A:~A"
                                  (config-transport config)
                                  (config-ip config)
                                  (config-shell-port config))))
          ;; (format t "shell endpoint is: ~A~%" endpoint)
          (pzmq:bind socket endpoint)
          shell)))))

(defun shell-loop (shell)
  (let ((active t))
    (format t "[Shell] loop started~%")
    (send-status-starting (kernel-iopub (shell-kernel shell)) (kernel-session (shell-kernel shell)) :key (kernel-key shell))
    (while active
      (vbinds (identities sig msg buffers)  (message-recv (shell-socket shell))
	      ;;(format t "Shell Received:~%")
	      ;;(format t "  | identities: ~A~%" identities)
	      ;;(format t "  | signature: ~W~%" sig)
	      ;;(format t "  | message: ~A~%" (encode-json-to-string (message-header msg)))
	      ;;(format t "  | buffers: ~W~%" buffers)

	      ;; TODO: check the signature (after that, sig can be forgotten)
	      (let ((msg-type (header-msg-type (message-header msg))))
		(cond ((equal msg-type "kernel_info_request")
		       (handle-kernel-info-request shell identities msg buffers))
		      ((equal msg-type "execute_request")  ;;; pre-proc here?
		       (setf active (handle-execute-request shell identities msg buffers)))
              ((equal msg-type "complete_request") ;;;+NEW
               (handle-complete-request shell identities msg buffers))
              ((equal msg-type "inspect_request") ;;;+NEW
               (handle-inspect-request shell identities msg buffers))
              ((equal msg-type "comm_open") ;;;+NEW
               nil)                     
		      (t (warn "[Shell] message type '~A' not (yet ?) supported, skipping..." msg-type))))))))


;; for protocol version 5  
(defclass content-kernel-info-reply (message-content)
  ((protocol-version :initarg :protocol-version :type string)
   (implementation :initarg :implementation :type string)
   (implementation-version :initarg :implementation-version :type string)
   (language-info-name :initarg :language-info-name :type string)
   (language-info-version :initarg :language-info-version :type string)
   (language-info-mimetype :initarg :language-info-mimetype :type string)
   (language-info-pygments-lexer :initarg :language-info-pygments-lexer :type string)
   (language-info-codemirror-mode :initarg :language-info-codemirror-mode :type string)
   (language-info-nbconvert-exporter :initarg :language-info-nbconvert-exporter :type string)
   (banner :initarg :banner :type string)
   ;; help links: (text . url) a-list
   (help-links :initarg :help-links)))


(defun help-links-to-json (help-links)
  (concatenate 'string "["
	       (concat-all 'string ""
			   (join "," (mapcar (lambda (link) 
					       (format nil "{ \"text\": ~W, \"url\": ~W }" (car link) (cdr link))) 
					     help-links)))
	       "]"))

;; for protocol version 5
(defmethod encode-json (stream (object content-kernel-info-reply) &key (indent nil) (first-line nil))
  (with-slots (protocol-version
               implementation implementation-version
               language-info-name language-info-version
               language-info-mimetype language-info-pygments-lexer language-info-codemirror-mode
               language-info-nbconvert-exporter
               banner help-links) object
    (encode-json stream `(("protocol_version" . ,protocol-version)
                          ("implementation" . ,implementation)
                          ("implementation_version" . ,implementation-version)
                          ("language_info" . (("name" . ,language-info-name)
                                              ("version" . ,language-info-version)
                                              ("mimetype" . ,language-info-mimetype)
                                              ("pygments_lexer" . ,language-info-pygments-lexer)
                                              ("codemirror_mode" . ,language-info-codemirror-mode)))
                                              ;("nbconvert_exporter" . ,language-info-nbconvert-exporter)))
                          ("banner" . "iSPAD") 
                          ("help_links" . ,help-links))
                 :indent indent :first-line first-line)))


(defun kernel-key (shell)
  (kernel-config-key (kernel-config (shell-kernel shell))))



(defun handle-kernel-info-request (shell identities msg buffers)
  ;;(format t "[Shell] handling 'kernel-info-request'~%")
  ;; status to busy
  (send-status-update (kernel-iopub (shell-kernel shell)) msg "busy" :key (kernel-key shell))
  ;; for protocol version 5
  (let ((reply (make-message
                msg "kernel_info_reply" nil
                (make-instance
                 'content-kernel-info-reply
                 :protocol-version (header-version (message-header msg))
                 :implementation +KERNEL-IMPLEMENTATION-NAME+
                 :implementation-version +KERNEL-IMPLEMENTATION-VERSION+
                 :language-info-name "SPAD"
                 :language-info-version "1.2.6"
                 :language-info-mimetype "text/x-spad"
                 :language-info-pygments-lexer "spad"
                 :language-info-codemirror-mode "spad"
                 :language-info-nbconvert-exporter ""
                 :banner "iSPAD"
                 :help-links (vector)))))

    (message-send (shell-socket shell) reply :identities identities :key (kernel-key shell))
    ;; status back to idle
    (send-status-update (kernel-iopub (shell-kernel shell)) msg "idle" :key (kernel-key shell))))


;;;+NEW

;;; catch a stream after command 'cmd' execution:
;;; example:  (setq res (catch-stream "y^2+1" *standard-output*))
(defmacro catch-stream (cmd my-stream)
    `(let ((tmpout (make-string-output-stream))
          (save ,my-stream))
       (setq ,my-stream tmpout)
       (boot::|parseAndInterpret| ,cmd)
       (let ((result (get-output-stream-string ,my-stream)))
         (setq ,my-stream save)
           result)))

;;; catch a stream after a sys command exec, e.g. ")d op sin"
;;; example:  (setq res (catch-stream ")d op sin" *standard-output*))
(defmacro syscmd-catch-stream (cmd my-stream)
    `(let ((tmpout (make-string-output-stream))
          (save ,my-stream))
       (setq ,my-stream tmpout)
       (boot::|parseAndEvalToString| ,cmd)
       (let ((result (get-output-stream-string ,my-stream)))
         (setq ,my-stream save)
           result)))


(defun get-token (code)
   "Returns (token pos) ; pos is nil or a number"
   ;(let ((pos (position #\Space s :from-end t)))
   (let* ((s (string-right-trim "()" code))
         (pos (position-if-not #'alphanumericp s :from-end t)))
     (if pos 
        (list (subseq s (+ pos 1)) (+ pos 1)) 
        (list s pos))))

(defun get-token2 (code pos)
    "Get token @ pos-1, e.g. sin() -> sin, sin(cos( -> cos"
    (let* ((s (subseq code 0 (max 0 (- pos 1))))
           (p (position-if-not #'alphanumericp s :from-end t)))
       (if p (subseq s (+ p 1)) s)))


(defun starts-with-p (str1 str2)
  "Determine whether `str1` starts with `str2`"
  (let ((p (search str2 str1)))
    (and p (= 0 p))))


(defun get-match-list (token kw-list)
    "Extract keywords starting with <token> into a list"
    (mapcan (lambda (x) (if (starts-with-p x token) (list x) nil)) kw-list)) 


(defun get-candidates (s)
    "Given a sentence returns a vector of completion candidates"
    (coerce (get-match-list (car (get-token s)) ax-tokens) 'vector))

;; must be in package :boot !
;; if token too short => yes/no question => hangs !!! 
;; return value: '("text of ')d op token' operation")
(defun get-inspect-list (code cursor-end)
    (let ((token (get-token2 code cursor-end))
           (*package* (find-package :boot)))  
      (if (position token ax-tokens :test #'equal) 
        (list (syscmd-catch-stream 
           (format nil ")d op ~A" token)  
		     *standard-output*)) 
		(list (format nil "[~A] not found." token)))))

;---

(defun handle-complete-request (shell identities msg buffers)
  (send-status-update (kernel-iopub (shell-kernel shell)) msg "busy" :key (kernel-key shell))
  (let ((content (parse-json-from-string (message-content msg))))
     (let ((code (afetch "code" content :test #'equal))
           (cursor-end (afetch "cursor_pos" content :test #'equal)))
       (let ((pos (cadr (get-token code))))
          (if pos (setq cursor-start pos) (setq cursor-start 0))
       (let ((reply (make-message msg "complete_reply" nil
		      `(("matches" . ,(get-candidates code))
		       ("cursor_start" . ,(write-to-string cursor-start))  
		       ("cursor_end" . ,(write-to-string cursor-end)) ;; = by def
     		   ("metadata" . nil)
	           ("status" . "ok")))))
        (send-status-update (kernel-iopub (shell-kernel shell)) msg "idle" :key (kernel-key shell))
        (message-send (shell-socket shell) reply :identities identities :key (kernel-key shell)) t)))))       



(defun handle-inspect-request (shell identities msg buffers)
    (send-status-update (kernel-iopub (shell-kernel shell)) msg "busy" :key (kernel-key shell))
    (let ((content (parse-json-from-string (message-content msg))))
      (let ((code (afetch "code" content :test #'equal))
           (cursor-end (afetch "cursor_pos" content :test #'equal)))
       
       (let ((reply (make-message msg "inspect_reply" nil
		     `(("found" . :true)
		       ("data" . ,(pairlis '("text/plain") 
		                     (get-inspect-list code cursor-end)))  
     		   ("metadata" . nil)
	           ("status" . "ok")))))
        (send-status-update (kernel-iopub (shell-kernel shell)) msg "idle" :key (kernel-key shell))
        (message-send (shell-socket shell) reply :identities identities :key (kernel-key shell)) t))))


(defun code-to-eval (code)
    (let ((nl (count #\newline code)))
      (if (> nl 0) 
        (when t (with-open-file 
          (stream "/tmp/tmp.input" :direction :output :if-exists :supersede)
          (format stream code))
           ")read /tmp/tmp.input )quiet )ifthere")  
         code)))

(defun pre-process (code)
    (cond 
      ((starts-with-p code ")") code)
      ((starts-with-p code "$") "output(reserved!)")
      (t (code-to-eval code))))


;;; -NEW


(defun handle-execute-request (shell identities msg buffers)
  (send-status-update (kernel-iopub (shell-kernel shell)) msg "busy" :key (kernel-key shell))
  (let ((content (parse-json-from-string (message-content msg))))
    (let ((code (afetch "code" content :test #'equal))) 

      (vbinds (execution-count results stdout stderr)
          (evaluate-code (kernel-evaluator (shell-kernel shell)) 
              (pre-process code))
          
        ;; broadcast the code to connected frontends
        (send-execute-code (kernel-iopub (shell-kernel shell)) msg execution-count code :key (kernel-key shell))
	(when (and (consp results) (typep (car results) 'cl-jupyter-user::cl-jupyter-quit-obj))
	    ;;;;;;;;;;;;;;;; ===>(caaar results) = )quit
	  ;; ----- ** request for shutdown ** -----
	  (let ((reply (make-message msg "execute_reply" nil
				     `(("status" . "abort")
				       ("execution_count" . ,execution-count)))))
	    (message-send (shell-socket shell) reply :identities identities :key (kernel-key shell)))
	  (return-from handle-execute-request nil))
	;; ----- ** normal request ** -----
        ;; send the stdout

;;;+NEW Hook for error handling (stdout <--> sterr) : (...) = has-error
         (when (string-equal (caaar results) "error") 
              (setq stderr stdout) (setq stdout nil))
;;;              
        (when (and stdout (> (length stdout) 0))
          (send-stream (kernel-iopub (shell-kernel shell)) msg "stdout" stdout :key (kernel-key shell)))
        ;; send the stderr
        (when (and stderr (> (length stderr) 0))
          (send-stream (kernel-iopub (shell-kernel shell)) msg "stderr" stderr :key (kernel-key shell)))
	
        ;; send the first result
	(send-execute-result (kernel-iopub (shell-kernel shell)) 
			     msg execution-count (car results) :key (kernel-key shell))
	;; status back to idle
	(send-status-update (kernel-iopub (shell-kernel shell)) msg "idle" :key (kernel-key shell))
	;; send reply (control)
	(let ((reply (make-message msg "execute_reply" nil
				   `(("status" . "ok")
				     ("execution_count" . ,execution-count)
				     ("payload" . ,(vector))))))
	  (message-send (shell-socket shell) reply :identities identities :key (kernel-key shell))
	  t)))))


(defclass message-content ()
  ()
  (:documentation "The base class of message contents."))


;;;;;;;;;;;;;
;;; IoPub ;;;
;;;;;;;;;;;;;

(in-package #:cl-jupyter)


(defclass iopub-channel ()
  ((kernel :initarg :kernel :reader iopub-kernel)
   (socket :initarg :socket :initform nil :accessor iopub-socket)))

(defun make-iopub-channel (kernel)
  (let ((socket (pzmq:socket (kernel-ctx kernel) :pub)))  
    (let ((iopub (make-instance 'iopub-channel
                                :kernel kernel
                                :socket socket)))
      (let ((config (slot-value kernel 'config)))
        (let ((endpoint (format nil "~A://~A:~A"
                                  (config-transport config)
                                  (config-ip config)
                                  (config-iopub-port config))))
          ;;(format t "[IOPUB] iopub endpoint is: ~A~%" endpoint)
          (pzmq:bind socket endpoint)
	  (setf (slot-value kernel 'iopub) iopub)
          iopub)))))

(defun send-status-starting (iopub session  &key (key nil))
  (let ((status-msg (make-orphan-message session "status" nil
					  `(("execution_state" . "starting")))))
    (message-send (iopub-socket iopub) status-msg :identities '("status") :key key)))
  
(defun send-status-update (iopub parent-msg status  &key (key nil))
  (let ((status-content `((:execution--state . ,status))))
    (let ((status-msg (make-message parent-msg "status" nil
				    `(("execution_state" . ,status)))))
      (message-send (iopub-socket iopub) status-msg :identities '("status") :key key))))

(defun send-execute-code (iopub parent-msg execution-count code &key (key nil))
  (let ((code-msg (make-message  parent-msg "execute_input" nil
				 `(("code" . ,code)
				   ("execution_count" . ,execution-count)))))
    ;;(format t "content to send = ~W~%" (encode-json-to-string (message-content code-msg)))
    (message-send (iopub-socket iopub) code-msg :identities '("execute_input") :key key)))


(defun send-execute-result (iopub parent-msg execution-count result  &key (key nil))
  (let ((display-obj (display result)))
    (let ((result-msg (make-message parent-msg "execute_result" nil
				    `(("execution_count" . ,execution-count)
				      ("data" . ,(display-object-data display-obj))
				      ("metadata" . ())))))
      (message-send (iopub-socket iopub) result-msg :identities '("execute_result") :key key))))

(defun send-stream (iopub parent-msg stream-name data  &key (key nil))
  (let ((stream-msg (make-message parent-msg "stream" nil
				  `(("name" . ,stream-name)
				    ("text" . ,data)))))
    (message-send (iopub-socket iopub) stream-msg :identities `(,(format nil "stream.~W" stream-name)) :key key)))

;;;;;;;;;;;;;;;
;;; Display ;;;
;;;;;;;;;;;;;;;


(in-package #:cl-jupyter)

(defun concstr (list)
;; concatenate a list of strings ; recall ~% = newline"
;; +kfp temp solution (move this to utils later)
(if (listp list)
  (with-output-to-string (s)
     (dolist (item list)
       (if (stringp item)
         (format s "~a~%" item))))))



(defclass display-object ()
  ((value :initarg :value :reader display-object-value)
   (data :initarg :data :reader display-object-data))
  (:documentation "The class of DISPLAY-OBJECTs, i.e. objets supposed
to be displayed by the Fishbowl/IPython frontend."))


(defgeneric render-plain (value)
  (:documentation "Render the VALUE as plain text (default rendering)."))


(defmethod render-plain ((value t))
  ;; Lisp printer by default
  ;; +kfp: if value is a string => value 
  (let ((alg (concstr (car value))))
    (if (stringp alg) alg
      (format nil "~S" alg))))

(defgeneric render-html (value)
  (:documentation "Render the VALUE as an HTML document (represented as a sting)."))

(defmethod render-html ((value t))
  (if (has-type value)
    (if (string-equal (get-type value) "FileName") 
       (if (not boot::|$texFormat|)  
          (let* ((filename (string-trim "\" " (caar value))))
             (if (probe-file filename) 
               (if (string-equal (pathname-type filename) "html") 
                    (read-string-file filename) nil)
               nil))
                 nil)
                   nil)
                     nil))

(defgeneric render-markdown (value)
  (:documentation "Render the VALUE as MARDOWN text."))

(defmethod render-markdown ((value t))
  (if (has-type value)
    (if (string-equal (get-type value) "FileName") 
       (if (not boot::|$texFormat|)  
          (let* ((filename (string-trim "\" " (caar value))))
             (if (probe-file filename) 
               (if (string-equal (pathname-type filename) "md") 
                    (read-string-file filename) nil)
               nil))
                 nil)
                   nil)
                     nil))


(defgeneric render-latex (value)
  (:documentation "Render the VALUE as a LATEX document."))


(defparameter *pretex* (concstr (list 
    "\\("        
    "\\def\\sp{^}\\def\\sb{_}\\def\\leqno(#1){}"
    "\\def\\erf{\\mathrm{erf}}\\def\\sinh{\\mathrm{sinh}}"
    "\\def\\zag#1#2{{{\\left.{#1}\\right|}\\over{\\left|{#2}\\right.}}}"
    "\\def\\csch{\\mathrm{csch}}"
    "\\require{color}"
    "\\)"
)))

(defparameter *type-format* 
   "\\(\\\\[3ex]\\color{blue}\\scriptsize\\text{~A}\\)")

(defun get-tex-with-type (result)
    (let ((tex (get-tex result)))
       (if (> (length tex) 0)
         (if (not (has-type result)) tex
           (let ((ts (get-type result)))
               (concstr (list tex "\\(\\\\" ts "\\)")))) nil )))

;;; --<

;;; assuming boot::|$texFormat| = t
;;; improving repr later, centering? ...

(defmethod render-latex ((value t))
  (let ((tex (get-tex value)))
     (if (> (length tex) 0) 
        (if (not (has-type value)) tex
           (let ((ts (get-type value)))
               (concstr (list *pretex* 
                  ;"<div style=\"text-align: center\">"
                  (format nil "~A" tex) 
                  ;"</div>" 
                  ;"<center>" 
                  (format nil *type-format* ts) 
                  ;"</center>" 
                  )))) 
         nil)))  
         
         
(defgeneric render-png (value)
  (:documentation "Render the VALUE as a PNG image. The expected
 encoding is a Base64-encoded string."))


;;;
;;; catch specific type (e.g. FileName) then act and return "png-file" 
;;; => base64 conversion => inline display (principle hold for all rend's)
;;; !!! check existence && filetype
;;;

(defmethod render-png ((value t))
  (if (has-type value)
    (if (string-equal (get-type value) "FileName") 
       (if (not boot::|$texFormat|)  
          (let* ((filename (string-trim "\" " (caar value))))
             (if (probe-file filename) 
               (if (string-equal (pathname-type filename) "png")
                  (cl-base64:usb8-array-to-base64-string 
                       (read-binary-file filename)) nil)
               nil))
                 nil)
                   nil)
                     nil))
          

(defgeneric render-jpeg (value)
  (:documentation "Render the VALUE as a JPEG image. The expected
 encoding is a Base64-encoded string."))

(defmethod render-jpeg ((value t))
  ;; no rendering by default
  nil)

(defgeneric render-svg (value)
  (:documentation "Render the VALUE as a SVG image (XML format represented as a string)."))

(defmethod render-svg ((value t))
  (if (has-type value)
    (if (string-equal (get-type value) "FileName") 
       (if (not boot::|$texFormat|)  
          (let* ((filename (string-trim "\" " (caar value))))
             (if (probe-file filename) 
               (if (string-equal (pathname-type filename) "svg") 
                    (read-string-file filename) nil)
               nil))
                 nil)
                   nil)
                     nil))

(defgeneric render-json (value)
  (:documentation "Render the VALUE as a JSON document. This uses the MYJSON encoding
 (alist with string keys)"))

(defmethod render-json ((value t))
  (if (has-type value)
    (if (string-equal (get-type value) "FileName") 
       (if (not boot::|$texFormat|)  
          (let* ((filename (string-trim "\" " (caar value))))
             (if (probe-file filename) 
               (if (string-equal (pathname-type filename) "json") 
                    (read-string-file filename) nil)
               nil))
                 nil)
                   nil)
                     nil))

(defgeneric render-javascript (value)
  (:documentation "Render the VALUE as a JAVASCRIPT source (represented as a string)."))

(defmethod render-javascript ((value t))
  (if (has-type value)
    (if (string-equal (get-type value) "FileName") 
       (if (not boot::|$texFormat|)  
          (let* ((filename (string-trim "\" " (caar value))))
             (if (probe-file filename) 
               (if (string-equal (pathname-type filename) "js") 
                    (read-string-file filename) nil)
               nil))
                 nil)
                   nil)
                     nil))


(defun combine-render (pairs)
  (loop 
   for pair in pairs 
     when (not (null (cdr pair)))
   collect pair))

(defun display-dispatch (value render-alist)
  (if (typep value 'display-object)
      value ; already displayed
      ;; otherwise needs to display
      (let ((data (combine-render (cons `("text/plain" . ,(render-plain value)) ; at least text/plain encoding is required
					render-alist))))
	(make-instance 'display-object :value value :data data))))


(defun display (value)
  "Display VALUE in all supported representations."
  (display-dispatch value  `(("text/html" . ,(render-html value))
			     ("text/markdown" . ,(render-markdown value))
			     ("text/latex" . ,(render-latex value))
			     ("image/png" . ,(render-png value))
			     ("image/jpeg" . ,(render-jpeg value))
			     ("image/svg+xml" . ,(render-svg value))
			     ("application/json" . ,(render-json value))
			     ("application/javascript" . ,(render-javascript value)))))

(defun display-html (value)
  "Display VALUE as HTML."
  (display-dispatch value `(("text/html" . ,(render-html value)))))

(defun display-markdown (value)
  "Display VALUE as MARDOWN text."
  (display-dispatch value `(("text/markdown" . ,(render-markdown value)))))

(defun display-latex (value)
  "Display VALUE as a LATEX document."
  (display-dispatch value `(("text/latex" . ,(render-latex value)))))

(defun display-png (value)
  "Display VALUE as a PNG image."
  (display-dispatch value `(("image/png" . ,(render-png value)))))

(defun display-jpeg (value)
  "Display VALUE as a JPEG image."
  (display-dispatch value `(("image/jpeg" . ,(render-jpeg value)))))

(defun display-svg (value)
  "Display VALUE as a SVG image."
  (display-dispatch value `(("image/svg+xml" . ,(render-svg value)))))

(defun display-json (value)
  "Display VALUE as a JSON document."
  (display-dispatch value `(("application/json" . ,(render-json value)))))

(defun display-javascript (value)
  "Display VALUE as embedded JAVASCRIPT."
  (display-dispatch value `(("application/javascript" . ,(render-javascript value)))))

;;;;;;;;;;;;;;;;;
;;; Evaluator ;;;
;;;;;;;;;;;;;;;;;

(in-package #:cl-jupyter)


(defun ispad-eval (s)
  (let ((*package* (find-package :boot)))
    (let ((tmpout (make-string-output-stream))
           (save boot::|$texOutputStream|))
        (setq boot::|$texOutputStream| tmpout)
        (let ((alg (boot::|parseAndEvalToString| s))
              (tex (get-output-stream-string boot::|$texOutputStream|)))
          (setq boot::|$texOutputStream| save)
            (list alg tex)))))


;;; result = ( (strings) string )
;;; cadr .... tex output string
;;; car ..... list alg output, last is type


(defun has-type (result)
    (let ((ts (string-trim " " (car(last (car result))))))
        (if (< (length ts) 5) nil
          (if (string-equal (subseq ts 0 5) "Type:") t nil))))


(defun has-error (result)
    (if (string-equal (caar result) "error") t nil))


(defun get-type (result)
    (let ((ts (string-trim " " (car(last (car result))))))
        (string-trim " " (subseq ts 6))))


(defun get-tex (result)
    (cadr result))



(defclass evaluator ()
  ((kernel :initarg :kernel :reader evaluator-kernel)
   (history-in :initform (make-array 64 :fill-pointer 0 :adjustable t)
	       :reader evaluator-history-in)
   (history-out :initform (make-array 64 :fill-pointer 0 :adjustable t)
		:reader evaluator-history-out)))

;;; clj 220d037
(defvar *evaluator* nil)

(defun make-evaluator (kernel)
  (let ((evaluator (make-instance 'evaluator
				  :kernel kernel)))
    (setf (slot-value kernel 'evaluator) evaluator)
    evaluator))


;;; macro taken from: http://www.cliki.net/REPL
;;; modified to handle warnings correctly 
(defmacro handling-errors-old (&body body)
  `(handler-case (progn ,@body)
     (simple-condition (err) 
       (format *error-output* "~&~A: ~%" (class-name (class-of err)))
       (apply (function format) *error-output*
              (simple-condition-format-control   err)
              (simple-condition-format-arguments err))
       (format *error-output* "~&"))
     (condition (err) 
       (format *error-output* "~&~A: ~%  ~S~%"
               (class-name (class-of err)) err))))

;;; new version 3a2e8f7
(defmacro handling-errors (&body body)
  `(handler-case
       (handler-bind ((simple-warning
		       #'(lambda (wrn)
			   (format *error-output* "~&~A: ~%" (class-name (class-of wrn)))
			   (apply (function format) *error-output*
				  (simple-condition-format-control   wrn)
				  (simple-condition-format-arguments wrn))
			   (format *error-output* "~&")
			   (muffle-warning)))
		      (warning
		       #'(lambda (wrn)
			   (format *error-output* "~&~A: ~%  ~S~%"
				   (class-name (class-of wrn)) wrn)
			   (muffle-warning))))
	 (progn ,@body))
     (simple-condition (err)
       (format *error-output* "~&~A: ~%" (class-name (class-of err)))
       (apply (function format) *error-output*
              (simple-condition-format-control   err)
              (simple-condition-format-arguments err))
       (format *error-output* "~&"))
     (condition (err)
       (format *error-output* "~&~A: ~%  ~S~%"
               (class-name (class-of err)) err))))



;;; update: b244f0c, 843d4db
(defun evaluate-code (evaluator code)
  ;;(format t "[Evaluator] Code to evaluate: ~W~%" code)
  ;;(vector-push-extend code (evaluator-history-in evaluator))
  (let ((execution-count (length (evaluator-history-in evaluator))))
    (let ((code-to-eval code))
      (let* ((stdout-str (make-array 0 :element-type 'character :fill-pointer 0 :adjustable t))
	     (stderr-str (make-array 0 :element-type 'character :fill-pointer 0 :adjustable t)))
	 (let ((results (with-output-to-string (stdout stdout-str)
	    (with-output-to-string (stderr stderr-str)
	      (let ((*standard-output* stdout) (*error-output* stderr))
		      ;(handling-errors
		        (let ((*evaluator* evaluator))       
			      (multiple-value-list 
		           ;;; EVAL
                    (ispad-eval code)))
              ;) 
   ))))) 
   ;;
   (vector-push-extend code (evaluator-history-in evaluator))
   (vector-push-extend results (evaluator-history-out evaluator))
   (values execution-count results stdout-str stderr-str))))))



;;;;;;;;;;;;
;;; User ;;;
;;;;;;;;;;;;

(in-package #:cl-jupyter-user)


(defclass cl-jupyter-quit-obj ()
  ()
  (:documentation "A quit object for identifying a request for kernel shutdown."))


(defun quit ()
  (make-instance 'cl-jupyter-quit-obj))
  

;; remark: this is not supported in IPython 2.x (will it be in 3 ?)
(defclass markdown-text ()
  ((text :initarg :text :reader markdown-text)))


(defmethod render-markdown ((doc markdown-text))
  (markdown-text doc))


(defun markdown (text)
  (display-markdown (make-instance 'markdown-text :text text)))


(defclass latex-text ()
  ((text :initarg :text :reader latex-text)))


(defmethod render-latex ((doc latex-text))
  (with-output-to-string (str)
    (format str "~A" (latex-text doc))))


(defun latex (text)
  (display-latex (make-instance 'latex-text :text text)))


(defclass html-text ()
  ((text :initarg :text :reader html-text)))


(defmethod render-html ((doc html-text))
  (html-text doc))
  ;(with-output-to-string (str)
  ;  (format str "~A" (html-text doc))))

  
(defun html (text)
  (display-html (make-instance 'html-text :text text)))


(defclass png-bytes ()
  ((bytes :initarg :bytes :reader png-bytes)))


(defmethod render-png ((img png-bytes))
  (cl-base64:usb8-array-to-base64-string (png-bytes img)))


(defun png-from-file (filename)
  (let ((bytes (read-binary-file filename)))
    (display-png (make-instance 'png-bytes :bytes bytes))))


(defclass svg-str ()
  ((str :initarg :str :reader svg-str)))


(defmethod render-svg ((img svg-str))
  (svg-str img))


(defun svg (desc)
  (display-svg (make-instance 'svg-str :str desc)))


(defun svg-from-file (filename)
  (let ((str (read-string-file filename)))
    (display-svg (make-instance 'svg-str :str str))))


;;; History management

(defun %in (hist-ref)
  (let ((history-in (slot-value cl-jupyter::*evaluator* 'cl-jupyter::history-in)))
    (if (and (>= hist-ref 0)
	     (< hist-ref (length history-in))) 
	(aref history-in hist-ref)
	nil)))

(defun %out (hist-ref &optional (value-ref 0))
  (let ((history-out (slot-value cl-jupyter::*evaluator* 'cl-jupyter::history-out)))
    (if (and (>= hist-ref 0)
	     (< hist-ref (length history-out)))
	(let ((out-values  (aref history-out hist-ref)))
	  (if (and (>= value-ref 0)
		   (< value-ref (length out-values))) 
	      (elt out-values value-ref)
	      nil)))))



;;;;;;;;;;;;;;
;;; Kernel ;;;
;;;;;;;;;;;;;;

(in-package #:cl-jupyter)


(defclass kernel ()
  ((config :initarg :config :reader kernel-config)
   (ctx :initarg :ctx :reader kernel-ctx)
   (shell :initarg :shell :initform nil :reader kernel-shell)
   (iopub :initarg :iopub :initform nil :reader kernel-iopub)
   (session :initarg :session :reader kernel-session)
   (evaluator :initarg :evaluator :initform nil :reader kernel-evaluator))
  (:documentation "Kernel state representation."))


(defun make-kernel (config)
  (let ((ctx (pzmq:ctx-new))
	(session-id (format nil "~W" (uuid:make-v4-uuid))))
    (make-instance 'kernel
                   :config config
                   :ctx ctx
		   :session session-id)))

;;; not used in ispad
(defun get-argv ()
  ;; Borrowed from apply-argv, command-line-arguments.  Temporary solution (?)
  #+sbcl (cdr sb-ext:*posix-argv*)
  #+clozure CCL:*UNPROCESSED-COMMAND-LINE-ARGUMENTS*  ;(ccl::command-line-arguments)
  #+gcl si:*command-args*
  #+ecl (loop for i from 0 below (si:argc) collect (si:argv i))
  #+cmu extensions:*command-line-strings*
  #+allegro (sys:command-line-arguments)
  #+lispworks sys:*line-arguments-list*
  #+clisp ext:*args*
  #-(or sbcl clozure gcl ecl cmu allegro lispworks clisp)
  (error "get-argv not supported for your implementation"))


(defun join (e l)
  (cond ((endp l) (list))
        ((endp (cdr l)) l)
        (t (cons (car l) (cons e (join e (cdr l)))))))


(defun concat-all (kind term ls)
  (if (endp ls)
      term
      (concatenate kind (car ls) (concat-all kind term (cdr ls)))))


(defun banner ()
  (concat-all
   'string ""
   (join (format nil "~%") '("cl-jupyter V???"))))

;; (format t (banner))



(defclass kernel-config ()
  ((transport :initarg :transport :reader config-transport :type string)
   (ip :initarg :ip :reader config-ip :type string)
   (shell-port :initarg :shell-port :reader config-shell-port :type fixnum)
   (iopub-port :initarg :iopub-port :reader config-iopub-port :type fixnum)
   (control-port :initarg :control-port :reader config-control-port :type fixnum)
   (stdin-port :initarg :stdin-port :reader config-stdin-port :type fixnum)
   (hb-port :initarg :hb-port :reader config-hb-port :type fixnum)
   (signature-scheme :initarg :signature-scheme :reader config-signature-scheme :type string)
   (key :initarg :key :reader kernel-config-key))) 


(defun kernel-start (connect-file)
  (let ((cmd-args (get-argv)))
    ;(princ (banner))
    (write-line "")
    (format t "iSPAD V~A, Jupyter kernel based on ~%" +ISPAD-VERSION+)
    (format t "~A: an enhanced interactive Common Lisp REPL~%" +KERNEL-IMPLEMENTATION-NAME+)
    (format t "(Version ~A - Jupyter protocol v.~A)~%"
            +KERNEL-IMPLEMENTATION-VERSION+
            +KERNEL-PROTOCOL-VERSION+)
    (format t "--> (C) 2014-2015 Frederic Peschanski (cf. LICENSE)~%")
    (write-line "")
    (let ((connection-file-name connect-file))
      ;; (format t "connection file = ~A~%" connection-file-name)
      (unless (stringp connection-file-name)
        (error "Wrong connection file argument (expecting a string)"))
      (let ((config-alist (parse-json-from-string (concat-all 'string "" (read-file-lines connection-file-name)))))
        ;; (format t "kernel configuration = ~A~%" config-alist)
        (let ((config
               (make-instance 'kernel-config
                   :transport (afetch "transport" config-alist :test #'equal)
                   :ip (afetch "ip" config-alist :test #'equal)
                   :shell-port (afetch "shell_port" config-alist :test #'equal)
                   :iopub-port (afetch "iopub_port" config-alist :test #'equal)
                   :control-port (afetch "control_port" config-alist :test #'equal)
                   :hb-port (afetch "hb_port" config-alist :test #'equal)
                   :signature-scheme (afetch "signature_scheme" config-alist :test #'equal)           
                   :key (let ((str-key (afetch "key" config-alist :test #'equal)))
                     (if (string= str-key "")
                       nil
                      (babel:string-to-octets str-key :encoding :ASCII))))))
          (when (not (string= (config-signature-scheme config) "hmac-sha256"))
            ;; XXX: only hmac-sha256 supported
            (error "Kernel only support signature scheme 'hmac-sha256' (provided ~S)" (config-signature-scheme config)))
               
          ;;(inspect config)
          (let* ((kernel (make-kernel config))
                 (evaluator (make-evaluator kernel))
                 (shell (make-shell-channel kernel))
                 (iopub (make-iopub-channel kernel)))
	    ;; Launch the hearbeat thread
	    (let ((hb-socket (pzmq:socket (kernel-ctx kernel) :rep)))
	      (let ((hb-endpoint (format nil "~A://~A:~A"
					 (config-transport config)
					 (config-ip config)
					 (config-hb-port config))))
		;;(format t "heartbeat endpoint is: ~A~%" endpoint)
		(pzmq:bind hb-socket hb-endpoint)
		(let ((heartbeat-thread-id (start-heartbeat hb-socket)))
		  ;; main loop
		  (unwind-protect
		       (format t "[Kernel] Entering mainloop ... ~%")
		       (shell-loop shell)
		    ;; clean up when exiting
		    (bordeaux-threads:destroy-thread heartbeat-thread-id)
		    (pzmq:close hb-socket)
		    (pzmq:close (iopub-socket iopub))
		    (pzmq:close (shell-socket shell))
		    (pzmq:ctx-destroy (kernel-ctx kernel))
		    (format t "Bye bye.~%")))))))))))


(defun start-heartbeat (socket)
  (let ((thread-id (bordeaux-threads:make-thread
		    (lambda ()
		      (format t "[Heartbeat] thread started ~%")
		      (loop
			 (pzmq:with-message msg
			   (pzmq:msg-recv msg socket)
					;;(format t "Heartbeat Received:~%")
			   (pzmq:msg-send msg socket)
					;;(format t "  | message: ~A~%" msg)
			   ))))))
    thread-id))


;;;;;;;;;;;;
;;; BOOT ;;;
;;;;;;;;;;;;

;(in-package #:boot)


        
          


;;;;;;;;;;;;
;;; DATA ;;;
;;;;;;;;;;;;

(in-package #:cl-jupyter)

;;;+NEW
(defparameter ax-tokens
'("AND" "Aleph" "An" "And" "B1solve"  "BY"  "BasicMethod"  "Beta"  "BumInSepFFE"
"Chi" "Ci" "D" "Delta" "DiffAction" "DiffC" "EQ" "EXPRR2F"  "Ei"  "F"  "F2EXPRR"
"F2FG"  "FG2F"  "FormatArabic"  "FormatRoman"  "Frobenius"  "GE"  "GF2FG"   "GT"
"Gamma"  "GospersMethod"  "HP_solve"  "HP_solve_A"  "HP_solve_I"    "HP_solve_M"
"HP_solve_P"    "HP_solve_PA"    "HankelMatrix"    "Hausdorff"      "HenselLift"
"HermiteIntegrate"  "I"  "Is"  "JContinuedFraction"  "K"   "KrullNumber"    "LE"
"LLFI_to_LPA"  "LLFPI_to_LPA"   "LLF_to_LPA"    "LODO2FUN"    "LT"    "LUDecomp"
"LUInverse"    "LUSolve"    "LagrangeInterpolation"    "Lazard"        "Lazard2"
"LazardQuotient"        "LazardQuotient2"        "LiePoly"        "LiePolyIfCan"
"LowTriBddDenomInv"    "LyndonBasis"    "LyndonCoordinates"    "LyndonWordsList"
"LyndonWordsList1" "MPtoMPT" "NOT" "Not"  "Nul"  "OMParseError?"  "OMReadError?"
"OMUnknownCD?"   "OMUnknownSymbol?"    "OMbindTCP"    "OMclose"    "OMcloseConn"
"OMconnInDevice"    "OMconnOutDevice"    "OMconnectTCP"       "OMencodingBinary"
"OMencodingSGML"  "OMencodingUnknown"  "OMencodingXML"  "OMgetApp"    "OMgetAtp"
"OMgetAttr" "OMgetBVar" "OMgetBind" "OMgetEndApp"  "OMgetEndAtp"  "OMgetEndAttr"
"OMgetEndBVar"  "OMgetEndBind"  "OMgetEndError"  "OMgetEndObject"   "OMgetError"
"OMgetFloat"   "OMgetInteger"    "OMgetObject"    "OMgetString"    "OMgetSymbol"
"OMgetType"    "OMgetVariable"    "OMlistCDs"    "OMlistSymbols"    "OMmakeConn"
"OMopenFile"  "OMopenString"  "OMputApp"  "OMputAtp"  "OMputAttr"    "OMputBVar"
"OMputBind"   "OMputEndApp"    "OMputEndAtp"    "OMputEndAttr"    "OMputEndBVar"
"OMputEndBind"  "OMputEndError"  "OMputEndObject"   "OMputError"    "OMputFloat"
"OMputInteger"  "OMputObject"  "OMputString"    "OMputSymbol"    "OMputVariable"
"OMread"    "OMreadFile"    "OMreadStr"    "OMreceive"    "OMsend"     "OMserve"
"OMsetEncoding"    "OMsupportsCD?"    "OMsupportsSymbol?"    "OMunhandledSymbol"
"OMwrite" "OR" "One" "Or" "P" "ParCond" "ParCondList"  "Pfaffian"  "Pm"  "Pnan?"
"PollardSmallFactor"    "Pr"    "R1_to_R2_coercion"    "RF2UTS"    "ReduceOrder"
"RemainderList"  "RittWuCompare"  "S"  "SEGMENT"  "SFunction"    "SPDEnocancel1"
"STransform" "STransform1"  "STransform2"  "ScanArabic"  "ScanFloatIgnoreSpaces"
"ScanFloatIgnoreSpacesIfCan"  "ScanRoman"  "Shi"  "ShiftAction"  "ShiftC"   "Si"
"Somos"   "SturmHabicht"    "SturmHabichtCoefficients"    "SturmHabichtMultiple"
"SturmHabichtSequence"  "U"  "UP2UTS"    "UP2ifCan"    "UTS2UP"    "UnVectorise"
"UpTriBddDenomInv"  "VSUPI_to_VPA"  "VSUPPI_to_VPA"  "VSUPS_to_VPA"  "Vectorise"
"X" "Y" "Zero" "aCubic" "aLinear" "aQuadratic" "aQuartic"  "abelianGroup"  "abs"
"absolutelyIrreducible?"  "acos"  "acosIfCan"  "acosh"    "acoshIfCan"    "acot"
"acotIfCan"  "acoth"  "acothIfCan"  "acsc"  "acscIfCan"  "acsch"    "acschIfCan"
"adaptive"    "adaptive3D?"    "adaptive?"    "addArrow!"      "addArrows2Din2D"
"addBadValue"    "addChild!"    "addMatch"    "addMatchRestricted"    "addNode!"
"addObject!"            "addPlot1Din2D"                "addPlot1Din2Dparametric"
"addPlot1Din3Dparametric" "addPlot2Din3D"  "addPlot2Din3Dparametric"  "addPoint"
"addPoint2"  "addPointLast"  "addPoints!"    "addSceneArrow"    "addSceneArrows"
"addSceneBox"  "addSceneClip"  "addSceneDef"   "addSceneGraph"    "addSceneGrid"
"addSceneGroup"       "addSceneIFS"        "addSceneLine"        "addSceneLines"
"addSceneMaterial"  "addSceneNamedPoints"   "addScenePattern"    "addSceneRuler"
"addSceneShape" "addSceneText"  "addSceneTransform"  "addSceneUse"  "addWArrow!"
"addWarning"  "add_slots"  "addiag"  "additive?"   "addmod"    "adjacencyMatrix"
"adjoint" "airyAi" "airyAiPrime" "airyBi" "airyBiPrime"  "algDepHP"  "algDsolve"
"algSplitSimple" "alg_reduce"  "alg_reduce0"  "alg_trial_division"  "algebraic?"
"algebraicCoefficients?"  "algebraicDecompose"   "algebraicGcd"    "algebraicOf"
"algebraicSort"  "algebraicVariables"  "algint"   "algintegrate"    "allDegrees"
"allIndices"    "allRepeated"    "allRootsOf"    "allSimpleCells"        "alpha"
"alphaHilbert"  "alphabetic"  "alphabetic?"    "alphanumeric"    "alphanumeric?"
"alternating"   "alternatingGroup"    "alternative?"    "analyseSymbol"    "and"
"anfactor"    "angerJ"    "annihilate?"       "ansatz"        "antiAssociative?"
"antiCommutative?"  "antiCommutator"  "anticoord"  "antipode"   "antisymmetric?"
"antisymmetricTensors"  "any"  "any?"  "append"    "appendPoint"    "appendRow!"
"apply" "applyQuote" "applyRules" "applyTaylor"  "apply_taylor"  "approxNthRoot"
"approxSqrt" "approximants" "approximate"  "arbFunctions"  "arcsineDistribution"
"areEquivalent?"  "arg1"  "arg2"    "argscript"    "argument"    "argumentList!"
"argumentListOf"  "arguments"  "arity"  "aromberg"   "arrayStack"    "arrowName"
"arrowsFromArrow"  "arrowsFromNode"  "arrowsToArrow"    "arrowsToNode"    "asec"
"asecIfCan"  "asech"  "asechIfCan"  "asimpson"  "asin"    "asinIfCan"    "asinh"
"asinhIfCan"    "assert"    "assign"        "assoc"        "associatedEquations"
"associatedSystem"       "associates?"        "associative?"        "associator"
"associatorDependence"   "atType"    "atan"    "atan1"    "atanIfCan"    "atanh"
"atanhIfCan"   "atom?"    "atoms"    "atrapezoidal"    "augment"    "autoReduce"
"autoReduced?"  "axes"  "axesColorDefault"    "back"    "backOldPos"    "badNum"
"badValues"    "balancedBinaryTree"    "balancedFactorisation"      "bandMatrix"
"bandedHessian"  "bandedJacobian"  "base"  "baseRDE"  "baseRDEsys"    "basicSet"
"basis"    "basisOfCenter"    "basisOfCentroid"       "basisOfCommutingElements"
"basisOfLeftAnnihilator"        "basisOfLeftNucleus"        "basisOfLeftNucloid"
"basisOfMiddleNucleus"        "basisOfNucleus"         "basisOfRightAnnihilator"
"basisOfRightNucleus"  "basisOfRightNucloid"  "bat"    "bat1"    "beauzamyBound"
"belong?"  "bernoulli"    "bernoulliB"    "bernoulliDistribution01"    "besselI"
"besselJ"    "besselK"    "besselY"    "bezoutDiscriminant"       "bezoutMatrix"
"bezoutResultant"  "biRank"   "binary"    "binaryFunction"    "binarySearchTree"
"binaryTournament"  "binaryTree"  "bind"  "binomThmExpt"  "binomial"   "bipolar"
"bipolarCylindrical" "birth"  "bit?"  "bitCoef"  "bitLength"  "bitTruth"  "bits"
"bivariate?" "bivariatePolynomials"  "bivariateSLPEBR"  "blankSeparate"  "block"
"blockConcat"   "blockSplit"    "blue"    "bombieriNorm"    "booleanConvolution"
"booleanCumulant"    "booleanCumulant2moment"        "booleanCumulantFromJacobi"
"booleanCumulants"  "bottom"  "bound"  "boundAt0"  "boundInf"    "boundOfCauchy"
"boundary" "box" "boxBoundary" "brace"  "bracket"  "branchIfCan"  "branchPoint?"
"branchPointAtInfinity?"  "bright"  "brillhartIrreducible?"    "brillhartTrials"
"bringDown"  "bsolve"  "btwFact"  "bubbleSort!"  "build"  "bumprow"    "bumptab"
"bumptab1" "cAcos" "cAcosh" "cAcot" "cAcoth" "cAcsc" "cAcsch"  "cAsec"  "cAsech"
"cAsin" "cAsinh" "cAtan" "cAtanh" "cCos" "cCosh" "cCot" "cCoth"  "cCsc"  "cCsch"
"cExp" "cLog" "cPower" "cRationalPower" "cSec"  "cSech"  "cSin"  "cSinh"  "cTan"
"cTanh"  "calcRanges"  "call"  "canonicalBasis"  "canonicalIfCan"  "cap"   "car"
"cardinality"  "carmichaelLambda"  "cartesian"   "catalan"    "cdr"    "ceiling"
"center"    "certainlySubVariety?"      "chainSubResultants"        "changeBase"
"changeExprLength"   "changeVar"    "changeWeightLevel"    "char"    "charClass"
"character?" "characteristic"  "characteristicPolynomial"  "characteristicSerie"
"characteristicSet"    "charlierC"    "charpol"    "charthRoot"     "chebyshevT"
"chebyshevU"   "check"    "checkExtraValues"    "checkForZero"    "checkOptions"
"checkRur" "checkType" "check_sol1a" "chiSquare" "chiSquare1"  "child"  "child?"
"children"  "chineseRemainder"  "chinese_update"  "chkLibraryError"  "choosemon"
"chvar"        "class"        "classicalConvolution"         "classicalCumulant"
"classicalCumulants" "clearCache"  "clearDenominator"  "clearFortranOutputStack"
"clearTable!"    "clearTheSymbolTable"     "clear_used_intrinsics"        "clip"
"clipBoolean"    "clipParametric"       "clipPointsDefault"        "clipSurface"
"clipWithRanges" "close" "close!" "closeComponent"  "closed?"  "closedCartesian"
"closedCurve"  "closedCurve?"  "closedTensor"  "cmult"  "coAdjoint"   "coHeight"
"code"  "coef"  "coefChoose"  "coefficient"   "coefficientSet"    "coefficients"
"coeffs0"  "coeffs1"  "coerce"  "coerceImages"  "coerceL"    "coerceListOfPairs"
"coerceP"   "coercePreimagesImages"    "coerceS"    "coerceToType"    "colSlice"
"coleman"    "colinearity"    "collect"    "collectQuasiMonic"    "collectUnder"
"collectUpper"  "color"  "colorDef"  "colorFunction"  "column"    "columnMatrix"
"columnSpace" "columns" "commaSeparate" "comment"  "common"  "commonDenominator"
"commutative?"    "commutativeEquality"    "commutator"    "comp"    "compBound"
"compactFraction"   "companionBlocks"    "comparison"    "compdegd"    "compile"
"compiledFunction"    "complement"    "complementSpace"     "complementaryBasis"
"complete" "complete2"  "completeEchelonBasis"  "completeEval"  "completeHensel"
"completeHermite"  "completeSmith"  "complex"  "complex?"   "complexEigenvalues"
"complexEigenvectors"    "complexElementary"    "complexExpand"    "complexForm"
"complexIntegrate"    "complexLimit"    "complexNormalize"      "complexNumeric"
"complexNumericIfCan" "complexRoots" "complexSolve"  "complexZeros"  "component"
"components"  "compose"  "composite"  "composites"  "compound"    "computeBasis"
"computeCycleEntry" "computeCycleLength" "computeInt"  "computePowers"  "concat"
"concat!"      "cond"        "condition"        "conditionP"        "conditions"
"conditionsForIdempotents" "conical" "conj"  "conjug"  "conjugate"  "conjugates"
"connect"  "cons"  "consRow!"  "consnewpol"  "const"   "const?"    "constDsolve"
"constant"    "constant?"      "constantCoefficientRicDE"        "constantIfCan"
"constantKernel"    "constantLeft"    "constantOpIfCan"       "constantOperator"
"constantRight"   "constantToUnaryFunction"    "construct"    "constructOrdered"
"contains?"   "containsPoint?"    "content"    "continue"    "continuedFraction"
"contraAdjoint"  "contract"   "contractSolve"    "controlPanel"    "convergents"
"convert"  "coord"  "coordinate"  "coordinates"   "coordinatesIfCan"    "copies"
"coproduct" "copy"  "copy!"  "copyInto!"  "copy_first"  "copy_slice"  "corrPoly"
"cos" "cos2sec" "cosIfCan" "cosSinInfo"  "cosh"  "cosh2sech"  "coshIfCan"  "cot"
"cot2tan" "cot2trig"  "cotIfCan"  "coth"  "coth2tanh"  "coth2trigh"  "cothIfCan"
"counit"  "count"   "countRealRoots"    "countRealRootsMultiple"    "countable?"
"create"    "create3Space"     "createArrows2Din2D"        "createGenericMatrix"
"createIrreduciblePoly"                         "createLowComplexityNormalBasis"
"createLowComplexityTable"                          "createMultiplicationMatrix"
"createMultiplicationTable"      "createNormalElement"        "createNormalPoly"
"createNormalPrimitivePoly"   "createPlot1Din2D"    "createPlot1Din2Dparametric"
"createPlot1Din3Dparametric"  "createPlot2Din3D"    "createPlot2Din3Dparametric"
"createPrimitiveElement"    "createPrimitiveNormalPoly"    "createPrimitivePoly"
"createRandomElement"  "createSceneArrow"  "createSceneArrows"  "createSceneBox"
"createSceneClip"    "createSceneDef"    "createSceneGraph"    "createSceneGrid"
"createSceneGroup"   "createSceneIFS"    "createSceneLine"    "createSceneLines"
"createSceneMaterial"       "createSceneNamedPoints"        "createScenePattern"
"createSceneRoot"  "createSceneRuler"    "createSceneShape"    "createSceneText"
"createSceneTransform"   "createSceneUse"    "createThreeSpace"    "createWidth"
"createX"  "createY"  "createZechTable"  "credPol"  "critB"  "critBonD"  "critM"
"critMTonD1"  "critMonD1"  "critT"  "critpOrder"  "cross"  "crushedSet"    "csc"
"csc2sin"  "cscIfCan"  "csch"  "csch2sinh"    "cschIfCan"    "csubst"    "cubic"
"cumulant2moment" "cup"  "currentSubProgram"  "curry"  "curryLeft"  "curryRight"
"curve"  "curve?"  "curveColor"   "curveColorPalette"    "curveLoops"    "cycle"
"cycleClosed"    "cycleElt"    "cycleEntry"     "cycleLength"        "cycleOpen"
"cyclePartition"  "cycleRagits"  "cycleSplit!"  "cycleTail"  "cycles"   "cyclic"
"cyclic?"    "cyclicCopy"    "cyclicEntries"    "cyclicEqual?"     "cyclicGroup"
"cyclicParents"   "cyclicSubmodule"    "cyclotomic"    "cyclotomicDecomposition"
"cyclotomicFactorization"    "cylindrical"    "cylindricalDecomposition"     "d"
"dAndcExp"  "dP"  "dSubst"  "dU"  "dX"  "dark"  "datalist"   "ddFact"    "debug"
"debug3D"  "dec"  "decFatal"  "decXfFatal"  "decXfPass"   "decimal"    "declare"
"declare!"  "decompose"   "decomposeFunc"    "decreasePrecision"    "deductions"
"deepCopy"  "deepDiagramSvg"   "deepExpand"    "deepestInitial"    "deepestTail"
"defineProperty" "definingEquations"  "definingInequation"  "definingPolynomial"
"degree"  "degreePartition"  "degreeSubResultant"  "degreeSubResultantEuclidean"
"delay"  "delete"  "delete!"  "deleteProperty!"  "deleteRow!"  "delta"   "denom"
"denomLODE"  "denomRicDE"  "denominator"  "denominators"    "depth"    "dequeue"
"dequeue!"    "deref"    "deriv"     "derivationCoordinates"        "derivative"
"derivativeOf?" "destruct" "detSys" "detSysNS" "determinant"  "diag"  "diagonal"
"diagonal?"  "diagonalMatrix"  "diagonalProduct"  "diagonals"    "diagramHeight"
"diagramSvg"  "diagramWidth"  "dictionary"  "diff"  "diffHP"  "diffP"    "diffU"
"diffX"  "diff_map"   "difference"    "differentialVariables"    "differentials"
"differentiate" "digamma" "digit" "digit?" "digits"  "dihedral"  "dihedralGroup"
"dilate" "dilog" "dim" "dimJ" "dimS" "dimension" 
"dimensionOfIrreducibleRepresentation"  "dimensions"  "dimensionsOf"  "dioSolve"
"diophantineSystem"  "directProduct"  "directSum"  "directedGraph"   "direction"
"directions" "directory"  "discreteLog"  "discriminant"  "discriminantEuclidean"
"discriminantSet"  "dispStatement"  "display"    "displayKind"    "displayLines"
"displayLines1"  "distFact"  "distance"    "distanceMatrix"    "distanceSquared"
"distanceWeighted"  "distdfact"  "distribute"   "distributionByBooleanCumulants"
"distributionByClassicalCumulants"                   "distributionByEvenMoments"
"distributionByFreeCumulants"                   "distributionByJacobiParameters"
"distributionByMoments"                        "distributionByMonotoneCumulants"
"distributionBySTransform"  "divergence"  "divide"  "divide!"  "divideExponents"
"divideIfCan" "divideIfCan!"  "divisor"  "divisorCascade"  "divisors"  "dmp2rfi"
"dmpToHdmp" "dmpToP" "doFactor" "do_liou"  "do_modular_solve"  "do_poly_integer"
"do_quo"    "do_with_error_env0"    "do_with_error_env1"    "do_with_error_env2"
"do_with_error_env3" "dom" "domainOf" "dominantTerm"  "dot"  "double"  "double?"
"doubleComplex?"     "doubleDisc"        "doubleFloatFormat"        "doubleRank"
"doubleResultant"        "doublyTransitive?"        "draw"         "drawComplex"
"drawComplexVectorField"  "drawCurves"   "drawStyle"    "drawToScale"    "droot"
"duplicates" "duplicates?" "e" "eFromBinaryMap"  "ePseudoscalar"  "ee"  "ei_int"
"eigenMatrix"        "eigenvalues"        "eigenvector"           "eigenvectors"
"eisensteinIrreducible?"  "elColumn2!"  "elRow1!"  "elRow2!"  "elem?"  "element"
"element?"    "elementary"    "elements"    "elimZeroCols!"    "ellipseBoundary"
"elliptic"    "ellipticCylindrical"    "ellipticE"    "ellipticF"    "ellipticK"
"ellipticPi"  "ellipticRC"  "ellipticRD"   "ellipticRF"    "ellipticRJ"    "elt"
"eltable?"  "empty"    "empty?"    "endOfFile?"    "endSubProgram"    "enqueue!"
"enterInCache" "enterPointData" "entries" "entry?" "enumerate"  "epilogue"  "eq"
"eq?"  "eqRep?"  "equality"  "equation"  "erf"  "erfi"    "error"    "errorInfo"
"errorKind" "escape" "euclideanGroebner"  "euclideanNormalForm"  "euclideanSize"
"euler"  "eulerE"  "eulerPhi"  "eval"  "eval1"  "eval1a"  "eval_at"   "evaluate"
"evaluateInverse" "even?" "evenInfiniteProduct" "evenlambert"  "every?"  "exQuo"
"exactQuotient"  "exactQuotient!"  "exists?"  "exp"  "exp0"  "exp1"   "expIfCan"
"expPot"    "expand"    "expandLog"    "expandPower"        "expandTrigProducts"
"expextendedint"  "expint"  "expintegrate"  "expintfldpoly"   "explicitEntries?"
"explicitlyEmpty?" "explicitlyFinite?"  "explogint"  "explogs2trigs"  "exponent"
"exponential"  "exponential1"  "exponentialOrder"  "exponents"    "exprToGenUPS"
"exprToPS"  "exprToUPS"  "exprToXXP"    "expr_to_series"    "expressIdealMember"
"expression2Fortran" "expression2Fortran1"  "exprex"  "expt"  "exptMod"  "exquo"
"extend"  "extendIfCan"  "extendToPoint"  "extendedCoords"   "extendedEuclidean"
"extendedIntegrate"        "extendedResultant"         "extendedSubResultantGcd"
"extended_gcd"        "extendedint"        "extension"         "extensionDegree"
"exteriorDifferential"  "external?"    "externalList"    "extract"    "extract!"
"extractBottom!" "extractClosed"  "extractIfCan"  "extractIndex"  "extractPoint"
"extractProperty"    "extractSplittingLeaf"    "extractSymbol"     "extractTop!"
"eyeDistance"   "factor"    "factor1"    "factorAndSplit"    "factorByRecursion"
"factorFraction"    "factorGroebnerBasis"    "factorList"       "factorOfDegree"
"factorPolynomial"          "factorSFBRlcUnit"                "factorSquareFree"
"factorSquareFreeByRecursion"    "factorSquareFreePolynomial"        "factorial"
"factorials"    "factors"    "factorsOfCyclicGroupSize"        "factorsOfDegree"
"factorset" "failed" "failed?" "false" "ffactor" "ffactor1"  "fffg"  "fglmIfCan"
"fibonacci"    "filename"    "fill!"    "fillPascalTriangle"       "filterUntil"
"filterWhile"    "find"    "findCycle"    "findNode"    "findPoint"    "finite?"
"finiteBasis" "fintegrate" "first" "firstDenom"  "firstNumer"  "firstSubsetGray"
"firstUncouplingMatrix"     "firstn"        "fixPredicate"        "fixedDivisor"
"fixedPointExquo"    "fixedPoints"    "flagFactor"    "flatten"      "flexible?"
"flexibleArray"  "float"  "float?"    "floor"    "flush"    "fmecg"    "forLoop"
"formalDiff"  "formalDiff2"  "formula"  "fortFormatHead"   "fortFormatTypeLines"
"fort_clean_lines"   "fort_format_types"    "fortran"    "fortranCarriageReturn"
"fortranCharacter"  "fortranComplex"   "fortranDouble"    "fortranDoubleComplex"
"fortranInteger"    "fortranLiteral"    "fortranLiteralLine"    "fortranLogical"
"fortranReal"    "fortranTypeOf"    "fprindINFO"    "fracPart"      "fractRadix"
"fractRagits"  "fractionFreeGauss!"  "fractionPart"  "free?"   "freeConvolution"
"freeCumulant"              "freeCumulant2moment"                "freeCumulants"
"freeMultiplicativeConvolution"       "freeOf?"        "freePoissonDistribution"
"freeVariable?"  "fresnelC"  "fresnelS"  "frobenius"  "front"  "froot"    "frst"
"fullDisplay" "fullPartialFraction"  "function"  "functionGraph"  "functionName"
"functionNames" "gamma" "gauge" "gaugeHilbert"  "gaussianDistribution"  "gbasis"
"gcd" "gcdBasis" "gcdDecomposition" "gcdPolynomial"  "gcdPrimitive"  "gcdcofact"
"gcdcofactprim"  "gcdprim"   "gderiv"    "genVectorStream"    "genVectorStream2"
"gen_Monte_Carlo_check"     "generalCoefficient"        "generalInfiniteProduct"
"generalInterpolation"    "generalLambert"    "generalPosition"    "generalSqFr"
"generalTwoFactor"                       "generalizedContinuumHypothesisAssumed"
"generalizedContinuumHypothesisAssumed?"                "generalizedEigenvector"
"generalizedEigenvectors" "generalizedInverse"  "generateIrredPoly"  "generator"
"generators"        "generic"        "generic?"        "genericLeftDiscriminant"
"genericLeftMinimalPolynomial"       "genericLeftNorm"        "genericLeftTrace"
"genericLeftTraceForm"       "genericPosition"        "genericRightDiscriminant"
"genericRightMinimalPolynomial"    "genericRightNorm"        "genericRightTrace"
"genericRightTraceForm"  "genus"   "geometric"    "getArrowIndex"    "getArrows"
"getBadValues" "getBoundValue" "getCentre"  "getChildren"  "getCode"  "getCurve"
"getDatabase" "getEq" "getGoodPrime"  "getGraph"  "getMatch"  "getMax"  "getMin"
"getMultiplicationMatrix"    "getMultiplicationTable"    "getName"    "getNames"
"getNotation"  "getOrder"  "getPickedPoints"  "getRef"   "getSimplifyDenomsFlag"
"getStatement"   "getStream"    "getType"    "getVariable"    "getVariableOrder"
"getVertexIndex"    "getVertices"        "getZechTable"        "get_fort_indent"
"get_rational_roots"    "get_used_intrinsics"    "get_variables"       "gnuDraw"
"goodPoint"  "gotoJump"  "grade"    "gradeInvolution"    "gradient"    "graeffe"
"gramschmidt" "graphCurves"  "graphImage"  "graphState"  "graphStates"  "graphs"
"green"  "groebSolve"  "groebgen"  "groebner"  "groebner?"   "groebnerFactorize"
"groebnerIdeal" "ground" "ground?" "guess" "guessADE"  "guessAlg"  "guessAlgDep"
"guessBinRat"  "guessExpRat"  "guessFE"  "guessHolo"  "guessPRec"    "guessPade"
"guessRat"    "guessRec"    "hMonic"    "hadamard"      "halfExtendedResultant1"
"halfExtendedResultant2"                          "halfExtendedSubResultantGcd1"
"halfExtendedSubResultantGcd2"    "hankelDeterminant"       "hankelDeterminants"
"hankelH1"    "hankelH2"    "harmonic"    "has?"    "hasDimension?"      "hasHi"
"hasPredicate?"    "hasSolution?"    "hasTopPredicate?"    "has_op?"      "hash"
"hashUpdate!" "hasoln" "hclf"  "hconcat"  "hcrf"  "hdmpToDmp"  "hdmpToP"  "head"
"headReduce"  "headReduced?"  "headRemainder"   "heap"    "heapSort"    "height"
"henselFact" "hensel_update" "hermite"  "hermiteH"  "hessian"  "hex"  "hexDigit"
"hexDigit?"    "hi"    "high"    "highCommonTerms"    "hilbert"    "hitherPlane"
"homogeneous" "homogeneous?"  "horizConcat"  "horizJoin"  "horizSplit"  "hspace"
"htrigs" "hue" "hyperelliptic" "hypergeometric0F1"  "hypergeometricF"  "iAiryAi"
"iAiryAiPrime" "iAiryBi" "iAiryBiPrime"  "iCompose"  "iExquo"  "iLambertW"  "id"
"id_map"    "ideal"    "idealSimplify"      "idealiser"        "idealiserMatrix"
"identification"    "identity"    "identityMatrix"        "identitySquareMatrix"
"iexactQuo"  "ignore?"  "iiAiryAi"  "iiAiryAiPrime"  "iiAiryBi"  "iiAiryBiPrime"
"iiBesselI"   "iiBesselJ"    "iiBesselK"    "iiBesselY"    "iiBeta"    "iiGamma"
"iiHypergeometricF" "iiPolylog" "iiabs" "iiacos"  "iiacosh"  "iiacot"  "iiacoth"
"iiacsc" "iiacsch" "iiasec"  "iiasech"  "iiasin"  "iiasinh"  "iiatan"  "iiatanh"
"iibinom"  "iicos"  "iicosh"  "iicot"  "iicoth"  "iicsc"  "iicsch"   "iidigamma"
"iidprod"  "iidsum"  "iiexp"  "iifact"  "iilog"  "iim2"  "iiperm"  "iipolygamma"
"iipow" "iiretractVar" "iisec" "iisech"  "iisin"  "iisinh"  "iisqrt2"  "iisqrt3"
"iitan" "iitanh" "imag" "imagE"  "imagI"  "imagJ"  "imagK"  "imagi"  "imaginary"
"imagj"  "imagk"  "implies"  "in?"  "inBounds?"   "inDegree"    "inGroundField?"
"inHallBasis?"    "inR?"    "inRadical?"    "inc"    "incFail"        "incFatal"
"incLibraryError"  "incPass"  "incXfFail"    "incXfFatal"    "incXfLibraryError"
"incXfPass"  "incidenceMatrix"  "inconsistent?"    "incr"    "increasePrecision"
"increment"  "incrementBy"  "incrementKthElement"   "indentFortLevel"    "index"
"index?" "indexName" "indexes" "indiceSubResultant" 
"indiceSubResultantEuclidean"        "indices"                "indicialEquation"
"indicialEquationAtInfinity" "indicialEquations"  "inf"  "infLex?"  "infRittWu?"
"infieldIntegrate"  "infieldint"  "infinite?"    "infiniteProduct"    "infinity"
"infinityNorm"  "infix"  "infix?"  "infsum"  "init"    "initTable!"    "initial"
"initializeGroupForWordProblem"     "initiallyReduce"        "initiallyReduced?"
"initials" "innerEigenvectors"  "innerSolve"  "innerSolve1"  "innerint"  "input"
"inrootof"  "insert"  "insert!"  "insertBottom!"  "insertMatch"    "insertRoot!"
"insertTop!"  "insertionSort!"   "inspect"    "int"    "intBasis"    "intChoose"
"intPatternMatch"  "intcompBasis"  "integ"  "integ_df"   "integer"    "integer?"
"integerBound" "integerIfCan" "integerPart"  "integers"  "integral"  "integral?"
"integralAtInfinity?"        "integralBasis"           "integralBasisAtInfinity"
"integralCoordinates"   "integralDerivationMatrix"    "integralLastSubResultant"
"integralMatrix"  "integralMatrixAtInfinity"  "integralRepresents"   "integrate"
"integrateIfCan"  "intensity"  "interReduce"    "internal?"    "internalAugment"
"internalDecompose"        "internalInfRittWu?"              "internalIntegrate"
"internalIntegrate0"      "internalLastSubResultant"        "internalSubPolSet?"
"internalSubQuasiComponent?"  "internalZeroSetSplit"  "interpolate"  "interpret"
"interpretString"  "intersect"  "intersection"  "interval"  "intoMatrix"   "inv"
"inverse" "inverseColeman" "inverseIntegralMatrix" 
"inverseIntegralMatrixAtInfinity" "inverseLaplace"  "invertIfCan"  "invertible?"
"invertibleElseSplit?" "invertibleSet" "invmod" "invmultisect"  "iomode"  "ipow"
"iprint"    "iroot"    "irootDep"      "irreducible?"        "irreducibleFactor"
"irreducibleFactors"            "irreducibleRepresentation"                "is?"
"isAbsolutelyIrreducible?"  "isAcyclic?"  "isBasis?"  "isBoundNode?"    "isBox?"
"isCompound?"  "isDirectSuccessor?"    "isDirected?"    "isEllipse?"    "isExpt"
"isFixPoint?"  "isFreeNode?"  "isFunctional?"  "isGreaterThan?"  "isI?"   "isK?"
"isLambda?" "isList" "isMult"  "isNodeBranch?"  "isNodeLeaf?"  "isNull?"  "isOp"
"isPlus"  "isPoint?"  "isPointLeaf?"  "isPower"  "isQuotient"  "isS?"  "isTimes"
"isVector?"  "is_symbol?"  "isobaric?"  "iter"    "iteratedInitials"    "jacobi"
"jacobi2poly" "jacobiCn" "jacobiDn" "jacobiIdentity?"  "jacobiMatrix"  "jacobiP"
"jacobiParameters"  "jacobiPathArray"  "jacobiSn"  "jacobiTheta"    "jacobiZeta"
"jacobian" "janko2" "jetVariables" "join"  "jordanAdmissible?"  "jordanAlgebra?"
"karatsuba"   "karatsubaDivide"    "karatsubaOnce"    "kelvinBei"    "kelvinBer"
"kelvinKei" "kelvinKer" "kernel" "kernels" "key" "key?" "keys"  "kgraph"  "kmax"
"knownInfBasis"   "kovacic"    "kprod"    "kroneckerDelta"    "kroneckerProduct"
"kroneckerSum"  "kronecker_prod1"  "ksec"  "kummerM"  "kummerU"    "lSpaceBasis"
"label"  "lagrange"  "laguerre"  "laguerreL"  "lambda"   "lambert"    "lambertW"
"lambertW0"        "lambert_inverse_series"                "lambert_via_newton1"
"lambert_via_newton2" "lambintegrate"  "landen"  "landen1"  "landen2"  "laplace"
"laplacian"    "laplacianMatrix"    "largest"    "last"       "lastSubResultant"
"lastSubResultantElseSplit"  "lastSubResultantEuclidean"    "latex"    "laurent"
"laurentIfCan"    "laurentRep"    "lazy?"    "lazyEvaluate"     "lazyGintegrate"
"lazyIntegrate"     "lazyIrreducibleFactors"        "lazyPquo"        "lazyPrem"
"lazyPremWithDefault"        "lazyPseudoDivide"             "lazyPseudoQuotient"
"lazyPseudoRemainder" "lazyResidueClass" "lazyVariations" "lc"  "lcm"  "lcmCoef"
"lcx0"    "lcz"    "leader"       "leadingBasisTerm"        "leadingCoefficient"
"leadingCoefficientRicDE"    "leadingDer"    "leadingExponent"    "leadingIdeal"
"leadingIndex"  "leadingMonomial"   "leadingSupport"    "leadingTerm"    "leaf?"
"leastAffineMultiple"    "leastMonomial"    "leastPower"    "leaves"      "left"
"leftAlternative?"      "leftCharacteristicPolynomial"        "leftDiscriminant"
"leftDivide"    "leftExactQuotient"        "leftExtendedGcd"        "leftFactor"
"leftFactorIfCan"  "leftGcd"  "leftLcm"    "leftMinimalPolynomial"    "leftMult"
"leftNorm"    "leftOne"      "leftPower"        "leftQuotient"        "leftRank"
"leftRankPolynomial"  "leftRecip"  "leftRegularRepresentation"   "leftRemainder"
"leftScalarTimes!"  "leftTrace"    "leftTraceMatrix"    "leftTrim"    "leftUnit"
"leftUnits"  "leftZero"  "legendre"  "legendreP"  "legendreQ"  "length"  "lepol"
"lerchPhi"    "less?"    "level"    "leviCivitaSymbol"    "lex"    "lexGroebner"
"lexTriangular"   "lexico"    "lfextendedint"    "lfextlimint"    "lfinfieldint"
"lfintegrate" "lflogint" "lfunc"  "lhs"  "li"  "li2"  "li_int"  "library"  "lie"
"lieAdmissible?" "lieAlgebra?" "lift" "lifting"  "lifting1"  "light"  "lighting"
"limit"  "limitPart"  "limitPlus"  "limitedIntegrate"  "limitedint"  "linGenPos"
"linSolve"  "lin_sol"  "lineColorDefault"  "lineIntersect"  "linear"   "linear?"
"linearAssociatedExp"       "linearAssociatedLog"        "linearAssociatedOrder"
"linearDependence"    "linearDependenceOverConstants"    "linearDependenceOverZ"
"linearExtend"      "linearPolynomials"        "linearSearch"        "linearize"
"linearlyDependent?"                           "linearlyDependentOverConstants?"
"linearlyDependentOverZ?"  "linears"  "link"  "linkToFortran"  "lintgcd"  "list"
"list?"   "listBranches"    "listConjugateBases"    "listLoops"    "listOfLists"
"listOfMonoms" "listOfTerms"  "listRepresentation"  "listYoungTableaus"  "lists"
"lllip"  "lllp"  "llprop"  "lo"  "localAbs"  "localIntegralBasis"   "localReal?"
"localUnquote"  "log"  "log1"  "log10"  "log2"    "logDependenceQ"    "logGamma"
"logIfCan"  "logicF"  "logicT"  "logical?"  "logpart"   "lommelS1"    "lommelS2"
"lookup"  "loop"  "loopPoints"    "loopsArrows"    "loopsAtNode"    "loopsNodes"
"looseEquals"  "low"  "lowerCase"  "lowerCase!"  "lowerCase?"  "lowerPolynomial"
"lp"  "lprop"  "lquo"  "lyndon"  "lyndon?"  "lyndonIfCan"   "m2r"    "m_inverse"
"magnitude"    "mainCharacterization"    "mainCoefficients"        "mainContent"
"mainDefiningPolynomial"    "mainForm"        "mainKernel"        "mainMonomial"
"mainMonomials"    "mainPrimitivePart"    "mainSquareFreePart"       "mainValue"
"mainVariable"  "mainVariable?"  "mainVariableOf"  "mainVariables"    "makeCell"
"makeCos"  "makeCrit"   "makeEq"    "makeFEq"    "makeFR"    "makeFloatFunction"
"makeGraphImage" "makeMulti" "makeObject"  "makeRec"  "makeRecord"  "makeResult"
"makeSUP"  "makeSeries"  "makeSin"    "makeSketch"    "makeSystem"    "makeTerm"
"makeUnit" "makeVariable" "makeViewport2D"  "makeViewport3D"  "makeYoungTableau"
"makeop"  "makingStats?"  "mantissa"  "map"  "map!"  "mapBivariate"    "mapCoef"
"mapContra"  "mapDown!"  "mapExpon"  "mapExponents"  "mapGen"   "mapMatrixIfCan"
"mapSolve"  "mapUnivariate"  "mapUnivariateIfCan"  "mapUp!"  "mapall"   "mapdiv"
"mapmult"  "mask"  "match"  "match?"   "mathieu11"    "mathieu12"    "mathieu22"
"mathieu23"    "mathieu24"    "matrix"    "matrixConcat3D"    "matrixDimensions"
"matrixGcd"  "max"  "maxColIndex"   "maxDegree"    "maxDerivative"    "maxIndex"
"maxLevel" "maxMixedDegree" "maxPoints" "maxPoints3D"  "maxPower"  "maxRowIndex"
"maxShift" "maxSubst" "maxdeg"  "maximumExponent"  "maxint"  "maxrank"  "maxrow"
"mdeg" "meatAxe" "medialSet" "meijerG" "meixnerM"  "member?"  "members"  "merge"
"merge!"  "merge2"  "mergeDifference"  "mergeFactors"  "merge_exponents"  "mesh"
"mesh?"  "meshFun2Var"  "meshPar1Var"  "meshPar2Var"  "message"   "messagePrint"
"middle"  "midpoint"   "midpoints"    "mightHaveRoots"    "min"    "minColIndex"
"minGbasis"  "minIndex"    "minPoints"    "minPoints3D"    "minPol"    "minPoly"
"minRowIndex"    "mindeg"    "mindegTerm"    "minimalPolynomial"      "minimize"
"minimumDegree"  "minimumExponent"  "minordet"  "minrank"   "minset"    "minus!"
"minusInfinity"  "mirror"  "mix"  "mkAnswer"  "mkIntegral"  "mkPrim"    "mkcomm"
"modTree"    "modifyPoint"    "modifyPointData"    "modpeval"    "modpreduction"
"modularFactor"    "modularGcd"    "modularGcdPrimitive"     "modularInvariantJ"
"module"  "moduleSum"  "moduloP"  "modulus"  "moebius"   "moebiusMu"    "moment"
"moment2Stransform"        "moment2booleanCumulant"            "moment2cumulant"
"moment2freeCumulant"            "moment2jacobi"                "moment2jacobi2"
"moment2monotoneCumulant"    "moment2nthJacobi"        "moments"        "monic?"
"monicCompleteDecompose" "monicDecomposeIfCan"  "monicDivide"  "monicLeftDivide"
"monicModulo"  "monicRightDivide"  "monicRightFactorIfCan"  "monom"   "monomRDE"
"monomRDEsys"  "monomial"  "monomial?"  "monomialIntPoly"    "monomialIntegrate"
"monomials"        "monotoneConvolution"               "monotoneCumulant2moment"
"monotoneCumulant2momentPoly"  "monotoneCumulants"   "more?"    "moreAlgebraic?"
"morphism"  "motzkinPathArray"  "move"  "movedPoints"  "mpsode"  "mr"  "mrv_cmp"
"mrv_limit"   "mrv_limit1"    "mrv_normalize"    "mrv_rewrite"    "mrv_rewrite0"
"mrv_set"  "mrv_sign"  "mul"    "mul_by_binomial"    "mul_by_scalar"    "mulmod"
"multMonom"  "multiEuclidean"  "multiEuclideanTree"  "multiIndex"   "multi_SPDE"
"multifunctionGraph"  "multinomial"  "multiple"  "multiple?"   "multiplicative?"
"multiplyCoefficients"    "multiplyExponents"      "multisect"        "multiset"
"multivariate"    "multivector"    "musserTrials"       "mvar"        "myDegree"
"naiveBeckermannLabahn"    "naiveBeckermannLabahn0"     "naiveBeckermannLabahn1"
"naiveBeckermannLabahnMultipoint"  "name"  "namedBranch"  "namedPoints"   "nand"
"nary?"  "ncDetSys"  "ncols"  "negative?"  "new"  "newFortranTempVar"  "newLine"
"newReduc"  "newSubProgram"    "newTypeLists"    "newline"    "newton"    "next"
"nextColeman"    "nextIrreduciblePoly"    "nextItem"    "nextLatticePermutation"
"nextNormalPoly"    "nextNormalPrimitivePoly"    "nextPartition"     "nextPrime"
"nextPrimitiveNormalPoly"  "nextPrimitivePoly"  "nextSublist"   "nextSubsetGray"
"next_sousResultant2"    "next_subResultant2"    "nil"    "nilFactor"     "nlde"
"noKaratsuba" "noLinearFactor?" "node"  "node?"  "nodeFromArrow"  "nodeFromNode"
"nodeOf?"  "nodeToArrow"  "nodeToNode"  "nodes"  "nonQsign"   "nonSingularModel"
"noncommutativeJordanAlgebra?"  "nor"    "norm"    "normDeriv2"    "normFactors"
"normInvertible?"  "normal"  "normal01"  "normal?"  "normalDenom"  "normalDeriv"
"normalElement"   "normalForm"    "normalise"    "normalisePoint"    "normalize"
"normalizeAtInfinity"  "normalizeIfCan"   "normalized?"    "normalizedAssociate"
"normalizedDivide"  "not"  "notelem"  "npcoef"  "nrows"   "nsqfree"    "nthCoef"
"nthExpon" "nthExponent"  "nthFactor"  "nthFlag"  "nthFractionalTerm"  "nthRoot"
"nthRootIfCan"  "nthr"  "null"  "null?"  "nullBoundary"  "nullSpace"   "nullary"
"nullary?"  "nullity"  "numDepVar"  "numFunEvals"  "numFunEvals3D"   "numIndVar"
"number?"    "numberOfChildren"    "numberOfComponents"     "numberOfComposites"
"numberOfComputedEntries"        "numberOfCycles"             "numberOfDivisors"
"numberOfFactors"        "numberOfFractionalTerms"                "numberOfHues"
"numberOfImproperPartitions"    "numberOfIrreduciblePoly"    "numberOfMonomials"
"numberOfNormalPoly"   "numberOfPrimitivePoly"    "numberOfVariables"    "numer"
"numerJP" "numerator" "numerators"  "numeric"  "numericIfCan"  "obj"  "objectOf"
"objects" "oblateSpheroidal" "octon" "odd?"  "oddInfiniteProduct"  "oddintegers"
"oddlambert" "ode" "ode1" "ode2" "omError"  "omega"  "omegapower"  "one"  "one?"
"oneDimensionalArray"  "op"  "opType"  "open"  "open?"  "operation"   "operator"
"operators"  "opeval"  "opposite?"  "option"  "option?"  "optional"  "optional?"
"options"  "optpair"  "or"  "orbit"   "orbits"    "ord"    "order"    "orderDim"
"ordinalAdd"    "ordinalMul"       "ordinalPower"        "orthogonalPolynomials"
"orthonormalBasis"  "outDegree"    "outerProduct"    "outlineRender"    "output"
"outputArgs"  "outputAsFortran"  "outputAsScript"  "outputAsTex"   "outputFixed"
"outputFloating"  "outputForm"  "outputGeneral"  "outputList"    "outputSpacing"
"outputVRML"  "over"  "overbar"  "overlabel"  "overlap"   "overset?"    "pToDmp"
"pToHdmp" "pack!" "pack_exps" "pack_exps0" "pack_modulus"  "packageCall"  "pade"
"padecf"  "padicFraction"  "padicallyExpand"  "pair?"  "palgLODE"    "palgLODE0"
"palgRDE"    "palgRDE0"    "palgextint"    "palgextint0"      "palgextintegrate"
"palginfieldint"    "palgint"    "palgint0"    "palgintegrate"      "palglimint"
"palglimint0"  "parabolic"  "parabolicCylindrical"  "paraboloidal"    "parallel"
"parametersOf"  "parametric?"  "paren"  "parent"  "parse"  "parseIL"  "parseIL2"
"parseILTerm" "parseLambda"  "parseSki"  "parseTerm"  "parseVar"  "parseVarTerm"
"parse_integer"  "partialDenominators"  "partialFraction"    "partialNumerators"
"partialQuotients"    "particularSolution"     "particularSolutionOverConstants"
"particularSolutionOverQ"  "partition"  "partitions"  "parts"   "pascalTriangle"
"pastel" "pattern" "patternMatch" "patternMatchTimes"  "patternVariable"  "pdct"
"perfectNthPower?"    "perfectNthRoot"     "perfectSqrt"        "perfectSquare?"
"perm_to_vec"        "permanent"        "permutation"         "permutationGroup"
"permutationRepresentation"   "permutations"    "perpendicular"    "perspective"
"phiCoord"  "physicalLength"  "physicalLength!"  "pi"  "pile"  "pivot"  "pivots"
"plenaryPower" "pleskenSplit" "plot" "plotPolar" "plus"  "plus!"  "plusInfinity"
"pmComplexintegrate"  "pmintegrate"  "po"    "point"    "point?"    "pointColor"
"pointColorDefault"  "pointColorPalette"  "pointData"  "pointList"  "pointLists"
"pointPlot" "pointSizeDefault" "points"  "poisson"  "poissonDistribution"  "pol"
"polCase" "polar" "polarCoordinates" "pole?"  "polyPart"  "polyRDE"  "polyRicDE"
"poly_int" "polygamma" "polygon"  "polygon?"  "polylog"  "polynomial"  "polyred"
"pomopo!"  "pop!"  "popFortranOutputStack"  "position"  "position!"  "positive?"
"positivePower"    "positiveRemainder"    "positiveSolve"        "possibleOrder"
"possiblyInfinite?" "possiblyNewVariety?"  "postfix"  "pow"  "powToUPS"  "power"
"power!"  "powerAssociative?"  "powerSum"  "powern"  "powers"  "powmod"   "pquo"
"pr2dmp"  "pre_gauss"  "pre_process"   "pre_smith"    "precision"    "predicate"
"predicates"  "prefix"  "prefix?"  "prefixRagits"   "prem"    "prepareDecompose"
"prepareSubResAlgo" "presub" "presuper" "pretendOfType"  "prevPrime"  "previous"
"primPartElseUnitCanonical"    "primPartElseUnitCanonical!"      "primaryDecomp"
"prime"  "prime?"  "primeFactor"  "primeFrobenius"  "primes"   "primextendedint"
"primextintfrac"     "primintegrate"        "primintfldpoly"        "primitive?"
"primitiveElement"   "primitiveMonomials"    "primitivePart"    "primitivePart!"
"primitiveRowEchelon"  "primlogint"  "primlogintfrac"    "prinb"    "principal?"
"principalIdeal"    "principalSubResultantSet"    "prindINFO"      "prinpolINFO"
"prinshINFO"  "print"  "printCode"  "printHeader"    "printInfo"    "printInfo!"
"printStatement"  "printStats!"    "printSys"    "printTypes"    "printingInfo?"
"probablyZeroDim?" "processTemplate"  "prod"  "product"  "project"  "projection"
"projectionSet"    "prolateSpheroidal"    "prologue"    "prolong"    "prolongMV"
"prolongSymbol"    "properties"    "property"    "proposition"    "pseudoDivide"
"pseudoQuotient"  "pseudoRem"  "pseudoRemainder"  "psolve"   "ptFunc"    "ptree"
"puiseux"   "pureLex"    "purelyAlgebraic?"    "purelyAlgebraicLeadingMonomial?"
"purelyTranscendental?"  "purge!"  "push!"  "pushFortranOutputStack"  "pushdown"
"pushdterm" "pushucoef" "pushuconst" "pushup" "putColorInfo"  "putGraph"  "qPot"
"qShiftAction"  "qShiftC"  "qcoerce"  "qconvert"  "qcumulant2nthmoment"   "qelt"
"qfactor"  "qinterval"  "qlog"   "qnew"    "qroot"    "qsetelt!"    "qsetfirst!"
"qsetrest!"  "qsqrt"  "quadratic"  "quadraticForm"  "quadraticNorm"    "quartic"
"quasiAlgebraicSet"  "quasiComponent"   "quasiMonic?"    "quasiMonicPolynomials"
"quasiRegular" "quasiRegular?" "quatern" "queue"  "quickSort"  "quo"  "quoByVar"
"quote" "quoted?"  "quotedOperators"  "quotient"  "quotientByP"  "r2m"  "rCoord"
"rabs"    "radPoly"    "radical"    "radicalEigenvalues"    "radicalEigenvector"
"radicalEigenvectors"        "radicalOfLeftTraceForm"             "radicalRoots"
"radicalSimplify"  "radicalSolve"    "radix"    "raisePolynomial"    "ramified?"
"ramifiedAtInfinity?" "ran"  "randnum"  "random"  "randomLC"  "randomR"  "range"
"rangePascalTriangle"  "ranges"  "rank"    "rarrow"    "ratDenom"    "ratDsolve"
"ratPoly"  "rational"  "rational?"  "rationalApproximation"   "rationalFunction"
"rationalIfCan"    "rationalPoint?"      "rationalPoints"        "rationalPower"
"rational_reconstruction"  "rationalize_ir"  "ratpart"  "ravel"  "rc"  "rdHack1"
"rdregime"  "read!"  "readIfCan!"  "readLine!"   "readLineIfCan!"    "readable?"
"real"    "real?"    "realEigenvalues"    "realEigenvectors"    "realElementary"
"realLiouvillian"    "realRoots"    "realSolve"       "realZeros"        "recip"
"reciprocalPolynomial"  "recolor"  "reconstruct"  "rectangularMatrix"    "recur"
"red" "redPo" "redPol" "redmat" "redpps" "reduce"  "reduceBasis"  "reduceBasis0"
"reduceBasisAtInfinity"    "reduceByQuasiMonic"    "reduceLODE"      "reduceMod"
"reduced?"  "reducedContinuedFraction"    "reducedDiscriminant"    "reducedForm"
"reducedQPowers" "reducedSystem" "reduction" "reductum" "redux"  "ref"  "refine"
"regime"    "region"    "regularRepresentation"    "reindex"    "relationsIdeal"
"relativeApprox" "relerror"  "rem"  "remainder"  "remainder!"  "remap_variables"
"remove"    "remove!"    "removeChild!"    "removeConstantTerm"    "removeCosSq"
"removeCoshSq"             "removeDuplicates"                "removeDuplicates!"
"removeIrreducibleRedundantFactors"                     "removeRedundantFactors"
"removeRedundantFactorsInContents"                "removeRedundantFactorsInPols"
"removeRepeats!"                       "removeRoughlyRedundantFactorsInContents"
"removeRoughlyRedundantFactorsInPol"       "removeRoughlyRedundantFactorsInPols"
"removeSinSq"  "removeSinhSq"   "removeSquaresIfCan"    "removeSuperfluousCases"
"removeSuperfluousQuasiComponents"  "removeZero"  "removeZeroes"   "removeZeros"
"remove_denoms"  "rename"  "rename!"  "reopen!"  "reorder"  "repSq"    "repack1"
"repack_polys"  "repeatUntilLoop"  "repeatedIndex"   "repeating"    "repeating?"
"replace" "replaceDiffs" "replaceKthElement"  "representationType"  "represents"
"reseed"  "reset"  "resetBadValues"  "resetNew"  "resetVariableOrder"  "reshape"
"resize"    "rest"       "result"        "resultant"        "resultantEuclidean"
"resultantEuclidean_naif"    "resultantReduit"        "resultantReduitEuclidean"
"resultantSet"  "resultant_naif"   "retract"    "retractIfCan"    "retractable?"
"returnType!"  "returnTypeOf"  "returns"  "reverse"   "reverse!"    "reverseLex"
"revert" "rewriteIdealWithHeadRemainder" 
"rewriteIdealWithQuasiMonicGenerators"               "rewriteIdealWithRemainder"
"rewriteSetByReducingWithParticularGenerators"  "rewriteSetWithReduction"  "rhs"
"ricDsolve"    "ridHack1"    "riemannZeta"    "right"        "rightAlternative?"
"rightCharacteristicPolynomial"        "rightDiscriminant"         "rightDivide"
"rightExactQuotient"        "rightExtendedGcd"            "rightFactorCandidate"
"rightFactorIfCan" "rightGcd"  "rightLcm"  "rightMinimalPolynomial"  "rightMult"
"rightNorm"    "rightOne"    "rightPower"     "rightQuotient"        "rightRank"
"rightRankPolynomial"        "rightRecip"           "rightRegularRepresentation"
"rightRemainder"    "rightScalarTimes!"    "rightTrace"       "rightTraceMatrix"
"rightTrim"  "rightUnit"  "rightUnits"  "rightZero"    "rischDE"    "rischDEsys"
"rischNormalize" "risch_de_ext"  "rk4"  "rk4a"  "rk4f"  "rk4qc"  "rmap"  "roman"
"romberg"  "rombergo"  "root"  "root?"  "rootBound"  "rootFactor"  "rootKerSimp"
"rootNormalize"  "rootOf"   "rootOfIrreduciblePoly"    "rootPoly"    "rootPower"
"rootProduct" "rootRadius" "rootSimp" "rootSplit" "rootSum"  "rootsOf"  "rotate"
"rotate!"  "rotatex"   "rotatey"    "rotatez"    "roughBase?"    "roughBasicSet"
"roughEqualIdeals?"     "roughSubIdeal?"        "roughUnitIdeal?"        "round"
"routeArrowWeight" "routeArrows" "routeNodeWeight" "routeNodes"  "row"  "rowEch"
"rowEchLocal"    "rowEchelon"    "rowEchelonLocal"    "rowMatrix"     "rowSlice"
"row_operation_base"  "row_operation_modular"  "rows"  "rquo"  "rroot"  "rspace"
"rst"  "rubiksGroup"  "rule"  "rules"  "ruleset"  "rur"  "sPol"    "safeCeiling"
"safeFloor"  "safety"  "safetyMargin"    "sample"    "samplePoint"    "satisfy?"
"saturate"  "save"  "say"  "sayLength"  "scalarMatrix"  "scalarTypeOf"   "scale"
"scaleRoots"    "scan"    "scanOneDimSubspaces"    "schema"        "schwerpunkt"
"screenCoordX" "screenCoordY" "screenCoordZ"  "screenCoords"  "screenResolution"
"screenResolution3D" "script"  "scripted?"  "scripts"  "se2rfi"  "search"  "sec"
"sec2cos" "secIfCan" "sech" "sech2cosh" "sechIfCan"  "second"  "seed"  "segment"
"select"    "select!"        "selectAndPolynomials"        "selectOrPolynomials"
"selectPolynomials"                            "semiDegreeSubResultantEuclidean"
"semiDiscriminantEuclidean"                    "semiIndiceSubResultantEuclidean"
"semiLastSubResultantEuclidean"                        "semiResultantEuclidean1"
"semiResultantEuclidean2"                          "semiResultantEuclidean_naif"
"semiResultantReduitEuclidean"                   "semiSubResultantGcdEuclidean1"
"semiSubResultantGcdEuclidean2"      "semicolonSeparate"        "sendGraphImage"
"separant"    "separate"    "separateDegrees"    "separateFactors"    "sequence"
"sequences"  "series"  "seriesSolve"  "seriesToOutputForm"  "set"  "setAdaptive"
"setAdaptive3D"  "setClipValue"   "setClosed"    "setColumn!"    "setCondition!"
"setDifference"  "setEmpty!"  "setEpilogue!"   "setErrorBound"    "setFieldInfo"
"setFormula!"  "setGcdMode"  "setImagSteps"  "setIntersection"   "setLabelValue"
"setLegalFortranSourceExtensions"        "setMaxPoints"         "setMaxPoints3D"
"setMinPoints" "setMinPoints3D" "setMode" "setNotation"  "setOfMinN"  "setOrder"
"setOutMode"    "setPoly"    "setPosition"    "setPredicates"     "setPrologue!"
"setProperties"    "setProperty"    "setRealSteps"    "setRedMode"     "setRow!"
"setScreenResolution"        "setScreenResolution3D"               "setSimpMode"
"setSimplifyDenomsFlag"  "setStatus"  "setStatus!"  "setTex!"  "setTopPredicate"
"setTransform!"  "setUnion"  "setValue!"    "setVariableOrder"    "setchildren!"
"setelt!"  "setfirst!"    "setlast!"    "setleaves!"    "setleft!"    "setnext!"
"setprevious!"  "setref"  "setrest!"  "setright!"  "setsubMatrix!"   "setvalue!"
"sh"    "shade"    "shallowCopy"    "shallowExpand"     "shanksDiscLogAlgorithm"
"shellSort"  "shift"  "shiftHP"  "shiftLeft"  "shiftRight"  "shiftRoots"  "show"
"showAll?" "showAllElements" "showArrayValues"  "showClipRegion"  "showElements"
"showFortranOutputStack"  "showRegion"  "showScalarValues"  "showTheSymbolTable"
"showTypeInOutput"  "shrinkable"  "shuffle"    "shufflein"    "sierpinskiDivide"
"sign"    "signAround"    "simpMod"    "simpOne"    "simpleCells"     "simplify"
"simplifyCoeffs"  "simplifyExp"    "simplifyLog"    "simplifyPower"    "simpson"
"simpsono" "sin" "sin2csc" "sin?" "sinIfCan" "sincos"  "singRicDE"  "singleFace"
"singleFactorBound"  "singular?"  "singularAtInfinity?"    "sinh"    "sinh2csch"
"sinhIfCan"  "sinhcosh"   "sipnt"    "sivec"    "size"    "size?"    "sizeLess?"
"sizeMultiplication" "sizePascalTriangle" "skewSFunction" "ski"  "slash"  "slex"
"smaller?" "smesh" "smith" "sn2"  "sncndn"  "solid"  "solid?"  "solve"  "solve1"
"solveFor"    "solveInField"     "solveLinear"        "solveLinearOverConstants"
"solveLinearPolynomialEquation"       "solveLinearPolynomialEquationByFractions"
"solveLinearPolynomialEquationByRecursion"  "solveLinearlyOverQ"  "solveRetract"
"solve_u"  "solveid"   "someBasis"    "sort"    "sort!"    "sortLD"    "sorted?"
"sortedPurge!"    "space"      "spanningForestArrow"        "spanningForestNode"
"spanningTreeArrow" "spanningTreeNode" "specialTrigs"  "specialise"  "spherical"
"split"    "split!"    "splitConstant"    "splitDenominator"      "splitNodeOf!"
"splitSquarefree" "spnt" "sqfrFactor"  "sqfree"  "sqrt"  "square?"  "squareFree"
"squareFreeBasis"        "squareFreeFactors"           "squareFreeLexTriangular"
"squareFreePart"    "squareFreePolynomial"    "squareFreePrim"    "squareMatrix"
"squareTop" "stFunc1" "stFunc2" "stFuncN" "stack" 
"standardBasisOfCyclicSubmodule" "startPolynomial"  "startStats!"  "startTable!"
"startTableGcd!" "startTableInvSet!" "statement2Fortran"  "statistics"  "status"
"stirling"  "stirling1"  "stirling2"  "stop"  "stopMusserTrials"    "stopTable!"
"stopTableGcd!"        "stopTableInvSet!"        "stoseIntegralLastSubResultant"
"stoseInternalLastSubResultant"    "stoseInvertible?"     "stoseInvertible?_reg"
"stoseInvertible?_sqfreg"    "stoseInvertibleSet"       "stoseInvertibleSet_reg"
"stoseInvertibleSet_sqfreg"  "stoseLastSubResultant"    "stosePrepareSubResAlgo"
"stoseSquareFreePart"  "stransform"  "stranslate"  "stream"  "string"  "string?"
"stripCommentsAndBlanks"        "strongGenerators"              "stronglyReduce"
"stronglyReduced?"    "structuralConstants"    "struveH"    "struveL"    "stube"
"sturmSequence"  "sturmVariationsOf"  "style"  "sub"   "subCase?"    "subMatrix"
"subNode?" "subNodeOf?"  "subPolSet?"  "subQuasiComponent?"  "subResultantChain"
"subResultantGcd"  "subResultantGcdEuclidean"   "subResultantsChain"    "subSet"
"subTriSet?"  "subdiagramSvg"  "subdivide"    "submod"    "subresultantSequence"
"subresultantVector"  "subscript"  "subset?"  "subspace"  "subspace?"    "subst"
"substHP" "substitute" "substring?" "subtractIfCan" "suchThat"  "suffix?"  "sum"
"sumBasis"  "sumOfDivisors"  "sumOfKthPowerDivisors"  "sumSquares"   "summation"
"sunion"  "sup"  "supDimElseRittWu?"    "supRittWu?"    "super"    "superscript"
"supersub"  "support"  "surface"   "svec"    "swap"    "swap!"    "swapColumns!"
"swapRows!" "sylvesterMatrix" "sylvesterSequence" "symFunc"  "symbol"  "symbol?"
"symbolIfCan" "symbolTable" "symbolTableOf"  "symmetric?"  "symmetricDifference"
"symmetricGroup"  "symmetricPower"    "symmetricProduct"    "symmetricRemainder"
"symmetricSquare"  "symmetricTensors"  "systemCommand"  "t"  "tRange"  "tValues"
"tab" "tab1" "table"  "tableForDiscreteLogarithm"  "tablePow"  "tableau"  "tail"
"tan" "tan2cot" "tan2trig" "tanAn" "tanIfCan"  "tanNa"  "tanQ"  "tanSum"  "tanh"
"tanh2coth"  "tanh2trigh"  "tanhIfCan"  "tanintegrate"  "taylor"   "taylorIfCan"
"taylorQuoByVar"  "taylorRep"  "taylor_via_deriv"  "taylor_via_lode"    "tensor"
"tensorMap" "tensorProduct" "terminal"  "terms"  "test"  "testAbsolutePrecision"
"testComplexEquals"    "testComplexEqualsAux"      "testDim"        "testEquals"
"testEqualsAux"  "testEqualsAuxCmp"  "testLibraryError"    "testLibraryErrorAux"
"testModulus"    "testNotEquals"      "testNotEqualsAux"        "testRealEquals"
"testRealEqualsAux"    "testRelativePrecision"    "testTrue"       "testTrueAux"
"testcase" "testcaseNoClear" "testsuite" "testsuiteNoClear"  "tex"  "thetaCoord"
"third"  "times"  "times!"  "title"  "toCayleyGraph"  "toObj"    "toPermutation"
"toPoint"  "toSVG"  "toScale"  "toString"  "toStringConven"  "toStringUnwrapped"
"toTable"  "toVector"  "toX3D"   "to_mod_pa"    "top"    "topFortranOutputStack"
"topPredicate"   "toroidal"    "torsion?"    "torsionIfCan"    "toseInvertible?"
"toseInvertibleSet"  "toseLastSubResultant"  "toseSquareFreePart"  "totalDegree"
"totalDegreeSorted"    "totalDifferential"     "totalGroebner"        "totalLex"
"totalfract"  "totolex"    "tower"    "trace"    "trace2PowMod"    "traceMatrix"
"tracePowMod"  "trailingCoefficient"    "transcendenceDegree"    "transcendent?"
"transcendentalDecompose"  "transform"  "translate"  "transpose"   "trapezoidal"
"trapezoidalo"    "traverse"    "tree"        "triangSolve"        "triangular?"
"triangularSystems"    "triangulate"    "trigs"    "trigs2explogs"        "trim"
"trivialIdeal?"  "true"  "trueEqual"  "trunc"  "truncate"    "truncated_mul_add"
"truncated_multiplication"                          "tryFunctionalDecomposition"
"tryFunctionalDecomposition?"  "tryTwoFactor"  "tube"  "tubePlot"   "tubePoints"
"tubePointsDefault"  "tubeRadius"  "tubeRadiusDefault"    "twist"    "twoFactor"
"type"    "typeList"    "typeLists"    "ucodeToString"    "uentries"    "unary?"
"unaryFunction"  "unbind"  "uncouplingMatrices"  "undirectedGraph"    "unexpand"
"uniform"  "uniform01"  "union"  "unit"  "unit?"  "unitCanonical"   "unitNormal"
"unitNormalize"   "unitVector"    "units"    "unitsColorDefault"    "univariate"
"univariate?"        "univariatePolynomial"              "univariatePolynomials"
"univariatePolynomialsGcds"    "univariateSolve"    "univcase"        "universe"
"unmakeSUP"    "unpack_poly"    "unparse"    "unprotectedRemoveRedundantFactors"
"unrankImproperPartitions0"  "unrankImproperPartitions1"    "unravel"    "untab"
"unvectorise"  "upDateBranches"    "updatD"    "updatF"    "update"    "update!"
"updateStatus!" "upperCase" "upperCase!"  "upperCase?"  "useEisensteinCriterion"
"useEisensteinCriterion?"        "useNagFunctions"        "useSingleFactorBound"
"useSingleFactorBound?"    "userOrdered?"    "usingTable?"    "validExponential"
"value"    "values"    "var"    "var1Steps"    "var1StepsDefault"    "var2Steps"
"var2StepsDefault"    "varList"    "variable"    "variable?"      "variableName"
"variableOf"   "variables"    "variablesOf"    "variationOfParameters"    "vark"
"varselect"    "vconcat"    "vector"    "vector_add_mul"    "vector_combination"
"vectorise"  "vertConcat"   "vertSplit"    "viewDefaults"    "viewDeltaXDefault"
"viewDeltaYDefault"    "viewPhiDefault"    "viewPosDefault"    "viewSizeDefault"
"viewThetaDefault"  "viewWriteAvailable"  "viewWriteDefault"   "viewZoomDefault"
"viewpoint"  "viewport2D"  "viewport3D"    "virtualDegree"    "void"    "vspace"
"weakBiRank"       "weberE"        "weierstrass"        "weierstrassHalfPeriods"
"weierstrassInvariants"  "weierstrassP"   "weierstrassP0"    "weierstrassPPrime"
"weierstrassPPrime0"  "weierstrassSigma"  "weierstrassSigma0"  "weierstrassZeta"
"weierstrassZeta0"    "weight"        "weighted"        "weightedDistanceMatrix"
"weightedGraph" "weights" "whatInfinity" "whileLoop"  "whittakerM"  "whittakerW"
"wholePart"    "wholeRadix"    "wholeRagits"    "width"     "wignerDistribution"
"withPredicates"        "wordInGenerators"              "wordInStrongGenerators"
"wordsForStrongGenerators"    "wreath"    "writable?"    "write"        "write!"
"writeCategory"    "writeLine!"    "writeObj"    "writePackage"       "writeSvg"
"writeSvgQuantised"  "writeVRML"   "writeX3d"    "writeXml"    "wronskianMatrix"
"wrregime"    "xCoord"      "xRange"        "xform"        "xftestComplexEquals"
"xftestComplexEqualsAux" "xftestEquals"  "xftestEqualsAux"  "xftestLibraryError"
"xftestLibraryErrorAux"        "xftestNotEquals"            "xftestNotEqualsAux"
"xftestRealEquals"    "xftestRealEqualsAux"    "xftestTrue"      "xftestTrueAux"
"xmlAttribute"  "xmlElement"  "xn"  "xor"  "yCoord"   "yCoordinates"    "yRange"
"yellow"  "youngGroup"  "zCoord"  "zRange"  "zag"  "zero"  "zero?"    "zeroDim?"
"zeroDimPrimary?"  "zeroDimPrime?"  "zeroDimensional?"  "zeroMatrix"    "zeroOf"
"zeroSetSplit"     "zeroSetSplitIntoTriangularSystems"        "zeroSquareMatrix"
"zeroVector" "zerosOf" "zeta" "zoom"
"%e" "%i" "%infinity" "%minusInfinity" "%pi" "%plusInfinity"  
"OneDimensionalArrayAggregate"        "AbelianGroup"          "AbelianSemiGroup"
"AlgebraicallyClosedFunctionSpace"    "PlaneAlgebraicCurvePlot"        "Algebra"
"AlgebraGivenByStructuralConstants"    "AssociationList"       "AlgebraicNumber"
"AntiSymm"        "TwoDimensionalArrayCategory"            "TwoDimensionalArray"
"ArcTrigonometricFunctionCategory"    "Automorphism"        "BalancedBinaryTree"
"BinaryExpansion"    "Bits"       "BasicOperator"        "BalancedPAdicRational"
"BinarySearchTree"    "BinaryTreeCategory"    "BinaryTree"     "CartesianTensor"
"ComplexDoubleFloatMatrix"  "Cell"  "Collection"    "Color"    "ComplexCategory"
"SubSpaceComponentProperty"     "Database"        "Dequeue"        "DoubleFloat"
"DoubleFloatVector"     "DenavitHartenbergMatrix"        "DifferentialExtension"
"DictionaryOperations"             "DirectProduct"                "Distribution"
"DistributedJetBundlePolynomial" "DataList" 
"DistributedMultivariatePolynomial"                  "DirectProductMatrixModule"
"DirectProductModule"       "DifferentialPolynomialCategory"        "DrawOption"
"DifferentialSparseMultivariatePolynomial"        "DifferentialVariableCategory"
"ExtAlgBasis"              "ElementaryFunctionsGeneralizedUnivariatePowerSeries"
"ElementaryFunctionsUnivariateLaurentSeries" 
"ElementaryFunctionsUnivariatePuiseuxSeries"         "ExtensibleLinearAggregate"
"EltableAggregate"    "EntireRing"    "EqTable"    "EuclideanDomain"      "Exit"
"Expression"    "ExponentialOfUnivariatePuiseuxSeries"        "FreeAbelianGroup"
"FiniteAbelianMonoidRing"    "FiniteAlgebraicExtensionField"       "FortranCode"
"FiniteDivisor"  "FullyEvalableOver"   "FiniteField"    "FiniteFieldCyclicGroup"
"FiniteFieldCyclicGroupExtensionByPolynomial" 
"FiniteFieldCyclicGroupExtension"                          "FiniteFieldCategory"
"FiniteFieldNormalBasis"           "FiniteFieldNormalBasisExtensionByPolynomial"
"FiniteFieldNormalBasisExtension"             "FiniteFieldExtensionByPolynomial"
"FiniteFieldExtension"    "FreeGroup"    "FiniteGraph"     "Field"        "File"
"FiniteRankNonAssociativeAlgebra"        "Finite"            "FiniteRankAlgebra"
"FiniteLinearAggregate"        "FullyLinearlyExplicitRingOver"           "Float"
"FreeModuleCategory"    "FileName"     "FreeNilpotentLie"        "FortranFormat"
"FullPartialFractionExpansion"        "FloatingPointSystem"           "Fraction"
"FullyRetractableTo"    "FramedModule"    "FunctionSpace"        "FourierSeries"
"FortranType"        "FunctionCalled"             "GenericNonAssociativeAlgebra"
"GeneralDistributedMultivariatePolynomial"    "GeneralizedUnivariatePowerSeries"
"GeneralModulePolynomial"    "GuessOptionFunctions0"      "GeneralPolynomialSet"
"GraphImage"  "Group"  "GeneralSparseTable"  "Pi"   "HashTable"    "GuessOption"
"MaybeSkewPolynomialCategory"        "GradedAlgebra"              "GradedModule"
"GeneralUnivariatePowerSeries"        "GeneralTriangularSet"         "HashState"
"HomogeneousDistributedMultivariatePolynomial"        "HomogeneousDirectProduct"
"HyperellipticFiniteDivisor" "HomogeneousAggregate" 
"HyperbolicFunctionCategory"    "IndexedOneDimensionalArray"       "IndexedBits"
"PolynomialIdeal"          "InnerEvalable"                "IndexedFlexibleArray"
"InnerIndexedTwoDimensionalArray"        "IndexedJetBundle"             "ILogic"
"IndexedExponents"  "IntegerNumberSystem"    "InnerTable"    "InnerPAdicInteger"
"IntegrationResult"    "InnerSparseUnivariatePowerSeries"    "InnerTaylorSeries"
"IndexedVector"       "JetBundleBaseFunctionCategory"        "JetBundleCategory"
"JetBundleFunctionCategory"        "JetBundlePolynomial"             "JetBundle"
"JetDifferentialEquation" "JetLazyFunction"  "JetVectorField"  "KeyedDictionary"
"LocalAlgebra"  "Lambda"   "LieExponentials"    "AssociatedLieAlgebra"    "List"
"ListMonoidOps"        "Localize"           "LinearOrdinaryDifferentialOperator"
"LinearOrdinaryDifferentialOperator1"      "LinearOrdinaryDifferentialOperator2"
"LinearOrdinaryDifferentialOperatorCategory"      "Logic"        "LiePolynomial"
"LieSquareMatrix"  "LazyStreamAggregate"  "ModularAlgebraicGcdTools2"    "Magma"
"Matrix"  "MultifunctionGraph"  "MachineInteger"    "MathMLFormat"    "ModMonic"
"ModuleOperator" "Module"  "Monad"  "MonogenicAlgebra"  "MultivariatePolynomial"
"Multiset"     "MultivariateTaylorSeriesCategory"        "NonAssociativeAlgebra"
"NonAssociativeRng"  "NonAssociativeRing"  "Enumeration"  "ping"  "Record"  "on"
"NonNegativeInteger"        "None"             "NewSparseMultivariatePolynomial"
"NewSparseUnivariatePolynomial"        "OctonionCategory"             "Octonion"
"OrderedDirectProduct"                           "OrderlyDifferentialPolynomial"
"OrdinaryDifferentialRing"  "OrderedExpression"   "OpenMath"    "OpenMathDevice"
"OpenMathError"    "OppositeMonogenicLinearOperator"        "OnePointCompletion"
"OrderedCompletion"       "OrderedSet"        "UnivariateSkewPolynomialCategory"
"SparseUnivariateSkewPolynomial"    "UnivariateSkewPolynomial"      "OutputForm"
"OrdinaryWeightedPolynomials" "PAdicRational"  "Palette"  "ParametricSpaceCurve"
"PatternMatchListResult"      "Pattern"        "PoincareBirkhoffWittLyndonBasis"
"PartialDifferentialOperator"        "PendantTree"            "PermutationGroup"
"PolynomialFactorizationExplicit"    "PartialFraction"     "Plot"        "Point"
"PolynomialCategory"    "PolynomialRing"    "Product"      "PowerSeriesCategory"
"QuasiAlgebraicSet"  "QuotientFieldCategory"  "Quaternion"  "QuaternionCategory"
"RadicalCategory" "RadixExpansion" "RealClosedField"  "Reference"  "ResidueRing"
"RetractableFrom"    "RegularChain"     "RectangularMatrixCategory"        "Rng"
"RightOpenIntervalRootCharacterization"                           "RomanNumeral"
"RealRootCharacterizationCategory"                "RegularTriangularSetCategory"
"RewriteRule"    "Ruleset"    "SingletonAsOrderedSet"    "SBoundary"     "Scene"
"SceneNamedPoints"        "SCartesian"        "SequentialDifferentialPolynomial"
"SequentialDifferentialVariable"    "Segment"    "SparseEchelonMatrix"     "Set"
"SetCategory" "SExpression" "SimpleFortranProgram" 
"SplitHomogeneousDirectProduct" "SingleInteger" 
"SparseMultivariateSkewPolynomial"                        "SquareMatrixCategory"
"SparseMultivariatePolynomialExpressions"       "SparseMultivariateTaylorSeries"
"SmallOrdinal"        "ThreeSpace"        "SplittingTree"         "SquareMatrix"
"SortedExponentVector"  "SplittingNode"    "SPointCategory"    "StringAggregate"
"SquareFreeRegularTriangularSet" "Stack"  "SparseTable"  "Stream"  "StringTable"
"SuchThat"    "StreamAggregate"    "STransform"       "String"        "SubSpace"
"SparseUnivariateLaurentSeries"                     "SparseUnivariatePolynomial"
"SparseUnivariatePuiseuxSeries"    "SparseUnivariateTaylorSeries"       "Symbol"
"TheSymbolTable"  "Table"  "TableAggregate"  "TensorPowerCategory"   "TexFormat"
"TexmacsFormat"  "Switch"    "SymmetricPolynomial"    "SymbolTable"    "Tableau"
"TensorProduct"  "TensorPower"    "TextFile"    "TranscendentalFunctionCategory"
"Tree"  "TrigonometricFunctionCategory"  "TaylorSeries"  "TaylorSeriesExpansion"
"TaylorSeriesExpansionGeneralized"                "TaylorSeriesExpansionLaurent"
"TaylorSeriesExpansionPuiseux"    "TaylorSeriesExpansionTaylor"       "TubePlot"
"Typed"  "U16Vector"    "U32Vector"    "U8Vector"    "UniqueFactorizationDomain"
"UnivariateLaurentSeries"    "TriangularSetCategory"    "Tuple"      "U16Matrix"
"U32Matrix"    "U8Matrix"    "UndirectedGraph"     "UnivariateFormalPowerSeries"
"UnivariateLaurentSeriesConstructorCategory" 
"UnivariateLaurentSeriesConstructor"        "UniversalSegment"         "Untyped"
"UnivariatePolynomial"                            "UnivariatePolynomialCategory"
"UnivariatePowerSeriesCategory"                        "UnivariatePuiseuxSeries"
"UnivariatePuiseuxSeriesConstructorCategory" 
"UnivariatePuiseuxSeriesConstructor" 
"UnivariatePuiseuxSeriesWithExponentialSingularity"    "UnaryRecursiveAggregate"
"UnivariateTaylorSeries"      "UnivariateTaylorSeriesCategory"        "Variable"
"VectorIntegerReconstructor"        "Vector"          "ThreeDimensionalViewport"
"VectorSpaceBasis"  "WeightedGraph"  "WuWenTsunTriangularSet"   "ExtensionField"
"XmlAttribute"    "XPBWPolynomial"    "XPolynomialRing"    "IntegerMod"       ""
"AlgebraicFunction"        "AlgebraicManipulations"             "AlgebraPackage"
"ApplyUnivariateSkewPolynomial"  "ApplyRules"    "OneDimensionalArrayFunctions2"
"TwoDimensionalArrayFunctions"                           "BalancedFactorisation"
"BasicOperatorFunctions1" "BrillhartTests" 
"CylindricalAlgebraicDecompositionPackage" 
"CylindricalAlgebraicDecompositionUtilities"         "CartesianTensorFunctions2"
"CommonDenominator"    "CharacteristicPolynomialPackage"      "ChangeOfVariable"
"ComplexIntegerSolveLinearPolynomialEquation"                  "CartanKuranishi"
"ConstantLinearDependence"  "TwoDimensionalPlotClipping"    "ComplexRootPackage"
"CombinatorialFunction"    "IntegerCombinatoricFunctions"      "CommonOperators"
"CommuteUnivariatePolynomialCategory"    "compCode"       "ComplexFactorization"
"ComplexFunctions2"    "ComplexPattern"    "compUtil"        "CoordinateSystems"
"CharacteristicPolynomialInMonogenicalAlgebra"             "ComplexPatternMatch"
"CRApackage"        "ComplexRootFindingPackage"              "CyclicStreamTools"
"ComplexTrigonometricManipulations"                  "CoerceVectorMatrixPackage"
"CycleIndicators"    "CyclotomicPolynomialPackage"      "DoubleResultantPackage"
"DistinctDegreeFactorize"                "ElementaryFunctionDefiniteIntegration"
"RationalFunctionDefiniteIntegration"                   "DegreeReductionPackage"
"DefiniteIntegrationTools"                         "DoubleFloatSpecialFunctions"
"DoubleFloatSpecialFunctions2"                      "DiophantineSolutionPackage"
"DirectProductFunctions2"        "DisplayPackage"          "DistributionPackage"
"DistributionPolynomialPackage"                         "DistributionFunctions2"
"DiscreteLogarithmPackage" "TopLevelDrawFunctions" 
"TopLevelDrawFunctionsForCompiledFunctions" 
"TopLevelDrawFunctionsForAlgebraicCurves"    "DrawComplex"     "DrawNumericHack"
"TopLevelDrawFunctionsForPoints"  "DrawOptionFunctions0"  "DrawOptionFunctions1"
"DistributionContinuedFractionPackage"                      "ElementaryFunction"
"ElementaryFunctionStructurePackage"   "EllipticFunctionsUnivariateTaylorSeries"
"ExpressionLinearSolve  ELIPIDF"  "DoubleFloatEllipticIntegrals"  "EigenPackage"
"EquationFunctions2"        "ErrorFunctions"         "ExpressionSpaceFunctions1"
"ExpressionSpaceFunctions2"        "EvaluateCycleIndicators"          "Export3D"
"ExpressionFunctions2"                       "ExpressionToUnivariatePowerSeries"
"ExpressionSpaceODESolver"        "ExpressionSolve"         "ExpressionTubePlot"
"FactoredFunctions"  "FactoringUtilities"    "FiniteAbelianMonoidRingFunctions2"
"FortranCodePackage1"        "FortranCodeTools"        "FiniteDivisorFunctions2"
"FloatEllipticFunctions"                       "FunctionFieldCategoryFunctions2"
"FiniteFieldFunctions" "FractionFreeFastGaussian" 
"FractionFreeFastGaussianFractions"                   "FiniteFieldHomomorphisms"
"FunctionFieldIntegralBasis"                      "FiniteFieldPolynomialPackage"
"FiniteFieldPolynomialPackage2"       "FiniteFieldSolveLinearPolynomialEquation"
"FGLMIfCanPackage"                             "FiniteLinearAggregateFunctions2"
"FiniteLinearAggregateSort"                           "FloatLiouvilianFunctions"
"FloatingComplexPackage"     "FloatingRealPackage"        "FreeModuleFunctions2"
"FortranOutputStackPackage"      "FindOrderFinite"        "ScriptFormulaFormat1"
"FortranPackage"        "FactoredFunctions2"                "FractionFunctions2"
"FractionalIdealFunctions2"              "FramedNonAssociativeAlgebraFunctions2"
"FactoredFunctionUtilities"                            "FunctionSpaceFunctions2"
"FunctionSpaceToExponentialExpansion"     "FunctionSpaceToUnivariatePowerSeries"
"FunctionSpaceToUnivariatePowerSeries2"           "FiniteSetAggregateFunctions2"
"FunctionSpaceComplexIntegration"                        "FloatSpecialFunctions"
"FunctionSpaceIntegration"                           "FunctionalSpecialFunction"
"FunctionSpacePrimitiveElement"                            "FunctionSpaceReduce"
"FunctionSpaceRationalRoots"           "FunctionSpaceUnivariatePolynomialFactor"
"GaloisGroupFactorizer"                      "GaloisGroupFactorizationUtilities"
"GaloisGroupPolynomialUtilities"                          "GaloisGroupUtilities"
"GaussianFactorizationPackage" "GroebnerPackage" 
"EuclideanGroebnerBasisPackage"                   "GroebnerFactorizationPackage"
"GroebnerInternalPackage"       "GcdBasis"        "GnuDraw"        "GenExEuclid"
"GeneralizedMultivariateFactorize"                 "GeneralPolynomialGcdPackage"
"GenUFactorize"    "GenerateUnivariatePowerSeries"        "GeneralHenselPackage"
"GrayCode" "GroebnerSolve" "GuessAlgebraicNumber"  "GuessFinite"  "GuessInteger"
"GuessPolynomialFunctions" "HankelPackage" "HeuGcd" 
"ChineseRemainderToolsForIntegralBases"                     "IntegralBasisTools"
"InnerCommonDenominator"                     "InnerMatrixLinearAlgebraFunctions"
"InnerMatrixQuotientFieldFunctions"                    "InnerModularHermitePade"
"InnerNormalBasisFieldFunctions"        "IncrementingMaps"            "Infinity"
"InfiniteProductCharacteristicZero"              "InnerNumericFloatSolvePackage"
"InnerModularGcd"        "InfiniteProductFiniteField"            "InnerPolySign"
"AlgebraicIntegrate"   "DenominatorIntegration"    "IntegerFactorizationPackage"
"IntegerNumberTheoryFunctions"                "TranscendentalHermiteIntegration"
"PureAlgebraicIntegration"  "RationalIntegration"  "RationalFunctionIntegration"
"IntegerSolveLinearPolynomialEquation"                        "IntegrationTools"
"InverseLaplaceTransform"    "IntegrationResultFunctions2"        "IntegerRoots"
"IntegrationResultRFToFunction"                            "IrrRepSymNatPackage"
"InternalRationalUnivariateRepresentationPackage"       "IntegerSmithNormalForm"
"InfiniteTupleFunctions2"                      "InnerTrigonometricManipulations"
"JetCoordinateTransformation"       "KernelFunctions2"        "LaplaceTransform"
"LeadingCoefDetermination"    "LiouvillianFunction"    "PowerSeriesLimitPackage"
"LinearDependence"  "ListToMap"  "ElementaryFunctionLODESolver"   "InnerPolySum"
"InfiniteTupleFunctions3"  "JetGroebner"  "Kovacic"    "LazardSetSolvingPackage"
"LexTriangularPackage"    "LinGroebnerPackage"    "RationalFunctionLimitPackage"
"ListFunctions2" "ListFunctions3" 
"LinearOrdinaryDifferentialOperatorFactorizer" 
"LinearOrdinaryDifferentialOperatorsOps"   "LinearPolynomialEquationByFractions"
"LinearSystemMatrixPackage"                         "LinearSystemMatrixPackage1"
"LinearSystemPolynomialPackage"    "LUDecomposition"       "ModularAlgebraicGcd"
"MatrixManipulation" "MappingPackageInternalHacks1" 
"MappingPackageInternalHacks2"                    "MappingPackageInternalHacks3"
"MappingPackage1"             "MappingPackage2"                "MappingPackage3"
"MatrixCategoryFunctions2"                        "MatrixLinearAlgebraFunctions"
"StorageEfficientMatrixOperations"              "MultiVariableCalculusFunctions"
"MatrixCommonDenominator"                      "ModularDistinctDegreeFactorizer"
"MeshCreationRoutinesForThreeDimensions"                   "MultFiniteFactorize"
"MakeBinaryCompiledFunction"    "MakeFunction"       "MakeUnaryCompiledFunction"
"MultipleMap"        "ModularHermitePadeSolver"         "MonomialExtensionTools"
"MPolyCatFunctions3"  "MPolyCatRationalFunctionFactorizer"  "MRationalFactorize"
"MrvLimitPackage"            "MergeThing"                "MultivariateFactorize"
"NaiveBeckermannLabahnModular"                        "NumericContinuedFraction"
"NonCommutativeOperatorDivision"    "NewtonInterpolation"     "NGroebnerPackage"
"NonLinearFirstOrderODESolver"  "NormInMonogenicAlgebra"    "NormRetractPackage"
"NumericRealEigenPackage"              "NewSparseUnivariatePolynomialFunctions2"
"NumberTheoreticPolynomialFunctions"        "Numeric"            "NumberFormats"
"NumericalOrdinaryDifferentialEquations"                   "NumericalQuadrature"
"NumericTubePlot"        "OctonionCategoryFunctions2"             "ConstantLODE"
"ElementaryFunctionODESolver"        "ODEIntegration"        "PureAlgebraicLODE"
"PrimitiveRatDE"    "PrimitiveRatRicDE"       "RationalLODE"        "ReduceLODE"
"RationalRicDE"     "SystemODESolver"        "ODETools"        "OutputFormTools"
"ExpressionToOpenMath"        "OpenMathPackage"          "OpenMathServerPackage"
"OnePointCompletionFunctions2"  "OperationsQuery"  "OrderedCompletionFunctions2"
"OrderingFunctions"                        "UnivariateSkewPolynomialCategoryOps"
"OrthogonalPolynomialFunctions"        "OutputPackage"        "PadeApproximants"
"PadeApproximantPackage" "PolynomialAN2Expression" 
"ParametricPlaneCurveFunctions2" "PathArrayPackage" 
"ParametricSpaceCurveFunctions2"                   "ParametricSurfaceFunctions2"
"PartitionsAndPermutations"    "PatternMatch"     "PatternMatchResultFunctions2"
"PatternFunctions1"        "PatternFunctions2"           "PolynomialComposition"
"PolynomialDecomposition"    "PartialDifferentialOperatorHelper"     "Permanent"
"PolynomialEvaluationUtilities"             "PolynomialFactorizationByRecursion"
"PolynomialFactorizationByRecursionUnivariate"             "PointsOfFiniteOrder"
"PointsOfFiniteOrderRational"                         "PointsOfFiniteOrderTools"
"PartialFractionPackage"    "PartialFractionUtilities"    "PolynomialGcdPackage"
"PermutationGroupExamples"           "PolyGroebner"                "PiCoercions"
"PolynomialInterpolation"                    "PolynomialInterpolationAlgorithms"
"ParallelIntegrationTools"    "ParametricLinearEquations"       "PlotFunctions1"
"PlotTools"        "PatternMatchAssertions"            "FunctionSpaceAssertions"
"PatternMatchPushDown" "PatternMatchFunctionSpace" 
"PatternMatchIntegerNumberSystem"                           "PatternMatchKernel"
"PatternMatchListAggregate"                     "PatternMatchPolynomialCategory"
"AttachPredicates" "FunctionSpaceAttachPredicates" 
"PatternMatchQuotientFieldCategory"  "PatternMatchSymbol"    "PatternMatchTools"
"PolynomialNumberTheoryFunctions"  "PolToPol"   "RealPolynomialUtilitiesPackage"
"PolynomialFunctions2"                        "PolynomialToUnivariatePolynomial"
"PolynomialCategoryQuotientFunctions"                "PolynomialCategoryLifting"
"PolynomialRoots" "U32VectorPolynomialOperations" 
"PrecomputedAssociatedEquations"     "PrimGCD"        "PrimitiveArrayFunctions2"
"PrimitiveElement"          "IntegerPrimesPackage"                "PrintPackage"
"PseudoRemainderSequence"                        "PolynomialSetUtilitiesPackage"
"PseudoLinearNormalForm"        "PolynomialSquareFree"         "PointFunctions2"
"PointPackage"      "PushVariables"        "PAdicWildFunctionFieldIntegralBasis"
"QuasiAlgebraicSet2"  "QuasiComponentPackage"  "QuotientFieldCategoryFunctions2"
"QuaternionCategoryFunctions2"    "RandomNumberSource"     "RationalRetractions"
"ElementaryRischDE"        "ElementaryRischDEX"          "TranscendentalRischDE"
"RandomDistributions"  "RealZeroPackage"  "RealSolvePackage"  "ReductionOfOrder"
"RepresentationPackage1"    "RepeatedDoubling"        "ResolveLatticeCompletion"
"RationalFunction"    "RationalFunctionFactor"      "RandomIntegerDistributions"
"RectangularMatrixCategoryFunctions2"           "RegularSetDecompositionPackage"
"RegularTriangularSetGcdPackage"       "RationalUnivariateRepresentationPackage"
"SimpleAlgebraicExtensionAlgFactor"               "SAERationalFunctionAlgFactor"
"SortedCache"        "ScanningUtilities"            "StructuralConstantsPackage"
"SegmentFunctions2"       "SegmentBindingFunctions2"        "SequenceFunctions2"
"SquareFreeQuasiComponentPackage"     "SquareFreeRegularTriangularSetGcdPackage"
"SymmetricGroupCombinatoricFunctions"                      "SturmHabichtPackage"
"ElementaryFunctionSign" "RationalFunctionSign" 
"SimplifyAlgebraicNumberConvertPackage"                        "SmithNormalForm"
"SparsePolynomialCoercionHelpers"                    "PolynomialSolveByFormulas"
"RadicalSolvePackage"      "TransSolvePackageService"        "TransSolvePackage"
"SortPackage"  "SpecialOutputPackage"    "SpecialFunctionUnivariateTaylorSeries"
"SquareFreeRegularSetDecompositionPackage"   "StreamExponentialSeriesOperations"
"StreamExponentialSeriesTranscendentalFunctions"         "StreamInfiniteProduct"
"StreamTensor"   "STransformPackage"    "StreamFunctions1"    "StreamFunctions2"
"StreamFunctions3" "StreamTaylorSeriesOperations" 
"StreamTranscendentalFunctions"    "StreamTranscendentalFunctionsNonCommutative"
"SubResultantPackage"        "FunctionSpaceSum"            "RationalFunctionSum"
"SparseUnivariatePolynomialFunctions2"                   "SupFractionFactorizer"
"SymmetricFunctions"      "TableauxBumpers"        "TabulatedComputationPackage"
"TensorPowerFunctions2"  "UnittestCount"    "TexFormat1"    "TopLevelThreeSpace"
"TriangularMatrixOperations"    "TubePlotTools"     "UserDefinedPartialOrdering"
"UnivariateFormalPowerSeriesFunctions"                 "UnitGaussianElimination"
"UnivariateLaurentSeriesFunctions2"                        "UnivariateFactorize"
"UniversalSegmentFunctions2"                    "UnivariatePolynomialFunctions2"
"UnivariatePolynomialCommonDenominator" 
"UnivariatePolynomialDecompositionPackage" 
"UnivariatePolynomialDivisionPackage" 
"UnivariatePolynomialMultiplicationPackage" 
"UnivariatePolynomialCategoryFunctions2"        "UnivariatePolynomialSquareFree"
"UnivariatePuiseuxSeriesFunctions2"           "UnivariateTaylorSeriesFunctions2"
"UnivariateTaylorSeriesODESolver"        "UTSodetools"             "TaylorSolve"
"VectorFunctions2"        "ViewportPackage"                "ViewDefaultsPackage"
"WeierstrassPreparation"                        "WildFunctionFieldIntegralBasis"
"XExponentialPackage"      "ExportXml"        "ParadoxicalCombinatorsForStreams"
"ZeroDimensionalSolvePackage"    "IntegerLinearDependence"       "AbelianMonoid"
"AlgebraicallyClosedField"        "Aggregate"           "AlgebraicFunctionField"
"AbelianMonoidRing"    "AnonymousFunction"    "Any"        "OneDimensionalArray"
"ArrayStack"    "BasicType"    "BagAggregate"      "BinaryFile"        "Boolean"
"BalancedPAdicInteger"        "BinaryRecursiveAggregate"          "BitAggregate"
"BinaryTournament"              "CardinalNumber"                "CharacterClass"
"ComplexDoubleFloatVector"    "Character"    "CliffordAlgebra"      "Commutator"
"Complex"    "ContinuedFraction"       "DecimalExpansion"        "DeRhamComplex"
"DoubleFloatMatrix"    "DirectedGraph"    "Dictionary"        "DifferentialRing"
"DirectProductCategory"            "DirichletRing"                "DivisionRing"
"ElementaryFunctionCategory"        "EuclideanModularRing"            "Equation"
"ExpressionSpace"    "Evalable"    "ExponentialExpansion"    "FreeAbelianMonoid"
"FlexibleArray" "FourierComponent"  "FiniteDivisorCategory"  "FortranExpression"
"FunctionFieldCategory"    "FreeModule"      "FreeMonoid"        "FunctionGraph"
"ScriptFormulaFormat" "FortranProgram"  "FieldOfPrimeCharacteristic"  "Factored"
"FramedAlgebra"        "FractionalIdeal"           "FramedNonAssociativeAlgebra"
"FiniteSetAggregate" "FortranScalarType"  "FortranTemplate"  "GcdDomain"  "Heap"
"HexadecimalExpansion"        "HTMLFormat"                "InnerAlgebraicNumber"
"IndexedTwoDimensionalArray"     "IndexCard"        "IndexedDirectProductObject"
"InnerFreeAbelianMonoid"  "InnerFiniteField"    "IndexedList"    "IndexedMatrix"
"InputForm"    "Integer"    "Interval"    "InnerPrimeField"      "IndexedString"
"InfiniteTuple"          "IndexedAggregate"                "JetBundleExpression"
"JetBundleLinearFunction"        "JetBundleSymAna"        "JetBundleXExpression"
"JetDifferential"    "AssociatedJordanAlgebra"    "KeyedAccessFile"     "Kernel"
"LeftAlgebra" "LaurentPolynomial" "Library"  "LieAlgebra"  "ListMultiDictionary"
"LinearAggregate" "Loop" "ListAggregate"  "LyndonWord"  "ThreeDimensionalMatrix"
"ModularAlgebraicGcdTools3"  "MatrixCategory"  "MachineComplex"   "MachineFloat"
"MakeCachableSet"    "ModularField"        "ModuleMonomial"        "ModularRing"
"MoebiusTransform"        "MonadWithUnit"        "Monoid"           "MonoidRing"
"OrderlyDifferentialVariable"    "OrderedFreeMonoid"        "OpenMathConnection"
"OpenMathEncoding"  "OpenMathErrorKind"  "Operator"  "OrderedRing"  "OrdSetInts"
"OrderedVariableList"        "PAdicInteger"           "PAdicRationalConstructor"
"ParametricPlaneCurve"        "ParametricSurface"           "PatternMatchResult"
"PartialDifferentialRing"    "Permutation"    "PrimeField"     "PositiveInteger"
"Plot3D"    "Polynomial"    "PartialOrder"    "PrimitiveArray"       "Partition"
"PolynomialSetCategory"  "QueryEquation"  "QuadraticForm"    "GeneralQuaternion"
"Queue"    "RadicalFunctionField"      "RecursiveAggregate"        "RealClosure"
"RegularTriangularSet"  "Result"  "RetractableTo"  "Ring"    "RectangularMatrix"
"RealNumberSystem"        "RecursivePolynomialCategory"             "RuleCalled"
"SimpleAlgebraicExtension"  "SArgand"  "SimpleCell"   "SceneIFS"    "SConformal"
"SegmentBinding"    "Sequence"    "SetAggregate"        "SetOfMIntegersInOneToN"
"SExpressionOf"  "SemiGroup"  "SKICombinators"    "SparseMultivariatePolynomial"
"VectorModularReconstructor"  "VectorCategory"  "TwoDimensionalViewport"  "Void"
"VectorSpace"  "WeightedPolynomials"    "XDistributedPolynomial"    "XHashTable"
"XmlElement"      "XPolynomial"        "XRecursivePolynomial"        "AlgFactor"
"AlgebraicMultFact"   "AnyFunctions1"    "AssociatedEquations"    "BezoutMatrix"
"BoundIntegerRoots"    "GosperSummationMethod"    "GraphicsDefaults"     "Guess"
"GuessExpBin"            "GuessFiniteFunctions"                "GuessPolynomial"
"GuessPolynomialInteger"             "HallBasis"                "InnerAlgFactor"
"IntegralBasisPolynomialTools"                       "IdealDecompositionPackage"
"InnerNumericEigenPackage"        "InputFormFunctions1"          "InnerMultFact"
"InfiniteProductPrimeField"        "AlgebraicIntegration"          "IntegerBits"
"ElementaryIntegration"  "GenusZeroIntegration"    "AlgebraicHermiteIntegration"
"PatternMatchIntegration"    "IntegerRetractions"    "TranscendentalIntegration"
"InternalPrintPackage"                             "IntegrationResultToFunction"
"IrredPolyOverFiniteField"                        "ModularHermitianRowReduction"
"MakeFloatCompiledFunction"        "MakeRecord"            "MultivariateLifting"
"ModularHermitePade"         "MomentPackage"                "MPolyCatFunctions2"
"MPolyCatPolyFactorizer"      "MonoidRingFunctions2"        "MoreSystemCommands"
"MultiplicativeDependence" "MultivariateSquareFree" 
"NumericComplexEigenPackage"                          "NumberFieldIntegralBasis"
"NonLinearSolvePackage"   "NoneFunctions1"    "NormalizationPackage"    "NPCoef"
"RadixUtilities"    "RationalFactorize"    "RDEaux"    "ElementaryRischDESystem"
"ElementaryRischDEX2"      "TranscendentalRischDESystem"        "ReducedDivisor"
"RealZeroPackageQ"        "RecurrenceOperator"             "RadicalEigenPackage"
"RepresentationPackage2"        "RepeatedSquaring"         "RetractSolvePackage"
"RandomFloatDistributions"                          "RationalFunctionFactorizer"
"RationalInterpolation"        "SymmetryAnalysis"           "SystemSolvePackage"
"TangentExpansions"    "TemplateUtilities"       "UnittestAux"        "Unittest"
"ToolsForSign"    "TrigonometricManipulations"     "TranscendentalManipulations"
"TwoFactorize" "UserDefinedVariableOrdering"))



;;;;;;;;;;;;;
;;; START ;;;
;;;;;;;;;;;;;

(in-package #:cl-jupyter-user)
