(defvar str-format nil "")
(setq str-format "Require")
(defvar current-dir nil "")
(setq current-dir (file-name-directory (or load-file-name buffer-file-name)))
(defvar copy-dir nil "")
(setq copy-dir (concat current-dir "Syntax/"))
(defun get-line-content () ""
		(interactive)
		(print (delete "Export" (delete "Import" (delete "Require" (split-string (buffer-substring-no-properties (line-beginning-position) (- (line-end-position) 1))))))))
(defun coq-LocateLibrary2 (name) ""
		(proof-shell-wait)
		(proof-shell-ready-prover)
  (proof-shell-invisible-command
			(format (concat "Locate Library" " %s . ") (funcall 'identity name)) t))
(defun name-to-location (name)
		"Change library name string to its .vo file location."
		(coq-LocateLibrary2 name)
		(car (last (split-string (proof-shell-strip-output-markup proof-shell-last-output)))))
(defun vo-location-to-v-location (location)
		(substring location 0 -1))
(defun check-validity (location)
		(setq source_name (car (last (split-string location "/"))))
		(setq path-list (remove source_name (split-string location "/")))
		(not (or (string-equal source_name "initial.coq")
											(member ".local" path-list))))
(defvar queue ""
		nil)
(defvar history ""
		nil)
(defun copy-dependency (my-file-dir) ""
		(unless (member my-file-dir history) 
				(push my-file-dir history)
				(if (file-exists-p my-file-dir)	
								(let ((my-file-buffer (find-file-noselect my-file-dir)))
										(copy-file my-file-dir copy-dir t)
										(switch-to-buffer my-file-buffer)
										(setq case-fold-search nil)
										(if proof-shell-buffer (proof-shell-exit t))
										(evil-goto-first-line)
										(while (search-forward str-format nil t))
										(proof-goto-point)
																																								;		(proof-process-buffer)
										(evil-goto-first-line)
										(while (search-forward str-format nil t)
												(if (= (- (point) (line-beginning-position)) 7)
																(let ((deps (mapcar 'name-to-location (get-line-content)))
																						(dep)
																						(depv))
																		(setq dep (car deps))
																		(print deps)
																		(print dep)
																		(setq queue (append (mapcar 'vo-location-to-v-location (cdr deps)) queue))
																		(print queue)

																		(setq depv (vo-location-to-v-location dep))
																		(if (check-validity dep) ;;why not just v_location? location such as such as initial.coq
																						(if (file-exists-p depv)
																										(progn
																												(print (concat "Copying from " depv " to " copy-dir))
																												;; (setq queue (cons v_location queue))
																												(setq queue (append (list depv) queue))
																												(copy-file depv copy-dir t))
																								(progn
																										(print "No .v file exists, copying .vo file instead.")
																										(copy-file dep copy-dir t)))
																				)
																		)
														)
												)
										(proof-shell-exit t)
										(kill-buffer)
										)
						)
				nil
				)
		)


(setq history nil)
(setq queue '("Vellvm/syntax.v"))
;;(setq queue '("/home/youngju.song/coq_related/vellvm-legacy-snu-sf/lib/metalib-20090714/CoqUniquenessTac.v"))
;;(setq queue '("/home/youngju.song/coq_related/vellvm-legacy-snu-sf/lib/compcert-1.9/Axioms.v"))

(condition-case nil
				(make-directory copy-dir)
		(error nil))
(while (not (equal queue nil))
		(print queue)
		;; (let ((current-target (car queue)))
		;; 		(setq queue (cdr queue))
		;; 	(copy-dependency current-target))
		(copy-dependency (pop queue))
		)
;(eval-buffer nil t)
;if you uncomment it, it is inf loop


;; Require ClassicalFacts.

;; (defun tmp (a)
;; 		(concat "!!!!" a))
;; (mapcar 'tmp (split-string "Decidable DecidableTypeEx FSetFacts"))
;; (split-string "Decidable")

;;    [uniqueness] tactic (defined below) requires. *)

;;Require Import Decidable.abcd.efg DecidableTypeEx FSetFacts.

;; (copy-dependency "Vellvm/syntax.v")
;; (describe-variable 'queue)






;; "/home/youngju.song/.local/lib/coq/theories/ZArith/ZArith.v"

;; (split-string "abc/def/ghi" "/")

;; (copy-dependency my-file-dir)
;; (copy-dependency "/home/youngju.song/coq_related/vellvm-legacy/src/Vellvm/syntax.v")
;; (copy-dependency "/home/youngju.song/coq_related/vellvm-legacy/src/Vellvm/ott/ott_list_core.v")
;; (copy-dependency "/home/youngju.song/coq_related/vellvm-legacy/src/Vellvm/datatype_base.v")

;; (if (shell-command "coq_makefile -install none *.v -o Makefile && make -j4")
;; 				(print "NOOOOO"))

;; (copy-file "/home/youngju.song/coq_related/vellvm-legacy/src/Vellvm/ott/ott_list_eq_dec.v" ".")


;; (defun coq-ask-do (ask do &optional dontguess postformatcmd)
;;   "Ask for an ident and print the corresponding term."
;;   (let* ((cmd) (postform (if (eq postformatcmd nil) 'identity postformatcmd)))
;;     (proof-shell-ready-prover)
;;     (setq cmd (coq-guess-or-ask-for-string ask dontguess))
;;     (proof-shell-invisible-command
;;      (format (concat do " %s . ") (funcall postform cmd)))))
;; (defun coq-LocateLibrary ()
;;   "Locate a library."
;;   (interactive)
;;   (coq-ask-do "Locate Library" "Locate Library"))


;; (pg-insert-last-output-as-comment)

;; (coq-LocateLibrary2 "syntax_base")

;; (while (re-search-forward "message" nil t)
;;   (replace-match "notfun"))

;; (defun pg-insert-last-output-as-comment ()
;;   "Insert the last output from the proof system as a comment in the proof script."
;;   (interactive)
;;   (if proof-shell-last-output
;;       (let  ((beg (point)))
;; 	(insert (proof-shell-strip-output-markup proof-shell-last-output))
;; 	(comment-region beg (point)))))






;; (defun proof-shell-invisible-command (cmd &optional wait invisiblecallback
;; 					  &rest flags)
;;   "Send CMD to the proof process.
;; The CMD is `invisible' in the sense that it is not recorded in buffer.
;; CMD may be a string or a string-yielding expression.

;; Automatically add `proof-terminal-string' if necessary, examining
;; `proof-shell-no-auto-terminate-commands'.

;; By default, let the command be processed asynchronously.
;; But if optional WAIT command is non-nil, wait for processing to finish
;; before and after sending the command.

;; In case CMD is (or yields) nil, do nothing.

;; INVISIBLECALLBACK will be invoked after the command has finished,
;; if it is set.  It should probably run the hook variables
;; `proof-state-change-hook'.

;; FLAGS are additional flags to put onto the `proof-action-list'.
;; The flag 'invisible is always added to FLAGS."
;;   (unless (stringp cmd)
;;     (setq cmd (eval cmd)))
;;   (if cmd
;;       (progn
;; 	(unless (or (null proof-terminal-string)
;; 		    (not proof-shell-auto-terminate-commands)
;; 		    (string-match (concat
;; 				   (regexp-quote proof-terminal-string)
;; 				   "[ \t]*$") cmd))
;; 	  (setq cmd (concat cmd proof-terminal-string)))
;; 	(if wait (proof-shell-wait))
;; 	(proof-shell-ready-prover)  ; start proof assistant; set vars.
;; 	(let* ((callback
;; 		(if invisiblecallback
;; 		    (lexical-let ((icb invisiblecallback))
;; 		      (lambda (span)
;; 			(funcall icb span)))
;; 		  'proof-done-invisible)))
;; 	  (proof-start-queue nil nil
;; 			     (list (proof-shell-action-list-item
;; 				    cmd
;; 				    callback
;; 				    (cons 'invisible flags)))))
;; 	(if wait (proof-shell-wait)))))



;; (defun proof-process-buffer ()
;;   "Process the current (or script) buffer, and maybe move point to the end."
;;   (interactive)
;;   (proof-with-script-buffer
;;    (save-excursion
;;      (goto-char (point-max))
;;      (proof-assert-until-point-interactive))
;;    (proof-maybe-follow-locked-end))
;;   (when proof-fast-process-buffer
;;     (message "Processing buffer...")
;;     (proof-shell-wait)
;;     (message "Processing buffer...done")))

