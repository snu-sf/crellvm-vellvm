;Assumption : all files with dependency are explicitly declared with "Require" Vernacular command.
;Assumption : coq-LocateLibrary works well.
;Assumption : dependent files compiles well.
;Assumption : Require command starts at the first column (broken, ListSet.v?)
;Optimize : just copy related commands at the beginning of buffer?

(defvar str-format nil
		"Searching target, to find Require Vernacular command.")
(setq str-format "Require")
(defvar current-dir nil
		"Current directory.")
(setq current-dir (file-name-directory (or load-file-name buffer-file-name)))
(defvar copy-dir nil
		"Copy destination directory.")
(setq copy-dir (concat current-dir "Syntax/"))
(defun get-line-content ()
		"It assumes the cursor is in a line containing \"Require\". The Vernacular command format is \"Require [Import|Export|] blah blah.\"."
		(interactive)
		(print (delete "Export" (delete "Import" (delete "Require" (split-string (buffer-substring-no-properties (line-beginning-position) (- (line-end-position) 1))))))))
(defun coq-LocateLibrary2 (name)
		"Modification of \"coq-LocateLibrary2\", as it requires interactive input."
		(proof-shell-wait)
		(proof-shell-ready-prover)
  (proof-shell-invisible-command
			(format (concat "Locate Library" " %s . ") (funcall 'identity name)) t))
(defun name-to-location (name)
		"Change library name string to its .vo file location."
		(coq-LocateLibrary2 name)
		(car (last (split-string (proof-shell-strip-output-markup proof-shell-last-output)))))
(defun vo-location-to-v-location (location)
		"Change string that ends with .vo to .v"
		(substring location 0 -1))
(defun check-validity (location)
		"Check if location is \"initial.coq\", I don't know what it is but it doesn't exist. Also, check if path contains \".local\", to check whether it is Coq's default library. Default library causes some problem with namespace like Coq.Bool instead of Bool."
		(setq source_name (car (last (split-string location "/"))))
		(setq path-list (remove source_name (split-string location "/")))
		(not (or (string-equal source_name "initial.coq")
											(member ".local" path-list))))
(defvar queue nil
		"Queue for search." )
(defvar history nil
		"Check whether the node is visited.")
(defun copy-dependency (my-file-dir)
		"Copy dependent files of argument."
		(unless (member my-file-dir history) 
				(push my-file-dir history)
				(if (file-exists-p my-file-dir)	
								(let ((my-file-buffer (find-file-noselect my-file-dir)))
										(copy-file my-file-dir copy-dir t)
										(switch-to-buffer my-file-buffer)
										(setq case-fold-search nil)
										(if proof-shell-buffer (proof-shell-exit t))
										(beginning-of-buffer)
										(while (search-forward str-format nil t))
										(proof-goto-point)
										(beginning-of-buffer)
										(while (search-forward str-format nil t)
												(if (= (- (point) (line-beginning-position)) 7)
																(let ((deps (mapcar 'name-to-location (get-line-content))) ;Require command may have list of names. It is list of its .vo file paths.
																						(dep) ;Treat only one this time, others are queued.
																						(depv)) ;dep is .vo file path, and it is .v file path obtained simply by chopping the last character. File may may not exist.
																		(setq dep (car deps))
																		(print deps)
																		(print dep)
																		(setq queue (append (mapcar 'vo-location-to-v-location (cdr deps)) queue))
																		(print queue)

																		(setq depv (vo-location-to-v-location dep))
																		(if (check-validity dep) ;;why not just v_location? location such as initial.coq
																						(if (file-exists-p depv)
																										(progn
																												(print (concat "Copying from " depv " to " copy-dir))
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
;; (setq queue '("Vellvm/opsem.v"))
(setq queue '("Vellvm/syntax.v"))

;Create directory, if it already exists, do nothing.
(condition-case nil
				(make-directory copy-dir)
		(error nil))
;Do search.
(while (not (equal queue nil))
		(print queue)
		(copy-dependency (pop queue))
		)

(let ((default-directory copy-dir))
		(shell-command "coq_makefile -arg -impredicative-set -install none *.v -o Makefile && make -j4"))
;(eval-buffer nil t)
;eval it!
;if you uncomment it, it is inf loop


