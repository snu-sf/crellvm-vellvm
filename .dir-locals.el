;; Specify coq-load path relative to project root
((coq-mode . ((eval . (flet
                          ((pre (s) (concat (locate-dominating-file buffer-file-name ".dir-locals.el") s)))
                        (setq coq-load-path
                              `((rec ,(pre "lib/metalib") "metalib")
                                (rec ,(pre "lib/cpdtlib") "cpdtlib")
                                (rec ,(pre "lib/compcert-2.4") "compcert")
                                (rec ,(pre "lib/GraphBasics") "GraphBasics")
                                (rec ,(pre "src/Vellvm") "Vellvm")))))
              (coq-prog-args . ("-emacs-U")))))
