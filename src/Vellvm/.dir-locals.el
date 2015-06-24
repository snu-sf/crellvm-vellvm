;; Specify coq-load path relative to project root
((coq-mode . ((eval . (flet ((pre (s) (concat 
                                       (locate-dominating-file buffer-file-name
                                                               ".dir-locals.el") 
                                       s)))
                        (setq coq-load-path 
                              `(
                                ,(pre "../Syntax")
                                ,(pre "../../lib/compcert-2.4/lib")
                                ,(pre "../../lib/compcert-2.4/ia32")
                                ,(pre "../../lib/compcert-2.4/common")
                                ,(pre "../../lib/compcert-2.4/old")
                                ,(pre "../../lib/compcert-2.4/flocq/Appli")
                                ,(pre "../../lib/compcert-2.4/flocq/Calc")
                                ,(pre "../../lib/compcert-2.4/flocq/Core")
                                ,(pre "../../lib/compcert-2.4/flocq/Prop")
                                ,(pre "../../lib/compcert-2.4/backend")
																																;; ,(pre "../../src/Vellvm")
                                ;; ,(pre "../../src/Vellvm/ott")
                                ;; ,(pre "../../src/Vellvm/Dominators")
                                ;; ,(pre "../../lib/compcert-1.9")
                                ;; ,(pre "../../lib/cpdtlib")
                                ;; ,(pre "../../lib/GraphBasics")
                                ,(pre "../../lib/metalib-20090714")
                                ;; ,(pre "../../lib/Coq-Equations-8.4/src")
                                ;; (rec ,(pre "../../lib/Coq-Equations-8.4/theories") "Equations")
																																))))
              (coq-prog-args . ("-emacs-U"
                                "-impredicative-set")))))
                                      
