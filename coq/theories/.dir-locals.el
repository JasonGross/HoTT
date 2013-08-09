((coq-mode . ((eval . (let ((default-directory (locate-dominating-file
                                                buffer-file-name ".dir-locals.el")))
                        (setq coq-prog-args `("-no-native-compiler" "-indices-matter" "-boot" "-nois" "-coqlib" ,(expand-file-name "..") "-R" ,(expand-file-name ".") "Coq" "-emacs-U")))))))
