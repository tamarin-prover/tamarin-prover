;;; spthy.el --- SPTHY major mode
;; Author: Katriel Cohn-Gordon

;; Keybindings
(defvar wpdl-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-j" 'newline-and-indent)
    map)
  "Keymap for SPTHY major mode")

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.spthy\\'" . spthy-mode))

(defvar spthy-keywords
  '("axiom" "lemma" "protocol" "property" "theory" "begin" "end" "subsection" "section" "text" "rule" "let" "in" "Fresh" "fresh" "Public" "public" "signing" "hashing" "All" "Ex" "h" "sk" "pk" "Fr" "In" "Out" "fr" "in" "out" "not"))

(defvar spthy-events
  '("pb" "lts" "diffie-hellman" "bilinear-pairing" "multiset" "symmetric-encryption" "asymmetric-encryption" "exists-trace" "all-traces" "enable" "assertions" "modulo" "default_rules" "anb-proto"))

(defvar spthy-operators
  '("&" "|" "!" "==>" "=" "<=>" "-->" "^"))

(defvar spthy-warnings
  '("@" "functions" "builtins" "equations"))

(defvar spthy-quiet
  '("~" "$"))

(defvar spthy-font-lock-defaults
  `((
     ( ,(regexp-opt spthy-keywords          'words) . font-lock-keyword-face)
     ( ,(regexp-opt spthy-events            'words) . font-lock-constant-face)
     ( ,(regexp-opt spthy-warnings                ) . font-lock-warning-face)
     ( ,(regexp-opt spthy-operators               ) . font-lock-constant-face)
     ( ,(regexp-opt spthy-quiet                   ) . font-lock-comment-face)
 )))

(define-derived-mode spthy-mode fundamental-mode "SPTHY"
  "Major mode for editing Tamarin's SPTHY files."
  
  ;; Fontify keywords
  (setq font-lock-defaults spthy-font-lock-defaults)

  ;; C-style comments
  (modify-syntax-entry ?/ ". 14b" spthy-mode-syntax-table)
  (modify-syntax-entry ?* ". 23b" spthy-mode-syntax-table)

  ;; Double quotes are for lemmas not strings
  (modify-syntax-entry ?\" "w" spthy-mode-syntax-table)
  (modify-syntax-entry ?' "\"" spthy-mode-syntax-table)

  ;; < > are delimiters too
  (modify-syntax-entry ?< "(" spthy-mode-syntax-table)
  (modify-syntax-entry ?> "(" spthy-mode-syntax-table)

  
  )

(provide 'spthy-mode)
