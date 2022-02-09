;;; spthy.el --- SPTHY major mode
;; Author: Katriel Cohn-Gordon

;; PRE-TAMARIN MODE: [UGLY HACK] this mode is only used to be able to highlight comments '//' AND  '/* */'
;;                   since 'modify-syntax-entry' seems unable to deal with both types of comments :(
(require 'generic-x)
(define-generic-mode
  'pre-spthy-mode
  '("//" ("/*" . "*/"))  ;; C-like comments
  '()
  '(((rx "X" (group (any ascii)) "X") . 'font-lock-keyword-face))
  '("\\.spthy$") ;; files for which to activate this mode
  nil            ;; other functions to call
  "A mode for Tamarin files") ;; doc string for this mode

;; TAMARIN-MODE
;; Keybindings
(defvar wpdl-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-j" 'newline-and-indent)
    map)
  "Keymap for SPTHY major mode")

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.spthy\\'" . spthy-mode))

(defvar spthy-keywords
  '("axiom" "lemma" "restriction" "protocol" "property" "text" "rule" "let" "in" "Fresh" "fresh" "Public" "public" "All" "Ex" "h" "sk" "pk" "Fr" "In" "Out" "fr" "in" "out" "not" "!"))

(defvar spthy-events
  '("theory" "begin" "end" "subsection" "section" "pb" "lts" "diffie-hellman" "bilinear-pairing" "multiset" "hashing" "symmetric-encryption" "asymmetric-encryption" "exists-trace" "all-traces" "enable" "assertions" "modulo" "default_rules" "anb-proto" "signing" "revealing-signing"))

(defvar spthy-operators
  '("&" "|" "==>" "=" "<=>" "-->" "^" "[" "]->" "-->" "]" "--["))

(defvar spthy-warnings
  '("@" "functions" "builtins" "equations" "heuristic" "!")) ; we may want to add ! in operators instead

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

(define-derived-mode spthy-mode pre-spthy-mode "SPTHY"
  "Major mode for editing Tamarin's SPTHY files."
  
  ;; Fontify keywords
  (setq font-lock-defaults spthy-font-lock-defaults)

  ;; Double quotes are for lemmas not strings
  (modify-syntax-entry ?\" "w" spthy-mode-syntax-table)
  (modify-syntax-entry ?' "\"" spthy-mode-syntax-table)

  ;; < > are delimiters too
  (modify-syntax-entry ?< "(" spthy-mode-syntax-table)
  (modify-syntax-entry ?> "(" spthy-mode-syntax-table)
  
  )

(provide 'spthy-mode)
