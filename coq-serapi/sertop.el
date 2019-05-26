;;; sertop.el --- Sertop REPL in Emacs               -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Clément Pit-Claudel

;; Author: Clément Pit--Claudel <clement.pitclaudel@live.com>
;; Keywords: convenience

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Open `sertop.el` and run `M-x eval-buffer` followed by `M-x
;;; sertop` to get a sertop REPL in Emacs, with highlighting and
;;; pretty-printing (useful for debugging).

;;; You may want to configure the variable `sertop-coq-directory` to
;;; point out the location of Coq's stdlib.

;;; Code:

(require 'comint)

(defconst sertop--root
  (file-name-directory (or load-file-name
                           (bound-and-true-p byte-compile-current-file)
                           (buffer-file-name))))

(defvar sertop-executable-path
  (or (expand-file-name "sertop.native" sertop--root)
      (executable-find "sertop"))
  "Path to sertop.")

(defvar sertop-coq-directory nil
  "Location of the directory containing Coq's sources, or nil.")

(defvar-local sertop--accumulator nil
  "List of strings accumulated from sertop in reverse order.")

(defun sertop--format (response)
  "Read RESPONSE into a sexp and return a pretty-printed, indented copy."
  (replace-regexp-in-string
   "^\\(.\\)" "  \\1"
   (pp-to-string (read response)) t))

(defun sertop--preoutput-filter (string)
  "Accumulate STRING, returning full responses."
  (let* ((parts (split-string string "\0" nil))
         (messages nil))
    (while (consp (cdr parts))
      (push (pop parts) sertop--accumulator)
      (push (apply #'concat (nreverse sertop--accumulator)) messages)
      (setq sertop--accumulator nil))
    (push (car parts) sertop--accumulator)
    (mapconcat #'sertop--format (nreverse messages) "")))

(defconst sertop--font-lock-keywords
  '(("([A-Z]\\(\\w\\|\\s_\\|\\\\.\\)+\\(\\s-\\|\n\\)" . font-lock-function-name-face)
    ("(\\(\\w\\|\\s_\\|\\\\.\\)+\\(\\s-\\|\n\\)" . font-lock-variable-name-face)
    ("\\_<nil\\_>" . font-lock-builtin-face))
  "Font lock pairs for `sertop-mode'.")

(defvar sertop-mode-syntax-table lisp-mode-syntax-table
  "Syntax table for `sertop-mode'.")

(define-derived-mode sertop-mode comint-mode "Sertop"
  "Major mode for interacting with Sertop.

Output is accumulated and printed once a full message has been received."
  (setq comint-process-echoes nil)
  (setq comint-use-prompt-regexp nil)
  (setq font-lock-defaults '(sertop--font-lock-keywords))
  (when (fboundp 'rainbow-delimiters-mode) (rainbow-delimiters-mode))
  (add-hook 'comint-preoutput-filter-functions #'sertop--preoutput-filter nil t))

(defun sertop--args ()
  "Compute sertop arguments."
  `("--print0"
    ,@(when sertop-coq-directory
        `("--prelude" ,sertop-coq-directory))))

(defun sertop ()
  "Launch sertop."
  (interactive)
  (let ((buffer (get-buffer-create (generate-new-buffer-name "*Sertop*"))))
    (pop-to-buffer buffer)
    (apply 'make-comint-in-buffer "Sertop"
           buffer sertop-executable-path nil (sertop--args))
    (sertop-mode)))

(provide 'sertop)
;;; sertop.el ends here
