(require 'agda2-highlight)

;; Change backgrounds to boxes.
(cl-loop for (_ . face) in agda2-highlight-faces
      do (if (string-prefix-p "agda2-" (symbol-name face)) ;; Some non-Agda faces are in the list; don't change them
             (unless (equal face 'agda2-highlight-incomplete-pattern-face) ;; Workaround; this face is not defined in recent versions?
             (set-face-attribute face nil
               :box (face-attribute face :background)
               :background 'unspecified))))

;; Coverage warnings highlight the whole function;
;; change the box to an underline to be less intrusive.
(set-face-attribute 'agda2-highlight-coverage-problem-face nil
  :underline (face-attribute 'agda2-highlight-coverage-problem-face :box)
  :box 'unspecified)

;; Deadcode warnings highlight the whole line;
;; change the box to a strikethrough to be less intrusive,
;; as well as thematically appropriate.
(set-face-attribute 'agda2-highlight-deadcode-face nil
  :strike-through (face-attribute 'agda2-highlight-deadcode-face :box)
  :box 'unspecified)

;; Non-definitional pattern matching may be ignored;
;; remove the colouring and just italicise it to be less intrusive.
(set-face-attribute 'agda2-highlight-catchall-clause-face nil
  :box 'unspecified
  :slant 'italic)
