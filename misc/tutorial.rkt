#lang racket
(require redex)

(define-language L
  (e (e e)
     (λ (x t) e)
     x
     (amb t e ...)
     number
     (+ e ...)
     (if0 e e e)
     (fix e))
  (t (→ t t) num)
  (x variable-not-otherwise-mentioned))

(define-extended-language L+Γ L [Γ · (x : t Γ)])

(define-judgment-form
  L+Γ
  #:mode (types I I O)
  #:contract (types Γ e t)
 
  [(types Γ e_1 (→ t_2 t_3))
   (types Γ e_2 t_2)
   -------------------------
   (types Γ (e_1 e_2) t_3)]
 
  [(types (x : t_1 Γ) e t_2)
   -----------------------------------
   (types Γ (λ (x t_1) e) (→ t_1 t_2))]
 
  [(types Γ e (→ (→ t_1 t_2) (→ t_1 t_2)))
   ---------------------------------------
   (types Γ (fix e) (→ t_1 t_2))]
 
  [---------------------
   (types (x : t Γ) x t)]
 
  [(types Γ x_1 t_1)
   (side-condition (different x_1 x_2))
   ------------------------------------
   (types (x_2 : t_2 Γ) x_1 t_1)]
 
  [(types Γ e num) ...
   -----------------------
   (types Γ (+ e ...) num)]
 
  [--------------------
   (types Γ number num)]
 
  [(types Γ e_1 num)
   (types Γ e_2 t)
   (types Γ e_3 t)
   -----------------------------
   (types Γ (if0 e_1 e_2 e_3) t)]
 
  [(types Γ e t) ...
   (side-condition (same t ...))
   --------------------------
   (types Γ (amb t_1 e ...) t_1)])

(define-metafunction L+Γ
  [(different x_1 x_1) #f]
  [(different x_1 x_2) #t])

(define-metafunction L+Γ
  [(same t_1) #t]
  [(same t_1 t_1 t_2 ...) (same t_1 t_2 ...)]
  [(same t_1 t_2 ...) #f])

(test-equal
 (judgment-holds
  (types · (λ (x num) x) t)
  t)
 (list (term (→ num num))))

(test-equal
 (judgment-holds
  (types · (amb num 1 2 3) t)
  t)
 (list (term num)))

(test-equal
 (judgment-holds
  (types · (amb (→ num num) (λ (x num) x) (λ (x num) 0)) t)
  t)
 (list (term (→ num num))))

(test-equal
 (judgment-holds
  (types · (+ 1 2) t)
  t)
 (list (term num)))