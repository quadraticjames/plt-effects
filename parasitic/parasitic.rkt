#lang racket
(require redex)

(define-language Pt
  (e x
     v
     (e e)
     (λ x e))
  (v unit
     (λ x e r)
     κ
     k)
  (x variable-not-otherwise-mentioned)
  (r (ρ (x v) ...))
  (k (f ...))
  (f (ret v)
     (arg e r)
     (fun v))
  (s (control e r k_0)
     (return k)
     (halt v)))

(define-extended-language Ev Pt
  (p s)
  (P S)
  (S s
     hole))

(define red
  (reduction-relation
   Ev
   #:domain p
   (--> (control v r (f ...))
        (return ((ret v) f ...))
        "value")
   (--> (control x (ρ (x_left v_left) ... (x v) (x_right v_right) ...) (f ...))
        (return ((ret v) f ...))
        "variable")
   (--> (control (λ x e) r (f ...))
        (return ((ret (λ x e r)) f ...))
        "closure")
   (--> (control (e_1 e_2) r (f ...))
        (control e_1 r ((arg e_2 r) f ...))
        "application")
   (--> (return ((ret v) (arg e r) f ...))
        (control e r ((fun v) f ...))
        "argument")
   (--> (return ((ret v) (fun (λ x e (ρ (x_0 v_0) ...))) f ...))
        (control e (ρ (x_0 v_0) ... (x v)) (f ...))
        "function")
   ))

(define-metafunction Ev
  var-lookup : r x -> v
  [(var-lookup (ρ (x v) (x_1 v_1) ...) x)
   v]
  [(var-lookup (ρ (x_0 v_0) (x_1 v_1) ...) x)
   (var-lookup (ρ (x_1 v_1) ...) x)])
