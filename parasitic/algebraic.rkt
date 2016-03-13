#lang racket
(require redex)

(define-language Pt
  (e x
     v
     (e e)
     (λ x e)
     (handle e e e))
  (v unit
     (λ x e r)
     k)
  (x variable-not-otherwise-mentioned)
  (r (ρ (x v) ...))
  (k (f ...))
  (f (ret v)
     (arg e r)
     (fun v))
  (s (control e r k_0 k_1 ...)
     (return k_0 k_1 ...)
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
   (--> (control v r (f ...) k ...)
        (return ((ret v) f ...) k ...)
        "value")
   #|
(control unit (ρ) ())
should reduce to
(return ((ret unit)))
   |#
   (--> (control x r (f ...) k ...)
        (return ((ret (var-lookup r x)) f ...) k ...)
        "variable")
   #|
(control x (ρ (x unit)) ())
should reduce to
(return ((ret unit)))
   |#
   (--> (control (λ x e) r (f ...) k ...)
        (return ((ret (λ x e r)) f ...) k ...)
        "closure")
   #|
(control (λ x x) (ρ) ())
should reduce to
(return ((ret (λ x x (ρ)))))
   |#
   (--> (control (e_1 e_2) r (f ...) k ...)
        (control e_1 r ((arg e_2 r) f ...) k ...)
        "application")
   #|
(control ((λ x x) unit) (ρ) ())
should reduce to
(control (λ x x) (ρ) ((arg unit (ρ))))
   |#
   (--> (return ((ret v) (arg e r) f ...) k ...)
        (control e r ((fun v) f ...) k ...)
        "argument")
   #|
(return ((ret (λ x x (ρ))) (arg unit (ρ))))
should reduce to
(control unit (ρ) ((fun (λ x x (ρ)))))
   |#
   (--> (return ((ret v) (fun (λ x e (ρ (x_0 v_0) ...))) f ...) k ...)
        (control e (ρ (x_0 v_0) ... (x v)) (f ...) k ...)
        "function")
   #|
(return ((ret unit) (fun (λ x x (ρ)))))
should reduce to
(control x (ρ (x unit)) ())
   |#
   (--> (return ((ret v)))
        (halt v)
        "threadHalt")
   #|
(return ((ret unit)))
should reduce to
(halt unit)
   |#
   (--> (return ((ret v)) k_1 k_2 ...)
        (return k_1 k_2 ...)
        "parasiteHalt")
   #|
(return ((ret unit)) ((ret unit)))
should reduce to
(return ((ret unit)))
   |#
   ))

(define-metafunction Ev
  var-lookup : r x -> v
  [(var-lookup (ρ (x v) (x_1 v_1) ...) x)
   v]
  [(var-lookup (ρ (x_0 v_0) (x_1 v_1) ...) x)
   (var-lookup (ρ (x_1 v_1) ...) x)])
