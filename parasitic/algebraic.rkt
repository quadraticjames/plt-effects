#lang racket
(require redex)

(define-language Pt
  (e x
     v
     (e e)
     (λ x e)
     (handle e e e)
     (perform e)
     (continue e e)
     (fst (e \, e))
     (snd (e \, e)))
  (v unit
     (λ x e r)
     k
     (v \, v))
  (x variable-not-otherwise-mentioned)
  (r (ρ (x v) ...))
  (k (f ...))
  (f (ret v)
     (arg e r)
     (fun v)
     (hnd1 e e r)
     (hnd2 v e r)
     (hnd3 v v)
     (hdl v v))
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
   (--> (return ((ret v)) ((hdl v_hval v_heff) f ...) k_1 ...)
        (return ((ret v) (fun v_hval) f ...) k_1 ...)
        "handleHalt")
   (--> (return ((ret v)) (f ...) k_1 ...)
        (return ((ret v) f ...) k_1 ...)
        "parasiteHalt")
   #|
(return ((ret unit)) ((ret unit)))
should reduce to
(return ((ret unit)))
   |#
   (--> (control (handle e_1 e_2 e_3) r (f ...) k_1 ...)
        (control e_1 r ((hnd1 e_2 e_3 r) f ...) k_1 ...)
        "handle1")
   (--> (return ((ret v) (hnd1 e_2 e_3 r) f ...) k_1 ...)
        (control e_2 r ((hnd2 v e_3 r) f ...) k_1 ...)
        "handle2")
   (--> (return ((ret v_2) (hnd2 v_1 e_3 r) f ...) k_1 ...)
        (control e_3 r ((hnd3 v_1 v_2) f ...) k_1 ...)
        "handle3")
   (--> (return ((ret v_3) (hnd3 v_1 v_2) f ...) k_1 ...)
        (return v_1 ((hdl v_2 v_3) f ...) k_1 ...)
        "handle4")
   (--> (control (perform v) r k_0 ((hdl v_hval v_heff) f ...) k_1 ...)
        (return ((ret (v \, k_0)) (fun v_heff) (hdl v_hval v_heff) f ...) k_1 ...)
        "perform")
   (--> (return ((ret v) (hdl v_hval v_heff) f ...) k_1 ...)
        (return ((ret v) f ...) k_1 ...)
        "h_effHalt")
   (--> (control (continue e_1 e_2) r (f ...) k_1 ...)
        (control e_1 r ((con1 e_2 r) f ...) k_1 ...)
        "continue1")
   (--> (return ((ret v) (con1 e r) f ...) k_1 ...)
        (control e r ((con2 v) f ...) k_1 ...)
        "continue2")
   (--> (return ((ret v_2) (con2 v_1) f_left ... (hdl v_hval v_heff) f_right ...) k_1 ...)
        (control v_2 (ρ) v_1 ((hdl v_hval v_heff) f_left ... (hdl v_hval v_heff) f_right ...) k_1 ...)
        "continue3")

   (--> (control (fst (e_1 \, e_2)) r k_0 k_1 ...)
        (control e_1 r k_0 k_1 ...)
        "first")
   (--> (control (snd (e_1 \, e_2)) r k_0 k_1 ...)
        (control e_2 r k_0 k_1 ...)
        "second")
   ))

(define-metafunction Ev
  var-lookup : r x -> v
  [(var-lookup (ρ (x v) (x_1 v_1) ...) x)
   v]
  [(var-lookup (ρ (x_0 v_0) (x_1 v_1) ...) x)
   (var-lookup (ρ (x_1 v_1) ...) x)])
