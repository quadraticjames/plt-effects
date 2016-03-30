#lang racket
(require redex)

(define-language Pt
  (e x
     v
     (e e)
     (λ x e)
     (letrec x v e)
     (handle e e e)
     (perform e)
     (continue e e)
     (fst (e \, e))
     (snd (e \, e))
     (if e e e e)
     (ref x e)
     (deref x))
  (v unit
     (λ x e r)
     k
     (v \, v)
     string)
  (x variable-not-otherwise-mentioned)
  (r (ρ (x v) ...))
  (k (f ...))
  (f (ret v)
     (arg e r)
     (fun v)
     (hnd1 e e r)
     (hnd2 v e r)
     (hnd3 v v)
     (hdl v v)
     (con1 e r)
     (con2 v)
     (if1 e e e r)
     (if2 v e e))
  (s (control e r k_0 k_1 ...)
     (return k_0 k_1 ...)
     (halt v))
  (m ((x v) ...)))

(define-extended-language Ev Pt
  (p (s m))
  (P (S m))
  (S s
     hole))

(define red
  (reduction-relation
   Ev
   #:domain p
   (--> ((control v r (f ...) k ...) m)
        ((return ((ret v) f ...) k ...) m)
        "value")
   #|
(control unit (ρ) ())
should reduce to
(return ((ret unit)))
   |#
   (--> ((control x r (f ...) k ...) m)
        ((return ((ret (var-lookup r x)) f ...) k ...) m)
        "variable")
   #|
(control x (ρ (x unit)) ())
should reduce to
(return ((ret unit)))
   |#
   (--> ((control (λ x e) r (f ...) k ...) m)
        ((return ((ret (λ x e r)) f ...) k ...) m)
        "closure")
   #|
(control (λ x x) (ρ) ())
should reduce to
(return ((ret (λ x x (ρ)))))
   |#
   (--> ((control (e_1 e_2) r (f ...) k ...) m)
        ((control e_1 r ((arg e_2 r) f ...) k ...) m)
        "application")
   #|
(control ((λ x x) unit) (ρ) ())
should reduce to
(control (λ x x) (ρ) ((arg unit (ρ))))
   |#
   (--> ((control (if e_1 e_2 e_3 e_4) r (f ...) k ...) m)
        ((control e_1 r ((if1 e_2 e_3 e_4 r) f ...) k ...) m)
        "if1")
   (--> ((return ((ret v) (if1 e_2 e_3 e_4 r) f ...) k ...) m)
        ((control e_2 r ((if2 v e_3 e_4 r) f ...) k ...) m)
        "if2")
   (--> ((return ((ret string_1) (if2 string_1 e_3 e_4 r) f ...) k ...) m)
        ((control e_3 r (f ...) k ...) m)
        "iftrue")
   (--> ((return ((ret string_2) (if2 string_1 e_3 e_4 r) f ...) k ...) m)
        ((control e_4 r (f ...) k ...) m)
        (side-condition (not (equal? (term string_1) (term string_2))))
        "iffalse")
   (--> ((control (letrec x v e) (ρ (x_0 v_0) ...) (f ...) k ...) m)
        ((control e (ρ (x_0 v_0) ... (x v)) (f ...) k ...) m)
        "letrec")
   (--> ((control (ref x e) r (f ...) k ...) m)
        ((control e r ((rfr x) f ...) k ...) m)
        "ref1")
   (--> ((return ((ret v) (rfr x) f ...) k ...) ((x_0 v_0) ...))
        ((return ((ret unit) f ...) k ...) ((x_0 v_0) ... (x v)))
        (side-condition (not (ref-exists ((x_0 v_0) ...) x)))
        "refnew")
   (--> ((return ((ret v) (rfr x) f ...) k ...) ((x_left v_left) ... (x v_old) (x_right v_right) ...))
        ((return ((ret unit) f ...) k ...) ((x_left v_left) ... (x v) (x_right v_right) ...))
        "refupdate")
   (--> ((control (deref x) r (f ...) k ...) ((x_left v_left) ... (x v) (x_right v_right) ...))
        ((return ((ret v) f ...) k ...) ((x_left v_left) ... (x v) (x_right v_right) ...))
        "deref")
   (--> ((return ((ret v) (arg e r) f ...) k ...) m)
        ((control e r ((fun v) f ...) k ...) m)
        "argument")
   #|
(return ((ret (λ x x (ρ))) (arg unit (ρ))))
should reduce to
(control unit (ρ) ((fun (λ x x (ρ)))))
   |#
   (--> ((return ((ret v) (fun (λ x e (ρ (x_0 v_0) ...))) f ...) k ...) m)
        ((control e (ρ (x_0 v_0) ... (x v)) (f ...) k ...) m)
        "function")
   #|
(return ((ret unit) (fun (λ x x (ρ)))))
should reduce to
(control x (ρ (x unit)) ())
   |#
   (--> ((return ((ret v))) m)
        ((halt v) m)
        "threadHalt")
   #|
(return ((ret unit)))
should reduce to
(halt unit)
   |#
   (--> ((return ((ret v)) ((hdl v_hval v_heff) f ...) k_1 ...) m)
        ((return ((ret v) (fun v_hval) f ...) k_1 ...) m)
        "handleHalt")
   (--> ((return ((ret v)) (f ...) k_1 ...) m)
        ((return ((ret v) f ...) k_1 ...) m)
        "parasiteHalt")
   #|
(return ((ret unit)) ((ret unit)))
should reduce to
(return ((ret unit)))
   |#
   (--> ((control (handle e_1 e_2 e_3) r (f ...) k_1 ...) m)
        ((control e_1 r ((hnd1 e_2 e_3 r) f ...) k_1 ...) m)
        "handle1")
   (--> ((return ((ret v) (hnd1 e_2 e_3 r) f ...) k_1 ...) m)
        ((control e_2 r ((hnd2 v e_3 r) f ...) k_1 ...) m)
        "handle2")
   (--> ((return ((ret v_2) (hnd2 v_1 e_3 r) f ...) k_1 ...) m)
        ((control e_3 r ((hnd3 v_1 v_2) f ...) k_1 ...) m)
        "handle3")
   (--> ((return ((ret v_3) (hnd3 v_1 v_2) f ...) k_1 ...) m)
        ((return v_1 ((hdl v_2 v_3) f ...) k_1 ...) m)
        "handle4")
   (--> ((control (perform v) r k_0 ((hdl v_hval v_heff) f ...) k_1 ...) m)
        ((return ((ret (v \, k_0)) (fun v_heff) (hdl v_hval v_heff) f ...) k_1 ...) m)
        "perform")
   (--> ((return ((ret v) (hdl v_hval v_heff) f ...) k_1 ...) m)
        ((return ((ret v) f ...) k_1 ...) m)
        "h_effHalt")
   (--> ((control (continue e_1 e_2) r (f ...) k_1 ...) m)
        ((control e_1 r ((con1 e_2 r) f ...) k_1 ...) m)
        "continue1")
   (--> ((return ((ret v) (con1 e r) f ...) k_1 ...) m)
        ((control e r ((con2 v) f ...) k_1 ...) m)
        "continue2")
   (--> ((return ((ret v_2) (con2 v_1) f_left ... (hdl v_hval v_heff) f_right ...) k_1 ...) m)
        ((control v_2 (ρ) v_1 ((hdl v_hval v_heff) f_left ... (hdl v_hval v_heff) f_right ...) k_1 ...) m)
        "continue3")

   (--> ((control (fst (e_1 \, e_2)) r k_0 k_1 ...) m)
        ((control e_1 r k_0 k_1 ...) m)
        "first")
   (--> ((control (snd (e_1 \, e_2)) r k_0 k_1 ...) m)
        ((control e_2 r k_0 k_1 ...) m)
        "second")
   ))

(define-metafunction Ev
  var-lookup : r x -> v
  [(var-lookup (ρ (x v) (x_1 v_1) ...) x)
   v]
  [(var-lookup (ρ (x_0 v_0) (x_1 v_1) ...) x)
   (var-lookup (ρ (x_1 v_1) ...) x)])

(define-metafunction Ev
  ref-exists : m x -> boolean
  [(ref-exists ((x v) (x_1 v_1) ...) x) true]
  [(ref-exists () x) false]
  [(ref-exists ((x_0 v_0) (x_1 v_1) ...) x)
   (ref-exists ((x_1 v_1) ...) x)])
