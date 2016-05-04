#lang racket
(require redex)

(define-language Alg
  (e x
     v
     (e e)
     (λ x e)
     (letrec x e e)
     (handle e e e)
     (perform e)
     (continue e e)
     (fst e)
     (snd e)
     (if e e e e)
     (ref x e)
     (deref x)
     (e \; e)
     (e \, e))
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
     prf
     (if1 e e e r)
     (if2 v e e r)
     (rfr x)
     (seq e r)
     fir
     sec
     (pair1 e r)
     (pair2 v))
  (s (control e r k_0 k_1 ...)
     (return k_0 k_1 ...)
     (halt v))
  (m ((x v) ...)))

(define-extended-language Ev Alg
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
   (--> ((control x r (f ...) k ...) m)
        ((return ((ret (var-lookup r x)) f ...) k ...) m)
        "variable")
   (--> ((control (λ x e) r (f ...) k ...) m)
        ((return ((ret (λ x e r)) f ...) k ...) m)
        "closure")
   (--> ((control (e_1 e_2) r (f ...) k ...) m)
        ((control e_1 r ((arg e_2 r) f ...) k ...) m)
        "application")
   (--> ((return ((ret v) (arg e r) f ...) k ...) m)
        ((control e r ((fun v) f ...) k ...) m)
        "argument")
   (--> ((return ((ret v) (fun (λ x e (ρ (x_0 v_0) ...))) f ...) k ...) m)
        ((control e (ρ (x v) (x_0 v_0) ...) (f ...) k ...) m)
        "function")
   (--> ((control (if e_1 e_2 e_3 e_4) r (f ...) k ...) m)
        ((control e_1 r ((if1 e_2 e_3 e_4 r) f ...) k ...) m)
        "if1")
   (--> ((return ((ret v) (if1 e_2 e_3 e_4 r) f ...) k ...) m)
        ((control e_2 r ((if2 v e_3 e_4 r) f ...) k ...) m)
        "if2")
   (--> ((return ((ret v_1) (if2 v_1 e_3 e_4 r) f ...) k ...) m)
        ((control e_3 r (f ...) k ...) m)
        "iftrue")
   (--> ((return ((ret v_2) (if2 v_1 e_3 e_4 r) f ...) k ...) m)
        ((control e_4 r (f ...) k ...) m)
        (side-condition (not (equal? (term v_1) (term v_2))))
        "iffalse")
   (--> ((control (letrec x e_1 e_2) (ρ (x_0 v_0) ...) (f ...) k ...) m)
        ((control ((ref x e_1) \; e_2) (ρ (x (λ x_x ((deref x) x_x) (ρ (x_0 v_0) ...))) (x_0 v_0) ...) (f ...) k ...) m)
        "letrec")
   (--> ((control (ref x e) r (f ...) k ...) m)
        ((control e r ((rfr x) f ...) k ...) m)
        "ref")
   (--> ((return ((ret v) (rfr x) f ...) k ...) ((x_0 v_0) ...))
        ((return ((ret unit) f ...) k ...) ((x_0 v_0) ... (x v)))
        (side-condition (not (term (ref-exists ((x_0 v_0) ...) x))))
        "refnew")
   (--> ((return ((ret v) (rfr x) f ...) k ...) ((x_left v_left) ... (x v_old) (x_right v_right) ...))
        ((return ((ret unit) f ...) k ...) ((x_left v_left) ... (x v) (x_right v_right) ...))
        "refupdate")
   (--> ((control (deref x) r (f ...) k ...) ((x_left v_left) ... (x v) (x_right v_right) ...))
        ((return ((ret v) f ...) k ...) ((x_left v_left) ... (x v) (x_right v_right) ...))
        "deref")
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
   (--> ((control (perform e) r (f ...) k ...) m)
        ((control e r (prf f ...) k ...) m)
        "perform1")
   (--> ((return ((ret v) prf f_0 ...) ((hdl v_hval v_heff) f_1 ...) k_1 ...) m)
        ((return ((ret (v \, (f_0 ...))) (fun v_heff) (hdl v_hval v_heff) f_1 ...) k_1 ...) m)
        "perform2")
   (--> ((return ((ret v) (hdl v_hval v_heff) f ...) k_1 ...) m)
        ((return ((ret v) f ...) k_1 ...) m)
        "effHalt")
   (--> ((control (continue e_1 e_2) r (f ...) k_1 ...) m)
        ((control e_1 r ((con1 e_2 r) f ...) k_1 ...) m)
        "continue1")
   (--> ((return ((ret v) (con1 e r) f ...) k_1 ...) m)
        ((control e r ((con2 v) f ...) k_1 ...) m)
        "continue2")
   (--> ((return ((ret v_2) (con2 v_1) f_left ... (hdl v_hval v_heff) f_right ...) k_1 ...) m)
        ((control v_2 (ρ) v_1 ((hdl v_hval v_heff) f_left ... (hdl v_hval v_heff) f_right ...) k_1 ...) m)
        "continue3")
   (--> ((control (fst e) r (f ...) k ...) m)
        ((control e r (fir f ...) k ...) m)
        "first1")
   (--> ((return ((ret (v_1 \, v_2)) fir f ...) k ...) m)
        ((return ((ret v_1) f ...) k ...) m)
        "first2")
   (--> ((control (snd e) r (f ...) k ...) m)
        ((control e r (sec f ...) k ...) m)
        "second1")
   (--> ((return ((ret (v_1 \, v_2)) sec f ...) k ...) m)
        ((return ((ret v_2) f ...) k ...) m)
        "second2")
   (--> ((control (e_1 \, e_2) r (f ...) k ...) m)
        ((control e_1 r ((pair1 e_2 r) f ...) k ...) m)
        "pair1")
   (--> ((return ((ret v) (pair1 e r) f ...) k ...) m)
        ((control e r ((pair2 v) f ...) k ...) m)
        "pair2")
   (--> ((return ((ret v_2) (pair2 v_1) f ...) k ...) m)
        ((return ((ret (v_1 \, v_2)) f ...) k ...) m)
        "pair3")
   (--> ((control (e_1 \; e_2) r (f ...) k_1 ...) m)
        ((control e_1 r ((seq e_2 r) f ...) k_1 ...) m)
        "seq1")
   (--> ((return ((ret v) (seq e r) f ...) k_1 ...) m)
        ((control e r (f ...) k_1 ...) m)
        "seq2")
   (--> ((return ((ret v))) m)
        ((halt v) m)
        "threadHalt")
   (--> ((return ((ret v)) ((hdl v_hval v_heff) f ...) k_1 ...) m)
        ((return ((ret v) (fun v_hval) f ...) k_1 ...) m)
        "handleHalt")
   (--> ((return ((ret v)) (f ...) k_1 ...) m)
        ((return ((ret v) f ...) k_1 ...) m)
        (side-condition (not (term (starts-with-hdl (f ...)))))
        "parasiteHalt")
   ))

(define-metafunction Ev
  var-lookup : r x -> v
  [(var-lookup (ρ (x v) (x_1 v_1) ...) x)
   v]
  [(var-lookup (ρ (x_0 v_0) (x_1 v_1) ...) x)
   (var-lookup (ρ (x_1 v_1) ...) x)])

(define-metafunction Ev
  ref-exists : m x -> boolean
  [(ref-exists ((x v) (x_1 v_1) ...) x) #t]
  [(ref-exists () x) #f]
  [(ref-exists ((x_0 v_0) (x_1 v_1) ...) x)
   (ref-exists ((x_1 v_1) ...) x)])

(define-metafunction Ev
  starts-with-hdl : k -> boolean
  [(starts-with-hdl ((hdl v_1 v_2) f ...)) #t]
  [(starts-with-hdl (f ...)) #f])

(define-metafunction Ev
  deterministic : p -> boolean
  [(deterministic p) (match (apply-reduction-relation red (term p))
                       [() #t]
                       [(p_next) (term (deterministic p_next))]
                       [() #f])])

(define (is_deterministic p)
  (let ([next
         (apply-reduction-relation red p)])
    (cond
      [(empty? next) #t]
      [(equal? (length next) 1)
       (andmap is_deterministic next)]
      [else #f])))

;(ref q_front unit)
;(ref q_rear unit)
;(ref enq (λ k (ref q_rear (k (deref q_rear)))))
;(ref deq (λ x (if unit (deref q_front) ((letrec rev () (rev unit)) \; (deq unit)) ((ref tmp (fst (deref q_front)) \; (ref q_front (snd (deref q_front))) \; (deref tmp))))))
#|
(traces red (term ((control ((ref q unit) \;
((ref deq (λ x (if (deref q) unit unit (continue ((ref tmp (fst (deref q))) \; ((ref q (snd (deref q))) \; (deref tmp))) unit)))) \;
((ref enq (λ x (ref q (x \, (deref q))))) \;

(letrec 
  spawn 
  (λ f 
    (handle f 
      (λ x ((deref deq) unit)) 
      (λ x 
        (if (fst (fst x)) 
        "Yield" 
        (((deref enq) (snd x)) \; ((deref deq) unit)) 
        (((deref enq) (snd x)) \; (spawn (snd (fst x)))))))) 
  (spawn ((ret unit))))))) (ρ) ()) ())))
|#
#|
(traces red (term
((control ((ref q unit) \;
((ref deq (λ x (if (deref q) unit unit
  (continue ((ref tmp (fst (deref q))) \;
    ((ref q (snd (deref q))) \;
      (deref tmp))) unit)))) \;
((ref enq (λ x (ref q (x \, (deref q))))) \;
((λ prog
  (letrec spawn 
  (λ f 
    (handle f 
      (λ x ((deref deq) unit)) 
      (λ x 
        (if (fst (fst x)) 
        "Yield" 
        (((deref enq) (snd x)) \;
            ((deref deq) unit)) 
        (((deref enq) (snd x)) \;
            (spawn (snd (fst x))))))))
  (spawn prog))))))))
())))

|#