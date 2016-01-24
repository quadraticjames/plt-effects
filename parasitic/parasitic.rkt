#lang racket
(require redex)

(define-language Pt
  (e x
     v
     (e e)
     (spawnHost e)
     (spawnParasite e)
     (attach e)
     (prepare e e)
     (reify e)
     (inflate e)
     chan
     (send e e)
     (recv e))
  (v unit
     (λ x e r)
     c
     κ
     k)
  (κ (const v))
  (c (ch x))
  (x variable-not-otherwise-mentioned)
  (t (th x))
  (r (ρ (x v) ...))
  (k (f ...))
  (n (e r k_0 k_1 ...))
  (f (ret v)
     (arg e x)
     (fun v)
     recv
     (sval e r)
     (send v)
     (rblk v)
     (sblk v_1 v_2)
     (pval e x)
     (prep v))
  (T (τ (t s) ...))
  (C (χ (c (k_0 ...) (k_1 ...)) ...))
  (s (control e r k_0 k_1 ...)
     (return k ...)
     (halt v)))

(define-extended-language Ev Pt
  (p (T C))
  (H (τ (t s) ... (t S) (t s) ...))
  (S s
     hole))

(define red
  (reduction-relation
   Ev
   #:domain p
   (--> ((in-hole H (control chan r (f ...) k_1 ...)) (χ (c_1 (k_2 ...) (k_3 ...)) ...))
        ((in-hole H (return ((ret (fresh c)) f ...) k_1 ...)) (χ c (c_1 (k_2 ...) (k_3 ...)) ...))
        "channel")
   (--> ((τ (t_left s_left) ...
            (t (control (spawnhost e) r (f ...) k ...))
            (t_right s_right) ...)
         C)
        ((τ (t_left s_left) ...
            (t (return ((ret unit) f ...) k ...))
            (t_right s_right) ...
            ((fresh t_1) (control e r)))
         C)
        "spawnhost")
   ))