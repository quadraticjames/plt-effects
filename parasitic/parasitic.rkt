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
   (--> ((in-hole H (control chan r k_0 k_1 ...)) C)
        ((in-hole H (return ((ret c)) k_0 k_1 ...)) C))))