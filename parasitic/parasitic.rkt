#lang racket
(require redex)

(define-language Par
  (e x
     v
     (e e)
     (spawn e)
     (parasite e)
     chan
     (send e e)
     (recv e))
  (v unit
     (λ x e r)
     c
     κ)
  (x variable-not-otherwise-mentioned)
  (r (ρ e))
  (c (ch x))
  (κ (const v))
  (n (e r k_0 k_1 ...))
  (k cont))

