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
  (f (ret v)
     (arg e x)
     (fun v)
     recv
     (sval e r)
     (send v)
     (rblk v)
     (sblk c v)
     (pval e x)
     (prep v))
  (T (τ (t s) ...))
  (m (c (k_0 ...) (k_1 ...)))
  (C (χ m ...))
  (s (control e r k_0 k_1 ...)
     (return k ...)
     (halt v)))

(define-extended-language Ev Pt
  (p (T C))
  (H (τ (t s) ... (t S) (t s) ...))
  (S s
     hole)
  (N (χ m ... M m ...))
  (M (c (k_0 ...) (k_1 ...))
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
            ((fresh t_1) (control e r ())))
         C)
        "spawnhost")
   (--> ((τ (t_left s_left) ...
            (t (control (inflate e) r (f ...) k ...))
            (t_right s_right) ...)
         C)
        ((τ (t_left s_left) ...
            (t (return k ...))
            (t_right s_right) ...
            ((fresh t_1) (control e r (f ...))))
         C)
        "inflate")
   (--> ((in-hole H (return ((sblk c v) f ...) k ...))
         (in-hole N (c (k_1 ...) ())))
        ((in-hole H (return k ...))
         (in-hole N (c (k_1 ... ((sblk c v) f ...)) ())))
        "sendreify")
   (--> ((in-hole H (return ((rblk c) f ...) k ...))
         (in-hole N (c () (k_1 ...))))
        ((in-hole H (return k ...))
         (in-hole N (c () (k_1 ... ((rblk c) f ...)))))
        "recvreify")
   (--> ((in-hole H (return ((sblk c v) f_1 ...) k_1 ...))
         (in-hole N (c (k_s ...) (((rblk c) f_2 ...) k_r ...))))
        ((in-hole H (return (((ret v) f_2 ...) ((ret unit) f_1 ...) k_1 ...)))
         (in-hole N (c (k_s ...) (k_r ...))))
        "sendMatch")
   (--> ((in-hole H (return ((rblk c) f_1 ...) k_1 ...))
         (in-hole N (c (((sblk c v) f_2 ...) k_s ...) (k_r ...))))
        ((in-hole H (return ((ret unit) f_2 ...) ((ret v) f_1 ...) k_1 ...))
         (in-hole N (c (k_s ...) (k_r ...))))
        "recvMatch")
   (--> ((in-hole H (control κ r (f ...) k ...)) C)
        ((in-hole H (return ((ret κ) f ...) k ...)) C)
        "constant")
   (--> ((in-hole H (control x r (f ...) k ...)) C)
        ((in-hole H (return ((ret x) f ...) k ...)) C)
        "variable")
   (--> ((in-hole H (control (λ x e r) r (f ...) k ...)) C)
        ((in-hole H (return ((ret (λ x e r)) f ...) k ...)) C)
        "closure")
   (--> ((in-hole H (control (e_1 e_2) r (f ...) k ...)) C)
        ((in-hole H (control e_1 r ((arg e_2 r) f ...) k ...)) C)
        "application")
   (--> ((in-hole H (control (reify e) r k_0 k_1 ...)) C)
        ((in-hole H (control (e k_0) r () k_1 ...)) C)
        "reify")
   (--> ((in-hole H (control (send e_1 e_2) r (f ...) k ...)) C)
        ((in-hole H (control e_1 r ((sval e_2 r) f ...) k ...)) C)
        "send")
   (--> ((in-hole H (control (prepare e_1 e_2) r (f ...) k ...)) C)
        ((in-hole H (control e_1 r ((pval e_2 r) f ...) k ...)) C)
        "prepare")
   (--> ((in-hole H (control (recv e) r (f ...) k ...)) C)
        ((in-hole H (control e r (recv f ...) k ...)) C)
        "receive")
   (--> ((in-hole H (control (spawnParasite e) r (f ...) k ...)) C)
        ((in-hole H (control e r () ((ret unit) f ...) k ...)) C)
        "spawnParasite")
   ))

(define-metafunction Ev
  var-lookup : r x -> v
  [(var-lookup (ρ (x v) (x_1 v_1) ...) x)
   v]
  [(var-lookup (ρ (x_0 v_0) (x_1 v_1) ...) x)
   (var-lookup (ρ (x_1 v_1) ...) x)])
