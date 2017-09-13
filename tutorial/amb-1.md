### 1 Amb: A Redex Tutorial

## 1.1 Defining a language

```racket
#lang racket
(require redex)

(define-language L
  (e (e e)
     (λ (x t) e)
     x
     (amb e ...)
     number
     (+ e ...)
     (if0 e e e)
     (fix e))
  (t (→ t t) num)
  (x variable-not-otherwise-mentioned))
```

**Exercise 1**

Use *redex-match* to extract the body of the λ expression from this object-language program:
```racket
((λ (x num) (+ x 1))
 17)
```

*Answer*
```racket
(redex-match
  L
  ((λ (x t) e_1) e_2)
   (term ((λ (x num) (+ x 1))
 17)))   

(list (match (list (bind 'e_1 '(+ x 1)) (bind 'e_2 17) (bind 't 'num) (bind 'x 'x))))
```


**Exercise 2**

Use *redex-match to extract the range portion of the type (→ num (→ num num)).

*Answer*
```racket
(redex-match
  L
  (→ num t)
  (term (→ num (→ num num))))

(list (match (list (bind 't '(→ num num)))))
```

**Exercise 3**

Redex’s pattern language supports ambiguity through non-terminals, the *in-hole* pattern, and ellipsis placement (as in the example just above). Use the latter source of ambiguity to design a pattern that matches one way for each adjacent pair of expressions in a sequence. That is, if you match the sequence *(1 2 3 4)*, then you’d expect one match for 1 & 2, one match for 2 & 3, and one match for 3 & 4. In general, this pattern should produce n matches when there are n+1 expressions in the sequence.

To test your solution use redex-match like this:
```racket
(redex-match
 L
  ; your solution goes here
 (term (1 2 3 4)))
where you expect a result like this
(list
 (match (list (bind 'e_1 1) (bind 'e_2 2)))
 (match (list (bind 'e_1 2) (bind 'e_2 3)))
 (match (list (bind 'e_1 3) (bind 'e_2 4))))
 ```
but possibly with more pattern variables in the resulting match.

*Answer*
```racket
(redex-match
  L
  (_ ... e_1 e_2 _ ...)
  (term (1 2 3 4)))
```

**Exercise 4**

The ellipsis pattern can also be “named” via subscripts that, when duplicated, force the lengths of the corresponding sequences to match. For example, the pattern
```racket
((λ (x ...) e) v ...)
```

matches application expressions where the function may have a different arity than the number of arguments it receives, but the pattern:
```racket
((λ (x ..._1) e) v ..._1)
```

ensures that the number of xs is the same as the number of vs.
Use this facility to write a pattern that matches odd length lists of expressions, returning one match for each pair of expressions that are equidistant from the ends of the sequence. For example, if matching the sequence *(1 2 3 4 5)*, there would be two matches, one for the pair 1 & 5 and another for the pair 2 & 4. Your match should include the bindings *e_left* and *e_right* that extract these pairs (one element of the pair bound to *e_left* and the other to *e_right*). Test your pattern with *redex-match*.


*Answer*
```racket
(redex-match
  L
  (_ ..._1 e_left _ ... e_right _ ..._1)
  (term (1 2 3 4 5)))

(list
 (match (list (bind 'e_left 1) (bind 'e_right 5)))
 (match (list (bind 'e_left 2) (bind 'e_right 4))))
```
## 1.2 Typing

```racket
(define-extended-language L+Γ L
  [Γ · (x : t Γ)])
```

```racket
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

  [(types Γ e num) ...
   --------------------------
   (types Γ (amb e ...) num)])
   ```

## 1.3 Testing Typing

```racket
> (judgment-holds
   (types ·
          ((λ (x num) (amb x 1))
           (+ 1 2))
          t)
   t)
'(num)
```

```racket
> (judgment-holds
   (types ·
          (λ (f (→ num (→ num num))) (f (amb 1 2)))
          (→ t_1 t_2))
   t_2)
'((→ num num))
```

**Exercise 5**

Remove the *different* side-condition and demonstrate how one expression now has multiple types, using judgment-holds. That is, find a use of *judgment-holds* that returns a list of length two, with two different types in it.

*Answer*

```racket
Exercise 5
> (judgment-holds
   (types (x : bool (x : num ·))
          x
          t)
   t)
'(bool num)
```
