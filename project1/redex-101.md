I am a new CS phd student at Northeastern University. My focus is pl. My background is three years of core cs undergrad courses and some grad courses at Iowa State and University of Hawaii, and two plmws, two oplsses, for external learning experience. No research experience.

Now I am on my first research project with Matthias Felleisen and Amal Ahmed. We want to explore compiled components from call-by-value and call-by-name languages and remedy any problems arising from the interactions between them using linking types.

First phase of my project is to model PCF (programmable computable functions, Plotkin 1977) with **list** and **def**. Since we modeled PCF at *redex summer school*, I jumped right into writing down the syntax. Then I realized our PCF didn't have types. So with Matthias's advice to look at redex manual for adding types to my PCF-list language, I started a redex tutorial (https://docs.racket-lang.org/redex/tutorial.html). It seemed going well, until I started testing my language.

Here are the list of subtle (or non-subtle, if you are more experience language designer) problems my naive language had:

1. **binding-forms** clause must come last in your syntax.

```racket
#:binding-forms             
 (λ (x T) e #:refers-to x)
```

2. For definitions that you want to use in your expression, a wrapper, a **program** here, is a good idea for scoping and typing.

```racket
;; Programs
(p (prog d ... e))
;; Defs
(d (def (x T) v))
```

But now you need a typing judgment for programs separately from expressions, which "calls" judgments for expressions in antecedents.

```racket
(define-judgment-form PCF-list
  #:mode (⊢_p I I O)
  #:contract (⊢_p Γ p T)
  [(⊢_e (Γ (x_1 T_1) ...) v_1 T_1)
   ...
   (⊢_e (Γ (x_1 T_1) ...) e T)
   ------------------------------------------ "T-PROG"
   (⊢_p Γ (prog (def (x_1 T_1) v_1) ... e) T)]
)
```

3. what is more general type environment? · or Γ?

```racket
(Γ ·
   (Γ (x T) ...))
```

This is my type environment. My intuition was defining judgment using · (the empty environment) is more general in that you don't need anything!

```racket
[--------------- "T-TRUE"
   (⊢_e · tt Bool)]

  [--------------- "T-FALSE"
   (⊢_e · ff Bool)]

  [------------- "T-NUM"
   (⊢_e · n Num)]
```

So this was my judgments for constants (that does not need further computation). More often than not, my intuition was wrong. Since · is a form of Γ, Γ includes · and thus more general. Some of failed tests succeeded after changing empty to gamma.

```racket
[--------------- "T-TRUE"
   (⊢_e Γ tt Bool)]

  [--------------- "T-FALSE"
   (⊢_e Γ ff Bool)]

  [------------- "T-NUM"
   (⊢_e Γ n Num)]
```

4. T-VAR, misunderstood.

```racket
[
  ----------------------------------------------------- "T-VAR"
  (⊢_e (Γ (x T) ... (x_1 T_1) (x_!_1 T_2) ...) x_1 T_1)]
```

5. ....
