In this repository, I am modeling PCF (programmable computable functions, Plotkin 1977) with **list** and **def**. 

Here are the list of subtle (or non-subtle) problems my redex model had which I want to remember:

1. **binding-forms** clause must come last in your syntax.

```racket
#:binding-forms             
 (λ (x T) e #:refers-to x)
```
The explanation behind this rule is that the grammars that come after #:binding-forms are considered as binding-forms.

2. what is more general type environment? · or Γ?

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

So this was my judgments for constants (that does not need further computation). My intuition was wrong (again). Since · is a form of Γ, Γ includes · and thus more general. Some of failed tests succeeded after changing empty to gamma.

```racket
[--------------- "T-TRUE"
   (⊢_e Γ tt Bool)]

  [--------------- "T-FALSE"
   (⊢_e Γ ff Bool)]

  [------------- "T-NUM"
   (⊢_e Γ n Num)]
```

3. T-VAR, misunderstood.

```racket
[
  ----------------------------------------------------- "T-VAR"
  (⊢_e (Γ (x T) ... (x_1 T_1) (x_!_1 T_2) ...) x_1 T_1)]
```

4. More to come ....
