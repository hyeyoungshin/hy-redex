
**Theorem (Progress) : Suppose $e$ is a well-typed term. Then either $e$ is a value or else there is $e'$ with $e \rightarrow e'$.**

```racket
;; Typing judgment for c-b-v cons
[(⊢_e Γ e_1 T_1)
   (⊢_e Γ e_2 (List T_1))
   --------------------------------- "T-CONS"
   (⊢_e Γ (cons e_1 e_2) (List T_1))]

;; Eval-context for c-b-v cons
   (E-value ...
           (cons E-value e)
           (cons v E-value)
           ...
```

*proof.* By induction on a derivation of $e:T$.

(other cases are skipped)

**Case T-CONS**:

$e$ = $\text{cons } e_1 e_2 : \text{List } T$  

$e_1 : T$, $e_2 : \text{List } T$

By induction hypothesis, either $e_1$ is a value or there exists $e'$ such that $e \rightarrow e'$. Similarly, $e_2$ is either a value or steps to $e_2'$

If $e_1$ is a value and $e_2$ is a value, $e$ is a value by:

```racket
  (v .... (cons v v))
```
If $e_1$ is a value and $e_2$ steps to $e_2'$, $e$ steps to $e' = \text{cons } e_1 e_2'$ by eval-context:

```racket
(E-value ...
        (cons v E-value)
        ...)
```

If $e_1$ steps to $e_1'$, then $e$ steps to $\text{cons } e_1' e_2$ by eval-context:

```racket
(E-value ...
        (cons E-value e)
        ...)
```

We showed in each case, $e$ is either a value or $e \rightarrow e'$. $\square$


**Theorem (Preservation) : If $e : T$ and $e \rightarrow e'$, then $e' : T$.**

*proof.* By induction on derivation of $e:T$.

(other cases are skipped)

**Case T-CONS**:

$e = \text{cons } e_1 e_2 : \text{List } T$

$e_1 : T$, $e_2 : \text{List } T$

If the last rule in the derivation is **T_CONS**, then we know from the form of this rule that $e$ must have the form $\text{cons } e_1 e_2$ for some e_1 and e_2.

We must also have subderivations with conclusions $e_1 : T$ and $e_2: \text{List } T$. Now looking at the eval-context, we find that there are two rules by which $e \rightarrow e'$ can be derived.

```racket
   (E-value ...
           (cons E-value e)
           (cons v E-value)
           ...
```

* $\text{cons E-value } e$

Then $\text{cons } e_1 e_2 \rightarrow \text{cons } e_1' e_2$. We have a subderivation of the original typing whose conclusion is $e_1 : T$. We can apply the I.H. to this, obtaining $e_1' : T$. Combining this with the facts that $e_2 : \text{List } T$, we can apply the **T-CONS** rule that $\text{cons } e_1' e_2 : \text{List } T$.

* $\text{cons } v \text{ E-value}$

Then $\text{cons } e_1 e_2 \rightarrow \text{cons } e_1 e_2'$ and $e_1$ is a value. We have a subderivation of the original typing that $e_2 : \text{List } T$. By the I.H. $e_2' : \text{List } T$. Combining this with the facts that $e_1 : T$, we conclude that $\text{cons } e_1 e_2' : \text{List } T$. $\square$
