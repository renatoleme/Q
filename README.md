# Q

> Um módulo simplificado dos números racionais para o Coq. Definições de tipo, operações e propriedades.

## Inteiros

Em primeiro lugar, definimos os inteiros como naturais assinalados. 

```coq
Inductive int :=
| Z : bool -> nat -> int.
```

Por convenção, estabelecemos que 

$$
\begin{align}
 +a = \text {Z true a}\\
 -a = \text {Z false a}
\end{align}
$$

onde $a$ é um número natural.

Para este tipo, definimos os seguintes métodos auxiliares. 

```coq
Definition abs (a : int) :=
  match a with
  | Z _ n => n
  end.

Definition signal (a : int) : bool :=
  match a with
  | Z b _ => b
  end.

Definition isZero (a : int) :=
  match a with
  | Z ab an =>
      match an with 
      | O => true
      | _ => false
    end
  end.
```

### Operações

Agora, definimos as operações aritméticas de soma, subtração e multiplicação. 

```coq
Definition mult_Z (a b : int) :=
  match a, b with
  | Z ab an, Z bb bn => Z (negb (xorb ab bb)) (an * bn)
  end.

Fixpoint sub_Z_aux 
  (a b : nat)
  :=
  match a, b with
  | O, O => Z true O
  | S n, O => Z true (S n)
  | O, S m => Z false (S m)
  | S n, S m => sub_Z_aux n m
  end.

Definition sub_Z (a b : int) :=
  match a, b with
  | Z ab an, Z bb bn =>
      if ab then
        if bb then
           sub_Z_aux an bn
        else
          Z true (an + bn)
      else
        if bb then
          Z false (an + bn)
        else
          sub_Z_aux bn an
   end.

Definition sum_Z (a b : int) :=
  match a, b with
  | Z ab an, Z bb bn =>
      if ab then
        if bb then
           Z true (an + bn)
        else
          sub_Z (Z true (abs a)) (Z true (abs b))
      else
        if bb then
          sub_Z (Z true (abs b)) (Z true (abs a))
        else
          Z false (an + bn)
  end.
```

#### Sinais iguais, multiplicação positiva

No que se segue, iremos demonstrar a seguinte propriedade.

> Sejam 'a' e 'b' dois números inteiros. 
> > Se o sinal de 'a' e 'b' são iguais, então a * b é positivo. 


```coq
Lemma signal_th :
  forall a b : int,
    signal (mult_Z a b) = (negb (xorb (signal a) (signal b))).
Proof.
  intros. unfold mult_Z. destruct a.
  - destruct b. 
    + reflexivity.
Qed. 

Lemma equal_positive :
  forall a b : int,
    signal a = signal b ->
    signal (mult_Z a b) = true.
Proof.
  intros. rewrite signal_th. rewrite H. 
  destruct b.
  - destruct b.
    + reflexivity.
    + reflexivity.
Qed.
```

## Racionais

```coq
Inductive rat :=
| undef
| Q : bool -> nat -> nat -> rat.

Definition q (a b : int) :=
  if isZero b then undef
  else
    match a, b with
    | Z ab an, Z bb bn =>
        Q (negb (xorb ab bb)) (abs a) (abs b)
    end.
```

Agora, podemos definir os números racionais. Por convenção, definimos

$$
\frac{a}{b} = \text {q a b}
$$

onde $a$ e $b$ são números inteiros, conforme definido acima.

Note que q é uma função que retorna **Q s a b** se, e somente se, $b \neq 0$. O sinal $s$ de $\frac{a}{b}$ é dado pela regra usual 

$$
(+ \frac{a}{b}) \Leftrightarrow signal (a) = signal(b) 
$$

### Exemplos

```coq
Definition q1 := q (Z false 7) (Z true 3). (* (- 7) / 3 = - (7 / 3) *)
Definition q2 := q (Z false 3) (Z false 13). (* (-3) / (-13) = 3 / 13 *) 
```

### Operações

```coq
Definition mult_Q_aux (a b : rat) :=
  match a with
  | undef => undef
  | Q ab a1 a2 => 
      match b with
      | undef => undef
      | Q bb b1 b2 =>
          Q (negb (xorb ab bb))
            (a1 * b1) (a2 * b2)
      end
  end.

Definition mult_Q (a b : rat) :=
  match (mult_Q_aux a b) with
  | undef => undef
  | Q ab a1 a2 =>
      if (Nat.eqb a2 0) then undef
      else Q ab a1 a2
  end.

Definition sum_Q (a b : rat) :=
  match a with
  | undef => undef
  | Q ab a1 a2 =>
      match b with
      | undef => undef
      | Q bb b1 b2 =>
          let aux :=
            (sum_Z
               (Z ab (mult b2 a1))
               (Z bb (mult a2 b1))) in
          Q (signal aux) (abs aux) (mult a2 b2)
      end
  end.

Definition sub_Q (a b : rat) :=
  match a with
  | undef => undef
  | Q ab a1 a2 =>
      match b with
      | undef => undef
      | Q bb b1 b2 =>
          let aux :=
            (sub_Z
               (Z ab (mult b2 a1))
               (Z bb (mult a2 b1))) in
          Q (signal aux) (abs aux) (mult a2 b2)
      end
  end.

Definition div_Q (a b : rat) :=
  match a with
  | undef => undef
  | Q ab a1 a2 =>
      match b with
      | undef => undef
      | Q bb b1 b2 =>
          mult_Q (Q ab a1 a2) (Q bb b2 b1)
      end
  end.
```

### Notações

```coq
Notation "- ( a | b )" := (Q false a b).
Notation "+ ( a | b )" := (Q true a b).
Notation "( a | b )" := (Q true a b). (* shorthand *)

Notation "a ⊗ b" := (mult_Q a b) (at level 50).
Notation "a ⊘ b" := (div_Q a b) (at level 51).
Notation "a ⊕ b" := (sum_Q a b) (at level 52).
Notation "a ⊖ b" := (sub_Q a b) (at level 53).
```

### Propriedades

```coq
(* Soma. *)

Theorem Q_sum_comm:
  forall a b, a ⊕ b = b ⊕ a.
Proof.
Admitted.

Theorem Q_sum_assoc:
  forall a b c, a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c.
Proof.
Admitted.

(* Multiplicação. *)

Theorem Q_mult_comm:
  forall a b, a ⊗ b = b ⊗ a.
Proof.
Admitted.

Theorem Q_mult_assoc:
  forall a b c, a ⊗ (b ⊗ c) = (a ⊗ b) ⊗ c.
Proof.
Admitted.
```