(** 
  Rational library. 
  Definitions, arithmetics and properties.
**)

(** 

Em primeiro lugar, definimos os inteiros como naturais assinalados. Por convenção, estabelecemos que 

  +a = Z true a
  -a = Z false a

onde a é um número natural.

**)

Inductive int :=
| Z : bool -> nat -> int.

(** Para este tipo, definimos os seguintes métodos auxiliares. **)

Definition abs (a : int) :=
  match a with
  | Z _ n => n
  end.

Definition signal (a : int) : bool :=
  match a with
  | Z b _ => b
  end.

(**

  Agora, definimos as operações aritméticas de soma, subtração e multiplicação. 

**)

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
           (* a - b *)
           sub_Z_aux an bn
        else
          (* a - (- b) = a + b*)
          Z true (an + bn)
      else
        if bb then
          (* - a - b *)
          Z false (an + bn)
        else
          (* - a - (- b) = b - a *)
          sub_Z_aux bn an
   end.

Definition sum_Z (a b : int) :=
  match a, b with
  | Z ab an, Z bb bn =>
      if ab then
        if bb then
           (* a + b *)
           Z true (an + bn)
        else
          (* a + (- b) = a - b*)
          sub_Z (Z true (abs a)) (Z true (abs b))
      else
        if bb then
          (* - a + b = b - a*)
          sub_Z (Z true (abs b)) (Z true (abs a))
        else
          (* - a + (- b) = - a - b *)
          Z false (an + bn)
  end.

Compute sum_Z (Z true 2) (Z true 3).

(** Função auxiliar. **)

Definition isZero (a : int) :=
  match a with
  | Z ab an =>
      match an with 
      | O => true
      | _ => false
    end
  end.

(** 

   No que se segue, iremos demonstrar a seguinte propriedade.

   Sejam 'a' e 'b' dois números inteiros. 

   > Se o sinal de 'a' e 'b' são iguais, então a * b é positivo. 

**)

(** Lema auxiliar **)

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

(** [To-do] Volta. **)

Inductive rat :=
| undef
| Q : bool -> nat -> nat -> rat.

(** 

 Agora, podemos definir os números racionais. Por convenção, definimos

    (def) a/b = q a b

 onde a e b são números inteiros, conforme definido acima.

**)

Definition q (a b : int) :=
  if isZero b then undef
  else
    match a, b with
    | Z ab an, Z bb bn =>
        Q (negb (xorb ab bb)) (abs a) (abs b)
    end.

(**

 Note que q é uma função que retorna Q a b se, e somente se, b <> 0.

 O sinal de a/b é dado pela regra usual 

 > (+ a/b) sse sinal de 'a' é igual ao sinal de 'b'. 

**)

(** exemplos **)
Definition q1 := q (Z false 7) (Z true 3).
Definition q2 := q (Z false 3) (Z false 13).

Compute q1.

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

(* exemplos *)
Compute mult_Q q1 q2.

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

(** exemplos **)
Definition q3 := Q false 2 4.
Definition q4 := Q true 1 10.

Definition q5 := Q true 2 4.
Definition q6 := Q false 1 10.

Definition q7 := Q true 2 4.
Definition q8 := Q true 1 10.

Definition q9 := Q false 2 4.
Definition q10 := Q false 1 10.

Compute q3.
Compute sum_Q q9 q10.

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

Compute sub_Z (Z true 20) (Z true 4).

Compute sub_Q q3 q4.
Compute sub_Q q5 q6.
Compute sub_Q q7 q8.
Compute sub_Q q9 q10.

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

(**

Algumas notações uteis.

**)

Notation "- ( a | b )" := (Q false a b).
Notation "+ ( a | b )" := (Q true a b).
Notation "( a | b )" := (Q true a b). (* shorthand *)

Notation "a ⊗ b" := (mult_Q a b) (at level 50).
Notation "a ⊕ b" := (sum_Q a b) (at level 51).
Notation "a ⊖ b" := (sub_Q a b) (at level 52).
Notation "a ⊘ b" := (div_Q a b) (at level 52).

Compute q1.
Compute q2.

Compute q2 ⊕ q1.
Compute q2 ⊗ q1.
Compute q2 ⊖ q1.
Compute q2 ⊘ q2.
