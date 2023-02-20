(* 
  Rational library. 
  Definitions, arithmetics and properties.
*)

(* 

Em primeiro lugar, definimos os inteiros como naturais assinalados. Por convenção, estabelecemos que 

  +a = Z true a
  -a = Z false a

onde a é um número natural.

*)

Inductive int :=
| Z : bool -> nat -> int.

(* Para este tipo, definimos os seguintes métodos auxiliares. *)

Definition abs (a : int) :=
  match a with
  | Z _ n => n
  end.

Definition signal (a : int) : bool :=
  match a with
  | Z b _ => b
  end.

(* 

  Agora, definimos as operações aritméticas de soma, subtração e multiplicação. 

*)

Definition mult_Z (a b : int) :=
  match a, b with
  | Z ab an, Z bb bn => Z (negb (xorb ab bb)) (an * bn)
  end.

(* Lema auxiliar *)

Lemma signal_th :
  forall a b : int,
    signal (mult_Z a b) = (negb (xorb (signal a) (signal b))).
Proof.
  intros. unfold mult_Z. destruct a.
  - destruct b. 
    + reflexivity.
Qed. 

(* Se os sinais são iguais, então a multiplicação retorna um número positivo. *)

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

(* [To-do] Demonstrar a volta. *)

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
          sub_Z a b
      else
        if bb then
          (* - a + b = b - a*)
          sub_Z b a
        else
          (* - a + (- b) = - a - b *)
          Z false (an + bn)
   end.

Compute mult_Z (Z true 2) (Z false 10).

(* 

Agora, podemos definir os números racionais. Por convenção, definimos

(def) a/b = Q a b

onde a e b são números inteiros, conforme definido acima.

Além disso, diremos que a/b é undef sse b = 0.
 
*)

Inductive rat :=
| undef
| Q : int -> int -> rat.

Definition isZero (a : int) :=
  match a with
  | Z ab an =>
      match an with 
      | O => true
      | _ => false
    end
  end.

Definition q (a b : int) :=
  if isZero b then undef
  else Q a b.

Compute q (Z true 2) (Z false 123).

Definition mult_Q (a b : rat) :=
  match a with
  | undef => undef
  | Q a1 a2 => 
      match b with
      | undef => undef
      | Q b1 b2 => q (mult_Z a1 b1) (mult_Z a2 b2)
      end
  end.

Definition sum_Q (a b : rat) :=
  match a with
  | undef => undef
  | Q a1 a2 =>
      match b with
      | undef => undef
      | Q b1 b2 => 
          q (sum_Z (mult_Z b2 a1) (mult_Z a2 b1))
            (mult_Z a2 b2)
      end
  end.

Definition q1 := q (Z false 2) (Z false 4).
Definition q2 := q (Z false 1) (Z false 10).

Compute sum_Q q1 q2.
Compute mult_Q q1 q2.

