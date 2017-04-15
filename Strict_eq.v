Require Import Overture.

Definition EapD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x≡y):
  p E# (f x) ≡ f y
  :=
  match p with refl => refl end.
Arguments EapD {A%type_scope B} f {x y} p%eq_scope : simpl nomatch.

Definition Etransport_Vp {A: Type} (P: A -> Type) {x y: A} (p: x ≡ y) (z: P x)
  : p^E E# p E# z ≡ z.
Proof.
  destruct p; reflexivity.
Defined.

Definition Etransport_compose {A B : Type} {x y : A} (P : B -> Type) (f : A -> B) 
           (p : x ≡ y) (z : P (f x)) :
  Etransport (fun x0 : A => P (f x0)) p z ≡ Etransport P (Eap f p) z.
destruct p. reflexivity.
Defined.


Definition eq_sigma {A: Type} (P: A -> Type) {x x': A} {y: P x} {y': P x'}
           (p: x ≡ x') (q: p E# y ≡ y')
  : (x; y) ≡ (x'; y').
Proof.
  destruct p, q; reflexivity.
Defined.

Definition Etransport_sigma' {A B : Type} {C : A -> B -> Type}
           {x1 x2 : A} (p : x1 ≡ x2) yz
: Etransport (fun x => sigT (C x)) p yz ≡
  (yz.1 ; Etransport (fun x => C x yz.1) p yz.2).
Proof.
  destruct p. destruct yz. reflexivity.
Defined.

Definition pr1_eq {A : Type} `{P : A -> Type} {u v : sigT P} (p : u ≡ v)
  : u.1 ≡ v.1
  := Eap pr1 p.

Notation "p ..1E" := (pr1_eq p) (at level 3).

Definition pr2_eq {A : Type} `{P : A -> Type} {u v : sigT P} (p : u ≡ v)
  : p..1E E# u.2 ≡ v.2
  := (Etransport_compose P pr1 p u.2)^E
     E@ (@EapD { x & P x} _ pr2 _ _ p).

Notation "p ..2E" := (pr2_eq p) (at level 3).