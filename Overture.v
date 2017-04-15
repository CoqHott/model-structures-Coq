Require Export MyTacs.


Notation idmap := (fun x => x).

Notation compose := (fun g f x => g (f x)).
Notation " g 'o' f " := (compose g f) (at level 40, left associativity) : core_scope.

Set Primitive Projections.
Record sigT {A} (P : A -> Type) := exist { π1 : A ; π2 : P π1 }.
Arguments exist {_} _ _ _.
Scheme sigT_rect := Induction for sigT Sort Type.

Notation "{ x & P }" := (sigT (fun x => P)) (only parsing) : type_scope.
Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) (only parsing) : type_scope.
Notation "'exists' x .. y , P"
  := (sigT (fun x => .. (sigT (fun y => P)) ..))
       (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "∃ x .. y , P"
  := (sigT (fun x => .. (sigT (fun y => P)) ..))
       (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "( x ; y )" := (exist _ x y) : core_scope.
Notation "( x ; y ; z )" := (x ; (y ; z)) : core_scope.
(* Notation "( x ; y ; .. ; z )" := (exist _ .. (exist _ x y) .. z) : core_scope. *)
Notation pr1 := (π1 _).
Notation pr2 := (π2 _).
Notation "x .1" := (π1 _ x) (at level 3, format "x '.1'") : core_scope.
Notation "x .2" := (π2 _ x) (at level 3, format "x '.2'") : core_scope.

Definition prod A B := sigT (fun _ : A => B).
Notation "A * B" := (prod A B) (at level 40, left associativity) : type_scope.
Notation "A × B" := (prod A B) (at level 90, right associativity) : type_scope.
Definition pair {A B} : A -> B -> A × B := fun x y => (x; y).
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Definition fst {A B} : A × B -> A := pr1.
Definition snd {A B} : A × B -> B := pr2.

Definition iff (A B : Type) := (A -> B) × (B -> A).
Notation "A <-> B" := (iff A B)%type : type_scope.

Definition transitive_iff {A B C}
  : A <-> B -> B <-> C -> A <-> C.
Proof.
  intros H1 H2. split; firstorder.
Defined.


Open Scope type_scope.

(* ********* Strict Eq ********* *)
Delimit Scope eq_scope with eq.
Open Scope eq_scope.

Local Unset Elimination Schemes.

Inductive Eq {A: Type} (a: A) : A -> Type :=
  refl : Eq a a.

Arguments refl {A a} , [A] a.

Scheme Eq_ind := Induction for Eq Sort Type.
Arguments Eq_ind [A] a P f y e.
Scheme Eq_rec := Minimality for Eq Sort Type.
Arguments Eq_rec [A] a P f y e.

Notation "x ≡ y :> A"
  := (@Eq A x y) (at level 70, y at next level, no associativity) : type_scope.
Notation "x ≡ y"
  := (@Eq _ x y) (at level 70, no associativity) : type_scope.

Axiom Eq_UIP : forall {A: Type} {x y: A} (p q: x ≡ y), p ≡ q.

Lemma Eq_rew A a y P (X : P a) (H : a ≡ y :> A) : P y.
Proof. rewrite <- H. assumption. Defined.

Lemma Eq_rew_r A a y P (X : P y) (H : a ≡ y :> A) : P a.
Proof. rewrite H. assumption. Defined.

Bind Scope eq_scope with Eq.

Definition Einverse {A : Type} {x y : A} (p : x ≡ y) : y ≡ x.
  symmetry; assumption.
Defined.
Arguments Einverse {A x y} p : simpl nomatch.

Definition Econcat {A : Type} {x y z : A} (p : x ≡ y) (q : y ≡ z) : x ≡ z :=
  match p, q with refl, refl => refl end.
Arguments Econcat {A x y z} p q : simpl nomatch.

Notation "'E1'" := refl : eq_scope.
Notation "p E@ q" := (Econcat p%eq q%eq) (at level 20) : eq_scope.
Notation "p ^E" := (Einverse p%eq) (at level 3, format "p '^E'") : eq_scope.

Definition Etransport {A : Type} (P : A -> Type) {x y : A} (p : x ≡ y) (u : P x) : P y :=
  match p with refl => u end.
Arguments Etransport {A}%type_scope P {x y} p%eq_scope u : simpl nomatch.

Notation "p E# x"
  := (Etransport _ p x) (right associativity, at level 65, only parsing) : eq_scope.

Notation "f ≡≡ g" := (forall x, f x ≡ g x) (at level 70, no associativity) : type_scope.

Definition Eap {A B:Type} (f:A -> B) {x y:A} (p:x ≡ y) : f x ≡ f y
  := match p with refl => refl end.
Global Arguments Eap {A B}%type_scope f {x y} p%eq_scope.

Definition EapD10 {A} {B: A -> Type} {f g: forall x, B x} (h: f ≡ g)
  : f ≡≡ g
  := fun x => match h with refl => E1 end.
Global Arguments EapD10 {A%type_scope B} {f g} h%eq_scope _.

Definition Eap10 {A B} {f g: A -> B} (h: f ≡ g) : f ≡≡ g
  := EapD10 h.
Global Arguments Eap10 {A B}%type_scope {f g} h%eq_scope _.

Axiom eq_funext: forall {A: Type} {P : A -> Type} {f g : forall x : A, P x},
    f ≡≡ g -> f ≡ g.