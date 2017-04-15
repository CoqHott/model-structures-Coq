Require Import Overture.
Set Universe Polymorphism.

Set Implicit Arguments.
Generalizable All Variables.


Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Local Open Scope morphism_scope.

Reserved Notation "f ∘ g" (at level 40, left associativity).

Record Category : Type :=
  Build_Category' {
      object :> Type;
      morphism : object -> object -> Type;

      identity : forall x, morphism x x;
      compose : forall s d d',
          morphism d d'
          -> morphism s d
          -> morphism s d'
      where "f ∘ g" := (compose f g);

      associativity : forall x1 x2 x3 x4
                             (m1 : morphism x1 x2)
                             (m2 : morphism x2 x3)
                             (m3 : morphism x3 x4),
          (m3 ∘ m2) ∘ m1 ≡ m3 ∘ (m2 ∘ m1);

      associativity_sym : forall x1 x2 x3 x4
                                 (m1 : morphism x1 x2)
                                 (m2 : morphism x2 x3)
                                 (m3 : morphism x3 x4),
          m3 ∘ (m2 ∘ m1) ≡ (m3 ∘ m2) ∘ m1;

      left_identity : forall a b (f : morphism a b), identity b ∘ f ≡ f;
      right_identity : forall a b (f : morphism a b), f ∘ identity a ≡ f;

      identity_identity : forall x, identity x ∘ identity x ≡ identity x
    }.

Bind Scope category_scope with Category.
Bind Scope object_scope with object.
Bind Scope morphism_scope with morphism.

Arguments object !C%category / : rename.
Arguments morphism !C%category / s d : rename.
Arguments identity {!C%category} / x%object : rename.
Arguments compose {!C%category} / {s d d'}%object (m1 m2)%morphism : rename.

Global Infix "∘" := compose : morphism_scope.
Global Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
Global Notation "1" := (identity _) : morphism_scope.

Definition Build_Category
           object morphism compose identity
           associativity left_identity right_identity
  := @Build_Category'
       object
       morphism
       compose
       identity
       associativity
       (fun _ _ _ _ _ _ _ => Einverse (associativity _ _ _ _ _ _ _))
       left_identity
       right_identity
       (fun _ => left_identity _ _ _).


Definition TYPE : Category.
Proof.
  rapply Build_Category.
  - exact Type.
  - exact (λ A B, A -> B).
  - exact (λ A, idmap).
  - exact (λ A B C g f, g o f).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

(* Lifting property between f and g *)
Definition LP {C: Category} {x y: C} (f: x --> y) {x' y': C} (g: x' --> y')
  := ∀ (F: x --> x') (G: y --> y'), g ∘ F ≡ G ∘ f -> ∃ (Ɣ: y --> x'), (Ɣ ∘ f ≡ F) × (g ∘ Ɣ ≡ G).

Definition LLP {C: Category} (R: ∀ {x y: C}, (x --> y) -> Type) {x y: C} (f: x --> y)
  := ∀ x' y' (g: x' --> y'), R g -> LP f g.

Definition RLP {C: Category} (L: ∀ {x y: C}, (x --> y) -> Type) {x' y': C} (g: x' --> y')
  := ∀ x y (f: x --> y), L f -> LP f g.

Definition LLP_functor {C: Category} (R R': ∀ {x y: C}, (x --> y) -> Type)
           (RR': ∀ x y (f: x --> y), R f -> R' f)
           {x y: C} (f: x --> y)
  : LLP (@R') f -> LLP (@R) f.
Proof.
  intros H x' y' g Hg. apply H. apply RR'; assumption.
Defined.

Definition RLP_functor {C: Category} (L L': ∀ {x y: C}, (x --> y) -> Type)
           (LL': ∀ x y (f: x --> y), L f -> L' f)
           {x y: C} (f: x --> y)
  : RLP (@L') f -> RLP (@L) f.
Proof.
  intros H x' y' g Hg. apply H. apply LL'; assumption.
Defined.

Record weak_factorization_system {C: Category} (L R: ∀ {x y: C}, (x --> y) -> Type) :=
  { facto: ∀ (x z: C) (f: x --> z),
      ∃ y (g: x --> y) (h: y --> z), (h ∘ g ≡ f) × L g × R h;
    LLP_R: ∀ (x y: C) (f: x --> y), L f <-> LLP (@R) f;
    RLP_L: ∀ (x y: C) (f: x --> y), R f <-> RLP (@L) f
  }.

Definition wfs_iff_R {C: Category} (L R R': ∀ {x y: C}, (x --> y) -> Type)
           (H: ∀ x y (f: x --> y), R f <-> R' f)
           (W: weak_factorization_system (@L) (@R))
  : weak_factorization_system (@L) (@R').
Proof.
  destruct W. use Build_weak_factorization_system.
  - intros x z f. destruct (facto0 x z f) as [y [g [h [H1 [H2 H3]]]]].
    ref (y; (g; h; (H1, (H2, _)))). now apply H.
  - intros x y f; split; intro H1.
    + eapply LLP_functor. apply H.
      apply LLP_R0. assumption.
    + apply LLP_R0. eapply LLP_functor.
      apply H. assumption.
  - intros x y f; split; intro H1.
    + apply RLP_L0. apply H. assumption.
    + apply H. eapply RLP_L0. assumption.
Defined.      
  

Definition wfs_iff_L {C: Category} (L L' R: ∀ {x y: C}, (x --> y) -> Type)
           (H: ∀ x y (f: x --> y), L f <-> L' f)
           (W: weak_factorization_system (@L) (@R))
  : weak_factorization_system (@L') (@R).
Proof.
  destruct W. use Build_weak_factorization_system.
  - intros x z f. destruct (facto0 x z f) as [y [g [h [H1 [H2 H3]]]]].
    ref (y; (g; h; (H1, (_, H3)))). now apply H.
  - intros x y f; split; intro H1.
    + apply LLP_R0. apply H. assumption.
    + apply H. eapply LLP_R0. assumption.
  - intros x y f; split; intro H1.
    + eapply RLP_functor. apply H.
      apply RLP_L0. assumption.
    + apply RLP_L0. eapply RLP_functor.
      apply H. assumption.
Defined.      


Definition two_out_of_three {C: Category} (W: ∀ {x y: C}, (x --> y) -> Type)
  := ∀ (x y z: C) (f: x --> y) (g: y --> z),
    (W f -> W g -> W (g ∘ f)) × (W g -> W (g ∘ f) -> W f) × (W (g ∘ f) -> W f -> W g).

Record model_structure (C: Category) :=
  { W: ∀ {x y: C}, (x --> y) -> Type;
    F: ∀ {x y: C}, (x --> y) -> Type;
    C: ∀ {x y: C}, (x --> y) -> Type;
    tot: two_out_of_three (@W);
    C_AF: weak_factorization_system (@C) (λ x y f, W f × F f);
    AC_F: weak_factorization_system (λ x y f, W f × C f) (@F)
  }.