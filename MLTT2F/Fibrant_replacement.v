Require Import MLTT2F.Overture MLTT2F.Path_eq.
Set Universe Polymorphism.

Module Export FibrantReplacement.

  Private Inductive repl (X: Type) : Type :=
  | η : X -> repl X.

  Arguments η {_} _.
  
  Axiom Fibrant_repl : forall X, Fibrant (repl X).
  
  Definition repl_ind {X} (P: repl X -> Type) {FibP: FibrantF P}
             (H: forall x : X, P (η x))
    : forall z, P z.
  Proof.
    destruct z. apply H.
  Defined.
End FibrantReplacement.

Definition repl_rec {X P} {FibP: Fibrant P} (H: X -> P)
  : repl X -> P
  := repl_ind (λ _ : repl X, P) H.


Axiom FibrantF_repl_rec : ∀ A (P: A -> Type) {FibP: FibrantF P},
    FibrantF (repl_rec P).
  
Definition repl_sigma {A} (B: repl A -> Type) {FibB: FibrantF B}
  : sigT B -> repl (sigT (B o η)).
Proof.
  intros [x y]; revert x y.
  use repl_ind; cbn. intros x y. exact (η (x; y)).
Defined.

Definition repl_J' {A} {x: A} (P: (∃ y: A, η x = η y) -> Type)
           {FibP: FibrantF P}
           {y: A} (p: η x = η y)
  : P (x; 1) -> P (y; p).
Proof.
  transparent assert (P' : ((∃ z, η x = z) → Type)). {
    refine (_ o repl_sigma (λ z, η x = z)).
    use repl_rec. exact P. }
  change (P' (η x; 1) -> P' (η y; p)).
  intro u; refine (paths_rec (η x; 1) P' u (η y; p) _).
  subst P'. classes.
  ref (path_sigma (λ z, η x = z) p _).
  exact (transport_paths_r _ p 1 @ concat_1p p).
Defined.
  
Definition repl_J {A} {x: A} (P: ∀ (y: A), η x = η y -> Type)
           {H: FibrantF (λ w: ∃ y, η x = η y, P w.1 w.2)}
           {y: A} (p: η x = η y)
  : P x 1 -> P y p.
Proof.
  ref (repl_J' (λ w, P w.1 w.2) p).
Defined.


Definition repl_f {A B} (f: A -> B) : repl A -> repl B
  := repl_rec (η o f).

Axiom repl_f_compose : forall {A B C} (f: A -> B) (g: B -> C), repl_f g o repl_f f ≡≡ repl_f (g o f).

Axiom repl_f_idmap : forall {A}, repl_f (λ x: A, x) ≡≡ idmap.
