Require Import MLTT2.Overture MLTT2.Path_eq.

Generalizable All Variables.

Module Export CylinderHIT.
  Private Inductive Cyl {X Y} (f: X -> Y) : Y -> Type :=
    | top : forall x, Cyl f (f x)
    | base : forall y, Cyl f y.

  Axiom cyl_eq : forall {X Y} {f: X -> Y}, (base f) o f == top f.

  Global Arguments top {X Y f} x.
  Global Arguments base {X Y f} y.
  
  Axiom Fibrant_Cyl : forall {X Y} {FibX: Fibrant X} {FibY: Fibrant Y} {f: X -> Y}, FibrantF (Cyl f).

  Definition Cyl_ind {X Y} {FibX: Fibrant X} {FibY: Fibrant Y} {f: X -> Y}
             (P: forall y, Cyl f y -> Type) {FibP: FibrantF2 P}
             (top': forall x, P (f x) (top x))
             (base': forall y, P y (base y))
             (cyl_eq' : forall x, (cyl_eq x) # (base' (f x)) = top' x)
  : forall y (w: Cyl f y), P y w
    := fun y w => match w with
                  | top x => top' x
                  | base x => base' x
                end.
End CylinderHIT.


Section Cylinder.
  Context {X Y} {FibX: Fibrant X} {FibY: Fibrant Y} {f: X -> Y}.

  Definition Cyl_Contr (y: Y) : Contr (Cyl f y).
  Proof.
    exists (base y).
    revert y. ref (Cyl_ind (fun y x => base y = x) _ _ _).
    - exact cyl_eq.
    - intro. exact 1.
    - intros x; cbn.
      ref (transport_paths_r (x:= base (f x)) _ (cyl_eq x) 1 @ _).
      exact (concat_1p _).
  Defined.

  (* ∃ y, Cyl f y  is the homotopy pushout of f and idmap *)
  Definition sig_cyl_ind (P: sigT (Cyl f) -> Type) {FibP: FibrantF P}
             (top': forall x, P (f x; top x))
             (base': forall y, P (y; base y))
             (cyl_eq': forall x,
                 transport (λ w, P (f x; w)) (cyl_eq x) (base' (f x)) = top' x)
    : forall w, P w.
  Proof.
    intros [y w].
    exact (Cyl_ind (λ y w, P (y; w)) top' base' cyl_eq' y w).
  Defined.

  Definition sig_cyl_rec P {FibP: Fibrant P}
             (top': X -> P) (base': Y -> P)
             (cyl_eq': forall x, base' (f x) = top' x)
    : (sigT (Cyl f)) -> P.
  Proof.
    intros [y w].
    ref (Cyl_ind (λ y w, P) top' base' _ y w); cbn.
    intro x. exact (transport_const _ _ @ cyl_eq' _).
  Defined.
End Cylinder.