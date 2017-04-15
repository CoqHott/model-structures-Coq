Require Import MLTT2.Overture MLTT2.Path_eq.

Record IsEquiv {A B} {FibA: Fibrant A} {FibB: Fibrant B} (f: A -> B) :=
  { equiv_inv : B -> A ;
    eisretr : f o equiv_inv == idmap;
    eissect : equiv_inv o f == idmap;
    eisadj :  ∀ x : A, eisretr (f x) = ap f (eissect x) }.

Arguments equiv_inv {_ _ _ _ _} _ _.
Arguments eisretr {_ _ _ _ _} _ _.
Arguments eissect {_ _ _ _ _} _ _.
Arguments eisadj {_ _ _ _ _} _ _.

Definition isequiv_adjointify {A B} {FibA: Fibrant A} {FibB: Fibrant B} {f: A -> B}
           (g: B -> A) : f o g == idmap -> g o f == idmap -> IsEquiv f.
Proof.
  intros isretr issect. use Build_IsEquiv.
  exact g. exact isretr.
  exact (λ x, ap g (ap f (issect x)^) @ ap g (isretr (f x)) @ issect x).
  intro a; cbn.
  apply moveR_M1.
  repeat (rew ap_pp; rew concat_p_pp); rew (ap_compose _ _ _)^.
  rew (concat_pA1 (fun b => (isretr b)^) (ap f (issect a)^)).
  repeat rew concat_pp_p; rew ap_V; apply moveL_Vp; rew concat_p1.
  rew concat_p_pp; rew (ap_compose _ _ _)^.
  rew (concat_pA1 (fun b => (isretr b)^) (isretr (f a))).
  rew concat_pV; rew concat_1p.
  exact 1.
Defined.
(* Qed. *)

Definition isequiv_compose {A B C} {FibA: Fibrant A} {FibB: Fibrant B} {FibC: Fibrant C}
           {f: A -> B} (Hf: IsEquiv f) {g: B -> C} (Hg: IsEquiv g)
  : IsEquiv (compose g f).
Proof.
  use isequiv_adjointify.
  exact ((equiv_inv Hf) o (equiv_inv Hg)).
  exact (fun c => ap g (eisretr _ (equiv_inv Hg c)) @ eisretr _ c).
  exact (fun a => ap _ (eissect _ (f a)) @ eissect _ a).
Defined.

Definition cancelR_isequiv {A B C} {FibA: Fibrant A} {FibB: Fibrant B} {FibC: Fibrant C}
           (f : A -> B) {g : B -> C}
           {Hf: IsEquiv f} {Hgf: IsEquiv (g o f)}
  : IsEquiv g.
Proof.
  use isequiv_adjointify.
  exact (f o (equiv_inv Hgf)).
  intro x; cbn. exact (eisretr Hgf x).
  intro x; cbn.
  ref (ap (λ x, f (equiv_inv Hgf (g x))) (eisretr Hf x)^ @ _).
  ref (ap f (eissect Hgf _) @ _).
  apply eisretr.
Defined.

Definition cancelL_isequiv {A B C} {FibA: Fibrant A} {FibB: Fibrant B} {FibC: Fibrant C}
           (g : B -> C) {f : A -> B}
           {Hg: IsEquiv g} {Hgf: IsEquiv (g o f)}
  : IsEquiv f.
Proof.
  use isequiv_adjointify.
  exact ((equiv_inv Hgf) o g).
  intro x; cbn.
  ref ((eissect Hg _)^ @ _).
  ref (ap (equiv_inv Hg) (eisretr Hgf _) @ _).
  apply eissect.
  intro x; cbn. exact (eissect Hgf x).
Defined.
