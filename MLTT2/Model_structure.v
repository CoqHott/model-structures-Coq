Require Import Category Strict_eq MLTT2.Overture MLTT2.Path_eq MLTT2.Equivalences MLTT2.Cylinder.

Definition FTYPE : Category.
Proof.
  rapply Build_Category.
  - exact TypeF.
  - exact (λ A B, A -> B).
  - exact (λ A, idmap). 
  - exact (λ A B C g f, g o f).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.


Set Implicit Arguments.
(* g is a retract of f *)
(* f in the middle, g on the side *)
Record Retract {A B} (g : A -> B) {A' B'} (f : A' -> B') :=
  { ret_s : A -> A' ;
    ret_r : A' -> A ;
    ret_s' : B -> B' ;
    ret_r' : B' -> B ;
    ret_sr : ret_r o ret_s ≡≡ idmap ;
    ret_sr' : ret_r' o ret_s' ≡≡ idmap;
    ret_H1 : f o ret_s ≡≡ ret_s' o g ;
    ret_H2 : ret_r' o f ≡≡ g o ret_r }.
Unset Implicit Arguments.

Global Arguments Build_Retract {A B g A' B' f} s r s' r' sr sr' H1 H2 : rename.

Infix "RetractOf" := Retract (at level 30).

Lemma LP_Retract {A A' B' B C C' D D'}
      {f: A -> A'} {g: B' -> B} {f': C -> C'} {g': D' -> D}
      (Hf : f' RetractOf f) (Hg : g' RetractOf g)
  : LP (C:=TYPE) f g -> LP (C:=TYPE) f' g'.
Proof.
  intros H F G H1; cbn in *.
  assert (X: g o (ret_s Hg o F o ret_r Hf) ≡≡ ret_s' Hg o G o ret_r' Hf o f). {
    intro. ref (ret_H1 Hg _ E@ _). apply Eap.
    ref (Eap10 H1 _ E@ _). apply Eap.
    exact (ret_H2 Hf _)^E. }
  specialize (H ((ret_s Hg) o F o (ret_r Hf)) ((ret_s' Hg) o G o (ret_r' Hf)) (eq_funext X)).
  destruct H as [h [H2 H3]]; cbn in *.
  exists ((ret_r Hg) o h o (ret_s' Hf)). split; apply eq_funext; intro x; simpl.
  - transitivity (ret_r Hg (h (f (ret_s Hf x)))).
    repeat apply Eap. exact (ret_H1 Hf _)^E.
    transitivity (ret_r Hg (ret_s Hg (F (ret_r Hf (ret_s Hf x))))).
    apply Eap. apply (Eap10 H2).
    transitivity (F (ret_r Hf (ret_s Hf x))).
    apply (ret_sr Hg). apply Eap. apply (ret_sr Hf).
  - ref ((ret_H2 Hg _)^E E@ _).
    ref (Eap _ (Eap10 H3 _) E@ _).
    ref (ret_sr' Hg _ E@ _).
    apply Eap. exact (ret_sr' Hf _).
Defined.

Definition retract_id {A B} (f: A -> B) : f RetractOf f.
Proof.
  use Build_Retract; intro; cbn; try reflexivity.
Defined.

Definition LP_TYPE_FTYPE {A B A' B': TypeF} {f: A -> B} {g: A' -> B'}
  : LP (C:=TYPE) f g -> LP (C:=FTYPE) f g.
  auto.
Defined.

Record IsFibration {A B} (f : A -> B) := (* F *)
  { fib_A : Type ;
    fib_P : fib_A -> Type ;
    fib_Fib : FibrantF fib_P;
    fib_H : f RetractOf (π1 fib_P) }.

Global Arguments Build_IsFibration {A B f B'} P {FibP} H : rename.

Notation Fib := @IsFibration.

Definition fiber {A B} (f: A -> B) := λ y, ∃ x, f x = y.

Let f' {A B} (f: A → B) : A -> ∃ y, fiber f y
  := λ x, (f x ; x ; 1).

Notation "` A" := (Build_TypeF A) (at level 10).


Definition LP_f'_F {A B: TypeF} (f: A → B)
  : LLP (C:=FTYPE) Fib (f' f : `_ -> `_).
Proof.
  intros A'' B'' g [B' P HP Hg]. apply LP_TYPE_FTYPE.
  ref (LP_Retract (retract_id _) Hg _).
  intros F G H; cbn in *.
  transparent assert (α: ((∃ y, fiber f y) -> ∃ y, P (G y))). {
    refine (λ y, (y; _)).
    destruct y as [y [x p]].
    pose proof (Etransport P (Eap10 H x) (F x).2); cbn in X.
    destruct_path p. exact X. }
  transparent assert (β: ((∃ y, P (G y)) -> sigT P)). {
    exact (λ w, (G w.1; w.2)). }
  exists (β o α). split; [|reflexivity].
  apply eq_funext; intro x.
  use eq_sigma; cbn. exact (Eap10 H _)^E.
  now rewrite Etransport_Vp.
Defined.

Definition wfs_AC_F : weak_factorization_system (@LLP FTYPE (@IsFibration)) (@IsFibration).
Proof.
  use Build_weak_factorization_system; cbn.
  - intros A B f. exists (` (∃ y, fiber f y)).
    exists (f' f). exists (π1 _).
    split; [reflexivity|]. split.
    (* + apply LP_f'_F.  bug?? *)
    + apply (LP_f'_F _).
    + refine (Build_IsFibration _ (retract_id _)).
  - intros A B f; split; auto.
  - intros A B f; split; intros Hf.
    + intros A' B' g Hg. now apply Hg.
    + assert (LP (C:=FTYPE) (f' f: `_ -> `_) f). {
        apply Hf. apply LP_f'_F. }
      specialize (X idmap (π1 _) E1); cbn in X. destruct X as [g [Hg1 Hg2]].
      refine (Build_IsFibration (fiber f) _).
      refine (Build_Retract (f' f) g idmap idmap _ _ _ _);
        intro; try reflexivity; cbn.
      exact (Eap10 Hg1 _). exact (Eap10 Hg2^E _).
Defined.


Record AFib A B (f : A -> B) := (* F *)
  { afib_A : TypeF ;
    afib_P : afib_A -> Type ;
    afib_Fib : FibrantF afib_P ;
    afib_H1 : ∀ y, Contr (afib_P y) ;
    afib_H2 : f RetractOf (π1 afib_P) }.

Global Arguments Build_AFib {A B f B'} P {FibP} HP H : rename.

Definition AFib_Fib {A B} (f: A -> B)
  : AFib _ _ f -> Fib _ _ f.
Proof.
  intros [B' P FibP HP H].
  exact (Build_IsFibration _ H).
Defined.


Section Cylinder.
  Context {X Y : TypeF} {f: X -> Y}.

  Definition top' : X -> exists y, Cyl f y := λ x, (f x; top x).
  Definition base' : Y -> exists y, Cyl f y := λ y, (y; base y).
  (* Definition cyl_eq' `{Fibrant Y} : ∀ x, base' (f x) = top' x *)
    (* := λ x, path_sigma (Cyl f) 1 (cyl_eq x). *)
End Cylinder.

Definition LP_top'_AF {A B: TypeF} (f: A → B)
  : LLP (C:=FTYPE) AFib (top' (f:=f): `_ -> `_).
Proof.
  intros A'' B'' g [B' P FibP HP Hg].
  refine (LP_Retract (g:=_:`_ -> `_) (retract_id _) Hg _).
  clear g Hg. intros F G H; cbn in *.
  use exist.
  - intro w. exists (G w). revert w.
    use sig_cyl_ind; cbn.
    + intro x. exact ((Eap10 H x) E# (F x).2).
    + intro y. use center. apply HP.
    + intro; cbn. use path_contr.
      apply HP.
  - split; cbn. 2: reflexivity.
    apply eq_funext; intro x. use eq_sigma. exact (Eap10 H x)^E.
    rew Etransport_Vp. reflexivity.
Defined.

Definition wfs_C_AF : weak_factorization_system (@LLP FTYPE AFib) AFib.
Proof.
  use Build_weak_factorization_system; cbn.
  - intros A B f. exists (` (sigT (Cyl f))).
    exists top'. exists (π1 _).
    split; [reflexivity|]. split.
    + exact (LP_top'_AF _).
    + ref (Build_AFib _ _ (retract_id _)); cbn.
      apply Cyl_Contr.
  - intros; split; auto.
  - intros A B f; split; intros Hf.
    + intros A' B' g Hg. now apply Hg.
    + assert (LP (C:=FTYPE) (top' (f:=f): `_ -> `_) f). {
        apply Hf. apply LP_top'_AF. }
      specialize (X idmap (π1 _) E1); cbn in X. destruct X as [g [Hg1 Hg2]].
      ref (Build_AFib (Cyl f) _ _); cbn.
      apply Cyl_Contr.
      refine (Build_Retract top' g idmap idmap _ _ _ _);
        intro; try reflexivity; cbn.
      exact (Eap10 Hg1 _). exact (Eap10 Hg2^E _). 
Defined.


Definition weak_eq_retract {A B A' B': TypeF}
           (f: A -> B) (f': A' -> B')
           (Hf': f' RetractOf f) (Hf: IsEquiv f)
  : IsEquiv f'.
Proof.
  destruct Hf as [g Hg1 Hg2].
  destruct Hf' as [s r s' r' sr sr' Hf1 Hf2].
  refine (isequiv_adjointify (r o g o s') _ _); intro.
  - rewi Hf2. ref (ap _ (Hg1 _) @ _). apply Eq_to_paths, sr'.
  - rewi Hf1. ref (ap _ (Hg2 _) @ _). apply Eq_to_paths, sr.
Defined.

Definition two_out_of_three_weak_equiv
  : @two_out_of_three FTYPE (fun _ _ f => IsEquiv f).
Proof.
  intros A B C f g; cbn in *. repeat split; intros H1 H2.
  - now apply isequiv_compose.
  - ref (cancelL_isequiv g); assumption. 
  - ref (cancelR_isequiv f); assumption. 
Defined.


Definition AFib_aux {B: TypeF} {P: B -> Type} {FibP: FibrantF P} (H: IsEquiv (π1 P))
  : ∀ y, Contr (P y).
Proof.
  destruct H as [g Hg1 Hg2 Hg3]. intro y.
  use Build_Contr.
  - refine ((Hg1 y) # (g y).2).
  - intro w.
    specialize (Hg3 (y; w)); cbn in Hg3. rew Hg3; clear Hg3.
    rew (transport_compose P (π1 _) (Hg2 (y; w)) _)^.
    exact (apD _ (Hg2 (y; w))).
Defined.

Definition AFib_ok {A B: TypeF} (f: A -> B)
  : AFib _ _ f  <->  (IsEquiv f × Fib _ _ f).
Proof.
  split; intro H.
  - split.
    + destruct H as [B' P FibP HP Hf].
      ref (weak_eq_retract (_ : ` _ -> ` _) _ Hf _). clear f Hf; cbn.
      use isequiv_adjointify.
      * intro x; exists x; apply HP.
      * intro; exact 1.
      * intros [x w]; cbn.
        rew (contr _ _ w). exact 1.
    + destruct H as [B' P FibP H1 H2]. econstructor. eassumption. exact H2.
  - ref (Build_AFib (fiber f) _ _).
    + pose proof (two_out_of_three_weak_equiv _ _ _ (f' f: `_ -> `_) (pr1: `_ -> `_)); cbn in X.
      destruct X as [_ [_ H2]]. specialize (H2 (fst H)).
      refine (AFib_aux (P:=fiber f) (H2 _)).
      clear H2 H. destruct A, B.
      use isequiv_adjointify.
      * exact (λ w, w.2.1).
      * intros [y [x p]]; cbn. unfold f'.
        destruct_path p. exact 1.
      * intro; exact 1.
    + assert (LP (C:=FTYPE) (f' f: `_ -> `_) f). {
        apply LP_f'_F. apply H. }
      specialize (X idmap pr1 E1); cbn in X. destruct X as [g [Hg1 Hg2]].
      refine (Build_Retract (f' f) g idmap idmap _ _ _ _);
        intro; try reflexivity; cbn.
      exact (Eap10 Hg1 _). exact (Eap10 Hg2^E _).
Defined.

Definition LLPAFib_ok {A B: TypeF} (f: A -> B)
  : LLP (C:=FTYPE) Fib f  <->  (IsEquiv f × LLP (C:=FTYPE) AFib f).
Proof.
  split.
  - intro H; split.
    + ref (let X := H _ B (pr1: `_ -> `_) _ (f' f) idmap E1 in _).
      ref (Build_IsFibration _ (retract_id _)).
      destruct X as [g [Hg1 Hg2]]; cbn in *.
      destruct A, B. use isequiv_adjointify.
      * exact (λ w, (g w).2.1).
      * intro x; pose (g x).2.2. cbn in *.
        rew p. apply Eq_to_paths. exact (Eap10 Hg2 _).
      * intro x; cbn. rew (Eap10 Hg1 x). exact 1.
    + intros A' B' F Hf. apply H. now apply AFib_Fib.
  - intros [H2 H1] A' B' g Hg.
    ref (LP_Retract (f:=f' f: `_ -> `_) _ (retract_id _) _).
    +  clear A' B' g Hg.
       assert (X : AFib (sigT (fiber f)) B pr1). {
         destruct H2 as [g Hg1 Hg2 Hg3].
         ref (Build_AFib _ _ (retract_id _)).
         intro y; cbn. exists (g y; Hg1 _).
         intros [x p].
         ref (path_sigma _ ((ap g p)^ @ Hg2 _) _).
         rew transport_paths_Fl. rew ap_pp. rew (Hg3 _)^.
         rew ap_V. rew inv_pp. rew inv_V.
         rew (ap_compose g f _)^.
         rew concat_pp_p. ref (moveR_Vp _ _ _ _).
         destruct_path p. cbn. exact (concat_1p _ @ (concat_p1 _)^). }
       specialize (H1 (` (sigT (fiber f))) B pr1 X (f' f) idmap E1); clear X.
       destruct H1 as [Ɣ [H H']]; cbn in *.
       use (Build_Retract idmap idmap Ɣ pr1); intro; try reflexivity.
       exact (Eap10 H' _). exact (Eap10 H^E _).
    + now ref (LP_f'_F _ _ _ _ _).
Defined.


Definition fibrant_types_give_fibrations {A: Type} {FibA: Fibrant A}
  : IsFibration (λ _:A, tt).
Proof.
  ref (Build_IsFibration (λ _:`unit, A) _).
  ref (Build_Retract (λ x, (tt; x)) (π2 (λ _:unit, A)) idmap idmap _ _ _ _);
    intro; try reflexivity; cbn.
  destruct x as [[] y]; reflexivity.
Defined.



Definition type_model_structure : model_structure FTYPE.
Proof.
  rapply Build_model_structure.
  - exact (fun _ _ f => IsEquiv f).
  - exact Fib. 
  - exact (@LLP FTYPE AFib).
  - apply two_out_of_three_weak_equiv.
  - eapply wfs_iff_R. apply @AFib_ok.
    exact wfs_C_AF.
  - eapply wfs_iff_L. apply @LLPAFib_ok. exact wfs_AC_F.
Defined.

(* Print Assumptions type_model_structure. *)


(* F are retracts of their π1 : Σ fiber -> B *)
Definition F_caract {A B: TypeF} {f: A -> B}
  : IsFibration f <-> ∃ (g: sigT (fiber f) -> A), f o g ≡≡ pr1 × g o (f' f) ≡≡ idmap.
Proof.
  split.
  - intros [B' P FibP [s r s' r' rs rs' H1 H2]].
    use exist.
    + intros [y [x p]]. apply r. exists (s' y).
      destruct_path p.
      ref ((H1 x) E# _). exact (s x).2.
    + split; cbn.
      * intros [y [x p]]; cbn.
        ref ((H2 _)^E E@ _); cbn. apply rs'.
      * intro x. ref (_ E@ rs x).
        apply Eap. use eq_sigma. exact (H1 _)^E.
        apply Etransport_Vp.
  - intros [g [H1 H2]].
    ref (Build_IsFibration (fiber f) _).
    ref (Build_Retract (f' f) g idmap idmap _ _ _ _);
      intro; cbn; try reflexivity.
    apply H2. sym H1.
Defined.


(* AC are retracts of their f' *)
Definition AC_caract {A B: TypeF} (f: A -> B)
  : LLP (C:=FTYPE) Fib f <-> ∃ (g: B -> sigT (fiber f)), g o f ≡≡ f' f × pr1 o g ≡≡ idmap.
Proof.
  split; intro H.
  - specialize (H (` (sigT (fiber f))) _ pr1 (Build_IsFibration _ (retract_id _))).
    specialize (H (f' f) idmap E1).
    destruct H as [g [H1 H2]]. exists g. split; apply Eap10; assumption.
  - intros X Y g Hg. ref (LP_Retract (f:=f' f: `_ -> `_) _ (retract_id _) _).
    use (Build_Retract idmap idmap H.1 pr1); try (intro; reflexivity).
    apply H.2. cbn. symmetry. apply H.2.
    now apply (LP_f'_F _).
Defined.

Record Cofib {A B} (f : A -> B) := (* C *)
  { cofib_A : TypeF ;
    cofib_B : TypeF ;
    cofib_k : cofib_A -> cofib_B ;
    cofib_H : f RetractOf (top' (f:=cofib_k)) }.
Arguments Build_Cofib {A B f A' B'} k H : rename.

(* C are injections into cylinders *)
Definition C_caract {A B: TypeF} (f: A -> B)
  : LLP (C:=FTYPE) AFib f <-> Cofib f.
Proof.
  split.
  - intro Hf. use (Build_Cofib f).
    specialize (Hf (` (sigT (Cyl f))) B pr1).
    specialize (Hf (Build_AFib (Cyl f) Cyl_Contr (retract_id _))).
    specialize (Hf top' idmap E1).
    destruct Hf as [g [Hg1 Hg2]]; cbn in *.
    use (Build_Retract idmap idmap g pr1); intro; try reflexivity.
    exact (Eap10 Hg2 _). exact (Eap10 Hg1^E _).
  - intros [A' B' f' Hf] A'' B'' g Hg.
    use (LP_Retract (f:=_:`_->`_) Hf (retract_id _)).
    ref (LP_top'_AF _ _ _ g Hg).
Defined.

(* C are injections in THEIR cylinders *)
Definition C_caract2 {A B: TypeF} (f: A -> B)
  : LLP (C:=FTYPE) AFib f <-> ∃ (g: B -> sigT (Cyl f)), g o f ≡≡ top' × pr1 o g ≡≡ idmap.
Proof.
  split.
  - intro Hf.
    specialize (Hf (` (sigT (Cyl f))) B pr1).
    specialize (Hf (Build_AFib (Cyl f) Cyl_Contr (retract_id _))).
    specialize (Hf top' idmap E1).
    destruct Hf as [g [Hg1 Hg2]]; cbn in *.
    exists g; split; now apply Eap10.
  - intros [g [H1 H2]].
    intros A' B' h H.
    ref (LP_Retract (f:=top' (f:=f): `_->`_) _ (retract_id _) _).
    + use (Build_Retract idmap idmap g pr1); try (intro; reflexivity).
      exact H2. intro; cbn; sym H1.
    + apply (LP_top'_AF _). assumption.
Defined.
  
Definition Cofib_W {A B: TypeF} (f: A -> B)
  : IsEquiv (top' (f:=f)) <-> IsEquiv f.
Proof.
  assert (H': IsEquiv (π1 (Cyl f))). {
    destruct A, B.
    use isequiv_adjointify. exact base'.
    intro; cbn. exact 1.
    intro x. unfold base'. ref (path_sigma _ 1 _); cbn.
    apply (contr _ (Cyl_Contr (f:=f) x.1)). }
  split; intro H.
  - exact (isequiv_compose H H').
  - ref (cancelL_isequiv (π1 (Cyl f))).
    exact H'. exact H.
Defined.

Record ACofib {A B} (f : A -> B) := (* AC *)
  { acofib_A : TypeF ;
    acofib_B : TypeF ;
    acofib_k : acofib_A -> acofib_B ;
    acofib_Hk : IsEquiv acofib_k ;
    acofib_H : f RetractOf (top' (f:=acofib_k)) }.

Arguments Build_ACofib {A B f A' B'} k Hk H : rename.

(* AC are injections into cylinders of weak equivalences *)
Definition AC_caract2 {A B: TypeF} (f: A -> B)
  : LLP (C:=FTYPE) Fib f <-> ACofib f.
Proof.
  use transitive_iff. 2: apply LLPAFib_ok. split.
  - intros [Hf H].
    ref (Build_ACofib f Hf _).
    specialize (H (` (sigT (Cyl f))) B pr1).
    assert (AFib (∃ y, Cyl f y) B pr1). {
      ref (Build_AFib _ _ (retract_id _)).
      cbn. apply Cyl_Contr. }
    specialize (H X top' idmap E1); clear X.
    destruct H as [g [H1 H2]]; cbn in *.
    ref (Build_Retract idmap idmap g pr1 _ _ _ _);
      intro; try reflexivity.
    now apply Eap10. exact (Eap10 H1 _)^E.
  - intros [A' B' k Hk H]; split.
    + ref (weak_eq_retract (_: `_ -> `_) _ H _); clear H; cbn.
      revert Hk. apply Cofib_W.
    + apply C_caract. ref (Build_Cofib k H).
Defined.


Definition IsInjEq {A B: TypeF} (f: A -> B)
  := ∃ (r: B -> A) (H1: r o f ≡≡ idmap) (H2: f o r == idmap),
  forall x, H2 (f x) ≡ Eq_to_paths (Eap f (H1 x)).

(* AC are injective equivalences *)
Definition AC_caract3 {A B: TypeF} (f: A -> B)
  : LLP (C:=FTYPE) Fib f <-> IsInjEq f.
Proof.
  use transitive_iff.
  2: apply AC_caract. split.
  - intros [g [H1 H2]]. exists (λ y, (g y).2.1).
    use exist. intro x. exact (Eap (λ w, w.2.1) (H1 x)).
    use exist. intro y. pose (g y).2.2. cbn in *.
    ref (concat_pE (g y).2.2 _). exact (H2 y).
    intro x; cbn.
    pose (EapD (λ w: sigT (fiber f), w.2.2) (H1 x)^E); cbn in *.
    rewi e; clear e.
    pose (Etransport_paths_FlFrE (f:=λ w, f w.2.1) (g:= pr1) (H1 x)^E E1);
      cbn in *.
    ref (Eap (λ p, concat_pE p (H2 (f x))) _ E@ _).
    2: exact e; clear e.
    ref (concat_pE_ETP _ _ E@ Eap Eq_to_paths (Eq_UIP _ _)).
  - intros [s [H1 [H2 H3]]].
    use exist. ref (fun y => (y; s y; H2 y)).
    split; cbn.
    intro x. ref (eq_sigma _ E1 _); cbn.
    ref (eq_sigma _ (H1 x) _). rew (H3 x).
    ref (Etransport_paths_FlFrE (H1 x) (Eap f (H1 x)) E@ _).
    set (H1 x). destruct e. reflexivity.
    reflexivity.
Defined.

Definition AF_caract {A B: TypeF} (f: A -> B)
  : AFib _ _ f <-> ∃ g : (∃ x, Cyl f x) -> A, g o top' ≡≡ idmap × f o g ≡≡ pr1.
Proof.
  split.
  - intro H.
    pose proof (LP_top'_AF f _ _ f H idmap pr1 E1).
    destruct X as [g [Hg1 Hg2]]; cbn in *.
    exists g. split; ref (Eap10 _); assumption.
  - intros [g [Hg1 Hg2]]. use (Build_AFib (Cyl f)).
    apply Cyl_Contr.
    ref (Build_Retract top' g idmap idmap _ _ _ _); cbn; try reflexivity.
    exact Hg1. intro; sym Hg2.
Defined.

(* Print Assumptions type_model_structure. *)
(* Print Assumptions F_caract. *)
(* Print Assumptions C_caract2. *)
(* Print Assumptions AF_caract. *)






Definition pi1_fib {A} (P: A -> Type) (H: forall x, IsFibration (fun _: P x => tt))
  : IsFibration (π1 P).
  pose (B := fun x => (fib_A _ (H x))).
  pose (Q := (fun w: sigT B => (fib_P _ (H w.1)) w.2)). 
  ref (Build_IsFibration Q _) .
  pose (Fib := fun x => (fib_Fib _ (H x))). classes.
  pose (R := fun x => (fib_H _ (H x))).
  pose (s := fun x => ret_s (R x) : _ -> exists y, Q (x; y)).
  pose (r := fun x => ret_r (R x) : (exists y, Q (x; y)) -> _).
  pose (s' := fun x => ret_s' (R x) : _ -> B x).
  pose (r' := fun x => ret_r' (R x) : B x -> _).
  use Build_Retract.    
  - intros [x y]. ref ((x; _); (s x y).2).
  - intros [[x y] z]. ref (x; r x (y; z)).
  - intro x. ref (x; s' x tt).
  - intros [x y]. exact x.
  - intros [x y]; cbn. ref (eq_sigma _ E1 _); cbn.
    exact (ret_sr (R x) y).
  - intros x; cbn. reflexivity.
  - intros [x y]; cbn.  ref (eq_sigma _ E1 _); simpl.
    exact (ret_H1 (R x) y).
  - intros  [[x y] z]; cbn.  reflexivity.
Defined.
    

