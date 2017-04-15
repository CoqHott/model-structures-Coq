(* -*- coq-prog-args: ("-top" "ModelStructure.MLTT2.Overture") -*-  *)
Require Export ModelStructure.Overture.

Axiom Fibrant : Type -> Type.
Existing Class Fibrant.

Notation "'FibrantF' P" := (forall x, Fibrant (P x)) (at level 10) : Fib_scope.
Notation "'FibrantF2' P" := (forall x y, Fibrant (P x y)) (at level 10) : Fib_scope.
Open Scope Fib_scope.

Record TypeF := {
  TypeF_T : Type;
  TypeF_F : Fibrant TypeF_T
}.

Arguments Build_TypeF _ {_}.

Coercion TypeF_T : TypeF >-> Sortclass.
Global Existing Instance TypeF_F.


Axiom Fibrant_forall
  : forall A (B: A -> Type), Fibrant A -> (forall x, Fibrant (B x)) -> Fibrant (forall x, B x).

Axiom Fibrant_sigma
  : forall A (B: A -> Type), Fibrant A -> (forall x, Fibrant (B x)) -> Fibrant (sigT B).

(* Axiom Fibrant_Type : Fibrant Type. *)

(* Axiom Fibrant_TypeF : Fibrant FType. *)

Axiom Fibrant_unit : Fibrant unit.

Module Export Paths.
  Private Inductive paths {A : Type} (a : A) : A -> Type :=
    idpath : paths a a.

  Arguments idpath {A a} , [A] a.

  Definition paths_ind (A : Type) {FibA: Fibrant A} (a : A)
             (P : forall a0 : A, paths a a0 -> Type) {FibP: FibrantF2 P}
             (f: P a idpath) (y : A) (p : paths a y) : P y p
    := match p as p0 in (paths _ y0) return (P y0 p0) with
       | idpath => f
       end.
  Arguments paths_ind [A _] a P [_] f y p.
  
  Definition paths_rec (A : Type) {FibA: Fibrant A} (a : A) (P : A -> Type)
             {FibP: FibrantF P} (f : P a) (y : A) (p : paths a y)
    : P y := 
    match p in (paths _ y0) return (P y0) with
    | idpath => f
    end.
    
  Axiom Fibrant_paths : forall (A: Type) {FibA: Fibrant A} (x y: A), Fibrant (paths x y).

  
  (** The inverse of a path. *)
  Definition inverse {A : Type} {FibA: Fibrant A} {x y : A} (p : paths x y) : paths y x
    := @paths_rec A FibA x (fun y => paths y x) _ idpath y p.
  
  Definition paths_rec' A {FibA: Fibrant A} a y P {FibP: FibrantF P} (X : P y)
             (H : @paths A a y) : P a
    := @paths_rec A FibA y P FibP X _ (inverse H).


  (* ****** myrewrite plugin ****** *)
  (* This plugin is to avoid a flaw in the mechanism of private inductive types. *)
  (* When we rewrite with a path equality, Coq uses the automatically generated terms internal_paths_rew and internal_paths_rew_r.*)
  (* However, those terms doesn't check the fibrancy condition.  *)
  (* Hence this plugin forces Coq to use paths_rec and paths_rec' instead. *)
  Declare ML Module "myrewrite".
End Paths.

Arguments paths_rec [A _] a P [_] f y p.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :> _) : type_scope.

Notation "f == g" := (forall x, f x = g x) (at level 70, no associativity) : type_scope.


Tactic Notation "rew" open_constr(H)
  := rewrite H; auto with typeclass_instances.
Tactic Notation "rewi" open_constr(H)
  := rewrite <- H; auto with typeclass_instances.

(* This does not fail if you comment the "Declare ML Module..." line above. *)
Lemma  paths_rew_r_test_should_fail A {FibA: Fibrant A} a y P (X : P y) (H : a = y :> A) : P a.
Proof. Fail rewrite H; assumption. Abort.

Lemma paths_rew_test A {FibA: Fibrant A} a y P {FibP: FibrantF P} (X : P a) (H : a = y :> A) : P y.
Proof. rewi H. Defined.

Lemma paths_rew_r_test A {FibA: Fibrant A} a y P {FibP: FibrantF P} (X : P y) (H : a = y :> A) : P a.
Proof. rew H. Defined.


Definition Eq_to_paths {A : Type} {FibA: Fibrant A} {x y : A} (p : x ≡ y) : x = y :=
  match p with
    | refl => idpath
  end.


Definition concat {A : Type} {FibA: Fibrant A} {x y z : A} (p : x = y) (q : y = z) : x = z.
Proof.
  ref (@paths_rec A _ y (fun z => x = z) _
                  (@paths_rec A _ x (fun y => x = y)_ idpath y p) z q).
Defined.

Arguments concat {A FibA x y z} !p !q.

Delimit Scope path_scope with path.
Open Scope path_scope.

Notation "p @ q" := (concat p%path q%path) (at level 20) : path_scope.
Notation "p ^" := (inverse p%path) (at level 3, format "p '^'") : path_scope.
Notation "1" := idpath : path_scope.



Definition transport {A : Type} {FibA: Fibrant A} (P : A -> Type)
           {FibP: FibrantF P}  {x y : A} (p : x = y) (u : P x) : P y
  := paths_rec x P u y p.

Arguments transport {A}%type_scope {FibA} P {FibP} {x y} p%path_scope u : simpl nomatch.

Notation "p # x"
  := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.


Record Contr (A: Type) {FibA: Fibrant A} :=
  { center : A;
    contr : ∀ x, center = x }.



(* ****** destruct_path tactic ****** *)

(* auxiliary tactics *)
Definition myid : forall A, A -> A := fun _ x => x.
Ltac mark H := let t := type of H in change (myid _ t) in H.
Ltac unmark H := let t := type of H in
                 match t with
                 | myid _ ?tt => change tt in H
                 end.
Hint Unfold myid : typeclass_instances.    

(* If p : x = y  then destruct_path revert all hypothesis depending on x and y.  *)
(* Then, it applies paths_ind and then it reintroduce reverted hypothesis. *)
Ltac destruct_path p :=
  let t := type of p in
  match t with
    @paths _ ?x ?y =>
    mark p;
      repeat match goal with
             | [X: context[y] |- _] =>
               match type of X with
               | myid _ _ => fail 1
               | _ => revert X;
                   match goal with
                   | |- forall (X: ?T), ?G => change (forall (X: myid _ T), G)
                   end
               end
             end;
      unmark p;
      generalize y p; clear p y;
      match goal with
      | |- forall y p, @?P y p => let y := fresh y in
                                  let p := fresh p in
                                  intros y p; refine (paths_ind x P _ y p)
      end;
      repeat match goal with
             | |- forall (H: myid _ _), _ => let H := fresh H in
                                             intro H; unfold myid in H
             end
  end.
