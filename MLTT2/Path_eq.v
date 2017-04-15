Require Import MLTT2.Overture.

Definition ap {A B: Type} {FibA: Fibrant A} {FibB: Fibrant B} (f: A -> B) {x y: A} (p: x = y)
  : f x = f y
  := paths_rec x (fun y => f x = f y) idpath y p.

Arguments ap {A B}%type_scope {FibA FibB} f {x y} p%path_scope.

Definition apD {A: Type} {FibA: Fibrant A} {B: A -> Type} {FibB: FibrantF B}
           (f: forall a: A, B a) {x y: A} (p: x = y)
  : p # (f x) = f y
  := paths_ind x (fun y p => transport B p (f x) = f y) 1 y p.

Arguments apD {A%type_scope FibA B FibB} f {x y} p%path_scope : simpl nomatch.


Definition ap_pp {A B} {FibA: Fibrant A} {FibB: Fibrant B} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q).
Proof.
  destruct_path p.
  destruct_path q.
  exact 1.
Defined.

Definition ap_V {A B} {FibA: Fibrant A} {FibB: Fibrant B} (f : A -> B) {x y : A} (p : x = y) :
  ap f (p^) = (ap f p)^.
Proof.
  destruct_path p; exact 1.
Defined.

Definition inv_pp {A} {FibA: Fibrant A} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q)^ = q^ @ p^.
Proof.
  destruct_path p.
  destruct_path q.
  exact 1.
Defined.

Definition inv_V {A} {FibA: Fibrant A} {x y : A} (p : x = y) :
  p^^ = p.
Proof.
  destruct_path p; exact 1.
Defined.

Definition ap_compose {A B C} {FibA: Fibrant A} {FibB: Fibrant B} {FibC: Fibrant C} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g o f) p = ap g (ap f p).
Proof.
  destruct_path p; exact 1.
Defined.

Definition concat_p_pp {A} {FibA: Fibrant A} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r.
Proof.
  destruct_path r.
  destruct_path q.
  destruct_path p.
  exact 1.
Defined.

Definition concat_pp_p {A} {FibA: Fibrant A} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p @ q) @ r = p @ (q @ r).
Proof.
  destruct_path r.
  destruct_path q.
  destruct_path p.
  exact 1.
Defined.

Definition concat_1p {A} {FibA: Fibrant A} {x y: A} (p: x = y)
  : 1 @ p = p.
Proof.
  destruct_path p.
  exact 1.
Defined.

Definition concat_p1 {A} {FibA: Fibrant A} {x y: A} (p: x = y)
  : p @ 1 = p.
Proof.
  destruct_path p.
  exact 1.
Defined.

Definition concat_pV {A} {FibA: Fibrant A} {x y : A} (p : x = y) :
  p @ p^ = 1
  := paths_ind x (fun y p => p @ p^ = 1) 1 _ _.

Definition concat_Vp {A} {FibA: Fibrant A} {x y : A} (p : x = y) :
  p^ @ p = 1
  := paths_ind x (fun y p => p^ @ p = 1) 1 _ _.

Definition moveR_Vp {A} {FibA: Fibrant A} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  p = r @ q -> r^ @ p = q.
Proof.
  destruct_path r.
  intro h. exact (concat_1p _ @ h @ concat_1p _).
Defined.

Definition moveL_Vp {A} {FibA: Fibrant A} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> q = r^ @ p.
Proof.
  destruct_path r.
  intro h. exact ((concat_1p _)^ @ h @ (concat_1p _)^).
Defined.

Definition moveR_M1 {A} {FibA: Fibrant A} {x y : A} (p q : x = y) :
  1 = p^ @ q -> p = q.
Proof.
  destruct_path p.
  intro h. exact (h @ (concat_1p _)).
Defined.

Definition concat_pA1 {A} {FibA: Fibrant A} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) =  q @ (p y)
    := paths_ind x (fun y q => (p x) @ (ap f q) = q @ (p y))
               (concat_p1 _ @ (concat_1p _)^) y q.


Definition path_sigma {A: Type} {FibA: Fibrant A}
           (P: A -> Type) {FibP: FibrantF P}
           {x x': A} {y: P x} {y': P x'}
           (p: x = x') (q: p # y = y')
  : (x; y) = (x'; y').
Proof.
  destruct_path p.
  destruct_path q.
  exact 1.
Defined.

Definition path_contr {A} {FibA: Fibrant A} {HA: Contr A} (x y : A)
  : x = y.
Proof.
  exact ((contr _ _ _)^ @ contr _ HA _).
Defined.



Definition transport_compose {A B} {FibA: Fibrant A} {FibB: Fibrant B}
           {x y: A} (P: B → Type) {FibP : FibrantF P}
           (f : A → B) (p : x = y) (z : P (f x))
  : transport (P o f) p z = transport P (ap f p) z.
Proof.
  destruct_path p.
  exact 1.
Defined.

Definition transport_const {A B} {FibA: Fibrant A} {FibB: Fibrant B}
           {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport (fun x => B) p y = y.
Proof.
  refine (paths_ind x1 (fun x2 p => p # y = y) 1 x2 p).
Defined.

Definition transport_paths_r A {FibA: Fibrant A} {x y1 y2: A}
           (p : y1 = y2) (q : x = y1)
  : transport (λ y : A, x = y) p q = q @ p.
Proof.
  destruct_path p. 
  destruct_path q.
  exact 1.
Defined.

Definition transport_paths_Fl {A B} {FibA: Fibrant A} {FibB: Fibrant B} 
           (f: A → B) {x1 x2: A} {y: B} (p: x1 = x2) (q: f x1 = y)
  : transport (λ x : A, f x = y) p q = (ap f p)^ @ q.
Proof.
  destruct_path q.
  destruct_path p.
  exact 1.
Defined.

Definition transport_paths_Fr {A B} {FibA: Fibrant A} {FibB: Fibrant B} 
           (f: A → B) {x1 x2: A} {y: B} (p: x1 = x2) (q: y = f x1)
  : transport (λ x : A, y = f x) p q = q @ ap f p.
Proof.
  destruct_path p. cbn.
  exact (concat_p1 _)^.
Defined.



Definition concat_Ep {A} {FibA: Fibrant A} {x y z : A} (e: x ≡ y) (p: y = z) : x = z
  := Etransport (λ u, u = z) e^E p.

Definition concat_EVp {A} {FibA: Fibrant A} {x y z : A} (e: y ≡ x) (p: y = z) : x = z
  := Etransport (λ u, u = z) e p.

Definition concat_pE {A} {FibA: Fibrant A} {x y z : A} (p: x = y) (e: y ≡ z) : x = z
  := Etransport (λ v, x = v) e p.

Definition concat_Ep_ETP {A} {FibA: Fibrant A} {x y z: A} (e: x ≡ y :> A) (p: y ≡ z)
  : concat_Ep e (Eq_to_paths p) ≡ Eq_to_paths (e E@ p).
Proof.
  destruct e; cbn. apply Eap, Eq_UIP.
Defined.

Definition concat_EVp_ETP {A} {FibA: Fibrant A} {x y z: A} (e: y ≡ x :> A) (p: y ≡ z)
  : concat_EVp e (Eq_to_paths p) ≡ Eq_to_paths (e^E E@ p).
Proof.
  destruct e; cbn. apply Eap, Eq_UIP.
Defined.

Definition concat_pE_ETP {A} {FibA: Fibrant A} {x y z: A} (p: x ≡ y) (e: y ≡ z)
  : concat_pE (Eq_to_paths p) e ≡ Eq_to_paths (p E@ e).
Proof.
  destruct e; cbn. apply Eap, Eq_UIP.
Defined.

Definition ap_concat_Ep {A B} {FibA: Fibrant A}  {FibB: Fibrant B} (f: A -> B)
           {x y z: A} (e: x ≡ y :> A) (p: y = z)
  : ap f (concat_Ep e p) ≡ concat_Ep (Eap f e) (ap f p).
Proof.
    now destruct e.
Defined.

Definition ap_concat_EVp {A B} {FibA: Fibrant A} {FibB: Fibrant B} (f: A -> B)
           {x y z: A} (e: y ≡ x) (p: y = z)
  : ap f (concat_EVp e p) ≡ concat_EVp (Eap f e) (ap f p).
Proof.
    now destruct e.
Defined.

Definition ap_concat_pE {A B} {FibA: Fibrant A} {FibB: Fibrant B} (f: A -> B)
           {x y z: A} (p: x = y) (e: y ≡ z)
  : ap f (concat_pE p e) ≡ concat_pE (ap f p) (Eap f e).
Proof.
    now destruct e.
Defined.


Definition Etransport_paths_FlFrE {A B} {FibB: Fibrant B} {f g: A -> B} {x1 x2: A} (p: x1 ≡ x2) (q: f x1 ≡ g x1)
  : Etransport (fun x => f x = g x) p (Eq_to_paths q) ≡ Eq_to_paths ((Eap f p^E) E@ q E@ (Eap g p)).
Proof.
  destruct p; simpl. apply Eap, Eq_UIP.
Defined.

(* Axiom ap_compose_strict : *)
(*   ∀ {A B C} {FibA: Fibrant A} {FibB: Fibrant B} {FibC: Fibrant C} *)
(*     (f: A → B) (g: B → C) {x y: A} (p: x = y), *)
(*     ap (g o f) p ≡ ap g (ap f p). *)
