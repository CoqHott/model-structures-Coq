Require Export Utf8_core.


Axiom proof_admitted : forall {a}, a.
Tactic Notation "admit" := exact proof_admitted.

Tactic Notation "sym" simple_intropattern(H) := symmetry; apply H.

Tactic Notation "ref" uconstr(p) := simple refine p.


(* From the HoTT library and a coment of Jason Gross on Github. *)

Ltac rapply p :=
  simple refine p ||
  simple refine (p _) ||
  simple refine (p _ _) ||
  simple refine (p _ _ _) ||
  simple refine (p _ _ _ _) ||
  simple refine (p _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

Tactic Notation "use" uconstr(p) := rapply p. 

Tactic Notation "classes" := typeclasses eauto.


(* From the HoTT library. *)

(** [transparent assert (H : T)] is like [assert (H : T)], but leaves the body transparent. *)
(** Since binders don't respect [fresh], we use a name unlikely to be reused. *)
Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" :=
  simple refine (let __transparent_assert_hypothesis := (_ : type) in _);
  [
  | ((* We cannot use the name [__transparent_assert_hypothesis], due to some infelicities in the naming of bound variables.  So instead we pull the bottommost hypothesis. *)
    let H := match goal with H := _ |- _ => constr:(H) end in
    rename H into name) ].
Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" "by" tactic3(tac) := let name := fresh "H" in transparent assert (name : type); [ solve [ tac ] | ].