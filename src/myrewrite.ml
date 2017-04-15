open Names

let mp = ModPath.MPfile (DirPath.make (List.rev_map Id.of_string ["ModelStructure"; "MLTT2"; "Overture"]))
let mp' = ModPath.MPdot (mp, Label.make "Paths")
let eq = MutInd.make2 mp' (Label.make "paths")

(* type constant_repr = *)
(* | Same of KerName.t *)
(* | Dual of KerName.t * KerName.t *)

let hack_replace_const scheme (kn : KerName.t) =
  let (const, _) = Ind_tables.find_scheme scheme (eq, 0) in
  let const = Obj.repr const in
  let () = Obj.truncate const 1 in
  let () = Obj.set_tag const 0 in
  let () = Obj.set_field const 0 (Obj.repr kn) in
  ()

let () =
  let open Eqschemes in
  let hack () =
    List.iter (fun (sk, kn) -> hack_replace_const sk kn) [
      rew_l2r_scheme_kind, KerName.make2 mp' (Label.make "paths_rec'");
      rew_r2l_scheme_kind, KerName.make2 mp' (Label.make "paths_rec");
    ]
  in
  Mltop.declare_cache_obj hack "myrewrite"
