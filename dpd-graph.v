Require HTS.Model_structure.

(* Add ML Path "/home/rascar/.opam/coq/lib/coq/user-contrib/dpdgraph". *)
Add ML Path "/home/rascar/Dépôts/coq-dpdgraph-bertot".
Print ML Path.


Declare ML Module "dpdgraph".

Set DependGraph File "type_model_structure.dpd".
Print DependGraph Model_structure.type_model_structure.

Set DependGraph File "Model_structure.dpd".
Print FileDependGraph Model_structure.

Set DependGraph File "All.dpd".
Print FileDependGraph ModelStructure.Overture ModelStructure.HTS.Overture HTS.Overture Category Strict_eq Path_eq Equivalences Cylinder Model_structure.