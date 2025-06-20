open HolKernel Parse boolLib bossLib;

val _ = new_theory "argmin_extreal";

open extrealTheory;
open dep_rewrite;

Definition argmin_def:
  argmin f xs = iterate (λx y. if f x < f y : extreal then x else y) xs I
End

Definition argmax_def:
  argmax f xs = argmin (λx. -(f x)) xs
End

val _ = export_theory();
