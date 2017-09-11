theory tests
imports
  "../lib/ComExtensions"
  "../lib/NondetExtensions"
  "../Abstract/AMonad"
begin

(* Parse the input file. *)
install_C_file "tests.c" [machinety = machine_state]

(* Abstract the input file. *)
autocorres [
] "tests.c"

lemma onf: "\<lbrace> \<lambda>s.  True \<rbrace> tests.f' ?symbol_table
             \<lbrace> \<lambda> r s. heap_w32 s (Ptr (?symbol_table ''a'')) =2 \<rbrace>!"
apply(auto)

end