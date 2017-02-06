theory Impl
imports
  "../lib/ComExtensions"
  "../lib/NondetExtensions"
begin

(* Parse the input file. *)
install_C_file  "../src/sable_verified.cpp"

(* Abstract the input file. *)
autocorres "../src/sable_verified.cpp"

context sable_verified
begin

thm get_pcr_info'_def
thm seal_passphrase'_def
thm unseal_passphrase'_def
thm write_passphrase'_def
thm read_passphrase'_def
thm configure'_def
thm trusted_boot'_def

end

locale sable = sable_verified
begin

definition
  C_proc :: "(globals myvars, observable) data_type"
where
  "C_proc \<equiv> \<lparr>
    Init = \<lambda>_. UNIV,
    Fin = \<lambda>_. ({}, {}), 
    Run = lift_com (Call main_'proc) (all_global_addresses.\<Gamma> symbol_table)
  \<rparr>"

abbreviation "main \<equiv> all.main' symbol_table :: (lifted_globals, int) nondet_monad"

definition
  AC_proc :: "(lifted_globals, observable) data_type"
where
  "AC_proc \<equiv> \<lparr>
    Init = \<lambda>_. UNIV,
    Fin = \<lambda>_. ({}, {}),
    Run = lift_nd main
  \<rparr>"

end

end