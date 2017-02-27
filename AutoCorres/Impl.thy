theory Impl
imports
  "../lib/ComExtensions"
  "../lib/NondetExtensions"
  "../Abstract/AMonad"
begin

(* Parse the input file. *)
install_C_file "../src/sable_verified_pp.c" [machinety = machine_state]

(* Abstract the input file. *)
autocorres "../src/sable_verified_pp.c"

context sable_verified_pp
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
  C_proc :: "(globals myvars, astate) data_type"
where
  "C_proc \<equiv> \<lparr>
    Init = \<lambda>_. UNIV,
    Fin = \<lambda>s. \<lparr>
        machine = phantom_machine_state_'' s,
        sessions = empty_Session
      \<rparr>,
    Run = lift_com (Call main_'proc) (all_global_addresses.\<Gamma> symbol_table)
  \<rparr>"

value "\<lambda>s :: lifted_globals. phantom_machine_state_'' s"

definition
  AC_proc :: "(lifted_globals, astate) data_type"
where
  "AC_proc \<equiv> \<lparr>
    Init = \<lambda>_. {s. (let ms = phantom_machine_state_'' s in powerOn ms = True) \<and>
        Ball (set (array_addrs (Ptr (symbol_table ''sessions'')) 2)) (\<lambda>p.
        is_valid_tdTPM_SESSION_C'ptr s p \<and> heap_tdTPM_SESSION_C'ptr s p = NULL)},
    Fin = \<lambda>s. \<lparr>
        machine = phantom_machine_state_'' s,
        sessions = empty_Session
      \<rparr>,
    Run = lift_nd trusted_boot'
  \<rparr>"

end

end