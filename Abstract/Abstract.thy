theory Abstract
imports
  "../lib/NondetExtensions"
  TPM_Driver
begin

(*definition
  exit :: "unit s_monad"
where
  "exit \<equiv> \<lambda>s. ({}, False)"

definition
  getAuthData :: "auth_data s_monad"
where
  "getAuthData \<equiv>
   do
    auth \<leftarrow> select UNIV;
    return auth
   od"

definition
  authorize :: "auth_data \<Rightarrow> (device_error + unit) s_monad"
where
  "authorize auth \<equiv> select UNIV"

definition
  main :: "int s_monad"
where
  "main \<equiv>
   do
    auth \<leftarrow> getAuthData;
    authorize auth
    <catch> (\<lambda>_. exit);
    return 0
   od"

definition
  A_proc :: "(astate, astate) data_type"
where
  "A_proc \<equiv> \<lparr>
    Init = \<lambda>s. {s},
    Fin = id,
    Run = lift_nd main
  \<rparr>"*)

end