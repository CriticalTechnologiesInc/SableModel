theory Abstract
imports
  "../lib/NondetExtensions"
  TPM_Driver
begin

definition
  get_authdata :: "TPM.AUTHDATA s_monad"
where
  "get_authdata \<equiv> unknown"

definition
  get_nonce :: "TPM.NONCE s_monad"
where
  "get_nonce \<equiv> unknown"

definition
  read_passphrase :: "(string TPM.STORED_DATA) s_monad"
where
  "read_passphrase \<equiv> TPM_NV_ReadValue 4 0 None <catch> (\<lambda>e. exit_r)"

definition
  A_proc :: "(astate, astate) data_type"
where
  "A_proc \<equiv> \<lparr>
    Init = \<lambda>s. {s},
    Fin = id,
    Run = lift_nd read_passphrase
  \<rparr>"

end