theory Abstract
imports
  "../lib/NondetExtensions"
  TPM_Driver
begin

definition
  get_authdata :: "TPM.AUTHDATA E_monad"
where
  "get_authdata \<equiv> unknown"

definition
  get_nonce :: "TPM.NONCE E_monad"
where
  "get_nonce \<equiv> unknown"

definition
  read_passphrase :: "nat \<Rightarrow> (string TPM.STORED_DATA) E_monad"
where
  "read_passphrase i \<equiv> TPM_NV_ReadValue i 0 None"

definition
  A_proc :: "(astate, astate) data_type"
where
  "A_proc \<equiv> \<lparr>
    Init = \<lambda>s. {s},
    Fin = id,
    Run = lift_nd (read_passphrase 4)
  \<rparr>"

end