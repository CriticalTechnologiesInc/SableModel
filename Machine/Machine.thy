theory Machine
imports
  TPM
begin

record machine_state =
  powerOn :: bool
  tpm :: tpm_state

type_synonym 'a machine_monad = "(machine_state, 'a) nondet_monad"

definition
  tpm_lift :: "'a tpm_monad \<Rightarrow> 'a machine_monad"
where
  "tpm_lift m \<equiv>
   do
    tpm_state \<leftarrow> gets tpm;
    (r, tpm_state') \<leftarrow> select_f (m tpm_state);
    modify (\<lambda>s. s \<lparr> tpm := tpm_state' \<rparr>);
    return r
   od"

end